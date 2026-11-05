module

public import VolumePolynomials.RightTrianglePrism

@[expose] public section
set_option autoImplicit false

/-! # Actual roof and floor weights of the right-triangle prism

The two weights are recovered from actual vertical extrusion and translation
invariance. This avoids assuming a surface-measure normalization formula.
-/

noncomputable section
open Set MeasureTheory Matrix Filter
open scoped Pointwise BigOperators Topology

namespace VolumePolynomials.PlanarInteraction

open PlanarExtrusion PlanarMixedForm PlanarCorner PlanarEdges OAI.Paper092
open PolytopeFirstVariation

theorem mixed3_zero_first (B C : ConvexBody Space) : mixed3 0 B C = 0 := by
  first
  | simpa only [mixed3, Matrix.vecCons, Fin.update_cons_zero] using
      mixedVolume_zero_arg volume ![B, B, C] 0

theorem mixed3_point_first (v : Space) (B C : ConvexBody Space) : mixed3 (pointBody v) B C = 0 := by
  first
  | have h := mixed3_translate (0 : ConvexBody Space) B C v 0 0
    simp only [translateBody_zero] at h
    change mixed3 (pointBody v + 0) B C = _ at h
    simpa only [add_zero, mixed3_zero_first] using h

def verticalUnit : ConvexBody Space where
  carrier := horizontal (E := Plane) 1
  convex' := (convex_Icc (0 : ℝ) 1).prod (convex_singleton (0 : Plane))
  isCompact' := horizontal_compact 1
  nonempty' := ⟨0, ⟨by norm_num, rfl⟩⟩

theorem verticalUnit_support (l : Space →L[ℝ] ℝ) :
    SupportGeometry.support (verticalUnit : Set Space) l = max 0 (l (1, 0)) := by
  first
  | have h0 : (0 : Space) ∈ verticalUnit := ⟨by norm_num, rfl⟩
    have h1 : ((1, 0) : Space) ∈ verticalUnit := ⟨by norm_num, rfl⟩
    apply le_antisymm
    · apply SupportGeometry.support_le verticalUnit.nonempty l
      rintro p ⟨hp, hp0⟩
      have hp' : p = p.1 • ((1, 0) : Space) := by
        first
        | apply Prod.ext
          · simp
          · simpa using hp0
      rw [hp', map_smul, smul_eq_mul]
      rcases le_total 0 (l (1, 0)) with hl | hl
      · rw [max_eq_right hl]
        nlinarith [hp.2]
      · rw [max_eq_left hl]
        exact mul_nonpos_of_nonneg_of_nonpos hp.1 hl
    · apply max_le
      · simpa using SupportGeometry.le_support verticalUnit.isCompact l h0
      · exact SupportGeometry.le_support verticalUnit.isCompact l h1

theorem smul_verticalUnit {t : ℝ} (ht : 0 ≤ t) :
    ((t • verticalUnit : ConvexBody Space) : Set Space) = horizontal t := by
  first
  | by_cases ht0 : t = 0
    · subst t
      ext p
      simp [verticalUnit, horizontal, Set.mem_prod, Prod.ext_iff]
    have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    ext p
    constructor
    · rintro ⟨q, ⟨hq, hq0⟩, rfl⟩
      exact ⟨⟨mul_nonneg ht hq.1, by simpa using mul_le_mul_of_nonneg_left hq.2 ht⟩,
        by
          change t • q.2 = (0 : Plane)
          rw [show q.2 = (0 : Plane) from hq0, smul_zero]⟩
    · rintro ⟨hp, hp0⟩
      refine ⟨(p.1 / t, 0), ⟨⟨div_nonneg hp.1 ht, (div_le_one htp).mpr hp.2⟩, rfl⟩, ?_⟩
      apply Prod.ext
      · change t * (p.1 / t) = p.1
        field_simp [ht0]
      · simpa using hp0.symm

theorem mixed3_verticalUnit (S : ConvexBody Space) :
    3 * mixed3 verticalUnit S S = volume.real (PlanarExtrusion.projection (S : Set Space)) := by
  first
  | have hp := mixed3_hasDerivWithinAt_volume verticalUnit S
    have he (t : ℝ) (ht : 0 ≤ t) : volume.real ((S + t • verticalUnit : ConvexBody Space) : Set Space) =
        volume.real (S : Set Space) + t * volume.real (PlanarExtrusion.projection (S : Set Space)) := by
      first
      | change volume.real ((S : Set Space) + ((t • verticalUnit : ConvexBody Space) : Set Space)) = _
        rw [smul_verticalUnit ht]
        exact realVolume_add_horizontal S.isCompact S.convex ht
    have hd : HasDerivWithinAt (fun t : ℝ => volume.real ((S + t • verticalUnit : ConvexBody Space) : Set Space))
        (volume.real (PlanarExtrusion.projection (S : Set Space))) (Ioi 0) 0 := by
      first
      | have h := ((hasDerivAt_id (0 : ℝ)).mul_const
          (volume.real (PlanarExtrusion.projection (S : Set Space)))).const_add
          (volume.real (S : Set Space))
        simpa only [one_mul] using h.hasDerivWithinAt.congr
          (fun (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) => he t ht.le) (he 0 le_rfl)
    exact tendsto_nhds_unique
      ((hasDerivWithinAt_iff_tendsto_slope' (self_notMem_Ioi : (0 : ℝ) ∉ Ioi 0)).mp hp)
      ((hasDerivWithinAt_iff_tendsto_slope' (self_notMem_Ioi : (0 : ℝ) ∉ Ioi 0)).mp hd)

theorem trianglePlaneSum_projection (a b c d : ℝ) :
    PlanarExtrusion.projection (trianglePlaneSum a b c d : Set Space) =
      Icc (min 0 c) (max 0 c) ×ˢ Icc (min 0 a) (max 0 a) := by
  first
  | ext p
    constructor
    · rintro ⟨q, ⟨u, ⟨u', hu, rfl⟩, v, ⟨v', hv, rfl⟩, he⟩, hqp⟩
      have hx : v'.1 = p.1 := by
        first
        | have hh := congrArg (fun z : Space => z.2.1) he
          have hp := congrArg Prod.fst hqp
          simpa [embedYZ, embedXZ, ← hp] using hh
      have hy : u'.1 = p.2 := by
        first
        | have hh := congrArg (fun z : Space => z.2.2) he
          have hp := congrArg Prod.snd hqp
          simpa [embedYZ, embedXZ, ← hp] using hh
      exact ⟨hx ▸ (rightTriangle_bounds c d hv).1, hy ▸ (rightTriangle_bounds a b hu).1⟩
    · intro hp
      refine ⟨(0, p), ?_, rfl⟩
      refine ⟨embedYZ (p.2, 0), ⟨(p.2, 0), rightTriangle_axisX hp.2, rfl⟩,
        embedXZ (p.1, 0), ⟨(p.1, 0), rightTriangle_axisX hp.1, rfl⟩, ?_⟩
      ext <;> simp [embedYZ, embedXZ]

theorem trianglePlaneSum_projection_area (a b c d : ℝ) :
    volume.real (PlanarExtrusion.projection (trianglePlaneSum a b c d : Set Space)) = |a| * |c| := by
  first
  | rw [trianglePlaneSum_projection, Measure.volume_eq_prod, measureReal_prod_prod,
      Real.volume_real_Icc_of_le min_le_max, Real.volume_real_Icc_of_le min_le_max,
      max_sub_min_eq_abs, max_sub_min_eq_abs]
    ring

def prismRightInverse (a b c d : ℝ) : Fin 6 → Space :=
  ![(0, (-c / 3, 0)), (0, (2 * c / 3, 0)),
    (0, (0, -a / 3)), (0, (0, 2 * a / 3)),
    (prismHalfHeight b d, 0), (-prismHalfHeight b d, 0)]

theorem prism_normal_unit {a b c d : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (i : Fin 6) :
    prismNormals a b c d i (prismRightInverse a b c d i) = 1 := by
  first
  | have hH := prismHalfHeight_positive (d := d) hb
    fin_cases i <;>
      simp [prismNormals, prismRightInverse, upperPrismNormal, lowerPrismNormal,
        zCoord, xCoord, yCoord, ha, hc, hH.ne'] <;> field_simp [ha, hc, hH.ne'] <;> ring

theorem prismNormals_injective {a b c d : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) : Function.Injective (prismNormals a b c d) := by
  first
  | intro i j hij
    have hH := prismHalfHeight_positive (d := d) hb
    have hz := congrArg (fun l : Space →L[ℝ] ℝ => l (1, 0)) hij
    have hx := congrArg (fun l : Space →L[ℝ] ℝ => l (0, (1, 0))) hij
    have hy := congrArg (fun l : Space →L[ℝ] ℝ => l (0, (0, 1))) hij
    fin_cases i <;> fin_cases j
    all_goals first
    | rfl
    | exfalso
      simp [prismNormals, upperPrismNormal, lowerPrismNormal, zCoord, xCoord, yCoord] at hz hx hy
      all_goals
        try field_simp [ha, hc, hH.ne'] at hz
        try field_simp [ha, hc, hH.ne'] at hx
        try field_simp [ha, hc, hH.ne'] at hy
        nlinarith

def prismWeight (a b c d : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (i : Fin 6) : ℝ :=
  canonicalFacetWeight (prismNormals a b c d) i (prismRightInverse a b c d i)
    (prism_normal_unit ha hb hc i)

theorem prism_first_variation {a b c d : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (A : ConvexBody Space) :
    3 * mixed3 A (trianglePlaneSum a b c d) (trianglePlaneSum a b c d) =
      ∑ i, prismWeight a b c d ha hb hc i *
        SupportGeometry.support (A : Set Space) (prismNormals a b c d i) := by
  first
  | let S := translateBody (-prismCenter a b c d) (trianglePlaneSum a b c d)
    have hbody := prism_halfspace_body ha hb hc hd
    have hcompact : IsCompact (HalfspacePyramids.body (prismNormals a b c d)) := by
      first
      | rw [hbody]
        exact S.isCompact
    have hf := PolytopeFirstVariation.first_variation (prismNormals a b c d)
      (prismNormals_injective ha hb hc) hcompact (prismRightInverse a b c d)
      (prism_normal_unit ha hb hc) A.isCompact A.convex A.nonempty
    have hp := mixed3_hasDerivWithinAt_volume A S
    rw [hbody] at hf
    have he := tendsto_nhds_unique
      ((hasDerivWithinAt_iff_tendsto_slope' (self_notMem_Ioi : (0 : ℝ) ∉ Ioi 0)).mp hp)
      ((hasDerivWithinAt_iff_tendsto_slope' (self_notMem_Ioi : (0 : ℝ) ∉ Ioi 0)).mp hf)
    have ht := mixed3_translate A (trianglePlaneSum a b c d) (trianglePlaneSum a b c d)
      0 (-prismCenter a b c d) (-prismCenter a b c d)
    simp only [translateBody_zero] at ht
    change 3 * mixed3 A S S = _ at he
    rw [ht] at he
    exact he

theorem prism_roof_weights {a b c d : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    prismWeight a b c d ha hb hc 4 / prismHalfHeight b d = |a| * |c| ∧
      prismWeight a b c d ha hb hc 5 / prismHalfHeight b d = |a| * |c| := by
  first
  | have hH := prismHalfHeight_positive (d := d) hb
    have hsegment := prism_first_variation ha hb hc hd verticalUnit
    rw [mixed3_verticalUnit, trianglePlaneSum_projection_area] at hsegment
    have hpoint := prism_first_variation ha hb hc hd (pointBody (1, 0))
    rw [mixed3_point_first, mul_zero] at hpoint
    have hs (l : Space →L[ℝ] ℝ) : SupportGeometry.support (pointBody ((1, 0) : Space) : Set Space) l = l (1, 0) := by
      first
      | simp [SupportGeometry.support, coe_pointBody]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, verticalUnit_support, hs,
      prismNormals, Matrix.cons_val_zero, Matrix.cons_val_succ, upperPrismNormal,
      lowerPrismNormal, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply, smul_eq_mul,
      zCoord, xCoord, yCoord, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', Prod.fst_zero, Prod.snd_zero,
      mul_zero, mul_one, zero_mul, add_zero, sub_zero,
      neg_zero, zero_sub, zero_add, mul_neg_one, one_mul, max_self, max_eq_right (inv_nonneg.mpr hH.le),
      max_eq_left (neg_nonpos.mpr (inv_nonneg.mpr hH.le))] at hsegment hpoint
    change |a| * |c| = prismWeight a b c d ha hb hc 4 * (prismHalfHeight b d)⁻¹ at hsegment
    change (0 : ℝ) = prismWeight a b c d ha hb hc 4 * (prismHalfHeight b d)⁻¹ +
      prismWeight a b c d ha hb hc 5 * -(prismHalfHeight b d)⁻¹ at hpoint
    constructor <;> simp only [div_eq_mul_inv] <;> linarith

end VolumePolynomials.PlanarInteraction
