module

public import Projection.Basic

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory Module MvPolynomial
open scoped BigOperators Pointwise

namespace RankThreeProjection

open VolumePolynomials

section Segment
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual segment, including its degenerate case. -/
def segmentBody (a b : E) : ConvexBody E where
  carrier := segment ℝ a b
  convex' := convex_segment a b
  isCompact' := by
    rw [segment_eq_image]
    exact isCompact_Icc.image (by fun_prop)
  nonempty' := ⟨a, left_mem_segment ℝ a b⟩

/-- An origin-based segment; translation invariance relates it to the
centered segment used in the paper. -/
def originSegment (v : E) : ConvexBody E := segmentBody 0 v

def centeredSegment (v : E) : ConvexBody E :=
  segmentBody (-(1 / 2 : ℝ) • v) ((1 / 2 : ℝ) • v)

theorem map_segmentBody {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (a b : E) :
    mapBody L (segmentBody a b) = segmentBody (L a) (L b) := by
  apply ConvexBody.ext
  exact image_segment ℝ L.toLinearMap.toAffineMap a b

theorem map_centeredSegment {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (v : E) :
    mapBody L (centeredSegment v) = centeredSegment (L v) := by
  simp only [centeredSegment, map_segmentBody, map_smul]

theorem translate_segmentBody (v a b : E) :
    translateBody v (segmentBody a b) = segmentBody (v + a) (v + b) := by
  apply ConvexBody.ext
  rw [coe_translateBody]
  change v +ᵥ segment ℝ a b = segment ℝ (v + a) (v + b)
  simp only [vadd_segment, vadd_eq_add]

theorem centered_eq_translate_origin (v : E) :
    centeredSegment v = translateBody (-(1 / 2 : ℝ) • v) (originSegment v) := by
  rw [centeredSegment, originSegment, translate_segmentBody]
  congr 1
  · simp
  · calc
      (1 / 2 : ℝ) • v = (-(1 / 2 : ℝ) + 1) • v := by congr 1; norm_num
      _ = (-(1 / 2 : ℝ)) • v + v := by rw [add_smul, one_smul]

end Segment

section Product
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def axisBody : ConvexBody (ℝ × E) where
  carrier := PlanarExtrusion.horizontal 1
  convex' := (convex_Icc 0 1).prod (convex_singleton 0)
  isCompact' := PlanarExtrusion.horizontal_compact 1
  nonempty' := ⟨(0, 0), ⟨⟨le_rfl, zero_le_one⟩, rfl⟩⟩

theorem smul_axisBody_coe {r : ℝ} (hr : 0 ≤ r) :
    ((r • axisBody (E := E) : ConvexBody (ℝ × E)) : Set (ℝ × E)) =
      PlanarExtrusion.horizontal r := by
  rcases hr.eq_or_lt with hr | hr
  · subst r
    simp [body_zero_smul, axisBody, PlanarExtrusion.horizontal,
      Set.prod_singleton]
    exact (Set.singleton_zero : ({(0 : ℝ × E)} : Set (ℝ × E)) = 0).symm
  · ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases hq with ⟨hq, hq0⟩
      change q.2 = 0 at hq0
      change (0 ≤ r * q.1 ∧ r * q.1 ≤ r) ∧ r • q.2 = 0
      exact ⟨⟨mul_nonneg hr.le hq.1,
        (mul_le_mul_of_nonneg_left hq.2 hr.le).trans_eq (mul_one r)⟩,
        by rw [hq0, smul_zero]⟩
    · intro hp
      rcases hp with ⟨hp, hp0⟩
      change p.2 = 0 at hp0
      refine ⟨(p.1 / r, 0), ?_, ?_⟩
      · exact ⟨⟨div_nonneg hp.1 hr.le, (div_le_one hr).mpr hp.2⟩, rfl⟩
      · apply Prod.ext
        · change r * (p.1 / r) = p.1
          field_simp [hr.ne']
        · simpa using hp0.symm

variable [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

/-- Exact polynomial form of interval-fiber extrusion in every dimension. -/
theorem volumePolynomial_axis {d : ℕ} (K : Fin d → ConvexBody (ℝ × E)) :
    volumePolynomial volume (Fin.cons axisBody K) =
      MvPolynomial.rename Fin.succ (volumePolynomial volume K) +
      X 0 * MvPolynomial.rename Fin.succ
        (volumePolynomial volume (fun i => mapBody (ContinuousLinearMap.snd ℝ ℝ E) (K i))) := by
  apply volumePolynomial_eq_of_eval
  intro t ht
  simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_X,
    MvPolynomial.eval_rename]
  rw [volumePolynomial_eval volume K (t ∘ Fin.succ) (fun i => ht i.succ),
    volumePolynomial_eval volume _ (t ∘ Fin.succ) (fun i => ht i.succ)]
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Function.comp_apply]
  let C : ConvexBody (ℝ × E) := ∑ i, t i.succ • K i
  have hmap : (∑ i, t i.succ • mapBody (ContinuousLinearMap.snd ℝ ℝ E) (K i)) =
      mapBody (ContinuousLinearMap.snd ℝ ℝ E) C := by
    simp only [C, ← mapBody_smul]
    exact (map_sum (mapBodyHom (ContinuousLinearMap.snd ℝ ℝ E)) _ _).symm
  rw [hmap]
  change volume.real (C : Set (ℝ × E)) + t 0 *
    volume.real (PlanarExtrusion.projection (C : Set (ℝ × E))) =
    volume.real ((t 0 • axisBody (E := E) + C : ConvexBody (ℝ × E)) : Set (ℝ × E))
  rw [add_comm (t 0 • axisBody (E := E)) C, ConvexBody.coe_add,
    smul_axisBody_coe (E := E) (ht 0)]
  exact (PlanarExtrusion.realVolume_add_horizontal C.isCompact C.convex (ht 0)).symm

theorem squarefree_succ (d : ℕ) :
    squarefreeExponent (d + 1) = Finsupp.single 0 1 +
      (squarefreeExponent d).mapDomain Fin.succ := by
  rw [← oldSquarefreeLift_eq_mapDomain]
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem coeff_rename_succ_squarefree {d : ℕ} (p : MvPolynomial (Fin d) ℝ) :
    (MvPolynomial.rename Fin.succ p).coeff (squarefreeExponent (d + 1)) = 0 := by
  apply MvPolynomial.coeff_rename_eq_zero
  intro u hu
  have hzero : (u.mapDomain Fin.succ) (0 : Fin (d + 1)) = 0 := by
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨i, hi⟩
    exact Fin.succ_ne_zero i hi
  rw [hu, squarefreeExponent_apply] at hzero
  exact (Nat.one_ne_zero hzero).elim

/-- Deleting one coordinate by one actual segment has exactly the factorial
normalization of standard mixed volume. No dimension restriction is assumed
on the individual bodies. -/
theorem mixedVolume_axis {d : ℕ} (K : Fin d → ConvexBody (ℝ × E)) :
    (d + 1 : ℝ) * mixedVolume volume (Fin.cons axisBody K) =
      mixedVolume volume (fun i => mapBody (ContinuousLinearMap.snd ℝ ℝ E) (K i)) := by
  unfold mixedVolume
  rw [volumePolynomial_axis, MvPolynomial.coeff_add,
    coeff_rename_succ_squarefree, zero_add, squarefree_succ,
    MvPolynomial.coeff_X_mul, MvPolynomial.coeff_rename_mapDomain _ (Fin.succ_injective d)]
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hd : (d.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  have hn : (d : ℝ) + 1 ≠ 0 := by positivity
  field_simp

end Product
end RankThreeProjection
