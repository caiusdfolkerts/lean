module

public import VolumePolynomials.PlanarLinearMixedArea

@[expose] public section
set_option autoImplicit false

/-! # Directional widths as sums of actual support values -/

noncomputable section
open Set MeasureTheory
open scoped Pointwise

namespace VolumePolynomials.PlanarEdges

open PlanarExtrusion PlanarMixedForm PlanarCorner OAI.Paper092

theorem image_length_eq_support (P : ConvexBody Plane) (l : Plane →L[ℝ] ℝ) :
    volume.real (l '' (P : Set Plane)) =
      SupportGeometry.support (P : Set Plane) l +
        SupportGeometry.support (P : Set Plane) (-l) := by
  first
  | let S := l '' (P : Set Plane)
    have hc : IsCompact S := P.isCompact.image l.continuous
    have hv : Convex ℝ S := P.convex.linear_image l.toLinearMap
    have hn : S.Nonempty := P.nonempty.image l
    have hI : S = Icc (sInf S) (sSup S) :=
      eq_Icc_of_connected_compact ⟨hn, Real.convex_iff_isPreconnected.mp hv⟩ hc
    have hle : sInf S ≤ sSup S := csInf_le_csSup hn hc.bddBelow hc.bddAbove
    have hneg : (-l) '' (P : Set Plane) = -S := by
      ext z
      change (∃ x, x ∈ P ∧ (-l) x = z) ↔ -z ∈ S
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, by simp⟩
      · rintro ⟨x, hx, he⟩
        refine ⟨x, hx, ?_⟩
        change -l x = z
        linarith
    change volume.real S = sSup S + sSup ((-l) '' (P : Set Plane))
    rw [hneg, Real.sSup_neg]
    calc
      volume.real S = volume.real (Icc (sInf S) (sSup S)) := congrArg volume.real hI
      _ = sSup S - sInf S := Real.volume_real_Icc_of_le hle
      _ = sSup S + -sInf S := sub_eq_add_neg _ _

@[simp] theorem normal_neg (e : Plane) : normal (-e) = -normal e := by
  first
  | apply ContinuousLinearMap.ext
    intro x
    simp only [normal_apply, Prod.fst_neg, Prod.snd_neg, ContinuousLinearMap.neg_apply]
    ring

@[simp] theorem normal_zero : normal (0 : Plane) = 0 := by
  first
  | apply ContinuousLinearMap.ext
    intro x
    simp only [normal_apply, Prod.fst_zero, Prod.snd_zero, zero_mul, sub_self,
      ContinuousLinearMap.zero_apply]

@[simp] theorem normal_pair_zero : normal ((0, 0) : Plane) = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [normal_apply, zero_mul, sub_self, ContinuousLinearMap.zero_apply]

@[simp] theorem support_zero (P : ConvexBody Plane) :
    SupportGeometry.support (P : Set Plane) (0 : Plane →L[ℝ] ℝ) = 0 := by
  first
  | apply le_antisymm
    · exact SupportGeometry.support_le P.nonempty 0 (fun _ _ => le_rfl)
    · obtain ⟨p, hp⟩ := P.nonempty
      exact SupportGeometry.le_support P.isCompact 0 hp

theorem twice_mixedArea_segment_support (P : ConvexBody Plane) (e : Plane) :
    2 * mixedArea volume P (PlanarCorner.segmentBody e) =
      SupportGeometry.support (P : Set Plane) (normal e) +
        SupportGeometry.support (P : Set Plane) (normal (-e)) := by
  first
  | rw [twice_mixedArea_segment]
    have he : (determinantMap e).toContinuousLinearMap = normal (-e) := by
      apply ContinuousLinearMap.ext
      intro x
      change determinantMap e x = normal (-e) x
      simp only [determinantMap_apply, normal_apply, Prod.fst_neg, Prod.snd_neg, determinant]
      ring
    change volume.real ((determinantMap e).toContinuousLinearMap '' (P : Set Plane)) = _
    rw [he, image_length_eq_support, normal_neg, neg_neg]
    exact add_comm _ _

theorem support_axisX_sum (P : ConvexBody Plane) :
    SupportGeometry.support (P : Set Plane) (normal (0, 1)) +
      SupportGeometry.support (P : Set Plane) (normal (0, -1)) = width P := by
  first
  | have h := twice_mixedArea_segment_support P (0, 1)
    rw [show PlanarCorner.segmentBody (0, 1) = unitY from rfl, twice_mixedArea_unitY] at h
    simpa only [Prod.neg_mk, neg_zero] using h.symm

theorem support_axisY_sum (P : ConvexBody Plane) :
    SupportGeometry.support (P : Set Plane) (normal (1, 0)) +
      SupportGeometry.support (P : Set Plane) (normal (-1, 0)) = height P := by
  first
  | have h := twice_mixedArea_segment_support P (1, 0)
    rw [show PlanarCorner.segmentBody (1, 0) = unitX from rfl, twice_mixedArea_unitX] at h
    simpa only [Prod.neg_mk, neg_zero] using h.symm

theorem originSegment_eq_translate_centered (v : Plane) :
    originSegment v = ({(1 / 2 : ℝ) • v} : Set Plane) + centeredSegment v := by
  first
  | ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨(1 / 2 : ℝ) • v, rfl, (t - 1 / 2) • v,
        ⟨t - 1 / 2, ⟨by linarith [ht.1], by linarith [ht.2]⟩, rfl⟩, ?_⟩
      change (1 / 2 : ℝ) • v + (t - 1 / 2) • v = t • v
      rw [← add_smul]
      congr 1
      ring
    · rintro ⟨u, hu, y, ⟨t, ht, rfl⟩, rfl⟩
      change u = (1 / 2 : ℝ) • v at hu
      subst u
      refine ⟨t + 1 / 2, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
      change (t + 1 / 2) • v = (1 / 2 : ℝ) • v + t • v
      rw [← add_smul]
      congr 1
      ring

theorem rightTriangle_zero_right (a : ℝ) :
    rightTriangle a 0 = translateBody ((1 / 2 : ℝ) • (a, 0)) (PlanarCorner.segmentBody (a, 0)) := by
  first
  | apply ConvexBody.ext
    have he : (rightTriangle a 0 : Set Plane) = originSegment (a, 0) := by
      change (diagonalLinear a 0) '' (unitTriangle : Set Plane) = _
      have hf : (diagonalLinear a 0 : Plane → Plane) =
          (fun t : ℝ => t • ((a, 0) : Plane)) ∘ Prod.fst := by
        funext x
        ext <;> simp [diagonalLinear_apply, mul_comm]
      rw [hf, Set.image_comp, unitTriangle_projections.1]
      rfl
    rw [he, originSegment_eq_translate_centered]
    rfl

theorem rightTriangle_zero_left (b : ℝ) :
    rightTriangle 0 b = translateBody ((1 / 2 : ℝ) • (0, b)) (PlanarCorner.segmentBody (0, b)) := by
  first
  | apply ConvexBody.ext
    have he : (rightTriangle 0 b : Set Plane) = originSegment (0, b) := by
      change (diagonalLinear 0 b) '' (unitTriangle : Set Plane) = _
      have hf : (diagonalLinear 0 b : Plane → Plane) =
          (fun t : ℝ => t • ((0, b) : Plane)) ∘ Prod.snd := by
        funext x
        ext <;> simp [diagonalLinear_apply, mul_comm]
      rw [hf, Set.image_comp, unitTriangle_projections.2]
      rfl
    rw [he, originSegment_eq_translate_centered]
    rfl

end VolumePolynomials.PlanarEdges
