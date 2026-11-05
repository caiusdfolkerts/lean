module

public import VolumePolynomials.LowerInteractionWitness
public import VolumePolynomials.ThresholdScalar

@[expose] public section
set_option autoImplicit false

/-! # The geometric estimates in Theorem 5.5

The upper estimate allows the averaged body in the higher-dimensional lift:
its area may exceed `2*s*T`. The lower estimate constructs actual planar
bodies and the exact attaining optimizer. All mixed areas and mixed volumes
are the coefficient functionals of their actual Lebesgue volume polynomials.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology Pointwise

namespace VolumePolynomials.PlanarInteraction

open PlanarExtrusion PlanarMixedForm PlanarCorner PlanarEdges OAI.Paper092

theorem IsInteraction.area_ge_inputs {B C Q : ConvexBody Plane}
    (hQ : IsInteraction B C Q)
    (hBw : width B = 1) (hBh : height B = 1) (hCw : width C = 1) (hCh : height C = 1) :
    max (volume.real (B : Set Plane)) (volume.real (C : Set Plane)) ≤ volume.real (Q : Set Plane) := by
  first
  | obtain ⟨R, hR, hRa⟩ := proposition_4_3 B C hBw hBh hCw hCh
    rwa [interaction_area_unique hR hQ] at hRa

theorem geometric_slice_lower_bound {A Q : ConvexBody Plane} {s T z : ℝ}
    (hs : 0 < s) (hT : 0 < T)
    (hAw : width A = 1) (hAh : height A = s)
    (hAa : 2 * s * T ≤ volume.real (A : Set Plane))
    (hQw : width Q = 1) (hQh : height Q = 1)
    (hz : 2 * T * z = 2 * mixedArea volume A Q) :
    T ≤ 1 / 2 ∧
      sliceLowerBound s (1 / 2 - T) (1 / 2 - volume.real (Q : Set Plane)) ≤ z := by
  first
  | have hAupper := area_le_width_mul_height A
    rw [hAw, hAh, one_mul] at hAupper
    have hThalf : T ≤ 1 / 2 := by nlinarith
    have hQupper := area_le_width_mul_height Q
    rw [hQw, hQh, one_mul] at hQupper
    have hcorner := mixedArea_corner_inequality A Q
    rw [hAw, hAh, hQw, hQh, one_mul, mul_one] at hcorner
    simp only [one_mul, mul_one] at hcorner
    have hproduct : (s - volume.real (A : Set Plane)) * (1 - volume.real (Q : Set Plane)) ≤
        (s - 2 * s * T) * (1 - volume.real (Q : Set Plane)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have hroot := Real.sqrt_le_sqrt hproduct
    have hsqrt : Real.sqrt (4 * s * (1 / 2 - T) *
        (1 + 2 * (1 / 2 - volume.real (Q : Set Plane)))) =
        2 * Real.sqrt ((s - 2 * s * T) * (1 - volume.real (Q : Set Plane))) := by
      first
      | rw [show 4 * s * (1 / 2 - T) * (1 + 2 * (1 / 2 - volume.real (Q : Set Plane))) =
          4 * ((s - 2 * s * T) * (1 - volume.real (Q : Set Plane))) by ring,
          Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
        rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    refine ⟨hThalf, ?_⟩
    unfold sliceLowerBound
    rw [hsqrt]
    apply (div_le_iff₀ (show 0 < 1 - 2 * (1 / 2 - T) by linarith)).mpr
    nlinarith

theorem deficit_log_square_le {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s)
    (hδs : δ ≤ s) (hsExp : s ≤ Real.exp (-1)) :
    δ ^ 2 * Real.log (1 / δ) ≤ 2 * s ^ 2 * Real.log (1 / s) := by
  first
  | have hlogS : 1 ≤ Real.log (1 / s) := by
      first
      | have h := Real.log_le_log hs hsExp
        rw [Real.log_exp, Real.log_div one_ne_zero hs.ne', Real.log_one] at *
        linarith
    have hsplit : Real.log (1 / δ) = Real.log (1 / s) + Real.log (s / δ) := by
      first
      | rw [Real.log_div one_ne_zero hδ.ne', Real.log_div one_ne_zero hs.ne',
          Real.log_div hs.ne' hδ.ne', Real.log_one]
        ring
    have hratio : Real.log (s / δ) ≤ s / δ :=
      (Real.log_le_sub_one_of_pos (div_pos hs hδ)).trans (by linarith)
    have hratioMul := mul_le_mul_of_nonneg_left hratio (sq_nonneg δ)
    have hcancel : δ ^ 2 * (s / δ) = s * δ := by field_simp [hδ.ne']
    rw [hcancel] at hratioMul
    have hsquare : δ ^ 2 ≤ s ^ 2 := by nlinarith
    have hfirst := mul_le_mul_of_nonneg_right hsquare (by linarith : 0 ≤ Real.log (1 / s))
    have hsecond : s * δ ≤ s ^ 2 * Real.log (1 / s) := by
      first
      | have hds := mul_le_mul_of_nonneg_left hδs hs.le
        have hlog := mul_le_mul_of_nonneg_left hlogS (sq_nonneg s)
        nlinarith
    rw [hsplit, mul_add]
    linarith

/-- The universal upper gap, in the form that also applies to Proposition 6.2.
No equality assumption is imposed on the area of the averaged first body. -/
theorem geometric_threshold_upper {A B C Q : ConvexBody Plane} {s T z : ℝ}
    (hs : 0 < s) (hsmall : s < min (1 / 128) (Real.exp (-1))) (hT : 0 < T)
    (hAw : width A = 1) (hAh : height A = s)
    (hAa : 2 * s * T ≤ volume.real (A : Set Plane))
    (hBw : width B = 1) (hBh : height B = 1) (hCw : width C = 1) (hCh : height C = 1)
    (hBa : volume.real (B : Set Plane) = T) (hCa : volume.real (C : Set Plane) = T)
    (hQ : IsInteraction B C Q) (hz : 2 * T * z = 2 * mixedArea volume A Q) :
    comparisonRoot s - z ≤ 34816 * s ^ 3 * Real.log (1 / s) := by
  first
  | have hs128 : s < 1 / 128 := hsmall.trans_le (min_le_left _ _)
    have hsExp : s ≤ Real.exp (-1) := (hsmall.trans_le (min_le_right _ _)).le
    have hlog : 0 ≤ Real.log (1 / s) := by
      first
      | apply Real.log_nonneg
        apply (one_le_div hs).mpr
        linarith
    by_cases hzr : comparisonRoot s ≤ z
    · have hnonneg : 0 ≤ 34816 * s ^ 3 * Real.log (1 / s) := by positivity
      linarith
    have hzlt : z < comparisonRoot s := lt_of_not_ge hzr
    obtain ⟨hThalf, hf⟩ := geometric_slice_lower_bound hs hT hAw hAh hAa hQ.1 hQ.2.1 hz
    let δ : ℝ := 1 / 2 - T
    let η : ℝ := 1 / 2 - volume.real (Q : Set Plane)
    have hδ : 0 ≤ δ := by dsimp [δ]; linarith
    have hδhalf : δ < 1 / 2 := by dsimp [δ]; linarith
    have hηδ : η ≤ δ := by
      first
      | have h := hQ.area_ge_inputs hBw hBh hCw hCh
        rw [hBa, hCa, max_self] at h
        dsimp [η, δ]
        linarith
    have himprove : sliceLowerBound s δ η < comparisonRoot s := hf.trans_lt hzlt
    obtain ⟨hδpos, hηpos, _, hδbound⟩ := improving_deficit_localization hs
      (by linarith) hδ hδhalf hηδ himprove
    have hδsmall : 2 * δ < min (1 / 64) (Real.exp (-1)) := by
      first
      | apply lt_min
        · linarith
        · have hsexp := hsmall.trans_le (min_le_right _ _)
          linarith
    have henergy : η ≤ 4352 * δ ^ 2 * Real.log (1 / δ) := by
      first
      | have h := corollary_5_3 hBw hBh hCw hCh hQ hδpos hδsmall
          (show volume.real (B : Set Plane) = 1 / 2 - δ by rw [hBa]; dsimp [δ]; ring)
          (show volume.real (C : Set Plane) = 1 / 2 - δ by rw [hCa]; dsimp [δ]; ring)
        exact h
    have hlogCompare := deficit_log_square_le hδpos hs (by linarith) hsExp
    have hηbound : η ≤ 8704 * s ^ 2 * Real.log (1 / s) := by nlinarith
    have hscalar := improvement_le_four_mul hs (by linarith) hδ hδhalf hηδ himprove
    have hmult := mul_le_mul_of_nonneg_left hηbound (show 0 ≤ 4 * s by positivity)
    nlinarith

theorem reference_optimizer_fits {s η : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (hη : 0 ≤ η) :
    Real.sqrt ((s - 2 * s * (1 / 2 - comparisonDeficit s)) /
      (1 - (1 / 2 - η))) ≤ min 1 s := by
  first
  | have hr := comparisonRoot_ge_one hs.le
    have hrpos := comparisonRoot_pos hs.le
    have hden : 0 < 1 - (1 / 2 - η) := by linarith
    have hratio : (s - 2 * s * (1 / 2 - comparisonDeficit s)) /
        (1 - (1 / 2 - η)) = s ^ 2 / (comparisonRoot s ^ 2 * (1 + 2 * η)) := by
      first
      | dsimp [comparisonDeficit]
        rw [show 1 - (1 / 2 - η) = (1 + 2 * η) / 2 by ring]
        have hp : 1 + 2 * η ≠ 0 := ne_of_gt (by linarith)
        field_simp [hrpos.ne', hp] <;> ring
    have hden' : 0 < comparisonRoot s ^ 2 * (1 + 2 * η) := by positivity
    have hden1 : 1 ≤ comparisonRoot s ^ 2 * (1 + 2 * η) := by
      first
      | have hr2 : 1 ≤ comparisonRoot s ^ 2 := by nlinarith
        have hp := mul_le_mul hr2 (show 1 ≤ 1 + 2 * η by linarith) (by norm_num) (by positivity)
        simpa only [one_mul] using hp
    have hsq : s ^ 2 / (comparisonRoot s ^ 2 * (1 + 2 * η)) ≤ s ^ 2 := by
      first
      | apply (div_le_iff₀ hden').mpr
        have h := mul_le_mul_of_nonneg_left hden1 (sq_nonneg s)
        simpa only [mul_one] using h
    rw [hratio]
    have hroot : Real.sqrt (s ^ 2 / (comparisonRoot s ^ 2 * (1 + 2 * η))) ≤ s :=
      (Real.sqrt_le_left hs.le).mpr hsq
    exact le_min (hroot.trans hs1) hroot

/-- The actual normalized lower witness for Theorem 5.5. The coefficient
normalization is supplied separately by Proposition 3.1 or its lifted converse. -/
theorem geometric_threshold_lower_polygons {s : ℝ} (hs : 0 < s) (hsSmall : s ≤ 1 / 2) :
    ∃ A B C : ConvexBody Plane, ∃ T z : ℝ, 0 < T ∧
      width A = 1 ∧ height A = s ∧ volume.real (A : Set Plane) = 2 * s * T ∧
      width B = 1 ∧ height B = 1 ∧ width C = 1 ∧ height C = 1 ∧
      volume.real (B : Set Plane) = T ∧ volume.real (C : Set Plane) = T ∧
      6 * triple A B C = 2 * T * z ∧
      (3 / 51200) * s ^ 3 * Real.log (1 / s) ≤ comparisonRoot s - z ∧
      PolytopeGeometry.IsFiniteHull (A : Set Plane) ∧
      PolytopeGeometry.IsFiniteHull (B : Set Plane) ∧
      PolytopeGeometry.IsFiniteHull (C : Set Plane) := by
  first
  | let δ := comparisonDeficit s
    have hδpos : 0 < δ := comparisonDeficit_pos hs
    have hδupper : δ ≤ s / 4 := comparisonDeficit_le_quarter hs.le
    have hδlower : s / 16 ≤ δ := comparisonDeficit_ge_sixteenth hs.le (by linarith)
    obtain ⟨B, Q, hBpoly, hQpoly, hBw, hBh, hBa, hQ, hQa, hgap⟩ := logarithmic_lower_polygon_interaction_witness
      hδpos (by linarith)
    let T := 1 / 2 - δ
    let η := 1 / 2 - volume.real (Q : Set Plane)
    have hT : 0 < T := by dsimp [T]; linarith
    have hηδ : η ≤ δ := by dsimp [η]; linarith
    have hlogδ : 0 < Real.log (1 / δ) := by
      first
      | apply Real.log_pos
        apply (one_lt_div hδpos).mpr
        linarith
    have hηpos : 0 < η := by
      first
      | have hterm : 0 < (3 / 50 : ℝ) * δ ^ 2 * Real.log (1 / δ) := by positivity
        exact hterm.trans_le hgap
    have hq1 : volume.real (Q : Set Plane) < 1 := by dsimp [η] at hηpos; linarith
    have hfit := reference_optimizer_fits hs (by linarith : s ≤ 1) hηpos.le
    obtain ⟨A, hAw, hAh, hAa, hAQ, hApoly⟩ := optimizer_attains_finiteHull Q hQpoly hQ.1 hQ.2.1 hq1
      (show 2 * s * T ≤ s by dsimp [T]; nlinarith)
      (by simpa only [T, δ, η, sub_sub_cancel] using hfit)
    let z := sliceLowerBound s δ η
    have hsqrt : Real.sqrt (4 * s * δ * (1 + 2 * η)) =
        2 * Real.sqrt ((s - 2 * s * T) * (1 - volume.real (Q : Set Plane))) := by
      first
      | rw [show 4 * s * δ * (1 + 2 * η) =
          4 * ((s - 2 * s * T) * (1 - volume.real (Q : Set Plane))) by dsimp [η, T]; ring,
          Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
        rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have hz : 6 * triple A B B = 2 * T * z := by
      first
      | rw [hQ.2.2 A, hAQ]
        dsimp only [z, sliceLowerBound]
        rw [hsqrt, show 1 - 2 * δ = 2 * T by dsimp [T]; ring]
        field_simp [hT.ne']
    have himprove := (reference_improvement_bounds hs.le hsSmall hηpos.le
      (show η ≤ 1 by linarith)).1
    change s * η / 4 ≤ comparisonRoot s - z at himprove
    have hlog : Real.log (1 / s) ≤ Real.log (1 / δ) :=
      Real.log_le_log (by positivity) (one_div_le_one_div_of_le hδpos (by linarith))
    have hlogs : 0 ≤ Real.log (1 / s) := Real.log_nonneg ((one_le_div hs).mpr (by linarith))
    have hsq : s ^ 2 / 256 ≤ δ ^ 2 := by nlinarith
    have hprod := mul_le_mul hsq hlog hlogs (sq_nonneg δ)
    change (3 / 50) * δ ^ 2 * Real.log (1 / δ) ≤ η at hgap
    have hηlower : (3 / 12800) * s ^ 2 * Real.log (1 / s) ≤ η := by nlinarith
    have hscale := mul_le_mul_of_nonneg_left hηlower (show 0 ≤ s / 4 by positivity)
    refine ⟨A, B, B, T, z, hT, hAw, hAh, hAa, hBw, hBh, hBw, hBh, hBa, hBa, hz,
      ?_, hApoly, hBpoly, hBpoly⟩
    nlinarith

theorem geometric_threshold_lower {s : ℝ} (hs : 0 < s) (hsSmall : s ≤ 1 / 2) :
    ∃ A B C : ConvexBody Plane, ∃ T z : ℝ, 0 < T ∧
      width A = 1 ∧ height A = s ∧ volume.real (A : Set Plane) = 2 * s * T ∧
      width B = 1 ∧ height B = 1 ∧ width C = 1 ∧ height C = 1 ∧
      volume.real (B : Set Plane) = T ∧ volume.real (C : Set Plane) = T ∧
      6 * triple A B C = 2 * T * z ∧
      (3 / 51200) * s ^ 3 * Real.log (1 / s) ≤ comparisonRoot s - z := by
  first
  | obtain ⟨A, B, C, T, z, hT, hAw, hAh, hAa, hBw, hBh, hCw, hCh,
      hBa, hCa, hz, hgap, _, _, _⟩ := geometric_threshold_lower_polygons hs hsSmall
    exact ⟨A, B, C, T, z, hT, hAw, hAh, hAa, hBw, hBh, hCw, hCh, hBa, hCa, hz, hgap⟩

end VolumePolynomials.PlanarInteraction
