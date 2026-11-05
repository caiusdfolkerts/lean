module

public import VolumePolynomials.CommonLineTransversality
public import VolumePolynomials.AveragedPlanarNormalization
public import VolumePolynomials.LiftedThresholdReduction

@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Normalization of every realization of the lifted slice

The input below is the original realization relation for all ordinary
coefficients. The fiber frame, independence of its three planes, Fubini
identity, mean body, and scale factors are all constructed from that input.
No geometric normalization is an additional premise of the final result.

The zero-dimensional base recovers the equality in Proposition 3.1;
positive base dimension gives the area inequality in Proposition 6.2.
-/

open Set MeasureTheory

namespace VolumePolynomials.HigherLift

open PlanarExtrusion PlanarInteraction

theorem normalizedPlanarData_of_realizes {k : ℕ} {α s z : ℝ}
    (hα : 0 < α) (hs : 0 < s) (hs1 : s < 1)
    {K : Fin 3 → Body (3 + k)} (hK : Realizes K (coefficients k α s z)) :
    ∃ D : NormalizedPlanarData α s z,
      k = 0 → volume.real (D.A : Set Plane) = α * D.T := by
  first
  | obtain ⟨F⟩ := exists_fiberFrameData hα hs hK
    obtain ⟨C⟩ := F.exists_coordinateFiberData (F.transverse hα hs hs1)
    exact ⟨C.normalize hα, C.normalize_area_zero hα⟩

theorem normalizedPlanarData_of_mem {k : ℕ} {α s z : ℝ}
    (hα : 0 < α) (hs : 0 < s) (hs1 : s < 1)
    (h : coefficients k α s z ∈ VolumeLocus 3 (3 + k)) :
    Nonempty (NormalizedPlanarData α s z) := by
  first
  | obtain ⟨K, hK⟩ := h
    obtain ⟨D, _⟩ := normalizedPlanarData_of_realizes hα hs hs1 hK
    exact ⟨D⟩

/-- The complete geometric conclusion of the forward direction of
Proposition 6.2, including its corner inequality. This also holds for `k = 0`.
The original cubic equality is stated separately below. -/
theorem proposition_6_2_forward {k : ℕ} {α s z : ℝ}
    (hα : 0 < α) (hs : 0 < s) (hs1 : s < 1)
    {K : Fin 3 → Body (3 + k)} (hK : Realizes K (coefficients k α s z)) :
    ∃ (D : NormalizedPlanarData α s z) (Q : ConvexBody Plane),
      IsInteraction D.B D.C Q ∧
      D.T ≤ volume.real (Q : Set Plane) ∧
      2 * D.T * z = 2 * PlanarMixedForm.mixedArea volume D.A Q ∧
      1 + s - 2 * Real.sqrt ((s - α * D.T) *
        (1 - volume.real (Q : Set Plane))) ≤ 2 * D.T * z ∧
      α * D.T ≤ s := by
  first
  | obtain ⟨D, _⟩ := normalizedPlanarData_of_realizes hα hs hs1 hK
    obtain ⟨Q, hQ, hQa⟩ := proposition_4_3 D.B D.C
      D.B_width D.B_height D.C_width D.C_height
    have hTq : D.T ≤ volume.real (Q : Set Plane) := by
      first
      | simpa only [D.B_area, D.C_area, max_self] using hQa
    have hz : 2 * D.T * z = 2 * PlanarMixedForm.mixedArea volume D.A Q :=
      D.triple_value.symm.trans (hQ.2.2 D.A)
    have hAa := area_le_width_mul_height D.A
    rw [D.A_width, D.A_height, one_mul] at hAa
    have hQa' := area_le_width_mul_height Q
    rw [hQ.1, hQ.2.1, one_mul] at hQa'
    have hprod : (s - volume.real (D.A : Set Plane)) *
        (1 - volume.real (Q : Set Plane)) ≤
        (s - α * D.T) * (1 - volume.real (Q : Set Plane)) :=
      mul_le_mul_of_nonneg_right (by linarith [D.A_area]) (by linarith)
    have hsqrt := Real.sqrt_le_sqrt hprod
    have hcorner := PlanarCorner.mixedArea_corner_inequality D.A Q
    rw [D.A_width, D.A_height, hQ.1, hQ.2.1, one_mul, mul_one] at hcorner
    simp only [one_mul, mul_one] at hcorner
    refine ⟨D, Q, hQ, hTq, hz, ?_, D.A_area.trans hAa⟩
    linarith

/-- The geometric premise used by the boundary theorem is now a theorem
of the original coefficient locus, for every base dimension. -/
theorem fiberValues_normalized (k : ℕ) (s z : ℝ)
    (hs : 0 < s) (hs1 : s < 1) (hz : z ∈ fiberValues k s) :
    Nonempty (NormalizedPlanarData (2 * s) s z) :=
  normalizedPlanarData_of_mem (by linarith) hs hs1 hz

/-- Theorem 5.5 for the actual cubic boundary (`k = 0`), together with
the same two-sided estimate on every lifted coefficient slice. -/
theorem boundaryValue_logarithmic_gap (k : ℕ) {s : ℝ} (hs : 0 < s)
    (hsmall : s < min (1 / 128) (Real.exp (-1))) :
    (3 / 51200) * s ^ 3 * Real.log (1 / s) ≤
        comparisonRoot s - boundaryValue k s ∧
      comparisonRoot s - boundaryValue k s ≤
        34816 * s ^ 3 * Real.log (1 / s) := by
  first
  | have hs128 : s < 1 / 128 := hsmall.trans_le (min_le_left _ _)
    have hshalf : s ≤ 1 / 2 := by linarith
    obtain ⟨D⟩ := fiberValues_normalized k s (boundaryValue k s) hs (by linarith)
      (boundaryValue_attained k hs hshalf).1
    exact ⟨boundaryValue_gap_lower k hs hshalf, D.threshold_upper hs hsmall⟩

theorem coefficientSlice_not_semialgebraic (k : ℕ) :
    ¬ TauCeti.IsSemialgebraic (coefficientSlice k) :=
  coefficientSlice_not_semialgebraic_of_normalization k (fiberValues_normalized k)

theorem volumeLocus_not_semialgebraic (k : ℕ) :
    ¬ TauCeti.IsSemialgebraic (VolumeLocus 3 (3 + k)) :=
  volumeLocus_not_semialgebraic_of_normalization k (fiberValues_normalized k)

end HigherLift

namespace PlanarInteraction

open PlanarExtrusion HigherLift

/-- Proposition 3.1 with every width, area and mixed-volume equality
retained in `NormalizedPlanarData` and the explicit area equality below. -/
theorem proposition_3_1 {α s z : ℝ} (hα : 0 < α) (hs : 0 < s) (hs1 : s < 1) :
    CubicSlice.coefficients α s z ∈ VolumeLocus 3 3 ↔
      ∃ D : NormalizedPlanarData α s z,
        volume.real (D.A : Set Plane) = α * D.T := by
  first
  | constructor
    · intro h
      have hzero : HigherLift.coefficients 0 α s z ∈ VolumeLocus 3 (3 + 0) := by
        first
        | simpa only [HigherLift.coefficients_zero] using h
      obtain ⟨K, hK⟩ := hzero
      obtain ⟨D, hD⟩ := HigherLift.normalizedPlanarData_of_realizes hα hs hs1 hK
      exact ⟨D, hD rfl⟩
    · rintro ⟨D, hD⟩
      exact normalized_mem_volumeLocus D hD

end PlanarInteraction
end VolumePolynomials
