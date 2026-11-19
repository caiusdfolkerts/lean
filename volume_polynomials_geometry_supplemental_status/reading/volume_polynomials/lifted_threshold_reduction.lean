module

public import VolumePolynomials.LiftedSliceCoordinates
public import VolumePolynomials.PlanarCubicVolume
public import VolumePolynomials.NormalizedThreshold

@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# From the geometric lifting proposition to the boundary obstruction

The affine slice and its minimum are defined in the original coefficient
locus. Closedness proves attainment. Polygonal cubic witnesses lift to all
dimensions. The remaining forward-normalization premise in the final
transfer lemma is discharged by the geometric lifting theorem, not treated
as an axiom or a definition of realizability.
-/

open Set MeasureTheory Filter
open scoped Topology Pointwise

namespace VolumePolynomials.PlanarInteraction

open PlanarExtrusion PlanarMixedForm PlanarCorner

def NormalizedData.toPlanarData {s z : ℝ} (D : NormalizedData s z) :
    NormalizedPlanarData (2 * s) s z where
  A := D.A
  B := D.B
  C := D.C
  T := D.T
  T_pos := D.T_pos
  A_width := D.A_width
  A_height := D.A_height
  A_area := D.A_area.ge
  B_width := D.B_width
  B_height := D.B_height
  C_width := D.C_width
  C_height := D.C_height
  B_area := D.B_area
  C_area := D.C_area
  triple_value := D.triple_value

theorem NormalizedData.mem_cubic_locus {s z : ℝ} (D : NormalizedData s z) :
    CubicSlice.coefficients (2 * s) s z ∈ VolumeLocus 3 3 :=
  normalized_mem_volumeLocus D.toPlanarData D.A_area

theorem NormalizedData.mem_lifted_slice {s z : ℝ} (D : NormalizedData s z) (k : ℕ) :
    z ∈ HigherLift.fiberValues k s :=
  HigherLift.mem_volumeLocus_of_cubic_all k D.mem_cubic_locus

theorem NormalizedPlanarData.threshold_upper {s z : ℝ}
    (D : NormalizedPlanarData (2 * s) s z) (hs : 0 < s)
    (hsmall : s < min (1 / 128) (Real.exp (-1))) :
    comparisonRoot s - z ≤ 34816 * s ^ 3 * Real.log (1 / s) := by
  first
  | obtain ⟨Q, hQ, hQa⟩ := proposition_4_3 D.B D.C D.B_width D.B_height D.C_width D.C_height
    apply geometric_threshold_upper hs hsmall D.T_pos D.A_width D.A_height D.A_area
      D.B_width D.B_height D.C_width D.C_height D.B_area D.C_area hQ
    exact D.triple_value.symm.trans (hQ.2.2 D.A)

end PlanarInteraction

namespace HigherLift

open PlanarInteraction

theorem fiberValues_nonempty (k : ℕ) {s : ℝ} (hs : 0 < s) (hsmall : s ≤ 1 / 2) :
    (fiberValues k s).Nonempty := by
  first
  | obtain ⟨z, ⟨D⟩, hz⟩ := normalized_nonempty hs hsmall
    exact ⟨z, D.mem_lifted_slice k⟩

theorem boundaryValue_attained (k : ℕ) {s : ℝ} (hs : 0 < s) (hsmall : s ≤ 1 / 2) :
    boundaryValue k s ∈ fiberValues k s ∧
      ∀ z ∈ fiberValues k s, boundaryValue k s ≤ z :=
  boundaryValue_attained_of_nonempty k s (fiberValues_nonempty k hs hsmall)

theorem lifted_lower_gap_witness (k : ℕ) {s : ℝ} (hs : 0 < s) (hsmall : s ≤ 1 / 2) :
    ∃ z ∈ fiberValues k s,
      (3 / 51200) * s ^ 3 * Real.log (1 / s) ≤ comparisonRoot s - z := by
  first
  | obtain ⟨A, B, C, T, z, hT, hAw, hAh, hAa, hBw, hBh, hCw, hCh,
      hBa, hCa, hz, hgap⟩ := geometric_threshold_lower hs hsmall
    let D : NormalizedData s z :=
      ⟨A, B, C, T, hT, hAw, hAh, hAa, hBw, hBh, hCw, hCh, hBa, hCa, hz⟩
    exact ⟨z, D.mem_lifted_slice k, hgap⟩

theorem boundaryValue_gap_lower (k : ℕ) {s : ℝ} (hs : 0 < s) (hsmall : s ≤ 1 / 2) :
    (3 / 51200) * s ^ 3 * Real.log (1 / s) ≤ comparisonRoot s - boundaryValue k s := by
  first
  | obtain ⟨z, hz, hgap⟩ := lifted_lower_gap_witness k hs hsmall
    have hmin := (boundaryValue_attained k hs hsmall).2 z hz
    linarith

/-- This transfer lemma isolates the exact geometric statement still to be
supplied: every original realization must yield actual normalized bodies.
It does not introduce a weaker realization relation. -/
theorem coefficientSlice_not_semialgebraic_of_normalization (k : ℕ)
    (hforward : ∀ s z : ℝ, 0 < s → s < 1 → z ∈ fiberValues k s →
      Nonempty (NormalizedPlanarData (2 * s) s z)) :
    ¬ TauCeti.IsSemialgebraic (coefficientSlice k) := by
  first
  | let a : ℝ := min (1 / 128) (Real.exp (-1))
    have ha : 0 < a := lt_min (by norm_num) (Real.exp_pos _)
    apply not_semialgebraic_of_logarithmic_minimum_gap_frontier
      (S := coefficientSlice k) (b := boundaryValue k) (a := a)
      (c := 3 / 51200) (C := 34816) ha (by norm_num)
    · intro s hs
      have hssmall : s ≤ 1 / 2 := by
        first
        | have h := hs.2.trans_le (min_le_left (1 / 128 : ℝ) (Real.exp (-1)))
          linarith
      exact (boundaryValue_attained k hs.1 hssmall).1
    · intro s hs z hz
      have hssmall : s ≤ 1 / 2 := by
        first
        | have h := hs.2.trans_le (min_le_left (1 / 128 : ℝ) (Real.exp (-1)))
          linarith
      exact (boundaryValue_attained k hs.1 hssmall).2 z hz
    · filter_upwards [self_mem_nhdsWithin,
        (show ∀ᶠ s in 𝓝[>] (0 : ℝ), s < a from
          Filter.Eventually.filter_mono nhdsWithin_le_nhds
            (show ∀ᶠ s : ℝ in 𝓝 0, s < a from Iio_mem_nhds ha))] with s hs hsa
      have hssmall : s ≤ 1 / 2 := by
        first
        | have h := hsa.trans_le (min_le_left (1 / 128 : ℝ) (Real.exp (-1)))
          linarith
      obtain ⟨D⟩ := hforward s (boundaryValue k s) hs (by linarith)
        (boundaryValue_attained k hs hssmall).1
      exact ⟨by simpa only [one_div] using boundaryValue_gap_lower k hs hssmall,
        by simpa only [one_div] using D.threshold_upper hs hsa⟩

theorem volumeLocus_not_semialgebraic_of_normalization (k : ℕ)
    (hforward : ∀ s z : ℝ, 0 < s → s < 1 → z ∈ fiberValues k s →
      Nonempty (NormalizedPlanarData (2 * s) s z)) :
    ¬ TauCeti.IsSemialgebraic (VolumeLocus 3 (3 + k)) := by
  first
  | intro h
    exact coefficientSlice_not_semialgebraic_of_normalization k hforward
      (isSemialgebraic_coefficientSlice k h)

end HigherLift
end VolumePolynomials
