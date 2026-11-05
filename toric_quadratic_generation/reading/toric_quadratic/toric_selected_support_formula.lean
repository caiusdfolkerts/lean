module

public import PaperVerification.ToricSelectedDegreeEstimates

@[expose] public section

/-!
# Rewriting a pulled-back correction in actual ray coefficients

This identity includes the discrepancy `q-1` of each inserted ray and
the number of chosen old rays in its focus.  Singleton foci obey the same
formula and introduce no extra discrepancy.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
variable {ι : Type*} [Fintype ι] (R : ι → «Σ».PrimitiveRelation)
variable (hne : ∀ i, (R i).negative.Nonempty)
variable (hdisj : «Σ».PairwiseDisjointFoci (fun i => (R i).negative))

def selectedCorrectionWeight (c side : ℝ) (D : Finset (Lattice n))
    (t : ι → ℝ) (i : ι) : ℝ :=
  c * ((R i).negative.card - 1 : ℝ) +
    side * (((R i).negative ∩ D).card : ℝ) + t i

include hne hdisj in
theorem selected_support_coefficient_formula (a : Lattice n → ℝ)
    (c side : ℝ) (D : Finset (Lattice n))
    (hD : ∀ i, «Σ».selectedRay R i ∉ D) (t : ι → ℝ) :
    simultaneousSupport (fun i => (R i).negative)
      (fun v => a v - c - side * (if v ∈ D then 1 else 0)) t =
    fun v => «Σ».selectedPullback R a v - c - side * (if v ∈ D then 1 else 0) -
      ∑ i, if v = «Σ».selectedRay R i then «Σ».selectedCorrectionWeight R c side D t i else 0 := by
  funext v
  by_cases hex : ∃ i, v = «Σ».selectedRay R i
  · obtain ⟨i, rfl⟩ := hex
    rw [«Σ».selectedSupport_at_selected_ray R hdisj,
      «Σ».selectedPullback_at_selected_ray R hne hdisj]
    have hsum : (∑ j, if «Σ».selectedRay R i = «Σ».selectedRay R j then
        «Σ».selectedCorrectionWeight R c side D t j else 0) =
        «Σ».selectedCorrectionWeight R c side D t i := by
      simp only [(«Σ».selectedRay_injective R hdisj).eq_iff]
      simp
    rw [hsum]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum, Finset.sum_boole, Finset.filter_mem_eq_inter,
      hD i, if_false, mul_zero, sub_zero, selectedCorrectionWeight]
    ring
  · have hv : ∀ i, v ≠ «Σ».selectedRay R i := by simpa only [not_exists] using hex
    rw [simultaneousSupport_of_not_sum _ _ t v hv]
    have hv' : ∀ i : «Σ».BlowupIndices R,
        v ≠ ∑ w ∈ «Σ».selectedStarFocus R i, w := fun i => hv i
    rw [selectedPullback, simultaneousSupport_of_not_sum _ a 0 v hv']
    simp only [hv, if_false, Finset.sum_const_zero, sub_zero]

include hne hdisj in
/-- A canonical-shift center written in the old fan and in the selected
fan has exactly the same coefficient function, including codimension one. -/
theorem selected_center_coefficient_formula (a : Lattice n → ℝ)
    (c : ℝ) (u : ι → ℝ) :
    simultaneousSupport (fun i => (R i).negative) (fun v => a v - c)
      (fun i => u i - c * ((R i).negative.card - 1 : ℝ)) =
      fun v => «Σ».selectedPullback R a v - c -
        ∑ i, if v = «Σ».selectedRay R i then u i else 0 := by
  have hh := «Σ».selected_support_coefficient_formula R hne hdisj a c 0 ∅
    (by simp) (fun i => u i - c * ((R i).negative.card - 1 : ℝ))
  have hu : «Σ».selectedCorrectionWeight R c 0 ∅
      (fun i => u i - c * ((R i).negative.card - 1 : ℝ)) = u := by
    funext i
    dsimp only [selectedCorrectionWeight]
    ring
  simpa only [zero_mul, sub_zero, hu] using hh

end SmoothCompleteFan

end PaperVerification.ToricGeometry
