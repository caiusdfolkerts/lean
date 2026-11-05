module

public import paper_verification.toric019

@[expose] public section

/-!
# Scalar facts for the manuscript's auxiliary proof corrections

These lemmas verify the real quotient correction and the zero-displacement
endpoint. They do not assert a new real-divisor version of Proposition 5.2.
The principal theorem chain already uses integral original supports, for
which its separately proved integer ceiling estimates apply.
-/

namespace ToricQuadratic

open scoped BigOperators

/-- The real quotient repairs the deficit exactly, stays positive, and
does not exceed the deficit when the positive slope is at least one. -/
theorem real_correction_bounds (δ amin : ℝ) (hδ : 0 < δ) (hmin : 1 ≤ amin) :
    0 < δ / amin ∧ δ / amin ≤ δ ∧ -δ + (δ / amin) * amin = 0 := by
  have hminpos : 0 < amin := lt_of_lt_of_le zero_lt_one hmin
  refine ⟨div_pos hδ hminpos, ?_, ?_⟩
  · apply (div_le_iff₀ hminpos).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hmin hδ.le
  · rw [div_mul_cancel₀ _ hminpos.ne']
    exact neg_add_cancel δ

/-- A nonnegative finite displacement with total budget at most zero
vanishes at every selected coordinate. No division by the budget occurs. -/
theorem nonnegative_zero_budget {ι : Type*} (I : Finset ι) (h : ι → ℝ)
    (hh : ∀ i ∈ I, 0 ≤ h i) (hbudget : (∑ i ∈ I, h i) ≤ 0) :
    ∀ i ∈ I, h i = 0 := by
  intro i hi
  exact le_antisymm ((Finset.single_le_sum hh hi).trans hbudget) (hh i hi)

end ToricQuadratic

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

/-- The zero-budget case in Lemma 3.2 leaves the actual support function
unchanged, so its original support face is precisely its zero-height slice. -/
theorem displacedSupport_eq_of_zero_budget {n : ℕ} (a : Lattice n → ℝ)
    (T : Finset (Lattice n)) (h : Lattice n → ℝ)
    (hh : ∀ u ∈ T, 0 ≤ h u) (hbudget : (∑ u ∈ T, h u) ≤ 0) :
    displacedSupport a T h = a := by
  funext u
  by_cases hu : u ∈ T
  · have hz := ToricQuadratic.nonnegative_zero_budget T h hh hbudget u hu
    simp [displacedSupport, facetWeight, hu, hz]
  · simp [displacedSupport, facetWeight, hu]

end PaperVerification.ToricGeometry
