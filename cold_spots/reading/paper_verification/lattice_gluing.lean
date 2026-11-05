module
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
@[expose] public section
/-!
# Exact finite-profile gluing inequality

This file proves the finite-dimensional inequality and equality statement used in
Proposition 7.1 of `lattice_cold_spots(2).pdf`. The theorem is an algebraic statement
about coset profiles; the identification of these profiles with Gaussian lattice
sums is a separate dependency and is not assumed to have been verified here.
-/

namespace PaperVerification.Lattice

open scoped BigOperators

variable {ι : Type*}

/-- The exact nonnegative-defect identity behind diagonal gluing. -/
theorem diagonal_gluing_defect (s : Finset ι) (u v : ι → ℝ) (κ σ : ℝ) :
    (∑ i ∈ s, u i * v i) - (2 * κ * σ - (s.card : ℝ) * κ ^ 2) =
      (∑ i ∈ s, (u i - κ) * (v i - κ)) +
        κ * ((∑ i ∈ s, u i) - σ) + κ * ((∑ i ∈ s, v i) - σ) := by
  have hexp (i : ι) : (u i - κ) * (v i - κ) =
      u i * v i - κ * u i - κ * v i + κ ^ 2 := by ring
  simp only [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, nsmul_eq_mul]
  ring

/-- Proposition 7.1's finite-profile bound, for an arbitrary finite quotient. -/
theorem diagonal_gluing_bound (s : Finset ι) (u v : ι → ℝ) (κ σ : ℝ)
    (hκ : 0 ≤ κ) (hu : ∀ i ∈ s, κ ≤ u i) (hv : ∀ i ∈ s, κ ≤ v i)
    (hSu : σ ≤ ∑ i ∈ s, u i) (hSv : σ ≤ ∑ i ∈ s, v i) :
    2 * κ * σ - (s.card : ℝ) * κ ^ 2 ≤ ∑ i ∈ s, u i * v i := by
  have hd : 0 ≤ ∑ i ∈ s, (u i - κ) * (v i - κ) :=
    Finset.sum_nonneg fun i hi => mul_nonneg (sub_nonneg.mpr (hu i hi))
      (sub_nonneg.mpr (hv i hi))
  have hU := mul_nonneg hκ (sub_nonneg.mpr hSu)
  have hV := mul_nonneg hκ (sub_nonneg.mpr hSv)
  linarith [diagonal_gluing_defect s u v κ σ]

/-- The exact equality locus. Strict positivity of the profile minimum is needed
for equality in the two marginal bounds; Gaussian profile minima are positive. -/
theorem diagonal_gluing_eq_iff (s : Finset ι) (u v : ι → ℝ) (κ σ : ℝ)
    (hκ : 0 < κ) (hu : ∀ i ∈ s, κ ≤ u i) (hv : ∀ i ∈ s, κ ≤ v i)
    (hSu : σ ≤ ∑ i ∈ s, u i) (hSv : σ ≤ ∑ i ∈ s, v i) :
    (∑ i ∈ s, u i * v i) = 2 * κ * σ - (s.card : ℝ) * κ ^ 2 ↔
      (∑ i ∈ s, u i) = σ ∧ (∑ i ∈ s, v i) = σ ∧
        ∀ i ∈ s, u i = κ ∨ v i = κ := by
  have hi : ∀ i ∈ s, 0 ≤ (u i - κ) * (v i - κ) :=
    fun i hi => mul_nonneg (sub_nonneg.mpr (hu i hi)) (sub_nonneg.mpr (hv i hi))
  have hd : 0 ≤ ∑ i ∈ s, (u i - κ) * (v i - κ) := Finset.sum_nonneg hi
  have hU := mul_nonneg hκ.le (sub_nonneg.mpr hSu)
  have hV := mul_nonneg hκ.le (sub_nonneg.mpr hSv)
  constructor
  · intro h
    have hdu : κ * ((∑ i ∈ s, u i) - σ) = 0 := by
      linarith [diagonal_gluing_defect s u v κ σ]
    have hdv : κ * ((∑ i ∈ s, v i) - σ) = 0 := by
      linarith [diagonal_gluing_defect s u v κ σ]
    have hz : (∑ i ∈ s, (u i - κ) * (v i - κ)) = 0 := by
      linarith [diagonal_gluing_defect s u v κ σ]
    refine ⟨?_, ?_, ?_⟩
    · exact sub_eq_zero.mp ((mul_eq_zero.mp hdu).resolve_left (ne_of_gt hκ))
    · exact sub_eq_zero.mp ((mul_eq_zero.mp hdv).resolve_left (ne_of_gt hκ))
    · intro i his
      have hp : (u i - κ) * (v i - κ) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg hi).mp hz i his
      exact (mul_eq_zero.mp hp).imp sub_eq_zero.mp sub_eq_zero.mp
  · rintro ⟨hUeq, hVeq, hzero⟩
    have hz : (∑ i ∈ s, (u i - κ) * (v i - κ)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rcases hzero i hi with h | h <;> simp [h]
    have hid := diagonal_gluing_defect s u v κ σ
    rw [hUeq, hVeq, hz] at hid
    simp only [sub_self, mul_zero, add_zero, zero_add] at hid
    exact sub_eq_zero.mp hid

end PaperVerification.Lattice

#print axioms PaperVerification.Lattice.diagonal_gluing_bound
#print axioms PaperVerification.Lattice.diagonal_gluing_eq_iff
