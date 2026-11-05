import bier.forster.bound
import Mathlib.LinearAlgebra.Matrix.HadamardMatrix

/-! # The Forster bound for arbitrary column restrictions of Hadamard matrices

The restriction need not be square, and its row and column types may be empty.
The conclusion uses genuine real sign rank and the ordinary number of columns.
-/

noncomputable section

namespace Bier.Forster

open Classical Finset Matrix

variable {R C : Type*} [Fintype R] [Fintype C] [DecidableEq R]

theorem hadamard_isSignMatrix (A : Matrix R R ℝ) (hA : A.IsHadamard) :
    Bier.IsSignMatrix A := by
  intro i j
  exact Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hA.apply_mem i j)

theorem hadamard_sum_squares (A : Matrix R R ℝ) (hA : A.IsHadamard)
    (x : R → ℝ) :
    (∑ j, (∑ r, A r j * x r) ^ 2) = (Fintype.card R : ℝ) * ∑ r, x r ^ 2 := by
  have hAA : A * Aᵀ = (Fintype.card R : ℝ) • (1 : Matrix R R ℝ) := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.mul_conjTranspose
  calc
    (∑ j, (∑ r, A r j * x r) ^ 2) = (Aᵀ *ᵥ x) ⬝ᵥ (Aᵀ *ᵥ x) := by
      simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, pow_two]
    _ = x ⬝ᵥ (A *ᵥ (Aᵀ *ᵥ x)) := Matrix.dotProduct_transpose_mulVec A _ x
    _ = (Fintype.card R : ℝ) * ∑ r, x r ^ 2 := by
      rw [Matrix.mulVec_mulVec, hAA]
      simp [Matrix.smul_mulVec, dotProduct, pow_two, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring

theorem hadamard_columnRestriction_operatorBound (A : Matrix R R ℝ)
    (hA : A.IsHadamard) (e : C ↪ R) :
    SquaredOperatorBound (A.submatrix id e) (Fintype.card R : ℝ) := by
  intro x
  let f : R → ℝ := fun j => (∑ r, A r j * x r) ^ 2
  have he : (∑ c : C, f (e c)) = ∑ j ∈ (univ : Finset C).image e, f j := by
    rw [Finset.sum_image]
    intro a ha b hb hab
    exact e.injective hab
  change (∑ c : C, f (e c)) ≤ _
  rw [he]
  calc
    (∑ j ∈ (univ : Finset C).image e, f j) ≤ ∑ j : R, f j := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
        intro i hi hni
        exact sq_nonneg _)
    _ = _ := hadamard_sum_squares A hA x

/-- Every column restriction of a square real Hadamard matrix has sign rank
at least the square root of its number of columns. -/
theorem hadamard_columnRestriction_signRank (A : Matrix R R ℝ)
    (hA : A.IsHadamard) (e : C ↪ R) :
    Fintype.card C ≤ Bier.signRank (A.submatrix id e) ^ 2 := by
  by_cases hR : Fintype.card R = 0
  · have hC : Fintype.card C = 0 := by
      have hh := Fintype.card_le_of_injective e e.injective
      omega
    simp [hC]
  have hRpos : (0 : ℝ) < Fintype.card R := by exact_mod_cast (Nat.pos_of_ne_zero hR)
  have hH : Bier.IsSignMatrix (A.submatrix id e) := fun r c => hadamard_isSignMatrix A hA r (e c)
  have hh := signRank_bound (A.submatrix id e) hH (Fintype.card R : ℝ)
    (by positivity) (hadamard_columnRestriction_operatorBound A hA e)
  have hc := (mul_le_mul_iff_right₀ hRpos).mp hh
  exact_mod_cast hc

end Bier.Forster
