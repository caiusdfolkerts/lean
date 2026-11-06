module

public import wishart.verified.real_remainder12

/-!
# Covariance factors with exactly the covariance rank many columns

A positive semidefinite covariance is factored by retaining the nonzero
columns of its eigenbasis square-root factor. The discarded columns vanish
identically. This gives a full-column-rank rectangular factor even when the
covariance is singular, including the zero-dimensional factor for rank zero.
-/

@[expose] public section

noncomputable section

open Matrix
open WishartVerification
open scoped Classical BigOperators Matrix.Norms.L2Operator

namespace Wishart.FiniteOrder

/-- Every positive semidefinite covariance has an injective square-root
factor whose source dimension is its exact rank. -/
theorem exists_reduced_covariance_factor {p : ℕ}
    {C : Matrix (Fin p) (Fin p) ℝ} (hC : C.PosSemidef) :
    ∃ L : Matrix (Fin p) (Fin C.rank) ℝ,
      L * Lᵀ = C ∧ Function.Injective L.mulVec := by
  let A := eigenGaussianMatrix hC
  let I := {i : Fin p // hC.isHermitian.eigenvalues i ≠ 0}
  let B : Matrix (Fin p) I ℝ := A.submatrix id Subtype.val
  have hzero (j : Fin p) (hj : hC.isHermitian.eigenvalues j = 0) (i : Fin p) :
      A i j = 0 := by
    simp only [A, eigenGaussianMatrix, Matrix.mul_diagonal, hj, Real.sqrt_zero, mul_zero]
  have hB : B * Bᵀ = C := by
    refine Eq.trans (b := A * Aᵀ) ?_ (eigenGaussianMatrix_covariance hC)
    apply Matrix.ext
    intro i j
    change (∑ k : I, A i k.val * A j k.val) = ∑ k : Fin p, A i k * A j k
    have hsplit := Fintype.sum_subtype_add_sum_subtype
      (fun k : Fin p => hC.isHermitian.eigenvalues k ≠ 0)
      (fun k => A i k * A j k)
    have hvanish : (∑ k : {k : Fin p // ¬hC.isHermitian.eigenvalues k ≠ 0},
        A i k.val * A j k.val) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [hzero k.val (not_ne_iff.mp k.property) i, zero_mul]
    rw [hvanish, add_zero] at hsplit
    exact hsplit
  have hcard : Fintype.card I = C.rank := hC.isHermitian.rank_eq_card_non_zero_eigs.symm
  let e : Fin C.rank ≃ I := (Fintype.equivFinOfCardEq hcard).symm
  let L : Matrix (Fin p) (Fin C.rank) ℝ := B.submatrix id e
  have hL : L * Lᵀ = C := by
    change B.submatrix id e * (B.submatrix id e)ᵀ = C
    rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id, hB]
  refine ⟨L, hL, ?_⟩
  apply (Matrix.rank_eq_card_iff_mulVec_injective L).mp
  exact Matrix.rank_left_factor_eq (by simp) hL.symm

end Wishart.FiniteOrder

end
