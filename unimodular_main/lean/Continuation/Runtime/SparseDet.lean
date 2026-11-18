module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

/-!
# A sparse determinant evaluator with the ordinary determinant as specification

Zero entries are tested before the recursive call. This is important for kernel
evaluation of families containing coordinate columns: expanding a zero term
would otherwise compute all of its minors before multiplying by zero.
-/

open scoped BigOperators

namespace Unimodular.FiniteMatrixCertificates

def sparseDet : (n : ℕ) → Matrix (Fin n) (Fin n) ℤ → ℤ
  | 0, _ => 1
  | n + 1, A => ∑ j : Fin (n + 1),
      if A 0 j = 0 then 0 else
        (-1) ^ j.val * A 0 j * sparseDet n (A.submatrix Fin.succ j.succAbove)

theorem sparseDet_eq_det : ∀ n A, sparseDet n A = A.det := by
  intro n
  induction n with
  | zero => intro A; simp [sparseDet]
  | succ n ih =>
      intro A
      rw [sparseDet, Matrix.det_succ_row_zero]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hz : A 0 j = 0
      · simp [hz]
      · simp only [if_neg hz, ih]

#print axioms sparseDet_eq_det
end Unimodular.FiniteMatrixCertificates
