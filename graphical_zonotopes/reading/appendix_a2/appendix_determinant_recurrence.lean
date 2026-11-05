module

public import Papers.GraphicalZonotopes.AppendixPathMatrix
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.SuccPred

/-! # The literal tridiagonal determinant recurrence

This file proves the two-step determinant identity directly from the matrix
of Appendix A. No recurrence is used as the definition of the polynomial.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Matrix
open Finset Matrix

namespace GraphicalZonotopes.PathDeterminant

variable {R : Type*} [CommRing R]

/-- Deleting the first row and column shifts the variable sequence by one. -/
theorem tridiagonal_tail {m : ℕ} (t : Fin (m+3) → R) :
    (tridiagonal t).submatrix Fin.succ Fin.succ =
      tridiagonal (fun j : Fin (m+2) => t j.succ) := by
  ext i j
  simp only [Matrix.submatrix_apply, tridiagonal, Fin.castSucc_succ, Fin.succ_inj]

/-- The entries of the first row beyond its two possible nonzero positions vanish. -/
theorem tridiagonal_zero_succ_succ {m : ℕ} (t : Fin (m+4) → R) (j : Fin m) :
    tridiagonal t 0 j.succ.succ = 0 := by
  apply tridiagonal_off_band
  · intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_succ] at hv
    omega
  · simp only [Fin.val_zero, Fin.val_succ]
    omega
  · simp only [Fin.val_zero, Fin.val_succ]
    omega

/-- The corresponding entries of the first column vanish. -/
theorem tridiagonal_succ_succ_zero {m : ℕ} (t : Fin (m+4) → R) (i : Fin m) :
    tridiagonal t i.succ.succ 0 = 0 := by
  apply tridiagonal_off_band
  · intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_succ] at hv
    omega
  · simp only [Fin.val_zero, Fin.val_succ]
    omega
  · simp only [Fin.val_zero, Fin.val_succ]
    omega

/-- Deleting the first two rows and columns shifts the variables twice. -/
theorem tridiagonal_tail_twice {m : ℕ} (t : Fin (m+4) → R) :
    (tridiagonal t).submatrix (fun i : Fin m => i.succ.succ)
        (fun j : Fin m => j.succ.succ) =
      tridiagonal (fun j : Fin (m+2) => t j.succ.succ) := by
  calc
    _ = ((tridiagonal t).submatrix Fin.succ Fin.succ).submatrix
        Fin.succ Fin.succ := rfl
    _ = _ := by rw [tridiagonal_tail, tridiagonal_tail]

/-- The other nonzero first-row cofactor has a first column with one
nonzero entry. Its determinant is therefore a smaller tridiagonal
determinant multiplied by the adjacent entry. -/
theorem tridiagonal_minor_one_det {m : ℕ} (t : Fin (m+4) → R) :
    ((tridiagonal t).submatrix Fin.succ (0 : Fin (m+1)).succ.succAbove).det =
      -t 1 * (tridiagonal (fun j : Fin (m+2) => t j.succ.succ)).det := by
  let N : Matrix (Fin (m+1)) (Fin (m+1)) R :=
    (tridiagonal t).submatrix Fin.succ (0 : Fin (m+1)).succ.succAbove
  change N.det = _
  have h00 : N 0 0 = -t 1 := by
    change tridiagonal t (0 : Fin (m+1)).succ
      ((0 : Fin (m+1)).succ.succAbove 0) = _
    rw [Fin.succ_succAbove_zero]
    simpa using tridiagonal_below t (0 : Fin (m+1)).succ 0 (by simp)
  have hzero : ∀ i : Fin m, N i.succ 0 = 0 := by
    intro i
    change tridiagonal t i.succ.succ
      ((0 : Fin (m+1)).succ.succAbove 0) = 0
    rw [Fin.succ_succAbove_zero]
    exact tridiagonal_succ_succ_zero t i
  have htail : N.submatrix Fin.succ Fin.succ =
      tridiagonal (fun j : Fin (m+2) => t j.succ.succ) := by
    ext i j
    change tridiagonal t i.succ.succ
      ((0 : Fin (m+1)).succ.succAbove j.succ) = _
    rw [Fin.succ_succAbove_succ, Fin.zero_succAbove]
    exact congrFun (congrFun (tridiagonal_tail_twice t) i) j
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero,
    hzero, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  rw [h00, htail]

/-- The characteristic-independent continuant identity for the exact matrix. -/
theorem tridiagonal_det_recurrence {m : ℕ} (t : Fin (m+4) → R) :
    (tridiagonal t).det =
      (t 0 + t 1 + t 2) *
        (tridiagonal (fun j : Fin (m+3) => t j.succ)).det -
      (t 1)^2 *
        (tridiagonal (fun j : Fin (m+2) => t j.succ.succ)).det := by
  have hdiag : tridiagonal t 0 0 = t 0 + t 1 + t 2 := by
    simpa using tridiagonal_diag t 0
  have hnext : tridiagonal t 0 (0 : Fin (m+1)).succ = -t 1 := by
    simpa using tridiagonal_above t 0 (0 : Fin (m+1)).succ (by simp)
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, Nat.zero_add, pow_zero, pow_one,
    one_mul, Fin.succAbove_zero, tridiagonal_zero_succ_succ,
    mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  rw [hdiag, hnext, tridiagonal_tail, tridiagonal_minor_one_det]
  ring

end GraphicalZonotopes.PathDeterminant
