/- One additional state supplies row sums without changing the detected score. -/
module

public import mixed_volume.computability.quadratic_encoding
public import Mathlib.Algebra.BigOperators.Option

set_option autoImplicit false

@[expose] public section
open Matrix
open scoped BigOperators

namespace MixedVolume.SevenState

open FractionalWords QuadraticEncoding MatrixMortality

abbrev State := Option (Fin 6)
abbrev M7 := Matrix State State ℚ

@[simp] theorem card_state : Fintype.card State = 7 := by simp [State]

def extend (M : M6) : M7
  | some i, some j => M i j
  | some i, none => 1 - ∑ j, M i j
  | none, some _ => 0
  | none, none => 1

theorem extend_row_sum (M : M6) (i : State) : ∑ j, extend M i j = 1 := by
  cases i <;> simp [extend, Fintype.sum_option]

theorem extend_column_sum (M : M6) (hc : ∀ j, ∑ i, M i j = 1)
    (j : State) : ∑ i, extend M i j = 1 := by
  cases j with
  | none =>
    have ht : (∑ i : Fin 6, ∑ j : Fin 6, M i j) = 6 := by
      calc
        _ = ∑ j : Fin 6, ∑ i : Fin 6, M i j := Finset.sum_comm
        _ = 6 := by simp [hc]
    simp only [Fintype.sum_option, extend, Finset.sum_sub_distrib]
    rw [ht]
    norm_num
  | some j => simp [extend, Fintype.sum_option, hc]

theorem extend_one : extend 1 = 1 := by
  ext i j
  cases i <;> cases j <;> simp [extend, Matrix.one_apply, Fintype.sum_option]

theorem extend_mul (M N : M6) : extend (M * N) = extend M * extend N := by
  ext i j
  cases i with
  | none => cases j <;> simp [extend, Matrix.mul_apply, Fintype.sum_option]
  | some i =>
    cases j with
    | some j => simp [extend, Matrix.mul_apply, Fintype.sum_option]
    | none =>
      simp only [extend, Matrix.mul_apply, Fintype.sum_option]
      simp only [mul_one, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
      rw [Finset.sum_comm]
      ring

def C (u v : List Bool) : M7 := extend (B u v)

@[simp] theorem C_nil : C [] [] = 1 := by simp [C, extend_one]

theorem C_append (u v U V : List Bool) :
    C (u ++ U) (v ++ V) = C u v * C U V := by
  rw [C, B_append, extend_mul]
  rfl

theorem C_row_sum (u v : List Bool) (i : State) : ∑ j, C u v i j = 1 :=
  extend_row_sum _ _

theorem C_column_sum (u v : List Bool) (j : State) : ∑ i, C u v i j = 1 :=
  extend_column_sum _ (B_column_sum u v) _

def row : State → ℚ
  | none => 0
  | some i => signedRow i

theorem row_sum : ∑ i, row i = 0 := by
  simpa [row, Fintype.sum_option] using signedRow_sum

theorem row_bounds (i : State) : -3 < row i ∧ row i < 3 := by
  cases i with
  | none => norm_num [row]
  | some i => exact signedRow_bounds i

theorem row_C_first (u v : List Bool) :
    (row ᵥ* C u v) (some 0) = score u v := by
  simpa only [row, C, Matrix.vecMul, dotProduct, Fintype.sum_option, extend,
    zero_mul, zero_add] using signedRow_B_first u v

theorem wordProduct_C {α : Type*} (upper lower : α → List Bool) (w : List α) :
    wordProduct (fun a => C (upper a) (lower a)) w =
      C (spell upper w) (spell lower w) := by
  induction w with
  | nil => simp [spell]
  | cons a w ih =>
    rw [wordProduct_cons, ih, ← C_append]
    rfl

end MixedVolume.SevenState
