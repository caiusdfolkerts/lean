/- Six-dimensional rational matrices detecting equality of arbitrary words. -/
module

public import mixed_volume.computability.fractional_words
public import matrix_mortality.matrix_semigroup
public import matrix_mortality.word_morphism
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NoncommRing

set_option autoImplicit false

@[expose] public section
open Matrix
open scoped BigOperators

namespace MixedVolume.QuadraticEncoding

open FractionalWords MatrixMortality

abbrev M6 := Matrix (Fin 6) (Fin 6) ℚ

def raw (x r y s : ℚ) : M6 :=
  !![1,0,0,0,0,0;
     x,r,0,0,0,0;
     x^2,2*r*x,r^2,0,0,0;
     y,0,0,s,0,0;
     y^2,0,0,2*s*y,s^2,0;
     x*y,r*y,0,s*x,0,r*s]

theorem raw_mul (x r y s X R Y S : ℚ) :
    raw x r y s * raw X R Y S = raw (x + r*X) (r*R) (y + s*Y) (s*S) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [raw, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem raw_identity : raw 0 1 0 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [raw, Matrix.one_apply]

def A (u v : List Bool) : M6 := raw (value u) (scale u) (value v) (scale v)

@[simp] theorem A_nil : A [] [] = 1 := by simpa [A] using raw_identity

theorem A_append (u v U V : List Bool) :
    A (u ++ U) (v ++ V) = A u v * A U V := by
  simp only [A, value_append, scale_append, raw_mul]

def S : M6 :=
  !![1,1,1,1,1,1;
     0,1,0,0,0,0;
     -(1/32),-(1/32),31/32,-(1/32),-(1/32),-(1/32);
     0,0,0,1,0,0;
     0,0,0,0,19/16,0;
     0,0,0,0,0,1]

def inverseS : M6 :=
  !![31/32,-1,-1,-1,-(16/19),-1;
     0,1,0,0,0,0;
     1/32,0,1,0,0,0;
     0,0,0,1,0,0;
     0,0,0,0,16/19,0;
     0,0,0,0,0,1]

theorem inverseS_mul_S : inverseS * S = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [S, inverseS, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]

theorem S_mul_inverseS : S * inverseS = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [S, inverseS, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]

def conjugate (M : M6) : M6 := inverseS * M * S

theorem conjugate_mul (M N : M6) : conjugate (M*N) = conjugate M * conjugate N := by
  unfold conjugate
  calc
    _ = inverseS * M * (S * inverseS) * N * S := by rw [S_mul_inverseS]; simp [mul_assoc]
    _ = _ := by noncomm_ring

@[simp] theorem conjugate_one : conjugate 1 = 1 := by
  simpa [conjugate] using inverseS_mul_S

def B (u v : List Bool) : M6 := conjugate (A u v)

@[simp] theorem B_nil : B [] [] = 1 := by simp [B]

theorem B_append (u v U V : List Bool) :
    B (u ++ U) (v ++ V) = B u v * B U V := by
  rw [B, A_append, conjugate_mul]
  rfl

/-- A fixed signed row with sum zero. -/
def signedRow : Fin 6 → ℚ := ![1/32,1/32,-(31/32),1/32,-(37/32),65/32]

theorem signedRow_sum : ∑ i, signedRow i = 0 := by
  norm_num [signedRow, Fin.sum_univ_succ]

theorem signedRow_bounds (i : Fin 6) : -3 < signedRow i ∧ signedRow i < 3 := by
  fin_cases i <;> norm_num [signedRow]

theorem B_column_sum (u v : List Bool) (j : Fin 6) : ∑ i, B u v i j = 1 := by
  fin_cases j <;>
    simp [B, conjugate, A, raw, S, inverseS, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem signedRow_B_first (u v : List Bool) :
    (signedRow ᵥ* B u v) 0 = score u v := by
  simp [B, conjugate, A, raw, S, inverseS, signedRow, Matrix.vecMul,
    dotProduct, Matrix.mul_apply, Fin.sum_univ_succ, score]
  ring

theorem wordProduct_B {α : Type*} (upper lower : α → List Bool) (w : List α) :
    wordProduct (fun a => B (upper a) (lower a)) w =
      B (spell upper w) (spell lower w) := by
  induction w with
  | nil => simp [spell]
  | cons a w ih =>
    rw [wordProduct_cons, ih, ← B_append]
    rfl

/-- Exact acceptance score for a prefix followed by an arbitrary source word. -/
theorem signedRow_prefix_product_first {α : Type*}
    (upper lower : α → List Bool) (u v : List Bool) (w : List α) :
    (signedRow ᵥ* (B u v * wordProduct (fun a => B (upper a) (lower a)) w)) 0 =
      score (u ++ spell upper w) (v ++ spell lower w) := by
  rw [wordProduct_B, ← B_append, signedRow_B_first]

end MixedVolume.QuadraticEncoding
