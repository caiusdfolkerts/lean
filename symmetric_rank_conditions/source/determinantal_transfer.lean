module
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 600000

/-!
# Universal determinant transfer over the integers

The double-Laplace identity underlying Bruns--Vetter, Lemma 10.11,
is valid for every matrix over every commutative ring.  No tuple is required
to be injective, and no integer is inverted.  Its right side is an explicit
integer linear combination of products of a minor of size `u+1` and a minor
of size `w`.

The final specialization to nested row sets is the transfer used in
Bruns, Lemma 1.4(b).  The subsequent integral-exchange and majorization
arguments use these identities to establish the determinant-product
lower inclusion for Corollary 7.2.
-/

noncomputable section

namespace FourPapers.Symmetric.DeterminantalTransfer

open scoped BigOperators

universe uR uι uκ
variable {R : Type uR} {ι : Type uι} {κ : Type uκ} [CommRing R]

/-- The determinant selected by the literal row and column tuples.
Repeated indices have their usual determinant meaning. -/
def minor (X : Matrix ι κ R) {t : ℕ} (a : Fin t → ι) (b : Fin t → κ) : R :=
  (X.submatrix a b).det

theorem minor_cons_rows (X : Matrix ι κ R) {w : ℕ}
    (c : ι) (C : Fin w → ι) (D : Fin (w + 1) → κ) :
    minor X (Fin.cons c C) D =
      ∑ j : Fin (w + 1), (-1 : R) ^ j.val * X c (D j) *
        minor X C (D ∘ j.succAbove) := by
  simpa only [minor, Matrix.submatrix, Matrix.of_apply, Fin.cons_zero, Fin.cons_succ,
    Function.comp_apply] using
    Matrix.det_succ_row_zero (X.submatrix (Fin.cons c C) D)

theorem minor_cons_columns (X : Matrix ι κ R) {u : ℕ}
    (A : Fin (u + 1) → ι) (b : κ) (B : Fin u → κ) :
    minor X A (Fin.cons b B) =
      ∑ i : Fin (u + 1), (-1 : R) ^ i.val * X (A i) b *
        minor X (A ∘ i.succAbove) B := by
  simpa only [minor, Matrix.submatrix, Matrix.of_apply, Fin.cons_zero, Fin.cons_succ,
    Function.comp_apply] using
    Matrix.det_succ_column_zero (X.submatrix A (Fin.cons b B))

/-- The universal double-Laplace exchange, with both signed sums displayed.
It includes the empty-minor boundary cases `u=0` and `w=0`. -/
theorem double_laplace (X : Matrix ι κ R) {u w : ℕ}
    (A : Fin (u + 1) → ι) (B : Fin u → κ)
    (C : Fin w → ι) (D : Fin (w + 1) → κ) :
    (∑ i : Fin (u + 1), (-1 : R) ^ i.val *
        minor X (A ∘ i.succAbove) B * minor X (Fin.cons (A i) C) D) =
      ∑ j : Fin (w + 1), (-1 : R) ^ j.val *
        minor X A (Fin.cons (D j) B) * minor X C (D ∘ j.succAbove) := by
  simp_rw [minor_cons_rows]
  calc
    _ = ∑ i : Fin (u + 1), ∑ j : Fin (w + 1),
        (-1 : R) ^ j.val *
          ((-1 : R) ^ i.val * X (A i) (D j) *
            minor X (A ∘ i.succAbove) B) *
          minor X C (D ∘ j.succAbove) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ac_rfl
    _ = ∑ j : Fin (w + 1), ∑ i : Fin (u + 1),
        (-1 : R) ^ j.val *
          ((-1 : R) ^ i.val * X (A i) (D j) *
            minor X (A ∘ i.succAbove) B) *
          minor X C (D ∘ j.succAbove) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [minor_cons_columns, Finset.mul_sum, Finset.sum_mul]

/-- The integer span of actual products of minors of the two specified
sizes.  In particular this is not an ideal enlarged by polynomial
coefficients. -/
def minorProductSpan (X : Matrix ι κ R) (u v : ℕ) : Submodule ℤ R :=
  Submodule.span ℤ {z | ∃ (a : Fin u → ι) (b : Fin u → κ)
      (c : Fin v → ι) (d : Fin v → κ),
    minor X a b * minor X c d = z}

theorem minor_mul_minor_mem_span (X : Matrix ι κ R) {u v : ℕ}
    (a : Fin u → ι) (b : Fin u → κ) (c : Fin v → ι) (d : Fin v → κ) :
    minor X a b * minor X c d ∈ minorProductSpan X u v :=
  Submodule.subset_span ⟨a, b, c, d, rfl⟩

/-- Bruns--Vetter 10.11 as a literal integer-span assertion.  The identity
above supplies all coefficients explicitly, so the assertion remains
valid in every characteristic. -/
theorem alternating_exchange_mem_span (X : Matrix ι κ R) {u w : ℕ}
    (A : Fin (u + 1) → ι) (B : Fin u → κ)
    (C : Fin w → ι) (D : Fin (w + 1) → κ) :
    (∑ i : Fin (u + 1), (-1 : R) ^ i.val *
        minor X (A ∘ i.succAbove) B * minor X (Fin.cons (A i) C) D) ∈
      minorProductSpan X (u + 1) w := by
  rw [double_laplace]
  apply Submodule.sum_mem
  intro j hj
  have h := (minorProductSpan X (u + 1) w).smul_mem ((-1 : ℤ) ^ j.val)
    (minor_mul_minor_mem_span X A (Fin.cons (D j) B) C (D ∘ j.succAbove))
  simpa only [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, mul_assoc] using h

theorem minor_cons_rows_eq_zero (X : Matrix ι κ R) {w : ℕ}
    (c : ι) (C : Fin w → ι) (D : Fin (w + 1) → κ)
    (h : ∃ j, c = C j) : minor X (Fin.cons c C) D = 0 := by
  obtain ⟨j, hj⟩ := h
  apply Matrix.det_zero_of_row_eq ((Fin.succ_ne_zero j).symm)
  funext l
  simp only [Matrix.submatrix, Matrix.of_apply, Fin.cons_zero, Fin.cons_succ, hj]

/-- If every row of the small minor occurs among the tail rows of the
large minor, all the other terms of the alternating exchange vanish.
The displayed identity, rather than division by a factorial, proves the
nested-row transfer. -/
theorem nested_rows_transfer (X : Matrix ι κ R) {u w : ℕ}
    (a : Fin u → ι) (B : Fin u → κ)
    (c : ι) (C : Fin w → ι) (D : Fin (w + 1) → κ)
    (ha : ∀ i, ∃ j, a i = C j) :
    minor X a B * minor X (Fin.cons c C) D =
      ∑ j : Fin (w + 1), (-1 : R) ^ j.val *
        minor X (Fin.cons c a) (Fin.cons (D j) B) *
          minor X C (D ∘ j.succAbove) := by
  have h := double_laplace X (Fin.cons c a) B C D
  rw [Fin.sum_univ_succ] at h
  have hz (i : Fin u) : minor X (Fin.cons (a i) C) D = 0 :=
    minor_cons_rows_eq_zero X (a i) C D (ha i)
  simpa only [Fin.val_zero, pow_zero, one_mul, Fin.cons_zero,
    Fin.succAbove_zero, Function.comp_def, Fin.cons_succ, hz,
    mul_zero, Finset.sum_const_zero, add_zero] using h

/-- The nested-row case of Bruns's Lemma 1.4(b), over an arbitrary
commutative ring and with integer coefficients. -/
theorem nested_rows_transfer_mem_span (X : Matrix ι κ R) {u w : ℕ}
    (a : Fin u → ι) (B : Fin u → κ)
    (c : ι) (C : Fin w → ι) (D : Fin (w + 1) → κ)
    (ha : ∀ i, ∃ j, a i = C j) :
    minor X a B * minor X (Fin.cons c C) D ∈
      minorProductSpan X (u + 1) w := by
  rw [nested_rows_transfer X a B c C D ha]
  apply Submodule.sum_mem
  intro j hj
  have h := (minorProductSpan X (u + 1) w).smul_mem ((-1 : ℤ) ^ j.val)
    (minor_mul_minor_mem_span X (Fin.cons c a) (Fin.cons (D j) B)
      C (D ∘ j.succAbove))
  simpa only [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, mul_assoc] using h

end FourPapers.Symmetric.DeterminantalTransfer

#print axioms FourPapers.Symmetric.DeterminantalTransfer.double_laplace
#print axioms FourPapers.Symmetric.DeterminantalTransfer.nested_rows_transfer_mem_span
