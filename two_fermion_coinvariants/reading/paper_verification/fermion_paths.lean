module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Tactic.Ring

/-!
# The path transfer identities

The height variable is `X`; `t` records total exterior degree. Summing the two
single-mark colors produces the transfer operator used in the rank calculation.
These identities are valid over arbitrary commutative semirings. They are the
enumerative part of the proof, and do not assert that the quotient has the
proposed path-indexed basis.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion
namespace Paths

open Polynomial

variable {R : Type*} [CommSemiring R]

/-- The paired height-transfer operator after summing the two single-mark colors. -/
def transfer (s t : R) (p : R[X]) : R[X] :=
  (X + C t) ^ 2 * derivative p + C s * (X + C t) * p

theorem transfer_power (s t a : R) (n : ℕ) :
    transfer s t (C a * (X + C t) ^ n) =
      C (a * (s + (n : R))) * (X + C t) ^ (n + 1) := by
  cases n with
  | zero => simp [transfer] <;> ring
  | succ n =>
    rw [transfer, derivative_C_mul, derivative_pow_succ, derivative_X_add_C]
    simp only [mul_one, map_mul, map_add, Nat.cast_succ, map_natCast, map_one, C_1, C_ofNat, pow_succ]
    ring

/-- The polynomial obtained by `n` applications of the paired transfer operator. -/
def transferPolynomial (s : ℕ) (t : R) : ℕ → R[X]
  | 0 => 1
  | n + 1 => transfer (s : R) t (transferPolynomial s t n)

theorem transferPolynomial_closed (s n : ℕ) (t : R) :
    transferPolynomial s t n =
      C (s.ascFactorial n : R) * (X + C t) ^ n := by
  induction n with
  | zero => simp [transferPolynomial]
  | succ n ih =>
    rw [transferPolynomial, ih, transfer_power, Nat.ascFactorial_succ]
    push_cast
    ring

/-- Evaluating the height variable at one forgets the final height. -/
theorem transferPolynomial_eval_one (s n : ℕ) (t : R) :
    (transferPolynomial s t n).eval 1 =
      (s.ascFactorial n : R) * (1 + t) ^ n := by
  rw [transferPolynomial_closed]
  simp

/-- The paired scalar total, before the covering-degree factors are restored. -/
theorem paired_total (s n : ℕ) :
    (transferPolynomial s (1 : ℕ) n).eval 1 = s.ascFactorial n * 2 ^ n := by
  simpa using transferPolynomial_eval_one s n (1 : ℕ)

/-- After the compulsory first up-step, strict paths use the paired operator with `s = 2`. -/
theorem strict_transfer_polynomial (n : ℕ) (t : R) :
    (transferPolynomial 2 t n).eval 1 = ((n + 1).factorial : R) * (1 + t) ^ n := by
  rw [transferPolynomial_eval_one]
  have h : (2 : ℕ).ascFactorial n = (n + 1).factorial := by
    simpa [Nat.add_comm] using Nat.factorial_mul_ascFactorial 1 n
  rw [h]

/-- One monomial has precisely the up, flat, and down weights stated in Section 5. -/
theorem transfer_monomial (s t a : R) (c : ℕ) :
    transfer s t (C a * X ^ c) =
      C (a * (s + c)) * X ^ (c + 1) +
        C (a * (s + 2 * c) * t) * X ^ c +
        C (a * c * t ^ 2) * X ^ (c - 1) := by
  cases c with
  | zero => simp [transfer, pow_two, mul_add, add_mul, mul_assoc] <;> ring
  | succ c =>
    rw [transfer, derivative_C_mul, derivative_X_pow_succ]
    simp only [Nat.add_sub_cancel, map_mul, map_add, Nat.cast_succ, map_natCast, map_one, C_1, C_ofNat, pow_succ]
    ring_nf <;> simp only [C_1,mul_one] <;> ring

end Paths

section MarkWeights

variable {R : Type*} [CommRing R]

/-- The two single-mark bounds combine independently of how the degree is split. -/
theorem paired_single_weight_sum (r s c u v : R) (huv : u + v = r * s) :
    (r * (s + c) - u) + (r * (s + c) - v) = r * (s + 2 * c) := by
  calc
    _ = 2 * (r * (s + c)) - (u + v) := by ring
    _ = r * (s + 2 * c) := by rw [huv]; ring

/-- The double-mark bound is `r` times the height before taking its down-step. -/
theorem paired_double_weight (r s c u v : R) (huv : u + v = r * s) :
    r * (s + c) - u - v = r * c := by
  calc
    _ = r * (s + c) - (u + v) := by ring
    _ = r * c := by rw [huv]; ring

end MarkWeights

end PaperVerification.Fermion
