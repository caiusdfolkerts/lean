module

public import VolumePolynomials.BodyOperations
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.Polynomial.Roots

@[expose] public section

set_option autoImplicit false
noncomputable section

/-! The literal binomially normalized binary polynomial and its unique
coefficient sequence. Only the entries from zero through the degree occur. -/

open Set MeasureTheory Polynomial
open scoped Pointwise BigOperators

namespace VolumePolynomials.BinarySimplex

def value (d : ℕ) (a : ℕ → ℝ) (t s : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (d + 1), (d.choose i : ℝ) * a i * t ^ (d - i) * s ^ i

def Realizes (d : ℕ) (a : ℕ → ℝ) (K L : Body d) : Prop :=
  ∀ t s : ℝ, 0 ≤ t → 0 ≤ s → bodyVolume (t • K + s • L) = value d a t s

def univariate (d : ℕ) (a : ℕ → ℝ) : Polynomial ℝ :=
  ∑ i ∈ Finset.range (d + 1), Polynomial.monomial i ((d.choose i : ℝ) * a i)

theorem eval_univariate (d : ℕ) (a : ℕ → ℝ) (s : ℝ) :
    (univariate d a).eval s = value d a 1 s := by
  first
  | simp only [univariate, Polynomial.eval_finsetSum, Polynomial.eval_monomial,
      value, one_pow, mul_one]

theorem coeff_univariate {d i : ℕ} (a : ℕ → ℝ) (hi : i ≤ d) :
    (univariate d a).coeff i = (d.choose i : ℝ) * a i := by
  first
  | simp [univariate, Polynomial.coeff_monomial, Finset.mem_range.mpr (show i < d + 1 by omega)]

theorem sequence_eq_of_value_eq {d : ℕ} {a b : ℕ → ℝ}
    (h : ∀ s : ℝ, 0 ≤ s → value d a 1 s = value d b 1 s) :
    ∀ i ≤ d, a i = b i := by
  first
  | have hp : univariate d a = univariate d b := by
      first
      | apply Polynomial.eq_of_infinite_eval_eq
        apply (Set.Ici_infinite (0 : ℝ)).mono
        intro s hs
        simpa only [Set.mem_setOf_eq, eval_univariate] using h s hs
    intro i hi
    have hc := congrArg (fun p : Polynomial ℝ => p.coeff i) hp
    rw [coeff_univariate a hi, coeff_univariate b hi] at hc
    have hchoose : (d.choose i : ℝ) ≠ 0 := by
      first
      | exact_mod_cast (Nat.choose_pos hi).ne'
    exact mul_left_cancel₀ hchoose hc

theorem Realizes.unique {d : ℕ} {a b : ℕ → ℝ} {K L : Body d}
    (ha : Realizes d a K L) (hb : Realizes d b K L) : ∀ i ≤ d, a i = b i :=
  sequence_eq_of_value_eq (fun s hs => (ha 1 s zero_le_one hs).symm.trans (hb 1 s zero_le_one hs))

end VolumePolynomials.BinarySimplex
