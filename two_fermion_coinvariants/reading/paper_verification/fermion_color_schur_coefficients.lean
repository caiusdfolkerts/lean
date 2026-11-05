module

public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Lean.Elab.Tactic.Omega

/-!
# Exact binomial-difference coefficients for two-color tensor powers

The j=0 convention is explicit: the binomial
coefficient with lower index -1 is zero, not the natural subtraction 0-1.
The coefficient calculation is valid for every tensor length. It is a
combinatorial dependency of the representation decomposition; it does not
by itself assert irreducibility or identify a transported group action.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace PaperVerification.Fermion.ColorSchur

open Polynomial

def precedingChoose (ell j : ℕ) : ℕ := if j=0 then 0 else ell.choose (j-1)

/-- The exact nonnegative binomial difference in the paper. -/
def ballotMultiplicity (ell j : ℕ) : ℕ := ell.choose j-precedingChoose ell j

theorem precedingChoose_le (ell j : ℕ) (hj : j≤ell/2) :
    precedingChoose ell j≤ell.choose j := by
  cases j with
  | zero => simp [precedingChoose]
  | succ j =>
      simp only [precedingChoose,Nat.succ_ne_zero,if_false,Nat.succ_sub_one]
      exact Nat.choose_le_succ_of_lt_half_left (by omega)

theorem ballotMultiplicity_cast (ell j : ℕ) (hj : j≤ell/2) :
    (ballotMultiplicity ell j : ℤ)=
      (ell.choose j : ℤ)-(precedingChoose ell j : ℤ) :=
  Nat.cast_sub (precedingChoose_le ell j hj)

/-- The binomial differences telescope without any out-of-range convention. -/
theorem sum_ballotMultiplicity (ell k : ℕ) (hk : k≤ell/2) :
    ∑ j∈Finset.range (k+1),ballotMultiplicity ell j=ell.choose k := by
  induction k with
  | zero => simp [ballotMultiplicity,precedingChoose]
  | succ k ih =>
      rw [Finset.sum_range_succ,ih (by omega)]
      have hle := Nat.choose_le_succ_of_lt_half_left (n := ell) (r := k) (by omega)
      simp only [ballotMultiplicity,precedingChoose,Nat.succ_ne_zero,if_false,
        Nat.succ_sub_one]
      omega

def geometricPolynomial (d : ℕ) : Polynomial ℕ :=
  ∑ i∈Finset.range (d+1),X^i

@[simp] theorem geometricPolynomial_coeff (d k : ℕ) :
    (geometricPolynomial d).coeff k=if k≤d then 1 else 0 := by
  simp [geometricPolynomial,Polynomial.finsetSum_coeff,Polynomial.coeff_X_pow,
    Finset.sum_ite_eq',Nat.lt_succ_iff,eq_comm]

/-- At the diagonal (1,t), Sym^(ell-2j) times det^j has this polynomial. -/
def schurWindow (ell j : ℕ) : Polynomial ℕ :=
  X^j*geometricPolynomial (ell-2*j)

theorem schurWindow_coeff (ell j k : ℕ) (hj : j≤ell/2) :
    (schurWindow ell j).coeff k=if j≤k ∧ k≤ell-j then 1 else 0 := by
  rw [schurWindow,Polynomial.coeff_X_pow_mul',geometricPolynomial_coeff]
  split_ifs <;> omega

/-- The complete two-color tensor-power expansion, proved coefficientwise
over the natural numbers. No finite-instance computation is used. -/
theorem tensor_power_schur_polynomial (ell : ℕ) :
    (1+X : Polynomial ℕ)^ell=
      ∑ j∈Finset.range (ell/2+1),C (ballotMultiplicity ell j)*schurWindow ell j := by
  ext k
  rw [Polynomial.coeff_one_add_X_pow,Polynomial.finsetSum_coeff]
  have hcoeff :
      (∑ j∈Finset.range (ell/2+1),
        (C (ballotMultiplicity ell j)*schurWindow ell j).coeff k)=
      ∑ j∈Finset.range (ell/2+1),
        if j≤k ∧ k≤ell-j then ballotMultiplicity ell j else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Polynomial.coeff_C_mul,schurWindow_coeff ell j k (by
      have := Finset.mem_range.mp hj
      omega)]
    split_ifs <;> simp only [mul_one,mul_zero]
  rw [hcoeff]
  by_cases hk : k≤ell
  · let m := min k (ell-k)
    have hm : m≤ell/2 := by dsimp only [m]; omega
    have he : (Finset.range (ell/2+1)).filter (fun j ↦ j≤k ∧ k≤ell-j)=
        Finset.range (m+1) := by
      ext j
      simp only [Finset.mem_filter,Finset.mem_range]
      dsimp only [m]
      omega
    rw [←Finset.sum_filter,he,sum_ballotMultiplicity ell m hm]
    by_cases hkm : k≤ell-k
    · simp only [m,min_eq_left hkm,Nat.cast_id]
    · rw [show m=ell-k by exact min_eq_right (by omega)]
      exact (Nat.choose_symm hk).symm
  · rw [Nat.choose_eq_zero_of_lt (by omega : ell<k)]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro j hj
    rw [if_neg]
    omega

end PaperVerification.Fermion.ColorSchur
