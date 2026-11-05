module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Tactic.Ring

/-!
# Weighted power operators and their commutator

These are the genuine polynomial differential operators of Section 2 of the
deformed-coinvariant paper. In particular, the reversed operator differentiates
the product by the power of the variable. The definitions are linear maps, and
their joint image is a vector submodule rather than a polynomial ideal.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open MvPolynomial
open scoped BigOperators

namespace PaperVerification.PowerOperators

variable {R ι : Type*} [CommRing R]
local instance : DecidableEq ι := Classical.decEq ι

/-- The coordinate Euler derivation `X_i ∂_i`, viewed as a linear map. -/
def euler (i : ι) : MvPolynomial ι R →ₗ[R] MvPolynomial ι R :=
  (LinearMap.mulLeft R (X i)).comp (pderiv i).toLinearMap

@[simp] theorem euler_apply (i : ι) (p : MvPolynomial ι R) :
    euler i p = X i * pderiv i p := rfl

theorem euler_mul (i : ι) (p q : MvPolynomial ι R) :
    euler i (p * q) = euler i p * q + p * euler i q := by
  simp only [euler_apply, pderiv_mul]
  ring

theorem euler_pow (i j : ι) (k : ℕ) :
    euler (R := R) i (X j ^ k) = (if i = j then (k : R) else 0) • (X j ^ k) := by
  classical
  cases k with
  | zero => simp [euler_apply]
  | succ k =>
    by_cases hij : i = j
    · subst j
      rw [euler_apply, pderiv_pow, pderiv_X_self, mul_one]
      simp only [Nat.succ_sub_one, ite_true, Algebra.smul_def, map_natCast]
      rw [pow_succ]
      ring
    · simp [euler_apply, pderiv_pow, pderiv_X_of_ne (Ne.symm hij), hij]

theorem euler_pow_mul (i j : ι) (k : ℕ) (p : MvPolynomial ι R) :
    euler i (X j ^ k * p) =
      (if i = j then (k : R) else 0) • (X j ^ k * p) + X j ^ k * euler i p := by
  classical
  rw [euler_mul, euler_pow, smul_mul_assoc]

theorem euler_comm (i j : ι) (p : MvPolynomial ι R) :
    euler i (euler j p) = euler j (euler i p) := by
  classical
  by_cases hij : i = j
  · subst j; rfl
  · simp only [euler_apply, pderiv_mul, pderiv_X_of_ne hij,
      pderiv_X_of_ne (Ne.symm hij), zero_mul, zero_add]
    rw [pderiv_comm i j p]
    ring

/-- One summand of the reversed weighted power operator, in expanded Euler form. -/
def component (c lam : R) (i : ι) (k : ℕ) :
    MvPolynomial ι R →ₗ[R] MvPolynomial ι R :=
  (LinearMap.mulLeft R (X i ^ k)).comp
    ((c + lam * (k : R)) • LinearMap.id + lam • euler i)

@[simp] theorem component_apply (c lam : R) (i : ι) (k : ℕ) (p : MvPolynomial ι R) :
    component c lam i k p = X i ^ k * ((c + lam * (k : R)) • p + lam • euler i p) := rfl

/-- This equality checks the order of multiplication and differentiation. -/
theorem component_eq_reversed (c lam : R) (i : ι) (k : ℕ) (p : MvPolynomial ι R) :
    component c lam i k p = c • (X i ^ k * p) + lam • euler i (X i ^ k * p) := by
  classical
  rw [component_apply, euler_pow_mul]
  simp only [ite_true]
  simp [Algebra.smul_def]
  ring

/-- The same-coordinate commutator, without characteristic assumptions. -/
theorem component_commutator_same (c lam : R) (i : ι) (a b : ℕ)
    (p : MvPolynomial ι R) :
    component c lam i a (component c lam i b p) -
      component c lam i b (component c lam i a p) =
      (lam * ((b : R) - (a : R))) • component c lam i (a + b) p := by
  classical
  simp only [component_apply, euler_pow_mul, ite_true, map_add, map_smul,
    Nat.cast_add]
  simp only [Algebra.smul_def, map_add, map_mul, map_sub, pow_add]
  ring

/-- Different-coordinate summands commute. -/
theorem component_commute_of_ne (c d lam : R) (i j : ι) (hij : i ≠ j) (a b : ℕ)
    (p : MvPolynomial ι R) :
    component c lam i a (component d lam j b p) =
      component d lam j b (component c lam i a p) := by
  classical
  simp only [component_apply, euler_pow_mul, ite_eq_right hij,
    ite_eq_right (Ne.symm hij), zero_smul, zero_add, map_add, map_smul]
  rw [euler_comm i j p]
  simp only [Algebra.smul_def, map_add, map_mul]
  ring

variable [Fintype ι]

/-- The reversed family `B_k = ∑ (c_i + lamE_i) M_(X_i^k)`. -/
def reversed (c : ι → R) (lam : R) (k : ℕ) :
    MvPolynomial ι R →ₗ[R] MvPolynomial ι R :=
  ∑ i, component (c i) lam i k

@[simp] theorem reversed_apply (c : ι → R) (lam : R) (k : ℕ)
    (p : MvPolynomial ι R) :
    reversed c lam k p = ∑ i, component (c i) lam i k p := by
  simp [reversed]

/-- The original family `A_k = ∑ M_(X_i^k) (c_i + lamE_i)`. -/
def original (c : ι → R) (lam : R) (k : ℕ) :
    MvPolynomial ι R →ₗ[R] MvPolynomial ι R :=
  ∑ i, (LinearMap.mulLeft R (X i ^ k)).comp
    (c i • LinearMap.id + lam • euler i)

/-- The literal vector-space sum of the images of every operator in a tail. -/
def tailHit (c : ι → R) (lam : R) (m : ℕ) : Submodule R (MvPolynomial ι R) :=
  Submodule.span R {p | ∃ k, m ≤ k ∧ ∃ q, p = reversed c lam k q}

/-- The commutator identity supplying the deformed Koszul relation in Section 2.1. -/
theorem reversed_commutator (c : ι → R) (lam : R) (a b : ℕ)
    (p : MvPolynomial ι R) :
    reversed c lam a (reversed c lam b p) - reversed c lam b (reversed c lam a p) =
      (lam * ((b : R) - (a : R))) • reversed c lam (a + b) p := by
  classical
  have hterm (i j : ι) :
      component (c i) lam i a (component (c j) lam j b p) -
        component (c j) lam j b (component (c i) lam i a p) =
      if i = j then
        (lam * ((b : R) - (a : R))) • component (c i) lam i (a + b) p else 0 := by
    by_cases hij : i = j
    · subst j
      simpa only [ite_true] using component_commutator_same (c i) lam i a b p
    · rw [ite_eq_right hij, component_commute_of_ne (c i) (c j) lam i j hij a b p,
        sub_self]
  calc
    _ = ∑ i, ∑ j,
        (component (c i) lam i a (component (c j) lam j b p) -
          component (c j) lam j b (component (c i) lam i a p)) := by
      simp only [reversed_apply, map_sum, Finset.sum_sub_distrib]
      congr 1
      exact Finset.sum_comm
    _ = ∑ i, (lam * ((b : R) - (a : R))) • component (c i) lam i (a + b) p := by
      simp_rw [hterm]
      simp
    _ = _ := by rw [reversed_apply, Finset.smul_sum]

end PaperVerification.PowerOperators
