module

public import PaperVerification.FermionMarkedPathCore

public import PaperVerification.FermionSupport
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Tactic.LinearCombination
public import Lean.Elab.Tactic.Omega

/-!
# The literal endpoint recursion and its cleared rational identity

The endpoint equations of Section 4.3 are recorded by actual monic division.
Their rational identity is proved after clearing denominators. A separate
remainder calculation recovers every polynomial moment from the resulting
numerator, including when moment parameters coincide.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace PaperVerification.Fermion.Endpoint

open scoped BigOperators
open Polynomial

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The characteristic product with one indexed factor removed. Repeated
values of the parameters remain separate indexed factors. -/
def deletedParameterPolynomial (x : Fin n → R) (i : Fin n) : R[X] :=
  ∏ j ∈ Finset.univ.erase i, (X - C (x j))

theorem deletedParameterPolynomial_monic (x : Fin n → R) (i : Fin n) :
    (deletedParameterPolynomial x i).Monic :=
  monic_prod_of_monic _ _ fun j _ ↦ monic_X_sub_C (x j)

theorem deletedParameterPolynomial_factor (x : Fin n → R) (i : Fin n) :
    (X - C (x i)) * deletedParameterPolynomial x i = parameterPolynomial x := by
  exact Finset.mul_prod_erase Finset.univ
    (fun j : Fin n ↦ (X-C (x j) : R[X])) (Finset.mem_univ i)

theorem deletedParameterPolynomial_eq_product (x : Fin n → R) (i : Fin n) :
    deletedParameterPolynomial x i = ∏ j, if j = i then 1 else (X - C (x j)) := by
  classical
  change (∏ j ∈ Finset.univ.erase i, (X-C (x j) : R[X])) = _
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j ↦ if j = i then (1 : R[X]) else (X - C (x j))) (Finset.mem_univ i)]
  simp only [if_pos rfl, if_true, one_mul]
  apply Finset.prod_congr rfl
  intro j hj
  exact (if_neg (Finset.mem_erase.mp hj).1).symm

theorem deletedParameterPolynomial_castSucc (x : Fin (n + 1) → R) (i : Fin n) :
    deletedParameterPolynomial x i.castSucc =
      deletedParameterPolynomial (fun j ↦ x j.castSucc) i * (X - C (x (Fin.last n))) := by
  have hlast : Fin.last n ≠ i.castSucc := (Fin.castSucc_ne_last i).symm
  simp only [deletedParameterPolynomial_eq_product, Fin.prod_univ_castSucc,
    Fin.castSucc_inj, hlast, if_false]

theorem deletedParameterPolynomial_last (x : Fin (n + 1) → R) :
    deletedParameterPolynomial x (Fin.last n) =
      parameterPolynomial (fun j ↦ x j.castSucc) := by
  simp only [deletedParameterPolynomial_eq_product, Fin.prod_univ_castSucc,
    Fin.castSucc_ne_last, if_false, if_pos rfl, if_true, mul_one, parameterPolynomial]

/-- The numerator of `Σ γᵢ/(t-xᵢ)` with the full characteristic denominator. -/
def residueNumerator (x γ : Fin n → R) : R[X] :=
  ∑ i, γ i • deletedParameterPolynomial x i

theorem residueNumerator_succ (x γ : Fin (n + 1) → R) :
    residueNumerator x γ =
      (X - C (x (Fin.last n))) *
        residueNumerator (fun i ↦ x i.castSucc) (fun i ↦ γ i.castSucc) +
      C (γ (Fin.last n)) * parameterPolynomial (fun i ↦ x i.castSucc) := by
  rw [residueNumerator, Fin.sum_univ_castSucc]
  simp only [deletedParameterPolynomial_castSucc, deletedParameterPolynomial_last,
    residueNumerator, smul_eq_C_mul]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Multiplying the partial-fraction numerator by the variable removes its
constant residue at infinity and changes each weight from `γᵢ` to `γᵢ xᵢ`. -/
theorem X_mul_residueNumerator_sub_total (x γ : Fin n → R) :
    X * residueNumerator x γ - C (∑ i, γ i) * parameterPolynomial x =
      residueNumerator x (fun i ↦ γ i * x i) := by
  simp only [residueNumerator, Finset.mul_sum, map_sum, Finset.sum_mul,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← deletedParameterPolynomial_factor x i]
  simp only [smul_eq_C_mul, map_mul]
  ring

section Remainders

variable [Nontrivial R]

theorem parameterPolynomial_natDegree (x : Fin n → R) :
    (parameterPolynomial x).natDegree = n := by
  simp [parameterPolynomial]

theorem deletedParameterPolynomial_natDegree (x : Fin n → R) (i : Fin n) :
    (deletedParameterPolynomial x i).natDegree = n - 1 := by
  simp [deletedParameterPolynomial]

theorem deletedParameterPolynomial_top_coeff (x : Fin n → R) (i : Fin n) :
    (deletedParameterPolynomial x i).coeff (n - 1) = 1 := by
  rw [← deletedParameterPolynomial_natDegree x i]
  exact (deletedParameterPolynomial_monic x i).coeff_natDegree

/-- Multiplying a deleted characteristic product by a polynomial and reducing
modulo the full product is exactly scalar evaluation at the deleted parameter. -/
theorem mul_deleted_mod_characteristic (x : Fin n → R) (p : R[X]) (i : Fin n) :
    (p * deletedParameterPolynomial x i) %ₘ parameterPolynomial x =
      p.eval (x i) • deletedParameterPolynomial x i := by
  have hdiv : C (p.eval (x i)) + (X - C (x i)) * (p /ₘ (X - C (x i))) = p := by
    have h := modByMonic_add_div p (X-C (x i))
    rw [modByMonic_X_sub_C_eq_C_eval] at h
    exact h
  apply (div_modByMonic_unique (p /ₘ (X - C (x i)))
    (p.eval (x i) • deletedParameterPolynomial x i) (parameterPolynomial_monic x) ?_).2
  constructor
  · rw [smul_eq_C_mul, ← deletedParameterPolynomial_factor x i]
    linear_combination deletedParameterPolynomial x i * hdiv
  · apply (degree_smul_le _ _).trans_lt
    rw [degree_eq_natDegree (deletedParameterPolynomial_monic x i).ne_zero,
      degree_eq_natDegree (parameterPolynomial_monic x).ne_zero,
      deletedParameterPolynomial_natDegree, parameterPolynomial_natDegree]
    have hlt : n - 1 < n := by have hi := i.isLt; omega
    exact_mod_cast hlt

/-- The residue functional is an actual linear map on the polynomial ring. -/
def residueFunctional (x : Fin n → R) (p : R[X]) : R[X] →ₗ[R] R :=
  (lcoeff R (n - 1)).comp
    ((modByMonicHom (parameterPolynomial x)).comp (LinearMap.mul R R[X] p))

theorem residueFunctional_deleted (x : Fin n → R) (p : R[X]) (i : Fin n) :
    residueFunctional x p (deletedParameterPolynomial x i) = p.eval (x i) := by
  change ((p * deletedParameterPolynomial x i) %ₘ parameterPolynomial x).coeff (n - 1) = _
  rw [mul_deleted_mod_characteristic, Polynomial.coeff_smul, deletedParameterPolynomial_top_coeff,
    smul_eq_mul, mul_one]

/-- A zero cleared numerator forces every polynomial moment to vanish.
This proof uses monic remainders, not distinct roots or division by a
Vandermonde determinant. -/
theorem polynomial_moments_zero_of_residueNumerator_zero (x γ : Fin n → R)
    (h : residueNumerator x γ = 0) (p : R[X]) :
    (∑ i, p.eval (x i) * γ i) = 0 := by
  have h' := congrArg (residueFunctional x p) h
  simpa only [residueNumerator, map_sum, map_smul, residueFunctional_deleted,
    map_zero, smul_eq_mul, mul_comm] using h'

theorem power_moments_zero_of_residueNumerator_zero (x γ : Fin n → R)
    (h : residueNumerator x γ = 0) : ∀ k : ℕ, moment x γ k = 0 := by
  intro k
  simpa only [eval_pow, eval_X, moment, smul_eq_mul] using
    polynomial_moments_zero_of_residueNumerator_zero x γ h (X ^ k)

end Remainders

/-- One index of the actual paired presentation. -/
structure Datum (R : Type*) where
  node : R
  beta : R
  leftFactor : R
  rightFactor : R
  mark : Mark

def Datum.weight (d : Datum R) : R := d.beta * d.leftFactor * d.rightFactor

/-- `D,N` record the full denominator and negative weighted numerator;
`A,B` are the two endpoint polynomials in the paper. -/
structure State (R : Type*) [CommRing R] where
  A : R[X]
  B : R[X]
  D : R[X]
  N : R[X]

def initial : State R := ⟨1, 0, 1, 0⟩

def quotient (A : R[X]) (y : R) : R[X] := A /ₘ (X - C y)

def next (S : State R) (d : Datum R) : State R where
  A := match d.mark with
    | .unmarked => (X - C d.node) * S.A
    | .theta | .xi => S.A
    | .double => quotient S.A d.node
  B := match d.mark with
    | .unmarked => (X - C d.node) * S.B - C d.weight * S.A
    | .theta | .xi => S.B - C d.weight * quotient S.A d.node
    | .double => quotient (S.B - C d.weight * quotient S.A d.node) d.node
  D := (X - C d.node) * S.D
  N := (X - C d.node) * S.N - C d.weight * S.D

/-- Precisely the one or two monic-division remainders imposed at this index. -/
def relations (S : State R) (d : Datum R) : List R :=
  match d.mark with
  | .unmarked => []
  | .theta => [d.rightFactor * S.A.eval d.node]
  | .xi => [d.leftFactor * S.A.eval d.node]
  | .double => [S.A.eval d.node,
      (S.B - C d.weight * quotient S.A d.node).eval d.node]

theorem quotient_identity (A : R[X]) (y : R) :
    (X - C y) * quotient A y + C (A.eval y) = A := by
  have h := modByMonic_add_div A (X-C y)
  rw [modByMonic_X_sub_C_eq_C_eval] at h
  simpa only [quotient,add_comm] using h

/-- Every imposed single-mark factor also kills the weighted remainder. -/
theorem weight_remainder_zero (S : State R) (d : Datum R)
    (h : ∀ r ∈ relations S d, r = 0) (hm : d.mark = .theta ∨ d.mark = .xi) :
    d.weight * S.A.eval d.node = 0 := by
  rcases hm with hm | hm
  · have hr : d.rightFactor * S.A.eval d.node = 0 := h _ (by simp [relations, hm])
    calc
      _ = (d.beta * d.leftFactor) * (d.rightFactor * S.A.eval d.node) := by
        simp only [Datum.weight, mul_assoc]
      _ = 0 := by rw [hr, mul_zero]
  · have hr : d.leftFactor * S.A.eval d.node = 0 := h _ (by simp [relations, hm])
    calc
      _ = (d.beta * d.rightFactor) * (d.leftFactor * S.A.eval d.node) := by
        unfold Datum.weight
        ring
      _ = 0 := by rw [hr, mul_zero]

/-- The endpoint update preserves its exact rational identity after clearing
the full denominator. No node or selected coefficient is cancelled. -/
theorem next_identity (S : State R) (d : Datum R)
    (hS : S.D * S.B = S.A * S.N) (h : ∀ r ∈ relations S d, r = 0) :
    (next S d).D * (next S d).B = (next S d).A * (next S d).N := by
  have hdiv := quotient_identity S.A d.node
  cases hm : d.mark with
  | unmarked =>
    simp only [next, hm]
    linear_combination (X - C d.node) ^ 2 * hS
  | theta =>
    have hz : C d.weight * C (S.A.eval d.node) = (0 : R[X]) := by
      rw [← map_mul, weight_remainder_zero S d h (Or.inl hm), map_zero]
    simp only [next, hm]
    linear_combination (X - C d.node) * hS - C d.weight * S.D * hdiv + S.D * hz
  | xi =>
    have hz : C d.weight * C (S.A.eval d.node) = (0 : R[X]) := by
      rw [← map_mul, weight_remainder_zero S d h (Or.inr hm), map_zero]
    simp only [next, hm]
    linear_combination (X - C d.node) * hS - C d.weight * S.D * hdiv + S.D * hz
  | double =>
    have hρ : S.A.eval d.node = 0 := h _ (by simp [relations, hm])
    have hτ : (S.B - C d.weight * quotient S.A d.node).eval d.node = 0 :=
      h _ (by simp [relations, hm])
    rw [hρ, map_zero, add_zero] at hdiv
    have hdivB := quotient_identity (S.B - C d.weight * quotient S.A d.node) d.node
    rw [hτ, map_zero, add_zero] at hdivB
    simp only [next, hm]
    linear_combination S.D * hdivB + hS - S.N * hdiv

def run (data : ℕ → Datum R) : ℕ → State R
  | 0 => initial
  | k + 1 => next (run data k) (data k)

def allRelations (data : ℕ → Datum R) : ℕ → List R
  | 0 => []
  | k + 1 => allRelations data k ++ relations (run data k) (data k)

theorem run_identity (data : ℕ → Datum R) (k : ℕ)
    (h : ∀ r ∈ allRelations data k, r = 0) :
    (run data k).D * (run data k).B = (run data k).A * (run data k).N := by
  revert h
  induction k with
  | zero => intro h; simp [run, initial]
  | succ k ih =>
    intro h
    apply next_identity
    · exact ih fun r hr ↦ h r (List.mem_append_left _ hr)
    · exact fun r hr ↦ h r (List.mem_append_right _ hr)

theorem run_denominator (data : ℕ → Datum R) (k : ℕ) :
    (run data k).D = parameterPolynomial (fun i : Fin k ↦ (data i).node) := by
  induction k with
  | zero => simp [run, initial, parameterPolynomial]
  | succ k ih =>
    simp only [run, next, ih, parameterPolynomial, Fin.prod_univ_castSucc,
      Fin.val_castSucc, Fin.val_last]
    rw [mul_comm]

theorem run_numerator (data : ℕ → Datum R) (k : ℕ) :
    (run data k).N =
      -residueNumerator (fun i : Fin k ↦ (data i).node) (fun i ↦ (data i).weight) := by
  induction k with
  | zero => simp [run, initial, residueNumerator]
  | succ k ih =>
    simp only [run, next, ih, run_denominator, residueNumerator_succ,
      Fin.val_castSucc, Fin.val_last]
    ring

end PaperVerification.Fermion.Endpoint
