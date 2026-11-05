module

public import PaperVerification.PowerRecurrence
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import TauCeti.RingTheory.MvPolynomial.Homogeneous
public import Lean.Elab.Tactic.Omega

/-!
# Homogeneous recurrence coefficients for the differential tail

Projecting the characteristic-polynomial recurrence gives coefficients of the
exact required degrees. This avoids assuming degree bounds for polynomial
division. The resulting operator relation still places multiplication before
the reversed differential operator.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open MvPolynomial
open scoped BigOperators

namespace PaperVerification.PowerOperators

variable {R ι : Type*} [CommRing R]

theorem homogeneousComponent_mul_X_pow (p : MvPolynomial ι R) (i : ι) (k d : ℕ) :
    homogeneousComponent d (p * X i ^ k) =
      if k ≤ d then homogeneousComponent (d-k) p * X i ^ k else 0 := by
  exact (isHomogeneous_X_pow i k).homogeneousComponent_mul_right p d

theorem euler_homogeneousComponent (i : ι) (p : MvPolynomial ι R) (d : ℕ) :
    euler i (homogeneousComponent d p) = homogeneousComponent d (euler i p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial a r =>
    rw [homogeneousComponent_of_mem (isHomogeneous_monomial r rfl)]
    split_ifs with ha
    · simp only [euler_apply, X_mul_pderiv_monomial, map_nsmul]
      rw [homogeneousComponent_of_mem (isHomogeneous_monomial r rfl)]
      simp only [ha, ite_true]
    · simp only [map_zero, euler_apply, X_mul_pderiv_monomial, map_nsmul]
      rw [homogeneousComponent_of_mem (isHomogeneous_monomial r rfl)]
      simp only [ha, ite_false, nsmul_zero]
  | add p q hp hq => simp only [map_add, hp, hq]

theorem euler_isHomogeneous (i : ι) {p : MvPolynomial ι R} {d : ℕ}
    (hp : p.IsHomogeneous d) : (euler i p).IsHomogeneous d := by
  have he : homogeneousComponent d (euler i p) = euler i p := by
    rw [← euler_homogeneousComponent, homogeneousComponent_eq_self hp]
  rw [← he]
  exact homogeneousComponent_isHomogeneous d _

theorem component_isHomogeneous (c lam : R) (i : ι) (k : ℕ)
    {p : MvPolynomial ι R} {d : ℕ} (hp : p.IsHomogeneous d) :
    (component c lam i k p).IsHomogeneous (d+k) := by
  rw [component_apply]
  have hq := (homogeneousSubmodule ι R d).add_mem
    ((homogeneousSubmodule ι R d).smul_mem (c + lam * (k : R)) hp)
    ((homogeneousSubmodule ι R d).smul_mem lam (euler_isHomogeneous i hp))
  simpa only [Nat.add_comm] using (isHomogeneous_X_pow i k).mul hq

theorem reversed_isHomogeneous [Fintype ι] (c : ι → R) (lam : R) (k : ℕ)
    {p : MvPolynomial ι R} {d : ℕ} (hp : p.IsHomogeneous d) :
    (reversed c lam k p).IsHomogeneous (d+k) := by
  rw [reversed_apply]
  exact IsHomogeneous.sum _ _ _ fun i _ => component_isHomogeneous (c i) lam i k hp

variable {n : ℕ}
local notation "P" => MvPolynomial (Fin n) R

def homogeneousTailCoefficient (k : ℕ) (j : Fin n) : P :=
  if j.val ≤ k then homogeneousComponent (k-j.val) (tailCoefficient k j) else 0

theorem homogeneousTailCoefficient_isHomogeneous (k : ℕ) (j : Fin n) :
    (homogeneousTailCoefficient (R := R) k j).IsHomogeneous (k-j.val) := by
  unfold homogeneousTailCoefficient
  split_ifs
  · exact homogeneousComponent_isHomogeneous _ _
  · exact isHomogeneous_zero (Fin n) R (k-j.val)

theorem homogeneousTailCoefficient_eq_zero (k : ℕ) (j : Fin n) (hj : k < j.val) :
    homogeneousTailCoefficient (R := R) k j = 0 := by
  simp only [homogeneousTailCoefficient, Nat.not_le.mpr hj, ite_false]

theorem homogeneous_power_tail_recurrence (m k : ℕ) (i : Fin n) :
    (X i : P) ^ (m+k) =
      ∑ j : Fin n, homogeneousTailCoefficient k j * X i ^ (m+j.val) := by
  have h := congrArg (homogeneousComponent (m+k))
    (power_tail_recurrence (K := R) m k i)
  rw [homogeneousComponent_eq_self (isHomogeneous_X_pow i (m+k)), map_sum] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro j _
  rw [homogeneousComponent_mul_X_pow, homogeneousTailCoefficient]
  have he : m+j.val ≤ m+k ↔ j.val ≤ k := by omega
  simp only [he, Nat.add_sub_add_left]
  split_ifs <;> simp only [zero_mul]

theorem reversed_homogeneous_tail_recurrence (c : Fin n → R) (lam : R)
    (m k : ℕ) (p : P) :
    reversed c lam (m+k) p =
      ∑ j : Fin n, reversed c lam (m+j.val) (homogeneousTailCoefficient k j * p) := by
  simp only [reversed_eq_sum_postEuler]
  simp_rw [homogeneous_power_tail_recurrence m k, Finset.sum_mul, map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring

end PaperVerification.PowerOperators
