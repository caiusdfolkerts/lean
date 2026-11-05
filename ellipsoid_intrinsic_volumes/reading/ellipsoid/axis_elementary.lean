module

public import Ellipsoid.NormalOffsetJacobian
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Polynomial.Derivative

@[expose] public section

noncomputable section

open Polynomial Finset
open scoped BigOperators

namespace EllipsoidVerification

def elementaryOn {ι : Type*} (s : Finset ι) (d : ι → ℝ) (k : ℕ) : ℝ :=
  (∏ i ∈ s, (1 + C (d i) * X)).coeff k

theorem elementaryOn_nonneg {ι : Type*} [DecidableEq ι] (s : Finset ι) (d : ι → ℝ)
    (hd : ∀ i ∈ s, 0 ≤ d i) (k : ℕ) : 0 ≤ elementaryOn s d k := by
  induction s using Finset.induction_on generalizing k with
  | empty =>
      by_cases hk : k = 0 <;> simp [elementaryOn, Polynomial.coeff_one, hk]
  | @insert i s hi ih =>
      rw [elementaryOn, Finset.prod_insert hi, Polynomial.coeff_mul]
      apply Finset.sum_nonneg
      intro p hp
      apply mul_nonneg
      · have hdi := hd i (Finset.mem_insert_self i s)
        simp only [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_C_mul_X]
        split_ifs <;> linarith
      · exact ih (fun j hj => hd j (Finset.mem_insert_of_mem hj)) p.2

theorem elementaryOn_scaling {ι : Type*} (s : Finset ι) (d : ι → ℝ) (c : ℝ) (k : ℕ) :
    elementaryOn s (fun i => c * d i) k = c ^ k * elementaryOn s d k := by
  have hp : (∏ i ∈ s, (1 + C (c * d i) * X)) =
      (∏ i ∈ s, (1 + C (d i) * X)).comp (C c * X) := by
    rw [Polynomial.prod_comp]
    apply Finset.prod_congr rfl
    intro i hi
    simp [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_mul]
    ring
  rw [elementaryOn, hp, Polynomial.comp_C_mul_X_coeff]
  exact mul_comm _ _

theorem coeff_prod_X_add_C {ι : Type*} [DecidableEq ι] (s : Finset ι) (d : ι → ℝ)
    {k : ℕ} (hk : k ≤ s.card) :
    (∏ i ∈ s, (X + C (d i))).coeff (s.card - k) = elementaryOn s d k := by
  have hone : (1 : ℝ[X]).reverse = 1 := by
    simpa only [Polynomial.C_1] using Polynomial.reverse_C (1 : ℝ)
  have hX : (X : ℝ[X]).reverse = 1 := by
    simpa only [mul_one, hone] using Polynomial.reverse_X_mul (1 : ℝ[X])
  have hrev (s : Finset ι) : (∏ i ∈ s, (X + C (d i))).reverse =
      ∏ i ∈ s, (1 + C (d i) * X) := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.prod_empty, hone]
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi, Polynomial.reverse_mul_of_domain, ih]
      simp [hX]
  have hn : (∏ i ∈ s, (X + C (d i))).natDegree = s.card := by
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun i hi => Polynomial.monic_X_add_C _)]
    simp
  rw [elementaryOn, ← hrev, Polynomial.coeff_reverse, hn, Polynomial.revAt_le hk]

theorem elementaryOn_erase {ι : Type*} [DecidableEq ι] (s : Finset ι) (d : ι → ℝ)
    {i : ι} (hi : i ∈ s) {k : ℕ} (hk : 0 < k) :
    elementaryOn s d k = elementaryOn (s.erase i) d k + d i * elementaryOn (s.erase i) d (k - 1) := by
  rw [elementaryOn, ← Finset.mul_prod_erase s (fun i => 1 + C (d i) * X) hi,
    add_mul, one_mul, mul_assoc, Polynomial.coeff_add, Polynomial.coeff_C_mul]
  congr 1
  rw [show k = (k - 1) + 1 by omega, Polynomial.coeff_X_mul]
  rfl

theorem elementaryOn_euler {ι : Type*} [DecidableEq ι] (s : Finset ι) (d : ι → ℝ)
    {k : ℕ} (hk : 0 < k) :
    (∑ i ∈ s, d i * elementaryOn (s.erase i) d (k - 1)) = (k : ℝ) * elementaryOn s d k := by
  have h := congrArg (fun p : ℝ[X] => p.coeff (k - 1))
    (Polynomial.derivative_prod_finset (s := s) (f := fun i => 1 + C (d i) * X))
  simp only [Polynomial.coeff_derivative, Polynomial.derivative_add,
    Polynomial.derivative_one, Polynomial.derivative_C_mul, Polynomial.derivative_X,
    mul_one, zero_add, Polynomial.finsetSum_coeff, Polynomial.coeff_mul_C,
    Nat.sub_add_cancel hk] at h
  have hcast : ((k - 1 : ℕ) : ℝ) + 1 = k := by
    rw [Nat.cast_sub hk, Nat.cast_one]
    ring
  simpa only [elementaryOn, mul_comm, hcast] using h.symm

theorem axisCoefficientPolynomial_natDegree_le {n : ℕ} (a : Fin n → ℝ) :
    (axisCoefficientPolynomial a).natDegree ≤ n := by
  apply (Polynomial.natDegree_prod_le _ _).trans
  have h (i : Fin n) : (1 + C (a i ^ 2) * X).natDegree ≤ 1 := by
    apply Polynomial.natDegree_add_le_of_degree_le (by simp)
    exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
  exact (Finset.sum_le_sum fun i hi => h i).trans_eq (by simp)

theorem axisCoefficients_admissible {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) :
    coefficientAdmissible (axisCoefficients a) := by
  refine ⟨fun j => elementaryOn_nonneg Finset.univ (fun i => a i ^ 2)
    (fun i hi => sq_nonneg _) _, ?_, ?_⟩
  · simp [axisCoefficients, axisCoefficientPolynomial, Polynomial.coeff_zero_prod]
  · have h := Polynomial.coeff_prod_of_natDegree_le (s := Finset.univ)
      (fun i : Fin n => 1 + C (a i ^ 2) * X) 1 (fun i hi => by
        apply Polynomial.natDegree_add_le_of_degree_le (by simp)
        exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp))
    simp only [Finset.card_univ, Fintype.card_fin, mul_one] at h
    change 0 < (axisCoefficientPolynomial a).coeff n
    rw [axisCoefficientPolynomial, h]
    simp only [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_C_mul_X,
      if_false, one_ne_zero, if_true, zero_add]
    exact Finset.prod_pos fun i _ => sq_pos_of_pos (ha i)

theorem coefficientPolynomial_axisCoefficients {n : ℕ} (a : Fin n → ℝ) (t : ℝ) :
    coefficientPolynomial (axisCoefficients a) t = ∏ i, (1 + a i ^ 2 * t ^ 2) := by
  have h := Polynomial.eval_eq_sum_range'
    (Nat.lt_succ_of_le (axisCoefficientPolynomial_natDegree_le a)) (t ^ 2)
  rw [axisCoefficientPolynomial, Polynomial.eval_prod] at h
  simp only [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X] at h
  rw [h]
  simp only [coefficientPolynomial, axisCoefficients, ← pow_mul]
  exact Fin.sum_univ_eq_sum_range
    (fun j : ℕ => (axisCoefficientPolynomial a).coeff j * t ^ (2 * j)) (n + 1)

def axisA {n : ℕ} (a : Fin n → ℝ) (k : ℕ) (x : Space n) : ℝ :=
  ∑ i, a i ^ 2 * (x i) ^ 2 * elementaryOn (Finset.univ.erase i) (fun j => a j ^ 2) (k - 1)

def axisC {n : ℕ} (a : Fin n → ℝ) (k : ℕ) (x : Space n) : ℝ :=
  ∑ i, a i ^ 2 * (x i) ^ 2 * elementaryOn (Finset.univ.erase i) (fun j => a j ^ 2) k

theorem axisC_identity {n k : ℕ} (a : Fin n → ℝ) (hk : 0 < k) (x : Space n) :
    axisC a k x = elementaryOn Finset.univ (fun i => a i ^ 2) k * axisSupport a x ^ 2 -
      ∑ i, (a i ^ 2) ^ 2 * (x i) ^ 2 *
        elementaryOn (Finset.univ.erase i) (fun j => a j ^ 2) (k - 1) := by
  rw [axisSupport_sq, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [elementaryOn_erase Finset.univ (fun j => a j ^ 2) (Finset.mem_univ i) hk]
  ring

end EllipsoidVerification
