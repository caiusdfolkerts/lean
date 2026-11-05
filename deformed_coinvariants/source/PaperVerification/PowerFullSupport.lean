module

public import PaperVerification.PowerRecurrence
public import PaperVerification.PowerParameters
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.Tactic.LinearCombination

/-!
# Full-support reduction for the weighted power tails

The characteristic-polynomial relation is applied before each coefficient
Euler operator. This keeps the multiplication order required by the paper.
It proves that the full-support ideal is hit when the tail starts at one,
and gives the exact lower-tail map for every higher starting index.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial
open scoped BigOperators

namespace PaperVerification.PowerOperators

variable {K : Type*} [Field K] {n : ℕ}
local notation "P" => MvPolynomial (Fin n) K

def fullProduct : P := ∏ i : Fin n, X i

def fullExponent : Fin n →₀ ℕ :=
  Finsupp.indicator Finset.univ (fun _ _ => 1)

@[simp] theorem fullExponent_apply (i : Fin n) : fullExponent i = 1 := by
  simp [fullExponent, Finsupp.indicator_apply]

theorem fullProduct_eq_monomial :
    fullProduct (K := K) (n := n) = monomial fullExponent 1 := by
  simpa only [fullProduct, fullExponent, pow_one] using
    (prod_X_pow (R := K) (fun _ : Fin n => 1) Finset.univ)

theorem fullProduct_homogeneous : (fullProduct (K := K) (n := n)).IsHomogeneous n := by
  simpa only [fullProduct, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one] using
    IsHomogeneous.prod (Finset.univ : Finset (Fin n))
      (fun i => (X i : P)) (fun _ => 1) (fun i _ => isHomogeneous_X K i)

theorem euler_fullProduct (i : Fin n) :
    euler i (fullProduct (K := K) (n := n)) = fullProduct := by
  rw [euler_apply, fullProduct_eq_monomial, X_mul_pderiv_monomial,
    fullExponent_apply, one_smul]

/-- An annihilating polynomial in the coordinate values gives an exact
operator relation, with its coefficient multipliers on the input side. -/
theorem reversed_annihilating_relation (c : Fin n → K) (lam : K)
    (Q : Polynomial P) (hQ : ∀ i : Fin n, Q.eval (X i) = 0)
    (ell : ℕ) (p : P) :
    ∑ k ∈ Finset.range (Q.natDegree + 1),
      reversed c lam (ell+k) (Q.coeff k * p) = 0 := by
  simp only [reversed_eq_sum_postEuler]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i _
  rw [← map_sum]
  have hs : ∑ k ∈ Finset.range (Q.natDegree + 1),
      X i ^ (ell+k) * (Q.coeff k * p) = 0 := by
    calc
      _ = X i ^ ell * (Q.eval (X i) * p) := by
        rw [Polynomial.eval_eq_sum_range, Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [pow_add]
        ring
      _ = 0 := by rw [hQ i, zero_mul, mul_zero]
  rw [hs, map_zero]

theorem parameterPolynomial_constant :
    (Fermion.parameterPolynomial (fun i : Fin n => (X i : P))).coeff 0 =
      ((-1 : K) ^ n) • fullProduct := by
  simp [Fermion.parameterPolynomial, Polynomial.coeff_zero_prod, fullProduct,
    Finset.prod_neg, Algebra.smul_def]

/-- The constant term of the characteristic relation expresses the indicated
operator image in the higher tail. -/
theorem reversed_parameter_constant_mem_tail
    (c : Fin n → K) (lam : K) (m ell : ℕ) (hm : m ≤ ell+1) (p : P) :
    reversed c lam ell
      ((Fermion.parameterPolynomial (fun i : Fin n => (X i : P))).coeff 0 * p)
        ∈ tailHit c lam m := by
  let Q := Fermion.parameterPolynomial (fun i : Fin n => (X i : P))
  have hr := reversed_annihilating_relation c lam Q
    (Fermion.parameterPolynomial_eval _) ell p
  rw [Finset.sum_range_succ'] at hr
  simp only [Nat.add_zero] at hr
  have hs : ∑ k ∈ Finset.range Q.natDegree,
      reversed c lam (ell+(k+1)) (Q.coeff (k+1) * p) ∈ tailHit c lam m := by
    apply Submodule.sum_mem
    intro k _
    exact Submodule.subset_span ⟨ell+(k+1), by omega, Q.coeff (k+1) * p, rfl⟩
  have hneg := (tailHit c lam m).neg_mem hs
  convert hneg using 1
  linear_combination hr

theorem reversed_fullProduct_mem_tail
    (c : Fin n → K) (lam : K) (m ell : ℕ) (hm : m ≤ ell+1) (p : P) :
    reversed c lam ell (fullProduct * p) ∈ tailHit c lam m := by
  have hx := reversed_parameter_constant_mem_tail c lam m ell hm p
  rw [parameterPolynomial_constant, smul_mul_assoc, map_smul] at hx
  have hs : (-1 : K) ^ n ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have h := (tailHit c lam m).smul_mem (((-1 : K)^n)⁻¹) hx
  simpa only [smul_smul, inv_mul_cancel₀ hs, one_smul] using h

/-- The zero-index operator acts on each homogeneous component by exactly
the full-subset Euler eigenvalue used in the nonresonance condition. -/
theorem reversed_zero_homogeneous (c : Fin n → K) (lam : K)
    (p : P) (d : ℕ) (hp : p.IsHomogeneous d) :
    reversed c lam 0 p = ((∑ i, c i) + lam * (d : K)) • p := by
  have he : ∑ i : Fin n, euler i p = (d : K) • p := by
    simpa only [euler_apply, Nat.cast_smul_eq_nsmul] using hp.sum_X_mul_pderiv
  simp only [reversed_eq_sum_postEuler, pow_zero, one_mul, postEuler_apply,
    Finset.sum_add_distrib, ← Finset.sum_smul, ← Finset.smul_sum, he,
    smul_smul, add_smul]

/-- All full-support homogeneous inputs are hit at tail index one. -/
theorem fullProduct_mul_homogeneous_mem_tail_one
    (hn : 0 < n) (c : Fin n → K) (lam : K)
    (hnr : Nonresonant c lam 1) (p : P) (d : ℕ) (hp : p.IsHomogeneous d) :
    fullProduct * p ∈ tailHit c lam 1 := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hx := reversed_fullProduct_mem_tail c lam 1 0 (by omega) p
  rw [reversed_zero_homogeneous c lam _ (n+d) (fullProduct_homogeneous.mul hp)] at hx
  have hs : (∑ i, c i) + lam * ((n+d : ℕ) : K) ≠ 0 := by
    exact hnr Finset.univ Finset.univ_nonempty (n+d) (by
      simp only [Finset.card_univ, Fintype.card_fin, one_mul]
      omega)
  have h := (tailHit c lam 1).smul_mem (((∑ i, c i) + lam * ((n+d : ℕ) : K))⁻¹) hx
  simpa only [smul_smul, inv_mul_cancel₀ hs, one_smul] using h

/-- The entire full-support ideal, with unrestricted polynomial degree, is hit. -/
theorem fullProduct_mul_mem_tail_one
    (hn : 0 < n) (c : Fin n → K) (lam : K)
    (hnr : Nonresonant c lam 1) (p : P) :
    fullProduct * p ∈ tailHit c lam 1 := by
  induction p using MvPolynomial.induction_on' with
  | monomial a r =>
    exact fullProduct_mul_homogeneous_mem_tail_one hn c lam hnr _ a.degree
      (isHomogeneous_monomial r rfl)
  | add p q hp hq =>
    simpa only [mul_add] using (tailHit c lam 1).add_mem hp hq

/-- Extracting the product of all variables adds exactly one Euler shift to
each coefficient; the multiplication order is verified directly. -/
theorem reversed_fullProduct (c : Fin n → K) (lam : K) (ell : ℕ) (p : P) :
    reversed c lam ell (fullProduct * p) =
      fullProduct * reversed (fun i => c i + lam) lam ell p := by
  simp only [reversed_apply, component_apply, euler_mul, euler_fullProduct,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Algebra.smul_def, map_add, map_mul]
  ring

/-- The full-support part of a higher-tail quotient is a quotient of the
entire shifted lower-tail quotient, as in equation (2.5). -/
theorem fullProduct_mul_mem_tail_of_mem_lower
    (c : Fin n → K) (lam : K) (m : ℕ) (hm : 0 < m) (p : P)
    (hp : p ∈ tailHit (fun i => c i + lam) lam (m-1)) :
    fullProduct * p ∈ tailHit c lam m := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨ell, hell, q, rfl⟩ := hp
    rw [← reversed_fullProduct]
    exact reversed_fullProduct_mem_tail c lam m ell (by omega) q
  | zero => simpa only [mul_zero] using (tailHit c lam m).zero_mem
  | add p q _ _ hp hq => simpa only [mul_add] using (tailHit c lam m).add_mem hp hq
  | smul a p _ hp => simpa only [mul_smul_comm] using (tailHit c lam m).smul_mem a hp

end PaperVerification.PowerOperators
