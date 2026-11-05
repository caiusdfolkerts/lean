module
public import VolumePolynomials.Definitions
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.List.FinRange
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Tactic.Positivity
public import Lean.Elab.Tactic.Omega

@[expose] public section

set_option autoImplicit false

/-!
# Explicit rational extraction of every coefficient

Substitution `tᵢ = z^((d+2)^i)` sends distinct degree-`d` monomials to distinct
powers of `z`, all below `(d+2)^n`. Ordinary univariate Lagrange interpolation
at the positive integers then extracts every coefficient by a fixed rational
linear combination of volume evaluations. The larger sampling set avoids
any unproved multivariate interpolation theorem.
-/

open Finset Polynomial
open scoped BigOperators

namespace VolumePolynomials

def coefficientCode {n d : ℕ} (α : MultiIndex n d) : ℕ :=
  Nat.ofDigits (d + 2) (List.ofFn fun i => (α.1 i : ℕ))

def interpolationSize (n d : ℕ) : ℕ := (d + 2) ^ n

theorem coefficientCode_lt {n d : ℕ} (α : MultiIndex n d) :
    coefficientCode α < interpolationSize n d := by
  first
  | have h := Nat.ofDigits_lt_base_pow_length (b := d + 2) (by omega)
      (l := List.ofFn fun i => (α.1 i : ℕ)) (by
        intro k hk
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hk
        exact (α.1 i).isLt.trans (by omega))
    simpa only [coefficientCode, interpolationSize, List.length_ofFn] using h

theorem coefficientCode_injective (n d : ℕ) :
    Function.Injective (coefficientCode (n := n) (d := d)) := by
  first
  | intro α β h
    have hlist := Nat.ofDigits_inj_of_len_eq (b := d + 2) (by omega)
      (by simp : (List.ofFn fun i => (α.1 i : ℕ)).length =
        (List.ofFn fun i => (β.1 i : ℕ)).length)
      (by
        intro k hk
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hk
        exact (α.1 i).isLt.trans (by omega))
      (by
        intro k hk
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hk
        exact (β.1 i).isLt.trans (by omega)) h
    have hfun := List.ofFn_injective hlist
    apply Subtype.ext
    funext i
    exact Fin.ext (congrFun hfun i)

theorem coefficientCode_eq_sum {n d : ℕ} (α : MultiIndex n d) :
    coefficientCode α = ∑ i : Fin n, (α.1 i : ℕ) * (d + 2) ^ (i : ℕ) := by
  first
  | have hmap : (List.ofFn fun i => (α.1 i : ℕ)).mapIdx
        (fun i a => a * (d + 2) ^ i) =
        List.ofFn (fun i : Fin n => (α.1 i : ℕ) * (d + 2) ^ (i : ℕ)) := by
      apply List.ext_getElem
      · simp
      · intro i hi hi'
        simp
    rw [coefficientCode, Nat.ofDigits_eq_sum_mapIdx, hmap, List.sum_ofFn]

def interpolationNode {n d : ℕ} (j : Fin (interpolationSize n d)) : ℚ :=
  (j.val : ℚ) + 1

def interpolationWeight {n d : ℕ} (j : Fin (interpolationSize n d)) (i : Fin n) : ℚ :=
  interpolationNode j ^ ((d + 2) ^ (i : ℕ))

/-- Coefficients of the product of the normalized linear factors
`(X-a)/(x-a)`. This recursion uses only executable rational arithmetic. -/
def lagrangeCoefficient (x : ℚ) : List ℚ → ℕ → ℚ
  | [], m => if m = 0 then 1 else 0
  | a :: l, 0 => (x - a)⁻¹ * (-(a * lagrangeCoefficient x l 0))
  | a :: l, m + 1 =>
      (x - a)⁻¹ * (lagrangeCoefficient x l m - a * lagrangeCoefficient x l (m + 1))

theorem lagrangeCoefficient_eq (x : ℚ) (l : List ℚ) (m : ℕ) :
    lagrangeCoefficient x l m =
      ((l.map (Lagrange.basisDivisor x)).prod).coeff m := by
  first
  | induction l generalizing m with
    | nil => simp [lagrangeCoefficient, Polynomial.coeff_one]
    | cons a l ih =>
        cases m with
        | zero =>
            simp only [lagrangeCoefficient, List.map_cons, List.prod_cons,
              Lagrange.basisDivisor, mul_assoc, sub_mul, Polynomial.coeff_C_mul,
              Polynomial.coeff_sub, Polynomial.coeff_X_mul_zero, zero_sub, ih]
        | succ m =>
            simp only [lagrangeCoefficient, List.map_cons, List.prod_cons,
              Lagrange.basisDivisor, mul_assoc, sub_mul, Polynomial.coeff_C_mul,
              Polynomial.coeff_sub, Polynomial.coeff_X_mul, ih]

/-- Every arithmetic entry is rational, with a finite, executable formula.
The definition does not call Mathlib's noncomputable polynomial operations. -/
def coefficientExtractionWeight {n d : ℕ} (α : MultiIndex n d)
    (j : Fin (interpolationSize n d)) : ℚ :=
  lagrangeCoefficient (interpolationNode j)
    (((List.finRange (interpolationSize n d)).filter (fun k => decide (k ≠ j))).map
      interpolationNode) (coefficientCode α)

/-- The executable recursion computes the exact Lagrange coefficient. -/
theorem coefficientExtractionWeight_eq {n d : ℕ} (α : MultiIndex n d)
    (j : Fin (interpolationSize n d)) :
    coefficientExtractionWeight α j =
      (Lagrange.basis Finset.univ (interpolationNode (n := n) (d := d)) j).coeff
        (coefficientCode α) := by
  first
  | let l := (List.finRange (interpolationSize n d)).filter (fun k => decide (k ≠ j))
    have hl : l.Nodup := (List.nodup_finRange _).filter _
    have hs : l.toFinset = (Finset.univ : Finset (Fin (interpolationSize n d))).erase j := by
      ext k
      simp [l, and_comm]
    unfold coefficientExtractionWeight
    rw [lagrangeCoefficient_eq]
    simp only [List.map_map]
    rw [← List.prod_toFinset _ hl, hs]
    rfl

theorem interpolationNode_pos {n d : ℕ} (j : Fin (interpolationSize n d)) :
    0 < interpolationNode j := by
  first
  | dsimp [interpolationNode]
    positivity

theorem interpolationWeight_pos {n d : ℕ} (j : Fin (interpolationSize n d)) (i : Fin n) :
    0 < interpolationWeight j i := pow_pos (interpolationNode_pos j) _

noncomputable def codedPolynomial {n d : ℕ} (c : Coefficients n d) : Polynomial ℝ :=
  ∑ α, Polynomial.monomial (coefficientCode α) (c α)

theorem codedPolynomial_coeff {n d : ℕ} (c : Coefficients n d) (α : MultiIndex n d) :
    (codedPolynomial c).coeff (coefficientCode α) = c α := by
  first
  | classical
    simp only [codedPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
      (coefficientCode_injective n d).eq_iff]
    simp

theorem codedPolynomial_degree_lt {n d : ℕ} (c : Coefficients n d) :
    (codedPolynomial c).degree < interpolationSize n d := by
  first
  | classical
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intro m hm
    rw [codedPolynomial, Polynomial.finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro α _
    exact Polynomial.coeff_monomial_of_ne (c α)
      (ne_of_gt ((coefficientCode_lt α).trans_le hm))

theorem codedPolynomial_eval {n d : ℕ} (c : Coefficients n d) (z : ℝ) :
    (codedPolynomial c).eval z = evaluate c (fun i => z ^ ((d + 2) ^ (i : ℕ))) := by
  first
  | classical
    simp only [codedPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial, evaluate]
    apply Finset.sum_congr rfl
    intro α _
    rw [coefficientCode_eq_sum, ← Finset.prod_pow_eq_pow_sum]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    rw [← pow_mul, Nat.mul_comm]

theorem map_rational_lagrange_basis {n d : ℕ}
    (j : Fin (interpolationSize n d)) :
    Polynomial.map (algebraMap ℚ ℝ)
      (Lagrange.basis Finset.univ (interpolationNode (n := n) (d := d)) j) =
      Lagrange.basis Finset.univ (fun k : Fin (interpolationSize n d) =>
        (interpolationNode k : ℝ)) j := by
  first
  | classical
    simp [Lagrange.basis, Lagrange.basisDivisor, Polynomial.map_prod,
      Polynomial.map_mul, Polynomial.map_sub]

/-- Exact coefficient recovery from a fixed finite list of strictly positive
integer weight vectors. There is no coefficient omission or bounded parameter
restriction in this statement. -/
theorem coefficient_eq_rational_samples {n d : ℕ} (c : Coefficients n d)
    (α : MultiIndex n d) :
    c α = ∑ j : Fin (interpolationSize n d),
      (coefficientExtractionWeight α j : ℝ) *
        evaluate c (fun i => (interpolationWeight j i : ℝ)) := by
  first
  | classical
    have hnode : Set.InjOn (fun j : Fin (interpolationSize n d) =>
        (interpolationNode j : ℝ))
        (↑(Finset.univ : Finset (Fin (interpolationSize n d))) : Set _) := by
      intro i _ j _ hij
      apply Fin.ext
      have hrat : interpolationNode i = interpolationNode j := Rat.cast_injective hij
      have hval : (i.val : ℚ) = (j.val : ℚ) := add_right_cancel hrat
      exact Nat.cast_injective hval
    have hdeg : (codedPolynomial c).degree <
        (Finset.univ : Finset (Fin (interpolationSize n d))).card := by
      simpa using codedPolynomial_degree_lt c
    have hp := Lagrange.eq_interpolate (f := codedPolynomial c) hnode hdeg
    have hcoeff := congrArg (fun p : Polynomial ℝ => p.coeff (coefficientCode α)) hp
    rw [codedPolynomial_coeff, Lagrange.interpolate_apply, Polynomial.finsetSum_coeff] at hcoeff
    refine hcoeff.trans (Finset.sum_congr rfl fun j _ => ?_)
    rw [Polynomial.coeff_C_mul, codedPolynomial_eval]
    have hw : (Lagrange.basis Finset.univ
        (fun k : Fin (interpolationSize n d) => (interpolationNode k : ℝ)) j).coeff
          (coefficientCode α) = (coefficientExtractionWeight α j : ℝ) := by
      rw [← map_rational_lagrange_basis, Polynomial.coeff_map]
      exact congrArg (fun q : ℚ => (q : ℝ)) (coefficientExtractionWeight_eq α j).symm
    rw [hw, mul_comm]
    simp only [interpolationWeight, Rat.cast_pow]

def coefficientExtractionBound (n d : ℕ) : ℚ :=
  ∑ α : MultiIndex n d, ∑ j : Fin (interpolationSize n d),
    |coefficientExtractionWeight α j|

theorem coefficientExtractionBound_nonneg (n d : ℕ) :
    0 ≤ coefficientExtractionBound n d :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))

/-- The interpolation formula supplies an explicit rational modulus for
coefficient error from uniformly bounded sample-evaluation errors. -/
theorem abs_coefficient_sub_le_of_samples {n d : ℕ} (c c' : Coefficients n d)
    {η : ℝ} (hη : 0 ≤ η)
    (hsample : ∀ j : Fin (interpolationSize n d),
      |evaluate c (fun i => (interpolationWeight j i : ℝ)) -
        evaluate c' (fun i => (interpolationWeight j i : ℝ))| ≤ η)
    (α : MultiIndex n d) :
    |c α - c' α| ≤ (coefficientExtractionBound n d : ℝ) * η := by
  first
  | classical
    rw [coefficient_eq_rational_samples c α, coefficient_eq_rational_samples c' α,
      ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ j : Fin (interpolationSize n d),
          |(coefficientExtractionWeight α j : ℝ)| * η := by
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro j _
        rw [← mul_sub, abs_mul]
        exact mul_le_mul_of_nonneg_left (hsample j) (abs_nonneg _)
      _ = (∑ j : Fin (interpolationSize n d),
          |(coefficientExtractionWeight α j : ℝ)|) * η := (Finset.sum_mul _ _ _).symm
      _ ≤ (coefficientExtractionBound n d : ℝ) * η := by
        apply mul_le_mul_of_nonneg_right _ hη
        simp only [coefficientExtractionBound, Rat.cast_sum, Rat.cast_abs]
        exact Finset.single_le_sum
          (fun β _ => Finset.sum_nonneg (fun j _ =>
            abs_nonneg (coefficientExtractionWeight β j : ℝ)))
          (Finset.mem_univ α)

end VolumePolynomials
