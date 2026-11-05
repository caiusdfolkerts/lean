module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Polynomial contraction of the explicit rational Newton columns

This is the partial-fraction calculation behind equation (7) and the first
identity in Section 2.2. It is proved from monic division and Mathlib's
Lagrange interpolation, with every nonzero denominator stated explicitly.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Newton

open Polynomial
open scoped BigOperators

variable {L ι : Type*} [Field L] [DecidableEq ι]

/-- The residue at a simple pole of `N/∏(t-xⱼ)`. -/
def simpleResidue (N : Polynomial L) (s : Finset ι) (x : ι → L) (j : ι) : L :=
  N.eval (x j) * Lagrange.nodalWeight s x j

/-- Exact partial fractions after monic division, including an empty pole set. -/
theorem eval_div_nodal_eq_polynomial_part_add_poles
    (N : Polynomial L) (s : Finset ι) (x : ι → L)
    (hx : Set.InjOn x s) (y : L) (hy : ∀ j ∈ s, y ≠ x j) :
    N.eval y / (Lagrange.nodal s x).eval y =
      (N /ₘ Lagrange.nodal s x).eval y +
        ∑ j ∈ s, simpleResidue N s x j / (y - x j) := by
  have hdegree : (N %ₘ Lagrange.nodal s x).degree < s.card := by
    simpa only [Lagrange.degree_nodal] using
      degree_modByMonic_lt N (Lagrange.nodal_monic (s := s) (v := x))
  have hvalues (j : ι) (hj : j ∈ s) :
      (N %ₘ Lagrange.nodal s x).eval (x j) = N.eval (x j) := by
    have h := congrArg (fun p : Polynomial L ↦ p.eval (x j))
      (modByMonic_add_div N (Lagrange.nodal s x))
    simpa only [eval_add, eval_mul, Lagrange.eval_nodal_at_node hj, zero_mul, add_zero] using h
  have hinterp : N %ₘ Lagrange.nodal s x =
      Lagrange.interpolate s x (fun j ↦ N.eval (x j)) :=
    Lagrange.eq_interpolate_of_eval_eq _ hx hdegree hvalues
  have hrem : (N %ₘ Lagrange.nodal s x).eval y =
      (Lagrange.nodal s x).eval y *
        ∑ j ∈ s, simpleResidue N s x j / (y - x j) := by
    rw [hinterp, Lagrange.eval_interpolate_not_at_node _ hy]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    simp only [simpleResidue, div_eq_mul_inv]
    ring
  apply (div_eq_iff (Lagrange.eval_nodal_not_at_node hy)).mpr
  have h := congrArg (fun p : Polynomial L ↦ p.eval y)
    (modByMonic_add_div N (Lagrange.nodal s x))
  simp only [eval_add, eval_mul] at h
  rw [← h, hrem]
  ring

/-- The polar contributions of the active evaluations cancel the weighted
normal residues. This is the literal contraction formula for a Newton column. -/
theorem rational_contraction_eq_polynomial_part
    (N : Polynomial L) (poles active : Finset ι) (x β : ι → L)
    (hx : Set.InjOn x poles)
    (hcross : ∀ i ∈ active, ∀ j ∈ poles, x i ≠ x j)
    (hβ : ∀ j ∈ poles, β j ≠ 0) :
    (∑ i ∈ active, β i * (N.eval (x i) / (Lagrange.nodal poles x).eval (x i))) +
      (∑ j ∈ poles, β j *
        (simpleResidue N poles x j / β j * ∑ i ∈ active, β i / (x j - x i))) =
      ∑ i ∈ active, β i * (N /ₘ Lagrange.nodal poles x).eval (x i) := by
  have hnegative :
      (∑ j ∈ poles, β j *
        (simpleResidue N poles x j / β j * ∑ i ∈ active, β i / (x j - x i))) =
      -∑ i ∈ active, β i * ∑ j ∈ poles, simpleResidue N poles x j / (x i - x j) := by
    calc
      _ = ∑ j ∈ poles, simpleResidue N poles x j *
          ∑ i ∈ active, β i / (x j - x i) := by
        apply Finset.sum_congr rfl
        intro j hj
        field_simp [hβ j hj]
      _ = ∑ j ∈ poles, ∑ i ∈ active,
          -(β i * (simpleResidue N poles x j / (x i - x j))) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [show x j - x i = -(x i - x j) by ring, div_neg]
        ring
      _ = _ := by
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum, Finset.sum_neg_distrib]
  rw [hnegative]
  have hpositive :
      (∑ i ∈ active, β i * (N.eval (x i) / (Lagrange.nodal poles x).eval (x i))) =
      (∑ i ∈ active, β i * (N /ₘ Lagrange.nodal poles x).eval (x i)) +
        ∑ i ∈ active, β i * ∑ j ∈ poles, simpleResidue N poles x j / (x i - x j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [eval_div_nodal_eq_polynomial_part_add_poles N poles x hx (x i) (hcross i hi),
      mul_add]
  rw [hpositive]
  ring

/-- The explicit column is supported precisely on the active interval and the
earlier negative indices, as in equation (7). -/
def rationalColumn (N : Polynomial L) (poles active : Finset ι) (x β : ι → L)
    (k : ι) : L :=
  if k ∈ active then N.eval (x k) / (Lagrange.nodal poles x).eval (x k)
  else if k ∈ poles then simpleResidue N poles x k / β k *
    ∑ i ∈ active, β i / (x k - x i)
  else 0

/-- The weighted coordinate sum of the actual rational column is polynomial
in the active evaluations of the quotient in monic division. -/
theorem rationalColumn_weighted_sum [Fintype ι]
    (N : Polynomial L) (poles active : Finset ι) (x β : ι → L)
    (hdisj : Disjoint active poles) (hx : Set.InjOn x poles)
    (hcross : ∀ i ∈ active, ∀ j ∈ poles, x i ≠ x j)
    (hβ : ∀ j ∈ poles, β j ≠ 0) :
    (∑ k, β k * rationalColumn N poles active x β k) =
      ∑ i ∈ active, β i * (N /ₘ Lagrange.nodal poles x).eval (x i) := by
  have hsplit : (∑ k, β k * rationalColumn N poles active x β k) =
      (∑ i ∈ active, β i * (N.eval (x i) / (Lagrange.nodal poles x).eval (x i))) +
      (∑ j ∈ poles, β j *
        (simpleResidue N poles x j / β j * ∑ i ∈ active, β i / (x j - x i))) := by
    have hpoint (k : ι) : β k * rationalColumn N poles active x β k =
        (if k ∈ active then β k * (N.eval (x k) /
          (Lagrange.nodal poles x).eval (x k)) else 0) +
        (if k ∈ poles then β k * (simpleResidue N poles x k / β k *
          ∑ i ∈ active, β i / (x k - x i)) else 0) := by
      by_cases ha : k ∈ active
      · have hp : k ∉ poles := fun hp ↦ Finset.disjoint_left.mp hdisj ha hp
        simp [rationalColumn, ha, hp]
      · simp [rationalColumn, ha, mul_ite]
    simp_rw [hpoint, Finset.sum_add_distrib]
    simp
  rw [hsplit]
  exact rational_contraction_eq_polynomial_part N poles active x β hx hcross hβ

end PaperVerification.Fermion.Newton
