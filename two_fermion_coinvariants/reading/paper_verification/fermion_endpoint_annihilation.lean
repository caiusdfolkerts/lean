module

public import PaperVerification.FermionEndpointIdeal
public import Mathlib.Algebra.Polynomial.Monic

/-!+# From the prefix polynomial identities to the literal endpoint annihilator

The scalar and rank-one Gauss equations satisfy the cleared transitions below.
This file carries those polynomial equations through every monic division in
the actual endpoint recursion. No selected coefficient, node, or difference of
nodes is cancelled. Only the monic polynomial `t-y` is cancelled.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Endpoint

open Polynomial

variable {R : Type*} [CommRing R]

/-- The exact cleared scalar transition for one occupation pattern. -/
def ScalarTransition (d : Datum R) (p P : R[X]) : Prop :=
  match d.mark with
  | .unmarked => P = (X - C d.node) * p
  | .theta | .xi => P = p
  | .double => (X - C d.node) * P = p

/-- The exact cleared first-order rank-one transition. Its double-mark
equation has two factors because both the occupation product and the trace
acquire a denominator. -/
def RankOneTransition (d : Datum R) (p q Q : R[X]) : Prop :=
  match d.mark with
  | .unmarked => Q = (X - C d.node) * q - C d.weight * p
  | .theta | .xi => (X - C d.node) * Q = (X - C d.node) * q - C d.weight * p
  | .double => (X - C d.node) ^ 2 * Q = (X - C d.node) * q - C d.weight * p

/-- The additional equation from adding the missing colour at a single mark. -/
def SingleCompletion (d : Datum R) (p : R[X]) : Prop :=
  match d.mark with
  | .theta => d.rightFactor * p.eval d.node = 0
  | .xi => d.leftFactor * p.eval d.node = 0
  | .unmarked | .double => True

theorem linear_factor_cancel (y : R) {p q : R[X]}
    (h : (X - C y) * p = (X - C y) * q) : p = q :=
  (monic_X_sub_C y).isRegular.left h

/-- The single-mark completion kills exactly the actual endpoint remainder. -/
theorem single_completion_relation (T : State R) (d : Datum R) (F : R)
    (h : SingleCompletion d (T.A * C F))
    (hm : d.mark = .theta ∨ d.mark = .xi) :
    ∀ r ∈ relations T d, r * F = 0 := by
  rcases hm with hm | hm
  · simp only [SingleCompletion, hm, eval_mul, eval_C] at h
    intro r hr
    simp only [relations, hm, List.mem_singleton] at hr
    subst r
    simpa only [mul_assoc] using h
  · simp only [SingleCompletion, hm, eval_mul, eval_C] at h
    intro r hr
    simp only [relations, hm, List.mem_singleton] at hr
    subst r
    simpa only [mul_assoc] using h

theorem weighted_remainder_annihilates (T : State R) (d : Datum R) (F : R)
    (h : ∀ r ∈ relations T d, r * F = 0)
    (hm : d.mark = .theta ∨ d.mark = .xi) :
    d.weight * T.A.eval d.node * F = 0 := by
  rcases hm with hm | hm
  · have hr := h (d.rightFactor * T.A.eval d.node) (by simp [relations, hm])
    calc
      _ = (d.beta * d.leftFactor) * (d.rightFactor * T.A.eval d.node * F) := by
        simp only [Datum.weight]; ring
      _ = 0 := by rw [hr, mul_zero]
  · have hr := h (d.leftFactor * T.A.eval d.node) (by simp [relations, hm])
    calc
      _ = (d.beta * d.rightFactor) * (d.leftFactor * T.A.eval d.node * F) := by
        simp only [Datum.weight]; ring
      _ = 0 := by rw [hr, mul_zero]

/-- One step of the actual recursion realizes the bounded Gauss polynomials,
and its literal remainder generators annihilate the selected coefficient. -/
theorem next_realizes_prefix_polynomials
    (T : State R) (d : Datum R) (F : R) (P Q : R[X])
    (hP : ScalarTransition d (T.A * C F) P)
    (hQ : RankOneTransition d (T.A * C F) (T.B * C F) Q)
    (hcompletion : SingleCompletion d (T.A * C F)) :
    (next T d).A * C F = P ∧ (next T d).B * C F = Q ∧
      ∀ r ∈ relations T d, r * F = 0 := by
  have hdivA := quotient_identity T.A d.node
  cases hm : d.mark with
  | unmarked =>
    simp only [ScalarTransition, RankOneTransition, hm] at hP hQ
    refine ⟨?_, ?_, ?_⟩
    · simp only [next, hm]
      rw [hP]
      ring
    · simp only [next, hm]
      rw [hQ]
      ring
    · simp [relations, hm]
  | theta =>
    have hr := single_completion_relation T d F hcompletion (Or.inl hm)
    have hz := weighted_remainder_annihilates T d F hr (Or.inl hm)
    have hzC : C d.weight * C (T.A.eval d.node) * C F = (0 : R[X]) := by
      rw [← map_mul, ← map_mul, hz, map_zero]
    simp only [ScalarTransition, RankOneTransition, hm] at hP hQ
    refine ⟨by simpa only [next, hm] using hP.symm, ?_, hr⟩
    simp only [next, hm]
    apply linear_factor_cancel d.node
    linear_combination -hQ - C F * C d.weight * hdivA + hzC
  | xi =>
    have hr := single_completion_relation T d F hcompletion (Or.inr hm)
    have hz := weighted_remainder_annihilates T d F hr (Or.inr hm)
    have hzC : C d.weight * C (T.A.eval d.node) * C F = (0 : R[X]) := by
      rw [← map_mul, ← map_mul, hz, map_zero]
    simp only [ScalarTransition, RankOneTransition, hm] at hP hQ
    refine ⟨by simpa only [next, hm] using hP.symm, ?_, hr⟩
    simp only [next, hm]
    apply linear_factor_cancel d.node
    linear_combination -hQ - C F * C d.weight * hdivA + hzC
  | double =>
    simp only [ScalarTransition, RankOneTransition, hm] at hP hQ
    have hρ : T.A.eval d.node * F = 0 := by
      have he := congrArg (eval d.node) hP
      simpa only [eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul] using he.symm
    have hρC : C (T.A.eval d.node) * C F = (0 : R[X]) := by
      rw [← map_mul, hρ, map_zero]
    have hA : quotient T.A d.node * C F = P := by
      apply linear_factor_cancel d.node
      linear_combination -hP + C F * hdivA - hρC
    have hQlinear : (X - C d.node) * Q = (T.B - C d.weight * quotient T.A d.node) * C F := by
      apply linear_factor_cancel d.node
      linear_combination hQ + C d.weight * hP +
        C d.weight * (X - C d.node) * hA
    have hτ : (T.B - C d.weight * quotient T.A d.node).eval d.node * F = 0 := by
      have he := congrArg (eval d.node) hQlinear
      simpa only [eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul] using he.symm
    have hτC : C ((T.B - C d.weight * quotient T.A d.node).eval d.node) * C F =
        (0 : R[X]) := by rw [← map_mul, hτ, map_zero]
    have hdivB := quotient_identity (T.B - C d.weight * quotient T.A d.node) d.node
    refine ⟨by simpa only [next, hm] using hA, ?_, ?_⟩
    · simp only [next, hm]
      apply linear_factor_cancel d.node
      linear_combination -hQlinear + C F * hdivB - hτC
    · intro r hr
      simp only [relations, hm, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hρ
      · exact hτ

/-- The full recursion is forced by the actual polynomial transition
identities, for every number of variables and every occupation pattern. -/
theorem run_realizes_prefix_polynomials
    (data : ℕ → Datum R) (F : R) (P Q : ℕ → R[X])
    (hPzero : P 0 = C F) (hQzero : Q 0 = 0) (n : ℕ)
    (hP : ∀ i < n, ScalarTransition (data i) (P i) (P (i + 1)))
    (hQ : ∀ i < n, RankOneTransition (data i) (P i) (Q i) (Q (i + 1)))
    (hc : ∀ i < n, SingleCompletion (data i) (P i)) :
    (run data n).A * C F = P n ∧ (run data n).B * C F = Q n ∧
      ∀ r ∈ allRelations data n, r * F = 0 := by
  revert hP hQ hc
  induction n with
  | zero =>
    intro hP hQ hc
    simp only [run, initial, one_mul, zero_mul, allRelations, List.not_mem_nil,
      hPzero, hQzero, forall_false, implies_true, and_self]
  | succ n ih =>
    intro hP hQ hc
    obtain ⟨hA, hB, hr⟩ := ih (fun i hi ↦ hP i (Nat.lt_succ_of_lt hi))
      (fun i hi ↦ hQ i (Nat.lt_succ_of_lt hi))
      (fun i hi ↦ hc i (Nat.lt_succ_of_lt hi))
    have hp := hP n (Nat.lt_succ_self n)
    have hq := hQ n (Nat.lt_succ_self n)
    have hcomp := hc n (Nat.lt_succ_self n)
    rw [← hA] at hp hq hcomp
    rw [← hB] at hq
    obtain ⟨hA', hB', hr'⟩ := next_realizes_prefix_polynomials (run data n) (data n) F
      (P (n + 1)) (Q (n + 1)) hp hq hcomp
    refine ⟨hA', hB', ?_⟩
    intro r hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact hr r hmem
    · exact hr' r hmem

/-- Once the global rank-one polynomial vanishes, every actual endpoint
generator annihilates the selected coefficient. -/
theorem endpoint_generators_annihilate_of_prefix_polynomials
    (data : ℕ → Datum R) (F : R) (P Q : ℕ → R[X])
    (hPzero : P 0 = C F) (hQzero : Q 0 = 0) (n c : ℕ)
    (hP : ∀ i < n, ScalarTransition (data i) (P i) (P (i + 1)))
    (hQ : ∀ i < n, RankOneTransition (data i) (P i) (Q i) (Q (i + 1)))
    (hc : ∀ i < n, SingleCompletion (data i) (P i))
    (hterminal : Q n = 0) :
    ∀ r ∈ generators data n c, r * F = 0 := by
  obtain ⟨hA, hB, hr⟩ := run_realizes_prefix_polynomials data F P Q hPzero hQzero n hP hQ hc
  intro r hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact hr r hmem
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hmem
    have hh := congrArg (fun p : R[X] ↦ p.coeff j) (hB.trans hterminal)
    simpa only [coeff_mul_C, coeff_zero] using hh

/-- The entire literal endpoint ideal, not just its chosen list of generators,
annihilates the selected harmonic coefficient. -/
theorem endpointIdeal_annihilates_of_prefix_polynomials
    (data : ℕ → Datum R) (F : R) (P Q : ℕ → R[X])
    (hPzero : P 0 = C F) (hQzero : Q 0 = 0) (n c : ℕ)
    (hP : ∀ i < n, ScalarTransition (data i) (P i) (P (i + 1)))
    (hQ : ∀ i < n, RankOneTransition (data i) (P i) (Q i) (Q (i + 1)))
    (hc : ∀ i < n, SingleCompletion (data i) (P i))
    (hterminal : Q n = 0) :
    ∀ r ∈ endpointIdeal data n c, r * F = 0 := by
  intro r hr
  induction hr using Submodule.span_induction with
  | mem r hr =>
    exact endpoint_generators_annihilate_of_prefix_polynomials data F P Q hPzero hQzero
      n c hP hQ hc hterminal r hr
  | zero => exact zero_mul F
  | add a b ha hb iha ihb => rw [add_mul, iha, ihb, add_zero]
  | smul a b hb ih => simpa only [smul_eq_mul, mul_assoc, ih, mul_zero]

end PaperVerification.Fermion.Endpoint
