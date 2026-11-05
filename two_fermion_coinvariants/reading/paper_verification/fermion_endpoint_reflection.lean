module

public import PaperVerification.FermionEndpointAnnihilation
public import PaperVerification.FermionPrefixCompletion

/-!
# Reversing the literal Gauss occupation polynomials

All rational factors below are represented by finite inverse polynomials of
nilpotent nodes. Reversal of the actual degree cutoffs produces the cleared
endpoint transitions. The extra zero coefficient of the rank-one identity is
retained, including at height zero.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Endpoint

open scoped BigOperators
open Polynomial

variable {R : Type*} [CommRing R]

def inverseLinear (y : R) (N : ℕ) : R[X] :=
  gaussNilpotentInverse 1 X (C (-y)) N

def atZeroLinear (y : R) : R[X] := 1 - C y * X

theorem inverseLinear_mul (y : R) (N : ℕ) (hy : y ^ N = 0) :
    inverseLinear y N * atZeroLinear y = 1 := by
  have hnil : ((-1 * (X : R[X])) * C (-y)) ^ N = 0 := by
    rw [mul_pow, ← map_pow, neg_pow, hy, mul_zero, map_zero, mul_zero]
  simpa only [inverseLinear, atZeroLinear, map_neg, one_mul, neg_mul, ← sub_eq_add_neg] using
    gaussNilpotentInverse_mul_of_product_pow_eq_zero (1 : R[X]) X (C (-y)) N hnil

theorem atZeroLinear_natDegree_le (y : R) : (atZeroLinear y).natDegree ≤ 1 := by
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · simp
  · simpa only [pow_one] using natDegree_C_mul_X_pow_le y 1

theorem reflect_atZeroLinear (y : R) : reflect 1 (atZeroLinear y) = X - C y := by
  rw [atZeroLinear, reflect_sub, reflect_one]
  rw [show C y * X = C y * X ^ 1 by rw [pow_one], reflect_C_mul_X_pow]
  simp only [pow_one, revAt_le le_rfl, Nat.sub_self, pow_zero, mul_one]

theorem reflect_succ_of_natDegree_le (h : ℕ) (p : R[X]) (hp : p.natDegree ≤ h) :
    reflect (h + 1) p = X * reflect h p := by
  have hh := reflect_mul (1 : R[X]) p (F := 1) (G := h) (by simp) hp
  simpa only [one_mul, reflect_one, pow_one, Nat.add_comm] using hh

theorem reflect_atZeroLinear_mul (h : ℕ) (y : R) (p : R[X]) (hp : p.natDegree ≤ h) :
    reflect (h + 1) (atZeroLinear y * p) = (X - C y) * reflect h p := by
  have hh := reflect_mul (atZeroLinear y) p (F := 1) (G := h)
    (atZeroLinear_natDegree_le y) hp
  simpa only [reflect_atZeroLinear, Nat.add_comm] using hh

theorem reflect_atZeroLinear_sq_mul (h : ℕ) (y : R) (p : R[X]) (hp : p.natDegree ≤ h) :
    reflect (h + 2) (atZeroLinear y ^ 2 * p) = (X - C y) ^ 2 * reflect h p := by
  have hmul : (atZeroLinear y * p).natDegree ≤ h + 1 := by
    exact (natDegree_mul_le).trans (by
      have := atZeroLinear_natDegree_le y
      omega)
  rw [pow_two, mul_assoc]
  have hh : h + 2 = (h + 1) + 1 := by omega
  rw [hh, reflect_atZeroLinear_mul (h + 1) y _ hmul,
    reflect_atZeroLinear_mul h y p hp]
  ring

theorem CoefficientBound.natDegree_le {p : R[X]} {h : ℕ}
    (hp : CoefficientBound p h) : p.natDegree ≤ h := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  exact hp j (Nat.le_of_lt hj)

/-- Reversal of the rank-one coefficient, divided by its known factor `t`.
This definition is valid at height zero as well. -/
def reverseRankOne (h : ℕ) (p : R[X]) : R[X] := (reflect h p) /ₘ X

theorem X_mul_reverseRankOne (h : ℕ) (p : R[X]) (hp : CoefficientBound p h) :
    X * reverseRankOne h p = reflect h p := by
  have hz : (reflect h p).eval 0 = 0 := by
    rw [← coeff_zero_eq_eval_zero, coeff_reflect, revAt_zero]
    exact hp h le_rfl
  simpa only [reverseRankOne, modByMonic_X, hz, map_zero, zero_add] using
    modByMonic_add_div (reflect h p) X

theorem reverseRankOne_zero (h : ℕ) : reverseRankOne h (0 : R[X]) = 0 := by
  simp only [reverseRankOne, reflect_zero, zero_divByMonic]

def AtZeroScalarTransition (d : Datum R) (p P : R[X]) : Prop :=
  match d.mark with
  | .unmarked => P = atZeroLinear d.node * p
  | .theta | .xi => P = p
  | .double => atZeroLinear d.node * P = p

def AtZeroRankOneTransition (d : Datum R) (p q Q : R[X]) : Prop :=
  match d.mark with
  | .unmarked => Q = atZeroLinear d.node * q - C d.weight * p
  | .theta | .xi => atZeroLinear d.node * Q = atZeroLinear d.node * q - C d.weight * p
  | .double => atZeroLinear d.node ^ 2 * Q = atZeroLinear d.node * q - C d.weight * p

/-- The actual degree cutoffs turn the identities at zero into precisely the
polynomial identities at infinity used by the endpoint divisions. -/
theorem reflected_prefix_transitions (d : Datum R) (h h' : ℕ)
    (hs : HeightStep d.mark h h') (p P q Q : R[X])
    (hp : p.natDegree ≤ h) (hP : P.natDegree ≤ h')
    (hq : CoefficientBound q h) (hQ : CoefficientBound Q h')
    (hscalar : AtZeroScalarTransition d p P)
    (hrank : AtZeroRankOneTransition d p q Q) :
    ScalarTransition d (reflect h p) (reflect h' P) ∧
      RankOneTransition d (reflect h p) (reverseRankOne h q) (reverseRankOne h' Q) := by
  have hb := X_mul_reverseRankOne h q hq
  have ha := X_mul_reverseRankOne h' Q hQ
  cases hm : d.mark with
  | unmarked =>
    simp only [HeightStep, hm] at hs
    subst h'
    simp only [AtZeroScalarTransition, AtZeroRankOneTransition, hm] at hscalar hrank
    constructor
    · simp only [ScalarTransition, hm]
      rw [hscalar, reflect_atZeroLinear_mul h d.node p hp]
    · simp only [RankOneTransition, hm]
      apply isRegular_X.left
      have hh := congrArg (reflect (h + 1)) hrank
      rw [reflect_sub, reflect_atZeroLinear_mul h d.node q hq.natDegree_le,
        reflect_C_mul, reflect_succ_of_natDegree_le h p hp, ← hb, ← ha] at hh
      linear_combination hh
  | theta =>
    simp only [HeightStep, hm] at hs
    subst h'
    simp only [AtZeroScalarTransition, AtZeroRankOneTransition, hm] at hscalar hrank
    constructor
    · simpa only [ScalarTransition, hm] using congrArg (reflect h) hscalar
    · simp only [RankOneTransition, hm]
      apply isRegular_X.left
      have hh := congrArg (reflect (h + 1)) hrank
      rw [reflect_atZeroLinear_mul h d.node Q hQ.natDegree_le, reflect_sub,
        reflect_atZeroLinear_mul h d.node q hq.natDegree_le,
        reflect_C_mul, reflect_succ_of_natDegree_le h p hp, ← hb, ← ha] at hh
      linear_combination hh
  | xi =>
    simp only [HeightStep, hm] at hs
    subst h'
    simp only [AtZeroScalarTransition, AtZeroRankOneTransition, hm] at hscalar hrank
    constructor
    · simpa only [ScalarTransition, hm] using congrArg (reflect h) hscalar
    · simp only [RankOneTransition, hm]
      apply isRegular_X.left
      have hh := congrArg (reflect (h + 1)) hrank
      rw [reflect_atZeroLinear_mul h d.node Q hQ.natDegree_le, reflect_sub,
        reflect_atZeroLinear_mul h d.node q hq.natDegree_le,
        reflect_C_mul, reflect_succ_of_natDegree_le h p hp, ← hb, ← ha] at hh
      linear_combination hh
  | double =>
    simp only [HeightStep, hm] at hs
    subst h
    simp only [AtZeroScalarTransition, AtZeroRankOneTransition, hm] at hscalar hrank
    constructor
    · simp only [ScalarTransition, hm]
      have hh := congrArg (reflect (h' + 1)) hscalar
      rwa [reflect_atZeroLinear_mul h' d.node P hP] at hh
    · simp only [RankOneTransition, hm]
      apply isRegular_X.left
      have hh := congrArg (reflect (h' + 2)) hrank
      rw [reflect_atZeroLinear_sq_mul h' d.node Q hQ.natDegree_le, reflect_sub] at hh
      have hnat : h' + 2 = (h' + 1) + 1 := by omega
      rw [hnat, reflect_atZeroLinear_mul (h' + 1) d.node q hq.natDegree_le,
        reflect_C_mul, reflect_succ_of_natDegree_le (h' + 1) p hp, ← hb, ← ha] at hh
      linear_combination hh

/-- The finite inverse occupation product, for the literal four path steps. -/
def occupationFactor (d : Datum R) (N : ℕ) : R[X] :=
  match d.mark with
  | .unmarked => atZeroLinear d.node
  | .theta | .xi => 1
  | .double => inverseLinear d.node N

def occupation (data : ℕ → Datum R) (N : ℕ) : ℕ → R[X]
  | 0 => 1
  | i + 1 => occupationFactor (data i) N * occupation data N i

def tracePolynomial (data : ℕ → Datum R) (N : ℕ) : ℕ → R[X]
  | 0 => 0
  | i + 1 => tracePolynomial data N i + C (data i).weight * inverseLinear (data i).node N

def scalarOccupation (data : ℕ → Datum R) (N : ℕ) (F : R) (i : ℕ) : R[X] :=
  occupation data N i * C F

def rankOneOccupation (data : ℕ → Datum R) (N : ℕ) (F : R) (i : ℕ) : R[X] :=
  -tracePolynomial data N i * scalarOccupation data N F i

theorem occupation_transitions (data : ℕ → Datum R) (N : ℕ) (F : R) (i : ℕ)
    (hy : (data i).node ^ N = 0) :
    AtZeroScalarTransition (data i) (scalarOccupation data N F i)
      (scalarOccupation data N F (i + 1)) ∧
    AtZeroRankOneTransition (data i) (scalarOccupation data N F i)
      (rankOneOccupation data N F i) (rankOneOccupation data N F (i + 1)) := by
  have hinv := inverseLinear_mul (data i).node N hy
  cases hm : (data i).mark <;>
    simp only [AtZeroScalarTransition, AtZeroRankOneTransition, hm,
      scalarOccupation, rankOneOccupation, occupation, occupationFactor, tracePolynomial, hm]
  · constructor
    · ring
    · linear_combination -occupation data N i * C F * C (data i).weight * hinv
  · constructor
    · ring
    · linear_combination -occupation data N i * C F * C (data i).weight * hinv
  · constructor
    · ring
    · linear_combination -occupation data N i * C F * C (data i).weight * hinv
  · constructor
    · linear_combination occupation data N i * C F * hinv
    · linear_combination
        -(tracePolynomial data N i * occupation data N i * C F * atZeroLinear (data i).node +
          C (data i).weight * occupation data N i * C F *
            (inverseLinear (data i).node N * atZeroLinear (data i).node + 1)) * hinv

theorem tracePolynomial_eq_sum (data : ℕ → Datum R) (N n : ℕ) :
    tracePolynomial data N n =
      ∑ i : Fin n, C (data i).weight * inverseLinear (data i).node N := by
  induction n with
  | zero => simp [tracePolynomial]
  | succ n ih =>
    rw [tracePolynomial, ih, Fin.sum_univ_castSucc]
    rfl

/-- Ordinary moment equations kill the complete rank-one trace as an actual
polynomial. This uses every finite inverse coefficient, not pointwise testing. -/
theorem tracePolynomial_eq_zero_of_moments (data : ℕ → Datum R) (N n : ℕ)
    (hmom : ∀ k : ℕ, moment (fun i : Fin n ↦ (data i).node)
      (fun i ↦ (data i).weight) k = 0) :
    tracePolynomial data N n = 0 := by
  rw [tracePolynomial_eq_sum]
  simp only [inverseLinear, gaussNilpotentInverse, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k hk
  calc
    _ = C (moment (fun i : Fin n ↦ (data i).node) (fun i ↦ (data i).weight) k) * X ^ k := by
      simp only [moment, smul_eq_mul, map_sum, map_mul, map_pow, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_neg]
      ring
    _ = 0 := by rw [hmom k, map_zero, zero_mul]

/-- Completing a single mark adds exactly one inverse occupation factor. -/
def completedOccupation (data : ℕ → Datum R) (N : ℕ) (F a : R) (i : ℕ) : R[X] :=
  C a * inverseLinear (data i).node N * scalarOccupation data N F (i + 1)

theorem completion_of_cutoff (data : ℕ → Datum R) (N : ℕ) (F : R)
    (height : ℕ → ℕ) (i : ℕ) (hy : (data i).node ^ N = 0)
    (hs : HeightStep (data i).mark (height i) (height (i + 1)))
    (hc : ∀ a : R,
      ((data i).mark = .theta ∧ a = (data i).rightFactor) ∨
        ((data i).mark = .xi ∧ a = (data i).leftFactor) →
      CoefficientBound (completedOccupation data N F a i) (height (i + 1))) :
    SingleCompletion (data i) (reflect (height i) (scalarOccupation data N F i)) := by
  have hinv := inverseLinear_mul (data i).node N hy
  have hcomp (a : R) : atZeroLinear (data i).node * completedOccupation data N F a i =
      C a * scalarOccupation data N F (i + 1) := by
    unfold completedOccupation
    linear_combination C a * scalarOccupation data N F (i + 1) * hinv
  have aux (a : R) (ha : ((data i).mark = .theta ∧ a = (data i).rightFactor) ∨
      ((data i).mark = .xi ∧ a = (data i).leftFactor))
      (hh : height (i + 1) = height i)
      (hP : scalarOccupation data N F (i + 1) = scalarOccupation data N F i) :
      a * (reflect (height i) (scalarOccupation data N F i)).eval (data i).node = 0 := by
    have hbound := hc a ha
    rw [hh] at hbound
    by_cases hzero : height i = 0
    · have hz : completedOccupation data N F a i = 0 := by
        ext j
        rw [coeff_zero]
        exact hbound j (by omega)
      have heq := hcomp a
      rw [hz, mul_zero, hP] at heq
      have he := congrArg (fun p : R[X] ↦ (reflect (height i) p).eval (data i).node) heq
      simpa only [reflect_zero, eval_zero, reflect_C_mul, eval_mul, eval_C] using he.symm
    · have hdegree : (completedOccupation data N F a i).natDegree ≤ height i - 1 := by
        apply natDegree_le_iff_coeff_eq_zero.mpr
        intro j hj
        exact hbound j (by omega)
      have heq := hcomp a
      rw [hP] at heq
      exact Exterior.singleMark_remainder_of_bounded_identity_sub (height i)
        (Nat.pos_of_ne_zero hzero) (data i).node a _ _ hdegree heq
  cases hm : (data i).mark with
  | unmarked => simp only [SingleCompletion, hm]
  | double => simp only [SingleCompletion, hm]
  | theta =>
    simp only [SingleCompletion, hm]
    apply aux (data i).rightFactor (Or.inl ⟨hm, rfl⟩)
    · simpa only [HeightStep, hm] using hs
    · simp only [scalarOccupation, occupation, occupationFactor, hm, one_mul]
  | xi =>
    simp only [SingleCompletion, hm]
    apply aux (data i).leftFactor (Or.inr ⟨hm, rfl⟩)
    · simpa only [HeightStep, hm] using hs
    · simp only [scalarOccupation, occupation, occupationFactor, hm, one_mul]

/-- The exact occupation cutoffs from the diagonal, rank-one and completion
Gauss equations imply annihilation by the literal endpoint ideal. This
includes all heights and all zero-divisor coefficient rings. -/
theorem endpointIdeal_annihilates_of_occupation_cutoffs
    (data : ℕ → Datum R) (N n : ℕ) (F : R) (height : ℕ → ℕ)
    (hzero : height 0 = 0)
    (hy : ∀ i < n, (data i).node ^ N = 0)
    (hstep : ∀ i < n, HeightStep (data i).mark (height i) (height (i + 1)))
    (hscalar : ∀ i ≤ n, (scalarOccupation data N F i).natDegree ≤ height i)
    (hrank : ∀ i ≤ n, CoefficientBound (rankOneOccupation data N F i) (height i))
    (hcompletion : ∀ i < n, ∀ a : R,
      ((data i).mark = .theta ∧ a = (data i).rightFactor) ∨
        ((data i).mark = .xi ∧ a = (data i).leftFactor) →
      CoefficientBound (completedOccupation data N F a i) (height (i + 1)))
    (hmom : ∀ k : ℕ, moment (fun i : Fin n ↦ (data i).node)
      (fun i ↦ (data i).weight) k = 0) :
    ∀ r ∈ endpointIdeal data n (height n), r * F = 0 := by
  let P := fun i ↦ reflect (height i) (scalarOccupation data N F i)
  let Q := fun i ↦ reverseRankOne (height i) (rankOneOccupation data N F i)
  have hPzero : P 0 = C F := by
    simp only [P, scalarOccupation, occupation, one_mul, hzero, reflect_C,
      pow_zero, mul_one]
  have hQzero : Q 0 = 0 := by
    simp only [Q, rankOneOccupation, tracePolynomial, neg_zero, zero_mul, reverseRankOne_zero]
  have htrans (i : ℕ) (hi : i < n) :
      ScalarTransition (data i) (P i) (P (i + 1)) ∧
        RankOneTransition (data i) (P i) (Q i) (Q (i + 1)) := by
    obtain ⟨hS, hR⟩ := occupation_transitions data N F i (hy i hi)
    exact reflected_prefix_transitions (data i) (height i) (height (i + 1)) (hstep i hi)
      _ _ _ _ (hscalar i hi.le) (hscalar (i + 1) (by omega))
      (hrank i hi.le) (hrank (i + 1) (by omega)) hS hR
  apply endpointIdeal_annihilates_of_prefix_polynomials data F P Q hPzero hQzero n (height n)
    (fun i hi ↦ (htrans i hi).1) (fun i hi ↦ (htrans i hi).2)
  · intro i hi
    exact completion_of_cutoff data N F height i (hy i hi) (hstep i hi) (hcompletion i hi)
  · dsimp only [Q]
    rw [rankOneOccupation, tracePolynomial_eq_zero_of_moments data N n hmom,
      neg_zero, zero_mul, reverseRankOne_zero]

end PaperVerification.Fermion.Endpoint
