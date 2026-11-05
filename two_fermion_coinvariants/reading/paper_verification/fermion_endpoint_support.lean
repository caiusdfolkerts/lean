module

public import PaperVerification.FermionEndpointPolynomial

/-!
# Monicity, degree bounds, and exact support of the endpoint equations

The degree assertions are proved for the literal recursive polynomials.
The origin-only zero-set argument then uses all endpoint equations and the
exact subset-sum hypothesis. Repeated nodes are included.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Endpoint

open scoped BigOperators
open Polynomial

variable {R : Type*} [CommRing R]

/-- All coefficients starting at `h` vanish. At height zero this means the
polynomial itself is zero, so no exceptional convention for degree zero is used. -/
def CoefficientBound (p : R[X]) (h : ℕ) : Prop :=
  ∀ j : ℕ, h ≤ j → p.coeff j = 0

theorem coefficientBound_iff_degree (p : R[X]) (h : ℕ) :
    CoefficientBound p h ↔ p.degree < h :=
  (degree_lt_iff_coeff_zero p h).symm

theorem coefficientBound_zero (h : ℕ) : CoefficientBound (0 : R[X]) h := by
  intro j hj
  exact coeff_zero j

theorem CoefficientBound.sub {p q : R[X]} {h : ℕ}
    (hp : CoefficientBound p h) (hq : CoefficientBound q h) :
    CoefficientBound (p - q) h := by
  intro j hj
  rw [coeff_sub, hp j hj, hq j hj, sub_self]

theorem CoefficientBound.C_mul {p : R[X]} {h : ℕ}
    (hp : CoefficientBound p h) (a : R) : CoefficientBound (C a * p) h := by
  intro j hj
  rw [coeff_C_mul, hp j hj, mul_zero]

theorem coefficientBound_of_natDegree_lt (p : R[X]) (h : ℕ) (hp : p.natDegree < h) :
    CoefficientBound p h := by
  intro j hj
  exact coeff_eq_zero_of_natDegree_lt (hp.trans_le hj)

theorem CoefficientBound.linear_mul {p : R[X]} {h : ℕ}
    (hp : CoefficientBound p h) (y : R) :
    CoefficientBound ((X - C y) * p) (h + 1) := by
  intro j hj
  cases j with
  | zero => omega
  | succ j =>
    rw [sub_mul, coeff_sub, coeff_X_mul, coeff_C_mul,
      hp j (by omega), hp (j + 1) (by omega), mul_zero, sub_self]

section Nontrivial

variable [Nontrivial R]

/-- Division of a degree-`h` polynomial by the monic linear factor has no
coefficient in degrees `h` or higher, including `h = 0`. -/
theorem quotient_coefficientBound (p : R[X]) (y : R) (h : ℕ)
    (hp : p.natDegree = h) : CoefficientBound (quotient p y) h := by
  by_cases hh : h = 0
  · have hz : quotient p y = 0 := by
      apply (divByMonic_eq_zero_iff (monic_X_sub_C y)).mpr
      calc
        p.degree ≤ (p.natDegree : WithBot ℕ) := degree_le_natDegree
        _ = 0 := by rw [hp, hh]; rfl
        _ < (X - C y : R[X]).degree := by rw [degree_X_sub_C]; exact zero_lt_one
    rw [hz]
    exact coefficientBound_zero h
  · apply coefficientBound_of_natDegree_lt
    rw [PaperVerification.Fermion.Endpoint.quotient, natDegree_divByMonic _ (monic_X_sub_C y), natDegree_X_sub_C, hp]
    omega

/-- Monic linear division lowers the complete coefficient cutoff by one. -/
theorem CoefficientBound.quotient {p : R[X]} {h : ℕ}
    (hp : CoefficientBound p (h + 1)) (y : R) :
    CoefficientBound (quotient p y) h := by
  by_cases hp0 : p = 0
  · simp only [hp0, PaperVerification.Fermion.Endpoint.quotient, zero_divByMonic]
    exact coefficientBound_zero h
  have hdeg : p.natDegree < h + 1 :=
    (natDegree_lt_iff_degree_lt hp0).mpr ((coefficientBound_iff_degree p (h + 1)).mp hp)
  by_cases hd0 : p.natDegree = 0
  · have hzero := quotient_coefficientBound p y 0 hd0
    exact fun j hj ↦ hzero j (Nat.zero_le j)
  · apply coefficientBound_of_natDegree_lt
    rw [PaperVerification.Fermion.Endpoint.quotient, natDegree_divByMonic _ (monic_X_sub_C y), natDegree_X_sub_C]
    omega

/-- The exact height update of a two-colour path. -/
def HeightStep (m : Mark) (h h' : ℕ) : Prop :=
  match m with
  | .unmarked => h' = h + 1
  | .theta | .xi => h' = h
  | .double => h = h' + 1

/-- Every literal endpoint update preserves monicity and the two asserted
degrees. The downward case has the required positive incoming height. -/
theorem next_shapes (S : State R) (d : Datum R) (h h' : ℕ)
    (hA : S.A.Monic) (hdegree : S.A.natDegree = h)
    (hB : CoefficientBound S.B h) (hstep : HeightStep d.mark h h') :
    (next S d).A.Monic ∧ (next S d).A.natDegree = h' ∧
      CoefficientBound (next S d).B h' := by
  cases hm : d.mark with
  | unmarked =>
    have hh : h' = h + 1 := by simpa only [HeightStep, hm] using hstep
    subst h'
    simp only [next, hm]
    refine ⟨(monic_X_sub_C d.node).mul hA, ?_, ?_⟩
    · rw [(monic_X_sub_C d.node).natDegree_mul hA, natDegree_X_sub_C, hdegree]
      omega
    · exact (hB.linear_mul d.node).sub
        ((coefficientBound_of_natDegree_lt S.A (h + 1) (by omega)).C_mul d.weight)
  | theta =>
    have hh : h' = h := by simpa only [HeightStep, hm] using hstep
    subst h'
    simp only [next, hm]
    exact ⟨hA, hdegree,
      hB.sub ((quotient_coefficientBound S.A d.node h hdegree).C_mul d.weight)⟩
  | xi =>
    have hh : h' = h := by simpa only [HeightStep, hm] using hstep
    subst h'
    simp only [next, hm]
    exact ⟨hA, hdegree,
      hB.sub ((quotient_coefficientBound S.A d.node h hdegree).C_mul d.weight)⟩
  | double =>
    have hh : h = h' + 1 := by simpa only [HeightStep, hm] using hstep
    rw [hh] at hdegree hB
    have hdivdeg : (X - C d.node : R[X]).degree ≤ S.A.degree := by
      rw [degree_X_sub_C, degree_eq_natDegree hA.ne_zero, hdegree]
      change ((1 : ℕ) : WithBot ℕ) ≤ ((h' + 1 : ℕ) : WithBot ℕ)
      exact WithBot.coe_le_coe.mpr (Nat.succ_le_succ (Nat.zero_le h'))
    simp only [next, hm]
    refine ⟨?_, ?_, ?_⟩
    · change (S.A /ₘ (X - C d.node)).leadingCoeff = 1
      rw [leadingCoeff_divByMonic_of_monic (monic_X_sub_C d.node) hdivdeg,
        hA.leadingCoeff]
    · rw [PaperVerification.Fermion.Endpoint.quotient, natDegree_divByMonic _ (monic_X_sub_C d.node),
        natDegree_X_sub_C, hdegree, Nat.add_sub_cancel]
    · exact (hB.sub
        ((quotient_coefficientBound S.A d.node (h' + 1) hdegree).C_mul d.weight)).quotient d.node

/-- The endpoint polynomial `A_k` remains monic of path height `h_k`, while
`B_k` has precisely the strict cutoff asserted in equation (16). -/
theorem run_shapes (data : ℕ → Datum R) (height : ℕ → ℕ) (hzero : height 0 = 0)
    (k : ℕ) (hsteps : ∀ j < k, HeightStep (data j).mark (height j) (height (j + 1))) :
    (run data k).A.Monic ∧ (run data k).A.natDegree = height k ∧
      CoefficientBound (run data k).B (height k) := by
  revert hsteps
  induction k with
  | zero =>
    intro hsteps
    refine ⟨monic_one, ?_, coefficientBound_zero _⟩
    simpa only [run, initial, natDegree_one] using hzero.symm
  | succ k ih =>
    intro hsteps
    obtain ⟨hA, hdegree, hB⟩ := ih (fun j hj ↦ hsteps j (Nat.lt_succ_of_lt hj))
    exact next_shapes (run data k) (data k) (height k) (height (k + 1))
      hA hdegree hB (hsteps k (Nat.lt_succ_self k))

theorem run_B_eq_zero_of_terminal_coefficients
    (data : ℕ → Datum R) (height : ℕ → ℕ) (hzero : height 0 = 0)
    (k : ℕ) (hsteps : ∀ j < k, HeightStep (data j).mark (height j) (height (j + 1)))
    (hterminal : ∀ j : Fin (height k), (run data k).B.coeff j = 0) :
    (run data k).B = 0 := by
  have hB := (run_shapes data height hzero k hsteps).2.2
  ext j
  rw [coeff_zero]
  by_cases hj : j < height k
  · exact hterminal ⟨j, hj⟩
  · exact hB j (Nat.le_of_not_gt hj)

end Nontrivial

section Field

variable {F : Type*} [Field F]

/-- The complete paired endpoint equations have only the origin as a common
zero, for every path and every positive exponent `s`.

The hypotheses are the actual recursively produced equations, the literal
height rule, and the factorization `a_i b_i = y_i^s`. There is no assumption
of a complete intersection or a length formula.
-/
theorem nodes_zero_of_endpoint_equations
    (data : ℕ → Datum F) (height : ℕ → ℕ) (hzero : height 0 = 0) (n s : ℕ)
    (hs : 0 < s)
    (hsteps : ∀ j < n, HeightStep (data j).mark (height j) (height (j + 1)))
    (hfactor : ∀ i : Fin n, (data i).leftFactor * (data i).rightFactor = (data i).node ^ s)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, (data i).beta))
    (hrelations : ∀ r ∈ allRelations data n, r = 0)
    (hterminal : ∀ j : Fin (height n), (run data n).B.coeff j = 0) :
    ∀ i : Fin n, (data i).node = 0 := by
  have hA := (run_shapes data height hzero n hsteps).1
  have hB := run_B_eq_zero_of_terminal_coefficients data height hzero n hsteps hterminal
  have hidentity := run_identity data n hrelations
  rw [hB, mul_zero] at hidentity
  have hN : (run data n).N = 0 :=
    (mul_eq_zero.mp hidentity.symm).resolve_left hA.ne_zero
  rw [run_numerator, neg_eq_zero] at hN
  have hweight (i : Fin n) : (data i).weight = (data i).beta * (data i).node ^ s := by
    rw [Datum.weight, mul_assoc, hfactor i]
  have hnodes : (fun i : Fin n ↦ (data i).node) = 0 :=
    (power_moments_zero_iff (fun i : Fin n ↦ (data i).node)
      (fun i ↦ (data i).beta) s hs (fun U hU ↦ (hβ U hU).ne_zero)).mp (by
        intro k
        simpa only [hweight] using
          power_moments_zero_of_residueNumerator_zero
            (fun i : Fin n ↦ (data i).node) (fun i ↦ (data i).weight) hN (k : ℕ))
  exact fun i ↦ congrFun hnodes i

/-- The strict endpoint equation (17) gives the same origin-only support.
The first positive moment is obtained from the exact polynomial numerator
identity, so a repeated nonzero node is not silently discarded. -/
theorem nodes_zero_of_strict_endpoint_equation
    (data : ℕ → Datum F) (height : ℕ → ℕ) (hzero : height 0 = 0) (n : ℕ)
    (hsteps : ∀ j < n, HeightStep (data j).mark (height j) (height (j + 1)))
    (hweight : ∀ i : Fin n, (data i).weight = (data i).beta)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, (data i).beta))
    (hrelations : ∀ r ∈ allRelations data n, r = 0)
    (hterminal : X * (run data n).B +
      C (∑ i : Fin n, (data i).beta) * (run data n).A = 0) :
    ∀ i : Fin n, (data i).node = 0 := by
  have hA := (run_shapes data height hzero n hsteps).1
  have hidentity := run_identity data n hrelations
  have hclear : (run data n).A *
      (X * (run data n).N + C (∑ i : Fin n, (data i).beta) * (run data n).D) = 0 := by
    linear_combination (run data n).D * hterminal - X * hidentity
  have hpoly := (mul_eq_zero.mp hclear).resolve_left hA.ne_zero
  rw [run_numerator, run_denominator] at hpoly
  simp only [hweight] at hpoly
  have hres := X_mul_residueNumerator_sub_total
    (fun i : Fin n ↦ (data i).node) (fun i ↦ (data i).beta)
  have hz : residueNumerator (fun i : Fin n ↦ (data i).node)
      (fun i ↦ (data i).beta * (data i).node) = 0 := by
    linear_combination -hres - hpoly
  have hnodes : (fun i : Fin n ↦ (data i).node) = 0 :=
    (power_moments_zero_iff (fun i : Fin n ↦ (data i).node)
      (fun i ↦ (data i).beta) 1 (by omega) (fun U hU ↦ (hβ U hU).ne_zero)).mp (by
        intro k
        simpa only [pow_one] using
          power_moments_zero_of_residueNumerator_zero
            (fun i : Fin n ↦ (data i).node)
            (fun i ↦ (data i).beta * (data i).node) hz (k : ℕ))
  exact fun i ↦ congrFun hnodes i

end Field

end PaperVerification.Fermion.Endpoint
