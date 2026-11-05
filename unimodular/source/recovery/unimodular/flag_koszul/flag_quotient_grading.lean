module

public import Recovery.Unimodular.FlagKoszul.FlagBasis

/-!
# Degree compatibility in the actual flag-algebra quotient modules

These are identities in A/J_S and its explicitly proved monomial basis. They
supply the degree hypotheses for the homogeneous coefficient-module bar proof.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators

namespace Unimodular.FlagKoszul

variable {E K : Type*} [Field K]

@[simp] theorem positive_smul_qmonomial (R : E → E → Prop) (S : Set E)
    (u : Positive R) (v : Exp E) :
    augmentedBasis R (K := K) (some u) • qmonomial R S (K := K) v = qmonomial R S (K := K) (u.1 + v) := by
  rw [augmentedBasis_some]
  change Ideal.Quotient.mk (variableIdeal R S (K := K))
    (Ideal.Quotient.mk (ideal R ∅ (K := K)) (MvPolynomial.monomial u.1 (1 : K))) *
    Ideal.Quotient.mk (variableIdeal R S (K := K))
      (Ideal.Quotient.mk (ideal R ∅ (K := K)) (MvPolynomial.monomial v (1 : K))) = _
  rw [← map_mul, ← map_mul]
  simp only [MvPolynomial.monomial_mul_monomial, one_mul, qmonomial]

theorem positive_smul_basis_of_allowed (R : E → E → Prop) (S : Set E)
    (u : Positive R) (v : Point R S) (huv : Allowed R S (u.1 + v.1)) :
    augmentedBasis R (K := K) (some u) • quotientBasis R S (K := K) v =
      quotientBasis R S (K := K) ⟨u.1 + v.1, huv⟩ := by
  rw [quotientBasis_apply, positive_smul_qmonomial, quotientBasis_apply]

theorem positive_smul_basis_of_not_allowed (R : E → E → Prop) (S : Set E)
    (u : Positive R) (v : Point R S) (huv : ¬ Allowed R S (u.1 + v.1)) :
    augmentedBasis R (K := K) (some u) • quotientBasis R S (K := K) v = 0 := by
  rw [quotientBasis_apply, positive_smul_qmonomial]
  exact qmonomial_eq_zero huv

/-- Nonzero coefficients of the actual action have exactly the sum degree. -/
theorem quotient_action_degree (R : E → E → Prop) (S : Set E)
    (u : Positive R) (v w : Point R S)
    (hc : (quotientBasis R S (K := K)).repr
      (augmentedBasis R (K := K) (some u) • quotientBasis R S (K := K) v) w ≠ 0) :
    w.1.degree = u.1.degree + v.1.degree := by
  classical
  by_cases h : Allowed R S (u.1 + v.1)
  · let z : Point R S := ⟨u.1 + v.1, h⟩
    rw [positive_smul_basis_of_allowed R S u v h, Module.Basis.repr_self] at hc
    have hzw : z = w := by
      by_contra hne
      simp [z, Finsupp.single_apply, hne] at hc
    rw [← hzw]
    simp [z]
  · rw [positive_smul_basis_of_not_allowed R S u v h, map_zero, Finsupp.zero_apply] at hc
    exact (hc rfl).elim

@[simp] theorem quotientEmptyEquiv_basis (R : E → E → Prop) (u : Point R ∅) :
    quotientEmptyEquiv R (quotientBasis R ∅ (K := K) u) = polynomialQuotientBasis R ∅ u := by
  rw [quotientBasis_apply, qmonomial, quotientEmptyEquiv_mk, polynomialQuotientBasis_apply]

theorem quotientEmptyEquiv_basis_option (R : E → E → Prop) (u : Point R ∅) :
    quotientEmptyEquiv R (quotientBasis R ∅ (K := K) u) =
      augmentedBasis R (K := K) ((pointOptionEquiv R).symm u) := by
  rw [quotientEmptyEquiv_basis, augmentedBasis, Module.Basis.reindex_apply,
    Equiv.symm_symm, Equiv.apply_symm_apply]

theorem degree_zero_iff_point_zero (R : E → E → Prop) (S : Set E) (u : Point R S) :
    u.1.degree = 0 ↔ u = zeroPoint R S := by
  rw [Finsupp.degree_eq_zero_iff]
  constructor
  · intro h; exact Subtype.ext h
  · intro h; exact congrArg Subtype.val h

def singlePositive {R : E → E → Prop} (hrefl : ∀ i, R i i) (i : E) : Positive R := by
  classical
  refine ⟨Finsupp.single i 1, ?_, ?_⟩
  · intro a ha b hb
    have hai : a = i := by by_contra h; simpa [Finsupp.single_apply, h, Ne.symm h] using ha
    have hbi : b = i := by by_contra h; simpa [Finsupp.single_apply, h, Ne.symm h] using hb
    subst a; subst b
    exact hrefl i
  · simp

@[simp] theorem singlePositive_degree {R : E → E → Prop} (hrefl : ∀ i, R i i) (i : E) :
    positiveDegree R (singlePositive hrefl i) = 1 := by simp [positiveDegree, singlePositive]

@[simp] theorem augmentedBasis_singlePositive {R : E → E → Prop} (hrefl : ∀ i, R i i) (i : E) :
    augmentedBasis R (K := K) (some (singlePositive hrefl i)) = generator (K := K) R i := by
  rw [augmentedBasis_some]
  rfl

/-- Every positive-degree quotient basis vector is a genuine degree-one
variable times a basis vector of degree one less. -/
theorem quotientBasis_positive_divisible (R : E → E → Prop) (S : Set E)
    (u : Point R S) (hdegree : 0 < u.1.degree) :
    ∃ i : E, i ∉ S ∧ ∃ v : Point R S,
      v.1.degree + 1 = u.1.degree ∧
      generator (K := K) R i • quotientBasis R S (K := K) v = quotientBasis R S (K := K) u := by
  classical
  have hunz : u.1 ≠ 0 := by intro h; simp [h] at hdegree
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hunz
  have hui : u.1 i ≠ 0 := Finsupp.mem_support_iff.mp hi
  have hsingle : Finsupp.single i 1 ≤ u.1 := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa using Nat.one_le_iff_ne_zero.mpr hui
    · simp [Finsupp.single_apply, hji, Ne.symm hji]
  let v : Point R S := ⟨u.1 - Finsupp.single i 1, allowed_of_le tsub_le_self u.2⟩
  have hsum : v.1 + Finsupp.single i 1 = u.1 := tsub_add_cancel_of_le hsingle
  refine ⟨i, fun hiS => hui (u.2.2 i hiS), v, ?_, ?_⟩
  · have he := congrArg Finsupp.degree hsum
    simpa using he
  · rw [quotientBasis_apply, variable_smul_qmonomial, hsum, quotientBasis_apply]

#print axioms quotient_action_degree
#print axioms quotientEmptyEquiv_basis_option
#print axioms degree_zero_iff_point_zero
#print axioms augmentedBasis_singlePositive
#print axioms quotientBasis_positive_divisible

end Unimodular.FlagKoszul

#check Unimodular.FlagKoszul.quotient_action_degree
