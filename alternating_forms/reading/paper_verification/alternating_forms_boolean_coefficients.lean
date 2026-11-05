module

public import PaperVerification.AlternatingFormsBoolean
public import PaperVerification.AlternatingFormsEvenDeterminants
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Data.Finsupp.Indicator
import Lean.Elab.Tactic.Omega

/-!
# Actual square-free polynomial coefficient spaces

The finite coordinate model is proved equivalent to the concrete homogeneous
multiaffine subspace of the ordinary polynomial ring. Directional derivatives
are computed on the original polynomial, including the vanishing of possible
repeated-variable terms. These are the coefficient spaces dual to the actual
Boolean multiplication matrices used in the even-pencil decomposition.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.BooleanCoefficients

open scoped BigOperators
open MvPolynomial
open EvenDeterminants

variable {K ι : Type*} [CommRing K] [Fintype ι] [DecidableEq ι]

/-- The ordinary square-free exponent attached to a finite subset. -/
def subsetExponent (s : Finset ι) : ι →₀ ℕ :=
  Finsupp.indicator s (fun _ _ => 1)

@[simp] theorem subsetExponent_apply (s : Finset ι) (i : ι) :
    subsetExponent s i = if i ∈ s then 1 else 0 := by
  simp [subsetExponent, Finsupp.indicator_apply]

@[simp] theorem subsetExponent_support (s : Finset ι) :
    (subsetExponent s).support = s := by
  ext i
  simp [Finsupp.mem_support_iff, subsetExponent_apply]

theorem subsetExponent_injective : Function.Injective (subsetExponent (ι := ι)) := by
  intro s t h
  simpa only [subsetExponent_support] using congrArg Finsupp.support h

@[simp] theorem subsetExponent_degree (s : Finset ι) :
    (subsetExponent s).degree = s.card := by
  rw [Finsupp.degree_apply, subsetExponent_support]
  simp only [subsetExponent_apply, Finset.mem_of_mem_filter]
  simp

def subsetMonomial (s : Finset ι) : MvPolynomial ι K :=
  monomial (subsetExponent s) 1

theorem subsetMonomial_eq_prod (s : Finset ι) :
    subsetMonomial (K := K) s = ∏ i ∈ s, (X i : MvPolynomial ι K) := by
  simpa only [subsetMonomial, subsetExponent, pow_one] using
    (MvPolynomial.prod_X_pow (R := K) (fun _ : ι => 1) s).symm

@[simp] theorem subsetMonomial_coeff (s t : Finset ι) :
    (subsetMonomial (K := K) s).coeff (subsetExponent t) =
      if s = t then 1 else 0 := by
  simp only [subsetMonomial, coeff_monomial, subsetExponent_injective.eq_iff]

/-- Actual expansion in the square-free monomials of degree q. -/
def evaluation (q : ℕ) :
    (FixedSubsets ι q → K) →ₗ[K] MvPolynomial ι K where
  toFun c := ∑ U, c U • subsetMonomial U.val
  map_add' c d := by simp [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a c := by simp [Pi.smul_apply, smul_smul, Finset.smul_sum]

theorem evaluation_coeff (q : ℕ) (c : FixedSubsets ι q → K)
    (U : FixedSubsets ι q) :
    (evaluation q c).coeff (subsetExponent U.val) = c U := by
  classical
  simp only [evaluation, LinearMap.coe_mk, AddHom.coe_mk, coeff_sum, coeff_smul,
    subsetMonomial_coeff, smul_eq_mul]
  have he (V : FixedSubsets ι q) : V.val = U.val ↔ V = U := Subtype.val_inj
  simp only [he, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem evaluation_injective (q : ℕ) : Function.Injective (evaluation (K := K) (ι := ι) q) := by
  intro c d h
  funext U
  have hc := congrArg (fun f : MvPolynomial ι K => f.coeff (subsetExponent U.val)) h
  simpa only [evaluation_coeff] using hc

/-- A supported exponent of a multiaffine homogeneous polynomial is an actual q-subset. -/
theorem support_exponent_subset (q : ℕ) (f : MvPolynomial ι K)
    (hhom : f.IsHomogeneous q) (hmulti : ∀ i, f.degreeOf i ≤ 1)
    (d : ι →₀ ℕ) (hd : d ∈ f.support) :
    ∃ U : FixedSubsets ι q, subsetExponent U.val = d := by
  have hbound (i : ι) : d i ≤ 1 :=
    (MvPolynomial.monomial_le_degreeOf i hd).trans (hmulti i)
  have hdegree : d.degree = q := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp hd) (hhom.coeff_eq_zero h)
  have he : subsetExponent d.support = d := by
    ext i
    by_cases hi : i ∈ d.support
    · have hn : d i ≠ 0 := Finsupp.mem_support_iff.mp hi
      have hiBound := hbound i
      simp only [subsetExponent_apply, hi, if_true]
      omega
    · simp only [subsetExponent_apply, hi, if_false,
        Finsupp.notMem_support_iff.mp hi]
  refine ⟨⟨d.support, ?_⟩, he⟩
  have hh := congrArg Finsupp.degree he
  simpa only [subsetExponent_degree, hdegree] using hh

/-- The concrete finite coefficient expansion recovers every homogeneous
multiaffine polynomial; no basis-size assertion is assumed. -/
theorem evaluation_coefficients_eq (q : ℕ) (f : MvPolynomial ι K)
    (hhom : f.IsHomogeneous q) (hmulti : ∀ i, f.degreeOf i ≤ 1) :
    evaluation q (fun U => f.coeff (subsetExponent U.val)) = f := by
  apply MvPolynomial.ext
  intro d
  by_cases hd : ∃ U : FixedSubsets ι q, subsetExponent U.val = d
  · obtain ⟨U, rfl⟩ := hd
    exact evaluation_coeff q _ U
  · have hz : f.coeff d = 0 := by
      apply MvPolynomial.notMem_support_iff.mp
      intro hs
      exact hd (support_exponent_subset q f hhom hmulti d hs)
    rw [hz]
    change (∑ U : FixedSubsets ι q,
      f.coeff (subsetExponent U.val) • subsetMonomial U.val).coeff d = 0
    rw [coeff_sum]
    apply Finset.sum_eq_zero
    intro U hU
    have hne : subsetExponent U.val ≠ d := fun h => hd ⟨U, h⟩
    simp only [coeff_smul, subsetMonomial, coeff_monomial, if_neg hne, smul_zero]

theorem directionalDerivative_eq_sum (b : ι → K) :
    directionalDerivative b =
      ∑ i, (MvPolynomial.C (b i) : MvPolynomial ι K) • MvPolynomial.pderiv i := by
  apply MvPolynomial.derivation_ext
  intro j
  rw [directionalDerivative_X]
  simp [sum_apply, Derivation.smul_apply, MvPolynomial.pderiv_X,
    smul_eq_mul, Pi.single_apply, mul_ite]

/-- The exact coefficient formula for the original derivation. -/
theorem directionalDerivative_coeff (b : ι → K) (f : MvPolynomial ι K)
    (d : ι →₀ ℕ) :
    (directionalDerivative b f).coeff d =
      ∑ i, b i * (f.coeff (d + Finsupp.single i 1) * (d i + 1)) := by
  rw [directionalDerivative_eq_sum]
  simp only [sum_apply, Derivation.smul_apply, smul_eq_mul,
    coeff_sum, coeff_C_mul, MvPolynomial.coeff_pderiv]

theorem subsetExponent_insert {s : Finset ι} {i : ι} (hi : i ∉ s) :
    subsetExponent s + Finsupp.single i 1 = subsetExponent (insert i s) := by
  ext j
  simp only [Finsupp.add_apply, Finsupp.single_apply, subsetExponent_apply,
    Finset.mem_insert]
  by_cases hji : j = i
  · subst j
    simp [hi]
  · simp [hji, Ne.symm hji]

/-- On a genuine multiaffine polynomial, the square-free derivative matrix has
only the expected insertion coefficients; repeated-variable terms vanish. -/
theorem directionalDerivative_subset_coeff (b : ι → K) (f : MvPolynomial ι K)
    (hmulti : ∀ i, f.degreeOf i ≤ 1) (T : Finset ι) :
    (directionalDerivative b f).coeff (subsetExponent T) =
      ∑ i ∈ Finset.univ.filter (fun i => i ∉ T),
        b i * f.coeff (subsetExponent (insert i T)) := by
  rw [directionalDerivative_coeff, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hm : i ∈ T
  · have hz : f.coeff (subsetExponent T + Finsupp.single i 1) = 0 := by
      apply MvPolynomial.notMem_support_iff.mp
      apply MvPolynomial.notMem_support_of_degreeOf_lt i
      simp only [Finsupp.add_apply, subsetExponent_apply, hm, if_true,
        Finsupp.single_eq_same]
      exact lt_of_le_of_lt (hmulti i) (by decide)
    simp only [hm, not_true_eq_false, if_false, hz, zero_mul, mul_zero]
  · rw [subsetExponent_insert hm]
    simp [subsetExponent_apply, hm]

end PaperVerification.AlternatingForms.BooleanCoefficients

