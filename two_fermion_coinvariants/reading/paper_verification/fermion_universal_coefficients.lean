module

public import PaperVerification.FermionDefinitions
public import PaperVerification.FermionIntegralJacobson
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.Data.Finset.Sum

/-!
# A literal universal coefficient ring for coupled paired data

The parameters are independent integral variables for the weights and for
every lower coefficient occurring in the given data.  A single localization
inverts exactly the factorial and all nonempty weight sums.  No equations
among lower coefficients are imposed.  This is a reduced Jacobson ring even
when the target coefficient ring has nilpotents or is the zero ring.

-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.Fermion.Universal

open MvPolynomial
open scoped BigOperators

inductive Kind
  | phi
  | left
  | right
  deriving DecidableEq, Fintype

variable {K : Type*} [CommRing K] {n : ℕ}

def degree (d : PairedData (K := K) (n := n)) : Kind → Fin n → ℕ
  | .phi,i => d.r i
  | .left,i => d.u i
  | .right,i => d.v i

def input (d : PairedData (K := K) (n := n)) : Kind → Fin n → PolynomialRing K n
  | .phi,i => d.phi i
  | .left,i => d.a i
  | .right,i => d.b i

theorem input_highest (d : PairedData (K := K) (n := n)) (k : Kind) (i : Fin n) :
    HasHighestPower d.r (input d k i) i (degree d k i) := by
  cases k
  · exact d.highest_phi i
  · exact d.highest_a i
  · exact d.highest_b i

def lowerSupport (d : PairedData (K := K) (n := n)) (k : Kind) (i : Fin n) :
    Finset (Fin n →₀ ℕ) := by
  classical
  exact (input d k i).support.erase (Finsupp.single i (degree d k i))

abbrev Variables (d : PairedData (K := K) (n := n)) :=
  Fin n ⊕ (Σ k : Kind, Σ i : Fin n, {a : Fin n →₀ ℕ // a ∈ lowerSupport d k i})

instance variables_fintype (d : PairedData (K := K) (n := n)) : Fintype (Variables d) := by
  classical
  unfold Variables
  infer_instance

abbrev Coefficients (d : PairedData (K := K) (n := n)) := MvPolynomial (Variables d) ℤ

def beta (d : PairedData (K := K) (n := n)) (i : Fin n) : Coefficients d := X (.inl i)

def nonemptySubsets (n : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.filter Finset.Nonempty

def denominator (d : PairedData (K := K) (n := n)) : Coefficients d :=
  (n.factorial : Coefficients d) *
    ∏ U ∈ nonemptySubsets n, ∑ i ∈ U, beta d i

abbrev Ring (d : PairedData (K := K) (n := n)) := Localization.Away (denominator d)

instance ring_isReduced (d : PairedData (K := K) (n := n)) : IsReduced (Ring d) :=
  inferInstance

instance ring_isJacobson (d : PairedData (K := K) (n := n)) : IsJacobsonRing (Ring d) :=
  isJacobsonRing_localization (denominator d)

def weight (d : PairedData (K := K) (n := n)) (i : Fin n) : Ring d :=
  algebraMap (Coefficients d) (Ring d) (beta d i)

theorem allowed_weights (d : PairedData (K := K) (n := n)) : AllowedWeights (weight d) := by
  have hD : IsUnit (algebraMap (Coefficients d) (Ring d) (denominator d)) :=
    IsLocalization.Away.algebraMap_isUnit (denominator d)
  change IsUnit (algebraMap (Coefficients d) (Ring d)
    ((n.factorial : Coefficients d) * ∏ U ∈ nonemptySubsets n, ∑ i ∈ U, beta d i)) at hD
  rw [map_mul,map_natCast] at hD
  obtain ⟨hfac,hprod⟩ := IsUnit.mul_iff.mp hD
  refine ⟨hfac,?_⟩
  intro U hU
  have hmem : U ∈ nonemptySubsets n := by simp [nonemptySubsets,hU]
  have hdiv : (∑ i ∈ U, beta d i) ∣
      ∏ V ∈ nonemptySubsets n, ∑ i ∈ V, beta d i :=
    Finset.dvd_prod_of_mem _ hmem
  have hunit := isUnit_of_dvd_unit (map_dvd (algebraMap (Coefficients d) (Ring d)) hdiv) hprod
  simpa only [map_sum,weight] using hunit

def coefficient (d : PairedData (K := K) (n := n)) (k : Kind) (i : Fin n)
    (a : {a : Fin n →₀ ℕ // a ∈ lowerSupport d k i}) : Ring d :=
  algebraMap (Coefficients d) (Ring d) (X (.inr ⟨k,i,a⟩))

/-- The leading coefficient is the integer one; only strictly lower
coefficients are independent variables. -/
def polynomial (d : PairedData (K := K) (n := n)) (k : Kind) (i : Fin n) :
    PolynomialRing (Ring d) n :=
  monomial (Finsupp.single i (degree d k i)) 1 +
    ∑ a : {a : Fin n →₀ ℕ // a ∈ lowerSupport d k i}, monomial a.val (coefficient d k i a)

theorem lowerSupport_ne_leading (d : PairedData (K := K) (n := n)) (k : Kind) (i : Fin n)
    (a : {a : Fin n →₀ ℕ // a ∈ lowerSupport d k i}) :
    a.val ≠ Finsupp.single i (degree d k i) :=
  (Finset.mem_erase.mp a.property).1

theorem polynomial_leading_coeff (d : PairedData (K := K) (n := n)) (k : Kind) (i : Fin n) :
    (polynomial d k i).coeff (Finsupp.single i (degree d k i)) = 1 := by
  classical
  rw [polynomial,MvPolynomial.coeff_add,coeff_monomial,if_pos rfl,coeff_sum]
  have hz : (∑ a : {a : Fin n →₀ ℕ // a ∈ lowerSupport d k i},
      (monomial a.val (coefficient d k i a)).coeff (Finsupp.single i (degree d k i))) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    rw [coeff_monomial,if_neg (lowerSupport_ne_leading d k i a)]
  rw [hz,add_zero]

theorem polynomial_coeff_zero_of_outside (d : PairedData (K := K) (n := n))
    (k : Kind) (i : Fin n) (a : Fin n →₀ ℕ)
    (hne : a ≠ Finsupp.single i (degree d k i)) (hnot : a ∉ lowerSupport d k i) :
    (polynomial d k i).coeff a = 0 := by
  classical
  rw [polynomial,MvPolynomial.coeff_add,coeff_monomial,if_neg hne.symm,zero_add,coeff_sum]
  apply Finset.sum_eq_zero
  intro b hb
  rw [coeff_monomial,if_neg (by intro he; exact hnot (he ▸ b.property))]

theorem polynomial_highest (d : PairedData (K := K) (n := n)) (k : Kind) (i : Fin n) :
    HasHighestPower d.r (polynomial d k i) i (degree d k i) := by
  refine ⟨polynomial_leading_coeff d k i,?_⟩
  intro a ha hne
  have hm : a ∈ lowerSupport d k i := by
    by_contra hn
    exact (MvPolynomial.mem_support_iff.mp ha)
      (polynomial_coeff_zero_of_outside d k i a hne hn)
  exact (input_highest d k i).2 a (Finset.mem_of_mem_erase hm) hne

/-- Every coefficient can be specialized to its original value. -/
def values (d : PairedData (K := K) (n := n)) : Variables d → K
  | .inl i => d.beta i
  | .inr ⟨k,i,a⟩ => (input d k i).coeff a.val

def evaluation (d : PairedData (K := K) (n := n)) : Coefficients d →+* K :=
  MvPolynomial.eval₂Hom (Int.castRingHom K) (values d)

@[simp] theorem evaluation_beta (d : PairedData (K := K) (n := n)) (i : Fin n) :
    evaluation d (beta d i) = d.beta i := by
  simp only [evaluation,beta,eval₂Hom_X',values]

theorem evaluation_denominator_isUnit (d : PairedData (K := K) (n := n)) :
    IsUnit (evaluation d (denominator d)) := by
  rw [denominator,map_mul,map_natCast,map_prod]
  apply d.allowed_weights.1.mul
  apply IsUnit.prod_iff.mpr
  intro U hU
  rw [map_sum]
  simp only [evaluation_beta]
  exact d.allowed_weights.2 U ((Finset.mem_filter.mp hU).2)

def specialize (d : PairedData (K := K) (n := n)) : Ring d →+* K :=
  IsLocalization.Away.lift (denominator d) (evaluation_denominator_isUnit d)

@[simp] theorem specialize_algebraMap (d : PairedData (K := K) (n := n)) (p : Coefficients d) :
    specialize d (algebraMap (Coefficients d) (Ring d) p) = evaluation d p :=
  IsLocalization.Away.lift_eq (denominator d) (evaluation_denominator_isUnit d) p

@[simp] theorem specialize_weight (d : PairedData (K := K) (n := n)) (i : Fin n) :
    specialize d (weight d i) = d.beta i := by
  rw [weight,specialize_algebraMap,evaluation_beta]

@[simp] theorem specialize_coefficient (d : PairedData (K := K) (n := n)) (k : Kind) (i : Fin n)
    (a : {a : Fin n →₀ ℕ // a ∈ lowerSupport d k i}) :
    specialize d (coefficient d k i a) = (input d k i).coeff a.val := by
  rw [coefficient,specialize_algebraMap]
  simp only [evaluation,eval₂Hom_X',values]

theorem polynomial_lower_coeff (d : PairedData (K := K) (n := n)) (k : Kind) (i : Fin n)
    (a : {a : Fin n →₀ ℕ // a ∈ lowerSupport d k i}) :
    (polynomial d k i).coeff a.val = coefficient d k i a := by
  classical
  rw [polynomial,MvPolynomial.coeff_add,coeff_monomial,
    if_neg (lowerSupport_ne_leading d k i a).symm,zero_add,coeff_sum]
  rw [Finset.sum_eq_single a]
  · rw [coeff_monomial,if_pos rfl]
  · intro b hb hba
    rw [coeff_monomial,if_neg (by intro he; exact hba (Subtype.ext he))]
  · simp

/-- Specialization recovers every original coupled polynomial, including all
its lower coefficients. -/
@[simp] theorem specialize_polynomial (d : PairedData (K := K) (n := n)) (k : Kind) (i : Fin n) :
    MvPolynomial.map (specialize d) (polynomial d k i) = input d k i := by
  classical
  apply MvPolynomial.ext
  intro a
  rw [MvPolynomial.coeff_map]
  by_cases he : a = Finsupp.single i (degree d k i)
  · subst a
    rw [polynomial_leading_coeff,map_one,(input_highest d k i).1]
  · by_cases hm : a ∈ lowerSupport d k i
    · have hh := polynomial_lower_coeff d k i ⟨a,hm⟩
      rw [hh,specialize_coefficient]
    · rw [polynomial_coeff_zero_of_outside d k i a he hm,map_zero]
      symm
      apply MvPolynomial.notMem_support_iff.mp
      intro ha
      exact hm (Finset.mem_erase.mpr ⟨he,ha⟩)

/-- The actual universal data satisfy the same unrestricted parameter
hypotheses, with the original cover degrees and degree splits. -/
def data (d : PairedData (K := K) (n := n)) : PairedData (K := Ring d) (n := n) where
  positive_n := d.positive_n
  s := d.s
  positive_s := d.positive_s
  r := d.r
  u := d.u
  v := d.v
  positive_r := d.positive_r
  degree_split := d.degree_split
  beta := weight d
  allowed_weights := allowed_weights d
  phi := polynomial d .phi
  a := polynomial d .left
  b := polynomial d .right
  highest_phi := polynomial_highest d .phi
  highest_a := polynomial_highest d .left
  highest_b := polynomial_highest d .right

@[simp] theorem data_specialize_phi (d : PairedData (K := K) (n := n)) (i : Fin n) :
    MvPolynomial.map (specialize d) ((data d).phi i) = d.phi i :=
  specialize_polynomial d .phi i

@[simp] theorem data_specialize_left (d : PairedData (K := K) (n := n)) (i : Fin n) :
    MvPolynomial.map (specialize d) ((data d).a i) = d.a i :=
  specialize_polynomial d .left i

@[simp] theorem data_specialize_right (d : PairedData (K := K) (n := n)) (i : Fin n) :
    MvPolynomial.map (specialize d) ((data d).b i) = d.b i :=
  specialize_polynomial d .right i

end PaperVerification.Fermion.Universal
