module

public import PaperVerification.FermionNewtonBasis
public import PaperVerification.FermionOrdinaryParameters
public import PaperVerification.FermionCompleteIntersectionLength

/-!
# Actual Newton contractions: degrees, regularity and colength

The displayed polynomial contractions generate the contraction ideal by the
literal Newton basis. Their homogeneous degrees are the paper's signed
heights. Positive heights give an actual homogeneous system of parameters,
and hence the exact product formula for its finite quotient.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Newton

open MvPolynomial
open scoped BigOperators

variable {F : Type*} [Field F] {n : ℕ}

/-- The height of Section 2, with the whole preceding signed prefix. -/
def profileHeight (δ : Fin n → ℕ) (σ : Fin n → ℤ) (i : Fin n) : ℤ :=
  (δ i : ℤ) + ∑ j ∈ Finset.univ.filter (fun j ↦ j < i), σ j

def heightDegree (δ : Fin n → ℕ) (σ : Fin n → ℤ) (i : Fin n) : ℕ :=
  δ i + (earlierPositive σ i).card - (earlierNegative σ i).card

theorem profileHeight_eq_card_difference
    (δ : Fin n → ℕ) (σ : Fin n → ℤ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1) (i : Fin n) :
    profileHeight δ σ i = (δ i : ℤ) + (earlierPositive σ i).card -
      (earlierNegative σ i).card := by
  have h := allOneHeight_eq_card_difference σ hσ i
  unfold profileHeight allOneHeight at *
  omega

theorem heightDegree_cast
    (δ : Fin n → ℕ) (σ : Fin n → ℤ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (i : Fin n) (hi : 0 ≤ profileHeight δ σ i) :
    (heightDegree δ σ i : ℤ) = profileHeight δ σ i := by
  rw [profileHeight_eq_card_difference δ σ hσ i] at hi ⊢
  unfold heightDegree
  omega

theorem columnNumeratorDegree_eq_denominator_add_height
    (δ : Fin n → ℕ) (σ : Fin n → ℤ) (i : Fin n)
    (hi : (earlierNegative σ i).card ≤ δ i + (earlierPositive σ i).card) :
    columnNumeratorDegree δ σ i = negativeEdgeCount σ + heightDegree δ σ i := by
  unfold columnNumeratorDegree heightDegree
  omega

/-- Rational homogeneity retains an actual polynomial numerator and a
nonzero homogeneous denominator, with their integer degree difference. -/
def IsRationalHomogeneous (z : RationalFunctions (F := F) (n := n)) (d : ℤ) : Prop :=
  ∃ (A Q : P (F := F) (n := n)) (a q : ℕ), Q ≠ 0 ∧ A.IsHomogeneous a ∧
    Q.IsHomogeneous q ∧ (a : ℤ) - q = d ∧
    algebraMap (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n)) A =
      algebraMap (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n)) Q * z

/-- Every displayed rational coordinate has exactly the signed degree
stated in Proposition 2.2, including negative heights. -/
theorem newtonColumn_rational_homogeneous
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) (hc : Compatible δ σ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1) (i k : Fin n) :
    IsRationalHomogeneous (newtonColumn β δ σ i k) (profileHeight δ σ i) := by
  refine ⟨columnCommonNumerator β δ σ hc i k, negativeDenominator σ,
    columnNumeratorDegree δ σ i, negativeEdgeCount σ,
    negativeDenominator_ne_zero σ,
    columnCommonNumerator_homogeneous β δ σ hc i k,
    negativeDenominator_homogeneous σ, ?_,
    map_columnCommonNumerator β δ σ hc i k⟩
  rw [profileHeight_eq_card_difference δ σ hσ i]
  have hle := earlierNegative_card_le σ i
  unfold columnNumeratorDegree
  omega

/-- Polynomial contraction has the nonnegative signed degree whenever
that signed height is nonnegative. No desired degree is assumed. -/
theorem columnContraction_homogeneous
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) (hc : Compatible δ σ)
    (hβ : ∀ k, β k ≠ 0) (i : Fin n)
    (hi : (earlierNegative σ i).card ≤ δ i + (earlierPositive σ i).card) :
    (columnContraction β δ σ i).IsHomogeneous (heightDegree δ σ i) := by
  have he := columnCommonNumerator_weighted_sum β δ σ hc hβ i
  have hs : (∑ k, C (β k) * columnCommonNumerator β δ σ hc i k).IsHomogeneous
      (columnNumeratorDegree δ σ i) := by
    apply IsHomogeneous.sum
    intro k hk
    exact (columnCommonNumerator_homogeneous β δ σ hc i k).C_mul _
  rw [he] at hs
  by_cases hz : columnContraction β δ σ i = 0
  · rw [hz]
    exact isHomogeneous_zero (Fin n) F _
  · have hp0 := mul_ne_zero (negativeDenominator_ne_zero (F := F) σ) hz
    have hq := hs.of_mul_right hp0
    have hd := hs.totalDegree hp0
    rw [totalDegree_mul_of_isDomain (negativeDenominator_ne_zero σ) hz,
      (negativeDenominator_homogeneous σ).totalDegree (negativeDenominator_ne_zero σ),
      columnNumeratorDegree_eq_denominator_add_height δ σ i hi] at hd
    have hdegree : (columnContraction β δ σ i).totalDegree = heightDegree δ σ i := by omega
    simpa only [hdegree] using hq

/-- High ordinary moments put every coordinate in the radical of the
actual contraction ideal, independently of any length assertion. -/
theorem variable_mem_contraction_radical
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i)) (i : Fin n) :
    X i ∈ (contractionIdeal β δ σ).radical := by
  let b : ℕ := 1 + ∑ j, δ j
  have hb (j : Fin n) : δ j ≤ b := by
    have h := Finset.single_le_sum (fun k _ ↦ Nat.zero_le (δ k)) (Finset.mem_univ j)
    dsimp only [b]
    omega
  have h := common_polynomial_mem_radical (contractionIdeal β δ σ)
    (fun j : Fin n ↦ (X j : P (F := F) (n := n))) β (Polynomial.X ^ b) hβ
    (fun k ↦ ordinaryMomentIdeal_le_contractionIdeal β δ σ b hb
      (Ideal.subset_span ⟨k,rfl⟩)) i
  simp only [map_pow, Polynomial.aeval_X] at h
  exact Ideal.mem_radical_of_pow_mem h

theorem contraction_origin_le_radical
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i)) :
    HomogeneousLocalization.originIdeal (K := F) (ι := Fin n) ≤
      (contractionIdeal β δ σ).radical := by
  rw [originIdeal_eq_polynomialOrigin_ker, ← span_variables_eq_origin]
  apply Ideal.span_le.mpr
  rintro _ ⟨i,rfl⟩
  exact variable_mem_contraction_radical β δ σ hβ i

/-- The literal polynomial contractions form the full regular sequence
asserted in Proposition 2.3 when all its heights are positive. -/
theorem columnContractions_isWeaklyRegular
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) (hc : Compatible δ σ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i))
    (hheight : ∀ i, 0 < profileHeight δ σ i) :
    RingTheory.Sequence.IsWeaklyRegular (P (F := F) (n := n))
      (List.ofFn (columnContraction β δ σ)) := by
  have hn (i : Fin n) : (earlierNegative σ i).card ≤ δ i + (earlierPositive σ i).card := by
    have h := hheight i
    rw [profileHeight_eq_card_difference δ σ hσ i] at h
    omega
  have hh (i : Fin n) := columnContraction_homogeneous β δ σ hc
    (singleton_weight_ne_zero β hβ) i (hn i)
  apply HomogeneousLocalization.homogeneous_family_regular (fun _ ↦ 1) (by simp)
  · intro i
    exact ⟨heightDegree δ σ i, hh i⟩
  · intro i
    rw [MvPolynomial.constantCoeff_eq]
    have hi : 0 < heightDegree δ σ i := by
      have h := hheight i
      have hd := heightDegree_cast δ σ hσ i (le_of_lt h)
      omega
    exact (hh i).coeff_eq_zero (d := 0) (by simpa using hi.ne'.symm)
  · rw [span_columnContractions_eq_contractionIdeal β δ σ hc hσ hβ]
    exact contraction_origin_le_radical β δ σ hβ

/-- The exact product of positive heights is the length of the actual
Newton contraction quotient. This is independent of the later box basis. -/
theorem contraction_quotient_finrank
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) (hc : Compatible δ σ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i))
    (hheight : ∀ i, 0 < profileHeight δ σ i) :
    Module.finrank F (P (F := F) (n := n) ⧸ contractionIdeal β δ σ) =
      ∏ i, heightDegree δ σ i := by
  letI := contraction_quotient_finite β δ σ hβ
  have hI := span_columnContractions_eq_contractionIdeal β δ σ hc hσ hβ
  letI : Module.Finite F (P (F := F) (n := n) ⧸ Ideal.span (Set.range (columnContraction β δ σ))) := by
    rw [hI]
    infer_instance
  have hhom (i : Fin n) : (columnContraction β δ σ i).IsWeightedHomogeneous
      (fun _ ↦ 1) (heightDegree δ σ i) := by
    apply columnContraction_homogeneous β δ σ hc (singleton_weight_ne_zero β hβ) i
    have h := hheight i
    rw [profileHeight_eq_card_difference δ σ hσ i] at h
    omega
  have h := GradedHilbert.homogeneous_complete_intersection_finrank
    (columnContraction β δ σ) (heightDegree δ σ) hhom
    (columnContractions_isWeaklyRegular β δ σ hc hσ hβ hheight)
  change Module.finrank F (MvPolynomial (Fin n) F ⧸ contractionIdeal β δ σ) = _
  rw [← hI]
  exact h

end PaperVerification.Fermion.Newton
