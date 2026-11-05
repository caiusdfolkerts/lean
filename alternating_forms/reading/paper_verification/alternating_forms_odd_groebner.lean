module

public import PaperVerification.AlternatingFormsOddGoodCoordinates

/-!
# A genuine quadratic Gröbner basis in the original good coordinates

The explicit order compares the odd-pencil vertex weight, then the band
diagonal weight, then the positive Hibi sorting weight. Actual quotient
normal-form coefficients satisfy these comparisons. Division therefore
leaves only chain monomials, whose independence in the original quotient
proves the full Gröbner property of the literal kernel.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

open MvPolynomial
open scoped BigOperators MonomialOrder
open Hibi WeightedMonomialOrder

variable {K : Type*} [Field K] [CharZero K]
  (k t : ℕ) (hs : t+2≤k+1)

local notation "α" => oddIntervalLower k (t+2) hs
local notation "β" => oddIntervalUpper k (t+2) hs
local notation "P" => MvPolynomial (IntervalIndex α β) K

/-- The three weights are compared in the same order as the two actual
degenerations followed by meet/join sorting. -/
def oddGoodOrder (m : MonomialOrder (IntervalIndex α β)) :
    MonomialOrder (IntervalIndex α β) :=
  weightedRefinement
    (weightedRefinement (sortingOrder α β m) (diagonalWeight α β))
    (oddGoodWeight k t hs)

theorem goodChainExponent_pairChain (I J : IntervalIndex α β) :
    goodChainExponent k t hs (pairChain α β I J)=
      pairExponent α β (meet α β I J) (join α β I J) := by
  apply MvPolynomial.monomial_left_injective (one_ne_zero : (1 : ℚ)≠0)
  change (monomial (goodChainExponent k t hs (pairChain α β I J)) 1 :
    MvPolynomial (IntervalIndex α β) ℚ) =
      monomial (pairExponent α β (meet α β I J) (join α β I J)) 1
  erw [←standardPolynomial_eq_monomial,standardPolynomial_pairChain,pair_monomial]

theorem odd_normal_term_lt (m : MonomialOrder (IntervalIndex α β))
    (I J : IntervalIndex α β) (hinc : incomparable α β I J)
    (C : OddStandardIndex k t hs)
    (hc : oddCoefficients (K := K) k t hs (X I.val*X J.val) C≠0) :
    goodChainExponent k t hs C ≺[oddGoodOrder k t hs m] pairExponent α β I J := by
  rcases odd_pair_coefficients_triangular k t hs I J C hc with hw | ⟨hw,hd⟩
  · apply lt_of_weight_lt
    simpa only [goodChainExponent_vertexWeight,pairExponent,map_add,
      Finsupp.weight_single,one_smul] using hw
  · apply lt_of_weight_eq_of_lt
    · simpa only [goodChainExponent_vertexWeight,pairExponent,map_add,
        Finsupp.weight_single,one_smul] using hw
    · rcases hd with hd | ⟨hd,hC⟩
      · apply lt_of_weight_lt
        simpa only [goodChainExponent_diagonalWeight,pairExponent,map_add,
          Finsupp.weight_single,one_smul] using hd
      · apply lt_of_weight_eq_of_lt
        · simpa only [goodChainExponent_diagonalWeight,pairExponent,map_add,
            Finsupp.weight_single,one_smul] using hd
        · rw [hC,goodChainExponent_pairChain]
          exact pair_sorting_lt α β m I J hinc

theorem oddGoodNormalForm_support (I J : IntervalIndex α β)
    (a : IntervalIndex α β →₀ ℕ)
    (ha : a∈(oddGoodNormalForm (K := K) k t hs (X I*X J)).support) :
    ∃ C : OddStandardIndex k t hs,
      oddCoefficients (K := K) k t hs (X I.val*X J.val) C≠0 ∧ a=goodChainExponent k t hs C := by
  classical
  have h := mem_support_iff.mp ha
  rw [oddGoodNormalForm_pair] at h
  simp only [Finsupp.sum,coeff_sum] at h
  obtain ⟨C,hC,hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨C,Finsupp.mem_support_iff.mp hC,?_⟩
  by_contra hne
  apply hterm
  simp only [coeff_smul,standardPolynomial_eq_monomial,coeff_monomial,
    if_neg (Ne.symm hne),smul_zero]

theorem pairExponent_ne_zero (I J : IntervalIndex α β) : pairExponent α β I J≠0 := by
  intro h
  have he := congrArg (fun a : IntervalIndex α β →₀ ℕ => a I) h
  simp only [pairExponent,Finsupp.add_apply,Finsupp.single_eq_same,
    Finsupp.zero_apply] at he
  omega

theorem oddGoodNormalForm_degree_lt (m : MonomialOrder (IntervalIndex α β))
    (I J : IntervalIndex α β) (hinc : incomparable α β I J) :
    (oddGoodOrder k t hs m).degree (oddGoodNormalForm (K := K) k t hs (X I*X J))
      ≺[oddGoodOrder k t hs m] pairExponent α β I J := by
  have hpos : 0 ≺[oddGoodOrder k t hs m] pairExponent α β I J := by
    rw [map_zero,MonomialOrder.toSyn_lt_iff_ne_zero]
    intro h
    exact pairExponent_ne_zero k t hs I J
      ((oddGoodOrder k t hs m).toSyn.injective (by simpa only [map_zero] using h))
  apply ((oddGoodOrder k t hs m).degree_lt_iff hpos).mpr
  intro a ha
  obtain ⟨C,hC,rfl⟩ := oddGoodNormalForm_support k t hs I J a ha
  exact odd_normal_term_lt k t hs m I J hinc C hC

theorem oddQuadraticRelation_degree (m : MonomialOrder (IntervalIndex α β))
    (I J : IntervalIndex α β) (hinc : incomparable α β I J) :
    (oddGoodOrder k t hs m).degree (oddQuadraticRelation (K := K) k t hs I J)=
      pairExponent α β I J := by
  classical
  have h := oddGoodNormalForm_degree_lt (K := K) k t hs m I J hinc
  have h' : (oddGoodOrder k t hs m).degree (oddGoodNormalForm (K := K) k t hs (X I*X J))
      ≺[oddGoodOrder k t hs m]
        (oddGoodOrder k t hs m).degree (X I*X J : P) := by
    simpa only [pair_monomial,MonomialOrder.degree_monomial,if_neg (one_ne_zero : (1 : K) ≠ 0)] using h
  rw [oddQuadraticRelation,(oddGoodOrder k t hs m).degree_sub_of_lt h',
    pair_monomial,MonomialOrder.degree_monomial,if_neg (one_ne_zero : (1 : K) ≠ 0)]

theorem oddQuadraticRelation_leadingCoeff (m : MonomialOrder (IntervalIndex α β))
    (I J : IntervalIndex α β) (hinc : incomparable α β I J) :
    (oddGoodOrder k t hs m).leadingCoeff (oddQuadraticRelation (K := K) k t hs I J)=1 := by
  classical
  have h := oddGoodNormalForm_degree_lt (K := K) k t hs m I J hinc
  have h' : (oddGoodOrder k t hs m).degree (oddGoodNormalForm (K := K) k t hs (X I*X J))
      ≺[oddGoodOrder k t hs m]
        (oddGoodOrder k t hs m).degree (X I*X J : P) := by
    simpa only [pair_monomial,MonomialOrder.degree_monomial,if_neg (one_ne_zero : (1 : K) ≠ 0)] using h
  rw [oddQuadraticRelation,(oddGoodOrder k t hs m).leadingCoeff_sub_of_lt h',
    pair_monomial,MonomialOrder.leadingCoeff_monomial]

theorem oddQuadraticRelation_ne_zero (m : MonomialOrder (IntervalIndex α β))
    (I J : IntervalIndex α β) (hinc : incomparable α β I J) :
    oddQuadraticRelation (K := K) k t hs I J≠0 := by
  intro h
  have hlead := oddQuadraticRelation_leadingCoeff (K := K) k t hs m I J hinc
  rw [h,MonomialOrder.leadingCoeff_zero] at hlead
  exact zero_ne_one hlead

theorem odd_remainder_normal_support (m : MonomialOrder (IntervalIndex α β))
    (p r : P) (hr : (oddGoodOrder k t hs m).IsRemainder p (oddQuadraticSet k t hs) r) :
    ∀ a∈r.support,NormalMonomial α β a := by
  intro a ha I hI J hJ
  by_contra h
  have hinc : incomparable α β I J := not_or.mp h
  have hne : I≠J := fun he => hinc.1 (he ▸ le_rfl)
  have hnot := hr.not_degree_le ha
    (show oddQuadraticRelation (K := K) k t hs I J∈oddQuadraticSet k t hs from
      ⟨I,J,hinc,rfl⟩) (oddQuadraticRelation_ne_zero k t hs m I J hinc)
  rw [oddQuadraticRelation_degree k t hs m I J hinc] at hnot
  exact hnot (pairExponent_le_of_support α β a I J hI hJ hne)

/-- The actual good-coordinate kernel of the canonical odd-pencil ring
has the asserted quadratic Gröbner basis. -/
theorem odd_good_quadratic_isGroebnerBasis (m : MonomialOrder (IntervalIndex α β)) :
    (oddGoodOrder k t hs m).IsGroebnerBasis
      (oddQuadraticSet (K := K) k t hs) (oddGoodIdeal k t hs) := by
  have hsub : oddQuadraticSet (K := K) k t hs ⊆ (oddGoodIdeal (K := K) k t hs : Set P) := by
    rintro p ⟨I,J,h,rfl⟩
    exact oddQuadraticRelation_mem k t hs I J
  apply MonomialOrder.isGroebnerBasis_iff_isRemainder_zero.mpr
  refine ⟨hsub,?_⟩
  intro p hp
  obtain ⟨r,hr⟩ := (oddGoodOrder k t hs m).exists_isRemainder (B := oddQuadraticSet (K := K) k t hs)
    (fun b hb hb0 => by
      obtain ⟨I,J,h,rfl⟩ := hb
      rw [oddQuadraticRelation_leadingCoeff k t hs m I J h]
      exact isUnit_one) p
  have hpr : p-r∈oddGoodIdeal (K := K) k t hs :=
    Ideal.span_le.mpr hsub hr.sub_mem_span
  have hrI : r∈oddGoodIdeal (K := K) k t hs := by
    simpa only [sub_sub_cancel] using (oddGoodIdeal (K := K) k t hs).sub_mem hp hpr
  have hr0 : r=0 := oddGood_normal_polynomial_eq_zero k t hs r
    (odd_remainder_normal_support k t hs m p r hr) hrI
  simpa only [hr0] using hr

theorem oddQuadraticSet_finite : (oddQuadraticSet (K := K) k t hs).Finite := by
  apply (Set.finite_range (fun a : IntervalIndex α β × IntervalIndex α β =>
    oddQuadraticRelation (K := K) k t hs a.1 a.2)).subset
  rintro p ⟨I,J,h,rfl⟩
  exact ⟨(I,J),rfl⟩

/-- Every member of the displayed finite Gröbner basis is an actual
homogeneous quadratic polynomial in the good coordinates. -/
theorem odd_good_quadratic_groebner_data (m : MonomialOrder (IntervalIndex α β)) :
    (oddQuadraticSet (K := K) k t hs).Finite ∧
    (∀ p∈oddQuadraticSet (K := K) k t hs,p.IsHomogeneous 2) ∧
    (oddGoodOrder k t hs m).IsGroebnerBasis
      (oddQuadraticSet (K := K) k t hs) (oddGoodIdeal k t hs) := by
  refine ⟨oddQuadraticSet_finite k t hs,?_,odd_good_quadratic_isGroebnerBasis k t hs m⟩
  rintro p ⟨I,J,h,rfl⟩
  exact oddQuadraticRelation_homogeneous k t hs I J

/-- The Gröbner assertion is existential in an actual monomial order;
there is no term-order or triangularity hypothesis on the original ring. -/
theorem odd_good_exists_quadratic_groebner :
    ∃ m : MonomialOrder.{0,0} (IntervalIndex α β),
      (oddQuadraticSet (K := K) k t hs).Finite ∧
      (∀ p∈oddQuadraticSet (K := K) k t hs,p.IsHomogeneous 2) ∧
      m.IsGroebnerBasis (oddQuadraticSet (K := K) k t hs) (oddGoodIdeal k t hs) :=
  ⟨oddGoodOrder k t hs (finiteBaseOrder (IntervalIndex α β)),
    odd_good_quadratic_groebner_data k t hs (finiteBaseOrder (IntervalIndex α β))⟩

end PaperVerification.AlternatingForms
