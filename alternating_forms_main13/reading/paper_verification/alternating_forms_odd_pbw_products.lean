module

public import PaperVerification.AlternatingFormsOddBarWords
public import PaperVerification.AlternatingFormsPBWWordOrder

/-!
# Actual multiplication lowers the PBW word filtration

Every coefficient below is a coefficient of a genuine product in the
original odd isotropic Plucker quotient. Homogeneity gives the exact
internal degree, the established Groebner basis bounds the monomial
exponent, and literal inversion counts deal with equality of exponents.
Thus every nonnormal adjacent product lowers the finite word weight in
every surrounding tensor word.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators MonomialOrder

namespace PaperVerification.AlternatingForms

open MvPolynomial Hibi PaperVerification.AugmentedAlgebraBasis

universe u
variable {K : Type u} [Field K] [CharZero K]
  (k t : ℕ) (hs : t+2≤k+1)

local notation "α" => oddIntervalLower k (t+2) hs
local notation "β" => oddIntervalUpper k (t+2) hs
local notation "I" => IntervalIndex α β
local notation "B" => oddAugmentedBasis (K := K) k t hs
local notation "B₀" => oddPluckerStandardBasis (K := K) k t hs
local notation "e" => oddPositiveWordEquiv (K := K) k t hs

theorem oddAugmentedBasis_repr_some
    (x : MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸
      isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k))
    (C : OddPositiveStandardIndex (K := K) k t hs) :
    (B).repr x (some C)=(B₀).repr x C.down.val := by
  rw [oddAugmentedBasis,Module.Basis.repr_reindex_apply]
  rfl

theorem odd_productCoefficient_actual
    (C D E : OddPositiveStandardIndex (K := K) k t hs) :
    productCoefficients B C D E=
      (B₀).repr (B₀ C.down.val*B₀ D.down.val) E.down.val := by
  rw [productCoefficients,positiveCoordinates_apply]
  change (B).repr (B (some C)*B (some D)) (some E)=_
  rw [oddAugmentedBasis_repr_some,oddAugmentedBasis_some,oddAugmentedBasis_some]

theorem oddGoodMap_product_monomial
    (C D : OddPositiveStandardIndex (K := K) k t hs) :
    oddGoodMap k t hs
      (monomial (goodChainExponent k t hs C.down.val+
        goodChainExponent k t hs D.down.val) (1 : K))=
      B₀ C.down.val*B₀ D.down.val := by
  rw [←one_mul (1 : K),←monomial_mul,
    ←standardPolynomial_eq_monomial k t hs C.down.val,
    ←standardPolynomial_eq_monomial k t hs D.down.val,
    map_mul,oddGoodMap_standardPolynomial,oddGoodMap_standardPolynomial]

theorem odd_productCoefficient_normalForm
    (C D E : OddPositiveStandardIndex (K := K) k t hs) :
    productCoefficients B C D E=
      (oddGoodNormalForm k t hs
        (monomial (goodChainExponent k t hs C.down.val+
          goodChainExponent k t hs D.down.val) (1 : K))).coeff (goodChainExponent k t hs E.down.val) := by
  rw [oddGoodNormalForm,oddGoodRepresentative_coeff,oddGoodMap_product_monomial,
    odd_productCoefficient_actual]

theorem odd_productCoefficient_degree
    (C D E : OddPositiveStandardIndex (K := K) k t hs)
    (h : productCoefficients B C D E≠0) :
    oddPositiveDegree k t hs E=oddPositiveDegree k t hs C+oddPositiveDegree k t hs D := by
  have h' : oddCoefficients (K := K) k t hs
      (oddStandardRepresentative k t hs C.down.val*
        oddStandardRepresentative k t hs D.down.val) E.down.val≠0 := by
    simpa only [odd_productCoefficient_actual,oddCoefficients,
      oddPluckerStandardBasis_apply,map_mul] using h
  exact oddCoefficients_degree_eq k t hs _ _
    ((oddStandardRepresentative_homogeneous (K := K) k t hs C.down.val).mul
      (oddStandardRepresentative_homogeneous (K := K) k t hs D.down.val)) E.down.val h'

theorem odd_productCoefficient_exponent_le (m : MonomialOrder I)
    (C D E : OddPositiveStandardIndex (K := K) k t hs)
    (h : productCoefficients B C D E≠0) :
    goodChainExponent k t hs E.down.val ≼[oddGoodOrder k t hs m]
      goodChainExponent k t hs C.down.val+goodChainExponent k t hs D.down.val := by
  apply oddGoodNormalForm_monomial_term_le (K := K) k t hs m
  apply mem_support_iff.mpr
  rwa [←odd_productCoefficient_normalForm k t hs C D E]

theorem word_eq_monomial_exponent (L : List I) :
    word (K := K) α β L=monomial (PBWWords.exponent L) 1 := by
  induction L with
  | nil => simp only [word_nil,PBWWords.exponent,monomial_zero',map_one]
  | cons a L ih =>
    rw [word_cons,ih]
    simp only [X,monomial_mul,one_mul,PBWWords.exponent]

theorem oddPositiveWord_exponent (C : OddPositiveStandardIndex (K := K) k t hs) :
    PBWWords.exponent (e C).val=goodChainExponent k t hs C.down.val := by
  change PBWWords.exponent (List.ofFn (intervalIndexOfChain α β C.down.val.2)) = _
  apply MvPolynomial.monomial_left_injective (one_ne_zero : (1 : K)≠0)
  change (monomial (PBWWords.exponent (List.ofFn (intervalIndexOfChain α β C.down.val.2))) 1 :
    MvPolynomial I K) = monomial (goodChainExponent k t hs C.down.val) 1
  rw [←word_eq_monomial_exponent k t hs,←standardPolynomial_eq_monomial]
  simp only [word,List.map_ofFn,List.prod_ofFn,standardPolynomial,Function.comp_def]

/-- This is the strict filtration bound for every actual nonzero
coefficient of every nonnormal adjacent product, in every context. -/
theorem odd_productCoefficient_context_weight_lt (m : MonomialOrder I)
    (P Q : List I) (C D E : OddPositiveStandardIndex (K := K) k t hs)
    (h : productCoefficients B C D E≠0)
    (hnormal : ¬((e C).val++(e D).val).IsChain (·≤·)) :
    PBWWords.weight (oddGoodOrder k t hs m) (·≤·)
      (P++((e C).val++(e D).val)++Q).length (P++(e E).val++Q) <
    PBWWords.weight (oddGoodOrder k t hs m) (·≤·)
      (P++((e C).val++(e D).val)++Q).length (P++((e C).val++(e D).val)++Q) := by
  apply PBWWords.weight_context_lt
  · have hd := odd_productCoefficient_degree k t hs C D E h
    simp only [List.length_append,oddPositiveWord_degree]
    omega
  · simpa only [PBWWords.exponent_append,oddPositiveWord_exponent] using
      odd_productCoefficient_exponent_le k t hs m C D E h
  · exact fun hp ↦ hnormal (List.isChain_iff_pairwise.mpr hp)
  · exact List.isChain_iff_pairwise.mp (e E).property.2

end PaperVerification.AlternatingForms

