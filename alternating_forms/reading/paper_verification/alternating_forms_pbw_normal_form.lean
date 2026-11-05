module

public import PaperVerification.AlternatingFormsOddGroebner

/-!
# Bounds for every actual PBW product

The previously proved quadratic Groebner basis controls arbitrary products,
not only pairs of generators. The normal form used here is the actual
coordinate expansion in the original odd Plucker quotient. Its support
and degree bounds therefore apply to the actual reduced bar differential.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

open MvPolynomial
open scoped BigOperators MonomialOrder
open Hibi

variable {K : Type*} [Field K] [CharZero K]
  (k t : ℕ) (hs : t+2≤k+1)

local notation "α" => oddIntervalLower k (t+2) hs
local notation "β" => oddIntervalUpper k (t+2) hs
local notation "P" => MvPolynomial (IntervalIndex α β) K
local notation "𝔅" => oddPluckerStandardBasis (K := K) k t hs

theorem goodChainExponent_support (C : OddStandardIndex k t hs)
    (I : IntervalIndex α β) (hI : I∈(goodChainExponent k t hs C).support) :
    ∃ j : Fin C.1,intervalIndexOfChain α β C.2 j=I := by
  classical
  by_contra h
  apply Finsupp.mem_support_iff.mp hI
  change (Finsupp.applyAddHom I)
    (∑ j : Fin C.1,Finsupp.single (intervalIndexOfChain α β C.2 j) 1)=0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro j hj
  apply Finsupp.single_eq_of_ne
  intro he
  exact h ⟨j,he.symm⟩

theorem goodChainExponent_normal (C : OddStandardIndex k t hs) :
    NormalMonomial α β (goodChainExponent k t hs C) := by
  intro I hI J hJ
  obtain ⟨i,rfl⟩ := goodChainExponent_support k t hs C I hI
  obtain ⟨j,rfl⟩ := goodChainExponent_support k t hs C J hJ
  rcases le_total i j with hij | hji
  · exact Or.inl (C.2.property.2.2 hij)
  · exact Or.inr (C.2.property.2.2 hji)

theorem goodChainExponent_injective :
    Function.Injective (goodChainExponent k t hs) := by
  intro C D h
  apply (oddPluckerStandardBasis (K := ℚ) k t hs).injective
  rw [←oddGoodMap_standardPolynomial k t hs C,
    ←oddGoodMap_standardPolynomial k t hs D,
    standardPolynomial_eq_monomial,standardPolynomial_eq_monomial,h]

theorem oddGoodRepresentative_support
    (q : MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸
      isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k))
    (a : IntervalIndex α β →₀ ℕ)
    (ha : a∈(oddGoodRepresentative k t hs q).support) :
    ∃ C : OddStandardIndex k t hs,((𝔅).repr q) C≠0 ∧ a=goodChainExponent k t hs C := by
  classical
  have h := mem_support_iff.mp ha
  rw [oddGoodRepresentative] at h
  simp only [Finsupp.sum,coeff_sum] at h
  obtain ⟨C,hC,hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨C,Finsupp.mem_support_iff.mp hC,?_⟩
  by_contra hne
  apply hterm
  simp only [coeff_smul,standardPolynomial_eq_monomial,coeff_monomial,
    if_neg (Ne.symm hne),smul_zero]

theorem oddGoodNormalForm_normal (p : P) :
    ∀ a∈(oddGoodNormalForm k t hs p).support,NormalMonomial α β a := by
  intro a ha
  obtain ⟨C,hC,rfl⟩ := oddGoodRepresentative_support k t hs _ a ha
  exact goodChainExponent_normal k t hs C

theorem oddGoodRepresentative_coeff
    (q : MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸
      isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k))
    (C : OddStandardIndex k t hs) :
    (oddGoodRepresentative k t hs q).coeff (goodChainExponent k t hs C)=((𝔅).repr q) C := by
  classical
  simp only [oddGoodRepresentative,Finsupp.sum,coeff_sum,coeff_smul,
    standardPolynomial_eq_monomial,coeff_monomial,smul_eq_mul]
  rw [Finset.sum_eq_single C]
  · simp
  · intro D hD hDC
    have hne : goodChainExponent k t hs D≠goodChainExponent k t hs C :=
      fun h ↦ hDC (goodChainExponent_injective k t hs h)
    simp [hne]
  · intro hC
    simp [Finsupp.notMem_support_iff.mp hC]

theorem oddGoodNormalForm_eq_of_normal (p r : P)
    (hr : ∀ a∈r.support,NormalMonomial α β a)
    (he : oddGoodMap k t hs p=oddGoodMap k t hs r) :
    oddGoodNormalForm k t hs p=r := by
  classical
  apply sub_eq_zero.mp
  apply oddGood_normal_polynomial_eq_zero k t hs
    (oddGoodNormalForm k t hs p-r)
  · intro a ha
    rcases Finset.mem_union.mp (support_sub _ _ _ ha) with ha | ha
    · exact oddGoodNormalForm_normal k t hs p a ha
    · exact hr a ha
  · rw [map_sub,oddGoodMap_normalForm,he,sub_self]

theorem oddGoodNormalForm_isRemainder (m : MonomialOrder (IntervalIndex α β)) (p : P) :
    (oddGoodOrder k t hs m).IsRemainder p (oddQuadraticSet k t hs)
      (oddGoodNormalForm k t hs p) := by
  obtain ⟨r,hr⟩ := (oddGoodOrder k t hs m).exists_isRemainder (B := oddQuadraticSet (K := K) k t hs)
    (fun b hb hb0 ↦ by
      obtain ⟨I,J,h,rfl⟩ := hb
      rw [oddQuadraticRelation_leadingCoeff k t hs m I J h]
      exact isUnit_one) p
  have hpr : p-r∈oddGoodIdeal (K := K) k t hs :=
    Ideal.span_le.mpr (odd_good_quadratic_isGroebnerBasis (K := K) k t hs m).subset
      hr.sub_mem_span
  have he : oddGoodMap k t hs p=oddGoodMap k t hs r := by
    change oddGoodMap k t hs (p-r)=0 at hpr
    rw [map_sub,sub_eq_zero] at hpr
    exact hpr
  rw [oddGoodNormalForm_eq_of_normal k t hs p r
    (odd_remainder_normal_support k t hs m p r hr) he]
  exact hr

/-- The degree bound follows from the actual ideal and the leading-term
criterion; no abstract multiplicative filtration hypothesis is assumed. -/
theorem oddGoodNormalForm_degree_le (m : MonomialOrder (IntervalIndex α β)) (p : P) :
    (oddGoodOrder k t hs m).degree (oddGoodNormalForm k t hs p)
      ≼[oddGoodOrder k t hs m] (oddGoodOrder k t hs m).degree p := by
  let M := oddGoodOrder k t hs m
  let r := oddGoodNormalForm (K := K) k t hs p
  have hr := oddGoodNormalForm_isRemainder k t hs m p
  by_contra h
  have hlt : M.degree p ≺[M] M.degree r := lt_of_not_ge h
  have hr0 : r≠0 := by
    intro hz
    rw [hz,M.degree_zero,map_zero,←M.bot_eq_zero] at hlt
    exact not_lt_of_ge bot_le hlt
  have hrp0 : r-p≠0 := by
    intro hz
    have he := sub_eq_zero.mp hz
    rw [he] at hlt
    exact lt_irrefl _ hlt
  have hrp : r-p∈oddGoodIdeal (K := K) k t hs := by
    change oddGoodMap k t hs (r-p)=0
    rw [map_sub,oddGoodMap_normalForm,sub_self]
  obtain ⟨q,hq,hq0,hqd⟩ :=
    (odd_good_quadratic_isGroebnerBasis (K := K) k t hs m).exists_degree_le_degree hrp hrp0
  rw [M.degree_sub_of_lt hlt] at hqd
  exact hr.not_degree_le (M.degree_mem_support hr0) hq hq0 hqd

theorem oddGoodNormalForm_monomial_term_le (m : MonomialOrder (IntervalIndex α β))
    (a b : IntervalIndex α β →₀ ℕ)
    (hb : b∈(oddGoodNormalForm (K := K) k t hs (monomial a 1)).support) :
    b ≼[oddGoodOrder k t hs m] a := by
  classical
  have h := (oddGoodOrder k t hs m).le_degree hb
  have h' := oddGoodNormalForm_degree_le k t hs m (monomial a (1 : K))
  rw [MonomialOrder.degree_monomial,if_neg (one_ne_zero : (1 : K) ≠ 0)] at h'
  exact h.trans h'

theorem oddGoodNormalForm_nonnormal_term_lt (m : MonomialOrder (IntervalIndex α β))
    (a b : IntervalIndex α β →₀ ℕ) (ha : ¬NormalMonomial α β a)
    (hb : b∈(oddGoodNormalForm (K := K) k t hs (monomial a 1)).support) :
    b ≺[oddGoodOrder k t hs m] a := by
  apply lt_of_le_of_ne (oddGoodNormalForm_monomial_term_le k t hs m a b hb)
  intro he
  apply ha
  have hab : b=a := (oddGoodOrder k t hs m).toSyn.injective he
  exact hab ▸ oddGoodNormalForm_normal k t hs (monomial a (1 : K)) b hb

theorem oddGoodNormalForm_normal_monomial (a : IntervalIndex α β →₀ ℕ)
    (ha : NormalMonomial α β a) :
    oddGoodNormalForm (K := K) k t hs (monomial a 1)=monomial a 1 := by
  apply oddGoodNormalForm_eq_of_normal k t hs _ _ ?_ rfl
  intro b hb
  have hab : b=a := Finset.mem_singleton.mp (support_monomial_subset hb)
  exact hab.symm ▸ ha

end PaperVerification.AlternatingForms

