module

public import PaperVerification.AlternatingFormsHibiMonomials
public import PaperVerification.WeightedMonomialOrder
public import TauCeti.RingTheory.MvPolynomial.Groebner.Basic

/-!
# The actual quadratic Gröbner basis of the Hibi ideal

The order refines the positive rank-square weight. Its division remainder
has only chain-support monomials. Their actual diagonal images are linearly
independent, so a remainder of an element of the Hibi ideal is zero. This
proves the full Gröbner property, not only termination of the displayed
quadratic substitutions.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.Hibi

open MvPolynomial
open scoped BigOperators MonomialOrder

variable {K : Type*} [Field K] {s n : ℕ} (α β : Fin s → Fin n)

def quadraticSet : Set (MvPolynomial (IntervalIndex α β) K) :=
  {p | ∃ I J,incomparable α β I J ∧ p=relation α β I J}

def pairExponent (I J : IntervalIndex α β) : IntervalIndex α β →₀ ℕ :=
  Finsupp.single I 1+Finsupp.single J 1

theorem pair_monomial (I J : IntervalIndex α β) :
    (X I*X J : MvPolynomial (IntervalIndex α β) K)=monomial (pairExponent α β I J) 1 := by
  simp only [X,monomial_mul,one_mul,pairExponent]

def sortingOrder (m : MonomialOrder (IntervalIndex α β)) :
    MonomialOrder (IntervalIndex α β) :=
  WeightedMonomialOrder.weightedRefinement m (sortingWeight α β)

theorem pair_sorting_lt (m : MonomialOrder (IntervalIndex α β))
    (I J : IntervalIndex α β) (h : incomparable α β I J) :
    pairExponent α β (meet α β I J) (join α β I J) ≺[sortingOrder α β m]
      pairExponent α β I J := by
  apply WeightedMonomialOrder.lt_of_weight_lt
  simpa only [pairExponent,map_add,Finsupp.weight_single,one_smul] using
    sortingWeight_decreases α β I J h

theorem relation_degree (m : MonomialOrder (IntervalIndex α β))
    (I J : IntervalIndex α β) (h : incomparable α β I J) :
    (sortingOrder α β m).degree (relation (K := K) α β I J)=pairExponent α β I J := by
  classical
  have hlt : (sortingOrder α β m).degree
      (monomial (pairExponent α β (meet α β I J) (join α β I J)) (1 : K))
        ≺[sortingOrder α β m]
      (sortingOrder α β m).degree (monomial (pairExponent α β I J) (1 : K)) := by
    simpa only [MonomialOrder.degree_monomial,ite_eq_right one_ne_zero] using
      pair_sorting_lt α β m I J h
  rw [relation,pair_monomial,pair_monomial,
    (sortingOrder α β m).degree_sub_of_lt hlt,MonomialOrder.degree_monomial,
    ite_eq_right one_ne_zero]

theorem relation_leadingCoeff (m : MonomialOrder (IntervalIndex α β))
    (I J : IntervalIndex α β) (h : incomparable α β I J) :
    (sortingOrder α β m).leadingCoeff (relation (K := K) α β I J)=1 := by
  classical
  have hlt : (sortingOrder α β m).degree
      (monomial (pairExponent α β (meet α β I J) (join α β I J)) (1 : K))
        ≺[sortingOrder α β m]
      (sortingOrder α β m).degree (monomial (pairExponent α β I J) (1 : K)) := by
    simpa only [MonomialOrder.degree_monomial,ite_eq_right one_ne_zero] using
      pair_sorting_lt α β m I J h
  rw [relation,pair_monomial,pair_monomial,
    (sortingOrder α β m).leadingCoeff_sub_of_lt hlt,MonomialOrder.leadingCoeff_monomial]

theorem relation_ne_zero (m : MonomialOrder (IntervalIndex α β))
    (I J : IntervalIndex α β) (h : incomparable α β I J) : relation (K := K) α β I J≠0 := by
  intro hz
  have he := relation_leadingCoeff (K := K) α β m I J h
  rw [hz,MonomialOrder.leadingCoeff_zero] at he
  exact zero_ne_one he

theorem pairExponent_le_of_support (a : IntervalIndex α β →₀ ℕ)
    (I J : IntervalIndex α β) (hI : I∈a.support) (hJ : J∈a.support) (hne : I≠J) :
    pairExponent α β I J≤a := by
  classical
  intro T
  by_cases hTI : T=I
  · subst T
    simpa only [pairExponent,Finsupp.add_apply,Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne hne,add_zero] using
        Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hI)
  · by_cases hTJ : T=J
    · subst T
      simpa only [pairExponent,Finsupp.add_apply,Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne hne.symm,zero_add] using
          Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hJ)
    · simp only [pairExponent,Finsupp.add_apply,Finsupp.single_eq_of_ne hTI,
        Finsupp.single_eq_of_ne hTJ,add_zero,Nat.zero_le]

theorem remainder_normal_support (m : MonomialOrder (IntervalIndex α β))
    (f r : MvPolynomial (IntervalIndex α β) K)
    (hr : (sortingOrder α β m).IsRemainder f (quadraticSet α β) r) :
    ∀ a∈r.support,NormalMonomial α β a := by
  intro a ha I hI J hJ
  by_contra h
  have hinc : incomparable α β I J := not_or.mp h
  have hne : I≠J := fun he => hinc.1 (he ▸ le_rfl)
  have hnot := hr.not_degree_le ha (show relation (K := K) α β I J∈quadraticSet α β from
    ⟨I,J,hinc,rfl⟩) (relation_ne_zero α β m I J hinc)
  rw [relation_degree α β m I J hinc] at hnot
  exact hnot (pairExponent_le_of_support α β a I J hI hJ hne)

/-- The displayed literal binomials are a genuine quadratic Gröbner basis
of their full ideal for the explicitly constructed sorting order. -/
theorem quadratic_isGroebnerBasis (m : MonomialOrder (IntervalIndex α β)) (hs : 0<s) :
    (sortingOrder α β m).IsGroebnerBasis (quadraticSet (K := K) α β) (relationIdeal α β) := by
  apply MonomialOrder.isGroebnerBasis_iff_isRemainder_zero.mpr
  refine ⟨fun p hp => Ideal.subset_span hp,?_⟩
  intro p hp
  obtain ⟨r,hr⟩ := (sortingOrder α β m).exists_isRemainder (B := quadraticSet (K := K) α β)
    (fun b hb hb0 => by
      obtain ⟨I,J,h,rfl⟩ := hb
      rw [relation_leadingCoeff α β m I J h]
      exact isUnit_one) p
  have hrI : r∈relationIdeal (K := K) α β := by
    have hsub : p-r∈relationIdeal α β := hr.sub_mem_span
    simpa only [sub_sub_cancel] using (relationIdeal (K := K) α β).sub_mem hp hsub
  have hr0 : r=0 := normal_polynomial_eq_zero α β hs r
    (remainder_normal_support α β m p r hr)
    (by rw [relationIdeal_eq_kernel α β hs] at hrI; exact hrI)
  simpa only [hr0] using hr

theorem quadratic_leadingIdeal (m : MonomialOrder (IntervalIndex α β)) (hs : 0<s) :
    Ideal.span ((sortingOrder α β m).leadingTerm ''
      (relationIdeal (K := K) α β : Set (MvPolynomial (IntervalIndex α β) K)))=
        incomparableIdeal α β := by
  rw [(quadratic_isGroebnerBasis (K := K) α β m hs).span_leadingTerm_image]
  congr 1
  ext p
  constructor
  · rintro ⟨q,⟨I,J,h,rfl⟩,rfl⟩
    refine ⟨I,J,h,?_⟩
    rw [MonomialOrder.leadingTerm,relation_degree α β m I J h,
      relation_leadingCoeff α β m I J h,pair_monomial]
  · rintro ⟨I,J,h,rfl⟩
    refine ⟨relation α β I J,⟨I,J,h,rfl⟩,?_⟩
    rw [MonomialOrder.leadingTerm,relation_degree α β m I J h,
      relation_leadingCoeff α β m I J h,pair_monomial]

end PaperVerification.AlternatingForms.Hibi
