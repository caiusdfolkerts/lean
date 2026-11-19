module

public import PaperVerification.AlternatingFormsHibiWeights
public import PaperVerification.WeightedSagbiSubstitution
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Multiset.Basic

/-!
# The actual monomials avoiding incomparable pairs

A monomial avoids the incomparable quadratic divisors exactly when its
support is a chain. Meet/join insertion of such a multiset only permutes
its entries, so its product is literally a standard chain product before
taking any quotient. Distinct such monomials have distinct diagonal images.
These statements identify the genuine division remainders needed for the
Hibi Gröbner proof.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.Hibi

open MvPolynomial
open scoped BigOperators

variable {K : Type*} [Field K] {s n : ℕ} (α β : Fin s → Fin n)

def ComparableSet (A : Set (IntervalIndex α β)) : Prop :=
  ∀ I∈A,∀ J∈A,I≤J ∨ J≤I

theorem meet_mem_comparable {A : Set (IntervalIndex α β)} (hA : ComparableSet α β A)
    (I J : IntervalIndex α β) (hI : I∈A) (hJ : J∈A) : meet α β I J∈A := by
  rcases hA I hI J hJ with h | h
  · rwa [meet_eq_left α β I J h]
  · rwa [meet_eq_right α β I J h]

theorem join_mem_comparable {A : Set (IntervalIndex α β)} (hA : ComparableSet α β A)
    (I J : IntervalIndex α β) (hI : I∈A) (hJ : J∈A) : join α β I J∈A := by
  rcases hA I hI J hJ with h | h
  · rwa [join_eq_right α β I J h]
  · rwa [join_eq_left α β I J h]

theorem insert_mem_comparable {A : Set (IntervalIndex α β)} (hA : ComparableSet α β A)
    (I : IntervalIndex α β) (L : List (IntervalIndex α β))
    (hI : I∈A) (hL : ∀ J∈L,J∈A) : ∀ J∈insert α β I L,J∈A := by
  induction L generalizing I with
  | nil => simpa only [insert,List.mem_singleton,forall_eq] using hI
  | cons J L ih =>
      intro Z hZ
      have hJ := hL J (List.mem_cons_self)
      rcases List.mem_cons.mp hZ with rfl | hZ
      · exact meet_mem_comparable α β hA I J hI hJ
      · exact ih (join α β I J) (join_mem_comparable α β hA I J hI hJ)
          (fun T hT => hL T (List.mem_cons_of_mem _ hT)) Z hZ

theorem sort_mem_comparable {A : Set (IntervalIndex α β)} (hA : ComparableSet α β A)
    (L : List (IntervalIndex α β)) (hL : ∀ J∈L,J∈A) : ∀ J∈sort α β L,J∈A := by
  induction L with
  | nil => simp only [sort,List.foldr_nil,List.not_mem_nil,false_implies,implies_true]
  | cons I L ih =>
      exact insert_mem_comparable α β hA I (sort α β L)
        (hL I (List.mem_cons_self))
        (ih (fun J hJ => hL J (List.mem_cons_of_mem _ hJ)))

theorem pair_eq_of_comparable (I J : IntervalIndex α β) (h : I≤J ∨ J≤I) :
    X (meet α β I J)*X (join α β I J)=(X I*X J : MvPolynomial (IntervalIndex α β) K) := by
  rcases h with h | h
  · rw [meet_eq_left α β I J h,join_eq_right α β I J h]
  · rw [meet_eq_right α β I J h,join_eq_left α β I J h,mul_comm]

theorem word_insert_eq_of_comparable {A : Set (IntervalIndex α β)}
    (hA : ComparableSet α β A) (I : IntervalIndex α β) (L : List (IntervalIndex α β))
    (hI : I∈A) (hL : ∀ J∈L,J∈A) :
    word (K := K) α β (insert α β I L)=X I*word α β L := by
  induction L generalizing I with
  | nil => simp only [insert,word_cons,word_nil,mul_one]
  | cons J L ih =>
      have hJ := hL J (List.mem_cons_self)
      rw [insert,word_cons,ih (join α β I J)
        (join_mem_comparable α β hA I J hI hJ)
        (fun T hT => hL T (List.mem_cons_of_mem _ hT)),word_cons,←mul_assoc,
        pair_eq_of_comparable α β I J (hA I hI J hJ),mul_assoc]

theorem word_sort_eq_of_comparable {A : Set (IntervalIndex α β)}
    (hA : ComparableSet α β A) (L : List (IntervalIndex α β)) (hL : ∀ J∈L,J∈A) :
    word (K := K) α β (sort α β L)=word α β L := by
  induction L with
  | nil => rfl
  | cons I L ih =>
      change word α β (insert α β I (sort α β L))=word α β (I::L)
      rw [word_insert_eq_of_comparable α β hA I _ (hL I (List.mem_cons_self))
        (sort_mem_comparable α β hA L (fun J hJ => hL J (List.mem_cons_of_mem _ hJ))),
        ih (fun J hJ => hL J (List.mem_cons_of_mem _ hJ)),word_cons]

def multisetWord (M : Multiset (IntervalIndex α β)) : MvPolynomial (IntervalIndex α β) K :=
  (M.map X).prod

theorem multisetWord_toMultiset (m : IntervalIndex α β →₀ ℕ) :
    multisetWord (K := K) α β m.toMultiset=monomial m 1 := by
  classical
  induction m using Finsupp.induction_linear with
  | zero => simp only [Finsupp.toMultiset_zero,multisetWord,Multiset.map_zero,
      Multiset.prod_zero,monomial_zero',map_one]
  | add m m' hm hm' =>
      simp only [Finsupp.toMultiset_add,multisetWord,Multiset.map_add,Multiset.prod_add] at *
      rw [hm,hm',monomial_mul,one_mul]
  | single I r =>
      have hmap : (r • ({I} : Multiset (IntervalIndex α β))).map
          (X : IntervalIndex α β → MvPolynomial (IntervalIndex α β) K)=r • {X I} := by
        simpa only [Multiset.coe_mapAddMonoidHom,Multiset.map_singleton] using
          (Multiset.mapAddMonoidHom (X : IntervalIndex α β →
            MvPolynomial (IntervalIndex α β) K)).map_nsmul r ({I} : Multiset (IntervalIndex α β))
      simp only [Finsupp.toMultiset_single,multisetWord,hmap,
        Multiset.prod_nsmul,Multiset.prod_singleton,X_pow_eq_monomial]

theorem word_toMultiset (m : IntervalIndex α β →₀ ℕ) :
    word (K := K) α β m.toMultiset.toList=monomial m 1 := by
  have h : word (K := K) α β m.toMultiset.toList=multisetWord α β m.toMultiset := by
    unfold word multisetWord
    rw [←Multiset.prod_coe,←Multiset.map_coe,Multiset.coe_toList]
  exact h.trans (multisetWord_toMultiset α β m)

def NormalMonomial (m : IntervalIndex α β →₀ ℕ) : Prop :=
  ComparableSet α β (m.support : Set (IntervalIndex α β))

def normalChain (m : IntervalIndex α β →₀ ℕ) : Σ r,BandChain α β r :=
  ⟨(sort α β m.toMultiset.toList).length,
    chainOfList α β _ (sort_sorted α β m.toMultiset.toList)⟩

theorem normalChain_polynomial (m : IntervalIndex α β →₀ ℕ) (hm : NormalMonomial α β m) :
    standardPolynomial (K := K) α β (normalChain α β m).2=monomial m 1 := by
  rw [normalChain,standardPolynomial_chainOfList,
    word_sort_eq_of_comparable α β hm,word_toMultiset]
  intro I hI
  exact (Finsupp.mem_toMultiset m I).mp (Multiset.mem_toList.mp hI)

def hibiExponentMap : (IntervalIndex α β →₀ ℕ) →ₗ[ℕ] ((Fin s × Fin n) →₀ ℕ) :=
  WeightedSagbi.exponentMap (fun I : IntervalIndex α β => minorTermExponent I.val.val 1)

theorem diagonalMap_monomial (m : IntervalIndex α β →₀ ℕ) (c : K) :
    diagonalMap α β (monomial m c)=monomial (hibiExponentMap α β m) c :=
  WeightedSagbi.monomialSubstitution_monomial _ m c

include K in
theorem normalChain_diagonal (m : IntervalIndex α β →₀ ℕ) (hm : NormalMonomial α β m) :
    chainDiagonalExponent (normalChain α β m).2.val=hibiExponentMap α β m := by
  apply MvPolynomial.monomial_left_injective (one_ne_zero : (1 : K)≠0)
  change (monomial (chainDiagonalExponent (normalChain α β m).2.val) 1 :
      MvPolynomial (Fin s × Fin n) K)=monomial (hibiExponentMap α β m) 1
  calc
    _ = diagonalMap α β (standardPolynomial α β (normalChain α β m).2) :=
      (diagonalMap_standardPolynomial α β (normalChain α β m).2).symm
    _ = diagonalMap α β (monomial m 1) :=
      congrArg (diagonalMap α β) (normalChain_polynomial α β m hm)
    _ = _ := diagonalMap_monomial α β m 1

include K in
theorem hibiExponentMap_normal_injective (hs : 0<s) :
    Function.Injective (fun m : {m : IntervalIndex α β →₀ ℕ // NormalMonomial α β m} =>
      hibiExponentMap α β m.val) := by
  intro m m' h
  have hc : normalChain α β m.val=normalChain α β m'.val := by
    apply allChainDiagonalExponent_injective α β hs
    change chainDiagonalExponent (normalChain α β m.val).2.val=
      chainDiagonalExponent (normalChain α β m'.val).2.val
    exact (normalChain_diagonal (K := K) α β m.val m.property).trans
      (h.trans (normalChain_diagonal (K := K) α β m'.val m'.property).symm)
  apply Subtype.ext
  apply MvPolynomial.monomial_left_injective (one_ne_zero : (1 : K)≠0)
  change (monomial m.val 1 : MvPolynomial (IntervalIndex α β) K)=monomial m'.val 1
  have hp := congrArg (fun C : Σ r,BandChain α β r =>
    standardPolynomial (K := K) α β C.2) hc
  exact (normalChain_polynomial α β m.val m.property).symm.trans
    (hp.trans (normalChain_polynomial α β m'.val m'.property))

/-- A polynomial supported on chain monomials has no diagonal-image
cancellation. This is the independence needed for actual remainders. -/
theorem normal_polynomial_eq_zero (hs : 0<s) (p : MvPolynomial (IntervalIndex α β) K)
    (hp : ∀ m∈p.support,NormalMonomial α β m) (hz : diagonalMap α β p=0) : p=0 := by
  classical
  have hli : LinearIndependent K (fun m : p.support =>
      diagonalMap α β (monomial m.val 1 : MvPolynomial (IntervalIndex α β) K)) := by
    simp only [diagonalMap_monomial]
    apply (MvPolynomial.basisMonomials (Fin s × Fin n) K).linearIndependent.comp
    intro m m' h
    have he := hibiExponentMap_normal_injective (K := K) α β hs
      (show hibiExponentMap α β (⟨m.val,hp m.val m.property⟩ :
        {m : IntervalIndex α β →₀ ℕ // NormalMonomial α β m})=
        hibiExponentMap α β (⟨m'.val,hp m'.val m'.property⟩ :
        {m : IntervalIndex α β →₀ ℕ // NormalMonomial α β m}) from h)
    apply Subtype.ext
    exact congrArg (fun a : {m : IntervalIndex α β →₀ ℕ // NormalMonomial α β m} => a.val) he
  have hsum : (∑ m : p.support,p.coeff m.val •
      diagonalMap α β (monomial m.val 1 : MvPolynomial (IntervalIndex α β) K))=0 := by
    rw [Finset.sum_coe_sort (s := p.support)
      (f := fun m : IntervalIndex α β →₀ ℕ => p.coeff m •
        diagonalMap α β (monomial m 1 : MvPolynomial (IntervalIndex α β) K))]
    rw [←WeightedSagbi.map_eq_coefficient_sum]
    exact hz
  have hc := Fintype.linearIndependent_iff.mp hli (fun m => p.coeff m.val) hsum
  ext m
  by_cases hm : m∈p.support
  · simpa only [MvPolynomial.coeff_zero,Finsupp.zero_apply] using hc ⟨m,hm⟩
  · simp only [notMem_support_iff.mp hm,MvPolynomial.coeff_zero,Finsupp.zero_apply]

end PaperVerification.AlternatingForms.Hibi
