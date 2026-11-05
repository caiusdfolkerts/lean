module

public import PaperVerification.AlternatingFormsHibiInterval

/-!
# The literal Hibi presentation and its complete chain basis

The defining binomials replace incomparable tuples by their coordinatewise
meet and join. Finite lattice insertion sorts every actual product modulo
these relations. Diagonal exponent vectors distinguish all chains, proving
both independence and equality with the actual diagonal-monomial kernel.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.Hibi

open MvPolynomial
open scoped BigOperators

variable {K : Type*} [Field K] {s n : ℕ} (α β : Fin s → Fin n)

def incomparable (I J : IntervalIndex α β) : Prop := ¬I≤J ∧ ¬J≤I

def relation (I J : IntervalIndex α β) : MvPolynomial (IntervalIndex α β) K :=
  X I*X J-X (meet α β I J)*X (join α β I J)

def relationIdeal : Ideal (MvPolynomial (IntervalIndex α β) K) :=
  Ideal.span {p | ∃ I J,incomparable α β I J ∧ p=relation α β I J}

theorem relation_mem (I J : IntervalIndex α β) : relation (K := K) α β I J∈relationIdeal α β := by
  classical
  by_cases hIJ : I≤J
  · simp only [relation,meet_eq_left α β I J hIJ,join_eq_right α β I J hIJ,sub_self,
      Ideal.zero_mem]
  · by_cases hJI : J≤I
    · simp only [relation,meet_eq_right α β I J hJI,join_eq_left α β I J hJI,
        mul_comm (X I) (X J),sub_self,Ideal.zero_mem]
    · exact Ideal.subset_span ⟨I,J,⟨hIJ,hJI⟩,rfl⟩

def diagonalMonomial (I : IntervalIndex α β) : MvPolynomial (Fin s × Fin n) K :=
  monomial (minorTermExponent I.val.val 1) 1

def diagonalMap : MvPolynomial (IntervalIndex α β) K →ₐ[K]
    MvPolynomial (Fin s × Fin n) K := aeval (diagonalMonomial α β)

theorem pair_exponents (I J : IntervalIndex α β) :
    minorTermExponent (meet α β I J).val.val 1+
        minorTermExponent (join α β I J).val.val 1=
      minorTermExponent I.val.val 1+minorTermExponent J.val.val 1 := by
  simp only [minorTermExponent,Equiv.Perm.one_apply]
  rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : I.val.val i≤J.val.val i
  · simp only [meet,join,min_eq_left h,max_eq_right h]
  · have h' : J.val.val i≤I.val.val i := (le_of_not_ge h)
    simp only [meet,join,min_eq_right h',max_eq_left h',add_comm]

theorem diagonalMap_relation (I J : IntervalIndex α β) :
    diagonalMap (K := K) α β (relation α β I J)=0 := by
  simp only [relation,diagonalMap,map_sub,map_mul,aeval_X,diagonalMonomial,
    monomial_mul,one_mul,pair_exponents,sub_self]

theorem relationIdeal_le_kernel :
    relationIdeal (K := K) α β≤RingHom.ker (diagonalMap α β).toRingHom := by
  apply Ideal.span_le.mpr
  rintro _ ⟨I,J,h,rfl⟩
  exact diagonalMap_relation α β I J

def diagonalQuotientMap :
    (MvPolynomial (IntervalIndex α β) K⧸relationIdeal α β) →ₐ[K]
      MvPolynomial (Fin s × Fin n) K :=
  Ideal.Quotient.liftₐ _ (diagonalMap α β) (fun p hp => relationIdeal_le_kernel α β hp)

def word (L : List (IntervalIndex α β)) : MvPolynomial (IntervalIndex α β) K :=
  (L.map X).prod

@[simp] theorem word_nil : word (K := K) α β []=1 := rfl

@[simp] theorem word_cons (I : IntervalIndex α β) (L : List (IntervalIndex α β)) :
    word (K := K) α β (I::L)=X I*word α β L := rfl

theorem quotient_pair (I J : IntervalIndex α β) :
    Ideal.Quotient.mk (relationIdeal (K := K) α β) (X I*X J)=
      Ideal.Quotient.mk _ (X (meet α β I J)*X (join α β I J)) :=
  (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (relation_mem α β I J)

theorem quotient_word_insert (I : IntervalIndex α β) (L : List (IntervalIndex α β)) :
    Ideal.Quotient.mk (relationIdeal (K := K) α β) (word α β (insert α β I L))=
      Ideal.Quotient.mk _ (X I*word α β L) := by
  induction L generalizing I with
  | nil => simp only [insert,word_cons,word_nil,mul_one]
  | cons J L ih =>
      simp only [insert,word_cons,map_mul]
      rw [ih,map_mul,←mul_assoc,←map_mul,←quotient_pair,map_mul,mul_assoc]

theorem quotient_word_sort (L : List (IntervalIndex α β)) :
    Ideal.Quotient.mk (relationIdeal (K := K) α β) (word α β (sort α β L))=
      Ideal.Quotient.mk _ (word α β L) := by
  induction L with
  | nil => rfl
  | cons I L ih =>
      change Ideal.Quotient.mk _ (word α β (insert α β I (sort α β L)))=_
      rw [quotient_word_insert,word_cons,map_mul,map_mul,ih]

def standardPolynomial {r : ℕ} (C : BandChain α β r) :
    MvPolynomial (IntervalIndex α β) K := ∏ j,X (intervalIndexOfChain α β C j)

def standardClass (C : Σ r,BandChain α β r) :
    MvPolynomial (IntervalIndex α β) K⧸relationIdeal α β :=
  Ideal.Quotient.mk _ (standardPolynomial α β C.2)

theorem standardPolynomial_word {r : ℕ} (C : BandChain α β r) :
    standardPolynomial (K := K) α β C=
      word α β (List.ofFn (intervalIndexOfChain α β C)) := by
  simp only [word,List.map_ofFn,List.prod_ofFn,standardPolynomial,Function.comp_def]

theorem standardPolynomial_chainOfList (L : List (IntervalIndex α β))
    (hL : L.Pairwise (·≤·)) :
    standardPolynomial (K := K) α β (chainOfList α β L hL)=word α β L := by
  rw [standardPolynomial_word]
  congr 1
  have he : intervalIndexOfChain α β (chainOfList α β L hL)=L.get := rfl
  rw [he,List.ofFn_get]

def standardSpan : Submodule K (MvPolynomial (IntervalIndex α β) K⧸relationIdeal α β) :=
  Submodule.span K (Set.range (standardClass α β))

theorem word_class_mem_standardSpan (L : List (IntervalIndex α β)) :
    Ideal.Quotient.mk (relationIdeal (K := K) α β) (word α β L)∈standardSpan α β := by
  rw [←quotient_word_sort]
  apply Submodule.subset_span
  refine ⟨⟨(sort α β L).length,chainOfList α β _ (sort_sorted α β L)⟩,?_⟩
  rw [standardClass,standardPolynomial_chainOfList]

theorem standardSpan_mul_variable
    {z : MvPolynomial (IntervalIndex α β) K⧸relationIdeal α β}
    (hz : z∈standardSpan α β) (I : IntervalIndex α β) :
    z*Ideal.Quotient.mk _ (X I)∈standardSpan α β := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨C,rfl⟩ := hz
      have h := word_class_mem_standardSpan (K := K) α β
        (I::List.ofFn (intervalIndexOfChain α β C.2))
      simpa only [word_cons,map_mul,←standardPolynomial_word,standardClass,mul_comm] using h
  | zero => simpa only [zero_mul] using (standardSpan (K := K) α β).zero_mem
  | add x y hx hy ihx ihy =>
      simpa only [add_mul] using (standardSpan α β).add_mem ihx ihy
  | smul a x hx ih =>
      simpa only [smul_mul_assoc] using (standardSpan α β).smul_mem a ih

theorem standardSpan_eq_top : standardSpan (K := K) α β=⊤ := by
  apply top_unique
  intro z hz
  clear hz
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective z
  induction p using MvPolynomial.induction_on with
  | C a =>
      have h1 := word_class_mem_standardSpan (K := K) α β []
      simp only [word_nil,map_one] at h1
      have ha := (standardSpan α β).smul_mem a h1
      change (algebraMap K (MvPolynomial (IntervalIndex α β) K ⧸ relationIdeal α β)) a ∈
        standardSpan α β
      rw [Algebra.algebraMap_eq_smul_one]
      exact ha
  | add p q hp hq => simpa only [map_add] using (standardSpan α β).add_mem hp hq
  | mul_X p I hp => simpa only [map_mul] using standardSpan_mul_variable α β hp I

theorem diagonalMap_standardPolynomial {r : ℕ} (C : BandChain α β r) :
    diagonalMap (K := K) α β (standardPolynomial α β C)=
      monomial (chainDiagonalExponent C.val) 1 := by
  unfold standardPolynomial
  rw [map_prod]
  trans ∏ i : Fin r,diagonalMonomial (K := K) α β (intervalIndexOfChain α β C i)
  · apply Finset.prod_congr rfl
    intro i hi
    exact MvPolynomial.aeval_X (diagonalMonomial (K := K) α β)
      (intervalIndexOfChain α β C i)
  · simp only [diagonalMonomial,intervalIndexOfChain,
      prod_monomial_eq_monomial_sum,Finset.prod_const_one,
      chainDiagonalExponent,chainTermExponent]

theorem diagonalStandardProducts_linearIndependent (hs : 0<s) :
    LinearIndependent K (fun C : Σ r,BandChain α β r =>
      (monomial (chainDiagonalExponent C.2.val) 1 : MvPolynomial (Fin s × Fin n) K)) := by
  simpa only [MvPolynomial.coe_basisMonomials,Function.comp_def] using
    (MvPolynomial.basisMonomials (Fin s × Fin n) K).linearIndependent.comp
      (fun C : Σ r,BandChain α β r => chainDiagonalExponent C.2.val)
      (allChainDiagonalExponent_injective α β hs)

theorem diagonalQuotientMap_injective (hs : 0<s) :
    Function.Injective (diagonalQuotientMap (K := K) α β) := by
  change Function.Injective (diagonalQuotientMap (K := K) α β).toLinearMap
  apply LinearMap.injective_of_linearIndependent
    (f := (diagonalQuotientMap (K := K) α β).toLinearMap)
    (show Submodule.span K (Set.range (standardClass (K := K) α β))=⊤ from
      standardSpan_eq_top α β)
  have he : (diagonalQuotientMap (K := K) α β).toLinearMap ∘ standardClass α β=
      fun C : Σ r,BandChain α β r => monomial (chainDiagonalExponent C.2.val) 1 := by
    funext C
    exact diagonalMap_standardPolynomial α β C.2
  rw [he]
  exact diagonalStandardProducts_linearIndependent α β hs

theorem relationIdeal_eq_kernel (hs : 0<s) :
    relationIdeal (K := K) α β=RingHom.ker (diagonalMap α β).toRingHom := by
  apply le_antisymm (relationIdeal_le_kernel α β)
  intro p hp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply diagonalQuotientMap_injective α β hs
  change diagonalMap α β p=diagonalQuotientMap α β 0
  rw [map_zero]
  exact hp

theorem relationIdeal_isPrime (hs : 0<s) : (relationIdeal (K := K) α β).IsPrime := by
  rw [relationIdeal_eq_kernel α β hs]
  exact RingHom.ker_isPrime _

theorem standardClass_linearIndependent (hs : 0<s) :
    LinearIndependent K (standardClass (K := K) α β) := by
  apply LinearIndependent.of_comp (diagonalQuotientMap α β).toLinearMap
  have he : (diagonalQuotientMap (K := K) α β).toLinearMap ∘ standardClass α β=
      fun C : Σ r,BandChain α β r => monomial (chainDiagonalExponent C.2.val) 1 := by
    funext C
    exact diagonalMap_standardPolynomial α β C.2
  rw [he]
  exact diagonalStandardProducts_linearIndependent α β hs

/-- The full Hibi chain basis, in the literal binomial quotient. -/
def standardBasis (hs : 0<s) : Module.Basis (Σ r,BandChain α β r) K
    (MvPolynomial (IntervalIndex α β) K⧸relationIdeal α β) :=
  Module.Basis.mk (standardClass_linearIndependent α β hs)
    (by rw [←standardSpan_eq_top (K := K) α β]; exact le_rfl)

end PaperVerification.AlternatingForms.Hibi
