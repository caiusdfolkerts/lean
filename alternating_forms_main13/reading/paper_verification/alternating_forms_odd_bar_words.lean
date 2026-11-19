module

public import PaperVerification.AlternatingFormsOddBar
public import PaperVerification.AlternatingFormsPBWNormalForm
public import PaperVerification.AlternatingFormsBarCutDifferential
public import Mathlib.Data.List.OfFn

/-!
# The original odd standard basis as normal words

The positive bar factors are put in bijection with nonempty increasing
words of actual good Plucker variables. The value of such a word is its
literal product in the original quotient. In particular, a concatenation
that is already increasing multiplies to the corresponding basis vector
with coefficient one, without lower terms.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

open MvPolynomial Hibi
open scoped BigOperators

universe u
variable {K : Type u} [Field K] [CharZero K]
  (k t : ℕ) (hs : t+2≤k+1)

local notation "α" => oddIntervalLower k (t+2) hs
local notation "β" => oddIntervalUpper k (t+2) hs
local notation "I" => IntervalIndex α β

def oddChainTupleEquiv :
    OddStandardIndex k t hs ≃ {q : Σ r,Fin r → I // Monotone q.2} where
  toFun C := ⟨⟨C.1,intervalIndexOfChain α β C.2⟩,C.2.property.2.2⟩
  invFun q := ⟨q.val.1,⟨fun j ↦ (q.val.2 j).val.val,
    (fun j ↦ (q.val.2 j).val.property),
    (fun j a ↦ (q.val.2 j).property a),q.property⟩⟩
  left_inv C := by
    rcases C with ⟨r,C⟩
    apply Sigma.ext rfl
    apply heq_of_eq
    apply Subtype.ext
    rfl
  right_inv q := by
    apply Subtype.ext
    apply Sigma.ext rfl
    apply heq_of_eq
    funext j
    apply Subtype.ext
    apply Subtype.ext
    rfl

def monotoneTupleWordEquiv (J : Type*) [Preorder J] :
    {q : Σ r,Fin r → J // Monotone q.2} ≃
      {L : List J // L.Pairwise (·≤·)} :=
  Equiv.subtypeEquiv List.equivSigmaTuple.symm (by
    intro q
    change Monotone q.2 ↔ (List.ofFn q.2).Pairwise (·≤·)
    rw [List.pairwise_ofFn]
    constructor
    · intro h i j hij
      exact h hij.le
    · intro h i j hij
      rcases hij.eq_or_lt with rfl | hij
      · exact le_rfl
      · exact h hij)

def oddStandardWordEquiv :
    OddStandardIndex k t hs ≃ {L : List I // L.Pairwise (·≤·)} :=
  (oddChainTupleEquiv k t hs).trans (monotoneTupleWordEquiv I)

@[simp] theorem oddStandardWordEquiv_val (C : OddStandardIndex k t hs) :
    (oddStandardWordEquiv k t hs C).val=
      List.ofFn (intervalIndexOfChain α β C.2) := rfl

@[simp] theorem oddStandardWordEquiv_length (C : OddStandardIndex k t hs) :
    (oddStandardWordEquiv k t hs C).val.length=C.1 := List.length_ofFn

def PositiveNormalWord (J : Type*) [Preorder J] :=
  {L : List J // 0<L.length ∧ L.IsChain (·≤·)}

def oddPositiveWord (C : OddPositiveStandardIndex (K := K) k t hs) :
    PositiveNormalWord I :=
  ⟨(oddStandardWordEquiv k t hs C.down.val).val,
    by rw [oddStandardWordEquiv_length]
       exact oddStandardIndex_degree_positive k t hs C.down.val C.down.property,
    List.isChain_iff_pairwise.mpr (oddStandardWordEquiv k t hs C.down.val).property⟩

theorem oddPositiveWord_bijective : Function.Bijective (oddPositiveWord (K := K) k t hs) := by
  constructor
  · intro C D h
    apply ULift.ext
    apply Subtype.ext
    apply (oddStandardWordEquiv k t hs).injective
    apply Subtype.ext
    exact congrArg (fun W : PositiveNormalWord I => W.val) h
  · intro L
    let C := (oddStandardWordEquiv k t hs).symm
      ⟨L.val,List.isChain_iff_pairwise.mp L.property.2⟩
    have hC : C≠oddEmptyStandardIndex k t hs := by
      intro he
      have hlen := oddStandardWordEquiv_length k t hs C
      have hword : (oddStandardWordEquiv k t hs C).val=L.val :=
        congrArg Subtype.val ((oddStandardWordEquiv k t hs).apply_symm_apply
          ⟨L.val,List.isChain_iff_pairwise.mp L.property.2⟩)
      rw [hword,he] at hlen
      have hpos := L.property.1
      change L.val.length=0 at hlen
      omega
    refine ⟨⟨⟨C,hC⟩⟩,?_⟩
    apply Subtype.ext
    change (oddStandardWordEquiv k t hs C).val = L.val
    exact congrArg (fun W : {L : List I // L.Pairwise (· ≤ ·)} => W.val)
      ((oddStandardWordEquiv k t hs).apply_symm_apply
        ⟨L.val,List.isChain_iff_pairwise.mp L.property.2⟩)

def oddPositiveWordEquiv :
    OddPositiveStandardIndex (K := K) k t hs ≃ PositiveNormalWord I :=
  Equiv.ofBijective (oddPositiveWord k t hs) (oddPositiveWord_bijective k t hs)

@[simp] theorem oddPositiveWord_degree (C : OddPositiveStandardIndex (K := K) k t hs) :
    (oddPositiveWordEquiv k t hs C).val.length=oddPositiveDegree (K := K) k t hs C :=
  oddStandardWordEquiv_length k t hs C.down.val

theorem oddGoodMap_standard_word (C : OddStandardIndex k t hs) :
    oddGoodMap (K := K) k t hs (word α β (oddStandardWordEquiv k t hs C).val)=
      oddPluckerStandardBasis k t hs C := by
  rw [←oddGoodMap_standardPolynomial k t hs C]
  congr 1
  simp only [oddStandardWordEquiv_val,word,List.map_ofFn,List.prod_ofFn,
    standardPolynomial,Function.comp_def]

theorem oddAugmentedBasis_word (C : OddPositiveStandardIndex (K := K) k t hs) :
    oddAugmentedBasis (K := K) k t hs (some C)=
      oddGoodMap k t hs (word α β (oddPositiveWordEquiv k t hs C).val) := by
  rw [oddAugmentedBasis_some]
  exact (oddGoodMap_standard_word k t hs C.down.val).symm

theorem word_append (L M : List I) :
    word (K := K) α β (L++M)=word α β L*word α β M := by
  simp only [word,List.map_append,List.prod_append]

def appendPositiveNormalWord (L M : PositiveNormalWord I)
    (h : (L.val++M.val).IsChain (·≤·)) : PositiveNormalWord I :=
  ⟨L.val++M.val,by rw [List.length_append]; exact Nat.add_pos_left L.property.1 _,h⟩

/-- Every already-normal product has its literal concatenation as its
unique output basis vector, with coefficient one. -/
theorem oddAugmentedBasis_mul_of_normal
    (C D : OddPositiveStandardIndex (K := K) k t hs)
    (h : ((oddPositiveWordEquiv k t hs C).val++
      (oddPositiveWordEquiv k t hs D).val).IsChain (·≤·)) :
    oddAugmentedBasis k t hs (some C)*oddAugmentedBasis k t hs (some D)=
      oddAugmentedBasis k t hs
        (some ((oddPositiveWordEquiv k t hs).symm
          (appendPositiveNormalWord k t hs
            (oddPositiveWordEquiv k t hs C) (oddPositiveWordEquiv k t hs D) h))) := by
  rw [oddAugmentedBasis_word,oddAugmentedBasis_word,oddAugmentedBasis_word,
    Equiv.apply_symm_apply]
  change oddGoodMap k t hs (word α β (oddPositiveWordEquiv k t hs C).val)*
    oddGoodMap k t hs (word α β (oddPositiveWordEquiv k t hs D).val)=
      oddGoodMap k t hs (word α β ((oddPositiveWordEquiv k t hs C).val++
        (oddPositiveWordEquiv k t hs D).val))
  rw [word_append,map_mul]

theorem odd_productCoefficients_of_normal
    (C D : OddPositiveStandardIndex (K := K) k t hs)
    (h : ((oddPositiveWordEquiv k t hs C).val++
      (oddPositiveWordEquiv k t hs D).val).IsChain (·≤·)) :
    PaperVerification.AugmentedAlgebraBasis.productCoefficients
        (oddAugmentedBasis (K := K) k t hs) C D=
      Finsupp.single ((oddPositiveWordEquiv k t hs).symm
        (appendPositiveNormalWord k t hs
          (oddPositiveWordEquiv k t hs C) (oddPositiveWordEquiv k t hs D) h)) 1 := by
  unfold PaperVerification.AugmentedAlgebraBasis.productCoefficients
  change PaperVerification.AugmentedAlgebraBasis.positiveCoordinates
    (oddAugmentedBasis k t hs)
      (oddAugmentedBasis k t hs (some C)*oddAugmentedBasis k t hs (some D))=_
  rw [oddAugmentedBasis_mul_of_normal k t hs C D h]
  exact PaperVerification.AugmentedAlgebraBasis.positiveCoordinates_vector _ _

end PaperVerification.AlternatingForms

