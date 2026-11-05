module

public import PaperVerification.FermionStrictPolynomialBoxes
public import PaperVerification.FermionPairedRank
public import Mathlib.Data.Fin.Embedding

/-!
# Every strict box is a first interval times a paired tail box

The compulsory first step is unmarked. Deleting it lowers all remaining
heights by one, and the remaining side lengths are exactly the paired
bounds with s=2 and u=v=r. This is an equivalence of the complete index
types, not a recurrence assumed for their cardinalities.

-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.Fermion

open Exterior Endpoint Newton
open scoped BigOperators

variable {n : ℕ}

local instance FermionStrictIndexRecursion_localInst_1 (m : ℕ) : DecidableEq (Fin m ⊕ Fin m) :=
  (interleavedOddOrder m).toDecidableEq

/-- Equality of a dependent rectangle index is equality of its actual word
and its actual exponent vector; proof fields carry no additional data. -/
theorem sigmaNestedSubtype_ext {I A : Type*} {p : I → A → Prop} {q : I → Prop}
    {x y : Sigma (fun i ↦ {a : {a : A // p i a} // q i})}
    (hi : x.1=y.1) (ha : x.2.val.val=y.2.val.val) : x=y := by
  rcases x with ⟨i,⟨⟨a,hpa⟩,hqa⟩⟩
  rcases y with ⟨j,⟨⟨b,hpb⟩,hqb⟩⟩
  cases hi
  cases ha
  rfl

def oddSuccEmbedding (n : ℕ) : OddIndex n ↪ OddIndex (n+1) :=
  (Fin.succEmb n).sumMap (Fin.succEmb n)

def wordCons (T : Finset (OddIndex n)) : Finset (OddIndex (n+1)) :=
  T.map (oddSuccEmbedding n)

def wordTail (T : Finset (OddIndex (n+1))) : Finset (OddIndex n) :=
  Finset.univ.filter (fun a ↦ oddSuccEmbedding n a ∈ T)

@[simp] theorem mem_wordCons_inl (T : Finset (OddIndex n)) (i : Fin n) :
    Sum.inl i.succ ∈ wordCons T ↔ Sum.inl i ∈ T := by
  change (oddSuccEmbedding n) (Sum.inl i) ∈ T.map (oddSuccEmbedding n) ↔ Sum.inl i ∈ T
  exact Finset.mem_map' (oddSuccEmbedding n)

@[simp] theorem mem_wordCons_inr (T : Finset (OddIndex n)) (i : Fin n) :
    Sum.inr i.succ ∈ wordCons T ↔ Sum.inr i ∈ T := by
  change (oddSuccEmbedding n) (Sum.inr i) ∈ T.map (oddSuccEmbedding n) ↔ Sum.inr i ∈ T
  exact Finset.mem_map' (oddSuccEmbedding n)

@[simp] theorem head_inl_not_mem_wordCons (T : Finset (OddIndex n)) :
    Sum.inl (0 : Fin (n+1)) ∉ wordCons T := by
  simp [wordCons,oddSuccEmbedding,Function.Embedding.sumMap,Finset.mem_map,Sum.exists]

@[simp] theorem head_inr_not_mem_wordCons (T : Finset (OddIndex n)) :
    Sum.inr (0 : Fin (n+1)) ∉ wordCons T := by
  simp [wordCons,oddSuccEmbedding,Function.Embedding.sumMap,Finset.mem_map,Sum.exists]

@[simp] theorem wordTail_wordCons (T : Finset (OddIndex n)) : wordTail (wordCons T)=T := by
  ext a
  simp only [wordTail,Finset.mem_filter,Finset.mem_univ,true_and,wordCons,Finset.mem_map']

theorem wordCons_wordTail (T : Finset (OddIndex (n+1)))
    (hθ : Sum.inl (0 : Fin (n+1)) ∉ T) (hξ : Sum.inr (0 : Fin (n+1)) ∉ T) :
    wordCons (wordTail T)=T := by
  ext a
  cases a with
  | inl i =>
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simp only [head_inl_not_mem_wordCons,hθ]
      · simp only [mem_wordCons_inl,wordTail,Finset.mem_filter,Finset.mem_univ,true_and]
        rfl
  | inr i =>
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simp only [head_inr_not_mem_wordCons,hξ]
      · simp only [mem_wordCons_inr,wordTail,Finset.mem_filter,Finset.mem_univ,true_and]
        rfl

theorem wordCons_prefix (T : Finset (OddIndex n)) (j : ℕ) :
    wordCons T ∩ pairedPrefix (n+1) (j+1)=wordCons (T ∩ pairedPrefix n j) := by
  ext a
  cases a with
  | inl i =>
      refine Fin.cases ?_ (fun q ↦ ?_) i
      · simp only [Finset.mem_inter,head_inl_not_mem_wordCons,false_and]
      · simp only [Finset.mem_inter,mem_wordCons_inl,mem_pairedPrefix_inl,
          Fin.val_succ,Nat.add_lt_add_iff_right]
  | inr i =>
      refine Fin.cases ?_ (fun q ↦ ?_) i
      · simp only [Finset.mem_inter,head_inr_not_mem_wordCons,false_and]
      · simp only [Finset.mem_inter,mem_wordCons_inr,mem_pairedPrefix_inr,
          Fin.val_succ,Nat.add_lt_add_iff_right]

theorem wordCons_prefix_card (T : Finset (OddIndex n)) (j : ℕ) :
    (wordCons T ∩ pairedPrefix (n+1) (j+1)).card=(T ∩ pairedPrefix n j).card := by
  rw [wordCons_prefix,wordCons,Finset.card_map]

@[simp] theorem wordCons_card (T : Finset (OddIndex n)) : (wordCons T).card=T.card :=
  Finset.card_map _

theorem strictWord_wordCons_iff (T : Finset (OddIndex n)) :
    StrictWord (wordCons T) ↔ ValidWord T := by
  constructor
  · intro h j hj
    have hh := h (j+1) (Nat.succ_pos _) (Nat.succ_le_succ hj)
    rw [wordCons_prefix_card] at hh
    omega
  · intro h j hj hjn
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hj)
    rw [wordCons_prefix_card]
    have hh := h k (by omega)
    omega

theorem StrictWord.head_absent {T : Finset (OddIndex (n+1))} (hT : StrictWord T) :
    Sum.inl (0 : Fin (n+1)) ∉ T ∧ Sum.inr (0 : Fin (n+1)) ∉ T := by
  have hc := hT 1 (by decide) (Nat.succ_le_succ (Nat.zero_le n))
  have he : T ∩ pairedPrefix (n+1) 1=∅ := Finset.card_eq_zero.mp (by omega)
  constructor
  · intro h
    have hm : Sum.inl (0 : Fin (n+1)) ∈ T ∩ pairedPrefix (n+1) 1 :=
      Finset.mem_inter.mpr ⟨h,by simp⟩
    rw [he] at hm
    exact Finset.notMem_empty _ hm
  · intro h
    have hm : Sum.inr (0 : Fin (n+1)) ∈ T ∩ pairedPrefix (n+1) 1 :=
      Finset.mem_inter.mpr ⟨h,by simp⟩
    rw [he] at hm
    exact Finset.notMem_empty _ hm

theorem wordHeight_wordCons (T : Finset (OddIndex n)) (hT : ValidWord T)
    (j : ℕ) (hj : j≤n) : wordHeight (wordCons T) (j+1)=1+wordHeight T j := by
  rw [wordHeight,wordHeight,wordCons_prefix_card]
  have hh := hT j hj
  omega

theorem strictWordBoxBounds_wordCons_zero (r : Fin (n+1) → ℕ)
    (T : Finset (OddIndex n)) (hT : ValidWord T) :
    strictWordBoxBounds r (wordCons T) 0=r 0 := by
  rw [strictWordBoxBounds,Fin.val_zero,zero_add,
    wordHeight_wordCons T hT 0 (Nat.zero_le n),wordHeight_zero,add_zero,mul_one]

theorem strictWordBoxBounds_wordCons_succ (r : Fin (n+1) → ℕ)
    (T : Finset (OddIndex n)) (hT : ValidWord T) (i : Fin n) :
    strictWordBoxBounds r (wordCons T) i.succ=
      wordBoxBounds (fun j ↦ r j.succ) (fun j ↦ r j.succ) (fun j ↦ r j.succ) 2 T i := by
  rw [strictWordBoxBounds,Fin.val_succ,
    wordHeight_wordCons T hT (i.val+1) (Nat.succ_le_of_lt i.isLt)]
  have hs := wordHeight_steps T hT i.val i.isLt
  by_cases hθ : Sum.inl i ∈ T <;> by_cases hξ : Sum.inr i ∈ T <;>
    simp only [wordBoxBounds,wordMark,hθ,hξ,if_true,if_false,pairedBoxBound,HeightStep] at hs ⊢ <;>
    nlinarith

def strictIndexTail (r : Fin (n+1) → ℕ) (z : StrictPowerIndex r) :
    Fin (r 0) × PairedPowerIndex (fun j ↦ r j.succ)
      (fun j ↦ r j.succ) (fun j ↦ r j.succ) 2 := by
  let T := wordTail z.1
  have hstrict := strictWord_of_polynomialIndex r z.1 z.2
  have he : wordCons T=z.1 := wordCons_wordTail z.1 hstrict.head_absent.1 hstrict.head_absent.2
  have hT : ValidWord T := strictWord_wordCons_iff T |>.mp (he.symm ▸ hstrict)
  have hfirst : z.2.val.val 0<r 0 := by
    have h := z.2.val.property 0
    have hb : strictWordBoxBounds r z.1 0 = r 0 := by
      rw [←he,strictWordBoxBounds_wordCons_zero r T hT]
    simpa only [hb] using h
  refine (⟨z.2.val.val 0,hfirst⟩,⟨T,⟨⟨Finsupp.equivFunOnFinite.symm
    (fun i ↦ z.2.val.val i.succ),?_⟩,hT⟩⟩)
  intro i
  change z.2.val.val i.succ < _
  rw [←strictWordBoxBounds_wordCons_succ r T hT i,he]
  exact z.2.val.property i.succ

def strictIndexCons (r : Fin (n+1) → ℕ)
    (z : Fin (r 0) × PairedPowerIndex (fun j ↦ r j.succ)
      (fun j ↦ r j.succ) (fun j ↦ r j.succ) 2) : StrictPowerIndex r := by
  let T := z.2.1
  have hT : ValidWord T := z.2.2.property
  refine ⟨wordCons T,⟨⟨Finsupp.equivFunOnFinite.symm
    (Fin.cons z.1.val (fun i ↦ z.2.2.val.val i)),?_⟩,
      (strictWord_wordCons_iff T |>.mpr hT).valid⟩⟩
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simpa only [Finsupp.coe_equivFunOnFinite_symm,Fin.cons_zero,
      strictWordBoxBounds_wordCons_zero r T hT] using z.1.isLt
  · simpa only [Finsupp.coe_equivFunOnFinite_symm,Fin.cons_succ,
      strictWordBoxBounds_wordCons_succ r T hT j] using z.2.2.val.property j

/-- The whole strict monomial index, preserving the full exterior support
after its compulsory unmarked first position. -/
def strictIndexTailEquiv (r : Fin (n+1) → ℕ) :
    StrictPowerIndex r ≃ Fin (r 0) × PairedPowerIndex (fun j ↦ r j.succ)
      (fun j ↦ r j.succ) (fun j ↦ r j.succ) 2 where
  toFun := strictIndexTail r
  invFun := strictIndexCons r
  left_inv z := by
    have hs := strictWord_of_polynomialIndex r z.1 z.2
    have he := wordCons_wordTail z.1 hs.head_absent.1 hs.head_absent.2
    apply sigmaNestedSubtype_ext he
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;>
      simp only [strictIndexTail,strictIndexCons,Finsupp.coe_equivFunOnFinite_symm,
        Fin.cons_zero,Fin.cons_succ]
  right_inv z := by
    apply Prod.ext
    · apply Fin.ext
      simp only [strictIndexTail,strictIndexCons,Finsupp.coe_equivFunOnFinite_symm,Fin.cons_zero]
    · apply sigmaNestedSubtype_ext (wordTail_wordCons z.2.1)
      ext i
      simp only [strictIndexTail,strictIndexCons,Finsupp.coe_equivFunOnFinite_symm,Fin.cons_succ]

theorem strictIndexTailEquiv_card (r : Fin (n+1) → ℕ) (z : StrictPowerIndex r) :
    ((strictIndexTailEquiv r z).2.1).card=z.1.card := by
  have hs := strictWord_of_polynomialIndex r z.1 z.2
  have he := wordCons_wordTail z.1 hs.head_absent.1 hs.head_absent.2
  have hc := congrArg Finset.card he
  change (wordTail z.1).card = z.1.card
  simpa only [wordCons_card] using hc

theorem card_strictPowerIndex (r : Fin n → ℕ) (hn : 0<n) :
    Fintype.card (StrictPowerIndex r)=2^(n-1)*(∏ i,r i)*n.factorial := by
  cases n with
  | zero => omega
  | succ n =>
      rw [Fintype.card_congr (strictIndexTailEquiv r),Fintype.card_prod,Fintype.card_fin,
        card_pairedPowerIndex_closed _ _ _ _ (fun i ↦ by omega),Fin.prod_univ_succ]
      have hfac : (2 : ℕ).ascFactorial n=(n+1).factorial := by
        simpa [Nat.add_comm] using Nat.factorial_mul_ascFactorial 1 n
      rw [hfac,Nat.add_sub_cancel]
      ring

end PaperVerification.Fermion
