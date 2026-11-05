module

public import PaperVerification.FermionPathEnumeration
public import PaperVerification.FermionPairedIndex

/-!
# Every actual exterior box occurs in the path enumeration

The finite mark functions and actual exterior supports are in bijection.
The recursive path weight is exactly the product of all printed side lengths
for valid words and zero for invalid words.  Thus the transfer calculation
enumerates every box, rather than a selected family of paths.

-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

local instance FermionPathBoxes_localInst_1 (p : Prop) : Decidable p := Classical.propDecidable p

namespace PaperVerification.Fermion.Paths

open Exterior Endpoint
open scoped BigOperators

variable {n : ℕ}

local instance FermionPathBoxes_localInst_2 (m : ℕ) : DecidableEq (Fin m ⊕ Fin m) :=
  (interleavedOddOrder m).toDecidableEq

def wordOfMarks (m : Fin n → Mark) : Finset (OddIndex n) :=
  (Finset.univ.filter (fun i ↦ m i=.theta ∨ m i=.double)).disjSum
    (Finset.univ.filter (fun i ↦ m i=.xi ∨ m i=.double))

@[simp] theorem wordOfMarks_inl (m : Fin n → Mark) (i : Fin n) :
    Sum.inl i ∈ wordOfMarks m ↔ m i=.theta ∨ m i=.double := by simp [wordOfMarks]

@[simp] theorem wordOfMarks_inr (m : Fin n → Mark) (i : Fin n) :
    Sum.inr i ∈ wordOfMarks m ↔ m i=.xi ∨ m i=.double := by simp [wordOfMarks]

@[simp] theorem wordMark_wordOfMarks (m : Fin n → Mark) (i : Fin n) :
    wordMark (wordOfMarks m) i=m i := by
  cases hm : m i <;> simp [wordMark,hm]

def marksWordEquiv (n : ℕ) : (Fin n → Mark) ≃ Finset (OddIndex n) where
  toFun := wordOfMarks
  invFun := wordMark
  left_inv m := funext (wordMark_wordOfMarks m)
  right_inv W := by
    ext a
    cases a with
    | inl i =>
        by_cases hθ : Sum.inl i ∈ W <;> by_cases hξ : Sum.inr i ∈ W <;>
          simp [wordMark,hθ,hξ]
    | inr i =>
        by_cases hθ : Sum.inl i ∈ W <;> by_cases hξ : Sum.inr i ∈ W <;>
          simp [wordMark,hθ,hξ]

@[simp] theorem wordMultiplicity_wordOfMarks (m : Fin n → Mark) (i : Fin n) :
    wordMultiplicity (wordOfMarks m) i=markDegree (m i) := by
  cases hm : m i <;> simp [wordMultiplicity,markDegree,hm]

theorem wordOfMarks_prefix_card (m : Fin n → Mark) (j : ℕ) :
    (wordOfMarks m ∩ pairedPrefix n j).card =
      ∑ i : Fin n, if i.val<j then markDegree (m i) else 0 := by
  rw [prefix_card_eq_multiplicity_sum,Finset.sum_filter]
  simp only [wordMultiplicity_wordOfMarks]

theorem pairedPrefix_full (n : ℕ) : pairedPrefix n n=Finset.univ := by
  ext a
  cases a <;> simp

theorem wordOfMarks_card (m : Fin n → Mark) :
    (wordOfMarks m).card=∑ i,markDegree (m i) := by
  have h := wordOfMarks_prefix_card m n
  simpa only [pairedPrefix_full,Finset.inter_univ,Fin.is_lt,if_true] using h

theorem wordOfMarks_snoc_prefix (m : Fin n → Mark) (a : Mark) (j : ℕ) (hj : j≤n) :
    (wordOfMarks (Fin.snoc m a) ∩ pairedPrefix (n+1) j).card =
      (wordOfMarks m ∩ pairedPrefix n j).card := by
  rw [wordOfMarks_prefix_card,wordOfMarks_prefix_card,Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc,Fin.snoc_castSucc,Fin.val_last,Fin.snoc_last,
    if_neg (Nat.not_lt.mpr hj),add_zero]

theorem wordOfMarks_snoc_card (m : Fin n → Mark) (a : Mark) :
    (wordOfMarks (Fin.snoc m a)).card=(wordOfMarks m).card+markDegree a := by
  rw [wordOfMarks_card,wordOfMarks_card,Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc,Fin.snoc_last]

theorem validWord_snoc_iff (m : Fin n → Mark) (a : Mark) :
    ValidWord (wordOfMarks (Fin.snoc m a)) ↔
      ValidWord (wordOfMarks m) ∧ (wordOfMarks m).card+markDegree a≤n+1 := by
  constructor
  · intro h
    constructor
    · intro j hj
      rw [← wordOfMarks_snoc_prefix m a j hj]
      exact h j (hj.trans (Nat.le_succ n))
    · have hh := h (n+1) le_rfl
      simpa only [pairedPrefix_full,Finset.inter_univ,wordOfMarks_snoc_card] using hh
  · rintro ⟨h,ha⟩ j hj
    by_cases he : j=n+1
    · subst j
      simpa only [pairedPrefix_full,Finset.inter_univ,wordOfMarks_snoc_card] using ha
    · have hle : j≤n := by omega
      rw [wordOfMarks_snoc_prefix m a j hle]
      exact h j hle

theorem pathHeight_eq_card (m : Fin n → Mark) (h : ValidWord (wordOfMarks m)) :
    pathHeight m=n-(wordOfMarks m).card := by
  induction n with
  | zero => simp [pathHeight,wordOfMarks]
  | succ n ih =>
      obtain ⟨⟨a,m⟩,rfl⟩ := (Fin.snocEquiv (fun _ : Fin (n+1) ↦ Mark)).surjective m
      obtain ⟨hm,ha⟩ := (validWord_snoc_iff m a).mp h
      have hc := hm n le_rfl
      rw [pairedPrefix_full,Finset.inter_univ] at hc
      simp only [Fin.snocEquiv_apply] at *
      rw [pathHeight,Fin.init_snoc,Fin.snoc_last,ih m hm,wordOfMarks_snoc_card]
      cases a <;> simp only [advance,markDegree] at * <;> omega

def boxProduct {A : Type*} [CommSemiring A] (r u v : ℕ → ℕ) (s : ℕ)
    (m : Fin n → Mark) : A :=
  ∏ i : Fin n, (pairedBoxBound (r i.val) (u i.val) (v i.val) s
    (wordHeight (wordOfMarks m) i.val) (m i) : A)

theorem boxProduct_snoc {A : Type*} [CommSemiring A]
    (r u v : ℕ → ℕ) (s : ℕ) (m : Fin n → Mark) (a : Mark) :
    boxProduct (A := A) r u v s (Fin.snoc m a) = boxProduct r u v s m *
      (pairedBoxBound (r n) (u n) (v n) s (n-(wordOfMarks m).card) a : A) := by
  rw [boxProduct,Fin.prod_univ_castSucc,boxProduct]
  have hprefix (i : Fin n) :
      wordHeight (wordOfMarks (Fin.snoc m a)) i.val=wordHeight (wordOfMarks m) i.val := by
    rw [wordHeight,wordHeight,wordOfMarks_snoc_prefix m a i.val i.isLt.le]
  have hlast : wordHeight (wordOfMarks (Fin.snoc m a)) n=n-(wordOfMarks m).card := by
    rw [wordHeight,wordOfMarks_snoc_prefix m a n le_rfl,pairedPrefix_full,Finset.inter_univ]
  simp only [Fin.val_castSucc,Fin.snoc_castSucc,hprefix,Fin.val_last,Fin.snoc_last,hlast]

theorem pathCoefficient_eq_boxes {A : Type*} [CommSemiring A]
    (r u v : ℕ → ℕ) (s : ℕ) (t : A) (m : Fin n → Mark) :
    pathCoefficient r u v s t m =
      if ValidWord (wordOfMarks m) then boxProduct r u v s m*t^(wordOfMarks m).card else 0 := by
  classical
  induction n with
  | zero =>
      have h : ValidWord (wordOfMarks m) := by
        intro j hj
        have hj0 : j=0 := by omega
        subst j
        simp [wordOfMarks,pairedPrefix]
      rw [if_pos h]
      simp [pathCoefficient,boxProduct,wordOfMarks]
  | succ n ih =>
      obtain ⟨⟨a,m⟩,rfl⟩ := (Fin.snocEquiv (fun _ : Fin (n+1) ↦ Mark)).surjective m
      simp only [Fin.snocEquiv_apply] at *
      rw [pathCoefficient,Fin.init_snoc,Fin.snoc_last,ih m]
      by_cases hm : ValidWord (wordOfMarks m)
      · rw [if_pos hm,pathHeight_eq_card m hm]
        by_cases ha : (wordOfMarks m).card+markDegree a≤n+1
        · rw [if_pos ((validWord_snoc_iff m a).mpr ⟨hm,ha⟩),boxProduct_snoc,
            wordOfMarks_snoc_card,pow_add]
          ring
        · have hn : ¬ValidWord (wordOfMarks (Fin.snoc m a)) := by
            intro h
            exact ha ((validWord_snoc_iff m a).mp h).2
          rw [if_neg hn]
          have hc := hm n le_rfl
          rw [pairedPrefix_full,Finset.inter_univ] at hc
          cases a <;> simp only [markDegree] at ha
          · omega
          · omega
          · omega
          · have hz : n-(wordOfMarks m).card=0 := by omega
            simp only [pairedBoxBound,hz,mul_zero,Nat.cast_zero,zero_mul]
      · have hn : ¬ValidWord (wordOfMarks (Fin.snoc m a)) := by
          intro h
          exact hm ((validWord_snoc_iff m a).mp h).1
        simp only [if_neg hm,if_neg hn,zero_mul]

/-- The full exterior-word sum is the literal box sum with its exterior
degree exponent; invalid words contribute zero. -/
theorem sum_boxes_eq_closed {A : Type*} [CommSemiring A]
    (r u v : ℕ → ℕ) (s : ℕ) (t : A) (huv : ∀ i,u i+v i=r i*s) (n : ℕ) :
    (∑ m : Fin n → Mark,
      if ValidWord (wordOfMarks m) then boxProduct r u v s m*t^(wordOfMarks m).card else 0) =
      ((∏ i ∈ Finset.range n,r i : ℕ) : A)*(s.ascFactorial n : A)*(1+t)^n := by
  simp only [← pathCoefficient_eq_boxes]
  exact allPathPolynomial_eval_one r u v s t huv n

end PaperVerification.Fermion.Paths
