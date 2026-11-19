module

public import PaperVerification.AlternatingFormsReplacementWords
public import Mathlib.Data.Finset.Sum

/-!
# The actual first-exit prefix as two matching selections

The even/odd bijection of a `2h`-vertex prefix gives the two finite sets used
by the Boolean inverse. Their cardinality is derived from the actual
increasing tuple, and their membership is identified with the original
canonical matching vertices. No selection or prefix-count hypothesis is
added to the first-failure theorem.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace PaperVerification.AlternatingForms

open scoped BigOperators

/-- The literal two matching positions in every finite even prefix. -/
def evenOddPrefixEquiv (h : ℕ) : Fin h ⊕ Fin h ≃ Fin (2*h) where
  toFun
    | .inl i => ⟨2*i.val,by have := i.isLt; omega⟩
    | .inr i => ⟨2*i.val+1,by have := i.isLt; omega⟩
  invFun j := if j.val%2=0 then Sum.inl ⟨j.val/2,by have := j.isLt; omega⟩
    else Sum.inr ⟨j.val/2,by have := j.isLt; omega⟩
  left_inv i := by
    cases i with
    | inl i =>
        have he : (2*i.val)%2=0 := by omega
        simp only [he,if_pos,Sum.inl.injEq]
        apply Fin.ext
        change (2*i.val)/2=i.val
        omega
    | inr i =>
        have he : ¬(2*i.val+1)%2=0 := by omega
        simp only [he,if_false,Sum.inr.injEq]
        apply Fin.ext
        change (2*i.val+1)/2=i.val
        omega
  right_inv j := by
    dsimp only
    split_ifs with he
    · apply Fin.ext
      dsimp
      omega
    · apply Fin.ext
      dsimp
      omega

@[simp] theorem evenOddPrefixEquiv_inl (h : ℕ) (i : Fin h) :
    (evenOddPrefixEquiv h (Sum.inl i)).val=2*i.val := rfl

@[simp] theorem evenOddPrefixEquiv_inr (h : ℕ) (i : Fin h) :
    (evenOddPrefixEquiv h (Sum.inr i)).val=2*i.val+1 := rfl

def tuplePrefixPositions {s n : ℕ} (I : Fin s → Fin n) (h : ℕ) : Finset (Fin s) :=
  Finset.univ.filter (fun i => (I i).val<2*h)

def tuplePrefixEmbedding {s n : ℕ} (I : Fin s → Fin n) (hI : StrictMono I) (h : ℕ) :
    tuplePrefixPositions I h ↪ Fin (2*h) where
  toFun i := ⟨(I i.val).val,(Finset.mem_filter.mp i.property).2⟩
  inj' a b hab := by
    apply Subtype.ext
    apply hI.injective
    apply Fin.ext
    exact congrArg (fun z : Fin (2*h) => z.val) hab

def tuplePrefixSelection {s n : ℕ} (I : Fin s → Fin n) (hI : StrictMono I) (h : ℕ) :
    Finset (Fin (2*h)) :=
  Finset.univ.map (tuplePrefixEmbedding I hI h)

theorem tuplePrefixSelection_card {s n : ℕ}
    (I : Fin s → Fin n) (hI : StrictMono I) (h : ℕ) :
    (tuplePrefixSelection I hI h).card=(tuplePrefixPositions I h).card := by
  simp only [tuplePrefixSelection,Finset.card_map,Finset.card_univ,Fintype.card_coe]

theorem mem_tuplePrefixSelection {s n : ℕ}
    (I : Fin s → Fin n) (hI : StrictMono I) (h : ℕ) (q : Fin (2*h)) :
    q∈tuplePrefixSelection I hI h ↔ ∃ i,(I i).val=q.val := by
  constructor
  · intro hq
    obtain ⟨i,hi,he⟩ := Finset.mem_map.mp hq
    exact ⟨i.val,congrArg Fin.val he⟩
  · rintro ⟨i,hi⟩
    let a : tuplePrefixPositions I h := ⟨i,Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,hi.symm ▸ q.isLt⟩⟩
    apply Finset.mem_map.mpr
    exact ⟨a,Finset.mem_univ _,Fin.ext hi⟩

def tuplePrefixMatchingSelection {s n : ℕ}
    (I : Fin s → Fin n) (hI : StrictMono I) (h : ℕ) : Finset (Fin h ⊕ Fin h) :=
  (tuplePrefixSelection I hI h).map (evenOddPrefixEquiv h).symm.toEmbedding

def tuplePrefixLeft {s n : ℕ} (I : Fin s → Fin n) (hI : StrictMono I) (h : ℕ) :
    Finset (Fin h) := (tuplePrefixMatchingSelection I hI h).toLeft

def tuplePrefixRight {s n : ℕ} (I : Fin s → Fin n) (hI : StrictMono I) (h : ℕ) :
    Finset (Fin h) := (tuplePrefixMatchingSelection I hI h).toRight

theorem tuplePrefix_matching_card {s n : ℕ}
    (I : Fin s → Fin n) (hI : StrictMono I) (h : ℕ) :
    (tuplePrefixLeft I hI h).card+(tuplePrefixRight I hI h).card=
      (tuplePrefixPositions I h).card := by
  rw [tuplePrefixLeft,tuplePrefixRight,Finset.card_toLeft_add_card_toRight,
    tuplePrefixMatchingSelection,Finset.card_map,tuplePrefixSelection_card]

theorem mem_tuplePrefixLeft {s n : ℕ}
    (I : Fin s → Fin n) (hI : StrictMono I) (h : ℕ) (a : Fin h) :
    a∈tuplePrefixLeft I hI h ↔ ∃ i,(I i).val=2*a.val := by
  rw [tuplePrefixLeft,Finset.mem_toLeft,tuplePrefixMatchingSelection,
    Finset.mem_map_equiv,Equiv.symm_symm,mem_tuplePrefixSelection,evenOddPrefixEquiv_inl]

theorem mem_tuplePrefixRight {s n : ℕ}
    (I : Fin s → Fin n) (hI : StrictMono I) (h : ℕ) (a : Fin h) :
    a∈tuplePrefixRight I hI h ↔ ∃ i,(I i).val=2*a.val+1 := by
  rw [tuplePrefixRight,Finset.mem_toRight,tuplePrefixMatchingSelection,
    Finset.mem_map_equiv,Equiv.symm_symm,mem_tuplePrefixSelection,evenOddPrefixEquiv_inr]

/-- The actual first-exit tuple gives the exact two selections required by
prefix division. In particular their degree is proved rather than assumed. -/
theorem odd_left_failure_matching_selection {k s : ℕ}
    (I : Fin s → Fin (2*k+1)) (hI : StrictMono I)
    (hbad : ∃ i,(I i).val<2*i.val) :
    ∃ h : ℕ,0<h ∧ h≤k ∧
      (tuplePrefixLeft I hI h).card+(tuplePrefixRight I hI h).card=h+1 := by
  obtain ⟨h,hpos,hk,hcount⟩ := odd_left_failure_prefix I hI hbad
  refine ⟨h,hpos,hk,?_⟩
  rw [tuplePrefix_matching_card]
  exact hcount

end PaperVerification.AlternatingForms
