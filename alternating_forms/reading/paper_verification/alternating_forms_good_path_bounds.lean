module

public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Finset.Sort

/-!
# The exact good-index inequalities and binary strip bounds

The original exterior positions are shifted by one because the binary path
starts with a fixed up-step.  A selected position contributes a down-step.
The prefix count therefore counts indices `I_j+1<q` in a prefix of length
`q`.  The two inequalities below are exactly nonnegative height and the
upper strip bound, without truncated subtraction.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.AlternatingForms.GoodPaths

/-- Number of selected original letters in the first `q` binary steps,
including the initial fixed up-step in the prefix length. -/
def selectedBefore {s n : ℕ} (I : Fin s → Fin n) (q : ℕ) : ℕ :=
  (Finset.univ.filter fun i => (I i).val+1<q).card

theorem selectedBefore_le {s n : ℕ} (I : Fin s → Fin n) (q : ℕ) :
    selectedBefore I q≤s := by
  exact (Finset.card_filter_le _ _).trans_eq (Fintype.card_fin s)

/-- A strictly increasing list meets every prefix in an initial segment. -/
theorem lt_selectedBefore_iff {s n : ℕ} {I : Fin s → Fin n}
    (hI : StrictMono I) (q : ℕ) (i : Fin s) :
    i.val<selectedBefore I q ↔ (I i).val+1<q := by
  apply Fin.lt_card_filter_univ_iff_apply_of_imp
  intro a b hba ha
  have hb : (I b).val≤(I a).val := hI.monotone hba
  omega

/-- Just before a selected down-step, exactly its predecessors have occurred. -/
theorem selectedBefore_at {s n : ℕ} {I : Fin s → Fin n}
    (hI : StrictMono I) (i : Fin s) :
    selectedBefore I ((I i).val+1)=i.val := by
  unfold selectedBefore
  have hf : (Finset.univ.filter fun j => (I j).val+1<(I i).val+1)=Finset.Iio i := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Iio]
    change (I j).val+1<(I i).val+1 ↔ j < i
    exact Nat.add_lt_add_iff_right.trans hI.lt_iff_lt
  rw [hf,Fin.card_Iio]

/-- Just after a selected down-step, it too has occurred. -/
theorem selectedBefore_after {s n : ℕ} {I : Fin s → Fin n}
    (hI : StrictMono I) (i : Fin s) :
    selectedBefore I ((I i).val+2)=i.val+1 := by
  unfold selectedBefore
  have hf : (Finset.univ.filter fun j => (I j).val+1<(I i).val+2)=Finset.Iic i := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Iic]
    have he : (I j).val≤(I i).val ↔ j ≤ i := hI.le_iff_le
    omega
  rw [hf,Fin.card_Iic]

/-- The literal down-step indicator at a binary position. -/
def selectedAt {s n : ℕ} (I : Fin s → Fin n) (q : ℕ) : ℕ :=
  if ∃ i,(I i).val+1=q then 1 else 0

theorem selectedAt_le_one {s n : ℕ} (I : Fin s → Fin n) (q : ℕ) :
    selectedAt I q≤1 := by
  unfold selectedAt
  split_ifs <;> omega

/-- A prefix grows by precisely the selected-position indicator. -/
theorem selectedBefore_succ {s n : ℕ} {I : Fin s → Fin n}
    (hI : StrictMono I) (q : ℕ) :
    selectedBefore I (q+1)=selectedBefore I q+selectedAt I q := by
  by_cases hq : ∃ i,(I i).val+1=q
  · obtain ⟨i,rfl⟩ := hq
    rw [show (I i).val+1+1=(I i).val+2 by omega,
      selectedBefore_after hI i,selectedBefore_at hI i]
    simp [selectedAt]
  · have hf : (Finset.univ.filter fun i => (I i).val+1<q+1)=
        (Finset.univ.filter fun i => (I i).val+1<q) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      have hi : (I i).val+1≠q := fun he => hq ⟨i,he⟩
      omega
    simp only [selectedBefore,hf,selectedAt,if_neg hq,Nat.add_zero]

@[simp] theorem selectedBefore_zero {s n : ℕ} (I : Fin s → Fin n) :
    selectedBefore I 0=0 := by simp [selectedBefore]

@[simp] theorem selectedAt_zero {s n : ℕ} (I : Fin s → Fin n) :
    selectedAt I 0=0 := by simp [selectedAt]

/-- The final fixed up-step adds no selected position. -/
theorem selectedBefore_all {s n : ℕ} (I : Fin s → Fin n) :
    selectedBefore I (n+1)=s := by
  have h : ∀ i,(I i).val+1<n+1 := fun i => by have := (I i).isLt; omega
  simp [selectedBefore,h]

theorem selectedBefore_eq_card_of_ge {s n : ℕ} (I : Fin s → Fin n) (q : ℕ)
    (hq : n+1≤q) : selectedBefore I q=s := by
  have h : ∀ i,(I i).val+1<q := fun i => by have := (I i).isLt; omega
  simp [selectedBefore,h]

/-- Exact equivalence between the printed good-index bounds and all binary
prefix heights in the strip.  It holds in every parameter range. -/
theorem good_bounds_iff_prefix_strip (k s : ℕ) (I : Fin s → Fin (2*k+1))
    (hI : StrictMono I) :
    (∀ i,2*i.val≤(I i).val ∧ (I i).val+2*s≤2*k+2+2*i.val) ↔
    (∀ q,q≤2*k+3 → 2*selectedBefore I q≤q ∧
      q+2*s≤2*k+3+2*selectedBefore I q) := by
  constructor
  · intro h q hq
    have hc := selectedBefore_le I q
    constructor
    · by_cases hz : selectedBefore I q=0
      · omega
      · let i : Fin s := ⟨selectedBefore I q-1,by omega⟩
        have hi : i.val<selectedBefore I q := by dsimp [i]; omega
        have hpos := (lt_selectedBefore_iff hI q i).mp hi
        have hb := (h i).1
        dsimp only [i] at hb hpos
        omega
    · by_cases he : selectedBefore I q=s
      · omega
      · let i : Fin s := ⟨selectedBefore I q,by omega⟩
        have hi : ¬ i.val<selectedBefore I q := by dsimp [i]; omega
        have hpos := mt (lt_selectedBefore_iff hI q i).mpr hi
        have hb := (h i).2
        dsimp only [i] at hb hpos
        omega
  · intro h i
    have hlt := (I i).isLt
    have hlo := (h ((I i).val+2) (by omega)).1
    have hhi := (h ((I i).val+1) (by omega)).2
    rw [selectedBefore_after hI i] at hlo
    rw [selectedBefore_at hI i] at hhi
    constructor <;> omega

/-- The actual finite selected set of an increasing exterior word. -/
def selectedSet {s n : ℕ} (I : Fin s → Fin n) : Finset (Fin n) :=
  Finset.univ.image I

theorem selectedSet_card {s n : ℕ} {I : Fin s → Fin n} (hI : StrictMono I) :
    (selectedSet I).card=s := by
  rw [selectedSet,Finset.card_image_of_injective _ hI.injective,Finset.card_univ,
    Fintype.card_fin]

/-- Sorted lists and subsets of the same cardinality are genuinely equivalent. -/
def increasingSelectionEquiv (s n : ℕ) :
    {I : Fin s → Fin n // StrictMono I} ≃ {S : Finset (Fin n) // S.card=s} where
  toFun I := ⟨selectedSet I.val,selectedSet_card I.property⟩
  invFun S := ⟨S.val.orderEmbOfFin S.property,(S.val.orderEmbOfFin S.property).strictMono⟩
  left_inv I := by
    apply Subtype.ext
    exact (Finset.orderEmbOfFin_unique (selectedSet_card I.property)
      (fun i => Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩) I.property).symm
  right_inv S := by
    apply Subtype.ext
    exact Finset.image_orderEmbOfFin_univ S.val S.property

/-- Prefix counts agree with the literal selected set, so the preceding
strip characterization is a statement about the actual binary word. -/
theorem selectedBefore_eq_filter_card {s n : ℕ} {I : Fin s → Fin n}
    (hI : StrictMono I) (q : ℕ) :
    selectedBefore I q=((selectedSet I).filter fun x => x.val+1<q).card := by
  rw [selectedSet,Finset.filter_image]
  exact (Finset.card_image_of_injective _ hI.injective).symm

end PaperVerification.AlternatingForms.GoodPaths
