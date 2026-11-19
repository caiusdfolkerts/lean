module

public import PaperVerification.AlternatingFormsGoodWalkMap
public import PaperVerification.AlternatingFormsWalkStates

/-!
# The full good-selection and colored-walk bijection

The inverse selects precisely the original positions whose corresponding
binary occupation bit is one.  Its cardinality is proved from the actual
walk's endpoint conservation law.  Every prefix satisfies the two strip
bounds, so sorting this actual selected set produces a good exterior index.
Neither the desired dimension nor a path-count formula is an assumption.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.AlternatingForms.GoodPaths

open BigradedTransfer

/-- Recover the original positions, omitting only the fixed initial up-step. -/
def walkSelection {k h : ℕ}
    (p : ColoredWalk h (k+1) 0 (Fin.last h)) : Finset (Fin (2*k+1)) :=
  Finset.univ.filter fun x => binaryOccupation (walkMarks h p)
    ⟨x.val+1,by have := x.isLt; omega⟩=1

/-- Any increasing enumeration of the recovered set has exactly the actual
binary bits, including the fixed zero at position zero. -/
theorem selectedAt_walkSelection {k h t : ℕ}
    (p : ColoredWalk h (k+1) 0 (Fin.last h)) (I : Fin t → Fin (2*k+1))
    (hS : selectedSet I=walkSelection p) (q : Fin (2*(k+1))) :
    selectedAt I q.val=binaryOccupation (walkMarks h p) q := by
  by_cases hq : q.val=0
  · have he : q=(⟨2*(0 : Fin (k+1)).val,by omega⟩ : Fin (2*(k+1))) :=
      Fin.ext hq
    rw [he,binaryOccupation_even,walk_first_occupation_zero]
    exact selectedAt_zero I
  · let x : Fin (2*k+1) := ⟨q.val-1,by have := q.isLt; omega⟩
    have hx : x.val+1=q.val := by dsimp [x]; omega
    have hq' : (⟨x.val+1,by have := x.isLt; omega⟩ : Fin (2*(k+1)))=q := Fin.ext hx
    have he : selectedAt I q.val=1 ↔ binaryOccupation (walkMarks h p) q=1 := by
      rw [←hx,←mem_selectedSet_iff_selectedAt,hS]
      simp only [walkSelection,Finset.mem_filter,Finset.mem_univ,true_and,hq']
    have h0 := selectedAt_le_one I q.val
    have h1 := binaryOccupation_le_one (walkMarks h p) q
    omega

theorem selectedAt_walkSelection_a {k h t : ℕ}
    (p : ColoredWalk h (k+1) 0 (Fin.last h)) (I : Fin t → Fin (2*k+1))
    (hS : selectedSet I=walkSelection p) (r : Fin (k+1)) :
    selectedAt I (2*r.val)=markADegree (walkMarks h p r) := by
  simpa only [binaryOccupation_even] using
    selectedAt_walkSelection p I hS ⟨2*r.val,by have := r.isLt; omega⟩

theorem selectedAt_walkSelection_b {k h t : ℕ}
    (p : ColoredWalk h (k+1) 0 (Fin.last h)) (I : Fin t → Fin (2*k+1))
    (hS : selectedSet I=walkSelection p) (r : Fin (k+1)) :
    selectedAt I (2*r.val+1)=markBDegree (walkMarks h p r) := by
  simpa only [binaryOccupation_odd] using
    selectedAt_walkSelection p I hS ⟨2*r.val+1,by have := r.isLt; omega⟩

/-- The recovered set has the exact required exterior degree. -/
theorem walkSelection_card {k s : ℕ} (hs : s≤k+1)
    (p : ColoredWalk (k+1-s) (k+1) 0 (Fin.last (k+1-s))) :
    (walkSelection p).card=s := by
  let S := walkSelection p
  let I : Fin S.card → Fin (2*k+1) := S.orderEmbOfFin rfl
  have hI : StrictMono I := (S.orderEmbOfFin rfl).strictMono
  have hS : selectedSet I=walkSelection p := Finset.image_orderEmbOfFin_univ S rfl
  have he := prefix_count_state_balance p I hI
    (selectedAt_walkSelection_a p I hS) (selectedAt_walkSelection_b p I hS)
    (Fin.last (k+1))
  rw [walkStates_last] at he
  change selectedBefore I (2*(k+1))+(k+1-s)=k+1 at he
  have hq : 2*(k+1)=(2*k+1)+1 := by omega
  rw [hq,selectedBefore_all] at he
  dsimp [S] at he
  omega

/-- The recovered sorted word satisfies both walls of the original strip. -/
theorem walkSelection_good_bounds {k s : ℕ} (hs : s≤k+1)
    (p : ColoredWalk (k+1-s) (k+1) 0 (Fin.last (k+1-s)))
    (I : Fin s → Fin (2*k+1)) (hI : StrictMono I)
    (hS : selectedSet I=walkSelection p) :
    ∀ i,2*i.val≤(I i).val ∧ (I i).val+2*s≤2*k+2+2*i.val := by
  apply (good_bounds_iff_prefix_strip k s I hI).mpr
  intro q hq
  have hb := prefix_count_state_balance p I hI
    (selectedAt_walkSelection_a p I hS) (selectedAt_walkSelection_b p I hS)
  by_cases hend : 2*k+2≤q
  · rw [selectedBefore_eq_card_of_ge I q (by omega)]
    constructor <;> omega
  · let r : Fin (k+1) := ⟨q/2,by omega⟩
    have hbal := hb r.castSucc
    change selectedBefore I (2*r.val)+(walkStates (k+1-s) p r.castSucc).val=r.val at hbal
    have hheight := (walkStates (k+1-s) p r.castSucc).isLt
    by_cases heven : q%2=0
    · have he : q=2*r.val := by dsimp [r]; omega
      rw [he]
      constructor <;> omega
    · have he : q=2*r.val+1 := by dsimp [r]; omega
      have hinc := selectedBefore_succ hI (2*r.val)
      rw [selectedAt_walkSelection_a p I hS r] at hinc
      have ha := ((stepAllowed_iff_degree_balance _ _ _).mp
        (walkStates_step (k+1-s) (k+1) 0 (Fin.last (k+1-s)) p r)).2
      rw [he]
      constructor <;> omega

/-- Sort the recovered original selected set, using its proved exact size. -/
def walkToGoodIndex {k s : ℕ} (hs : s≤k+1)
    (p : ColoredWalk (k+1-s) (k+1) 0 (Fin.last (k+1-s))) : GoodPathIndex k s :=
  let S := walkSelection p
  let hS := walkSelection_card hs p
  let I := S.orderEmbOfFin hS
  ⟨⟨I,I.strictMono⟩,walkSelection_good_bounds hs p I I.strictMono
    (Finset.image_orderEmbOfFin_univ S hS)⟩

theorem walkToGoodIndex_selectedSet {k s : ℕ} (hs : s≤k+1)
    (p : ColoredWalk (k+1-s) (k+1) 0 (Fin.last (k+1-s))) :
    selectedSet (walkToGoodIndex hs p).val.val=walkSelection p :=
  Finset.image_orderEmbOfFin_univ (walkSelection p) (walkSelection_card hs p)

/-- The inverse construction recovers every actual walk and both loop colors. -/
theorem goodIndexToWalk_walkToGoodIndex {k s : ℕ} (hs : s≤k+1)
    (p : ColoredWalk (k+1-s) (k+1) 0 (Fin.last (k+1-s))) :
    goodIndexToWalk hs (walkToGoodIndex hs p)=p := by
  apply walkMarks_injective (k+1-s) (k+1) 0 (Fin.last (k+1-s))
  rw [goodIndexToWalk_marks]
  funext r
  apply pairMark_ext
  · rw [pairedMark_a]
    exact selectedAt_walkSelection_a p _ (walkToGoodIndex_selectedSet hs p) r
  · rw [pairedMark_b]
    exact selectedAt_walkSelection_b p _ (walkToGoodIndex_selectedSet hs p) r

/-- The complete, all-size good-index and actual weighted-walk equivalence. -/
def goodIndexWalkEquiv (k s : ℕ) (hs : s≤k+1) :
    GoodPathIndex k s ≃ ColoredWalk (k+1-s) (k+1) 0 (Fin.last (k+1-s)) where
  toFun := goodIndexToWalk hs
  invFun := walkToGoodIndex hs
  left_inv I := (goodIndexToWalk_injective hs) (goodIndexToWalk_walkToGoodIndex hs _)
  right_inv := goodIndexToWalk_walkToGoodIndex hs

end PaperVerification.AlternatingForms.GoodPaths
