module

public import PaperVerification.AlternatingFormsGoodPathBounds
public import PaperVerification.AlternatingFormsWalkWords

/-!
# Pairing the literal good-monomial binary path

The first paired position is the fixed up-step followed by `b_0`.
Every subsequent pair is `(a_i,b_i)`.  Heights are computed from the actual
prefix count and divided by two.  The good inequalities prove the strip
bounds and the absence of an `a` loop at height zero.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.AlternatingForms.GoodPaths

open BigradedTransfer

/-- The same sorted selections and inequalities as the exterior good basis,
kept here independent of its algebraic proof dependencies. -/
def GoodPathIndex (k s : ℕ) :=
  {I : {I : Fin s → Fin (2*k+1) // StrictMono I} //
    ∀ i,2*i.val≤(I.val i).val ∧ (I.val i).val+2*s≤2*k+2+2*i.val}

instance goodPathIndex_fintype (k s : ℕ) : Fintype (GoodPathIndex k s) := by
  unfold GoodPathIndex
  infer_instance

theorem index_prefix_bounds {k s : ℕ} (I : GoodPathIndex k s) (q : ℕ)
    (hq : q≤2*k+3) :
    2*selectedBefore I.val.val q≤q ∧
      q+2*s≤2*k+3+2*selectedBefore I.val.val q :=
  (good_bounds_iff_prefix_strip k s I.val.val I.val.property).mp I.property q hq

/-- The even-position height, after halving the actual binary height. -/
def pairedHeight {k s : ℕ} (hs : s≤k+1) (I : GoodPathIndex k s)
    (r : Fin (k+2)) : Fin (k+1-s+1) :=
  ⟨r.val-selectedBefore I.val.val (2*r.val),by
    have hb := index_prefix_bounds I (2*r.val) (by have := r.isLt; omega)
    have hr := r.isLt
    omega⟩

theorem pairedHeight_zero {k s : ℕ} (hs : s≤k+1) (I : GoodPathIndex k s) :
    pairedHeight hs I 0=0 := by
  apply Fin.ext
  simp [pairedHeight]

theorem pairedHeight_last {k s : ℕ} (hs : s≤k+1) (I : GoodPathIndex k s) :
    pairedHeight hs I (Fin.last (k+1))=Fin.last (k+1-s) := by
  apply Fin.ext
  change k+1-selectedBefore I.val.val (2*(k+1))=k+1-s
  have hq : 2*(k+1)=(2*k+1)+1 := by omega
  rw [hq,selectedBefore_all]

/-- The two literal selected-position bits determine the pair's color. -/
def pairedMark {k s : ℕ} (I : GoodPathIndex k s) (r : Fin (k+1)) : PairMark :=
  pairMarkOfDegrees (selectedAt I.val.val (2*r.val))
    (selectedAt I.val.val (2*r.val+1))

theorem pairedMark_a {k s : ℕ} (I : GoodPathIndex k s) (r : Fin (k+1)) :
    markADegree (pairedMark I r)=selectedAt I.val.val (2*r.val) :=
  markADegree_ofDegrees _ _ (selectedAt_le_one _ _) (selectedAt_le_one _ _)

theorem pairedMark_b {k s : ℕ} (I : GoodPathIndex k s) (r : Fin (k+1)) :
    markBDegree (pairedMark I r)=selectedAt I.val.val (2*r.val+1) :=
  markBDegree_ofDegrees _ _ (selectedAt_le_one _ _) (selectedAt_le_one _ _)

/-- Every paired step is legal in the exact finite strip, including the
asymmetric boundary loop at zero. -/
theorem paired_step_allowed {k s : ℕ} (hs : s≤k+1) (I : GoodPathIndex k s)
    (r : Fin (k+1)) :
    stepAllowed (pairedHeight hs I r.castSucc) (pairedHeight hs I r.succ) (pairedMark I r) := by
  rw [stepAllowed_iff_degree_balance,pairedMark_a,pairedMark_b]
  have hr := r.isLt
  have h0 := (index_prefix_bounds I (2*r.val) (by omega)).1
  have h1 := (index_prefix_bounds I (2*r.val+1) (by omega)).1
  have h2 := (index_prefix_bounds I (2*r.val+2) (by omega)).1
  have he0 := selectedBefore_succ I.val.property (2*r.val)
  have he1 := selectedBefore_succ I.val.property (2*r.val+1)
  change selectedBefore I.val.val (2*r.val+2)=
    selectedBefore I.val.val (2*r.val+1)+selectedAt I.val.val (2*r.val+1) at he1
  have hc0 : selectedBefore I.val.val (2*r.val) ≤ r.val := by omega
  have hc1 : selectedBefore I.val.val (2*r.val+1) ≤ r.val := by omega
  have hc2 : selectedBefore I.val.val (2*r.val+2) ≤ r.val+1 := by omega
  change ((r.val+1)-selectedBefore I.val.val (2*(r.val+1)))+
      selectedAt I.val.val (2*r.val)+selectedAt I.val.val (2*r.val+1)=
        (r.val-selectedBefore I.val.val (2*r.val))+1 ∧
      selectedAt I.val.val (2*r.val)≤r.val-selectedBefore I.val.val (2*r.val)
  have hq : 2*(r.val+1)=2*r.val+2 := by omega
  rw [hq]
  omega

/-- The actual paired walk associated with a good exterior word. -/
def goodIndexToWalk {k s : ℕ} (hs : s≤k+1) (I : GoodPathIndex k s) :
    ColoredWalk (k+1-s) (k+1) 0 (Fin.last (k+1-s)) :=
  reindexWalk (pairedHeight_zero hs I) (pairedHeight_last hs I)
    (walkOfSteps (k+1-s) (k+1) (pairedHeight hs I) (pairedMark I)
      (paired_step_allowed hs I))

@[simp] theorem goodIndexToWalk_marks {k s : ℕ} (hs : s≤k+1) (I : GoodPathIndex k s) :
    walkMarks (k+1-s) (goodIndexToWalk hs I)=pairedMark I := by
  simp only [goodIndexToWalk,reindexWalk_marks,walkOfSteps_marks]

/-- A selected-set membership statement is the literal binary down-step. -/
theorem mem_selectedSet_iff_selectedAt {s n : ℕ} (I : Fin s → Fin n) (x : Fin n) :
    x∈selectedSet I ↔ selectedAt I (x.val+1)=1 := by
  have he : (∃ i,(I i).val+1=x.val+1) ↔ ∃ i,I i=x := by
    constructor
    · rintro ⟨i,hi⟩
      exact ⟨i,Fin.ext (by omega)⟩
    · rintro ⟨i,rfl⟩
      exact ⟨i,rfl⟩
  have hm : x∈selectedSet I ↔ ∃ i,I i=x := by simp [selectedSet]
  rw [hm]
  unfold selectedAt
  by_cases hsel : ∃ i,I i=x
  · have hval := he.mpr hsel
    simp only [hsel,hval,if_true]
  · have hval : ¬∃ i,(I i).val+1=x.val+1 := fun h => hsel (he.mp h)
    simp only [hsel,hval,if_false,Nat.zero_ne_one]

/-- All original selected letters are recovered from the paired colors. -/
theorem pairedMark_injective (k s : ℕ) :
    Function.Injective (pairedMark (k := k) (s := s)) := by
  intro I J he
  have hbit : ∀ q,q≤2*k+1 → selectedAt I.val.val q=selectedAt J.val.val q := by
    intro q hq
    let r : Fin (k+1) := ⟨q/2,by omega⟩
    have hm := congrFun he r
    by_cases hp : q%2=0
    · have hq' : 2*r.val=q := by dsimp [r]; omega
      have ha := congrArg markADegree hm
      simpa only [pairedMark_a,hq'] using ha
    · have hq' : 2*r.val+1=q := by dsimp [r]; omega
      have hb := congrArg markBDegree hm
      simpa only [pairedMark_b,hq'] using hb
  have hS : selectedSet I.val.val=selectedSet J.val.val := by
    ext x
    rw [mem_selectedSet_iff_selectedAt,mem_selectedSet_iff_selectedAt,
      hbit (x.val+1) (by have := x.isLt; omega)]
  apply Subtype.ext
  apply (increasingSelectionEquiv s (2*k+1)).injective
  exact Subtype.ext hS

theorem goodIndexToWalk_injective {k s : ℕ} (hs : s≤k+1) :
    Function.Injective (goodIndexToWalk (k := k) hs) := by
  intro I J he
  apply pairedMark_injective k s
  simpa only [goodIndexToWalk_marks] using congrArg (walkMarks (k+1-s)) he

end PaperVerification.AlternatingForms.GoodPaths
