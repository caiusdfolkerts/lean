module

public import PaperVerification.AlternatingFormsWalkWords
public import PaperVerification.AlternatingFormsGoodPathBounds

/-!
# Literal states and binary occupations of a colored walk

The states are read from the actual recursive walk, and their transitions
are its stored edge proofs.  Splitting each color into its two occupation
bits recovers the binary path, with its first position unselected.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.AlternatingForms.BigradedTransfer

/-- All actual visited vertices, including both endpoints. -/
def walkStates (h : ℕ) : {n : ℕ} → {i j : Fin (h+1)} →
    ColoredWalk h n i j → Fin (n+1) → Fin (h+1)
  | 0,i,_,_ => fun _ => i
  | n+1,i,_,p => Fin.cons i (walkStates h p.2.2)

@[simp] theorem walkStates_zero (h n : ℕ) (i j : Fin (h+1))
    (p : ColoredWalk h n i j) : walkStates h p 0=i := by
  cases n <;> rfl

@[simp] theorem walkStates_last (h n : ℕ) (i j : Fin (h+1))
    (p : ColoredWalk h n i j) : walkStates h p (Fin.last n)=j := by
  induction n generalizing i with
  | zero => exact p.down
  | succ n ih =>
      obtain ⟨q,e,p⟩ := p
      change walkStates h p (Fin.last n)=j
      exact ih q p

theorem walkStates_step (h n : ℕ) (i j : Fin (h+1))
    (p : ColoredWalk h n i j) (r : Fin n) :
    stepAllowed (walkStates h p r.castSucc) (walkStates h p r.succ) (walkMarks h p r) := by
  induction n generalizing i with
  | zero => exact Fin.elim0 r
  | succ n ih =>
      obtain ⟨q,e,p⟩ := p
      refine Fin.cases ?_ (fun r => ?_) r
      · simpa only [walkStates,walkMarks,Fin.castSucc_zero,Fin.cons_zero,Fin.cons_succ,walkStates_zero]
          using e.property
      · simpa only [walkStates,walkMarks,Fin.cons_succ,Fin.castSucc_succ]
          using ih q p r

/-- Unpair a color word into its literal first/second occupation bits. -/
def binaryOccupation {n : ℕ} (m : Fin n → PairMark) (q : Fin (2*n)) : ℕ :=
  if q.val%2=0 then markADegree (m ⟨q.val/2,by have := q.isLt; omega⟩)
  else markBDegree (m ⟨q.val/2,by have := q.isLt; omega⟩)

theorem binaryOccupation_le_one {n : ℕ} (m : Fin n → PairMark) (q : Fin (2*n)) :
    binaryOccupation m q≤1 := by
  unfold binaryOccupation
  split_ifs
  · exact markADegree_le_one _
  · exact markBDegree_le_one _

theorem binaryOccupation_even {n : ℕ} (m : Fin n → PairMark) (r : Fin n) :
    binaryOccupation m ⟨2*r.val,by have := r.isLt; omega⟩=markADegree (m r) := by
  have hm : (2*r.val)%2=0 := by omega
  have hd : (⟨(2*r.val)/2,by have := r.isLt; omega⟩ : Fin n)=r := by
    apply Fin.ext
    change (2*r.val)/2=r.val
    omega
  simp only [binaryOccupation,hm,if_true,hd]

theorem binaryOccupation_odd {n : ℕ} (m : Fin n → PairMark) (r : Fin n) :
    binaryOccupation m ⟨2*r.val+1,by have := r.isLt; omega⟩=markBDegree (m r) := by
  have hm : (2*r.val+1)%2≠0 := by omega
  have hd : (⟨(2*r.val+1)/2,by have := r.isLt; omega⟩ : Fin n)=r := by
    apply Fin.ext
    change (2*r.val+1)/2=r.val
    omega
  simp only [binaryOccupation,hm,if_false,hd]

theorem walk_first_occupation_zero (h n : ℕ) (j : Fin (h+1))
    (p : ColoredWalk h (n+1) 0 j) :
    markADegree (walkMarks h p 0)=0 := by
  have he := (stepAllowed_iff_degree_balance _ _ _).mp (walkStates_step h (n+1) 0 j p 0)
  have h0 := walkStates_zero h (n+1) 0 j p
  change walkStates h p (0 : Fin (n+2))=0 at h0
  have ha : markADegree (walkMarks h p 0)≤0 := by simpa only [Fin.castSucc_zero,h0,Fin.val_zero] using he.2
  omega

/-- A selected-list prefix count with the same two literal bits satisfies
exactly the actual state conservation law at every paired position. -/
theorem prefix_count_state_balance {h n t l : ℕ}
    (p : ColoredWalk h n 0 (Fin.last h)) (I : Fin t → Fin l) (hI : StrictMono I)
    (ha : ∀ r : Fin n,GoodPaths.selectedAt I (2*r.val)=markADegree (walkMarks h p r))
    (hb : ∀ r : Fin n,GoodPaths.selectedAt I (2*r.val+1)=markBDegree (walkMarks h p r)) :
    ∀ r : Fin (n+1),GoodPaths.selectedBefore I (2*r.val)+(walkStates h p r).val=r.val := by
  intro r
  induction r using Fin.induction with
  | zero => simp only [Fin.val_zero,Nat.mul_zero,GoodPaths.selectedBefore_zero,
      walkStates_zero,Nat.add_zero]
  | succ r ih =>
      have hc0 := GoodPaths.selectedBefore_succ hI (2*r.val)
      have hc1 := GoodPaths.selectedBefore_succ hI (2*r.val+1)
      change GoodPaths.selectedBefore I (2*r.val+2)=
        GoodPaths.selectedBefore I (2*r.val+1)+GoodPaths.selectedAt I (2*r.val+1) at hc1
      have hs := ((stepAllowed_iff_degree_balance _ _ _).mp
        (walkStates_step h n 0 (Fin.last h) p r)).1
      rw [ha r] at hc0
      rw [hb r] at hc1
      change GoodPaths.selectedBefore I (2*(r.val+1))+
        (walkStates h p r.succ).val=r.val+1
      change GoodPaths.selectedBefore I (2*r.val)+
        (walkStates h p r.castSucc).val=r.val at ih
      have hq : 2*(r.val+1)=2*r.val+2 := by omega
      rw [hq]
      omega

end PaperVerification.AlternatingForms.BigradedTransfer
