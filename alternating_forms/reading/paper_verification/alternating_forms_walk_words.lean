module

public import PaperVerification.AlternatingFormsWeightedWalks
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Recovering literal color words from bounded walks

A legal color and an initial height determine the next height uniquely.
Consequently the color word determines an actual bounded walk with fixed
endpoints.  The construction from a sequence of legal heights and colors is
explicit and preserves every color and both color degrees.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace PaperVerification.AlternatingForms.BigradedTransfer

def pairMarkOfDegrees (a b : ℕ) : PairMark :=
  if a=0 then (if b=0 then .up else .bLoop)
  else (if b=0 then .aLoop else .down)

theorem markADegree_ofDegrees (a b : ℕ) (ha : a≤1) (hb : b≤1) :
    markADegree (pairMarkOfDegrees a b)=a := by
  unfold pairMarkOfDegrees
  split_ifs <;> simp only [markADegree] <;> omega

theorem markBDegree_ofDegrees (a b : ℕ) (ha : a≤1) (hb : b≤1) :
    markBDegree (pairMarkOfDegrees a b)=b := by
  unfold pairMarkOfDegrees
  split_ifs <;> simp only [markBDegree] <;> omega

theorem pairMark_ext {a b : PairMark}
    (ha : markADegree a=markADegree b) (hb : markBDegree a=markBDegree b) : a=b := by
  cases a <;> cases b <;> simp_all [markADegree,markBDegree]

theorem step_target_unique {h : ℕ} {i j q : Fin (h+1)} {m : PairMark}
    (hj : stepAllowed i j m) (hq : stepAllowed i q m) : j=q := by
  have h1 := ((stepAllowed_iff_degree_balance i j m).mp hj).1
  have h2 := ((stepAllowed_iff_degree_balance i q m).mp hq).1
  apply Fin.ext
  omega

/-- The actual color chosen at every step of a bounded walk. -/
def walkMarks (h : ℕ) : {n : ℕ} → {i j : Fin (h+1)} →
    ColoredWalk h n i j → Fin n → PairMark
  | 0,_,_,_ => Fin.elim0
  | n+1,_,_,p => Fin.cons p.2.1.val (walkMarks h p.2.2)

/-- The initial height and the color word uniquely determine every vertex. -/
theorem walkMarks_injective (h n : ℕ) (i j : Fin (h+1)) :
    Function.Injective (walkMarks h (n := n) (i := i) (j := j)) := by
  induction n generalizing i with
  | zero =>
      intro p q hpq
      exact @Subsingleton.elim (PLift (i=j)) inferInstance p q
  | succ n ih =>
      rintro ⟨q,e,p⟩ ⟨q',e',p'⟩ he
      have hm : e.val=e'.val := by
        simpa only [walkMarks,Fin.cons_zero] using congrArg (fun f => f 0) he
      have hq : q=q' := step_target_unique e.property (hm.symm ▸ e'.property)
      subst q'
      have hee : e=e' := Subtype.ext hm
      subst e'
      have ht : walkMarks h p=walkMarks h p' := by
        funext r
        simpa only [walkMarks,Fin.cons_succ] using congrArg (fun f => f r.succ) he
      have hp : p=p' := ih q ht
      subst p'
      rfl

/-- Construct the actual walk by following a prescribed legal sequence. -/
def walkOfSteps (h : ℕ) : (n : ℕ) →
    (v : Fin (n+1) → Fin (h+1)) → (m : Fin n → PairMark) →
    (∀ r,stepAllowed (v r.castSucc) (v r.succ) (m r)) →
    ColoredWalk h n (v 0) (v (Fin.last n))
  | 0,v,m,hm => ⟨rfl⟩
  | n+1,v,m,hm =>
      ⟨v (0 : Fin (n+1)).succ,⟨m 0,hm 0⟩,
        walkOfSteps h n (fun r => v r.succ) (fun r => m r.succ)
          (fun r => by simpa only [Fin.castSucc_succ] using hm r.succ)⟩

@[simp] theorem walkOfSteps_marks (h n : ℕ)
    (v : Fin (n+1) → Fin (h+1)) (m : Fin n → PairMark)
    (hm : ∀ r,stepAllowed (v r.castSucc) (v r.succ) (m r)) :
    walkMarks h (walkOfSteps h n v m hm)=m := by
  induction n with
  | zero => funext r; exact Fin.elim0 r
  | succ n ih =>
      change Fin.cons (m 0)
        (walkMarks h (walkOfSteps h n (fun r => v r.succ) (fun r => m r.succ) _))=m
      rw [ih]
      exact Fin.cons_self_tail m

/-- Changing only proved-equal endpoint names changes no underlying colors. -/
def reindexWalk {h n : ℕ} {i j i' j' : Fin (h+1)}
    (hi : i=i') (hj : j=j') (p : ColoredWalk h n i j) : ColoredWalk h n i' j' := by
  subst i'
  subst j'
  exact p

@[simp] theorem reindexWalk_marks {h n : ℕ} {i j i' j' : Fin (h+1)}
    (hi : i=i') (hj : j=j') (p : ColoredWalk h n i j) :
    walkMarks h (reindexWalk hi hj p)=walkMarks h p := by
  subst i'
  subst j'
  rfl

theorem walkADegree_eq_sum_marks (h n : ℕ) (i j : Fin (h+1))
    (p : ColoredWalk h n i j) :
    walkADegree h p=∑ r,markADegree (walkMarks h p r) := by
  induction n generalizing i with
  | zero => simp only [walkADegree,Fin.sum_univ_zero]
  | succ n ih =>
      obtain ⟨q,e,p⟩ := p
      simp only [walkADegree,walkMarks,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,ih]

theorem walkBDegree_eq_sum_marks (h n : ℕ) (i j : Fin (h+1))
    (p : ColoredWalk h n i j) :
    walkBDegree h p=∑ r,markBDegree (walkMarks h p r) := by
  induction n generalizing i with
  | zero => simp only [walkBDegree,Fin.sum_univ_zero]
  | succ n ih =>
      obtain ⟨q,e,p⟩ := p
      simp only [walkBDegree,walkMarks,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,ih]

end PaperVerification.AlternatingForms.BigradedTransfer
