module

public import PaperVerification.AlternatingFormsTransferDefinitions
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The actual four-colored bounded walks in Proposition 5.1

A walk records every intermediate height and every selected color.  Its
weight is the product of the literal edge weights.  Thus a positive-height
loop has two distinct choices, of weights `u` and `v`, whereas a loop at zero
has only the `v` choice.  The matrix-power formula below is proved by finite
summation over these actual walks.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace PaperVerification.AlternatingForms.BigradedTransfer

/-- The four pairs of binary steps: `UU`, `UD`, `DU`, and `DD`. -/
inductive PairMark
  | up | bLoop | aLoop | down
  deriving DecidableEq

instance pairMark_fintype : Fintype PairMark where
  elems := {.up,.bLoop,.aLoop,.down}
  complete m := by cases m <;> simp

theorem sum_pairMark {R : Type*} [AddCommMonoid R] (f : PairMark → R) :
    (∑ m,f m)=f .up+f .bLoop+f .aLoop+f .down := by
  change (∑ m∈({.up,.bLoop,.aLoop,.down} : Finset PairMark),f m)=_
  simp [add_assoc]

/-- A legal paired step in the actual closed height strip. -/
def stepAllowed {h : ℕ} (i j : Fin (h+1)) : PairMark → Prop
  | .up => i.val+1=j.val
  | .bLoop => i=j
  | .aLoop => i=j ∧ 0 < i.val
  | .down => j.val+1=i.val

instance stepAllowed_decidable {h : ℕ} (i j : Fin (h+1)) (m : PairMark) :
    Decidable (stepAllowed i j m) := by cases m <;> unfold stepAllowed <;> infer_instance

/-- The distinct colored edges, including their literal transition proof. -/
def ColoredEdge {h : ℕ} (i j : Fin (h+1)) := {m : PairMark // stepAllowed i j m}

instance coloredEdge_fintype {h : ℕ} (i j : Fin (h+1)) : Fintype (ColoredEdge i j) :=
  inferInstanceAs (Fintype {m : PairMark // stepAllowed i j m})

def markWeight {R : Type*} [MulOneClass R] (u v : R) : PairMark → R
  | .up => 1
  | .bLoop => v
  | .aLoop => u
  | .down => u*v

/-- Summing the actual colors gives exactly the printed transfer entry. -/
theorem coloredEdge_weight_sum {R : Type*} [CommRing R] (h : ℕ) (u v : R)
    (i j : Fin (h+1)) :
    (∑ e : ColoredEdge i j,markWeight u v e.val)=transferMatrix h u v i j := by
  have hs : (∑ e : ColoredEdge i j,markWeight u v e.val)=
      ∑ m : PairMark,if stepAllowed i j m then markWeight u v m else 0 := by
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype (Finset.univ.filter (stepAllowed i j))
      (by simp) (markWeight u v)).symm
  rw [hs,sum_pairMark]
  simp only [stepAllowed,markWeight,transferMatrix]
  by_cases hij : i=j
  · subst j
    by_cases hi : i.val=0
    · simp [hi]
    · have hip : 0 < i.val := Nat.pos_of_ne_zero hi
      simp [hi,hip,add_comm,add_left_comm,add_assoc]
  · simp [hij,add_comm,add_left_comm,add_assoc]

/-- An actual colored walk with its exact initial and final vertices.
The sigma type records the first target and the remaining walk. -/
def ColoredWalk (h : ℕ) : ℕ → Fin (h+1) → Fin (h+1) → Type
  | 0,i,j => PLift (i=j)
  | n+1,i,j => (q : Fin (h+1)) × (ColoredEdge i q × ColoredWalk h n q j)

instance coloredWalk_fintype (h : ℕ) :
    (n : ℕ) → (i j : Fin (h+1)) → Fintype (ColoredWalk h n i j)
  | 0,i,j => inferInstanceAs (Fintype (PLift (i=j)))
  | n+1,i,j => by
      letI : ∀ q : Fin (h+1),Fintype (ColoredWalk h n q j) :=
        fun q => coloredWalk_fintype h n q j
      exact inferInstanceAs
        (Fintype ((q : Fin (h+1)) × (ColoredEdge i q × ColoredWalk h n q j)))

/-- The product of all literal edge weights, with the empty product one. -/
def walkWeight {R : Type*} [MulOneClass R] (h : ℕ) (u v : R) :
    {n : ℕ} → {i j : Fin (h+1)} → ColoredWalk h n i j → R
  | 0,_,_,_ => 1
  | n+1,_,_,p => markWeight u v p.2.1.val * walkWeight h u v p.2.2

/-- Weighted path enumeration is the actual matrix power, over every
commutative coefficient ring and for all heights and lengths. -/
theorem coloredWalk_weight_sum {R : Type*} [CommRing R] (h N : ℕ) (u v : R)
    (i j : Fin (h+1)) :
    (∑ p : ColoredWalk h N i j,walkWeight h u v p)=
      (transferMatrix h u v ^ N) i j := by
  induction N generalizing i j with
  | zero =>
      change (∑ _ : PLift (i=j),(1 : R))=(1 : Matrix (Fin (h+1)) (Fin (h+1)) R) i j
      by_cases hij : i=j
      · subst j
        letI : Unique (PLift (i=i)) :=
          { default := ⟨rfl⟩, uniq := fun _ => Subsingleton.elim _ _ }
        simp [Matrix.one_apply]
      · letI : IsEmpty (PLift (i=j)) := ⟨fun p => hij p.down⟩
        simp [Matrix.one_apply,hij]
  | succ N ih =>
      change (∑ p : (q : Fin (h+1)) ×
        (ColoredEdge i q × ColoredWalk h N q j),
        markWeight u v p.2.1.val * walkWeight h u v p.2.2)=_
      rw [Fintype.sum_sigma]
      simp only [Fintype.sum_prod_type,← Finset.mul_sum,← Finset.sum_mul,ih,
        coloredEdge_weight_sum]
      rw [pow_succ',Matrix.mul_apply]

/-- Numbers of selected `a` and `b` letters in one paired step. -/
def markADegree : PairMark → ℕ
  | .up => 0
  | .bLoop => 0
  | .aLoop => 1
  | .down => 1

def markBDegree : PairMark → ℕ
  | .up => 0
  | .bLoop => 1
  | .aLoop => 0
  | .down => 1

theorem markADegree_le_one (m : PairMark) : markADegree m≤1 := by
  cases m <;> decide

theorem markBDegree_le_one (m : PairMark) : markBDegree m≤1 := by
  cases m <;> decide

/-- This numerical criterion includes the missing `a` loop at zero. -/
theorem stepAllowed_iff_degree_balance {h : ℕ} (i j : Fin (h+1)) (m : PairMark) :
    stepAllowed i j m ↔
      j.val+markADegree m+markBDegree m=i.val+1 ∧ markADegree m ≤ i.val := by
  cases m <;> simp only [stepAllowed,markADegree,markBDegree,Fin.ext_iff] <;> omega

def walkADegree (h : ℕ) : {n : ℕ} → {i j : Fin (h+1)} → ColoredWalk h n i j → ℕ
  | 0,_,_,_ => 0
  | n+1,_,_,p => markADegree p.2.1.val+walkADegree h p.2.2

def walkBDegree (h : ℕ) : {n : ℕ} → {i j : Fin (h+1)} → ColoredWalk h n i j → ℕ
  | 0,_,_,_ => 0
  | n+1,_,_,p => markBDegree p.2.1.val+walkBDegree h p.2.2

/-- The endpoint determines the total number of selected original letters. -/
theorem walk_degree_balance (h n : ℕ) (i j : Fin (h+1))
    (p : ColoredWalk h n i j) :
    walkADegree h p+walkBDegree h p+j.val=i.val+n := by
  induction n generalizing i with
  | zero =>
      change 0+0+j.val=i.val+0
      have he : i=j := p.down
      omega
  | succ n ih =>
      obtain ⟨q,e,p⟩ := p
      have he := ((stepAllowed_iff_degree_balance i q e.val).mp e.property).1
      have ht := ih q p
      change (markADegree e.val+walkADegree h p)+
        (markBDegree e.val+walkBDegree h p)+j.val=i.val+(n+1)
      omega

/-- The literal product weight agrees with the two actual color counts. -/
theorem walkWeight_eq_degrees {R : Type*} [CommRing R] (h n : ℕ) (u v : R)
    (i j : Fin (h+1)) (p : ColoredWalk h n i j) :
    walkWeight h u v p=u^walkADegree h p*v^walkBDegree h p := by
  induction n generalizing i with
  | zero => simp only [walkWeight,walkADegree,walkBDegree,pow_zero,mul_one]
  | succ n ih =>
      obtain ⟨q,e,p⟩ := p
      change markWeight u v e.val*walkWeight h u v p=
        u^(markADegree e.val+walkADegree h p)*v^(markBDegree e.val+walkBDegree h p)
      rw [ih q p,pow_add,pow_add]
      cases e.val <;> simp [markWeight,markADegree,markBDegree,mul_assoc,mul_left_comm,mul_comm]

end PaperVerification.AlternatingForms.BigradedTransfer
