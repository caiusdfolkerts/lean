module

public import PaperVerification.AlternatingFormsBooleanGoodSubsets
public import PaperVerification.AlternatingFormsStripWalks
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations

/-!
# Good subsets are the actual walks in a strip

The forward map follows the height `r - 2 * number of previous down steps`.
The inverse records exactly the downward edges of the graph walk.  The
prefix balance identity proves the cardinality and both inequalities, so
this is an equivalence of the literal finite combinatorial objects.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.AlternatingForms.BooleanWalks

section GraphSequences

variable {V : Type*} {G : SimpleGraph V}

def graphWalkOfVertices : (n : ℕ) → (v : Fin (n + 1) → V) →
    (∀ i : Fin n, G.Adj (v i.castSucc) (v i.succ)) →
      G.Walk (v 0) (v (Fin.last n))
  | 0, v, _ => .nil
  | n + 1, v, hv =>
      .cons (hv 0) (graphWalkOfVertices n (fun i => v i.succ)
        (fun i => by simpa only [Fin.castSucc_succ] using hv i.succ))

@[simp] theorem graphWalkOfVertices_length (n : ℕ) (v : Fin (n + 1) → V)
    (hv : ∀ i : Fin n, G.Adj (v i.castSucc) (v i.succ)) :
    (graphWalkOfVertices n v hv).length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (graphWalkOfVertices n (fun i => v i.succ) _).length + 1 = n + 1
      rw [ih]

theorem graphWalkOfVertices_getVert (n : ℕ) (v : Fin (n + 1) → V)
    (hv : ∀ i : Fin n, G.Adj (v i.castSucc) (v i.succ)) (i : Fin (n + 1)) :
    (graphWalkOfVertices n v hv).getVert i.val = v i := by
  induction n with
  | zero =>
      have hi : i = 0 := by apply Fin.ext; have := i.isLt; omega
      subst i
      rfl
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · exact SimpleGraph.Walk.getVert_zero _
      · change (graphWalkOfVertices n (fun r => v r.succ) _).getVert j.val = v j.succ
        exact ih _ _ j

end GraphSequences

abbrev StripWalk (w n : ℕ) :=
  {p : (SimpleGraph.pathGraph (w + 1)).Walk 0 (Fin.last w) // p.length = n}

def goodGraphVertex {m q : ℕ} (S : GoodSubset m q) (i : Fin (m + 1)) :
    Fin (m - 2 * q + 1) :=
  ⟨height S i.val, Nat.lt_succ_of_le (height_bound S i.val (Nat.le_of_lt_succ i.isLt))⟩

theorem goodGraphVertex_zero {m q : ℕ} (S : GoodSubset m q) :
    goodGraphVertex S 0 = 0 := Fin.ext (height_zero S)

theorem goodGraphVertex_last {m q : ℕ} (S : GoodSubset m q) :
    goodGraphVertex S (Fin.last m) = Fin.last (m - 2 * q) := Fin.ext (height_final S)

theorem goodGraphVertex_adj {m q : ℕ} (S : GoodSubset m q) (i : Fin m) :
    (SimpleGraph.pathGraph (m - 2 * q + 1)).Adj
      (goodGraphVertex S i.castSucc) (goodGraphVertex S i.succ) := by
  rw [SimpleGraph.pathGraph_adj]
  rcases height_step S i.val i.isLt with h | h
  · exact Or.inl h.symm
  · exact Or.inr h.symm

def goodSubsetToGraphWalk {m q : ℕ} (S : GoodSubset m q) : StripWalk (m - 2 * q) m :=
  ⟨(graphWalkOfVertices m (goodGraphVertex S) (goodGraphVertex_adj S)).copy
      (goodGraphVertex_zero S) (goodGraphVertex_last S), by simp⟩

theorem goodSubsetToGraphWalk_getVert {m q : ℕ} (S : GoodSubset m q)
    (r : ℕ) (hr : r ≤ m) :
    ((goodSubsetToGraphWalk S).val.getVert r).val = height S r := by
  change (((graphWalkOfVertices m (goodGraphVertex S) _).copy _ _).getVert r).val = _
  rw [SimpleGraph.Walk.getVert_copy]
  exact congrArg Fin.val (graphWalkOfVertices_getVert m (goodGraphVertex S) _
    ⟨r, Nat.lt_succ_of_le hr⟩)

def graphDownSet {m w : ℕ} (p : StripWalk w m) : Finset (Fin m) :=
  Finset.univ.filter fun i =>
    (p.val.getVert (i.val + 1)).val + 1 = (p.val.getVert i.val).val

@[simp] theorem mem_graphDownSet {m w : ℕ} (p : StripWalk w m) (i : Fin m) :
    i ∈ graphDownSet p ↔
      (p.val.getVert (i.val + 1)).val + 1 = (p.val.getVert i.val).val := by
  simp only [graphDownSet, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Each actual downward edge increases the down count by one; an upward
edge does not.  This is the complete endpoint conservation law. -/
theorem graphDownSet_balance {m w : ℕ} (p : StripWalk w m) (r : ℕ) (hr : r ≤ m) :
    (p.val.getVert r).val + 2 * prefixCount (graphDownSet p) r = r := by
  induction r with
  | zero => simp only [SimpleGraph.Walk.getVert_zero, Fin.val_zero, prefixCount_zero,
      Nat.mul_zero, Nat.add_zero]
  | succ r ih =>
      have hprev := ih (by omega)
      have hadj := p.val.adj_getVert_succ (show r < p.val.length by rw [p.property]; omega)
      rw [SimpleGraph.pathGraph_adj] at hadj
      have hsucc := prefixCount_succ (graphDownSet p) r
      have hrlt : r < m := by omega
      rw [selectedAt_position (graphDownSet p) ⟨r, hrlt⟩] at hsucc
      by_cases hd : (p.val.getVert (r + 1)).val + 1 = (p.val.getVert r).val
      · have hm : (⟨r, hrlt⟩ : Fin m) ∈ graphDownSet p := (mem_graphDownSet _ _).mpr hd
        rw [if_pos hm] at hsucc
        omega
      · have hm : (⟨r, hrlt⟩ : Fin m) ∉ graphDownSet p := by
          simpa only [mem_graphDownSet] using hd
        rw [if_neg hm] at hsucc
        omega

theorem graphDownSet_card {m q : ℕ} (hq : 2 * q ≤ m) (p : StripWalk (m - 2 * q) m) :
    (graphDownSet p).card = q := by
  have hb := graphDownSet_balance p m le_rfl
  rw [prefixCount_all _ _ le_rfl] at hb
  have he : p.val.getVert m = Fin.last (m - 2 * q) := by
    simpa only [p.property] using p.val.getVert_length
  rw [he] at hb
  simp only [Fin.val_last] at hb
  omega

theorem graphDownSet_good {m q : ℕ} (hq : 2 * q ≤ m)
    (p : StripWalk (m - 2 * q) m) :
    Good (⟨graphDownSet p, graphDownSet_card hq p⟩ : FixedSubsets (Fin m) q) := by
  intro r hr
  have hb := graphDownSet_balance p r hr
  have hv := (p.val.getVert r).isLt
  change 2 * prefixCount (graphDownSet p) r ≤ r ∧
    r + 2 * q ≤ m + 2 * prefixCount (graphDownSet p) r
  constructor <;> omega

def graphWalkToGoodSubset {m q : ℕ} (hq : 2 * q ≤ m)
    (p : StripWalk (m - 2 * q) m) : GoodSubset m q :=
  ⟨⟨graphDownSet p, graphDownSet_card hq p⟩, graphDownSet_good hq p⟩

@[simp] theorem graphDownSet_goodSubsetToGraphWalk {m q : ℕ} (S : GoodSubset m q) :
    graphDownSet (goodSubsetToGraphWalk S) = S.val.val := by
  ext i
  rw [mem_graphDownSet, goodSubsetToGraphWalk_getVert _ _ (by omega),
    goodSubsetToGraphWalk_getVert _ _ (by omega), height_downward_iff]

theorem graphWalkToGoodSubset_left_inv {m q : ℕ} (hq : 2 * q ≤ m) (S : GoodSubset m q) :
    graphWalkToGoodSubset hq (goodSubsetToGraphWalk S) = S := by
  apply Subtype.ext
  apply Subtype.ext
  exact graphDownSet_goodSubsetToGraphWalk S

theorem graphWalkToGoodSubset_right_inv {m q : ℕ} (hq : 2 * q ≤ m)
    (p : StripWalk (m - 2 * q) m) :
    goodSubsetToGraphWalk (graphWalkToGoodSubset hq p) = p := by
  apply Subtype.ext
  apply SimpleGraph.Walk.ext_getVert_le_length
  · exact (goodSubsetToGraphWalk _).property.trans p.property.symm
  · intro r hr
    rw [(goodSubsetToGraphWalk _).property] at hr
    apply Fin.ext
    rw [goodSubsetToGraphWalk_getVert _ _ hr]
    have hb := graphDownSet_balance p r hr
    change r - 2 * prefixCount (graphDownSet p) r = (p.val.getVert r).val
    omega

def goodSubsetGraphWalkEquiv (m q : ℕ) (hq : 2 * q ≤ m) :
    GoodSubset m q ≃ StripWalk (m - 2 * q) m where
  toFun := goodSubsetToGraphWalk
  invFun := graphWalkToGoodSubset hq
  left_inv := graphWalkToGoodSubset_left_inv hq
  right_inv := graphWalkToGoodSubset_right_inv hq

theorem card_goodSubset_eq_walkCount (m q : ℕ) (hq : 2 * q ≤ m) :
    Fintype.card (GoodSubset m q) = StripWalks.walkCount (m - 2 * q) m :=
  Fintype.card_congr (goodSubsetGraphWalkEquiv m q hq)

end PaperVerification.AlternatingForms.BooleanWalks
