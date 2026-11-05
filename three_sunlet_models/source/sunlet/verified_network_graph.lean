module

public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.Dart
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Sum
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Tactic.Abel

/-! Exact ordinary proof stage 1 of 3.
All source bodies below are preserved from the canonical project.
Generation alone is not verification; require a successful stock Lean check. -/

@[expose] public section

#eval IO.println "NETWORK_STAGE_IMPORTS_COMPLETE VerifiedNetworkGraph"

section NetworkStageSource_Sunlet_NetworkGraphDecomposition


/-!
# The actual finite graphs underlying binary level-one networks

Cycles are indexed by the edge sets of genuine simple closed walks, so
rotations and reversal are counted only once. Cutting a bridge `u–v` uses
the two induced subgraphs on its components together with the opposite
endpoint. That endpoint is the new cut leaf. Consequently the two cut
graphs retain literal embeddings into the original graph and duplicate
exactly the cut edge.
-/

set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace Sunlet.NetworkGraphDecomposition

open SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

theorem list_toFinset_map {A B : Type*} [DecidableEq A] [DecidableEq B]
    (f : A → B) (l : List A) : (l.map f).toFinset = l.toFinset.image f := by
  ext x
  simp only [List.mem_toFinset, List.mem_map, Finset.mem_image]

def vertexDegree (v : V) : ℕ := Nat.card (G.neighborSet v)

def IsBinary : Prop := ∀ v, vertexDegree G v = 1 ∨ vertexDegree G v = 3

abbrev Leaf := {v : V // vertexDegree G v = 1}

def edgeCount : ℕ := Nat.card G.edgeSet
def leafCount : ℕ := Nat.card (Leaf G)

section Cycles

variable [DecidableEq V]

/-- A cycle is an actual simple closed walk, identified by its edge set. -/
abbrev Cycle := {S : Finset (Sym2 V) //
  ∃ v : V, ∃ p : G.Walk v v, p.IsCycle ∧ p.edges.toFinset = S}

instance cycleFinite [Finite V] : Finite (Cycle G) := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  infer_instance

def cycleVertices (c : Cycle G) : Finset V := c.val.biUnion Sym2.toFinset

def cycleCount : ℕ := Nat.card (Cycle G)
def triangleCount : ℕ := Nat.card {c : Cycle G // c.val.card = 3}

/-- This is precisely the paper's vertex-disjoint-cycle hypothesis,
independent of any asserted block decomposition. -/
def HasDisjointCycles : Prop :=
  ∀ c d : Cycle G, c ≠ d → Disjoint (cycleVertices G c) (cycleVertices G d)

structure IsBinaryCactus : Prop where
  connected : G.Connected
  binary : IsBinary G
  disjoint_cycles : HasDisjointCycles G

theorem cycle_card_ge_three (c : Cycle G) : 3 ≤ c.val.card := by
  obtain ⟨v, p, hp, he⟩ := c.property
  rw [← he, List.toFinset_card_of_nodup hp.isTrail.edges_nodup, p.length_edges]
  exact hp.three_le_length

theorem bridge_not_mem_cycle {e : Sym2 V} (he : G.IsBridge e) (c : Cycle G) :
    e ∉ c.val := by
  obtain ⟨v, p, hp, hs⟩ := c.property
  rw [← hs, List.mem_toFinset]
  exact he.notMem_edges_of_isCycle hp

theorem cycle_edges_subset (c : Cycle G) : (c.val : Set (Sym2 V)) ⊆ G.edgeSet := by
  obtain ⟨v, p, hp, he⟩ := c.property
  intro e hem
  exact p.edges_subset_edgeSet (List.mem_toFinset.mp (he.symm ▸ hem))

theorem cycleVertices_eq_support (c : Cycle G) {v : V} {p : G.Walk v v}
    (hp : p.IsCycle) (he : p.edges.toFinset = c.val) :
    cycleVertices G c = p.support.toFinset := by
  ext x
  simp only [cycleVertices, ← he, Finset.mem_biUnion, List.mem_toFinset,
    Sym2.mem_toFinset, SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hp.not_nil]

theorem cycleVertices_nonempty (c : Cycle G) : (cycleVertices G c).Nonempty := by
  obtain ⟨v, p, hp, he⟩ := c.property
  rw [cycleVertices_eq_support G c hp he]
  exact ⟨v, List.mem_toFinset.mpr p.start_mem_support⟩

theorem mem_cycleVertices_of_mem_edge (c : Cycle G) {e : Sym2 V} (he : e ∈ c.val)
    {x : V} (hx : x ∈ e) : x ∈ cycleVertices G c :=
  Finset.mem_biUnion.mpr ⟨e, he, Sym2.mem_toFinset.mpr hx⟩

end Cycles

section Cut

variable (u v : V)

def cutBase : SimpleGraph V := G.deleteEdges {s(u, v)}

def cutSide : Set V := {x | (cutBase G u v).Reachable u x}

def cutVertices : Set V := {x | x ∈ cutSide G u v ∨ x = v}

def cutGraph : SimpleGraph (cutVertices G u v) := G.induce (cutVertices G u v)

@[simp] theorem cutBase_swap : cutBase G v u = cutBase G u v := by
  simp only [cutBase, Sym2.eq_swap]

@[simp] theorem start_mem_cutSide : u ∈ cutSide G u v := SimpleGraph.Reachable.rfl

@[simp] theorem start_mem_cutVertices : u ∈ cutVertices G u v :=
  Or.inl (start_mem_cutSide G u v)

@[simp] theorem end_mem_cutVertices : v ∈ cutVertices G u v := Or.inr rfl

theorem end_not_mem_cutSide (hb : G.IsBridge s(u, v)) : v ∉ cutSide G u v :=
  (SimpleGraph.isBridge_iff.mp hb)

theorem cutSide_eq_component :
    cutSide G u v = ((cutBase G u v).connectedComponentMk u).supp := by
  ext x
  simp only [cutSide, Set.mem_setOf_eq, ConnectedComponent.mem_supp_iff,
    ConnectedComponent.eq, reachable_comm]

/-- Removing one edge from a connected graph leaves at most the two
components containing its endpoints. -/
theorem reachable_cut_either (hG : G.Connected) (x : V) :
    (cutBase G u v).Reachable u x ∨ (cutBase G u v).Reachable v x := by
  have step : ∀ a b, G.Adj a b →
      ((cutBase G u v).Reachable u a ∨ (cutBase G u v).Reachable v a) →
      ((cutBase G u v).Reachable u b ∨ (cutBase G u v).Reachable v b) := by
    intro a b hab hreach
    by_cases he : s(a, b) = s(u, v)
    · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr SimpleGraph.Reachable.rfl
      · exact Or.inl SimpleGraph.Reachable.rfl
    · have hadj : (cutBase G u v).Adj a b :=
        SimpleGraph.deleteEdges_adj.mpr ⟨hab, by simpa only [Set.mem_singleton_iff] using he⟩
      exact hreach.elim (fun h => Or.inl (h.trans hadj.reachable))
        (fun h => Or.inr (h.trans hadj.reachable))
  have hreach := (SimpleGraph.reachable_iff_reflTransGen u x).mp (hG.preconnected u x)
  induction hreach with
  | refl => exact Or.inl SimpleGraph.Reachable.rfl
  | tail _ hab ih => exact step _ _ hab ih

theorem other_side_iff_not_side (hG : G.Connected) (hb : G.IsBridge s(u, v)) (x : V) :
    (cutBase G u v).Reachable v x ↔ x ∉ cutSide G u v := by
  constructor
  · intro hvx hux
    exact (end_not_mem_cutSide G u v hb) (hux.trans hvx.symm)
  · intro hx
    exact (reachable_cut_either G u v hG x).resolve_left hx

/-- The deleted bridge is the only edge between the two components. -/
theorem crossing_edge (hb : G.IsBridge s(u, v)) {x y : V}
    (hx : x ∈ cutSide G u v) (hy : y ∉ cutSide G u v) (hxy : G.Adj x y) :
    x = u ∧ y = v := by
  have he : s(x, y) = s(u, v) := by
    by_contra he
    have hadj : (cutBase G u v).Adj x y :=
      SimpleGraph.deleteEdges_adj.mpr ⟨hxy, by simpa only [Set.mem_singleton_iff] using he⟩
    exact hy (hx.trans hadj.reachable)
  rcases Sym2.eq_iff.mp he with h | h
  · exact h
  · exact ((end_not_mem_cutSide G u v hb) (h.1 ▸ hx)).elim

theorem neighbors_mem_cutVertices (hb : G.IsBridge s(u, v)) {x : V}
    (hx : x ∈ cutSide G u v) : G.neighborSet x ⊆ cutVertices G u v := by
  intro y hxy
  by_cases hy : y ∈ cutSide G u v
  · exact Or.inl hy
  · exact Or.inr (crossing_edge G u v hb hx hy hxy).2

theorem boundary_neighbor_eq (hb : G.IsBridge s(u, v)) {x : V}
    (hx : x ∈ cutVertices G u v) (hadj : G.Adj v x) : x = u := by
  rcases hx with hx | rfl
  · exact (crossing_edge G u v hb hx (end_not_mem_cutSide G u v hb) hadj.symm).1
  · exact (G.irrefl hadj).elim

/-- The retained component together with the opposite endpoint is
connected; the opposite endpoint is joined by the original cut edge. -/
theorem cutGraph_connected (hadj : G.Adj u v) : (cutGraph G u v).Connected := by
  have hS : ((cutBase G u v).induce (cutSide G u v)).Connected := by
    rw [cutSide_eq_component]
    exact ((cutBase G u v).connectedComponentMk u).connected_toSimpleGraph
  let f : ((cutBase G u v).induce (cutSide G u v)) →g cutGraph G u v :=
    { toFun := fun x => ⟨x.val, Or.inl x.property⟩
      map_rel' := fun h => (SimpleGraph.deleteEdges_adj.mp h).1 }
  have hr : ∀ x : cutVertices G u v,
      (cutGraph G u v).Reachable ⟨u, start_mem_cutVertices G u v⟩ x := by
    rintro ⟨x, hx⟩
    rcases hx with hx | hx
    · exact (hS.preconnected ⟨u, start_mem_cutSide G u v⟩ ⟨x, hx⟩).map f
    · subst x
      exact (show (cutGraph G u v).Adj
        ⟨u, start_mem_cutVertices G u v⟩ ⟨v, end_mem_cutVertices G u v⟩ from hadj).reachable
  exact
    { preconnected := fun x y => (hr x).symm.trans (hr y)
      nonempty := ⟨⟨u, start_mem_cutVertices G u v⟩⟩ }

/-- Old vertices retain all of their original neighbors after cutting;
the opposite endpoint is the one added cut leaf. -/
def oldNeighborEquiv (hb : G.IsBridge s(u, v)) {x : V} (hx : x ∈ cutSide G u v) :
    (cutGraph G u v).neighborSet ⟨x, Or.inl hx⟩ ≃ G.neighborSet x where
  toFun y := ⟨y.val.val, y.property⟩
  invFun y := ⟨⟨y.val, neighbors_mem_cutVertices G u v hb hx y.property⟩, y.property⟩
  left_inv y := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv y := by apply Subtype.ext; rfl

theorem old_vertexDegree (hb : G.IsBridge s(u, v)) {x : V} (hx : x ∈ cutSide G u v) :
    vertexDegree (cutGraph G u v) ⟨x, Or.inl hx⟩ = vertexDegree G x :=
  Nat.card_congr (oldNeighborEquiv G u v hb hx)

def boundaryNeighborEquiv (hadj : G.Adj u v) (hb : G.IsBridge s(u, v)) :
    (cutGraph G u v).neighborSet ⟨v, end_mem_cutVertices G u v⟩ ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨⟨u, start_mem_cutVertices G u v⟩, hadj.symm⟩
  left_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    exact (boundary_neighbor_eq G u v hb y.val.property y.property).symm
  right_inv _ := rfl

theorem boundary_vertexDegree (hadj : G.Adj u v) (hb : G.IsBridge s(u, v)) :
    vertexDegree (cutGraph G u v) ⟨v, end_mem_cutVertices G u v⟩ = 1 := by
  simpa only [vertexDegree, Nat.card_unique] using Nat.card_congr (boundaryNeighborEquiv G u v hadj hb)

theorem cutGraph_binary (hbinary : IsBinary G) (hadj : G.Adj u v)
    (hb : G.IsBridge s(u, v)) : IsBinary (cutGraph G u v) := by
  rintro ⟨x, hx⟩
  rcases hx with hx | hx
  · simpa only [old_vertexDegree G u v hb hx] using hbinary x
  · subst x
    exact Or.inl (boundary_vertexDegree G u v hadj hb)

/-- The opposite endpoint is genuinely a fresh cut leaf relative to the
retained component. This equivalence exposes the usual `Option` indexing. -/
def cutVertexEquiv (hb : G.IsBridge s(u, v)) :
    cutVertices G u v ≃ Option (cutSide G u v) := by
  classical
  refine
    { toFun := fun x => if hx : x.val ∈ cutSide G u v then some ⟨x.val, hx⟩ else none
      invFun := fun x => match x with
        | none => ⟨v, end_mem_cutVertices G u v⟩
        | some y => ⟨y.val, Or.inl y.property⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    by_cases hx : x.val ∈ cutSide G u v
    · simp only [dif_pos hx]
    · simp only [dif_neg hx]
      apply Subtype.ext
      exact (x.property.resolve_left hx).symm
  · rintro (_ | x)
    · simp only [dif_neg (end_not_mem_cutSide G u v hb)]
    · simp only [dif_pos x.property]

theorem cutVertices_proper (hb : G.IsBridge s(u, v)) (hv : vertexDegree G v = 3) :
    ∃ x, x ∉ cutVertices G u v := by
  by_contra h
  have hall (x : V) : x ∈ cutVertices G u v := by
    by_contra hx
    exact h ⟨x, hx⟩
  have hs : Subsingleton (G.neighborSet v) :=
    ⟨fun x y => Subtype.ext ((boundary_neighbor_eq G u v hb (hall x) x.property).trans
      (boundary_neighbor_eq G u v hb (hall y) y.property).symm)⟩
  have hne : Nonempty (G.neighborSet v) :=
    (Nat.card_ne_zero.mp (by change vertexDegree G v ≠ 0; omega)).1
  have hc : vertexDegree G v = 1 := by
    letI := hs
    letI := hne
    exact Nat.card_unique
  omega

/-- An internal bridge produces strictly smaller vertex types on each
side. The decrease is proved from the original endpoint degree. -/
theorem cutGraph_card_lt [Finite V] (hb : G.IsBridge s(u, v))
    (hv : vertexDegree G v = 3) : Nat.card (cutVertices G u v) < Nat.card V := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  obtain ⟨x, hx⟩ := cutVertices_proper G u v hb hv
  simpa only [Nat.card_eq_fintype_card] using
    (Fintype.card_subtype_lt (p := fun x => x ∈ cutVertices G u v) hx)

abbrev OldLeafSide := {x : Leaf G // x.val ∈ cutSide G u v}

/-- Exactly one leaf is added on each side; the old leaves are precisely
the original leaves belonging to that component. -/
def cutLeafEquiv (hadj : G.Adj u v) (hb : G.IsBridge s(u, v)) :
    Leaf (cutGraph G u v) ≃ Option (OldLeafSide G u v) := by
  classical
  refine
    { toFun := fun x => if hx : x.val.val ∈ cutSide G u v then
        some ⟨⟨x.val.val, (old_vertexDegree G u v hb hx).symm.trans x.property⟩, hx⟩
        else none
      invFun := fun x => match x with
        | none => ⟨⟨v, end_mem_cutVertices G u v⟩, boundary_vertexDegree G u v hadj hb⟩
        | some y =>
            ⟨⟨y.val.val, Or.inl y.property⟩,
              (old_vertexDegree G u v hb y.property).trans y.val.property⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    by_cases hx : x.val.val ∈ cutSide G u v
    · simp only [dif_pos hx]
    · simp only [dif_neg hx]
      apply Subtype.ext
      apply Subtype.ext
      exact (x.val.property.resolve_left hx).symm
  · rintro (_ | x)
    · simp only [dif_neg (end_not_mem_cutSide G u v hb)]
    · simp only [dif_pos x.property]

theorem cutSide_swap_iff (hG : G.Connected) (hb : G.IsBridge s(u, v)) (x : V) :
    x ∈ cutSide G v u ↔ x ∉ cutSide G u v := by
  change (cutBase G v u).Reachable v x ↔ _
  rw [cutBase_swap]
  exact other_side_iff_not_side G u v hG hb x

def leafPartitionEquiv (hG : G.Connected) (hb : G.IsBridge s(u, v)) :
    Leaf G ≃ OldLeafSide G u v ⊕ OldLeafSide G v u := by
  classical
  refine
    { toFun := fun x => if hx : x.val ∈ cutSide G u v then .inl ⟨x, hx⟩
        else .inr ⟨x, (cutSide_swap_iff G u v hG hb x).mpr hx⟩
      invFun := Sum.elim Subtype.val Subtype.val
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    dsimp only
    split_ifs <;> rfl
  · rintro (x | x)
    · dsimp only
      simp only [Sum.elim_inl]
      exact dite_eq_left x.property
    · have hx : x.val.val ∉ cutSide G u v :=
        (cutSide_swap_iff G u v hG hb x.val).mp x.property
      dsimp only
      simp only [Sum.elim_inr]
      exact dite_eq_right hx

theorem cut_leafCount [Finite V] (hadj : G.Adj u v) (hb : G.IsBridge s(u, v)) :
    leafCount (cutGraph G u v) = Nat.card (OldLeafSide G u v) + 1 := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  simpa only [leafCount, Nat.card_eq_fintype_card, Fintype.card_option] using
    Nat.card_congr (cutLeafEquiv G u v hadj hb)

theorem cut_leafCounts [Finite V] (hG : G.Connected)
    (hadj : G.Adj u v) (hb : G.IsBridge s(u, v)) :
    leafCount (cutGraph G u v) + leafCount (cutGraph G v u) = leafCount G + 2 := by
  have hb' : G.IsBridge s(v, u) := by simpa only [Sym2.eq_swap] using hb
  have hpart := Nat.card_congr (leafPartitionEquiv G u v hG hb)
  rw [Nat.card_sum] at hpart
  rw [cut_leafCount G u v hadj hb, cut_leafCount G v u hadj.symm hb']
  change Nat.card (OldLeafSide G u v) + 1 + (Nat.card (OldLeafSide G v u) + 1) = _
  change Nat.card (Leaf G) = _ at hpart
  unfold leafCount
  omega

theorem mem_both_cutVertices_iff (hG : G.Connected) (hb : G.IsBridge s(u, v)) (x : V) :
    x ∈ cutVertices G u v ∧ x ∈ cutVertices G v u ↔ x = u ∨ x = v := by
  constructor
  · rintro ⟨hx, hy⟩
    rcases hx with hx | hx
    · rcases hy with hy | hy
      · exact ((cutSide_swap_iff G u v hG hb x).mp hy hx).elim
      · exact Or.inl hy
    · exact Or.inr hx
  · rintro (hx | hx)
    · subst x
      exact ⟨start_mem_cutVertices G u v, end_mem_cutVertices G v u⟩
    · subst x
      exact ⟨end_mem_cutVertices G u v, start_mem_cutVertices G v u⟩

theorem edge_contained_cut (hG : G.Connected) (hb : G.IsBridge s(u, v))
    {x y : V} (hxy : G.Adj x y) :
    (x ∈ cutVertices G u v ∧ y ∈ cutVertices G u v) ∨
      (x ∈ cutVertices G v u ∧ y ∈ cutVertices G v u) := by
  by_cases hx : x ∈ cutSide G u v
  · exact Or.inl ⟨Or.inl hx, neighbors_mem_cutVertices G u v hb hx hxy⟩
  · have hx' : x ∈ cutSide G v u := (cutSide_swap_iff G u v hG hb x).mpr hx
    have hb' : G.IsBridge s(v, u) := by simpa only [Sym2.eq_swap] using hb
    exact Or.inr ⟨Or.inl hx', neighbors_mem_cutVertices G v u hb' hx' hxy⟩

theorem edge_both_cut_iff (hG : G.Connected) (hb : G.IsBridge s(u, v))
    {x y : V} (hxy : G.Adj x y) :
    (x ∈ cutVertices G u v ∧ y ∈ cutVertices G u v) ∧
      (x ∈ cutVertices G v u ∧ y ∈ cutVertices G v u) ↔ s(x, y) = s(u, v) := by
  constructor
  · rintro ⟨⟨hxL, hyL⟩, ⟨hxR, hyR⟩⟩
    rcases (mem_both_cutVertices_iff G u v hG hb x).mp ⟨hxL, hxR⟩ with hx | hx <;>
      rcases (mem_both_cutVertices_iff G u v hG hb y).mp ⟨hyL, hyR⟩ with hy | hy
    · exact (hxy.ne (hx.trans hy.symm)).elim
    · exact Sym2.eq_iff.mpr (Or.inl ⟨hx, hy⟩)
    · exact Sym2.eq_iff.mpr (Or.inr ⟨hx, hy⟩)
    · exact (hxy.ne (hx.trans hy.symm)).elim
  · intro he
    rcases Sym2.eq_iff.mp he with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · subst x
      subst y
      exact ⟨⟨start_mem_cutVertices G u v, end_mem_cutVertices G u v⟩,
        ⟨end_mem_cutVertices G v u, start_mem_cutVertices G v u⟩⟩
    · subst x
      subst y
      exact ⟨⟨end_mem_cutVertices G u v, start_mem_cutVertices G u v⟩,
        ⟨start_mem_cutVertices G v u, end_mem_cutVertices G v u⟩⟩

/-- Exactly the original bridge occurs in both induced cut graphs. -/
theorem cut_edgeCounts [Finite V] [DecidableEq V] (hG : G.Connected)
    (hadj : G.Adj u v) (hb : G.IsBridge s(u, v)) :
    edgeCount (cutGraph G u v) + edgeCount (cutGraph G v u) = edgeCount G + 1 := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  let A := G.edgeFinset ∩ (cutVertices G u v).toFinset.sym2
  let B := G.edgeFinset ∩ (cutVertices G v u).toFinset.sym2
  have hA : edgeCount (cutGraph G u v) = A.card := by
    have h := congrArg Finset.card (SimpleGraph.map_edgeFinset_induce
      (G := G) (s := cutVertices G u v))
    simpa only [Finset.card_map, edgeCount, cutGraph, Nat.card_eq_fintype_card,
      SimpleGraph.edgeFinset_card, A] using h
  have hB : edgeCount (cutGraph G v u) = B.card := by
    have h := congrArg Finset.card (SimpleGraph.map_edgeFinset_induce
      (G := G) (s := cutVertices G v u))
    simpa only [Finset.card_map, edgeCount, cutGraph, Nat.card_eq_fintype_card,
      SimpleGraph.edgeFinset_card, B] using h
  have hu : A ∪ B = G.edgeFinset := by
    ext e
    refine Sym2.ind ?_ e
    intro x y
    simp only [A, B, Finset.mem_union, Finset.mem_inter, SimpleGraph.mem_edgeFinset,
      SimpleGraph.mem_edgeSet, Finset.mk_mem_sym2_iff, Set.mem_toFinset]
    constructor
    · rintro (⟨hxy, _⟩ | ⟨hxy, _⟩) <;> exact hxy
    · intro hxy
      exact (edge_contained_cut G u v hG hb hxy).elim
        (fun h => Or.inl ⟨hxy, h⟩) (fun h => Or.inr ⟨hxy, h⟩)
  have hi : A ∩ B = {s(u, v)} := by
    ext e
    refine Sym2.ind ?_ e
    intro x y
    simp only [A, B, Finset.mem_inter, SimpleGraph.mem_edgeFinset,
      SimpleGraph.mem_edgeSet, Finset.mk_mem_sym2_iff, Set.mem_toFinset,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hxy, hL⟩, ⟨_, hR⟩⟩
      exact (edge_both_cut_iff G u v hG hb hxy).mp ⟨hL, hR⟩
    · intro he
      have hxy : G.Adj x y := by
        rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hadj
        · exact hadj.symm
      obtain ⟨hL, hR⟩ := (edge_both_cut_iff G u v hG hb hxy).mpr he
      exact ⟨⟨hxy, hL⟩, ⟨hxy, hR⟩⟩
  have hc := Finset.card_union_add_card_inter A B
  rw [hu, hi, Finset.card_singleton] at hc
  rw [hA, hB]
  simpa only [edgeCount, Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card] using hc.symm

end Cut

section InducedCycles

variable [DecidableEq V] (s : Set V)

/-- A cycle in an induced graph is sent to its literal edge set in the
original graph. The map is injective, including at the level of cycles. -/
def cycleMapInduce (c : Cycle (G.induce s)) : Cycle G := by
  let f : (G.induce s) →g G := (SimpleGraph.Embedding.induce s).toHom
  refine ⟨c.val.map (Function.Embedding.subtype (· ∈ s)).sym2Map, ?_⟩
  obtain ⟨x, p, hp, he⟩ := c.property
  refine ⟨f x, p.map f, hp.map Subtype.val_injective, ?_⟩
  rw [SimpleGraph.Walk.edges_map, list_toFinset_map, he, Finset.map_eq_image]
  rfl

theorem cycleMapInduce_injective : Function.Injective (cycleMapInduce G s) := by
  intro c d he
  apply Subtype.ext
  exact Finset.map_injective (Function.Embedding.subtype (· ∈ s)).sym2Map
    (congrArg Subtype.val he)

@[simp] theorem cycleMapInduce_card (c : Cycle (G.induce s)) :
    (cycleMapInduce G s c).val.card = c.val.card := by
  exact Finset.card_map _

theorem mem_cycleVertices_map {c : Cycle (G.induce s)} {x : s}
    (hx : x ∈ cycleVertices (G.induce s) c) :
    x.val ∈ cycleVertices G (cycleMapInduce G s c) := by
  obtain ⟨e, he, hxe⟩ := Finset.mem_biUnion.mp hx
  apply Finset.mem_biUnion.mpr
  refine ⟨(Function.Embedding.subtype (· ∈ s)).sym2Map e,
    Finset.mem_map.mpr ⟨e, he, rfl⟩, ?_⟩
  apply Sym2.mem_toFinset.mpr
  exact Sym2.mem_map.mpr ⟨x, Sym2.mem_toFinset.mp hxe, rfl⟩

theorem cycleMapInduce_edge_vertices (c : Cycle (G.induce s)) {e : Sym2 V}
    (he : e ∈ (cycleMapInduce G s c).val) {x : V} (hx : x ∈ e) : x ∈ s := by
  obtain ⟨e', he', rfl⟩ := Finset.mem_map.mp he
  obtain ⟨x', hx', hxeq⟩ := Sym2.mem_map.mp hx
  exact hxeq ▸ x'.property

/-- An actual cycle whose vertices lie in an induced set lifts to that
induced graph. The image is equal as an edge-set cycle, not only up to a
choice of cyclic ordering. -/
theorem exists_cycle_induce (c : Cycle G) (hc : ∀ x ∈ cycleVertices G c, x ∈ s) :
    ∃ d : Cycle (G.induce s), cycleMapInduce G s d = c := by
  obtain ⟨v, p, hp, he⟩ := c.property
  have hs : ∀ x ∈ p.support, x ∈ s := by
    intro x hx
    apply hc x
    rw [cycleVertices_eq_support G c hp he]
    exact List.mem_toFinset.mpr hx
  let q := p.induce s hs
  have hq : q.IsCycle := by
    apply SimpleGraph.Walk.IsCycle.of_map (f := (SimpleGraph.Embedding.induce s).toHom)
    exact (congrArg (fun r : G.Walk v v => r.IsCycle)
      (SimpleGraph.Walk.map_induce p hs)).mpr hp
  refine ⟨⟨q.edges.toFinset, ⟨_, q, hq, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  change q.edges.toFinset.map (Function.Embedding.subtype (· ∈ s)).sym2Map = c.val
  have hmap := congrArg (fun w => w.edges.toFinset)
    (SimpleGraph.Walk.map_induce p hs)
  rw [SimpleGraph.Walk.edges_map, list_toFinset_map] at hmap
  rw [Finset.map_eq_image]
  exact hmap.trans he

/-- Vertex-disjointness of actual cycles passes to every induced graph. -/
theorem hasDisjointCycles_induce (hG : HasDisjointCycles G) :
    HasDisjointCycles (G.induce s) := by
  intro c d hne
  apply Finset.disjoint_left.mpr
  intro x hxc hxd
  have hne' : cycleMapInduce G s c ≠ cycleMapInduce G s d :=
    fun h => hne (cycleMapInduce_injective G s h)
  exact Finset.disjoint_left.mp (hG _ _ hne')
    (mem_cycleVertices_map G s hxc) (mem_cycleVertices_map G s hxd)

end InducedCycles

theorem cutGraph_isBinaryCactus [DecidableEq V] (hG : IsBinaryCactus G) (u v : V)
    (hadj : G.Adj u v) (hb : G.IsBridge s(u, v)) : IsBinaryCactus (cutGraph G u v) where
  connected := cutGraph_connected G u v hadj
  binary := cutGraph_binary G u v hG.binary hadj hb
  disjoint_cycles := hasDisjointCycles_induce G (cutVertices G u v) hG.disjoint_cycles

section CutCycles

variable [DecidableEq V] (u v : V)

/-- A simple cycle cannot cross a bridge. Its entire support belongs to
one of the two original components after deletion. -/
theorem cycle_on_one_cutSide (hG : G.Connected) (hb : G.IsBridge s(u, v))
    (c : Cycle G) :
    (∀ x ∈ cycleVertices G c, x ∈ cutSide G u v) ∨
      (∀ x ∈ cycleVertices G c, x ∈ cutSide G v u) := by
  obtain ⟨w, p, hp, he⟩ := c.property
  have havoid : s(u, v) ∉ p.edges := hb.notMem_edges_of_isCycle hp
  let q := p.toDeleteEdge s(u, v) havoid
  have hreach (x : V) (hx : x ∈ cycleVertices G c) :
      (cutBase G u v).Reachable w x := by
    have hxp : x ∈ p.support := by
      rw [cycleVertices_eq_support G c hp he] at hx
      exact List.mem_toFinset.mp hx
    have hxq : x ∈ q.support := by simpa only [q, SimpleGraph.Walk.support_transfer] using hxp
    exact (q.takeUntil x hxq).reachable
  rcases reachable_cut_either G u v hG w with hw | hw
  · exact Or.inl (fun x hx => hw.trans (hreach x hx))
  · apply Or.inr
    intro x hx
    change (cutBase G v u).Reachable v x
    rw [cutBase_swap]
    exact hw.trans (hreach x hx)

def cutCycleMap : Cycle (cutGraph G u v) ⊕ Cycle (cutGraph G v u) → Cycle G :=
  Sum.elim (cycleMapInduce G (cutVertices G u v))
    (cycleMapInduce G (cutVertices G v u))

theorem cutCycleMap_injective (hG : G.Connected) (hb : G.IsBridge s(u, v)) :
    Function.Injective (cutCycleMap G u v) := by
  have hcross (a : Cycle (cutGraph G u v)) (b : Cycle (cutGraph G v u)) :
      cycleMapInduce G (cutVertices G u v) a ≠
        cycleMapInduce G (cutVertices G v u) b := by
    intro heq
    let c := cycleMapInduce G (cutVertices G u v) a
    have hnon : c.val.Nonempty := Finset.card_pos.mp (by have := cycle_card_ge_three G c; omega)
    obtain ⟨e, he⟩ := hnon
    have heR : e ∈ (cycleMapInduce G (cutVertices G v u) b).val := heq ▸ he
    have hed : e ∈ G.edgeSet := cycle_edges_subset G c he
    have hbridge : e = s(u, v) := by
      revert he heR hed
      refine Sym2.ind ?_ e
      intro x y he heR hed
      apply (edge_both_cut_iff G u v hG hb hed).mp
      exact ⟨⟨cycleMapInduce_edge_vertices G _ a he (by simp),
        cycleMapInduce_edge_vertices G _ a he (by simp)⟩,
        ⟨cycleMapInduce_edge_vertices G _ b heR (by simp),
        cycleMapInduce_edge_vertices G _ b heR (by simp)⟩⟩
    exact bridge_not_mem_cycle G hb c (hbridge ▸ he)
  rintro (a | a) (b | b) heq
  · exact congrArg Sum.inl (cycleMapInduce_injective G _ heq)
  · exact (hcross a b heq).elim
  · exact (hcross b a heq.symm).elim
  · exact congrArg Sum.inr (cycleMapInduce_injective G _ heq)

theorem cutCycleMap_surjective (hG : G.Connected) (hb : G.IsBridge s(u, v)) :
    Function.Surjective (cutCycleMap G u v) := by
  intro c
  rcases cycle_on_one_cutSide G u v hG hb c with hL | hR
  · obtain ⟨d, hd⟩ := exists_cycle_induce G (cutVertices G u v) c
      (fun x hx => Or.inl (hL x hx))
    exact ⟨Sum.inl d, hd⟩
  · obtain ⟨d, hd⟩ := exists_cycle_induce G (cutVertices G v u) c
      (fun x hx => Or.inl (hR x hx))
    exact ⟨Sum.inr d, hd⟩

/-- Cutting duplicates a bridge, but every genuine simple cycle belongs
to exactly one side and retains all its original edges. -/
def cutCycleEquiv (hG : G.Connected) (hb : G.IsBridge s(u, v)) :
    Cycle (cutGraph G u v) ⊕ Cycle (cutGraph G v u) ≃ Cycle G :=
  Equiv.ofBijective (cutCycleMap G u v)
    ⟨cutCycleMap_injective G u v hG hb, cutCycleMap_surjective G u v hG hb⟩

@[simp] theorem cutCycleEquiv_inl (hG : G.Connected) (hb : G.IsBridge s(u, v))
    (c : Cycle (cutGraph G u v)) :
    cutCycleEquiv G u v hG hb (Sum.inl c) = cycleMapInduce G (cutVertices G u v) c := rfl

@[simp] theorem cutCycleEquiv_inr (hG : G.Connected) (hb : G.IsBridge s(u, v))
    (c : Cycle (cutGraph G v u)) :
    cutCycleEquiv G u v hG hb (Sum.inr c) = cycleMapInduce G (cutVertices G v u) c := rfl

theorem cut_cycleCounts [Finite V] (hG : G.Connected) (hb : G.IsBridge s(u, v)) :
    cycleCount (cutGraph G u v) + cycleCount (cutGraph G v u) = cycleCount G := by
  simpa only [cycleCount, Nat.card_sum] using Nat.card_congr (cutCycleEquiv G u v hG hb)

def cutTriangleMap :
    {c : Cycle (cutGraph G u v) // c.val.card = 3} ⊕
      {c : Cycle (cutGraph G v u) // c.val.card = 3} →
        {c : Cycle G // c.val.card = 3}
  | Sum.inl c => ⟨cycleMapInduce G (cutVertices G u v) c.val,
      (cycleMapInduce_card G _ c.val).trans c.property⟩
  | Sum.inr c => ⟨cycleMapInduce G (cutVertices G v u) c.val,
      (cycleMapInduce_card G _ c.val).trans c.property⟩

def cutTriangleEquiv (hG : G.Connected) (hb : G.IsBridge s(u, v)) :
    {c : Cycle (cutGraph G u v) // c.val.card = 3} ⊕
      {c : Cycle (cutGraph G v u) // c.val.card = 3} ≃
        {c : Cycle G // c.val.card = 3} := by
  refine Equiv.ofBijective (cutTriangleMap G u v) ⟨?_, ?_⟩
  · rintro (a | a) (b | b) hab
    · exact congrArg Sum.inl (Subtype.ext
        (cycleMapInduce_injective G _ (congrArg Subtype.val hab)))
    · have h : (Sum.inl a.val : Cycle (cutGraph G u v) ⊕ Cycle (cutGraph G v u)) =
          Sum.inr b.val := cutCycleMap_injective G u v hG hb (congrArg Subtype.val hab)
      cases h
    · have h : (Sum.inr a.val : Cycle (cutGraph G u v) ⊕ Cycle (cutGraph G v u)) =
          Sum.inl b.val := cutCycleMap_injective G u v hG hb (congrArg Subtype.val hab)
      cases h
    · exact congrArg Sum.inr (Subtype.ext
        (cycleMapInduce_injective G _ (congrArg Subtype.val hab)))
  · intro c
    obtain ⟨d, hd⟩ := cutCycleMap_surjective G u v hG hb c.val
    cases d with
    | inl d =>
      have hcard : d.val.card = 3 := by
        rw [← cycleMapInduce_card G (cutVertices G u v) d]
        exact (congrArg (fun z : Cycle G => z.val.card) hd).trans c.property
      exact ⟨Sum.inl ⟨d, hcard⟩, Subtype.ext hd⟩
    | inr d =>
      have hcard : d.val.card = 3 := by
        rw [← cycleMapInduce_card G (cutVertices G v u) d]
        exact (congrArg (fun z : Cycle G => z.val.card) hd).trans c.property
      exact ⟨Sum.inr ⟨d, hcard⟩, Subtype.ext hd⟩

theorem cut_triangleCounts [Finite V] (hG : G.Connected) (hb : G.IsBridge s(u, v)) :
    triangleCount (cutGraph G u v) + triangleCount (cutGraph G v u) = triangleCount G := by
  simpa only [triangleCount, Nat.card_sum] using Nat.card_congr (cutTriangleEquiv G u v hG hb)

end CutCycles

section LocalBlocks

variable [Finite V] [DecidableEq V]

def IsInternalBridge (u v : V) : Prop :=
  G.Adj u v ∧ G.IsBridge s(u, v) ∧ vertexDegree G u = 3 ∧ vertexDegree G v = 3

def EveryBridgeHasLeaf : Prop :=
  ∀ u v, G.Adj u v → G.IsBridge s(u, v) →
    vertexDegree G u = 1 ∨ vertexDegree G v = 1

theorem everyBridgeHasLeaf_of_no_internal (hbin : IsBinary G)
    (hno : ¬∃ u v, IsInternalBridge G u v) : EveryBridgeHasLeaf G := by
  intro u v hadj hb
  rcases hbin u with hu | hu
  · exact Or.inl hu
  rcases hbin v with hv | hv
  · exact Or.inr hv
  · exact (hno ⟨u, v, hadj, hb, hu, hv⟩).elim

theorem leaf_neighbor_unique {v x y : V} (hv : vertexDegree G v = 1)
    (hx : G.Adj v x) (hy : G.Adj v y) : x = y := by
  have hs : Subsingleton (G.neighborSet v) := (Nat.card_eq_one_iff_unique.mp hv).1
  exact congrArg Subtype.val (hs.elim (⟨x, hx⟩ : G.neighborSet v) ⟨y, hy⟩)

/-- In a connected graph, a nonempty set closed under taking neighbors
contains every vertex. -/
theorem all_mem_of_neighbor_closed (hG : G.Connected) (S : Set V)
    (hne : S.Nonempty) (hclosed : ∀ x ∈ S, ∀ y, G.Adj x y → y ∈ S) :
    ∀ x, x ∈ S := by
  obtain ⟨v, hv⟩ := hne
  intro x
  have hr := (SimpleGraph.reachable_iff_reflTransGen v x).mp (hG.preconnected v x)
  induction hr with
  | refl => exact hv
  | tail _ hadj ih => exact hclosed _ ih _ hadj

def cycleNeighborSet (c : Cycle G) (x : V) : Set V := {y | s(x, y) ∈ c.val}

theorem cycleNeighborSet_subset (c : Cycle G) (x : V) :
    cycleNeighborSet G c x ⊆ G.neighborSet x :=
  fun _ hy => cycle_edges_subset G c hy

theorem cycleNeighborSet_ncard (c : Cycle G) {x : V}
    (hx : x ∈ cycleVertices G c) : (cycleNeighborSet G c x).ncard = 2 := by
  obtain ⟨v, p, hp, he⟩ := c.property
  have hxp : x ∈ p.support := by
    rw [cycleVertices_eq_support G c hp he] at hx
    exact List.mem_toFinset.mp hx
  have hset : cycleNeighborSet G c x = p.toSubgraph.neighborSet x := by
    ext y
    simp only [cycleNeighborSet, Set.mem_setOf_eq, ← he, List.mem_toFinset,
      SimpleGraph.Subgraph.mem_neighborSet, SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges]
  rw [hset]
  exact hp.ncard_neighborSet_toSubgraph_eq_two hxp

theorem cycle_vertexDegree (hbin : IsBinary G) (c : Cycle G) {x : V}
    (hx : x ∈ cycleVertices G c) : vertexDegree G x = 3 := by
  have hle := Set.ncard_le_ncard (cycleNeighborSet_subset G c x)
  rw [cycleNeighborSet_ncard G c hx] at hle
  change 2 ≤ vertexDegree G x at hle
  rcases hbin x with h | h
  · omega
  · exact h

/-- An edge leaving a cycle is a bridge. Any other simple cycle
containing that edge would share its endpoint with the first cycle. -/
theorem cycle_external_isBridge (hcactus : HasDisjointCycles G) (c : Cycle G)
    {x y : V} (hx : x ∈ cycleVertices G c) (hxy : G.Adj x y)
    (he : s(x, y) ∉ c.val) : G.IsBridge s(x, y) := by
  apply (SimpleGraph.isBridge_iff_forall_cycle_notMem hxy).mpr
  intro v p hp hep
  let d : Cycle G := ⟨p.edges.toFinset, ⟨v, p, hp, rfl⟩⟩
  have hed : s(x, y) ∈ d.val := List.mem_toFinset.mpr hep
  have hxd : x ∈ cycleVertices G d :=
    mem_cycleVertices_of_mem_edge G d hed (by simp)
  have hdc : d = c := by
    by_contra hne
    exact Finset.disjoint_left.mp (hcactus d c hne) hxd hx
  exact he (hdc ▸ hed)

theorem cycle_external_leaf (hcactus : IsBinaryCactus G) (hbridge : EveryBridgeHasLeaf G)
    (c : Cycle G) {x y : V} (hx : x ∈ cycleVertices G c) (hxy : G.Adj x y)
    (he : s(x, y) ∉ c.val) : vertexDegree G y = 1 := by
  have h := hbridge x y hxy (cycle_external_isBridge G hcactus.disjoint_cycles c hx hxy he)
  have hx3 := cycle_vertexDegree G hcactus.binary c hx
  exact h.resolve_left (by omega)

/-- Every cycle vertex has exactly one neighbor outside the cycle.
The cardinal calculation is the original degree three minus the two
neighbors of the genuine simple cycle. -/
theorem cycle_external_existsUnique (hbin : IsBinary G) (c : Cycle G) {x : V}
    (hx : x ∈ cycleVertices G c) :
    ∃! y, G.Adj x y ∧ s(x, y) ∉ c.val := by
  let S := G.neighborSet x \ cycleNeighborSet G c x
  have hn : S.ncard = 1 := by
    change (G.neighborSet x \ cycleNeighborSet G c x).ncard = 1
    rw [Set.ncard_sdiff (cycleNeighborSet_subset G c x),
      cycleNeighborSet_ncard G c hx]
    change vertexDegree G x - 2 = 1
    rw [cycle_vertexDegree G hbin c hx]
  obtain ⟨y, hy⟩ := Set.ncard_eq_one.mp hn
  refine ⟨y, ?_, ?_⟩
  · have hys : y ∈ S := by rw [hy]; exact Set.mem_singleton y
    exact hys
  · intro z hz
    have hzs : z ∈ S := hz
    simpa only [hy, Set.mem_singleton_iff] using hzs

/-- A completely explicit sunlet presentation indexed by the vertices
of an actual simple cycle. The cyclic order is supplied by `Cycle`'s
closed-walk witness. There is one distinct pendant leaf at every cycle
vertex and these are all the other vertices of the graph. -/
structure SunletPresentation (c : Cycle G) where
  leaf : (cycleVertices G c) → V
  leaf_adj : ∀ x, G.Adj x.val (leaf x)
  leaf_degree : ∀ x, vertexDegree G (leaf x) = 1
  leaf_outside : ∀ x, leaf x ∉ cycleVertices G c
  leaf_injective : Function.Injective leaf
  external_unique : ∀ x y, G.Adj x.val y → s(x.val, y) ∉ c.val → y = leaf x
  covers : ∀ y, y ∈ cycleVertices G c ∨ ∃ x, y = leaf x

theorem exists_sunletPresentation (hcactus : IsBinaryCactus G)
    (hbridge : EveryBridgeHasLeaf G) (c : Cycle G) : Nonempty (SunletPresentation G c) := by
  classical
  let leaf : (cycleVertices G c) → V := fun x =>
    Classical.choose (cycle_external_existsUnique G hcactus.binary c x.property)
  have leaf_spec (x : cycleVertices G c) :
      G.Adj x.val (leaf x) ∧ s(x.val, leaf x) ∉ c.val :=
    (Classical.choose_spec (cycle_external_existsUnique G hcactus.binary c x.property)).1
  have leaf_unique (x : cycleVertices G c) (y : V)
      (hy : G.Adj x.val y ∧ s(x.val, y) ∉ c.val) : y = leaf x :=
    (Classical.choose_spec (cycle_external_existsUnique G hcactus.binary c x.property)).2 y hy
  have leaf_degree (x : cycleVertices G c) : vertexDegree G (leaf x) = 1 :=
    cycle_external_leaf G hcactus hbridge c x.property (leaf_spec x).1 (leaf_spec x).2
  have leaf_outside (x : cycleVertices G c) : leaf x ∉ cycleVertices G c := by
    intro hx
    have h3 := cycle_vertexDegree G hcactus.binary c hx
    have h1 := leaf_degree x
    omega
  have leaf_inj : Function.Injective leaf := by
    intro x y hxy
    apply Subtype.ext
    exact leaf_neighbor_unique G (leaf_degree x) (leaf_spec x).1.symm
      (hxy.symm ▸ (leaf_spec y).1.symm)
  have hcover : ∀ y, y ∈ cycleVertices G c ∨ ∃ x, y = leaf x := by
    apply all_mem_of_neighbor_closed G hcactus.connected
      {y | y ∈ cycleVertices G c ∨ ∃ x, y = leaf x}
    · obtain ⟨x, hx⟩ := cycleVertices_nonempty G c
      exact ⟨x, Or.inl hx⟩
    · intro x hx y hxy
      rcases hx with hx | ⟨z, rfl⟩
      · by_cases he : s(x, y) ∈ c.val
        · exact Or.inl (mem_cycleVertices_of_mem_edge G c he (by simp))
        · exact Or.inr ⟨⟨x, hx⟩, leaf_unique ⟨x, hx⟩ y ⟨hxy, he⟩⟩
      · have hy : y = z.val := leaf_neighbor_unique G (leaf_degree z) hxy (leaf_spec z).1.symm
        exact Or.inl (hy ▸ z.property)
  exact ⟨⟨leaf, fun x => (leaf_spec x).1, leaf_degree, leaf_outside, leaf_inj,
    fun x y hxy he => leaf_unique x y ⟨hxy, he⟩, hcover⟩⟩

namespace SunletPresentation

variable {G} {c : Cycle G} (P : SunletPresentation G c)

include P

def vertexEquiv : (cycleVertices G c) ⊕ (cycleVertices G c) ≃ V := by
  refine Equiv.ofBijective (Sum.elim Subtype.val P.leaf) ⟨?_, ?_⟩
  · rintro (x | x) (y | y) hxy
    · exact congrArg Sum.inl (Subtype.ext hxy)
    · change x.val = P.leaf y at hxy
      exact (P.leaf_outside y (hxy ▸ x.property)).elim
    · change P.leaf x = y.val at hxy
      exact (P.leaf_outside x (hxy.symm ▸ y.property)).elim
    · exact congrArg Sum.inr (P.leaf_injective hxy)
  · intro y
    rcases P.covers y with hy | ⟨x, rfl⟩
    · exact ⟨Sum.inl ⟨y, hy⟩, rfl⟩
    · exact ⟨Sum.inr x, rfl⟩

theorem cycle_adj_iff (x y : cycleVertices G c) :
    G.Adj x.val y.val ↔ s(x.val, y.val) ∈ c.val := by
  constructor
  · intro hxy
    by_contra he
    have hy := P.external_unique x y hxy he
    exact P.leaf_outside x (hy ▸ y.property)
  · intro hxy
    exact cycle_edges_subset G c hxy

theorem cycle_leaf_adj_iff (x y : cycleVertices G c) :
    G.Adj x.val (P.leaf y) ↔ x = y := by
  constructor
  · intro h
    exact Subtype.ext (leaf_neighbor_unique G (P.leaf_degree y) h.symm (P.leaf_adj y).symm)
  · intro hxy
    subst x
    exact P.leaf_adj y

theorem leaf_not_adj (x y : cycleVertices G c) : ¬G.Adj (P.leaf x) (P.leaf y) := by
  intro h
  have he := leaf_neighbor_unique G (P.leaf_degree x) h (P.leaf_adj x).symm
  exact P.leaf_outside y (he.symm ▸ x.property)

end SunletPresentation

/-- A star presentation retains the actual center and its actual
neighbor type. In a binary graph that neighbor type has cardinal one
or three, yielding precisely the single edge or the three-leaf claw. -/
structure StarPresentation (center : V) : Prop where
  neighbors_are_leaves : ∀ x, G.Adj center x → vertexDegree G x = 1
  covers : ∀ x, x = center ∨ G.Adj center x

theorem starPresentation_of_leaf_neighbors (hG : G.Connected) (center : V)
    (hleaf : ∀ x, G.Adj center x → vertexDegree G x = 1) : StarPresentation G center := by
  refine ⟨hleaf, ?_⟩
  apply all_mem_of_neighbor_closed G hG {x | x = center ∨ G.Adj center x}
  · exact ⟨center, Or.inl rfl⟩
  · intro x hx y hxy
    rcases hx with rfl | hx
    · exact Or.inr hxy
    · exact Or.inl (leaf_neighbor_unique G (hleaf x hx) hxy hx.symm)

theorem exists_starPresentation_of_acyclic (hG : G.Connected) (hbin : IsBinary G)
    (ha : G.IsAcyclic) (hbridge : EveryBridgeHasLeaf G) :
    ∃ center, StarPresentation G center := by
  by_cases hc : ∃ c, vertexDegree G c = 3
  · obtain ⟨c, hc⟩ := hc
    refine ⟨c, starPresentation_of_leaf_neighbors G hG c ?_⟩
    intro x hcx
    have hb := (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp ha) hcx
    exact (hbridge c x hcx hb).resolve_left (by omega)
  · let c := hG.nonempty.some
    refine ⟨c, starPresentation_of_leaf_neighbors G hG c ?_⟩
    intro x hcx
    exact (hbin x).resolve_right (fun hx => hc ⟨x, hx⟩)

namespace StarPresentation

variable {G} {center : V} (P : StarPresentation G center)

include P

def vertexEquiv : Option (G.neighborSet center) ≃ V := by
  refine Equiv.ofBijective (fun x => match x with | none => center | some y => y.val) ⟨?_, ?_⟩
  · rintro (_ | x) (_ | y) hxy
    · rfl
    · change center = y.val at hxy
      exact (G.irrefl (hxy.symm ▸ y.property)).elim
    · change x.val = center at hxy
      exact (G.irrefl (hxy ▸ x.property)).elim
    · exact congrArg some (Subtype.ext hxy)
  · intro x
    rcases P.covers x with rfl | hx
    · exact ⟨none, rfl⟩
    · exact ⟨some ⟨x, hx⟩, rfl⟩

theorem neighbors_not_adj (x y : G.neighborSet center) : ¬G.Adj x.val y.val := by
  intro h
  have he := leaf_neighbor_unique G (P.neighbors_are_leaves x x.property) h x.property.symm
  exact G.irrefl (he ▸ y.property)

theorem vertexEquiv_adj_iff (x y : Option (G.neighborSet center)) :
    G.Adj (P.vertexEquiv x) (P.vertexEquiv y) ↔
      (x = none ∧ y ≠ none) ∨ (x ≠ none ∧ y = none) := by
  cases x with
  | none =>
    cases y with
    | none => simp [vertexEquiv]
    | some y => simp [vertexEquiv, show G.Adj center y.val from y.property]
  | some x =>
    cases y with
    | none => simp [vertexEquiv, x.property.symm]
    | some y => simp [vertexEquiv, P.neighbors_not_adj x y]

end StarPresentation

/-- A binary cactus without an internal bridge is an actual single
edge, three-leaf claw, or sunlet. The presentations give all vertices
and all adjacencies explicitly; no block-decomposition assumption is
part of the hypotheses. -/
theorem localBlock_of_no_internal (hG : IsBinaryCactus G)
    (hno : ¬∃ u v, IsInternalBridge G u v) :
    (∃ center, StarPresentation G center) ∨
      ∃ c : Cycle G, Nonempty (SunletPresentation G c) := by
  have hb := everyBridgeHasLeaf_of_no_internal G hG.binary hno
  by_cases ha : G.IsAcyclic
  · exact Or.inl (exists_starPresentation_of_acyclic G hG.connected hG.binary ha hb)
  · apply Or.inr
    simp only [SimpleGraph.IsAcyclic, not_forall, not_not] at ha
    obtain ⟨v, p, hp⟩ := ha
    let c : Cycle G := ⟨p.edges.toFinset, ⟨v, p, hp, rfl⟩⟩
    exact ⟨c, exists_sunletPresentation G hG hb c⟩

end LocalBlocks

section Counts

variable [Finite V] [DecidableEq V]

/-- The handshaking identity specialized to the paper's degree-one /
degree-three convention. -/
theorem binary_degree_sum (hbin : IsBinary G) :
    2 * edgeCount G + 2 * leafCount G = 3 * Nat.card V := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  have hd (x : V) : vertexDegree G x = G.degree x := by
    rw [vertexDegree, Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree]
  have hsum : (∑ x : V, vertexDegree G x) = 2 * edgeCount G := by
    simpa only [hd, edgeCount, Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card]
      using G.sum_degrees_eq_twice_card_edges
  have hleaf : (∑ x : V, if vertexDegree G x = 1 then 1 else 0) = leafCount G := by
    rw [← Finset.card_filter]
    simp only [leafCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hpoint (x : V) :
      vertexDegree G x + 2 * (if vertexDegree G x = 1 then 1 else 0) = 3 := by
    rcases hbin x with h | h <;> simp only [h] <;> decide
  have h := Finset.sum_congr (s₁ := Finset.univ) rfl (fun x _ => hpoint x)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hsum, hleaf,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card] at h
  rw [Nat.card_eq_fintype_card]
  omega

namespace StarPresentation

variable {G} {center : V} (P : StarPresentation G center)

include P

theorem vertexCount : Nat.card V = vertexDegree G center + 1 := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  have h := Nat.card_congr P.vertexEquiv
  simpa only [vertexDegree, Nat.card_eq_fintype_card, Fintype.card_option] using h.symm

def leafEquivNeighbor (hc : vertexDegree G center = 3) : Leaf G ≃ G.neighborSet center where
  toFun x := ⟨x.val, (P.covers x).resolve_left (fun he => by
    have hx := x.property
    rw [he, hc] at hx
    contradiction)⟩
  invFun x := ⟨x.val, P.neighbors_are_leaves x x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem leafCount_of_three (hc : vertexDegree G center = 3) : leafCount G = 3 :=
  (Nat.card_congr (P.leafEquivNeighbor hc)).trans hc

theorem leafCount_of_one (hc : vertexDegree G center = 1) : leafCount G = 2 := by
  have hall (x : V) : vertexDegree G x = 1 := by
    rcases P.covers x with rfl | hx
    · exact hc
    · exact P.neighbors_are_leaves x hx
  let e : Leaf G ≃ V :=
    { toFun := Subtype.val
      invFun := fun x => ⟨x, hall x⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h := (Nat.card_congr e).trans P.vertexCount
  simpa only [leafCount, hc] using h

theorem cycleCount_eq_zero (hbin : IsBinary G) : cycleCount G = 0 := by
  have hempty : IsEmpty (Cycle G) := ⟨by
    intro c
    obtain ⟨v, p, hp, he⟩ := c.property
    have hev : s(v, p.snd) ∈ c.val := he ▸ List.mem_toFinset.mpr (p.mk_start_snd_mem_edges hp.not_nil)
    have hv3 := cycle_vertexDegree G hbin c
      (mem_cycleVertices_of_mem_edge G c hev (x := v) (by simp))
    have hw3 := cycle_vertexDegree G hbin c
      (mem_cycleVertices_of_mem_edge G c hev (x := p.snd) (by simp))
    have hleaf : vertexDegree G v = 1 ∨ vertexDegree G p.snd = 1 := by
      rcases P.covers v with rfl | hv
      · exact Or.inr (P.neighbors_are_leaves _ (p.adj_snd hp.not_nil))
      · exact Or.inl (P.neighbors_are_leaves v hv)
    rcases hleaf with h | h <;> omega⟩
  letI := hempty
  exact Nat.card_of_isEmpty

theorem triangleCount_eq_zero (hbin : IsBinary G) : triangleCount G = 0 := by
  have hzero := P.cycleCount_eq_zero hbin
  have hempty : IsEmpty {c : Cycle G // c.val.card = 3} := ⟨fun c => by
    letI : Nonempty (Cycle G) := ⟨c.val⟩
    have hpos : 0 < Nat.card (Cycle G) := Nat.card_pos
    change Nat.card (Cycle G) = 0 at hzero
    omega⟩
  letI := hempty
  exact Nat.card_of_isEmpty

theorem counts (hbin : IsBinary G) :
    edgeCount G + 3 = 2 * leafCount G + 3 * cycleCount G ∧ 2 ≤ leafCount G := by
  have hd := binary_degree_sum G hbin
  have hv := P.vertexCount
  have hz := P.cycleCount_eq_zero hbin
  rcases hbin center with h1 | h3
  · have hn := P.leafCount_of_one h1
    omega
  · have hn := P.leafCount_of_three h3
    omega

end StarPresentation

namespace SunletPresentation

variable {G} {c : Cycle G} (P : SunletPresentation G c)

include P

def leafEquivCycleVertices (hbin : IsBinary G) : Leaf G ≃ (cycleVertices G c) := by
  refine (Equiv.ofBijective (fun x : cycleVertices G c =>
    (⟨P.leaf x, P.leaf_degree x⟩ : Leaf G)) ⟨?_, ?_⟩).symm
  · intro x y h
    exact P.leaf_injective (congrArg Subtype.val h)
  · intro x
    rcases P.covers x with hx | ⟨y, hy⟩
    · have h3 := cycle_vertexDegree G hbin c hx
      have h1 := x.property
      omega
    · exact ⟨y, Subtype.ext hy.symm⟩

theorem vertexCount : Nat.card V = 2 * Nat.card (cycleVertices G c) := by
  have h := Nat.card_congr P.vertexEquiv
  rw [Nat.card_sum] at h
  omega

theorem leafCount_eq (hbin : IsBinary G) : leafCount G = Nat.card (cycleVertices G c) :=
  Nat.card_congr (P.leafEquivCycleVertices hbin)

theorem cycle_eq (hG : IsBinaryCactus G) (d : Cycle G) : d = c := by
  obtain ⟨x, hx⟩ := cycleVertices_nonempty G d
  have hxc : x ∈ cycleVertices G c := by
    rcases P.covers x with hxc | ⟨y, rfl⟩
    · exact hxc
    · have h3 := cycle_vertexDegree G hG.binary d hx
      have h1 := P.leaf_degree y
      omega
  by_contra hne
  exact Finset.disjoint_left.mp (hG.disjoint_cycles d c hne) hx hxc

theorem cycleCount_eq_one (hG : IsBinaryCactus G) : cycleCount G = 1 := by
  letI : Subsingleton (Cycle G) := ⟨fun a b => (P.cycle_eq hG a).trans (P.cycle_eq hG b).symm⟩
  letI : Nonempty (Cycle G) := ⟨c⟩
  exact Nat.card_unique

theorem triangleCount_eq (hG : IsBinaryCactus G) :
    triangleCount G = if c.val.card = 3 then 1 else 0 := by
  classical
  by_cases hc : c.val.card = 3
  · rw [if_pos hc]
    letI : Subsingleton {d : Cycle G // d.val.card = 3} :=
      ⟨fun a b => Subtype.ext ((P.cycle_eq hG a.val).trans (P.cycle_eq hG b.val).symm)⟩
    letI : Nonempty {d : Cycle G // d.val.card = 3} := ⟨⟨c, hc⟩⟩
    exact Nat.card_unique
  · rw [if_neg hc]
    letI : IsEmpty {d : Cycle G // d.val.card = 3} := ⟨fun d => hc (P.cycle_eq hG d.val ▸ d.property)⟩
    exact Nat.card_of_isEmpty

end SunletPresentation

theorem cycleVertices_card_eq (c : Cycle G) : (cycleVertices G c).card = c.val.card := by
  obtain ⟨v, p, hp, he⟩ := c.property
  rw [cycleVertices_eq_support G c hp he, ← he,
    List.toFinset_card_of_nodup hp.isTrail.edges_nodup, p.length_edges]
  have htail : p.support.toFinset = p.support.tail.toFinset := by
    ext x
    simp only [List.mem_toFinset]
    rw [← p.cons_tail_support]
    simp only [List.mem_cons, List.tail_cons]
    exact or_iff_right_of_imp (fun hx => hx.symm ▸ p.end_mem_tail_support hp.not_nil)
  rw [htail, List.toFinset_card_of_nodup hp.support_nodup, List.length_tail, p.length_support]
  omega

namespace SunletPresentation

variable {G} {c : Cycle G} (P : SunletPresentation G c)

include P

theorem counts (hG : IsBinaryCactus G) :
    edgeCount G + 3 = 2 * leafCount G + 3 * cycleCount G ∧ 2 ≤ leafCount G := by
  have hd := binary_degree_sum G hG.binary
  have hv := P.vertexCount
  have hn := P.leafCount_eq hG.binary
  have hC := P.cycleCount_eq_one hG
  have hm : 3 ≤ Nat.card (cycleVertices G c) := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe, cycleVertices_card_eq]
      using cycle_card_ge_three G c
  omega

end SunletPresentation

end Counts

section CyclicOrders

variable [Finite V] [DecidableEq V]

def cycleSpanningGraph (c : Cycle G) : SimpleGraph V where
  Adj x y := s(x, y) ∈ c.val
  symm.symm x y h := by simpa only [Sym2.eq_swap] using h
  loopless.irrefl x h := G.irrefl (cycle_edges_subset G c h)

theorem cycleSpanningGraph_edgeSet (c : Cycle G) :
    (cycleSpanningGraph G c).edgeSet = (c.val : Set (Sym2 V)) := by
  ext e
  refine Sym2.ind ?_ e
  intro x y
  rfl

/-- A finite cyclic ordering of all vertices of an actual simple cycle,
with both directions of the adjacency correspondence. -/
structure CycleOrder (c : Cycle G) where
  extra : ℕ
  length_eq : extra + 3 = c.val.card
  vertex : Fin (extra + 3) ≃ (cycleVertices G c)
  adj_iff : ∀ i j,
    s((vertex i).val, (vertex j).val) ∈ c.val ↔ (SimpleGraph.cycleGraph (extra + 3)).Adj i j

theorem exists_cycleOrder (c : Cycle G) : Nonempty (CycleOrder G c) := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  obtain ⟨v, p, hp, he⟩ := c.property
  let K := cycleSpanningGraph G c
  have hpe : ∀ e, e ∈ p.edges → e ∈ K.edgeSet := by
    intro e hem
    rw [cycleSpanningGraph_edgeSet]
    exact he ▸ List.mem_toFinset.mpr hem
  let q := p.transfer K hpe
  have hq : q.IsCycle := hp.transfer hpe
  let n := p.length - 3
  have hlen : n + 3 = p.length := by have := hp.three_le_length; omega
  have hcontained : SimpleGraph.cycleGraph (n + 3) ⊑ K :=
    (SimpleGraph.cycleGraph_isContained_iff (by omega)).mpr
      ⟨v, q, hq, by simpa only [q, SimpleGraph.Walk.length_transfer] using hlen.symm⟩
  obtain ⟨f⟩ := hcontained
  have fmem (i : Fin (n + 3)) : f i ∈ cycleVertices G c := by
    have hadj : (SimpleGraph.cycleGraph (n + 3)).Adj i (i + 1) := by
      change i + 1 ∈ (SimpleGraph.cycleGraph (n + 3)).neighborSet i
      rw [SimpleGraph.cycleGraph_neighborSet]
      exact Or.inr rfl
    exact mem_cycleVertices_of_mem_edge G c (f.toHom.map_rel hadj) (by simp)
  let f' : Fin (n + 3) → (cycleVertices G c) := fun i => ⟨f i, fmem i⟩
  have hfi : Function.Injective f' :=
    fun i j hij => f.injective (congrArg Subtype.val hij)
  have hlength : n + 3 = c.val.card := by
    rw [← he, List.toFinset_card_of_nodup hp.isTrail.edges_nodup, p.length_edges]
    exact hlen
  have hfs : Function.Surjective f' := by
    by_contra hns
    have hlt := Fintype.card_lt_of_injective_not_surjective f' hfi hns
    simp only [Fintype.card_fin, Fintype.card_coe, cycleVertices_card_eq G c] at hlt
    omega
  let e := Equiv.ofBijective f' ⟨hfi, hfs⟩
  have hiff (i j : Fin (n + 3)) :
      s((e i).val, (e j).val) ∈ c.val ↔ (SimpleGraph.cycleGraph (n + 3)).Adj i j := by
    change K.Adj (f i) (f j) ↔ _
    constructor
    · intro hij
      let g := f.mapNeighborSet i
      have hs : Fintype.card ((SimpleGraph.cycleGraph (n + 3)).neighborSet i) = 2 := by
        rw [SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.cycleGraph_degree_three_le]
      have ht : Fintype.card (K.neighborSet (f i)) = 2 := by
        rw [Set.fintypeCard_eq_ncard]
        exact cycleNeighborSet_ncard G c (fmem i)
      have hgs : Function.Surjective g := by
        by_contra hng
        have hlt := Fintype.card_lt_of_injective_not_surjective g g.injective hng
        omega
      obtain ⟨z, hz⟩ := hgs ⟨f j, hij⟩
      have hzj : z.val = j := f.injective (congrArg Subtype.val hz)
      exact hzj ▸ z.property
    · exact f.toHom.map_rel
  exact ⟨⟨n, hlength, e, hiff⟩⟩

namespace CycleOrder

variable {G} {c : Cycle G}

def shift (O : CycleOrder G c) (a : Fin (O.extra + 3)) : CycleOrder G c where
  extra := O.extra
  length_eq := O.length_eq
  vertex :=
    ({ toFun := fun i => i + a
       invFun := fun i => i - a
       left_inv := fun i => add_sub_cancel_right i a
       right_inv := fun i => sub_add_cancel i a } : Fin (O.extra + 3) ≃ Fin (O.extra + 3)).trans O.vertex
  adj_iff i j := by
    change s((O.vertex (i + a)).val, (O.vertex (j + a)).val) ∈ c.val ↔ _
    simpa only [SimpleGraph.cycleGraph_adj, add_sub_add_right_eq_sub]
      using O.adj_iff (i + a) (j + a)

def reflect (O : CycleOrder G c) (a : Fin (O.extra + 3)) : CycleOrder G c where
  extra := O.extra
  length_eq := O.length_eq
  vertex :=
    ({ toFun := fun i => a - i
       invFun := fun i => a - i
       left_inv := fun i => sub_sub_cancel a i
       right_inv := fun i => sub_sub_cancel a i } : Fin (O.extra + 3) ≃ Fin (O.extra + 3)).trans O.vertex
  adj_iff i j := by
    change s((O.vertex (a - i)).val, (O.vertex (a - j)).val) ∈ c.val ↔ _
    simpa only [SimpleGraph.cycleGraph_adj, sub_sub_sub_cancel_left, or_comm]
      using O.adj_iff (a - i) (a - j)

/-- Choose the cyclic order so that a prescribed directed cycle edge is
the edge from index zero to index one. -/
theorem orient_edge (O : CycleOrder G c) (x y : cycleVertices G c)
    (hxy : s(x.val, y.val) ∈ c.val) :
    ∃ Q : CycleOrder G c, Q.vertex 0 = x ∧ Q.vertex 1 = y := by
  let a := O.vertex.symm x
  let b := O.vertex.symm y
  have hab : (SimpleGraph.cycleGraph (O.extra + 3)).Adj a b := by
    apply (O.adj_iff a b).mp
    simpa only [a, b, Equiv.apply_symm_apply] using hxy
  have hb : b = a - 1 ∨ b = a + 1 := by
    change b ∈ (SimpleGraph.cycleGraph (O.extra + 3)).neighborSet a at hab
    rw [SimpleGraph.cycleGraph_neighborSet] at hab
    exact hab
  rcases hb with hb | hb
  · refine ⟨O.reflect a, ?_, ?_⟩
    · change O.vertex (a - 0) = x
      simpa only [sub_zero] using O.vertex.apply_symm_apply x
    · change O.vertex (a - 1) = y
      rw [← hb]
      exact O.vertex.apply_symm_apply y
  · refine ⟨O.shift a, ?_, ?_⟩
    · change O.vertex (0 + a) = x
      simpa only [zero_add] using O.vertex.apply_symm_apply x
    · change O.vertex (1 + a) = y
      rw [add_comm (1 : Fin (O.extra + 3)) a, ← hb]
      exact O.vertex.apply_symm_apply y

end CycleOrder

/-- The two distinct marked cycle edges sharing a reticulation vertex
become the two edges incident to index zero, in the prescribed Boolean
order. This is the exact graph interface used for the two sunlet terms. -/
theorem exists_cycleOrder_marked (c : Cycle G) (e₀ e₁ : Sym2 V)
    (h₀ : e₀ ∈ c.val) (h₁ : e₁ ∈ c.val) (hne : e₀ ≠ e₁)
    (hcommon : ∃ x, x ∈ e₀ ∧ x ∈ e₁) :
    ∃ Q : CycleOrder G c,
      e₀ = s((Q.vertex 0).val, (Q.vertex 1).val) ∧
      e₁ = s((Q.vertex 0).val, (Q.vertex (-1)).val) := by
  obtain ⟨x, hx₀, hx₁⟩ := hcommon
  obtain ⟨y₀, hy₀⟩ := Sym2.mem_iff_exists.mp hx₀
  obtain ⟨y₁, hy₁⟩ := Sym2.mem_iff_exists.mp hx₁
  have hx : x ∈ cycleVertices G c := mem_cycleVertices_of_mem_edge G c h₀ hx₀
  have hy₀mem : y₀ ∈ cycleVertices G c :=
    mem_cycleVertices_of_mem_edge G c h₀ (by rw [hy₀]; simp)
  have hy₁mem : y₁ ∈ cycleVertices G c :=
    mem_cycleVertices_of_mem_edge G c h₁ (by rw [hy₁]; simp)
  obtain ⟨O⟩ := exists_cycleOrder G c
  obtain ⟨Q, hQ₀, hQ₁⟩ := O.orient_edge ⟨x, hx⟩ ⟨y₀, hy₀mem⟩ (hy₀ ▸ h₀)
  have hyne : y₀ ≠ y₁ := by
    intro h
    exact hne (hy₀.trans ((congrArg (fun y => s(x, y)) h).trans hy₁.symm))
  let b := Q.vertex.symm ⟨y₁, hy₁mem⟩
  have hAdj : (SimpleGraph.cycleGraph (Q.extra + 3)).Adj 0 b := by
    apply (Q.adj_iff 0 b).mp
    simpa only [hQ₀, b, Equiv.apply_symm_apply] using (hy₁ ▸ h₁)
  have hb : b = -1 ∨ b = 1 := by
    change b ∈ (SimpleGraph.cycleGraph (Q.extra + 3)).neighborSet 0 at hAdj
    rw [SimpleGraph.cycleGraph_neighborSet] at hAdj
    simpa only [zero_sub, zero_add, Set.mem_insert_iff, Set.mem_singleton_iff] using hAdj
  have hbneg : b = -1 := hb.resolve_right (by
    intro hb1
    have hy : (⟨y₁, hy₁mem⟩ : cycleVertices G c) = ⟨y₀, hy₀mem⟩ := by
      calc
        _ = Q.vertex b := (Q.vertex.apply_symm_apply _).symm
        _ = Q.vertex 1 := congrArg Q.vertex hb1
        _ = _ := hQ₁
    exact hyne (congrArg Subtype.val hy).symm)
  refine ⟨Q, ?_, ?_⟩
  · simpa only [hQ₀, hQ₁] using hy₀
  · have hQlast : Q.vertex (-1) = (⟨y₁, hy₁mem⟩ : cycleVertices G c) := by
      rw [← hbneg]
      exact Q.vertex.apply_symm_apply _
    simpa only [hQ₀, hQlast] using hy₁

end CyclicOrders

section EdgeInterfaces

variable [DecidableEq V]

def inducedEdgeEmbedding (s : Set V) : (G.induce s).edgeSet ↪ G.edgeSet :=
  (SimpleGraph.Embedding.induce s).toCopy.mapEdgeSet

theorem inducedEdge_vertex {s : Set V} (e : (G.induce s).edgeSet) {x : V}
    (hx : x ∈ (inducedEdgeEmbedding G s e).val) : x ∈ s := by
  obtain ⟨y, hy, he⟩ := Sym2.mem_map.mp hx
  exact he ▸ y.property

theorem exists_inducedCycleEdge (s : Set V) (c : Cycle (G.induce s)) (e : G.edgeSet)
    (he : e.val ∈ (cycleMapInduce G s c).val) :
    ∃ d : (G.induce s).edgeSet, d.val ∈ c.val ∧ inducedEdgeEmbedding G s d = e := by
  obtain ⟨d, hd, hde⟩ := Finset.mem_map.mp he
  refine ⟨⟨d, cycle_edges_subset (G.induce s) c hd⟩, hd, Subtype.ext hde⟩

/-- Lift a marked edge belonging to an induced cycle. This is the
canonical transport used for the reticulation pairs under a bridge cut. -/
def inducedCycleEdge (s : Set V) (c : Cycle (G.induce s)) (e : G.edgeSet)
    (he : e.val ∈ (cycleMapInduce G s c).val) : (G.induce s).edgeSet :=
  Classical.choose (exists_inducedCycleEdge G s c e he)

theorem inducedCycleEdge_mem (s : Set V) (c : Cycle (G.induce s)) (e : G.edgeSet)
    (he : e.val ∈ (cycleMapInduce G s c).val) :
    (inducedCycleEdge G s c e he).val ∈ c.val :=
  (Classical.choose_spec (exists_inducedCycleEdge G s c e he)).1

@[simp] theorem inducedCycleEdge_map (s : Set V) (c : Cycle (G.induce s)) (e : G.edgeSet)
    (he : e.val ∈ (cycleMapInduce G s c).val) :
    inducedEdgeEmbedding G s (inducedCycleEdge G s c e he) = e :=
  (Classical.choose_spec (exists_inducedCycleEdge G s c e he)).2

theorem inducedEdges_common_vertex (s : Set V) (e f : (G.induce s).edgeSet)
    (h : ∃ x : V, x ∈ (inducedEdgeEmbedding G s e).val ∧
      x ∈ (inducedEdgeEmbedding G s f).val) :
    ∃ x : s, x ∈ e.val ∧ x ∈ f.val := by
  obtain ⟨x, hxe, hxf⟩ := h
  obtain ⟨a, hae, hax⟩ := Sym2.mem_map.mp hxe
  obtain ⟨b, hbf, hbx⟩ := Sym2.mem_map.mp hxf
  have hab : a = b := Subtype.ext (hax.trans hbx.symm)
  exact ⟨a, hae, hab.symm ▸ hbf⟩

variable (u v : V)

abbrev CoreEdge := (G.induce (cutSide G u v)).edgeSet

def coreVertexEquiv (hG : G.Connected) (hb : G.IsBridge s(u, v)) :
    (cutSide G u v) ⊕ (cutSide G v u) ≃ V := by
  classical
  refine
    { toFun := Sum.elim Subtype.val Subtype.val
      invFun := fun x => if hx : x ∈ cutSide G u v then Sum.inl ⟨x, hx⟩
        else Sum.inr ⟨x, (cutSide_swap_iff G u v hG hb x).mpr hx⟩
      left_inv := ?_
      right_inv := ?_ }
  · rintro (x | x)
    · dsimp only
      simp only [Sum.elim_inl]
      exact dite_eq_left x.property
    · have hx := (cutSide_swap_iff G u v hG hb x).mp x.property
      dsimp only
      simp only [Sum.elim_inr]
      exact dite_eq_right hx
  · intro x
    dsimp only
    split_ifs <;> rfl

theorem coreEdge_ne_bridge (hb : G.IsBridge s(u, v)) (e : CoreEdge G u v) :
    (inducedEdgeEmbedding G (cutSide G u v) e).val ≠ s(u, v) := by
  intro he
  have hv : v ∈ (inducedEdgeEmbedding G (cutSide G u v) e).val := by rw [he]; simp
  exact end_not_mem_cutSide G u v hb (inducedEdge_vertex G e hv)

theorem coreEdges_distinct (hG : G.Connected) (hb : G.IsBridge s(u, v))
    (e : CoreEdge G u v) (f : CoreEdge G v u) :
    inducedEdgeEmbedding G (cutSide G u v) e ≠
      inducedEdgeEmbedding G (cutSide G v u) f := by
  intro he
  let x := (inducedEdgeEmbedding G (cutSide G u v) e).val.out.1
  have hx : x ∈ (inducedEdgeEmbedding G (cutSide G u v) e).val := Sym2.out_fst_mem _
  have hxL := inducedEdge_vertex G e hx
  have hxR := inducedEdge_vertex G f (he ▸ hx)
  exact (cutSide_swap_iff G u v hG hb x).mp hxR hxL

def coreEdgeSumMap (hadj : G.Adj u v) : Option (CoreEdge G u v ⊕ CoreEdge G v u) → G.edgeSet
  | none => ⟨s(u, v), hadj⟩
  | some (Sum.inl e) => inducedEdgeEmbedding G (cutSide G u v) e
  | some (Sum.inr e) => inducedEdgeEmbedding G (cutSide G v u) e

/-- All original edges consist of the internal edges of the two
components and one bridge. The correspondence uses actual edge sets. -/
def coreEdgeEquiv (hG : G.Connected) (hadj : G.Adj u v) (hb : G.IsBridge s(u, v)) :
    Option (CoreEdge G u v ⊕ CoreEdge G v u) ≃ G.edgeSet := by
  have hb' : G.IsBridge s(v, u) := by simpa only [Sym2.eq_swap] using hb
  refine Equiv.ofBijective (coreEdgeSumMap G u v hadj) ⟨?_, ?_⟩
  · rintro (_ | (e | e)) (_ | (f | f)) he
    · rfl
    · exact (coreEdge_ne_bridge G u v hb f (congrArg Subtype.val he).symm).elim
    · have h := coreEdge_ne_bridge G v u hb' f
      exact (h (by simpa only [coreEdgeSumMap, Sym2.eq_swap] using (congrArg Subtype.val he).symm)).elim
    · exact (coreEdge_ne_bridge G u v hb e (congrArg Subtype.val he)).elim
    · exact congrArg (fun z => some (Sum.inl z))
        ((inducedEdgeEmbedding G (cutSide G u v)).injective he)
    · exact (coreEdges_distinct G u v hG hb e f he).elim
    · have h := coreEdge_ne_bridge G v u hb' e
      exact (h (by simpa only [coreEdgeSumMap, Sym2.eq_swap] using congrArg Subtype.val he)).elim
    · exact (coreEdges_distinct G u v hG hb f e he.symm).elim
    · exact congrArg (fun z => some (Sum.inr z))
        ((inducedEdgeEmbedding G (cutSide G v u)).injective he)
  · rintro ⟨e, he⟩
    revert he
    refine Sym2.ind ?_ e
    intro x y hxy
    by_cases hedge : s(x, y) = s(u, v)
    · exact ⟨none, Subtype.ext hedge.symm⟩
    · by_cases hx : x ∈ cutSide G u v
      · have hy : y ∈ cutSide G u v := by
          by_contra hy
          obtain ⟨hxu, hyv⟩ := crossing_edge G u v hb hx hy hxy
          exact hedge (by rw [hxu, hyv])
        exact ⟨some (Sum.inl ⟨s(⟨x, hx⟩, ⟨y, hy⟩), hxy⟩), rfl⟩
      · have hx' := (cutSide_swap_iff G u v hG hb x).mpr hx
        have hy' : y ∈ cutSide G v u := by
          by_contra hy
          obtain ⟨hxv, hyu⟩ := crossing_edge G v u hb' hx' hy hxy
          exact hedge (by rw [hxv, hyu]; exact Sym2.eq_swap)
        exact ⟨some (Sum.inr ⟨s(⟨x, hx'⟩, ⟨y, hy'⟩), hxy⟩), rfl⟩

def coreToCutEmbedding : (G.induce (cutSide G u v)) ↪g cutGraph G u v :=
  G.induceHomOfLE (fun _ hx => Or.inl hx)

def cutEdgeMap (hadj : G.Adj u v) : Option (CoreEdge G u v) → (cutGraph G u v).edgeSet
  | none => ⟨s(⟨u, start_mem_cutVertices G u v⟩, ⟨v, end_mem_cutVertices G u v⟩), hadj⟩
  | some e => (coreToCutEmbedding G u v).toCopy.mapEdgeSet e

@[simp] theorem induced_cutEdgeMap_none (hadj : G.Adj u v) :
    inducedEdgeEmbedding G (cutVertices G u v) (cutEdgeMap G u v hadj none) =
      (⟨s(u, v), hadj⟩ : G.edgeSet) := rfl

@[simp] theorem induced_cutEdgeMap_some (hadj : G.Adj u v) (e : CoreEdge G u v) :
    inducedEdgeEmbedding G (cutVertices G u v) (cutEdgeMap G u v hadj (some e)) =
      inducedEdgeEmbedding G (cutSide G u v) e := by
  apply Subtype.ext
  change Sym2.map Subtype.val (Sym2.map _ e.val) = Sym2.map Subtype.val e.val
  rw [Sym2.map_map]
  rfl

/-- Cutting replaces the unique bridge by a single new pendant edge;
every other edge is literally an edge of the retained component. -/
def cutEdgeEquiv (hadj : G.Adj u v) (hb : G.IsBridge s(u, v)) :
    Option (CoreEdge G u v) ≃ (cutGraph G u v).edgeSet := by
  refine Equiv.ofBijective (cutEdgeMap G u v hadj) ⟨?_, ?_⟩
  · rintro (_ | e) (_ | f) he
    · rfl
    · have h := congrArg (inducedEdgeEmbedding G (cutVertices G u v)) he
      simp only [induced_cutEdgeMap_none, induced_cutEdgeMap_some] at h
      exact (coreEdge_ne_bridge G u v hb f (congrArg Subtype.val h).symm).elim
    · have h := congrArg (inducedEdgeEmbedding G (cutVertices G u v)) he
      simp only [induced_cutEdgeMap_none, induced_cutEdgeMap_some] at h
      exact (coreEdge_ne_bridge G u v hb e (congrArg Subtype.val h)).elim
    · exact congrArg some ((coreToCutEmbedding G u v).toCopy.mapEdgeSet.injective he)
  · rintro ⟨e, he⟩
    revert he
    refine Sym2.ind ?_ e
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact ⟨some ⟨s(⟨x, hx⟩, ⟨y, hy⟩), hxy⟩, rfl⟩
    · subst y
      have hxu := boundary_neighbor_eq G u v hb (Or.inl hx) hxy.symm
      subst x
      exact ⟨none, rfl⟩
    · subst x
      have hyu := boundary_neighbor_eq G u v hb (Or.inl hy) hxy
      subst y
      refine ⟨none, Subtype.ext ?_⟩
      exact Sym2.eq_swap
    · subst x
      subst y
      exact (G.irrefl hxy).elim

end EdgeInterfaces

universe u

/-- Structural induction for the graphs in Corollary 8.1. Each recursive
step is an actual internal bridge cut; both vertex types strictly
decrease. The three terminal models are exposed by the concrete star
and simple-cycle sunlet presentations above. -/
theorem binaryCactus_induction
    (P : {W : Type u} → [Finite W] → [DecidableEq W] → SimpleGraph W → Prop)
    (hstar : ∀ {W : Type u} [Finite W] [DecidableEq W] (H : SimpleGraph W),
      IsBinaryCactus H → ∀ center, StarPresentation H center → P H)
    (hsunlet : ∀ {W : Type u} [Finite W] [DecidableEq W] (H : SimpleGraph W),
      IsBinaryCactus H → ∀ c : Cycle H, SunletPresentation H c → P H)
    (hcut : ∀ {W : Type u} [Finite W] [DecidableEq W] (H : SimpleGraph W),
      IsBinaryCactus H → ∀ x y, IsInternalBridge H x y →
        P (cutGraph H x y) → P (cutGraph H y x) → P H)
    {W : Type u} [Finite W] [DecidableEq W] (H : SimpleGraph W)
    (hH : IsBinaryCactus H) : P H := by
  have main : ∀ n : ℕ, ∀ {W : Type u} [Finite W] [DecidableEq W] (H : SimpleGraph W),
      Nat.card W = n → IsBinaryCactus H → P H := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ _ H hcard hH
      by_cases hb : ∃ x y, IsInternalBridge H x y
      · obtain ⟨x, y, hxy⟩ := hb
        obtain ⟨hadj, hbridge, hx3, hy3⟩ := hxy
        have hbridge' : H.IsBridge s(y, x) := by simpa only [Sym2.eq_swap] using hbridge
        have hL : Nat.card (cutVertices H x y) < n :=
          (cutGraph_card_lt H x y hbridge hy3).trans_eq hcard
        have hR : Nat.card (cutVertices H y x) < n :=
          (cutGraph_card_lt H y x hbridge' hx3).trans_eq hcard
        exact hcut H hH x y ⟨hadj, hbridge, hx3, hy3⟩
          (ih _ hL _ rfl (cutGraph_isBinaryCactus H hH x y hadj hbridge))
          (ih _ hR _ rfl (cutGraph_isBinaryCactus H hH y x hadj.symm hbridge'))
      · rcases localBlock_of_no_internal H hH hb with ⟨center, hc⟩ | ⟨c, ⟨hc⟩⟩
        · exact hstar H hH center hc
        · exact hsunlet H hH c hc
  exact main (Nat.card W) H rfl hH

theorem binaryCactus_counts {W : Type u} [Finite W] [DecidableEq W]
    (H : SimpleGraph W) (hH : IsBinaryCactus H) :
    edgeCount H + 3 = 2 * leafCount H + 3 * cycleCount H ∧ 2 ≤ leafCount H := by
  refine binaryCactus_induction (P := fun {_} _ _ K =>
    edgeCount K + 3 = 2 * leafCount K + 3 * cycleCount K ∧ 2 ≤ leafCount K)
    ?_ ?_ ?_ H hH
  · intro W _ _ K hK center P
    exact P.counts hK.binary
  · intro W _ _ K hK c P
    exact P.counts hK
  · intro W _ _ K hK x y hxy hL hR
    obtain ⟨hadj, hb, hx, hy⟩ := hxy
    have he := cut_edgeCounts K x y hK.connected hadj hb
    have hn := cut_leafCounts K x y hK.connected hadj hb
    have hc := cut_cycleCounts K x y hK.connected hb
    omega

/-- The paper's edge-count identity, derived from genuine graph
decomposition and the degree hypotheses. -/
theorem binaryCactus_edgeCount {W : Type u} [Finite W] [DecidableEq W]
    (H : SimpleGraph W) (hH : IsBinaryCactus H) :
    edgeCount H = 2 * leafCount H - 3 + 3 * cycleCount H := by
  obtain ⟨h, hn⟩ := binaryCactus_counts H hH
  omega

end Sunlet.NetworkGraphDecomposition
end
end NetworkStageSource_Sunlet_NetworkGraphDecomposition
#eval IO.println "NETWORK_CHAPTER_COMPLETE Sunlet.NetworkGraphDecomposition"

section NetworkStageSource_Sunlet_NetworkFlowGluing


/-!
# Leaf flows at a cut edge

A cut replaces the edge by one new leaf on each component. The two new
leaf labels have opposite signs. This module constructs the exact bijection
of zero-sum leaf flows and identifies orbit-class matching with genuine
group-label matching, using the group action on all leaf labels.
-/

noncomputable section
open scoped BigOperators

namespace Sunlet.NetworkFlowGluing

variable {G L R C K P Q : Type*} [AddCommGroup G]
  [Fintype L] [Fintype R]

/-- Every leaf assignment satisfying the Fourier conservation law. -/
abbrev Flow (L G : Type*) [Fintype L] [AddCommGroup G] :=
  {g : L → G // ∑ i,g i=0}

def leftFlow (g : Flow (L ⊕ R) G) : Flow (Option L) G :=
  ⟨fun i => match i with
    | none => -(∑ l,g.val (.inl l))
    | some l => g.val (.inl l),by simp [Fintype.sum_option]⟩

def rightFlow (g : Flow (L ⊕ R) G) : Flow (Option R) G :=
  ⟨fun i => match i with
    | none => -(∑ r,g.val (.inr r))
    | some r => g.val (.inr r),by simp [Fintype.sum_option]⟩

theorem cut_labels_opposite (g : Flow (L ⊕ R) G) :
    (leftFlow g).val none = -(rightFlow g).val none := by
  have h := g.property
  rw [Fintype.sum_sum_type] at h
  change -(∑ l,g.val (.inl l)) = -(-(∑ r,g.val (.inr r)))
  simpa using (neg_eq_iff_add_eq_zero.mpr h)

abbrev MatchedFlow (L R G : Type*) [Fintype L] [Fintype R] [AddCommGroup G] :=
  {p : Flow (Option L) G × Flow (Option R) G // p.1.val none = -p.2.val none}

def joinFlow (p : MatchedFlow L R G) : Flow (L ⊕ R) G := by
  refine ⟨Sum.elim (fun l => p.val.1.val (some l))
    (fun r => p.val.2.val (some r)),?_⟩
  have hL := p.val.1.property
  have hR := p.val.2.property
  rw [Fintype.sum_option] at hL hR
  rw [Fintype.sum_sum_type]
  have hsL : (∑ l,p.val.1.val (some l)) = -p.val.1.val none :=
    eq_neg_of_add_eq_zero_right hL
  have hsR : (∑ r,p.val.2.val (some r)) = -p.val.2.val none :=
    eq_neg_of_add_eq_zero_right hR
  simp only [Sum.elim_inl,Sum.elim_inr,hsL,hsR,p.property,neg_neg,add_neg_cancel]

/-- This is a bijection of the complete Fourier coordinate index sets. -/
def cutFlowEquiv : Flow (L ⊕ R) G ≃ MatchedFlow L R G where
  toFun g := ⟨(leftFlow g,rightFlow g),cut_labels_opposite g⟩
  invFun := joinFlow
  left_inv g := by
    apply Subtype.ext
    funext i
    cases i <;> rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      funext i
      cases i with
      | none =>
          have h := p.val.1.property
          rw [Fintype.sum_option] at h
          exact (eq_neg_of_add_eq_zero_left h).symm
      | some l => rfl
    · apply Subtype.ext
      funext i
      cases i with
      | none =>
          have h := p.val.2.property
          rw [Fintype.sum_option] at h
          exact (eq_neg_of_add_eq_zero_left h).symm
      | some r => rfl

/-- Relabelling all leaves by a group automorphism preserves the Fourier
conservation law. -/
def mapFlow {T : Type*} [Fintype T] (φ : G ≃+ G) (g : Flow T G) : Flow T G :=
  ⟨fun i => φ (g.val i),by rw [← map_sum,g.property,map_zero]⟩

@[simp] theorem mapFlow_apply {T : Type*} [Fintype T]
    (φ : G ≃+ G) (g : Flow T G) (i : T) :
    (mapFlow φ g).val i = φ (g.val i) := rfl

variable [CommSemiring K]

/-- Coordinates after cutting are products of coordinates in disjoint
edge-parameter sets. The duplicated cut-edge parameters are retained. -/
def gluedCoordinate
    (p : Flow (Option L) G → MvPolynomial P K)
    (q : Flow (Option R) G → MvPolynomial Q K)
    (g : Flow (L ⊕ R) G) : MvPolynomial (P ⊕ Q) K :=
  MvPolynomial.rename Sum.inl (p (leftFlow g)) *
    MvPolynomial.rename Sum.inr (q (rightFlow g))

def pairedCoordinate
    (p : Flow (Option L) G → MvPolynomial P K)
    (q : Flow (Option R) G → MvPolynomial Q K)
    (g : Flow (Option L) G × Flow (Option R) G) : MvPolynomial (P ⊕ Q) K :=
  MvPolynomial.rename Sum.inl (p g.1) * MvPolynomial.rename Sum.inr (q g.2)

abbrev ClassMatched (c : G → C) :=
  {p : Flow (Option L) G × Flow (Option R) G //
    c (p.1.val none) = c (-p.2.val none)}

/-- If class equality means an orbit under class-preserving automorphisms,
every class-matched pair can be made group-matched without changing its
coordinate polynomial. This includes arbitrary automorphism subgroups,
whether or not they contain negation. -/
theorem classMatched_range_eq_glued_range
    (c : G → C)
    (horbit : ∀ a b,c a=c b → ∃ φ : G ≃+ G,(∀ x,c (φ x)=c x) ∧ φ a=b)
    (p : Flow (Option L) G → MvPolynomial P K)
    (q : Flow (Option R) G → MvPolynomial Q K)
    (hq : ∀ (φ : G ≃+ G),(∀ x,c (φ x)=c x) →
      ∀ g,q (mapFlow φ g)=q g) :
    Set.range (fun g : ClassMatched (L := L) (R := R) c => pairedCoordinate p q g.val) =
      Set.range (gluedCoordinate p q) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨g,rfl⟩
    obtain ⟨φ,hφ,hmatch⟩ := horbit (-g.val.2.val none) (g.val.1.val none) g.property.symm
    let h : MatchedFlow L R G := ⟨(g.val.1,mapFlow φ g.val.2),by
      change g.val.1.val none = -φ (g.val.2.val none)
      simpa only [map_neg] using hmatch.symm⟩
    refine ⟨cutFlowEquiv.symm h,?_⟩
    have he := congrArg Subtype.val (cutFlowEquiv.apply_symm_apply h)
    change (leftFlow (cutFlowEquiv.symm h),rightFlow (cutFlowEquiv.symm h)) =
      (g.val.1,mapFlow φ g.val.2) at he
    simp only [gluedCoordinate,pairedCoordinate,Prod.mk.injEq] at *
    rw [he.1,he.2,hq φ hφ]
  · rintro _ ⟨g,rfl⟩
    refine ⟨⟨(leftFlow g,rightFlow g),congrArg c (cut_labels_opposite g)⟩,rfl⟩

end Sunlet.NetworkFlowGluing
end
end NetworkStageSource_Sunlet_NetworkFlowGluing
#eval IO.println "NETWORK_CHAPTER_COMPLETE Sunlet.NetworkFlowGluing"

section NetworkStageSource_Sunlet_NetworkFourierMonomials


/-! Elementary identities for literal finite Fourier monomial sums.
These statements use only polynomial algebra, independently of the
later differential dimension comparison. -/

noncomputable section
open scoped BigOperators

namespace Sunlet.NetworkFourierTerms

variable {K P Q O I J C : Type*} [CommSemiring K] [Fintype I]

def coordinate (a : I → O → P →₀ ℕ) (o : O) : MvPolynomial P K :=
  ∑ i,MvPolynomial.monomial (a i o) 1

@[simp] theorem coordinate_at_one (a : I → O → P →₀ ℕ) (o : O) :
    MvPolynomial.aeval (fun _ : P => (1 : K)) (coordinate (K := K) a o)=
      (Fintype.card I : K) := by
  simp [coordinate,MvPolynomial.aeval_monomial]

/-- There is no cancellation among the actual displayed-tree terms in
characteristic zero, including repeated monomials. -/
theorem coordinate_ne_zero [CharZero K] [Nonempty I]
    (a : I → O → P →₀ ℕ) (o : O) : coordinate (K := K) a o≠0 := by
  intro h
  have hh := congrArg (MvPolynomial.aeval (fun _ : P => (1 : K))) h
  rw [coordinate_at_one,map_zero] at hh
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero hh

theorem coordinate_relabel (a : I → O → P →₀ ℕ) (σ : O → O)
    (hσ : ∀ i o,a i (σ o)=a i o) (o : O) :
    coordinate (K := K) a (σ o)=coordinate a o := by
  simp only [coordinate,hσ]

/-- Every tree term contains exactly one parameter from the cut-leaf
class family. This is the precise grading used in the dimension proof. -/
theorem euler_coordinate [DecidableEq C] [DecidableEq P]
    (a : I → O → P →₀ ℕ) (leaf : C → P) (label : O → C)
    (hdegree : ∀ i o c,a i o (leaf c)=if c=label o then 1 else 0)
    (o : O) (c : C) :
    MvPolynomial.X (leaf c)*MvPolynomial.pderiv (leaf c) (coordinate (K := K) a o)=
      if c=label o then coordinate a o else 0 := by
  simp only [coordinate,map_sum,Finset.mul_sum,MvPolynomial.X_mul_pderiv_monomial,hdegree]
  split_ifs <;> simp

def pairExponent (a : I → O → P →₀ ℕ) (b : J → O → Q →₀ ℕ)
    (ij : I × J) (o : O) : (P ⊕ Q) →₀ ℕ :=
  (a ij.1 o).mapDomain Sum.inl+(b ij.2 o).mapDomain Sum.inr

/-- A displayed-tree choice on each side gives the product of the two
component coordinates. This is an equality of the original polynomials. -/
theorem coordinate_pairExponent [Fintype J]
    (a : I → O → P →₀ ℕ) (b : J → O → Q →₀ ℕ) (o : O) :
    coordinate (K := K) (pairExponent a b) o =
      MvPolynomial.rename Sum.inl (coordinate a o)*
        MvPolynomial.rename Sum.inr (coordinate b o) := by
  simp only [coordinate,pairExponent,map_sum,MvPolynomial.rename_monomial,
    Finset.sum_mul_sum,Fintype.sum_prod_type,MvPolynomial.monomial_mul_monomial,one_mul]

end Sunlet.NetworkFourierTerms
end
end NetworkStageSource_Sunlet_NetworkFourierMonomials
#eval IO.println "NETWORK_CHAPTER_COMPLETE Sunlet.NetworkFourierMonomials"

section NetworkStageSource_Sunlet_NetworkIncidenceFlows


/-!
# The literal Fourier flow sum on a finite incidence network

For each displayed-tree choice, an edge labelling is retained precisely
when it satisfies conservation at every vertex and is zero on deleted
edges. Its term is the product of the active edge-class variables. This
definition retains the actual graph edges and every zero-sum leaf
assignment. The cut-flux calculation below is a finite sum identity.
-/

noncomputable section
open scoped BigOperators

namespace Sunlet.NetworkIncidenceFlows

variable {V E L S G C K : Type*} [Fintype V] [Fintype E] [Fintype L] [Fintype S]
  [DecidableEq V] [DecidableEq E] [AddCommGroup G] [Fintype G] [DecidableEq G]
  [DecidableEq C]

/-- Endpoint and leaf data, together with the edges retained by each
displayed-tree choice. Graph hypotheses are added by the graph model. -/
structure Data (V E L S : Type*) [Fintype E] where
  source : E → V
  target : E → V
  leaf : L → V
  active : S → Finset E

def divergence (source target : E → V) (x : E → G) (v : V) : G :=
  (∑ e,if source e=v then x e else 0)-(∑ e,if target e=v then x e else 0)

def leafBoundary (leaf : L → V) (g : L → G) (v : V) : G :=
  ∑ l,if leaf l=v then g l else 0

theorem sum_divergence (source target : E → V) (x : E → G) :
    ∑ v,divergence source target x v=0 := by
  simp only [divergence,Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun v e => if source e=v then x e else 0),
    Finset.sum_comm (f := fun v e => if target e=v then x e else 0)]
  simp

theorem sum_leafBoundary (leaf : L → V) (g : L → G) :
    ∑ v,leafBoundary leaf g v=∑ l,g l := by
  simp only [leafBoundary]
  rw [Finset.sum_comm]
  simp

theorem sum_divergence_on (source target : E → V) (x : E → G) (U : Finset V) :
    ∑ v∈U,divergence source target x v=
      ∑ e,((if source e∈U then x e else 0)-(if target e∈U then x e else 0)) := by
  simp only [divergence,Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun v e => if source e=v then x e else 0),
    Finset.sum_comm (f := fun v e => if target e=v then x e else 0)]
  simp

theorem sum_leafBoundary_on (leaf : L → V) (g : L → G) (U : Finset V) :
    ∑ v∈U,leafBoundary leaf g v=∑ l,if leaf l∈U then g l else 0 := by
  simp only [leafBoundary]
  rw [Finset.sum_comm]
  simp

/-- Conservation determines the label of a bridge from the leaves on
one side of the cut. -/
theorem cut_flux (source target : E → V) (leaf : L → V)
    (x : E → G) (g : L → G) (U : Finset V) (e₀ : E)
    (hs : source e₀∈U) (ht : target e₀∉U)
    (hcut : ∀ e,e≠e₀ → (source e∈U ↔ target e∈U))
    (hconserve : ∀ v,divergence source target x v=leafBoundary leaf g v) :
    x e₀=∑ l,if leaf l∈U then g l else 0 := by
  have he : (∑ e,((if source e∈U then x e else 0)-
      (if target e∈U then x e else 0)))=x e₀ := by
    rw [Finset.sum_eq_single e₀]
    · simp [hs,ht]
    · intro e he hne
      simp [hcut e hne]
    · simp
  rw [← he,← sum_divergence_on]
  simp_rw [hconserve]
  exact sum_leafBoundary_on leaf g U

def Valid (N : Data V E L S) (g : L → G) (s : S) (x : E → G) : Prop :=
  (∀ e,e∉N.active s → x e=0) ∧
    ∀ v,divergence N.source N.target x v=leafBoundary N.leaf g v

abbrev Term (N : Data V E L S) (g : L → G) :=
  {sx : S × (E → G) // Valid N g sx.1 sx.2}

instance (N : Data V E L S) (g : L → G) : Fintype (Term N g) :=
  Fintype.ofFinite (Term N g)

def exponent (N : Data V E L S) (q : G → C) {g : L → G} (t : Term N g) :
    (E × C) →₀ ℕ :=
  ∑ e∈N.active t.val.1,Finsupp.single (e,q (t.val.2 e)) 1

variable [CommSemiring K]

def termPolynomial (N : Data V E L S) (q : G → C) {g : L → G} (t : Term N g) :
    MvPolynomial (E × C) K := MvPolynomial.monomial (exponent N q t) 1

theorem termPolynomial_eq_prod (N : Data V E L S) (q : G → C) {g : L → G}
    (t : Term N g) : termPolynomial (K := K) N q t=
      ∏ e∈N.active t.val.1,MvPolynomial.X (e,q (t.val.2 e)) := by
  simp [termPolynomial,exponent,MvPolynomial.monomial_sum_one,MvPolynomial.X]

/-- The displayed-tree Fourier polynomial, including every allowed edge
flow. For a tree the conservation law has one solution, so it is its
usual Fourier monomial. -/
def coordinate (N : Data V E L S) (q : G → C) (g : NetworkFlowGluing.Flow L G) :
    MvPolynomial (E × C) K :=
  ∑ t : Term N g.val,MvPolynomial.monomial (exponent N q t) 1

theorem coordinate_eq_sum_terms (N : Data V E L S) (q : G → C)
    (g : NetworkFlowGluing.Flow L G) : coordinate (K := K) N q g=
      ∑ t : Term N g.val,termPolynomial N q t := rfl

theorem valid_zero_sum (N : Data V E L S) {g : L → G} {s : S} {x : E → G}
    (h : Valid N g s x) : ∑ l,g l=0 := by
  rw [← sum_leafBoundary N.leaf g]
  simp_rw [← h.2]
  exact sum_divergence N.source N.target x

theorem divergence_map (source target : E → V) (φ : G ≃+ G) (x : E → G) (v : V) :
    divergence source target (fun e => φ (x e)) v=φ (divergence source target x v) := by
  simp [divergence,map_sub,map_sum,apply_ite,map_zero]

theorem leafBoundary_map (leaf : L → V) (φ : G ≃+ G) (g : L → G) (v : V) :
    leafBoundary leaf (fun l => φ (g l)) v=φ (leafBoundary leaf g v) := by
  simp [leafBoundary,map_sum,apply_ite,map_zero]

def mapTerm (N : Data V E L S) (φ : G ≃+ G) {g : L → G} (t : Term N g) :
    Term N (fun l => φ (g l)) :=
  ⟨(t.val.1,fun e => φ (t.val.2 e)),by
    constructor
    · intro e he
      change φ (t.val.2 e)=0
      rw [t.property.1 e he,map_zero]
    · intro v
      rw [divergence_map,leafBoundary_map,t.property.2 v]⟩

def mapTermEquiv (N : Data V E L S) (φ : G ≃+ G) (g : L → G) :
    Term N g ≃ Term N (fun l => φ (g l)) where
  toFun := mapTerm N φ
  invFun t := ⟨(t.val.1,fun e => φ.symm (t.val.2 e)),by
    constructor
    · intro e he
      change φ.symm (t.val.2 e)=0
      rw [t.property.1 e he,map_zero]
    · intro v
      apply φ.injective
      rw [← divergence_map,← leafBoundary_map]
      simpa only [φ.apply_symm_apply] using t.property.2 v⟩
  left_inv t := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext e
      exact φ.symm_apply_apply _
  right_inv t := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext e
      exact φ.apply_symm_apply _

/-- Automorphism relabelling changes neither the Fourier coordinate nor
its polynomial parameters when those parameters are orbit classes. -/
theorem coordinate_mapFlow (N : Data V E L S) (q : G → C) (φ : G ≃+ G)
    (hq : ∀ a,q (φ a)=q a) (g : NetworkFlowGluing.Flow L G) :
    coordinate (K := K) N q (NetworkFlowGluing.mapFlow φ g)=coordinate N q g := by
  symm
  apply Fintype.sum_equiv (mapTermEquiv N φ g.val)
  intro t
  simp [exponent,mapTermEquiv,mapTerm,hq]

theorem leafBoundary_at_leaf (leaf : L → V) (hinj : Function.Injective leaf)
    (g : L → G) (l : L) : leafBoundary leaf g (leaf l)=g l := by
  classical
  simp [leafBoundary,hinj.eq_iff]

theorem term_leaf_value (N : Data V E L S) (hinj : Function.Injective N.leaf)
    (l : L) (e₀ : E) (hs : N.source e₀=N.leaf l)
    (hsource : ∀ e,N.source e=N.leaf l → e=e₀)
    (htarget : ∀ e,N.target e≠N.leaf l)
    {g : L → G} (t : Term N g) : t.val.2 e₀=g l := by
  have h := t.property.2 (N.leaf l)
  rw [leafBoundary_at_leaf N.leaf hinj] at h
  have hfirst : (∑ e,if N.source e=N.leaf l then t.val.2 e else 0)=t.val.2 e₀ := by
    rw [Finset.sum_eq_single e₀]
    · simp [hs]
    · intro e he hne
      simp only [ite_eq_right_iff]
      intro h
      exact (hne (hsource e h)).elim
    · simp
  simpa [divergence,hfirst,htarget] using h

theorem term_incoming_leaf_value (N : Data V E L S) (hinj : Function.Injective N.leaf)
    (l : L) (e₀ : E) (ht : N.target e₀=N.leaf l)
    (htarget : ∀ e,N.target e=N.leaf l → e=e₀)
    (hsource : ∀ e,N.source e≠N.leaf l)
    {g : L → G} (t : Term N g) : t.val.2 e₀=-g l := by
  have h := t.property.2 (N.leaf l)
  rw [leafBoundary_at_leaf N.leaf hinj] at h
  have hsecond : (∑ e,if N.target e=N.leaf l then t.val.2 e else 0)=t.val.2 e₀ := by
    rw [Finset.sum_eq_single e₀]
    · simp [ht]
    · intro e he hne
      simp only [ite_eq_right_iff]
      intro h
      exact (hne (htarget e h)).elim
    · simp
  have hneg : -t.val.2 e₀=g l := by simpa [divergence,hsecond,hsource] using h
  exact eq_neg_of_add_eq_zero_left (by rw [← hneg]; exact add_neg_cancel _)

theorem exponent_at_edge (N : Data V E L S) (q : G → C) {g : L → G}
    (t : Term N g) (e : E) (c : C) :
    exponent N q t (e,c)=
      if e∈N.active t.val.1 then (if q (t.val.2 e)=c then 1 else 0) else 0 := by
  classical
  simp only [exponent,Finsupp.finsetSum_apply,Finsupp.single_apply,Prod.mk.injEq]
  have h (e' : E) : (if e'=e ∧ q (t.val.2 e')=c then (1 : ℕ) else 0)=
      if e'=e then (if q (t.val.2 e)=c then 1 else 0) else 0 := by
    by_cases he : e'=e
    · subst e'
      simp
    · simp [he]
  simp_rw [h]
  simp

/-- The original Fourier polynomial has degree one in exactly the class
of each outgoing leaf label, uniformly over all displayed-tree choices. -/
theorem coordinate_leaf_euler (N : Data V E L S) (q : G → C)
    (hinj : Function.Injective N.leaf) (l : L) (e₀ : E)
    (hs : N.source e₀=N.leaf l)
    (hsource : ∀ e,N.source e=N.leaf l → e=e₀)
    (htarget : ∀ e,N.target e≠N.leaf l)
    (hactive : ∀ s,e₀∈N.active s)
    (g : NetworkFlowGluing.Flow L G) (c : C) :
    MvPolynomial.X (e₀,c)*MvPolynomial.pderiv (e₀,c) (coordinate (K := K) N q g)=
      if c=q (g.val l) then coordinate N q g else 0 := by
  classical
  simp only [coordinate,map_sum,Finset.mul_sum,MvPolynomial.X_mul_pderiv_monomial,
    exponent_at_edge,hactive,if_true]
  simp_rw [term_leaf_value N hinj l e₀ hs hsource htarget]
  by_cases hc : c=q (g.val l) <;> simp [hc,eq_comm]

/-- At an incoming cut leaf, the edge label is the negative of its leaf
label. This form preserves arbitrary orbit partitions under negation. -/
theorem coordinate_incoming_leaf_euler (N : Data V E L S) (q : G → C)
    (hinj : Function.Injective N.leaf) (l : L) (e₀ : E)
    (ht : N.target e₀=N.leaf l)
    (htarget : ∀ e,N.target e=N.leaf l → e=e₀)
    (hsource : ∀ e,N.source e≠N.leaf l)
    (hactive : ∀ s,e₀∈N.active s)
    (g : NetworkFlowGluing.Flow L G) (c : C) :
    MvPolynomial.X (e₀,c)*MvPolynomial.pderiv (e₀,c) (coordinate (K := K) N q g)=
      if c=q (-g.val l) then coordinate N q g else 0 := by
  classical
  simp only [coordinate,map_sum,Finset.mul_sum,MvPolynomial.X_mul_pderiv_monomial,
    exponent_at_edge,hactive,if_true]
  simp_rw [term_incoming_leaf_value N hinj l e₀ ht htarget hsource]
  by_cases hc : c=q (-g.val l) <;> simp [hc,eq_comm]

theorem coordinate_at_one (N : Data V E L S) (q : G → C)
    (g : NetworkFlowGluing.Flow L G) :
    MvPolynomial.aeval (fun _ : E × C => (1 : K)) (coordinate (K := K) N q g)=
      (Fintype.card (Term N g.val) : K) := by
  classical
  simp [coordinate,MvPolynomial.aeval_monomial]

/-- A genuine conserved flow supplies a nonzero Fourier polynomial. -/
theorem coordinate_ne_zero_of_term [CharZero K]
    (N : Data V E L S) (q : G → C) (g : NetworkFlowGluing.Flow L G)
    (t : Term N g.val) : coordinate (K := K) N q g≠0 := by
  classical
  letI : Nonempty (Term N g.val) := ⟨t⟩
  intro h
  have hh := congrArg (MvPolynomial.aeval (fun _ : E × C => (1 : K))) h
  rw [coordinate_at_one,map_zero] at hh
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero hh

end Sunlet.NetworkIncidenceFlows
end
end NetworkStageSource_Sunlet_NetworkIncidenceFlows
#eval IO.println "NETWORK_CHAPTER_COMPLETE Sunlet.NetworkIncidenceFlows"

section NetworkStageSource_Sunlet_NetworkGraphModel


/-!
# Fourier coordinates of a decorated finite level-one graph

The graph is an ordinary finite simple graph. Every simple cycle carries
its two distinct adjacent reticulation edges, and a displayed-tree choice
deletes one of them. The model is the conserved-flow polynomial sum on
the remaining actual graph edges. No dimension formula or gluing law is
part of these definitions.
-/

noncomputable section
open scoped BigOperators

namespace Sunlet.NetworkGraphModel

open SimpleGraph NetworkGraphDecomposition NetworkIncidenceFlows

variable {V G C K : Type*} [Fintype V] [DecidableEq V]
  [AddCommGroup G] [Fintype G] [DecidableEq G] [DecidableEq C]

/-- A choice of direction for each actual undirected edge. Reversing a
direction corresponds to negating its flow and relabelling its orbit
parameters by the induced negation permutation. -/
structure Orientation (H : SimpleGraph V) where
  source : H.edgeSet → V
  target : H.edgeSet → V
  edge_eq : ∀ e,s(source e,target e)=e.val

def canonicalOrientation (H : SimpleGraph V) : Orientation H where
  source e := e.val.out.1
  target e := e.val.out.2
  edge_eq e := e.val.out_eq

/-- The two incoming reticulation edges on each cycle. Adjacency is
expressed by a common endpoint; distinctness and membership in the actual
cycle are retained explicitly. -/
structure ReticulationData (H : SimpleGraph V) where
  incoming : Cycle H → Bool → H.edgeSet
  distinct : ∀ c,incoming c false≠incoming c true
  cycle_mem : ∀ c b,(incoming c b).val∈c.val
  common_vertex : ∀ c,∃ v : V,v∈(incoming c false).val ∧ v∈(incoming c true).val

abbrev Choice (H : SimpleGraph V) := Cycle H → Bool

instance (H : SimpleGraph V) : Fintype H.edgeSet := Fintype.ofFinite H.edgeSet
instance (H : SimpleGraph V) : Fintype (Leaf H) := Fintype.ofFinite (Leaf H)
instance (H : SimpleGraph V) : Fintype (Cycle H) := Fintype.ofFinite (Cycle H)

def activeEdges (H : SimpleGraph V) (R : ReticulationData H) (s : Choice H) :
    Finset H.edgeSet :=
  Finset.univ.filter fun e => ∀ c : Cycle H,e≠R.incoming c (s c)

theorem incoming_choice_injective (H : SimpleGraph V) (hH : HasDisjointCycles H)
    (R : ReticulationData H) (s : Choice H) :
    Function.Injective (fun c => R.incoming c (s c)) := by
  intro c d h
  change R.incoming c (s c)=R.incoming d (s d) at h
  by_contra hcd
  let v := (R.incoming c (s c)).val.out.1
  have hvc : v∈cycleVertices H c := by
    apply Finset.mem_biUnion.mpr
    exact ⟨_,R.cycle_mem c (s c),Sym2.mem_toFinset.mpr (Sym2.out_fst_mem _)⟩
  have hvd : v∈cycleVertices H d := by
    apply Finset.mem_biUnion.mpr
    refine ⟨_,R.cycle_mem d (s d),?_⟩
    rw [← h]
    exact Sym2.mem_toFinset.mpr (Sym2.out_fst_mem _)
  exact (Finset.disjoint_left.mp (hH c d hcd)) hvc hvd

theorem activeEdges_card (H : SimpleGraph V) (hH : HasDisjointCycles H)
    (R : ReticulationData H) (s : Choice H) :
    (activeEdges H R s).card=edgeCount H-cycleCount H := by
  classical
  have he : activeEdges H R s=Finset.univ\
      Finset.univ.image (fun c : Cycle H => R.incoming c (s c)) := by
    ext e
    constructor
    · intro h
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
      intro hm
      obtain ⟨c, _, hc⟩ := Finset.mem_image.mp hm
      exact (Finset.mem_filter.mp h).2 c hc.symm
    · intro h
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      intro c hc
      exact (Finset.mem_sdiff.mp h).2
        (Finset.mem_image.mpr ⟨c, Finset.mem_univ _, hc.symm⟩)
  rw [he,Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,
    Finset.card_image_of_injective _ (incoming_choice_injective H hH R s),Finset.card_univ]
  simp [edgeCount,cycleCount,Nat.card_eq_fintype_card]

def incidenceData (H : SimpleGraph V) (O : Orientation H) (R : ReticulationData H) :
    Data V H.edgeSet (Leaf H) (Choice H) where
  source := O.source
  target := O.target
  leaf := Subtype.val
  active := activeEdges H R

variable [CommSemiring K]

/-- The full graph Fourier parameterization, indexed by every zero-sum
assignment to its actual degree-one vertices. -/
def coordinate (H : SimpleGraph V) (O : Orientation H) (R : ReticulationData H)
    (q : G → C) (g : NetworkFlowGluing.Flow (Leaf H) G) :
    MvPolynomial (H.edgeSet × C) K :=
  NetworkIncidenceFlows.coordinate (incidenceData H O R) q g

/-- Exact polynomial identities of the graph model. -/
def definingIdeal (H : SimpleGraph V) (O : Orientation H) (R : ReticulationData H)
    (q : G → C) : Ideal (MvPolynomial (NetworkFlowGluing.Flow (Leaf H) G) K) :=
  RingHom.ker (MvPolynomial.aeval (coordinate (K := K) H O R q))

theorem coordinate_automorphism (H : SimpleGraph V) (O : Orientation H)
    (R : ReticulationData H) (q : G → C) (φ : G ≃+ G)
    (hq : ∀ a,q (φ a)=q a) (g : NetworkFlowGluing.Flow (Leaf H) G) :
    coordinate (K := K) H O R q (NetworkFlowGluing.mapFlow φ g)=coordinate H O R q g :=
  coordinate_mapFlow (incidenceData H O R) q φ hq g

/-- A bridge belongs to no cycle, hence is retained by every displayed
tree choice. In particular no parameter is silently deleted at a cut. -/
theorem bridge_mem_active (H : SimpleGraph V) (R : ReticulationData H)
    (e : H.edgeSet) (he : H.IsBridge e.val) (s : Choice H) : e∈activeEdges H R s := by
  classical
  simp only [activeEdges,Finset.mem_filter,Finset.mem_univ,true_and]
  intro c h
  apply bridge_not_mem_cycle H he c
  rw [h]
  exact R.cycle_mem c (s c)

end Sunlet.NetworkGraphModel
end
end NetworkStageSource_Sunlet_NetworkGraphModel
#eval IO.println "NETWORK_CHAPTER_COMPLETE Sunlet.NetworkGraphModel"

section NetworkStageSource_Sunlet_NetworkDisplayedTrees


/-!
# The actual displayed graphs are spanning trees

A displayed choice deletes exactly one of the two marked reticulation
edges on every actual simple cycle.  Every surviving cycle would contain
its own deleted marked edge.  The exact graph counts show that the
remaining acyclic spanning graph already has the edge count of a tree;
extending it to a spanning tree therefore adds no edges.
-/

noncomputable section

namespace Sunlet.NetworkDisplayedTrees

open SimpleGraph NetworkGraphDecomposition NetworkGraphModel

variable {V : Type*} [Fintype V] [DecidableEq V]
  (H : SimpleGraph V) (R : ReticulationData H) (s : Choice H)

/-- The displayed graph has the same vertex set as the original graph
and precisely the edges retained by the incidence-flow model. -/
def displayedGraph : SimpleGraph V :=
  H.deleteEdges (Set.range (fun c : Cycle H => (R.incoming c (s c)).val))

theorem displayedGraph_le : displayedGraph H R s ≤ H := H.deleteEdges_le _

theorem displayedGraph_edgeSet :
    (displayedGraph H R s).edgeSet =
      H.edgeSet \ Set.range (fun c : Cycle H => (R.incoming c (s c)).val) :=
  H.edgeSet_deleteEdges _

/-- No simple cycle survives deletion.  This uses the literal cycle
index, not a chosen cycle basis or an assumed feedback-edge property. -/
theorem displayedGraph_isAcyclic : (displayedGraph H R s).IsAcyclic := by
  intro v p hp
  have hE : ∀ e ∈ p.edges, e ∈ H.edgeSet := fun e he =>
    SimpleGraph.edgeSet_mono (displayedGraph_le H R s) (p.edges_subset_edgeSet he)
  let c : Cycle H := ⟨p.edges.toFinset, ⟨v, p.transfer H hE,
    hp.transfer hE, by rw [SimpleGraph.Walk.edges_transfer]⟩⟩
  have hmem : (R.incoming c (s c)).val ∈ p.edges :=
    List.mem_toFinset.mp (R.cycle_mem c (s c))
  have hret := p.edges_subset_edgeSet hmem
  rw [displayedGraph_edgeSet] at hret
  exact hret.2 ⟨c, rfl⟩

/-- The retained-edge type in the conserved-flow definition is exactly
the edge set of the displayed graph. -/
def displayedEdgeEquiv : (displayedGraph H R s).edgeSet ≃ activeEdges H R s where
  toFun e := by
    have he : e.val ∈ H.edgeSet ∧
        e.val ∉ Set.range (fun c : Cycle H => (R.incoming c (s c)).val) := by
      simpa only [displayedGraph_edgeSet, Set.mem_diff] using e.property
    refine ⟨⟨e.val, he.1⟩, ?_⟩
    simp only [activeEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    intro c hc
    exact he.2 ⟨c, (congrArg Subtype.val hc).symm⟩
  invFun e := by
    refine ⟨e.val.val, ?_⟩
    rw [displayedGraph_edgeSet]
    refine ⟨e.val.property, ?_⟩
    rintro ⟨c, hc⟩
    have havoid : ∀ c, e.val ≠ R.incoming c (s c) := by
      simpa only [activeEdges, Finset.mem_filter, Finset.mem_univ, true_and] using e.property
    exact havoid c (Subtype.ext hc.symm)
  left_inv e := Subtype.ext rfl
  right_inv e := Subtype.ext (Subtype.ext rfl)

theorem displayedGraph_edgeCount (hH : HasDisjointCycles H) :
    edgeCount (displayedGraph H R s) = edgeCount H - cycleCount H := by
  calc
    edgeCount (displayedGraph H R s) = (activeEdges H R s).card := by
      simpa only [edgeCount, Nat.card_eq_fintype_card, Fintype.card_coe] using
        Nat.card_congr (displayedEdgeEquiv H R s)
    _ = edgeCount H - cycleCount H := activeEdges_card H hH R s

include R s in
theorem cycleCount_le_edgeCount (hH : HasDisjointCycles H) : cycleCount H ≤ edgeCount H := by
  have h := Fintype.card_le_of_injective _ (incoming_choice_injective H hH R s)
  simpa only [cycleCount, edgeCount, Nat.card_eq_fintype_card] using h

/-- Euler's relation here is a consequence of the proved binary-cactus
decomposition and the ordinary handshaking identity. -/
theorem binaryCactus_euler (hH : IsBinaryCactus H) :
    edgeCount H + 1 = Nat.card V + cycleCount H := by
  have hd := binary_degree_sum H hH.binary
  have hc := (binaryCactus_counts H hH).1
  omega

theorem displayedGraph_card (hH : IsBinaryCactus H) :
    edgeCount (displayedGraph H R s) + 1 = Nat.card V := by
  rw [displayedGraph_edgeCount H R s hH.disjoint_cycles]
  have he := binaryCactus_euler H hH
  have hc := cycleCount_le_edgeCount H R s hH.disjoint_cycles
  omega

/-- Every displayed choice is an actual spanning tree on all original
vertices.  No graph connectedness is inserted into the model definition. -/
theorem displayedGraph_isTree (hH : IsBinaryCactus H) : (displayedGraph H R s).IsTree := by
  obtain ⟨T, hDT, hTH, hT⟩ := hH.connected.exists_isTree_le_of_le_of_isAcyclic
    (displayedGraph_le H R s) (displayedGraph_isAcyclic H R s)
  have hDcard := displayedGraph_card H R s hH
  have hTcard := (SimpleGraph.isTree_iff_connected_and_card.mp hT).2
  have heq : Nat.card (displayedGraph H R s).edgeSet = Nat.card T.edgeSet := by
    change edgeCount T + 1 = Nat.card V at hTcard
    change edgeCount (displayedGraph H R s) = edgeCount T
    omega
  have hfin : (displayedGraph H R s).edgeFinset.card = T.edgeFinset.card := by
    simpa only [SimpleGraph.edgeFinset_card, Nat.card_eq_fintype_card] using heq
  have hgraph : displayedGraph H R s = T := SimpleGraph.edgeFinset_inj.mp
    (Finset.eq_of_subset_of_card_le (SimpleGraph.edgeFinset_mono hDT) hfin.ge)
  rw [hgraph]
  exact hT

theorem displayedGraph_connected (hH : IsBinaryCactus H) :
    (displayedGraph H R s).Connected := (displayedGraph_isTree H R s hH).connected

end Sunlet.NetworkDisplayedTrees
end
end NetworkStageSource_Sunlet_NetworkDisplayedTrees
#eval IO.println "NETWORK_CHAPTER_COMPLETE Sunlet.NetworkDisplayedTrees"

section NetworkStageSource_Sunlet_NetworkValidFlowCuts


/-!
# Conserved flows on actual displayed-tree cuts

Summing conservation over a component of an actual displayed tree proves
that every valid edge flow has exactly the paper's leaf-cut group labels.
This statement applies to all valid flows; the canonical flow is identified
in `NetworkDisplayedFlowCuts` after existence and uniqueness are proved.
-/

noncomputable section
open scoped BigOperators

namespace Sunlet.NetworkDisplayedFlowCuts

open SimpleGraph NetworkIncidenceFlows NetworkGraphDecomposition NetworkGraphModel
open NetworkDisplayedTrees

attribute [local instance] Classical.propDecidable

variable {V E L S G : Type*} [Fintype V] [Fintype E] [Fintype L] [Fintype S]
  [DecidableEq V] [DecidableEq E] [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem conserved_cut_flux (N : Data V E L S) (g : L → G) (s : S) (x : E → G)
    (hx : Valid N g s x) (U : Finset V) (e₀ : E)
    (hs : N.source e₀∈U) (ht : N.target e₀∉U)
    (hcut : ∀ e,e∈N.active s → e≠e₀ → (N.source e∈U ↔ N.target e∈U)) :
    x e₀=∑ l,if N.leaf l∈U then g l else 0 := by
  have he : (∑ e,((if N.source e∈U then x e else 0)-
      (if N.target e∈U then x e else 0)))=x e₀ := by
    rw [Finset.sum_eq_single e₀]
    · simp [hs,ht]
    · intro e he hne
      by_cases ha : e∈N.active s
      · simp only [hcut e ha hne,sub_self]
      · simp [hx.1 e ha]
    · simp
  rw [← he,← sum_divergence_on]
  simp_rw [hx.2]
  exact sum_leafBoundary_on N.leaf g U

theorem active_edge_adj (H : SimpleGraph V) (O : Orientation H) (R : ReticulationData H)
    (s : Choice H) (e : H.edgeSet) (he : e∈activeEdges H R s) :
    (displayedGraph H R s).Adj (O.source e) (O.target e) := by
  change s(O.source e,O.target e)∈(displayedGraph H R s).edgeSet
  rw [O.edge_eq]
  exact ((displayedEdgeEquiv H R s).symm ⟨e,he⟩).property

/-- The exact Fourier group label on a retained edge is the sum of the
leaf labels on its source side in that displayed tree. Opposite edge
directions give opposite sums, as handled by the class-negation theorem. -/
theorem valid_edgeFlow_eq_leaf_sum (H : SimpleGraph V) (hH : IsBinaryCactus H)
    (O : Orientation H) (R : ReticulationData H)
    (g : NetworkFlowGluing.Flow (Leaf H) G) (s : Choice H)
    (x : H.edgeSet → G) (hx : Valid (incidenceData H O R) g.val s x)
    (e : H.edgeSet) (he : e∈activeEdges H R s) :
    x e=
      ∑ l : Leaf H,if l.val∈cutSide (displayedGraph H R s) (O.source e) (O.target e)
        then g.val l else 0 := by
  let D := displayedGraph H R s
  let U := (cutSide D (O.source e) (O.target e)).toFinset
  have hU (v : V) : v∈U ↔ v∈cutSide D (O.source e) (O.target e) := by
    change v∈(cutSide D (O.source e) (O.target e)).toFinset ↔
      v∈cutSide D (O.source e) (O.target e)
    exact Set.mem_toFinset
  have hadj : D.Adj (O.source e) (O.target e) := active_edge_adj H O R s e he
  have hb : D.IsBridge s(O.source e,O.target e) :=
    (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp
      (displayedGraph_isTree H R s hH).isAcyclic) hadj
  have hs : O.source e∈U := by
    apply (hU _).mpr
    exact SimpleGraph.Reachable.rfl
  have ht : O.target e∉U := by
    exact fun h => end_not_mem_cutSide D (O.source e) (O.target e) hb ((hU _).mp h)
  have hcut : ∀ f : H.edgeSet,f∈activeEdges H R s → f≠e →
      (O.source f∈U ↔ O.target f∈U) := by
    intro f hf hne
    have hremain : (cutBase D (O.source e) (O.target e)).Adj (O.source f) (O.target f) := by
      rw [cutBase,SimpleGraph.deleteEdges_adj]
      refine ⟨active_edge_adj H O R s f hf,?_⟩
      simp only [Set.mem_singleton_iff,O.edge_eq]
      exact fun h =>hne (Subtype.ext h)
    rw [hU,hU]
    change (cutBase D (O.source e) (O.target e)).Reachable (O.source e) (O.source f) ↔
      (cutBase D (O.source e) (O.target e)).Reachable (O.source e) (O.target f)
    exact ⟨fun h =>h.trans hremain.reachable,fun h =>h.trans hremain.symm.reachable⟩
  simpa only [incidenceData,hU] using
    conserved_cut_flux (incidenceData H O R) g.val s
      x hx
      U e hs ht hcut

end Sunlet.NetworkDisplayedFlowCuts
end
end NetworkStageSource_Sunlet_NetworkValidFlowCuts
#eval IO.println "NETWORK_CHAPTER_COMPLETE Sunlet.NetworkValidFlowCuts"

section NetworkStageSource_Sunlet_NetworkFiniteFlows


/-!
# Existence and uniqueness of conserved flows on displayed trees

The cut formula makes the divergence map injective. Its domain and the
zero-sum vertex labellings have the same finite cardinality, because an
actual displayed tree has one fewer edge than vertices. Hence every
zero-sum leaf boundary has a unique conserved flow.
-/

noncomputable section
open scoped BigOperators

namespace Sunlet.NetworkFiniteFlows

open NetworkIncidenceFlows NetworkFlowGluing NetworkGraphDecomposition
open NetworkGraphModel NetworkDisplayedTrees NetworkDisplayedFlowCuts

attribute [local instance] Classical.propDecidable

variable {V E G : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem sum_eq_root_add (root : V) (f : V → G) :
    ∑ v,f v = f root + ∑ v : {v : V // v≠root},f v.val := by
  classical
  letI : Fintype {v : V // v=root} := Subtype.fintype (fun v : V =>v=root)
  calc
    ∑ v,f v = (∑ v : {v : V // v=root},f v.val) +
        ∑ v : {v : V // v≠root},f v.val :=
      (Fintype.sum_subtype_add_sum_subtype (fun v : V =>v=root) f).symm
    _ = _ := by
      congr 1
      exact Fintype.sum_subsingleton (fun v : {v : V // v=root} =>f v.val) ⟨root,rfl⟩

/-- Prescribe every vertex label except one; conservation determines the last. -/
def zeroSumEquiv (root : V) : Flow V G ≃ ({v : V // v≠root} → G) where
  toFun g v := g.val v.val
  invFun f := ⟨fun v =>if h : v=root then -(∑ w,f w) else f ⟨v,h⟩,by
    rw [sum_eq_root_add root]
    simp only [dif_pos rfl]
    have hs : (∑ v : {v : V // v≠root},
        if h : v.val=root then -(∑ w,f w) else f ⟨v.val,h⟩)=∑ w,f w := by
      apply Finset.sum_congr rfl
      intro v hv
      exact dif_neg v.property
    rw [hs]
    exact neg_add_cancel _⟩
  left_inv g := by
    apply Subtype.ext
    funext v
    by_cases h : v=root
    · subst v
      have hg := g.property
      rw [sum_eq_root_add root] at hg
      simpa using (eq_neg_of_add_eq_zero_left hg).symm
    · simp [h]
  right_inv f := by
    funext v
    simp [v.property]

theorem card_zeroSum (root : V) :
    Fintype.card (Flow V G)=Fintype.card G^(Fintype.card V-1) := by
  rw [Fintype.card_congr (zeroSumEquiv (G := G) root),Fintype.card_fun]
  congr 1
  simpa only [Fintype.card_subtype_eq] using
    Fintype.card_subtype_compl (fun v : V =>v=root)

theorem divergence_sub (source target : E → V) (x y : E → G) (v : V) :
    divergence source target (fun e =>x e-y e) v=
      divergence source target x v-divergence source target y v := by
  have hs (p : E → Prop) [DecidablePred p] :
      (∑ e,if p e then x e-y e else 0)=
        (∑ e,if p e then x e else 0)-(∑ e,if p e then y e else 0) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e he
    by_cases h : p e <;> simp [h]
  unfold divergence
  rw [hs,hs]
  abel

def extendActive (H : SimpleGraph V) (R : ReticulationData H) (s : Choice H)
    (x : activeEdges H R s → G) (e : H.edgeSet) : G :=
  if h : e∈activeEdges H R s then x ⟨e,h⟩ else 0

def divergenceMap (H : SimpleGraph V) (O : Orientation H) (R : ReticulationData H)
    (s : Choice H) (x : activeEdges H R s → G) : Flow V G :=
  ⟨divergence O.source O.target (extendActive H R s x),sum_divergence _ _ _⟩

/-- A flow with zero divergence has zero sum across every displayed-tree cut. -/
theorem divergenceMap_injective (H : SimpleGraph V) (hH : IsBinaryCactus H)
    (O : Orientation H) (R : ReticulationData H) (s : Choice H) :
    Function.Injective (divergenceMap (G := G) H O R s) := by
  intro x y hxy
  let g : Flow (Leaf H) G := ⟨fun _ =>0,by simp⟩
  let z : H.edgeSet → G := fun e =>extendActive H R s x e-extendActive H R s y e
  have hz : Valid (incidenceData H O R) g.val s z := by
    constructor
    · intro e he
      simp only [incidenceData] at he
      simp [z,extendActive,he]
    · intro v
      have hv := congrArg (fun f : Flow V G =>f.val v) hxy
      change divergence O.source O.target (extendActive H R s x) v=
        divergence O.source O.target (extendActive H R s y) v at hv
      change divergence O.source O.target z v=leafBoundary Subtype.val g.val v
      rw [show z=(fun e =>extendActive H R s x e-extendActive H R s y e) from rfl,
        divergence_sub,hv,sub_self]
      change 0=∑ l : Leaf H,if l.val=v then (0 : G) else 0
      symm
      apply Finset.sum_eq_zero
      intro l hl
      by_cases h : l.val=v <;> simp [h]
  funext e
  have he := valid_edgeFlow_eq_leaf_sum H hH O R g s z hz e.val e.property
  have he0 : x e-y e=0 := by
    simpa only [z,extendActive,dif_pos e.property,g,ite_self,Finset.sum_const_zero] using he
  exact sub_eq_zero.mp he0

theorem divergenceMap_bijective (H : SimpleGraph V) (hH : IsBinaryCactus H)
    (O : Orientation H) (R : ReticulationData H) (s : Choice H) :
    Function.Bijective (divergenceMap (G := G) H O R s) := by
  haveI : Nonempty V := hH.connected.nonempty
  let root : V := Classical.choice inferInstance
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨divergenceMap_injective H hH O R s,?_⟩
  rw [Fintype.card_fun,card_zeroSum (G := G) root]
  congr 1
  have he := displayedGraph_card H R s hH
  have hc := Fintype.card_congr (displayedEdgeEquiv H R s)
  change Nat.card (displayedGraph H R s).edgeSet+1=Nat.card V at he
  simp only [Nat.card_eq_fintype_card] at he
  omega

/-- Every zero-sum leaf labelling has exactly one edge flow for each actual choice. -/
theorem exists_unique_valid (H : SimpleGraph V) (hH : IsBinaryCactus H)
    (O : Orientation H) (R : ReticulationData H)
    (g : Flow (Leaf H) G) (s : Choice H) :
    ∃! x : H.edgeSet → G,Valid (incidenceData H O R) g.val s x := by
  let boundary : Flow V G := ⟨leafBoundary Subtype.val g.val,by
    rw [sum_leafBoundary]
    exact g.property⟩
  obtain ⟨x,hx⟩ := (divergenceMap_bijective H hH O R s).2 boundary
  refine ⟨extendActive H R s x,?_,?_⟩
  · constructor
    · intro e he
      simp only [incidenceData] at he
      simp [extendActive,he]
    · intro v
      exact congrArg (fun f : Flow V G =>f.val v) hx
  · intro y hy
    have hxy : divergenceMap H O R s (fun e =>y e.val)=divergenceMap H O R s x := by
      rw [hx]
      apply Subtype.ext
      funext v
      change divergence O.source O.target
        (extendActive H R s (fun e =>y e.val)) v=leafBoundary Subtype.val g.val v
      have he : extendActive H R s (fun e =>y e.val)=y := by
        funext e
        by_cases h : e∈activeEdges H R s
        · simp [extendActive,h]
        · simp [extendActive,h,hy.1 e h]
      rw [he]
      exact hy.2 v
    have heq := (divergenceMap_bijective H hH O R s).1 hxy
    funext e
    by_cases he : e∈activeEdges H R s
    · simpa only [extendActive,dif_pos he] using congrFun heq ⟨e,he⟩
    · simp [extendActive,he,hy.1 e he]

end Sunlet.NetworkFiniteFlows
end
end NetworkStageSource_Sunlet_NetworkFiniteFlows
#eval IO.println "NETWORK_CHAPTER_COMPLETE Sunlet.NetworkFiniteFlows"

section NetworkStageSource_Sunlet_NetworkFlowUniqueness


/-!
# One Fourier monomial for each actual displayed-tree choice

The incidence definition sums over conserved edge flows. This module
proves, for every graph in Corollary8.1, that each displayed-tree choice
has exactly one such flow. The coordinate is consequently the paper's
sum of one edge-parameter monomial for each choice.
-/

noncomputable section
open scoped BigOperators

namespace Sunlet.NetworkFlowUniqueness

open NetworkIncidenceFlows NetworkFlowGluing NetworkGraphDecomposition NetworkGraphModel

attribute [local instance] Classical.propDecidable

variable {V E L S G C K : Type*} [Fintype V] [Fintype E] [Fintype L] [Fintype S]
  [DecidableEq V] [DecidableEq E] [AddCommGroup G] [Fintype G] [DecidableEq G]

def choiceProjection (N : Data V E L S) (g : Flow L G) : Term N g.val → S := fun t =>t.val.1

def EachChoiceUnique (N : Data V E L S) : Prop :=
  ∀ g : Flow L G,Function.Bijective (choiceProjection N g)

/-- Every displayed-tree choice of an actual finite binary cactus has
exactly one conserved group flow for every zero-sum leaf labelling. -/
theorem graph_eachChoiceUnique {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (hH : IsBinaryCactus H) (O : Orientation H) (R : ReticulationData H) :
    EachChoiceUnique (G := G) (incidenceData H O R) := by
  intro g
  constructor
  · intro x y h
    change x.val.1=y.val.1 at h
    apply Subtype.ext
    apply Prod.ext h
    obtain ⟨z,hz,hu⟩ := NetworkFiniteFlows.exists_unique_valid H hH O R g x.val.1
    have hy : Valid (incidenceData H O R) g.val x.val.1 y.val.2 := by
      rw [h]
      exact y.property
    exact (hu x.val.2 x.property).trans (hu y.val.2 hy).symm
  · intro s
    obtain ⟨x,hx,_⟩ := NetworkFiniteFlows.exists_unique_valid H hH O R g s
    exact ⟨⟨(s,x),hx⟩,rfl⟩

def displayedTermEquiv {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (hH : IsBinaryCactus H) (O : Orientation H) (R : ReticulationData H)
    (g : Flow (Leaf H) G) : Term (incidenceData H O R) g.val ≃ Choice H :=
  Equiv.ofBijective (choiceProjection (incidenceData H O R) g) (graph_eachChoiceUnique H hH O R g)

def displayedEdgeFlow {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (hH : IsBinaryCactus H) (O : Orientation H) (R : ReticulationData H)
    (g : Flow (Leaf H) G) (s : Choice H) : H.edgeSet → G :=
  ((displayedTermEquiv H hH O R g).symm s).val.2

theorem displayedEdgeFlow_valid {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (hH : IsBinaryCactus H) (O : Orientation H) (R : ReticulationData H)
    (g : Flow (Leaf H) G) (s : Choice H) :
    Valid (incidenceData H O R) g.val s (displayedEdgeFlow H hH O R g s) := by
  have hs := (displayedTermEquiv H hH O R g).apply_symm_apply s
  change ((displayedTermEquiv H hH O R g).symm s).val.1=s at hs
  simpa only [hs,displayedEdgeFlow] using
    ((displayedTermEquiv H hH O R g).symm s).property

theorem displayedEdgeFlow_unique {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (hH : IsBinaryCactus H) (O : Orientation H) (R : ReticulationData H)
    (g : Flow (Leaf H) G) (s : Choice H) (x : H.edgeSet → G)
    (hx : Valid (incidenceData H O R) g.val s x) :
    x=displayedEdgeFlow H hH O R g s := by
  let t : Term (incidenceData H O R) g.val := ⟨(s,x),hx⟩
  have ht : t=(displayedTermEquiv H hH O R g).symm s := by
    apply (displayedTermEquiv H hH O R g).injective
    rw [Equiv.apply_symm_apply]
    rfl
  exact congrArg (fun z : Term (incidenceData H O R) g.val =>z.val.2) ht

/-- Explicit equality with the paper's Fourier formula: a product over
the retained actual edges, summed once over every reticulation choice. -/
theorem coordinate_eq_displayed_sum {W : Type*} [Fintype W] [DecidableEq W]
    [DecidableEq C] [CommSemiring K]
    (H : SimpleGraph W) (hH : IsBinaryCactus H) (O : Orientation H) (R : ReticulationData H)
    (q : G → C) (g : Flow (Leaf H) G) :
    NetworkGraphModel.coordinate (K := K) H O R q g=
      ∑ s : Choice H,∏ e∈activeEdges H R s,
        MvPolynomial.X (e,q (displayedEdgeFlow H hH O R g s e)) := by
  change NetworkIncidenceFlows.coordinate (incidenceData H O R) q g=_
  rw [coordinate_eq_sum_terms]
  calc
    (∑ t : Term (incidenceData H O R) g.val,termPolynomial (incidenceData H O R) q t)=
        ∑ s : Choice H,termPolynomial (incidenceData H O R) q
          ((displayedTermEquiv H hH O R g).symm s) := by
      apply Fintype.sum_equiv (displayedTermEquiv H hH O R g)
      intro t
      simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [termPolynomial_eq_prod]
      have hchoice := (displayedTermEquiv H hH O R g).apply_symm_apply s
      change ((displayedTermEquiv H hH O R g).symm s).val.1=s at hchoice
      change (∏ e∈activeEdges H R ((displayedTermEquiv H hH O R g).symm s).val.1,
        MvPolynomial.X (e,q (((displayedTermEquiv H hH O R g).symm s).val.2 e)))=_
      rw [hchoice]
      rfl

end Sunlet.NetworkFlowUniqueness
end
end NetworkStageSource_Sunlet_NetworkFlowUniqueness
#eval IO.println "NETWORK_CHAPTER_COMPLETE Sunlet.NetworkFlowUniqueness"

section NetworkStageSource_Sunlet_NetworkLeafCutCoordinates


/-!
# The displayed edge labels are the paper's leaf-cut sums

Conservation is summed over one component after deleting a retained
edge of the actual displayed tree. Inactive original edges contribute
zero. This identifies the edge labels in the formal Fourier polynomial
with sums of the original leaf labels on the corresponding cut side.
-/

noncomputable section
open scoped BigOperators

namespace Sunlet.NetworkDisplayedFlowCuts

open SimpleGraph NetworkIncidenceFlows NetworkGraphDecomposition NetworkGraphModel
open NetworkDisplayedTrees NetworkFlowUniqueness

attribute [local instance] Classical.propDecidable

variable {V E L S G : Type*} [Fintype V] [Fintype E] [Fintype L] [Fintype S]
  [DecidableEq V] [DecidableEq E] [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The exact Fourier group label on a retained edge is the sum of the
leaf labels on its source side in that displayed tree. Opposite edge
directions give opposite sums, as handled by the class-negation theorem. -/
theorem displayedEdgeFlow_eq_leaf_sum (H : SimpleGraph V) (hH : IsBinaryCactus H)
    (O : Orientation H) (R : ReticulationData H)
    (g : NetworkFlowGluing.Flow (Leaf H) G) (s : Choice H)
    (e : H.edgeSet) (he : e∈activeEdges H R s) :
    displayedEdgeFlow H hH O R g s e=
      ∑ l : Leaf H,if l.val∈cutSide (displayedGraph H R s) (O.source e) (O.target e)
        then g.val l else 0 := by
  exact valid_edgeFlow_eq_leaf_sum H hH O R g s
    (displayedEdgeFlow H hH O R g s) (displayedEdgeFlow_valid H hH O R g s) e he

/-- The ordinary Fourier formula written entirely with the graph's
displayed choices, retained edges, and sums over their actual leaf cuts. -/
theorem coordinate_eq_leaf_cut_formula {C K : Type*} [DecidableEq C] [CommSemiring K]
    (H : SimpleGraph V) (hH : IsBinaryCactus H) (O : Orientation H) (R : ReticulationData H)
    (q : G → C) (g : NetworkFlowGluing.Flow (Leaf H) G) :
    NetworkGraphModel.coordinate (K := K) H O R q g=
      ∑ s : Choice H,∏ e∈activeEdges H R s,MvPolynomial.X
        (e,q (∑ l : Leaf H,
          if l.val∈cutSide (displayedGraph H R s) (O.source e) (O.target e)
          then g.val l else 0)) := by
  rw [coordinate_eq_displayed_sum H hH O R q g]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.prod_congr rfl
  intro e he
  rw [displayedEdgeFlow_eq_leaf_sum H hH O R g s e he]

/-- The paper's Fourier map stated directly as a sum over displayed
choices, with every edge class computed from its actual leaf cut. -/
def leafCutCoordinate {C K : Type*} [DecidableEq C] [CommSemiring K]
    (H : SimpleGraph V) (O : Orientation H) (R : ReticulationData H)
    (q : G → C) (g : NetworkFlowGluing.Flow (Leaf H) G) :
    MvPolynomial (H.edgeSet × C) K :=
  ∑ s : Choice H,∏ e∈activeEdges H R s,MvPolynomial.X
    (e,q (∑ l : Leaf H,
      if l.val∈cutSide (displayedGraph H R s) (O.source e) (O.target e)
      then g.val l else 0))

theorem leafCutCoordinate_eq_coordinate {C K : Type*} [DecidableEq C] [CommSemiring K]
    (H : SimpleGraph V) (hH : IsBinaryCactus H) (O : Orientation H)
    (R : ReticulationData H) (q : G → C) :
    leafCutCoordinate (K := K) H O R q=NetworkGraphModel.coordinate H O R q :=
  (funext (coordinate_eq_leaf_cut_formula H hH O R q)).symm

end Sunlet.NetworkDisplayedFlowCuts
end
end NetworkStageSource_Sunlet_NetworkLeafCutCoordinates
#eval IO.println "NETWORK_CHAPTER_COMPLETE Sunlet.NetworkLeafCutCoordinates"

#print axioms Sunlet.NetworkGraphDecomposition.binaryCactus_induction
#print axioms Sunlet.NetworkFlowUniqueness.graph_eachChoiceUnique
#print axioms Sunlet.NetworkDisplayedFlowCuts.leafCutCoordinate_eq_coordinate
#eval IO.println "NETWORK_STAGE_SOURCE_COMPLETE VerifiedNetworkGraph"
