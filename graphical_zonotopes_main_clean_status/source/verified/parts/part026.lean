module

public import Aesop
public import Lean.Elab.Command
public import Lean.Elab.Tactic.Omega
public import Lean.Meta.Basic
public import Lean.PrettyPrinter
public import Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Analysis.Normed.Group.Submodule
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.Graph.Delete
public import Mathlib.Combinatorics.Graph.Maps
public import Mathlib.Combinatorics.Graph.Simple
public import Mathlib.Combinatorics.Graph.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Fin.Embedding
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Sigma.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Order.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Order.Sum.Order
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Tauto
public import Mathlib.Topology.Algebra.Affine
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.UnitInterval

public import verified.parts.part025
import all verified.parts.part025

@[expose] public section

set_option debug.skipKernelTC false
set_option linter.all false
set_option Elab.async false
set_option internal.cmdlineSnapshots true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

section BundlePart373
/- Source: dev/planar_search/schoenflies_port/Schoenflies/Graph/Walk.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/




/-!
# Walks and paths in a multigraph

Mathlib's `Graph α β` carries incidence (`G.IsLink e x y`) and nothing that moves along it.
This file is the bottom of the combinatorial layer: walks, paths, reachability and
connectedness, all of which the plane development consumes through one theorem —
`Graph.IsWalk.contains_path`, the blueprint's "shorten an arbitrary walk at repeated
vertices".

## A walk is a list of edges

`G.IsWalk u W v` says the edge list `W` walks from `u` to `v`, each edge taken from the vertex
the previous one arrived at. It names its **edges**, not its vertices. That is forced by
parallel edges: two edges with the same ends are distinguishable only by name, and a walk
along one of them must be able to say which it took — a two-vertex cycle, which the plane
layer builds out of a Jordan curve cut at two points, is exactly such a graph. Nothing is
lost by naming edges, because an edge determines where taking it arrives
(`Graph.IsLink.right_unique` upstream, `Graph.IsWalk.target_unique` here).

It is an **inductive family**, not a recursion over the list. Every consumer argues by
induction along the walk, and the inductive gives that directly, naming the waypoint of each
step; a recursion `fun u (e :: W) v => ∃ w, G.IsLink e u w ∧ IsWalk G w W v` would force
every proof to generalize the source vertex by hand and to destructure an existential at each
step. The relation is built at the **source** end, since that is the end a list is extended
at; concatenation (`Graph.IsWalk.append`) and reversal (`Graph.IsWalk.reverse`) are proved
here once, and after that no argument has to care.

The empty walk demands `x ∈ V(G)`. This buys the whole file: every vertex a walk visits is a
vertex of the graph with *no* side hypothesis, because Mathlib's `Graph` already forces the
ends of an edge into `V(G)`.

## A path carries its own freshness

`G.IsPath u W v` is a walk with one clause added at each step: the vertex the step departs
from is not among those the rest of the path visits. The condition travels with the
induction, instead of being imposed afterwards on a separately computed vertex list — which
would have to be computed, and would need the graph to be loopless before it was even
correct.

## Loops

Mathlib's `Graph` allows an edge with both ends equal; the blueprint's graphs have none.
**Walks tolerate loops and paths exclude them automatically** — no hypothesis on `G` anywhere
in this file. A step of a path from `u` along `e` to `w` requires `u ∉ G.walkVertices w W`,
and `w` is always in that set, so `u ≠ w`: the freshness clause already says a path's step is
not a loop (`Graph.IsPath.not_isLoopAt`). Imposing looplessness on the graph instead would
put a hypothesis on every statement in the layer to rule out something the definitions
already rule out.

## Namespace

Declarations live in the root `Graph` namespace, extending Mathlib's, rather than in
`Schoenflies`: `G.IsWalk`, `hW.append`, `hP.isWalk` are the spellings every consumer wants,
and dot notation on a Mathlib type resolves through the type's own namespace.

## Blueprint

The blueprint uses finite graphs as an imported foundation (§"Imported facts", *Finite
graphs*: "in a finite connected graph, any two vertices are joined by a simple path, obtained
by shortening an arbitrary walk at repeated vertices"). This file supplies that import.

* `Graph.IsWalk.contains_path` — shortening a walk to a path; used at
  `lem:polygonal-connected` ("take a simple path in the resulting finite graph"),
  `lem:finite-polygonal-union` ("a simple graph path has the required realization") and
  `lem:skeleton-crosscuts` ("the resulting finite graph is connected, so it contains a
  simple graph path `P` from `a` to `b`").
* `Graph.Reaches`, `Graph.Connected` — the connectedness those three lemmas invoke.
* `Graph.IsPath.nodup` — a simple path repeats no edge; underneath the finiteness arguments
  that bound a path's length.
* `Graph.IsPath.reverse`, `Graph.IsPath.split` — a path backwards, and a path cut in two at a
  vertex it visits; what `lem:subdivision-ear-preserve` and `lem:relative-ear` run on.
-/

open Set

variable {α β : Type*} {G H : Graph α β} {u v w x y z : α} {e f : β} {W W₁ W₂ P : List β}

namespace Graph

/-! ### The vertices an edge list touches -/

/-- The vertices lying on at least one edge of `W`. -/
def coveredVertices (G : Graph α β) (W : List β) : Set α := {x | ∃ e ∈ W, G.Inc e x}

/-- The vertices a walk from `u` along `W` visits: its source, plus the ends of every edge it
takes. Defined for any edge list, not just for one that walks — the freshness clause of a
path reads it about the *rest* of the path before that rest is known to be a walk at all. -/
def walkVertices (G : Graph α β) (u : α) (W : List β) : Set α := insert u (G.coveredVertices W)

theorem mem_coveredVertices_iff : x ∈ G.coveredVertices W ↔ ∃ e ∈ W, G.Inc e x := Iff.rfl

theorem mem_walkVertices_iff : x ∈ G.walkVertices u W ↔ x = u ∨ x ∈ G.coveredVertices W :=
  Set.mem_insert_iff

@[simp]
theorem coveredVertices_nil : G.coveredVertices ([] : List β) = ∅ := by
  simp [coveredVertices]

@[simp]
theorem walkVertices_nil : G.walkVertices u ([] : List β) = {u} := by
  simp [walkVertices]

theorem mem_coveredVertices (he : e ∈ W) (hx : G.Inc e x) : x ∈ G.coveredVertices W :=
  ⟨e, he, hx⟩

theorem mem_walkVertices_self : u ∈ G.walkVertices u W := Set.mem_insert _ _

theorem mem_walkVertices_of_mem_covered (hx : x ∈ G.coveredVertices W) :
    x ∈ G.walkVertices u W :=
  Set.mem_insert_of_mem _ hx

theorem coveredVertices_mono (h : W₁ ⊆ W₂) : G.coveredVertices W₁ ⊆ G.coveredVertices W₂ :=
  fun _ ⟨e, he, hx⟩ ↦ ⟨e, h he, hx⟩

theorem walkVertices_mono (h : W₁ ⊆ W₂) : G.walkVertices u W₁ ⊆ G.walkVertices u W₂ :=
  Set.insert_subset_insert (coveredVertices_mono h)

@[simp]
theorem coveredVertices_reverse : G.coveredVertices W.reverse = G.coveredVertices W := by
  simp [coveredVertices]

@[simp]
theorem walkVertices_reverse : G.walkVertices u W.reverse = G.walkVertices u W := by
  simp [walkVertices]

theorem coveredVertices_append :
    G.coveredVertices (W₁ ++ W₂) = G.coveredVertices W₁ ∪ G.coveredVertices W₂ := by
  ext x
  simp only [mem_coveredVertices_iff, List.mem_append, Set.mem_union]
  constructor
  · rintro ⟨e, he | he, hx⟩
    exacts [Or.inl ⟨e, he, hx⟩, Or.inr ⟨e, he, hx⟩]
  · rintro (⟨e, he, hx⟩ | ⟨e, he, hx⟩)
    exacts [⟨e, Or.inl he, hx⟩, ⟨e, Or.inr he, hx⟩]

/-- Every vertex on an edge of the graph is a vertex of the graph. -/
theorem coveredVertices_subset_vertexSet : G.coveredVertices W ⊆ V(G) :=
  fun _ ⟨_, _, hx⟩ ↦ hx.vertex_mem

theorem walkVertices_subset_vertexSet (hu : u ∈ V(G)) : G.walkVertices u W ⊆ V(G) :=
  Set.insert_subset hu coveredVertices_subset_vertexSet

/-- Moving the visited set across a first step, forwards: a vertex the walk visits is either
the vertex it departs from or a vertex the rest of it visits. This is where the step lemma is
used — the edge `e` has only the two ends `u` and `w`, so a vertex on `e` is one of them. -/
theorem mem_walkVertices_cons (hl : G.IsLink e u w) (hx : x ∈ G.walkVertices u (e :: W)) :
    x = u ∨ x ∈ G.walkVertices w W := by
  rcases mem_walkVertices_iff.1 hx with rfl | ⟨f, hf, hxf⟩
  · exact Or.inl rfl
  rcases List.mem_cons.1 hf with rfl | hf
  · rcases hxf.eq_or_eq_of_isLink hl with rfl | rfl
    exacts [Or.inl rfl, Or.inr mem_walkVertices_self]
  · exact Or.inr (mem_walkVertices_of_mem_covered ⟨f, hf, hxf⟩)

/-- Moving the visited set across a first step, backwards. -/
theorem mem_walkVertices_cons_of_mem (hl : G.IsLink e u w) (hx : x ∈ G.walkVertices w W) :
    x ∈ G.walkVertices u (e :: W) := by
  rcases mem_walkVertices_iff.1 hx with rfl | hx
  · exact mem_walkVertices_of_mem_covered ⟨e, List.mem_cons_self, hl.inc_right⟩
  · exact mem_walkVertices_of_mem_covered (coveredVertices_mono (List.subset_cons_self _ _) hx)

/-! ### Walks -/

/-- `G.IsWalk u W v` : the edges of `W`, in order, walk from `u` to `v` in `G`. Each edge is
taken from the vertex the previous one arrived at; the list is read at its head, so the
relation is built at the source end. -/
inductive IsWalk (G : Graph α β) : α → List β → α → Prop
  /-- Standing still at a vertex of the graph is a walk. -/
  | nil {x : α} (hx : x ∈ V(G)) : G.IsWalk x [] x
  /-- Taking an edge from the source of a walk prepends it. -/
  | cons {u w v : α} {e : β} {W : List β} (hl : G.IsLink e u w) (hW : G.IsWalk w W v) :
      G.IsWalk u (e :: W) v

theorem IsWalk.single (hl : G.IsLink e u v) : G.IsWalk u [e] v :=
  .cons hl (.nil hl.right_mem)

theorem IsWalk.left_mem (h : G.IsWalk u W v) : u ∈ V(G) := by
  cases h with
  | nil hx => exact hx
  | cons hl _ => exact hl.left_mem

theorem IsWalk.right_mem (h : G.IsWalk u W v) : v ∈ V(G) := by
  induction h with
  | nil hx => exact hx
  | cons _ _ ih => exact ih

/-- The edges of a walk are edges of the graph. -/
theorem IsWalk.edge_mem (h : G.IsWalk u W v) (he : e ∈ W) : e ∈ E(G) := by
  induction h with
  | nil => simp at he
  | cons hl _ ih =>
    rcases List.mem_cons.1 he with rfl | he
    exacts [hl.edge_mem, ih he]

theorem IsWalk.edgeSet_subset (h : G.IsWalk u W v) : ∀ e ∈ W, e ∈ E(G) := fun _ he ↦ h.edge_mem he

theorem IsWalk.target_mem_walkVertices (h : G.IsWalk u W v) : v ∈ G.walkVertices u W := by
  induction h with
  | nil => exact mem_walkVertices_self
  | cons hl _ ih => exact mem_walkVertices_cons_of_mem hl ih

/-- Every vertex a walk visits is a vertex of the graph — with no hypothesis, since the
empty walk already stands at one. -/
theorem IsWalk.walkVertices_subset (h : G.IsWalk u W v) : G.walkVertices u W ⊆ V(G) :=
  walkVertices_subset_vertexSet h.left_mem

@[simp]
theorem isWalk_nil_iff : G.IsWalk u [] v ↔ u = v ∧ u ∈ V(G) := by
  constructor
  · rintro ⟨hx⟩; exact ⟨rfl, hx⟩
  · rintro ⟨rfl, hx⟩; exact .nil hx

theorem IsWalk.eq_of_nil (h : G.IsWalk u [] v) : u = v := (isWalk_nil_iff.1 h).1

/-- The step lemma, run along a whole walk: naming the edges determines the vertices, so a
walk from a given source along a given edge list arrives nowhere else. Its engine is that an
edge has only two ends, `Graph.IsLink.right_unique`, which holds in Mathlib's `Graph` with no
distinctness hypothesis (a loop arrives back where it started, deterministically). -/
theorem IsWalk.target_unique (h : G.IsWalk u W v) (h' : G.IsWalk u W w) : v = w := by
  induction h generalizing w with
  | nil hx => exact h'.eq_of_nil.symm ▸ rfl
  | @cons u w' v e W hl _ ih =>
    cases h' with
    | cons hl' hW' => exact ih (hl.right_unique hl' ▸ hW')

/-- Walks concatenate, with no side condition. -/
theorem IsWalk.append (h₁ : G.IsWalk u W₁ w) (h₂ : G.IsWalk w W₂ v) :
    G.IsWalk u (W₁ ++ W₂) v := by
  induction h₁ with
  | nil => simpa using h₂
  | cons hl _ ih => exact .cons hl (ih h₂)

/-- A walk runs backwards along the reverse of its edge list, with no side condition. -/
theorem IsWalk.reverse (h : G.IsWalk u W v) : G.IsWalk v W.reverse u := by
  induction h with
  | nil hx => simpa using IsWalk.nil hx
  | @cons u w v e W hl _ ih =>
    rw [List.reverse_cons]
    exact ih.append (IsWalk.single hl.symm)

/-- A walk in a subgraph is a walk in the graph. -/
theorem IsWalk.mono (hHG : H ≤ G) (h : H.IsWalk u W v) : G.IsWalk u W v := by
  induction h with
  | nil hx => exact .nil (hHG.vertexSet_mono hx)
  | cons hl _ ih => exact .cons (hl.mono hHG) ih

/-- A walk of a graph whose edges all survive into a subgraph is a walk of that subgraph.
This is the direction a deletion argument needs: an edge is removed, and a walk that never
used it is still there. -/
theorem IsWalk.anti (hHG : H ≤ G) (h : G.IsWalk u W v) (hu : u ∈ V(H))
    (hE : ∀ e ∈ W, e ∈ E(H)) : H.IsWalk u W v := by
  induction h with
  | nil => exact .nil hu
  | @cons u w v e W hl _ ih =>
    have he : e ∈ E(H) := hE e List.mem_cons_self
    have hl' : H.IsLink e u w := (hHG.isLink_iff he).2 hl
    exact .cons hl' (ih hl'.right_mem fun f hf ↦ hE f (List.mem_cons_of_mem _ hf))

/-- A walk that starts inside a set of vertices and ends outside it crosses the boundary
along one of its own edges. -/
theorem IsWalk.crossing {S : Set α} (h : G.IsWalk u W v) (hu : u ∈ S) (hv : v ∉ S) :
    ∃ e ∈ W, ∃ x y, G.IsLink e x y ∧ x ∈ S ∧ y ∉ S := by
  induction h with
  | nil => exact absurd hu hv
  | @cons u w v e W hl _ ih =>
    by_cases hw : w ∈ S
    · obtain ⟨f, hf, x, y, hxy, hx, hy⟩ := ih hw hv
      exact ⟨f, List.mem_cons_of_mem _ hf, x, y, hxy, hx, hy⟩
    · exact ⟨e, List.mem_cons_self, u, w, hl, hu, hw⟩

/-! ### Paths -/

/-- `G.IsPath u W v` : a walk from `u` to `v` that never returns to a vertex it has left.
The condition is carried step by step — the vertex a step departs from is not among those the
rest of the path visits — rather than imposed afterwards on a computed vertex list. -/
inductive IsPath (G : Graph α β) : α → List β → α → Prop
  /-- Standing still at a vertex of the graph is a path. -/
  | nil {x : α} (hx : x ∈ V(G)) : G.IsPath x [] x
  /-- A step onto a path is allowed when the vertex it departs from is fresh. -/
  | cons {u w v : α} {e : β} {W : List β} (hl : G.IsLink e u w) (hW : G.IsPath w W v)
      (hfresh : u ∉ G.walkVertices w W) : G.IsPath u (e :: W) v

theorem IsPath.isWalk (h : G.IsPath u W v) : G.IsWalk u W v := by
  induction h with
  | nil hx => exact .nil hx
  | cons hl _ _ ih => exact .cons hl ih

theorem IsPath.left_mem (h : G.IsPath u W v) : u ∈ V(G) := h.isWalk.left_mem

theorem IsPath.right_mem (h : G.IsPath u W v) : v ∈ V(G) := h.isWalk.right_mem

theorem IsPath.edge_mem (h : G.IsPath u W v) (he : e ∈ W) : e ∈ E(G) := h.isWalk.edge_mem he

/-- One edge between two distinct vertices is a path. -/
theorem IsPath.single (hl : G.IsLink e u v) (huv : u ≠ v) : G.IsPath u [e] v :=
  .cons hl (.nil hl.right_mem) (by simpa using huv)

/-- A path's step never departs from where it arrives: the freshness clause already says so,
because a walk always visits its own source. -/
theorem IsPath.cons_ne (hW : G.IsPath w W v) (hfresh : u ∉ G.walkVertices w W) : u ≠ w := by
  rintro rfl
  exact hfresh mem_walkVertices_self

/-- **A path never takes a loop.** This is why nothing in this file has to assume the graph is
loopless: a step along a loop would depart from the vertex it arrives at, which the freshness
clause forbids. -/
theorem IsPath.not_isLoopAt (h : G.IsPath u W v) (he : e ∈ W) (x : α) : ¬ G.IsLoopAt e x := by
  induction h with
  | nil => simp at he
  | @cons u w v f W hl hW hfresh ih =>
    rcases List.mem_cons.1 he with rfl | he
    · intro hloop
      -- `hloop : G.IsLink e x x` shares an edge with `hl : G.IsLink e u w`, so `u = w`.
      rcases hl.eq_and_eq_or_eq_and_eq hloop with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        exact IsPath.cons_ne hW hfresh rfl
    · exact ih he

/-- A path takes no edge twice: an edge it took again would put the vertex it departed from
back among the ones the rest of the path visits. -/
theorem IsPath.nodup (h : G.IsPath u W v) : W.Nodup := by
  induction h with
  | nil => exact List.nodup_nil
  | @cons u w v e W hl hW hfresh ih =>
    refine List.nodup_cons.2 ⟨fun he ↦ hfresh ?_, ih⟩
    exact mem_walkVertices_of_mem_covered ⟨e, he, hl.inc_left⟩

/-- A path in a subgraph is a path in the graph: the freshness clause reads only which
vertices the remaining edges touch, and a subgraph's edges have the same ends there. -/
theorem IsPath.mono (hHG : H ≤ G) (h : H.IsPath u W v) : G.IsPath u W v := by
  induction h with
  | nil hx => exact .nil (hHG.vertexSet_mono hx)
  | @cons u w v e W hl hW hfresh ih =>
    refine .cons (hl.mono hHG) ih fun hmem ↦ hfresh ?_
    -- Freshness travels because `H`'s edges link the same pairs in `G`.
    rcases mem_walkVertices_iff.1 hmem with rfl | ⟨f, hf, hinc⟩
    · exact mem_walkVertices_self
    · obtain ⟨y, hy⟩ := hinc
      exact mem_walkVertices_of_mem_covered
        ⟨f, hf, ((hHG.isLink_iff (hW.isWalk.edge_mem hf)).2 hy).inc_left⟩

theorem IsPath.target_mem_walkVertices (h : G.IsPath u W v) : v ∈ G.walkVertices u W :=
  h.isWalk.target_mem_walkVertices

/-- A path grows at its **target** end. The relation is built at the source end, so this is
the direction that has to be worked for; it is what reversal runs on. -/
theorem IsPath.extend_at_target (h : G.IsPath u P w) (hl : G.IsLink e w v)
    (hv : v ∉ G.walkVertices u P) : G.IsPath u (P ++ [e]) v := by
  induction h with
  | nil hx =>
    rw [walkVertices_nil] at hv
    exact List.nil_append _ ▸ IsPath.single hl (Ne.symm hv)
  | @cons u w₀ w f P₀ hl₀ hP₀ hfresh ih =>
    have hv₀ : v ∉ G.walkVertices w₀ P₀ := fun hmem ↦ hv (mem_walkVertices_cons_of_mem hl₀ hmem)
    refine List.cons_append .. ▸ .cons hl₀ (ih hl hv₀) fun hmem ↦ ?_
    -- The departure vertex is still fresh: the only new edge is `e`, whose ends are the old
    -- target `w` — already visited — and `v`, which the source is not.
    rcases mem_walkVertices_iff.1 hmem with rfl | hcov
    · exact hfresh mem_walkVertices_self
    rw [coveredVertices_append] at hcov
    rcases hcov with hcov | ⟨f', hf', hinc⟩
    · exact hfresh (mem_walkVertices_of_mem_covered hcov)
    · obtain rfl : f' = e := by simpa using hf'
      rcases hinc.eq_or_eq_of_isLink hl with rfl | rfl
      · exact hfresh hP₀.target_mem_walkVertices
      · exact hv mem_walkVertices_self

/-- A path runs backwards over the same edges. -/
theorem IsPath.reverse (h : G.IsPath u W v) : G.IsPath v W.reverse u := by
  induction h with
  | nil hx => simpa using IsPath.nil hx
  | @cons u w v e W hl hW hfresh ih =>
    rw [List.reverse_cons]
    refine ih.extend_at_target hl.symm fun hmem ↦ hfresh ?_
    -- `u` avoids everything the rest of the path visits, and reversal changes none of that.
    rw [walkVertices_reverse] at hmem
    rcases mem_walkVertices_iff.1 hmem with rfl | hcov
    · exact hW.target_mem_walkVertices
    · exact mem_walkVertices_of_mem_covered hcov

/-- **Cutting a path at a vertex it passes through.** A path through `x` has a piece of itself
running from `x` to its target, and that piece uses only the path's own edges. This is the
engine of `Graph.IsWalk.contains_path`: when the next vertex is already on the path built so
far, the path is cut there instead of extended, so nothing ever gets longer. -/
theorem IsPath.from_visited (h : G.IsPath u W v) (hx : x ∈ G.walkVertices u W) :
    ∃ T, G.IsPath x T v ∧ T ⊆ W := by
  induction h with
  | nil hx' =>
    rw [walkVertices_nil] at hx
    obtain rfl := hx
    exact ⟨[], .nil hx', List.nil_subset _⟩
  | @cons u w v e W hl hW hfresh ih =>
    rcases mem_walkVertices_cons hl hx with rfl | hx'
    · exact ⟨e :: W, .cons hl hW hfresh, List.Subset.refl _⟩
    · obtain ⟨T, hT, hTW⟩ := ih hx'
      exact ⟨T, hT, List.Subset.trans hTW (List.subset_cons_self _ _)⟩

/-- A path splits at any vertex it visits, and the far half never returns to the source.
`Graph.IsPath.from_visited` is the suffix alone; the prefix is the awkward half, since the
relation is built at the source end and the prefix is what the induction has to carry
forward. -/
theorem IsPath.split (h : G.IsPath u W v) (hx : x ∈ G.walkVertices u W) :
    ∃ W₁ W₂, W = W₁ ++ W₂ ∧ G.IsPath u W₁ x ∧ G.IsPath x W₂ v ∧
      (x = u ∨ u ∉ G.walkVertices x W₂) := by
  induction h with
  | nil hx' =>
    rw [walkVertices_nil] at hx
    obtain rfl := hx
    exact ⟨[], [], rfl, .nil hx', .nil hx', Or.inl rfl⟩
  | @cons u w v e W hl hW hfresh ih =>
    rcases mem_walkVertices_cons hl hx with rfl | hx'
    · exact ⟨[], e :: W, rfl, .nil hl.left_mem, .cons hl hW hfresh, Or.inl rfl⟩
    obtain ⟨W₁, W₂, rfl, h₁, h₂, -⟩ := ih hx'
    have hsub₁ : W₁ ⊆ W₁ ++ W₂ := List.subset_append_left _ _
    have hsub₂ : W₂ ⊆ W₁ ++ W₂ := List.subset_append_right _ _
    refine ⟨e :: W₁, W₂, rfl, .cons hl h₁ fun hmem ↦ hfresh (walkVertices_mono hsub₁ hmem),
      h₂, Or.inr fun hmem ↦ hfresh ?_⟩
    -- The far half's edges are among the rest, which the source already avoided.
    rcases mem_walkVertices_iff.1 hmem with rfl | hcov
    · exact hx'
    · exact mem_walkVertices_of_mem_covered (coveredVertices_mono hsub₂ hcov)

/-- **Every walk contains a path** between the same two vertices, using only the walk's own
edges. This is the blueprint's "shorten an arbitrary walk at repeated vertices"; the
induction never lengthens anything, because the only alternative to prepending an edge is to
cut the path already built (`Graph.IsPath.from_visited`). -/
theorem IsWalk.contains_path (h : G.IsWalk u W v) : ∃ P, G.IsPath u P v ∧ P ⊆ W := by
  induction h with
  | nil hx => exact ⟨[], .nil hx, List.Subset.refl _⟩
  | @cons u w v e W hl hW ih =>
    obtain ⟨P, hP, hPW⟩ := ih
    by_cases hu : u ∈ G.walkVertices w P
    · -- The step lands on the path already built: cut it there rather than extend it.
      obtain ⟨T, hT, hTP⟩ := hP.from_visited hu
      exact ⟨T, hT, List.Subset.trans (List.Subset.trans hTP hPW) (List.subset_cons_self _ _)⟩
    · exact ⟨e :: P, .cons hl hP hu, List.cons_subset_cons _ hPW⟩

/-! ### Reachability -/

/-- `G.Reaches u v` : some walk of `G` runs from `u` to `v`. Stated with a walk rather than a
path because walks are what arguments build — they concatenate and reverse with no side
condition — and a path is recovered on demand (`Graph.Reaches.exists_isPath`). -/
def Reaches (G : Graph α β) (u v : α) : Prop := ∃ W, G.IsWalk u W v

theorem Reaches.left_mem (h : G.Reaches u v) : u ∈ V(G) := h.choose_spec.left_mem

theorem Reaches.right_mem (h : G.Reaches u v) : v ∈ V(G) := h.choose_spec.right_mem

@[refl]
theorem Reaches.refl (hu : u ∈ V(G)) : G.Reaches u u := ⟨[], .nil hu⟩

theorem Reaches.symm (h : G.Reaches u v) : G.Reaches v u :=
  let ⟨W, hW⟩ := h; ⟨W.reverse, hW.reverse⟩

theorem Reaches.trans (h₁ : G.Reaches u v) (h₂ : G.Reaches v w) : G.Reaches u w :=
  let ⟨W₁, hW₁⟩ := h₁; let ⟨W₂, hW₂⟩ := h₂; ⟨W₁ ++ W₂, hW₁.append hW₂⟩

theorem reaches_comm : G.Reaches u v ↔ G.Reaches v u := ⟨Reaches.symm, Reaches.symm⟩

theorem Reaches.of_isLink (hl : G.IsLink e u v) : G.Reaches u v := ⟨[e], .single hl⟩

theorem Reaches.of_adj (h : G.Adj u v) : G.Reaches u v :=
  let ⟨_, hl⟩ := h; .of_isLink hl

/-- Whatever a walk reaches, a path reaches. -/
theorem Reaches.exists_isPath (h : G.Reaches u v) : ∃ P, G.IsPath u P v :=
  let ⟨_, hW⟩ := h; let ⟨P, hP, _⟩ := hW.contains_path; ⟨P, hP⟩

theorem Reaches.mono (hHG : H ≤ G) (h : H.Reaches u v) : G.Reaches u v :=
  let ⟨W, hW⟩ := h; ⟨W, hW.mono hHG⟩

/-! ### Connectedness -/

/-- A graph is connected when it has a vertex and every vertex reaches every other. The
nonemptiness clause is not bureaucracy: it is what makes the counting statements about trees
true as stated. -/
def Connected (G : Graph α β) : Prop :=
  V(G).Nonempty ∧ ∀ ⦃u⦄, u ∈ V(G) → ∀ ⦃v⦄, v ∈ V(G) → G.Reaches u v

theorem Connected.nonempty (h : G.Connected) : V(G).Nonempty := h.1

theorem Connected.reaches (h : G.Connected) (hu : u ∈ V(G)) (hv : v ∈ V(G)) : G.Reaches u v :=
  h.2 hu hv

/-- A graph is connected as soon as one vertex reaches all the others: reachability is
symmetric and transitive, so a common hub joins every pair. -/
theorem Connected.of_hub (hu : u ∈ V(G)) (h : ∀ v ∈ V(G), G.Reaches u v) : G.Connected :=
  ⟨⟨u, hu⟩, fun _ hx _ hy ↦ ((h _ hx).symm).trans (h _ hy)⟩

/-- In a connected graph any two vertices are joined by a path — the blueprint's imported
fact about finite graphs, with the finiteness it does not actually need dropped. -/
theorem Connected.exists_isPath (h : G.Connected) (hu : u ∈ V(G)) (hv : v ∈ V(G)) :
    ∃ P, G.IsPath u P v :=
  (h.reaches hu hv).exists_isPath

/-! ### Transferring walks and paths along an inclusion or a deletion

`IsWalk.anti` above pulls a walk down an inclusion. These are its companions, factored here
because both the cycle module and the two-connectivity module reached for them independently.
-/

theorem coveredVertices_mono_of_le (hHG : H ≤ G) : H.coveredVertices W ⊆ G.coveredVertices W :=
  fun _ ⟨f, hf, y, hy⟩ ↦ ⟨f, hf, y, hy.mono hHG⟩

theorem walkVertices_mono_of_le (hHG : H ≤ G) : H.walkVertices u W ⊆ G.walkVertices u W :=
  Set.insert_subset_insert (coveredVertices_mono_of_le hHG)

/-- A path of a graph whose edges all survive into a subgraph is a path of that subgraph —
the companion of `Graph.IsWalk.anti`, which it is otherwise identical to. Freshness comes
down the inclusion because the subgraph's edges touch no vertices the graph's do not. -/
theorem IsPath.anti (hHG : H ≤ G) (h : G.IsPath u W v) (hu : u ∈ V(H))
    (hE : ∀ e ∈ W, e ∈ E(H)) : H.IsPath u W v := by
  induction h with
  | nil => exact .nil hu
  | @cons u w v e W hl hW hfresh ih =>
    have he : e ∈ E(H) := hE e List.mem_cons_self
    have hl' : H.IsLink e u w := (hHG.isLink_iff he).2 hl
    exact .cons hl' (ih hl'.right_mem fun f hf ↦ hE f (List.mem_cons_of_mem _ hf))
      fun hmem ↦ hfresh (walkVertices_mono_of_le hHG hmem)

theorem mem_edgeSet_deleteEdges_iff {F : Set β} {f : β} :
    f ∈ E(G.deleteEdges F) ↔ f ∈ E(G) ∧ f ∉ F := by
  simp

/-- A walk that avoids the deleted names survives the deletion. -/
theorem IsWalk.deleteEdges {F : Set β} (h : G.IsWalk u W v) (hW : ∀ f ∈ W, f ∉ F) :
    (G.deleteEdges F).IsWalk u W v :=
  h.anti deleteEdges_le (by simpa using h.left_mem)
    fun f hf ↦ mem_edgeSet_deleteEdges_iff.2 ⟨h.edge_mem hf, hW f hf⟩

end Graph

end BundlePart373

section BundlePart374
/- Source: dev/planar_search/schoenflies_port/Schoenflies/Graph/Cycle.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/



/-!
# Cycles, acyclicity and bridges

This file sits directly on `Schoenflies/Graph/Walk.lean` and answers one question: which
edges of a multigraph lie on a cycle. Its main theorem is the blueprint's cycle criterion —
an edge lies on a cycle exactly when deleting it leaves its two ends joined — and a bridge is
read off it.

## A cycle is presented through one of its edges

`G.IsCycleThrough e u v D` is an edge `e` linking `u` to `v`, together with a **path** `D`
from `u` to `v` that does not use `e`. The closed walk is never assembled.

This is not a weakening. Every question the blueprint asks about a cycle is asked *at an
edge* — is this edge on a cycle, does deleting it disconnect its ends, is it a bridge, can it
be deleted from a spanning subgraph — so the edge is always available to present the cycle
through. And presenting it this way is what makes the definition short: the blueprint's
"connected subgraph in which every vertex has degree exactly two" would have to rule out, by
hand, every repetition that a closed walk can contain, whereas `Graph.IsPath` already forbids
them. The blueprint's own proof of the criterion runs in exactly this shape ("take a shortest
walk from `x` to `y` avoiding `e`; a shortest walk repeats no vertex, so it is a simple
path").

**Length two is included, and is why edges are names.** Two parallel edges — the same pair of
ends, two different names — are a cycle: one of them is `e`, the other is the one-edge path
`D`. The blueprint needs those ("two-vertex cycles do occur below, as boundaries of faces
created by overlays and by ears parallel to an existing edge"), and a walk that named
vertices could not tell the two apart.

## Loops

Mathlib's `Graph` allows an edge with both ends equal. **A loop is taken to be a cycle of
length one**, which is the usual convention and also what the blueprint's own definition
gives (a loop contributes two to the degree of its vertex, so the subgraph consisting of a
loop and its vertex is connected with every vertex of degree two). It comes out of the
definition here for free: `G.IsLink e x x` together with the empty path at `x`, which does
not use `e`, is a cycle through `e`. So `Graph.liesOnCycle_of_isLoopAt` needs no proof, no
graph is acyclic while carrying a loop, and no bridge is a loop. Nothing in this file
hypothesises looplessness.

## Deletion

Edge deletion is Mathlib's `Graph.deleteEdges`, not a new definition; `G.deleteEdges {e}` is
the graph with the single name `e` removed. What this file adds is the transfer interface —
a walk or a path survives a deletion exactly when it never took a deleted edge — which is the
whole content of a deletion argument, since which vertices an edge joins is not a question a
subgraph can answer differently. `Graph.IsWalk.anti` from `Walk.lean` is the engine;
`Graph.IsPath.anti` is proved here, since freshness has to be carried down too.

## Blueprint

* `Graph.liesOnCycle_iff_deleteEdges_reaches` — `lem:cycle-criterion`, "in a finite graph, an
  edge lies on a cycle if and only if deleting it does not disconnect its endpoints", both
  directions, with the finiteness the proof does not use dropped. The two halves are
  `Graph.LiesOnCycle.deleteEdges_reaches` and `Graph.LiesOnCycle.of_deleteEdges_reaches`.
* `Graph.IsSchoenfliesBridge`, `Graph.isBridge_iff_not_reaches` — the bridges of
  `lem:subdivision-ear-preserve` ("a 2-connected graph has no bridge. Indeed, if `uv` were a
  bridge, the two components of `G - uv` …"), stated as the separation of the two ends.
* `Graph.IsAcyclic`, `Graph.Connected.deleteEdges_singleton` — the acyclicity underneath
  `lem:three-leaf-tree`, and the minimal spanning subgraph of the H5 construction ("take a
  minimal connected subgraph `T_i` spanning the three terminals. It is a tree: an edge of a
  cycle could be deleted"), which is exactly the statement that deleting an edge on a cycle
  keeps the graph connected.
* `Graph.IsPath.chord_liesOnCycle`, `Graph.IsAcyclic.mem_of_isLink_of_mem_walkVertices` — the
  step of `lem:three-leaf-tree`'s proof that says "a second neighbor on the path would close
  a cycle"; the form the tree module's longest-path argument consumes.
-/

open Set

variable {α β : Type*} {G H : Graph α β} {u v w x y : α} {e f : β} {F : Set β} {W P D : List β}

namespace Graph

/-! ### Visited vertices along an inclusion

`Walk.lean` proves `walkVertices` monotone in the edge list. It is also monotone in the
graph, which is what pulling a path *down* into a subgraph needs: the freshness clause of a
path speaks about the subgraph's visited set, and that is the smaller one. -/

/-! ### Edge deletion

`Graph.deleteEdges` is Mathlib's. These are the four transfer lemmas every deletion argument
below reduces to. -/

/-- Deleting edges never removes a vertex, so a walk in the deletion is a walk. -/
theorem IsWalk.of_deleteEdges (h : (G.deleteEdges F).IsWalk u W v) : G.IsWalk u W v :=
  h.mono deleteEdges_le

/-- Conversely, a walk in the deletion could not have used a deleted name. -/
theorem IsWalk.notMem_of_deleteEdges (h : (G.deleteEdges F).IsWalk u W v) (hf : f ∈ W) :
    f ∉ F :=
  (mem_edgeSet_deleteEdges_iff.1 (h.edge_mem hf)).2

theorem IsPath.of_deleteEdges (h : (G.deleteEdges F).IsPath u W v) : G.IsPath u W v :=
  h.mono deleteEdges_le

theorem IsPath.deleteEdges (h : G.IsPath u W v) (hW : ∀ f ∈ W, f ∉ F) :
    (G.deleteEdges F).IsPath u W v :=
  h.anti deleteEdges_le (by simpa using h.left_mem)
    fun f hf ↦ mem_edgeSet_deleteEdges_iff.2 ⟨h.edge_mem hf, hW f hf⟩

theorem IsPath.notMem_of_deleteEdges (h : (G.deleteEdges F).IsPath u W v) (hf : f ∈ W) :
    f ∉ F :=
  h.isWalk.notMem_of_deleteEdges hf

theorem Reaches.of_deleteEdges (h : (G.deleteEdges F).Reaches u v) : G.Reaches u v :=
  h.mono deleteEdges_le

theorem IsWalk.reaches_deleteEdges (h : G.IsWalk u W v) (hW : ∀ f ∈ W, f ∉ F) :
    (G.deleteEdges F).Reaches u v :=
  ⟨W, h.deleteEdges hW⟩

/-! ### Cycles -/

/-- `G.IsCycleThrough e u v D` : the edge `e` links `u` to `v`, and `D` is a path from `u`
back to `v` that does not use `e`. The cycle is `e` together with `D`; it is presented
through `e` because that is the edge every question is asked about. -/
def IsCycleThrough (G : Graph α β) (e : β) (u v : α) (D : List β) : Prop :=
  G.IsLink e u v ∧ G.IsPath u D v ∧ e ∉ D

/-- `G.LiesOnCycle e` : the edge `e` lies on a cycle of `G`. -/
def LiesOnCycle (G : Graph α β) (e : β) : Prop := ∃ u v D, G.IsCycleThrough e u v D

theorem IsCycleThrough.isLink (h : G.IsCycleThrough e u v D) : G.IsLink e u v := h.1

theorem IsCycleThrough.isPath (h : G.IsCycleThrough e u v D) : G.IsPath u D v := h.2.1

theorem IsCycleThrough.notMem (h : G.IsCycleThrough e u v D) : e ∉ D := h.2.2

theorem IsCycleThrough.liesOnCycle (h : G.IsCycleThrough e u v D) : G.LiesOnCycle e :=
  ⟨u, v, D, h⟩

theorem liesOnCycle_iff : G.LiesOnCycle e ↔ ∃ u v D, G.IsCycleThrough e u v D := Iff.rfl

/-- An edge on a cycle is an edge of the graph. There is no converse hypothesis to carry
around: `Graph.IsLink` already forces it. -/
theorem LiesOnCycle.edge_mem (h : G.LiesOnCycle e) : e ∈ E(G) :=
  let ⟨_, _, _, hc⟩ := h; hc.isLink.edge_mem

/-- **A loop is a cycle of length one.** The path back is the empty one, which trivially
avoids the loop. -/
theorem liesOnCycle_of_isLoopAt (h : G.IsLoopAt e x) : G.LiesOnCycle e :=
  ⟨x, x, [], h, .nil h.left_mem, List.not_mem_nil⟩

/-- **Two parallel edges are a cycle**, on both of them. This is the length-two case, and the
reason a walk names its edges. -/
theorem liesOnCycle_of_parallel (h : G.IsLink e u v) (h' : G.IsLink f u v) (hef : e ≠ f) :
    G.LiesOnCycle e := by
  by_cases huv : u = v
  · subst huv
    exact liesOnCycle_of_isLoopAt h
  exact ⟨u, v, [f], h, .single h' huv, by simpa using hef⟩

/-- A cycle of a subgraph is a cycle of the graph. -/
theorem LiesOnCycle.mono (hHG : H ≤ G) (h : H.LiesOnCycle e) : G.LiesOnCycle e :=
  let ⟨u, v, D, hl, hP, hD⟩ := h
  ⟨u, v, D, hl.mono hHG, hP.mono hHG, hD⟩

/-! ### The cycle criterion

The blueprint's `lem:cycle-criterion`. Both directions are one step each, once the deletion
interface above is in place: forwards, the detour of the cycle is a walk that avoided `e`;
backwards, a path in the deletion cannot have used `e` because `e` is not there. -/

/-- **An edge on a cycle is not needed to join its ends**: the rest of the cycle still does.

The ends are given as an arbitrary pair `u, v` that `e` links, not as the pair the cycle was
presented with — an edge has only two ends, so the two presentations agree up to a swap, and
reachability is symmetric. -/
theorem LiesOnCycle.deleteEdges_reaches (hl : G.IsLink e u v) (h : G.LiesOnCycle e) :
    (G.deleteEdges {e}).Reaches u v := by
  obtain ⟨u', v', D, hl', hP, hD⟩ := h
  -- The detour avoids `e` by definition, so it is still there after `e` goes.
  have hR : (G.deleteEdges {e}).Reaches u' v' :=
    hP.isWalk.reaches_deleteEdges fun f hf hmem ↦ hD (Set.mem_singleton_iff.1 hmem ▸ hf)
  rcases hl.eq_and_eq_or_eq_and_eq hl' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [hR, hR.symm]

/-- **An edge whose deletion leaves its ends joined lies on a cycle.** The route that
survives is a walk of the deletion, hence contains a path of the deletion, and a path of the
deletion cannot have used the name that was deleted. -/
theorem LiesOnCycle.of_deleteEdges_reaches (hl : G.IsLink e u v)
    (h : (G.deleteEdges {e}).Reaches u v) : G.LiesOnCycle e := by
  obtain ⟨D, hD⟩ := h.exists_isPath
  exact ⟨u, v, D, hl, hD.of_deleteEdges, fun hmem ↦ hD.notMem_of_deleteEdges hmem rfl⟩

/-- **The cycle criterion**: an edge lies on a cycle if and only if deleting it does not
disconnect its endpoints. -/
theorem liesOnCycle_iff_deleteEdges_reaches (hl : G.IsLink e u v) :
    G.LiesOnCycle e ↔ (G.deleteEdges {e}).Reaches u v :=
  ⟨LiesOnCycle.deleteEdges_reaches hl, LiesOnCycle.of_deleteEdges_reaches hl⟩

/-- **A walk reroutes around an edge that lies on a cycle**: wherever it took `e`, it can go
the long way round instead. Proved by induction along the walk rather than by splicing the
detour into the edge list, so nothing has to be said about what the spliced list looks
like. -/
theorem IsWalk.reaches_deleteEdges_of_liesOnCycle (h : G.LiesOnCycle e) (hW : G.IsWalk u W v) :
    (G.deleteEdges {e}).Reaches u v := by
  induction hW with
  | nil hx => exact .refl (by simpa using hx)
  | @cons u w v f W hl _ ih =>
    refine Reaches.trans ?_ ih
    by_cases hfe : f = e
    · subst hfe
      exact h.deleteEdges_reaches hl
    · refine (IsWalk.single hl).reaches_deleteEdges fun g hg ↦ ?_
      obtain rfl : g = f := by simpa using hg
      simpa using hfe

/-- **Deleting an edge that lies on a cycle keeps the graph connected** — the blueprint's "it
is a tree: an edge of a cycle could be deleted", which is what makes a minimal connected
spanning subgraph acyclic. -/
theorem Connected.deleteEdges_singleton (hG : G.Connected) (h : G.LiesOnCycle e) :
    (G.deleteEdges {e}).Connected := by
  refine ⟨by simpa using hG.nonempty, fun u hu v hv ↦ ?_⟩
  rw [vertexSet_deleteEdges] at hu hv
  exact (hG.reaches hu hv).choose_spec.reaches_deleteEdges_of_liesOnCycle h

/-! ### Chords

An edge from the source of a path to a vertex the path already visits closes a cycle. This
is the shape in which acyclicity is used: it says a path cannot be extended backwards onto
itself. -/

/-- A chord of a path lies on a cycle: the piece of the path from its source to the far end
of the chord is a path avoiding the chord, so the chord closes it. -/
theorem IsPath.chord_liesOnCycle (hP : G.IsPath u P v) (hl : G.IsLink e u x) (hoff : e ∉ P)
    (hx : x ∈ G.walkVertices u P) : G.LiesOnCycle e := by
  obtain ⟨P₁, P₂, rfl, h₁, -, -⟩ := hP.split hx
  exact ⟨u, x, P₁, hl, h₁, fun hmem ↦ hoff (List.mem_append_left _ hmem)⟩

/-! ### Acyclicity -/

/-- `G.IsAcyclic` : no edge of `G` lies on a cycle. Stated over the edges of `G` because that
is how a tree consumes it — every edge is a bridge — while `Graph.IsAcyclic.not_liesOnCycle`
drops the membership hypothesis for the uses that do not have it to hand. -/
def IsAcyclic (G : Graph α β) : Prop := ∀ ⦃e⦄, e ∈ E(G) → ¬ G.LiesOnCycle e

/-- Acyclicity with no membership hypothesis: an edge on a cycle would be an edge. -/
theorem IsAcyclic.not_liesOnCycle (h : G.IsAcyclic) (e : β) : ¬ G.LiesOnCycle e :=
  fun hc ↦ h hc.edge_mem hc

theorem isAcyclic_iff : G.IsAcyclic ↔ ∀ e, ¬ G.LiesOnCycle e :=
  ⟨fun h e ↦ h.not_liesOnCycle e, fun h _ _ ↦ h _⟩

/-- **An acyclic graph has no loop.** No hypothesis is needed anywhere else in this layer
because of this: looplessness is a consequence of acyclicity, not a side condition on it. -/
theorem IsAcyclic.not_isLoopAt (h : G.IsAcyclic) (e : β) (x : α) : ¬ G.IsLoopAt e x :=
  fun hloop ↦ h.not_liesOnCycle e (liesOnCycle_of_isLoopAt hloop)

/-- **An acyclic graph has no parallel edges.** -/
theorem IsAcyclic.eq_of_isLink (h : G.IsAcyclic) (hl : G.IsLink e u v) (hl' : G.IsLink f u v) :
    e = f := by
  by_contra hef
  exact h.not_liesOnCycle e (liesOnCycle_of_parallel hl hl' hef)

/-- A subgraph of an acyclic graph is acyclic. -/
theorem IsAcyclic.anti (hHG : H ≤ G) (h : G.IsAcyclic) : H.IsAcyclic :=
  fun _ _ hc ↦ h.not_liesOnCycle _ (hc.mono hHG)

theorem IsAcyclic.deleteEdges (h : G.IsAcyclic) (F : Set β) : (G.deleteEdges F).IsAcyclic :=
  h.anti deleteEdges_le

/-- **In an acyclic graph, an edge at the source of a path whose far end the path visits is
one of the path's own edges.** This is the blueprint's "a second neighbor on the path would
close a cycle" — the step that makes the end of a longest path a leaf, which is what the tree
module runs on. -/
theorem IsAcyclic.mem_of_isLink_of_mem_walkVertices (hac : G.IsAcyclic) (hP : G.IsPath u P v)
    (hl : G.IsLink e u x) (hx : x ∈ G.walkVertices u P) : e ∈ P := by
  by_contra hoff
  exact hac.not_liesOnCycle e (hP.chord_liesOnCycle hl hoff hx)

/-! ### Bridges -/

/-- `G.IsSchoenfliesBridge e` : an edge of `G` that lies on no cycle. Equivalently — and this is the
form every use wants — an edge whose deletion separates its two ends
(`Graph.isBridge_iff_not_reaches`). -/
def IsSchoenfliesBridge (G : Graph α β) (e : β) : Prop := e ∈ E(G) ∧ ¬ G.LiesOnCycle e

theorem IsSchoenfliesBridge.edge_mem (h : G.IsSchoenfliesBridge e) : e ∈ E(G) := h.1

theorem IsSchoenfliesBridge.not_liesOnCycle (h : G.IsSchoenfliesBridge e) : ¬ G.LiesOnCycle e := h.2

/-- **Deleting a bridge separates its ends.** -/
theorem IsSchoenfliesBridge.not_reaches (h : G.IsSchoenfliesBridge e) (hl : G.IsLink e u v) :
    ¬ (G.deleteEdges {e}).Reaches u v :=
  fun hR ↦ h.not_liesOnCycle (LiesOnCycle.of_deleteEdges_reaches hl hR)

/-- **An edge whose deletion separates its ends is a bridge.** -/
theorem isBridge_of_not_reaches (hl : G.IsLink e u v)
    (h : ¬ (G.deleteEdges {e}).Reaches u v) : G.IsSchoenfliesBridge e :=
  ⟨hl.edge_mem, fun hc ↦ h (hc.deleteEdges_reaches hl)⟩

/-- **A bridge is exactly an edge whose deletion separates its ends** — the cycle criterion,
negated. -/
theorem isBridge_iff_not_reaches (hl : G.IsLink e u v) :
    G.IsSchoenfliesBridge e ↔ ¬ (G.deleteEdges {e}).Reaches u v :=
  ⟨fun h ↦ h.not_reaches hl, isBridge_of_not_reaches hl⟩

/-- A bridge is never a loop: a loop is a cycle. -/
theorem IsSchoenfliesBridge.not_isLoopAt (h : G.IsSchoenfliesBridge e) (x : α) : ¬ G.IsLoopAt e x :=
  fun hloop ↦ h.not_liesOnCycle (liesOnCycle_of_isLoopAt hloop)

/-- **A graph is acyclic exactly when every one of its edges is a bridge.** This is the form
the tree module wants acyclicity in: "it is a tree — an edge of a cycle could be deleted"
reads backwards as "no edge can be deleted without separating its ends". -/
theorem isAcyclic_iff_forall_isBridge : G.IsAcyclic ↔ ∀ e ∈ E(G), G.IsSchoenfliesBridge e :=
  ⟨fun h _ he ↦ ⟨he, h he⟩, fun h _ he ↦ (h _ he).not_liesOnCycle⟩

theorem IsAcyclic.isBridge (h : G.IsAcyclic) (he : e ∈ E(G)) : G.IsSchoenfliesBridge e := ⟨he, h he⟩

end Graph

end BundlePart374

section BundlePart375
/- Source: dev/planar_search/schoenflies_port/Schoenflies/PolyPath.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/



/-!
# Polygonal paths

A polygonal path is carried by a list of vertices; its `poly` carrier is the union of the
segments joining consecutive entries. This is the combinatorial representation the whole
of Part I works with — by the blueprint's polygonal overlay convention only finite
polygonal objects are ever overlaid, so vertex lists, not parametrizations, are the
primitive.

## Blueprint

* `poly` — the carrier of a polygonal path.
* `exists_poly_of_isPreconnected` — Lemma 1.1 (polygonal connectedness), less the passage
  to a *simple* arc, which needs the finite-graph machinery and is proved with Lemma 1.2.
-/

open Metric Set

namespace Schoenflies

variable {Ω : Set Plane} {x y z : Plane}

/-! ### Segments -/

theorem isCompact_segment (x y : Plane) : IsCompact (segment ℝ x y) := by
  rw [segment_eq_image' ℝ x y]
  exact isCompact_Icc.image (by fun_prop)

/-! ### The carrier of a vertex list -/

/-- The carrier of a polygonal path: the union of the segments joining consecutive vertices.
A single vertex carries itself, so that a path may be constant. -/
def poly : List Plane → Set Plane
  | [] => ∅
  | [v] => {v}
  | u :: v :: rest => segment ℝ u v ∪ poly (v :: rest)

@[simp] theorem poly_nil : poly [] = ∅ := rfl

@[simp] theorem poly_singleton (v : Plane) : poly [v] = {v} := rfl

@[simp] theorem poly_cons_cons (u v : Plane) (rest : List Plane) :
    poly (u :: v :: rest) = segment ℝ u v ∪ poly (v :: rest) := rfl

theorem poly_nonempty : ∀ {vs : List Plane}, vs ≠ [] → (poly vs).Nonempty
  | [], h => absurd rfl h
  | [v], _ => ⟨v, rfl⟩
  | _ :: v :: _, _ => ⟨v, Or.inl (right_mem_segment ℝ _ _)⟩

theorem isCompact_poly : ∀ vs : List Plane, IsCompact (poly vs)
  | [] => by simp
  | [v] => by simp
  | u :: v :: rest => by
    rw [poly_cons_cons]
    exact (isCompact_segment u v).union (isCompact_poly (v :: rest))

/-- Every vertex lies on the carrier. -/
theorem mem_poly_of_mem : ∀ {vs : List Plane} {v : Plane}, v ∈ vs → v ∈ poly vs
  | [], _, h => absurd h (by simp)
  | [_], _, h => by simpa using h
  | u :: w :: rest, v, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact Or.inl (left_mem_segment ℝ _ _)
    · exact Or.inr (mem_poly_of_mem h)

theorem head_mem_poly {vs : List Plane} (h : vs ≠ []) : vs.head h ∈ poly vs :=
  mem_poly_of_mem (List.head_mem h)

theorem getLast_mem_poly {vs : List Plane} (h : vs ≠ []) : vs.getLast h ∈ poly vs :=
  mem_poly_of_mem (List.getLast_mem h)

/-- The carrier of a nonempty vertex list is connected: consecutive segments share a vertex. -/
theorem isConnected_poly : ∀ {vs : List Plane}, vs ≠ [] → IsConnected (poly vs)
  | [], h => absurd rfl h
  | [v], _ => by simpa using isConnected_singleton (x := v)
  | u :: v :: rest, _ => by
    rw [poly_cons_cons]
    refine IsConnected.union ⟨v, right_mem_segment ℝ u v, head_mem_poly (by simp)⟩
      ((convex_segment u v).isConnected ⟨u, left_mem_segment ℝ u v⟩)
      (isConnected_poly (List.cons_ne_nil v rest))

/-- Appending one vertex extends the carrier by one segment. -/
theorem poly_concat : ∀ {vs : List Plane} (h : vs ≠ []) (z : Plane),
    poly (vs ++ [z]) = poly vs ∪ segment ℝ (vs.getLast h) z
  | [], h, _ => absurd rfl h
  | [v], _, z => by
    simp only [List.singleton_append, poly_cons_cons, poly_singleton, List.getLast_singleton]
    rw [union_singleton, insert_eq_self.2 (right_mem_segment ℝ v z), singleton_union,
      insert_eq_self.2 (left_mem_segment ℝ v z)]
  | u :: v :: rest, _, z => by
    simp only [List.cons_append, poly_cons_cons]
    rw [← List.cons_append, poly_concat (List.cons_ne_nil v rest) z,
      List.getLast_cons (List.cons_ne_nil v rest)]
    exact (union_assoc _ _ _).symm

/-! ### Polygonal connectedness -/

/-- Lemma 1.1 (polygonal connectedness), existence half. Any two points of a region are
joined in it by a polygonal path.

The blueprint goes on to make the path *simple*, by subdividing at self-intersections and
taking a simple path in the resulting finite graph; that half is deferred to the graph
module, where the subdivision procedure is available. -/
theorem exists_poly_of_isPreconnected (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hx : x ∈ Ω) (hy : y ∈ Ω) :
    ∃ vs : List Plane, ∃ h : vs ≠ [], poly vs ⊆ Ω ∧ vs.head h = x ∧ vs.getLast h = y := by
  -- `R` is the set of points reachable from `x` by a polygonal path inside `Ω`.
  set R : Set Plane :=
    {w ∈ Ω | ∃ vs : List Plane, ∃ h : vs ≠ [], poly vs ⊆ Ω ∧ vs.head h = x ∧ vs.getLast h = w}
    with hR
  -- Extending a path by a segment inside a convex subset of `Ω` keeps it inside `Ω`. Applied
  -- to a ball this makes `R` open, and applied in the other direction makes `Ω \ R` open.
  have key : ∀ C : Set Plane, Convex ℝ C → C ⊆ Ω → ∀ w ∈ C, ∀ z ∈ C,
      (∃ vs : List Plane, ∃ h : vs ≠ [], poly vs ⊆ Ω ∧ vs.head h = x ∧ vs.getLast h = w) →
      ∃ vs : List Plane, ∃ h : vs ≠ [], poly vs ⊆ Ω ∧ vs.head h = x ∧ vs.getLast h = z := by
    rintro C hC hCΩ w hw z hz ⟨vs, hne, hsub, hhead, hlast⟩
    refine ⟨vs ++ [z], by simp, ?_, ?_, ?_⟩
    · rw [poly_concat hne z, hlast]
      exact union_subset hsub ((hC.segment_subset hw hz).trans hCΩ)
    · rw [List.head_append_of_ne_nil hne]; exact hhead
    · simp
  have hRopen : IsOpen R := by
    rw [isOpen_iff_forall_mem_open]
    rintro w ⟨hw, hpath⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hΩ w hw
    exact ⟨ball w r, fun z hz =>
      ⟨hball hz, key _ (convex_ball w r) hball w (mem_ball_self hr) z hz hpath⟩,
      isOpen_ball, mem_ball_self hr⟩
  have hRcompl : IsOpen (Ω \ R) := by
    rw [isOpen_iff_forall_mem_open]
    rintro w ⟨hw, hwR⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hΩ w hw
    refine ⟨ball w r, fun z hz => ⟨hball hz, fun hzR => ?_⟩, isOpen_ball, mem_ball_self hr⟩
    -- A path to `z` runs back to `w` through the same ball, so `w ∈ R` after all.
    exact hwR ⟨hw, key _ (convex_ball w r) hball z hz w (mem_ball_self hr) hzR.2⟩
  -- `R` is nonempty, open and closed in the preconnected `Ω`, so `R = Ω`.
  have hxR : x ∈ R := ⟨hx, [x], by simp, by simpa using hx, rfl, rfl⟩
  have : y ∈ R := by
    by_contra hyR
    obtain ⟨w, _, hw⟩ := hconn R (Ω \ R) hRopen hRcompl
      (fun w hw => (em (w ∈ R)).imp id fun h => ⟨hw, h⟩) ⟨x, hx, hxR⟩ ⟨y, hy, hy, hyR⟩
    exact hw.2.2 hw.1
  exact this.2

/-- Concatenating two vertex lists that agree at the join concatenates their carriers. The
hypothesis is what makes this true: without it `poly [a] ∪ poly [b] = {a, b}` misses the segment
that `poly [a, b]` carries. -/
theorem poly_append : ∀ {vs : List Plane} (h : vs ≠ []) (w : Plane) (rest : List Plane),
    vs.getLast h = w → poly (vs ++ w :: rest) = poly vs ∪ poly (w :: rest)
  | [], h, _, _, _ => absurd rfl h
  | [v], _, w, rest, hvw => by
    simp only [List.getLast_singleton] at hvw
    subst hvw
    simp [segment_same]
  | u :: v :: tl, _, w, rest, hvw => by
    have h' : (v :: tl).getLast (List.cons_ne_nil v tl) = w := by
      rw [← List.getLast_cons (a := u) (List.cons_ne_nil v tl)]; exact hvw
    simp only [List.cons_append, poly_cons_cons]
    rw [← List.cons_append, poly_append (List.cons_ne_nil v tl) w rest h']
    exact (union_assoc _ _ _).symm

end Schoenflies

end BundlePart375

section BundlePart376
/- Source: dev/planar_search/schoenflies_port/Schoenflies/Polygonal.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/



/-!
# Polygonal sets, and segments as arcs

`IsPolygonal` is the blueprint's set-level predicate: a finite union of line segments, which
here is exactly the carrier of some vertex list.

The theorem the plane-graph layer needs from this module is `isArcBetween_segment`: a
*nondegenerate* segment is an arc between its endpoints. It is what makes the drawing
condition free for a polygonal plane graph — an edge's arc obligation is discharged by the
segment itself, and the distinctness of its ends is already part of well-formedness.

## Blueprint

* `IsPolygonal` — §1, "an arc or curve is polygonal if it is a finite union of line segments".
* `isArcBetween_segment` — a nondegenerate segment is an arc between its endpoints.
-/

open Metric Set

namespace Schoenflies

/-- A set is polygonal when it is the carrier of a finite vertex list, that is, a finite union
of line segments. -/
def IsPolygonal (A : Set Plane) : Prop := ∃ vs : List Plane, A = poly vs

theorem IsPolygonal.isCompact {A : Set Plane} (h : IsPolygonal A) : IsCompact A := by
  obtain ⟨vs, rfl⟩ := h
  exact isCompact_poly vs

@[simp] theorem poly_pair (a b : Plane) : poly [a, b] = segment ℝ a b := by
  rw [poly_cons_cons, poly_singleton]
  exact union_eq_self_of_subset_right (singleton_subset_iff.2 (right_mem_segment ℝ a b))

theorem isPolygonal_segment (a b : Plane) : IsPolygonal (segment ℝ a b) :=
  ⟨[a, b], (poly_pair a b).symm⟩

/-- `lineMap a b` is injective on the unit interval exactly when the segment is
nondegenerate: two parameters differ by a multiple of `b - a`. Exposed separately because the
plane-graph drawing condition asks for the parametrization, not just its image. -/
theorem injOn_lineMap {a b : Plane} (hab : a ≠ b) :
    Set.InjOn (AffineMap.lineMap a b : ℝ → Plane) I := by
  intro s _ t _ hst
  have hba : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  have key : (s - t) • (b - a) = 0 := by
    simp only [AffineMap.lineMap_apply_module] at hst
    linear_combination (norm := module) hst
  rcases smul_eq_zero.1 key with h | h
  · linarith
  · exact absurd h hba

/-- A nondegenerate segment is an arc between its endpoints, parametrized by
`AffineMap.lineMap a b`. -/
theorem isArcBetween_segment {a b : Plane} (hab : a ≠ b) :
    IsArcBetween (segment ℝ a b) a b := by
  refine ⟨AffineMap.lineMap a b, AffineMap.lineMap_continuous.continuousOn, ?_, ?_, ?_, ?_⟩
  · exact injOn_lineMap hab
  · rw [segment_eq_image_lineMap]
  · simp
  · simp

theorem isArc_segment {a b : Plane} (hab : a ≠ b) : IsArc (segment ℝ a b) :=
  (isArcBetween_segment hab).isArc

/-- **A polygonal set is carried by a vertex list running from any of its points to any other.**
The list is written with its two ends displayed, so no `List.head`/`List.getLast` obligations
appear. -/
theorem exists_poly_anchored : ∀ (vs : List Plane), vs ≠ [] → ∀ z w : Plane,
    z ∈ poly vs → w ∈ poly vs → ∃ mid : List Plane, poly (z :: (mid ++ [w])) = poly vs := by
  intro vs
  induction vs with
  | nil => exact fun h => absurd rfl h
  | cons u tl ih =>
    rcases tl with _ | ⟨v, rest⟩
    · -- A one-point carrier: both ends are that point.
      intro _ z w hz hw
      rw [poly_singleton, Set.mem_singleton_iff] at hz hw
      subst hz; subst hw
      exact ⟨[], by simp [segment_same]⟩
    · intro _ z w hz hw
      have hne : (v :: rest) ≠ [] := List.cons_ne_nil v rest
      have hv : v ∈ poly (v :: rest) := mem_poly_of_mem (List.mem_cons_self ..)
      rw [poly_cons_cons] at hz hw
      -- `segment z u ⊆ segment u v` for `z` on the first edge, and likewise for `w`.
      have hsub : ∀ p ∈ segment ℝ u v, segment ℝ p u ⊆ segment ℝ u v := fun p hp =>
        (convex_segment u v).segment_subset hp (left_mem_segment ℝ u v)
      have hsub' : ∀ p ∈ segment ℝ u v, segment ℝ u p ⊆ segment ℝ u v := fun p hp =>
        (convex_segment u v).segment_subset (left_mem_segment ℝ u v) hp
      rcases hz with hz | hz
      · rcases hw with hw | hw
        · -- Both ends on the first edge: run out along the rest of the list and back.
          obtain ⟨Z, hZ⟩ := ih hne v v hv hv
          refine ⟨u :: v :: (Z ++ [v, v, u]), ?_⟩
          have hlast : (z :: u :: (v :: (Z ++ [v]))).getLast (by simp) = v := by
            simp
          have hsplit : z :: ((u :: v :: (Z ++ [v, v, u])) ++ [w])
              = (z :: u :: (v :: (Z ++ [v]))) ++ (v :: u :: [w]) := by
            simp
          have h1 : poly (z :: u :: (v :: (Z ++ [v])))
              = segment ℝ z u ∪ (segment ℝ u v ∪ poly (v :: rest)) := by
            rw [poly_cons_cons, poly_cons_cons, hZ]
          have h2 : poly (v :: u :: [w]) = segment ℝ u v ∪ segment ℝ u w := by
            rw [poly_cons_cons, poly_pair, segment_symm ℝ v u]
          have hd1 : segment ℝ z u ⊆ segment ℝ u v ∪ poly (v :: rest) :=
            (hsub z hz).trans Set.subset_union_left
          have hd2 : segment ℝ u v ∪ segment ℝ u w ⊆ segment ℝ u v ∪ poly (v :: rest) :=
            Set.union_subset Set.subset_union_left ((hsub' w hw).trans Set.subset_union_left)
          rw [hsplit, poly_append (by simp) v (u :: [w]) hlast, h1, h2, poly_cons_cons,
            Set.union_eq_self_of_subset_left hd1, Set.union_eq_self_of_subset_right hd2]
        · -- The far end is on the rest: append its list to the first edge.
          obtain ⟨Y, hY⟩ := ih hne v w hv hw
          refine ⟨u :: v :: Y, ?_⟩
          have hsplit : z :: ((u :: v :: Y) ++ [w]) = z :: u :: (v :: (Y ++ [w])) := by simp
          have hd1 : segment ℝ z u ⊆ segment ℝ u v ∪ poly (v :: rest) :=
            (hsub z hz).trans Set.subset_union_left
          rw [hsplit, poly_cons_cons, poly_cons_cons, hY, poly_cons_cons,
            Set.union_eq_self_of_subset_left hd1]
      · rcases hw with hw | hw
        · -- The near end is on the rest: run to `v`, then out along the first edge.
          obtain ⟨X, hX⟩ := ih hne z v hz hv
          refine ⟨X ++ [v, v, u], ?_⟩
          have hlast : (z :: (X ++ [v])).getLast (by simp) = v := by simp
          have hsplit : z :: ((X ++ [v, v, u]) ++ [w]) = (z :: (X ++ [v])) ++ (v :: u :: [w]) := by
            simp
          have h2 : poly (v :: u :: [w]) = segment ℝ u v ∪ segment ℝ u w := by
            rw [poly_cons_cons, poly_pair, segment_symm ℝ v u]
          rw [hsplit, poly_append (by simp) v (u :: [w]) hlast, hX, h2, poly_cons_cons,
            Set.union_eq_self_of_subset_right (hsub' w hw), Set.union_comm]
        · -- Both ends on the rest: run from one to `v`, out and back along the first edge, on.
          obtain ⟨X, hX⟩ := ih hne z v hz hv
          obtain ⟨Y, hY⟩ := ih hne v w hv hw
          refine ⟨X ++ [v, v, u] ++ (v :: Y), ?_⟩
          have hlast : (z :: (X ++ [v])).getLast (by simp) = v := by simp
          have hsplit : z :: ((X ++ [v, v, u] ++ (v :: Y)) ++ [w])
              = (z :: (X ++ [v])) ++ (v :: u :: (v :: (Y ++ [w]))) := by simp
          have h2 : poly (v :: u :: (v :: (Y ++ [w])))
              = segment ℝ u v ∪ (segment ℝ u v ∪ poly (v :: rest)) := by
            rw [poly_cons_cons, poly_cons_cons, hY, segment_symm ℝ v u]
          have hd1 : segment ℝ u v ⊆ segment ℝ u v ∪ poly (v :: rest) := Set.subset_union_left
          have hd2 : poly (v :: rest) ⊆ segment ℝ u v ∪ poly (v :: rest) := Set.subset_union_right
          rw [hsplit, poly_append (by simp) v (u :: (v :: (Y ++ [w]))) hlast, hX, h2,
            poly_cons_cons, Set.union_eq_self_of_subset_left hd1,
            Set.union_eq_self_of_subset_left hd2]

/-- **Two polygonal sets that meet have a polygonal union.** Anchor both lists at a common
point and concatenate. -/
theorem IsPolygonal.union {A B : Set Plane} (hA : IsPolygonal A) (hB : IsPolygonal B)
    (hmeet : (A ∩ B).Nonempty) : IsPolygonal (A ∪ B) := by
  obtain ⟨vs, rfl⟩ := hA
  obtain ⟨ws, rfl⟩ := hB
  obtain ⟨z, hzA, hzB⟩ := hmeet
  have hvs : vs ≠ [] := by rintro rfl; exact hzA
  have hws : ws ≠ [] := by rintro rfl; exact hzB
  obtain ⟨X, hX⟩ := exists_poly_anchored vs hvs z z hzA hzA
  obtain ⟨Y, hY⟩ := exists_poly_anchored ws hws z z hzB hzB
  refine ⟨(z :: (X ++ [z])) ++ (z :: (Y ++ [z])), ?_⟩
  have hlast : (z :: (X ++ [z])).getLast (by simp) = z := by simp
  rw [poly_append (by simp) z (Y ++ [z]) hlast, hX, hY]

end Schoenflies

end BundlePart376

section BundlePart377
/- Source: dev/planar_search/schoenflies_port/Schoenflies/Graph/CycleJordan.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/





/-!
# The realisation of a cycle is a Jordan curve

A cycle of a plane graph arrives as `Schoenflies/Graph/Cycle.lean` presents it: an edge, and a
path between that edge's two ends which does not use it. Its realisation is the set of points
the arcs of those edges occupy, and the claim is that this set is a Jordan curve.

## The argument is set-level; no parametrisation of a walk is built

The obvious approach — a `walkArc` definition folding `Schoenflies.concatenate` along the edge
list — is the wrong shape twice over. The empty-list base case is a *constant* map, which is
not an arc, so the fold cannot be shown injective at the last step; and threading a
parametrisation through the induction buys nothing, since every consumer wants the point set.

Instead **the existence of the arc is what the induction carries**, in
`Schoenflies.IsArcBetween`. The arcs are chosen inside the induction and the concatenation of
them is chosen by the gluing theorem; no parametrisation is ever named.

## Where the geometry enters

Exactly once, in `Graph.IsDrawing.first_edge_meets_rest`: a common point of the first edge's
arc and the rest of the path is a vertex incident with both edges
(`Graph.IsDrawing.arcs_meet_at_vertex`), hence one of the two ends of the first edge, and the
path's own freshness clause — the vertex a step departs from is not one the rest visits —
forbids it being the source. Taking the same edge again is refused by the *same* clause, so a
separate "the edges of a path are distinct" lemma is not needed.

## Loops

Nothing here hypothesises looplessness, and nothing needs to: `Graph.IsDrawing.ne_of_isLink`
derives it. An edge with equal ends would be drawn by an arc whose parametrisation takes the
same value at `0` and at `1`, which its injectivity forbids. That is what rules out the
degenerate cycle `Graph.liesOnCycle_of_isLoopAt` — a loop with an empty detour — whose
realisation is a single arc and not a Jordan curve.

## Blueprint

* `Graph.edgesCover` — what a *list* of edges occupies. `Graph.pointSet` is the vertices
  together with this, taken over all the edges of the graph.
* `Graph.IsDrawing.path_isArcBetween` — the realisation of a path is an arc between its two
  ends.
* `Graph.IsDrawing.cycle_isJordanCurve` — §"Plane graphs and the utility graph": "in a plane
  graph the realization of a cycle is a Jordan curve: its edges are simple arcs with pairwise
  disjoint interiors, and consecutive edges meet exactly at their shared vertices, so the edge
  arcs concatenate injectively into a simple closed curve".
* `Graph.IsDrawing.cycle_inter` — the meeting condition in full: the detour and the edge meet
  in exactly the edge's two ends. `Schoenflies.IsJordanCurve.of_two_arcs` consumes only one
  inclusion of it, but the equality is what the blueprint asserts.
-/

open Set Schoenflies unitInterval
open scoped Graph

namespace Graph

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}
variable {e f : β} {u v w z : Plane} {W D : List β}

/-! ### What a list of edges occupies -/

/-- The point set of a list of edges: the union of their edge arcs. A walk is a list of edges,
so this is what a walk of a plane graph draws. -/
def edgesCover (drawing : β → ℝ → Plane) (W : List β) : Set Plane :=
  ⋃ e ∈ W, edgeArc drawing e

theorem mem_edgesCover_iff :
    z ∈ edgesCover drawing W ↔ ∃ e ∈ W, z ∈ edgeArc drawing e := by
  simp [edgesCover]

theorem mem_edgesCover (he : e ∈ W) (hz : z ∈ edgeArc drawing e) : z ∈ edgesCover drawing W :=
  mem_edgesCover_iff.2 ⟨e, he, hz⟩

@[simp]
theorem edgesCover_nil : edgesCover drawing ([] : List β) = ∅ := by
  simp [edgesCover]

@[simp]
theorem edgesCover_cons :
    edgesCover drawing (e :: W) = edgeArc drawing e ∪ edgesCover drawing W := by
  ext z
  simp [edgesCover]

theorem edgesCover_mono (h : W ⊆ D) : edgesCover drawing W ⊆ edgesCover drawing D :=
  fun _ hz ↦ let ⟨_, he, hze⟩ := mem_edgesCover_iff.1 hz; mem_edgesCover (h he) hze

/-- A list of edges of the graph occupies part of what the graph occupies. -/
theorem edgesCover_subset_pointSet (hW : ∀ e ∈ W, e ∈ E(G)) :
    edgesCover drawing W ⊆ pointSet G drawing := by
  intro z hz
  obtain ⟨e, he, hze⟩ := mem_edgesCover_iff.1 hz
  exact edgeArc_subset_pointSet (hW e he) hze

/-! ### A plane graph has no loops

This is not a hypothesis anywhere in this file; it is a consequence of the drawing condition,
and it is what makes the degenerate cycle — a loop, with the empty path back — impossible. -/

/-- **An edge of a plane graph has two distinct ends.** An edge with equal ends would be drawn
by an arc whose parametrisation returns to its start, which its injectivity forbids. -/
theorem IsDrawing.ne_of_isLink (h : IsDrawing G drawing) (hl : G.IsLink e u v) : u ≠ v := by
  rintro rfl
  obtain ⟨g, -, hinj, -, hg0, hg1⟩ := h.edge_isArcBetween hl
  have : (0 : ℝ) = 1 := hinj zero_mem_I one_mem_I (hg0.trans hg1.symm)
  norm_num at this

theorem IsDrawing.not_isLoopAt (h : IsDrawing G drawing) (e : β) (u : Plane) :
    ¬ G.IsLoopAt e u :=
  fun hloop ↦ h.ne_of_isLink hloop rfl

/-! ### The realisation of a path

The induction carries the *existence* of an arc, not a parametrisation. Its one geometric
step is `Graph.IsDrawing.first_edge_meets_rest`. -/

/-- **The first edge's arc meets the rest of the path only at the waypoint.** Two cases, and
neither is geometric beyond the workhorse `Graph.IsDrawing.arcs_meet_at_vertex`: if the rest
takes the same edge again, the source is one of its ends; if it takes a different one, a
common point is a vertex incident with both, so it is the source or the waypoint. Either way a
point that was the source would put the source among the vertices the rest visits, which is
what the path's freshness clause forbids. -/
theorem IsDrawing.first_edge_meets_rest (h : IsDrawing G drawing) (hl : G.IsLink e u w)
    (hW : ∀ f ∈ W, f ∈ E(G)) (hfresh : u ∉ G.walkVertices w W)
    (hze : z ∈ edgeArc drawing e) (hzW : z ∈ edgesCover drawing W) : z = w := by
  obtain ⟨f, hf, hzf⟩ := mem_edgesCover_iff.1 hzW
  -- Taking the same edge again would put the source among the vertices the rest visits.
  have hef : e ≠ f := by
    rintro rfl
    exact hfresh (mem_walkVertices_of_mem_covered ⟨e, hf, hl.inc_left⟩)
  obtain ⟨-, hinc, hincf⟩ := h.edge_inter hl.edge_mem (hW f hf) hef hze hzf
  rcases hinc.eq_or_eq_of_isLink hl with rfl | rfl
  · exact absurd (mem_walkVertices_of_mem_covered ⟨f, hf, hincf⟩) hfresh
  · rfl

/-- **The realisation of a path is an arc between its two ends.** The path must go somewhere:
the empty path draws the empty set, which is not an arc.

The induction is on the path, at the source end, and what it carries is the existence of the
arc. At each step the first edge's arc and the rest's arc meet only at the waypoint
(`Graph.IsDrawing.first_edge_meets_rest`), so `Schoenflies.IsArcBetween.concatenate` glues
them. -/
theorem IsDrawing.path_isArcBetween (h : IsDrawing G drawing) (hP : G.IsPath u W v)
    (hne : W ≠ []) : IsArcBetween (edgesCover drawing W) u v := by
  induction hP with
  | nil => exact absurd rfl hne
  | @cons u w v e W hl hP hfresh ih =>
    rcases eq_or_ne W [] with rfl | hW
    · -- A single edge: the rest contributes nothing, and the path arrives where the edge does.
      obtain rfl : w = v := hP.isWalk.eq_of_nil
      simpa using h.edge_isArcBetween hl
    · refine edgesCover_cons ▸ (h.edge_isArcBetween hl).concatenate (ih hW) ?_
      exact fun z hze hzW ↦
        h.first_edge_meets_rest hl (fun f hf ↦ hP.edge_mem hf) hfresh hze hzW

/-! ### The realisation of a cycle -/

/-- The detour of a cycle is a path with at least one edge — an empty detour would return to
where it set out, and the edge it is a detour for has two distinct ends — so it is drawn by an
arc between those ends. -/
theorem IsDrawing.detour_isArcBetween (h : IsDrawing G drawing) (hc : G.IsCycleThrough e u v D) :
    IsArcBetween (edgesCover drawing D) u v := by
  refine h.path_isArcBetween hc.isPath fun hD ↦ ?_
  exact h.ne_of_isLink hc.isLink (hD ▸ hc.isPath.isWalk).eq_of_nil

/-- **The detour of a cycle meets the edge only at the edge's two ends.** A common point lies
on the edge and on some edge of the detour, which the detour does not contain, so it is a
vertex incident with the edge — and an edge has only its two ends. -/
theorem IsDrawing.detour_meets_edge (h : IsDrawing G drawing) (hc : G.IsCycleThrough e u v D)
    (hzD : z ∈ edgesCover drawing D) (hze : z ∈ edgeArc drawing e) : z = u ∨ z = v := by
  obtain ⟨f, hf, hzf⟩ := mem_edgesCover_iff.1 hzD
  have hef : e ≠ f := fun hEq ↦ hc.notMem (hEq ▸ hf)
  obtain ⟨-, hinc, -⟩ :=
    h.edge_inter hc.isLink.edge_mem (hc.isPath.edge_mem hf) hef hze hzf
  exact hinc.eq_or_eq_of_isLink hc.isLink

/-- **The detour and the edge meet in exactly the edge's two ends.** The inclusion
`Graph.IsDrawing.detour_meets_edge` is what `Schoenflies.IsJordanCurve.of_two_arcs` consumes;
the reverse one is free, since both ends are endpoints of both arcs. -/
theorem IsDrawing.cycle_inter (h : IsDrawing G drawing) (hc : G.IsCycleThrough e u v D) :
    edgesCover drawing D ∩ edgeArc drawing e = {u, v} := by
  have hD := h.detour_isArcBetween hc
  have hE := h.edge_isArcBetween hc.isLink
  refine Set.eq_of_subset_of_subset (fun z hz ↦ h.detour_meets_edge hc hz.1 hz.2) ?_
  rintro z (rfl | rfl)
  exacts [⟨hD.left_mem, hE.left_mem⟩, ⟨hD.right_mem, hE.right_mem⟩]

/-- **The realisation of a cycle is a Jordan curve.** The detour is drawn by an arc from one
end of the edge to the other, the edge is drawn by an arc back, and the two meet only at those
two ends, so `Schoenflies.IsJordanCurve.of_two_arcs` closes the loop. -/
theorem IsDrawing.cycle_isJordanCurve (h : IsDrawing G drawing)
    (hc : G.IsCycleThrough e u v D) : IsJordanCurve (edgesCover drawing (e :: D)) := by
  have hJ : IsJordanCurve (edgesCover drawing D ∪ edgeArc drawing e) :=
    IsJordanCurve.of_two_arcs (h.detour_isArcBetween hc)
      (h.edge_isArcBetween hc.isLink).reverse fun z hzD hze ↦ h.detour_meets_edge hc hzD hze
  rw [edgesCover_cons, Set.union_comm]
  exact hJ

/-- The source of a nonempty walk lies on what the walk draws. -/
theorem IsWalk.left_mem_edgesCover {u v : Plane} {W : List β} (hW : G.IsWalk u W v)
    (hd : IsDrawing G drawing) (hne : W ≠ []) : u ∈ edgesCover drawing W := by
  cases hW with
  | nil => exact absurd rfl hne
  | cons hl _ => exact mem_edgesCover (List.mem_cons_self ..) (hd.edge_isArcBetween hl).left_mem

/-- **A walk of a polygonal plane graph draws a polygonal set.** Consecutive edges share the
vertex between them, so the union stays a single vertex list. -/
theorem IsDrawing.isPolygonal_edgesCover (hd : IsDrawing G drawing)
    (hpoly : ∀ f ∈ E(G), Schoenflies.IsPolygonal (edgeArc drawing f)) :
    ∀ {u v : Plane} {W : List β}, G.IsWalk u W v → W ≠ [] →
      Schoenflies.IsPolygonal (edgesCover drawing W) := by
  intro u v W hW
  induction hW with
  | nil => exact fun h => absurd rfl h
  | @cons u w v f W hl hW ih =>
    intro _
    rcases eq_or_ne W [] with rfl | hWne
    · simpa using hpoly f hl.edge_mem
    · rw [edgesCover_cons]
      exact ((hpoly f hl.edge_mem).union (ih hWne)
        ⟨w, (hd.edge_isArcBetween hl).right_mem, hW.left_mem_edgesCover hd hWne⟩)

end Graph

end BundlePart377

section BundlePart378
/- Source: Papers/GraphicalZonotopes/ArcK5PathReplacement.lean -/



noncomputable section
open Set Schoenflies
open scoped Graph Classical
namespace Graph

/-- The single edge represented by a possibly subdivided path. -/
def IsApexPair (i j : Fin 5) : Prop := (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3)

@[simp] theorem isApexPair_comm (i j : Fin 5) : IsApexPair i j ↔ IsApexPair j i := by
  simp only [IsApexPair]
  tauto

def apexPathFamily {β : Type*} (drawing : β → ℝ → Plane)
    (e : Fin 5 → Fin 5 → β) (W : List β) (i j : Fin 5) : Set Plane :=
  if IsApexPair i j then edgesCover drawing W else edgeArc drawing (e i j)

/-- A finite drawing with all the edges of K₅ except the last one, together
with a path joining the missing endpoints and avoiding the other three
vertices, gives a genuine ten-arc K₅ configuration. -/
theorem IsDrawing.arcK5_of_apex_path {β : Type*} {G : Graph Plane β}
    {drawing : β → ℝ → Plane} (hd : IsDrawing G drawing)
    (x : Fin 5 → Plane) (hx : Function.Injective x)
    (hvertex : ∀ i,x i ∈ V(G)) (e : Fin 5 → Fin 5 → β)
    (hesymm : ∀ i j,e i j = e j i)
    (helink : ∀ i j,i ≠ j → ¬ IsApexPair i j → G.IsLink (e i j) (x i) (x j))
    (W : List β) (hpath : G.IsPath (x 3) W (x 4))
    (havoid : ∀ i : Fin 3,x ⟨i.1,by omega⟩ ∉ edgesCover drawing W) :
    IsArcK5 x (apexPathFamily drawing e W) := by
  classical
  let A := edgesCover drawing W
  have hA : IsArcBetween A (x 3) (x 4) := by
    apply hd.path_isArcBetween hpath
    intro hnil
    have heq := (hnil ▸ hpath.isWalk).eq_of_nil
    have h34 : (3 : Fin 5) ≠ 4 := by decide
    exact h34 (hx heq)
  have hAV : ∀ k : Fin 5,x k ∈ A → k = 3 ∨ k = 4 := by
    intro k hk
    by_cases hlt : k.1 < 3
    · exact False.elim (havoid ⟨k.1,hlt⟩ hk)
    · have hcases : k.1 = 3 ∨ k.1 = 4 := by omega
      exact hcases.imp Fin.ext Fin.ext
  have htriangleEnd : ∀ i j : Fin 5,i ≠ j → ¬ IsApexPair i j →
      i.1 < 3 ∨ j.1 < 3 := by
    intro i j hij hbad
    by_contra hno
    push_neg at hno
    have hi : i = 3 ∨ i = 4 := by
      have hh : i.1 = 3 ∨ i.1 = 4 := by omega
      exact hh.imp Fin.ext Fin.ext
    have hj : j = 3 ∨ j = 4 := by
      have hh : j.1 = 3 ∨ j.1 = 4 := by omega
      exact hh.imp Fin.ext Fin.ext
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact hij rfl
    · exact hbad (Or.inl ⟨rfl,rfl⟩)
    · exact hbad (Or.inr ⟨rfl,rfl⟩)
    · exact hij rfl
  have hnotW : ∀ i j : Fin 5,∀ hij : i ≠ j,∀ hbad : ¬ IsApexPair i j,e i j ∉ W := by
    intro i j hij hbad heW
    have he := helink i j hij hbad
    have hArc := hd.edge_isArcBetween he
    rcases htriangleEnd i j hij hbad with hi | hj
    · exact havoid ⟨i.1,hi⟩ (mem_edgesCover heW hArc.left_mem)
    · exact havoid ⟨j.1,hj⟩ (mem_edgesCover heW hArc.right_mem)
  have hcross : ∀ i j : Fin 5,i ≠ j → ¬ IsApexPair i j →
      A ∩ edgeArc drawing (e i j) ⊆ ({x 3,x 4} : Set Plane) ∩ {x i,x j} := by
    intro i j hij hbad z hz
    obtain ⟨f,hf,hzf⟩ := mem_edgesCover_iff.mp hz.1
    have he := helink i j hij hbad
    have hef : e i j ≠ f := fun hh => hnotW i j hij hbad (hh.symm ▸ hf)
    obtain ⟨_,hze,_⟩ := hd.edge_inter he.edge_mem (hpath.edge_mem hf) hef hz.2 hzf
    have hends := hze.eq_or_eq_of_isLink he
    refine ⟨?_,hends⟩
    rcases hends with rfl | rfl
    · exact (hAV i hz.1).imp (congrArg x) (congrArg x)
    · exact (hAV j hz.1).imp (congrArg x) (congrArg x)
  have hbadends : ∀ i j,IsApexPair i j → ({x i,x j} : Set Plane) = {x 3,x 4} := by
    intro i j hbad
    rcases hbad with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · rfl
    · exact Set.pair_comm _ _
  constructor
  · exact hx
  · intro i j hij
    by_cases hbad : IsApexPair i j
    · rw [apexPathFamily,if_pos hbad]
      rcases hbad with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hA
      · exact hA.reverse
    · rw [apexPathFamily,if_neg hbad]
      exact hd.edge_isArcBetween (helink i j hij hbad)
  · intro i j
    simp only [apexPathFamily,isApexPair_comm i j,hesymm i j]
  · intro i j k hij hk
    by_cases hbad : IsApexPair i j
    · rw [apexPathFamily,if_pos hbad] at hk
      have hkv := hAV k hk
      rcases hbad with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hkv
      · exact hkv.symm
    · rw [apexPathFamily,if_neg hbad] at hk
      exact (hd.vertex_mem_edgeArc (helink i j hij hbad) (hvertex k) hk).imp
        (fun hh => hx hh) (fun hh => hx hh)
  · intro i j k l hij hkl hpairs hreverse
    by_cases hbad1 : IsApexPair i j
    · by_cases hbad2 : IsApexPair k l
      · rcases hbad1 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
          rcases hbad2 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact False.elim (hpairs rfl)
        · exact False.elim (hreverse rfl)
        · exact False.elim (hreverse rfl)
        · exact False.elim (hpairs rfl)
      · rw [apexPathFamily,if_pos hbad1,apexPathFamily,if_neg hbad2,hbadends i j hbad1]
        exact hcross k l hkl hbad2
    · by_cases hbad2 : IsApexPair k l
      · rw [apexPathFamily,if_neg hbad1,apexPathFamily,if_pos hbad2,hbadends k l hbad2]
        intro z hz
        exact (hcross i j hij hbad1 ⟨hz.2,hz.1⟩).symm
      · rw [apexPathFamily,if_neg hbad1,apexPathFamily,if_neg hbad2]
        intro z hz
        have he1 := helink i j hij hbad1
        have he2 := helink k l hkl hbad2
        have hef : e i j ≠ e k l := by
          intro heq
          have he2' : G.IsLink (e i j) (x k) (x l) := heq.symm ▸ he2
          rcases he1.eq_and_eq_or_eq_and_eq he2' with ⟨h1,h2⟩ | ⟨h1,h2⟩
          · exact hpairs (Prod.ext (hx h1) (hx h2))
          · exact hreverse (Prod.ext (hx h1) (hx h2))
        obtain ⟨_,hze,hzf⟩ := hd.edge_inter he1.edge_mem he2.edge_mem hef hz.1 hz.2
        exact ⟨hze.eq_or_eq_of_isLink he1,hzf.eq_or_eq_of_isLink he2⟩

end Graph

end
end BundlePart378

section BundlePart379
/- Source: Papers/GraphicalZonotopes/PlanarApexArc.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical Graph
namespace GraphicalZonotopes
open Finset Schoenflies
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An actual graph path avoiding a prescribed finite set is realized by a
simple plane arc avoiding the corresponding points. The proof transports
Mathlib walks to the library's edge-list walks, then shortens them without
adding an edge. -/
theorem PlaneDrawing.avoiding_path {G : SimpleGraph V} {p : V → Plane}
    (hp : Function.Injective p) {drawing : Sym2 V → ℝ → Plane}
    (hd : Graph.IsDrawing (planeGraph G p) drawing)
    (T : Finset V) (u w : V) (hu : u ∉ T) (hw : w ∉ T)
    (hreach : (G.induce ((T : Set V)ᶜ)).Reachable ⟨u,hu⟩ ⟨w,hw⟩) :
    ∃ W : List (Sym2 V),(planeGraph G p).IsPath (p u) W (p w) ∧
      ∀ t ∈ T,p t ∉ Graph.edgesCover drawing W := by
  let H := planeGraph G p
  have aux : ∀ {a b : ↥((T : Set V)ᶜ)},(G.induce ((T : Set V)ᶜ)).Walk a b →
      ∃ W : List (Sym2 V),H.IsWalk (p a.1) W (p b.1) ∧
        ∀ e ∈ W,∃ r s : V,r ∉ T ∧ s ∉ T ∧ H.IsLink e (p r) (p s) := by
    intro a b q
    induction q with
    | @nil a =>
      refine ⟨[],Graph.IsWalk.nil ?_,?_⟩
      · change p a.1 ∈ V(planeGraph G p)
        rw [planeGraph_vertexSet]
        exact ⟨a.1,rfl⟩
      · intro e he
        simp at he
    | @cons a b c hab q ih =>
      obtain ⟨W,hW,hends⟩ := ih
      have hl : H.IsLink s(a.1,b.1) (p a.1) (p b.1) :=
        (planeGraph_isLink G p hp _ _ _).mpr ⟨rfl,hab⟩
      refine ⟨s(a.1,b.1)::W,Graph.IsWalk.cons hl hW,?_⟩
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact ⟨a.1,b.1,a.2,b.2,hl⟩
      · exact hends e he
  obtain ⟨W,hW,hends⟩ := aux hreach.some
  obtain ⟨P,hP,hPW⟩ := hW.contains_path
  refine ⟨P,hP,?_⟩
  intro t ht hmem
  obtain ⟨e,he,hte⟩ := Graph.mem_edgesCover_iff.mp hmem
  obtain ⟨r,s,hr,hs,hl⟩ := hends e (hPW he)
  have hv : p t ∈ V(H) := by
    change p t ∈ V(planeGraph G p)
    rw [planeGraph_vertexSet]
    exact ⟨t,rfl⟩
  rcases hd.vertex_mem_edgeArc hl hv hte with htr | hts
  · exact hr (hp htr ▸ ht)
  · exact hs (hp hts ▸ ht)

/-- The forbidden configuration behind the planar triangle-apex separation:
a triangle, two distinct vertices complete to it, and a path joining those
two vertices away from the triangle yield ten genuine noncrossing K₅ arcs. -/
theorem HasPlaneDrawing.arcK5_of_triangle_apex_path {G : SimpleGraph V}
    (hG : HasPlaneDrawing G) (T : Finset V) (hT : T.card = 3) (hcT : G.IsClique T)
    (u w : V) (hu : u ∉ T) (hw : w ∉ T) (huw : u ≠ w)
    (huAdj : ∀ t ∈ T,G.Adj u t) (hwAdj : ∀ t ∈ T,G.Adj w t)
    (hreach : (G.induce ((T : Set V)ᶜ)).Reachable ⟨u,hu⟩ ⟨w,hw⟩) :
    ∃ (x : Fin 5 → Plane) (P : Fin 5 → Fin 5 → Set Plane),Graph.IsArcK5 x P := by
  obtain ⟨p,hp,drawing,hd⟩ := hG
  obtain ⟨W,hpath,havoid⟩ := PlaneDrawing.avoiding_path hp hd T u w hu hw hreach
  obtain ⟨a,b,c,hab,hac,hbc,hTabc⟩ := card_eq_three.mp hT
  have haT : a ∈ T := by rw [hTabc]; simp
  have hbT : b ∈ T := by rw [hTabc]; simp
  have hcT' : c ∈ T := by rw [hTabc]; simp
  have hua : u ≠ a := fun he => hu (he.symm ▸ haT)
  have hub : u ≠ b := fun he => hu (he.symm ▸ hbT)
  have huc : u ≠ c := fun he => hu (he.symm ▸ hcT')
  have hwa : w ≠ a := fun he => hw (he.symm ▸ haT)
  have hwb : w ≠ b := fun he => hw (he.symm ▸ hbT)
  have hwc : w ≠ c := fun he => hw (he.symm ▸ hcT')
  let names : Fin 5 → V := ![a,b,c,u,w]
  let x : Fin 5 → Plane := p ∘ names
  let e : Fin 5 → Fin 5 → Sym2 V := fun i j => s(names i,names j)
  have hnames : Function.Injective names := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [names]
  have hxab := hcT haT hbT hab
  have hxac := hcT haT hcT' hac
  have hxbc := hcT hbT hcT' hbc
  have hxuA := huAdj a haT
  have hxuB := huAdj b hbT
  have hxuC := huAdj c hcT'
  have hxwA := hwAdj a haT
  have hxwB := hwAdj b hbT
  have hxwC := hwAdj c hcT'
  have hadj : ∀ i j : Fin 5,i ≠ j → ¬ Graph.IsApexPair i j → G.Adj (names i) (names j) := by
    intro i j hij hbad
    fin_cases i <;> fin_cases j <;>
      simp_all [names,Graph.IsApexPair,SimpleGraph.adj_comm]
  have hvertex : ∀ i,x i ∈ V(PlaneDrawing.planeGraph G p) := by
    intro i
    rw [PlaneDrawing.planeGraph_vertexSet]
    exact ⟨names i,rfl⟩
  have he : ∀ i j : Fin 5,i ≠ j → ¬ Graph.IsApexPair i j →
      (PlaneDrawing.planeGraph G p).IsLink (e i j) (x i) (x j) := by
    intro i j hij hbad
    exact (PlaneDrawing.planeGraph_isLink G p hp _ _ _).mpr ⟨rfl,hadj i j hij hbad⟩
  have hpath' : (PlaneDrawing.planeGraph G p).IsPath (x 3) W (x 4) := by
    simpa [x,names] using hpath
  have havoid' : ∀ i : Fin 3,x ⟨i.1,by omega⟩ ∉ Graph.edgesCover drawing W := by
    intro i
    apply havoid
    fin_cases i <;> simp [names,hTabc]
  exact ⟨x,Graph.apexPathFamily drawing e W,hd.arcK5_of_apex_path x (hp.comp hnames)
    hvertex e (fun i j => Sym2.eq_swap) he W hpath' havoid'⟩

end GraphicalZonotopes

end
end
end BundlePart379

section BundlePart380
/- Source: dev/planar_search/schoenflies_port/Schoenflies/UniformBound.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/


/-!
# One positive bound for finitely many

Every "choose `ε` small enough for all of them" step in the development is this lemma: a
finite family of positive bounds has a single positive bound below all of them. The
polygonal-redrawing argument alone uses it three times, and the two-sided strip lemma chooses
its vertex disks and edge blocks the same way.

It is stated for a *predicate that is monotone downward in the bound* rather than as a `min`
fold, because no consumer wants the value — only that some positive value works for every
member at once.

## Blueprint

* `exists_pos_le_of_finite` — the numerical form.
* `exists_pos_forall_of_finite` — the form consumers use: a downward-monotone predicate
  holding at some positive bound for each member holds at one common positive bound.
-/

open Set

namespace Schoenflies

variable {ι : Type*}

/-- A finite family of positive reals is bounded below by a positive real. -/
theorem exists_pos_le_of_finite {S : Set ι} (hS : S.Finite) {f : ι → ℝ}
    (hf : ∀ i ∈ S, 0 < f i) : ∃ ε > 0, ∀ i ∈ S, ε ≤ f i := by
  classical
  induction S, hS using Set.Finite.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | @insert a S ha hS ih =>
    obtain ⟨ε, hε, hbound⟩ := ih fun i hi => hf i (mem_insert_of_mem _ hi)
    refine ⟨min ε (f a), lt_min hε (hf a (mem_insert _ _)), fun i hi => ?_⟩
    rcases mem_insert_iff.1 hi with rfl | hi
    · exact min_le_right _ _
    · exact le_trans (min_le_left _ _) (hbound i hi)

/-- The form the geometry uses: if a property that only gets easier as the bound shrinks holds
at *some* positive bound for each member of a finite family, then it holds at *one* positive
bound for all of them at once. -/
theorem exists_pos_forall_of_finite {S : Set ι} (hS : S.Finite) {P : ι → ℝ → Prop}
    (hmono : ∀ i, ∀ ⦃δ ε : ℝ⦄, 0 < δ → δ ≤ ε → P i ε → P i δ)
    (hex : ∀ i ∈ S, ∃ ε > 0, P i ε) :
    ∃ ε > 0, ∀ i ∈ S, P i ε := by
  classical
  -- Pick a witness for each member, then take a positive bound below all the witnesses.
  choose! f hfpos hfP using hex
  obtain ⟨ε, hε, hbound⟩ := exists_pos_le_of_finite hS (f := f) hfpos
  exact ⟨ε, hε, fun i hi => hmono i hε (hbound i hi) (hfP i hi)⟩

end Schoenflies

end BundlePart380
