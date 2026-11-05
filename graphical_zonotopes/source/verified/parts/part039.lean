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

public import verified.parts.part038
import all verified.parts.part038

@[expose] public section

set_option debug.skipKernelTC false
set_option linter.all false
set_option Elab.async false
set_option internal.cmdlineSnapshots true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

section BundlePart420
/- Source: dev/planar_search/schoenflies_port/Schoenflies/Graph/K33.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/



/-!
# The utility graph `K(3,3)` inside a plane graph

The blueprint's proof of `lem:k33` is four sentences: regard `K(3,3)` as the six-cycle
`x₀y₀x₁y₁x₂y₂x₀` together with the three remaining edges `x₀y₁, x₁y₂, x₂y₀`; the six-cycle is
a Jordan curve; each remaining edge lies wholly on one side of it; two of the three lie on the
same side, and their endpoints alternate on the six-cycle, contrary to
`cor:alternating-crosscuts`.

**Everything in that proof except the last two citations is established here.** What is left is
the polygonal Jordan curve theorem — which supplies "the two sides" — and the alternating
crosscut corollary itself; neither exists yet, so `lem:k33` is not stated. See the note at the
end of this docstring for exactly how the last step will read.

## `K(3,3)` is a configuration, not a graph

There is no `K33 : Graph α β`. A copy of `K(3,3)` inside `G` is `Graph.IsK33Config G x y e`:
six vertices `x 0, x 1, x 2, y 0, y 1, y 2`, all distinct, and nine edge names `e i j` with
`e i j` linking `x i` to `y j`. Nothing says `G` has no other vertex or edge.

This is the shape the theorem is used in — one always *finds* a `K(3,3)` inside a graph one
already has, never constructs the abstract one — and it is also what makes the drawing
hypothesis land correctly: `Graph.IsDrawing G drawing` is a hypothesis about all of `G`, so
taking `G` larger only strengthens it.

Two economies follow from stating the configuration this way. The nine edge names are
automatically distinct (`Graph.IsK33Config.eq_of_e_eq`): an edge has only two ends, so two
names coinciding would force the index pairs to agree. And no looplessness clause is needed:
`x i ≠ y j` is one of the four fields.

## The indexing is arithmetic in `Fin 3`, so that `decide` can do the bookkeeping

The six-cycle uses the edges `e i i` and `e (i+1) i`; the three remaining edges are
`e s (s+1)` for `s : Fin 3`. Every combinatorial side condition below — that a remaining edge
is not a cycle edge, that the two arcs of the cut cycle cover it and meet only at the cut
points — is a statement about index pairs quantified over `Fin 3`, and is discharged by
`decide`. The edges themselves never have to be compared.

The two arcs into which the ends of the remaining edge `e s (s+1)` cut the six-cycle are named
by their index pairs as well (`Graph.arcAPairs`, `Graph.arcBPairs`); `Graph.arcA` and
`Graph.arcB` are the corresponding edge lists, `rfl`-equal to the mapped pair lists so that
both presentations are available with no conversion lemma.

## Blueprint

* `Graph.IsK33Config` — a copy of the utility graph.
* `Graph.IsK33Config.hexagon_isCycleThrough` — §"Plane graphs and the utility graph": "regard
  `K(3,3)` as the six-cycle `x₁y₁x₂y₂x₃y₃x₁` together with the three remaining edges".
* `Graph.IsK33Config.hexagon_isJordanCurve` — `lem:k33`, "the six-cycle is a polygonal Jordan
  curve". Polygonality plays no part; it is needed only where the *polygonal* Jordan curve
  theorem is applied to the result.
* `Graph.IsK33Config.chord_inter_hexSet`, `Graph.IsK33Config.chord_openArc_eq`,
  `Graph.IsK33Config.chord_openArc_subset_connectedComponentIn` — `lem:k33`, "each remaining
  edge lies wholly on one side": a remaining edge meets the six-cycle in exactly its own two
  ends, so its interior is a connected subset of the complement, hence lies in one component.
  This is also the crosscut hypothesis of `thm:polygonal-crosscut` and
  `cor:alternating-crosscuts`.
* `Graph.IsK33Config.exists_two_chords_same_side` — `lem:k33`, "two of the three lie on the
  same side". The two sides arrive as an arbitrary pair of disjoint open sets covering the
  complement, which is the form `thm:polygonal-jordan` will supply them in.
* `Graph.IsK33Config.chords_alternate` — `lem:k33`, "their endpoints alternate on the
  six-cycle", in the form `cor:alternating-crosscuts` consumes: the ends of one remaining edge
  cut the cycle into two arcs meeting only at those ends, and the two ends of another remaining
  edge lie one interior to each. Every pair of remaining edges is of the form `(s, s+1)`, so
  the single index `s` covers all three pairs.
* `Graph.IsK33Config.chords_disjoint` — the disjointness that `cor:alternating-crosscuts`
  contradicts: two remaining edges have four distinct ends, and distinct edges of a plane graph
  meet only at a shared end.

**How `lem:k33` will close.** Given a plane drawing of a graph with a `K(3,3)` configuration,
make it polygonal (`Graph.polygonal_redrawing`, `lem:polygonal-redrawing`); the six-cycle is
then a polygonal Jordan curve, and `thm:polygonal-jordan` gives the two disjoint open sides
that `exists_two_chords_same_side` wants. It returns two remaining edges on the same side;
`chords_alternate` says their ends alternate, so `cor:alternating-crosscuts` makes them meet,
and `chords_disjoint` says they do not.
-/

open Set Schoenflies unitInterval
open scoped Graph

namespace Graph

variable {α β : Type*} {G : Graph α β} {x y : Fin 3 → α} {e : Fin 3 → Fin 3 → β}
variable {i j k l s t : Fin 3} {z : α}

/-- A copy of the utility graph `K(3,3)` inside `G`. -/
structure IsK33Config (G : Graph α β) (x y : Fin 3 → α) (e : Fin 3 → Fin 3 → β) : Prop where
  /-- `e i j` joins the `i`-th vertex of one side to the `j`-th vertex of the other. -/
  isLink : ∀ i j, G.IsLink (e i j) (x i) (y j)
  /-- The three vertices of the first side are distinct. -/
  x_injective : Function.Injective x
  /-- The three vertices of the second side are distinct. -/
  y_injective : Function.Injective y
  /-- The two sides are disjoint. -/
  ne : ∀ i j, x i ≠ y j

namespace IsK33Config

theorem x_ne_x (h : IsK33Config G x y e) (hik : i ≠ k) : x i ≠ x k :=
  fun he ↦ hik (h.x_injective he)

theorem y_ne_y (h : IsK33Config G x y e) (hjl : j ≠ l) : y j ≠ y l :=
  fun he ↦ hjl (h.y_injective he)

theorem x_ne_y (h : IsK33Config G x y e) (i j : Fin 3) : x i ≠ y j := h.ne i j

theorem y_ne_x (h : IsK33Config G x y e) (j i : Fin 3) : y j ≠ x i := (h.ne i j).symm

/-- **The nine edges carry nine different names.** This is not an axiom of the configuration:
an edge has only two ends, so two of the nine names being equal would force the two index
pairs to agree. -/
theorem eq_of_e_eq (h : IsK33Config G x y e) (heq : e i j = e k l) : i = k ∧ j = l := by
  have h' : G.IsLink (e i j) (x k) (y l) := by rw [heq]; exact h.isLink k l
  rcases (h.isLink i j).eq_and_eq_or_eq_and_eq h' with ⟨h1, h2⟩ | ⟨h1, -⟩
  · exact ⟨h.x_injective h1, h.y_injective h2⟩
  · exact absurd h1 (h.ne i l)

theorem e_ne (h : IsK33Config G x y e) (hne : ¬ (i = k ∧ j = l)) : e i j ≠ e k l :=
  fun heq ↦ hne (h.eq_of_e_eq heq)

/-- A vertex on one of the nine edges is one of that edge's two ends. -/
theorem inc_elim (h : IsK33Config G x y e) (hz : G.Inc (e i j) z) : z = x i ∨ z = y j :=
  hz.eq_or_eq_of_isLink (h.isLink i j)

/-- **Freshness, in the form the path constructor asks for.** A vertex which is neither the
source of the rest of the walk nor an end of any of its edges is not among the vertices that
rest visits. -/
theorem notMem_walkVertices (h : IsK33Config G x y e) {W : List β} {w : α} (hzw : z ≠ w)
    (hW : ∀ f ∈ W, ∃ i j, f = e i j ∧ z ≠ x i ∧ z ≠ y j) :
    z ∉ G.walkVertices w W := by
  intro hz
  rcases mem_walkVertices_iff.1 hz with rfl | ⟨f, hf, hinc⟩
  · exact hzw rfl
  obtain ⟨i, j, rfl, hxi, hyj⟩ := hW f hf
  rcases h.inc_elim hinc with hh | hh
  exacts [hxi hh, hyj hh]

end IsK33Config

/-! ### The six-cycle

The blueprint reads `K(3,3)` as the six-cycle `x₀y₀x₁y₁x₂y₂x₀` together with the three
remaining edges. The cycle is presented as `Schoenflies/Graph/Cycle.lean` presents one:
through the edge `e 0 0`, with a detour path running the other way round. -/

/-- The index pairs of the six edges of the six-cycle, in the order the cycle is traversed
starting from `e 0 0`. Kept as index pairs, not as edges, because every question about which
edges the cycle uses is then decidable. -/
def hexPairs : List (Fin 3 × Fin 3) := [(0, 0), (0, 2), (2, 2), (2, 1), (1, 1), (1, 0)]

/-- The five edges of the detour of the six-cycle: the path
`x₀ → y₂ → x₂ → y₁ → x₁ → y₀` that returns to the other end of `e 0 0`. -/
def hexDetour (e : Fin 3 → Fin 3 → β) : List β := [e 0 2, e 2 2, e 2 1, e 1 1, e 1 0]

/-- The six edges of the six-cycle. -/
def hexList (e : Fin 3 → Fin 3 → β) : List β := e 0 0 :: hexDetour e

theorem hexList_eq_map (e : Fin 3 → Fin 3 → β) :
    hexList e = hexPairs.map fun p ↦ e p.1 p.2 := rfl

theorem mem_hexList_iff {f : β} : f ∈ hexList e ↔ ∃ p ∈ hexPairs, f = e p.1 p.2 := by
  rw [hexList_eq_map]
  simp only [List.mem_map, eq_comm]

namespace IsK33Config

/-- The detour of the six-cycle is a path. Each freshness clause says that the vertex a step
departs from is none of the six vertices the rest of the detour meets. -/
theorem hexDetour_isPath (h : IsK33Config G x y e) : G.IsPath (x 0) (hexDetour e) (y 0) := by
  have h5 : G.IsPath (x 1) [e 1 0] (y 0) := .single (h.isLink 1 0) (h.x_ne_y 1 0)
  have h4 : G.IsPath (y 1) [e 1 1, e 1 0] (y 0) := by
    refine .cons (h.isLink 1 1).symm h5 (h.notMem_walkVertices (h.y_ne_x 1 1) ?_)
    rintro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl
    exact ⟨1, 0, rfl, h.y_ne_x 1 1, h.y_ne_y (by decide)⟩
  have h3 : G.IsPath (x 2) [e 2 1, e 1 1, e 1 0] (y 0) := by
    refine .cons (h.isLink 2 1) h4 (h.notMem_walkVertices (h.x_ne_y 2 1) ?_)
    rintro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · exact ⟨1, 1, rfl, h.x_ne_x (by decide), h.x_ne_y 2 1⟩
    · exact ⟨1, 0, rfl, h.x_ne_x (by decide), h.x_ne_y 2 0⟩
  have h2 : G.IsPath (y 2) [e 2 2, e 2 1, e 1 1, e 1 0] (y 0) := by
    refine .cons (h.isLink 2 2).symm h3 (h.notMem_walkVertices (h.y_ne_x 2 2) ?_)
    rintro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · exact ⟨2, 1, rfl, h.y_ne_x 2 2, h.y_ne_y (by decide)⟩
    · exact ⟨1, 1, rfl, h.y_ne_x 2 1, h.y_ne_y (by decide)⟩
    · exact ⟨1, 0, rfl, h.y_ne_x 2 1, h.y_ne_y (by decide)⟩
  refine .cons (h.isLink 0 2) h2 (h.notMem_walkVertices (h.x_ne_y 0 2) ?_)
  rintro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact ⟨2, 2, rfl, h.x_ne_x (by decide), h.x_ne_y 0 2⟩
  · exact ⟨2, 1, rfl, h.x_ne_x (by decide), h.x_ne_y 0 1⟩
  · exact ⟨1, 1, rfl, h.x_ne_x (by decide), h.x_ne_y 0 1⟩
  · exact ⟨1, 0, rfl, h.x_ne_x (by decide), h.x_ne_y 0 0⟩

/-- **The six-cycle is a cycle**, presented through the edge `e 0 0`. -/
theorem hexagon_isCycleThrough (h : IsK33Config G x y e) :
    G.IsCycleThrough (e 0 0) (x 0) (y 0) (hexDetour e) := by
  refine ⟨h.isLink 0 0, h.hexDetour_isPath, ?_⟩
  simp only [hexDetour, List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨h.e_ne (by decide), h.e_ne (by decide), h.e_ne (by decide), h.e_ne (by decide),
    h.e_ne (by decide)⟩

/-! ### The three remaining edges

`e s (s+1)`, for `s : Fin 3`, are the three edges of `K(3,3)` that the six-cycle leaves out. -/

/-- The three remaining edges are not edges of the six-cycle. -/
theorem chord_notMem_hexList (h : IsK33Config G x y e) (s : Fin 3) : e s (s + 1) ∉ hexList e := by
  intro hmem
  obtain ⟨p, hp, heq⟩ := mem_hexList_iff.1 hmem
  have key : ∀ (s : Fin 3) (p : Fin 3 × Fin 3), p ∈ hexPairs → ¬ (s = p.1 ∧ s + 1 = p.2) := by
    decide
  exact key s p hp (h.eq_of_e_eq heq)

/-- Two distinct remaining edges carry distinct names, and share no end. -/
theorem chord_ne (h : IsK33Config G x y e) (hst : s ≠ t) : e s (s + 1) ≠ e t (t + 1) :=
  h.e_ne (fun hc ↦ hst hc.1)

/-- The edges of the six-cycle are edges of the graph. -/
theorem hexList_edge_mem (h : IsK33Config G x y e) {f : β} (hf : f ∈ hexList e) : f ∈ E(G) := by
  obtain ⟨p, -, rfl⟩ := mem_hexList_iff.1 hf
  exact (h.isLink p.1 p.2).edge_mem

end IsK33Config

theorem mem_hexList (e : Fin 3 → Fin 3 → β) {p : Fin 3 × Fin 3} (hp : p ∈ hexPairs) :
    e p.1 p.2 ∈ hexList e :=
  mem_hexList_iff.2 ⟨p, hp, rfl⟩

/-! ### The six-cycle cut at the ends of one remaining edge

The two ends of the remaining edge `e s (s+1)` are `x s` and `y (s+1)`, and they cut the
six-cycle into two paths: `x s → y s → x (s+1) → y (s+1)` and
`x s → y (s+2) → x (s+2) → y (s+1)`. The other two remaining edges each have one end interior
to the first and one end interior to the second — this is the blueprint's "their endpoints
alternate on the six-cycle". -/

/-- Index pairs of the first of the two paths the ends of `e s (s+1)` cut the six-cycle into. -/
def arcAPairs (s : Fin 3) : List (Fin 3 × Fin 3) := [(s, s), (s + 1, s), (s + 1, s + 1)]

/-- Index pairs of the second of the two paths. -/
def arcBPairs (s : Fin 3) : List (Fin 3 × Fin 3) := [(s, s + 2), (s + 2, s + 2), (s + 2, s + 1)]

/-- The edges of the first path. -/
def arcA (e : Fin 3 → Fin 3 → β) (s : Fin 3) : List β := [e s s, e (s + 1) s, e (s + 1) (s + 1)]

/-- The edges of the second path. -/
def arcB (e : Fin 3 → Fin 3 → β) (s : Fin 3) : List β :=
  [e s (s + 2), e (s + 2) (s + 2), e (s + 2) (s + 1)]

theorem arcA_eq_map (e : Fin 3 → Fin 3 → β) (s : Fin 3) :
    arcA e s = (arcAPairs s).map fun p ↦ e p.1 p.2 := rfl

theorem arcB_eq_map (e : Fin 3 → Fin 3 → β) (s : Fin 3) :
    arcB e s = (arcBPairs s).map fun p ↦ e p.1 p.2 := rfl

namespace IsK33Config

/-- The first of the two paths is a path. -/
theorem arcA_isPath (h : IsK33Config G x y e) (s : Fin 3) :
    G.IsPath (x s) (arcA e s) (y (s + 1)) := by
  have hab : s ≠ s + 1 := by revert s; decide
  have p3 : G.IsPath (x (s + 1)) [e (s + 1) (s + 1)] (y (s + 1)) :=
    .single (h.isLink (s + 1) (s + 1)) (h.x_ne_y _ _)
  have p2 : G.IsPath (y s) [e (s + 1) s, e (s + 1) (s + 1)] (y (s + 1)) := by
    refine .cons (h.isLink (s + 1) s).symm p3 (h.notMem_walkVertices (h.y_ne_x _ _) ?_)
    rintro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl
    exact ⟨s + 1, s + 1, rfl, h.y_ne_x _ _, h.y_ne_y hab⟩
  refine .cons (h.isLink s s) p2 (h.notMem_walkVertices (h.x_ne_y _ _) ?_)
  rintro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact ⟨s + 1, s, rfl, h.x_ne_x hab, h.x_ne_y _ _⟩
  · exact ⟨s + 1, s + 1, rfl, h.x_ne_x hab, h.x_ne_y _ _⟩

/-- The second of the two paths is a path. -/
theorem arcB_isPath (h : IsK33Config G x y e) (s : Fin 3) :
    G.IsPath (x s) (arcB e s) (y (s + 1)) := by
  have hac : s ≠ s + 2 := by revert s; decide
  have hcb : s + 2 ≠ s + 1 := by revert s; decide
  have q3 : G.IsPath (x (s + 2)) [e (s + 2) (s + 1)] (y (s + 1)) :=
    .single (h.isLink (s + 2) (s + 1)) (h.x_ne_y _ _)
  have q2 : G.IsPath (y (s + 2)) [e (s + 2) (s + 2), e (s + 2) (s + 1)] (y (s + 1)) := by
    refine .cons (h.isLink (s + 2) (s + 2)).symm q3 (h.notMem_walkVertices (h.y_ne_x _ _) ?_)
    rintro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl
    exact ⟨s + 2, s + 1, rfl, h.y_ne_x _ _, h.y_ne_y hcb⟩
  refine .cons (h.isLink s (s + 2)) q2 (h.notMem_walkVertices (h.x_ne_y _ _) ?_)
  rintro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact ⟨s + 2, s + 2, rfl, h.x_ne_x hac, h.x_ne_y _ _⟩
  · exact ⟨s + 2, s + 1, rfl, h.x_ne_x hac, h.x_ne_y _ _⟩

end IsK33Config

end Graph

/-! ## The six-cycle drawn in the plane

Everything from here on is about a *drawing* of the configuration. Nothing in this section
uses more geometry than the three clauses of `Graph.IsDrawing`. -/

namespace Graph

variable {β : Type*} {G : Graph Plane β} {x y : Fin 3 → Plane} {e : Fin 3 → Fin 3 → β}
variable {drawing : β → ℝ → Plane} {s t : Fin 3}

/-- The point set of the six-cycle of a drawn `K(3,3)`. -/
def hexSet (drawing : β → ℝ → Plane) (e : Fin 3 → Fin 3 → β) : Set Plane :=
  edgesCover drawing (hexList e)

theorem mem_edgesCover_map_iff {L : List (Fin 3 × Fin 3)} {p : Plane} :
    p ∈ edgesCover drawing (L.map fun q ↦ e q.1 q.2) ↔
      ∃ q ∈ L, p ∈ edgeArc drawing (e q.1 q.2) := by
  constructor
  · intro hp
    obtain ⟨f, hf, hpf⟩ := mem_edgesCover_iff.1 hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hf
    exact ⟨q, hq, hpf⟩
  · rintro ⟨q, hq, hpq⟩
    exact mem_edgesCover (List.mem_map_of_mem hq) hpq

theorem mem_hexSet_iff {p : Plane} :
    p ∈ hexSet drawing e ↔ ∃ q ∈ hexPairs, p ∈ edgeArc drawing (e q.1 q.2) := by
  rw [hexSet, hexList_eq_map]; exact mem_edgesCover_map_iff

theorem mem_arcA_iff {p : Plane} :
    p ∈ edgesCover drawing (arcA e s) ↔ ∃ q ∈ arcAPairs s, p ∈ edgeArc drawing (e q.1 q.2) := by
  rw [arcA_eq_map]; exact mem_edgesCover_map_iff

theorem mem_arcB_iff {p : Plane} :
    p ∈ edgesCover drawing (arcB e s) ↔ ∃ q ∈ arcBPairs s, p ∈ edgeArc drawing (e q.1 q.2) := by
  rw [arcB_eq_map]; exact mem_edgesCover_map_iff

namespace IsK33Config

/-- **The six-cycle of a drawn `K(3,3)` is a Jordan curve.** This is the blueprint's "the
six-cycle is a polygonal Jordan curve"; polygonality plays no part in it, and is needed only
where the *polygonal* Jordan curve theorem is applied to the result. -/
theorem hexagon_isJordanCurve (h : IsK33Config G x y e) (hd : IsDrawing G drawing) :
    IsJordanCurve (hexSet drawing e) :=
  hd.cycle_isJordanCurve h.hexagon_isCycleThrough

/-- The `i`-th vertex of the first side lies on the six-cycle. -/
theorem x_mem_hexSet (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (i : Fin 3) :
    x i ∈ hexSet drawing e := by
  have hp : ∀ i : Fin 3, ((i, i) : Fin 3 × Fin 3) ∈ hexPairs := by decide
  exact mem_edgesCover (mem_hexList e (hp i)) (hd.edge_isArcBetween (h.isLink i i)).left_mem

/-- The `j`-th vertex of the second side lies on the six-cycle. -/
theorem y_mem_hexSet (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (j : Fin 3) :
    y j ∈ hexSet drawing e := by
  have hp : ∀ j : Fin 3, ((j, j) : Fin 3 × Fin 3) ∈ hexPairs := by decide
  exact mem_edgesCover (mem_hexList e (hp j)) (hd.edge_isArcBetween (h.isLink j j)).right_mem

/-- **Each of the three remaining edges is a crosscut of the six-cycle**: its arc meets the
cycle in exactly its own two ends. -/
theorem chord_inter_hexSet (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (s : Fin 3) :
    edgeArc drawing (e s (s + 1)) ∩ hexSet drawing e = {x s, y (s + 1)} := by
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rintro p ⟨hpe, hph⟩
    obtain ⟨f, hf, hpf⟩ := mem_edgesCover_iff.1 hph
    have hne : e s (s + 1) ≠ f := fun hc ↦ h.chord_notMem_hexList s (hc ▸ hf)
    obtain ⟨-, hinc, -⟩ :=
      hd.edge_inter (h.isLink s (s + 1)).edge_mem (h.hexList_edge_mem hf) hne hpe hpf
    exact h.inc_elim hinc
  · rintro p (rfl | rfl)
    · exact ⟨(hd.edge_isArcBetween (h.isLink s (s + 1))).left_mem, h.x_mem_hexSet hd s⟩
    · exact ⟨(hd.edge_isArcBetween (h.isLink s (s + 1))).right_mem, h.y_mem_hexSet hd (s + 1)⟩

/-- The interior of a remaining edge, as the blueprint reads it: its arc without its two
ends. -/
theorem chord_openArc_eq (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (s : Fin 3) :
    openArc (drawing (e s (s + 1))) = edgeArc drawing (e s (s + 1)) \ {x s, y (s + 1)} := by
  obtain ⟨-, hi, hlink⟩ := hd.edge_param (h.isLink s (s + 1)).edge_mem
  have hpair : ({drawing (e s (s + 1)) 0, drawing (e s (s + 1)) 1} : Set Plane)
      = {x s, y (s + 1)} := by
    rcases hlink.eq_and_eq_or_eq_and_eq (h.isLink s (s + 1)) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, Set.pair_comm]
  rw [openArc_eq_diff hi, hpair]
  rfl

/-- **A remaining edge lies wholly off the six-cycle except at its ends.** -/
theorem chord_openArc_subset_compl (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (s : Fin 3) : openArc (drawing (e s (s + 1))) ⊆ (hexSet drawing e)ᶜ := by
  rw [h.chord_openArc_eq hd s]
  rintro p ⟨hpe, hpn⟩ hph
  exact hpn ((h.chord_inter_hexSet hd s).subset ⟨hpe, hph⟩)

theorem chord_openArc_isPreconnected (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (s : Fin 3) : IsPreconnected (openArc (drawing (e s (s + 1)))) :=
  isPreconnected_Ioo.image _
    ((hd.edge_param (h.isLink s (s + 1)).edge_mem).1.mono Ioo_subset_I)

theorem chord_openArc_nonempty (s : Fin 3) :
    (openArc (drawing (e s (s + 1)))).Nonempty :=
  ⟨drawing (e s (s + 1)) (1 / 2), 1 / 2, by norm_num, rfl⟩

/-- **Each of the three remaining edges lies wholly on one side of the six-cycle**: its
interior, being connected and disjoint from the cycle, lies in a single connected component of
the complement. -/
theorem chord_openArc_subset_connectedComponentIn (h : IsK33Config G x y e)
    (hd : IsDrawing G drawing) (s : Fin 3) {p : Plane}
    (hp : p ∈ openArc (drawing (e s (s + 1)))) :
    openArc (drawing (e s (s + 1))) ⊆ connectedComponentIn (hexSet drawing e)ᶜ p :=
  (h.chord_openArc_isPreconnected hd s).subset_connectedComponentIn hp
    (h.chord_openArc_subset_compl hd s)

/-- **Two distinct remaining edges are disjoint.** Their four ends are distinct, and two
distinct edges of a plane graph meet only at a shared end. -/
theorem chords_disjoint (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (hst : s ≠ t) :
    edgeArc drawing (e s (s + 1)) ∩ edgeArc drawing (e t (t + 1)) = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun p ⟨hps, hpt⟩ ↦ ?_
  obtain ⟨-, hincs, hinct⟩ := hd.edge_inter (h.isLink s (s + 1)).edge_mem
    (h.isLink t (t + 1)).edge_mem (h.chord_ne hst) hps hpt
  have hne1 : s ≠ t := hst
  have hne2 : s + 1 ≠ t + 1 := fun hc ↦ hst (by simpa using hc)
  rcases h.inc_elim hincs with rfl | rfl <;> rcases h.inc_elim hinct with hh | hh
  · exact (h.x_ne_x hne1) hh
  · exact (h.x_ne_y s (t + 1)) hh
  · exact (h.y_ne_x (s + 1) t) hh
  · exact (h.y_ne_y hne2) hh

/-! ### The two arcs the ends of a remaining edge cut the six-cycle into -/

theorem arcA_isArcBetween (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (s : Fin 3) :
    IsArcBetween (edgesCover drawing (arcA e s)) (x s) (y (s + 1)) :=
  hd.path_isArcBetween (h.arcA_isPath s) (by simp [arcA])

theorem arcB_isArcBetween (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (s : Fin 3) :
    IsArcBetween (edgesCover drawing (arcB e s)) (x s) (y (s + 1)) :=
  hd.path_isArcBetween (h.arcB_isPath s) (by simp [arcB])

/-- **The two arcs make up the six-cycle.** -/
theorem arcs_union (s : Fin 3) :
    edgesCover drawing (arcA e s) ∪ edgesCover drawing (arcB e s) = hexSet drawing e := by
  have hA : ∀ s : Fin 3, ∀ q ∈ arcAPairs s, q ∈ hexPairs := by decide
  have hB : ∀ s : Fin 3, ∀ q ∈ arcBPairs s, q ∈ hexPairs := by decide
  have hC : ∀ s : Fin 3, ∀ q ∈ hexPairs, q ∈ arcAPairs s ∨ q ∈ arcBPairs s := by decide
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rintro p (hp | hp)
    · obtain ⟨q, hq, hpq⟩ := mem_arcA_iff.1 hp
      exact mem_hexSet_iff.2 ⟨q, hA s q hq, hpq⟩
    · obtain ⟨q, hq, hpq⟩ := mem_arcB_iff.1 hp
      exact mem_hexSet_iff.2 ⟨q, hB s q hq, hpq⟩
  · intro p hp
    obtain ⟨q, hq, hpq⟩ := mem_hexSet_iff.1 hp
    rcases hC s q hq with hq' | hq'
    exacts [Or.inl (mem_arcA_iff.2 ⟨q, hq', hpq⟩), Or.inr (mem_arcB_iff.2 ⟨q, hq', hpq⟩)]

/-- **The two arcs meet exactly in the two ends of the remaining edge that cuts the cycle.** -/
theorem arcs_inter (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (s : Fin 3) :
    edgesCover drawing (arcA e s) ∩ edgesCover drawing (arcB e s) = {x s, y (s + 1)} := by
  have hne : ∀ s : Fin 3, ∀ q ∈ arcAPairs s, ∀ r ∈ arcBPairs s, ¬ (q.1 = r.1 ∧ q.2 = r.2) := by
    decide
  have h1 : ∀ s : Fin 3, ∀ q ∈ arcAPairs s, ∀ r ∈ arcBPairs s, q.1 = r.1 → q.1 = s := by decide
  have h2 : ∀ s : Fin 3, ∀ q ∈ arcAPairs s, ∀ r ∈ arcBPairs s, q.2 = r.2 → q.2 = s + 1 := by
    decide
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rintro p ⟨hpA, hpB⟩
    obtain ⟨q, hq, hpq⟩ := mem_arcA_iff.1 hpA
    obtain ⟨r, hr, hpr⟩ := mem_arcB_iff.1 hpB
    obtain ⟨-, hincq, hincr⟩ := hd.edge_inter (h.isLink q.1 q.2).edge_mem
      (h.isLink r.1 r.2).edge_mem (h.e_ne (hne s q hq r hr)) hpq hpr
    rcases h.inc_elim hincq with hh | hh <;> rcases h.inc_elim hincr with hh' | hh'
    · exact Or.inl (hh.trans (by rw [h1 s q hq r hr (h.x_injective (hh.symm.trans hh'))]))
    · exact absurd (hh.symm.trans hh') (h.x_ne_y _ _)
    · exact absurd (hh.symm.trans hh') (h.y_ne_x _ _)
    · exact Or.inr (hh.trans (by rw [h2 s q hq r hr (h.y_injective (hh.symm.trans hh'))]))
  · rintro p (rfl | rfl)
    · exact ⟨mem_arcA_iff.2 ⟨(s, s), by simp [arcAPairs],
        (hd.edge_isArcBetween (h.isLink s s)).left_mem⟩,
        mem_arcB_iff.2 ⟨(s, s + 2), by simp [arcBPairs],
          (hd.edge_isArcBetween (h.isLink s (s + 2))).left_mem⟩⟩
    · exact ⟨mem_arcA_iff.2 ⟨(s + 1, s + 1), by simp [arcAPairs],
        (hd.edge_isArcBetween (h.isLink (s + 1) (s + 1))).right_mem⟩,
        mem_arcB_iff.2 ⟨(s + 2, s + 1), by simp [arcBPairs],
          (hd.edge_isArcBetween (h.isLink (s + 2) (s + 1))).right_mem⟩⟩

/-- **The endpoints of two of the three remaining edges alternate on the six-cycle.**

The remaining edge indexed by `s` has ends `x s` and `y (s+1)`; they cut the six-cycle into
two arcs `A` and `B` meeting only in those two points. The remaining edge indexed by `s+1`
has ends `x (s+1)` and `y (s+1+1)`, and this says one of them is interior to `A` and the other
interior to `B`. Since the three remaining edges are indexed by `Fin 3`, every *pair* of them
is of this form, which is what the blueprint's "their endpoints alternate on the six-cycle"
asserts. -/
theorem chords_alternate (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (s : Fin 3) :
    ∃ A B : Set Plane,
      IsArcBetween A (x s) (y (s + 1)) ∧ IsArcBetween B (x s) (y (s + 1)) ∧
        A ∪ B = hexSet drawing e ∧ A ∩ B = {x s, y (s + 1)} ∧
        x (s + 1) ∈ A \ ({x s, y (s + 1)} : Set Plane) ∧
        y (s + 1 + 1) ∈ B \ ({x s, y (s + 1)} : Set Plane) := by
  have hsucc : s + 1 + 1 = s + 2 := by revert s; decide
  have hs1 : s + 1 ≠ s := by revert s; decide
  have hs2 : s + 2 ≠ s + 1 := by revert s; decide
  refine ⟨_, _, h.arcA_isArcBetween hd s, h.arcB_isArcBetween hd s, arcs_union s,
    h.arcs_inter hd s, ⟨?_, ?_⟩, ?_, ?_⟩
  · exact mem_arcA_iff.2 ⟨(s + 1, s), by simp [arcAPairs],
      (hd.edge_isArcBetween (h.isLink (s + 1) s)).left_mem⟩
  · rintro (hc | hc)
    exacts [h.x_ne_x hs1 hc, h.x_ne_y _ _ hc]
  · rw [hsucc]
    exact mem_arcB_iff.2 ⟨(s + 2, s + 2), by simp [arcBPairs],
      (hd.edge_isArcBetween (h.isLink (s + 2) (s + 2))).right_mem⟩
  · rw [hsucc]
    rintro (hc | hc)
    exacts [h.y_ne_x _ _ hc, h.y_ne_y hs2 hc]

/-! ### Two of the three remaining edges lie on the same side -/

/-- A remaining edge lies wholly in one of two disjoint open sets covering the complement of
the six-cycle: its interior is connected and misses the cycle. -/
theorem chord_subset_or (h : IsK33Config G x y e) (hd : IsDrawing G drawing) {U V : Set Plane}
    (hUo : IsOpen U) (hVo : IsOpen V) (hUV : Disjoint U V)
    (hcover : (hexSet drawing e)ᶜ ⊆ U ∪ V) (s : Fin 3) :
    openArc (drawing (e s (s + 1))) ⊆ U ∨ openArc (drawing (e s (s + 1))) ⊆ V := by
  have hsub : openArc (drawing (e s (s + 1))) ⊆ U ∪ V :=
    (h.chord_openArc_subset_compl hd s).trans hcover
  obtain ⟨p, hp⟩ := chord_openArc_nonempty (drawing := drawing) (e := e) s
  rcases hsub hp with hpU | hpV
  · exact Or.inl ((h.chord_openArc_isPreconnected hd s).subset_left_of_subset_union
      hUo hVo hUV hsub ⟨p, hp, hpU⟩)
  · refine Or.inr ((h.chord_openArc_isPreconnected hd s).subset_left_of_subset_union
      hVo hUo hUV.symm (hsub.trans (by rw [Set.union_comm])) ⟨p, hp, hpV⟩)

/-- **Two of the three remaining edges lie on the same side of the six-cycle.** The blueprint's
"two of the three lie on the same side": three edges, two sides. The two sides arrive here as
an arbitrary pair of disjoint open sets covering the complement of the cycle, which is the form
the polygonal Jordan curve theorem supplies them in. -/
theorem exists_two_chords_same_side (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    {U V : Set Plane} (hUo : IsOpen U) (hVo : IsOpen V) (hUV : Disjoint U V)
    (hcover : (hexSet drawing e)ᶜ ⊆ U ∪ V) :
    ∃ s t : Fin 3, s ≠ t ∧
      ((openArc (drawing (e s (s + 1))) ⊆ U ∧ openArc (drawing (e t (t + 1))) ⊆ U) ∨
        (openArc (drawing (e s (s + 1))) ⊆ V ∧ openArc (drawing (e t (t + 1))) ⊆ V)) := by
  have key := fun s ↦ h.chord_subset_or hd hUo hVo hUV hcover s
  rcases key 0 with h0 | h0 <;> rcases key 1 with h1 | h1 <;> rcases key 2 with h2 | h2
  exacts [⟨0, 1, by decide, Or.inl ⟨h0, h1⟩⟩, ⟨0, 1, by decide, Or.inl ⟨h0, h1⟩⟩,
    ⟨0, 2, by decide, Or.inl ⟨h0, h2⟩⟩, ⟨1, 2, by decide, Or.inr ⟨h1, h2⟩⟩,
    ⟨1, 2, by decide, Or.inl ⟨h1, h2⟩⟩, ⟨0, 2, by decide, Or.inr ⟨h0, h2⟩⟩,
    ⟨0, 1, by decide, Or.inr ⟨h0, h1⟩⟩, ⟨0, 1, by decide, Or.inr ⟨h0, h1⟩⟩]

end IsK33Config

end Graph

end BundlePart420

section BundlePart421
/- Source: dev/planar_search/schoenflies_port/Schoenflies/AlternatingCrosscuts.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/



/-!
# Corollary 2.9: alternating crosscuts intersect

Two crosscuts of a simple closed polygon whose four endpoints alternate around the curve, and
whose interiors lie on the same side of it, must meet.

## What the proof actually uses, and what it therefore assumes

The blueprint's proof is three sentences, and it uses exactly three things about the *second*
crosscut: its interior is connected, its interior lies in the same region of `ℝ² ∖ C` as the
first crosscut's, and its two endpoints are limits of its interior lying one on each of the two
arcs. **Nothing about the second crosscut is polygonal, and nothing about it is simple.** So the
core statement here, `IsPolygonalCrosscut.inter_cover_nonempty`, takes the second crosscut as a
bare preconnected set `Q` — the blueprint's `P₂ ∖ {endpoints}` — with two named points of
`closure Q`. This is not a weakening: the polygonality of `P₂` is a hypothesis of the blueprint's
corollary that its proof never consumes, and dropping it is what lets a consumer apply the
corollary to a *drawn* edge of a plane graph, which is a topological arc.

`IsPolygonalCrosscut.arc_inter_cover_nonempty` is the same statement with `Q` presented as
`P ∖ {w₁, w₂}` for a simple arc `P` from `w₁` to `w₂`, which is the blueprint's own reading; the
two hypotheses about `closure Q` are then automatic (`IsArcBetween.left_mem_closure_diff`).

## The alternation hypothesis

"The endpoints alternate around `C`" is, concretely, that one endpoint of the second crosscut
lies on the first arc and not the second, and the other the other way round. That is how the
core statement takes it. The packaged form `IsPolygonalCrosscut.alternating_inter_nonempty`
takes instead the shape a plane-graph argument produces — two arcs `A, B` meeting exactly in the
two cut points `{p, q}`, one endpoint in `A ∖ {p, q}` and one in `B ∖ {p, q}` — which is
verbatim the conclusion of `Graph.IsK33Config.chords_alternate`, and derives the
non-memberships from `A ∩ B = {p, q}`.

## The "same side" hypothesis, in three interchangeable forms

Theorem 2.8 is parametrized by a reference point `y` in the region of `ℝ² ∖ C` that the first
crosscut does *not* enter, so "the region the crosscut enters" is `farRegion C.carrier y`. The
second crosscut's interior has to lie there too. A consumer may supply that as

* `Q ⊆ farRegion C.carrier y` — the primitive form;
* `Q ⊆ connectedComponentIn C.carrierᶜ z` for some point `z` of the first crosscut off `C`
  — literally "both interiors lie in the same component", which is what a plane-graph argument
  has in hand (`IsPolygonalCrosscut.connectedComponentIn_cover_eq` converts it);
* `Q ⊆ inside C.carrier` with `y ∈ outside C.carrier`, or `Q ⊆ outside C.carrier` with
  `y ∈ inside C.carrier` — the blueprint's literal "the same one of `Int(C)`, `Ext(C)`".

## How the `K(3,3)` argument closes on this

`alternating_inter_nonempty` was written against `Graph.IsK33Config.chords_alternate`, and the
fit was checked: with `hK33 : Graph.IsK33Config G x y e`, `hd : Graph.IsDrawing G drawing`,
`hcross : IsPolygonalCrosscut C J₁ J₂ K a k yref` the realization of the chord `e s (s+1)` as a
crosscut, and `hside` the "same side" clause supplied by
`Graph.IsK33Config.exists_two_chords_same_side`, the last step is one term:

```
obtain ⟨A, B, hAarc, hBarc, hunion, hinter, hw₁, hw₂⟩ := hK33.chords_alternate hd s
obtain ⟨hA, hB⟩ := hreal A B hAarc hBarc hunion
exact hcross.alternating_inter_nonempty hA hB hinter
  (hd.edge_isArcBetween (hK33.isLink (s + 1) (s + 1 + 1))) hside hw₁ hw₂
```

with `hreal` the still-missing realization step: the hexagon, as a polygonal Jordan curve cut
into the two arcs `A` and `B`, presented as a `ClosedPolygon` with `C.arc a k = A` and
`C.arc (a + k) (m + 3 - k) = B`. Everything on either side of that step is in place. Note that
the two arcs must be obtained from `chords_alternate` *before* the realization, since it is
those particular sets the realization has to reproduce.

## Blueprint

* `IsArcBetween.isPreconnected_diff`, `IsArcBetween.left_mem_closure_diff`,
  `IsArcBetween.right_mem_closure_diff` — the interior of an arc is connected and has both
  endpoints in its closure. General-purpose; they belong in `Subarc.lean`.
* `IsPolygonalCrosscut.connectedComponentIn_cover_eq` — the region the crosscut enters is the
  component of any of its points off `C`.
* `IsPolygonalCrosscut.inter_cover_nonempty` — `cor:alternating-crosscuts`, core form.
* `IsPolygonalCrosscut.arc_inter_cover_nonempty` — the same for a second crosscut presented as
  a simple arc.
* `IsPolygonalCrosscut.alternating_inter_nonempty` — the same in the two-arcs shape that
  `Graph.IsK33Config.chords_alternate` produces.
* `IsPolygonalCrosscut.alternating_inter_nonempty_of_same_side` — the same with "both interiors
  lie in one component of `ℝ² ∖ C`" as the side hypothesis.
* `IsPolygonalCrosscut.alternating_inter_nonempty_inside`,
  `…_outside` — the blueprint's literal cases (a) and (b).
* `alternating_crosscuts` — `cor:alternating-crosscuts`, bundled.
-/

open Set unitInterval

namespace Schoenflies

/-! ## The interior of an arc

`openArc f` is `f '' Ioo 0 1`; for an arc between two named points it is the arc minus those
points (`openArc_eq_diff`). The two facts the corollary needs — that the interior is connected,
and that each endpoint lies in its closure — are `Schoenflies.IsArcBetween.isPreconnected_diff`
and `…left_mem_closure_diff` in `Schoenflies/Subarc.lean`, where three modules can share them.
-/

variable {A : Set Plane} {p q : Plane}

/-! ## The corollary -/

variable {m m₁ m₂ : ℕ} {C : ClosedPolygon m} {J₁ : ClosedPolygon m₁} {J₂ : ClosedPolygon m₂}
  {K : List Piece} {a : ZMod (m + 3)} {k : ℕ} {y : Plane}

namespace IsPolygonalCrosscut

variable (h : IsPolygonalCrosscut C J₁ J₂ K a k y)
include h

/-- **The region the crosscut enters is the component of any of its points off `C`.** This is
what lets "both crosscuts lie on the same side" be supplied as a statement about one connected
component, which is the form a plane-graph argument has it in. -/
theorem connectedComponentIn_cover_eq {z : Plane} (hz : z ∈ cover K) (hzC : z ∉ C.carrier) :
    connectedComponentIn C.carrierᶜ z = farRegion C.carrier y :=
  h.regionPairC.left.connectedComponentIn_eq C.isSeparating_carrier
    (diff_subset_farRegion h.avoids ⟨hz, hzC⟩)

/-- **Corollary 2.9, core form.** Let `K` be a crosscut of `C` cutting it at `a` and `a + k`, and
let `Q` be a connected set lying in the same region of `ℝ² ∖ C` as `K` — the interior of a second
crosscut. If `Q` has in its closure a point of the first arc that is not on the second, and a
point of the second arc that is not on the first — that is, if the endpoints of the two crosscuts
alternate — then `Q` meets `K`.

The proof is the blueprint's. By Theorem 2.8 the region minus the first crosscut is the union of
the two cells; `Q`, being connected and (for contradiction) missing the first crosscut, lies in
one of them; and the closure of that cell meets `C` in one arc only
(`IsPolygonalCrosscut.closure_cell_inter₁`), so one of the two named points cannot be there. -/
theorem inter_cover_nonempty {Q : Set Plane} {w₁ w₂ : Plane}
    (hconn : IsPreconnected Q) (hside : Q ⊆ farRegion C.carrier y)
    (hw₁ : w₁ ∈ closure Q) (hw₂ : w₂ ∈ closure Q)
    (hw₁A : w₁ ∈ C.arc a k) (hw₁B : w₁ ∉ C.arc (a + k) (m + 3 - k))
    (hw₂B : w₂ ∈ C.arc (a + k) (m + 3 - k)) (hw₂A : w₂ ∉ C.arc a k) :
    (Q ∩ cover K).Nonempty := by
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty, Set.eq_empty_iff_forall_notMem] at hempty
  -- The second crosscut's interior lies in the region minus the first crosscut.
  have hsub : Q ⊆ farRegion C.carrier y \ cover K :=
    fun z hz => ⟨hside hz, fun hzK => hempty z ⟨hz, hzK⟩⟩
  -- It is nonempty, because it has a point in its closure.
  obtain ⟨z, hz⟩ : Q.Nonempty := by
    by_contra hQ
    rw [Set.not_nonempty_iff_eq_empty] at hQ
    rw [hQ, closure_empty] at hw₁
    simp at hw₁
  have hzcell : z ∈ farRegion J₁.carrier y ∪ farRegion J₂.carrier y := by
    rw [← h.region_eq]; exact hsub hz
  -- Being connected, it lies in a single cell; the closure of that cell meets `C` in one arc.
  rcases hzcell with hz₁ | hz₂
  · have hQ₁ : Q ⊆ farRegion J₁.carrier y := by
      have hcc := hconn.subset_connectedComponentIn hz hsub
      rwa [h.cell_isComponent₁ z hz₁] at hcc
    have hmem : w₂ ∈ closure (farRegion J₁.carrier y) ∩ C.carrier :=
      ⟨closure_mono hQ₁ hw₂, C.arc_subset_carrier _ _ hw₂B⟩
    rw [h.closure_cell_inter₁] at hmem
    exact hw₂A hmem
  · have hQ₂ : Q ⊆ farRegion J₂.carrier y := by
      have hcc := hconn.subset_connectedComponentIn hz hsub
      rwa [h.cell_isComponent₂ z hz₂] at hcc
    have hmem : w₁ ∈ closure (farRegion J₂.carrier y) ∩ C.carrier :=
      ⟨closure_mono hQ₂ hw₁, C.arc_subset_carrier _ _ hw₁A⟩
    rw [h.closure_cell_inter₂] at hmem
    exact hw₁B hmem

/-- **Corollary 2.9 for a second crosscut presented as a simple arc.** `P` is an arc from `w₁` to
`w₂` whose interior `P ∖ {w₁, w₂}` lies in the same region of `ℝ² ∖ C` as the first crosscut, and
whose endpoints alternate with the first crosscut's around `C`. Then `P` meets the first
crosscut — and in fact it does so in the *interior* of `P`, which is what the conclusion of
`inter_cover_nonempty` says. -/
theorem arc_inter_cover_nonempty {P : Set Plane} {w₁ w₂ : Plane}
    (hP : IsArcBetween P w₁ w₂) (hside : P \ {w₁, w₂} ⊆ farRegion C.carrier y)
    (hw₁A : w₁ ∈ C.arc a k) (hw₁B : w₁ ∉ C.arc (a + k) (m + 3 - k))
    (hw₂B : w₂ ∈ C.arc (a + k) (m + 3 - k)) (hw₂A : w₂ ∉ C.arc a k) :
    (P ∩ cover K).Nonempty := by
  obtain ⟨z, hzQ, hzK⟩ := h.inter_cover_nonempty hP.isPreconnected_diff hside
    hP.left_mem_closure_diff hP.right_mem_closure_diff hw₁A hw₁B hw₂B hw₂A
  exact ⟨z, hzQ.1, hzK⟩

/-- **Corollary 2.9 in the shape a plane-graph argument produces it.** The two arcs of `C` cut off
by the first crosscut are handed over as sets `A, B` meeting exactly in the two cut points
`{p, q}`; the second crosscut is an arc from `w₁` to `w₂` with `w₁` interior to `A` and `w₂`
interior to `B`. This is verbatim the data `Graph.IsK33Config.chords_alternate` returns. -/
theorem alternating_inter_nonempty {A B P : Set Plane} {p q w₁ w₂ : Plane}
    (hA : C.arc a k = A) (hB : C.arc (a + k) (m + 3 - k) = B)
    (hAB : A ∩ B = ({p, q} : Set Plane))
    (hP : IsArcBetween P w₁ w₂) (hside : P \ {w₁, w₂} ⊆ farRegion C.carrier y)
    (hw₁ : w₁ ∈ A \ ({p, q} : Set Plane)) (hw₂ : w₂ ∈ B \ ({p, q} : Set Plane)) :
    (P ∩ cover K).Nonempty := by
  -- A point interior to one arc is off the other, since the two arcs meet only in `{p, q}`.
  refine h.arc_inter_cover_nonempty hP hside (hA ▸ hw₁.1) ?_ (hB ▸ hw₂.1) ?_
  · rw [hB]; exact fun hmem => hw₁.2 (hAB ▸ Set.mem_inter hw₁.1 hmem)
  · rw [hA]; exact fun hmem => hw₂.2 (hAB ▸ Set.mem_inter hmem hw₂.1)

/-- **Corollary 2.9 with "the same side" read as "the same connected component".** The point `z`
is any point of the first crosscut off `C`; the hypothesis is that the interior of the second
crosscut lies in the component of `ℝ² ∖ C` containing `z`. -/
theorem alternating_inter_nonempty_of_same_side {A B P : Set Plane} {p q w₁ w₂ z : Plane}
    (hz : z ∈ cover K) (hzC : z ∉ C.carrier)
    (hA : C.arc a k = A) (hB : C.arc (a + k) (m + 3 - k) = B)
    (hAB : A ∩ B = ({p, q} : Set Plane))
    (hP : IsArcBetween P w₁ w₂)
    (hside : P \ {w₁, w₂} ⊆ connectedComponentIn C.carrierᶜ z)
    (hw₁ : w₁ ∈ A \ ({p, q} : Set Plane)) (hw₂ : w₂ ∈ B \ ({p, q} : Set Plane)) :
    (P ∩ cover K).Nonempty :=
  h.alternating_inter_nonempty hA hB hAB hP
    (hside.trans (h.connectedComponentIn_cover_eq hz hzC).subset) hw₁ hw₂

/-- **Corollary 2.9, case (a):** both crosscuts run inside `C`. The reference point of the first
crosscut lying in `Ext(C)` is exactly the statement that the first crosscut runs inside. -/
theorem alternating_inter_nonempty_inside {A B P : Set Plane} {p q w₁ w₂ : Plane}
    (hy : y ∈ outside C.carrier)
    (hA : C.arc a k = A) (hB : C.arc (a + k) (m + 3 - k) = B)
    (hAB : A ∩ B = ({p, q} : Set Plane))
    (hP : IsArcBetween P w₁ w₂) (hside : P \ {w₁, w₂} ⊆ inside C.carrier)
    (hw₁ : w₁ ∈ A \ ({p, q} : Set Plane)) (hw₂ : w₂ ∈ B \ ({p, q} : Set Plane)) :
    (P ∩ cover K).Nonempty :=
  h.alternating_inter_nonempty hA hB hAB hP
    (hside.trans (C.isSeparating_carrier.farRegion_eq_inside hy).symm.subset) hw₁ hw₂

/-- **Corollary 2.9, case (b):** both crosscuts run outside `C`. -/
theorem alternating_inter_nonempty_outside {A B P : Set Plane} {p q w₁ w₂ : Plane}
    (hy : y ∈ inside C.carrier)
    (hA : C.arc a k = A) (hB : C.arc (a + k) (m + 3 - k) = B)
    (hAB : A ∩ B = ({p, q} : Set Plane))
    (hP : IsArcBetween P w₁ w₂) (hside : P \ {w₁, w₂} ⊆ outside C.carrier)
    (hw₁ : w₁ ∈ A \ ({p, q} : Set Plane)) (hw₂ : w₂ ∈ B \ ({p, q} : Set Plane)) :
    (P ∩ cover K).Nonempty :=
  h.alternating_inter_nonempty hA hB hAB hP
    (hside.trans (C.isSeparating_carrier.farRegion_eq_outside hy).symm.subset) hw₁ hw₂

end IsPolygonalCrosscut

/-- **Corollary 2.9 (alternating crosscuts intersect).** Let `C` be a simple closed polygon and
`K` a polygonal crosscut of it cutting it at the vertices `a` and `a + k`, with `J₁` and `J₂` the
two closed polygons it forms with the two arcs `A` and `B`, and `y` a point of the region of
`ℝ² ∖ C` the crosscut does not enter. Let `P` be a second crosscut: a simple arc from `w₁` to
`w₂`, with interior in the same region of `ℝ² ∖ C` as `K`, and with its two endpoints alternating
with `K`'s around `C` — one interior to `A`, the other interior to `B`. Then the two crosscuts
meet.

The blueprint also assumes `P` polygonal and its four endpoints distinct. Neither is used: the
distinctness of the endpoints is subsumed by `w₁` and `w₂` being interior to different arcs, and
polygonality of `P` plays no part in the argument at all. -/
theorem alternating_crosscuts {A B P : Set Plane} {p q w₁ w₂ : Plane}
    (h : IsPolygonalCrosscut C J₁ J₂ K a k y)
    (hA : C.arc a k = A) (hB : C.arc (a + k) (m + 3 - k) = B)
    (hAB : A ∩ B = ({p, q} : Set Plane))
    (hP : IsArcBetween P w₁ w₂) (hside : P \ {w₁, w₂} ⊆ farRegion C.carrier y)
    (hw₁ : w₁ ∈ A \ ({p, q} : Set Plane)) (hw₂ : w₂ ∈ B \ ({p, q} : Set Plane)) :
    (P ∩ cover K).Nonempty :=
  h.alternating_inter_nonempty hA hB hAB hP hside hw₁ hw₂

end Schoenflies

end BundlePart421

section BundlePart422
/- Source: dev/planar_search/schoenflies_port/Schoenflies/Graph/K33Planar.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/




/-!
# Lemma 3.10: the utility graph is not planar, and Corollary 3.11 for its subdivisions

`Schoenflies/Graph/K33.lean` built the whole configuration: the six-cycle of a drawn `K(3,3)`
is a Jordan curve, each of the three remaining edges is a crosscut of it, two of the three lie
on the same side, their endpoints alternate, and any two of them are disjoint. This module
wires those five facts to `Schoenflies.alternating_crosscuts` and derives the contradiction; it
then does the blueprint's reduction of `cor:k33-subdivision` to `lem:k33`.

**One hypothesis is assumed and not proved: `Graph.IsHexRealization`. See "The gap" below.**
The remaining results use only the hypotheses in their statements.

## Blueprint

* `Graph.IsHexCrosscut` — the six-cycle, together with one of the three remaining edges, in the
  vocabulary `Schoenflies.IsPolygonalCrosscut` speaks: a `Schoenflies.ClosedPolygon`, its two
  arcs, the crosscut, and a reference point.
* `Graph.IsK33Config.endpoints_subset_arcA`, `…_arcB`, `…exists_reference_point`,
  `…isHexCrosscut` — the four *topological* clauses of `Schoenflies.IsPolygonalCrosscut`,
  discharged from the drawing, so that only the combinatorial realization has to be assumed.
* `Graph.IsHexRealization` — that combinatorial realization, and the one thing assumed here.
* `Graph.IsK33Config.exists_two_chords_same_region` — `lem:k33`, "two of the three lie on the
  same side", with the side named as a region of the complement rather than as one of a pair
  of open sets, which is the form the crosscut corollary consumes.
* `Graph.IsK33Config.false_of_isHexCrosscut` — the contradiction at a *fixed* pair of remaining
  edges: `cor:alternating-crosscuts` makes them meet, `chords_disjoint` says they do not.
* `Graph.IsK33Config.false_of_hexCrosscuts`, `…false_of_hexRealizations` — `lem:k33` for a
  drawing that is already polygonal.
* `Graph.IsK33Config.not_isDrawing` — `lem:k33`: a graph carrying a copy of `K(3,3)` has no
  plane drawing at all. `lem:polygonal-redrawing` reduces the general drawing to a polygonal
  one, which is the only place polygonality is used.
* `Graph.IsArcK33`, `Graph.k33Graph`, `Graph.IsArcK33.arcDrawing`, `…isDrawing`,
  `…isK33Config`, `…false_of_realization` — `cor:k33-subdivision`, first half: nine arcs in the
  plane meeting only where a `K(3,3)` forces them to already *are* a plane drawing of `K(3,3)`,
  on an abstract graph built here for the purpose.
* `Graph.IsK33Subdivision`, `…isArcK33`, `…false_of_realization` — `cor:k33-subdivision`: in a
  plane drawing of a subdivision, the branch paths draw nine such arcs.

## The gap: realizing the six-cycle as a `ClosedPolygon`

Every statement of `Schoenflies/PolygonalJordan.lean`, `Schoenflies/PolygonalCrosscut.lean` and
`Schoenflies/AlternatingCrosscuts.lean` is about a `Schoenflies.ClosedPolygon m` — a cyclic
*vertex list* with `vertex_inj`, `edges_meet` and `corner`. The six-cycle of a polygonally
drawn `K(3,3)` is a polygonal Jordan curve as a **point set**, and nothing in the development
turns a point set into a `ClosedPolygon`: there is no declaration anywhere whose conclusion is
`∃ m (C : ClosedPolygon m), C.carrier = _`. The only closed polygons that exist are the
hand-built `Schoenflies.triangle` and `Schoenflies.unitTriangle`.

`IsHexRealization` is exactly that missing step, stated for the one curve this argument needs
it for and pared down to its combinatorial core: four closed polygons and four equations
identifying their carriers and edge lists with the drawing. No topological side condition
survives in it — the reference point of Theorem 2.8 and the three "meets" clauses are proved
here from the drawing. It is *not proved here*, and every theorem below that mentions it is
therefore requires that realization as a hypothesis.

**Why the realization is allowed to change the drawing.** `IsHexRealization` asks for
`C.arc a k = arcA e s`, which pins the two ends of that arc — the vertices `x s` and
`y (s+1)` — to be *vertices* of `C`. A `Schoenflies.ClosedPolygon` has no straight vertices
(its `corner` field), so this is possible only if the six-cycle actually turns at `x s` and at
`y (s+1)`. A polygonal drawing need not do that: two of the three polygonal edges at a vertex
may leave it in exactly opposite directions, and then no closed polygon with that carrier has
that point as a vertex. A realization must therefore be free to bend the drawing at the six
vertices first, and `Graph.IsK33Config.not_isDrawing` gives it that freedom: it hands the
realization a polygonal drawing and accepts *any* drawing back. This restriction comes from
`Schoenflies.IsPolygonalCrosscut`, not from anything here; the alternative is a crosscut
interface that lets the two cut points be interior to edges of `C`.
-/

open Set Schoenflies unitInterval
open scoped Graph

namespace Graph

variable {β : Type*} {G : Graph Plane β} {x y : Fin 3 → Plane} {e : Fin 3 → Fin 3 → β}
variable {drawing : β → ℝ → Plane} {s t : Fin 3} {R : Set Plane}

/-! ### The missing realization, isolated

The six-cycle of a polygonally drawn `K(3,3)`, cut by the remaining edge `e s (s+1)`, presented
in the vocabulary of `Schoenflies.IsPolygonalCrosscut`: a `ClosedPolygon` whose carrier is the
six-cycle, whose two arcs from the cut are the two halves `arcA e s` and `arcB e s`, and whose
crosscut occupies exactly the remaining edge's arc. -/

/-- **The six-cycle and one remaining edge, realized as a polygonal crosscut.** `C` is the
six-cycle as a `Schoenflies.ClosedPolygon`, cut at the vertices `a` and `a + k` — which are the
two ends `x s` and `y (s+1)` of the remaining edge indexed by `s` — into the two arcs
`arcA e s` and `arcB e s`; `K` is the remaining edge, and `J₁`, `J₂` the two closed polygons it
forms with the two arcs.

This is the *only* thing the argument below assumes, and it is exactly what a bridge from
polygonal Jordan curves to `Schoenflies.ClosedPolygon` would supply. -/
def IsHexCrosscut (drawing : β → ℝ → Plane) (e : Fin 3 → Fin 3 → β) (s : Fin 3) : Prop :=
  ∃ (m m₁ m₂ : ℕ) (C : ClosedPolygon m) (J₁ : ClosedPolygon m₁) (J₂ : ClosedPolygon m₂)
    (K : List Piece) (a : ZMod (m + 3)) (k : ℕ) (yref : Plane),
      C.carrier = hexSet drawing e ∧
      C.arc a k = edgesCover drawing (arcA e s) ∧
      C.arc (a + k) (m + 3 - k) = edgesCover drawing (arcB e s) ∧
      cover K = edgeArc drawing (e s (s + 1)) ∧
      IsPolygonalCrosscut C J₁ J₂ K a k yref

/-- The six-cycle separates the plane: it is the carrier of a closed polygon, and
`thm:polygonal-jordan` applies to that. -/
theorem isSeparating_hexSet (h : IsHexCrosscut drawing e s) :
    IsSeparating (hexSet drawing e) := by
  obtain ⟨_, _, _, C, _, _, _, _, _, _, hcar, _⟩ := h
  exact hcar ▸ C.isSeparating_carrier

namespace IsK33Config

/-! ### The alternation, with the two arcs named

`Graph.IsK33Config.chords_alternate` returns the two arcs existentially. The crosscut corollary
has to be handed *those particular sets*, since the realization has to reproduce them, so the
two membership clauses are restated here with the arcs written out. -/

/-- The near end of the next remaining edge is interior to the first arc. -/
theorem x_succ_mem_arcA (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (s : Fin 3) :
    x (s + 1) ∈ edgesCover drawing (arcA e s) \ ({x s, y (s + 1)} : Set Plane) := by
  have hs1 : ∀ s : Fin 3, s + 1 ≠ s := by decide
  refine ⟨mem_arcA_iff.2 ⟨(s + 1, s), by simp [arcAPairs],
    (hd.edge_isArcBetween (h.isLink (s + 1) s)).left_mem⟩, ?_⟩
  rintro (hc | hc)
  exacts [h.x_ne_x (hs1 s) hc, h.x_ne_y _ _ hc]

/-- The far end of the next remaining edge is interior to the second arc. -/
theorem y_succ_mem_arcB (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (s : Fin 3) :
    y (s + 1 + 1) ∈ edgesCover drawing (arcB e s) \ ({x s, y (s + 1)} : Set Plane) := by
  have hsucc : ∀ s : Fin 3, s + 1 + 1 = s + 2 := by decide
  have hs2 : ∀ s : Fin 3, s + 2 ≠ s + 1 := by decide
  rw [hsucc s]
  refine ⟨mem_arcB_iff.2 ⟨(s + 2, s + 2), by simp [arcBPairs],
    (hd.edge_isArcBetween (h.isLink (s + 2) (s + 2))).right_mem⟩, ?_⟩
  rintro (hc | hc)
  exacts [h.y_ne_x _ _ hc, h.y_ne_y (hs2 s) hc]

/-! ### Two of the three remaining edges lie in one region -/

/-- A remaining edge's interior lies inside the edge's arc. -/
theorem chord_openArc_subset_edgeArc (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (s : Fin 3) : openArc (drawing (e s (s + 1))) ⊆ edgeArc drawing (e s (s + 1)) := by
  rw [h.chord_openArc_eq hd s]; exact Set.sdiff_subset

/-- **Two of the three remaining edges lie in one and the same region of the complement of the
six-cycle.** This is `Graph.IsK33Config.exists_two_chords_same_side` with the two sides read as
the two regions `Int` and `Ext` of the polygonal Jordan curve theorem, which is the form the
crosscut corollary consumes. -/
theorem exists_two_chords_same_region (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hsep : IsSeparating (hexSet drawing e)) :
    ∃ s t : Fin 3, s ≠ t ∧ ∃ R : Set Plane, IsRegionOf (hexSet drawing e) R ∧
      openArc (drawing (e s (s + 1))) ⊆ R ∧ openArc (drawing (e t (t + 1))) ⊆ R := by
  obtain ⟨s, t, hst, hcase⟩ := h.exists_two_chords_same_side hd hsep.isOpen_inside
    hsep.isOpen_outside disjoint_inside_outside (inside_union_outside _).ge
  rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨s, t, hst, _, IsRegionOf.inside _, h1, h2⟩
  · exact ⟨s, t, hst, _, IsRegionOf.outside _, h1, h2⟩

/-! ### The topological side conditions of the crosscut, discharged

`Schoenflies.IsPolygonalCrosscut` asks for four things beyond the edge lists: that the crosscut
meets the polygon only in points of each arc, and a reference point off the polygon in the
region the crosscut does not enter. All four are properties of the *drawing*, and are proved
here, so that what has to be assumed from outside is only the combinatorial realization
(`Graph.IsHexRealization`). -/

/-- The two ends of the remaining edge lie on the first arc of the cut. -/
theorem endpoints_subset_arcA (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (s : Fin 3) :
    ({x s, y (s + 1)} : Set Plane) ⊆ edgesCover drawing (arcA e s) := by
  rintro p (rfl | rfl)
  · exact mem_arcA_iff.2 ⟨(s, s), by simp [arcAPairs],
      (hd.edge_isArcBetween (h.isLink s s)).left_mem⟩
  · exact mem_arcA_iff.2 ⟨(s + 1, s + 1), by simp [arcAPairs],
      (hd.edge_isArcBetween (h.isLink (s + 1) (s + 1))).right_mem⟩

/-- The two ends of the remaining edge lie on the second arc of the cut. -/
theorem endpoints_subset_arcB (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (s : Fin 3) :
    ({x s, y (s + 1)} : Set Plane) ⊆ edgesCover drawing (arcB e s) := by
  rintro p (rfl | rfl)
  · exact mem_arcB_iff.2 ⟨(s, s + 2), by simp [arcBPairs],
      (hd.edge_isArcBetween (h.isLink s (s + 2))).left_mem⟩
  · exact mem_arcB_iff.2 ⟨(s + 2, s + 1), by simp [arcBPairs],
      (hd.edge_isArcBetween (h.isLink (s + 2) (s + 1))).right_mem⟩

/-- **The reference point of Theorem 2.8, for a remaining edge.** The interior of the remaining
edge lies in one region of the complement of the six-cycle; any point of the *other* region is a
legitimate reference point, and the other region is nonempty because it is a region. -/
theorem exists_reference_point (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hsep : IsSeparating (hexSet drawing e)) (s : Fin 3) :
    ∃ yref : Plane, yref ∉ hexSet drawing e ∧
      Disjoint (edgeArc drawing (e s (s + 1)))
        (connectedComponentIn (hexSet drawing e)ᶜ yref) := by
  obtain ⟨z, hz⟩ := chord_openArc_nonempty (drawing := drawing) (e := e) s
  have hzC : z ∉ hexSet drawing e := h.chord_openArc_subset_compl hd s hz
  -- The region of `z` and the region on the far side of it are the two regions.
  have hpair := hsep.isRegionPair_farRegion hzC
  obtain ⟨yref, hyref⟩ := (hpair.right.isConnected hsep).nonempty
  refine ⟨yref, hpair.right.subset_compl hyref, ?_⟩
  rw [hpair.right.connectedComponentIn_eq hsep hyref, Set.disjoint_left]
  intro p hp hpfar
  by_cases hpin : p ∈ ({x s, y (s + 1)} : Set Plane)
  · refine hpfar.1 ?_
    rcases hpin with rfl | rfl
    exacts [h.x_mem_hexSet hd s, h.y_mem_hexSet hd (s + 1)]
  · refine hpfar.2 (h.chord_openArc_subset_connectedComponentIn hd s hz ?_)
    rw [h.chord_openArc_eq hd s]
    exact ⟨hp, hpin⟩

end IsK33Config

/-! ### What must still be assumed: the combinatorial realization

Everything above is proved. What is not is that the six-cycle, its two arcs, and the two closed
curves the remaining edge forms with them are *closed polygons at all* — that a polygonal Jordan
curve given as a point set carries a cyclic vertex list. `IsHexRealization` says exactly that,
and nothing more: no reference point, no meeting condition, only the four `ClosedPolygon`s and
the four equations identifying their carriers and edge lists with the drawing. -/

/-- **The six-cycle and one remaining edge, realized combinatorially.** The six-cycle is a
`Schoenflies.ClosedPolygon` `C` whose two arcs from the cut at `a`, `a + k` are the two halves
`arcA e s`, `arcB e s` of the six-cycle; the remaining edge occupies the segments `K`; and the
two closed curves it forms with the two arcs are closed polygons `J₁`, `J₂` carrying exactly
those segments.

This is the one thing this module assumes and does not prove. See "The gap" in the module
docstring. -/
def IsHexRealization (drawing : β → ℝ → Plane) (e : Fin 3 → Fin 3 → β) (s : Fin 3) : Prop :=
  ∃ (m m₁ m₂ : ℕ) (C : ClosedPolygon m) (J₁ : ClosedPolygon m₁) (J₂ : ClosedPolygon m₂)
    (K : List Piece) (a : ZMod (m + 3)) (k : ℕ),
      k ≤ m + 3 ∧
      C.carrier = hexSet drawing e ∧
      C.arc a k = edgesCover drawing (arcA e s) ∧
      C.arc (a + k) (m + 3 - k) = edgesCover drawing (arcB e s) ∧
      cover K = edgeArc drawing (e s (s + 1)) ∧
      SameEdges J₁.pieces (C.arcPieces a k ++ K) ∧
      SameEdges J₂.pieces (C.arcPieces (a + k) (m + 3 - k) ++ K)

namespace IsK33Config

/-- **The realization is enough.** The four topological clauses of
`Schoenflies.IsPolygonalCrosscut` come from the drawing: the remaining edge meets the six-cycle
exactly in its own two ends (`chord_inter_hexSet`), which lie on both arcs, and the reference
point is `exists_reference_point`. -/
theorem isHexCrosscut (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hr : IsHexRealization drawing e s) : IsHexCrosscut drawing e s := by
  obtain ⟨m, m₁, m₂, C, J₁, J₂, K, a, k, hk, hcar, hA, hB, hK, hE₁, hE₂⟩ := hr
  have hsep : IsSeparating (hexSet drawing e) := hcar ▸ C.isSeparating_carrier
  obtain ⟨yref, hyref, hdisj⟩ := h.exists_reference_point hd hsep s
  refine ⟨m, m₁, m₂, C, J₁, J₂, K, a, k, yref, hcar, hA, hB, hK,
    ⟨hk, hE₁, hE₂, ?_, ?_, ?_, ?_⟩⟩
  · rw [hK, hcar, hA, h.chord_inter_hexSet hd s]
    exact h.endpoints_subset_arcA hd s
  · rw [hK, hcar, hB, h.chord_inter_hexSet hd s]
    exact h.endpoints_subset_arcB hd s
  · rw [hcar]; exact hyref
  · rw [hK, hcar]; exact hdisj

/-! ### The contradiction -/

/-- **The two remaining edges indexed by `s` and `s + 1` cannot lie in one region.** Their four
ends alternate around the six-cycle (`chords_alternate`), so `cor:alternating-crosscuts` makes
them meet; but distinct edges of a plane graph meet only at shared vertices, and these two share
none (`chords_disjoint`). -/
theorem false_of_isHexCrosscut (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hcross : IsHexCrosscut drawing e s) (hsep : IsSeparating (hexSet drawing e))
    (hR : IsRegionOf (hexSet drawing e) R)
    (h1 : openArc (drawing (e s (s + 1))) ⊆ R)
    (h2 : openArc (drawing (e (s + 1) (s + 1 + 1))) ⊆ R) : False := by
  obtain ⟨m, m₁, m₂, C, J₁, J₂, K, a, k, yref, hcar, hA, hB, hK, hcc⟩ := hcross
  -- A point of the first remaining edge, off the six-cycle: it pins down the region.
  obtain ⟨z, hz⟩ := chord_openArc_nonempty (drawing := drawing) (e := e) s
  have hzK : z ∈ cover K := by rw [hK]; exact h.chord_openArc_subset_edgeArc hd s hz
  have hzC : z ∉ C.carrier := by rw [hcar]; exact h.chord_openArc_subset_compl hd s hz
  have hzR : z ∈ R := h1 hz
  -- The second remaining edge's interior lies in the component of `z`.
  have hside : edgeArc drawing (e (s + 1) (s + 1 + 1)) \ ({x (s + 1), y (s + 1 + 1)} : Set Plane)
      ⊆ connectedComponentIn C.carrierᶜ z := by
    rw [hcar, hR.connectedComponentIn_eq hsep hzR, ← h.chord_openArc_eq hd (s + 1)]
    exact h2
  -- `cor:alternating-crosscuts`.
  obtain ⟨w, hw₁, hw₂⟩ := hcc.alternating_inter_nonempty_of_same_side hzK hzC hA hB
    (h.arcs_inter hd s) (hd.edge_isArcBetween (h.isLink (s + 1) (s + 1 + 1))) hside
    (h.x_succ_mem_arcA hd s) (h.y_succ_mem_arcB hd s)
  -- … against the disjointness of two remaining edges.
  have hs1 : ∀ s : Fin 3, s + 1 ≠ s := by decide
  have := h.chords_disjoint hd (hs1 s)
  rw [Set.eq_empty_iff_forall_notMem] at this
  exact this w ⟨hw₁, by rwa [hK] at hw₂⟩

/-- **`lem:k33` for a drawing that is already polygonal.** Three remaining edges, two sides:
two of them lie in one region (`exists_two_chords_same_region`); every pair of remaining edges
is indexed by `s` and `s + 1` for some `s`, so `false_of_isHexCrosscut` applies. -/
theorem false_of_hexCrosscuts (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hcross : ∀ s : Fin 3, IsHexCrosscut drawing e s) : False := by
  have hsep : IsSeparating (hexSet drawing e) := isSeparating_hexSet (hcross 0)
  obtain ⟨s, t, hst, R, hR, h1, h2⟩ := h.exists_two_chords_same_region hd hsep
  -- In `Fin 3` two distinct indices are consecutive one way or the other.
  have hpair : ∀ s t : Fin 3, s ≠ t → t = s + 1 ∨ s = t + 1 := by decide
  rcases hpair s t hst with rfl | rfl
  · exact h.false_of_isHexCrosscut hd (hcross s) hsep hR h1 h2
  · exact h.false_of_isHexCrosscut hd (hcross t) hsep hR h2 h1

/-- **`lem:k33` for a polygonal drawing, from the combinatorial realization alone.** -/
theorem false_of_hexRealizations (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hr : ∀ s : Fin 3, IsHexRealization drawing e s) : False :=
  h.false_of_hexCrosscuts hd fun s => h.isHexCrosscut hd (hr s)

/-- **Lemma 3.10 (nonplanarity of `K(3,3)`).** A finite graph carrying a copy of `K(3,3)` has no
plane drawing.

`lem:polygonal-redrawing` replaces an arbitrary drawing by a polygonal one on the same graph and
the same vertices, which is the only use polygonality is put to; the contradiction itself is
`false_of_hexRealizations`. The realization hypothesis is therefore consulted only about
drawings that are already polygonal — and it is allowed to *change* the drawing again, which it
must be: see "The gap" in the module docstring. -/
theorem not_isDrawing [G.Finite] (h : IsK33Config G x y e)
    (hreal : ∀ dr : β → ℝ → Plane, IsDrawing G dr → (∀ f ∈ E(G), IsPolygonal (edgeArc dr f)) →
      ∃ dr' : β → ℝ → Plane, IsDrawing G dr' ∧ ∀ s : Fin 3, IsHexRealization dr' e s) :
    ¬ ∃ dr : β → ℝ → Plane, IsDrawing G dr := by
  rintro ⟨dr, hdr⟩
  obtain ⟨dr', hdr', hpoly⟩ := polygonal_redrawing G dr hdr
  obtain ⟨dr'', hdr'', hr⟩ := hreal dr' hdr' hpoly
  exact h.false_of_hexRealizations hdr'' hr

end IsK33Config

/-! ## Corollary 3.11: no subdivision of `K(3,3)` has a plane drawing

The blueprint's proof replaces each branch path of a subdivision by the simple arc it draws and
then treats that arc as a single edge. Both halves are done here, in that order: first the
*abstract* statement that nine arcs meeting only where they must already carry a drawn
`K(3,3)` (`Graph.IsArcK33`), then the reduction of a drawn subdivision to nine such arcs. -/

/-- **Nine arcs in the plane, meeting only where they must.** This is what a plane drawing of a
subdivision of `K(3,3)` leaves once each branch path has been replaced by the arc it draws: six
distinct points, and for each pair `(i, j)` an arc from `x i` to `y j`, with two distinct arcs
meeting only in a point that is an endpoint of both.

Nothing here mentions a graph. The abstract `K(3,3)` that carries these arcs is built below. -/
structure IsArcK33 (x y : Fin 3 → Plane) (P : Fin 3 → Fin 3 → Set Plane) : Prop where
  /-- The `(i, j)`-th arc runs from `x i` to `y j`. -/
  arc : ∀ i j, IsArcBetween (P i j) (x i) (y j)
  /-- The three points of the first side are distinct. -/
  x_injective : Function.Injective x
  /-- The three points of the second side are distinct. -/
  y_injective : Function.Injective y
  /-- The two sides are disjoint. -/
  ne : ∀ i j, x i ≠ y j
  /-- Two distinct arcs meet only in a common endpoint. -/
  meet : ∀ i j k l, (i, j) ≠ (k, l) →
    P i j ∩ P k l ⊆ ({x i, y j} : Set Plane) ∩ ({x k, y l} : Set Plane)

/-- **The abstract `K(3,3)` on six named points of the plane.** Its edges are index pairs, and
`(i, j)` links `x i` to `y j`. The edge set is all of `Fin 3 × Fin 3`, so no membership side
condition ever has to be discharged. -/
def k33Graph (x y : Fin 3 → Plane) : Graph Plane (Fin 3 × Fin 3) where
  vertexSet := Set.range x ∪ Set.range y
  edgeSet := Set.univ
  IsLink p u v := (u = x p.1 ∧ v = y p.2) ∨ (u = y p.2 ∧ v = x p.1)
  isLink_symm := by
    rintro ⟨i, j⟩ -
    constructor
    rintro u v (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    exacts [Or.inr ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩]
  eq_or_eq_of_isLink_of_isLink := by
    rintro ⟨i, j⟩ u v a b (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp
  edge_mem_iff_exists_isLink := by
    rintro ⟨i, j⟩
    exact ⟨fun _ => ⟨x i, y j, Or.inl ⟨rfl, rfl⟩⟩, fun _ => Set.mem_univ _⟩
  left_mem_of_isLink := by
    rintro ⟨i, j⟩ u v (⟨rfl, -⟩ | ⟨rfl, -⟩)
    exacts [Or.inl ⟨i, rfl⟩, Or.inr ⟨j, rfl⟩]

@[simp] theorem k33Graph_vertexSet (x y : Fin 3 → Plane) :
    V(k33Graph x y) = Set.range x ∪ Set.range y := rfl

@[simp] theorem k33Graph_edgeSet (x y : Fin 3 → Plane) :
    E(k33Graph x y) = (Set.univ : Set (Fin 3 × Fin 3)) := rfl

theorem k33Graph_isLink (x y : Fin 3 → Plane) (i j : Fin 3) :
    (k33Graph x y).IsLink (i, j) (x i) (y j) := Or.inl ⟨rfl, rfl⟩

/-- An endpoint of an edge of the abstract `K(3,3)` is incident with it. -/
theorem k33Graph_inc {x y : Fin 3 → Plane} {i j : Fin 3} {p : Plane}
    (hp : p ∈ ({x i, y j} : Set Plane)) : (k33Graph x y).Inc (i, j) p := by
  rcases hp with rfl | rfl
  · exact ⟨y j, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨x i, Or.inr ⟨rfl, rfl⟩⟩

instance (x y : Fin 3 → Plane) : (k33Graph x y).Finite where
  finite_vertexSet := (Set.finite_range x).union (Set.finite_range y)
  finite_edgeSet := Set.finite_univ

namespace IsArcK33

variable {x y : Fin 3 → Plane} {P : Fin 3 → Fin 3 → Set Plane}

/-- The nine arcs, parametrized: a drawing of `k33Graph`. The parametrizations are the ones the
arcs come with, so the point set of an edge is the arc it was built from
(`IsArcK33.edgeArc_eq`). -/
noncomputable def arcDrawing (h : IsArcK33 x y P) : Fin 3 × Fin 3 → ℝ → Plane :=
  fun p => (h.arc p.1 p.2).choose

theorem edgeArc_eq (h : IsArcK33 x y P) (i j : Fin 3) :
    edgeArc h.arcDrawing (i, j) = P i j := (h.arc i j).choose_spec.2.2.1

theorem arcDrawing_zero (h : IsArcK33 x y P) (i j : Fin 3) : h.arcDrawing (i, j) 0 = x i :=
  (h.arc i j).choose_spec.2.2.2.1

theorem arcDrawing_one (h : IsArcK33 x y P) (i j : Fin 3) : h.arcDrawing (i, j) 1 = y j :=
  (h.arc i j).choose_spec.2.2.2.2

/-- An arc carries none of the six points except its own two ends: a third point `x k` lies on
the arc `P k l` for every `l`, and two distinct arcs meet only in a common end. -/
theorem mem_arc_elim (h : IsArcK33 x y P) {i j : Fin 3} {p : Plane}
    (hpV : p ∈ Set.range x ∪ Set.range y) (hp : p ∈ P i j) :
    p ∈ ({x i, y j} : Set Plane) := by
  have hsucc : ∀ i : Fin 3, i + 1 ≠ i := by decide
  rcases hpV with ⟨k, rfl⟩ | ⟨l, rfl⟩
  · -- `x k` lies on `P k (j+1)`, an arc with a different index pair.
    exact (h.meet i j k (j + 1) (fun hc => hsucc j (congrArg Prod.snd hc).symm)
      ⟨hp, (h.arc k (j + 1)).left_mem⟩).1
  · -- `y l` lies on `P (i+1) l`.
    exact (h.meet i j (i + 1) l (fun hc => hsucc i (congrArg Prod.fst hc).symm)
      ⟨hp, (h.arc (i + 1) l).right_mem⟩).1

/-- **The nine arcs draw the abstract `K(3,3)` in the plane.** -/
theorem isDrawing (h : IsArcK33 x y P) : IsDrawing (k33Graph x y) h.arcDrawing := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨i, j⟩ -
    obtain ⟨hc, hi, -, -, -⟩ := (h.arc i j).choose_spec
    refine ⟨hc, hi, ?_⟩
    rw [show h.arcDrawing (i, j) 0 = x i from h.arcDrawing_zero i j,
      show h.arcDrawing (i, j) 1 = y j from h.arcDrawing_one i j]
    exact k33Graph_isLink x y i j
  · rintro ⟨i, j⟩ u v w hl hwV hw
    have hmem : w ∈ ({x i, y j} : Set Plane) :=
      h.mem_arc_elim hwV (by rwa [h.edgeArc_eq i j] at hw)
    rcases hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hmem
    · exact hmem.symm
  · rintro ⟨i, j⟩ ⟨k, l⟩ - - hne p hp hq
    rw [h.edgeArc_eq i j] at hp
    rw [h.edgeArc_eq k l] at hq
    obtain ⟨hij, hkl⟩ := h.meet i j k l hne ⟨hp, hq⟩
    refine ⟨?_, k33Graph_inc hij, k33Graph_inc hkl⟩
    rcases hij with rfl | rfl
    exacts [Or.inl ⟨i, rfl⟩, Or.inr ⟨j, rfl⟩]

/-- The nine arcs carry a copy of `K(3,3)`, on the graph they draw. -/
theorem isK33Config (h : IsArcK33 x y P) :
    IsK33Config (k33Graph x y) x y (fun i j => (i, j)) where
  isLink := k33Graph_isLink x y
  x_injective := h.x_injective
  y_injective := h.y_injective
  ne := h.ne

/-- **`lem:k33` for nine arcs**: no nine arcs in the plane meet only where a `K(3,3)` forces
them to. This assumes the realization, exactly as `Graph.IsK33Config.not_isDrawing` does. -/
theorem false_of_realization (h : IsArcK33 x y P)
    (hreal : ∀ dr : Fin 3 × Fin 3 → ℝ → Plane, IsDrawing (k33Graph x y) dr →
      (∀ f ∈ E(k33Graph x y), IsPolygonal (edgeArc dr f)) →
      ∃ dr' : Fin 3 × Fin 3 → ℝ → Plane, IsDrawing (k33Graph x y) dr' ∧
        ∀ s : Fin 3, IsHexRealization dr' (fun i j => (i, j)) s) : False :=
  h.isK33Config.not_isDrawing hreal ⟨h.arcDrawing, h.isDrawing⟩

end IsArcK33

/-! ### From a drawn subdivision to nine arcs -/

variable {H : Graph Plane β} {W : Fin 3 → Fin 3 → List β}

/-- **A subdivision of `K(3,3)` inside a graph.** Six distinct branch vertices and nine branch
paths, the `(i, j)`-th running from `x i` to `y j`; distinct branch paths share no edge and meet
only in vertices that are branch vertices of both.

Both clauses are combinatorial: no drawing appears. That distinct branch paths meet only in
common branch vertices is the blueprint's own phrasing of what a subdivision is. -/
structure IsK33Subdivision (H : Graph Plane β) (x y : Fin 3 → Plane)
    (W : Fin 3 → Fin 3 → List β) : Prop where
  /-- The `(i, j)`-th branch path runs from `x i` to `y j`. -/
  isPath : ∀ i j, H.IsPath (x i) (W i j) (y j)
  /-- The three branch vertices of the first side are distinct. -/
  x_injective : Function.Injective x
  /-- The three branch vertices of the second side are distinct. -/
  y_injective : Function.Injective y
  /-- The two sides are disjoint. -/
  ne : ∀ i j, x i ≠ y j
  /-- Distinct branch paths share no edge. -/
  edge_ne : ∀ i j k l, (i, j) ≠ (k, l) → ∀ f ∈ W i j, f ∉ W k l
  /-- Distinct branch paths meet only in vertices that are branch vertices of both. -/
  vertex_meet : ∀ i j k l, (i, j) ≠ (k, l) → ∀ v ∈ H.walkVertices (x i) (W i j),
    v ∈ H.walkVertices (x k) (W k l) → v ∈ ({x i, y j} : Set Plane) ∩ ({x k, y l} : Set Plane)

namespace IsK33Subdivision

variable {x y : Fin 3 → Plane}

/-- A branch path has at least one edge: an empty one would identify its two ends. -/
theorem ne_nil (h : IsK33Subdivision H x y W) (i j : Fin 3) : W i j ≠ [] := by
  intro hnil
  have hp := h.isPath i j
  rw [hnil] at hp
  exact h.ne i j hp.isWalk.eq_of_nil

/-- **The branch paths of a drawn subdivision are nine arcs meeting only where they must.**
A point on two branch paths lies on an edge of each; the two edges are distinct, so a plane
drawing puts the point at a vertex incident with both, and a vertex on two branch paths is a
branch vertex of both. -/
theorem isArcK33 {drawing : β → ℝ → Plane} (hd : IsDrawing H drawing)
    (h : IsK33Subdivision H x y W) : IsArcK33 x y fun i j => edgesCover drawing (W i j) := by
  refine ⟨fun i j => hd.path_isArcBetween (h.isPath i j) (h.ne_nil i j), h.x_injective,
    h.y_injective, h.ne, ?_⟩
  rintro i j k l hne p ⟨hp1, hp2⟩
  obtain ⟨f, hf, hpf⟩ := mem_edgesCover_iff.1 hp1
  obtain ⟨g, hg, hpg⟩ := mem_edgesCover_iff.1 hp2
  have hfg : f ≠ g := fun hEq => h.edge_ne i j k l hne f hf (hEq ▸ hg)
  obtain ⟨-, hincf, hincg⟩ := hd.edge_inter ((h.isPath i j).edge_mem hf)
    ((h.isPath k l).edge_mem hg) hfg hpf hpg
  exact h.vertex_meet i j k l hne p (mem_walkVertices_of_mem_covered ⟨f, hf, hincf⟩)
    (mem_walkVertices_of_mem_covered ⟨g, hg, hincg⟩)

/-- **Corollary 3.11 (subdivisions of `K(3,3)`).** No subdivision of `K(3,3)` has a plane
drawing. This assumes the realization, exactly as `Graph.IsK33Config.not_isDrawing` does, and
the realization is needed only for the *contracted* graph `k33Graph x y`, whose nine edges are
the branch paths. -/
theorem false_of_realization {drawing : β → ℝ → Plane} (hd : IsDrawing H drawing)
    (h : IsK33Subdivision H x y W)
    (hreal : ∀ dr : Fin 3 × Fin 3 → ℝ → Plane, IsDrawing (k33Graph x y) dr →
      (∀ f ∈ E(k33Graph x y), IsPolygonal (edgeArc dr f)) →
      ∃ dr' : Fin 3 × Fin 3 → ℝ → Plane, IsDrawing (k33Graph x y) dr' ∧
        ∀ s : Fin 3, IsHexRealization dr' (fun i j => (i, j)) s) : False :=
  (h.isArcK33 hd).false_of_realization hreal

end IsK33Subdivision

end Graph

end BundlePart422
