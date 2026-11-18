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

public import verified.parts.part028
import all verified.parts.part028

@[expose] public section

set_option debug.skipKernelTC false
set_option linter.all false
set_option Elab.async false
set_option internal.cmdlineSnapshots true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

section BundlePart391
/- Source: dev/planar_search/schoenflies_port/Schoenflies/Graph/Ear.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/



/-!
# Ears

The ear decomposition: `lem:subdivision-ear-preserve` in both halves, and the step of
`lem:relative-ear` that grows a 2-connected subgraph towards the graph containing it.

## Rerouting is the engine of half (a)

`Graph.Reaches.reroute` says the obvious thing in the one form every consumer wants: if every
edge but `e` survives from `G` into `H`, and whatever `e` joins in `G` is joined in `H` by
other means, then `H` reaches whatever `G` reaches. A walk that took `e` takes the
replacement route instead, and the induction is over the walk.

Its `hends` premise is stated as "**whatever** `e` joins in `G` is joined in `H`", not as "the
two named ends are joined". That is what makes the premise dischargeable in the case where
`e` is not an edge of `G` at all: it is then vacuous. `Graph.Reaches.across_edge_replacement`
is the specialisation the subdivision runs on, and it is where the vacuous case is used — its
`routed` premise carries the three-way choice the blueprint's proof makes in prose:

* reroute along the new path — the deleted vertex is not on it, so the path survives whole;
* reroute around the old graph — the deleted vertex *is* on the path, so the old graph is
  untouched and the replaced edge was not a bridge (`Graph.IsTwoConnected.no_bridge`);
* do not reroute at all — the deleted vertex is an end of the replaced edge, so no surviving
  walk could have taken that edge.

## Half (a) is stated for a path

`Graph.IsTwoConnected.replace_edge_by_path` replaces an edge by a whole path, not by a single
new vertex. Nothing in the argument cares how long the replacement is, and the general form is
what a subdivision needs: subdividing one edge by one vertex is the case where the path has
two edges.

## Half (b) does not need the blueprint's freshness hypothesis

`Graph.IsTwoConnected.ear` attaches an ear, and the blueprint's "whose internal vertices are
new" is **not** assumed — the proof does not use it. What carries the argument is
`Graph.IsPathGraph.reaches_an_end`: whatever vertex is deleted, every remaining vertex of the
path still reaches one of the two ends. The two ends live in a 2-connected graph, at least one
of them survives the deletion, and that survivor is the hub everything routes through.

Half (a) *does* use freshness, and for a real reason: without it the deleted vertex could sit
both on the replacement path and inside the old graph, and then neither of the two routes
between the replaced edge's ends need exist.

## Finding the ear

`Graph.IsTwoConnected.ear_exists` needs neither the components of `G - V(H)` nor a shortest
path, which is what the blueprint's proof reaches for. The ear is *found*: walk out of the
subgraph to a vertex outside it, take the edge where the walk **first** leaves the subgraph
(`Graph.IsWalk.crossing`), and walk back from that edge's outer end to a *different* vertex of
the subgraph inside `G` minus the edge's inner end — a graph that is connected because `G` is
2-connected, and whose walks therefore never touch the inner end. That walk with the crossing
edge in front is a path of `G` between two vertices of the subgraph, and the crossing edge is
one the subgraph did not have.

`Graph.pathGraphOf` turns it into a graph and `Graph.IsTwoConnected.grows_by_ear` glues it on.
Termination — the blueprint's "finiteness terminates the process" — is not here; this is the
single step, and a consumer that counts edges iterates it.

## Looplessness

`Graph.IsTwoConnected.ear_exists` is the one statement here that has to assume the graph has
no loop, and the hypothesis is not bureaucracy: adding a loop to a 2-connected graph leaves it
2-connected, so a 2-connected subgraph missing only a loop grows by no ear at all, and the
conclusion — a path between *distinct* vertices — is false. It is used only in the degenerate
branch where every vertex is already present and the missing object is an edge. A plane
consumer discharges it from its drawing.

## Blueprint

* `Graph.IsTwoConnected.replace_edge_by_path` — `lem:subdivision-ear-preserve` (a), "every
  subdivision of `G` is 2-connected", stated for a replacement path of any length.
* `Graph.IsTwoConnected.ear` — `lem:subdivision-ear-preserve` (b), "if `P` is a path whose
  distinct endpoints lie in `G` … then `G ∪ P` is 2-connected".
* `Graph.IsTwoConnected.ear_exists`, `Graph.IsTwoConnected.grows_by_ear` — the step of
  `lem:relative-ear`, "`G` is obtained from `H` by repeatedly adding paths whose distinct
  endpoints are already present".
* `Graph.Reaches.reroute`, `Graph.Reaches.across_edge_replacement` — the blueprint's "the
  remaining part of the subdivided edge attaches `w` to `u` or `v`" together with "a
  2-connected graph has no bridge", turned into one transfer lemma.
-/

open Set
open scoped Graph

namespace Graph

variable {α β : Type*} {G H K P : Graph α β} {a b c s t u v x y z : α} {e f : β}
  {W D : List β}

/-! ### The union of two subgraphs

`Graph.union` and the two inclusions *into* it live in `Schoenflies/Graph/TwoConnected.lean`;
this is the inclusion *out of* it, which the ear construction needs in order to know that the
enlarged subgraph is still a subgraph. It is general and belongs beside the other two — the
integrator should hoist it. -/

/-! ### Rerouting one edge -/

/-- **One edge swapped for any route between its ends.** If every edge of `G` other than `e`
links the same pair in `H`, and whatever `e` links in `G` is joined in `H` by some other
means, then `H` reaches whatever `G` reaches: a walk that took `e` takes the replacement route
instead.

The premise about `e` is universally quantified over its ends rather than stated for a named
pair, so that it is *vacuous* when `e` is not an edge of `G` — which is the case a vertex
deletion produces, and the reason this is the shape that gets used. -/
theorem Reaches.reroute (hV : V(G) ⊆ V(H))
    (hE : ∀ ⦃g p q⦄, G.IsLink g p q → g ≠ e → H.IsLink g p q)
    (hends : ∀ ⦃p q⦄, G.IsLink e p q → H.Reaches p q)
    (h : G.Reaches s t) : H.Reaches s t := by
  obtain ⟨R, hR⟩ := h
  induction hR with
  | nil hx => exact Reaches.refl (hV hx)
  | @cons p w q g R hl _ ih =>
    -- Either this step took the replaced edge, or it survives verbatim.
    refine Reaches.trans ?_ ih
    by_cases hg : g = e
    · exact hends (hg ▸ hl)
    · exact Reaches.of_isLink (hE hl hg)

/-- **The form a subdivision needs.** A walk of `G - c` transfers to any graph holding the
surviving edges, provided the replaced edge's ends are joined there *or* that edge was
incident to the deleted vertex — in which case no walk of `G - c` could have taken it, and the
`hends` premise of `Graph.Reaches.reroute` is vacuous.

That disjunction is the blueprint's three-way case analysis: route along the replacement,
route around the old graph, or do not route at all. -/
theorem Reaches.across_edge_replacement (hV : V(G.deleteVerts {c}) ⊆ V(H))
    (hl : G.IsLink e u v)
    (hE : ∀ ⦃g p q⦄, (G.deleteVerts {c}).IsLink g p q → g ≠ e → H.IsLink g p q)
    (routed : H.Reaches u v ∨ G.Inc e c)
    (h : (G.deleteVerts {c}).Reaches s t) : H.Reaches s t := by
  refine Reaches.reroute (e := e) hV hE (fun p q hpq ↦ ?_) h
  rw [deleteVerts_isLink] at hpq
  obtain ⟨hpq, hp, hq⟩ := hpq
  have hpc : p ≠ c := fun hh ↦ hp (by simp [hh])
  have hqc : q ≠ c := fun hh ↦ hq (by simp [hh])
  rcases routed with hr | ⟨w, hw⟩
  · -- The ends are joined in `H`; the step ran between them, one way or the other.
    rcases hl.eq_and_eq_or_eq_and_eq hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    exacts [hr, hr.symm]
  · -- The edge met the deleted vertex, so `G - c` does not have it: nothing to prove.
    rcases hw.left_eq_or_eq hpq with hh | hh
    exacts [(hpc hh.symm).elim, (hqc hh.symm).elim]

/-! ### Attaching an ear -/

/-- **`lem:subdivision-ear-preserve` (b): attaching an ear preserves 2-connectivity.** `P` is
a path whose two distinct ends lie in the 2-connected graph `G`; then `G ∪ P` is 2-connected.

The blueprint's hypothesis that the ear's internal vertices are new is **not** needed. Delete
a vertex `c`. One of the ear's two ends survives, and it is the hub: `G - c` is connected and
contains it, and every surviving vertex of the ear reaches one of the two ends inside the ear
(`Graph.IsPathGraph.reaches_an_end`) — an end which, having been reached after the deletion, is
itself not `c`, so it lies in `G - c` too. -/
theorem IsTwoConnected.ear (hG : G.IsTwoConnected) (hcompat : G.Compatible P)
    (hP : P.IsPathGraph u W v) (huv : u ≠ v) (hu : u ∈ V(G)) (hv : v ∈ V(G)) :
    (G.union P).IsTwoConnected where
  hasThreeVertices := hG.hasThreeVertices.mono (left_le_union G P).vertexSet_mono
  connected := hcompat.union_connected hG.connected hP.connected hu hP.source_mem
  deleteVerts_connected := by
    intro c _
    -- One of the ear's two ends survives the deletion; it is the hub.
    obtain ⟨z, hzG, hzc⟩ : ∃ z, z ∈ V(G) ∧ z ≠ c := by
      by_cases hcu : u = c
      · exact ⟨v, hv, fun hh ↦ huv (hcu.trans hh.symm)⟩
      · exact ⟨u, hu, hcu⟩
    have hGle : G.deleteVerts {c} ≤ (G.union P).deleteVerts {c} :=
      deleteVerts_mono (left_le_union G P) _
    have hPle : P.deleteVerts {c} ≤ (G.union P).deleteVerts {c} :=
      deleteVerts_mono hcompat.right_le_union _
    have hGc : (G.deleteVerts {c}).Connected := hG.deleteVerts_connected' c
    -- Every surviving vertex of the graph side reaches the hub inside the graph side.
    have key : ∀ x ∈ V(G), x ≠ c → ((G.union P).deleteVerts {c}).Reaches z x := fun x hx hxc ↦
      (hGc.reaches (mem_deleteVerts_singleton_of_ne hzG hzc)
        (mem_deleteVerts_singleton_of_ne hx hxc)).mono hGle
    refine Connected.of_hub (mem_deleteVerts_singleton_of_ne
      ((left_le_union G P).vertexSet_mono hzG) hzc) fun x hx ↦ ?_
    rw [vertexSet_deleteVerts] at hx
    obtain ⟨hxS, hxc⟩ := hx
    have hxc' : x ≠ c := by simpa using hxc
    rcases (hxS : x ∈ V(G) ∪ V(P)) with hxG | hxP
    · exact key x hxG hxc'
    · -- On the ear, one of the two ends is still reachable, and it survived the deletion.
      rcases hP.reaches_an_end hxP hxc' with hr | hr
      · have hune : u ≠ c := by
          have h₂ := hr.right_mem
          rw [vertexSet_deleteVerts] at h₂
          simpa using h₂.2
        exact (key u hu hune).trans (hr.mono hPle).symm
      · have hvne : v ≠ c := by
          have h₂ := hr.right_mem
          rw [vertexSet_deleteVerts] at h₂
          simpa using h₂.2
        exact (key v hv hvne).trans (hr.mono hPle).symm

/-! ### Replacing an edge by a path -/

/-- **`lem:subdivision-ear-preserve` (a): a subdivision of a 2-connected graph is
2-connected.** Stated for a replacement *path* rather than for a single new vertex, because
nothing in the argument cares how long the replacement is; subdividing one edge by one vertex
is the case where `P` has two edges.

Delete a vertex `c`. One end of the replaced edge survives and is the hub. Everything on the
old side reaches it by `Graph.Reaches.across_edge_replacement`, whose `routed` premise is
discharged by the three-way case analysis: if `c` is an end of the replaced edge there is
nothing to route; if `c` is an old vertex then it is not on the path — this is where the
freshness hypothesis `hnew` is used — and the path itself joins the ends; and if `c` is new
then the old graph is untouched and has no bridge. Everything on the path side reaches an end
of the path, and an end reached after the deletion survived it. -/
theorem IsTwoConnected.replace_edge_by_path (hG : G.IsTwoConnected) (hl : G.IsLink e u v)
    (huv : u ≠ v) (hcompat : (G.deleteEdges {e}).Compatible P) (hP : P.IsPathGraph u W v)
    (hnew : ∀ x ∈ V(P), x ≠ u → x ≠ v → x ∉ V(G)) :
    ((G.deleteEdges {e}).union P).IsTwoConnected := by
  set T := G.deleteEdges {e} with hT
  set S := T.union P with hS
  have hTS : T ≤ S := left_le_union T P
  have hPS : P ≤ S := hcompat.right_le_union
  have hVT : V(T) = V(G) := by rw [hT]; simp
  have hu : u ∈ V(G) := hl.left_mem
  have hv : v ∈ V(G) := hl.right_mem
  -- Every old edge but the replaced one links the same pair in the new graph.
  have hGS : ∀ ⦃g p q⦄, G.IsLink g p q → g ≠ e → S.IsLink g p q := by
    intro g p q hg hge
    refine hTS.isLink_mono (show T.IsLink g p q from ?_)
    rw [hT]
    exact ⟨hg, by simpa using hge⟩
  have hVGS : V(G) ⊆ V(S) := by
    rw [hS, vertexSet_union, hVT]
    exact Set.subset_union_left
  -- The replacement route.
  have hPuv : P.Reaches u v := hP.connected.reaches hP.source_mem hP.target_mem
  refine ⟨hG.hasThreeVertices.mono hVGS, ?_, ?_⟩
  · refine Connected.of_hub (hVGS hu) fun x hx ↦ ?_
    rcases (hx : x ∈ V(T) ∪ V(P)) with hxT | hxP
    · refine Reaches.reroute (e := e) hVGS hGS ?_
        (hG.connected.reaches hu (by rwa [hVT] at hxT))
      intro p q hpq
      rcases hl.eq_and_eq_or_eq_and_eq hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      exacts [hPuv.mono hPS, (hPuv.mono hPS).symm]
    · exact (hP.connected.reaches hP.source_mem hxP).mono hPS
  intro c _
  -- One end of the replaced edge survives; it is the hub.
  obtain ⟨z, hzG, hzc⟩ : ∃ z, z ∈ V(G) ∧ z ≠ c := by
    by_cases hcu : u = c
    · exact ⟨v, hv, fun hh ↦ huv (hcu.trans hh.symm)⟩
    · exact ⟨u, hu, hcu⟩
  have hTle : T.deleteVerts {c} ≤ S.deleteVerts {c} := deleteVerts_mono hTS _
  have hPle : P.deleteVerts {c} ≤ S.deleteVerts {c} := deleteVerts_mono hPS _
  have hGc : (G.deleteVerts {c}).Connected := hG.deleteVerts_connected' c
  -- The replaced edge's ends are still joined, unless the deleted vertex is one of them.
  have routed : (S.deleteVerts {c}).Reaches u v ∨ G.Inc e c := by
    by_cases hcu : c = u
    · exact Or.inr (hcu ▸ hl.inc_left)
    by_cases hcv : c = v
    · exact Or.inr (hcv ▸ hl.inc_right)
    by_cases hcG : c ∈ V(G)
    · -- An old vertex and not an end: the path is untouched, and it joins the ends.
      have hcP : c ∉ V(P) := fun hh ↦ hnew c hh hcu hcv hcG
      have hreach : (P.deleteVerts {c}).Reaches u v := by
        rw [deleteVerts_singleton_eq_self hcP]; exact hPuv
      exact Or.inl (hreach.mono hPle)
    · -- A new vertex: the old graph is untouched, and it has no bridge.
      have hcT : c ∉ V(T) := by rw [hVT]; exact hcG
      have hreach : (T.deleteVerts {c}).Reaches u v := by
        rw [deleteVerts_singleton_eq_self hcT, hT]
        exact hG.no_bridge hl
      exact Or.inl (hreach.mono hTle)
  -- Every surviving old vertex reaches the hub.
  have key : ∀ x ∈ V(G), x ≠ c → (S.deleteVerts {c}).Reaches x z := by
    intro x hx hxc
    refine Reaches.across_edge_replacement (e := e) ?_ hl ?_ routed
      (hGc.reaches (mem_deleteVerts_singleton_of_ne hx hxc)
        (mem_deleteVerts_singleton_of_ne hzG hzc))
    · rw [vertexSet_deleteVerts, vertexSet_deleteVerts]
      exact Set.sdiff_subset_sdiff_left hVGS
    · intro g p q hg hge
      rw [deleteVerts_isLink] at hg ⊢
      exact ⟨hGS hg.1 hge, hg.2.1, hg.2.2⟩
  refine Connected.of_hub (mem_deleteVerts_singleton_of_ne (hVGS hzG) hzc) fun x hx ↦ ?_
  rw [vertexSet_deleteVerts] at hx
  obtain ⟨hxS, hxc⟩ := hx
  have hxc' : x ≠ c := by simpa using hxc
  rcases (hxS : x ∈ V(T) ∪ V(P)) with hxT | hxP
  · exact (key x (by rwa [hVT] at hxT) hxc').symm
  · rcases hP.reaches_an_end hxP hxc' with hr | hr
    · have hune : u ≠ c := by
        have h₂ := hr.right_mem
        rw [vertexSet_deleteVerts] at h₂
        simpa using h₂.2
      exact (key u hu hune).symm.trans (hr.mono hPle).symm
    · have hvne : v ≠ c := by
        have h₂ := hr.right_mem
        rw [vertexSet_deleteVerts] at h₂
        simpa using h₂.2
      exact (key v hv hvne).symm.trans (hr.mono hPle).symm

/-! ### Finding an ear -/

/-- **A 2-connected subgraph that is not all of a 2-connected graph has an ear.** The ear is
found, not chosen: if the subgraph already has every vertex then a missing edge joins two of
them and is an ear by itself; otherwise a walk out of the subgraph crosses its boundary, and
deleting the crossing edge's inner end leaves `G` connected, so the outer end walks back to a
*different* vertex of the subgraph without passing through the first.

The looplessness hypothesis is used only in the first, degenerate branch, and it cannot be
dropped: a 2-connected graph plus a loop is 2-connected, and no ear is missing from it. -/
theorem IsTwoConnected.ear_exists (hG : G.IsTwoConnected) (hK : K.IsTwoConnected) (hKG : K ≤ G)
    (hnl : ∀ ⦃g x⦄, ¬ G.IsLoopAt g x)
    (hproper : (∃ x ∈ V(G), x ∉ V(K)) ∨ (∃ g ∈ E(G), g ∉ E(K))) :
    ∃ a b D g, G.IsPath a D b ∧ a ≠ b ∧ a ∈ V(K) ∧ b ∈ V(K) ∧ g ∈ D ∧ g ∉ E(K) := by
  by_cases hout : ∃ x ∈ V(G), x ∉ V(K)
  · obtain ⟨o, hoG, hoK⟩ := hout
    -- Walk from the subgraph out to `o`; it crosses the boundary along one of its own edges.
    obtain ⟨anchor, hanchor⟩ := hK.connected.nonempty
    obtain ⟨R, hR⟩ := hG.connected.reaches (hKG.vertexSet_mono hanchor) hoG
    obtain ⟨g, hgR, p, q, hlpq, hpK, hqK⟩ := hR.crossing hanchor hoK
    have hpq : p ≠ q := fun hh ↦ hqK (hh ▸ hpK)
    -- The subgraph has a second vertex to come back to.
    obtain ⟨b, hbK, hbp, -⟩ := hK.hasThreeVertices.exists_ne_ne p p
    have hqG : q ∈ V(G) := hlpq.right_mem
    have hbG : b ∈ V(G) := hKG.vertexSet_mono hbK
    -- Deleting the inner end leaves `G` connected, so the outer end walks back to `b`.
    obtain ⟨D, hD⟩ := ((hG.deleteVerts_connected' p).reaches
      (mem_deleteVerts_singleton_of_ne hqG (Ne.symm hpq))
      (mem_deleteVerts_singleton_of_ne hbG hbp)).exists_isPath
    have hfresh : p ∉ G.walkVertices q D := by
      rintro hmem
      rcases mem_walkVertices_iff.1 hmem with rfl | ⟨g', hg', hinc⟩
      · exact hpq rfl
      · exact hD.isWalk.notMem_of_inc_of_deleteVerts hinc hg'
    refine ⟨p, b, g :: D, g, .cons hlpq (hD.mono deleteVerts_le) hfresh, Ne.symm hbp, hpK,
      hbK, List.mem_cons_self, fun hgK ↦ ?_⟩
    -- The crossing edge is not the subgraph's: its outer end would then be a vertex of it.
    exact hqK ((hKG.isLink_iff hgK).2 hlpq).right_mem
  · -- Every vertex is already there, so a missing edge is an ear of length one.
    push Not at hout
    obtain ⟨g, hgG, hgK⟩ := hproper.resolve_left (by rintro ⟨x, hx, hx'⟩; exact hx' (hout x hx))
    obtain ⟨p, q, hpq⟩ := exists_isLink_of_mem_edgeSet hgG
    have hne : p ≠ q := by rintro rfl; exact hnl hpq
    exact ⟨p, q, [g], g, .single hpq hne, hne, hout p hpq.left_mem, hout q hpq.right_mem,
      List.mem_cons_self, hgK⟩

/-- **H5: a 2-connected subgraph of a 2-connected graph grows to it by adding ears.** One
step: the subgraph gains an ear and at least one edge, and is still a 2-connected subgraph of
the big graph. Iterating on the number of missing edges is the caller's business — the
blueprint's "finiteness terminates the process". -/
theorem IsTwoConnected.grows_by_ear (hG : G.IsTwoConnected) (hK : K.IsTwoConnected)
    (hKG : K ≤ G) (hnl : ∀ ⦃g x⦄, ¬ G.IsLoopAt g x)
    (hproper : (∃ x ∈ V(G), x ∉ V(K)) ∨ (∃ g ∈ E(G), g ∉ E(K))) :
    ∃ B : Graph α β, B.IsTwoConnected ∧ K ≤ B ∧ B ≤ G ∧ ∃ g ∈ E(B), g ∉ E(K) := by
  obtain ⟨a, b, D, g, hpath, hab, haK, hbK, hgD, hgK⟩ := hG.ear_exists hK hKG hnl hproper
  -- The path, presented as a graph, is the ear.
  have hearle : G.pathGraphOf a D ≤ G := pathGraphOf_le hpath.isWalk
  have hearP : (G.pathGraphOf a D).IsPathGraph a D b := hpath.isPathGraph_pathGraphOf
  exact ⟨K.union (G.pathGraphOf a D),
    hK.ear (Compatible.of_le_le hKG hearle) hearP hab haK hbK,
    left_le_union _ _, union_le hKG hearle, g,
    Set.mem_union_right _ (hearP.mem_edgeSet hgD), hgK⟩

end Graph

end BundlePart391

section BundlePart392
/- Source: dev/planar_search/schoenflies_port/Schoenflies/Graph/Tree.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/



/-!
# Trees

A tree is a connected graph in which no edge lies on a cycle. What the blueprint asks of a
tree is always about its leaves, and every such question starts the same way: **take a longest
path**. Neither of its ends can carry a second edge — an edge back onto the path would close a
cycle, and an edge off the path would make a longer path — so both ends are leaves.

## The three theorems this file exists for

* deleting a leaf leaves a tree (`Graph.IsTree.delete_leaf`),
* a tree on `n` vertices has `n - 1` edges (`Graph.IsTree.edge_count`), by peeling leaves,
* **a tree with exactly three leaves has one vertex of degree three**
  (`Graph.IsTree.three_leaves`), which is where the handshake lemma finally pays.

## Why a longest path rather than a maximal one

A longest path is produced by `Nat.findGreatest` over the lengths of paths, bounded because a
path repeats no edge (`Graph.IsPath.nodup`) and the graph has finitely many. That needs
`Graph.Finite` and nothing else — in particular no well-founded recursion and no choice of a
maximal element in an order. The bound is the only place finiteness enters the longest-path
argument.

## Vertex deletion

`Graph.deleteVerts` is Mathlib's. What this file adds is the transfer lemma every deletion
argument reduces to — `Graph.IsWalk.deleteVerts`, a walk that never visits a deleted vertex
survives — together with the reason the hypothesis is ever available:
`Graph.IsLeaf.path_avoids`, a path whose two ends are elsewhere never visits a vertex of
degree one. To pass through such a vertex a path would have to arrive and leave along its
single edge, and a path takes no edge twice.

## Blueprint

* `Graph.IsTree.three_leaves` — `lem:three-leaf-tree` ("a finite tree with exactly three
  leaves has exactly one vertex of degree at least three; that vertex has degree exactly
  three, and every other vertex is a leaf or has degree two"), used at the H5 step of
  `lem:two-components` to produce the three internally disjoint branches of each spanning
  tree `T_i`.
* `Graph.IsTree.edge_count` — the same lemma's "a finite tree with `n` vertices has exactly
  `n - 1` edges".
* `Graph.IsTree.has_leaf`, `Graph.IsTree.delete_leaf` — its "a tree with an edge has a leaf,
  since an endpoint of a maximal simple path has no neighbor off the path, and a second
  neighbor on the path would close a cycle; deleting a leaf and its edge leaves a tree".
* `Graph.IsTree` — the trees of `lem:two-components` ("take a minimal connected subgraph
  `T_i` spanning the three terminals. It is a tree").

## Namespace

The root `Graph` namespace, as in `Walk.lean`, `Degree.lean` and `Cycle.lean`.
-/

open Set
open scoped Graph

variable {α β : Type*} {G H : Graph α β} {u v w x y : α} {e f : β} {P W : List β}

namespace Graph

/-! ### Trees -/

/-- `G.IsTree` : a connected graph in which no edge lies on a cycle. Connectedness carries
nonemptiness (`Graph.Connected`), which is what makes the counting statements below true as
stated. -/
def IsTree (G : Graph α β) : Prop := G.Connected ∧ G.IsAcyclic

theorem IsTree.connected (h : G.IsTree) : G.Connected := h.1

theorem IsTree.isAcyclic (h : G.IsTree) : G.IsAcyclic := h.2

theorem isTree_iff : G.IsTree ↔ G.Connected ∧ G.IsAcyclic := Iff.rfl

/-! ### A walk departs along an edge -/

/-- A walk that gets anywhere leaves along an edge at its source. -/
theorem IsWalk.exists_inc_source (h : G.IsWalk u W v) (hW : W ≠ []) : ∃ e ∈ W, G.Inc e u := by
  cases h with
  | nil => exact absurd rfl hW
  | cons hl _ => exact ⟨_, List.mem_cons_self, hl.inc_left⟩

/-- A path between two distinct vertices takes at least one edge. -/
theorem IsPath.ne_nil (h : G.IsPath u P v) (huv : u ≠ v) : P ≠ [] := by
  rintro rfl
  exact huv h.isWalk.eq_of_nil

/-- **In a connected graph on two or more vertices nothing is isolated.** -/
theorem Connected.degree_pos [G.Finite] (hG : G.Connected) (h2 : 2 ≤ V(G).ncard)
    (hx : x ∈ V(G)) : 0 < G.degree x := by
  obtain ⟨b, hb, hbx⟩ := Set.exists_ne_of_one_lt_ncard (s := V(G)) (by omega) x
  obtain ⟨R, hR⟩ := hG.exists_isPath hx hb
  obtain ⟨e, -, hinc⟩ := hR.isWalk.exists_inc_source (hR.ne_nil (Ne.symm hbx))
  exact degree_pos_of_inc hinc

/-! ### A path leaves its source once and for all

Two edges of a path incident with its source are the same edge: the departing step is the
only candidate, since a later edge at the source would put the source back among the vertices
the rest of the path visits. -/

/-- An edge of a path incident with the path's source is the one the path departs along. -/
theorem IsPath.eq_head_of_inc_source (h : G.IsPath u (e :: W) v) (hf : f ∈ e :: W)
    (hinc : G.Inc f u) : f = e := by
  cases h with
  | cons hl hW hfresh =>
    rcases List.mem_cons.1 hf with rfl | hf
    · rfl
    · exact absurd (mem_walkVertices_of_mem_covered ⟨f, hf, hinc⟩) hfresh

/-- **A path has at most one edge at its source.** -/
theorem IsPath.inc_source_unique (h : G.IsPath u P v) (hf : f ∈ P) (he : e ∈ P)
    (hfi : G.Inc f u) (hei : G.Inc e u) : f = e := by
  cases P with
  | nil => simp at hf
  | cons a t => rw [h.eq_head_of_inc_source hf hfi, h.eq_head_of_inc_source he hei]

/-! ### A longest path -/

/-- A path repeats no edge, so it is no longer than the graph has edges. -/
theorem IsPath.length_le_ncard_edgeSet [G.Finite] (h : G.IsPath u P v) :
    P.length ≤ E(G).ncard := by
  classical
  have hsub : P.toFinset ⊆ G.edgeFinset := fun f hf ↦
    mem_edgeFinset.2 (h.edge_mem (List.mem_toFinset.1 hf))
  calc P.length = P.toFinset.card := (List.toFinset_card_of_nodup h.nodup).symm
    _ ≤ G.edgeFinset.card := Finset.card_le_card hsub
    _ = E(G).ncard := card_edgeFinset

/-- **A finite graph with a vertex has a longest path.** The lengths of paths are bounded by
the number of edges, so `Nat.findGreatest` picks the largest length that occurs, and the
witnessing path is longest. -/
theorem exists_longest_path [G.Finite] (hu : u ∈ V(G)) :
    ∃ x y Q, G.IsPath x Q y ∧ ∀ x' y' (Q' : List β), G.IsPath x' Q' y' → Q'.length ≤ Q.length := by
  classical
  -- `p n` : some path has length exactly `n`.
  set p : ℕ → Prop :=
    fun n ↦ ∃ (x : α) (y : α) (Q : List β), G.IsPath x Q y ∧ Q.length = n with hp
  have hp0 : p 0 := ⟨u, u, [], .nil hu, rfl⟩
  obtain ⟨x, y, Q, hQ, hQlen⟩ := Nat.findGreatest_spec (P := p) (Nat.zero_le E(G).ncard) hp0
  refine ⟨x, y, Q, hQ, fun x' y' Q' hQ' ↦ ?_⟩
  have hle := Nat.le_findGreatest (P := p) hQ'.length_le_ncard_edgeSet ⟨x', y', Q', hQ', rfl⟩
  omega

/-! ### Both ends of a longest path are leaves -/

/-- **Every edge at the source of a longest path is one of the path's own edges.** The two
ways out are both closed: an edge onto a vertex the path visits closes a cycle
(`Graph.IsAcyclic.mem_of_isLink_of_mem_walkVertices`), and an edge to a vertex it does not
visit extends the path. -/
theorem IsAcyclic.longest_path_source_edge (hac : G.IsAcyclic) (hP : G.IsPath u P v)
    (hlong : ∀ x' y' (Q : List β), G.IsPath x' Q y' → Q.length ≤ P.length)
    (hinc : G.Inc e u) : e ∈ P := by
  obtain ⟨z, hl⟩ := hinc
  by_cases hz : z ∈ G.walkVertices u P
  · exact hac.mem_of_isLink_of_mem_walkVertices hP hl hz
  · have hlt := hlong z v (e :: P) (.cons hl.symm hP hz)
    rw [List.length_cons] at hlt
    omega

/-- **The source of a longest path in an acyclic graph is a leaf**, as soon as it carries an
edge at all: every edge there is one of the path's, and the path leaves the vertex only once,
so they are all the same edge. -/
theorem IsAcyclic.longest_path_source_is_leaf [G.Finite] (hac : G.IsAcyclic)
    (hP : G.IsPath u P v)
    (hlong : ∀ x' y' (Q : List β), G.IsPath x' Q y' → Q.length ≤ P.length)
    (hinc : G.Inc e u) : G.IsLeaf u := by
  refine isLeaf_of_isNonloopAt hinc.vertex_mem (fun g ↦ ⟨fun hg ↦ ?_, fun hg ↦ hg ▸ hinc⟩)
    (hinc.isLoopAt_or_isNonloopAt.resolve_left (hac.not_isLoopAt e u))
  exact hP.inc_source_unique (hac.longest_path_source_edge hP hlong hg)
    (hac.longest_path_source_edge hP hlong hinc) hg hinc

/-- **The target of a longest path in an acyclic graph is a leaf** too: reversing a path
preserves its length, so the reverse is longest as well. -/
theorem IsAcyclic.longest_path_target_is_leaf [G.Finite] (hac : G.IsAcyclic)
    (hP : G.IsPath u P v)
    (hlong : ∀ x' y' (Q : List β), G.IsPath x' Q y' → Q.length ≤ P.length)
    (hinc : G.Inc e v) : G.IsLeaf v := by
  refine hac.longest_path_source_is_leaf hP.reverse (fun x' y' Q hQ ↦ ?_) hinc
  rw [List.length_reverse]
  exact hlong x' y' Q hQ

/-- **A tree on two or more vertices has a leaf.** Two distinct vertices are joined by a path
that takes an edge, so a longest path takes one too, and its source is a leaf. -/
theorem IsTree.has_leaf [G.Finite] (hT : G.IsTree) (h2 : 2 ≤ V(G).ncard) :
    ∃ x, G.IsLeaf x := by
  obtain ⟨a, ha⟩ := hT.connected.nonempty
  obtain ⟨b, hb, hba⟩ := Set.exists_ne_of_one_lt_ncard (s := V(G)) (by omega) a
  obtain ⟨x, y, Q, hQ, hlong⟩ := exists_longest_path ha
  -- Some path is nonempty, so the longest one is.
  obtain ⟨R, hR⟩ := hT.connected.exists_isPath ha hb
  have hRpos : 1 ≤ R.length := List.length_pos_iff.2 (hR.ne_nil (Ne.symm hba))
  have hQne : Q ≠ [] := by
    intro hQnil
    have hle := hlong a b R hR
    rw [hQnil, List.length_nil] at hle
    omega
  obtain ⟨e, -, hinc⟩ := hQ.isWalk.exists_inc_source hQne
  exact ⟨x, hT.isAcyclic.longest_path_source_is_leaf hQ hlong hinc⟩

/-! ### A path steers clear of a leaf -/

/-- **A path whose two ends are elsewhere never visits a vertex of degree one.** To pass
through such a vertex the path would have to arrive and leave along that vertex's single
edge, and a path takes no edge twice. This is what makes connectivity survive the deletion of
a leaf. -/
theorem IsLeaf.path_avoids [G.Finite] (hx : G.IsLeaf x) (hP : G.IsPath u P v) :
    u ≠ x → v ≠ x → x ∉ G.walkVertices u P := by
  induction hP with
  | nil hy =>
    intro hu _ hmem
    rw [walkVertices_nil] at hmem
    exact hu hmem.symm
  | @cons a w b e W hl hW hfresh ih =>
    intro ha hb hmem
    rcases mem_walkVertices_cons hl hmem with rfl | hmem'
    · exact ha rfl
    by_cases hwx : w = x
    · -- The step arrives at the leaf, so the rest has to leave it — along the leaf's one
      -- edge, which the step has already used.
      subst hwx
      have hWne : W ≠ [] := hW.ne_nil (Ne.symm hb)
      obtain ⟨g, hg, hginc⟩ := hW.isWalk.exists_inc_source hWne
      obtain ⟨e', -, huniq⟩ := hx.existsUnique_inc
      have hge : g = e := (huniq g hginc).trans (huniq e hl.inc_right).symm
      exact hfresh (mem_walkVertices_of_mem_covered ⟨e, hge ▸ hg, hl.inc_left⟩)
    · exact ih hwx hb hmem'

/-! ### Vertex deletion -/

/-- **A walk that visits no deleted vertex survives the deletion.** Both ends of each of its
edges are vertices it visits, so they too survive. -/
theorem IsWalk.deleteVerts {X : Set α} (h : G.IsWalk u W v)
    (hX : ∀ z ∈ G.walkVertices u W, z ∉ X) : (G.deleteVerts X).IsWalk u W v := by
  refine h.anti deleteVerts_le ?_ fun g hg ↦ ?_
  · rw [vertexSet_deleteVerts]
    exact ⟨h.left_mem, hX u mem_walkVertices_self⟩
  · obtain ⟨p, q, hpq⟩ := exists_isLink_of_mem_edgeSet (h.edge_mem hg)
    simp only [edgeSet_deleteVerts, Set.mem_setOf_eq]
    exact ⟨p, q, hpq, hX p (mem_walkVertices_of_mem_covered ⟨g, hg, hpq.inc_left⟩),
      hX q (mem_walkVertices_of_mem_covered ⟨g, hg, hpq.inc_right⟩)⟩

/-- Deleting a vertex removes exactly the edges that meet it. -/
theorem edgeSet_deleteVerts_singleton (G : Graph α β) (x : α) :
    E(G.deleteVerts {x}) = E(G) \ G.incidenceSet x := by
  ext g
  simp only [edgeSet_deleteVerts, Set.mem_setOf_eq, Set.mem_sdiff, mem_incidenceSet,
    Set.mem_singleton_iff]
  refine ⟨fun ⟨p, q, hpq, hp, hq⟩ ↦ ⟨hpq.edge_mem, fun hinc ↦ ?_⟩, fun ⟨hg, hninc⟩ ↦ ?_⟩
  · rcases hinc.eq_or_eq_of_isLink hpq with rfl | rfl
    exacts [hp rfl, hq rfl]
  · obtain ⟨p, q, hpq⟩ := exists_isLink_of_mem_edgeSet hg
    exact ⟨p, q, hpq, fun h ↦ hninc (h ▸ hpq.inc_left), fun h ↦ hninc (h ▸ hpq.inc_right)⟩

/-- **A tree minus a leaf is a tree.** Acyclicity is inherited by every subgraph;
connectedness survives because every path between two surviving vertices already steered
clear of the leaf (`Graph.IsLeaf.path_avoids`). -/
theorem IsTree.delete_leaf [G.Finite] (hT : G.IsTree) (hx : G.IsLeaf x) (h2 : 2 ≤ V(G).ncard) :
    (G.deleteVerts {x}).IsTree := by
  refine ⟨⟨?_, fun a ha b hb ↦ ?_⟩, hT.isAcyclic.anti deleteVerts_le⟩
  · obtain ⟨c, hc, hcx⟩ := Set.exists_ne_of_one_lt_ncard (s := V(G)) (by omega) x
    exact ⟨c, by rw [vertexSet_deleteVerts]; exact ⟨hc, by simpa using hcx⟩⟩
  · rw [vertexSet_deleteVerts] at ha hb
    obtain ⟨R, hR⟩ := hT.connected.exists_isPath ha.1 hb.1
    have havoid := hx.path_avoids hR (by simpa using ha.2) (by simpa using hb.2)
    exact ⟨R, hR.isWalk.deleteVerts fun z hz hzX ↦ havoid (Set.mem_singleton_iff.1 hzX ▸ hz)⟩

/-! ### A tree has one edge fewer than it has vertices -/

/-- The induction behind `Graph.IsTree.edge_count`, with a bound on the number of vertices to
walk down: peel a leaf and recurse on what is left, which is a tree with one vertex and one
edge fewer. -/
private theorem isTree_edge_count_aux :
    ∀ (n : ℕ) (G : Graph α β), G.Finite → V(G).ncard ≤ n → G.IsTree →
      E(G).ncard + 1 = V(G).ncard := by
  intro n
  induction n with
  | zero =>
    intro G hfin hle hT
    haveI := hfin
    obtain ⟨a, ha⟩ := hT.connected.nonempty
    have := (Set.ncard_pos (finite_vertexSet G)).2 ⟨a, ha⟩
    omega
  | succ n ih =>
    intro G hfin hle hT
    haveI := hfin
    by_cases h2 : 2 ≤ V(G).ncard
    · obtain ⟨x, hx⟩ := hT.has_leaf h2
      haveI : (G.deleteVerts {x}).Finite := Finite.of_le deleteVerts_le
      have hT' : (G.deleteVerts {x}).IsTree := hT.delete_leaf hx h2
      have hV : V(G.deleteVerts {x}).ncard = V(G).ncard - 1 := by
        rw [vertexSet_deleteVerts, Set.ncard_sdiff_singleton_of_mem hx.mem_vertexSet]
      -- A leaf sits on exactly one edge, and that edge is what the deletion removes.
      obtain ⟨e₀, he₀⟩ := Set.ncard_eq_one.1 hx.ncard_incidenceSet
      have he₀G : e₀ ∈ E(G) :=
        G.incidenceSet_subset_edgeSet x (he₀ ▸ Set.mem_singleton e₀)
      have hE : E(G.deleteVerts {x}).ncard = E(G).ncard - 1 := by
        rw [edgeSet_deleteVerts_singleton, he₀, Set.ncard_sdiff_singleton_of_mem he₀G]
      have hEpos := (Set.ncard_pos (finite_edgeSet G)).2 ⟨e₀, he₀G⟩
      have := ih _ inferInstance (by omega) hT'
      omega
    · -- A single vertex, and no edge: an edge would be a loop, and no acyclic graph has one.
      obtain ⟨a, ha⟩ := hT.connected.nonempty
      have hpos := (Set.ncard_pos (finite_vertexSet G)).2 ⟨a, ha⟩
      have hV1 : V(G).ncard = 1 := by omega
      obtain ⟨c, hVc⟩ := Set.ncard_eq_one.1 hV1
      have hE : E(G).ncard = 0 := by
        refine (Set.ncard_eq_zero (finite_edgeSet G)).2 (Set.eq_empty_iff_forall_notMem.2 ?_)
        intro g hg
        obtain ⟨p, q, hpq⟩ := exists_isLink_of_mem_edgeSet hg
        have hp : p = c := by have := hpq.left_mem; rw [hVc] at this; exact this
        have hq : q = c := by have := hpq.right_mem; rw [hVc] at this; exact this
        rw [hp, hq] at hpq
        exact hT.isAcyclic.not_isLoopAt g c hpq
      omega

/-- **A tree has one edge fewer than it has vertices.** -/
theorem IsTree.edge_count [G.Finite] (hT : G.IsTree) : E(G).ncard + 1 = V(G).ncard :=
  isTree_edge_count_aux V(G).ncard G inferInstance le_rfl hT

/-! ### A tree with three leaves

The blueprint's `lem:three-leaf-tree`, and the one place the handshake lemma is used. Three
leaves contribute one apiece to the degree sum, every other vertex contributes two plus
whatever it carries above two, and the totals leave exactly one degree to carry. -/

/-- **A tree with exactly three leaves has a vertex of degree three, and every other vertex
has degree at most two** — so it is a leaf or has degree exactly two, and the vertex of degree
three is unique.

The count: with `k` non-leaf vertices the tree has `k + 3` vertices, hence `k + 2` edges
(`Graph.IsTree.edge_count`), hence degree sum `2k + 4` (the handshake lemma). The leaves
contribute `3`, so the non-leaves contribute `2k + 1`; each contributes at least `2`, so
between them they carry exactly one degree above two. -/
theorem IsTree.three_leaves [G.Finite] (hT : G.IsTree)
    (hleaves : {z | G.IsLeaf z}.ncard = 3) :
    ∃ x ∈ V(G), G.degree x = 3 ∧ ∀ z ∈ V(G), z ≠ x → G.degree z ≤ 2 := by
  classical
  set L : Finset α := G.vertexFinset.filter (fun z ↦ G.degree z = 1) with hL
  set I : Finset α := G.vertexFinset.filter (fun z ↦ ¬ G.degree z = 1) with hI
  -- The filter really is the set of leaves.
  have hcoe : (L : Set α) = {z | G.IsLeaf z} := by
    ext z
    simp [hL, isLeaf_iff]
  have hLcard : L.card = 3 := by rw [← Set.ncard_coe_finset, hcoe]; exact hleaves
  -- Three leaves is already three vertices.
  have h2 : 2 ≤ V(G).ncard := by
    have := Finset.card_le_card (Finset.filter_subset (fun z ↦ G.degree z = 1) G.vertexFinset)
    rw [hLcard, card_vertexFinset] at this
    omega
  -- Each leaf contributes one to the degree sum.
  have hsumL : ∑ z ∈ L, G.degree z = 3 := by
    rw [Finset.sum_congr rfl fun z hz ↦ (Finset.mem_filter.1 hz).2, Finset.sum_const, hLcard]
    simp
  -- Each non-leaf is on at least two edges.
  have hdeg2 : ∀ z ∈ I, 2 ≤ G.degree z := by
    intro z hz
    obtain ⟨hzV, hzd⟩ := Finset.mem_filter.1 hz
    have := hT.connected.degree_pos h2 (mem_vertexFinset.1 hzV)
    omega
  -- So it contributes two plus whatever it carries above two.
  have hsumI : ∑ z ∈ I, G.degree z = 2 * I.card + ∑ z ∈ I, (G.degree z - 2) := by
    rw [Finset.sum_congr rfl fun z hz ↦ (Nat.add_sub_cancel' (hdeg2 z hz)).symm,
      Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm]
  -- The two halves are the whole graph, and the handshake lemma reads the total.
  have hsplit : ∑ z ∈ L, G.degree z + ∑ z ∈ I, G.degree z = 2 * E(G).ncard := by
    rw [hL, hI, Finset.sum_filter_add_sum_filter_not]
    exact G.sum_degree_eq_two_mul_ncard_edgeSet
  have hcards : L.card + I.card = V(G).ncard := by
    rw [hL, hI, Finset.card_filter_add_card_filter_not, card_vertexFinset]
  -- The count: the non-leaves carry exactly one degree between them.
  have hexcess : ∑ z ∈ I, (G.degree z - 2) = 1 := by
    have hedges := hT.edge_count
    omega
  -- Whichever non-leaf carries it has degree three, and the others have degree two.
  obtain ⟨x, hxI, hxne⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero (by rw [hexcess]; exact one_ne_zero)
  have hrest : ∑ z ∈ I.erase x, (G.degree z - 2) + (G.degree x - 2) = 1 := by
    rw [Finset.sum_erase_add _ _ hxI]; exact hexcess
  have hx3 : G.degree x = 3 := by
    have := hdeg2 x hxI
    omega
  refine ⟨x, mem_vertexFinset.1 (Finset.mem_filter.1 hxI).1, hx3, fun z hz hzx ↦ ?_⟩
  by_cases hzL : G.degree z = 1
  · omega
  · have hzI : z ∈ I := Finset.mem_filter.2 ⟨mem_vertexFinset.2 hz, hzL⟩
    have hze : z ∈ I.erase x := Finset.mem_erase.2 ⟨hzx, hzI⟩
    have hzero : ∑ z ∈ I.erase x, (G.degree z - 2) = 0 := by omega
    have := (Finset.sum_eq_zero_iff.1 hzero) z hze
    have := hdeg2 z hzI
    omega

end Graph

end BundlePart392

section BundlePart393
/- Source: dev/planar_search/schoenflies_port/Schoenflies/Graph/RelativeEar.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/




/-!
# The relative ear decomposition

`lem:relative-ear`: *if `H` is a 2-connected subgraph of a finite 2-connected graph `G`, then
`G` is obtained from `H` by repeatedly adding paths whose distinct endpoints are already
present and whose internal vertices are new.*

Two things are delivered, and they are different in kind.

* `Graph.IsTwoConnected.relative_ear_exists` — the **relative** ear: the blueprint's own
  construction, through a component of `G - V(K)`, which is what makes the internal vertices
  new. `Graph.IsTwoConnected.ear_exists` in `Schoenflies/Graph/Ear.lean` finds *an* ear by a
  crossing walk, but says nothing about where the ear's interior lies — its path may run back
  and forth through the subgraph. That is enough to make the subgraph grow; it is **not**
  enough for the consumers, which need "whose internal vertices are new" verbatim (the ear's
  interior must be disjoint from the current skeleton, so that it lies in one current face).
* `Graph.IsTwoConnected.ear_decomposition` — the **iterated** form, as an induction principle.
  `Graph.IsTwoConnected.grows_by_ear` is deliberately one step; the finiteness induction the
  blueprint hides behind "finiteness terminates the process" is done here.

## Why the relative form is a different theorem

The blueprint's proof does not walk out of the subgraph and hope. It looks at a component `L`
of `G - V(H₀)`: if `L` has a vertex it has two distinct neighbours in `H₀`, since otherwise
its unique neighbour would be a cut vertex of `G`, and a shortest path through `L` between two
such neighbours is an ear. That path meets `V(H₀)` only at its two ends **by construction**,
because its interior was built inside `G - V(H₀)`.

All of that is already proved: `Graph.IsTwoConnected.exists_path_through_component` in
`Schoenflies/Graph/Component.lean` packages the component argument and the path through it.
What is left here is to feed it `S = V(K)` — the two distinct vertices of `S` it asks for are
two of the three that a 2-connected `K` has — and to read its "every edge has an end outside
`S`" as "no edge of the ear is an edge of `K`".

The degenerate branch is the blueprint's second sentence: if every vertex of `G` is already
present, a missing edge is an ear of length one, and it has no internal vertex at all. As in
`Graph.IsTwoConnected.ear_exists`, that branch — and only that branch — needs `G` to be
loopless: a loop added to a 2-connected graph leaves it 2-connected, and no ear between
*distinct* endpoints can supply it.

## The termination measure

Edges, not vertices: `(E(G) \ E(B)).ncard`, which is finite because `G` is. Every ear
contributes at least one edge that `B` did not have — in the relative form *every* edge of the
ear is new, since each has an end outside `V(B)` — so the measure strictly drops, and the
process stops exactly when `B = G`. The stopping step is `Graph.eq_of_le_of_subset_subset`: a
subgraph with all the vertices and all the edges is the graph.

Note that the measure never needs to see a vertex. It is tempting to stop when `E(B) = E(G)`
and argue that a connected `G` has no isolated vertex; that is true but needs the degree
theory, and is unnecessary: if `V(B) ≠ V(G)` the ear that the first branch produces has an
edge outside `E(B)`, so the measure was not zero after all.

## One import that looks wrong

`Schoenflies/Graph/Tree.lean` is imported for a single two-line fact, `Graph.IsPath.ne_nil` —
a path between distinct vertices has an edge — which happens to live there. Nothing else in
this file has anything to do with trees. The honest fix is for the integrator to hoist
`Graph.IsPath.ne_nil` into `Schoenflies/Graph/Walk.lean`, where it belongs, and drop the
import; it is not restated here.

## What the induction principle gives a consumer

`motive G`, from `motive K` and one step. The step is handed the ear in full — the path `D` of
`G`, its distinct ends in `V(B)`, and the freshness of its interior — together with
`B.IsTwoConnected`, `K ≤ B` and `B ≤ G`, and must produce `motive (B.union (G.pathGraphOf a D))`.
That is exactly the shape of the induction in `lem:face-cycles` ("suppose it holds for the
current graph and add the next geometric ear") and of the finite transfer of Part II.

## Blueprint

* `Graph.IsTwoConnected.relative_ear_exists` — `lem:relative-ear`, the ear itself: "a shortest
  path through `L` between two such neighbours is an ear", plus "if all vertices are already
  present, add a missing edge as an ear of length one".
* `Graph.IsTwoConnected.relative_grows_by_ear` — the same, glued on: one step of "`G` is
  obtained from `H` by repeatedly adding paths".
* `Graph.IsTwoConnected.ear_decomposition` — `lem:relative-ear` in full, including
  "finiteness terminates the process", as an induction principle.

## Namespace

Root `Graph`, as fixed by `Schoenflies/Graph/Walk.lean`.
-/

open Set
open scoped Graph

namespace Graph

variable {α β : Type*} {G K B : Graph α β} {a b x y : α} {e f : β} {D : List β}

/-! ### Two facts about a subgraph inclusion

Both are general and neither is in `Schoenflies/Graph/Walk.lean`; the integrator may want to
hoist them. -/

/-- **An edge of a subgraph has its ends in the subgraph**, even when the incidence is only
known in the big graph. This is what turns "every edge of the ear has an end outside `V(K)`"
into "no edge of the ear is an edge of `K`". -/
theorem mem_vertexSet_of_inc_of_mem_edgeSet (hKG : K ≤ G) (hf : f ∈ E(K)) (h : G.Inc f y) :
    y ∈ V(K) :=
  ((hKG.inc_congr hf).2 h).vertex_mem

/-- **A subgraph with all the vertices and all the edges is the graph.** The termination
condition of the ear process. -/
theorem eq_of_le_of_subset_subset (hKG : K ≤ G) (hV : V(G) ⊆ V(K)) (hE : E(G) ⊆ E(K)) :
    K = G :=
  le_antisymm hKG ((Compatible.of_ge hKG).le_iff.2 ⟨hV, hE⟩)

/-! ### The relative ear -/

/-- **`lem:relative-ear`, the ear.** A 2-connected subgraph `K` of a loopless 2-connected `G`
that is missing a vertex or an edge has a *relative* ear: a path of `G` whose two distinct
endpoints lie in `K`, whose every other vertex lies **outside** `K`, and none of whose edges
belongs to `K`.

This is the blueprint's own construction, and the freshness of the interior is what
distinguishes it from `Graph.IsTwoConnected.ear_exists`. The first branch takes a component
`L` of `G - V(K)` and a path across it between two of its neighbours in `K`
(`Graph.IsTwoConnected.exists_path_through_component`); the two distinct vertices of `V(K)`
that construction needs are supplied by the counting clause of `K.IsTwoConnected`. The second
branch is the blueprint's "if all vertices are already present, add a missing edge as an ear
of length one", and it is the only place looplessness is used. -/
theorem IsTwoConnected.relative_ear_exists (hG : G.IsTwoConnected) (hK : K.IsTwoConnected)
    (hKG : K ≤ G) (hnl : ∀ ⦃g x⦄, ¬ G.IsLoopAt g x)
    (hproper : (∃ x ∈ V(G), x ∉ V(K)) ∨ (∃ g ∈ E(G), g ∉ E(K))) :
    ∃ a b D, G.IsPath a D b ∧ a ≠ b ∧ a ∈ V(K) ∧ b ∈ V(K) ∧ D ≠ [] ∧
      (∀ y ∈ G.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(K)) ∧ (∀ g ∈ D, g ∉ E(K)) := by
  by_cases hout : ∃ x ∈ V(G), x ∉ V(K)
  · obtain ⟨x, hxG, hxK⟩ := hout
    -- The subgraph's three vertices supply the two distinct targets the component needs.
    obtain ⟨p, hp, q, hq, -, -, hpq, -, -⟩ := hK.hasThreeVertices
    obtain ⟨a, ha, b, hb, D, hab, hpath, hint, -, hedge⟩ :=
      hG.exists_path_through_component hKG.vertexSet_mono hp hq hpq hxG hxK
    refine ⟨a, b, D, hpath, hab, ha, hb, hpath.ne_nil hab, hint, fun f hf hfK ↦ ?_⟩
    -- Each edge of the ear has an end outside `V(K)`, so it is not an edge of `K`.
    obtain ⟨y, hy, hyK⟩ := hedge f hf
    exact hyK (mem_vertexSet_of_inc_of_mem_edgeSet hKG hfK hy)
  · -- Every vertex is already present, so a missing edge is an ear of length one.
    push Not at hout
    obtain ⟨f, hfG, hfK⟩ := hproper.resolve_left (by rintro ⟨x, hx, hx'⟩; exact hx' (hout x hx))
    obtain ⟨p, q, hpq⟩ := exists_isLink_of_mem_edgeSet hfG
    have hne : p ≠ q := by rintro rfl; exact hnl hpq
    refine ⟨p, q, [f], .single hpq hne, hne, hout p hpq.left_mem, hout q hpq.right_mem,
      by simp, fun y hy hyp hyq ↦ ?_, fun g hg ↦ ?_⟩
    · -- A one-edge path visits nothing but its two ends, so freshness is vacuous.
      rw [walkVertices_cons hpq, walkVertices_nil] at hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      exacts [absurd rfl hyp, absurd rfl hyq]
    · obtain rfl : g = f := by simpa using hg
      exact hfK

/-- **One step of the relative ear decomposition.** The ear of
`Graph.IsTwoConnected.relative_ear_exists`, glued on with `Graph.IsTwoConnected.ear`: the
enlarged graph is again a 2-connected subgraph of `G` between `K` and `G`, and it has an edge
that `K` did not have.

The ear data is handed back alongside the enlarged graph, because a consumer of the geometric
version needs the *path*, not merely the fact that the subgraph grew. -/
theorem IsTwoConnected.relative_grows_by_ear (hG : G.IsTwoConnected) (hK : K.IsTwoConnected)
    (hKG : K ≤ G) (hnl : ∀ ⦃g x⦄, ¬ G.IsLoopAt g x)
    (hproper : (∃ x ∈ V(G), x ∉ V(K)) ∨ (∃ g ∈ E(G), g ∉ E(K))) :
    ∃ a b D, G.IsPath a D b ∧ a ≠ b ∧ a ∈ V(K) ∧ b ∈ V(K) ∧
      (∀ y ∈ G.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(K)) ∧
      (K.union (G.pathGraphOf a D)).IsTwoConnected ∧
      K ≤ K.union (G.pathGraphOf a D) ∧ K.union (G.pathGraphOf a D) ≤ G ∧
      ∃ g ∈ E(K.union (G.pathGraphOf a D)), g ∉ E(K) := by
  obtain ⟨a, b, D, hpath, hab, ha, hb, hDne, hint, hnew⟩ :=
    hG.relative_ear_exists hK hKG hnl hproper
  have hearle : G.pathGraphOf a D ≤ G := pathGraphOf_le hpath.isWalk
  have hearP : (G.pathGraphOf a D).IsPathGraph a D b := hpath.isPathGraph_pathGraphOf
  obtain ⟨g, hgD⟩ : ∃ g, g ∈ D := by
    cases D with
    | nil => exact absurd rfl hDne
    | cons g t => exact ⟨g, List.mem_cons_self⟩
  exact ⟨a, b, D, hpath, hab, ha, hb, hint,
    hK.ear (Compatible.of_le_le hKG hearle) hearP hab ha hb,
    left_le_union _ _, union_le hKG hearle,
    g, Set.mem_union_right _ (hearP.mem_edgeSet hgD), hnew g hgD⟩

/-! ### Reading the enlarged graph

Two unfoldings a consumer of the induction principle below needs immediately, since the step's
conclusion is about `B.union (G.pathGraphOf a D)`. Both are immediate from the simp lemmas of
`Schoenflies/Graph/TwoConnected.lean` and `Schoenflies/Graph/PathGraph.lean`; they are here
only so that no consumer has to rediscover which two to combine. -/

@[simp]
theorem vertexSet_union_pathGraphOf (B G : Graph α β) (a : α) (D : List β) :
    V(B.union (G.pathGraphOf a D)) = V(B) ∪ G.walkVertices a D := rfl

theorem edgeSet_union_pathGraphOf (h : G.IsWalk a D b) :
    E(B.union (G.pathGraphOf a D)) = E(B) ∪ {e | e ∈ D} := by
  rw [edgeSet_union, pathGraphOf_edgeSet h]

/-! ### Iterating: the decomposition itself -/

/-- **`lem:relative-ear`.** A 2-connected subgraph `K` of a finite loopless 2-connected graph
`G` grows to `G` by repeatedly adding relative ears, stated as the induction principle a
consumer uses: whatever holds of `K` and survives the addition of one ear holds of `G`.

The step is given the whole ear — the path `D` of `G`, its two distinct ends in the current
subgraph `B`, and the fact that its other vertices are outside `B` — together with
`B.IsTwoConnected`, `K ≤ B` and `B ≤ G`.

"Finiteness terminates the process" is the strong induction below on `(E(G) \ E(B)).ncard`:
every ear contributes an edge of `G` that `B` was missing, and the process can only be stuck
when `B` has all of `G`'s vertices and edges, which makes `B = G`. -/
theorem IsTwoConnected.ear_decomposition {motive : Graph α β → Prop} [G.Finite]
    (hG : G.IsTwoConnected) (hnl : ∀ ⦃g x⦄, ¬ G.IsLoopAt g x)
    (hK : K.IsTwoConnected) (hKG : K ≤ G) (base : motive K)
    (step : ∀ (B : Graph α β) (a b : α) (D : List β), B.IsTwoConnected → K ≤ B → B ≤ G →
      motive B → G.IsPath a D b → a ≠ b → a ∈ V(B) → b ∈ V(B) →
      (∀ y ∈ G.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B)) →
      motive (B.union (G.pathGraphOf a D))) :
    motive G := by
  -- One step, packaged with the strict drop of the measure.
  have hstep : ∀ B : Graph α β, B ≠ G → B.IsTwoConnected → K ≤ B → B ≤ G → motive B →
      ∃ B' : Graph α β, B'.IsTwoConnected ∧ K ≤ B' ∧ B' ≤ G ∧ motive B' ∧
        (E(G) \ E(B')).ncard < (E(G) \ E(B)).ncard := by
    intro B hBne hB hKB hBG hmot
    -- A subgraph that is not the graph is missing a vertex or an edge.
    have hproper : (∃ x ∈ V(G), x ∉ V(B)) ∨ (∃ g ∈ E(G), g ∉ E(B)) := by
      by_contra hcon
      push Not at hcon
      exact hBne (eq_of_le_of_subset_subset hBG (fun x hx ↦ hcon.1 x hx) fun g hg ↦ hcon.2 g hg)
    obtain ⟨a, b, D, hpath, hab, ha, hb, hint, hB'two, hBB', hB'G, g, hgB', hgB⟩ :=
      hG.relative_grows_by_ear hB hBG hnl hproper
    refine ⟨_, hB'two, hKB.trans hBB', hB'G,
      step B a b D hB hKB hBG hmot hpath hab ha hb hint, ?_⟩
    -- The new edge is one the old subgraph was missing, and nothing was lost.
    refine Set.ncard_lt_ncard ⟨fun f hf ↦ ⟨hf.1, fun hfB ↦ hf.2 (hBB'.edgeSet_mono hfB)⟩, ?_⟩
      ((finite_edgeSet G).subset sdiff_subset)
    exact fun hcon ↦ (hcon ⟨hB'G.edgeSet_mono hgB', hgB⟩).2 hgB'
  -- Strong induction on the number of edges of `G` the subgraph is still missing.
  have key : ∀ n, ∀ B : Graph α β, (E(G) \ E(B)).ncard ≤ n → B.IsTwoConnected → K ≤ B →
      B ≤ G → motive B → motive G := by
    intro n
    induction n with
    | zero =>
      intro B hcard hB hKB hBG hmot
      by_cases hBne : B = G
      · exact hBne ▸ hmot
      · -- Nothing is missing, yet an ear was found: its edges were missing after all.
        obtain ⟨B', -, -, -, -, hlt⟩ := hstep B hBne hB hKB hBG hmot
        exact absurd (Nat.lt_of_lt_of_le hlt hcard) (Nat.not_lt_zero _)
    | succ n ih =>
      intro B hcard hB hKB hBG hmot
      by_cases hBne : B = G
      · exact hBne ▸ hmot
      · obtain ⟨B', hB', hKB', hB'G, hmot', hlt⟩ := hstep B hBne hB hKB hBG hmot
        exact ih B' (by omega) hB' hKB' hB'G hmot'
  exact key _ K le_rfl hK le_rfl hKG base

end Graph

end BundlePart393

section BundlePart394
/- Source: dev/planar_search/schoenflies_port/Schoenflies/Graph/OuterFace.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/


/-!
# The outer face

Exactly one face of a finite plane graph is unbounded.

The plane fact this needs is not "the exterior of a large disk is connected" but the exterior
of a *square*, and that one is elementary — `Plane.isConnected_beyondSquare`, four convex
half-planes with consecutive ones sharing a corner. The disk version is what would have
needed a traversal of the circle, which a trigonometry-free development withholds.

No face is produced as data: a face is named by a point of it, as `Graph.face` always has
been, so "the outer face" is "the face through any point far enough out".

## Blueprint

* `exists_unbounded_face` — some face is unbounded.
* `unbounded_face_unique` — any two unbounded faces coincide.
* `beyondSquare_subset_face` — an unbounded face swallows the whole outside of any square
  containing the drawing. This is the working form: it is how one proves a given point lies in
  the outer face.
-/

open Metric Set Schoenflies unitInterval
open scoped Graph

namespace Graph

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}

/-- A closed axis-parallel square is bounded: it sits inside a Euclidean ball of radius
`√2 · r`, by the norm comparison. -/
theorem isBounded_closedSquare (r : ℝ) :
    Bornology.IsBounded (Schoenflies.Plane.closedSquare 0 r) := by
  refine (Metric.isBounded_closedBall (x := (0 : Plane)) (r := Real.sqrt 2 * r)).subset ?_
  intro x hx
  have hsup : Schoenflies.Plane.supNorm x ≤ r := by
    simpa [Schoenflies.Plane.closedSquare] using hx
  have : ‖x‖ ≤ Real.sqrt 2 * r := by
    refine le_trans (Schoenflies.Plane.norm_le_sqrt_two_mul_supNorm x) ?_
    exact mul_le_mul_of_nonneg_left hsup (Real.sqrt_nonneg 2)
  simpa [Metric.mem_closedBall, dist_eq_norm] using this

/-- A square containing the whole drawing. -/
theorem IsDrawing.exists_closedSquare [G.Finite] (h : IsDrawing G drawing) :
    ∃ r : ℝ, 0 ≤ r ∧ pointSet G drawing ⊆ Schoenflies.Plane.closedSquare 0 r :=
  Schoenflies.Plane.exists_closedSquare_of_isBounded h.isCompact_pointSet.isBounded

/-- Outside a square containing the drawing, every point is in the exterior. -/
theorem beyondSquare_subset_exterior {r : ℝ}
    (hr : pointSet G drawing ⊆ Schoenflies.Plane.closedSquare 0 r) :
    Schoenflies.Plane.beyondSquare r ⊆ exterior G drawing := by
  rw [Schoenflies.Plane.beyondSquare_eq_compl]
  exact compl_subset_compl.2 hr

/-- The outside of a containing square lies wholly inside one face — the face through any of
its points. This is the working form of "there is an outer face". -/
theorem beyondSquare_subset_face {r : ℝ}
    (hr : pointSet G drawing ⊆ Schoenflies.Plane.closedSquare 0 r) {base : Plane}
    (hbase : base ∈ Schoenflies.Plane.beyondSquare r) :
    Schoenflies.Plane.beyondSquare r ⊆ face G drawing base :=
  (Schoenflies.Plane.isConnected_beyondSquare r).isPreconnected.subset_connectedComponentIn
    hbase (beyondSquare_subset_exterior hr)

/-- The outside of a square is unbounded: it contains points of every size. -/
theorem not_isBounded_beyondSquare (r : ℝ) :
    ¬ Bornology.IsBounded (Schoenflies.Plane.beyondSquare r) := by
  intro hb
  obtain ⟨s, -, hs⟩ := Schoenflies.Plane.exists_closedSquare_of_isBounded hb
  -- A point beyond both radii is in the outside but not in the square that was claimed to
  -- contain it.
  set t : ℝ := max (max r s) 0 + 1 with ht
  have ht0 : 0 ≤ t := by
    have := le_max_right (max r s) 0; simp only [ht]; linarith
  have htr : r < t := by
    have h1 := le_max_left r s
    have h2 := le_max_left (max r s) 0
    simp only [ht]; linarith
  have hts : s < t := by
    have h1 := le_max_right r s
    have h2 := le_max_left (max r s) 0
    simp only [ht]; linarith
  -- `Plane.mk t 0` has first coordinate `t` definitionally, so `show` states the real goal.
  have hmem : Schoenflies.Plane.mk t 0 ∈ Schoenflies.Plane.beyondSquare r :=
    Or.inl (show r < |t| by rw [abs_of_nonneg ht0]; exact htr)
  have hin := hs hmem
  simp only [Schoenflies.Plane.closedSquare, mem_setOf_eq, Schoenflies.Plane.supDist_zero,
    Schoenflies.Plane.supNorm, max_le_iff] at hin
  have h1 : |t| ≤ s := hin.1
  rw [abs_of_nonneg ht0] at h1
  linarith

/-- Some face is unbounded. -/
theorem exists_unbounded_face [G.Finite] (h : IsDrawing G drawing) :
    ∃ base ∈ exterior G drawing, ¬ Bornology.IsBounded (face G drawing base) := by
  obtain ⟨r, hr0, hr⟩ := h.exists_closedSquare
  have hmem : Schoenflies.Plane.mk (r + 1) 0 ∈ Schoenflies.Plane.beyondSquare r :=
    Or.inl (show r < |r + 1| by
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ r + 1)]; linarith)
  refine ⟨Schoenflies.Plane.mk (r + 1) 0, beyondSquare_subset_exterior hr hmem, fun hb => ?_⟩
  exact not_isBounded_beyondSquare r (hb.subset (beyondSquare_subset_face hr hmem))

/-- Any two unbounded faces coincide: an unbounded face escapes every containing square, so it
swallows the whole outside and is named by any point of it. -/
theorem unbounded_face_unique [G.Finite] (h : IsDrawing G drawing) {b c : Plane}
    (hbu : ¬ Bornology.IsBounded (face G drawing b))
    (hcu : ¬ Bornology.IsBounded (face G drawing c)) :
    face G drawing b = face G drawing c := by
  obtain ⟨r, hr0, hr⟩ := h.exists_closedSquare
  -- An unbounded face is not contained in the square, so it meets the outside.
  have escape : ∀ z : Plane, ¬ Bornology.IsBounded (face G drawing z) →
      ∃ w, w ∈ face G drawing z ∧ w ∈ Schoenflies.Plane.beyondSquare r := by
    intro z hz
    by_contra hcon
    push Not at hcon
    refine hz ((isBounded_closedSquare r).subset fun w hw => ?_)
    have hw' : w ∉ Schoenflies.Plane.beyondSquare r := hcon w hw
    rw [Schoenflies.Plane.beyondSquare_eq_compl] at hw'
    simpa using hw'
  obtain ⟨w, hwb, hwout⟩ := escape b hbu
  obtain ⟨v, hvc, hvout⟩ := escape c hcu
  -- Each face therefore swallows the whole outside, so the two share a point.
  have hbeyond_b : Schoenflies.Plane.beyondSquare r ⊆ face G drawing b := by
    have hsub := beyondSquare_subset_face (G := G) (drawing := drawing) hr hwout
    have hwe : face G drawing w = face G drawing b := (connectedComponentIn_eq hwb).symm
    rwa [hwe] at hsub
  have hbeyond_c : Schoenflies.Plane.beyondSquare r ⊆ face G drawing c := by
    have hsub := beyondSquare_subset_face (G := G) (drawing := drawing) hr hvout
    have hve : face G drawing v = face G drawing c := (connectedComponentIn_eq hvc).symm
    rwa [hve] at hsub
  obtain ⟨z, hz⟩ := (Schoenflies.Plane.isConnected_beyondSquare r).nonempty
  have e1 : face G drawing b = face G drawing z := connectedComponentIn_eq (hbeyond_b hz)
  have e2 : face G drawing c = face G drawing z := connectedComponentIn_eq (hbeyond_c hz)
  rw [e1, e2]

end Graph

end BundlePart394

section BundlePart395
/- Source: dev/planar_search/schoenflies_port/Schoenflies/FaceCycles.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/





/-!
# Face cycles: the base cycle, and the faces of a plane graph that grows by ears

`lem:face-cycles` — *every face of a finite 2-connected polygonal plane graph has a cycle as
its boundary and is one of the two complementary regions of that cycle* — is proved by growing
the graph from a cycle by ears (`Graph.IsTwoConnected.ear_decomposition`) and applying
`thm:polygonal-crosscut` at each step. This file supplies everything in that proof that is not
the crosscut application itself. **The lemma is not proved here**; see "What is missing" below,
which says exactly what is in the way.

## The base cycle

The blueprint's first paragraph, in full. *"First choose a cycle of length at least three.
Such a cycle exists: under our convention the graph has at least three vertices, and every
vertex has at least two distinct neighbors. Indeed, if a vertex `v` had only one distinct
neighbor `w`, then deleting `w` would isolate `v` from some third vertex, contrary to
2-connectivity. Now take a maximal simple path. An endpoint has a neighbor on the path other
than its predecessor, and the resulting closed subpath is a cycle of length at least three."*

`Graph.IsTwoConnected.exists_adj_ne` is the two-neighbours sentence; "take a maximal simple
path" is `Graph.exists_longest_path`, already in `Schoenflies/Graph/Tree.lean` and not rebuilt
here; and `Graph.IsTwoConnected.exists_long_cycle` is the conclusion, packaged as
`Graph.IsLongCycle`, a cycle together with a *named* third vertex. Naming the third vertex
rather than counting is what both consumers want: the counting clause of
`Graph.IsTwoConnected`, and — later — the non-degeneracy of the polygon the cycle draws.

`Graph.cycleGraph` is that cycle as a subgraph, and `Graph.IsLongCycle.isTwoConnected` is
*"the cycle `C` is 2-connected, so Lemma `lem:relative-ear` builds the graph from `C`"*. This
is the one place "length at least three" is used: a two-vertex cycle is a `Graph.banana`, and
`Graph.not_isTwoConnected_banana` says it is not 2-connected.

## One step of the induction

Adding an ear removes the ear's own point set from the exterior and changes nothing else:
`Graph.pointSet_union`, `Graph.exterior_union` and `Graph.face_union_eq_of_disjoint` are
*"all other faces are unchanged"*.

`Graph.IsDrawing.exists_face_of_ear` is *"its interior is connected and disjoint from the
current graph, so it lies in one current face `F`"*: the ear's realisation without its two ends
is the interior of an arc, hence connected
(`Schoenflies.IsArcBetween.isConnected_diff`), and it misses the drawing of the current
subgraph altogether (`Graph.IsDrawing.edgesCover_inter_pointSet`).
`Graph.IsDrawing.ends_mem_frontier_face` is the next sentence, *"the ear's two endpoints are
limits of its interior, which lies in `F`, so they lie on `∂F`"* — which is what makes the ear
a crosscut of that face.

`Graph.IsDrawing.mono` — a subgraph of a plane graph is a plane graph, with the same drawing —
is what lets the induction talk about the faces of the current subgraph at all.

## An interface repair

`Graph.IsTwoConnected.ear_decomposition` hands its step the ear's path but **not** the clause
`∀ g ∈ D, g ∉ E(B)`, which `Graph.IsTwoConnected.relative_ear_exists` proves and which
`Graph.IsTwoConnected.relative_grows_by_ear` drops on the way. A geometric consumer needs it:
without it the ear may be drawn right on top of the current subgraph, and
`Graph.IsDrawing.edgesCover_inter_pointSet` is false. `Graph.ear_edges_notMem_or_union_eq`
recovers it in the only form available from the outside — either every edge of the ear is new,
or the ear is a single edge the subgraph already had and the enlarged graph *is* the old graph,
so the step has nothing to prove. The better fix is for the integrator to add the clause to
`relative_grows_by_ear` and to `ear_decomposition`; that would make this lemma unnecessary.

## What is missing

The crosscut application, and therefore `lem:face-cycles` itself. `thm:polygonal-crosscut` is
available as `Schoenflies.IsPolygonalCrosscut` and `Schoenflies.polygonal_crosscut`, whose
hypotheses are stated for `Schoenflies.ClosedPolygon`s: an explicit cyclic vertex list with
`vertex_inj`, `edges_meet` and `corner` (no two consecutive edges collinear). The realisation
of a graph cycle arrives here as a **set** — `Graph.edgesCover drawing (e :: D)` — which
`Graph.IsDrawing.cycle_isJordanCurve` knows to be a Jordan curve and `Graph.polygonal_redrawing`
knows to be polygonal. Turning such a set into a `ClosedPolygon` (enumerate its vertices
cyclically, delete the redundant collinear ones, and derive `vertex_inj` and `edges_meet` from
simplicity) is a construction `main` does not have, and the same construction is needed again
for the two curves `Aᵢ ∪ P` that the crosscut produces. Nothing below pretends to it, and no
statement below is weaker than its blueprint counterpart.

## Namespace

Root `Graph`, as fixed by `Schoenflies/Graph/Walk.lean`. The two arc lemmas are stated in
`Schoenflies`, where the rest of the arc theory lives.

## Blueprint

* `Graph.IsTwoConnected.exists_adj_ne` — "every vertex has at least two distinct neighbors".
* `Graph.IsLongCycle`, `Graph.IsTwoConnected.exists_long_cycle` — "the resulting closed subpath
  is a cycle of length at least three".
* `Graph.cycleGraph`, `Graph.IsLongCycle.isTwoConnected` — "the cycle `C` is 2-connected, so
  Lemma `lem:relative-ear` builds the graph from `C`".
* `Graph.ear_edges_notMem_or_union_eq` — the ear's edges are new, or the ear is not an ear.
* `Graph.pointSet_union`, `Graph.exterior_union`, `Graph.face_union_subset`,
  `Graph.face_union_eq_of_disjoint` — "all other faces are unchanged".
* `Graph.IsDrawing.mono` — the current subgraph is itself a plane graph.
* `Schoenflies.IsArcBetween.isConnected_diff`,
  `Schoenflies.IsArcBetween.left_mem_closure_diff`, `…right_mem_closure_diff`,
  `Graph.IsDrawing.edgesCover_inter_pointSet`, `Graph.IsDrawing.exists_face_of_ear`,
  `Graph.IsDrawing.ends_mem_frontier_face` — "its interior is connected and disjoint from the
  current graph, so it lies in one current face `F` … the ear's two endpoints are limits of its
  interior, which lies in `F`, so they lie on `∂F`; the ear is therefore a crosscut of that
  side".
-/

open Set
open scoped Graph

namespace Graph

variable {α β : Type*} {G H K B : Graph α β} {u v w x y z c : α} {e f g : β} {D W : List β}

/-! ## Two distinct neighbours -/

/-- **A vertex of a loopless 2-connected graph has a neighbour other than any prescribed
vertex** — in particular it has two distinct neighbours, and neither is itself. -/
theorem IsTwoConnected.exists_adj_ne (h : G.IsTwoConnected)
    (hnl : ∀ ⦃g x⦄, ¬ G.IsLoopAt g x) (hv : v ∈ V(G)) (w : α) :
    ∃ x, G.Adj v x ∧ x ≠ w := by
  rcases eq_or_ne v w with rfl | hvw
  · -- Deleting nothing: a walk to any other vertex leaves along a non-loop.
    obtain ⟨z, hz, hzv, -⟩ := h.hasThreeVertices.exists_ne_ne v v
    obtain ⟨T, hT⟩ := h.connected.reaches hv hz
    cases hT with
    | nil => exact absurd rfl hzv
    | @cons _ y _ g _ hl _ => exact ⟨y, ⟨g, hl⟩, fun hh ↦ hnl (hh ▸ hl)⟩
  · -- Deleting `w`: a walk to a third vertex leaves along an edge that survived it.
    obtain ⟨z, hz, hzv, hzw⟩ := h.hasThreeVertices.exists_ne_ne v w
    obtain ⟨T, hT⟩ := (h.deleteVerts_connected' w).reaches
      (mem_deleteVerts_singleton_of_ne hv hvw) (mem_deleteVerts_singleton_of_ne hz hzw)
    cases hT with
    | nil => exact absurd rfl (Ne.symm hzv)
    | @cons _ y _ g _ hl _ =>
      exact ⟨y, ⟨g, hl.mono deleteVerts_le⟩, (mem_deleteVerts_singleton.1 hl.right_mem).2⟩

/-! ## The base cycle

"Take a maximal simple path" is `Graph.exists_longest_path`, already in
`Schoenflies/Graph/Tree.lean` — it is what the three-leaf lemma runs on — so nothing here
rebuilds it. -/

/-- **A path from a vertex back to itself is empty.** The first step would depart from the
vertex the rest of the path arrives at, which the freshness clause forbids. -/
theorem IsPath.eq_nil_of_eq (h : G.IsPath u W u) : W = [] := by
  cases h with
  | nil => rfl
  | cons _ hT hfresh => exact absurd hT.target_mem_walkVertices hfresh

/-- A cycle with at least three vertices — the blueprint's "cycle of length at least three".
The third vertex is named rather than counted, because that is what both consumers want. -/
structure IsLongCycle (G : Graph α β) (e : β) (u v : α) (D : List β) (w : α) : Prop where
  /-- The edge and the detour form a cycle. -/
  isCycle : G.IsCycleThrough e u v D
  /-- The detour visits a third vertex … -/
  mem : w ∈ G.walkVertices u D
  /-- … distinct from the source of the edge … -/
  ne_left : w ≠ u
  /-- … and from its target. -/
  ne_right : w ≠ v

namespace IsLongCycle

variable (h : G.IsLongCycle e u v D w)
include h

theorem isLink : G.IsLink e u v := h.isCycle.isLink

theorem isPath : G.IsPath u D v := h.isCycle.isPath

theorem notMem : e ∉ D := h.isCycle.notMem

/-- The two ends of the edge are distinct: otherwise the detour would be a path from a vertex
to itself, hence empty, and would visit no third vertex. -/
theorem ne : u ≠ v := by
  rintro rfl
  have hnil : D = [] := h.isPath.eq_nil_of_eq
  have hmem := h.mem
  rw [hnil, walkVertices_nil] at hmem
  exact h.ne_left hmem

end IsLongCycle

/-- **"The resulting closed subpath is a cycle of length at least three."** A finite loopless
2-connected graph has a cycle with three distinct vertices.

Take a maximal path `u —W→ v`. Its source `u` has a neighbour `x` other than the vertex `w₀`
the path first steps to (`Graph.IsTwoConnected.exists_adj_ne`), and `x` lies on the path:
otherwise the edge to it could be prepended, contradicting maximality. Cutting the path at `x`
gives a path from `u` to `x` whose first step is still to `w₀`, and the chord closes it into a
cycle through `u`, `w₀` and `x`. The chord is not an edge of that piece: an edge at `u` in the
tail is what the path's freshness clause forbids, and the first edge is not the chord because
their far ends differ. -/
theorem IsTwoConnected.exists_long_cycle [G.Finite] (h : G.IsTwoConnected)
    (hnl : ∀ ⦃g x⦄, ¬ G.IsLoopAt g x) :
    ∃ g u x D w, G.IsLongCycle g u x D w := by
  obtain ⟨p, hp, -⟩ := h.hasThreeVertices
  obtain ⟨u, v, W, hpath, hmax⟩ := exists_longest_path hp
  -- The maximal path is not empty: an edge at its source could otherwise be prepended.
  obtain ⟨f, W', rfl⟩ : ∃ f W', W = f :: W' := by
    cases hW : W with
    | cons f W' => exact ⟨f, W', rfl⟩
    | nil =>
      obtain ⟨y, ⟨g, hl⟩, hyu⟩ := h.exists_adj_ne hnl hpath.left_mem u
      have hle := hmax _ _ _ (IsPath.single hl.symm hyu)
      rw [hW] at hle
      simp at hle
  obtain ⟨w₀, hl₀, hpath', hfresh⟩ : ∃ w₀, G.IsLink f u w₀ ∧ G.IsPath w₀ W' v ∧
      u ∉ G.walkVertices w₀ W' := by
    cases hpath with
    | cons hl hW hfr => exact ⟨_, hl, hW, hfr⟩
  -- A second neighbour of the source, distinct from the vertex the path first steps to.
  obtain ⟨x, ⟨g, hlg⟩, hxw₀⟩ := h.exists_adj_ne hnl hpath.left_mem w₀
  have hxu : x ≠ u := fun hh ↦ hnl (hh ▸ hlg)
  -- It lies on the path: otherwise the chord would prepend to it.
  have hxW : x ∈ G.walkVertices u (f :: W') := by
    by_contra hx
    have hle := hmax _ _ _ (IsPath.cons hlg.symm hpath hx)
    simp at hle
  obtain ⟨W₁, W₂, hsplit, h₁, -, -⟩ := hpath.split hxW
  have hW₁sub : W₁ ⊆ f :: W' := hsplit ▸ List.subset_append_left _ _
  -- The chord is not an edge of the piece: not the first edge, and not one further along.
  have hgW₁ : g ∉ W₁ := by
    intro hg
    rcases List.mem_cons.1 (hW₁sub hg) with rfl | hg'
    · exact hxw₀ (hlg.right_unique hl₀)
    · exact hfresh (mem_walkVertices_of_mem_covered ⟨g, hg', hlg.inc_left⟩)
  -- The piece starts with the first edge, so it visits the vertex the path first stepped to.
  have hfW₁ : f ∈ W₁ := by
    rcases W₁ with _ | ⟨a, T⟩
    · exact absurd h₁.isWalk.eq_of_nil (Ne.symm hxu)
    · obtain ⟨rfl, -⟩ : f = a ∧ W' = T ++ W₂ := by simpa using hsplit
      exact List.mem_cons_self
  exact ⟨g, u, x, W₁, w₀, ⟨hlg, h₁, hgW₁⟩,
    mem_walkVertices_of_mem_covered ⟨f, hfW₁, hl₀.inc_right⟩,
    fun hh ↦ hnl (hh ▸ hl₀), Ne.symm hxw₀⟩

/-! ## The cycle as a subgraph, and its 2-connectivity

`Graph.IsTwoConnected.ear_decomposition` starts from a 2-connected subgraph. The subgraph the
blueprint starts from is the base cycle, and this section builds it and proves it 2-connected.
This is the one place where "length at least three" is used: a two-vertex cycle is a
`Graph.banana`, and `Graph.not_isTwoConnected_banana` says it is not 2-connected. -/

/-- **A path graph grows with its edge list.** General, and not in
`Schoenflies/Graph/PathGraph.lean`; the integrator may want to hoist it. -/
theorem pathGraphOf_mono (h : W ⊆ D) : G.pathGraphOf u W ≤ G.pathGraphOf u D where
  vertexSet_mono := by
    simpa only [pathGraphOf_vertexSet] using walkVertices_mono (u := u) h
  isLink_mono := by
    intro f x y hl
    obtain ⟨hf, hxy, hx, hy⟩ := pathGraphOf_isLink.1 hl
    exact pathGraphOf_isLink.2
      ⟨h hf, hxy, walkVertices_mono h hx, walkVertices_mono h hy⟩

/-- The subgraph of `G` drawn by a cycle: the detour followed by the edge, as a closed walk.
Exported as the object rather than hidden behind an existential — the consumer of
`lem:face-cycles` needs the graph itself, to feed it to the ear decomposition. -/
def cycleGraph (G : Graph α β) (u : α) (e : β) (D : List β) : Graph α β :=
  G.pathGraphOf u (D ++ [e])

/-- The detour spans a path subgraph of the cycle. -/
theorem pathGraphOf_le_cycleGraph : G.pathGraphOf u D ≤ G.cycleGraph u e D :=
  pathGraphOf_mono (List.subset_append_left _ _)

namespace IsCycleThrough

variable (hc : G.IsCycleThrough e u v D)
include hc

/-- Going round: the detour and then the edge is a closed walk at the source. -/
theorem isWalk_round : G.IsWalk u (D ++ [e]) u :=
  hc.isPath.isWalk.append (IsWalk.single hc.isLink.symm)

/-- Closing the cycle adds no vertex: both ends of the edge are already on the detour. -/
theorem walkVertices_round : G.walkVertices u (D ++ [e]) = G.walkVertices u D := by
  refine Set.Subset.antisymm (fun y hy ↦ ?_) (walkVertices_mono (List.subset_append_left _ _))
  rcases mem_walkVertices_iff.1 hy with rfl | hcov
  · exact mem_walkVertices_self
  rw [coveredVertices_append] at hcov
  rcases hcov with hcov | ⟨g, hg, hinc⟩
  · exact mem_walkVertices_of_mem_covered hcov
  obtain rfl : g = e := by simpa using hg
  rcases hinc.eq_or_eq_of_isLink hc.isLink with rfl | rfl
  · exact mem_walkVertices_self
  · exact hc.isPath.target_mem_walkVertices

@[simp]
theorem cycleGraph_vertexSet : V(G.cycleGraph u e D) = G.walkVertices u D := by
  rw [cycleGraph, pathGraphOf_vertexSet, hc.walkVertices_round]

theorem cycleGraph_le : G.cycleGraph u e D ≤ G := pathGraphOf_le hc.isWalk_round

theorem cycleGraph_edgeSet : E(G.cycleGraph u e D) = {f | f ∈ D ++ [e]} :=
  pathGraphOf_edgeSet hc.isWalk_round

theorem left_mem_cycleGraph : u ∈ V(G.cycleGraph u e D) := by
  rw [hc.cycleGraph_vertexSet]; exact mem_walkVertices_self

theorem right_mem_cycleGraph : v ∈ V(G.cycleGraph u e D) := by
  rw [hc.cycleGraph_vertexSet]; exact hc.isPath.target_mem_walkVertices

/-- The edge of the cycle really is an edge of the cycle graph, joining the same two ends. -/
theorem cycleGraph_isLink : (G.cycleGraph u e D).IsLink e u v :=
  pathGraphOf_isLink.2 ⟨by simp, hc.isLink,
    hc.walkVertices_round ▸ mem_walkVertices_self,
    hc.walkVertices_round ▸ hc.isPath.target_mem_walkVertices⟩

/-- The cycle graph is connected: every vertex it has is visited by the detour, and the
detour's own prefix runs there from the source. -/
theorem cycleGraph_connected : (G.cycleGraph u e D).Connected := by
  refine Connected.of_hub hc.left_mem_cycleGraph fun x hx ↦ ?_
  rw [hc.cycleGraph_vertexSet] at hx
  obtain ⟨W₁, W₂, hcat, h₁, -, -⟩ := hc.isPath.split hx
  refine ⟨W₁, h₁.isWalk.anti hc.cycleGraph_le hc.left_mem_cycleGraph fun g hg ↦ ?_⟩
  rw [hc.cycleGraph_edgeSet]
  exact List.mem_append_left _ (hcat ▸ List.mem_append_left _ hg)

end IsCycleThrough

namespace IsLongCycle

variable (h : G.IsLongCycle e u v D w)
include h

theorem mem_cycleGraph : w ∈ V(G.cycleGraph u e D) := by
  rw [h.isCycle.cycleGraph_vertexSet]; exact h.mem

/-- **A cycle with three vertices is 2-connected**, which is what
`Graph.IsTwoConnected.ear_decomposition` asks of its starting subgraph.

Delete a vertex `c`. One of the two ends of the cycle's edge survives, and it is the hub:
every remaining vertex reaches an end of the *detour* inside the detour
(`Graph.IsPathGraph.reaches_an_end`), an end which — having been reached after the deletion —
survived it too, so the cycle's edge is still there to carry it the rest of the way. -/
theorem isTwoConnected : (G.cycleGraph u e D).IsTwoConnected where
  hasThreeVertices :=
    ⟨u, h.isCycle.left_mem_cycleGraph, v, h.isCycle.right_mem_cycleGraph,
      w, h.mem_cycleGraph, h.ne, Ne.symm h.ne_left, Ne.symm h.ne_right⟩
  connected := h.isCycle.cycleGraph_connected
  deleteVerts_connected := by
    intro c _
    set Kc := G.cycleGraph u e D with hKc
    set Pc := G.pathGraphOf u D with hPc
    have hPK : Pc.deleteVerts {c} ≤ Kc.deleteVerts {c} :=
      deleteVerts_mono pathGraphOf_le_cycleGraph _
    have hPpath : Pc.IsPathGraph u D v := h.isPath.isPathGraph_pathGraphOf
    -- The hub is whichever end of the cycle's edge survived; the argument is symmetric in
    -- the two, so it is done once for a named pair and applied twice.
    have main : ∀ a b : α, Kc.IsLink e a b → a ≠ c →
        (∀ x ∈ V(Kc), x ≠ c →
          (Pc.deleteVerts {c}).Reaches x a ∨ (Pc.deleteVerts {c}).Reaches x b) →
        (Kc.deleteVerts {c}).Connected := by
      intro a b hab hac hends
      refine Connected.of_hub (mem_deleteVerts_singleton_of_ne hab.left_mem hac) fun x hx ↦ ?_
      rw [vertexSet_deleteVerts] at hx
      obtain ⟨hxK, hxc⟩ := hx
      have hxc' : x ≠ c := by simpa using hxc
      rcases hends x hxK hxc' with hr | hr
      · exact (hr.mono hPK).symm
      · -- The far end was reached, so it survived; the cycle's edge joins it to the hub.
        have hbc : b ≠ c := (mem_deleteVerts_singleton.1 (hr.mono hPK).right_mem).2
        have hedge : (Kc.deleteVerts {c}).Reaches b a :=
          ⟨[e], IsWalk.single ((deleteVerts_isLink _ _).2 ⟨hab.symm, by simpa using hbc,
            by simpa using hac⟩)⟩
        exact ((hr.mono hPK).trans hedge).symm
    have hV : ∀ x ∈ V(Kc), x ∈ V(Pc) := fun x hx ↦ by
      rw [hKc, h.isCycle.cycleGraph_vertexSet] at hx; exact hx
    by_cases hcu : u = c
    · -- The source is gone, so the target is the hub.
      refine main v u h.isCycle.cycleGraph_isLink.symm (fun hh ↦ h.ne (hh.trans hcu.symm).symm)
        fun x hx hxc ↦ (hPpath.reaches_an_end (hV x hx) hxc).symm
    · exact main u v h.isCycle.cycleGraph_isLink hcu
        fun x hx hxc ↦ hPpath.reaches_an_end (hV x hx) hxc

end IsLongCycle


/-- A machine check that the two halves fit: the base cycle really is a legal starting point
for `Graph.IsTwoConnected.ear_decomposition`, so a consumer that can do the base case on
`G.cycleGraph u e D` and the ear step gets the conclusion for `G`. Nothing but the two
theorems is used. -/
example {motive : Graph α β → Prop} [G.Finite] (hG : G.IsTwoConnected)
    (hnl : ∀ ⦃g x⦄, ¬ G.IsLoopAt g x)
    (base : ∀ (e : β) (u v : α) (D : List β) (w : α), G.IsLongCycle e u v D w →
      motive (G.cycleGraph u e D))
    (step : ∀ (B : Graph α β) (a b : α) (D : List β), B.IsTwoConnected → B ≤ G → motive B →
      G.IsPath a D b → a ≠ b → a ∈ V(B) → b ∈ V(B) →
      (∀ y ∈ G.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B)) →
      motive (B.union (G.pathGraphOf a D))) :
    motive G := by
  obtain ⟨e, u, v, D, w, hcyc⟩ := hG.exists_long_cycle hnl
  exact hG.ear_decomposition hnl hcyc.isTwoConnected hcyc.isCycle.cycleGraph_le
    (base e u v D w hcyc)
    fun B a b D' hB _ hBG hmot hpath hab ha hb hint ↦
      step B a b D' hB hBG hmot hpath hab ha hb hint

/-! ## An ear that is not new

`Graph.IsTwoConnected.ear_decomposition` hands its step the ear's path but **not** the clause
`∀ g ∈ D, g ∉ E(B)` that `Graph.IsTwoConnected.relative_ear_exists` proves and that
`Graph.IsTwoConnected.relative_grows_by_ear` drops. A *geometric* consumer needs it: the ear's
drawing has to miss the drawing of the current subgraph, and an edge shared with `B` would sit
right on it.

It is recoverable, and this section recovers it. An edge of the ear that `B` already has must
join the ear's two ends; the ear is then that single edge, and the enlarged graph is the old
one, so the step has nothing to prove. The integrator may prefer to add the clause to
`relative_grows_by_ear` and to `ear_decomposition` instead — that is the better fix, and it
makes this section unnecessary. -/

/-- **An edge of a path incident to its source is the path's first edge**, in the form that
decomposes the path — `Graph.IsPath.eq_head_of_inc_source` says the same about a list already
known to be a cons, and is what does the work here. -/
theorem IsPath.eq_cons_of_inc_left (h : G.IsPath u D v) (hg : g ∈ D) (hinc : G.Inc g u) :
    ∃ w T, D = g :: T ∧ G.IsLink g u w ∧ G.IsPath w T v := by
  cases D with
  | nil => simp at hg
  | cons a T =>
    obtain rfl : g = a := h.eq_head_of_inc_source hg hinc
    cases h with
    | cons hl hT _ => exact ⟨_, T, rfl, hl, hT⟩

/-- **An edge of an ear that the subgraph already has is the whole ear.** Both ends of such an
edge lie in the subgraph, so the ear's freshness clause makes them the ear's own two ends; the
edge is then the ear's first edge and its far end is the ear's target, so nothing follows it.
-/
theorem IsPath.eq_singleton_of_edge_mem (hBG : B ≤ G) (hpath : G.IsPath u D v) (huv : u ≠ v)
    (hint : ∀ y ∈ G.walkVertices u D, y ≠ u → y ≠ v → y ∉ V(B))
    (hg : g ∈ D) (hgB : g ∈ E(B)) : D = [g] ∧ G.IsLink g u v := by
  -- Both ends of the edge lie in the subgraph, so both are ends of the path.
  have hends : ∀ y, G.Inc g y → y = u ∨ y = v := by
    intro y hy
    by_contra hcon
    push Not at hcon
    exact hint y (mem_walkVertices_of_mem_covered ⟨g, hg, hy⟩) hcon.1 hcon.2
      (mem_vertexSet_of_inc_of_mem_edgeSet hBG hgB hy)
  -- The edge is not a loop, so its two ends are exactly the two ends of the path.
  obtain ⟨p, q, hpq⟩ := exists_isLink_of_mem_edgeSet (hpath.edge_mem hg)
  have hpqne : p ≠ q := by rintro rfl; exact hpath.not_isLoopAt hg p hpq
  have hincu : G.Inc g u := by
    rcases hends p hpq.inc_left with rfl | rfl
    · exact hpq.inc_left
    · rcases hends q hpq.inc_right with rfl | rfl
      · exact hpq.inc_right
      · exact absurd rfl hpqne
  -- So it is the path's first edge, and its far end is the path's target.
  obtain ⟨w, T, rfl, hl, hT⟩ := hpath.eq_cons_of_inc_left hg hincu
  have hwv : w = v := by
    rcases hends w hl.inc_right with rfl | hh
    · exact absurd hl (hpath.not_isLoopAt List.mem_cons_self _)
    · exact hh
  subst hwv
  exact ⟨by rw [hT.eq_nil_of_eq], hl⟩

/-- **Either every edge of the ear is new, or the ear changes nothing.** The disjunction the
step of `Graph.IsTwoConnected.ear_decomposition` has to open before it can do any geometry. -/
theorem ear_edges_notMem_or_union_eq (hBG : B ≤ G) (hpath : G.IsPath u D v) (huv : u ≠ v)
    (hu : u ∈ V(B)) (hv : v ∈ V(B))
    (hint : ∀ y ∈ G.walkVertices u D, y ≠ u → y ≠ v → y ∉ V(B)) :
    (∀ g ∈ D, g ∉ E(B)) ∨ B.union (G.pathGraphOf u D) = B := by
  by_cases hall : ∀ g ∈ D, g ∉ E(B)
  · exact Or.inl hall
  refine Or.inr ?_
  push Not at hall
  obtain ⟨g, hg, hgB⟩ := hall
  obtain ⟨rfl, hl⟩ := hpath.eq_singleton_of_edge_mem hBG huv hint hg hgB
  -- The ear is a single edge the subgraph already carries, joining two of its own vertices.
  refine le_antisymm (union_le le_rfl ?_) (left_le_union _ _)
  refine ⟨fun y hy ↦ ?_, fun f x y hf ↦ ?_⟩
  · rcases mem_walkVertices_iff.1 (pathGraphOf_vertexSet ▸ hy) with rfl | ⟨f, hf, hinc⟩
    · exact hu
    · obtain rfl : f = g := by simpa using hf
      rcases hinc.eq_or_eq_of_isLink hl with rfl | rfl
      exacts [hu, hv]
  · obtain ⟨hfg, hxy, -, -⟩ := pathGraphOf_isLink.1 hf
    obtain rfl : f = g := by simpa using hfg
    exact (hBG.isLink_iff hgB).2 hxy

/-! ## The faces of a graph that grows

Adding an ear removes the ear's own point set from the exterior and changes nothing else. That
is the whole of "all other faces are unchanged", and the half of "its interior is connected and
disjoint from the current graph, so it lies in one current face `F`" that is pure topology. -/

section Plane

open Schoenflies

variable {β : Type*} {G B P : Graph Plane β} {drawing : β → ℝ → Plane} {z a b : Plane}
  {S : Set Plane} {D : List β}

/-- What a union of two plane graphs occupies is what the two of them occupy. -/
@[simp]
theorem pointSet_union (B P : Graph Plane β) (drawing : β → ℝ → Plane) :
    pointSet (B.union P) drawing = pointSet B drawing ∪ pointSet P drawing := by
  simp only [pointSet, vertexSet_union, edgeSet_union, Set.biUnion_union]
  ext w
  simp only [Set.mem_union]
  tauto

/-- Adding a graph removes exactly its own point set from the exterior. -/
theorem exterior_union (B P : Graph Plane β) (drawing : β → ℝ → Plane) :
    exterior (B.union P) drawing = exterior B drawing \ pointSet P drawing := by
  rw [exterior, exterior, pointSet_union, Set.compl_union]
  rfl

/-- A face of the enlarged graph lies inside a face of the old one. -/
theorem face_union_subset : face (B.union P) drawing z ⊆ face B drawing z := by
  by_cases hz : z ∈ exterior (B.union P) drawing
  · refine IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn
      (mem_face hz) fun w hw ↦ ?_
    exact ((exterior_union B P drawing) ▸ face_subset_exterior _ _ _ hw).1
  · rw [face, connectedComponentIn_eq_empty hz]
    exact Set.empty_subset _

/-- **"All other faces are unchanged."** A face the ear does not touch survives the ear. -/
theorem face_union_eq_of_disjoint (hz : z ∈ exterior B drawing)
    (hdis : Disjoint (face B drawing z) (pointSet P drawing)) :
    face (B.union P) drawing z = face B drawing z := by
  refine Set.Subset.antisymm face_union_subset ?_
  refine IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn
    (mem_face hz) fun w hw ↦ ?_
  rw [exterior_union]
  exact ⟨face_subset_exterior _ _ _ hw, fun hwP ↦ Set.disjoint_left.1 hdis hw hwP⟩

/-- **"Its interior is connected and disjoint from the current graph, so it lies in one current
face."** The topological half: a nonempty preconnected subset of the exterior lies in one
face. -/
theorem exists_face_of_isPreconnected (hS : IsPreconnected S) (hSne : S.Nonempty)
    (hsub : S ⊆ exterior B drawing) :
    ∃ z ∈ exterior B drawing, S ⊆ face B drawing z := by
  obtain ⟨z, hz⟩ := hSne
  exact ⟨z, hsub hz, hS.subset_connectedComponentIn hz hsub⟩

/-! ### The ear lies in one face

The blueprint's *"its interior is connected and disjoint from the current graph, so it lies in
one current face `F`"*, in full. -/

/- "An arc without its two endpoints is connected" is
`Schoenflies.IsArcBetween.isConnected_diff`, now in `Schoenflies/Subarc.lean`. -/

/-- **The ear's realisation meets the drawing of the current subgraph only in the ear's two
ends.** Two cases, and both come down to the ear's freshness clause: a point of the ear on a
*vertex* of `B` is an end of the edge of the ear it lies on
(`Graph.IsDrawing.vertex_mem_edgeArc`), and a point of the ear on an *edge* of `B` is a vertex
incident with both (`Graph.IsDrawing.edge_inter`) — the two edges being distinct because no
edge of the ear belongs to `B`. Either way the point is a vertex of `B` that the ear visits,
which the freshness clause makes one of the ear's two ends. -/
theorem IsDrawing.edgesCover_inter_pointSet (hG : IsDrawing G drawing) (hBG : B ≤ G)
    (hpath : G.IsPath a D b)
    (hint : ∀ y ∈ G.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B))
    (hnew : ∀ g ∈ D, g ∉ E(B)) :
    edgesCover drawing D ∩ pointSet B drawing ⊆ {a, b} := by
  -- A vertex of `B` that an edge of the ear is incident with is one of the ear's two ends.
  have key : ∀ p, (∃ f ∈ D, G.Inc f p) → p ∈ V(B) → p = a ∨ p = b := by
    rintro p ⟨f, hf, hinc⟩ hpB
    by_contra hcon
    push Not at hcon
    exact hint p (mem_walkVertices_of_mem_covered ⟨f, hf, hinc⟩) hcon.1 hcon.2 hpB
  rintro p ⟨hpD, hpB⟩
  obtain ⟨f, hf, hpf⟩ := mem_edgesCover_iff.1 hpD
  have hfG : f ∈ E(G) := hpath.edge_mem hf
  rcases hpB with hpV | hpE
  · obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet hfG
    have hinc : G.Inc f p := by
      rcases hG.vertex_mem_edgeArc hxy (hBG.vertexSet_mono hpV) hpf with rfl | rfl
      exacts [hxy.inc_left, hxy.inc_right]
    exact key p ⟨f, hf, hinc⟩ hpV
  · simp only [Set.mem_iUnion, exists_prop] at hpE
    obtain ⟨g, hgB, hpg⟩ := hpE
    have hfg : f ≠ g := fun hh ↦ hnew f hf (hh ▸ hgB)
    obtain ⟨-, hincf, hincg⟩ := hG.edge_inter hfG (hBG.edgeSet_mono hgB) hfg hpf hpg
    exact key p ⟨f, hf, hincf⟩ (mem_vertexSet_of_inc_of_mem_edgeSet hBG hgB hincg)

/-- **"Its interior is connected and disjoint from the current graph, so it lies in one current
face `F`."** The ear's realisation without its two ends is an arc's interior, hence connected,
and it misses the drawing of `B` altogether, so it lies in a single face. -/
theorem IsDrawing.exists_face_of_ear (hG : IsDrawing G drawing) (hBG : B ≤ G)
    (hpath : G.IsPath a D b) (hab : a ≠ b)
    (hint : ∀ y ∈ G.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B))
    (hnew : ∀ g ∈ D, g ∉ E(B)) :
    ∃ z ∈ exterior B drawing, edgesCover drawing D \ {a, b} ⊆ face B drawing z := by
  have harc : IsArcBetween (edgesCover drawing D) a b :=
    hG.path_isArcBetween hpath (hpath.ne_nil hab)
  have hconn := harc.isConnected_diff
  refine exists_face_of_isPreconnected hconn.isPreconnected hconn.nonempty fun w hw hwB ↦ ?_
  exact hw.2 (hG.edgesCover_inter_pointSet hBG hpath hint hnew ⟨hw.1, hwB⟩)

/-! ### A subgraph of a plane graph is a plane graph

The induction speaks of the faces of the *current* subgraph, so every step needs the current
subgraph to be a plane graph in its own right. Nothing has to be redrawn: the same drawing
serves. General, and not in `Schoenflies/Graph/Drawing.lean`; the integrator may want to hoist
it. -/

/-- **A subgraph of a plane graph is a plane graph**, with the same drawing. -/
theorem IsDrawing.mono (hG : IsDrawing G drawing) (hBG : B ≤ G) : IsDrawing B drawing where
  edge_param := fun e he ↦ by
    obtain ⟨hc, hi, hl⟩ := hG.edge_param (hBG.edgeSet_mono he)
    exact ⟨hc, hi, (hBG.isLink_iff he).2 hl⟩
  vertex_mem_edgeArc := fun _ _ _ _ hl hv hmem ↦
    hG.vertex_mem_edgeArc (hl.mono hBG) (hBG.vertexSet_mono hv) hmem
  edge_inter := fun e f he hf hef p hpe hpf ↦ by
    obtain ⟨-, hince, hincf⟩ :=
      hG.edge_inter (hBG.edgeSet_mono he) (hBG.edgeSet_mono hf) hef hpe hpf
    obtain ⟨y, hy⟩ := hince
    obtain ⟨y', hy'⟩ := hincf
    exact ⟨mem_vertexSet_of_inc_of_mem_edgeSet hBG he ⟨y, hy⟩,
      ⟨y, (hBG.isLink_iff he).2 hy⟩, ⟨y', (hBG.isLink_iff hf).2 hy'⟩⟩

/-! ### The ear's ends lie on the boundary of the face its interior lies in -/

/- "An endpoint of an arc is a limit of the arc's interior" is
`Schoenflies.IsArcBetween.left_mem_closure_diff` / `…right_mem_closure_diff`, hoisted into
`Schoenflies/Subarc.lean` alongside `…isConnected_diff`. This module had its own copy, with the
same statement as the one in `Schoenflies/AlternatingCrosscuts.lean`; the two modules do not
import each other, so the build accepted both. -/

/-- **"The ear's two endpoints are limits of its interior, which lies in `F`, so they lie on
`∂F`."** This is the hypothesis `thm:polygonal-crosscut` needs of a crosscut: its two ends are
on the boundary curve of the region it cuts. -/
theorem IsDrawing.ends_mem_frontier_face (hG : IsDrawing G drawing)
    (hopen : IsOpen (face B drawing z)) (hpath : G.IsPath a D b) (hab : a ≠ b)
    (ha : a ∈ V(B)) (hb : b ∈ V(B))
    (hsub : edgesCover drawing D \ {a, b} ⊆ face B drawing z) :
    a ∈ frontier (face B drawing z) ∧ b ∈ frontier (face B drawing z) := by
  have harc : IsArcBetween (edgesCover drawing D) a b :=
    hG.path_isArcBetween hpath (hpath.ne_nil hab)
  have hnot : ∀ y ∈ V(B), y ∉ face B drawing z := fun y hy hyf ↦
    face_subset_exterior _ _ _ hyf (vertexSet_subset_pointSet hy)
  refine ⟨⟨closure_mono hsub harc.left_mem_closure_diff, ?_⟩,
    ⟨closure_mono hsub harc.right_mem_closure_diff, ?_⟩⟩
  · rw [hopen.interior_eq]; exact hnot a ha
  · rw [hopen.interior_eq]; exact hnot b hb

end Plane

end Graph

end BundlePart395

section BundlePart396
/- Source: dev/planar_search/schoenflies_port/Schoenflies/SegmentCut.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/


/-!
# Cutting a segment

Mathlib has no lemma splitting a segment at an interior point, and the polygonal subdivision
of Layer 6 is built entirely out of one: cutting loses nothing (`segment_split`) and cutting
is permanent (`openSegment_left_subset`, `openSegment_right_subset` — each half's interior
stays inside the whole's, so nothing later can put a removed point back into an interior).

Everything here is an identity between convex combinations. The `⊇` half of the split is
convexity; the `⊆` half rescales the parameter, and the only case analysis is on whether the
far coefficient vanishes.

## Blueprint

* `segment_split` — cutting at a point of the segment loses nothing; underneath
  `subdivide_covers`.
* `openSegment_left_subset`, `openSegment_right_subset` — a cut is permanent; underneath
  `subdivide_inside`.
-/

open Set

namespace Schoenflies

variable {a b p : Plane}

/-- Cutting a segment at one of its points loses nothing: the two halves cover it. -/
theorem segment_split (hp : p ∈ segment ℝ a b) :
    segment ℝ a b = segment ℝ a p ∪ segment ℝ p b := by
  refine subset_antisymm ?_ (union_subset
    ((convex_segment a b).segment_subset (left_mem_segment ℝ a b) hp)
    ((convex_segment a b).segment_subset hp (right_mem_segment ℝ a b)))
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hp
  rintro x ⟨u, v, hu, hv, huv, rfl⟩
  rcases le_or_gt v β with hvβ | hvβ
  · -- `x` lies on the near half. Rescale `v` by `β`, unless `β = 0`, when the cut is at `a`.
    left
    rcases eq_or_lt_of_le hβ with rfl | hβpos
    · have hv0 : v = 0 := le_antisymm hvβ hv
      have hu1 : u = 1 := by linarith
      subst hv0; subst hu1
      simp only [zero_smul, add_zero, one_smul]
      exact left_mem_segment ℝ a _
    · refine ⟨1 - v / β, v / β, by
        rw [sub_nonneg]
        exact div_le_one_of_le₀ hvβ hβpos.le, by positivity, by ring, ?_⟩
      have hβne : β ≠ 0 := ne_of_gt hβpos
      have hvβ' : v / β * β = v := div_mul_cancel₀ v hβne
      have hcoef : (1 - v / β) + (v / β) * α = u := by
        have hα' : α = 1 - β := by linarith
        calc (1 - v / β) + (v / β) * α
            = (1 - v / β) + (v / β) * (1 - β) := by rw [hα']
          _ = 1 - v / β * β := by ring
          _ = 1 - v := by rw [hvβ']
          _ = u := by linarith
      rw [smul_add, smul_smul, smul_smul, ← add_assoc, ← add_smul, hcoef, hvβ']
  · -- `x` lies on the far half. Rescale `u` by `α`, which is positive because `v > β`.
    right
    have hαpos : 0 < α := by linarith
    have hαne : α ≠ 0 := ne_of_gt hαpos
    have huα : u ≤ α := by linarith
    refine ⟨u / α, 1 - u / α, by positivity, by
      rw [sub_nonneg]
      exact div_le_one_of_le₀ huα hαpos.le, by ring, ?_⟩
    have huα' : u / α * α = u := div_mul_cancel₀ u hαne
    have hcoef : (u / α) * β + (1 - u / α) = v := by
      have hβ' : β = 1 - α := by linarith
      calc (u / α) * β + (1 - u / α)
          = (u / α) * (1 - α) + (1 - u / α) := by rw [hβ']
        _ = 1 - u / α * α := by ring
        _ = 1 - u := by rw [huα']
        _ = v := by linarith
    rw [smul_add, smul_smul, smul_smul, add_assoc, ← add_smul, hcoef, huα']

/-- Cutting is permanent, near half: the interior of the near piece stays inside the
interior of the whole. -/
theorem openSegment_left_subset (hp : p ∈ openSegment ℝ a b) :
    openSegment ℝ a p ⊆ openSegment ℝ a b := by
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hp
  rintro x ⟨s, t, hs, ht, hst, rfl⟩
  refine ⟨s + t * α, t * β, by positivity, by positivity, by nlinarith, ?_⟩
  rw [smul_add, smul_smul, smul_smul, ← add_assoc, ← add_smul]

/-- Cutting is permanent, far half. -/
theorem openSegment_right_subset (hp : p ∈ openSegment ℝ a b) :
    openSegment ℝ p b ⊆ openSegment ℝ a b := by
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hp
  rintro x ⟨s, t, hs, ht, hst, rfl⟩
  refine ⟨s * α, s * β + t, by positivity, by positivity, by nlinarith, ?_⟩
  rw [smul_add, smul_smul, smul_smul, add_assoc, ← add_smul]

end Schoenflies

end BundlePart396
