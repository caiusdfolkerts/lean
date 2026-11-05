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

public import verified.parts.part037
import all verified.parts.part037

@[expose] public section

set_option debug.skipKernelTC false
set_option linter.all false
set_option Elab.async false
set_option internal.cmdlineSnapshots true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

section BundlePart418
/- Source: dev/planar_search/schoenflies_port/Schoenflies/PrePolygonArc.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/


/-!
# The arcs of a `PrePolygon`, and inserting a vertex

`Schoenflies.PrePolygon` is `Schoenflies.ClosedPolygon` without the `corner` field, so its
vertices may sit anywhere on the curve. This module carries §1 and §2 of the blueprint for such
a presentation: the edge list of an arc, the arc as a set, the two arcs of a splitting, and the
construction that makes the whole thing worth having — a prescribed point of the curve can be
made a vertex.

Everything below is the `Schoenflies.ClosedPolygon` development of
`Schoenflies/PolygonBridge.lean`, `Schoenflies/ParitySplitting.lean`,
`Schoenflies/PolygonalCrosscut.lean` and `Schoenflies/Realization.lean` with the structure
changed; every proof uses only `vertex_inj` and `edges_meet`, and `corner` is never mentioned.

## Why this module exists

`Schoenflies/Graph/K33Land.lean` and `Schoenflies/FaceCyclesLand.lean` each needed the same
apparatus and each transcribed it, the second under an `FC` suffix. The two copies were not
alpha-equivalent — `insertLast` in particular carried an extra hypothesis in one of them — so
the import checker never complained, and there were two of everything. This module is the
single copy; both consumers import it.

The one signature that genuinely differed is `Schoenflies.PrePolygon.insertLast`. The
`FaceCyclesLand` copy took, besides `hz : z ∈ openSegment ℝ (P.vertex (-1)) (P.vertex 0)`, a
hypothesis `∀ j, P.vertex j ≠ z` saying the new point is not already a vertex. That is not an
extra assumption but a consequence: `Schoenflies.PrePolygon.vertex_ne_of_mem_openSegment`
derives it from `hz`. The general form — the one with `hz` alone — is what survives here.

## Inserting a vertex, and why it is the crux

`Schoenflies.PrePolygon.deleteLast` removes a vertex at which the curve runs straight (the
blueprint's Lemma 1.8); `Schoenflies.PrePolygon.insertLast` is the inverse move, and it is the
reason `PrePolygon` is the right structure for a consumer that needs named points to be
vertices. The vertex is inserted at the end of the list, interior to the last edge, so that the
only edge that changes is the last one, which splits in two;
`Schoenflies.PrePolygon.rotate` brings any edge there. Simplicity survives because the far end
of the split edge lies on neither half.

## Blueprint

* `Schoenflies.PrePolygon.vertex_natCast_ne`, `…edge_meet_earlier` — the elementary simplicity
  facts, §1.
* `Schoenflies.PrePolygon.chain`, `…mem_chain_iff`, `…isArcBetween_chain` — the union of the
  first `k` edges, and that it is an arc.
* `Schoenflies.PrePolygon.arcPieces`, `…arcPieces_add`, `…arcPieces_full`,
  `…isChainFrom_arcPieces`, `…arcPieces_split_perm`, `…sameEdges_arcPieces_split`,
  `…parity_splitting` — the edge list of an arc, and Lemma 2.7 for it.
* `Schoenflies.PrePolygon.arc`, `…arc_union`, `…arc_inter`, `…isArcBetween_arc`,
  `…arc_not_subset_endpoints`, `…isCompact_arc` — the two arcs of a splitting, §2.
* `Schoenflies.PrePolygon.parity_ne_iff_mem_farRegion` — `thm:polygonal-jordan` read as a
  separation criterion.
* `Schoenflies.PrePolygon.arcList`, `…poly_arcList`, `…isPolygonal_arc` — an arc as a polyline,
  which is how it is glued to a crosscut.
* `Schoenflies.segment_halves_inter`, `Schoenflies.right_notMem_left_half`,
  `Schoenflies.left_notMem_right_half` — §1: cutting a segment at an interior point, in order.
  General-purpose; they belong beside `Schoenflies.segment_split` in `Schoenflies/SegmentCut.lean`.
* `Schoenflies.PrePolygon.insertLast`, `…carrier_insertLast`,
  `Schoenflies.PrePolygon.exists_prePolygon_insert`, `…exists_prePolygon_vertices` — the inverse
  of the blueprint's "delete redundant vertices" (Lemma 1.8): *insert* one, anywhere on the curve.
* `Schoenflies.exists_prePolygon_points`, `…exists_prePolygon_split` — §1, the realization
  theorem **with the cut points anywhere on the curve**. Compare
  `Schoenflies.exists_closedPolygon_split`, which requires them to be corners.
-/

open Bornology Metric Set

namespace Schoenflies

open Plane

namespace PrePolygon

variable {m : ℕ} {P : PrePolygon m} {a : ZMod (m + 3)} {k : ℕ} {u : Plane}

/-! ## Indices, edges and the elementary simplicity facts

Verbatim the `Schoenflies.ClosedPolygon` facts of `Schoenflies/PolygonBridge.lean` whose proofs
use only `vertex_inj` and `edges_meet`. -/

/-- Distinct indices below the modulus name distinct vertices. -/
theorem vertex_natCast_ne {j l : ℕ} (hj : j < m + 3) (hl : l < m + 3) (hjl : j ≠ l) :
    P.vertex (j : ZMod (m + 3)) ≠ P.vertex (l : ZMod (m + 3)) :=
  fun heq => hjl (ClosedPolygon.natCast_inj hj hl (P.vertex_inj heq))

/-- **An edge meets an earlier edge only at its own initial vertex.** -/
theorem edge_meet_earlier {j l : ℕ} (hjl : j < l) (hl : l + 1 < m + 3) {z : Plane}
    (hzj : z ∈ P.edge (j : ZMod (m + 3))) (hzl : z ∈ P.edge (l : ZMod (m + 3))) :
    z = P.vertex (l : ZMod (m + 3)) := by
  have hjn : j < m + 3 := by omega
  have hln : l < m + 3 := by omega
  have hne : (l : ZMod (m + 3)) ≠ (j : ZMod (m + 3)) :=
    fun heq => (by omega : l ≠ j) (ClosedPolygon.natCast_inj hln hjn heq)
  have hmem := P.edges_meet _ _ hne (Set.mem_inter hzl hzj)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with hmem | hmem
  · exact hmem
  exfalso
  have hmem2 := P.edges_meet _ _ (Ne.symm hne) (Set.mem_inter hzj hzl)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem2
  rw [← ClosedPolygon.natCast_succ] at hmem
  rcases hmem2 with hmem2 | hmem2
  · have : l + 1 = j := ClosedPolygon.natCast_inj hl hjn (P.vertex_inj (hmem ▸ hmem2))
    omega
  · rw [← ClosedPolygon.natCast_succ] at hmem2
    have : l + 1 = j + 1 :=
      ClosedPolygon.natCast_inj hl (by omega) (P.vertex_inj (hmem ▸ hmem2))
    omega

/-! ## The chain of the first `k` edges, and that it is an arc -/

/-- The union of the edges leaving vertices `0, 1, …, k`. -/
def chain (P : PrePolygon m) : ℕ → Set Plane
  | 0 => P.edge 0
  | k + 1 => chain P k ∪ P.edge ((k + 1 : ℕ) : ZMod (m + 3))

theorem mem_chain_iff {z : Plane} : z ∈ P.chain k ↔ ∃ j ≤ k, z ∈ P.edge (j : ZMod (m + 3)) := by
  induction k with
  | zero =>
    constructor
    · intro hz
      exact ⟨0, le_rfl, by simpa [chain] using hz⟩
    · rintro ⟨j, hj, hzj⟩
      obtain rfl : j = 0 := Nat.le_zero.1 hj
      simpa [chain] using hzj
  | succ k ih =>
    simp only [chain, Set.mem_union]
    constructor
    · rintro (hz | hz)
      · obtain ⟨j, hj, hzj⟩ := ih.1 hz
        exact ⟨j, le_trans hj (Nat.le_succ k), hzj⟩
      · exact ⟨k + 1, le_rfl, hz⟩
    · rintro ⟨j, hj, hzj⟩
      rcases Nat.lt_or_ge j (k + 1) with hlt | hge
      · exact Or.inl (ih.2 ⟨j, Nat.lt_succ_iff.1 hlt, hzj⟩)
      · obtain rfl : j = k + 1 := le_antisymm hj hge
        exact Or.inr hzj

/-- **The partial chains are arcs.** One edge at a time, glued at the vertex they share. -/
theorem isArcBetween_chain (P : PrePolygon m) :
    ∀ k : ℕ, k + 1 < m + 3 →
      IsArcBetween (P.chain k) (P.vertex 0) (P.vertex ((k + 1 : ℕ) : ZMod (m + 3))) := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [ClosedPolygon.natCast_succ]
    exact isArcBetween_segment (vertex_ne_succ 0)
  | succ k ih =>
    intro hk
    have hA := ih (by omega)
    have hB : IsArcBetween (P.edge ((k + 1 : ℕ) : ZMod (m + 3)))
        (P.vertex ((k + 1 : ℕ) : ZMod (m + 3)))
        (P.vertex ((k + 1 + 1 : ℕ) : ZMod (m + 3))) := by
      rw [ClosedPolygon.natCast_succ (k + 1)]
      exact isArcBetween_segment (vertex_ne_succ _)
    have hmeet : ∀ z ∈ P.chain k, z ∈ P.edge ((k + 1 : ℕ) : ZMod (m + 3)) →
        z = P.vertex ((k + 1 : ℕ) : ZMod (m + 3)) := by
      intro z hz hze
      obtain ⟨j, hj, hzj⟩ := mem_chain_iff.1 hz
      exact edge_meet_earlier (by omega) (by omega) hzj hze
    exact hA.concatenate hB hmeet

/-! ## The edge list of an arc

`Schoenflies.ClosedPolygon.arcPieces` with the structure changed; every proof below uses only
`vertex_inj` and `edges_meet`, so it is the old proof verbatim. -/

/-- The edge list of the arc of `P` that leaves vertex `a` and runs forward through `k` edges. -/
def arcPieces (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) : List Piece :=
  (List.range k).map fun t : ℕ => (P.vertex (a + t), P.vertex (a + t + 1))

/-- Forgetting the `corner` field does not change the edge list of an arc. -/
@[simp] theorem arcPieces_toPre (C : ClosedPolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    C.toPre.arcPieces a k = C.arcPieces a k := rfl

@[simp] theorem arcPieces_zero (P : PrePolygon m) (a : ZMod (m + 3)) : P.arcPieces a 0 = [] := rfl

/-- Running through `k + l` edges is running through `k` and then through `l`. -/
theorem arcPieces_add (P : PrePolygon m) (a : ZMod (m + 3)) (k l : ℕ) :
    P.arcPieces a (k + l) = P.arcPieces a k ++ P.arcPieces (a + k) l := by
  rw [arcPieces, arcPieces, arcPieces, List.range_add, List.map_append, List.map_map]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  simp only [Function.comp_apply, Nat.cast_add, ← add_assoc]

/-- Running through all `m + 3` edges from vertex `0` is the whole edge list. -/
theorem arcPieces_full (P : PrePolygon m) : P.arcPieces 0 (m + 3) = P.pieces := by
  rw [arcPieces, pieces]
  exact List.map_congr_left fun t _ => by rw [zero_add]

/-- Every edge of an arc is an edge of the polygon. -/
theorem mem_pieces_of_mem_arcPieces {Q : Piece} (hQ : Q ∈ P.arcPieces a k) : Q ∈ P.pieces := by
  obtain ⟨t, -, rfl⟩ := List.mem_map.1 hQ
  exact P.mem_pieces _

theorem arcPieces_nondeg (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    ∀ Q ∈ P.arcPieces a k, Q.Nondeg :=
  fun _ hQ => P.pieces_nondeg _ (mem_pieces_of_mem_arcPieces hQ)

theorem arcPieces_hgt_ne (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) :
    ∀ Q ∈ P.arcPieces a k, hgt u Q.1 ≠ hgt u Q.2 :=
  fun _ hQ => hL _ (mem_pieces_of_mem_arcPieces hQ)

/-- **An arc is a chain from its first vertex to its last.** -/
theorem isChainFrom_arcPieces (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    IsChainFrom (P.arcPieces a k) (P.vertex a) (P.vertex (a + k)) := by
  intro f
  have hmap : ((P.arcPieces a k).map fun Q => f Q.1 + f Q.2)
      = (List.range k).map fun j : ℕ =>
          f (P.vertex (a + (j : ZMod (m + 3))))
            + f (P.vertex (a + ((j + 1 : ℕ) : ZMod (m + 3)))) := by
    rw [arcPieces, List.map_map]
    refine List.map_congr_left fun t _ => ?_
    simp only [Function.comp_apply, ClosedPolygon.natCast_succ, ← add_assoc]
  have key := sum_range_boundary (fun i : ℕ => f (P.vertex (a + (i : ZMod (m + 3))))) k
  rw [hmap, key]
  simp

/-- **The two arcs from a vertex use every edge exactly once.** -/
theorem arcPieces_full_perm (P : PrePolygon m) (a : ZMod (m + 3)) :
    (P.arcPieces a (m + 3)).Perm P.pieces := by
  have hlt : a.val < m + 3 := ZMod.val_lt a
  have hcast : ((a.val : ℕ) : ZMod (m + 3)) = a := ZMod.natCast_rightInverse a
  have hzero : a + ((m + 3 - a.val : ℕ) : ZMod (m + 3)) = 0 := by
    rw [Nat.cast_sub hlt.le, hcast]
    simp
  have hsplit1 : P.arcPieces a (m + 3)
      = P.arcPieces a (m + 3 - a.val) ++ P.arcPieces 0 a.val := by
    have h1 : (m + 3 - a.val) + a.val = m + 3 := by omega
    have h2 := arcPieces_add P a (m + 3 - a.val) a.val
    rwa [h1, hzero] at h2
  have hsplit2 : P.pieces = P.arcPieces 0 a.val ++ P.arcPieces a (m + 3 - a.val) := by
    have h1 : a.val + (m + 3 - a.val) = m + 3 := by omega
    have h2 := arcPieces_add P 0 a.val (m + 3 - a.val)
    rw [h1, arcPieces_full, zero_add, hcast] at h2
    exact h2
  rw [hsplit1, hsplit2]
  exact List.perm_append_comm

/-- **The split.** For `k ≤ m + 3` the two arcs at `a` and `a + k` between them use every edge
of `P` exactly once. -/
theorem arcPieces_split_perm (P : PrePolygon m) (a : ZMod (m + 3)) (hk : k ≤ m + 3) :
    (P.arcPieces a k ++ P.arcPieces (a + k) (m + 3 - k)).Perm P.pieces := by
  rw [← arcPieces_add, Nat.add_sub_cancel' hk]
  exact arcPieces_full_perm P a

theorem sameEdges_arcPieces_split (P : PrePolygon m) (a : ZMod (m + 3)) (hk : k ≤ m + 3) :
    SameEdges P.pieces (P.arcPieces a k ++ P.arcPieces (a + k) (m + 3 - k)) :=
  SameEdges.of_perm (arcPieces_split_perm P a hk).symm

/-- The two arcs between them carry the polygon. -/
theorem cover_arcPieces_union (P : PrePolygon m) (a : ZMod (m + 3)) (hk : k ≤ m + 3) :
    cover (P.arcPieces a k) ∪ cover (P.arcPieces (a + k) (m + 3 - k)) = P.carrier := by
  rw [← cover_append, cover_perm (arcPieces_split_perm P a hk), cover_pieces]

theorem cover_arcPieces_subset (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    cover (P.arcPieces a k) ⊆ P.carrier := by
  intro z hz
  obtain ⟨R, hR, hzR⟩ := ClosedPolygon.exists_of_mem_cover hz
  rw [← cover_pieces]
  exact mem_cover (mem_pieces_of_mem_arcPieces hR) hzR

theorem arcPieces_append_hgt_ne {K : List Piece}
    (hC : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) (hK : ∀ Q ∈ K, hgt u Q.1 ≠ hgt u Q.2) :
    ∀ Q ∈ P.arcPieces a k ++ K, hgt u Q.1 ≠ hgt u Q.2 :=
  hgt_ne_append (arcPieces_hgt_ne hC) hK

/-- **A curve of the split occupies its arc together with the crosscut.** -/
theorem carrier_eq_of_sameEdges {m' : ℕ} {J : PrePolygon m'} {K : List Piece}
    (h : SameEdges J.pieces (P.arcPieces a k ++ K)) :
    J.carrier = cover (P.arcPieces a k) ∪ cover K := by
  rw [← cover_pieces, h.cover_eq, cover_append]

/-- A point off `P` and off the crosscut is off `J`. -/
theorem notMem_carrier_of_sameEdges {m' : ℕ} {J : PrePolygon m'} {K : List Piece}
    (h : SameEdges J.pieces (P.arcPieces a k ++ K)) {x : Plane} (hxC : x ∉ P.carrier)
    (hxK : x ∉ cover K) : x ∉ J.carrier := by
  rw [carrier_eq_of_sameEdges h]
  rintro (hx | hx)
  · exact hxC (cover_arcPieces_subset P a k hx)
  · exact hxK hx

/-- **Parity splitting** (Lemma 2.7) for a polygon presented with redundant vertices. -/
theorem parity_splitting (P : PrePolygon m) (u : Plane) (a : ZMod (m + 3)) (hk : k ≤ m + 3)
    {L₁ L₂ K : List Piece} (h₁ : SameEdges L₁ (P.arcPieces a k ++ K))
    (h₂ : SameEdges L₂ (P.arcPieces (a + k) (m + 3 - k) ++ K)) (q : Plane) :
    parity u L₁ q + parity u L₂ q = parity u P.pieces q :=
  parity_split u (sameEdges_arcPieces_split P a hk) h₁ h₂ q

/-! ## The arcs as sets -/

/-- The arc of `P` that leaves vertex `a` and runs forward through `k` edges, as a set. -/
def arc (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) : Set Plane := cover (P.arcPieces a k)

@[simp] theorem arc_toPre (C : ClosedPolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    C.toPre.arc a k = C.arc a k := rfl

theorem arc_subset_carrier (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    P.arc a k ⊆ P.carrier := cover_arcPieces_subset P a k

theorem arc_union (P : PrePolygon m) (a : ZMod (m + 3)) (hk : k ≤ m + 3) :
    P.arc a k ∪ P.arc (a + k) (m + 3 - k) = P.carrier := cover_arcPieces_union P a hk

/-- An arc is compact: it is a finite union of segments. -/
theorem isCompact_arc (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) : IsCompact (P.arc a k) :=
  isCompact_cover _

theorem mem_arc_iff {z : Plane} :
    z ∈ P.arc a k ↔ ∃ t < k, z ∈ P.edge (a + (t : ZMod (m + 3))) := by
  constructor
  · intro hz
    obtain ⟨R, hR, hzR⟩ := ClosedPolygon.exists_of_mem_cover hz
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hR
    exact ⟨t, List.mem_range.1 ht, hzR⟩
  · rintro ⟨t, ht, hz⟩
    exact mem_cover (List.mem_map.2 ⟨t, List.mem_range.2 ht, rfl⟩) hz

/-- The first vertex of a nonempty arc lies on it. -/
theorem vertex_mem_arc (P : PrePolygon m) (a : ZMod (m + 3)) (hk : 1 ≤ k) :
    P.vertex a ∈ P.arc a k := by
  refine mem_arc_iff.2 ⟨0, hk, ?_⟩
  rw [Nat.cast_zero, add_zero, edge]
  exact left_mem_segment ℝ _ _

/-- The last vertex of a nonempty arc lies on it. -/
theorem vertex_add_mem_arc (P : PrePolygon m) (a : ZMod (m + 3)) (hk : 1 ≤ k) :
    P.vertex (a + k) ∈ P.arc a k := by
  have hlast : a + ((k - 1 : ℕ) : ZMod (m + 3)) + 1 = a + (k : ZMod (m + 3)) := by
    have h : ((k - 1 : ℕ) : ZMod (m + 3)) + 1 = ((k : ℕ) : ZMod (m + 3)) := by
      rw [show ((k : ℕ) : ZMod (m + 3)) = (((k - 1) + 1 : ℕ) : ZMod (m + 3)) by
        congr 1; omega, Nat.cast_add, Nat.cast_one]
    rw [add_assoc, h]
  refine mem_arc_iff.2 ⟨k - 1, by omega, ?_⟩
  rw [edge, hlast]
  exact right_mem_segment ℝ _ _

/-- **The two cut vertices lie on both arcs.** -/
theorem endpoints_subset_arc (P : PrePolygon m) (a : ZMod (m + 3)) (hk : 1 ≤ k) :
    ({P.vertex a, P.vertex (a + k)} : Set Plane) ⊆ P.arc a k := by
  rintro w (rfl | rfl)
  · exact P.vertex_mem_arc a hk
  · exact P.vertex_add_mem_arc a hk

theorem endpoints_subset_arc' (P : PrePolygon m) (a : ZMod (m + 3)) (hk2 : k ≤ m + 2) :
    ({P.vertex a, P.vertex (a + k)} : Set Plane) ⊆ P.arc (a + k) (m + 3 - k) := by
  have hpos : 1 ≤ m + 3 - k := by omega
  have hwrap := zmod_add_sub_cancel (k := k) (by omega) a
  rintro w (rfl | rfl)
  · have hm := P.vertex_add_mem_arc (a + k) hpos
    rwa [hwrap] at hm
  · exact P.vertex_mem_arc (a + k) hpos

/-- Distinct index numerals below the modulus name distinct vertices, after any shift. -/
theorem natCast_shift_inj (P : PrePolygon m) (a : ZMod (m + 3)) {x z : ℕ} (hx : x < m + 3)
    (hz : z < m + 3) (he : P.vertex (a + (x : ZMod (m + 3))) = P.vertex (a + (z : ZMod (m + 3)))) :
    x = z :=
  ClosedPolygon.natCast_inj hx hz (add_left_cancel (P.vertex_inj he))

/-- An arc of `P` is a chain of the polygon read from its first vertex. -/
theorem arc_eq_chain (P : PrePolygon m) (a : ZMod (m + 3)) (hk : 1 ≤ k) :
    P.arc a k = (P.rotate a).chain (k - 1) := by
  have hedge : ∀ j : ZMod (m + 3), (P.rotate a).edge j = P.edge (a + j) := by
    intro j
    rw [edge, edge, rotate_vertex, rotate_vertex, show a + (j + 1) = a + j + 1 by ring]
  ext z
  rw [mem_arc_iff, mem_chain_iff]
  constructor
  · rintro ⟨t, ht, hz⟩
    exact ⟨t, by omega, by rw [hedge]; exact hz⟩
  · rintro ⟨j, hj, hz⟩
    rw [hedge] at hz
    exact ⟨j, by omega, hz⟩

/-- **An arc of a splitting is an arc between the two cut vertices.** -/
theorem isArcBetween_arc (P : PrePolygon m) (a : ZMod (m + 3)) (hk1 : 1 ≤ k)
    (hk2 : k ≤ m + 2) : IsArcBetween (P.arc a k) (P.vertex a) (P.vertex (a + k)) := by
  have h := (P.rotate a).isArcBetween_chain (k - 1) (by omega)
  rw [← arc_eq_chain P a hk1, show ((k - 1 + 1 : ℕ) : ZMod (m + 3)) = (k : ZMod (m + 3)) by
    congr 1; omega] at h
  simpa using h

/-- **The two arcs of a splitting meet exactly at the two cut vertices.** -/
theorem arc_inter (P : PrePolygon m) (a : ZMod (m + 3)) (hk1 : 1 ≤ k) (hk2 : k ≤ m + 2) :
    P.arc a k ∩ P.arc (a + k) (m + 3 - k) = {P.vertex a, P.vertex (a + k)} := by
  refine Set.Subset.antisymm ?_ (Set.subset_inter (P.endpoints_subset_arc a hk1)
    (P.endpoints_subset_arc' a hk2))
  rintro z ⟨hz1, hz2⟩
  obtain ⟨s, hs, hzs⟩ := mem_arc_iff.1 hz1
  obtain ⟨t, ht, hzt⟩ := mem_arc_iff.1 hz2
  have hkt : k + t < m + 3 := by omega
  rw [show a + (k : ZMod (m + 3)) + (t : ZMod (m + 3)) = a + ((k + t : ℕ) : ZMod (m + 3)) by
    push_cast; ring] at hzt
  have hij : a + (s : ZMod (m + 3)) ≠ a + ((k + t : ℕ) : ZMod (m + 3)) := fun he =>
    absurd (ClosedPolygon.natCast_inj (by omega) hkt (add_left_cancel he)) (by omega)
  have hsucc₁ : a + (s : ZMod (m + 3)) + 1 = a + ((s + 1 : ℕ) : ZMod (m + 3)) := by
    push_cast; ring
  have hsucc₂ : a + ((k + t : ℕ) : ZMod (m + 3)) + 1 = a + ((k + t + 1 : ℕ) : ZMod (m + 3)) := by
    push_cast; ring
  have hA := P.edges_meet _ _ hij (Set.mem_inter hzs hzt)
  have hB := P.edges_meet _ _ (Ne.symm hij) (Set.mem_inter hzt hzs)
  rw [hsucc₁] at hA
  rw [hsucc₂] at hB
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA hB ⊢
  have hzero : k + t + 1 = m + 3 →
      ((k + t + 1 : ℕ) : ZMod (m + 3)) = ((0 : ℕ) : ZMod (m + 3)) := by
    intro he
    rw [he, Nat.cast_zero, ZMod.natCast_self]
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · exact absurd (hA.symm.trans hB) fun he => hij (P.vertex_inj he)
  · rcases Nat.lt_or_ge (k + t + 1) (m + 3) with hlt | hge
    · exact absurd (P.natCast_shift_inj a (by omega) hlt (hA.symm.trans hB)) (by omega)
    · have he : k + t + 1 = m + 3 := by omega
      have hs0 : s = 0 := P.natCast_shift_inj a (by omega) (by omega)
        ((hA.symm.trans hB).trans (by rw [hzero he]))
      exact Or.inl (by rw [hA, hs0, Nat.cast_zero, add_zero])
  · have hst : s + 1 = k + t := P.natCast_shift_inj a (by omega) hkt (hA.symm.trans hB)
    exact Or.inr (by rw [hA, show s + 1 = k by omega])
  · exfalso
    rcases Nat.lt_or_ge (k + t + 1) (m + 3) with hlt | hge
    · exact absurd (P.natCast_shift_inj a (by omega) hlt (hA.symm.trans hB)) (by omega)
    · have he : k + t + 1 = m + 3 := by omega
      have := P.natCast_shift_inj a (show s + 1 < m + 3 by omega) (show 0 < m + 3 by omega)
        ((hA.symm.trans hB).trans (by rw [hzero he]))
      omega

/-- An interior point of the first edge of an arc: a point of the arc that is neither cut
vertex, which is what says the arc is more than its two ends. -/
theorem arc_not_subset_endpoints (P : PrePolygon m) (a : ZMod (m + 3)) (hk1 : 1 ≤ k)
    (hk2 : k ≤ m + 2) : ¬ P.arc a k ⊆ ({P.vertex a, P.vertex (a + k)} : Set Plane) := by
  intro hsub
  set x : Plane := (1 / 2 : ℝ) • P.vertex a + (1 / 2 : ℝ) • P.vertex (a + 1) with hxdef
  have hxo : x ∈ openSegment ℝ (P.vertex a) (P.vertex (a + 1)) :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  have hxarc : x ∈ P.arc a k :=
    mem_arc_iff.2 ⟨0, hk1, by
      rw [Nat.cast_zero, add_zero]; exact openSegment_subset_segment ℝ _ _ hxo⟩
  have hkne : (k : ZMod (m + 3)) ≠ 0 := by
    intro he
    have h0 : ((k : ℕ) : ZMod (m + 3)) = ((0 : ℕ) : ZMod (m + 3)) := by rw [he, Nat.cast_zero]
    have hk0 := ClosedPolygon.natCast_inj (m := m) (show k < m + 3 by omega)
      (show 0 < m + 3 by omega) h0
    omega
  rcases hsub hxarc with h | h
  · exact P.vertex_ne_succ a (left_mem_openSegment_iff.1 (h ▸ hxo))
  · refine notMem_edge_of_mem_openSegment (P := P) (i := a) (j := a + k)
      (fun he => hkne (by linear_combination he)) hxo ?_
    rw [edge, h]
    exact left_mem_segment ℝ _ _

/-- **The crossing count separates points exactly as the polygon does** (Theorem 2.3, read as a
criterion), for a polygon presented with redundant vertices. -/
theorem parity_ne_iff_mem_farRegion (P : PrePolygon m) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) {x y : Plane}
    (hx : x ∉ P.carrier) (hy : y ∉ P.carrier) :
    parity u P.pieces x ≠ parity u P.pieces y ↔ x ∈ farRegion P.carrier y := by
  rw [mem_farRegion_iff_connectedComponentIn_ne hx]
  constructor
  · intro hne heq
    exact hne (P.parity_eq_of_mem_connectedComponentIn_carrier hu hL hy
      (heq ▸ mem_connectedComponentIn hx))
  · intro hne
    rcases P.connectedComponentIn_eq_inside_or_outside hx with hxr | hxr <;>
      rcases P.connectedComponentIn_eq_inside_or_outside hy with hyr | hyr
    · exact absurd (hxr.trans hyr.symm) hne
    · rw [P.parity_eq_one_of_mem_inside hu hL (hxr ▸ mem_connectedComponentIn hx),
        P.parity_eq_zero_of_mem_outside hu hL (hyr ▸ mem_connectedComponentIn hy)]
      decide
    · rw [P.parity_eq_zero_of_mem_outside hu hL (hxr ▸ mem_connectedComponentIn hx),
        P.parity_eq_one_of_mem_inside hu hL (hyr ▸ mem_connectedComponentIn hy)]
      decide
    · exact absurd (hxr.trans hyr.symm) hne

/-! ### An arc as a polyline

`arc a k` is the carrier of the vertex list `v a, v (a+1), …, v (a+k)`; that is how it is seen
to be polygonal, and how it is glued to a crosscut. -/

/-- The vertex list of an arc. -/
def arcList (P : PrePolygon m) (a : ZMod (m + 3)) : ℕ → List Plane
  | 0 => [P.vertex a]
  | k + 1 => P.vertex a :: arcList P (a + 1) k

theorem arcList_ne_nil (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) : P.arcList a k ≠ [] := by
  cases k <;> simp [arcList]

theorem head_arcList (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    (P.arcList a k).head (P.arcList_ne_nil a k) = P.vertex a := by
  cases k <;> rfl

theorem getLast_arcList : ∀ (k : ℕ) (P : PrePolygon m) (a : ZMod (m + 3)),
    (P.arcList a k).getLast (P.arcList_ne_nil a k) = P.vertex (a + k)
  | 0, P, a => by simp [arcList]
  | k + 1, P, a => by
    change (P.vertex a :: P.arcList (a + 1) k).getLast (List.cons_ne_nil _ _)
        = P.vertex (a + ((k + 1 : ℕ) : ZMod (m + 3)))
    rw [List.getLast_cons (P.arcList_ne_nil (a + 1) k), getLast_arcList k P (a + 1)]
    congr 1
    push_cast
    ring

theorem arcPieces_succ (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    P.arcPieces a (k + 1) = (P.vertex a, P.vertex (a + 1)) :: P.arcPieces (a + 1) k := by
  rw [arcPieces, arcPieces, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · rw [Nat.cast_zero, add_zero]
  · refine List.map_congr_left fun t _ => ?_
    simp only [Function.comp_apply]
    congr 2 <;> · push_cast; ring

theorem poly_arcList : ∀ (k : ℕ) (P : PrePolygon m) (a : ZMod (m + 3)),
    poly (P.arcList a (k + 1)) = P.arc a (k + 1)
  | 0, P, a => by
    change segment ℝ (P.vertex a) (P.vertex (a + 1)) ∪ ({P.vertex (a + 1)} : Set Plane)
        = cover (P.arcPieces a 1)
    rw [arcPieces_succ P a 0, arcPieces_zero, cover_cons, cover_nil, Set.union_empty]
    exact union_eq_self_of_subset_right (singleton_subset_iff.2 (right_mem_segment ℝ _ _))
  | k + 1, P, a => by
    have hstep : poly (P.arcList a (k + 2))
        = segment ℝ (P.vertex a) (P.vertex (a + 1)) ∪ poly (P.arcList (a + 1) (k + 1)) := rfl
    rw [hstep, poly_arcList k P (a + 1)]
    change segment ℝ (P.vertex a) (P.vertex (a + 1)) ∪ cover (P.arcPieces (a + 1) (k + 1))
        = cover (P.arcPieces a (k + 2))
    rw [arcPieces_succ P a (k + 1), cover_cons]
    rfl

theorem poly_arcList_of_pos (P : PrePolygon m) (a : ZMod (m + 3)) (hk : 1 ≤ k) :
    poly (P.arcList a k) = P.arc a k := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  exact poly_arcList k' P a

theorem isPolygonal_arc (P : PrePolygon m) (a : ZMod (m + 3)) (hk : 1 ≤ k) :
    IsPolygonal (P.arc a k) := ⟨P.arcList a k, (poly_arcList_of_pos P a hk).symm⟩

end PrePolygon

/-! ## Cutting a segment at an interior point, in order

The two halves of a cut segment meet only at the cut, and neither reaches the far end of the
other. Both are read off `Schoenflies/SegmentOrder.lean`: along a nondegenerate segment the
distance from one end is a coordinate. -/

/-- **The two halves of a cut segment meet only at the cut point.** -/
theorem segment_halves_inter {u v w : Plane} (huv : u ≠ v) (hw : w ∈ openSegment ℝ u v) :
    segment ℝ u w ∩ segment ℝ w v ⊆ {w} := by
  rintro x ⟨hx1, hx2⟩
  have hws : w ∈ segment ℝ u v := openSegment_subset_segment ℝ _ _ hw
  have hwd := dist_le_of_mem_segment huv (left_mem_segment ℝ u v) (right_mem_segment ℝ u v)
    (by simp) hws
  have h1 := dist_le_of_mem_segment huv (left_mem_segment ℝ u v) hws (by simp) hx1
  have h2 := dist_le_of_mem_segment huv hws (right_mem_segment ℝ u v) hwd.2 hx2
  have hxs : x ∈ segment ℝ u v :=
    (convex_segment u v).segment_subset (left_mem_segment ℝ u v) hws hx1
  exact eq_of_dist_left_eq huv hxs hws (le_antisymm h1.2 h2.1)

/-- The far end of a cut segment is not on the near half. -/
theorem right_notMem_left_half {u v w : Plane} (huv : u ≠ v) (hw : w ∈ openSegment ℝ u v) :
    v ∉ segment ℝ u w := by
  intro hv
  have hvw : v = w := segment_halves_inter huv hw ⟨hv, right_mem_segment ℝ w v⟩
  rw [← hvw] at hw
  exact huv (right_mem_openSegment_iff.1 hw)

/-- The near end of a cut segment is not on the far half. -/
theorem left_notMem_right_half {u v w : Plane} (huv : u ≠ v) (hw : w ∈ openSegment ℝ u v) :
    u ∉ segment ℝ w v := by
  intro hu
  have huw : u = w := segment_halves_inter huv hw ⟨left_mem_segment ℝ u w, hu⟩
  rw [← huw] at hw
  exact huv (left_mem_openSegment_iff.1 hw)

namespace PrePolygon

/-! ## Inserting a vertex

`Schoenflies.PrePolygon.deleteLast` removes a redundant vertex; this is the inverse operation,
and it is what makes `PrePolygon` the right presentation for a consumer that must cut the curve
at prescribed points. The vertex is inserted at the end of the list, interior to the last edge;
`Schoenflies.PrePolygon.rotate` brings any edge there. -/

section Insert

variable {m : ℕ} {P : PrePolygon m} {z : Plane}

/-- The index `-1` of a cyclic list of length `m + 3`, as a numeral. -/
theorem val_neg_one : (-1 : ZMod (m + 3)).val = m + 2 := by
  have h : (-1 : ZMod (m + 3)) = ((m + 2 : ℕ) : ZMod (m + 3)) := by
    have h0 : ((m + 3 : ℕ) : ZMod (m + 3)) = 0 := ZMod.natCast_self _
    push_cast at h0 ⊢
    linear_combination -h0
  rw [h, ZMod.val_cast_of_lt (by omega)]

/-- The last edge, with its second endpoint written as vertex `0`. -/
theorem edge_neg_one (P : PrePolygon m) :
    P.edge (-1) = segment ℝ (P.vertex (-1)) (P.vertex 0) := by
  rw [edge, show (-1 : ZMod (m + 3)) + 1 = 0 by ring]

/-- **A point interior to an edge is a vertex of no index.** -/
theorem vertex_ne_of_mem_openSegment {i : ZMod (m + 3)} {w : Plane}
    (hw : w ∈ openSegment ℝ (P.vertex i) (P.vertex (i + 1))) (j : ZMod (m + 3)) :
    P.vertex j ≠ w := by
  intro he
  by_cases hji : j = i
  · rw [hji] at he
    rw [← he] at hw
    exact vertex_ne_succ i (left_mem_openSegment_iff.1 hw)
  · have hmem : w ∈ P.edge j := by rw [edge, ← he]; exact left_mem_segment ℝ _ _
    exact notMem_edge_of_mem_openSegment hji hw hmem

/-- The vertex family with `z` appended at the end: the old numerals name the old vertices, and
the one new index names `z`. -/
def insVertex (P : PrePolygon m) (z : Plane) (j : ZMod (m + 1 + 3)) : Plane :=
  if j.val < m + 3 then P.vertex ((j.val : ℕ) : ZMod (m + 3)) else z

theorem insVertex_emb (P : PrePolygon m) (z : Plane) (j : ZMod (m + 3)) :
    insVertex P z (emb j) = P.vertex j := by
  have hlt : j.val < m + 3 := ZMod.val_lt j
  have hval : (emb j).val = j.val := by
    rw [emb, ZMod.val_cast_of_lt (by omega)]
  rw [insVertex, if_pos (by rw [hval]; exact hlt), hval, ZMod.natCast_rightInverse j]

theorem val_neg_one' : (-1 : ZMod (m + 1 + 3)).val = m + 3 := by
  rw [neg_one_eq_cast, ZMod.val_cast_of_lt (by omega)]

theorem insVertex_neg_one (P : PrePolygon m) (z : Plane) : insVertex P z (-1) = z := by
  rw [insVertex, if_neg (by rw [val_neg_one' (m := m)]; omega)]

/-- Away from the inserted vertex the edges are unchanged. -/
theorem insEdge_of_lt {j : ZMod (m + 3)} (h : j.val + 1 < m + 3) :
    segment ℝ (insVertex P z (emb j)) (insVertex P z (emb j + 1)) = P.edge j := by
  rw [← emb_succ_of_lt h, insVertex_emb, insVertex_emb, edge]

/-- The penultimate edge of the lengthened list: the near half of the cut edge. -/
theorem insEdge_pen (P : PrePolygon m) (z : Plane) :
    segment ℝ (insVertex P z (-1 - 1)) (insVertex P z (-1 - 1 + 1))
      = segment ℝ (P.vertex (-1)) z := by
  have he : emb (-1 : ZMod (m + 3)) = -1 - 1 := emb_eq_last (by rw [val_neg_one])
  have h1 : insVertex P z (-1 - 1) = P.vertex (-1) := by rw [← he, insVertex_emb]
  have h2 : insVertex P z (-1 - 1 + 1) = z := by
    rw [show (-1 - 1 : ZMod (m + 1 + 3)) + 1 = -1 by ring, insVertex_neg_one]
  rw [h1, h2]

/-- The last edge of the lengthened list: the far half of the cut edge. -/
theorem insEdge_last (P : PrePolygon m) (z : Plane) :
    segment ℝ (insVertex P z (-1)) (insVertex P z (-1 + 1)) = segment ℝ z (P.vertex 0) := by
  have hemb0 : emb (0 : ZMod (m + 3)) = 0 := by rw [emb, ZMod.val_zero, Nat.cast_zero]
  have h1 : insVertex P z (-1) = z := insVertex_neg_one P z
  have h2 : insVertex P z (-1 + 1) = P.vertex 0 := by
    rw [show (-1 : ZMod (m + 1 + 3)) + 1 = 0 by ring, ← hemb0, insVertex_emb]
  rw [h1, h2]

theorem vertex_neg_one_ne_zero (P : PrePolygon m) : P.vertex (-1) ≠ P.vertex 0 := by
  have h := vertex_ne_succ (P := P) (-1)
  rwa [show (-1 : ZMod (m + 3)) + 1 = 0 by ring] at h

variable (hz : z ∈ openSegment ℝ (P.vertex (-1)) (P.vertex 0))
include hz

/-- The two new edges cover the edge they replace. -/
theorem insEdge_union : segment ℝ (P.vertex (-1)) z ∪ segment ℝ z (P.vertex 0) = P.edge (-1) := by
  rw [edge_neg_one]
  exact (segment_split (openSegment_subset_segment ℝ _ _ hz)).symm

theorem insEdge_pen_subset : segment ℝ (P.vertex (-1)) z ⊆ P.edge (-1) := by
  rw [← insEdge_union hz]; exact Set.subset_union_left

theorem insEdge_last_subset : segment ℝ z (P.vertex 0) ⊆ P.edge (-1) := by
  rw [← insEdge_union hz]; exact Set.subset_union_right

/-- **The polygon with one extra vertex, interior to its last edge** — equivalently, with the
last edge split in two at a prescribed interior point. -/
def insertLast (P : PrePolygon m) (hz : z ∈ openSegment ℝ (P.vertex (-1)) (P.vertex 0)) :
    PrePolygon (m + 1) where
  vertex := insVertex P z
  vertex_inj := by
    intro i j hij
    have hzv : ∀ l : ZMod (m + 3), P.vertex l ≠ z := by
      intro l
      refine vertex_ne_of_mem_openSegment (i := -1) ?_ l
      rwa [show (-1 : ZMod (m + 3)) + 1 = 0 by ring]
    simp only [insVertex] at hij
    have hi := ZMod.val_lt i
    have hj := ZMod.val_lt j
    by_cases hli : i.val < m + 3 <;> by_cases hlj : j.val < m + 3
    · rw [if_pos hli, if_pos hlj] at hij
      exact ZMod.val_injective _
        (ClosedPolygon.natCast_inj hli hlj (P.vertex_inj hij))
    · rw [if_pos hli, if_neg hlj] at hij
      exact absurd hij (hzv _)
    · rw [if_neg hli, if_pos hlj] at hij
      exact absurd hij.symm (hzv _)
    · exact ZMod.val_injective _ (by omega)
  edges_meet := by
    have hne0 : P.vertex (-1) ≠ P.vertex 0 := vertex_neg_one_ne_zero P
    have hhalf := segment_halves_inter hne0 hz
    have hpen := insEdge_pen P z
    have hlast := insEdge_last P z
    -- The shape of the edge at each of the three kinds of index.
    have hshape : ∀ i : ZMod (m + 1 + 3),
        (∃ j : ZMod (m + 3), j.val + 1 < m + 3 ∧ emb j = i ∧
            segment ℝ (insVertex P z i) (insVertex P z (i + 1)) = P.edge j ∧
            ({insVertex P z i, insVertex P z (i + 1)} : Set Plane)
              = {P.vertex j, P.vertex (j + 1)}) ∨
          (i = -1 - 1 ∧ segment ℝ (insVertex P z i) (insVertex P z (i + 1))
              = segment ℝ (P.vertex (-1)) z) ∨
          (i = -1 ∧ segment ℝ (insVertex P z i) (insVertex P z (i + 1))
              = segment ℝ z (P.vertex 0)) := by
      intro i
      by_cases h1 : i = -1
      · exact Or.inr (Or.inr ⟨h1, by rw [h1]; exact hlast⟩)
      by_cases h2 : i = -1 - 1
      · exact Or.inr (Or.inl ⟨h2, by rw [h2]; exact hpen⟩)
      obtain ⟨j, hjv, rfl⟩ := exists_emb_eq h1 h2
      refine Or.inl ⟨j, hjv, rfl, insEdge_of_lt hjv, ?_⟩
      rw [insVertex_emb, ← emb_succ_of_lt hjv, insVertex_emb]
    intro i j hij
    have hi := hshape i
    have hj := hshape j
    -- The names of the two ends of the edge at `i`, in each case.
    rcases hi with ⟨ji, hjiv, rfl, hEi, hVi⟩ | ⟨rfl, hEi⟩ | ⟨rfl, hEi⟩
    · have hjine : ji ≠ -1 := by
        intro he
        rw [he, val_neg_one] at hjiv
        omega
      rw [hEi, hVi]
      rcases hj with ⟨jj, hjjv, rfl, hEj, -⟩ | ⟨rfl, hEj⟩ | ⟨rfl, hEj⟩
      · rw [hEj]
        exact P.edges_meet ji jj fun he => hij (by rw [he])
      · rw [hEj]
        exact fun x hx =>
          P.edges_meet ji (-1) hjine ⟨hx.1, insEdge_pen_subset hz hx.2⟩
      · rw [hEj]
        exact fun x hx =>
          P.edges_meet ji (-1) hjine ⟨hx.1, insEdge_last_subset hz hx.2⟩
    · rw [hEi]
      have hV : ({insVertex P z (-1 - 1), insVertex P z (-1 - 1 + 1)} : Set Plane)
          = {P.vertex (-1), z} := by
        have he : emb (-1 : ZMod (m + 3)) = -1 - 1 := emb_eq_last (by rw [val_neg_one])
        rw [show insVertex P z (-1 - 1) = P.vertex (-1) by rw [← he, insVertex_emb],
          show insVertex P z (-1 - 1 + 1) = z by
            rw [show (-1 - 1 : ZMod (m + 1 + 3)) + 1 = -1 by ring, insVertex_neg_one]]
      rw [hV]
      rcases hj with ⟨jj, hjjv, rfl, hEj, -⟩ | ⟨rfl, -⟩ | ⟨rfl, hEj⟩
      · have hjjne : jj ≠ -1 := by
          intro he
          rw [he, val_neg_one] at hjjv
          omega
        rw [hEj]
        rintro x ⟨hx1, hx2⟩
        have hmem := P.edges_meet (-1) jj (Ne.symm hjjne)
          ⟨insEdge_pen_subset hz hx1, hx2⟩
        rw [show (-1 : ZMod (m + 3)) + 1 = 0 by ring] at hmem
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem ⊢
        rcases hmem with hmem | hmem
        · exact Or.inl hmem
        · exact absurd (hmem ▸ hx1) (right_notMem_left_half hne0 hz)
      · exact absurd rfl hij
      · rw [hEj]
        exact fun x hx => Or.inr (hhalf hx)
    · rw [hEi]
      have hV : ({insVertex P z (-1), insVertex P z (-1 + 1)} : Set Plane)
          = {z, P.vertex 0} := by
        have hemb0 : emb (0 : ZMod (m + 3)) = 0 := by rw [emb, ZMod.val_zero, Nat.cast_zero]
        rw [insVertex_neg_one,
          show insVertex P z (-1 + 1) = P.vertex 0 by
            rw [show (-1 : ZMod (m + 1 + 3)) + 1 = 0 by ring, ← hemb0, insVertex_emb]]
      rw [hV]
      rcases hj with ⟨jj, hjjv, rfl, hEj, -⟩ | ⟨rfl, hEj⟩ | ⟨rfl, -⟩
      · have hjjne : jj ≠ -1 := by
          intro he
          rw [he, val_neg_one] at hjjv
          omega
        rw [hEj]
        rintro x ⟨hx1, hx2⟩
        have hmem := P.edges_meet (-1) jj (Ne.symm hjjne)
          ⟨insEdge_last_subset hz hx1, hx2⟩
        rw [show (-1 : ZMod (m + 3)) + 1 = 0 by ring] at hmem
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem ⊢
        rcases hmem with hmem | hmem
        · exact absurd (hmem ▸ hx1) (left_notMem_right_half hne0 hz)
        · exact Or.inr hmem
      · rw [hEj]
        exact fun x hx => Or.inl (hhalf ⟨hx.2, hx.1⟩)
      · exact absurd rfl hij

@[simp] theorem insertLast_vertex : (insertLast P hz).vertex = insVertex P z := rfl

/-- **Inserting a vertex does not move the curve.** -/
theorem carrier_insertLast : (insertLast P hz).carrier = P.carrier := by
  have hpen := insEdge_pen P z
  have hlast := insEdge_last P z
  refine Set.Subset.antisymm (Set.iUnion_subset fun i => ?_) (Set.iUnion_subset fun j => ?_)
  · by_cases h1 : i = -1
    · subst h1
      refine le_trans (le_of_eq ?_) (le_trans (insEdge_last_subset hz) (edge_subset_carrier _))
      exact hlast
    by_cases h2 : i = -1 - 1
    · subst h2
      refine le_trans (le_of_eq ?_) (le_trans (insEdge_pen_subset hz) (edge_subset_carrier _))
      exact hpen
    · obtain ⟨j, hjv, rfl⟩ := exists_emb_eq h1 h2
      refine le_trans (le_of_eq ?_) (edge_subset_carrier j)
      exact insEdge_of_lt hjv
  · by_cases hjlast : j.val + 1 < m + 3
    · refine le_trans (le_of_eq ?_) (edge_subset_carrier (P := insertLast P hz) (emb j))
      exact (insEdge_of_lt hjlast (P := P) (z := z)).symm
    · have hjm : j = -1 := by
        have := ZMod.val_lt j
        exact ZMod.val_injective _ (by rw [val_neg_one]; omega)
      subst hjm
      rw [← insEdge_union hz]
      refine Set.union_subset ?_ ?_
      · refine le_trans (le_of_eq hpen.symm)
          (edge_subset_carrier (P := insertLast P hz) (-1 - 1))
      · refine le_trans (le_of_eq hlast.symm)
          (edge_subset_carrier (P := insertLast P hz) (-1))

/-- The inserted vertex is a vertex. -/
theorem insertLast_mem_vertex : ∃ j, (insertLast P hz).vertex j = z :=
  ⟨-1, insVertex_neg_one P z⟩

/-- The old vertices are still vertices. -/
theorem insertLast_old_vertex (i : ZMod (m + 3)) : ∃ j, (insertLast P hz).vertex j = P.vertex i :=
  ⟨emb i, insVertex_emb P z i⟩

end Insert

/-- **A named point of the curve becomes a vertex**, and the old vertices stay vertices. Either
the point already is a vertex, or it is interior to exactly one edge, and then that edge is
brought to the end of the list by `Schoenflies.PrePolygon.rotate` and cut by
`Schoenflies.PrePolygon.insertLast`. -/
theorem exists_prePolygon_insert {m : ℕ} (P : PrePolygon m) {z : Plane} (hz : z ∈ P.carrier) :
    ∃ (m' : ℕ) (P' : PrePolygon m'), P'.carrier = P.carrier ∧ (∃ j, P'.vertex j = z) ∧
      ∀ i, ∃ j, P'.vertex j = P.vertex i := by
  obtain ⟨i, hzi⟩ := Set.mem_iUnion.1 hz
  by_cases hend : z = P.vertex i ∨ z = P.vertex (i + 1)
  · exact ⟨m, P, rfl, by rcases hend with rfl | rfl; exacts [⟨i, rfl⟩, ⟨i + 1, rfl⟩],
      fun i => ⟨i, rfl⟩⟩
  · push Not at hend
    have hopen : z ∈ openSegment ℝ (P.vertex i) (P.vertex (i + 1)) :=
      mem_openSegment_of_ne_left_right (Ne.symm hend.1) (Ne.symm hend.2) hzi
    -- Rotate so that the edge in question is the last one.
    set Q : PrePolygon m := P.rotate (i + 1) with hQ
    have hQm : Q.vertex (-1) = P.vertex i := by
      rw [hQ, rotate_vertex, show i + 1 + (-1 : ZMod (m + 3)) = i by ring]
    have hQ0 : Q.vertex 0 = P.vertex (i + 1) := by
      rw [hQ, rotate_vertex, add_zero]
    have hopen' : z ∈ openSegment ℝ (Q.vertex (-1)) (Q.vertex 0) := by rw [hQm, hQ0]; exact hopen
    refine ⟨m + 1, insertLast Q hopen', ?_, insertLast_mem_vertex hopen', fun l => ?_⟩
    · rw [carrier_insertLast hopen', hQ, carrier_rotate]
    · obtain ⟨j, hj⟩ := insertLast_old_vertex hopen' (l - (i + 1))
      exact ⟨j, by rw [hj, hQ, rotate_vertex, add_sub_cancel]⟩

/-- **Every point of a finite list on the curve can be made a vertex at once.** -/
theorem exists_prePolygon_vertices : ∀ (S : List Plane) {m : ℕ} (P : PrePolygon m),
    (∀ z ∈ S, z ∈ P.carrier) →
      ∃ (m' : ℕ) (P' : PrePolygon m'), P'.carrier = P.carrier ∧
        (∀ z ∈ S, ∃ j, P'.vertex j = z) ∧ (∀ i, ∃ j, P'.vertex j = P.vertex i)
  | [], m, P, _ => ⟨m, P, rfl, by simp, fun i => ⟨i, rfl⟩⟩
  | z :: S, m, P, hS => by
    obtain ⟨m₁, P₁, hcar₁, ⟨j₀, hj₀⟩, hold₁⟩ :=
      exists_prePolygon_insert P (hS z (List.mem_cons_self ..))
    obtain ⟨m₂, P₂, hcar₂, hnew₂, hold₂⟩ := exists_prePolygon_vertices S P₁
      (fun w hw => by rw [hcar₁]; exact hS w (List.mem_cons_of_mem _ hw))
    refine ⟨m₂, P₂, by rw [hcar₂, hcar₁], fun w hw => ?_, fun i => ?_⟩
    · rcases List.mem_cons.1 hw with rfl | hw'
      · obtain ⟨j, hj⟩ := hold₂ j₀
        exact ⟨j, by rw [hj, hj₀]⟩
      · exact hnew₂ w hw'
    · obtain ⟨j₁, hj₁⟩ := hold₁ i
      obtain ⟨j, hj⟩ := hold₂ j₁
      exact ⟨j, by rw [hj, hj₁]⟩

/-- A one-edge arc is that edge. -/
theorem arc_one {m : ℕ} (P : PrePolygon m) (a : ZMod (m + 3)) : P.arc a 1 = P.edge a := by
  ext z
  rw [mem_arc_iff]
  constructor
  · rintro ⟨t, ht, hz⟩
    obtain rfl : t = 0 := by omega
    rwa [Nat.cast_zero, add_zero] at hz
  · intro hz
    exact ⟨0, by omega, by rwa [Nat.cast_zero, add_zero]⟩

/-- **A vertex on an edge is one of that edge's own two ends.** -/
theorem vertex_mem_edge_elim {m : ℕ} {P : PrePolygon m} {c i : ZMod (m + 3)}
    (hc : P.vertex c ∈ P.edge i) :
    P.vertex c ∈ ({P.vertex i, P.vertex (i + 1)} : Set Plane) := by
  by_cases hci : c = i
  · exact Or.inl (by rw [hci])
  · exact P.edges_meet i c (Ne.symm hci) ⟨hc, left_mem_segment ℝ _ _⟩

end PrePolygon

/-! ## The realization theorem, with the cut points anywhere on the curve

`Schoenflies.exists_closedPolygon_split` requires the two cut points to be *corners*, and by
`Schoenflies.ClosedPolygon.isCornerAt_vertex` that requirement cannot be dropped while the
realization is a `ClosedPolygon`. For a `PrePolygon` there is no such obstruction: a point of the
curve is either already a vertex or interior to an edge, and an edge may be cut. -/

/-- **The realization theorem for `PrePolygon`, with named points.** Any finite list of points of
the curve — corners or not — can be required to be among the vertices. -/
theorem exists_prePolygon_points {C : Set Plane} (hJ : IsJordanCurve C) (hP : IsPolygonal C)
    (S : List Plane) (hS : ∀ p ∈ S, p ∈ C) :
    ∃ (m : ℕ) (P : PrePolygon m), P.carrier = C ∧ ∀ p ∈ S, ∃ i : ZMod (m + 3), P.vertex i = p := by
  obtain ⟨m, P, hcar⟩ := exists_prePolygon_of_isJordanCurve hJ hP
  obtain ⟨m', P', hcar', hnew, -⟩ :=
    PrePolygon.exists_prePolygon_vertices S P (fun z hz => by rw [hcar]; exact hS z hz)
  exact ⟨m', P', by rw [hcar', hcar], hnew⟩

/-- **The realization theorem tracking two named points**, for a presentation that may carry
redundant vertices. Unlike `Schoenflies.exists_closedPolygon_split` this asks nothing of the two
points but that they lie on the curve: a `PrePolygon` has no `corner` field to obstruct a vertex
where the curve runs straight. -/
theorem exists_prePolygon_split {C : Set Plane} (hJ : IsJordanCurve C) (hP : IsPolygonal C)
    {p q : Plane} (hp : p ∈ C) (hq : q ∈ C) (hpq : p ≠ q) :
    ∃ (m : ℕ) (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ), P.carrier = C ∧
      P.vertex a = p ∧ P.vertex (a + (k : ZMod (m + 3))) = q ∧ 1 ≤ k ∧ k ≤ m + 2 := by
  obtain ⟨m, P, hcar, hvert⟩ := exists_prePolygon_points hJ hP [p, q]
    (by
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      exacts [hp, hq])
  obtain ⟨a, ha⟩ := hvert p (by simp)
  obtain ⟨b, hb⟩ := hvert q (by simp)
  have hab : b - a ≠ 0 := fun he => hpq (by rw [← ha, ← hb, show b = a by linear_combination he])
  refine ⟨m, P, a, (b - a).val, hcar, ha, ?_, ?_, ?_⟩
  · rw [ZMod.natCast_rightInverse (b - a), add_sub_cancel]; exact hb
  · rcases Nat.eq_zero_or_pos (b - a).val with h0 | h0
    · exact absurd (by rw [← ZMod.natCast_rightInverse (b - a), h0, Nat.cast_zero]) hab
    · exact h0
  · have := ZMod.val_lt (b - a)
    omega

end Schoenflies

end BundlePart418

section BundlePart419
/- Source: dev/planar_search/schoenflies_port/Schoenflies/FaceCyclesLand.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/



/-!
# `lem:face-cycles`, with nothing assumed

`Schoenflies/FaceCyclesProof.lean` proves `lem:face-cycles` modulo one hypothesis,
`Schoenflies.CrosscutSplitsRegion`: the exhaustion clause of `thm:polygonal-crosscut` for a
crosscut whose two endpoints are *arbitrary points* of the curve. This module proves that
hypothesis and restates the lemma without it (`Graph.face_cycles'`,
`Graph.IsDrawing.hasFaceCycles_union'`).

## Why the crosscut theorem had to be redone, and how far

`main`'s Theorem 2.8 (`Schoenflies.IsPolygonalCrosscut`) cuts a `ClosedPolygon` at two of *its
vertices*, and `Schoenflies.ClosedPolygon.isCornerAt_vertex` says a point at which the curve runs
straight is a vertex of no `ClosedPolygon` presentation of it. In the ear induction the two cut
points are graph vertices, at which the two cycle edges may leave along opposite rays. So the
presentation has to be `Schoenflies.PrePolygon`, which has no `corner` field, and the two `main`
hypotheses `edges₁`/`edges₂` — multiset equalities `SameEdges Jᵢ.pieces (Aᵢ ++ K)` — have to go
as well, for the reason `Schoenflies/FaceCyclesProof.lean` records: the merged curve `Aᵢ ∪ P` may
run straight through a cut point, and then no presentation of it has an edge ending there.

Both go away at once by never realizing `J₁` and `J₂` at all. The two curves of the split are
given by *literal* edge lists `Aᵢ ++ K`, so Lemma 2.7 (`Schoenflies.parity_split`) applies with
nothing to check, and only the *easy* half of Theorem 2.3 is asked of them: "points in the same
region have the same crossing count", which is Lemma 2.2
(`Schoenflies.parity_eq_of_mem_connectedComponentIn`) and needs no realization. The hard half —
the two values `0` and `1` — is needed for `J` alone, where
`Schoenflies.PrePolygon.parity_eq_one_iff` of `Schoenflies/PrePolygonSep.lean` supplies it. That
is the whole of the reduction; Lemma 2.6 (`Schoenflies.crosscut_cells`) is already stated at the
set level and is quoted unchanged.

What the presentation still has to do is put the two cut points *on* its vertex list, and that is
`Schoenflies.PrePolygon.insertLast` of `Schoenflies/PrePolygonArc.lean`, the inverse of
`Schoenflies.PrePolygon.deleteLast`. A point interior to an edge is brought to the last edge by
`Schoenflies.PrePolygon.rotate` and the edge is split in two; simplicity survives because the far
end of the split edge lies on neither half.

## For the integrator

The `Schoenflies.PrePolygon` arc apparatus this module runs on —
`Schoenflies.PrePolygon.arcPieces`, `…arc`, `…arcList`, `…insertLast` and
`Schoenflies.exists_prePolygon_split` — lives in `Schoenflies/PrePolygonArc.lean`, shared with
`Schoenflies/Graph/K33Land.lean`. It is `Schoenflies.ClosedPolygon.arcPieces` and its API of
`Schoenflies/ParitySplitting.lean` and `Schoenflies/Realization.lean` transcribed with the
structure changed — the proofs use `vertex_inj` and `edges_meet` and nothing else. The right
arrangement, as `Schoenflies/PrePolygonSep.lean` already says of `pieces`, is to prove them once
for `PrePolygon` and define the `ClosedPolygon` versions as `P.toPre.arcPieces`; that needs
`PrePolygon` moved up beside `ClosedPolygon` in `Schoenflies/Strip.lean`.

Three declarations here are general and belong elsewhere:
`Schoenflies.isSeparating_of_isJordanCurve` in `Schoenflies/Realization.lean`,
`Schoenflies.IsArcBetween.ne` in `Schoenflies/Curve.lean`, and
`Schoenflies.isChainFrom_segsOf` in `Schoenflies/ParitySplitting.lean` beside
`Schoenflies.isChainFrom_pathPieces`. `Schoenflies.two_arcs_unique_of_isClosed` subsumes
`Schoenflies.two_arcs_unique` and should replace it in `Schoenflies/Realization.lean`.

Once this module is moved above `Schoenflies/FaceCyclesProof.lean`, the hypothesis
`Schoenflies.CrosscutSplitsRegion` can be deleted from `Graph.face_cycles` and
`Graph.IsDrawing.hasFaceCycles_union`, and the two primed statements at the end here dropped.

## Blueprint

* `Schoenflies.two_arcs_unique_of_isClosed` — the two arcs a pair of points cuts a curve into are
  determined, with the competing splitting known only to be closed and nondegenerate.
* `Schoenflies.crosscutSplitsRegion` — the exhaustion clause of `thm:polygonal-crosscut` at
  arbitrary cut points: `Schoenflies.CrosscutSplitsRegion`, proved.
* `Graph.IsDrawing.hasFaceCycles_union'` — one ear of `lem:face-cycles`.
* `Graph.face_cycles'` — **`lem:face-cycles`**.
* `Graph.IsFaceCycle.eq_inside_of_isBounded'` — "in particular, every bounded face is the
  interior of its boundary cycle".
-/
open Bornology Metric Set

namespace Schoenflies

/-! ## Small pieces the assembly needs -/

/-- **A polygonal Jordan curve separates the plane** (Theorem 2.3, at the set level): realize it
and quote `Schoenflies.ClosedPolygon.isSeparating_carrier`. -/
theorem isSeparating_of_isJordanCurve {S : Set Plane} (hJ : IsJordanCurve S)
    (hP : IsPolygonal S) : IsSeparating S := by
  obtain ⟨m, Q, hQ⟩ := exists_closedPolygon hJ hP
  exact hQ ▸ Q.isSeparating_carrier

/-- The two ends of an arc are distinct: they are the images of `0` and `1`. -/
theorem IsArcBetween.ne {A : Set Plane} {p q : Plane} (h : IsArcBetween A p q) : p ≠ q := by
  obtain ⟨f, -, hinj, -, hf0, hf1⟩ := h
  intro he
  have h01 : (0 : ℝ) = 1 := hinj zero_mem_I one_mem_I (by rw [hf0, hf1, he])
  norm_num at h01

/-- **A polyline is a chain from its first point to its last**, with its degenerate steps
dropped. `Schoenflies.isChainFrom_pathPieces` says this for `Schoenflies.pathPieces`, which keeps
them; `Schoenflies.segsOf` is the list a consumer needing nondegenerate edges must use. -/
theorem isChainFrom_segsOf : ∀ (vs : List Plane) (h : vs ≠ []),
    IsChainFrom (segsOf vs) (vs.head h) (vs.getLast h)
  | [], h => absurd rfl h
  | [v], _ => by simpa using isChainFrom_nil v
  | u :: v :: rest, hu => by
    classical
    have hne : (v :: rest) ≠ [] := List.cons_ne_nil _ _
    have ih : IsChainFrom (segsOf (v :: rest)) v ((v :: rest).getLast hne) :=
      isChainFrom_segsOf (v :: rest) hne
    have hgl : (u :: v :: rest).getLast hu = (v :: rest).getLast hne := List.getLast_cons hne
    rw [show (u :: v :: rest).head hu = u from rfl, hgl, segsOf_cons_cons]
    split_ifs with huv
    · rw [huv]; exact ih
    · intro f
      simp only [List.map_cons, List.sum_cons]
      rw [ih f]
      linear_combination add_self_zmod_two (f v)

/-- **The two-arc decomposition is determined, and the competitor need not be known to be two
arcs.** This is `Schoenflies.two_arcs_unique` with the hypotheses on the second splitting weakened
to what its proof uses: the two sets are closed and neither is just the two cut points. The edge
lists of a polygon supply exactly that, and nothing tells us they are arcs until this lemma has
said so. -/
theorem two_arcs_unique_of_isClosed {C A₁ A₂ D₁ D₂ : Set Plane} {p q : Plane}
    (hA : A₁ ∪ A₂ = C) (hAi : A₁ ∩ A₂ = {p, q})
    (hD : D₁ ∪ D₂ = C) (hDi : D₁ ∩ D₂ = {p, q})
    (hA1 : IsArcBetween A₁ p q) (hA2 : IsArcBetween A₂ p q)
    (hc1 : IsClosed D₁) (hc2 : IsClosed D₂)
    (hn1 : ¬ D₁ ⊆ ({p, q} : Set Plane)) (hn2 : ¬ D₂ ⊆ ({p, q} : Set Plane)) :
    (A₁ = D₁ ∧ A₂ = D₂) ∨ (A₁ = D₂ ∧ A₂ = D₁) := by
  have hpA : p ∈ A₁ ∩ A₂ := by rw [hAi]; exact Or.inl rfl
  have hqA : q ∈ A₁ ∩ A₂ := by rw [hAi]; exact Or.inr rfl
  have hpD : p ∈ D₁ ∩ D₂ := by rw [hDi]; exact Or.inl rfl
  have hqD : q ∈ D₁ ∩ D₂ := by rw [hDi]; exact Or.inr rfl
  -- An arc between the two points lies on one side of the other splitting.
  have key : ∀ A : Set Plane, IsArcBetween A p q → A ⊆ C → A ⊆ D₁ ∨ A ⊆ D₂ := by
    intro A hAar hAC
    obtain ⟨hconn, hne⟩ := hAar.preconnected_diff
    have hsub : A \ {p, q} ⊆ D₁ᶜ ∪ D₂ᶜ := by
      intro w hw
      by_cases h1 : w ∈ D₁
      · by_cases h2 : w ∈ D₂
        · exact absurd (show w ∈ ({p, q} : Set Plane) by rw [← hDi]; exact ⟨h1, h2⟩) hw.2
        · exact Or.inr h2
      · exact Or.inl h1
    have hnone : ¬ ((A \ {p, q}) ∩ (D₁ᶜ ∩ D₂ᶜ)).Nonempty := by
      rintro ⟨w, hw, h1, h2⟩
      have hwC : w ∈ C := hAC hw.1
      rw [← hD] at hwC
      exact hwC.elim h1 h2
    have hends : ∀ D : Set Plane, p ∈ D → q ∈ D → A \ {p, q} ⊆ D → A ⊆ D := by
      intro D hpD' hqD' hsub' w hw
      by_cases hwpq : w ∈ ({p, q} : Set Plane)
      · rcases hwpq with rfl | rfl
        exacts [hpD', hqD']
      · exact hsub' ⟨hw, hwpq⟩
    by_cases hcase : ((A \ {p, q}) ∩ D₁ᶜ).Nonempty
    · refine Or.inr (hends D₂ hpD.2 hqD.2 fun w hw => ?_)
      by_contra hwD2
      exact hnone (hconn _ _ hc1.isOpen_compl hc2.isOpen_compl hsub hcase ⟨w, hw, hwD2⟩)
    · refine Or.inl (hends D₁ hpD.1 hqD.1 fun w hw => ?_)
      by_contra hwD1
      exact hcase ⟨w, hw, hwD1⟩
  -- Both arcs cannot land on the same side: the other side would be just the two points.
  have hnotboth : ∀ D D' : Set Plane, D ∪ D' = C → D ∩ D' = {p, q} →
      ¬ D' ⊆ ({p, q} : Set Plane) → A₁ ⊆ D → A₂ ⊆ D → False := by
    intro D D' hDD hDDi hD'n h1 h2
    refine hD'n ?_
    rw [← hDDi]
    intro w hw
    have hwC : w ∈ C := by rw [← hDD]; exact Or.inr hw
    rw [← hA] at hwC
    exact hwC.elim (fun h => ⟨h1 h, hw⟩) fun h => ⟨h2 h, hw⟩
  have heq : ∀ X Y X' Y' : Set Plane, X ∪ Y = C → X' ∪ Y' = C → X' ∩ Y' = {p, q} →
      p ∈ X → q ∈ X → X ⊆ X' → Y ⊆ Y' → X = X' := by
    intro X Y X' Y' hXY hX'Y' hX'Y'i hpX hqX hXX hYY
    refine Set.Subset.antisymm hXX fun w hw => ?_
    have hwC : w ∈ C := by rw [← hX'Y']; exact Or.inl hw
    rw [← hXY] at hwC
    rcases hwC with h | h
    · exact h
    · have hwpq : w ∈ ({p, q} : Set Plane) := by rw [← hX'Y'i]; exact ⟨hw, hYY h⟩
      rcases hwpq with rfl | rfl
      exacts [hpX, hqX]
  have hAC₁ : A₁ ⊆ C := by rw [← hA]; exact Set.subset_union_left
  have hAC₂ : A₂ ⊆ C := by rw [← hA]; exact Set.subset_union_right
  rcases key A₁ hA1 hAC₁ with h1 | h1 <;> rcases key A₂ hA2 hAC₂ with h2 | h2
  · exact absurd (hnotboth D₁ D₂ hD hDi hn2 h1 h2) (by simp)
  · exact Or.inl ⟨heq A₁ A₂ D₁ D₂ hA hD hDi hpA.1 hqA.1 h1 h2,
      heq A₂ A₁ D₂ D₁ (by rw [Set.union_comm]; exact hA) (by rw [Set.union_comm]; exact hD)
        (by rw [Set.inter_comm]; exact hDi) hpA.2 hqA.2 h2 h1⟩
  · exact Or.inr ⟨heq A₁ A₂ D₂ D₁ hA (by rw [Set.union_comm]; exact hD)
      (by rw [Set.inter_comm]; exact hDi) hpA.1 hqA.1 h1 h2,
      heq A₂ A₁ D₁ D₂ (by rw [Set.union_comm]; exact hA) hD hDi hpA.2 hqA.2 h2 h1⟩
  · exact absurd (hnotboth D₂ D₁ (by rw [Set.union_comm]; exact hD)
      (by rw [Set.inter_comm]; exact hDi) hn1 h1 h2) (by simp)

/-! ## Theorem 2.8 at arbitrary cut points

The blueprint's Theorem 2.8 is proved on `main` for a crosscut cutting a `ClosedPolygon` at two
of *its vertices*; `Schoenflies.ClosedPolygon.isCornerAt_vertex` makes that a real restriction,
since a point where the curve runs straight is a vertex of no `ClosedPolygon` presentation. The
exhaustion clause is what a consumer splitting a face at two graph vertices needs, and here it is
proved with no condition on the two points beyond lying on the curve.

The route is the blueprint's, with `PrePolygon` in place of `ClosedPolygon` and with the two
`Schoenflies.SameEdges` hypotheses of `Schoenflies.IsPolygonalCrosscut` replaced by *literal*
edge lists: the two curves of the split are presented as `Aᵢ ++ K`, so Lemma 2.7
(`Schoenflies.parity_split`) applies with nothing to check. Only one direction of Theorem 2.3 is
needed for those two lists — "the same region forces the same count", which is Lemma 2.2 and asks
for no realization at all. The other direction is needed only for the curve `C` itself, and there
`Schoenflies.PrePolygon.parity_eq_one_iff` supplies it. -/

/-- **The exhaustion clause of the polygonal crosscut theorem, at arbitrary cut points.** This is
`Schoenflies.CrosscutSplitsRegion`, the hypothesis `Schoenflies/FaceCyclesProof.lean` was left
with. -/
theorem crosscutSplitsRegion : CrosscutSplitsRegion := by
  intro J A₁ A₂ P Ω p q hJsep hJpoly hPpoly hA1 hA2 hunion hinter hParc hPJ hΩ hPsub z hz
  have hpq : p ≠ q := hA1.ne
  have hpJ : p ∈ J := by rw [← hunion]; exact Or.inl hA1.left_mem
  have hqJ : q ∈ J := by rw [← hunion]; exact Or.inl hA1.right_mem
  -- 1. Present the curve with the two cut points among its vertices.
  obtain ⟨m, C, a, k, hcar, hva, hvb, hk1, hk2⟩ :=
    exists_prePolygon_split hJsep.isJordanCurve hJpoly hpJ hqJ hpq
  have hk3 : k ≤ m + 3 := by omega
  have hDunion : C.arc a k ∪ C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) = J := by
    rw [C.arc_union a hk3, hcar]
  have hDinter : C.arc a k ∩ C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) = {p, q} := by
    rw [C.arc_inter a hk1 hk2, hva, hvb]
  have hD1n : ¬ C.arc a k ⊆ ({p, q} : Set Plane) := by
    rw [← hva, ← hvb]; exact C.arc_not_subset_endpoints a hk1 hk2
  have hD2n : ¬ C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ⊆ ({p, q} : Set Plane) := by
    have h := C.arc_not_subset_endpoints (a + (k : ZMod (m + 3))) (k := m + 3 - k)
      (by omega) (by omega)
    rw [zmod_add_sub_cancel hk3 a, hva, hvb, Set.pair_comm q p] at h
    exact h
  -- 2. The two arcs of the presentation are the two given arcs.
  have hids := two_arcs_unique_of_isClosed hunion hinter hDunion hDinter hA1 hA2
    (C.isCompact_arc a k).isClosed (C.isCompact_arc _ _).isClosed hD1n hD2n
  have harc1 : IsArcBetween (C.arc a k) p q := by
    rcases hids with ⟨e1, -⟩ | ⟨-, e2⟩
    · exact e1 ▸ hA1
    · exact e2 ▸ hA2
  have harc2 : IsArcBetween (C.arc (a + (k : ZMod (m + 3))) (m + 3 - k)) p q := by
    rcases hids with ⟨-, e2⟩ | ⟨e1, -⟩
    · exact e2 ▸ hA2
    · exact e1 ▸ hA1
  have hD1J : C.arc a k ⊆ J := by rw [← hcar]; exact C.arc_subset_carrier a k
  have hD2J : C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ⊆ J := by
    rw [← hcar]; exact C.arc_subset_carrier _ _
  have hpqD1 : ({p, q} : Set Plane) ⊆ C.arc a k := by
    rw [← hDinter]; exact Set.inter_subset_left
  have hpqD2 : ({p, q} : Set Plane) ⊆ C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) := by
    rw [← hDinter]; exact Set.inter_subset_right
  -- 3. The crosscut, as a vertex list in each direction and as an edge list.
  obtain ⟨ws, hwsne, hwhead, hwlast, hwpoly⟩ := hParc.exists_poly_eq hPpoly hpq
  obtain ⟨ws', hwsne', hwhead', hwlast', hwpoly'⟩ := hParc.reverse.exists_poly_eq hPpoly hpq.symm
  have hKcover : cover (segsOf ws) = P := by
    rw [cover_segsOf_eq (a := p) (b := q) (by rw [hwpoly]; exact hParc.left_mem)
      (by rw [hwpoly]; exact hParc.right_mem) hpq, hwpoly]
  have hKchain : IsChainFrom (segsOf ws) p q := by
    have h := isChainFrom_segsOf ws hwsne
    rwa [hwhead, hwlast] at h
  -- 4. The two curves of the split are separating.
  have hpolyD1P : IsPolygonal (C.arc a k ∪ P) :=
    ⟨C.arcList a k ++ ws', by
      rw [poly_append_of_eq (C.arcList_ne_nil a k) hwsne'
          (by rw [PrePolygon.getLast_arcList k C a, hvb, hwhead']),
        PrePolygon.poly_arcList_of_pos C a hk1, hwpoly']⟩
  have hpolyD2P : IsPolygonal (C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P) :=
    ⟨C.arcList (a + (k : ZMod (m + 3))) (m + 3 - k) ++ ws, by
      rw [poly_append_of_eq (C.arcList_ne_nil _ _) hwsne
          (by rw [PrePolygon.getLast_arcList (m + 3 - k) C _, zmod_add_sub_cancel hk3 a, hva,
            hwhead]),
        PrePolygon.poly_arcList_of_pos C _ (by omega : 1 ≤ m + 3 - k), hwpoly]⟩
  have hmeetP : ∀ (S : Set Plane), S ⊆ J → ∀ w ∈ S, w ∈ P → w = p ∨ w = q := by
    intro S hSJ w hw hwP
    have hmem : w ∈ ({p, q} : Set Plane) := by rw [← hPJ]; exact ⟨hwP, hSJ hw⟩
    simpa using hmem
  have hJ1 : IsSeparating (C.arc a k ∪ P) :=
    isSeparating_of_isJordanCurve (isJordanCurve_union harc1 hParc (hmeetP _ hD1J)) hpolyD1P
  have hJ2 : IsSeparating (C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P) :=
    isSeparating_of_isJordanCurve (isJordanCurve_union harc2 hParc (hmeetP _ hD2J)) hpolyD2P
  -- 5. A reference point in the region the crosscut does not enter.
  obtain ⟨Ω', hΩpair⟩ : ∃ Ω' : Set Plane, IsRegionPair J Ω Ω' := by
    rcases hΩ with h | h
    · exact ⟨outside J, Or.inl ⟨h, rfl⟩⟩
    · exact ⟨inside J, Or.inr ⟨h, rfl⟩⟩
  obtain ⟨y, hy⟩ := (hΩpair.right.isConnected hJsep).nonempty
  have hyJ : y ∉ J := hΩpair.right.subset_compl hy
  have hnotP : ∀ w ∈ Ω', w ∉ P := by
    intro w hw hwP
    have hwJ : w ∉ J := hΩpair.right.subset_compl hw
    have hwpq : w ∉ ({p, q} : Set Plane) := by
      rintro (rfl | rfl)
      exacts [hwJ hpJ, hwJ hqJ]
    exact Set.disjoint_left.1 hΩpair.disjoint (hPsub ⟨hwP, hwpq⟩) hw
  have hΩ'sub : ∀ S : Set Plane, S ⊆ J → Ω' ⊆ (S ∪ P)ᶜ := by
    intro S hSJ w hw
    rintro (h | h)
    · exact hΩpair.right.subset_compl hw (hSJ h)
    · exact hnotP w hw h
  have hyJ1 : y ∉ C.arc a k ∪ P := hΩ'sub _ hD1J hy
  have hyJ2 : y ∉ C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P := hΩ'sub _ hD2J hy
  have hΩW1 : Ω' ⊆ connectedComponentIn (C.arc a k ∪ P)ᶜ y :=
    (hΩpair.right.isConnected hJsep).isPreconnected.subset_connectedComponentIn hy
      (hΩ'sub _ hD1J)
  have hΩW2 : Ω' ⊆
      connectedComponentIn (C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P)ᶜ y :=
    (hΩpair.right.isConnected hJsep).isPreconnected.subset_connectedComponentIn hy
      (hΩ'sub _ hD2J)
  have heqΩ' : connectedComponentIn Jᶜ y = Ω' := hΩpair.right.connectedComponentIn_eq hJsep hy
  -- 6. Lemma 2.6: the two cells are components of `Ω ∖ P`.
  obtain ⟨⟨-, hV1comp⟩, ⟨-, hV2comp⟩, -, -, -⟩ :=
    crosscut_cells hJsep hJ1 hJ2 hD1J hD2J (by rw [hPJ]; exact hpqD1) (by rw [hPJ]; exact hpqD2)
      (arcs_ne (le_of_eq hDinter) hD1n) hΩpair (hJ1.isRegionPair_farRegion hyJ1) hΩW1
      (hJ2.isRegionPair_farRegion hyJ2) hΩW2
  -- 7. Exhaustion, by Lemma 2.7 and the two values of Theorem 2.3.
  obtain ⟨u, hu, hlev⟩ := exists_direction_hgt_ne (C.pieces ++ segsOf ws) (by
    intro Q hQ
    rcases List.mem_append.1 hQ with h | h
    · exact C.pieces_nondeg Q h
    · exact segsOf_nondeg ws Q h)
  have hlevC : ∀ Q ∈ C.pieces, hgt u Q.1 ≠ hgt u Q.2 :=
    fun Q hQ => hlev Q (List.mem_append_left _ hQ)
  have hlevK : ∀ Q ∈ segsOf ws, hgt u Q.1 ≠ hgt u Q.2 :=
    fun Q hQ => hlev Q (List.mem_append_right _ hQ)
  have hlev1 : ∀ Q ∈ C.arcPieces a k ++ segsOf ws, hgt u Q.1 ≠ hgt u Q.2 :=
    hgt_ne_append (PrePolygon.arcPieces_hgt_ne hlevC) hlevK
  have hlev2 : ∀ Q ∈ C.arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k) ++ segsOf ws,
      hgt u Q.1 ≠ hgt u Q.2 := hgt_ne_append (PrePolygon.arcPieces_hgt_ne hlevC) hlevK
  have hchain1 : IsChainFrom (C.arcPieces a k) p q := by
    have h := C.isChainFrom_arcPieces a k
    rwa [hva, hvb] at h
  have hchain2 : IsChainFrom (C.arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k)) q p := by
    have h := C.isChainFrom_arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k)
    rw [zmod_add_sub_cancel hk3 a] at h
    rwa [hva, hvb] at h
  have hclosed1 : IsClosedChain (C.arcPieces a k ++ segsOf ws) :=
    hchain1.isClosedChain_append hKchain
  have hclosed2 : IsClosedChain
      (C.arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k) ++ segsOf ws) :=
    isChainFrom_self_iff.1 (hchain2.append hKchain)
  have hcov1 : cover (C.arcPieces a k ++ segsOf ws) = C.arc a k ∪ P := by
    rw [cover_append, hKcover]
    rfl
  have hcov2 : cover (C.arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k) ++ segsOf ws)
      = C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P := by
    rw [cover_append, hKcover]
    rfl
  have hsplit : ∀ w : Plane,
      parity u (C.arcPieces a k ++ segsOf ws) w
        + parity u (C.arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k) ++ segsOf ws) w
        = parity u C.pieces w :=
    fun w => parity_split u (C.sameEdges_arcPieces_split a hk3) (List.Perm.refl _)
      (List.Perm.refl _) w
  have hexh : ∀ w ∈ Ω \ P, w ∈ farRegion (C.arc a k ∪ P) y ∨
      w ∈ farRegion (C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P) y := by
    intro w hw
    by_contra hcon
    push Not at hcon
    obtain ⟨hn1, hn2⟩ := hcon
    have hwJ : w ∉ J := hΩ.subset_compl hw.1
    have hw1 : w ∉ C.arc a k ∪ P := by
      rintro (h | h)
      · exact hwJ (hD1J h)
      · exact hw.2 h
    have hw2 : w ∉ C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P := by
      rintro (h | h)
      · exact hwJ (hD2J h)
      · exact hw.2 h
    have hmem1 : w ∈ connectedComponentIn (C.arc a k ∪ P)ᶜ y := by
      by_contra hc1
      exact hn1 ⟨hw1, hc1⟩
    have hmem2 : w ∈
        connectedComponentIn (C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P)ᶜ y := by
      by_contra hc2
      exact hn2 ⟨hw2, hc2⟩
    have hp1 : parity u (C.arcPieces a k ++ segsOf ws) w
        = parity u (C.arcPieces a k ++ segsOf ws) y :=
      parity_eq_of_mem_connectedComponentIn hu hlev1 hclosed1 (by rw [hcov1]; exact hyJ1)
        (by rw [hcov1]; exact hmem1)
    have hp2 : parity u (C.arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k) ++ segsOf ws) w
        = parity u (C.arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k) ++ segsOf ws) y :=
      parity_eq_of_mem_connectedComponentIn hu hlev2 hclosed2 (by rw [hcov2]; exact hyJ2)
        (by rw [hcov2]; exact hmem2)
    have hkey : parity u C.pieces w = parity u C.pieces y := by
      rw [← hsplit w, ← hsplit y, hp1, hp2]
    rcases hΩpair with ⟨hin, hout⟩ | ⟨hout, hin⟩
    · rw [C.parity_eq_one_of_mem_inside hu hlevC
          (show w ∈ inside C.carrier by rw [hcar]; exact hin ▸ hw.1),
        C.parity_eq_zero_of_mem_outside hu hlevC
          (show y ∈ outside C.carrier by rw [hcar]; exact hout ▸ hy)] at hkey
      exact absurd hkey (by decide)
    · rw [C.parity_eq_zero_of_mem_outside hu hlevC
          (show w ∈ outside C.carrier by rw [hcar]; exact hout ▸ hw.1),
        C.parity_eq_one_of_mem_inside hu hlevC
          (show y ∈ inside C.carrier by rw [hcar]; exact hin ▸ hy)] at hkey
      exact absurd hkey (by decide)
  -- 8. Read the conclusion off the identification of the two arcs.
  rcases hids with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rcases hexh z hz with hv | hv
    · exact Or.inl (by rw [e1, hV1comp z hv]; exact hJ1.isRegionOf_farRegion hyJ1)
    · exact Or.inr (by rw [e2, hV2comp z hv]; exact hJ2.isRegionOf_farRegion hyJ2)
  · rcases hexh z hz with hv | hv
    · exact Or.inr (by rw [e2, hV1comp z hv]; exact hJ1.isRegionOf_farRegion hyJ1)
    · exact Or.inl (by rw [e1, hV2comp z hv]; exact hJ2.isRegionOf_farRegion hyJ2)

end Schoenflies

namespace Graph

open scoped Graph

open Schoenflies

variable {β : Type*} {G B : Graph Plane β} {drawing : β → ℝ → Plane} {a b : Plane}

/-! ## `lem:face-cycles`, with nothing assumed

`Graph.IsDrawing.hasFaceCycles_union` and `Graph.face_cycles` of
`Schoenflies/FaceCyclesProof.lean` carry the hypothesis `Schoenflies.CrosscutSplitsRegion`;
`Schoenflies.crosscutSplitsRegion` above proves it, so here are the two statements with the
hypothesis discharged. **These are the forms a consumer should use.** Once this module's
`PrePolygon` development is hoisted above `Schoenflies/FaceCyclesProof.lean` the hypothesis can
be deleted from the originals and the primes here dropped. -/

/-- **One ear**, with no hypothesis assumed: `Graph.IsDrawing.hasFaceCycles_union` with
`Schoenflies.CrosscutSplitsRegion` discharged. -/
theorem IsDrawing.hasFaceCycles_union' [G.Finite] (h : IsDrawing G drawing)
    (hpoly : ∀ g ∈ E(G), IsPolygonal (edgeArc drawing g))
    (hBG : B ≤ G) (hmot : HasFaceCycles B drawing) {D' : List β}
    (hpath : G.IsPath a D' b) (hab : a ≠ b) (ha : a ∈ V(B)) (hb : b ∈ V(B))
    (hint : ∀ y ∈ G.walkVertices a D', y ≠ a → y ≠ b → y ∉ V(B))
    (hnew : ∀ g ∈ D', g ∉ E(B)) :
    HasFaceCycles (B.union (G.pathGraphOf a D')) drawing :=
  h.hasFaceCycles_union crosscutSplitsRegion hpoly hBG hmot hpath hab ha hb hint hnew

/-- **`lem:face-cycles` (face cycles).** Every face of a finite 2-connected polygonal plane graph
has a cycle as its boundary and is one of the two complementary regions of that cycle.

This is `Graph.face_cycles` with its hypothesis `Schoenflies.CrosscutSplitsRegion` discharged by
`Schoenflies.crosscutSplitsRegion`; nothing is assumed. -/
theorem face_cycles' [G.Finite] (h : IsDrawing G drawing)
    (hpoly : ∀ g ∈ E(G), IsPolygonal (edgeArc drawing g)) (hG : G.IsTwoConnected) :
    HasFaceCycles G drawing :=
  face_cycles crosscutSplitsRegion h hpoly hG

/-- **Every bounded face is the interior of its boundary cycle.** -/
theorem IsFaceCycle.eq_inside_of_isBounded' {z : Plane} {e : β} {u v : Plane} {D : List β}
    (hf : IsFaceCycle G drawing z e u v D)
    (hbdd : Bornology.IsBounded (face G drawing z)) :
    face G drawing z = Schoenflies.inside (edgesCover drawing (e :: D)) :=
  hf.eq_inside_of_isBounded hbdd

end Graph

end BundlePart419
