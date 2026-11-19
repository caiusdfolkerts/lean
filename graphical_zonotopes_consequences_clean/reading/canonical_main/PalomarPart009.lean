module

public import canonical_main.PalomarPart008
import all canonical_main.PalomarPart008
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

section BundlePart423
/- Source: dev/planar_search/schoenflies_port/Schoenflies/Graph/K33Closed.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/



/-!
# Discharging the realization hypothesis of `lem:k33`

`Schoenflies/Graph/K33Planar.lean` proves the nonplanarity of `K(3,3)` from one assumption,
`Graph.IsHexRealization`: that the six-cycle, the two arcs the chord cuts it into, and the two
closed curves the chord forms with them are all presented by cyclic vertex lists.
`Schoenflies/Realization.lean` now supplies the presentations. This module wires the two
together.

## Blueprint

* `Schoenflies.exists_poly_anchored`, `Schoenflies.IsPolygonal.union`,
  `Graph.IsDrawing.isPolygonal_edgesCover` — §1: a polygonal set is the carrier of a vertex list
  running between any two of its points, so two polygonal sets that meet have a polygonal union,
  and a walk of a polygonal plane graph draws a polygonal set.
* `Schoenflies.ClosedPolygon.reverse` — a closed polygon read backwards.
* `Schoenflies.ClosedPolygon.arc_vertex_eq`, `…arcPieces_eq` — **the decomposition of an arc is
  the arc's own**: two closed polygons that share an arc, starting at the same vertex, run
  through the same vertices along it. This is what makes the three presentations below fit
  together into one crosscut.
* `Schoenflies.exists_closedPolygon_arcs_oriented` — the realization of a splitting with the
  first arc's *direction* fixed as well, so that two realizations of one arc can be compared.
* `Graph.IsK33Config.isPolygonal_hexSet`, `…chord_inter_arcA`, `…chord_inter_arcB` — the three
  curves the crosscut is built from, as polygonal Jordan curves.
* `Graph.IsHexGeneric` — the general-position hypothesis that survives: at each of the two cut
  points, the six-cycle and both spliced curves turn.
* `Graph.IsK33Config.isHexRealization` — `Graph.IsHexRealization`, discharged from it. **This is
  the theorem this module exists for.**
* `Graph.Bendable`, `Graph.IsK33Config.false_of_hexGeneric`, `…not_isDrawing_of_bendable`,
  `Graph.IsArcK33.false_of_bendable`, `Graph.IsK33Subdivision.false_of_bendable`,
  `Graph.k33Graph_not_isDrawing` — `lem:k33` and `cor:k33-subdivision` with `IsHexRealization`
  replaced by `IsHexGeneric`.

## What is still assumed, and why — READ THIS BEFORE USING THE THEOREMS BELOW

**Milestone H8 is not closed here.** `Graph.IsHexRealization` is gone, but a strictly smaller
hypothesis has taken its place, and it is not discharged.

`Schoenflies.ClosedPolygon` forbids a vertex at which the curve runs straight through, and
`Schoenflies.ClosedPolygon.isCornerAt_vertex` says that this is not a defect of the proofs:
*every* vertex of *every* realization is a corner of the curve. A crosscut whose ends are cut
points of `C` therefore forces those ends to be corners — of `C`, and of both curves the
crosscut forms with the two arcs. `Graph.IsHexGeneric` says exactly that and nothing more, and
by the two corner theorems it cannot be weakened while the crosscut is presented as a
`Schoenflies.IsPolygonalCrosscut`.

For a drawn `K(3,3)` it is the statement that at each of the six vertices the three edges leave
along three pairwise non-collinear germs. A polygonal drawing need not have that: two of the
three edges at a vertex may leave along exactly opposite rays, which is perfectly compatible
with the drawing condition. The remaining gap is therefore a *bending* lemma — every polygonal
drawing can be redrawn so that no two edges at a vertex are collinear there — and it is
genuinely about changing the drawing, not about presentations. `Graph.Bendable` is that
statement in the shape the theorems below consume; nothing here proves it.
-/

open Metric Set unitInterval
open scoped Graph

namespace Schoenflies

/-! ## A polygonal set is a vertex list between any two of its points

`Schoenflies.IsPolygonal` is "the carrier of a vertex list", and a vertex list carries a *path*,
so the predicate is not closed under arbitrary finite unions — two disjoint segments are not the
carrier of any one list. It is closed under unions that meet, and the way to see that is to move
the ends of the list: a list can be made to start and end wherever one likes on its own carrier,
by running out and back. -/

/-! ## A closed polygon read backwards

A realization of a splitting names its two arcs *in a direction*, and two realizations of one
arc need not agree on it. Reversing the cyclic order is what reconciles them. -/

namespace ClosedPolygon

variable {m : ℕ}

/-- **The same closed polygon, traversed the other way.** -/
def reverse (P : ClosedPolygon m) : ClosedPolygon m where
  vertex j := P.vertex (-j)
  vertex_inj _ _ h := neg_injective (P.vertex_inj h)
  edges_meet i j hij := by
    have e1 : (-(i + 1) : ZMod (m + 3)) = -i - 1 := by ring
    have e2 : (-(j + 1) : ZMod (m + 3)) = -j - 1 := by ring
    have e3 : (-i - 1 : ZMod (m + 3)) + 1 = -i := by ring
    have e4 : (-j - 1 : ZMod (m + 3)) + 1 = -j := by ring
    have hij' : (-i - 1 : ZMod (m + 3)) ≠ -j - 1 := fun h => hij (by linear_combination -h)
    have h := P.edges_meet (-i - 1) (-j - 1) hij'
    rw [e3, e4] at h
    simp only [e1, e2]
    rw [segment_symm ℝ (P.vertex (-i)) (P.vertex (-i - 1)),
      segment_symm ℝ (P.vertex (-j)) (P.vertex (-j - 1)), Set.pair_comm]
    exact h
  corner i := by
    have e1 : (-(i - 1) : ZMod (m + 3)) = -i + 1 := by ring
    have e2 : (-(i + 1) : ZMod (m + 3)) = -i - 1 := by ring
    simp only [e1, e2]
    rw [Plane.det_comm]
    exact fun h => P.corner (-i) (by linear_combination -h)

@[simp] theorem reverse_vertex (P : ClosedPolygon m) (j : ZMod (m + 3)) :
    P.reverse.vertex j = P.vertex (-j) := rfl

theorem reverse_edge (P : ClosedPolygon m) (j : ZMod (m + 3)) :
    P.reverse.edge j = P.edge (-j - 1) := by
  rw [edge, edge, reverse_vertex, reverse_vertex,
    show (-(j + 1) : ZMod (m + 3)) = -j - 1 by ring,
    show (-j - 1 : ZMod (m + 3)) + 1 = -j by ring]
  exact segment_symm ℝ _ _

@[simp] theorem reverse_carrier (P : ClosedPolygon m) : P.reverse.carrier = P.carrier := by
  ext z
  constructor
  · intro hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hz
    rw [reverse_edge] at hi
    exact Set.mem_iUnion.2 ⟨_, hi⟩
  · intro hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hz
    refine Set.mem_iUnion.2 ⟨-i - 1, ?_⟩
    rw [reverse_edge, show (-(-i - 1) - 1 : ZMod (m + 3)) = i by ring]
    exact hi

/-- The `t`-th edge of the reversed arc is the `k - 1 - t`-th of the original: the same edges,
listed backwards. -/
theorem reverse_natCast {n k t : ℕ} (ht : t < k) :
    ((k - t - 1 : ℕ) : ZMod n) + (t : ZMod n) + 1 = (k : ZMod n) := by
  have h : (k - t - 1) + t + 1 = k := by omega
  have hc := congrArg (fun j : ℕ => (j : ZMod n)) h
  push_cast at hc
  linear_combination hc

/-- **Reversing does not move an arc**, it only starts it at the other end. -/
theorem reverse_arc (P : ClosedPolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    P.reverse.arc (-a - (k : ZMod (m + 3))) k = P.arc a k := by
  ext z
  rw [mem_arc_iff, mem_arc_iff]
  constructor
  · rintro ⟨t, ht, hz⟩
    rw [reverse_edge] at hz
    refine ⟨k - t - 1, by omega, ?_⟩
    rw [show a + ((k - t - 1 : ℕ) : ZMod (m + 3))
        = -(-a - (k : ZMod (m + 3)) + (t : ZMod (m + 3))) - 1 by
      linear_combination reverse_natCast (n := m + 3) ht]
    exact hz
  · rintro ⟨t, ht, hz⟩
    refine ⟨k - t - 1, by omega, ?_⟩
    rw [reverse_edge, show -(-a - (k : ZMod (m + 3)) + ((k - t - 1 : ℕ) : ZMod (m + 3))) - 1
        = a + (t : ZMod (m + 3)) by linear_combination -reverse_natCast (n := m + 3) ht]
    exact hz

/-- **Reversing does not change the edge list either**, up to the order and the naming of each
edge's two ends — which is exactly what `Schoenflies.SameEdges` forgives. -/
theorem sameEdges_reverse_arcPieces (P : ClosedPolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    SameEdges (P.reverse.arcPieces (-a - (k : ZMod (m + 3))) k) (P.arcPieces a k) := by
  have key : (P.reverse.arcPieces (-a - (k : ZMod (m + 3))) k).map orientPiece
      = ((P.arcPieces a k).map orientPiece).reverse := by
    rw [arcPieces, arcPieces, List.map_map, List.map_map, ← List.map_reverse,
      List.range_eq_range', List.reverse_range', ← List.range_eq_range', List.map_map]
    refine List.map_congr_left fun t ht => ?_
    have htk : t < k := List.mem_range.1 ht
    have he : (0 + k - 1 - t : ℕ) = k - t - 1 := by omega
    simp only [Function.comp_apply, he, reverse_vertex]
    rw [show -(-a - (k : ZMod (m + 3)) + (t : ZMod (m + 3)))
          = a + ((k - t - 1 : ℕ) : ZMod (m + 3)) + 1 by
        linear_combination -reverse_natCast (n := m + 3) htk,
      show -(-a - (k : ZMod (m + 3)) + (t : ZMod (m + 3)) + 1)
        = a + ((k - t - 1 : ℕ) : ZMod (m + 3)) by
        linear_combination -reverse_natCast (n := m + 3) htk]
    exact orientPiece_swap (_, _)
  rw [SameEdges, key]
  exact List.reverse_perm _

/-! ## The decomposition of an arc is the arc's own

`Graph.IsHexRealization` asks for three closed polygons that agree on the arcs they share. They
are found independently, and nothing so far says they agree — until this: two closed polygons
carrying the same arc, and starting it at the same vertex, run through the same vertices along
it. The proof walks the arc: the first edges of the two are two segments leaving one point along
one ray, so one contains the other, and the shorter one's far end would be a vertex of its own
polygon interior to an edge of the other — which `corner` forbids. -/

/-- A numeral strictly between `0` and the modulus is not `0` in the cyclic index. -/
theorem natCast_ne_zero_of_lt {m t : ℕ} (ht1 : 0 < t) (ht2 : t < m + 3) :
    ((t : ℕ) : ZMod (m + 3)) ≠ 0 := by
  intro h
  have h0 : ((t : ℕ) : ZMod (m + 3)) = ((0 : ℕ) : ZMod (m + 3)) := by simpa using h
  have := natCast_inj (m := m) ht2 (by omega) h0
  omega

/-- **The first vertex of an arc lies on none of its later edges** — a step index below the
modulus reaches neither the edge leaving that vertex nor the one arriving at it. -/
theorem vertex_notMem_edge_natCast (P : ClosedPolygon m) (a : ZMod (m + 3)) {t : ℕ}
    (ht1 : 0 < t) (ht2 : t < m + 2) : P.vertex a ∉ P.edge (a + (t : ZMod (m + 3))) := by
  refine vertex_notMem_edge (fun h => ?_) (fun h => ?_)
  · exact natCast_ne_zero_of_lt (t := t + 1) (m := m) (by omega) (by omega)
      (by push_cast; linear_combination h)
  · exact natCast_ne_zero_of_lt (m := m) ht1 (by omega) (by linear_combination h)

/-- **Around a point that no later edge of the arc reaches, the arc is its first edge alone.** -/
theorem exists_ball_arc_subset_edge (P : ClosedPolygon m) (a : ZMod (m + 3)) (k : ℕ) {w : Plane}
    (hw : ∀ t : ℕ, 0 < t → t < k → w ∉ P.edge (a + (t : ZMod (m + 3)))) :
    ∃ r > 0, ball w r ∩ P.arc a k ⊆ P.edge a := by
  obtain ⟨r, hr, hball⟩ := exists_pos_forall_of_finite
    (S := {t : ℕ | 0 < t ∧ t < k})
    ((Set.finite_Icc 0 k).subset fun t ht => ⟨Nat.zero_le t, ht.2.le⟩)
    (P := fun t ε => ∀ y ∈ ball w ε, y ∉ P.edge (a + (t : ZMod (m + 3))))
    (fun _ _ _ _ hδε hQ y hy => hQ y (ball_subset_ball hδε hy))
    (fun t ht => by
      obtain ⟨ρ, hρ, hsub⟩ := Metric.isOpen_iff.1
        (isCompact_segment _ _).isClosed.isOpen_compl w (hw t ht.1 ht.2)
      exact ⟨ρ, hρ, fun y hy => hsub hy⟩)
  refine ⟨r, hr, ?_⟩
  rintro z ⟨hzb, hzA⟩
  obtain ⟨t, ht, hzt⟩ := mem_arc_iff.1 hzA
  rcases Nat.eq_zero_or_pos t with rfl | htpos
  · simpa using hzt
  · exact absurd hzt (hball t ⟨htpos, ht⟩ z hzb)

/-- Bounds a step along two directions inside one ball. -/
theorem exists_step_lt {ρ : ℝ} (hρ : 0 < ρ) (u v : Plane) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧ s * ‖u‖ < ρ ∧ s * ‖v‖ < ρ := by
  refine ⟨min 1 (ρ / (2 * (‖u‖ + ‖v‖ + 1))), lt_min one_pos (by positivity), min_le_left _ _,
    ?_, ?_⟩
  · calc min 1 (ρ / (2 * (‖u‖ + ‖v‖ + 1))) * ‖u‖
        ≤ (ρ / (2 * (‖u‖ + ‖v‖ + 1))) * ‖u‖ :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg u)
      _ < ρ := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [norm_nonneg u, norm_nonneg v]
  · calc min 1 (ρ / (2 * (‖u‖ + ‖v‖ + 1))) * ‖v‖
        ≤ (ρ / (2 * (‖u‖ + ‖v‖ + 1))) * ‖v‖ :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg v)
      _ < ρ := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [norm_nonneg u, norm_nonneg v]

/-- **Two segments leaving one point and agreeing near it leave along the same ray.** -/
theorem exists_pos_smul_of_ball_subset {v₀ v₁ u₁ : Plane} {r : ℝ} (hr : 0 < r) (hv : v₁ ≠ v₀)
    (hsub : segment ℝ v₀ v₁ ∩ ball v₀ r ⊆ segment ℝ v₀ u₁) :
    ∃ c : ℝ, 0 < c ∧ v₁ - v₀ = c • (u₁ - v₀) := by
  have hdne : v₁ - v₀ ≠ 0 := sub_ne_zero.2 hv
  obtain ⟨t, htpos, htle, ht, -⟩ := exists_step_lt hr (v₁ - v₀) (v₁ - v₀)
  have hzs : v₀ + t • (v₁ - v₀) ∈ segment ℝ v₀ v₁ := by
    rw [segment_eq_image' ℝ v₀ v₁]; exact ⟨t, ⟨htpos.le, htle⟩, rfl⟩
  have hzb : v₀ + t • (v₁ - v₀) ∈ ball v₀ r := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos htpos]
    exact ht
  have hmem := hsub ⟨hzs, hzb⟩
  rw [segment_eq_image' ℝ v₀ u₁] at hmem
  obtain ⟨θ, hθ, hθe⟩ := hmem
  simp only at hθe
  have hkey : t • (v₁ - v₀) = θ • (u₁ - v₀) := by
    linear_combination (norm := module) -hθe
  have hθpos : 0 < θ := by
    rcases lt_or_eq_of_le hθ.1 with h | h
    · exact h
    · exfalso
      rw [← h, zero_smul] at hkey
      exact hdne ((smul_eq_zero.1 hkey).resolve_left htpos.ne')
  refine ⟨θ / t, by positivity, ?_⟩
  have hrw : (θ / t) • (u₁ - v₀) = (1 / t) • (θ • (u₁ - v₀)) := by
    rw [smul_smul]; congr 1; field_simp
  rw [hrw, ← hkey, smul_smul, one_div, inv_mul_cancel₀ htpos.ne', one_smul]

/-- **A vertex of one polygon is never interior to the other's first edge.** Either the shared
arc is that single edge — and then the far end of the edge cannot be strictly inside it — or the
other polygon has two edges at the vertex, both lying near it inside one straight segment, which
is what its `corner` field forbids. -/
theorem notMem_openSegment_first_edge {m m' : ℕ} (P : ClosedPolygon m) (Q : ClosedPolygon m')
    (a : ZMod (m + 3)) (b : ZMod (m' + 3)) {k l : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ m + 2)
    (hl1 : 1 ≤ l) (harc : P.arc a k = Q.arc b l) (hstart : P.vertex a = Q.vertex b) :
    Q.vertex (b + 1) ∉ openSegment ℝ (P.vertex a) (P.vertex (a + 1)) := by
  intro hw
  have hedgeP : P.edge a ⊆ P.arc a k := fun z hz =>
    mem_arc_iff.2 ⟨0, by omega, by simpa using hz⟩
  rcases eq_or_lt_of_le hl1 with hl | hl
  · -- `l = 1`: the arc is `Q`'s single edge, which *ends* at the point in question.
    subst hl
    have hQarc : Q.arc b 1 = segment ℝ (P.vertex a) (Q.vertex (b + 1)) := by
      refine Set.Subset.antisymm (fun z hz => ?_) (fun z hz => ?_)
      · obtain ⟨t, ht, hzt⟩ := mem_arc_iff.1 hz
        have ht0 : t = 0 := by omega
        subst ht0
        rw [hstart]
        simpa [edge] using hzt
      · refine mem_arc_iff.2 ⟨0, by omega, ?_⟩
        rw [hstart] at hz
        simpa [edge] using hz
    have hmem : P.vertex (a + 1) ∈ segment ℝ (P.vertex a) (Q.vertex (b + 1)) := by
      rw [← hQarc, ← harc]
      exact hedgeP (right_mem_segment ℝ _ _)
    -- Reading both memberships as parameters: `μ θ = 1` with `θ < 1` and `μ ≤ 1`.
    rw [openSegment_eq_image' ℝ] at hw
    rw [segment_eq_image' ℝ] at hmem
    obtain ⟨θ, hθ, hθe⟩ := hw
    obtain ⟨μ, hμ, hμe⟩ := hmem
    simp only at hθe hμe
    have hne : P.vertex (a + 1) - P.vertex a ≠ 0 := sub_ne_zero.2 (P.vertex_ne a).symm
    have hkey : (1 - μ * θ) • (P.vertex (a + 1) - P.vertex a) = 0 := by
      linear_combination (norm := module) -hμe - μ • hθe
    rcases smul_eq_zero.1 hkey with h | h
    · nlinarith [hθ.1, hθ.2, hμ.1, hμ.2]
    · exact hne h
  · -- `l ≥ 2`: `Q` turns at the point, but near it the arc is one straight segment.
    obtain ⟨ρ, hρ, hball⟩ := P.exists_ball_arc_subset_edge a k (w := Q.vertex (b + 1))
      fun t ht1 ht2 => notMem_edge_of_mem_openSegment
        (fun h => natCast_ne_zero_of_lt (m := m) ht1 (by omega) (by linear_combination h)) hw
    obtain ⟨s, hs0, hs1, hsu, hsv⟩ :=
      exists_step_lt hρ (Q.vertex b - Q.vertex (b + 1)) (Q.vertex (b + 2) - Q.vertex (b + 1))
    have hstep : ∀ y : Plane, s * ‖y - Q.vertex (b + 1)‖ < ρ →
        Q.vertex (b + 1) + s • (y - Q.vertex (b + 1)) ∈ ball (Q.vertex (b + 1)) ρ := by
      intro y hy
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos hs0]
      exact hy
    have hseg : ∀ y : Plane,
        Q.vertex (b + 1) + s • (y - Q.vertex (b + 1)) ∈ segment ℝ (Q.vertex (b + 1)) y :=
      fun y => by rw [segment_eq_image' ℝ]; exact ⟨s, ⟨hs0.le, hs1⟩, rfl⟩
    have hz₁ : Q.vertex (b + 1) + s • (Q.vertex b - Q.vertex (b + 1)) ∈ P.edge a := by
      refine hball ⟨hstep _ hsu, ?_⟩
      rw [harc]
      refine mem_arc_iff.2 ⟨0, by omega, ?_⟩
      rw [show b + ((0 : ℕ) : ZMod (m' + 3)) = b by simp, edge,
        segment_symm ℝ (Q.vertex b) (Q.vertex (b + 1))]
      exact hseg (Q.vertex b)
    have hz₂ : Q.vertex (b + 1) + s • (Q.vertex (b + 2) - Q.vertex (b + 1)) ∈ P.edge a := by
      refine hball ⟨hstep _ hsv, ?_⟩
      rw [harc]
      refine mem_arc_iff.2 ⟨1, by omega, ?_⟩
      rw [show b + ((1 : ℕ) : ZMod (m' + 3)) = b + 1 by push_cast; ring, edge,
        show b + 1 + 1 = b + 2 by ring]
      exact hseg (Q.vertex (b + 2))
    have hwmem : Q.vertex (b + 1) ∈ P.edge a := openSegment_subset_segment ℝ _ _ hw
    have hdet := det_eq_zero_of_mem_segment hz₁ hz₂ hwmem
    rw [add_sub_cancel_left, add_sub_cancel_left, Plane.det_smul_left, Plane.det_smul_right]
      at hdet
    refine Q.corner (b + 1) ?_
    rw [show b + 1 - 1 = b by ring, show b + 1 + 1 = b + 2 by ring]
    rcases mul_eq_zero.1 hdet with h | h
    · exact absurd h hs0.ne'
    · rcases mul_eq_zero.1 h with h' | h'
      · exact absurd h' hs0.ne'
      · exact h'

/-- Stepping the cyclic index by a positive numeral. -/
theorem natCast_pred_succ {n t : ℕ} (ht : 0 < t) : ((t - 1 : ℕ) : ZMod n) + 1 = (t : ZMod n) := by
  have h : (t - 1) + 1 = t := by omega
  have hc := congrArg (fun j : ℕ => (j : ZMod n)) h
  push_cast at hc
  linear_combination hc

/-- **An arc is its first edge together with the arc that leaves the next vertex.** -/
theorem arc_succ (P : ClosedPolygon m) (a : ZMod (m + 3)) {k : ℕ} (hk : 1 ≤ k) :
    P.arc a k = P.edge a ∪ P.arc (a + 1) (k - 1) := by
  ext z
  rw [mem_arc_iff, Set.mem_union, mem_arc_iff]
  constructor
  · rintro ⟨t, ht, hz⟩
    rcases Nat.eq_zero_or_pos t with rfl | htpos
    · exact Or.inl (by simpa using hz)
    · refine Or.inr ⟨t - 1, by omega, ?_⟩
      rw [show a + 1 + ((t - 1 : ℕ) : ZMod (m + 3)) = a + (t : ZMod (m + 3)) by
        linear_combination natCast_pred_succ (n := m + 3) htpos]
      exact hz
  · rintro (hz | ⟨t, ht, hz⟩)
    · exact ⟨0, by omega, by simpa using hz⟩
    · refine ⟨t + 1, by omega, ?_⟩
      rw [show a + ((t + 1 : ℕ) : ZMod (m + 3)) = a + 1 + (t : ZMod (m + 3)) by push_cast; ring]
      exact hz

/-- **The first edge of an arc meets the rest of it only at the vertex between them.** -/
theorem edge_inter_arc_succ (P : ClosedPolygon m) (a : ZMod (m + 3)) {k : ℕ} (hk : k ≤ m + 2) :
    P.edge a ∩ P.arc (a + 1) (k - 1) ⊆ {P.vertex (a + 1)} := by
  rintro z ⟨hze, hza⟩
  obtain ⟨t, ht, hzt⟩ := mem_arc_iff.1 hza
  rw [show a + 1 + (t : ZMod (m + 3)) = a + ((t + 1 : ℕ) : ZMod (m + 3)) by push_cast; ring] at hzt
  have hne : a ≠ a + ((t + 1 : ℕ) : ZMod (m + 3)) := fun h =>
    natCast_ne_zero_of_lt (m := m) (t := t + 1) (by omega) (by omega) (by linear_combination -h)
  have hmem := P.edges_meet a (a + ((t + 1 : ℕ) : ZMod (m + 3))) hne ⟨hze, hzt⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem ⊢
  rcases hmem with rfl | rfl
  · exact absurd hzt (P.vertex_notMem_edge_natCast a (by omega) (by omega))
  · rfl

/-- **A one-edge arc has no second edge.** If the same arc were also presented with two or more
edges, its second edge would lie inside its first, which `edges_meet` forbids. -/
theorem arc_one_ne {m m' : ℕ} (P : ClosedPolygon m) (Q : ClosedPolygon m') (a : ZMod (m + 3))
    (b : ZMod (m' + 3)) {l : ℕ} (hl : 2 ≤ l) (harc : P.arc a 1 = Q.arc b l)
    (hedge : P.edge a = Q.edge b) : False := by
  have hsub : Q.edge (b + 1) ⊆ Q.edge b := by
    intro z hz
    have hzQ : z ∈ Q.arc b l := mem_arc_iff.2 ⟨1, by omega, by
      rw [show b + ((1 : ℕ) : ZMod (m' + 3)) = b + 1 by push_cast; ring]; exact hz⟩
    rw [← harc] at hzQ
    obtain ⟨t, ht, hzt⟩ := mem_arc_iff.1 hzQ
    have ht0 : t = 0 := by omega
    subst ht0
    rw [← hedge]
    simpa using hzt
  obtain ⟨p, hp, hp1, hp2⟩ := PrePolygon.exists_mem_segment_ne (Q.vertex_ne (b + 1))
  have hmem := Q.edges_meet (b + 1) b (succ_ne_self b) ⟨hp, hsub hp⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h
  exacts [hp1 h, hp2 h]

/-- **Two closed polygons that carry the same arc, starting it at the same vertex, run through
the same vertices along it** — and in particular use the same number of edges. This is what makes
independent realizations of the six-cycle and of the two spliced curves agree. -/
theorem arc_vertex_eq : ∀ (k : ℕ) {m m' : ℕ} (P : ClosedPolygon m) (Q : ClosedPolygon m')
    (a : ZMod (m + 3)) (b : ZMod (m' + 3)) (l : ℕ), 1 ≤ k → k ≤ m + 2 → 1 ≤ l → l ≤ m' + 2 →
      P.arc a k = Q.arc b l → P.vertex a = Q.vertex b →
      k = l ∧ ∀ t : ℕ, t ≤ k →
        P.vertex (a + (t : ZMod (m + 3))) = Q.vertex (b + (t : ZMod (m' + 3))) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro m m' P Q a b l hk1 hk2 hl1 hl2 harc hstart
    -- The two first edges leave the common vertex along one ray, and neither may overshoot the
    -- other: the shorter one's far end would be a vertex of its polygon interior to the other's
    -- edge.
    have hA : Q.vertex (b + 1) ∉ openSegment ℝ (P.vertex a) (P.vertex (a + 1)) :=
      notMem_openSegment_first_edge P Q a b hk1 hk2 hl1 harc hstart
    have hB : P.vertex (a + 1) ∉ openSegment ℝ (Q.vertex b) (Q.vertex (b + 1)) :=
      notMem_openSegment_first_edge Q P b a hl1 hl2 hk1 harc.symm hstart.symm
    obtain ⟨rP, hrP, hballP⟩ := P.exists_ball_arc_subset_edge a k (w := P.vertex a)
      fun t ht1 ht2 => P.vertex_notMem_edge_natCast a ht1 (by omega)
    obtain ⟨rQ, hrQ, hballQ⟩ := Q.exists_ball_arc_subset_edge b l (w := Q.vertex b)
      fun t ht1 ht2 => Q.vertex_notMem_edge_natCast b ht1 (by omega)
    have hsub : segment ℝ (P.vertex a) (P.vertex (a + 1)) ∩ ball (P.vertex a) (min rP rQ)
        ⊆ segment ℝ (P.vertex a) (Q.vertex (b + 1)) := by
      rintro z ⟨hzs, hzb⟩
      have hzA : z ∈ P.arc a k := mem_arc_iff.2 ⟨0, by omega, by simpa [edge] using hzs⟩
      have hzQ := hballQ ⟨by rw [← hstart]; exact ball_subset_ball (min_le_right _ _) hzb,
        by rw [← harc]; exact hzA⟩
      rw [edge, ← hstart] at hzQ
      exact hzQ
    obtain ⟨c, hc, hce⟩ :=
      exists_pos_smul_of_ball_subset (lt_min hrP hrQ) (P.vertex_ne a).symm hsub
    have hv1 : P.vertex (a + 1) = Q.vertex (b + 1) := by
      rcases lt_trichotomy c 1 with hlt | heq | hgt
      · refine absurd ?_ hB
        rw [← hstart, openSegment_eq_image' ℝ]
        exact ⟨c, ⟨hc, hlt⟩, by linear_combination (norm := module) -hce⟩
      · rw [heq, one_smul] at hce
        exact sub_left_inj.1 hce
      · have hq : P.vertex a + (1 / c) • (P.vertex (a + 1) - P.vertex a) = Q.vertex (b + 1) := by
          rw [hce, smul_smul, one_div, inv_mul_cancel₀ (by linarith), one_smul, add_sub_cancel]
        refine absurd ?_ hA
        rw [openSegment_eq_image' ℝ]
        exact ⟨1 / c, ⟨by positivity, by rw [div_lt_one (by linarith)]; linarith⟩, hq⟩
    have hedge : P.edge a = Q.edge b := by rw [edge, edge, hstart, hv1]
    rcases Nat.lt_or_ge k 2 with hk | hk
    · -- One edge each: the arc is a single segment.
      have hk' : k = 1 := by omega
      subst hk'
      have hl' : l = 1 := by
        by_contra hcon
        exact arc_one_ne P Q a b (by omega) harc hedge
      subst hl'
      refine ⟨rfl, fun t ht => ?_⟩
      interval_cases t
      · simpa using hstart
      · simpa using hv1
    · -- Both arcs continue: strip the common first edge and recurse.
      have hl' : 2 ≤ l := by
        by_contra hcon
        have hl1' : l = 1 := by omega
        subst hl1'
        exact arc_one_ne Q P b a (by omega) harc.symm hedge.symm
      have hsplitP := P.arc_succ a hk1
      have hsplitQ := Q.arc_succ b hl1
      have hinterP := P.edge_inter_arc_succ a (k := k) hk2
      have hinterQ := Q.edge_inter_arc_succ b (k := l) hl2
      have hmemP : P.vertex (a + 1) ∈ P.arc (a + 1) (k - 1) := P.vertex_mem_arc (a + 1) (by omega)
      have hmemQ : Q.vertex (b + 1) ∈ Q.arc (b + 1) (l - 1) := Q.vertex_mem_arc (b + 1) (by omega)
      have htail : P.arc (a + 1) (k - 1) = Q.arc (b + 1) (l - 1) := by
        refine Set.Subset.antisymm (fun z hz => ?_) (fun z hz => ?_)
        · have hzQ : z ∈ Q.arc b l := by rw [← harc, hsplitP]; exact Or.inr hz
          rw [hsplitQ] at hzQ
          rcases hzQ with hzE | hzR
          · have hzv : z = P.vertex (a + 1) := hinterP ⟨by rw [hedge]; exact hzE, hz⟩
            rw [hzv, hv1]; exact hmemQ
          · exact hzR
        · have hzP : z ∈ P.arc a k := by rw [harc, hsplitQ]; exact Or.inr hz
          rw [hsplitP] at hzP
          rcases hzP with hzE | hzR
          · have hzv : z = Q.vertex (b + 1) := hinterQ ⟨by rw [← hedge]; exact hzE, hz⟩
            rw [hzv, ← hv1]; exact hmemP
          · exact hzR
      obtain ⟨hkl, hvt⟩ := ih (k - 1) (by omega) P Q (a + 1) (b + 1) (l - 1)
        (by omega) (by omega) (by omega) (by omega) htail hv1
      refine ⟨by omega, fun t ht => ?_⟩
      rcases Nat.eq_zero_or_pos t with rfl | htpos
      · simpa using hstart
      · have hstep := hvt (t - 1) (by omega)
        rw [show a + 1 + ((t - 1 : ℕ) : ZMod (m + 3)) = a + (t : ZMod (m + 3)) by
            linear_combination natCast_pred_succ (n := m + 3) htpos,
          show b + 1 + ((t - 1 : ℕ) : ZMod (m' + 3)) = b + (t : ZMod (m' + 3)) by
            linear_combination natCast_pred_succ (n := m' + 3) htpos] at hstep
        exact hstep

/-- **Two closed polygons that carry the same arc, starting it at the same vertex, cut it into
the same edges.** -/
theorem arcPieces_eq {m m' : ℕ} (P : ClosedPolygon m) (Q : ClosedPolygon m') (a : ZMod (m + 3))
    (b : ZMod (m' + 3)) {k l : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ m + 2) (hl1 : 1 ≤ l)
    (hl2 : l ≤ m' + 2) (harc : P.arc a k = Q.arc b l) (hstart : P.vertex a = Q.vertex b) :
    P.arcPieces a k = Q.arcPieces b l := by
  obtain ⟨hkl, hv⟩ := arc_vertex_eq k P Q a b l hk1 hk2 hl1 hl2 harc hstart
  subst hkl
  refine List.map_congr_left fun t ht => ?_
  have htk : t < k := List.mem_range.1 ht
  have h1 := hv t htk.le
  have h2 := hv (t + 1) htk
  rw [show a + ((t + 1 : ℕ) : ZMod (m + 3)) = a + (t : ZMod (m + 3)) + 1 by push_cast; ring,
    show b + ((t + 1 : ℕ) : ZMod (m' + 3)) = b + (t : ZMod (m' + 3)) + 1 by push_cast; ring]
    at h2
  rw [h1, h2]

end ClosedPolygon

/-- **The realization of a splitting, with the first arc's direction fixed too.** The two arcs of
`Schoenflies.exists_closedPolygon_arcs_ordered` come out in the order they were given, but the
polygon may traverse them either way; reading it backwards when it does is what pins the first
arc to start at `p`. Two realizations of one arc can then be compared with
`Schoenflies.ClosedPolygon.arcPieces_eq`. -/
theorem exists_closedPolygon_arcs_oriented {C A₁ A₂ : Set Plane} (hJ : IsJordanCurve C)
    (hP : IsPolygonal C) {p q : Plane} (hp : IsCornerAt C p) (hq : IsCornerAt C q) (hpq : p ≠ q)
    (hA1 : IsArcBetween A₁ p q) (hA2 : IsArcBetween A₂ p q) (hunion : A₁ ∪ A₂ = C)
    (hinter : A₁ ∩ A₂ = {p, q}) :
    ∃ (m : ℕ) (P : ClosedPolygon m) (a : ZMod (m + 3)) (k : ℕ), P.carrier = C ∧
      1 ≤ k ∧ k ≤ m + 2 ∧ P.vertex a = p ∧ P.vertex (a + (k : ZMod (m + 3))) = q ∧
      P.arc a k = A₁ ∧ P.arc (a + (k : ZMod (m + 3))) (m + 3 - k) = A₂ := by
  obtain ⟨m, P, a, k, hcar, hpa, hqa, hk1, hk2⟩ :=
    exists_closedPolygon_split hJ hP hp hq hpq
  have hD1 : IsArcBetween (P.arc a k) p q := by
    rw [← hpa, ← hqa]; exact P.isArcBetween_arc a hk1 hk2
  have hD2 : IsArcBetween (P.arc (a + (k : ZMod (m + 3))) (m + 3 - k)) p q := by
    have h := P.isArcBetween_arc (a + (k : ZMod (m + 3))) (k := m + 3 - k) (by omega) (by omega)
    rw [zmod_add_sub_cancel (by omega) a] at h
    rw [← hpa, ← hqa]
    exact h.reverse
  have hDunion : P.arc a k ∪ P.arc (a + (k : ZMod (m + 3))) (m + 3 - k) = C := by
    rw [P.arc_union a (by omega), hcar]
  have hDinter : P.arc a k ∩ P.arc (a + (k : ZMod (m + 3))) (m + 3 - k) = {p, q} := by
    rw [P.arc_inter a hk1 hk2, hpa, hqa]
  rcases two_arcs_unique hunion hinter hDunion hDinter hA1 hA2 hD1 hD2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact ⟨m, P, a, k, hcar, hk1, hk2, hpa, hqa, e1.symm, e2.symm⟩
  · -- The realization runs the two arcs the other way round: read it backwards.
    have hneg : ((m + 3 - k : ℕ) : ZMod (m + 3)) = -(k : ZMod (m + 3)) := by
      linear_combination zmod_add_sub_cancel (m := m) (k := k) (by omega) 0
    refine ⟨m, P.reverse, -a, m + 3 - k, ?_, by omega, by omega, ?_, ?_, ?_, ?_⟩
    · rw [ClosedPolygon.reverse_carrier]; exact hcar
    · rw [ClosedPolygon.reverse_vertex, neg_neg]; exact hpa
    · rw [ClosedPolygon.reverse_vertex, hneg,
        show -(-a + -(k : ZMod (m + 3))) = a + (k : ZMod (m + 3)) by ring]
      exact hqa
    · have h := P.reverse_arc (a + (k : ZMod (m + 3))) (m + 3 - k)
      rw [hneg, show -(a + (k : ZMod (m + 3))) - -(k : ZMod (m + 3)) = -a by ring] at h
      rw [h]; exact e1.symm
    · have h := P.reverse_arc a k
      rw [show m + 3 - (m + 3 - k) = k by omega, hneg,
        show -a + -(k : ZMod (m + 3)) = -a - (k : ZMod (m + 3)) by ring, h]
      exact e2.symm

end Schoenflies

namespace Graph

open Schoenflies

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}

/-! ## What the realization needs from the drawing, and nothing else -/

variable {x y : Fin 3 → Plane} {e : Fin 3 → Fin 3 → β} {s : Fin 3}

/-- **General position at the two cut points of the crosscut indexed by `s`.** At each of the two
ends `x s` and `y (s + 1)` of the remaining edge, the six-cycle turns, and so does each of the two
closed curves the remaining edge forms with the two halves of the six-cycle.

This is not a hypothesis chosen for convenience. `Schoenflies.ClosedPolygon.isCornerAt_vertex` and
`Schoenflies.ClosedPolygon.exists_vertex_eq_of_isCornerAt` together say that the vertex set of a
realization *is* the corner set of the curve; a crosscut cutting `C` at these two points forces
them to be vertices of all three closed polygons, hence corners of all three curves. For a drawn
`K(3,3)` it says that at each of the six vertices no two of the three edges leave along one
line. -/
def IsHexGeneric (drawing : β → ℝ → Plane) (e : Fin 3 → Fin 3 → β) (x y : Fin 3 → Plane)
    (s : Fin 3) : Prop :=
  ∀ p ∈ ({x s, y (s + 1)} : Set Plane),
    IsCornerAt (hexSet drawing e) p ∧
    IsCornerAt (edgesCover drawing (arcA e s) ∪ edgeArc drawing (e s (s + 1))) p ∧
    IsCornerAt (edgesCover drawing (arcB e s) ∪ edgeArc drawing (e s (s + 1))) p

namespace IsK33Config

/-- The first half of the six-cycle is polygonal: it is drawn by a path. -/
theorem isPolygonal_arcA (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hpoly : ∀ f ∈ E(G), IsPolygonal (edgeArc drawing f)) (s : Fin 3) :
    IsPolygonal (edgesCover drawing (arcA e s)) :=
  hd.isPolygonal_edgesCover hpoly (h.arcA_isPath s).isWalk (by simp [arcA])

/-- The second half of the six-cycle is polygonal. -/
theorem isPolygonal_arcB (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hpoly : ∀ f ∈ E(G), IsPolygonal (edgeArc drawing f)) (s : Fin 3) :
    IsPolygonal (edgesCover drawing (arcB e s)) :=
  hd.isPolygonal_edgesCover hpoly (h.arcB_isPath s).isWalk (by simp [arcB])

/-- **The six-cycle of a polygonally drawn `K(3,3)` is polygonal**: it is the union of its two
halves, which meet. -/
theorem isPolygonal_hexSet (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hpoly : ∀ f ∈ E(G), IsPolygonal (edgeArc drawing f)) :
    IsPolygonal (hexSet drawing e) := by
  rw [← arcs_union (drawing := drawing) (e := e) 0]
  exact (h.isPolygonal_arcA hd hpoly 0).union (h.isPolygonal_arcB hd hpoly 0)
    ⟨x 0, (h.arcA_isArcBetween hd 0).left_mem, (h.arcB_isArcBetween hd 0).left_mem⟩

/-- A remaining edge meets the first half of the six-cycle exactly in its own two ends. -/
theorem chord_inter_arcA (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (s : Fin 3) :
    edgesCover drawing (arcA e s) ∩ edgeArc drawing (e s (s + 1)) = {x s, y (s + 1)} := by
  refine Set.Subset.antisymm (fun z hz => ?_) ?_
  · have hzhex : z ∈ hexSet drawing e := by
      rw [← arcs_union (drawing := drawing) (e := e) s]; exact Or.inl hz.1
    rw [← h.chord_inter_hexSet hd s]
    exact ⟨hz.2, hzhex⟩
  · rintro z (rfl | rfl)
    exacts [⟨(h.arcA_isArcBetween hd s).left_mem,
      (hd.edge_isArcBetween (h.isLink s (s + 1))).left_mem⟩,
      ⟨(h.arcA_isArcBetween hd s).right_mem,
      (hd.edge_isArcBetween (h.isLink s (s + 1))).right_mem⟩]

/-- A remaining edge meets the second half of the six-cycle exactly in its own two ends. -/
theorem chord_inter_arcB (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (s : Fin 3) :
    edgesCover drawing (arcB e s) ∩ edgeArc drawing (e s (s + 1)) = {x s, y (s + 1)} := by
  refine Set.Subset.antisymm (fun z hz => ?_) ?_
  · have hzhex : z ∈ hexSet drawing e := by
      rw [← arcs_union (drawing := drawing) (e := e) s]; exact Or.inr hz.1
    rw [← h.chord_inter_hexSet hd s]
    exact ⟨hz.2, hzhex⟩
  · rintro z (rfl | rfl)
    exacts [⟨(h.arcB_isArcBetween hd s).left_mem,
      (hd.edge_isArcBetween (h.isLink s (s + 1))).left_mem⟩,
      ⟨(h.arcB_isArcBetween hd s).right_mem,
      (hd.edge_isArcBetween (h.isLink s (s + 1))).right_mem⟩]

/-- **`Graph.IsHexRealization`, discharged.** The six-cycle and the two curves the remaining edge
forms with its halves are three polygonal Jordan curves, so
`Schoenflies.exists_closedPolygon_arcs_oriented` presents each of them as a closed polygon whose
two arcs are the two given halves, both read from `x s` to `y (s+1)`.

The three presentations are found independently, and what makes them fit together is
`Schoenflies.ClosedPolygon.arcPieces_eq`: two closed polygons carrying one arc from one vertex cut
it into the same edges. So the six-cycle's presentation and the first spliced curve's agree on the
first half, the six-cycle's and the second spliced curve's agree on the second half, and the two
spliced curves agree on the remaining edge — the last only after reversing one of them, since a
crosscut is traversed one way in each of the two curves it bounds. -/
theorem isHexRealization (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hpoly : ∀ f ∈ E(G), IsPolygonal (edgeArc drawing f)) (hgen : IsHexGeneric drawing e x y s) :
    IsHexRealization drawing e s := by
  obtain ⟨hcp, hcp1, hcp2⟩ := hgen (x s) (by simp)
  obtain ⟨hcq, hcq1, hcq2⟩ := hgen (y (s + 1)) (by simp)
  have hpq : x s ≠ y (s + 1) := h.x_ne_y s (s + 1)
  have hA1 := h.arcA_isArcBetween hd s
  have hA2 := h.arcB_isArcBetween hd s
  have hCh := hd.edge_isArcBetween (h.isLink s (s + 1))
  have hinterA := h.chord_inter_arcA hd s
  have hinterB := h.chord_inter_arcB hd s
  have hPch : IsPolygonal (edgeArc drawing (e s (s + 1))) :=
    hpoly _ (h.isLink s (s + 1)).edge_mem
  have hP1 : IsPolygonal (edgesCover drawing (arcA e s) ∪ edgeArc drawing (e s (s + 1))) :=
    (h.isPolygonal_arcA hd hpoly s).union hPch ⟨x s, hA1.left_mem, hCh.left_mem⟩
  have hP2 : IsPolygonal (edgesCover drawing (arcB e s) ∪ edgeArc drawing (e s (s + 1))) :=
    (h.isPolygonal_arcB hd hpoly s).union hPch ⟨x s, hA2.left_mem, hCh.left_mem⟩
  have hJ1 : IsJordanCurve (edgesCover drawing (arcA e s) ∪ edgeArc drawing (e s (s + 1))) :=
    IsJordanCurve.of_two_arcs hA1 hCh.reverse fun z hz1 hz2 => by
      have hz : z ∈ ({x s, y (s + 1)} : Set Plane) := hinterA ▸ ⟨hz1, hz2⟩
      simpa using hz
  have hJ2 : IsJordanCurve (edgesCover drawing (arcB e s) ∪ edgeArc drawing (e s (s + 1))) :=
    IsJordanCurve.of_two_arcs hA2 hCh.reverse fun z hz1 hz2 => by
      have hz : z ∈ ({x s, y (s + 1)} : Set Plane) := hinterB ▸ ⟨hz1, hz2⟩
      simpa using hz
  obtain ⟨m, C, a, k, hCcar, hk1, hk2, hCa, hCak, hCarc1, hCarc2⟩ :=
    exists_closedPolygon_arcs_oriented (h.hexagon_isJordanCurve hd)
      (h.isPolygonal_hexSet hd hpoly) hcp hcq hpq hA1 hA2
      (arcs_union (drawing := drawing) (e := e) s) (h.arcs_inter hd s)
  obtain ⟨m₁, J₁, b, l, -, hl1, hl2, hJ1b, hJ1bl, hJ1a1, hJ1a2⟩ :=
    exists_closedPolygon_arcs_oriented hJ1 hP1 hcp1 hcq1 hpq hA1 hCh rfl hinterA
  obtain ⟨m₂, J₂, b₂, l₂, -, hl21, hl22, hJ2b, hJ2bl, hJ2a1, hJ2a2⟩ :=
    exists_closedPolygon_arcs_oriented hJ2 hP2 hcq2 hcp2 hpq.symm hA2.reverse hCh.reverse rfl
      (by rw [hinterB, Set.pair_comm])
  refine ⟨m, m₁, m₂, C, J₁, J₂, J₁.arcPieces (b + (l : ZMod (m₁ + 3))) (m₁ + 3 - l), a, k,
    by omega, hCcar, hCarc1, hCarc2, hJ1a2, ?_, ?_⟩
  · -- The first curve: the first half of the six-cycle, then the remaining edge.
    have hpieces : C.arcPieces a k = J₁.arcPieces b l :=
      ClosedPolygon.arcPieces_eq C J₁ a b hk1 hk2 hl1 hl2 (hCarc1.trans hJ1a1.symm)
        (hCa.trans hJ1b.symm)
    rw [hpieces]
    exact ClosedPolygon.sameEdges_arcPieces_split J₁ b (by omega)
  · -- The second curve: the second half, then the remaining edge — traversed the other way.
    have hpieces : C.arcPieces (a + (k : ZMod (m + 3))) (m + 3 - k) = J₂.arcPieces b₂ l₂ :=
      ClosedPolygon.arcPieces_eq C J₂ _ b₂ (by omega) (by omega) hl21 hl22
        (hCarc2.trans hJ2a1.symm) (hCak.trans hJ2b.symm)
    have hrev := J₂.reverse_arc (b₂ + (l₂ : ZMod (m₂ + 3))) (m₂ + 3 - l₂)
    have hstart2 : J₂.reverse.vertex (-(b₂ + (l₂ : ZMod (m₂ + 3)))
        - ((m₂ + 3 - l₂ : ℕ) : ZMod (m₂ + 3))) = y (s + 1) := by
      rw [ClosedPolygon.reverse_vertex,
        show -(-(b₂ + (l₂ : ZMod (m₂ + 3))) - ((m₂ + 3 - l₂ : ℕ) : ZMod (m₂ + 3)))
          = b₂ + (l₂ : ZMod (m₂ + 3)) + ((m₂ + 3 - l₂ : ℕ) : ZMod (m₂ + 3)) by ring,
        zmod_add_sub_cancel (by omega) b₂]
      exact hJ2b
    have hKeq : J₂.reverse.arcPieces (-(b₂ + (l₂ : ZMod (m₂ + 3)))
          - ((m₂ + 3 - l₂ : ℕ) : ZMod (m₂ + 3))) (m₂ + 3 - l₂)
        = J₁.arcPieces (b + (l : ZMod (m₁ + 3))) (m₁ + 3 - l) :=
      ClosedPolygon.arcPieces_eq J₂.reverse J₁ _ _ (by omega) (by omega) (by omega) (by omega)
        (by rw [hrev, hJ2a2, hJ1a2]) (by rw [hstart2, hJ1bl])
    have hKsame : SameEdges (J₂.arcPieces (b₂ + (l₂ : ZMod (m₂ + 3))) (m₂ + 3 - l₂))
        (J₁.arcPieces (b + (l : ZMod (m₁ + 3))) (m₁ + 3 - l)) := by
      rw [← hKeq]
      exact (J₂.sameEdges_reverse_arcPieces (b₂ + (l₂ : ZMod (m₂ + 3))) (m₂ + 3 - l₂)).symm
    refine (ClosedPolygon.sameEdges_arcPieces_split (k := l₂) J₂ b₂ (by omega)).trans ?_
    rw [← hpieces]
    exact SameEdges.append (SameEdges.refl _) hKsame

/-! ### `lem:k33` and `cor:k33-subdivision`, with the realization gone

What is left as a hypothesis is a *bending* step, and only that: every polygonal drawing can be
redrawn so that no two edges at a vertex leave it along one line. -/

/-- **`lem:k33` for a polygonal drawing in general position.** -/
theorem false_of_hexGeneric (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hpoly : ∀ f ∈ E(G), IsPolygonal (edgeArc drawing f))
    (hgen : ∀ s : Fin 3, IsHexGeneric drawing e x y s) : False :=
  h.false_of_hexRealizations hd fun s => h.isHexRealization hd hpoly (hgen s)

/-- **Lemma 3.10 (nonplanarity of `K(3,3)`), with only the bending step assumed.** A graph
carrying a copy of `K(3,3)` has no plane drawing, provided a polygonal drawing can be bent into
general position at the six vertices. -/
theorem not_isDrawing_of_bendable [G.Finite] (h : IsK33Config G x y e)
    (hbend : ∀ dr : β → ℝ → Plane, IsDrawing G dr → (∀ f ∈ E(G), IsPolygonal (edgeArc dr f)) →
      ∃ dr' : β → ℝ → Plane, IsDrawing G dr' ∧ (∀ f ∈ E(G), IsPolygonal (edgeArc dr' f)) ∧
        ∀ s : Fin 3, IsHexGeneric dr' e x y s) :
    ¬ ∃ dr : β → ℝ → Plane, IsDrawing G dr := by
  rintro ⟨dr, hdr⟩
  obtain ⟨dr', hdr', hpoly'⟩ := polygonal_redrawing G dr hdr
  obtain ⟨dr'', hdr'', hpoly'', hgen⟩ := hbend dr' hdr' hpoly'
  exact h.false_of_hexGeneric hdr'' hpoly'' hgen

end IsK33Config

/-- **The bending step**, for the abstract `K(3,3)` on six named points of the plane: every
polygonal drawing of it can be redrawn, polygonally, so that at each of the six vertices no two
of the three edges leave along one line. This is the one thing left unproved; see "What is still
assumed" in the module docstring. -/
abbrev Bendable (x y : Fin 3 → Plane) : Prop :=
  ∀ dr : Fin 3 × Fin 3 → ℝ → Plane, IsDrawing (k33Graph x y) dr →
    (∀ f ∈ E(k33Graph x y), IsPolygonal (edgeArc dr f)) →
    ∃ dr' : Fin 3 × Fin 3 → ℝ → Plane, IsDrawing (k33Graph x y) dr' ∧
      (∀ f ∈ E(k33Graph x y), IsPolygonal (edgeArc dr' f)) ∧
      ∀ s : Fin 3, IsHexGeneric dr' (fun i j => (i, j)) x y s

/-- **`lem:k33` for nine arcs**: no nine arcs in the plane meet only where a `K(3,3)` forces them
to, assuming `Graph.Bendable`. -/
theorem IsArcK33.false_of_bendable {P : Fin 3 → Fin 3 → Set Plane} (h : IsArcK33 x y P)
    (hbend : Bendable x y) : False :=
  h.isK33Config.not_isDrawing_of_bendable hbend ⟨h.arcDrawing, h.isDrawing⟩

/-- **Corollary 3.11 (subdivisions of `K(3,3)`).** No subdivision of `K(3,3)` has a plane
drawing, assuming `Graph.Bendable`, and only for the *contracted* graph `k33Graph x y`,
whose nine edges are the branch paths. -/
theorem IsK33Subdivision.false_of_bendable {H : Graph Plane β} {W : Fin 3 → Fin 3 → List β}
    (hd : IsDrawing H drawing) (h : IsK33Subdivision H x y W) (hbend : Bendable x y) : False :=
  (h.isArcK33 hd).false_of_bendable hbend

/-- **The headline: `K(3,3)` has no plane drawing.** Stated for the concrete graph
`Graph.k33Graph x y`, whose nine edges are the index pairs. Assuming `Graph.Bendable`, the
one hypothesis this module leaves standing. -/
theorem k33Graph_not_isDrawing (x y : Fin 3 → Plane) (hx : Function.Injective x)
    (hy : Function.Injective y) (hxy : ∀ i j, x i ≠ y j) (hbend : Bendable x y) :
    ¬ ∃ dr : Fin 3 × Fin 3 → ℝ → Plane, IsDrawing (k33Graph x y) dr :=
  IsK33Config.not_isDrawing_of_bendable
    ⟨k33Graph_isLink x y, hx, hy, hxy⟩ hbend

end Graph

end BundlePart423

section BundlePart424
/- Source: dev/planar_search/schoenflies_port/Schoenflies/Graph/K33Land.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/



/-!
# `lem:k33` and `cor:k33-subdivision`, with nothing assumed

`Schoenflies/Graph/K33Planar.lean` proves the nonplanarity of `K(3,3)` from
`Graph.IsHexRealization`; `Schoenflies/Graph/K33Closed.lean` reduces that to `Graph.Bendable` —
"every polygonal drawing can be redrawn so that no two edges leave a vertex along one line". This
module removes the hypothesis altogether. Nothing is bent.

## Where the hypothesis came from, and why it is not needed

`Schoenflies.ClosedPolygon` carries a `corner` field, and
`Schoenflies.ClosedPolygon.isCornerAt_vertex` shows the field is not slack: *every* vertex of
*every* `ClosedPolygon` presentation is a point at which the curve turns. So a crosscut interface
phrased with `ClosedPolygon`s — `Schoenflies.IsPolygonalCrosscut`, and hence
`Schoenflies.alternating_crosscuts` — can only cut the curve at corners, and a drawn `K(3,3)` puts
its branch points wherever it likes.

The blueprint's `cor:alternating-crosscuts` has no such condition: it is stated for a set-level
simple closed polygonal curve and simple polygonal arcs with endpoints anywhere on it. The fix is
to state the crosscut for `Schoenflies.PrePolygon` — `ClosedPolygon` without `corner` — whose
vertices may sit anywhere on the curve. `Schoenflies/PrePolygonSep.lean` already supplies the two
things Theorem 2.8 asks of such a curve: that its carrier separates the plane, and the two values
of the crossing parity. Everything else in the chain is about *edge lists*, and edge lists do not
know about corners.

## The one construction this needed

Three closed polygons enter Theorem 2.8 — the curve `C` and the two curves `Jᵢ` the crosscut
forms with the two arcs — and their **edge lists** must agree: `SameEdges Jᵢ.pieces (Aᵢ ++ K)`.
`Schoenflies/Graph/K33Closed.lean` found three realizations independently and matched them with
`Schoenflies.ClosedPolygon.arcPieces_eq`, whose proof is exactly where `corner` was consumed. For
`PrePolygon` no such matching theorem can exist: two presentations of one arc need not agree.

So the two spliced curves are not found — they are *built*. `Schoenflies.PrePolygon.exists_splice`
lays two chains with common ends end to end and returns a `PrePolygon` whose edge list is their
concatenation, so the three lists agree by construction and nothing has to be matched. The chains
themselves come from `Schoenflies.exists_prePolygon_arcs_oriented`, which needs
`Schoenflies.PrePolygon.insertLast` of `Schoenflies/PrePolygonArc.lean`: a point of the curve that
is not yet a vertex is interior to an edge, and an edge may be cut. That is the inverse of
`Schoenflies.PrePolygon.deleteLast`, and it is what makes "a `PrePolygon` may be presented with
vertices at any prescribed finite set of points of its carrier" a theorem
(`Schoenflies.PrePolygon.exists_prePolygon_vertices`).

## What this module rests on

The `Schoenflies.PrePolygon` arc apparatus — `chain`, `arcPieces`, `arc`, `arc_inter`,
`isArcBetween_arc`, `parity_splitting`, `parity_ne_iff_mem_farRegion`, `insertLast`,
`exists_prePolygon_vertices`, `Schoenflies.exists_prePolygon_split` and the segment-cutting
lemmas — is in `Schoenflies/PrePolygonArc.lean`, shared with `Schoenflies/FaceCyclesLand.lean`.
Only what is peculiar to the crosscut wiring is left here.

## Blueprint

* `Schoenflies.PrePolygon.exists_splice` — two arcs with common ends, laid end to end.
* `Schoenflies.PrePolygon.reverse`, `…reverse_arc`, `…sameEdges_reverse_arcPieces` — the polygon
  traversed the other way, which is what pins the direction of a prescribed arc.
* `Schoenflies.exists_prePolygon_arcs`, `…exists_prePolygon_arcs_oriented` — §1, the realization
  theorem **with the cut points anywhere on the curve**, tracking a prescribed splitting.
  Compare `Schoenflies.exists_closedPolygon_arcs`, which requires the cut points to be corners.
* `Schoenflies.IsPrePolygonalCrosscut` and its API up to
  `…alternating_inter_nonempty_of_same_side` — `thm:polygonal-crosscut` and
  `cor:alternating-crosscuts` in the blueprint's own generality: the split points need not be
  corners.
* `Graph.IsPreHexCrosscut`, `Graph.IsK33Config.isPreHexCrosscut` — the six-cycle of a polygonally
  drawn `K(3,3)`, cut at the two ends of one remaining edge, as such a crosscut. **This is what
  `Graph.IsHexRealization` was assuming, and it is proved here.**
* `Graph.IsK33Config.false_of_isPreHexCrosscut`, `…false_of_polygonal`,
  `Graph.IsK33Config.not_exists_isDrawing` — `lem:k33`.
* `Graph.IsArcK33.elim`, `Graph.IsK33Subdivision.elim` — `cor:k33-subdivision`.
* `Graph.k33Graph_not_exists_isDrawing` — `lem:k33` for the concrete graph.

## A note on names, for the integrator

The direct statements use eliminator-style names because the realization-parametric lemmas are
still in the import closure:

| realization-parametric lemma                      | direct theorem                             |
|---------------------------------------------------|--------------------------------------------|
| `Graph.IsK33Config.not_isDrawing` (K33Planar)      | `Graph.IsK33Config.not_exists_isDrawing`   |
| `Graph.IsK33Config.not_isDrawing_of_bendable`      | `Graph.IsK33Config.not_exists_isDrawing`   |
| `Graph.IsArcK33.false_of_realization`/`_bendable`  | `Graph.IsArcK33.elim`                      |
| `Graph.IsK33Subdivision.false_of_realization`/`…`  | `Graph.IsK33Subdivision.elim`              |
| `Graph.k33Graph_not_isDrawing`                     | `Graph.k33Graph_not_exists_isDrawing`      |

With this module in place `Graph.IsHexRealization`, `Graph.IsHexCrosscut`, `Graph.IsHexGeneric`
and `Graph.Bendable` have no consumers left.
-/

open Bornology Metric Set unitInterval
open scoped Graph

namespace Schoenflies

open Plane

namespace PrePolygon

/-! ## Splicing two chains into a closed polygon

The crosscut of Theorem 2.8 asks for three closed polygons whose *edge lists* fit together, and
independent realizations of three curves do not. The way out is to realize only the curve `C`,
and to build the two spliced curves out of one arc of `C` and one presentation of the crosscut —
so that the three edge lists agree by construction. This is that construction: two chains with
the same pair of ends, meeting only there, laid end to end. -/

/-- **Two arcs with common ends splice into a closed polygon whose edge list is their
concatenation.** `P.arcPieces a k` runs from `p` to `q` and `P'.arcPieces b l` runs from `q` back
to `p`; the two meet only at `p` and `q`. -/
theorem exists_splice {m m' : ℕ} (P : PrePolygon m) (P' : PrePolygon m')
    {a : ZMod (m + 3)} {k : ℕ} {b : ZMod (m' + 3)} {l : ℕ}
    (hk1 : 1 ≤ k) (hk2 : k ≤ m + 2) (hl1 : 1 ≤ l) (hl2 : l ≤ m' + 2)
    (hstart : P'.vertex b = P.vertex (a + (k : ZMod (m + 3))))
    (hend : P'.vertex (b + (l : ZMod (m' + 3))) = P.vertex a)
    (hinter : P.arc a k ∩ P'.arc b l = {P.vertex a, P.vertex (a + (k : ZMod (m + 3)))}) :
    ∃ (n : ℕ) (Q : PrePolygon n), Q.pieces = P.arcPieces a k ++ P'.arcPieces b l := by
  -- The two chains cannot both be a single edge: they would be the same segment.
  have hthree : 3 ≤ k + l := by
    by_contra hcon
    obtain rfl : k = 1 := by omega
    obtain rfl : l = 1 := by omega
    rw [Nat.cast_one] at hstart hinter
    rw [Nat.cast_one] at hend
    have hseg : P'.edge b = P.edge a := by
      rw [edge, edge, hstart, hend, segment_symm]
    rw [P.arc_one a, P'.arc_one b, hseg, Set.inter_self] at hinter
    obtain ⟨z, hz, hz1, hz2⟩ := exists_mem_segment_ne (vertex_ne_succ (P := P) a)
    rcases hinter.subset hz with h | h
    exacts [hz1 h, hz2 h]
  obtain ⟨n, hn⟩ : ∃ n, k + l = n + 3 := ⟨k + l - 3, by omega⟩
  -- Pieces of one arc lie in that arc; that is all the intersection hypothesis is used through.
  have hPedge : ∀ t : ℕ, t < k → P.edge (a + (t : ZMod (m + 3))) ⊆ P.arc a k :=
    fun t ht z hz => mem_arc_iff.2 ⟨t, ht, hz⟩
  have hP'edge : ∀ t : ℕ, t < l → P'.edge (b + (t : ZMod (m' + 3))) ⊆ P'.arc b l :=
    fun t ht z hz => mem_arc_iff.2 ⟨t, ht, hz⟩
  have hcross : ∀ s : ℕ, s < k → ∀ t : ℕ, t < l →
      P.edge (a + (s : ZMod (m + 3))) ∩ P'.edge (b + (t : ZMod (m' + 3)))
        ⊆ ({P.vertex a, P.vertex (a + (k : ZMod (m + 3)))} : Set Plane) := by
    intro s hs t ht z hz
    rw [← hinter]
    exact ⟨hPedge s hs hz.1, hP'edge t ht hz.2⟩
  -- The spliced vertex list.
  set w : ZMod (n + 3) → Plane := fun j =>
    if j.val < k then P.vertex (a + ((j.val : ℕ) : ZMod (m + 3)))
    else P'.vertex (b + ((j.val - k : ℕ) : ZMod (m' + 3))) with hwdef
  have hbound : ∀ j : ZMod (n + 3), j.val < k + l := fun j => by
    have := ZMod.val_lt j; omega
  have hw_lt : ∀ j : ZMod (n + 3), j.val < k →
      w j = P.vertex (a + ((j.val : ℕ) : ZMod (m + 3))) := fun j hj => by
    rw [hwdef]; exact if_pos hj
  have hw_ge : ∀ j : ZMod (n + 3), ¬ j.val < k →
      w j = P'.vertex (b + ((j.val - k : ℕ) : ZMod (m' + 3))) := fun j hj => by
    rw [hwdef]; exact if_neg hj
  have hsucc_lt : ∀ j : ZMod (n + 3), j.val < k →
      w (j + 1) = P.vertex (a + ((j.val : ℕ) : ZMod (m + 3)) + 1) := by
    intro j hj
    have hval : (j + 1).val = j.val + 1 := val_succ_of_lt (m := n) (by omega)
    by_cases hlt : j.val + 1 < k
    · rw [hw_lt (j + 1) (by omega), hval]
      congr 1
      push_cast
      ring
    · have hk' : j.val + 1 = k := by omega
      rw [hw_ge (j + 1) (by omega), hval, hk', Nat.sub_self, Nat.cast_zero, add_zero, hstart]
      congr 1
      rw [← hk']
      push_cast
      ring
  have hsucc_ge : ∀ j : ZMod (n + 3), ¬ j.val < k →
      w (j + 1) = P'.vertex (b + ((j.val - k : ℕ) : ZMod (m' + 3)) + 1) := by
    intro j hj
    have hjb := hbound j
    by_cases hlt : j.val + 1 < n + 3
    · have hval : (j + 1).val = j.val + 1 := val_succ_of_lt (m := n) (by omega)
      rw [hw_ge (j + 1) (by omega), hval]
      congr 1
      rw [show j.val + 1 - k = (j.val - k) + 1 by omega]
      push_cast
      ring
    · have hval : (j + 1).val = 0 := val_succ_last (m := n) (by omega)
      rw [hw_lt (j + 1) (by omega), hval, Nat.cast_zero, add_zero, ← hend]
      congr 1
      have hc : ((l - 1 : ℕ) : ZMod (m' + 3)) + 1 = ((l : ℕ) : ZMod (m' + 3)) :=
        ClosedPolygon.natCast_pred_succ (by omega)
      rw [show j.val - k = l - 1 by omega, add_assoc, hc]
  -- The edges of the spliced list are the edges of the two arcs.
  have hE_lt : ∀ j : ZMod (n + 3), j.val < k →
      segment ℝ (w j) (w (j + 1)) = P.edge (a + ((j.val : ℕ) : ZMod (m + 3))) := by
    intro j hj
    rw [hw_lt j hj, hsucc_lt j hj, edge]
  have hE_ge : ∀ j : ZMod (n + 3), ¬ j.val < k →
      segment ℝ (w j) (w (j + 1)) = P'.edge (b + ((j.val - k : ℕ) : ZMod (m' + 3))) := by
    intro j hj
    rw [hw_ge j hj, hsucc_ge j hj, edge]
  have hends_lt : ∀ j : ZMod (n + 3), j.val < k →
      ({w j, w (j + 1)} : Set Plane)
        = {P.vertex (a + ((j.val : ℕ) : ZMod (m + 3))),
           P.vertex (a + ((j.val : ℕ) : ZMod (m + 3)) + 1)} := by
    intro j hj
    rw [hw_lt j hj, hsucc_lt j hj]
  have hends_ge : ∀ j : ZMod (n + 3), ¬ j.val < k →
      ({w j, w (j + 1)} : Set Plane)
        = {P'.vertex (b + ((j.val - k : ℕ) : ZMod (m' + 3))),
           P'.vertex (b + ((j.val - k : ℕ) : ZMod (m' + 3)) + 1)} := by
    intro j hj
    rw [hw_ge j hj, hsucc_ge j hj]
  refine ⟨n, ⟨w, ?_, ?_⟩, ?_⟩
  · -- injectivity
    intro i j hij
    have hib := hbound i
    have hjb := hbound j
    have hcase : ∀ i' j' : ZMod (n + 3), i'.val < k → ¬ j'.val < k → w i' ≠ w j' := by
      intro i' j' hi' hj' he
      rw [hw_lt i' hi', hw_ge j' hj'] at he
      have hval : P.vertex (a + ((i'.val : ℕ) : ZMod (m + 3))) ∈
          ({P.vertex a, P.vertex (a + (k : ZMod (m + 3)))} : Set Plane) := by
        rw [← hinter]
        exact ⟨hPedge i'.val hi' (left_mem_segment ℝ _ _),
          he ▸ hP'edge (j'.val - k) (by have := hbound j'; omega) (left_mem_segment ℝ _ _)⟩
      rcases hval with hval | hval
      · -- the common point is `p`: on the second arc that forces the last index
        have h0 : i'.val = 0 := by
          have := P.natCast_shift_inj a (show i'.val < m + 3 by omega) (show 0 < m + 3 by omega)
            (by rw [hval, Nat.cast_zero, add_zero])
          omega
        have hlast : P'.vertex (b + ((j'.val - k : ℕ) : ZMod (m' + 3)))
            = P'.vertex (b + ((l : ℕ) : ZMod (m' + 3))) := by rw [hend, ← he, hval]
        have := P'.natCast_shift_inj b (show j'.val - k < m' + 3 by have := hbound j'; omega)
          (show l < m' + 3 by omega) hlast
        have := hbound j'
        omega
      · have := P.natCast_shift_inj a (show i'.val < m + 3 by omega) (show k < m + 3 by omega)
          (by rw [hval])
        omega
    by_cases hli : i.val < k <;> by_cases hlj : j.val < k
    · rw [hw_lt i hli, hw_lt j hlj] at hij
      exact ZMod.val_injective _ (P.natCast_shift_inj a (by omega) (by omega) hij)
    · exact absurd hij (hcase i j hli hlj)
    · exact absurd hij.symm (hcase j i hlj hli)
    · rw [hw_ge i hli, hw_ge j hlj] at hij
      have := P'.natCast_shift_inj b (show i.val - k < m' + 3 by omega)
        (show j.val - k < m' + 3 by omega) hij
      exact ZMod.val_injective _ (by omega)
  · -- simplicity
    intro i j hij
    have hib := hbound i
    have hjb := hbound j
    by_cases hli : i.val < k <;> by_cases hlj : j.val < k
    · rw [hE_lt i hli, hE_lt j hlj, hends_lt i hli]
      refine P.edges_meet _ _ fun he => hij (ZMod.val_injective _ ?_)
      exact P.natCast_shift_inj a (by omega) (by omega) (by rw [he])
    · rw [hE_lt i hli, hE_ge j hlj, hends_lt i hli]
      intro z hz
      have hz' := hcross i.val hli (j.val - k) (by omega) hz
      rcases hz' with rfl | rfl
      exacts [vertex_mem_edge_elim (P := P) (c := a) hz.1,
        vertex_mem_edge_elim (P := P) (c := a + (k : ZMod (m + 3))) hz.1]
    · rw [hE_ge i hli, hE_lt j hlj, hends_ge i hli]
      intro z hz
      have hz' := hcross j.val hlj (i.val - k) (by omega) ⟨hz.2, hz.1⟩
      rcases hz' with rfl | rfl
      · rw [← hend]
        exact vertex_mem_edge_elim (P := P') (c := b + (l : ZMod (m' + 3)))
          (by rw [hend]; exact hz.1)
      · rw [← hstart]
        exact vertex_mem_edge_elim (P := P') (c := b) (by rw [hstart]; exact hz.1)
    · rw [hE_ge i hli, hE_ge j hlj, hends_ge i hli]
      refine P'.edges_meet _ _ fun he => hij (ZMod.val_injective _ ?_)
      have := P'.natCast_shift_inj b (show i.val - k < m' + 3 by omega)
        (show j.val - k < m' + 3 by omega) (by rw [he])
      omega
  · -- the edge list
    have hrange : List.range (n + 3) = List.range k ++ (List.range l).map (k + ·) := by
      rw [← hn]; exact List.range_add
    change ((List.range (n + 3)).map fun j : ℕ =>
        (w ((j : ℕ) : ZMod (n + 3)), w (((j : ℕ) : ZMod (n + 3)) + 1))) = _
    rw [hrange, List.map_append, List.map_map, arcPieces, arcPieces]
    congr 1
    · refine List.map_congr_left fun t ht => ?_
      have htk : t < k := List.mem_range.1 ht
      have hval : ((t : ZMod (n + 3))).val = t := ZMod.val_cast_of_lt (by omega)
      have h1 : ((t : ZMod (n + 3))).val < k := by rw [hval]; exact htk
      rw [hw_lt _ h1, hsucc_lt _ h1, hval]
    · refine List.map_congr_left fun s hs => ?_
      have hsl : s < l := List.mem_range.1 hs
      have hval : (((k + s : ℕ) : ZMod (n + 3))).val = k + s := ZMod.val_cast_of_lt (by omega)
      have h1 : ¬ (((k + s : ℕ) : ZMod (n + 3))).val < k := by rw [hval]; omega
      simp only [Function.comp_apply]
      rw [hw_ge _ h1, hsucc_ge _ h1, hval, show k + s - k = s by omega]

/-! ## The polygon read backwards

Needed only to pin the *direction* in which a realization traverses a prescribed arc; the
`Schoenflies.ClosedPolygon` version is in `Schoenflies/Graph/K33Closed.lean`, and this is the
same construction with the `corner` field dropped. -/

/-- **The same closed polygon, traversed the other way.** -/
def reverse {m : ℕ} (P : PrePolygon m) : PrePolygon m where
  vertex j := P.vertex (-j)
  vertex_inj _ _ h := neg_injective (P.vertex_inj h)
  edges_meet i j hij := by
    have e1 : (-(i + 1) : ZMod (m + 3)) = -i - 1 := by ring
    have e2 : (-(j + 1) : ZMod (m + 3)) = -j - 1 := by ring
    have e3 : (-i - 1 : ZMod (m + 3)) + 1 = -i := by ring
    have e4 : (-j - 1 : ZMod (m + 3)) + 1 = -j := by ring
    have hij' : (-i - 1 : ZMod (m + 3)) ≠ -j - 1 := fun h => hij (by linear_combination -h)
    have h := P.edges_meet (-i - 1) (-j - 1) hij'
    rw [e3, e4] at h
    simp only [e1, e2]
    rw [segment_symm ℝ (P.vertex (-i)) (P.vertex (-i - 1)),
      segment_symm ℝ (P.vertex (-j)) (P.vertex (-j - 1)), Set.pair_comm]
    exact h

@[simp] theorem reverse_vertex {m : ℕ} (P : PrePolygon m) (j : ZMod (m + 3)) :
    P.reverse.vertex j = P.vertex (-j) := rfl

theorem reverse_edge {m : ℕ} (P : PrePolygon m) (j : ZMod (m + 3)) :
    P.reverse.edge j = P.edge (-j - 1) := by
  rw [edge, edge, reverse_vertex, reverse_vertex,
    show (-(j + 1) : ZMod (m + 3)) = -j - 1 by ring,
    show (-j - 1 : ZMod (m + 3)) + 1 = -j by ring]
  exact segment_symm ℝ _ _

@[simp] theorem reverse_carrier {m : ℕ} (P : PrePolygon m) : P.reverse.carrier = P.carrier := by
  ext z
  constructor
  · intro hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hz
    rw [reverse_edge] at hi
    exact Set.mem_iUnion.2 ⟨_, hi⟩
  · intro hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hz
    refine Set.mem_iUnion.2 ⟨-i - 1, ?_⟩
    rw [reverse_edge, show (-(-i - 1) - 1 : ZMod (m + 3)) = i by ring]
    exact hi

/-- **Reversing does not move an arc**, it only starts it at the other end. -/
theorem reverse_arc {m : ℕ} (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    P.reverse.arc (-a - (k : ZMod (m + 3))) k = P.arc a k := by
  ext z
  rw [mem_arc_iff, mem_arc_iff]
  constructor
  · rintro ⟨t, ht, hz⟩
    rw [reverse_edge] at hz
    refine ⟨k - t - 1, by omega, ?_⟩
    rw [show a + ((k - t - 1 : ℕ) : ZMod (m + 3))
        = -(-a - (k : ZMod (m + 3)) + (t : ZMod (m + 3))) - 1 by
      linear_combination ClosedPolygon.reverse_natCast (n := m + 3) ht]
    exact hz
  · rintro ⟨t, ht, hz⟩
    refine ⟨k - t - 1, by omega, ?_⟩
    rw [reverse_edge, show -(-a - (k : ZMod (m + 3)) + ((k - t - 1 : ℕ) : ZMod (m + 3))) - 1
        = a + (t : ZMod (m + 3)) by
      linear_combination -ClosedPolygon.reverse_natCast (n := m + 3) ht]
    exact hz

/-- **Reversing does not change the edge list either**, up to the order and the naming of each
edge's two ends — which is exactly what `Schoenflies.SameEdges` forgives. -/
theorem sameEdges_reverse_arcPieces {m : ℕ} (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    SameEdges (P.reverse.arcPieces (-a - (k : ZMod (m + 3))) k) (P.arcPieces a k) := by
  have key : (P.reverse.arcPieces (-a - (k : ZMod (m + 3))) k).map orientPiece
      = ((P.arcPieces a k).map orientPiece).reverse := by
    rw [arcPieces, arcPieces, List.map_map, List.map_map, ← List.map_reverse,
      List.range_eq_range', List.reverse_range', ← List.range_eq_range', List.map_map]
    refine List.map_congr_left fun t ht => ?_
    have htk : t < k := List.mem_range.1 ht
    have he : (0 + k - 1 - t : ℕ) = k - t - 1 := by omega
    simp only [Function.comp_apply, he, reverse_vertex]
    rw [show -(-a - (k : ZMod (m + 3)) + (t : ZMod (m + 3)))
          = a + ((k - t - 1 : ℕ) : ZMod (m + 3)) + 1 by
        linear_combination -ClosedPolygon.reverse_natCast (n := m + 3) htk,
      show -(-a - (k : ZMod (m + 3)) + (t : ZMod (m + 3)) + 1)
        = a + ((k - t - 1 : ℕ) : ZMod (m + 3)) by
        linear_combination -ClosedPolygon.reverse_natCast (n := m + 3) htk]
    exact orientPiece_swap (_, _)
  rw [SameEdges, key]
  exact List.reverse_perm _

end PrePolygon

/-! ## The realization theorem, tracking a prescribed splitting

`Schoenflies.exists_prePolygon_split` of `Schoenflies/PrePolygonArc.lean` presents the curve with
the two cut points among its vertices, with no corner condition on them. What remains is to say
*which* arc of that presentation is which of two prescribed arcs, and in which direction the
first is traversed. -/

/-- **The realization theorem, tracking a splitting into two named arcs.** -/
theorem exists_prePolygon_arcs {C A₁ A₂ : Set Plane} (hJ : IsJordanCurve C) (hP : IsPolygonal C)
    {p q : Plane} (hp : p ∈ C) (hq : q ∈ C) (hpq : p ≠ q)
    (hA1 : IsArcBetween A₁ p q) (hA2 : IsArcBetween A₂ p q) (hunion : A₁ ∪ A₂ = C)
    (hinter : A₁ ∩ A₂ = {p, q}) :
    ∃ (m : ℕ) (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ), P.carrier = C ∧
      1 ≤ k ∧ k ≤ m + 2 ∧ P.vertex a = p ∧ P.vertex (a + (k : ZMod (m + 3))) = q ∧
      ((P.arc a k = A₁ ∧ P.arc (a + (k : ZMod (m + 3))) (m + 3 - k) = A₂) ∨
        (P.arc a k = A₂ ∧ P.arc (a + (k : ZMod (m + 3))) (m + 3 - k) = A₁)) := by
  obtain ⟨m, P, a, k, hcar, hpa, hqa, hk1, hk2⟩ := exists_prePolygon_split hJ hP hp hq hpq
  refine ⟨m, P, a, k, hcar, hk1, hk2, hpa, hqa, ?_⟩
  have hD1 : IsArcBetween (P.arc a k) p q := by
    rw [← hpa, ← hqa]; exact P.isArcBetween_arc a hk1 hk2
  have hD2 : IsArcBetween (P.arc (a + (k : ZMod (m + 3))) (m + 3 - k)) p q := by
    have h := P.isArcBetween_arc (a + (k : ZMod (m + 3))) (k := m + 3 - k) (by omega) (by omega)
    rw [zmod_add_sub_cancel (by omega) a] at h
    rw [← hpa, ← hqa]
    exact h.reverse
  have hDunion : P.arc a k ∪ P.arc (a + (k : ZMod (m + 3))) (m + 3 - k) = C := by
    rw [P.arc_union a (by omega), hcar]
  have hDinter : P.arc a k ∩ P.arc (a + (k : ZMod (m + 3))) (m + 3 - k) = {p, q} := by
    rw [P.arc_inter a hk1 hk2, hpa, hqa]
  rcases two_arcs_unique hunion hinter hDunion hDinter hA1 hA2 hD1 hD2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact Or.inl ⟨e1.symm, e2.symm⟩
  · exact Or.inr ⟨e2.symm, e1.symm⟩

/-- **The realization of a splitting, with both the arcs and the direction fixed.** The two arcs
come out in the order they were given *and* the first is traversed from `p` to `q`; reading the
polygon backwards when it is not is what pins the direction.

This is the shape the crosscut wiring consumes, and — unlike
`Schoenflies.exists_closedPolygon_arcs_oriented` — it asks nothing of `p` and `q` beyond lying on
the curve. -/
theorem exists_prePolygon_arcs_oriented {C A₁ A₂ : Set Plane} (hJ : IsJordanCurve C)
    (hP : IsPolygonal C) {p q : Plane} (hp : p ∈ C) (hq : q ∈ C) (hpq : p ≠ q)
    (hA1 : IsArcBetween A₁ p q) (hA2 : IsArcBetween A₂ p q) (hunion : A₁ ∪ A₂ = C)
    (hinter : A₁ ∩ A₂ = {p, q}) :
    ∃ (m : ℕ) (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ), P.carrier = C ∧
      1 ≤ k ∧ k ≤ m + 2 ∧ P.vertex a = p ∧ P.vertex (a + (k : ZMod (m + 3))) = q ∧
      P.arc a k = A₁ ∧ P.arc (a + (k : ZMod (m + 3))) (m + 3 - k) = A₂ := by
  obtain ⟨m, P, a, k, hcar, hk1, hk2, hpa, hqa, hcase⟩ :=
    exists_prePolygon_arcs hJ hP hp hq hpq hA1 hA2 hunion hinter
  rcases hcase with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact ⟨m, P, a, k, hcar, hk1, hk2, hpa, hqa, e1, e2⟩
  · -- The realization runs the two arcs the other way round: read it backwards.
    have hneg : ((m + 3 - k : ℕ) : ZMod (m + 3)) = -(k : ZMod (m + 3)) := by
      linear_combination zmod_add_sub_cancel (m := m) (k := k) (by omega) 0
    refine ⟨m, P.reverse, -a, m + 3 - k, ?_, by omega, by omega, ?_, ?_, ?_, ?_⟩
    · rw [PrePolygon.reverse_carrier]; exact hcar
    · rw [PrePolygon.reverse_vertex, neg_neg]; exact hpa
    · rw [PrePolygon.reverse_vertex, hneg,
        show -(-a + -(k : ZMod (m + 3))) = a + (k : ZMod (m + 3)) by ring]
      exact hqa
    · have h := P.reverse_arc (a + (k : ZMod (m + 3))) (m + 3 - k)
      rw [hneg, show -(a + (k : ZMod (m + 3))) - -(k : ZMod (m + 3)) = -a by ring] at h
      rw [h]; exact e2
    · have h := P.reverse_arc a k
      rw [show m + 3 - (m + 3 - k) = k by omega, hneg,
        show -a + -(k : ZMod (m + 3)) = -a - (k : ZMod (m + 3)) by ring, h]
      exact e1

/-! ## Theorem 2.8 and Corollary 2.9 for a polygon presented with redundant vertices

`Schoenflies.IsPolygonalCrosscut` is stated for `ClosedPolygon`s, and by
`Schoenflies.ClosedPolygon.isCornerAt_vertex` that pins the two cut points to be *corners* of the
curve. Nothing in the proof of Theorem 2.8 needs the `corner` field: what it uses of `C`, `J₁`,
`J₂` is that their carriers separate the plane and that their crossing counts are the ones the
edge lists compute. `Schoenflies/PrePolygonSep.lean` supplies both for a `PrePolygon`, so the
whole chain goes through with the cut points anywhere on the curve. -/

variable {m m₁ m₂ : ℕ} {C : PrePolygon m} {J₁ : PrePolygon m₁} {J₂ : PrePolygon m₂}
  {K : List Piece} {a : ZMod (m + 3)} {k : ℕ} {y : Plane}

/-- **The setting of Theorem 2.8, with the cut points unrestricted.** Word for word
`Schoenflies.IsPolygonalCrosscut`, with `PrePolygon` for `ClosedPolygon`. -/
structure IsPrePolygonalCrosscut (C : PrePolygon m) (J₁ : PrePolygon m₁) (J₂ : PrePolygon m₂)
    (K : List Piece) (a : ZMod (m + 3)) (k : ℕ) (y : Plane) : Prop where
  /-- The first arc runs forward through at most a full turn. -/
  le : k ≤ m + 3
  /-- `J₁` carries the edges of the first arc together with those of the crosscut. -/
  edges₁ : SameEdges J₁.pieces (C.arcPieces a k ++ K)
  /-- `J₂` carries the edges of the second arc together with those of the crosscut. -/
  edges₂ : SameEdges J₂.pieces (C.arcPieces (a + k) (m + 3 - k) ++ K)
  /-- The crosscut meets the polygon only in points of the first arc … -/
  meets₁ : cover K ∩ C.carrier ⊆ C.arc a k
  /-- … and only in points of the second arc. -/
  meets₂ : cover K ∩ C.carrier ⊆ C.arc (a + k) (m + 3 - k)
  /-- The reference point lies off the polygon … -/
  notMem : y ∉ C.carrier
  /-- … and the crosscut does not enter its region. -/
  avoids : Disjoint (cover K) (connectedComponentIn C.carrierᶜ y)

/-- **The front door.** A crosscut is normally presented by saying that it meets `C` exactly in
its two endpoints, and that those endpoints are the two cut vertices. -/
theorem IsPrePolygonalCrosscut.of_endpoints (hk1 : 1 ≤ k) (hk2 : k ≤ m + 2)
    (edges₁ : SameEdges J₁.pieces (C.arcPieces a k ++ K))
    (edges₂ : SameEdges J₂.pieces (C.arcPieces (a + k) (m + 3 - k) ++ K))
    (meets : cover K ∩ C.carrier ⊆ ({C.vertex a, C.vertex (a + k)} : Set Plane))
    (notMem : y ∉ C.carrier)
    (avoids : Disjoint (cover K) (connectedComponentIn C.carrierᶜ y)) :
    IsPrePolygonalCrosscut C J₁ J₂ K a k y :=
  ⟨by omega, edges₁, edges₂, meets.trans (C.endpoints_subset_arc a hk1),
    meets.trans (C.endpoints_subset_arc' a hk2), notMem, avoids⟩

namespace IsPrePolygonalCrosscut

variable (h : IsPrePolygonalCrosscut C J₁ J₂ K a k y)
include h

/-- **The two arcs may be swapped.** -/
theorem symm : IsPrePolygonalCrosscut C J₂ J₁ K (a + k) (m + 3 - k) y := by
  have hk : k ≤ m + 3 := h.le
  have hnat : m + 3 - (m + 3 - k) = k := by omega
  have hzmod := zmod_add_sub_cancel (k := k) hk a
  refine ⟨by omega, h.edges₂, ?_, h.meets₂, ?_, h.notMem, h.avoids⟩
  · rw [hzmod, hnat]; exact h.edges₁
  · rw [hzmod, hnat]; exact h.meets₁

/-! ### The elementary consequences -/

theorem notMem_cover : y ∉ cover K :=
  fun hy => Set.disjoint_left.1 h.avoids hy (mem_connectedComponentIn h.notMem)

theorem carrier₁ : J₁.carrier = C.arc a k ∪ cover K :=
  PrePolygon.carrier_eq_of_sameEdges h.edges₁

theorem notMem_carrier₁ : y ∉ J₁.carrier :=
  PrePolygon.notMem_carrier_of_sameEdges h.edges₁ h.notMem h.notMem_cover

theorem cover_subset_carrier₁ : cover K ⊆ J₁.carrier := by
  rw [h.carrier₁]; exact Set.subset_union_right

theorem carrier₁_subset : J₁.carrier ⊆ C.carrier ∪ cover K := by
  rw [h.carrier₁]
  exact Set.union_subset_union_left _ (C.arc_subset_carrier a k)

/-- The edges of the crosscut are nondegenerate, because they are edges of `J₁`. -/
theorem nondeg : ∀ Q ∈ K, Q.Nondeg := by
  intro Q hQ
  obtain ⟨R, hR, hRQ⟩ := h.edges₁.symm.exists_mem (List.mem_append_right _ hQ)
  have hRn : (orientPiece R).Nondeg := orientPiece_nondeg (J₁.pieces_nondeg R hR)
  rw [hRQ] at hRn
  rcases orientPiece_eq_or Q with e | e
  · rw [e] at hRn; exact hRn
  · rw [e] at hRn; exact fun hh => hRn hh.symm

/-- A ray direction transverse to every edge of `C` and of the crosscut at once. -/
theorem exists_direction : ∃ u : Plane, Plane.IsDirection u ∧
    (∀ Q ∈ C.pieces, hgt u Q.1 ≠ hgt u Q.2) ∧ (∀ Q ∈ K, hgt u Q.1 ≠ hgt u Q.2) := by
  obtain ⟨u, hu, hlev⟩ := exists_direction_hgt_ne (C.pieces ++ K) (by
    intro Q hQ
    rcases List.mem_append.1 hQ with hQ' | hQ'
    · exact C.pieces_nondeg Q hQ'
    · exact h.nondeg Q hQ')
  exact ⟨u, hu, fun Q hQ => hlev Q (List.mem_append_left _ hQ),
    fun Q hQ => hlev Q (List.mem_append_right _ hQ)⟩

/-! ### The two cells -/

theorem regionPairC :
    IsRegionPair C.carrier (farRegion C.carrier y) (connectedComponentIn C.carrierᶜ y) :=
  (C.isSeparating_carrier.isRegionPair_farRegion h.notMem).symm

theorem regionPair₁ :
    IsRegionPair J₁.carrier (connectedComponentIn J₁.carrierᶜ y) (farRegion J₁.carrier y) :=
  J₁.isSeparating_carrier.isRegionPair_farRegion h.notMem_carrier₁

/-- The untouched region of `ℝ² ∖ C` lies in one region of `ℝ² ∖ J₁`, namely the one of `y`. -/
theorem near_subset₁ :
    connectedComponentIn C.carrierᶜ y ⊆ connectedComponentIn J₁.carrierᶜ y := by
  refine IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn
    (mem_connectedComponentIn h.notMem) (fun w hw => ?_)
  have hwC : w ∉ C.carrier := connectedComponentIn_subset _ _ hw
  have hwK : w ∉ cover K := fun hK => Set.disjoint_left.1 h.avoids hK hw
  exact PrePolygon.notMem_carrier_of_sameEdges h.edges₁ hwC hwK

/-- **Lemma 2.6(a), first half**: the cell lies in `Ω ∖ P`. -/
theorem cell_subset₁ : farRegion J₁.carrier y ⊆ farRegion C.carrier y \ cover K :=
  cell_subset_region_diff (P := cover K) C.isSeparating_carrier J₁.isSeparating_carrier
    h.regionPairC h.regionPair₁ h.near_subset₁ h.cover_subset_carrier₁

theorem cell_subset₂ : farRegion J₂.carrier y ⊆ farRegion C.carrier y \ cover K :=
  h.symm.cell_subset₁

/-- **Lemma 2.6(a)**: the cell is a connected component of `Ω ∖ P`. -/
theorem cell_isComponent₁ : ∀ z ∈ farRegion J₁.carrier y,
    connectedComponentIn (farRegion C.carrier y \ cover K) z = farRegion J₁.carrier y :=
  cell_isComponent (P := cover K) C.isSeparating_carrier J₁.isSeparating_carrier
    h.regionPairC h.regionPair₁ h.near_subset₁ h.cover_subset_carrier₁ h.carrier₁_subset

theorem cell_isComponent₂ : ∀ z ∈ farRegion J₂.carrier y,
    connectedComponentIn (farRegion C.carrier y \ cover K) z = farRegion J₂.carrier y :=
  h.symm.cell_isComponent₁

/-- **Lemma 2.6(c)**: the closure of the cell meets the polygon exactly in its arc. -/
theorem closure_cell_inter₁ : closure (farRegion J₁.carrier y) ∩ C.carrier = C.arc a k := by
  rw [closure_cell_inter_curve C.isSeparating_carrier J₁.isSeparating_carrier
    h.regionPairC.right h.regionPair₁ h.near_subset₁, h.carrier₁]
  refine Set.Subset.antisymm ?_ (fun w hw => ⟨Or.inl hw, C.arc_subset_carrier a k hw⟩)
  rintro w ⟨hw | hw, hwC⟩
  · exact hw
  · exact h.meets₁ ⟨hw, hwC⟩

theorem closure_cell_inter₂ :
    closure (farRegion J₂.carrier y) ∩ C.carrier = C.arc (a + k) (m + 3 - k) :=
  h.symm.closure_cell_inter₁

/-! ### Exhaustion: the crossing counts add up -/

/-- **A point off `C ∪ P` is separated from `y` by `C` exactly when it is separated from `y` by
exactly one of `J₁, J₂`.** -/
theorem separates_xor {x : Plane} (hxC : x ∉ C.carrier) (hxK : x ∉ cover K) :
    x ∈ farRegion C.carrier y ↔
      (x ∈ farRegion J₁.carrier y ↔ ¬ x ∈ farRegion J₂.carrier y) := by
  obtain ⟨u, hu, hlevC, hlevK⟩ := h.exists_direction
  have hlev₁ := h.edges₁.hgt_ne (PrePolygon.arcPieces_append_hgt_ne hlevC hlevK)
  have hlev₂ := h.edges₂.hgt_ne (PrePolygon.arcPieces_append_hgt_ne hlevC hlevK)
  have hxJ₁ := PrePolygon.notMem_carrier_of_sameEdges h.edges₁ hxC hxK
  have hxJ₂ := PrePolygon.notMem_carrier_of_sameEdges h.edges₂ hxC hxK
  rw [← C.parity_ne_iff_mem_farRegion hu hlevC hxC h.notMem,
    ← J₁.parity_ne_iff_mem_farRegion hu hlev₁ hxJ₁ h.notMem_carrier₁,
    ← J₂.parity_ne_iff_mem_farRegion hu hlev₂ hxJ₂ h.symm.notMem_carrier₁]
  have hsx := C.parity_splitting u a h.le h.edges₁ h.edges₂ x
  have hsy := C.parity_splitting u a h.le h.edges₁ h.edges₂ y
  have key : ∀ s₁ s₂ s t₁ t₂ t : ZMod 2, s₁ + s₂ = s → t₁ + t₂ = t →
      (s ≠ t ↔ ((s₁ ≠ t₁) ↔ ¬ (s₂ ≠ t₂))) := by decide
  exact key _ _ _ _ _ _ hsx hsy

/-- **Theorem 2.8, the two cells.** -/
theorem region_eq :
    farRegion C.carrier y \ cover K = farRegion J₁.carrier y ∪ farRegion J₂.carrier y := by
  refine Set.Subset.antisymm ?_ (Set.union_subset h.cell_subset₁ h.cell_subset₂)
  rintro w ⟨hwΩ, hwK⟩
  by_cases hw₁ : w ∈ farRegion J₁.carrier y
  · exact Or.inl hw₁
  · refine Or.inr ?_
    by_contra hw₂
    exact hw₁ (((h.separates_xor hwΩ.1 hwK).1 hwΩ).2 hw₂)

/-! ### Corollary 2.9 -/

/-- **The region the crosscut enters is the component of any of its points off `C`.** -/
theorem connectedComponentIn_cover_eq {z : Plane} (hz : z ∈ cover K) (hzC : z ∉ C.carrier) :
    connectedComponentIn C.carrierᶜ z = farRegion C.carrier y :=
  h.regionPairC.left.connectedComponentIn_eq C.isSeparating_carrier
    (diff_subset_farRegion h.avoids ⟨hz, hzC⟩)

/-- **Corollary 2.9, core form.** -/
theorem inter_cover_nonempty {Q : Set Plane} {w₁ w₂ : Plane}
    (hconn : IsPreconnected Q) (hside : Q ⊆ farRegion C.carrier y)
    (hw₁ : w₁ ∈ closure Q) (hw₂ : w₂ ∈ closure Q)
    (hw₁A : w₁ ∈ C.arc a k) (hw₁B : w₁ ∉ C.arc (a + k) (m + 3 - k))
    (hw₂B : w₂ ∈ C.arc (a + k) (m + 3 - k)) (hw₂A : w₂ ∉ C.arc a k) :
    (Q ∩ cover K).Nonempty := by
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty, Set.eq_empty_iff_forall_notMem] at hempty
  have hsub : Q ⊆ farRegion C.carrier y \ cover K :=
    fun z hz => ⟨hside hz, fun hzK => hempty z ⟨hz, hzK⟩⟩
  obtain ⟨z, hz⟩ : Q.Nonempty := by
    by_contra hQ
    rw [Set.not_nonempty_iff_eq_empty] at hQ
    rw [hQ, closure_empty] at hw₁
    simp at hw₁
  have hzcell : z ∈ farRegion J₁.carrier y ∪ farRegion J₂.carrier y := by
    rw [← h.region_eq]; exact hsub hz
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

/-- **Corollary 2.9 for a second crosscut presented as a simple arc.** -/
theorem arc_inter_cover_nonempty {Q : Set Plane} {w₁ w₂ : Plane}
    (hQ : IsArcBetween Q w₁ w₂) (hside : Q \ {w₁, w₂} ⊆ farRegion C.carrier y)
    (hw₁A : w₁ ∈ C.arc a k) (hw₁B : w₁ ∉ C.arc (a + k) (m + 3 - k))
    (hw₂B : w₂ ∈ C.arc (a + k) (m + 3 - k)) (hw₂A : w₂ ∉ C.arc a k) :
    (Q ∩ cover K).Nonempty := by
  obtain ⟨z, hzQ, hzK⟩ := h.inter_cover_nonempty hQ.isPreconnected_diff hside
    hQ.left_mem_closure_diff hQ.right_mem_closure_diff hw₁A hw₁B hw₂B hw₂A
  exact ⟨z, hzQ.1, hzK⟩

/-- **Corollary 2.9 in the shape a plane-graph argument produces it.** -/
theorem alternating_inter_nonempty {A B Q : Set Plane} {p q w₁ w₂ : Plane}
    (hA : C.arc a k = A) (hB : C.arc (a + k) (m + 3 - k) = B)
    (hAB : A ∩ B = ({p, q} : Set Plane))
    (hQ : IsArcBetween Q w₁ w₂) (hside : Q \ {w₁, w₂} ⊆ farRegion C.carrier y)
    (hw₁ : w₁ ∈ A \ ({p, q} : Set Plane)) (hw₂ : w₂ ∈ B \ ({p, q} : Set Plane)) :
    (Q ∩ cover K).Nonempty := by
  refine h.arc_inter_cover_nonempty hQ hside (hA ▸ hw₁.1) ?_ (hB ▸ hw₂.1) ?_
  · rw [hB]; exact fun hmem => hw₁.2 (hAB ▸ Set.mem_inter hw₁.1 hmem)
  · rw [hA]; exact fun hmem => hw₂.2 (hAB ▸ Set.mem_inter hmem hw₂.1)

/-- **Corollary 2.9 with "the same side" read as "the same connected component".** -/
theorem alternating_inter_nonempty_of_same_side {A B Q : Set Plane} {p q w₁ w₂ z : Plane}
    (hz : z ∈ cover K) (hzC : z ∉ C.carrier)
    (hA : C.arc a k = A) (hB : C.arc (a + k) (m + 3 - k) = B)
    (hAB : A ∩ B = ({p, q} : Set Plane))
    (hQ : IsArcBetween Q w₁ w₂)
    (hside : Q \ {w₁, w₂} ⊆ connectedComponentIn C.carrierᶜ z)
    (hw₁ : w₁ ∈ A \ ({p, q} : Set Plane)) (hw₂ : w₂ ∈ B \ ({p, q} : Set Plane)) :
    (Q ∩ cover K).Nonempty :=
  h.alternating_inter_nonempty hA hB hAB hQ
    (hside.trans (h.connectedComponentIn_cover_eq hz hzC).subset) hw₁ hw₂

end IsPrePolygonalCrosscut

end Schoenflies

namespace Graph

open Schoenflies

variable {β : Type*} {G : Graph Plane β} {x y : Fin 3 → Plane} {e : Fin 3 → Fin 3 → β}
variable {drawing : β → ℝ → Plane} {s : Fin 3} {R : Set Plane}

/-! ## The six-cycle and one remaining edge, as a crosscut

`Graph.IsHexCrosscut` of `Schoenflies/Graph/K33Planar.lean` is the same statement with
`Schoenflies.ClosedPolygon` for `Schoenflies.PrePolygon`; the change is what removes the corner
condition on the two cut points, which is the whole of the remaining gap. -/

/-- **The six-cycle and one remaining edge, realized as a polygonal crosscut**, with the two cut
points wherever the drawing put them. -/
def IsPreHexCrosscut (drawing : β → ℝ → Plane) (e : Fin 3 → Fin 3 → β) (s : Fin 3) : Prop :=
  ∃ (m m₁ m₂ : ℕ) (C : PrePolygon m) (J₁ : PrePolygon m₁) (J₂ : PrePolygon m₂)
    (K : List Piece) (a : ZMod (m + 3)) (k : ℕ) (yref : Plane),
      C.carrier = hexSet drawing e ∧
      C.arc a k = edgesCover drawing (arcA e s) ∧
      C.arc (a + k) (m + 3 - k) = edgesCover drawing (arcB e s) ∧
      cover K = edgeArc drawing (e s (s + 1)) ∧
      IsPrePolygonalCrosscut C J₁ J₂ K a k yref

namespace IsK33Config

/-- **The crosscut exists for any polygonal drawing.** The six-cycle is
realized as a `Schoenflies.PrePolygon` cut at the two ends of the remaining edge — possible
because a `PrePolygon` may have a vertex wherever one likes — and the two closed curves the
remaining edge forms with the two halves are then *built* from that realization and from one
presentation of the remaining edge, rather than found independently. That is what makes the three
edge lists agree, and it is why no matching lemma, and hence no general position, is needed. -/
theorem isPreHexCrosscut (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hpoly : ∀ f ∈ E(G), IsPolygonal (edgeArc drawing f)) (s : Fin 3) :
    IsPreHexCrosscut drawing e s := by
  have hpq : x s ≠ y (s + 1) := h.x_ne_y s (s + 1)
  have hA1 := h.arcA_isArcBetween hd s
  have hA2 := h.arcB_isArcBetween hd s
  have hCh := hd.edge_isArcBetween (h.isLink s (s + 1))
  have hinterA := h.chord_inter_arcA hd s
  have hinterB := h.chord_inter_arcB hd s
  have hPch : IsPolygonal (edgeArc drawing (e s (s + 1))) :=
    hpoly _ (h.isLink s (s + 1)).edge_mem
  have hP1 : IsPolygonal (edgesCover drawing (arcA e s) ∪ edgeArc drawing (e s (s + 1))) :=
    (h.isPolygonal_arcA hd hpoly s).union hPch ⟨x s, hA1.left_mem, hCh.left_mem⟩
  have hJ1 : IsJordanCurve (edgesCover drawing (arcA e s) ∪ edgeArc drawing (e s (s + 1))) :=
    IsJordanCurve.of_two_arcs hA1 hCh.reverse fun z hz1 hz2 => by
      have hz : z ∈ ({x s, y (s + 1)} : Set Plane) := hinterA ▸ ⟨hz1, hz2⟩
      simpa using hz
  -- The six-cycle, cut at the two ends of the remaining edge.
  obtain ⟨m, C, a, k, hCcar, hk1, hk2, hCa, hCak, hCarc1, hCarc2⟩ :=
    exists_prePolygon_arcs_oriented (h.hexagon_isJordanCurve hd) (h.isPolygonal_hexSet hd hpoly)
      (h.x_mem_hexSet hd s) (h.y_mem_hexSet hd (s + 1)) hpq hA1 hA2
      (arcs_union (drawing := drawing) (e := e) s) (h.arcs_inter hd s)
  -- The remaining edge, as the second arc of the curve it forms with the first half.
  obtain ⟨m₁, D, b, l, -, hl1, hl2, hDb, hDbl, hDarc1, hDarc2⟩ :=
    exists_prePolygon_arcs_oriented hJ1 hP1 (Or.inl hA1.left_mem) (Or.inl hA1.right_mem) hpq
      hA1 hCh rfl hinterA
  set c : ZMod (m₁ + 3) := b + (l : ZMod (m₁ + 3)) with hc
  set r : ℕ := m₁ + 3 - l with hr
  have hwrapD : c + (r : ZMod (m₁ + 3)) = b := zmod_add_sub_cancel (by omega) b
  have hDc : D.vertex c = y (s + 1) := hDbl
  have hDcr : D.vertex (c + (r : ZMod (m₁ + 3))) = x s := by rw [hwrapD]; exact hDb
  have hKcover : cover (D.arcPieces c r) = edgeArc drawing (e s (s + 1)) := hDarc2
  have hKinter : C.arc a k ∩ D.arc c r
      = ({C.vertex a, C.vertex (a + (k : ZMod (m + 3)))} : Set Plane) := by
    rw [hCarc1, hDarc2, hCa, hCak]; exact hinterA
  -- The first spliced curve: the first half of the six-cycle, then the remaining edge.
  obtain ⟨n₁, J₁, hJ₁p⟩ := PrePolygon.exists_splice C D hk1 hk2 (by omega) (by omega)
    (by rw [hDc, hCak]) (by rw [hDcr, hCa]) hKinter
  -- The second spliced curve, with the remaining edge traversed the other way.
  have hwrapC : a + (k : ZMod (m + 3)) + ((m + 3 - k : ℕ) : ZMod (m + 3)) = a :=
    zmod_add_sub_cancel (by omega) a
  set c' : ZMod (m₁ + 3) := -c - (r : ZMod (m₁ + 3)) with hc'
  have hDrev1 : D.reverse.vertex c' = x s := by
    rw [PrePolygon.reverse_vertex, hc', show -(-c - (r : ZMod (m₁ + 3))) = c + (r : ZMod (m₁ + 3))
      by ring]
    exact hDcr
  have hDrev2 : D.reverse.vertex (c' + (r : ZMod (m₁ + 3))) = y (s + 1) := by
    rw [PrePolygon.reverse_vertex, hc',
      show -(-c - (r : ZMod (m₁ + 3)) + (r : ZMod (m₁ + 3))) = c by ring]
    exact hDc
  have hKinter' : C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∩ D.reverse.arc c' r
      = ({C.vertex (a + (k : ZMod (m + 3))),
          C.vertex (a + (k : ZMod (m + 3)) + ((m + 3 - k : ℕ) : ZMod (m + 3)))} : Set Plane) := by
    rw [hCarc2, hc', D.reverse_arc c r, hDarc2, hwrapC, hCa, hCak, Set.pair_comm]
    exact hinterB
  obtain ⟨n₂, J₂, hJ₂p⟩ := PrePolygon.exists_splice C D.reverse (a := a + (k : ZMod (m + 3)))
    (k := m + 3 - k) (b := c') (l := r) (by omega) (by omega) (by omega) (by omega)
    (by rw [hDrev1, hwrapC, hCa]) (by rw [hDrev2, hCak]) hKinter'
  -- The reference point, and the two "meets" clauses.
  have hsep : IsSeparating (hexSet drawing e) := hCcar ▸ C.isSeparating_carrier
  obtain ⟨yref, hyref, hdisj⟩ := h.exists_reference_point hd hsep s
  refine ⟨m, n₁, n₂, C, J₁, J₂, D.arcPieces c r, a, k, yref, hCcar, hCarc1, hCarc2, hKcover,
    ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hJ₁p]
  · rw [hJ₂p]
    exact SameEdges.append (SameEdges.refl _) (D.sameEdges_reverse_arcPieces c r)
  · rw [hKcover, hCcar, hCarc1, h.chord_inter_hexSet hd s]
    exact h.endpoints_subset_arcA hd s
  · rw [hKcover, hCcar, hCarc2, h.chord_inter_hexSet hd s]
    exact h.endpoints_subset_arcB hd s
  · rw [hCcar]; exact hyref
  · rw [hKcover, hCcar]; exact hdisj

/-! ### The contradiction -/

/-- **The two remaining edges indexed by `s` and `s + 1` cannot lie in one region.** Their four
ends alternate around the six-cycle, so `cor:alternating-crosscuts` makes them meet; but distinct
edges of a plane graph meet only at shared vertices, and these two share none. -/
theorem false_of_isPreHexCrosscut (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hcross : IsPreHexCrosscut drawing e s) (hsep : IsSeparating (hexSet drawing e))
    (hR : IsRegionOf (hexSet drawing e) R)
    (h1 : openArc (drawing (e s (s + 1))) ⊆ R)
    (h2 : openArc (drawing (e (s + 1) (s + 1 + 1))) ⊆ R) : False := by
  obtain ⟨m, m₁, m₂, C, J₁, J₂, K, a, k, yref, hcar, hA, hB, hK, hcc⟩ := hcross
  obtain ⟨z, hz⟩ := chord_openArc_nonempty (drawing := drawing) (e := e) s
  have hzK : z ∈ cover K := by rw [hK]; exact h.chord_openArc_subset_edgeArc hd s hz
  have hzC : z ∉ C.carrier := by rw [hcar]; exact h.chord_openArc_subset_compl hd s hz
  have hzR : z ∈ R := h1 hz
  have hside : edgeArc drawing (e (s + 1) (s + 1 + 1)) \ ({x (s + 1), y (s + 1 + 1)} : Set Plane)
      ⊆ connectedComponentIn C.carrierᶜ z := by
    rw [hcar, hR.connectedComponentIn_eq hsep hzR, ← h.chord_openArc_eq hd (s + 1)]
    exact h2
  obtain ⟨w, hw₁, hw₂⟩ := hcc.alternating_inter_nonempty_of_same_side hzK hzC hA hB
    (h.arcs_inter hd s) (hd.edge_isArcBetween (h.isLink (s + 1) (s + 1 + 1))) hside
    (h.x_succ_mem_arcA hd s) (h.y_succ_mem_arcB hd s)
  have hs1 : ∀ s : Fin 3, s + 1 ≠ s := by decide
  have hdis := h.chords_disjoint hd (hs1 s)
  rw [Set.eq_empty_iff_forall_notMem] at hdis
  exact hdis w ⟨hw₁, by rwa [hK] at hw₂⟩

/-- **`lem:k33` for a drawing that is already polygonal, with nothing assumed.** -/
theorem false_of_polygonal (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hpoly : ∀ f ∈ E(G), IsPolygonal (edgeArc drawing f)) : False := by
  have hsep : IsSeparating (hexSet drawing e) := by
    obtain ⟨_, _, _, C, _, _, _, _, _, _, hcar, _⟩ := h.isPreHexCrosscut hd hpoly 0
    exact hcar ▸ C.isSeparating_carrier
  obtain ⟨s, t, hst, R, hR, h1, h2⟩ := h.exists_two_chords_same_region hd hsep
  have hpair : ∀ s t : Fin 3, s ≠ t → t = s + 1 ∨ s = t + 1 := by decide
  rcases hpair s t hst with rfl | rfl
  · exact h.false_of_isPreHexCrosscut hd (h.isPreHexCrosscut hd hpoly s) hsep hR h1 h2
  · exact h.false_of_isPreHexCrosscut hd (h.isPreHexCrosscut hd hpoly t) hsep hR h2 h1

/-- **Lemma 3.10 (nonplanarity of `K(3,3)`), with no hypothesis left.** A finite graph carrying a
copy of `K(3,3)` has no plane drawing.

`lem:polygonal-redrawing` replaces an arbitrary drawing by a polygonal one on the same graph and
the same vertices; the contradiction is then `false_of_polygonal`. This is
`Graph.IsK33Config.not_isDrawing` of `Schoenflies/Graph/K33Planar.lean` with its realization
hypothesis discharged, and `Graph.IsK33Config.not_isDrawing_of_bendable` of
`Schoenflies/Graph/K33Closed.lean` with `Graph.Bendable` discharged: no drawing has to be bent,
because the crosscut no longer needs the six vertices to be corners. -/
theorem not_exists_isDrawing [G.Finite] (h : IsK33Config G x y e) :
    ¬ ∃ dr : β → ℝ → Plane, IsDrawing G dr := by
  rintro ⟨dr, hdr⟩
  obtain ⟨dr', hdr', hpoly'⟩ := polygonal_redrawing G dr hdr
  exact h.false_of_polygonal hdr' hpoly'

end IsK33Config

/-- **`lem:k33` for nine arcs**: no nine arcs in the plane meet only where a
`K(3,3)` forces them to. -/
theorem IsArcK33.elim {P : Fin 3 → Fin 3 → Set Plane} (h : IsArcK33 x y P) : False :=
  h.isK33Config.not_exists_isDrawing ⟨h.arcDrawing, h.isDrawing⟩

/-- **Corollary 3.11 (subdivisions of `K(3,3)`).** No subdivision of `K(3,3)`
has a plane drawing. -/
theorem IsK33Subdivision.elim {H : Graph Plane β} {W : Fin 3 → Fin 3 → List β}
    (hd : IsDrawing H drawing) (h : IsK33Subdivision H x y W) : False :=
  (h.isArcK33 hd).elim

/-- **The headline: `K(3,3)` has no plane drawing.** Stated for the concrete graph
`Graph.k33Graph x y`, whose nine edges are the index pairs, with nothing assumed beyond the six
points being six distinct points of the plane. -/
theorem k33Graph_not_exists_isDrawing (x y : Fin 3 → Plane) (hx : Function.Injective x)
    (hy : Function.Injective y) (hxy : ∀ i j, x i ≠ y j) :
    ¬ ∃ dr : Fin 3 × Fin 3 → ℝ → Plane, IsDrawing (k33Graph x y) dr :=
  IsK33Config.not_exists_isDrawing ⟨k33Graph_isLink x y, hx, hy, hxy⟩

end Graph

end BundlePart424

section BundlePart425
/- Source: Papers/GraphicalZonotopes/PlanarCrosscutObstruction.lean -/



/-!
Actual plane-drawing obstructions used in the planar corollaries.

The auxiliary intersection theorem below uses the proved polygonal crosscut theorem,
not an assumed Euler identity or a definition of planarity by an edge inequality.
-/

open Set Schoenflies

namespace GraphicalZonotopes.PlanarGeometry

/-- Alternating simple arcs in the same complementary region of a polygonal
Jordan curve must intersect.  The second arc may be an arbitrary topological arc. -/
theorem alternating_arc_inter_nonempty
    {C A B P Q Ω : Set Plane} {p q u v : Plane}
    (hC : IsSeparating C) (hCpoly : IsPolygonal C)
    (hA : IsArcBetween A p q) (hB : IsArcBetween B p q)
    (hApoly : IsPolygonal A) (hBpoly : IsPolygonal B)
    (hAB : A ∪ B = C) (hAiB : A ∩ B = {p, q})
    (hP : IsArcBetween P p q) (hPpoly : IsPolygonal P)
    (hPC : P ∩ C = {p, q})
    (hΩ : IsRegionOf C Ω) (hPΩ : P \ {p, q} ⊆ Ω)
    (hQ : IsArcBetween Q u v) (hQΩ : Q \ {u, v} ⊆ Ω)
    (hu : u ∈ A \ {p, q}) (hv : v ∈ B \ {p, q}) :
    (Q ∩ P).Nonempty := by
  classical
  by_contra hempty
  have hdis : ∀ z ∈ Q, z ∉ P := by
    intro z hz hzp
    exact hempty ⟨z, hz, hzp⟩
  have hsub : Q \ {u, v} ⊆ Ω \ P := fun z hz =>
    ⟨hQΩ hz, hdis z hz.1⟩
  obtain ⟨z, hz⟩ : (Q \ {u, v}).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hlim := hQ.left_mem_closure_diff
    simpa [h] using hlim
  have hsubset := hQ.isPreconnected_diff.subset_connectedComponentIn hz hsub
  have hucl : u ∈ closure (connectedComponentIn (Ω \ P) z) :=
    closure_mono hsubset hQ.left_mem_closure_diff
  have hvcl : v ∈ closure (connectedComponentIn (Ω \ P) z) :=
    closure_mono hsubset hQ.right_mem_closure_diff
  have hAC : A ⊆ C := by rw [← hAB]; exact Set.subset_union_left
  have hBC : B ⊆ C := by rw [← hAB]; exact Set.subset_union_right
  have hsep : ∀ {D : Set Plane}, IsArcBetween D p q →
      IsPolygonal D → D ⊆ C → IsSeparating (D ∪ P) := by
    intro D hD hDp hDC
    apply Schoenflies.isSeparating_of_isJordanCurve
    · apply Schoenflies.isJordanCurve_union hD hP
      intro w hwD hwP
      have hw : w ∈ ({p, q} : Set Plane) := by
        rw [← hPC]
        exact ⟨hwP, hDC hwD⟩
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hw
    · exact hDp.union hPpoly ⟨p, hD.left_mem, hP.left_mem⟩
  have huB : u ∉ B := by
    intro huB
    exact hu.2 (hAiB ▸ (show u ∈ A ∩ B from ⟨hu.1, huB⟩))
  have hvA : v ∉ A := by
    intro hvA
    exact hv.2 (hAiB ▸ (show v ∈ A ∩ B from ⟨hvA, hv.1⟩))
  have hcompC : connectedComponentIn (Ω \ P) z ⊆ Cᶜ :=
    (connectedComponentIn_subset _ _).trans (Set.diff_subset.trans hΩ.subset_compl)
  rcases Schoenflies.crosscutSplitsRegion C A B P Ω p q hC hCpoly hPpoly
      hA hB hAB hAiB hP hPC hΩ hPΩ z (hsub hz) with hreg | hreg
  · rw [hreg.closure_eq (hsep hA hApoly hAC)] at hvcl
    rcases hvcl with hvcomp | hvA' | hvP
    · exact hcompC hvcomp (hBC hv.1)
    · exact hvA hvA'
    · exact hdis v hQ.right_mem hvP
  · rw [hreg.closure_eq (hsep hB hBpoly hBC)] at hucl
    rcases hucl with hucomp | huB' | huP
    · exact hcompC hucomp (hAC hu.1)
    · exact huB huB'
    · exact hdis u hQ.left_mem huP

end GraphicalZonotopes.PlanarGeometry

end BundlePart425

section BundlePart426
/- Source: Papers/GraphicalZonotopes/ArcK5Geometry.lean -/




open Set Schoenflies GraphicalZonotopes.PlanarGeometry

namespace Graph
namespace IsArcK5

variable {x : Fin 5 → Plane} {P : Fin 5 → Fin 5 → Set Plane}
variable (h : IsArcK5 x P)
include h

theorem inter_indices {i j k l : Fin 5} (hij : i ≠ j) (hkl : k ≠ l)
    (hne : (i, j) ≠ (k, l)) (hrev : (i, j) ≠ (l, k))
    {z : Plane} (hz : z ∈ P i j) (hz' : z ∈ P k l) :
    ∃ t : Fin 5, z = x t ∧ (t = i ∨ t = j) ∧ (t = k ∨ t = l) := by
  have hm := (h.meet i j k l hij hkl hne hrev ⟨hz, hz'⟩).1
  rcases hm with rfl | rfl
  · exact ⟨i, rfl, Or.inl rfl, h.vertex k l i hkl hz'⟩
  · exact ⟨j, rfl, Or.inr rfl, h.vertex k l j hkl hz'⟩

theorem disjoint_edges {i j k l : Fin 5} (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    Disjoint (P i j) (P k l) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  obtain ⟨t, _, ht, ht'⟩ := h.inter_indices hij hkl
    (fun e => hik (congrArg Prod.fst e))
    (fun e => hil (congrArg Prod.fst e)) hz hz'
  rcases ht with rfl | rfl <;> rcases ht' with h' | h'
  exacts [hik h', hil h', hjk h', hjl h']

omit h in
def two (P : Fin 5 → Fin 5 → Set Plane) (i j k : Fin 5) : Set Plane :=
  P i j ∪ P j k

theorem two_arc {i j k : Fin 5} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    IsArcBetween (two P i j k) (x i) (x k) := by
  apply (h.arc i j hij).concatenate (h.arc j k hjk)
  intro z hz hz'
  obtain ⟨t, rfl, ht, ht'⟩ := h.inter_indices hij hjk
    (fun e => hij (congrArg Prod.fst e))
    (fun e => hik (congrArg Prod.fst e)) hz hz'
  rcases ht with rfl | rfl
  · rcases ht' with h' | h'
    · exact (hij h').elim
    · exact (hik h').elim
  · rfl

theorem two_poly (hpoly : ∀ i j, i ≠ j → IsPolygonal (P i j))
    {i j k : Fin 5} (hij : i ≠ j) (hjk : j ≠ k) :
    IsPolygonal (two P i j k) :=
  (hpoly i j hij).union (hpoly j k hjk)
    ⟨x j, (h.arc i j hij).right_mem, (h.arc j k hjk).left_mem⟩

theorem vertex_two {i j k t : Fin 5} (hij : i ≠ j) (hjk : j ≠ k)
    (ht : x t ∈ two P i j k) : t = i ∨ t = j ∨ t = k := by
  rcases ht with ht | ht
  · rcases h.vertex i j t hij ht with he | he
    · exact Or.inl he
    · exact Or.inr (Or.inl he)
  · exact Or.inr (h.vertex j k t hjk ht)

omit h in
/-- The four-cycle through the first four branch vertices. -/
def fourCycle (P : Fin 5 → Fin 5 → Set Plane) : Set Plane :=
  two P 0 1 2 ∪ two P 0 3 2

theorem fourCycle_arcs_inter :
    two P 0 1 2 ∩ two P 0 3 2 = ({x 0, x 2} : Set Plane) := by
  apply Set.Subset.antisymm
  · rintro z ⟨hz, hz'⟩
    rcases hz with hz | hz <;> rcases hz' with hz' | hz'
    all_goals
      obtain ⟨t, rfl, ht, ht'⟩ := h.inter_indices
        (by decide) (by decide) (by decide) (by decide) hz hz'
      fin_cases t <;> simp_all
  · rintro z (rfl | rfl)
    · exact ⟨(h.two_arc (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide)).left_mem,
        (h.two_arc (i := 0) (j := 3) (k := 2) (by decide) (by decide) (by decide)).left_mem⟩
    · exact ⟨(h.two_arc (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide)).right_mem,
        (h.two_arc (i := 0) (j := 3) (k := 2) (by decide) (by decide) (by decide)).right_mem⟩

theorem fourCycle_sep (hpoly : ∀ i j, i ≠ j → IsPolygonal (P i j)) :
    IsSeparating (fourCycle P) := by
  apply Schoenflies.isSeparating_of_isJordanCurve
  · apply Schoenflies.isJordanCurve_union
      (h.two_arc (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide))
      (h.two_arc (i := 0) (j := 3) (k := 2) (by decide) (by decide) (by decide))
    intro z hz hz'
    have hm := h.fourCycle_arcs_inter ▸ (show z ∈ two P 0 1 2 ∩ two P 0 3 2 from ⟨hz, hz'⟩)
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hm
  · exact (h.two_poly hpoly (i := 0) (j := 1) (k := 2) (by decide) (by decide)).union
      (h.two_poly hpoly (i := 0) (j := 3) (k := 2) (by decide) (by decide))
      ⟨x 0,
        (h.two_arc (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide)).left_mem,
        (h.two_arc (i := 0) (j := 3) (k := 2) (by decide) (by decide) (by decide)).left_mem⟩

theorem fifth_not_fourCycle : x 4 ∉ fourCycle P := by
  rintro (hm | hm)
  · have := h.vertex_two (by decide : (0 : Fin 5) ≠ 1) (by decide : (1 : Fin 5) ≠ 2) hm
    simp at this
  · have := h.vertex_two (by decide : (0 : Fin 5) ≠ 3) (by decide : (3 : Fin 5) ≠ 2) hm
    simp at this

omit h in
abbrev cycleSide (i j : Fin 5) : Prop :=
  (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 2)

theorem inter_fourCycle_pair {i j : Fin 5} (hij : i ≠ j)
    (hne : ∀ a b, cycleSide a b → (i, j) ≠ (a, b) ∧ (i, j) ≠ (b, a)) :
    P i j ∩ fourCycle P ⊆ ({x i, x j} : Set Plane) := by
  rintro z ⟨hz, hzC⟩
  rcases hzC with (hzC | hzC) | (hzC | hzC)
  · exact (h.meet i j 0 1 hij (by decide) (hne 0 1 (by decide)).1
      (hne 0 1 (by decide)).2 ⟨hz, hzC⟩).1
  · exact (h.meet i j 1 2 hij (by decide) (hne 1 2 (by decide)).1
      (hne 1 2 (by decide)).2 ⟨hz, hzC⟩).1
  · exact (h.meet i j 0 3 hij (by decide) (hne 0 3 (by decide)).1
      (hne 0 3 (by decide)).2 ⟨hz, hzC⟩).1
  · exact (h.meet i j 3 2 hij (by decide) (hne 3 2 (by decide)).1
      (hne 3 2 (by decide)).2 ⟨hz, hzC⟩).1

theorem diagonal_inter_fourCycle :
    P 0 2 ∩ fourCycle P = ({x 0, x 2} : Set Plane) := by
  apply Set.Subset.antisymm (h.inter_fourCycle_pair (by decide) (by decide))
  rintro z (rfl | rfl)
  · exact ⟨(h.arc 0 2 (by decide)).left_mem,
      Or.inl (h.two_arc (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide)).left_mem⟩
  · exact ⟨(h.arc 0 2 (by decide)).right_mem,
      Or.inl (h.two_arc (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide)).right_mem⟩

theorem fourCycle_poly (hpoly : ∀ i j, i ≠ j → IsPolygonal (P i j)) :
    IsPolygonal (fourCycle P) :=
  (h.two_poly hpoly (i := 0) (j := 1) (k := 2) (by decide) (by decide)).union
    (h.two_poly hpoly (i := 0) (j := 3) (k := 2) (by decide) (by decide))
    ⟨x 0,
      (h.two_arc (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide)).left_mem,
      (h.two_arc (i := 0) (j := 3) (k := 2) (by decide) (by decide) (by decide)).left_mem⟩

theorem diagonal_intersects (hpoly : ∀ i j, i ≠ j → IsPolygonal (P i j))
    {Q Ω : Set Plane} (hΩ : IsRegionOf (fourCycle P) Ω)
    (hPΩ : P 0 2 \ {x 0, x 2} ⊆ Ω)
    (hQ : IsArcBetween Q (x 1) (x 3)) (hQΩ : Q \ {x 1, x 3} ⊆ Ω) :
    (Q ∩ P 0 2).Nonempty := by
  apply alternating_arc_inter_nonempty (h.fourCycle_sep hpoly) (h.fourCycle_poly hpoly)
    (h.two_arc (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide))
    (h.two_arc (i := 0) (j := 3) (k := 2) (by decide) (by decide) (by decide))
    (h.two_poly hpoly (i := 0) (j := 1) (k := 2) (by decide) (by decide))
    (h.two_poly hpoly (i := 0) (j := 3) (k := 2) (by decide) (by decide))
    rfl h.fourCycle_arcs_inter (h.arc 0 2 (by decide)) (hpoly 0 2 (by decide))
    h.diagonal_inter_fourCycle hΩ hPΩ hQ hQΩ
  · refine ⟨Or.inl (h.arc 0 1 (by decide)).right_mem, ?_⟩
    rintro (he | he) <;> have := h.injective he <;> norm_num at this
  · refine ⟨Or.inl (h.arc 0 3 (by decide)).right_mem, ?_⟩
    rintro (he | he) <;> have := h.injective he <;> norm_num at this

theorem fifth_path_diff_subset_compl :
    two P 1 4 3 \ {x 1, x 3} ⊆ (fourCycle P)ᶜ := by
  rintro z ⟨hz, hzends⟩ hzC
  rcases hz with hz | hz
  · have hm := h.inter_fourCycle_pair (i := 1) (j := 4) (by decide) (by decide) ⟨hz, hzC⟩
    rcases hm with rfl | rfl
    · exact hzends (Or.inl rfl)
    · exact h.fifth_not_fourCycle hzC
  · have hm := h.inter_fourCycle_pair (i := 4) (j := 3) (by decide) (by decide) ⟨hz, hzC⟩
    rcases hm with rfl | rfl
    · exact h.fifth_not_fourCycle hzC
    · exact hzends (Or.inr rfl)

theorem fifth_mem_path_diff : x 4 ∈ two P 1 4 3 \ {x 1, x 3} := by
  refine ⟨Or.inl (h.arc 1 4 (by decide)).right_mem, ?_⟩
  rintro (he | he) <;> have := h.injective he <;> norm_num at this

/-- A region containing the first diagonal cannot also contain the fifth vertex:
the two incident edges through that vertex give an alternating crosscut. -/
theorem diagonal_fifth_false (hpoly : ∀ i j, i ≠ j → IsPolygonal (P i j))
    {Ω : Set Plane} (hΩ : IsRegionOf (fourCycle P) Ω)
    (hPΩ : P 0 2 \ {x 0, x 2} ⊆ Ω) (hx4 : x 4 ∈ Ω) : False := by
  have hR := h.two_arc (i := 1) (j := 4) (k := 3) (by decide) (by decide) (by decide)
  have hRΩ : two P 1 4 3 \ {x 1, x 3} ⊆ Ω := by
    have hh := hR.isPreconnected_diff.subset_connectedComponentIn
      h.fifth_mem_path_diff h.fifth_path_diff_subset_compl
    rwa [hΩ.connectedComponentIn_eq (h.fourCycle_sep hpoly) hx4] at hh
  obtain ⟨z, hzR, hzP⟩ := h.diagonal_intersects hpoly hΩ hPΩ hR hRΩ
  rcases hzR with hzR | hzR
  · exact Set.disjoint_left.1 (h.disjoint_edges
      (i := 0) (j := 2) (k := 1) (l := 4)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hzP hzR
  · exact Set.disjoint_left.1 (h.disjoint_edges
      (i := 0) (j := 2) (k := 4) (l := 3)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hzP hzR

theorem relabel (e : Fin 5 ≃ Fin 5) :
    IsArcK5 (fun i => x (e i)) (fun i j => P (e i) (e j)) where
  injective := h.injective.comp e.injective
  arc i j hij := h.arc (e i) (e j) (fun h' => hij (e.injective h'))
  symm i j := h.symm (e i) (e j)
  vertex i j k hij hmem := by
    rcases h.vertex (e i) (e j) (e k) (fun h' => hij (e.injective h')) hmem with he | he
    · exact Or.inl (e.injective he)
    · exact Or.inr (e.injective he)
  meet i j k l hij hkl hne hrev := by
    apply h.meet (e i) (e j) (e k) (e l)
      (fun h' => hij (e.injective h')) (fun h' => hkl (e.injective h'))
    · intro he
      exact hne (Prod.ext (e.injective (congrArg Prod.fst he))
        (e.injective (congrArg Prod.snd he)))
    · intro he
      exact hrev (Prod.ext (e.injective (congrArg Prod.fst he))
        (e.injective (congrArg Prod.snd he)))

omit h in
def alternateOrder : Fin 5 ≃ Fin 5 := (Equiv.swap 0 1).trans (Equiv.swap 2 3)

theorem fourCycle_alternate :
    fourCycle (fun i j => P (alternateOrder i) (alternateOrder j)) = fourCycle P := by
  change (P 1 0 ∪ P 0 3) ∪ (P 1 2 ∪ P 2 3) = (P 0 1 ∪ P 1 2) ∪ (P 0 3 ∪ P 3 2)
  rw [h.symm 1 0, h.symm 2 3]
  ext z
  simp only [Set.mem_union]
  tauto

omit h in
private theorem arc_diff_nonempty {A : Set Plane} {a b : Plane}
    (hA : IsArcBetween A a b) : (A \ {a, b}).Nonempty := by
  by_contra hn
  rw [Set.not_nonempty_iff_eq_empty] at hn
  have hh := hA.left_mem_closure_diff
  simpa [hn] using hh

/-- Five pairwise connected branch points cannot be drawn by polygonal arcs
meeting only at their common endpoints. -/
theorem false_of_polygonal (hpoly : ∀ i j, i ≠ j → IsPolygonal (P i j)) : False := by
  classical
  have hC := h.fourCycle_sep hpoly
  have hP := h.arc 0 2 (by decide)
  have hQ := h.arc 1 3 (by decide)
  have hPcomp : P 0 2 \ {x 0, x 2} ⊆ (fourCycle P)ᶜ := by
    rintro z ⟨hz, hzends⟩ hzC
    exact hzends (h.inter_fourCycle_pair (by decide) (by decide) ⟨hz, hzC⟩)
  have hQcomp : P 1 3 \ {x 1, x 3} ⊆ (fourCycle P)ᶜ := by
    rintro z ⟨hz, hzends⟩ hzC
    exact hzends (h.inter_fourCycle_pair (by decide) (by decide) ⟨hz, hzC⟩)
  obtain ⟨Ω, Ω', hpair, hPΩ⟩ := hC.exists_isRegionPair_subset
    hP.isPreconnected_diff (arc_diff_nonempty hP) (Set.disjoint_left.2 hPcomp)
  have hcover : P 1 3 \ {x 1, x 3} ⊆ Ω ∪ Ω' := by
    rw [hpair.union_eq]
    exact hQcomp
  have hQΩ' : P 1 3 \ {x 1, x 3} ⊆ Ω' := by
    intro z hz
    rcases hcover hz with hzΩ | hzΩ'
    · have hQΩ := hQ.isPreconnected_diff.subset_left_of_subset_union
        (hpair.left.isOpen hC) (hpair.right.isOpen hC) hpair.disjoint hcover ⟨z, hz, hzΩ⟩
      obtain ⟨w, hwQ, hwP⟩ := h.diagonal_intersects hpoly hpair.left hPΩ hQ hQΩ
      exact (Set.disjoint_left.1 (h.disjoint_edges
        (i := 0) (j := 2) (k := 1) (l := 3)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hwP hwQ).elim
    · exact hzΩ'
  have hx4 : x 4 ∈ Ω ∪ Ω' := by
    rw [hpair.union_eq]
    exact h.fifth_not_fourCycle
  rcases hx4 with hx4 | hx4
  · exact h.diagonal_fifth_false hpoly hpair.left hPΩ hx4
  · have h' := h.relabel alternateOrder
    have hp' : ∀ i j, i ≠ j → IsPolygonal (P (alternateOrder i) (alternateOrder j)) :=
      fun i j hij => hpoly _ _ (fun he => hij (alternateOrder.injective he))
    apply h'.diagonal_fifth_false hp' (Ω := Ω')
    · rw [h.fourCycle_alternate]
      exact hpair.right
    · change P 1 3 \ {x 1, x 3} ⊆ Ω'
      exact hQΩ'
    · change x 4 ∈ Ω'
      exact hx4

/-- No topological K5 arc configuration exists.  This includes subdivisions:
each branch path is simply the arc joining its two branch vertices. -/
theorem elim : False := by
  obtain ⟨P', hP', hpoly⟩ := h.exists_polygonal
  exact hP'.false_of_polygonal hpoly

end IsArcK5
end Graph

end BundlePart426

section BundlePart427
/- Source: Papers/GraphicalZonotopes/ThreeTreeTriangleApex.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every component left after deleting a triangle of a 3-tree contains
an apex of a tetrahedron on that triangle. The path is an actual graph path
in the complement of the triangle, rather than a clique-incidence path. -/
theorem ThreeTreeOn.triangle_apex_reachable {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (T : Finset V) (hT : T.card = 3) (hcT : G.IsClique T)
    (x : V) (hxS : x ∈ S) (hxT : x ∉ T) :
    ∃ w, w ∈ S ∧ ∃ hwT : w ∉ T,
      (∀ t ∈ T, G.Adj w t) ∧
      (G.induce ((T : Set V)ᶜ)).Reachable ⟨x,hxT⟩ ⟨w,hwT⟩ := by
  induction h generalizing T x with
  | tetrahedron C hC =>
    have hTC := (ThreeTreeOn.tetrahedron C hC).clique_subset_active (by omega) hcT
    refine ⟨x,hxS,hxT,?_,SimpleGraph.Reachable.rfl⟩
    intro t ht
    exact ⟨fun he => hxT (he ▸ ht),hxS,hTC ht⟩
  | @attach S G h u hu A hA hAS hcA ih =>
    by_cases huT : u ∈ T
    · have hTA : T.erase u ⊆ A := by
        intro t ht
        exact (attached_vertex_adj_iff h hu hAS t).mp
          (hcT huT (mem_of_mem_erase ht) (Ne.symm (ne_of_mem_erase ht)))
      have hnot : ¬ A ⊆ T := by
        intro hAT
        have he : A = T := eq_of_subset_of_card_le hAT (by omega)
        exact hu (hAS (he.symm ▸ huT))
      obtain ⟨w,hwA,hwT⟩ := not_subset.mp hnot
      have hxold : x ∈ S := (mem_insert.mp hxS).resolve_left
        (fun he => hxT (he ▸ huT))
      have hxE : x ∉ T.erase u := fun hx => hxT (mem_of_mem_erase hx)
      have hwE : w ∉ T.erase u := fun hw => hwT (mem_of_mem_erase hw)
      let f : activeDelete G S (T.erase u) →g
          (G ⊔ attachmentStar u A).induce ((T : Set V)ᶜ) :=
        { toFun := fun v => ⟨v.1,by
            intro hvT
            exact v.2.2 (mem_erase.mpr
              ⟨fun he => hu (he ▸ v.2.1),hvT⟩)⟩
          map_rel' := fun hab => Or.inl hab }
      have hconn := h.delete_at_most_two_connected (T.erase u)
        (by rw [card_erase_of_mem huT,hT])
      have hp := (hconn.preconnected ⟨x,hxold,hxE⟩ ⟨w,hAS hwA,hwE⟩).map f
      refine ⟨w,mem_insert_of_mem (hAS hwA),hwT,?_,hp⟩
      intro t ht
      by_cases htu : t = u
      · subst t
        exact (G ⊔ attachmentStar u A).adj_symm
          ((attached_vertex_adj_iff h hu hAS w).mpr hwA)
      · exact Or.inl (hcA hwA (hTA (mem_erase.mpr ⟨htu,ht⟩))
          (fun he => hwT (he ▸ ht)))
    · have hcOld : G.IsClique T := clique_before_attachment huT hcT
      have hmono : G.induce ((T : Set V)ᶜ) ≤
          (G ⊔ attachmentStar u A).induce ((T : Set V)ᶜ) :=
        fun _ _ hvw => Or.inl hvw
      by_cases hxu : x = u
      · subst x
        by_cases hAT : A = T
        · refine ⟨u,mem_insert_self _ _,huT,?_,SimpleGraph.Reachable.rfl⟩
          intro t ht
          exact (attached_vertex_adj_iff h hu hAS t).mpr (hAT.symm ▸ ht)
        · have hnot : ¬ A ⊆ T := fun hh => hAT (eq_of_subset_of_card_le hh (by omega))
          obtain ⟨a,haA,haT⟩ := not_subset.mp hnot
          obtain ⟨w,hwS,hwT,hwAdj,hwPath⟩ := ih T hT hcOld a (hAS haA) haT
          refine ⟨w,mem_insert_of_mem hwS,hwT,fun t ht => Or.inl (hwAdj t ht),?_⟩
          have hua : ((G ⊔ attachmentStar u A).induce ((T : Set V)ᶜ)).Adj
              ⟨u,huT⟩ ⟨a,haT⟩ := (attached_vertex_adj_iff h hu hAS a).mpr haA
          exact hua.reachable.trans (hwPath.mono hmono)
      · have hxold : x ∈ S := (mem_insert.mp hxS).resolve_left hxu
        obtain ⟨w,hwS,hwT,hwAdj,hwPath⟩ := ih T hT hcOld x hxold hxT
        exact ⟨w,mem_insert_of_mem hwS,hwT,fun t ht => Or.inl (hwAdj t ht),
          hwPath.mono hmono⟩

/-- A graph-theoretic obstruction forced by a plane drawing: two different
apices over one triangle cannot be joined while avoiding that triangle.
The forbidden configuration consists of a triangle, its six apex spokes,
and an apex-to-apex path, hence is a subdivision of K₅. -/
def TriangleApexSeparated (G : SimpleGraph V) : Prop :=
  ∀ (T : Finset V), T.card = 3 → G.IsClique T →
    ∀ (u w : V) (hu : u ∉ T) (hw : w ∉ T), u ≠ w →
      (∀ t ∈ T, G.Adj u t) → (∀ t ∈ T, G.Adj w t) →
      ¬ (G.induce ((T : Set V)ᶜ)).Reachable ⟨u,hu⟩ ⟨w,hw⟩

theorem TriangleApexSeparated.mono {G H : SimpleGraph V}
    (hH : TriangleApexSeparated H) (hGH : G ≤ H) : TriangleApexSeparated G := by
  intro T hT hcT u w hu hw huw huT hwT hp
  exact hH T hT (fun a ha b hb hab => hGH (hcT ha hb hab)) u w hu hw huw
    (fun t ht => hGH (huT t ht)) (fun t ht => hGH (hwT t ht))
    (hp.mono (fun _ _ hadj => hGH hadj))

theorem TriangleApexSeparated.cliqueFree_five {G : SimpleGraph V}
    (hG : TriangleApexSeparated G) : G.CliqueFree 5 := by
  intro C hC
  obtain ⟨T,hTC,hT⟩ := exists_subset_card_eq (show 3 ≤ C.card by rw [hC.card_eq]; omega)
  have hd : (C \ T).card = 2 := by
    rw [card_sdiff_of_subset hTC,hC.card_eq,hT]
  obtain ⟨u,w,huw,hew⟩ := card_eq_two.mp hd
  have hu : u ∈ C ∧ u ∉ T := mem_sdiff.mp (by rw [hew]; simp)
  have hw : w ∈ C ∧ w ∉ T := mem_sdiff.mp (by rw [hew]; simp)
  apply hG T hT (fun a ha b hb hab => hC.isClique (hTC ha) (hTC hb) hab)
    u w hu.2 hw.2 huw
    (fun t ht => hC.isClique hu.1 (hTC ht) (fun he => hu.2 (he ▸ ht)))
    (fun t ht => hC.isClique hw.1 (hTC ht) (fun he => hw.2 (he ▸ ht)))
  exact SimpleGraph.Adj.reachable (hC.isClique hu.1 hw.1 huw)

/-- Under the actual triangle-apex obstruction, tetrahedral growth never
introduces an extra edge. This is the planar support argument without an
Euler formula or any assumed edge-density inequality. -/
theorem TetrahedralGrowth.induced_threeTree {G : SimpleGraph V} {S : Finset V}
    (h : TetrahedralGrowth G S) (hG : TriangleApexSeparated G) :
    ThreeTreeOn S (inducedOn G S) := by
  induction h with
  | base C hc hcl =>
    rw [inducedOn_clique hcl]
    exact ThreeTreeOn.tetrahedron C hc
  | @attach S h u hu T hT hTS hcT hadj ih =>
    have hcOld : (inducedOn G S).IsClique T :=
      fun a ha b hb hab => ⟨hcT ha hb hab,hTS ha,hTS hb⟩
    have hNT : earlierNeighbors G S u = T := by
      apply subset_antisymm
      · intro x hx
        obtain ⟨hxS,hux⟩ := (mem_earlierNeighbors G S u x).mp hx
        by_contra hxT
        obtain ⟨w,hwS,hwT,hwAdj,hwPath⟩ :=
          ih.triangle_apex_reachable T hT hcOld x hxS hxT
        have huT : u ∉ T := fun ht => hu (hTS ht)
        have huw : u ≠ w := fun he => hu (he ▸ hwS)
        apply hG T hT hcT u w huT hwT huw hadj
          (fun t ht => (hwAdj t ht).1)
        have hux' : (G.induce ((T : Set V)ᶜ)).Adj ⟨u,huT⟩ ⟨x,hxT⟩ := hux
        have hmono : (inducedOn G S).induce ((T : Set V)ᶜ) ≤
            G.induce ((T : Set V)ᶜ) := fun _ _ he => he.1
        exact hux'.reachable.trans (hwPath.mono hmono)
      · intro x hx
        exact (mem_earlierNeighbors G S u x).mpr ⟨hTS hx,hadj x hx⟩
    rw [inducedOn_insert_eq_attach G S T u hu hNT]
    exact ThreeTreeOn.attach ih u hu T hT hTS hcOld

theorem TriangleApexSeparated.connected_family_threeTree {G : SimpleGraph V}
    (hG : TriangleApexSeparated G) (F : Finset (Finset V)) (hne : F.Nonempty)
    (hcl : ∀ C ∈ F, C.card = 4 ∧ G.IsClique C)
    (hconn : (tetrahedronGraph F).Preconnected) :
    ThreeTreeOn (F.biUnion id) (inducedOn G (F.biUnion id)) :=
  (tetrahedralGrowth_of_connected_family G F hne hcl hconn).induced_threeTree hG

end GraphicalZonotopes

end
end
end BundlePart427

section BundlePart428
/- Source: Papers/GraphicalZonotopes/PlanarApexSeparation.lean -/






@[expose] public section
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- In a genuinely drawn planar graph, two distinct apices on one triangle
lie in different components after deleting that triangle. The proof constructs
a K₅ configuration from any alleged avoiding path and uses the complete
Jordan-separation obstruction for arbitrary continuous arcs. -/
theorem HasPlaneDrawing.triangle_apex_separated {G : SimpleGraph V}
    (hG : HasPlaneDrawing G) : TriangleApexSeparated G := by
  intro T hT hcT u w hu hw huw huAdj hwAdj hreach
  obtain ⟨x,P,hK5⟩ := hG.arcK5_of_triangle_apex_path
    T hT hcT u w hu hw huw huAdj hwAdj hreach
  exact hK5.elim

end GraphicalZonotopes

end
end
end BundlePart428

section BundlePart429
/- Source: Papers/GraphicalZonotopes/TriangleApexCount.lean -/





@[expose] public section
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The common neighbors of a triangle, with its own vertices excluded. -/
def commonApices (G : SimpleGraph V) (T : Finset V) : Finset V :=
  univ.filter (fun v => v ∉ T ∧ ∀ t ∈ T, G.Adj v t)

@[simp] theorem mem_commonApices (G : SimpleGraph V) (T : Finset V) (v : V) :
    v ∈ commonApices G T ↔ v ∉ T ∧ ∀ t ∈ T, G.Adj v t := by
  simp [commonApices]

theorem tetrahedra_over_triangle_eq_image {G : SimpleGraph V} {T : Finset V}
    (hT : T.card = 3) (hcT : G.IsClique T) :
    (tetrahedra G).filter (fun C => T ⊆ C) =
      (commonApices G T).image (fun u => insert u T) := by
  ext C
  constructor
  · intro hC
    obtain ⟨hC,hTC⟩ := mem_filter.mp hC
    obtain ⟨hcC,hclC⟩ := (mem_filter.mp hC).2
    have hd : (C \ T).card = 1 := by
      rw [card_sdiff_of_subset hTC,hcC,hT]
    obtain ⟨u,hu⟩ := card_eq_one.mp hd
    have huCT : u ∈ C ∧ u ∉ T := mem_sdiff.mp (by rw [hu]; simp)
    refine mem_image.mpr ⟨u,(mem_commonApices G T u).mpr ⟨huCT.2,?_⟩,?_⟩
    · intro t ht
      exact hclC huCT.1 (hTC ht) (fun he => huCT.2 (he ▸ ht))
    · ext v
      constructor
      · intro hv
        rcases mem_insert.mp hv with rfl | hv
        · exact huCT.1
        · exact hTC hv
      · intro hv
        by_cases hvT : v ∈ T
        · exact mem_insert_of_mem hvT
        · have hvm : v ∈ C \ T := mem_sdiff.mpr ⟨hv,hvT⟩
          rw [hu] at hvm
          exact mem_insert.mpr (Or.inl (mem_singleton.mp hvm))
  · intro hC
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hC
    obtain ⟨huT,huAdj⟩ := (mem_commonApices G T u).mp hu
    apply mem_filter.mpr
    refine ⟨mem_filter.mpr ⟨mem_univ _,?_,?_⟩,subset_insert _ _⟩
    · rw [card_insert_of_notMem huT,hT]
    · intro a ha b hb hab
      rcases mem_insert.mp ha with hau | haT
      · subst a
        exact huAdj b ((mem_insert.mp hb).resolve_left (Ne.symm hab))
      · rcases mem_insert.mp hb with hbu | hbT
        · subst b
          exact G.adj_symm (huAdj a haT)
        · exact hcT haT hbT hab

/-- The paper's tetrahedron multiplicity is literally the number of common
neighbors of its triangle. No maximal-clique or planarity convention enters
this elementary finite-set dictionary. -/
theorem triangleMultiplicity_eq_commonApices_card {G : SimpleGraph V} {T : Finset V}
    (hT : T.card = 3) (hcT : G.IsClique T) :
    triangleMultiplicity G T = (commonApices G T).card := by
  rw [triangleMultiplicity,tetrahedra_over_triangle_eq_image hT hcT]
  apply card_image_of_injOn
  intro u hu v hv he
  change insert u T = insert v T at he
  have huT := ((mem_commonApices G T u).mp hu).1
  have hum : u ∈ insert v T := by rw [← he]; exact mem_insert_self _ _
  exact (mem_insert.mp hum).resolve_right huT

end GraphicalZonotopes

end
end
end BundlePart429

section BundlePart430
/- Source: Papers/GraphicalZonotopes/PlanarK33.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical Graph
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A genuine plane drawing excludes a K₃,₃ subgraph. The imported obstruction
is the closed theorem for arbitrary continuous injective edge arcs. -/
theorem HasPlaneDrawing.no_complete_bipartite_three_three {G : SimpleGraph V}
    (hG : HasPlaneDrawing G) (x y : Fin 3 → V)
    (hx : Function.Injective x) (hy : Function.Injective y)
    (hxy : ∀ i j,x i ≠ y j) (hadj : ∀ i j,G.Adj (x i) (y j)) : False := by
  obtain ⟨p,hp,drawing,hd⟩ := hG
  let e : Fin 3 → Fin 3 → Sym2 V := fun i j => s(x i,y j)
  have hk : Graph.IsK33Config (PlaneDrawing.planeGraph G p) (p ∘ x) (p ∘ y) e := by
    constructor
    · intro i j
      exact (PlaneDrawing.planeGraph_isLink G p hp _ _ _).mpr ⟨rfl,hadj i j⟩
    · exact hp.comp hx
    · exact hp.comp hy
    · intro i j heq
      exact hxy i j (hp heq)
  exact hk.not_exists_isDrawing ⟨drawing,hd⟩

/-- Any three distinct vertices in a planar graph have at most two common
neighbours outside the triple. The three vertices need not themselves form
a triangle; the stronger statement is exactly the K₃,₃ obstruction. -/
theorem HasPlaneDrawing.common_apices_bound {G : SimpleGraph V}
    (hG : HasPlaneDrawing G) (T : Finset V) (hT : T.card = 3) :
    (univ.filter (fun v : V => v ∉ T ∧ ∀ t ∈ T,G.Adj v t)).card ≤ 2 := by
  classical
  by_contra hnot
  have hthree : 2 < (univ.filter
      (fun v : V => v ∉ T ∧ ∀ t ∈ T,G.Adj v t)).card := by omega
  obtain ⟨u,v,w,hu,hv,hw,huv,huw,hvw⟩ := two_lt_card_iff.mp hthree
  have hu' := (mem_filter.mp hu).2
  have hv' := (mem_filter.mp hv).2
  have hw' := (mem_filter.mp hw).2
  obtain ⟨a,b,c,hab,hac,hbc,hTabc⟩ := card_eq_three.mp hT
  let x : Fin 3 → V := ![a,b,c]
  let y : Fin 3 → V := ![u,v,w]
  have hx : Function.Injective x := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [x]
  have hy : Function.Injective y := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [y]
  have hxmem : ∀ i,x i ∈ T := by
    intro i
    fin_cases i <;> simp [x,hTabc]
  have hyoutside : ∀ j,y j ∉ T := by
    intro j
    fin_cases j
    · exact hu'.1
    · exact hv'.1
    · exact hw'.1
  have hyadj : ∀ j,∀ t ∈ T,G.Adj (y j) t := by
    intro j
    fin_cases j
    · exact hu'.2
    · exact hv'.2
    · exact hw'.2
  exact hG.no_complete_bipartite_three_three x y hx hy
    (fun i j heq => hyoutside j (heq ▸ hxmem i))
    (fun i j => G.adj_symm (hyadj j _ (hxmem i)))

/-- Planarity bounds the number of tetrahedra on any triangle by two. -/
theorem HasPlaneDrawing.triangleMultiplicity_le_two {G : SimpleGraph V}
    (hG : HasPlaneDrawing G) (T : Finset V) (hT : T.card = 3)
    (hcT : G.IsClique T) : triangleMultiplicity G T ≤ 2 := by
  rw [triangleMultiplicity_eq_commonApices_card hT hcT]
  exact hG.common_apices_bound T hT

/-- In particular every planar graph satisfies the admissibility bound used
by the full three-tree theorem. -/
theorem HasPlaneDrawing.admissible {G : SimpleGraph V}
    (hG : HasPlaneDrawing G) : Admissible G := by
  intro T hT hcT
  exact (hG.triangleMultiplicity_le_two T hT hcT).trans (by omega)

end GraphicalZonotopes

end
end
end BundlePart430

section BundlePart431
/- Source: Papers/GraphicalZonotopes/PlanarCombinatorics.lean -/






end BundlePart431

section BundlePart432
/- Source: Papers/GraphicalZonotopes/PlanarAnalyticSupport.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical BigOperators Pointwise
namespace GraphicalZonotopes
open Finset RefinedTriangleComponents
variable {V : Type*} [Fintype V] [LinearOrder V]

/-- The support argument needs only the actual forbidden triangle-apex
configuration. Its use for planar graphs is discharged by the independent
continuous-drawing obstruction, rather than an edge-count hypothesis. -/
theorem TriangleApexSeparated.extreme_support {G : SimpleGraph V} (hG : TriangleApexSeparated G)
    {z : SetFunction V} (hz : ExtremeSupermodular z) (hg : Graphical G z)
    (hd : 3 ≤ Module.finrank ℝ (vectorSpan ℝ (basePolytope z))) :
    ∃ U : Finset V,4 ≤ U.card ∧
      actualDirectionGraph (basePolytope z) = inducedOn G U ∧
      ThreeTreeOn U (inducedOn G U) ∧ Admissible (inducedOn G U) ∧
      Module.finrank ℝ (vectorSpan ℝ (basePolytope z)) = U.card-1 := by
  classical
  let F := family (mobius z)
  let U := F.biUnion id
  obtain ⟨hne,hconn,hactual,hdep⟩ := refined_support_of_dimension_ge_three
    hG.cliqueFree_five hz hg hd
  have hy : CliqueSupported G (mobius z) := (mobius_cliqueSupported_iff G z).mpr ⟨hz.1,hg⟩
  have hcl : ∀ C ∈ F,C.card = 4 ∧ G.IsClique C := by
    intro C hC
    obtain ⟨hc,hn⟩ := (mem_family _ C).mp hC
    refine ⟨hc,?_⟩
    by_contra hnot
    exact hn (coefficient_zero_of_not_clique hy C (by rintro ⟨_,hh⟩; exact hnot hh))
  have htree := hG.connected_family_threeTree F hne hcl hconn
  have hU : 4 ≤ U.card := htree.active_card_ge_four
  let H := actualDirectionGraph (basePolytope z)
  have hHU : H ≤ inducedOn G U := by
    intro u v huv
    have he : (edgeGraph (mobius z)).Adj u v := by simpa only [H,hactual] using huv
    obtain ⟨_,C,hC,hu,hv⟩ := he
    exact ⟨actualRootEdge_of_graphical hz.1.1 hz.2.1 hg huv,
      mem_biUnion.mpr ⟨C,hC,hu⟩,mem_biUnion.mpr ⟨C,hC,hv⟩⟩
  have hclH : ∀ C ∈ F,C.card = 4 ∧ H.IsClique C := by
    intro C hC
    refine ⟨(mem_family _ C).mp hC |>.1,?_⟩
    rw [show H = edgeGraph (mobius z) from hactual]
    exact family_subset_edgeGraph_clique hC
  have hHg := tetrahedralGrowth_of_connected_family H F hne hclH hconn
  have hiH : inducedOn H U = H := by
    ext u v
    constructor
    · exact fun h => h.1
    · intro h
      exact ⟨h,(hHU h).2⟩
  have hlow := hHg.edge_bound_and_equality.1
  change 3*U.card-6 ≤ (edgeFamily (inducedOn H U)).card at hlow
  rw [hiH] at hlow
  have heq : H = inducedOn G U := graph_eq_of_le_card_edges hHU
    (by rw [htree.edgeFamily_card]; exact hlow)
  have htreeH : ThreeTreeOn U (actualDirectionGraph (basePolytope z)) := by
    change ThreeTreeOn U H
    rw [heq]
    exact htree
  obtain ⟨hdim,hA⟩ := threeTree_actual_dimension_admissible hz htreeH
  exact ⟨U,hU,heq,htree,heq ▸ hA,hdim⟩

theorem TriangleApexSeparated.polytope_support {G : SimpleGraph V}
    (hG : TriangleApexSeparated G) {Q : Set (V → ℝ)} (hQ : IsFinitePolytope Q)
    (hi : MinkowskiIndecomposable Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope G))
    (hd : 3 ≤ Module.finrank ℝ (vectorSpan ℝ Q)) :
    ∃ U : Finset V,4 ≤ U.card ∧ actualDirectionGraph Q = inducedOn G U ∧
      ThreeTreeOn U (inducedOn G U) ∧ Admissible (inducedOn G U) ∧
      Module.finrank ℝ (vectorSpan ℝ Q) = U.card-1 := by
  obtain ⟨z,hz,he,hdim,hgraph⟩ := weak_summand_normalized_function hQ hi hw
  have hdz : 3 ≤ Module.finrank ℝ (vectorSpan ℝ (basePolytope z.1)) := by rwa [hdim] at hd
  have hext : ExtremeSupermodular z.1 := by
    rcases he with he | he
    · rw [he,basePolytope_zero,_root_.vectorSpan_singleton,finrank_bot] at hdz
      omega
    · exact he
  obtain ⟨U,hU,ha,ht,hA,hD⟩ := hG.extreme_support hext z.2.2 hdz
  exact ⟨U,hU,hgraph.trans ha,ht,hA,hdim.trans hD⟩

/-- The full-support criterion following from the geometric obstruction
and the actual triangle multiplicity bound. The drawing corollary supplies
both graph properties from ordinary plane planarity. -/
theorem TriangleApexSeparated.supports_full_iff_threeTree {G : SimpleGraph V}
    (hG : TriangleApexSeparated G) (hn : 4 ≤ Fintype.card V) (hA : Admissible G) :
    SupportsFullIndecomposable G ↔ IsThreeTree G := by
  constructor
  · rintro ⟨Q,hQ,hi,hd,hw⟩
    have hd3 : 3 ≤ Module.finrank ℝ (vectorSpan ℝ Q) := by
      change Module.finrank ℝ (vectorSpan ℝ Q) = Fintype.card V-1 at hd
      omega
    obtain ⟨U,hU,ha,ht,hUA,hD⟩ := hG.polytope_support hQ hi hw hd3
    have hcard : U.card = Fintype.card V := by
      change Module.finrank ℝ (vectorSpan ℝ Q) = Fintype.card V-1 at hd
      omega
    have hUniv : U = univ := eq_univ_of_card U hcard
    rw [hUniv,inducedOn_univ] at ht
    exact ht
  · intro ht
    obtain ⟨f,hf,hfi,hfd,hfa,hfg⟩ := admissible_threeTree_witness_fintype ht hA
    exact ⟨basePolytope f,(hfi.basePolytope hf.1.1 hf.2.1).finitePolytope,
      hf.minkowskiIndecomposable,hfd,
      (isWeakMinkowskiSummand_graphical_iff hf.1.1 hf.2.1).mpr hfg⟩

end GraphicalZonotopes

end
end
end BundlePart432

section BundlePart433
/- Source: Papers/GraphicalZonotopes/PlanarAnalyticSpectrum.lean -/





/-! # Dimension and lattice spectrum under the triangle-apex obstruction

These lemmas are the analytic part of the planar corollaries. Their graph
hypothesis is independently derived from a genuine noncrossing drawing in
the public planar statements. All intermediate dimensions are attained.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical BigOperators Pointwise
namespace GraphicalZonotopes
open Finset SetFunctionEmbedding
variable {V : Type*} [Fintype V] [LinearOrder V]

theorem IsAdmissibleCliqueCollection.induced_structure_of_apex_separated {G : SimpleGraph V}
    (hG : TriangleApexSeparated G) {F : Finset (Finset V)}
    (hF : IsAdmissibleCliqueCollection G F) :
    ThreeTreeOn (F.biUnion id) (inducedOn G (F.biUnion id)) ∧
      tetrahedra (inducedOn G (F.biUnion id)) = F ∧
      Admissible (inducedOn G (F.biUnion id)) ∧
      (F.biUnion id).card = F.card + 3 := by
  let U := F.biUnion id
  have ht := hG.connected_family_threeTree F hF.nonempty hF.four hF.connected
  have hsub : F ⊆ tetrahedra (inducedOn G U) := by
    intro C hC
    refine mem_filter.mpr ⟨mem_univ _,(hF.four C hC).1,?_⟩
    intro u hu v hv huv
    exact ⟨(hF.four C hC).2 hu hv huv,
      mem_biUnion.mpr ⟨C,hC,hu⟩,mem_biUnion.mpr ⟨C,hC,hv⟩⟩
  have hu := connected_tetrahedra_union_card F hF.nonempty
    (fun C hC => (hF.four C hC).1) hF.connected
  have hfour : 4 ≤ U.card := ht.active_card_ge_four
  have hcard : (tetrahedra (inducedOn G U)).card = U.card - 3 := ht.tetrahedra_card
  have he : tetrahedra (inducedOn G U) = F := by
    apply (eq_of_subset_of_card_le hsub ?_).symm
    rw [hcard]
    change U.card ≤ F.card + 3 at hu
    omega
  refine ⟨ht,he,?_,?_⟩
  · intro T hT hc
    change ((tetrahedra (inducedOn G U)).filter (fun C => T ⊆ C)).card ≤ 3
    rw [he]
    exact hF.thin T hT
  · rw [he] at hcard
    change U.card = F.card + 3
    omega

theorem TriangleApexSeparated.dimension_le_clique_count {G : SimpleGraph V}
    (hG : TriangleApexSeparated G) {Q : Set (V → ℝ)} (hQ : IsFinitePolytope Q)
    (hi : MinkowskiIndecomposable Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope G)) :
    Module.finrank ℝ (vectorSpan ℝ Q) ≤ maximumAdmissibleCliqueCount G+2 := by
  by_cases hd : 3 ≤ Module.finrank ℝ (vectorSpan ℝ Q)
  · obtain ⟨U,hU,ha,ht,hA,hD⟩ := TriangleApexSeparated.polytope_support hG hQ hi hw hd
    have hF := ht.admissibleCliqueCollection hA (inducedOn_le G U)
    have hb := admissibleClique_count_le_maximum hF
    rw [ht.tetrahedra_card] at hb
    omega
  · omega

/-- The maximum admissible clique collection gives an actual lattice witness
for the supremum defining the dimension invariant. -/
theorem TriangleApexSeparated.maximum_witness {G : SimpleGraph V}
    (hG : TriangleApexSeparated G) (hK : (tetrahedra G).Nonempty) :
    ∃ Q : Set (V → ℝ), LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
      Module.finrank ℝ (vectorSpan ℝ Q) = maximumAdmissibleCliqueCount G+2 := by
  obtain ⟨F,hF,hmax⟩ := maximumAdmissibleCliqueCount_attained hK
  obtain ⟨ht,he,hA,hcard⟩ := hF.induced_structure_of_apex_separated hG
  obtain ⟨Q,hQ,hi,hw,ha,hd⟩ := induced_admissible_threeTree_witness ht hA
  exact ⟨Q,hQ,hi,hw,by omega⟩

theorem TriangleApexSeparated.maximum_dimension {G : SimpleGraph V}
    (hG : TriangleApexSeparated G) (hK : (tetrahedra G).Nonempty) :
    maximumIndecomposableDimension G = maximumAdmissibleCliqueCount G+2 := by
  apply le_antisymm
  · apply csSup_le'
    rintro d ⟨Q,hQ,hi,hw,hd⟩
    rw [← hd]
    exact TriangleApexSeparated.dimension_le_clique_count hG hQ hi hw
  · obtain ⟨Q,hQ,hi,hw,hd⟩ := TriangleApexSeparated.maximum_witness hG hK
    rw [← hd]
    exact dimension_le_maximum hQ.finitePolytope hi hw

/-- Every positive integer through the sharp maximum occurs, with no gap and
with a lattice representative. The construction uses an arbitrary prefix of
a maximizing admissible three-tree and actual clique simplices at dimensions
one and two. -/
theorem TriangleApexSeparated.dimension_spectrum {G : SimpleGraph V}
    (hG : TriangleApexSeparated G) (hK : (tetrahedra G).Nonempty)
    (d : ℕ) (hd : 1 ≤ d) (hdM : d ≤ maximumAdmissibleCliqueCount G+2) :
    ∃ Q : Set (V → ℝ), LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
      Module.finrank ℝ (vectorSpan ℝ Q) = d := by
  by_cases hd3 : 3 ≤ d
  · obtain ⟨F,hF,hmax⟩ := maximumAdmissibleCliqueCount_attained hK
    obtain ⟨ht,he,hA,hcard⟩ := hF.induced_structure_of_apex_separated hG
    obtain ⟨U,H,hU,hcardU,hH,htH⟩ := ht.prefix (m := d+1) (by omega) (by omega)
    have hHA : Admissible H := hA.mono hH
    obtain ⟨f,hf,hfi,hfd,hfa,hfg⟩ := admissible_threeTree_active_witness htH hHA
    refine ⟨basePolytope f,hfi.basePolytope hf.1.1 hf.2.1,hf.minkowskiIndecomposable,?_,?_⟩
    · exact (isWeakMinkowskiSummand_graphical_iff hf.1.1 hf.2.1).mpr
        (hfg.mono_graph (hH.trans (inducedOn_le G _)))
    · omega
  · obtain ⟨C,hC⟩ := hK
    obtain ⟨hfour,hcl⟩ := (mem_filter.mp hC).2
    obtain ⟨D,hDC,hD⟩ := exists_subset_card_eq (s := C) (n := d+1) (by omega)
    obtain ⟨Q,hQ,hi,hw,hqdim⟩ := clique_simplex_witness
      (by omega : 2 ≤ D.card) (fun u hu v hv huv => hcl (hDC hu) (hDC hv) huv)
    exact ⟨Q,hQ,hi,hw,by omega⟩

theorem TriangleApexSeparated.no_tetrahedron_dimension_le_two {G : SimpleGraph V}
    (hG : TriangleApexSeparated G) (hK : tetrahedra G = ∅)
    {Q : Set (V → ℝ)} (hQ : IsFinitePolytope Q) (hi : MinkowskiIndecomposable Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope G)) :
    Module.finrank ℝ (vectorSpan ℝ Q) ≤ 2 := by
  by_contra hd
  have hd3 : 3 ≤ Module.finrank ℝ (vectorSpan ℝ Q) := by omega
  obtain ⟨U,hU,ha,ht,hA,hD⟩ := TriangleApexSeparated.polytope_support hG hQ hi hw hd3
  obtain ⟨C,hC⟩ := ht.tetrahedra_nonempty
  have hc := tetrahedra_mono (inducedOn_le G U) hC
  rw [hK] at hc
  exact notMem_empty C hc

theorem TriangleApexSeparated.triangle_maximum {G : SimpleGraph V}
    (hG : TriangleApexSeparated G) (hK : tetrahedra G = ∅)
    (hT : ∃ T : Finset V,T.card = 3 ∧ G.IsClique T) :
    maximumIndecomposableDimension G = 2 := by
  apply le_antisymm
  · apply csSup_le'
    rintro d ⟨Q,hQ,hi,hw,hd⟩
    rw [← hd]
    exact TriangleApexSeparated.no_tetrahedron_dimension_le_two hG hK hQ hi hw
  · obtain ⟨T,hT,hcl⟩ := hT
    obtain ⟨Q,hQ,hi,hw,hd⟩ := clique_simplex_witness (by omega) hcl
    have hb := dimension_le_maximum hQ.finitePolytope hi hw
    rw [hd,hT] at hb
    exact hb

theorem TriangleApexSeparated.piecewise_maximum {G : SimpleGraph V}
    (hG : TriangleApexSeparated G) :
    maximumIndecomposableDimension G = partialThreeTreeDimension G := by
  unfold partialThreeTreeDimension
  by_cases hK : (tetrahedra G).Nonempty
  · rw [if_pos hK]
    exact TriangleApexSeparated.maximum_dimension hG hK
  · rw [if_neg hK]
    have hKe : tetrahedra G = ∅ := not_nonempty_iff_eq_empty.mp hK
    by_cases hT : ∃ T : Finset V,T.card = 3 ∧ G.IsClique T
    · rw [if_pos hT]
      exact TriangleApexSeparated.triangle_maximum hG hKe hT
    · rw [if_neg hT]
      have hcf : G.CliqueFree 3 := fun T h => hT ⟨T,h.card_eq,h.isClique⟩
      by_cases hE : ∃ u v : V,G.Adj u v
      · rw [if_pos hE]
        exact triangleFree_maximum_dimension hcf hE
      · rw [if_neg hE]
        exact edgeless_maximum_dimension (fun u v huv => hE ⟨u,v,huv⟩)

/-- The full positive spectrum, including graphs with no tetrahedron. -/
theorem TriangleApexSeparated.full_dimension_spectrum {G : SimpleGraph V}
    (hG : TriangleApexSeparated G) (d : ℕ) (hd : 1 ≤ d)
    (hmax : d ≤ maximumIndecomposableDimension G) :
    ∃ Q : Set (V → ℝ),LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
      Module.finrank ℝ (vectorSpan ℝ Q) = d := by
  by_cases hK : (tetrahedra G).Nonempty
  · apply TriangleApexSeparated.dimension_spectrum hG hK d hd
    rwa [TriangleApexSeparated.maximum_dimension hG hK] at hmax
  · have hKe : tetrahedra G = ∅ := not_nonempty_iff_eq_empty.mp hK
    by_cases hT : ∃ T : Finset V,T.card = 3 ∧ G.IsClique T
    · rw [TriangleApexSeparated.triangle_maximum hG hKe hT] at hmax
      obtain ⟨T,hT,hcl⟩ := hT
      obtain ⟨C,hCT,hC⟩ := exists_subset_card_eq (s := T) (n := d+1) (by omega)
      obtain ⟨Q,hQ,hi,hw,hqdim⟩ := clique_simplex_witness (by omega : 2 ≤ C.card)
        (fun u hu v hv huv => hcl (hCT hu) (hCT hv) huv)
      exact ⟨Q,hQ,hi,hw,by omega⟩
    · have hcf : G.CliqueFree 3 := fun T h => hT ⟨T,h.card_eq,h.isClique⟩
      by_cases hE : ∃ u v : V,G.Adj u v
      · rw [triangleFree_maximum_dimension hcf hE] at hmax
        have hd1 : d = 1 := by omega
        obtain ⟨u,v,huv⟩ := hE
        have hcl : G.IsClique ({u,v} : Finset V) := by
          intro a ha b hb hab
          change a ∈ ({u,v} : Finset V) at ha
          change b ∈ ({u,v} : Finset V) at hb
          simp only [mem_insert,mem_singleton] at ha hb
          rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
          · exact False.elim (hab rfl)
          · exact huv
          · exact huv.symm
          · exact False.elim (hab rfl)
        obtain ⟨Q,hQ,hi,hw,hqdim⟩ := clique_simplex_witness
          (by rw [card_pair huv.ne]) hcl
        refine ⟨Q,hQ,hi,hw,?_⟩
        simpa only [card_pair huv.ne,hd1] using hqdim
      · have hdim := edgeless_maximum_dimension (fun u v huv => hE ⟨u,v,huv⟩)
        omega

end GraphicalZonotopes

end
end
end BundlePart433

section BundlePart434
/- Source: Papers/GraphicalZonotopes/PlanarComponentDimension.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [LinearOrder V]

namespace TetrahedronComponents

/-- The actual connected components of the graph of all tetrahedra, with
adjacency given by sharing a triangle. -/
abbrev Component (G : SimpleGraph V) :=
  (tetrahedronGraph (tetrahedra G)).ConnectedComponent

def family (G : SimpleGraph V) (c : Component G) : Finset (Finset V) :=
  (tetrahedra G).filter (fun C => ∃ hC : C ∈ tetrahedra G,
    (tetrahedronGraph (tetrahedra G)).connectedComponentMk ⟨C,hC⟩ = c)

@[simp] theorem mem_family (G : SimpleGraph V) (c : Component G) (C : Finset V) :
    C ∈ family G c ↔ ∃ hC : C ∈ tetrahedra G,
      (tetrahedronGraph (tetrahedra G)).connectedComponentMk ⟨C,hC⟩ = c := by
  simp only [family,mem_filter]
  exact ⟨fun h => h.2,fun ⟨hC,h⟩ => ⟨hC,hC,h⟩⟩

theorem family_subset (G : SimpleGraph V) (c : Component G) :
    family G c ⊆ tetrahedra G := filter_subset _ _

theorem family_nonempty (G : SimpleGraph V) (c : Component G) : (family G c).Nonempty := by
  obtain ⟨C,hC⟩ := c.exists_rep
  exact ⟨C.1,(mem_family G c C.1).mpr ⟨C.2,hC⟩⟩

theorem family_connected (G : SimpleGraph V) (c : Component G) :
    (tetrahedronGraph (family G c)).Preconnected := by
  let f : c.toSimpleGraph →g tetrahedronGraph (family G c) :=
    { toFun := fun C => ⟨C.1.1,(mem_family G c C.1.1).mpr ⟨C.1.2,C.2⟩⟩
      map_rel' := by
        intro C D hCD
        change (tetrahedronGraph (tetrahedra G)).Adj C.1 D.1 at hCD
        refine ⟨?_,hCD.2⟩
        intro he
        have heval : C.1.1 = D.1.1 := congrArg
          (fun E : {E : Finset V // E ∈ family G c} => E.1) he
        exact hCD.1 (Subtype.ext heval) }
  intro A B
  obtain ⟨hA,hAc⟩ := (mem_family G c A.1).mp A.2
  obtain ⟨hB,hBc⟩ := (mem_family G c B.1).mp B.2
  exact ((c.connected_toSimpleGraph).preconnected
    ⟨⟨A.1,hA⟩,hAc⟩ ⟨⟨B.1,hB⟩,hBc⟩).map f

/-- Every nonempty connected collection is contained in one actual component
of the graph of all tetrahedra, rather than an arbitrary chosen enlargement. -/
theorem connected_family_subset_component (G : SimpleGraph V) (F : Finset (Finset V))
    (hne : F.Nonempty) (hsub : F ⊆ tetrahedra G)
    (hconn : (tetrahedronGraph F).Preconnected) :
    ∃ c : Component G,F ⊆ family G c := by
  obtain ⟨A,hA⟩ := hne
  let f : tetrahedronGraph F →g tetrahedronGraph (tetrahedra G) :=
    { toFun := fun C => ⟨C.1,hsub C.2⟩
      map_rel' := by
        intro C D hCD
        refine ⟨?_,hCD.2⟩
        intro he
        have heval : C.1 = D.1 := congrArg
          (fun E : {E : Finset V // E ∈ tetrahedra G} => E.1) he
        exact hCD.1 (Subtype.ext heval) }
  let c : Component G := (tetrahedronGraph (tetrahedra G)).connectedComponentMk ⟨A,hsub hA⟩
  refine ⟨c,?_⟩
  intro C hC
  apply (mem_family G c C).mpr
  refine ⟨hsub hC,?_⟩
  exact SimpleGraph.ConnectedComponent.sound ((hconn ⟨C,hC⟩ ⟨A,hA⟩).map f)

theorem family_admissible {G : SimpleGraph V} (hA : Admissible G) (c : Component G) :
    IsAdmissibleCliqueCollection G (family G c) := by
  refine ⟨family_nonempty G c,family_subset G c,family_connected G c,?_⟩
  intro T hT
  by_cases hcT : G.IsClique T
  · exact (card_le_card (filter_subset_filter _ (family_subset G c))).trans (hA T hT hcT)
  · have hempty : (family G c).filter (fun C => T ⊆ C) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro C hC
      obtain ⟨hCF,hTC⟩ := mem_filter.mp hC
      have hcl := (mem_filter.mp (family_subset G c hCF)).2.2
      exact hcT (fun u hu v hv huv => hcl (hTC hu) (hTC hv) huv)
    rw [hempty,card_empty]
    omega

/-- The exact vertex set denoted V(C) in Corollary 6.5. -/
def vertices (G : SimpleGraph V) (c : Component G) : Finset V := (family G c).biUnion id

theorem vertices_card {G : SimpleGraph V} (hG : TriangleApexSeparated G)
    (hA : Admissible G) (c : Component G) :
    (vertices G c).card = (family G c).card + 3 :=
  ((family_admissible hA c).induced_structure_of_apex_separated hG).2.2.2

/-- Maximum of |V(C)|−1 over the actual triangle-adjacency components of
all four-cliques. The empty maximum is zero. -/
def maximumDimension (G : SimpleGraph V) : ℕ :=
  (univ : Finset (Component G)).sup (fun c => (vertices G c).card - 1)

/-- The component formula in the planar corollary is exactly equal to the
admissible-collection formula, with equivalence proved rather than stipulated. -/
theorem maximumDimension_eq {G : SimpleGraph V} (hG : TriangleApexSeparated G)
    (hA : Admissible G) (hK : (tetrahedra G).Nonempty) :
    maximumDimension G = maximumAdmissibleCliqueCount G + 2 := by
  apply le_antisymm
  · apply Finset.sup_le_iff.mpr
    intro c _
    have hc := vertices_card hG hA c
    have hm := admissibleClique_count_le_maximum (family_admissible hA c)
    omega
  · obtain ⟨F,hF,hmax⟩ := maximumAdmissibleCliqueCount_attained hK
    obtain ⟨c,hFc⟩ := connected_family_subset_component G F hF.nonempty hF.included hF.connected
    have hcard := card_le_card hFc
    have hc := vertices_card hG hA c
    have hm : (vertices G c).card - 1 ≤ maximumDimension G := by
      unfold maximumDimension
      exact Finset.le_sup (f := fun c : Component G => (vertices G c).card - 1) (mem_univ c)
    omega

end TetrahedronComponents

/-- The literal piecewise formula of Corollary 6.5, using actual connected
components of the tetrahedron graph, followed by triangles, edges, and zero. -/
def planarComponentDimension (G : SimpleGraph V) : ℕ :=
  if (tetrahedra G).Nonempty then TetrahedronComponents.maximumDimension G
  else if ∃ T : Finset V,T.card = 3 ∧ G.IsClique T then 2
  else if ∃ u v : V,G.Adj u v then 1 else 0

theorem planarComponentDimension_eq_partialThreeTreeDimension {G : SimpleGraph V}
    (hG : TriangleApexSeparated G) (hA : Admissible G) :
    planarComponentDimension G = partialThreeTreeDimension G := by
  unfold planarComponentDimension partialThreeTreeDimension
  split_ifs with hK hT hE
  · exact TetrahedronComponents.maximumDimension_eq hG hA hK
  all_goals rfl

end GraphicalZonotopes

end
end
end BundlePart434

section BundlePart435
/- Source: Papers/GraphicalZonotopes/StackedTriangulation.lean -/






/-! # The boundary-face dictionary for stacked triangulations

The face set is part of the construction. Starting with the four faces of a
tetrahedron, a stacking step removes one available face and inserts its three
cones over the face's edges. The dictionary identifies those actual boundary
faces with triangles contained in exactly one construction tetrahedron.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

def boundaryTriangles (G : SimpleGraph V) : Finset (Finset V) :=
  (triangles G).filter (fun T => triangleMultiplicity G T = 1)

@[simp] theorem mem_boundaryTriangles {G : SimpleGraph V} {T : Finset V} :
    T ∈ boundaryTriangles G ↔ T.card = 3 ∧ G.IsClique T ∧ triangleMultiplicity G T = 1 := by
  simp only [boundaryTriangles,mem_filter,mem_triangles,and_assoc]

theorem triangleMultiplicity_cliqueGraph_of_subset {C T : Finset V}
    (hC : C.card = 4) (hTC : T ⊆ C) : triangleMultiplicity (cliqueGraph C) T = 1 := by
  rw [triangleMultiplicity,tetrahedra_cliqueGraph hC,filter_singleton,if_pos hTC,card_singleton]

theorem boundaryTriangles_cliqueGraph {C : Finset V} (hC : C.card = 4) :
    boundaryTriangles (cliqueGraph C) = C.powersetCard 3 := by
  ext T
  rw [boundaryTriangles,mem_filter,triangles_cliqueGraph hC]
  exact ⟨fun h => h.1,fun h => ⟨h,
    triangleMultiplicity_cliqueGraph_of_subset hC (mem_powersetCard.mp h).1⟩⟩

private theorem old_triangle_subset_attach_iff {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {u : V} (hu : u ∉ S) {A T : Finset V}
    (hA : A.card = 3) (hT : T.card = 3) (hcT : G.IsClique T) :
    T ⊆ insert u A ↔ T = A := by
  constructor
  · intro hsub
    have huT : u ∉ T := fun hm => hu (h.clique_subset_active (by omega) hcT hm)
    apply eq_of_subset_of_card_le
    · intro t ht
      exact (mem_insert.mp (hsub ht)).resolve_left (fun he => huT (he ▸ ht))
    · omega
  · rintro rfl
    exact subset_insert _ _

/-- The boundary update is exactly the usual one-to-three subdivision of a
triangular face. It is proved from actual clique incidences. -/
theorem boundaryTriangles_after_attachment {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {u : V} (hu : u ∉ S) {A : Finset V}
    (hA : A.card = 3) (hAS : A ⊆ S) (hcA : G.IsClique A)
    (hbA : triangleMultiplicity G A = 1) :
    boundaryTriangles (G ⊔ attachmentStar u A) =
      (boundaryTriangles G).erase A ∪ (A.powersetCard 2).image (insert u) := by
  ext T
  constructor
  · intro hT
    obtain ⟨hTc,hTcl,hTm⟩ := mem_boundaryTriangles.mp hT
    by_cases huT : u ∈ T
    · apply mem_union_right
      have ht : T ∈ triangles (G ⊔ attachmentStar u A) := mem_triangles.mpr ⟨hTc,hTcl⟩
      rw [triangles_after_attachment h hu hA hAS hcA] at ht
      refine (mem_union.mp ht).resolve_left ?_
      intro htold
      exact hu (h.clique_subset_active (by omega) (mem_triangles.mp htold).2 huT)
    · have hcOld : G.IsClique T := clique_before_attachment huT hTcl
      have hTA : T ≠ A := by
        rintro rfl
        rw [triangleMultiplicity_after_attachment h hu hA hAS hcA,
          hbA,if_pos (subset_insert _ _)] at hTm
        omega
      have hnot : ¬ T ⊆ insert u A := fun hh => hTA
        ((old_triangle_subset_attach_iff h hu hA hTc hcOld).mp hh)
      rw [triangleMultiplicity_after_attachment h hu hA hAS hcA,if_neg hnot,Nat.add_zero] at hTm
      exact mem_union_left _ (mem_erase.mpr ⟨hTA,mem_boundaryTriangles.mpr ⟨hTc,hcOld,hTm⟩⟩)
  · intro hT
    rcases mem_union.mp hT with hT | hT
    · obtain ⟨hTA,hT⟩ := mem_erase.mp hT
      obtain ⟨hTc,hTcl,hTm⟩ := mem_boundaryTriangles.mp hT
      have hnot : ¬ T ⊆ insert u A := fun hh => hTA
        ((old_triangle_subset_attach_iff h hu hA hTc hTcl).mp hh)
      apply mem_boundaryTriangles.mpr
      refine ⟨hTc,fun a ha b hb hab => Or.inl (hTcl ha hb hab),?_⟩
      rw [triangleMultiplicity_after_attachment h hu hA hAS hcA,if_neg hnot,Nat.add_zero,hTm]
    · obtain ⟨E,hE,rfl⟩ := mem_image.mp hT
      obtain ⟨hEA,hEc⟩ := mem_powersetCard.mp hE
      have huE : u ∉ E := fun hh => hu (hAS (hEA hh))
      have htri : insert u E ∈ triangles (G ⊔ attachmentStar u A) := by
        rw [triangles_after_attachment h hu hA hAS hcA]
        exact mem_union_right _ (mem_image.mpr ⟨E,mem_powersetCard.mpr ⟨hEA,hEc⟩,rfl⟩)
      apply mem_boundaryTriangles.mpr
      refine ⟨(mem_triangles.mp htri).1,(mem_triangles.mp htri).2,?_⟩
      rw [triangleMultiplicity_after_attachment h hu hA hAS hcA,
        h.triangleMultiplicity_eq_zero_of_outside hu (mem_insert_self _ _),
        if_pos (insert_subset_insert u hEA)]

private theorem thin_after_boundary_attachment {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {u : V} (hu : u ∉ S) {A : Finset V}
    (hA : A.card = 3) (hAS : A ⊆ S) (hcA : G.IsClique A)
    (hbA : triangleMultiplicity G A = 1)
    (hthin : ∀ T : Finset V,T.card = 3 → G.IsClique T → triangleMultiplicity G T ≤ 2) :
    ∀ T : Finset V,T.card = 3 → (G ⊔ attachmentStar u A).IsClique T →
      triangleMultiplicity (G ⊔ attachmentStar u A) T ≤ 2 := by
  intro T hT hcT
  rw [triangleMultiplicity_after_attachment h hu hA hAS hcA]
  by_cases huT : u ∈ T
  · rw [h.triangleMultiplicity_eq_zero_of_outside hu huT]
    split_ifs <;> omega
  · have hcOld : G.IsClique T := clique_before_attachment huT hcT
    by_cases hTA : T = A
    · subst T
      rw [hbA]
      split_ifs <;> omega
    · have hnot : ¬ T ⊆ insert u A := fun hh => hTA
        ((old_triangle_subset_attach_iff h hu hA hT hcOld).mp hh)
      rw [if_neg hnot,Nat.add_zero]
      exact hthin T hT hcOld

/-- The ordinary combinatorial definition of a stacked boundary
triangulation, including its explicit evolving triangular face set. -/
inductive StackedTriangulationOn : Finset V → SimpleGraph V → Finset (Finset V) → Prop
  | tetrahedron (C : Finset V) (hC : C.card = 4) :
      StackedTriangulationOn C (cliqueGraph C) (C.powersetCard 3)
  | stack {S : Finset V} {G : SimpleGraph V} {F : Finset (Finset V)}
      (h : StackedTriangulationOn S G F) (u : V) (hu : u ∉ S)
      (T : Finset V) (hT : T.card = 3) (hTS : T ⊆ S) (hcT : G.IsClique T)
      (hface : T ∈ F) :
      StackedTriangulationOn (insert u S) (G ⊔ attachmentStar u T)
        (F.erase T ∪ (T.powersetCard 2).image (insert u))

theorem StackedTriangulationOn.properties {S : Finset V} {G : SimpleGraph V}
    {F : Finset (Finset V)} (h : StackedTriangulationOn S G F) :
    ThreeTreeOn S G ∧
      (∀ T : Finset V,T.card = 3 → G.IsClique T → triangleMultiplicity G T ≤ 2) ∧
      F = boundaryTriangles G := by
  induction h with
  | tetrahedron C hC =>
    refine ⟨ThreeTreeOn.tetrahedron C hC,?_,(boundaryTriangles_cliqueGraph hC).symm⟩
    intro T hT hcT
    rw [triangleMultiplicity_cliqueGraph_of_subset hC
      ((ThreeTreeOn.tetrahedron C hC).clique_subset_active (by omega) hcT)]
    omega
  | @stack S G F h u hu T hT hTS hcT hface ih =>
    obtain ⟨ht,hthin,hF⟩ := ih
    have hb : triangleMultiplicity G T = 1 :=
      (mem_boundaryTriangles.mp (hF ▸ hface)).2.2
    refine ⟨ThreeTreeOn.attach ht u hu T hT hTS hcT,
      thin_after_boundary_attachment ht hu hT hTS hcT hb hthin,?_⟩
    rw [hF,boundaryTriangles_after_attachment ht hu hT hTS hcT hb]

theorem ThreeTreeOn.stacked {S : Finset V} {G : SimpleGraph V} (h : ThreeTreeOn S G) :
    (∀ T : Finset V,T.card = 3 → G.IsClique T → triangleMultiplicity G T ≤ 2) →
      StackedTriangulationOn S G (boundaryTriangles G) := by
  induction h with
  | tetrahedron C hC =>
    intro _
    rw [boundaryTriangles_cliqueGraph hC]
    exact StackedTriangulationOn.tetrahedron C hC
  | @attach S G h u hu T hT hTS hcT ih =>
    intro hthin
    have hOld : ∀ A : Finset V,A.card = 3 → G.IsClique A → triangleMultiplicity G A ≤ 2 := by
      intro A hA hcA
      exact (triangleMultiplicity_mono (show G ≤ G ⊔ attachmentStar u T from le_sup_left) A).trans
        (hthin A hA (fun a ha b hb hab => Or.inl (hcA ha hb hab)))
    have hb : triangleMultiplicity G T = 1 := by
      obtain ⟨C,hC,hTC⟩ := h.triangle_extends hT hcT
      have hpos : 0 < triangleMultiplicity G T :=
        card_pos.mpr ⟨C,mem_filter.mpr ⟨hC,hTC⟩⟩
      have hnew := hthin T hT (fun a ha b hb hab => Or.inl (hcT ha hb hab))
      rw [triangleMultiplicity_after_attachment h hu hT hTS hcT,
        if_pos (subset_insert _ _)] at hnew
      omega
    rw [boundaryTriangles_after_attachment h hu hT hTS hcT hb]
    exact StackedTriangulationOn.stack (ih hOld) u hu T hT hTS hcT
      (mem_boundaryTriangles.mpr ⟨hT,hcT,hb⟩)

def IsStackedTriangulation (G : SimpleGraph V) : Prop :=
  ∃ F : Finset (Finset V),StackedTriangulationOn univ G F

/-- Equivalence with the usual three-tree formulation, with the exact
boundary face set recovered as a theorem. -/
theorem isStackedTriangulation_iff {G : SimpleGraph V} :
    IsStackedTriangulation G ↔ IsThreeTree G ∧
      (∀ T : Finset V,T.card = 3 → G.IsClique T → triangleMultiplicity G T ≤ 2) := by
  constructor
  · rintro ⟨F,hF⟩
    exact ⟨hF.properties.1,hF.properties.2.1⟩
  · rintro ⟨ht,hthin⟩
    exact ⟨boundaryTriangles G,ht.stacked hthin⟩

end GraphicalZonotopes

end
end
end BundlePart435

section BundlePart436
/- Source: Papers/GraphicalZonotopes/PlanarPaperStatements.lean -/









/-! # The planar classification and complete dimension spectrum

Planarity means an injective placement in the Euclidean plane with arbitrary
simple continuous edge arcs meeting only at shared endpoints. The geometric
obstructions are proved from that definition. No Euler inequality, forbidden
minor characterization, or straight-line realization is a premise here.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical Pointwise
namespace GraphicalZonotopes
variable {V : Type*} [Fintype V] [LinearOrder V]

/-- On distinct actual four-cliques, the formal overlap threshold is
exactly the paper's adjacency relation of sharing a triangle. -/
theorem TetrahedronComponents.adj_iff_shared_triangle (G : SimpleGraph V)
    (C D : {C : Finset V // C ∈ tetrahedra G}) :
    (tetrahedronGraph (tetrahedra G)).Adj C D ↔ (C.1 ∩ D.1).card = 3 := by
  have hC : C.1.card = 4 := (Finset.mem_filter.mp C.2).2.1
  have hD : D.1.card = 4 := (Finset.mem_filter.mp D.2).2.1
  constructor
  · intro h
    have hle := Finset.card_le_card (Finset.inter_subset_left : C.1 ∩ D.1 ⊆ C.1)
    have hne : (C.1 ∩ D.1).card ≠ 4 := by
      intro he
      have hleft : C.1 ∩ D.1 = C.1 := Finset.eq_of_subset_of_card_le
        Finset.inter_subset_left (by omega)
      have hright : C.1 ∩ D.1 = D.1 := Finset.eq_of_subset_of_card_le
        Finset.inter_subset_right (by omega)
      exact h.1 (Subtype.ext (hleft.symm.trans hright))
    have hlo := h.2
    omega
  · intro h
    refine ⟨?_,by omega⟩
    intro he
    have hv := congrArg Subtype.val he
    rw [hv,Finset.inter_self,hD] at h
    omega

theorem HasPlaneDrawing.maximum_dimension {G : SimpleGraph V}
    (hG : HasPlaneDrawing G) :
    maximumIndecomposableDimension G = planarComponentDimension G := by
  have hs := hG.triangle_apex_separated
  exact hs.piecewise_maximum.trans
    (planarComponentDimension_eq_partialThreeTreeDimension hs hG.admissible).symm

theorem HasPlaneDrawing.full_polytopal_iff_threeTree {G : SimpleGraph V}
    (hG : HasPlaneDrawing G) (hn : 4 ≤ Fintype.card V) :
    (∃ Q : Set (V → ℝ),IsFinitePolytope Q ∧
      PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G)) ↔ IsThreeTree G := by
  rw [← supportsFullIndecomposable_iff_polytopal_weak]
  exact hG.triangle_apex_separated.supports_full_iff_threeTree hn hG.admissible

theorem HasPlaneDrawing.isStackedTriangulation_iff_threeTree {G : SimpleGraph V}
    (hG : HasPlaneDrawing G) : IsStackedTriangulation G ↔ IsThreeTree G := by
  rw [isStackedTriangulation_iff]
  exact ⟨fun h => h.1,fun h => ⟨h,hG.triangleMultiplicity_le_two⟩⟩

theorem HasPlaneDrawing.lattice_full_witness {G : SimpleGraph V}
    (hG : HasPlaneDrawing G) (ht : IsThreeTree G) :
    ∃ Q : Set (V → ℝ),LatticePolytope Q ∧
      PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧ actualDirectionGraph Q = G := by
  obtain ⟨f,hf,hfi,hfd,hfa,hfg⟩ := admissible_threeTree_witness_fintype ht hG.admissible
  have hQ := hfi.basePolytope hf.1.1 hf.2.1
  have hw := (isWeakMinkowskiSummand_graphical_iff hf.1.1 hf.2.1).mpr hfg
  exact ⟨basePolytope f,hQ,
    (weakSummand_indecomposable_iff_polytopal hQ.finitePolytope hw).mp
      hf.minkowskiIndecomposable,hfd,hw,hfa⟩

theorem HasPlaneDrawing.full_lattice_spectrum {G : SimpleGraph V}
    (hG : HasPlaneDrawing G) (d : ℕ) (hd : 1 ≤ d)
    (hmax : d ≤ planarComponentDimension G) :
    ∃ Q : Set (V → ℝ),LatticePolytope Q ∧
      PolytopalMinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
      Module.finrank ℝ (vectorSpan ℝ Q) = d := by
  obtain ⟨Q,hQ,hi,hw,hD⟩ := hG.triangle_apex_separated.full_dimension_spectrum
    d hd (by rwa [hG.maximum_dimension])
  exact ⟨Q,hQ,(weakSummand_indecomposable_iff_polytopal hQ.finitePolytope hw).mp hi,hw,hD⟩

/-- Corollary 6.4 for every finite simple planar graph on at least four
vertices. The chosen vertex order is internal coordinate infrastructure,
not an additional assumption on the graph or its drawing. -/
theorem paper_corollary_6_4 {W : Type*} [Fintype W] :
    letI : LinearOrder W := Separator.finiteVertexOrder W;
    ∀ G : SimpleGraph W,HasPlaneDrawing G → 4 ≤ Fintype.card W →
      ((∃ Q : Set (W → ℝ),IsFinitePolytope Q ∧
        PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
        IsWeakMinkowskiSummand Q (graphicalZonotope G)) ↔ IsThreeTree G) := by
  letI : LinearOrder W := Separator.finiteVertexOrder W
  exact fun G hG hn => hG.full_polytopal_iff_threeTree hn

/-- The same classification with the paper's explicit stacked-triangulation
formulation: tetrahedral boundary faces are built by repeated one-to-three
face replacements, as certified by the independent boundary dictionary. -/
theorem paper_corollary_6_4_stacked {W : Type*} [Fintype W] :
    letI : LinearOrder W := Separator.finiteVertexOrder W;
    ∀ G : SimpleGraph W,HasPlaneDrawing G → 4 ≤ Fintype.card W →
      ((∃ Q : Set (W → ℝ),IsFinitePolytope Q ∧
        PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
        IsWeakMinkowskiSummand Q (graphicalZonotope G)) ↔ IsStackedTriangulation G) := by
  letI : LinearOrder W := Separator.finiteVertexOrder W
  intro G hG hn
  exact (hG.full_polytopal_iff_threeTree hn).trans hG.isStackedTriangulation_iff_threeTree.symm

/-- The lattice witness in the converse of the planar classification has
exactly the original graph as its actual exposed-edge direction graph. -/
theorem planar_threeTree_lattice_witness_finite {W : Type*} [Fintype W] :
    letI : LinearOrder W := Separator.finiteVertexOrder W;
    ∀ G : SimpleGraph W,HasPlaneDrawing G → IsThreeTree G →
      ∃ Q : Set (W → ℝ),LatticePolytope Q ∧
        PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
        IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧ actualDirectionGraph Q = G := by
  letI : LinearOrder W := Separator.finiteVertexOrder W
  exact fun G hG ht => hG.lattice_full_witness ht

/-- Corollary 6.5 with the literal maximum over the connected components of
the graph of all tetrahedra, and every positive dimension through that maximum.
The fallback values are exactly two for triangles, one for edges, and zero
for edgeless graphs. Both the supremum and witnesses use ordinary polytopal
Minkowski indecomposability. -/
theorem paper_corollary_6_5 {W : Type*} [Fintype W] :
    letI : LinearOrder W := Separator.finiteVertexOrder W;
    ∀ G : SimpleGraph W,HasPlaneDrawing G →
      (sSup {d : ℕ | ∃ Q : Set (W → ℝ),IsFinitePolytope Q ∧
        PolytopalMinkowskiIndecomposable Q ∧
        IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
        Module.finrank ℝ (vectorSpan ℝ Q) = d}) = planarComponentDimension G ∧
      ∀ d : ℕ,1 ≤ d → d ≤ planarComponentDimension G →
        ∃ Q : Set (W → ℝ),LatticePolytope Q ∧
          PolytopalMinkowskiIndecomposable Q ∧
          IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
          Module.finrank ℝ (vectorSpan ℝ Q) = d := by
  letI : LinearOrder W := Separator.finiteVertexOrder W
  intro G hG
  refine ⟨?_,fun d hd hm => hG.full_lattice_spectrum d hd hm⟩
  rw [← maximumIndecomposableDimension_eq_polytopal_supremum]
  exact hG.maximum_dimension

end GraphicalZonotopes

end
end
end BundlePart436

section BundlePart437
/- Source: Papers/GraphicalZonotopes/TriangleFreeSeparatorPaper.lean -/






@[expose] public section
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset

/-- The literal connectivity conclusion includes nonemptiness of every
remaining vertex set. The cardinality hypothesis supplies that fact. -/
theorem SupportsFullIndecomposable.delete_lt_three_connected {n : ℕ} (hn : 4 ≤ n)
    {G : SimpleGraph (Fin n)} (hG : SupportsFullIndecomposable G)
    (B : Finset (Fin n)) (hB : B.card < 3) :
    (G.induce ((B : Set (Fin n))ᶜ)).Connected := by
  classical
  have hout : ∃ v : Fin n,v ∉ B := by
    by_contra h
    push_neg at h
    have he : B = univ := by
      ext v
      simp only [mem_univ,iff_true]
      exact h v
    have hc := congrArg Finset.card he
    simp only [card_univ,Fintype.card_fin] at hc
    omega
  obtain ⟨v,hv⟩ := hout
  letI : Nonempty {w : Fin n // w ∈ (B : Set (Fin n))ᶜ} := ⟨⟨v,hv⟩⟩
  exact ⟨hG.delete_lt_three_preconnected hn B hB⟩

/-- Corollary 5.2 with ordinary polytopal indecomposability and the full
three-vertex-connectivity conclusion, expressed directly by all deletions. -/
theorem paper_corollary_5_2 {n : ℕ} (hn : 4 ≤ n) (G : SimpleGraph (Fin n))
    (hG : ∃ Q : Set (Fin n → ℝ),IsFinitePolytope Q ∧
      PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G)) :
    (∀ B : Finset (Fin n),
      2 ≤ Nat.card ((G.induce ((B : Set (Fin n))ᶜ)).ConnectedComponent) →
      ∃ T : Finset (Fin n),T ⊆ B ∧ T.card = 3 ∧ G.IsClique T) ∧
    (∀ B : Finset (Fin n),B.card < 3 →
      (G.induce ((B : Set (Fin n))ᶜ)).Connected) := by
  have hs := (supportsFullIndecomposable_iff_polytopal_weak G).mpr hG
  exact ⟨fun B hB => hs.separator_contains_triangle (by omega) B hB,
    fun B hB => hs.delete_lt_three_connected hn B hB⟩

/-- The printed extension of Corollary 5.2 to the actual direction graph of
any full-dimensional indecomposable generalized permutahedron. -/
theorem full_generalized_permutahedron_triangle_separators {n : ℕ} (hn : 4 ≤ n)
    {Q : Set (Fin n → ℝ)} (hQ : IsGeneralizedPermutahedron Q)
    (hi : PolytopalMinkowskiIndecomposable Q) (hd : FullDimension Q) :
    (∀ B : Finset (Fin n),
      2 ≤ Nat.card (((actualDirectionGraph Q).induce
        ((B : Set (Fin n))ᶜ)).ConnectedComponent) →
      ∃ T : Finset (Fin n),T ⊆ B ∧ T.card = 3 ∧ (actualDirectionGraph Q).IsClique T) ∧
    (∀ B : Finset (Fin n),B.card < 3 →
      ((actualDirectionGraph Q).induce ((B : Set (Fin n))ᶜ)).Connected) := by
  have hw : IsWeakMinkowskiSummand Q (graphicalZonotope (actualDirectionGraph Q)) := by
    obtain ⟨z,hzn,hzs,rfl⟩ := hQ
    exact (isWeakMinkowskiSummand_graphical_iff hzn hzs).mpr
      (graphical_actualDirectionGraph hzn hzs)
  exact paper_corollary_5_2 hn (actualDirectionGraph Q) ⟨Q,hQ.finitePolytope,hi,hd,hw⟩

end GraphicalZonotopes

end
end
end BundlePart437

section BundlePart438
/- Source: Papers/GraphicalZonotopes/UnitActiveSupport.lean -/








@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical Pointwise BigOperators
namespace GraphicalZonotopes
namespace UnitLatticeGeometry
open Finset RefinedTriangleComponents FourPartGraphRecognition

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- The unit-summand geometry does not need ambient full dimension. In every
actual dimension at least three it produces the Cartesian tetrahedral family
on exactly the active coordinates. -/
theorem active_coefficient_model {G : SimpleGraph V} (hG : G.CliqueFree 5)
    {Q : Set (V → ℝ)} (hQ : LatticePolytope Q)
    (hi : PolytopalMinkowskiIndecomposable Q)
    (hd : 3 ≤ Module.finrank ℝ (vectorSpan ℝ Q))
    (hsum : IsMinkowskiSummand Q (graphicalZonotope G)) :
    ∃ (z : SetFunction V) (A : Fin 4 → Finset V),
      ExtremeSupermodular z ∧
      (∀ i, (A i).card = 1 ∨ (A i).card = 2) ∧
      (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧
      ProductFamily (family (mobius z)) A ∧
      actualDirectionGraph Q = unionGraph (family (mobius z)) ∧
      DependsOn z ((family (mobius z)).biUnion id) ∧
      Module.finrank ℝ (vectorSpan ℝ (basePolytope z)) =
        Module.finrank ℝ (vectorSpan ℝ Q) := by
  obtain ⟨R,hR,hcR,hnR,he⟩ := hsum
  have he' : Q + R = (1 : ℝ) • graphicalZonotope G := by simpa using he
  obtain ⟨hfn,hfs,hbody,hgraph,hbound⟩ := actual_summand_lowerSupport
    hQ.compact hQ.convex hi.1 hR hcR hnR (by norm_num : (0 : ℝ) ≤ 1) he'
  let f := lowerSupport Q
  let z := normalize f
  have hzn : TranslationNormalized z := normalize_translationNormalized hfn
  have hzs : Supermodular z := hfs.normalize
  have hzi : IntegerValued z := (hQ.lowerSupport_integerValued hi.1).normalize
  have hzg : Graphical G z := by
    intro u v huv hnon S hu hv
    rw [delta_normalize f huv hu hv]
    exact hgraph u v huv hnon S hu hv
  have hdim : Module.finrank ℝ (vectorSpan ℝ (basePolytope z)) =
      Module.finrank ℝ (vectorSpan ℝ Q) := by
    rw [vectorSpan_basePolytope_normalize,← hbody]
  have hdim3 : 3 ≤ Module.finrank ℝ (vectorSpan ℝ (basePolytope z)) := by
    rw [hdim]
    exact hd
  have hne : z ≠ 0 := by
    intro hz
    rw [hz,basePolytope_zero] at hdim3
    have hspan : vectorSpan ℝ ({0} : Set (V → ℝ)) =
        (⊥ : Submodule ℝ (V → ℝ)) := _root_.vectorSpan_singleton ℝ (0 : V → ℝ)
    rw [hspan,_root_.finrank_bot] at hdim3
    omega
  have hgp : IsGeneralizedPermutahedron Q := ⟨f,hfn,hfs,hbody⟩
  have hic : MinkowskiIndecomposable Q :=
    (minkowskiIndecomposable_iff_polytopal hgp).mpr hi
  have hext : ExtremeSupermodular z := by
    apply MinkowskiIndecomposable.extremeSupermodular_normalize hfn hfs hne
    rwa [← hbody]
  obtain ⟨hF,hconn,hactual,hdep⟩ :=
    refined_support_of_dimension_ge_three hG hext hzg hdim3
  have hsupported : CliqueSupported G (mobius z) :=
    (mobius_cliqueSupported_iff G z).mpr ⟨hzn,hzg⟩
  have hboolean : ∀ u v : V, u ≠ v → ∀ S : Finset V, u ∉ S → v ∉ S →
      delta (zeta (mobius z)) u v S = 0 ∨ delta (zeta (mobius z)) u v S = 1 := by
    intro u v huv S hu hv
    rw [zeta_mobius]
    by_cases hadj : G.Adj u v
    · apply integer_between_zero_one (integer_delta hzi u v S)
        (hzs.elemental u v huv S hu hv)
      rw [delta_normalize f huv hu hv]
      exact hbound u v huv hadj S hu hv
    · exact Or.inl (hzg u v huv hadj S hu hv)
  have hmem : ∀ D, D ∈ family (mobius z) ↔ D.card = 4 ∧ mobius z D ≠ 0 :=
    mem_family _
  obtain ⟨hthin,hsquare⟩ := UnitFamilyStructure.structure_of_boolean
    hG hsupported hboolean hmem
  obtain ⟨A,hsize,hdis,hprod⟩ := FourPartCompletion.cartesian_completion
    (family (mobius z)) (fun D hD => ((hmem D).mp hD).1) hF hconn hthin hsquare
  refine ⟨z,A,hext,hsize,hdis,hprod,?_,hdep,hdim⟩
  rw [actualDirectionGraph_normalize,← hbody] at hactual
  exact hactual

end UnitLatticeGeometry
end GraphicalZonotopes

end
end
end BundlePart438

section BundlePart439
/- Source: Papers/GraphicalZonotopes/FourPartActiveSupport.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.FourPartGraphRecognition
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A Cartesian tetrahedron family gives the literal complete four-partite
graph on its active vertices. No coverage of the ambient vertex type is
assumed: every vertex outside the four displayed parts is isolated. -/
theorem product_unionGraph_adj_iff {F : Finset (Finset V)} {A : Fin 4 → Finset V}
    (hne : ∀ i,(A i).Nonempty) (hdis : ∀ i j,i ≠ j → Disjoint (A i) (A j))
    (hprod : ProductFamily F A) (u v : V) :
    (unionGraph F).Adj u v ↔ ∃ i j : Fin 4,i ≠ j ∧ u ∈ A i ∧ v ∈ A j := by
  constructor
  · rintro ⟨huv,D,hD,hu,hv⟩
    obtain ⟨w,hw,rfl⟩ := (hprod D).mp hD
    obtain ⟨i,_,hi⟩ := mem_image.mp hu
    obtain ⟨j,_,hj⟩ := mem_image.mp hv
    refine ⟨i,j,?_,hi ▸ hw i,hj ▸ hw j⟩
    intro hij
    subst j
    exact huv (hi.symm.trans hj)
  · rintro ⟨i,j,hij,hu,hv⟩
    let w : Fin 4 → V := fun k =>
      if k = i then u else if k = j then v else Classical.choose (hne k)
    have hw : ∀ k,w k ∈ A k := by
      intro k
      dsimp [w]
      split_ifs with hki hkj
      · simpa only [hki] using hu
      · simpa only [hkj] using hv
      · exact Classical.choose_spec (hne k)
    have hwi : w i = u := by simp [w]
    have hwj : w j = v := by simp [w,Ne.symm hij]
    have huv : u ≠ v := by
      intro he
      exact Finset.disjoint_left.mp (hdis i j hij) hu (he.symm ▸ hv)
    refine ⟨huv,univ.image w,(hprod _).mpr ⟨w,hw,rfl⟩,?_,?_⟩
    · exact mem_image.mpr ⟨i,mem_univ _,hwi⟩
    · exact mem_image.mpr ⟨j,mem_univ _,hwj⟩

/-- The nonisolated vertices are exactly the union of the four parts. This
is the precise dictionary needed when the ambient polytope is not full
dimensional and unused coordinates remain in the ambient type. -/
theorem product_unionGraph_support {F : Finset (Finset V)} {A : Fin 4 → Finset V}
    (hne : ∀ i,(A i).Nonempty) (hdis : ∀ i j,i ≠ j → Disjoint (A i) (A j))
    (hprod : ProductFamily F A) :
    (unionGraph F).support = ((univ.biUnion A : Finset V) : Set V) := by
  ext u
  rw [SimpleGraph.mem_support]
  constructor
  · rintro ⟨v,huv⟩
    obtain ⟨i,j,hij,hu,hv⟩ := (product_unionGraph_adj_iff hne hdis hprod u v).mp huv
    exact mem_biUnion.mpr ⟨i,mem_univ _,hu⟩
  · intro hu
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hu
    obtain ⟨j,hji⟩ := exists_ne i
    obtain ⟨v,hv⟩ := hne j
    exact ⟨v,(product_unionGraph_adj_iff hne hdis hprod u v).mpr ⟨i,j,Ne.symm hji,hi,hv⟩⟩

end GraphicalZonotopes.FourPartGraphRecognition

end
end
end BundlePart439

section BundlePart440
/- Source: Papers/GraphicalZonotopes/UnitActiveClassification.lean -/






/-! # Unit-lattice direction supports without ambient full dimension

This is the active-coordinate formulation stated in the introduction. The
polytope may use only part of the ambient graph. The conclusion classifies its
actual edge directions, including every unused coordinate as an isolated
vertex, rather than imposing full dimension or ambient graph coverage.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical Pointwise BigOperators
namespace GraphicalZonotopes
open Finset RefinedTriangleComponents FourPartGraphRecognition

/-- Every indecomposable lattice summand of an unscaled K5-free graphical
zonotope, in any actual dimension at least three, has a complete four-partite
actual direction graph on its active coordinates. Each part has one or two
vertices. In particular there are at most eight active coordinates and the
affine dimension is at most seven. The finite vertex order is chosen
internally and is not an added hypothesis. -/
theorem unit_lattice_active_classification_finite {V : Type*} [Fintype V] :
    letI : LinearOrder V := Separator.finiteVertexOrder V;
    ∀ (G : SimpleGraph V), G.CliqueFree 5 →
      ∀ (Q : Set (V → ℝ)), LatticePolytope Q →
      PolytopalMinkowskiIndecomposable Q →
      3 ≤ Module.finrank ℝ (vectorSpan ℝ Q) →
      IsMinkowskiSummand Q (graphicalZonotope G) →
      ∃ A : Fin 4 → Finset V,
        (∀ i, (A i).card = 1 ∨ (A i).card = 2) ∧
        (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧
        (∀ u v, (actualDirectionGraph Q).Adj u v ↔
          ∃ i j : Fin 4, i ≠ j ∧ u ∈ A i ∧ v ∈ A j) ∧
        (actualDirectionGraph Q).support =
          ((univ.biUnion A : Finset V) : Set V) ∧
        (actualDirectionGraph Q).support.ncard ≤ 8 ∧
        Module.finrank ℝ (vectorSpan ℝ Q) ≤ 7 := by
  letI : LinearOrder V := Separator.finiteVertexOrder V
  intro G hG Q hQ hi hd hsum
  obtain ⟨z,A,hz,hsize,hdis,hprod,hactual,hdep,hdim⟩ :=
    UnitLatticeGeometry.active_coefficient_model hG hQ hi hd hsum
  have hne : ∀ i, (A i).Nonempty := by
    intro i
    apply card_pos.mp
    rcases hsize i with h | h <;> omega
  have hadj : ∀ u v, (actualDirectionGraph Q).Adj u v ↔
      ∃ i j : Fin 4, i ≠ j ∧ u ∈ A i ∧ v ∈ A j := by
    intro u v
    rw [hactual]
    exact product_unionGraph_adj_iff hne hdis hprod u v
  have hsupport : (actualDirectionGraph Q).support =
      ((univ.biUnion A : Finset V) : Set V) := by
    rw [hactual]
    exact product_unionGraph_support hne hdis hprod
  have hU : (univ.biUnion A).card ≤ 8 := by
    apply card_biUnion_le.trans
    calc
      (∑ i : Fin 4, (A i).card) ≤ ∑ _i : Fin 4, 2 := by
        apply sum_le_sum
        intro i _
        rcases hsize i with h | h <;> omega
      _ = 8 := by norm_num
  have hFsub : (family (mobius z)).biUnion id ⊆ univ.biUnion A := by
    intro v hv
    obtain ⟨D,hD,hvD⟩ := mem_biUnion.mp hv
    obtain ⟨w,hw,rfl⟩ := (hprod D).mp hD
    obtain ⟨i,_,hiv⟩ := mem_image.mp hvD
    exact mem_biUnion.mpr ⟨i,mem_univ _,hiv ▸ hw i⟩
  have hFcard := (card_le_card hFsub).trans hU
  have hdimle := finrank_vectorSpan_le_support hz.1 hz.2.1 hdep
  rw [hdim] at hdimle
  refine ⟨A,hsize,hdis,hadj,hsupport,?_,by omega⟩
  rw [hsupport,Set.ncard_coe_finset]
  exact hU

end GraphicalZonotopes

end
end
end BundlePart440

section BundlePart441
/- Source: Papers/GraphicalZonotopes/PlanarStraightLineAdapter.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical Graph
namespace GraphicalZonotopes

/-- A literal noncrossing straight-line drawing gives an ordinary drawing by
simple continuous arcs. The two real-plane representations are related by an
explicit continuous linear equivalence. -/
theorem HasPlaneStraightLineDrawing.hasPlaneDrawing {V : Type*} {G : SimpleGraph V}
    (hG : HasPlaneStraightLineDrawing G) : HasPlaneDrawing G := by
  obtain ⟨p,hp,hvertex,hcross⟩ := hG
  let L : (Fin 2 → ℝ) ≃L[ℝ] Schoenflies.Plane := (EuclideanSpace.equiv (Fin 2) ℝ).symm
  let q : V → Schoenflies.Plane := fun v => L (p v)
  have hq : Function.Injective q := L.injective.comp hp
  let drawing : Sym2 V → ℝ → Schoenflies.Plane := fun e t =>
    L (AffineMap.lineMap (p e.out.1) (p e.out.2) t)
  have hadj : ∀ e ∈ G.edgeSet,G.Adj e.out.1 e.out.2 := by
    intro e he
    apply G.mem_edgeSet.mp
    rwa [Sym2.mk_fst_out_snd_out]
  have hlink : ∀ e ∈ G.edgeSet,(PlaneDrawing.planeGraph G q).IsLink
      e (q e.out.1) (q e.out.2) := by
    intro e he
    exact (PlaneDrawing.planeGraph_isLink G q hq _ _ _).mpr
      ⟨(Sym2.mk_fst_out_snd_out e).symm,hadj e he⟩
  have himage : ∀ e,Graph.edgeArc drawing e =
      L '' segment ℝ (p e.out.1) (p e.out.2) := by
    intro e
    rw [segment_eq_image_lineMap,Set.image_image]
    rfl
  have hpull : ∀ e (z : Fin 2 → ℝ),L z ∈ Graph.edgeArc drawing e →
      z ∈ segment ℝ (p e.out.1) (p e.out.2) := by
    intro e z hz
    rw [himage] at hz
    obtain ⟨w,hw,he⟩ := hz
    have hzw : w = z := L.injective he
    exact hzw ▸ hw
  refine ⟨q,hq,drawing,?_⟩
  constructor
  · intro e he
    have heG : e ∈ G.edgeSet := he
    have hcont : Continuous (drawing e) := L.continuous.comp AffineMap.lineMap_continuous
    have hinj : Function.Injective (drawing e) := L.injective.comp
      (AffineMap.lineMap_injective ℝ (fun h => (hadj e heG).ne (hp h)))
    refine ⟨hcont.continuousOn,hinj.injOn,?_⟩
    simpa only [drawing,AffineMap.lineMap_apply_zero,AffineMap.lineMap_apply_one] using hlink e heG
  · intro e x y v hl hv hve
    have heG : e ∈ G.edgeSet := hl.edge_mem
    rw [PlaneDrawing.planeGraph_vertexSet] at hv
    obtain ⟨w,rfl⟩ := hv
    have hseg : p w ∈ segment ℝ (p e.out.1) (p e.out.2) := hpull e (p w) hve
    have hw : w = e.out.1 ∨ w = e.out.2 := by
      by_contra hh
      have h₁ : w ≠ e.out.1 := fun he => hh (Or.inl he)
      have h₂ : w ≠ e.out.2 := fun he => hh (Or.inr he)
      exact hvertex _ _ _ (hadj e heG) h₁ h₂ hseg
    have hwq : q w = q e.out.1 ∨ q w = q e.out.2 :=
      hw.imp (congrArg q) (congrArg q)
    rcases hl.eq_and_eq_or_eq_and_eq (hlink e heG) with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact hwq
    · exact hwq.symm
  · intro e f he hf hef x hxe hxf
    have heG : e ∈ G.edgeSet := he
    have hfG : f ∈ G.edgeSet := hf
    rw [himage] at hxe
    obtain ⟨z,hz,hzx⟩ := hxe
    have hzf : z ∈ segment ℝ (p f.out.1) (p f.out.2) := by
      apply hpull f z
      rwa [hzx]
    rcases hcross _ _ _ _ (hadj e heG) (hadj f hfG) z hz hzf with h | h | h
    · obtain ⟨hu,hv⟩ := h
      apply False.elim
      apply hef
      calc
        e = s(e.out.1,e.out.2) := (Sym2.mk_fst_out_snd_out e).symm
        _ = s(f.out.1,f.out.2) := by rw [hu,hv]
        _ = f := Sym2.mk_fst_out_snd_out f
    · obtain ⟨hu,hv⟩ := h
      apply False.elim
      apply hef
      calc
        e = s(e.out.1,e.out.2) := (Sym2.mk_fst_out_snd_out e).symm
        _ = s(f.out.2,f.out.1) := by rw [hu,hv]
        _ = s(f.out.1,f.out.2) := Sym2.eq_swap
        _ = f := Sym2.mk_fst_out_snd_out f
    · obtain ⟨w,hwe,hwf,hzw⟩ := h
      have hxq : x = q w := hzx.symm.trans (congrArg L hzw)
      rw [hxq]
      refine ⟨?_,?_,?_⟩
      · rw [PlaneDrawing.planeGraph_vertexSet]
        exact ⟨w,rfl⟩
      · rcases hwe with hew | hew
        · rw [hew]
          exact (hlink e heG).inc_left
        · rw [hew]
          exact (hlink e heG).inc_right
      · rcases hwf with hfw | hfw
        · rw [hfw]
          exact (hlink f hfG).inc_left
        · rw [hfw]
          exact (hlink f hfG).inc_right

/-- The previously checked explicit straight-line sharpness family is planar
under exactly the same ordinary-arc definition used in the planar corollaries. -/
theorem PathDrawing.path_hasPlaneDrawing (n : ℕ) : HasPlaneDrawing (Path.graph n) :=
  (PathDrawing.path_plane_drawing n).hasPlaneDrawing

end GraphicalZonotopes

end
end
end BundlePart441

section BundlePart442
/- Source: Papers/GraphicalZonotopes/PartialThreeTreeIncidenceForest.lean -/






@[expose] public section
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem triangles_mono_graph {G H : SimpleGraph V} (h : G ≤ H) :
    triangles G ⊆ triangles H := by
  intro T hT
  obtain ⟨hc,hcl⟩ := mem_triangles.mp hT
  exact mem_triangles.mpr ⟨hc,fun u hu v hv huv => h (hcl hu hv huv)⟩

/-- The inclusion of a graph into a supergraph induces an actual injective
map of all its tetrahedron and triangle incidence nodes. -/
def incidenceHomOfLE {G H : SimpleGraph V} (h : G ≤ H) :
    cliqueTriangleIncidence G →g cliqueTriangleIncidence H where
  toFun := Sum.map (fun C => ⟨C.1,tetrahedra_mono h C.2⟩)
    (fun T => ⟨T.1,triangles_mono_graph h T.2⟩)
  map_rel' := by
    intro x y hxy
    cases x <;> cases y <;> exact hxy

theorem incidenceHomOfLE_injective {G H : SimpleGraph V} (h : G ≤ H) :
    Function.Injective (incidenceHomOfLE h) := by
  apply Sum.map_injective.mpr
  constructor
  · intro C D he
    exact Subtype.ext (congrArg (fun E : {E : Finset V // E ∈ tetrahedra H} => E.1) he)
  · intro C D he
    exact Subtype.ext (congrArg (fun E : {E : Finset V // E ∈ triangles H} => E.1) he)

/-- The structural assertion in Corollary 6.8: the intrinsic incidence graph
of every partial three-tree is a forest, including all small-vertex cases.
No tree completion is part of the resulting graph or of its definition. -/
theorem IsPartialThreeTree.incidence_isAcyclic {G : SimpleGraph V}
    (hG : IsPartialThreeTree G) : (cliqueTriangleIncidence G).IsAcyclic := by
  rcases hG with hsmall | ⟨H,hH,hGH⟩
  · have hno : ∀ C : {C : Finset V // C ∈ tetrahedra G},False := by
      intro C
      have hfour : C.1.card = 4 := (mem_filter.mp C.2).2.1
      have hle := card_le_card (subset_univ C.1)
      rw [card_univ,hfour] at hle
      omega
    have hbot : cliqueTriangleIncidence G = ⊥ := by
      ext x y
      cases x with
      | inl C => exact (hno C).elim
      | inr T =>
        cases y with
        | inl C => exact (hno C).elim
        | inr U => rfl
    rw [hbot]
    exact SimpleGraph.isAcyclic_bot
  · exact hH.incidence_isTree.isAcyclic.comap
      (incidenceHomOfLE hGH) (incidenceHomOfLE_injective hGH)

end GraphicalZonotopes

end
end
end BundlePart442


section ReadOnlyPrintAudit
public meta section

open Lean Meta Elab Command

namespace VerificationPrintAudit

def origin (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!
  | none => env.mainModule

def projectModule (env : Environment) (n : Name) : Bool :=
  let m := origin env n
  m == env.mainModule || (`Papers).isPrefixOf m || (`Cubical).isPrefixOf m ||
    (`Verified).isPrefixOf m || (`Audit).isPrefixOf m || (`Consolidated).isPrefixOf m ||
    (`ConsolidatedDev).isPrefixOf m

def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient primitive"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def valueRequired : ConstantInfo → Bool
  -- Module export may represent an imported, already proved theorem by an
  -- axiom-shaped constant while retaining its genuine axiom cache. Such a
  -- project declaration has no proof body available for this graph walk.
  | .axiomInfo _ | .defnInfo _ | .thmInfo _ | .opaqueInfo _ => true
  | _ => false

/-- The same depth-first graph walk as the recursive implementation, with an
explicit work list and one accumulated completeness flag. No recursive return
frames retain earlier versions of the JSON node array. Dependencies are pushed
in their original sorted order, so node order and all output fields agree. -/
partial def graph (env : Environment) (pending : List Name)
    (seen : NameSet := {}) (nodes : Array Json := #[]) : Array Json × Bool := Id.run do
  let mut work := pending
  let mut visited := seen
  let mut output := nodes
  let mut complete := true
  let foundations : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  while !work.isEmpty do
    match work with
    | [] => pure ()
    | n :: rest =>
      work := rest
      if !visited.contains n then
        visited := visited.insert n
        let isProject := projectModule env n && !foundations.contains n
        match env.checked.get.find? n with
        | none =>
          let node := Json.mkObj [("name", toJson n.toString), ("missing", toJson true)]
          output := output.push node
          complete := false
        | some info =>
          let deps := if isProject then info.getUsedConstantsAsSet.toArray.qsort Name.lt else #[]
          let available := !valueRequired info || (info.value? (allowOpaque := true)).isSome
          let node := Json.mkObj [
            ("name", toJson n.toString),
            ("module", toJson (origin env n).toString),
            ("kind", toJson (kind info)),
            ("projectDeclaration", toJson isProject),
            ("valueAvailable", toJson available),
            ("dependencies", toJson (deps.map Name.toString))]
          output := output.push node
          complete := complete && (!isProject || available)
          work := deps.toList ++ work
  return (output, complete)

/-- Print a checked constant's type, transitive axioms, and available proof graph.
An axiom outside the three standard foundations causes a command error. -/
elab "#print_proof_audit " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let info ← getConstInfo n
  let axioms ← collectAxioms n
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let rejected := axioms.filter (fun a => !allowed.contains a)
  unless rejected.isEmpty do
    throwError "Unapproved axioms in {n}: {rejected}"
  let env := (← getEnv).setExporting false
  let (nodes, complete) := graph env [n]
  let typeText ← liftTermElabM do return (← ppExpr info.type).pretty
  let expandedType ← liftTermElabM do return (← ppExpr (← whnf info.type)).pretty
  let output := Json.mkObj [
    ("theorem", toJson n.toString),
    ("type", toJson typeText),
    ("headUnfoldedType", toJson expandedType),
    ("axioms", toJson (axioms.qsort Name.lt |>.map Name.toString)),
    ("completeLocalValueGraph", toJson complete),
    ("boundary", toJson "Imported non-project constants are checked-library leaves."),
    ("nodes", Json.arr nodes)]
  logInfo m!"PROOF_AUDIT_JSON {output.compress}"

end VerificationPrintAudit

end
end ReadOnlyPrintAudit

section ReadOnlyBundleAudit
public meta section
open Lean Meta Elab Command
namespace VerificationPrintAudit

elab "#print_proof_audit_bundle " "[" ids:ident,* "]" : command => do
  let mut names : Array Name := #[]
  let mut roots : Array Json := #[]
  for id in ids.getElems do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    if names.contains n then
      throwError "Duplicate audit root: {n}"
    names := names.push n
    let info ← getConstInfo n
    let axioms ← collectAxioms n
    let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
    let rejected := axioms.filter (fun a => !allowed.contains a)
    unless rejected.isEmpty do
      throwError "Unapproved axioms in {n}: {rejected}"
    let typeText ← liftTermElabM do return (← ppExpr info.type).pretty
    let expandedType ← liftTermElabM do return (← ppExpr (← whnf info.type)).pretty
    roots := roots.push <| Json.mkObj [
      ("theorem", toJson n.toString),
      ("type", toJson typeText),
      ("headUnfoldedType", toJson expandedType),
      ("axioms", toJson (axioms.qsort Name.lt |>.map Name.toString))]
  unless !names.isEmpty do
    throwError "The principal audit needs at least one theorem."
  let env := (← getEnv).setExporting false
  let (nodes, complete) := graph env names.toList
  let output := Json.mkObj [
    ("roots", Json.arr roots),
    ("completeLocalValueGraph", toJson complete),
    ("boundary", toJson "Imported non-project constants are checked-library leaves."),
    ("nodes", Json.arr nodes)]
  logInfo m!"PROOF_AUDIT_BUNDLE_JSON {output.compress}"

end VerificationPrintAudit

end
end ReadOnlyBundleAudit

#print_proof_audit_bundle [
  GraphicalZonotopes.Path.principal_path_theorem,
  GraphicalZonotopes.Path.polytope_defining_equations,
  GraphicalZonotopes.Path.polytope_defining_equations_real,
  GraphicalZonotopes.Path.polytope_defining_equations_sums,
  GraphicalZonotopes.Path.setFunction_expansion,
  GraphicalZonotopes.Path.every_exposed_edge_is_graph_direction,
  GraphicalZonotopes.generalizedPermutahedron_iff_weak_complete,
  GraphicalZonotopes.minkowskiIndecomposable_iff_polytopal,
  GraphicalZonotopes.sharp_direction_bounds,
  GraphicalZonotopes.generalizedPermutahedron_exposed_edge_is_root,
  GraphicalZonotopes.root_parallel_pair_eq,
  GraphicalZonotopes.direction_bounds_polytopal,
  GraphicalZonotopes.ExtremeSupermodular.spanning_tetrahedra,
  GraphicalZonotopes.edge_bound_of_connected_tetrahedra,
  GraphicalZonotopes.maximum_degree_bound_of_connected_tetrahedra,
  GraphicalZonotopes.Path.setFunction_eq_booleanFormula,
  GraphicalZonotopes.Path.polytope_boolean_defining_equations,
  GraphicalZonotopes.DoubledParts.principal_boolean_phase_theorem,
  GraphicalZonotopes.BooleanFourier.boolean_face_line,
  GraphicalZonotopes.BooleanFourier.faceKernel_finrank,
  GraphicalZonotopes.threeTree_classification_polytopal,
  GraphicalZonotopes.threeTree_classification,
  GraphicalZonotopes.threeTree_classification_literal,
  GraphicalZonotopes.admissible_threeTree_lattice_witness,
  GraphicalZonotopes.threeTree_lattice_dilation_sharp,
  GraphicalZonotopes.threeTree_lattice_lower_bound_polytopal,
  GraphicalZonotopes.Separator.induced_separator_capacity_finite,
  GraphicalZonotopes.Separator.positive_response_gluing_finite,
  GraphicalZonotopes.Separator.clique_separator_capacity_finite,
  GraphicalZonotopes.unit_lattice_classification_sharp,
  GraphicalZonotopes.unit_lattice_classification_polytopal,
  GraphicalZonotopes.unit_translated_lattice_classification_polytopal,
  GraphicalZonotopes.threeTree_translated_lattice_lower_bound,
  GraphicalZonotopes.FourPartCompletion.cartesian_completion,
  GraphicalZonotopes.four_partite_spanning_threeTrees,
  GraphicalZonotopes.four_partite_threeTree_dimension_attained,
  GraphicalZonotopes.threeTree_actual_dimension_admissible,
  GraphicalZonotopes.admissible_threeTree_active_witness,
  GraphicalZonotopes.maximumThreeTreeSupportDimension_eq_polytopal,
  GraphicalZonotopes.optimal_k5_free_dilation,
  GraphicalZonotopes.optimal_k5_free_dilation_attained,
  GraphicalZonotopes.optimal_k5_free_dilation_lower_bound_polytopal,
  GraphicalZonotopes.DoubledParts.one_singleton_decomposition,
  GraphicalZonotopes.FourSmallParts.four_small_parts_decomposition,
  GraphicalZonotopes.boolean_decomposition_every_dimension,
  GraphicalZonotopes.BooleanModule.small_count_lattice_books,
  GraphicalZonotopes.BooleanModule.one_outer_lattice_book,
  GraphicalZonotopes.BooleanModule.small_count_lattice_books_literal,
  GraphicalZonotopes.DiamondBook.paper_theorem_8_1_literal,
  GraphicalZonotopes.DiamondBook.paper_theorem_8_1,
  GraphicalZonotopes.DiamondBook.maximum_dimension,
  GraphicalZonotopes.DiamondBook.diamond_witness_multipartite,
  GraphicalZonotopes.DiamondBook.no_supporting_spanning_threeTree,
  GraphicalZonotopes.BooleanModule.positive_star_interpolation,
  GraphicalZonotopes.BooleanModule.negative_star_interpolation,
  GraphicalZonotopes.BooleanModule.threshold_book_interval,
  GraphicalZonotopes.BooleanModule.book_upper_interval,
  GraphicalZonotopes.maximumIndecomposableDimension_eq_polytopal,
  GraphicalZonotopes.DiamondBook.paper_theorem_8_1_polytopal,
  GraphicalZonotopes.not_fullLatticeSummandAt_zero,
  GraphicalZonotopes.PathJoin.corollary_nine_four,
  GraphicalZonotopes.PathJoin.appendix_B_one,
  GraphicalZonotopes.clique_book_classification,
  GraphicalZonotopes.clique_book_classification_polytopal,
  GraphicalZonotopes.SaturatedDirections.paper_theorem_7_12,
  GraphicalZonotopes.SaturatedDirections.paper_theorem_7_12_polytopal,
  GraphicalZonotopes.SaturatedDirections.paper_theorem_7_12_geometric,
  GraphicalZonotopes.saturatedHubNeighbors_closed_formula,
  GraphicalZonotopes.SparseFamily.paper_theorem_8_2,
  GraphicalZonotopes.SparseFamily.paper_theorem_8_2_polytopal,
  GraphicalZonotopes.TwoHub.exponential_lattice_summand,
  GraphicalZonotopes.TwoHub.exponential_family,
  GraphicalZonotopes.TwoHub.exponential_polytopal_summand,
  GraphicalZonotopes.TwoHub.two_singleton_classification,
  GraphicalZonotopes.TwoHub.classification_polytopal,
  GraphicalZonotopes.TwoHub.full_polytopal_iff,
  GraphicalZonotopes.TwoHub.lattice_polytopal_attainment,
  GraphicalZonotopes.partial_threeTree_piecewise_maximum,
  GraphicalZonotopes.partial_threeTree_full_dimension_spectrum,
  GraphicalZonotopes.threeTree_dimension_and_spectrum,
  GraphicalZonotopes.partial_threeTree_support_classification_polytopal_finite,
  GraphicalZonotopes.partial_threeTree_piecewise_maximum_finite,
  GraphicalZonotopes.partial_threeTree_full_dimension_spectrum_polytopal_finite,
  GraphicalZonotopes.SupportsFullIndecomposable.triangle_free_components_le_one,
  GraphicalZonotopes.SupportsFullIndecomposable.separator_contains_triangle,
  GraphicalZonotopes.SupportsFullIndecomposable.delete_lt_three_preconnected,
  GraphicalZonotopes.weak_summand_exposed_edge_direction,
  GraphicalZonotopes.weakSummand_indecomposable_iff_polytopal,
  GraphicalZonotopes.isWeakMinkowskiSummand_graphical_iff_finite_complement,
  GraphicalZonotopes.isMinkowskiSummand_graphical_iff_finite_complement,
  GraphicalZonotopes.partial_threeTree_polytope_support,
  GraphicalZonotopes.BooleanModule.cliqueCapacity_int_formula,
  GraphicalZonotopes.TwoHub.paper_corollary_8_5,
  GraphicalZonotopes.HamiltonianDeletion.hamiltonian_component_card_delete_le,
  GraphicalZonotopes.IsThreeTree.admissible_of_hamiltonian,
  GraphicalZonotopes.hamiltonian_threeTree_lattice_polytopal_finite,
  GraphicalZonotopes.actualEdgeDirectionLines_finite,
  GraphicalZonotopes.directionCount_eq_geometric_line_count,
  GraphicalZonotopes.three_hub_book_maximum,
  GraphicalZonotopes.TreeJoin.induced_subcubic_iff_subtree,
  GraphicalZonotopes.TreeJoin.maximum_dimension,
  GraphicalZonotopes.TreeJoin.supports_full_iff,
  GraphicalZonotopes.TreeJoin.paper_corollary_6_9_tree_join,
  GraphicalZonotopes.SparseFamily.complete_family,
  GraphicalZonotopes.TwoHub.CellDecisionTree.root_valid,
  GraphicalZonotopes.TwoHub.CellDecisionTree.leaves_card,
  GraphicalZonotopes.TwoHub.CellDecisionTree.root_proper,
  GraphicalZonotopes.TwoHub.PartitionData.partitionDilation_eq,
  GraphicalZonotopes.TwoHub.decision_tree_lattice_summand,
  GraphicalZonotopes.TwoHub.paper_lemma_8_6,
  GraphicalZonotopes.paper_corollary_6_4,
  GraphicalZonotopes.paper_corollary_6_4_stacked,
  GraphicalZonotopes.paper_corollary_6_5,
  GraphicalZonotopes.planar_threeTree_lattice_witness_finite,
  GraphicalZonotopes.HasPlaneDrawing.triangle_apex_separated,
  GraphicalZonotopes.TetrahedronComponents.maximumDimension_eq,
  GraphicalZonotopes.TetrahedronComponents.adj_iff_shared_triangle,
  GraphicalZonotopes.boundaryTriangles_after_attachment,
  Graph.IsArcK5.elim,
  GraphicalZonotopes.paper_corollary_5_2,
  GraphicalZonotopes.full_generalized_permutahedron_triangle_separators,
  GraphicalZonotopes.unit_lattice_active_classification_finite,
  GraphicalZonotopes.HasPlaneStraightLineDrawing.hasPlaneDrawing,
  GraphicalZonotopes.PathDrawing.path_hasPlaneDrawing,
  GraphicalZonotopes.IsPartialThreeTree.incidence_isAcyclic
]
