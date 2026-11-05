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

public import verified.parts.part039
import all verified.parts.part039

@[expose] public section

set_option debug.skipKernelTC false
set_option linter.all false
set_option Elab.async false
set_option internal.cmdlineSnapshots true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

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
