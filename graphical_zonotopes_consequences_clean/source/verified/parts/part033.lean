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

public import verified.parts.part032
import all verified.parts.part032

@[expose] public section

set_option debug.skipKernelTC false
set_option linter.all false
set_option Elab.async false
set_option internal.cmdlineSnapshots true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

section BundlePart408
/- Source: dev/planar_search/schoenflies_port/Schoenflies/StripConnected.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/


/-!
# The collar of a closed polygon is two-sided

`Schoenflies/Strip.lean` builds the blocks of Lemma 1.8 and proves the hard local half of the
statement: the two labelled sides are disjoint. This module closes the lemma for a *closed*
polygon by supplying the two remaining global facts.

* **Each side is connected.** The blueprint says "consecutive edge and vertex blocks overlap in
  a nonempty labelled half-strip, so the union of all left pieces is connected". Here that
  overlap is produced explicitly: `StripData.mem_overlapL_start` puts the point at frame
  position `(3 lam / 2, rho / 2)` in both `blockL i` and `sectorL i`, and
  `StripData.mem_overlapL_finish` puts the point at `(len i - 3 lam / 2, rho / 2)` in both
  `blockL i` and `sectorL (i + 1)`. The two `StripData` constraints that make these work are
  exactly the two the structure advertises for the purpose: `four_lam_lt_len` keeps the frame
  position inside the block, and `two_lam_lt_R` keeps it inside the sector, since
  `3 lam / 2 + rho / 2 < 2 lam < R`.

  The chaining is then a finite induction along `chainL`, and it does **not** need the
  wrap-around: connectedness of a union of connected sets only needs *some* spanning tree of
  the overlap graph, and the linear chain `0, 1, …, m + 2` is one. The blueprint's "the labels
  return consistently after one circuit" is a statement about the *labelling*, not about
  connectedness, and it is `Strip.sideL_disjoint_sideR`, already proved: it is what makes
  `sideL` and `sideR` two sets rather than one.

* **The collar is a neighbourhood, and removing the curve leaves exactly the two sides.**
  `StripData.nbhd_diff_carrier` is immediate from the two disjointness results of `Strip.lean`.
  Openness of `nbhd` is not: `nbhd` contains the curve, so it has to be recognised as a union
  of open sets. `StripData.nbhd_eq` does that, rewriting it as the union of the vertex balls
  and the full edge tubes; the two inclusions are `ball_diff_carrier_subset` and
  `tube_diff_carrier_subset` one way, and the covering of each edge by "near the first vertex,
  near the second vertex, or in the trimmed middle" the other way.

## Blueprint

* `Schoenflies.StripData.isConnected_sideL`, `.isConnected_sideR` — "the union of all left
  pieces is connected; the same is true on the right", inside Lemma 1.8 (a).
* `Schoenflies.StripData.nbhd_diff_carrier` — `N \ P = N_L ⊔ N_R`, Lemma 1.8 (a).
* `Schoenflies.StripData.collar` — Lemma 1.8 (a) for a closed polygon, given the constants.

Producing the constants is `exists_stripData`, which lives elsewhere; every statement here is
for a given `D : StripData P`, exactly as in `Schoenflies/Strip.lean`.
-/

open Metric Set

namespace Schoenflies

open Plane

variable {m : ℕ}

namespace ClosedPolygon

variable {P : ClosedPolygon m} {i : ZMod (m + 3)} {c t s : ℝ}

/-! ### Two frames at one edge

Everything below needs the edge frame read from *both* ends: `Strip.lean` has the departure
end, and the overlap with the sector at the far vertex needs the arrival end. -/

/-- The incoming ray at a vertex is a unit vector. -/
theorem isDirection_rayIn : IsDirection (P.rayIn i) := isDirection_dir vertex_pred_ne

/-- The far vertex of edge `i` sits at frame position `(len i, 0)`. -/
theorem off_sub_vertex_succ :
    P.off i t s - P.vertex (i + 1) = (t - P.len i) • P.tang i + s • perp (P.tang i) := by
  have hv : P.vertex (i + 1) = P.vertex i + (P.len i) • P.tang i := by
    rw [len_smul_tang]; module
  rw [off, hv]; module

/-- The block-to-far-sector distance bound, the mirror of `dist_off_vertex_le`. -/
theorem dist_off_vertex_succ_le : dist (P.off i t s) (P.vertex (i + 1)) ≤ |t - P.len i| + |s| := by
  rw [dist_eq_norm, off_sub_vertex_succ]
  calc ‖(t - P.len i) • P.tang i + s • perp (P.tang i)‖
      ≤ ‖(t - P.len i) • P.tang i‖ + ‖s • perp (P.tang i)‖ := norm_add_le _ _
    _ = |t - P.len i| + |s| := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, norm_perp,
          isDirection_tang.norm, mul_one, mul_one]

/-- The distance from a point of edge `i` to the edge's far endpoint, the mirror of
`dist_pt_vertex`. -/
theorem dist_pt_vertex_succ : dist (P.pt i c) (P.vertex (i + 1)) = |c - P.len i| := by
  rw [pt, dist_eq_norm, off_sub_vertex_succ, zero_smul, add_zero, norm_smul, Real.norm_eq_abs,
    isDirection_tang.norm, mul_one]

/-! ### The two incident edges, as rays out of a vertex

`mem_edge_sub` and `mem_edge_pred_sub` read a point of an incident edge as a multiple of a ray.
The converses are what says that a ball about a vertex minus the curve is covered by the two
sectors: a direction on one of the two rays is *on the curve*, not beside it. -/

/-- Walking back along the incoming ray from vertex `i` traverses the previous edge. -/
theorem vertex_add_smul_rayIn (P : ClosedPolygon m) (i : ZMod (m + 3)) (c : ℝ) :
    P.vertex i + c • P.rayIn i = P.pt (i - 1) (P.len (i - 1) - c) := by
  have hsucc : i - 1 + 1 = i := sub_add_cancel i 1
  have hr : P.rayIn i = -P.tang (i - 1) := by
    have h := rayIn_succ (P := P) (i := i - 1)
    rwa [hsucc] at h
  have hlen : P.vertex i = P.vertex (i - 1) + (P.len (i - 1)) • P.tang (i - 1) := by
    rw [len_smul_tang, hsucc]; module
  rw [pt_eq, hr, hlen]
  module

/-- A point of the incoming ray at distance at most the previous edge's length lies on that
edge. -/
theorem mem_edge_pred_of_smul_rayIn (hc0 : 0 ≤ c) (hc1 : c ≤ P.len (i - 1)) :
    P.vertex i + c • P.rayIn i ∈ P.edge (i - 1) := by
  rw [vertex_add_smul_rayIn]
  exact pt_mem_edge ⟨by linarith, by linarith⟩

/-- A point of the outgoing ray at distance at most the edge's length lies on that edge. -/
theorem mem_edge_of_smul_tang (hc0 : 0 ≤ c) (hc1 : c ≤ P.len i) :
    P.vertex i + c • P.tang i ∈ P.edge i := by
  rw [← pt_eq]
  exact pt_mem_edge ⟨hc0, hc1⟩

end ClosedPolygon

namespace StripData

variable {P : ClosedPolygon m} (D : StripData P) {i j : ZMod (m + 3)} {x : Plane}

/-! ### The overlaps

The blueprint's "consecutive edge and vertex blocks overlap in a nonempty labelled half-strip".
Both witnesses sit at across-coordinate `rho / 2`, at along-coordinate `3 lam / 2` from the
vertex in question. The two hypotheses of `StripData` that were put there for this are
`four_lam_lt_len` — which gives `3 lam / 2 < len i - lam`, so the point is inside the block —
and `two_lam_lt_R` together with `rho < lam` — which gives
`3 lam / 2 + rho / 2 < 2 lam < R`, so the point is inside the sector. -/

/-- The along-coordinate of the witnesses clears the near trim. -/
theorem lam_lt_three_halves_lam : D.lam < 3 * D.lam / 2 := by have := D.lam_pos; linarith

/-- …and stays short of the far one, by `four_lam_lt_len`. -/
theorem three_halves_lam_lt : 3 * D.lam / 2 < P.len i - D.lam := by
  have := D.lam_pos
  have := D.four_lam_lt_len i
  linarith

/-- …and the whole witness stays inside the sector, by `rho_lt_lam` and `two_lam_lt_R`. -/
theorem overlap_dist_lt : 3 * D.lam / 2 + D.rho / 2 < D.R := by
  have := D.rho_lt_lam
  have := D.two_lam_lt_R
  linarith

/-- **The overlap at the departure vertex.** The point at frame position `(3 lam / 2, rho / 2)`
of edge `i` lies both in the left block of that edge and in the left sector at `i`. -/
theorem mem_overlapL_start :
    P.off i (3 * D.lam / 2) (D.rho / 2) ∈ D.blockL i ∩ D.sectorL i := by
  have hmem : P.off i (3 * D.lam / 2) (D.rho / 2) ∈ D.blockL i :=
    D.mem_blockL_off.2 ⟨D.lam_lt_three_halves_lam, D.three_halves_lam_lt,
      by linarith [D.rho_pos], by linarith [D.rho_pos]⟩
  refine ⟨hmem, D.blockL_sub_mem_arcL_start hmem, ?_⟩
  -- The sector reaches this far because `3 lam / 2 + rho / 2 < 2 lam < R`.
  refine lt_of_le_of_lt ClosedPolygon.dist_off_vertex_le ?_
  rw [abs_of_pos (by linarith [D.lam_pos] : (0:ℝ) < 3 * D.lam / 2),
    abs_of_pos (by linarith [D.rho_pos] : (0:ℝ) < D.rho / 2)]
  exact D.overlap_dist_lt

/-- **The overlap at the arrival vertex.** The point at frame position
`(len i - 3 lam / 2, rho / 2)` of edge `i` lies both in the left block of that edge and in the
left sector at `i + 1`. -/
theorem mem_overlapL_finish :
    P.off i (P.len i - 3 * D.lam / 2) (D.rho / 2) ∈ D.blockL i ∩ D.sectorL (i + 1) := by
  have h1 : D.lam < P.len i - 3 * D.lam / 2 := by
    have := D.lam_pos; have := D.four_lam_lt_len i; linarith
  have h2 : P.len i - 3 * D.lam / 2 < P.len i - D.lam := by have := D.lam_pos; linarith
  have hmem : P.off i (P.len i - 3 * D.lam / 2) (D.rho / 2) ∈ D.blockL i :=
    D.mem_blockL_off.2 ⟨h1, h2, by linarith [D.rho_pos], by linarith [D.rho_pos]⟩
  refine ⟨hmem, D.blockL_sub_mem_arcL_finish hmem, ?_⟩
  refine lt_of_le_of_lt ClosedPolygon.dist_off_vertex_succ_le ?_
  rw [show P.len i - 3 * D.lam / 2 - P.len i = -(3 * D.lam / 2) by ring,
    abs_neg, abs_of_pos (by linarith [D.lam_pos] : (0:ℝ) < 3 * D.lam / 2),
    abs_of_pos (by linarith [D.rho_pos] : (0:ℝ) < D.rho / 2)]
  exact D.overlap_dist_lt

/-- The right-hand mirror of `mem_overlapL_start`. -/
theorem mem_overlapR_start :
    P.off i (3 * D.lam / 2) (-(D.rho / 2)) ∈ D.blockR i ∩ D.sectorR i := by
  have hmem : P.off i (3 * D.lam / 2) (-(D.rho / 2)) ∈ D.blockR i :=
    D.mem_blockR_off.2 ⟨D.lam_lt_three_halves_lam, D.three_halves_lam_lt,
      by linarith [D.rho_pos], by linarith [D.rho_pos]⟩
  refine ⟨hmem, D.blockR_sub_mem_arcR_start hmem, ?_⟩
  refine lt_of_le_of_lt ClosedPolygon.dist_off_vertex_le ?_
  rw [abs_of_pos (by linarith [D.lam_pos] : (0:ℝ) < 3 * D.lam / 2),
    abs_neg, abs_of_pos (by linarith [D.rho_pos] : (0:ℝ) < D.rho / 2)]
  exact D.overlap_dist_lt

/-- The right-hand mirror of `mem_overlapL_finish`. -/
theorem mem_overlapR_finish :
    P.off i (P.len i - 3 * D.lam / 2) (-(D.rho / 2)) ∈ D.blockR i ∩ D.sectorR (i + 1) := by
  have h1 : D.lam < P.len i - 3 * D.lam / 2 := by
    have := D.lam_pos; have := D.four_lam_lt_len i; linarith
  have h2 : P.len i - 3 * D.lam / 2 < P.len i - D.lam := by have := D.lam_pos; linarith
  have hmem : P.off i (P.len i - 3 * D.lam / 2) (-(D.rho / 2)) ∈ D.blockR i :=
    D.mem_blockR_off.2 ⟨h1, h2, by linarith [D.rho_pos], by linarith [D.rho_pos]⟩
  refine ⟨hmem, D.blockR_sub_mem_arcR_finish hmem, ?_⟩
  refine lt_of_le_of_lt ClosedPolygon.dist_off_vertex_succ_le ?_
  rw [show P.len i - 3 * D.lam / 2 - P.len i = -(3 * D.lam / 2) by ring,
    abs_neg, abs_of_pos (by linarith [D.lam_pos] : (0:ℝ) < 3 * D.lam / 2),
    abs_neg, abs_of_pos (by linarith [D.rho_pos] : (0:ℝ) < D.rho / 2)]
  exact D.overlap_dist_lt

theorem blockL_nonempty : (D.blockL i).Nonempty := ⟨_, D.mem_overlapL_start.1⟩
theorem blockR_nonempty : (D.blockR i).Nonempty := ⟨_, D.mem_overlapR_start.1⟩

theorem isConnected_blockL : IsConnected (D.blockL i) :=
  D.convex_blockL.isConnected D.blockL_nonempty

theorem isConnected_blockR : IsConnected (D.blockR i) :=
  D.convex_blockR.isConnected D.blockR_nonempty

end StripData

/-! ## Chaining a cyclic family

The union of the left pieces is connected because consecutive pieces overlap. This is a fact
about any cyclically indexed family, and it is worth isolating: it is used once on the left and
once on the right, and it is where the "cyclic" of the blueprint gets examined.

The point to notice is that the closing overlap `F (last) ∩ F 0` is **not used**. A union of
connected sets is connected as soon as the overlap graph is connected, and the path
`0 — 1 — ⋯ — N-1` already spans it; the extra edge back to `0` is a cycle, not a new vertex.
The blueprint's "the labels return consistently after one circuit" is therefore not needed
*here*: it is needed to know that the left label and the right label never collide, which is
`StripData.sideL_disjoint_sideR`, and that is already proved. -/

/-- A cyclically indexed family of connected sets in which every member meets its successor has
connected union. Only the overlaps along the linear chain `0, 1, …, N - 1` are consumed. -/
theorem isConnected_iUnion_zmod {α : Type*} [TopologicalSpace α] {N : ℕ} [NeZero N]
    (F : ZMod N → Set α) (hconn : ∀ i, IsConnected (F i))
    (hmeet : ∀ i, (F i ∩ F (i + 1)).Nonempty) : IsConnected (⋃ i, F i) := by
  -- `chain k` is the union of the pieces with index the cast of some `j ≤ k`.
  set chain : ℕ → Set α := fun k => ⋃ j : ℕ, ⋃ _ : j ≤ k, F (j : ZMod N) with hchain
  have hstep : ∀ k : ℕ, chain (k + 1) = chain k ∪ F ((k + 1 : ℕ) : ZMod N) := by
    intro k
    ext y
    simp only [hchain, Set.mem_iUnion, Set.mem_union, exists_prop]
    constructor
    · rintro ⟨j, hj, hy⟩
      rcases Nat.lt_or_ge j (k + 1) with h | h
      · exact Or.inl ⟨j, Nat.lt_succ_iff.1 h, hy⟩
      · exact Or.inr ((le_antisymm hj h) ▸ hy)
    · rintro (⟨j, hj, hy⟩ | hy)
      · exact ⟨j, le_trans hj (Nat.le_succ k), hy⟩
      · exact ⟨k + 1, le_refl _, hy⟩
  have hzero : chain 0 = F 0 := by
    ext y
    simp only [hchain, Set.mem_iUnion, Nat.le_zero, exists_prop]
    constructor
    · rintro ⟨j, rfl, hy⟩; simpa using hy
    · intro hy; exact ⟨0, rfl, by simpa using hy⟩
  have key : ∀ k : ℕ, IsConnected (chain k) := by
    intro k
    induction k with
    | zero => rw [hzero]; exact hconn 0
    | succ k ih =>
        rw [hstep k]
        refine IsConnected.union ?_ ih (hconn _)
        -- The overlap of the last two links, transported along `((k+1 : ℕ) : ZMod N) = k + 1`.
        obtain ⟨y, hy1, hy2⟩ := hmeet ((k : ℕ) : ZMod N)
        refine ⟨y, ?_, ?_⟩
        · exact Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨le_refl k, hy1⟩⟩
        · rwa [show ((k + 1 : ℕ) : ZMod N) = ((k : ℕ) : ZMod N) + 1 by push_cast; ring]
  have hcover : (⋃ i, F i) = chain (N - 1) := by
    refine Set.Subset.antisymm ?_ ?_
    · refine Set.iUnion_subset fun i y hy => ?_
      have hval : ((i.val : ℕ) : ZMod N) = i := ZMod.natCast_rightInverse i
      have hlt : i.val < N := ZMod.val_lt i
      refine Set.mem_iUnion.2 ⟨i.val, Set.mem_iUnion.2 ⟨by omega, ?_⟩⟩
      rw [hval]
      exact hy
    · refine Set.iUnion_subset fun j => Set.iUnion_subset fun _ => Set.subset_iUnion _ _
  rw [hcover]
  exact key _

namespace StripData

variable {P : ClosedPolygon m} (D : StripData P) {i j : ZMod (m + 3)} {x : Plane}

/-! ### The two sides are connected -/

/-- The left piece at index `i`: the left sector at vertex `i` glued to the left block of the
edge leaving `i`. -/
def pieceL (i : ZMod (m + 3)) : Set Plane := D.sectorL i ∪ D.blockL i

/-- The right piece at index `i`. -/
def pieceR (i : ZMod (m + 3)) : Set Plane := D.sectorR i ∪ D.blockR i

theorem sideL_eq_iUnion : D.sideL = ⋃ i, D.pieceL i := rfl
theorem sideR_eq_iUnion : D.sideR = ⋃ i, D.pieceR i := rfl

/-- A piece is connected: its sector and its block overlap, at `mem_overlapL_start`. -/
theorem isConnected_pieceL : IsConnected (D.pieceL i) :=
  IsConnected.union ⟨_, D.mem_overlapL_start.2, D.mem_overlapL_start.1⟩ D.isConnected_sectorL
    D.isConnected_blockL

theorem isConnected_pieceR : IsConnected (D.pieceR i) :=
  IsConnected.union ⟨_, D.mem_overlapR_start.2, D.mem_overlapR_start.1⟩ D.isConnected_sectorR
    D.isConnected_blockR

/-- Consecutive pieces overlap: the block of edge `i` reaches into the sector at `i + 1`. -/
theorem pieceL_inter_succ_nonempty : (D.pieceL i ∩ D.pieceL (i + 1)).Nonempty :=
  ⟨_, Or.inr D.mem_overlapL_finish.1, Or.inl D.mem_overlapL_finish.2⟩

theorem pieceR_inter_succ_nonempty : (D.pieceR i ∩ D.pieceR (i + 1)).Nonempty :=
  ⟨_, Or.inr D.mem_overlapR_finish.1, Or.inl D.mem_overlapR_finish.2⟩

/-- **The left side of the collar is connected.** -/
theorem isConnected_sideL : IsConnected D.sideL := by
  rw [D.sideL_eq_iUnion]
  exact isConnected_iUnion_zmod _ (fun i => D.isConnected_pieceL)
    (fun i => D.pieceL_inter_succ_nonempty)

/-- **The right side of the collar is connected.** -/
theorem isConnected_sideR : IsConnected D.sideR := by
  rw [D.sideR_eq_iUnion]
  exact isConnected_iUnion_zmod _ (fun i => D.isConnected_pieceR)
    (fun i => D.pieceR_inter_succ_nonempty)

theorem isOpen_sideL : IsOpen D.sideL :=
  isOpen_iUnion fun _ => D.isOpen_sectorL.union D.isOpen_blockL

theorem isOpen_sideR : IsOpen D.sideR :=
  isOpen_iUnion fun _ => D.isOpen_sectorR.union D.isOpen_blockR

/-! ### The collar minus the curve is exactly the two sides

`nbhd` was *defined* as `sideL ∪ sideR ∪ carrier`, so this is only the two disjointness
statements of `Strip.lean` read backwards. -/

/-- **Lemma 1.8 (a), the set equality.** Removing the curve from the collar leaves exactly the
two labelled sides. With `sideL_disjoint_sideR` this is `N \ P = N_L ⊔ N_R`. -/
theorem nbhd_diff_carrier : D.nbhd \ P.carrier = D.sideL ∪ D.sideR := by
  ext y
  constructor
  · rintro ⟨hy, hyc⟩
    rcases hy with h | h
    · exact h
    · exact absurd h hyc
  · intro hy
    refine ⟨Or.inl hy, ?_⟩
    rcases hy with h | h
    · exact fun hc => Set.disjoint_left.1 D.sideL_disjoint_carrier h hc
    · exact fun hc => Set.disjoint_left.1 D.sideR_disjoint_carrier h hc

theorem carrier_subset_nbhd : P.carrier ⊆ D.nbhd := fun _ hy => Or.inr hy

/-! ### The collar is open

`nbhd` contains the curve, so openness is not formal: it has to be exhibited as a union of open
sets. The two families are the vertex balls and the *full* edge tubes — the block of half-width
`rho` on both sides of the trimmed edge, core included. Each of the two is covered by
`nbhd` because its points off the curve are labelled (`ball_diff_carrier_subset`,
`tube_diff_carrier_subset`); conversely they cover `nbhd`, the only nontrivial part being that
they cover the curve itself, which is the three-way split of an edge into "within `R` of the
first vertex", "within `R` of the second", and "in the trimmed middle". -/

/-- The full tube of edge `i`: the trimmed edge thickened by `rho` on both sides. It is the
union of the two blocks with the piece of the edge between them. -/
def tube (i : ZMod (m + 3)) : Set Plane :=
  strip (P.vertex i) (P.tang i) D.lam (P.len i - D.lam) (-D.rho) D.rho

theorem isOpen_tube : IsOpen (D.tube i) := isOpen_strip _ _ _ _ _ _

theorem mem_tube_off {t s : ℝ} : P.off i t s ∈ D.tube i ↔
    D.lam < t ∧ t < P.len i - D.lam ∧ -D.rho < s ∧ s < D.rho := by
  rw [tube, mem_strip_iff, ClosedPolygon.coordAlong_off, ClosedPolygon.coordAcross_off]

theorem blockL_subset_tube : D.blockL i ⊆ D.tube i := by
  intro y hy
  obtain ⟨h1, h2, h3, h4⟩ := D.mem_blockL_iff.1 hy
  exact ⟨h1, h2, by linarith [D.rho_pos], h4⟩

theorem blockR_subset_tube : D.blockR i ⊆ D.tube i := by
  intro y hy
  obtain ⟨h1, h2, h3, h4⟩ := D.mem_blockR_iff.1 hy
  exact ⟨h1, h2, h3, by linarith [D.rho_pos]⟩

/-- **A vertex ball minus the curve is covered by the two sectors at that vertex.** A point of
the ball off the curve points in some direction from the vertex; by `mem_ray_or_mem_arcCCW'`
that direction is either one of the two incident rays — and then the point is *on* the incident
edge, because `R_le_len` says the sector does not run past the far end — or on one of the two
arcs, and then the point is in the corresponding sector. -/
theorem ball_diff_carrier_subset :
    ball (P.vertex i) D.R \ P.carrier ⊆ D.sectorL i ∪ D.sectorR i := by
  rintro y ⟨hy, hyc⟩
  have hne : y - P.vertex i ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    apply hyc
    rw [h]
    exact ClosedPolygon.vertex_mem_carrier
  rcases mem_ray_or_mem_arcCCW' (ClosedPolygon.det_rays_ne_zero (P := P) (i := i)) hne with
    ⟨c, hc, hcy⟩ | ⟨c, hc, hcy⟩ | harc | harc
  · -- Back along the incoming edge: the point lies on edge `i - 1`.
    exfalso
    apply hyc
    have hd : dist y (P.vertex i) = c := by
      rw [dist_eq_norm, hcy, norm_smul, Real.norm_eq_abs,
        ClosedPolygon.isDirection_rayIn.norm, mul_one, abs_of_pos hc]
    rw [mem_ball, hd] at hy
    have hy' : y = P.vertex i + c • P.rayIn i := by rw [← hcy]; module
    rw [hy']
    exact ClosedPolygon.edge_subset_carrier (ClosedPolygon.mem_edge_pred_of_smul_rayIn hc.le
      (le_trans hy.le (D.R_le_len (i - 1))))
  · -- Out along the outgoing edge: the point lies on edge `i`.
    exfalso
    apply hyc
    have hd : dist y (P.vertex i) = c := by
      rw [dist_eq_norm, hcy, norm_smul, Real.norm_eq_abs,
        ClosedPolygon.isDirection_tang.norm, mul_one, abs_of_pos hc]
    rw [mem_ball, hd] at hy
    have hy' : y = P.vertex i + c • P.tang i := by rw [← hcy]; module
    rw [hy']
    exact ClosedPolygon.edge_subset_carrier (ClosedPolygon.mem_edge_of_smul_tang hc.le
      (le_trans hy.le (D.R_le_len i)))
  · exact Or.inr ⟨harc, hy⟩
  · exact Or.inl ⟨harc, hy⟩

/-- **A tube minus the curve is its two blocks.** The only points of a tube on the curve are
those on the core of its own edge. -/
theorem tube_diff_carrier_subset : D.tube i \ P.carrier ⊆ D.blockL i ∪ D.blockR i := by
  rintro y ⟨⟨h1, h2, h3, h4⟩, hyc⟩
  rcases lt_trichotomy (coordAcross (P.vertex i) (P.tang i) y) 0 with h | h | h
  · exact Or.inr (D.mem_blockR_iff.2 ⟨h1, h2, h3, h⟩)
  · exfalso
    apply hyc
    have hy0 : y = P.pt i (coordAlong (P.vertex i) (P.tang i) y) := by
      rw [ClosedPolygon.pt, ← h]
      exact ClosedPolygon.off_coord P i y
    rw [hy0]
    exact ClosedPolygon.edge_subset_carrier (ClosedPolygon.pt_mem_edge
      ⟨by linarith [D.lam_pos], by linarith [D.lam_pos]⟩)
  · exact Or.inl (D.mem_blockL_iff.2 ⟨h1, h2, h, h4⟩)

/-- Each edge is covered by the ball at its first vertex, the ball at its second, and its own
tube: `lam < R` leaves no gap in the middle. -/
theorem carrier_subset_balls_union_tubes :
    P.carrier ⊆ (⋃ i, ball (P.vertex i) D.R) ∪ (⋃ i, D.tube i) := by
  rintro y hy
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
  rw [ClosedPolygon.mem_edge_iff] at hi
  obtain ⟨c, ⟨hc0, hc1⟩, rfl⟩ := hi
  rcases lt_or_ge c D.R with h1 | h1
  · refine Or.inl (Set.mem_iUnion.2 ⟨i, ?_⟩)
    rw [mem_ball, ClosedPolygon.dist_pt_vertex, abs_of_nonneg hc0]
    exact h1
  rcases lt_or_ge (P.len i - D.R) c with h2 | h2
  · refine Or.inl (Set.mem_iUnion.2 ⟨i + 1, ?_⟩)
    rw [mem_ball, ClosedPolygon.dist_pt_vertex_succ, abs_of_nonpos (by linarith)]
    linarith
  · refine Or.inr (Set.mem_iUnion.2 ⟨i, ?_⟩)
    rw [ClosedPolygon.pt]
    have hlam := D.lam_pos
    have hR := D.two_lam_lt_R
    exact D.mem_tube_off.2 ⟨by linarith, by linarith, by linarith [D.rho_pos], D.rho_pos⟩

/-- The collar is the union of the vertex balls and the edge tubes. This is the presentation
that makes it visibly open. -/
theorem nbhd_eq : D.nbhd = (⋃ i, ball (P.vertex i) D.R) ∪ (⋃ i, D.tube i) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro y ((hy | hy) | hy)
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
      rcases hi with hi | hi
      · exact Or.inl (Set.mem_iUnion.2 ⟨i, D.sector_subset_ball hi⟩)
      · exact Or.inr (Set.mem_iUnion.2 ⟨i, D.blockL_subset_tube hi⟩)
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
      rcases hi with hi | hi
      · exact Or.inl (Set.mem_iUnion.2 ⟨i, D.sectorR_subset_ball hi⟩)
      · exact Or.inr (Set.mem_iUnion.2 ⟨i, D.blockR_subset_tube hi⟩)
    · exact D.carrier_subset_balls_union_tubes hy
  · rintro y (hy | hy)
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
      by_cases hc : y ∈ P.carrier
      · exact Or.inr hc
      · rcases D.ball_diff_carrier_subset ⟨hi, hc⟩ with h | h
        · exact Or.inl (Or.inl (Set.mem_iUnion.2 ⟨i, Or.inl h⟩))
        · exact Or.inl (Or.inr (Set.mem_iUnion.2 ⟨i, Or.inl h⟩))
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
      by_cases hc : y ∈ P.carrier
      · exact Or.inr hc
      · rcases D.tube_diff_carrier_subset ⟨hi, hc⟩ with h | h
        · exact Or.inl (Or.inl (Set.mem_iUnion.2 ⟨i, Or.inr h⟩))
        · exact Or.inl (Or.inr (Set.mem_iUnion.2 ⟨i, Or.inr h⟩))

theorem isOpen_nbhd : IsOpen D.nbhd := by
  rw [D.nbhd_eq]
  exact (isOpen_iUnion fun _ => isOpen_ball).union (isOpen_iUnion fun _ => D.isOpen_tube)

/-! ### Lemma 1.8 (a) -/

/-- **Two-sided polygonal strips, the closed case.** Given the constants, the collar of a simple
closed polygon is an open neighbourhood of the curve whose complement in it is the disjoint
union of the two connected open local sides. This is Lemma 1.8 (a) of the blueprint, modulo
`exists_stripData`, which produces the constants. -/
theorem collar :
    IsOpen D.nbhd ∧ P.carrier ⊆ D.nbhd ∧ D.nbhd \ P.carrier = D.sideL ∪ D.sideR ∧
      IsOpen D.sideL ∧ IsOpen D.sideR ∧ IsConnected D.sideL ∧ IsConnected D.sideR ∧
      Disjoint D.sideL D.sideR :=
  ⟨D.isOpen_nbhd, D.carrier_subset_nbhd, D.nbhd_diff_carrier, D.isOpen_sideL, D.isOpen_sideR,
    D.isConnected_sideL, D.isConnected_sideR, D.sideL_disjoint_sideR⟩

/-- The existential form of Lemma 1.8 (a): a simple closed polygonal curve for which the
constants exist has an open neighbourhood `N` with `N \ P` the disjoint union of two connected
open sets. -/
theorem exists_collar (D : StripData P) :
    ∃ N NL NR : Set Plane, IsOpen N ∧ P.carrier ⊆ N ∧ IsOpen NL ∧ IsOpen NR ∧
      IsConnected NL ∧ IsConnected NR ∧ Disjoint NL NR ∧ N \ P.carrier = NL ∪ NR :=
  ⟨D.nbhd, D.sideL, D.sideR, D.isOpen_nbhd, D.carrier_subset_nbhd, D.isOpen_sideL, D.isOpen_sideR,
    D.isConnected_sideL, D.isConnected_sideR, D.sideL_disjoint_sideR, D.nbhd_diff_carrier⟩

end StripData

end Schoenflies

end BundlePart408

section BundlePart409
/- Source: dev/planar_search/schoenflies_port/Schoenflies/StripLocal.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/



/-!
# The local two-sidedness assertion of Lemma 1.8

`Schoenflies/Strip.lean`, `Schoenflies/StripConstants.lean` and `Schoenflies/StripConnected.lean`
build the collar of a simple closed polygon and prove the *global* half of Lemma 1.8 (a): the
collar minus the curve is the disjoint union of two connected open sets. This module adds the
*local* half, the sentence of the blueprint that begins "In either case the two sets `N_L`, `N_R`
are the two local sides of the curve in the following precise sense".

Two statements come out of it, and they are the two the polygonal Jordan curve theorem consumes.

* `Schoenflies.StripData.local_two_sided` and its packaging
  `Schoenflies.StripData.exists_reference_points`: a small enough disk about a point of the
  *relative interior* of an edge meets the polygon exactly in that edge, and the rest of the disk
  is the two open half-disks, one in each side. This is what supplies the two reference points
  `z_L`, `z_R` of the parity argument, together with the fact that they are separated by a single
  crossing of the curve.
* `Schoenflies.StripData.carrier_subset_closure_sideL` and `…_sideR`: every point of the polygon
  is in the closure of both sides. With `StripData.sideL_disjoint_carrier` this says the polygon
  is contained in the boundary of each side, which is what turns "there are exactly two regions"
  into "both regions have boundary `C`".

## What is proved, and how

The disk argument along an edge is `StripData.core_ball_trichotomy`: both frame coordinates are
`1`-Lipschitz, so a ball of radius at most `min lam rho` about a point of the middle stretch of
an edge cannot leave the block range in the longitudinal coordinate nor the block width in the
transverse one; the sign of the transverse coordinate then reads off which of the three pieces —
left block, edge, right block — the point is in.

Approaching a point of the polygon from a given side is `StripData.exists_near_sides`. Away from
the vertices the block does it. Near a vertex the block is not available (it stops short by
`lam`), and the approach is through the *sector*, reached by shrinking the transverse offset with
the longitudinal one held fixed: the germ lemmas `ClosedPolygon.off_sub_mem_arcL_start` and
friends need only that the offset be small against the progress, so at a point at distance `t > 0`
from the vertex any offset below `t · |det| / (1 + |⟪·,·⟫|)` works. At the vertex itself neither
is available and the approach is instead by shrinking a point of the sector towards the vertex,
which stays in the sector because an arc of directions is a cone (`Plane.smul_mem_arcCCW`).

## Blueprint

* `Schoenflies.StripData.local_two_sided`, `Schoenflies.StripData.exists_reference_points` —
  Lemma 1.8, the local two-sidedness assertion, along the relative interior of an edge.
* `Schoenflies.StripData.carrier_subset_closure_sideL`, `…_sideR` — the consequence of it used
  for "both regions have boundary `C`".
* `Schoenflies.ClosedPolygon.exists_two_sided_collar` — Lemma 1.8 (a) with those two clauses
  added, in existential form.

The local two-sidedness assertion *at a vertex* is not proved here; see the module note at the
end.
-/

open Metric Set

namespace Schoenflies

namespace Plane

variable {u w : Plane}

/-- The origin is on no arc: the arcs are open arcs of *directions*. -/
theorem zero_notMem_arcCCW (u w : Plane) : (0 : Plane) ∉ arcCCW u w := by
  have h := (notMem_arcCCW_smul u w (le_refl (0 : ℝ))).1
  rwa [zero_smul] at h

end Plane

open Plane

variable {m : ℕ}

namespace ClosedPolygon

variable {P : ClosedPolygon m} {i : ZMod (m + 3)} {t s : ℝ}

/-- Seen from the vertex it arrives at, a frame position of edge `i` is a germ at the incoming
ray there. This is the companion of `ClosedPolygon.off_sub_vertex`, which does the same at the
vertex the edge leaves. -/
theorem off_sub_vertex_succ_ray : P.off i t s - P.vertex (i + 1) =
    (P.len i - t) • P.rayIn (i + 1) - s • perp (P.rayIn (i + 1)) := by
  have hr : P.rayIn (i + 1) = -P.tang i := rayIn_succ
  have hp : perp (-P.tang i) = -perp (P.tang i) := by ext k; fin_cases k <;> simp [perp]
  rw [off_sub_vertex_succ, hr, hp]
  module

/-! ### The four germs, for an arbitrary frame position

`StripData.blockL_sub_mem_arcL_start` and its three companions apply `Plane.germs_split'` to a
point of a *block*, where the smallness of the offset comes from the `germ` field of the
`StripData`. The four lemmas here are the same projections with the smallness left as a
hypothesis, which is what an approach to a point of the curve needs: there the progress `t` is
fixed by the point being approached and only the offset shrinks. -/

theorem off_sub_mem_arcL_start (hs : 0 < s)
    (hsm : s * |inner ℝ (P.rayIn i) (P.tang i)| < t * |det (P.rayIn i) (P.tang i)|) :
    P.off i t s - P.vertex i ∈ arcCCW (P.tang i) (P.rayIn i) := by
  rw [off_sub_vertex]
  exact (germs_split' det_rays_ne_zero hs hsm).1.2

theorem off_sub_mem_arcR_start (hs : s < 0)
    (hsm : (-s) * |inner ℝ (P.rayIn i) (P.tang i)| < t * |det (P.rayIn i) (P.tang i)|) :
    P.off i t s - P.vertex i ∈ arcCCW (P.rayIn i) (P.tang i) := by
  have h : P.off i t s - P.vertex i = t • P.tang i - (-s) • perp (P.tang i) := by
    rw [off_sub_vertex]; module
  rw [h]
  exact (germs_split' det_rays_ne_zero (by linarith) hsm).2.2

theorem off_sub_mem_arcL_finish (hs : 0 < s)
    (hsm : s * |inner ℝ (P.rayIn (i + 1)) (P.tang (i + 1))| <
      (P.len i - t) * |det (P.rayIn (i + 1)) (P.tang (i + 1))|) :
    P.off i t s - P.vertex (i + 1) ∈ arcCCW (P.tang (i + 1)) (P.rayIn (i + 1)) := by
  rw [off_sub_vertex_succ_ray]
  exact (germs_split' det_rays_ne_zero hs hsm).1.1

theorem off_sub_mem_arcR_finish (hs : s < 0)
    (hsm : (-s) * |inner ℝ (P.rayIn (i + 1)) (P.tang (i + 1))| <
      (P.len i - t) * |det (P.rayIn (i + 1)) (P.tang (i + 1))|) :
    P.off i t s - P.vertex (i + 1) ∈ arcCCW (P.rayIn (i + 1)) (P.tang (i + 1)) := by
  have h : P.off i t s - P.vertex (i + 1) =
      (P.len i - t) • P.rayIn (i + 1) + (-s) • perp (P.rayIn (i + 1)) := by
    rw [off_sub_vertex_succ_ray]; module
  rw [h]
  exact (germs_split' det_rays_ne_zero (by linarith) hsm).2.1

/-- Offsetting a point of an edge moves it exactly the offset. -/
theorem dist_off_pt : dist (P.off i t s) (P.pt i t) = |s| := by
  rw [ClosedPolygon.pt, dist_eq_norm, show P.off i t s - P.off i t 0 = s • perp (P.tang i) by
    rw [off, off]; module, norm_smul, Real.norm_eq_abs, norm_perp, isDirection_tang.norm,
    mul_one]

end ClosedPolygon

/-- One positive number below several prescribed thresholds at once. Used to offset a point of an
edge by less than the germ threshold at both of its endpoints, less than the block half-width and
less than a prescribed accuracy. -/
private theorem exists_common_bound {a b X₁ X₂ K₁ K₂ Y : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) (hY : 0 < Y) :
    ∃ σ : ℝ, 0 < σ ∧ σ < a ∧ σ < b ∧ σ * K₁ ≤ X₁ ∧ σ * K₂ ≤ X₂ ∧ σ < Y := by
  refine ⟨min (min (a / 2) (b / 2)) (min (min (X₁ / K₁) (X₂ / K₂)) (Y / 2)),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [lt_min_iff, lt_min_iff, lt_min_iff, lt_min_iff]
    exact ⟨⟨by linarith, by linarith⟩, ⟨div_pos hX₁ hK₁, div_pos hX₂ hK₂⟩, by linarith⟩
  · exact lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_left _ _)) (by linarith)
  · exact lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_right _ _)) (by linarith)
  · have h : min (min (a / 2) (b / 2)) (min (min (X₁ / K₁) (X₂ / K₂)) (Y / 2)) ≤ X₁ / K₁ :=
      le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
    have h2 := mul_le_mul_of_nonneg_right h hK₁.le
    rwa [div_mul_cancel₀ _ hK₁.ne'] at h2
  · have h : min (min (a / 2) (b / 2)) (min (min (X₁ / K₁) (X₂ / K₂)) (Y / 2)) ≤ X₂ / K₂ :=
      le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
    have h2 := mul_le_mul_of_nonneg_right h hK₂.le
    rwa [div_mul_cancel₀ _ hK₂.ne'] at h2
  · exact lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_right _ _)) (by linarith)

namespace StripData

variable {P : ClosedPolygon m} (D : StripData P) {i : ZMod (m + 3)}

/-! ### The disk about a point in the middle of an edge -/

/-- **The local picture along an edge.** A ball of radius at most `min lam rho` about a point of
the middle stretch of an edge is split by the sign of the transverse coordinate: positive is the
left block, negative the right block, zero the edge itself. Both coordinates are `1`-Lipschitz,
which is the whole proof. -/
theorem core_ball_trichotomy {c η : ℝ} (h1 : 2 * D.lam ≤ c) (h2 : c ≤ P.len i - 2 * D.lam)
    (hη : η ≤ min D.lam D.rho) {y : Plane} (hy0 : y ∈ ball (P.pt i c) η) :
    (0 < coordAcross (P.vertex i) (P.tang i) y → y ∈ D.blockL i) ∧
      (coordAcross (P.vertex i) (P.tang i) y < 0 → y ∈ D.blockR i) ∧
      (coordAcross (P.vertex i) (P.tang i) y = 0 → y ∈ P.edge i) := by
  have hy : dist y (P.pt i c) < min D.lam D.rho := lt_of_lt_of_le (mem_ball.1 hy0) hη
  set t := coordAlong (P.vertex i) (P.tang i) y with ht
  set σ := coordAcross (P.vertex i) (P.tang i) y with hσ
  have hyeq : y = P.off i t σ := ClosedPolygon.off_coord P i y
  have hpt : P.pt i c = P.off i c 0 := rfl
  have hta : |t - c| ≤ dist y (P.pt i c) := by
    have h := abs_coordAlong_sub_le (u := P.tang i) ClosedPolygon.isDirection_tang (P.vertex i) y
      (P.pt i c)
    rw [hpt, ClosedPolygon.coordAlong_off] at h
    exact h
  have hsa : |σ| ≤ dist y (P.pt i c) := by
    have h := abs_coordAcross_sub_le (u := P.tang i) ClosedPolygon.isDirection_tang (P.vertex i) y
      (P.pt i c)
    rw [hpt, ClosedPolygon.coordAcross_off, sub_zero] at h
    exact h
  have hlam : dist y (P.pt i c) < D.lam := lt_of_lt_of_le hy (min_le_left _ _)
  have hrho : dist y (P.pt i c) < D.rho := lt_of_lt_of_le hy (min_le_right _ _)
  have htlow : D.lam < t := by
    have h := abs_lt.1 (lt_of_le_of_lt hta hlam)
    linarith [h.1]
  have hthigh : t < P.len i - D.lam := by
    have h := abs_lt.1 (lt_of_le_of_lt hta hlam)
    linarith [h.2]
  refine ⟨fun hs => ?_, fun hs => ?_, fun hs => ?_⟩
  · rw [hyeq]
    exact D.mem_blockL_off.2 ⟨htlow, hthigh, hs, by
      have h := abs_lt.1 (lt_of_le_of_lt hsa hrho); linarith [h.2]⟩
  · rw [hyeq]
    exact D.mem_blockR_off.2 ⟨htlow, hthigh, by
      have h := abs_lt.1 (lt_of_le_of_lt hsa hrho); linarith [h.1], hs⟩
  · rw [hyeq, hs, ← ClosedPolygon.pt]
    exact ClosedPolygon.pt_mem_edge ⟨by linarith [D.lam_pos], by linarith [D.lam_pos]⟩

/-- **Local two-sidedness at an interior point of an edge.** A small enough disk about a point in
the middle stretch of an edge meets the polygon exactly in that edge; off the edge the disk lies
in the two blocks, one on each side; and both sides are met, at the two points obtained by
offsetting the centre. -/
theorem local_two_sided {c η : ℝ} (h1 : 2 * D.lam ≤ c) (h2 : c ≤ P.len i - 2 * D.lam)
    (hηpos : 0 < η) (hη : η ≤ min D.lam D.rho) :
    ball (P.pt i c) η ∩ P.carrier ⊆ P.edge i ∧
      (∀ y ∈ ball (P.pt i c) η, y ∉ P.carrier →
        (0 < coordAcross (P.vertex i) (P.tang i) y ∧ y ∈ D.sideL) ∨
          (coordAcross (P.vertex i) (P.tang i) y < 0 ∧ y ∈ D.sideR)) ∧
      P.off i c (η / 2) ∈ ball (P.pt i c) η ∩ D.sideL ∧
      P.off i c (-(η / 2)) ∈ ball (P.pt i c) η ∩ D.sideR := by
  have hsplit : ∀ y ∈ ball (P.pt i c) η,
      (0 < coordAcross (P.vertex i) (P.tang i) y → y ∈ D.sideL) ∧
        (coordAcross (P.vertex i) (P.tang i) y < 0 → y ∈ D.sideR) ∧
        (coordAcross (P.vertex i) (P.tang i) y = 0 → y ∈ P.edge i) := by
    intro y hy
    obtain ⟨hL, hR, hE⟩ := D.core_ball_trichotomy h1 h2 hη hy
    exact ⟨fun hs => Set.mem_iUnion.2 ⟨i, Or.inr (hL hs)⟩,
      fun hs => Set.mem_iUnion.2 ⟨i, Or.inr (hR hs)⟩, hE⟩
  have hball : ∀ σ : ℝ, |σ| < η → P.off i c σ ∈ ball (P.pt i c) η := by
    intro σ hσ
    rw [mem_ball, ClosedPolygon.dist_off_pt]
    exact hσ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro y ⟨hy, hyc⟩
    rcases lt_trichotomy (coordAcross (P.vertex i) (P.tang i) y) 0 with hs | hs | hs
    · exact absurd hyc (Set.disjoint_left.1 D.sideR_disjoint_carrier ((hsplit y hy).2.1 hs))
    · exact (hsplit y hy).2.2 hs
    · exact absurd hyc (Set.disjoint_left.1 D.sideL_disjoint_carrier ((hsplit y hy).1 hs))
  · intro y hy hyc
    rcases lt_trichotomy (coordAcross (P.vertex i) (P.tang i) y) 0 with hs | hs | hs
    · exact Or.inr ⟨hs, (hsplit y hy).2.1 hs⟩
    · exact absurd (ClosedPolygon.edge_subset_carrier ((hsplit y hy).2.2 hs)) hyc
    · exact Or.inl ⟨hs, (hsplit y hy).1 hs⟩
  · have hmem := hball (η / 2) (by rw [abs_of_pos (by linarith)]; linarith)
    refine ⟨hmem, (hsplit _ hmem).1 ?_⟩
    rw [ClosedPolygon.coordAcross_off]
    linarith
  · have hmem := hball (-(η / 2)) (by rw [abs_of_neg (by linarith)]; linarith)
    refine ⟨hmem, (hsplit _ hmem).2.1 ?_⟩
    rw [ClosedPolygon.coordAcross_off]
    linarith

/-- **The two reference points of the parity argument.** On every edge there is a disk that meets
the polygon only in that edge and contains a point of each side, on the two sides of the edge's
line. A horizontal segment joining the two crosses the polygon exactly once, which is what makes
the two reference points have opposite parity. -/
theorem exists_reference_points (i : ZMod (m + 3)) :
    ∃ (p : Plane) (η : ℝ), 0 < η ∧ p ∈ P.edge i ∧ ball p η ∩ P.carrier ⊆ P.edge i ∧
      (∃ zL ∈ ball p η, zL ∈ D.sideL ∧ 0 < coordAcross (P.vertex i) (P.tang i) zL) ∧
      (∃ zR ∈ ball p η, zR ∈ D.sideR ∧ coordAcross (P.vertex i) (P.tang i) zR < 0) := by
  have h4 := D.four_lam_lt_len i
  have hl := D.lam_pos
  have hlow : 2 * D.lam ≤ P.len i / 2 := by linarith
  have hhigh : P.len i / 2 ≤ P.len i - 2 * D.lam := by linarith
  have hηpos : 0 < min D.lam D.rho := lt_min hl D.rho_pos
  obtain ⟨h1, -, ⟨hbL, hsL⟩, ⟨hbR, hsR⟩⟩ :=
    D.local_two_sided (i := i) hlow hhigh hηpos (le_refl _)
  refine ⟨P.pt i (P.len i / 2), min D.lam D.rho, hηpos,
    ClosedPolygon.pt_mem_edge ⟨by linarith, by linarith⟩, h1, ⟨_, hbL, hsL, ?_⟩,
    ⟨_, hbR, hsR, ?_⟩⟩
  · rw [ClosedPolygon.coordAcross_off]; linarith
  · rw [ClosedPolygon.coordAcross_off]; linarith

/-! ### Every point of the polygon is on the boundary of both sides -/

/-- A sector comes arbitrarily close to its vertex: shrink a point of it towards the vertex, which
stays in the arc because an arc of directions is a cone. -/
theorem exists_near_sectorL {ε : ℝ} (hε : 0 < ε) (i : ZMod (m + 3)) :
    ∃ y ∈ D.sectorL i, dist y (P.vertex i) < ε := by
  obtain ⟨z, hz⟩ := (D.isConnected_sectorL (i := i)).nonempty
  have harc : z - P.vertex i ∈ arcCCW (P.tang i) (P.rayIn i) := hz.1
  have hwne : z - P.vertex i ≠ 0 := fun h => zero_notMem_arcCCW _ _ (h ▸ harc)
  have hwpos : 0 < ‖z - P.vertex i‖ := norm_pos_iff.2 hwne
  have hzR : ‖z - P.vertex i‖ < D.R := by rw [← dist_eq_norm]; exact hz.2
  refine ⟨P.vertex i + (min 1 (ε / (2 * ‖z - P.vertex i‖))) • (z - P.vertex i), ⟨?_, ?_⟩, ?_⟩ <;>
    (have hδpos : 0 < min 1 (ε / (2 * ‖z - P.vertex i‖)) := lt_min one_pos (by positivity)
     have hsub : P.vertex i + (min 1 (ε / (2 * ‖z - P.vertex i‖))) • (z - P.vertex i) -
         P.vertex i = (min 1 (ε / (2 * ‖z - P.vertex i‖))) • (z - P.vertex i) := by module)
  · rw [Set.mem_setOf_eq, hsub]
    exact (smul_mem_arcCCW hδpos).2 harc
  · rw [mem_ball, dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hδpos]
    have h1 : min 1 (ε / (2 * ‖z - P.vertex i‖)) ≤ 1 := min_le_left _ _
    nlinarith
  · rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hδpos]
    have h2 : min 1 (ε / (2 * ‖z - P.vertex i‖)) ≤ ε / (2 * ‖z - P.vertex i‖) := min_le_right _ _
    have hkey : ε / (2 * ‖z - P.vertex i‖) * ‖z - P.vertex i‖ = ε / 2 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_right h2 hwpos.le]

theorem exists_near_sectorR {ε : ℝ} (hε : 0 < ε) (i : ZMod (m + 3)) :
    ∃ y ∈ D.sectorR i, dist y (P.vertex i) < ε := by
  obtain ⟨z, hz⟩ := (D.isConnected_sectorR (i := i)).nonempty
  have harc : z - P.vertex i ∈ arcCCW (P.rayIn i) (P.tang i) := hz.1
  have hwne : z - P.vertex i ≠ 0 := fun h => zero_notMem_arcCCW _ _ (h ▸ harc)
  have hwpos : 0 < ‖z - P.vertex i‖ := norm_pos_iff.2 hwne
  have hzR : ‖z - P.vertex i‖ < D.R := by rw [← dist_eq_norm]; exact hz.2
  refine ⟨P.vertex i + (min 1 (ε / (2 * ‖z - P.vertex i‖))) • (z - P.vertex i), ⟨?_, ?_⟩, ?_⟩ <;>
    (have hδpos : 0 < min 1 (ε / (2 * ‖z - P.vertex i‖)) := lt_min one_pos (by positivity)
     have hsub : P.vertex i + (min 1 (ε / (2 * ‖z - P.vertex i‖))) • (z - P.vertex i) -
         P.vertex i = (min 1 (ε / (2 * ‖z - P.vertex i‖))) • (z - P.vertex i) := by module)
  · rw [Set.mem_setOf_eq, hsub]
    exact (smul_mem_arcCCW hδpos).2 harc
  · rw [mem_ball, dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hδpos]
    have h1 : min 1 (ε / (2 * ‖z - P.vertex i‖)) ≤ 1 := min_le_left _ _
    nlinarith
  · rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hδpos]
    have h2 : min 1 (ε / (2 * ‖z - P.vertex i‖)) ≤ ε / (2 * ‖z - P.vertex i‖) := min_le_right _ _
    have hkey : ε / (2 * ‖z - P.vertex i‖) * ‖z - P.vertex i‖ = ε / 2 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_right h2 hwpos.le]

/-- **Both sides come arbitrarily close to every point of the polygon.** Away from the vertices
this is the block; at a vertex it is `exists_near_sectorL`; in between it is the germ with the
progress held fixed and the offset shrunk below the corner's threshold. -/
theorem exists_near_sides {x : Plane} (hx : x ∈ P.carrier) {ε : ℝ} (hε : 0 < ε) :
    (∃ y ∈ D.sideL, dist x y < ε) ∧ (∃ y ∈ D.sideR, dist x y < ε) := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
  obtain ⟨c, ⟨hc0, hc1⟩, rfl⟩ := ClosedPolygon.mem_edge_iff.1 hi
  rcases eq_or_lt_of_le hc0 with hc0' | hc0'
  · -- the initial vertex
    rw [← hc0', ClosedPolygon.pt_zero]
    obtain ⟨y, hy, hd⟩ := D.exists_near_sectorL hε i
    obtain ⟨y', hy', hd'⟩ := D.exists_near_sectorR hε i
    exact ⟨⟨y, Set.mem_iUnion.2 ⟨i, Or.inl hy⟩, by rw [dist_comm]; exact hd⟩,
      ⟨y', Set.mem_iUnion.2 ⟨i, Or.inl hy'⟩, by rw [dist_comm]; exact hd'⟩⟩
  rcases eq_or_lt_of_le hc1 with hc1' | hc1'
  · -- the terminal vertex
    rw [hc1', ClosedPolygon.pt_len]
    obtain ⟨y, hy, hd⟩ := D.exists_near_sectorL hε (i + 1)
    obtain ⟨y', hy', hd'⟩ := D.exists_near_sectorR hε (i + 1)
    exact ⟨⟨y, Set.mem_iUnion.2 ⟨i + 1, Or.inl hy⟩, by rw [dist_comm]; exact hd⟩,
      ⟨y', Set.mem_iUnion.2 ⟨i + 1, Or.inl hy'⟩, by rw [dist_comm]; exact hd'⟩⟩
  -- an interior point of the edge: offset it, by less than every threshold at once
  have hL₁ : 0 < |det (P.rayIn i) (P.tang i)| := abs_pos.2 ClosedPolygon.det_rays_ne_zero
  have hL₂ : 0 < |det (P.rayIn (i + 1)) (P.tang (i + 1))| :=
    abs_pos.2 ClosedPolygon.det_rays_ne_zero
  have hK₁ : (0 : ℝ) < 1 + |inner ℝ (P.rayIn i) (P.tang i)| := by positivity
  have hK₂ : (0 : ℝ) < 1 + |inner ℝ (P.rayIn (i + 1)) (P.tang (i + 1))| := by positivity
  have hRlam : D.lam < D.R := by have := D.lam_pos; linarith [D.two_lam_lt_R]
  obtain ⟨σ, hσpos, hσε, hσrho, hσ1, hσ2, hσR⟩ := exists_common_bound hε D.rho_pos
    (mul_pos hc0' hL₁) (mul_pos (show (0:ℝ) < P.len i - c by linarith) hL₂) hK₁ hK₂
    (show (0:ℝ) < D.R - D.lam by linarith)
  have hg1 : σ * |inner ℝ (P.rayIn i) (P.tang i)| < c * |det (P.rayIn i) (P.tang i)| := by
    nlinarith
  have hg2 : σ * |inner ℝ (P.rayIn (i + 1)) (P.tang (i + 1))| <
      (P.len i - c) * |det (P.rayIn (i + 1)) (P.tang (i + 1))| := by nlinarith
  have hdistL : dist (P.pt i c) (P.off i c σ) < ε := by
    rw [dist_comm, ClosedPolygon.dist_off_pt, abs_of_pos hσpos]; linarith
  have hdistR : dist (P.pt i c) (P.off i c (-σ)) < ε := by
    rw [dist_comm, ClosedPolygon.dist_off_pt, abs_of_neg (by linarith : -σ < 0)]; linarith
  by_cases hmid : D.lam < c ∧ c < P.len i - D.lam
  · -- the block does it
    exact ⟨⟨P.off i c σ, Set.mem_iUnion.2 ⟨i, Or.inr
        (D.mem_blockL_off.2 ⟨hmid.1, hmid.2, hσpos, hσrho⟩)⟩, hdistL⟩,
      ⟨P.off i c (-σ), Set.mem_iUnion.2 ⟨i, Or.inr
        (D.mem_blockR_off.2 ⟨hmid.1, hmid.2, by linarith, by linarith⟩)⟩, hdistR⟩⟩
  push Not at hmid
  by_cases hnear : c ≤ D.lam
  · -- near the initial vertex: the sector there, reached by the germ
    have hdv : ∀ τ : ℝ, |τ| ≤ σ → dist (P.off i c τ) (P.vertex i) < D.R := by
      intro τ hτ
      have h := ClosedPolygon.dist_off_vertex_le (P := P) (i := i) (t := c) (s := τ)
      rw [abs_of_pos hc0'] at h
      linarith
    refine ⟨⟨P.off i c σ, Set.mem_iUnion.2 ⟨i, Or.inl
        ⟨ClosedPolygon.off_sub_mem_arcL_start hσpos hg1,
          hdv σ (by rw [abs_of_pos hσpos])⟩⟩, hdistL⟩,
      ⟨P.off i c (-σ), Set.mem_iUnion.2 ⟨i, Or.inl
        ⟨ClosedPolygon.off_sub_mem_arcR_start (by linarith) (by rw [neg_neg]; exact hg1),
          hdv (-σ) (by rw [abs_of_neg (by linarith : -σ < 0), neg_neg])⟩⟩, hdistR⟩⟩
  · -- near the terminal vertex
    push Not at hnear
    have hfar : P.len i - c ≤ D.lam := by have h := hmid hnear; linarith
    have hdv : ∀ τ : ℝ, |τ| ≤ σ → dist (P.off i c τ) (P.vertex (i + 1)) < D.R := by
      intro τ hτ
      have h := ClosedPolygon.dist_off_vertex_succ_le (P := P) (i := i) (t := c) (s := τ)
      rw [abs_sub_comm, abs_of_pos (by linarith : (0:ℝ) < P.len i - c)] at h
      linarith
    refine ⟨⟨P.off i c σ, Set.mem_iUnion.2 ⟨i + 1, Or.inl
        ⟨ClosedPolygon.off_sub_mem_arcL_finish hσpos hg2,
          hdv σ (by rw [abs_of_pos hσpos])⟩⟩, hdistL⟩,
      ⟨P.off i c (-σ), Set.mem_iUnion.2 ⟨i + 1, Or.inl
        ⟨ClosedPolygon.off_sub_mem_arcR_finish (by linarith) (by rw [neg_neg]; exact hg2),
          hdv (-σ) (by rw [abs_of_neg (by linarith : -σ < 0), neg_neg])⟩⟩, hdistR⟩⟩

/-- Every point of the polygon is in the closure of the left side. With
`StripData.sideL_disjoint_carrier` this says the polygon is contained in the boundary of the left
side. -/
theorem carrier_subset_closure_sideL : P.carrier ⊆ closure D.sideL := by
  intro x hx
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨⟨y, hy, hd⟩, -⟩ := D.exists_near_sides hx hε
  exact ⟨y, hy, hd⟩

theorem carrier_subset_closure_sideR : P.carrier ⊆ closure D.sideR := by
  intro x hx
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨-, ⟨y, hy, hd⟩⟩ := D.exists_near_sides hx hε
  exact ⟨y, hy, hd⟩

end StripData

/-- **Lemma 1.8 (a), with the boundary clause.** A simple closed polygon has an open neighbourhood
`N`, inside any prescribed open set containing it, whose complement in `N` is the disjoint union
of two connected open sets, each of which has the polygon in its closure. -/
theorem ClosedPolygon.exists_two_sided_collar (P : ClosedPolygon m) {U : Set Plane}
    (hU : IsOpen U) (hPU : P.carrier ⊆ U) :
    ∃ N NL NR : Set Plane, IsOpen N ∧ P.carrier ⊆ N ∧ N ⊆ U ∧ IsOpen NL ∧ IsOpen NR ∧
      IsConnected NL ∧ IsConnected NR ∧ Disjoint NL NR ∧ N \ P.carrier = NL ∪ NR ∧
      P.carrier ⊆ closure NL ∧ P.carrier ⊆ closure NR := by
  obtain ⟨D, hD⟩ := exists_stripData_subset P hU hPU
  exact ⟨D.nbhd, D.sideL, D.sideR, D.isOpen_nbhd, D.carrier_subset_nbhd, hD, D.isOpen_sideL,
    D.isOpen_sideR, D.isConnected_sideL, D.isConnected_sideR, D.sideL_disjoint_sideR,
    D.nbhd_diff_carrier, D.carrier_subset_closure_sideL, D.carrier_subset_closure_sideR⟩

/-!
## What is still missing from Lemma 1.8

Two things.

* The local two-sidedness assertion *at a vertex*. `StripData.ball_diff_carrier_subset` already
  says that a ball of radius `R` about a vertex minus the polygon lies in the two sectors there,
  and `StripData.sectorL_disjoint_sectorR` (through `sideL_disjoint_sideR`) says those are
  disjoint; what is not proved is that each of the two intersections
  `ball (P.vertex i) η ∩ sectorL i` is *connected*, i.e. that the ball minus the curve has
  exactly two components at a vertex rather than merely being covered by two disjoint open sets.
  For a ball of radius `η ≤ R` this is true and the proof is the one in
  `Plane.isConnected_arcCCW_ball`, since `ball (P.vertex i) η ∩ sectorL i = cone (P.vertex i) A η`
  for the same arc `A`. Nothing in the polygonal Jordan curve theorem needs it.
* Lemma 1.8 (b), the case of a polygonal *arc* with a compact subarc of its interior. The blocks
  and sectors here are built from a cyclic vertex family; the arc case needs the same
  construction along a linear chain, with the two end cross-sections and no cap. None of it is
  formalised.
-/

end Schoenflies

end BundlePart409

section BundlePart410
/- Source: dev/planar_search/schoenflies_port/Schoenflies/CrosscutCells.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/




/-!
# Separating curves, absorption, and the two cells of a crosscut

Definition 2.4 calls a Jordan curve *separating* when its complement has exactly two regions,
one bounded and one unbounded, each with the curve as its boundary. Everything Part I proves
about a polygonal curve and Part II proves about a general one is packaged in that single
predicate, and the two lemmas below are the ones needed on both sides of the divide: they are
proved from the definition alone.

## The interface: `inside` and `outside` are total functions

The blueprint writes `Int(C)` and `Ext(C)` for the two regions and its consumers — the two
crosscut theorems — name them in their *statements*. So the two regions must be functions of
`C`, not sets produced by an existential inside the definition of separation. They are defined
here for an arbitrary set: `inside C` is the union of the bounded components of the complement
and `outside C` the union of the unbounded ones; together they partition `Cᶜ`.
Separation is then the assertion that each of the two halves is *one* region with boundary `C`
(Definition 2.4); that one is bounded and the other unbounded is then automatic, and so is
"exactly two regions", since a connected clopen piece of `Cᶜ` is a component of it.

`IsRegionOf C Ω` says `Ω` is one of the two, and `IsRegionPair C Ω Ω'` that `Ω, Ω'` are the two
in one order or the other. That is what lets Lemma 2.6 be stated once instead of twice: the
blueprint's `Ω` is sometimes `Int(C)` and sometimes `Ext(C)`, and every step of its proof is
symmetric in that choice.

## What the crosscut lemma actually needs

Lemma 2.6 is stated for a crosscut `P` of a separating curve `C` with arcs `A₁, A₂`, but its
proof never uses that `P` and the `Aᵢ` are arcs, nor the endpoints `p, q`, nor even that
`C = A₁ ∪ A₂`. What it uses is: `Aᵢ ⊆ C`, `P ∩ C ⊆ Aᵢ` (the crosscut meets the curve only in
the shared endpoints, which lie on both arcs), `Jᵢ = Aᵢ ∪ P` separating, and `A₁ ≠ A₂`. The
lemmas below are therefore stated at that level of generality, with `arcs_ne` supplying
`A₁ ≠ A₂` from the arc picture and `isJordanCurve_union` supplying the sentence "these are
Jordan curves" from `IsJordanCurve.of_two_arcs`.

One further hypothesis of the blueprint is dropped: `Ω` is described there as the region
containing `P ∖ {p, q}`, but what actually pins the roles of `Ω`, `Ω†`, `Wᵢ` and `Vᵢ` is the
inclusion `Ω† ⊆ Wᵢ`, which is a hypothesis here. A consumer supplies it by
`IsSeparating.exists_isRegionPair_subset`, which is the formal content of the blueprint's
"being connected it lies in one region of `ℝ² ∖ Jᵢ`, so `Wᵢ` and `Vᵢ` are well defined".

## Blueprint

* `inside`, `outside`, `IsSeparating` — Definition 2.4 (separating Jordan curve).
* `IsSeparating.absorption` — Lemma 2.5 (absorption).
* `crosscut_cells` — Lemma 2.6 (crosscut cells), all three parts, with the per-part lemmas
  `cell_subset_region_diff`, `cell_isComponent`, `closure_cell_inter_curve` stated separately
  because the bundled form carries the hypotheses of both indices at once.
-/

open Bornology Set

namespace Schoenflies

variable {C J P A A₁ A₂ Ω Ω' W V : Set Plane} {x p q : Plane}

/-! ### The inside and the outside of a set

Both are defined for an arbitrary set, without any separation hypothesis: `inside C` collects
the points whose component in the complement is bounded, `outside C` the rest of the
complement. -/

/-- The union of the bounded components of the complement — the blueprint's `Int(C)` once `C`
is known to be separating. -/
def inside (C : Set Plane) : Set Plane :=
  {x | x ∉ C ∧ IsBounded (connectedComponentIn Cᶜ x)}

/-- The union of the unbounded components of the complement — the blueprint's `Ext(C)` once `C`
is known to be separating. -/
def outside (C : Set Plane) : Set Plane :=
  {x | x ∉ C ∧ ¬ IsBounded (connectedComponentIn Cᶜ x)}

theorem mem_inside_iff : x ∈ inside C ↔ x ∉ C ∧ IsBounded (connectedComponentIn Cᶜ x) := Iff.rfl

theorem mem_outside_iff : x ∈ outside C ↔ x ∉ C ∧ ¬ IsBounded (connectedComponentIn Cᶜ x) :=
  Iff.rfl

theorem inside_subset_compl : inside C ⊆ Cᶜ := fun _ hx => hx.1

theorem outside_subset_compl : outside C ⊆ Cᶜ := fun _ hx => hx.1

theorem inside_union_outside (C : Set Plane) : inside C ∪ outside C = Cᶜ := by
  ext z
  constructor
  · rintro (⟨hz, -⟩ | ⟨hz, -⟩) <;> exact hz
  · intro hz
    by_cases hb : IsBounded (connectedComponentIn Cᶜ z)
    · exact Or.inl ⟨hz, hb⟩
    · exact Or.inr ⟨hz, hb⟩

theorem disjoint_inside_outside : Disjoint (inside C) (outside C) := by
  rw [Set.disjoint_left]
  rintro z ⟨-, hb⟩ ⟨-, hb'⟩
  exact hb' hb

/-- Boundedness of the component is constant along a component, so the inside is a union of
whole components. -/
theorem connectedComponentIn_subset_inside (hx : x ∈ inside C) :
    connectedComponentIn Cᶜ x ⊆ inside C := by
  intro z hz
  refine ⟨connectedComponentIn_subset _ _ hz, ?_⟩
  rw [← connectedComponentIn_eq hz]
  exact hx.2

theorem connectedComponentIn_subset_outside (hx : x ∈ outside C) :
    connectedComponentIn Cᶜ x ⊆ outside C := by
  intro z hz
  refine ⟨connectedComponentIn_subset _ _ hz, ?_⟩
  rw [← connectedComponentIn_eq hz]
  exact hx.2

/-- A union of components of an open set is open. -/
theorem isOpen_inside (hC : IsClosed C) : IsOpen (inside C) := by
  rw [isOpen_iff_forall_mem_open]
  exact fun z hz => ⟨connectedComponentIn Cᶜ z, connectedComponentIn_subset_inside hz,
    Plane.isOpen_connectedComponentIn hC.isOpen_compl, mem_connectedComponentIn hz.1⟩

theorem isOpen_outside (hC : IsClosed C) : IsOpen (outside C) := by
  rw [isOpen_iff_forall_mem_open]
  exact fun z hz => ⟨connectedComponentIn Cᶜ z, connectedComponentIn_subset_outside hz,
    Plane.isOpen_connectedComponentIn hC.isOpen_compl, mem_connectedComponentIn hz.1⟩

/-! ### Definition 2.4: a separating Jordan curve -/

/-- Definition 2.4. A Jordan curve is *separating* when its complement has exactly two regions,
one bounded and one unbounded, each with boundary `C`.

Since `inside C` and `outside C` always partition the complement into the bounded-component
part and the unbounded-component part, "exactly two regions, one bounded and one unbounded"
says precisely that each part is a single region; and the boundedness of one and unboundedness
of the other are then consequences rather than hypotheses (`IsSeparating.isBounded_inside`,
`IsSeparating.not_isBounded_outside`). -/
structure IsSeparating (C : Set Plane) : Prop where
  /-- The set is a Jordan curve. -/
  isJordanCurve : IsJordanCurve C
  /-- The bounded part of the complement is a single region. -/
  isConnected_inside : IsConnected (inside C)
  /-- The unbounded part of the complement is a single region. -/
  isConnected_outside : IsConnected (outside C)
  /-- The inside has the curve as its boundary. -/
  frontier_inside : frontier (inside C) = C
  /-- The outside has the curve as its boundary. -/
  frontier_outside : frontier (outside C) = C

namespace IsSeparating

theorem isClosed (h : IsSeparating C) : IsClosed C := h.isJordanCurve.isClosed

theorem isOpen_inside (h : IsSeparating C) : IsOpen (Schoenflies.inside C) :=
  Schoenflies.isOpen_inside h.isClosed

theorem isOpen_outside (h : IsSeparating C) : IsOpen (Schoenflies.outside C) :=
  Schoenflies.isOpen_outside h.isClosed

/-- The inside is bounded: it is connected and lies inside the complement, hence inside the
component of any of its points, which is bounded by definition of `inside`. -/
theorem isBounded_inside (h : IsSeparating C) : IsBounded (Schoenflies.inside C) := by
  obtain ⟨z, hz⟩ := h.isConnected_inside.nonempty
  exact hz.2.subset
    (h.isConnected_inside.isPreconnected.subset_connectedComponentIn hz inside_subset_compl)

/-- The outside is unbounded: it contains an unbounded component. -/
theorem not_isBounded_outside (h : IsSeparating C) : ¬ IsBounded (Schoenflies.outside C) := by
  obtain ⟨z, hz⟩ := h.isConnected_outside.nonempty
  exact fun hb => hz.2 (hb.subset (connectedComponentIn_subset_outside hz))

/-- The inside really is one *region* of the complement, that is, a connected component of it:
it is a union of components which is itself connected. Together with its twin below this is
the "exactly two regions" clause of Definition 2.4. -/
theorem connectedComponentIn_eq_inside (h : IsSeparating C) (hx : x ∈ Schoenflies.inside C) :
    connectedComponentIn Cᶜ x = Schoenflies.inside C :=
  Set.Subset.antisymm (connectedComponentIn_subset_inside hx)
    (h.isConnected_inside.isPreconnected.subset_connectedComponentIn hx inside_subset_compl)

/-- The outside is a connected component of the complement. -/
theorem connectedComponentIn_eq_outside (h : IsSeparating C) (hx : x ∈ Schoenflies.outside C) :
    connectedComponentIn Cᶜ x = Schoenflies.outside C :=
  Set.Subset.antisymm (connectedComponentIn_subset_outside hx)
    (h.isConnected_outside.isPreconnected.subset_connectedComponentIn hx outside_subset_compl)

end IsSeparating

/-! ### The two regions, named

`IsRegionOf C Ω` is "`Ω` is a region of `ℝ² ∖ C`" and `IsRegionPair C Ω Ω'` is "`Ω` and `Ω'`
are *the* two regions". Both are stated without a separation hypothesis; the facts that make
them useful carry one. -/

/-- `Ω` is a region of the complement of `C`. -/
def IsRegionOf (C Ω : Set Plane) : Prop := Ω = inside C ∨ Ω = outside C

/-- `Ω` and `Ω'` are the two regions of the complement of `C`, in one order or the other. -/
def IsRegionPair (C Ω Ω' : Set Plane) : Prop :=
  (Ω = inside C ∧ Ω' = outside C) ∨ (Ω = outside C ∧ Ω' = inside C)

/-- Every component of the complement is one of the two regions: there are no others. This is
the last clause of "exactly two regions". -/
theorem IsSeparating.isRegionOf_connectedComponentIn (h : IsSeparating C) (hx : x ∉ C) :
    IsRegionOf C (connectedComponentIn Cᶜ x) := by
  have hx' : x ∈ inside C ∪ outside C := by rw [inside_union_outside]; exact hx
  rcases hx' with hx' | hx'
  · exact Or.inl (h.connectedComponentIn_eq_inside hx')
  · exact Or.inr (h.connectedComponentIn_eq_outside hx')

namespace IsRegionOf

theorem inside (C : Set Plane) : IsRegionOf C (Schoenflies.inside C) := Or.inl rfl

theorem outside (C : Set Plane) : IsRegionOf C (Schoenflies.outside C) := Or.inr rfl

theorem subset_compl (h : IsRegionOf C Ω) : Ω ⊆ Cᶜ := by
  rcases h with rfl | rfl
  · exact inside_subset_compl
  · exact outside_subset_compl

theorem isOpen (h : IsRegionOf C Ω) (hC : IsSeparating C) : IsOpen Ω := by
  rcases h with rfl | rfl
  · exact hC.isOpen_inside
  · exact hC.isOpen_outside

theorem isConnected (h : IsRegionOf C Ω) (hC : IsSeparating C) : IsConnected Ω := by
  rcases h with rfl | rfl
  · exact hC.isConnected_inside
  · exact hC.isConnected_outside

/-- A region is a connected component of the complement. -/
theorem connectedComponentIn_eq (h : IsRegionOf C Ω) (hC : IsSeparating C) (hx : x ∈ Ω) :
    connectedComponentIn Cᶜ x = Ω := by
  rcases h with rfl | rfl
  · exact hC.connectedComponentIn_eq_inside hx
  · exact hC.connectedComponentIn_eq_outside hx

theorem frontier_eq (h : IsRegionOf C Ω) (hC : IsSeparating C) : frontier Ω = C := by
  rcases h with rfl | rfl
  · exact hC.frontier_inside
  · exact hC.frontier_outside

/-- Every point of the curve is a limit of points of the region: this is the half of
`frontier Ω = C` that absorption uses. -/
theorem subset_closure (h : IsRegionOf C Ω) (hC : IsSeparating C) : C ⊆ closure Ω := by
  rw [← h.frontier_eq hC]
  exact frontier_subset_closure

/-- The closure of a region is the region together with the curve. -/
theorem closure_eq (h : IsRegionOf C Ω) (hC : IsSeparating C) : closure Ω = Ω ∪ C := by
  have hfr := h.frontier_eq hC
  rw [(h.isOpen hC).frontier_eq] at hfr
  rw [← hfr, Set.union_sdiff_cancel _root_.subset_closure]

end IsRegionOf

namespace IsRegionPair

theorem left (h : IsRegionPair C Ω Ω') : IsRegionOf C Ω := by
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem right (h : IsRegionPair C Ω Ω') : IsRegionOf C Ω' := by
  rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem symm (h : IsRegionPair C Ω Ω') : IsRegionPair C Ω' Ω := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩

theorem union_eq (h : IsRegionPair C Ω Ω') : Ω ∪ Ω' = Cᶜ := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact inside_union_outside C
  · rw [Set.union_comm]
    exact inside_union_outside C

theorem disjoint (h : IsRegionPair C Ω Ω') : Disjoint Ω Ω' := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact disjoint_inside_outside
  · exact disjoint_inside_outside.symm

/-- A connected set off the curve and off one region lies in the other. This is the only place
where "exactly two regions" is used, and it is used in exactly that form. -/
theorem subset_left_of_isPreconnected (h : IsRegionPair C Ω Ω') (hC : IsSeparating C)
    {S : Set Plane} (hS : IsPreconnected S) (hne : S.Nonempty) (hSC : S ⊆ Cᶜ)
    (hSΩ' : Disjoint S Ω') : S ⊆ Ω := by
  obtain ⟨z, hz⟩ := hne
  have hcover : S ⊆ Ω ∪ Ω' := by rw [h.union_eq]; exact hSC
  have hzΩ : z ∈ Ω := (hcover hz).resolve_right fun hz' => Set.disjoint_left.1 hSΩ' hz hz'
  exact hS.subset_left_of_subset_union (h.left.isOpen hC) (h.right.isOpen hC) h.disjoint hcover
    ⟨z, hz, hzΩ⟩

end IsRegionPair

/-- A nonempty connected set disjoint from the curve lies in one of the two regions. This is
the well-definedness clause of Lemma 2.6: "being connected it lies in one region of
`ℝ² ∖ Jᵢ`, so `Wᵢ` and `Vᵢ` are well defined". -/
theorem IsSeparating.exists_isRegionPair_subset (hC : IsSeparating C) {S : Set Plane}
    (hS : IsPreconnected S) (hne : S.Nonempty) (hSC : Disjoint S C) :
    ∃ W V, IsRegionPair C W V ∧ S ⊆ W := by
  obtain ⟨z, hz⟩ := hne
  have hSc : S ⊆ Cᶜ := fun w hw => Set.disjoint_left.1 hSC hw
  have hcover : S ⊆ inside C ∪ outside C := by rw [inside_union_outside]; exact hSc
  by_cases hzin : z ∈ inside C
  · exact ⟨inside C, outside C, Or.inl ⟨rfl, rfl⟩,
      hS.subset_left_of_subset_union hC.isOpen_inside hC.isOpen_outside disjoint_inside_outside
        hcover ⟨z, hz, hzin⟩⟩
  · refine ⟨outside C, inside C, Or.inr ⟨rfl, rfl⟩, ?_⟩
    refine hS.subset_left_of_subset_union hC.isOpen_outside hC.isOpen_inside
      disjoint_inside_outside.symm ?_ ⟨z, hz, (hcover hz).resolve_left hzin⟩
    rw [Set.union_comm]
    exact hcover

/-! ### Lemma 2.5: absorption -/

/-- Lemma 2.5 (absorption), set-theoretic core. If every point of `C` is a limit of points of
`Ω`, and `Ω` sits inside an open `V` whose frontier lies in `J`, then `C` misses `V` only where
`J` does. -/
theorem absorption_of_subset_closure (hCΩ : C ⊆ closure Ω) (hV : IsOpen V)
    (hfr : frontier V ⊆ J) (hsub : Ω ⊆ V) : C \ J ⊆ V := by
  rintro z ⟨hzC, hzJ⟩
  by_contra hzV
  -- `z` lies in the closure of `V` but not in `V`, so it lies on the frontier, hence in `J`.
  exact hzJ (hfr (by rw [hV.frontier_eq]; exact ⟨closure_mono hsub (hCΩ hzC), hzV⟩))

/-- Lemma 2.5 (absorption). If a region `Ω` of the complement of a separating curve `C` is
contained in a region `V` of the complement of a separating curve `J`, then all of `C` off `J`
lies in `V`. -/
theorem IsSeparating.absorption (hC : IsSeparating C) (hJ : IsSeparating J)
    (hΩ : IsRegionOf C Ω) (hV : IsRegionOf J V) (hsub : Ω ⊆ V) : C \ J ⊆ V :=
  absorption_of_subset_closure (hΩ.subset_closure hC) (hV.isOpen hJ)
    (hV.frontier_eq hJ).subset hsub

/-! ### Lemma 2.6: the two cells of a crosscut

The setting: `C` is a separating curve, `Ω` and `Ω'` its two regions, `J` a separating curve
with `P ⊆ J ⊆ C ∪ P`, and `W, V` the two regions of `ℝ² ∖ J`, with `Ω' ⊆ W`. The blueprint's
`J` is `Aᵢ ∪ P` for one of the two arcs `Aᵢ`; the proof only needs the two inclusions. -/

/-- The far region `Ω'` absorbs all of `C` off `J`, so the near cell `V` misses `C` entirely:
the part of `C` off `J` is in `W`, and the part on `J` is off `V` because `V` misses `J`. -/
theorem disjoint_cell_curve (hC : IsSeparating C) (hJ : IsSeparating J)
    (hΩ' : IsRegionOf C Ω') (hWV : IsRegionPair J W V)
    (hΩW : Ω' ⊆ W) : Disjoint V C := by
  have hCW : C \ J ⊆ W := hC.absorption hJ hΩ' hWV.left hΩW
  rw [Set.disjoint_left]
  intro z hzV hzC
  by_cases hzJ : z ∈ J
  · exact hWV.right.subset_compl hzV hzJ
  · exact Set.disjoint_left.1 hWV.symm.disjoint hzV (hCW ⟨hzC, hzJ⟩)

/-- Lemma 2.6, first half of (a): the cell `V` is contained in `Ω ∖ P`. It misses `C`, it is
connected, and it misses `Ω'` because `Ω' ⊆ W`; so it lies in `Ω`. It misses `P` because it
misses `J ⊇ P`. -/
theorem cell_subset_region_diff (hC : IsSeparating C) (hJ : IsSeparating J)
    (hΩ : IsRegionPair C Ω Ω') (hWV : IsRegionPair J W V)
    (hΩW : Ω' ⊆ W) (hPJ : P ⊆ J) : V ⊆ Ω \ P := by
  have hVC : Disjoint V C := disjoint_cell_curve hC hJ hΩ.right hWV hΩW
  have hVJ : V ⊆ Jᶜ := hWV.right.subset_compl
  -- `V` and `W` are the two regions of `ℝ² ∖ J`, and `Ω'` sits inside `W`.
  have hVΩ' : Disjoint V Ω' := hWV.symm.disjoint.mono_right hΩW
  have hVΩ : V ⊆ Ω :=
    hΩ.subset_left_of_isPreconnected hC (hWV.right.isConnected hJ).isPreconnected
      (hWV.right.isConnected hJ).nonempty (fun z hz => Set.disjoint_left.1 hVC hz) hVΩ'
  exact fun z hz => ⟨hVΩ hz, fun hzP => hVJ hz (hPJ hzP)⟩

/-- Lemma 2.6 (a): the cell `V` is a connected component of `Ω ∖ P`. Its frontier is `J`, which
lies in `C ∪ P` and so misses the open set `Ω ∖ P`; Lemma 1.7 does the rest. -/
theorem cell_isComponent (hC : IsSeparating C) (hJ : IsSeparating J)
    (hΩ : IsRegionPair C Ω Ω') (hWV : IsRegionPair J W V)
    (hΩW : Ω' ⊆ W) (hPJ : P ⊆ J) (hJCP : J ⊆ C ∪ P) :
    ∀ z ∈ V, connectedComponentIn (Ω \ P) z = V := by
  intro z hz
  refine Plane.connectedComponentIn_eq_of_frontier_disjoint (hWV.right.isOpen hJ)
    (hWV.right.isConnected hJ).isPreconnected
    (cell_subset_region_diff hC hJ hΩ hWV hΩW hPJ) ?_ hz
  rw [hWV.right.frontier_eq hJ]
  refine Set.eq_empty_iff_forall_notMem.2 ?_
  rintro w ⟨hwJ, hwΩ, hwP⟩
  rcases hJCP hwJ with hwC | hwP'
  · exact hΩ.left.subset_compl hwΩ hwC
  · exact hwP hwP'

/-- Lemma 2.6 (c): the closure of the cell meets `C` exactly in `J ∩ C`. The closure is
`V ∪ J`, and `V` misses `C`. -/
theorem closure_cell_inter_curve (hC : IsSeparating C) (hJ : IsSeparating J)
    (hΩ' : IsRegionOf C Ω') (hWV : IsRegionPair J W V)
    (hΩW : Ω' ⊆ W) : closure V ∩ C = J ∩ C := by
  have hVC : Disjoint V C := disjoint_cell_curve hC hJ hΩ' hWV hΩW
  rw [hWV.right.closure_eq hJ, Set.union_inter_distrib_right, hVC.inter_eq, Set.empty_union]

/-! ### The arc-level side conditions

Two small facts turn the blueprint's arc picture into the hypotheses the lemmas above take. -/

/-- The two curves of Lemma 2.6 are Jordan curves: an arc from `p` to `q` and a second arc from
`p` to `q` meeting it only at those two points glue to a Jordan curve. -/
theorem isJordanCurve_union (hA : IsArcBetween A p q) (hP : IsArcBetween P p q)
    (hmeet : ∀ z ∈ A, z ∈ P → z = p ∨ z = q) : IsJordanCurve (A ∪ P) :=
  IsJordanCurve.of_two_arcs hA hP.reverse hmeet

/-- Lemma 2.6 (b), arc side: the two arcs of `C` from `p` to `q` are distinct, because they
meet only at `p` and `q` while neither is just `{p, q}`. -/
theorem arcs_ne (hmeet : A₁ ∩ A₂ ⊆ {p, q}) (hA : ¬ A₁ ⊆ {p, q}) : A₁ ≠ A₂ := by
  rintro rfl
  exact hA fun z hz => hmeet ⟨hz, hz⟩

/-! ### Lemma 2.6, bundled -/

/-- **Lemma 2.6 (crosscut cells).** Let `C` be a separating curve with regions `Ω` and `Ω'`,
let `A₁, A₂ ⊆ C` be the two arcs cut out by a crosscut `P` which meets `C` only in points of
both arcs, and suppose the two curves `Jᵢ = Aᵢ ∪ P` are separating. Let `Wᵢ` be the region of
`ℝ² ∖ Jᵢ` containing `Ω'` and `Vᵢ` the other one. Then

* (a) each `Vᵢ` is a connected component of `Ω ∖ P`;
* (b) `V₁ ≠ V₂`;
* (c) `closure Vᵢ ∩ C = Aᵢ`.

The blueprint proves (b) from the boundaries; here it falls straight out of (c), since
`V₁ = V₂` would make `A₁ = A₂`. -/
theorem crosscut_cells (hC : IsSeparating C)
    (hJ₁ : IsSeparating (A₁ ∪ P)) (hJ₂ : IsSeparating (A₂ ∪ P))
    (hA₁ : A₁ ⊆ C) (hA₂ : A₂ ⊆ C) (hP₁ : P ∩ C ⊆ A₁) (hP₂ : P ∩ C ⊆ A₂) (hne : A₁ ≠ A₂)
    (hΩ : IsRegionPair C Ω Ω')
    {W₁ V₁ W₂ V₂ : Set Plane}
    (hWV₁ : IsRegionPair (A₁ ∪ P) W₁ V₁) (hΩW₁ : Ω' ⊆ W₁)
    (hWV₂ : IsRegionPair (A₂ ∪ P) W₂ V₂) (hΩW₂ : Ω' ⊆ W₂) :
    (V₁ ⊆ Ω \ P ∧ ∀ z ∈ V₁, connectedComponentIn (Ω \ P) z = V₁) ∧
      (V₂ ⊆ Ω \ P ∧ ∀ z ∈ V₂, connectedComponentIn (Ω \ P) z = V₂) ∧
      V₁ ≠ V₂ ∧ closure V₁ ∩ C = A₁ ∧ closure V₂ ∩ C = A₂ := by
  -- The two inclusions that replace the arc hypotheses.
  have hPJ : ∀ A : Set Plane, P ⊆ A ∪ P := fun A => Set.subset_union_right
  have hJCP : ∀ {A : Set Plane}, A ⊆ C → A ∪ P ⊆ C ∪ P := fun hA =>
    Set.union_subset_union_left P hA
  -- (c): `(Aᵢ ∪ P) ∩ C = Aᵢ`, since `Aᵢ ⊆ C` and `P ∩ C ⊆ Aᵢ`.
  have hinter : ∀ {A : Set Plane}, A ⊆ C → P ∩ C ⊆ A → (A ∪ P) ∩ C = A := by
    intro A hAC hPC
    refine Set.Subset.antisymm ?_ fun z hz => ⟨Or.inl hz, hAC hz⟩
    rintro z ⟨hz | hz, hzC⟩
    · exact hz
    · exact hPC ⟨hz, hzC⟩
  have hc₁ : closure V₁ ∩ C = A₁ := by
    rw [closure_cell_inter_curve hC hJ₁ hΩ.right hWV₁ hΩW₁]; exact hinter hA₁ hP₁
  have hc₂ : closure V₂ ∩ C = A₂ := by
    rw [closure_cell_inter_curve hC hJ₂ hΩ.right hWV₂ hΩW₂]; exact hinter hA₂ hP₂
  refine ⟨⟨cell_subset_region_diff hC hJ₁ hΩ hWV₁ hΩW₁ (hPJ A₁),
      cell_isComponent hC hJ₁ hΩ hWV₁ hΩW₁ (hPJ A₁) (hJCP hA₁)⟩,
    ⟨cell_subset_region_diff hC hJ₂ hΩ hWV₂ hΩW₂ (hPJ A₂),
      cell_isComponent hC hJ₂ hΩ hWV₂ hΩW₂ (hPJ A₂) (hJCP hA₂)⟩, ?_, hc₁, hc₂⟩
  -- (b): equal cells would have equal closures, hence equal arcs.
  rintro rfl
  exact hne (hc₁.symm.trans hc₂)

end Schoenflies

end BundlePart410
