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

public import verified.parts.part029
import all verified.parts.part029

@[expose] public section

set_option debug.skipKernelTC false
set_option linter.all false
set_option Elab.async false
set_option internal.cmdlineSnapshots true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

section BundlePart397
/- Source: dev/planar_search/schoenflies_port/Schoenflies/SegmentOrder.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/



/-!
# Along one segment: the distance from an end as a coordinate

Everything the polygonal overlay has to say about several collinear segments — which piece
lies inside which, where a piece may end, when two pieces have to coincide — is
one-dimensional: it happens along a single straight segment. This module supplies the
coordinate that makes it ordinary arithmetic. Along a nondegenerate `segment ℝ a b` the
distance from `a` determines the point, and it reads betweenness off as a pair of
inequalities, so a claim about four collinear points becomes a claim about four reals.

No new geometry is needed. `dist_left_lineMap` already says the distance from `a` *is* the
parameter of `AffineMap.lineMap a b`, scaled by the segment's length, and `image_segment`
already says that parametrization carries segments of `ℝ` to segments of the plane. What is
added here is the translation, stated once so that the arithmetic does not have to be redone
at every use.

The two results the module exists for come last, and they are what makes cutting at every
meet enough:

* a piece that meets an overlap and keeps the overlap's ends out of its interior lies inside
  the overlap (`segment_inside_of_ends_outside`);
* two pieces whose interiors meet, each keeping the other's ends out of its interior, are the
  same pair of points (`same_ends_of_meeting_interiors`).

Both are stated **inside one ambient segment**. Collinearity is not optional: a piece crossing
the overlap transversally would meet it and avoid both its ends without lying inside it, so
every point named is a point of one ambient `segment ℝ a b`.

Both are also stated with no orientation asked of the caller. The `_oriented` forms they wrap
are near-end-first, which is what the arithmetic wants; the unoriented forms decide the
orientation themselves, and they are what the overlay uses.

## A note on degenerate pieces

Mathlib's `openSegment ℝ u u` is `{u}`, not `∅`. A degenerate piece therefore has a nonempty
interior, and the strict translation `dist_lt_of_mem_openSegment` genuinely needs `u ≠ v`.
The two headline theorems do *not* ask for it: in each of them a degenerate piece is either
excluded by the hypotheses or settled outright, and that case split lives inside the proof.

## Blueprint

* `segment_inside_of_ends_outside`, `same_ends_of_meeting_interiors` — the separation behind
  the deduplication clause of the polygonal overlay (`lem:polygonal-overlay`, "represent every
  duplicate geometric subsegment only once") and of the subdivision in
  `lem:polygonal-connected` ("delete duplicate subsegments"): once every piece's ends are cut
  points, and so interior to nothing, two pieces that share an interior point coincide instead
  of merely overlapping.
-/

open Set

namespace Schoenflies

variable {a b : Plane}

/-! ### The parametrization of a segment

`AffineMap.lineMap a b` walks from `a` to `b`. It carries a segment of `ℝ` onto the
corresponding piece of `[a, b]`, and it turns the distance from `a` into multiplication by
the segment's length. Those two facts are the whole content of the module; the rest is
arithmetic. -/

/-- The distance from the left endpoint to the point at parameter `t` is `t` times the
segment's length. This is `dist_left_lineMap` with the absolute value discharged. -/
theorem dist_left_lineMap_of_nonneg (a b : Plane) {t : ℝ} (ht : 0 ≤ t) :
    dist a (AffineMap.lineMap a b t) = t * dist a b := by
  rw [dist_left_lineMap, Real.norm_eq_abs, abs_of_nonneg ht]

/-- The piece of `[a, b]` spanned by two parameters is the image of the segment they span. -/
theorem segment_lineMap_image (a b : Plane) (p q : ℝ) :
    segment ℝ (AffineMap.lineMap a b p) (AffineMap.lineMap a b q)
      = (AffineMap.lineMap a b : ℝ →ᵃ[ℝ] Plane) '' segment ℝ p q := by
  simp

/-- The same for interiors. -/
theorem openSegment_lineMap_image (a b : Plane) (p q : ℝ) :
    openSegment ℝ (AffineMap.lineMap a b p) (AffineMap.lineMap a b q)
      = (AffineMap.lineMap a b : ℝ →ᵃ[ℝ] Plane) '' openSegment ℝ p q := by
  simp

/-- Every point of `[a, b]` carries a parameter: a number `t ∈ [0, 1]` placing it on the
segment, whose distance from `a` is `t` times the segment's length. This is the only way the
rest of the module looks at a point of the segment. -/
theorem exists_param_of_mem_segment {x : Plane} (hx : x ∈ segment ℝ a b) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ AffineMap.lineMap a b t = x ∧ dist a x = t * dist a b := by
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hx
  exact ⟨t, ht0, ht1, rfl, dist_left_lineMap_of_nonneg a b ht0⟩

/-! ### The coordinate -/

/-- Along a nondegenerate segment, the distance from the left endpoint **orders the
parameters**: a nonzero length cancels from `s * ‖b - a‖ ≤ t * ‖b - a‖`. -/
theorem parameter_le_of_distance (hab : a ≠ b) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (h : dist a (AffineMap.lineMap a b s) ≤ dist a (AffineMap.lineMap a b t)) : s ≤ t := by
  have hd : 0 < dist a b := dist_pos.2 hab
  rw [dist_left_lineMap_of_nonneg a b hs, dist_left_lineMap_of_nonneg a b ht] at h
  exact le_of_mul_le_mul_right (by linarith) hd

/-- The distance from `a` determines the point: two points of a nondegenerate `[a, b]` at
equal distance from `a` are equal. -/
theorem eq_of_dist_left_eq (hab : a ≠ b) {x y : Plane} (hx : x ∈ segment ℝ a b)
    (hy : y ∈ segment ℝ a b) (h : dist a x = dist a y) : x = y := by
  have hd : 0 < dist a b := dist_pos.2 hab
  obtain ⟨s, -, -, rfl, hsd⟩ := exists_param_of_mem_segment hx
  obtain ⟨t, -, -, rfl, htd⟩ := exists_param_of_mem_segment hy
  rw [hsd, htd] at h
  rw [mul_right_cancel₀ (ne_of_gt hd) h]

/-! ### Betweenness as a pair of inequalities -/

/-- A point between two points of the segment is between them in distance from `a` as well:
measured from `a`, the nearer end comes first. -/
theorem dist_le_of_mem_segment (hab : a ≠ b) {u v x : Plane} (hu : u ∈ segment ℝ a b)
    (hv : v ∈ segment ℝ a b) (huv : dist a u ≤ dist a v) (hx : x ∈ segment ℝ u v) :
    dist a u ≤ dist a x ∧ dist a x ≤ dist a v := by
  have hd : (0 : ℝ) ≤ dist a b := dist_nonneg
  obtain ⟨p, hp0, -, rfl, hpd⟩ := exists_param_of_mem_segment hu
  obtain ⟨q, hq0, -, rfl, hqd⟩ := exists_param_of_mem_segment hv
  have hpq : p ≤ q := parameter_le_of_distance hab hp0 hq0 huv
  -- The parametrization carries `[p, q]` onto the piece, so `x` has a parameter in `[p, q]`.
  rw [segment_lineMap_image, segment_eq_Icc hpq] at hx
  obtain ⟨t, ⟨hpt, htq⟩, rfl⟩ := hx
  rw [hpd, hqd, dist_left_lineMap_of_nonneg a b (hp0.trans hpt)]
  exact ⟨by nlinarith, by nlinarith⟩

/-- The converse: a point of the segment whose distance from `a` lies between the two ends'
distances lies between the ends. -/
theorem mem_segment_of_dist_le (hab : a ≠ b) {u v x : Plane} (hu : u ∈ segment ℝ a b)
    (hv : v ∈ segment ℝ a b) (hx : x ∈ segment ℝ a b) (h₁ : dist a u ≤ dist a x)
    (h₂ : dist a x ≤ dist a v) : x ∈ segment ℝ u v := by
  obtain ⟨p, hp0, -, rfl, -⟩ := exists_param_of_mem_segment hu
  obtain ⟨q, hq0, -, rfl, -⟩ := exists_param_of_mem_segment hv
  obtain ⟨t, ht0, -, rfl, -⟩ := exists_param_of_mem_segment hx
  have hpt : p ≤ t := parameter_le_of_distance hab hp0 ht0 h₁
  have htq : t ≤ q := parameter_le_of_distance hab ht0 hq0 h₂
  rw [segment_lineMap_image, segment_eq_Icc (hpt.trans htq)]
  exact ⟨t, ⟨hpt, htq⟩, rfl⟩

/-! ### The same translation for interiors

`openSegment ℝ u u = {u}` in Mathlib, so the strict form asks for a nondegenerate piece; its
converse does not, since strict inequalities force nondegeneracy on their own. -/

/-- A point interior to a nondegenerate piece of the segment is strictly between its ends in
distance from `a`. -/
theorem dist_lt_of_mem_openSegment (hab : a ≠ b) {u v x : Plane} (hu : u ∈ segment ℝ a b)
    (hv : v ∈ segment ℝ a b) (huv : u ≠ v) (hor : dist a u ≤ dist a v)
    (hx : x ∈ openSegment ℝ u v) : dist a u < dist a x ∧ dist a x < dist a v := by
  have hd : 0 < dist a b := dist_pos.2 hab
  obtain ⟨p, hp0, -, rfl, hpd⟩ := exists_param_of_mem_segment hu
  obtain ⟨q, hq0, -, rfl, hqd⟩ := exists_param_of_mem_segment hv
  have hpq : p < q :=
    lt_of_le_of_ne (parameter_le_of_distance hab hp0 hq0 hor) fun h => huv (by rw [h])
  rw [openSegment_lineMap_image, openSegment_eq_Ioo hpq] at hx
  obtain ⟨t, ⟨hpt, htq⟩, rfl⟩ := hx
  rw [hpd, hqd, dist_left_lineMap_of_nonneg a b (hp0.trans hpt.le)]
  exact ⟨by nlinarith, by nlinarith⟩

/-- The converse: a point of the segment strictly between the ends in distance from `a` is
interior to the piece they span. -/
theorem mem_openSegment_of_dist_lt (hab : a ≠ b) {u v x : Plane} (hu : u ∈ segment ℝ a b)
    (hv : v ∈ segment ℝ a b) (hx : x ∈ segment ℝ a b) (h₁ : dist a u < dist a x)
    (h₂ : dist a x < dist a v) : x ∈ openSegment ℝ u v := by
  have hd : 0 < dist a b := dist_pos.2 hab
  obtain ⟨p, -, -, rfl, hpd⟩ := exists_param_of_mem_segment hu
  obtain ⟨q, -, -, rfl, hqd⟩ := exists_param_of_mem_segment hv
  obtain ⟨t, -, -, rfl, htd⟩ := exists_param_of_mem_segment hx
  rw [hpd, htd] at h₁
  rw [htd, hqd] at h₂
  have hpt : p < t := lt_of_mul_lt_mul_right h₁ hd.le
  have htq : t < q := lt_of_mul_lt_mul_right h₂ hd.le
  rw [openSegment_lineMap_image, openSegment_eq_Ioo (hpt.trans htq)]
  exact ⟨t, ⟨hpt, htq⟩, rfl⟩

/-! ### Where a point that is not interior to a piece must sit

These two carry the whole one-dimensional argument. A point of the ambient segment kept out
of a piece's interior has to be outside on one side or the other, and knowing which side it
is not settles it. -/

/-- A point of the ambient segment kept out of `[u, v]`'s interior and lying before `v` lies
at or before `u`. -/
theorem dist_le_left_of_notMem_openSegment (hab : a ≠ b) {u v y : Plane}
    (hu : u ∈ segment ℝ a b) (hv : v ∈ segment ℝ a b) (hy : y ∈ segment ℝ a b)
    (hout : y ∉ openSegment ℝ u v) (hlt : dist a y < dist a v) : dist a y ≤ dist a u := by
  by_contra hcon
  exact hout (mem_openSegment_of_dist_lt hab hu hv hy (lt_of_not_ge hcon) hlt)

/-- The mirror: a point of the ambient segment kept out of `[u, v]`'s interior and lying
after `u` lies at or after `v`. -/
theorem le_dist_right_of_notMem_openSegment (hab : a ≠ b) {u v y : Plane}
    (hu : u ∈ segment ℝ a b) (hv : v ∈ segment ℝ a b) (hy : y ∈ segment ℝ a b)
    (hout : y ∉ openSegment ℝ u v) (hlt : dist a u < dist a y) : dist a v ≤ dist a y := by
  by_contra hcon
  exact hout (mem_openSegment_of_dist_lt hab hu hv hy hlt (lt_of_not_ge hcon))

/-! ### What the overlay is after -/

/-- A piece that meets an overlap and keeps the overlap's two ends out of its interior lies
inside the overlap — near-end-first form. -/
theorem segment_inside_of_ends_outside_oriented (hab : a ≠ b) {u v s t x : Plane}
    (hu : u ∈ segment ℝ a b) (hv : v ∈ segment ℝ a b) (hpiece : dist a u ≤ dist a v)
    (hs : s ∈ segment ℝ a b) (ht : t ∈ segment ℝ a b) (hover : dist a s ≤ dist a t)
    (hxp : x ∈ openSegment ℝ u v) (hxo : x ∈ openSegment ℝ s t)
    (hsout : s ∉ openSegment ℝ u v) (htout : t ∉ openSegment ℝ u v) :
    segment ℝ u v ⊆ segment ℝ s t := by
  -- A degenerate overlap is impossible: its only interior point is `s`, which by hypothesis
  -- is not interior to the piece, whereas `x` is.
  rcases eq_or_ne s t with rfl | hst
  · rw [openSegment_same, mem_singleton_iff] at hxo
    rw [← hxo] at hsout
    exact absurd hxp hsout
  -- A degenerate piece is the single point `x`, which already lies in the overlap.
  rcases eq_or_ne u v with rfl | huv
  · rw [openSegment_same, mem_singleton_iff] at hxp
    rw [segment_same, singleton_subset_iff, ← hxp]
    exact openSegment_subset_segment ℝ s t hxo
  obtain ⟨hux, hxv⟩ := dist_lt_of_mem_openSegment hab hu hv huv hpiece hxp
  obtain ⟨hsx, hxt⟩ := dist_lt_of_mem_openSegment hab hs ht hst hover hxo
  -- The overlap starts at or before the piece and ends at or after it.
  have hsu : dist a s ≤ dist a u :=
    dist_le_left_of_notMem_openSegment hab hu hv hs hsout (hsx.trans hxv)
  have hvt : dist a v ≤ dist a t :=
    le_dist_right_of_notMem_openSegment hab hu hv ht htout (hux.trans hxt)
  intro y hy
  have hyab : y ∈ segment ℝ a b := (convex_segment a b).segment_subset hu hv hy
  obtain ⟨huy, hyv⟩ := dist_le_of_mem_segment hab hu hv hpiece hy
  exact mem_segment_of_dist_le hab hs ht hyab (hsu.trans huy) (hyv.trans hvt)

/-- Two pieces of one ambient segment whose interiors meet, each keeping the other's ends out
of its interior, have the same ends — near-end-first form. -/
theorem same_ends_of_meeting_interiors_oriented (hab : a ≠ b) {u v s t x : Plane}
    (hu : u ∈ segment ℝ a b) (hv : v ∈ segment ℝ a b) (hfirst : dist a u ≤ dist a v)
    (hs : s ∈ segment ℝ a b) (ht : t ∈ segment ℝ a b) (hsecond : dist a s ≤ dist a t)
    (hxu : x ∈ openSegment ℝ u v) (hxs : x ∈ openSegment ℝ s t)
    (hsout : s ∉ openSegment ℝ u v) (htout : t ∉ openSegment ℝ u v)
    (huout : u ∉ openSegment ℝ s t) (hvout : v ∉ openSegment ℝ s t) :
    u = s ∧ v = t := by
  -- Neither piece can be degenerate: its only interior point would then be one of its own
  -- ends, which the other piece is required to keep out of its interior.
  rcases eq_or_ne u v with rfl | huv
  · rw [openSegment_same, mem_singleton_iff] at hxu
    rw [← hxu] at huout
    exact absurd hxs huout
  rcases eq_or_ne s t with rfl | hst
  · rw [openSegment_same, mem_singleton_iff] at hxs
    rw [← hxs] at hsout
    exact absurd hxu hsout
  obtain ⟨hux, hxv⟩ := dist_lt_of_mem_openSegment hab hu hv huv hfirst hxu
  obtain ⟨hsx, hxt⟩ := dist_lt_of_mem_openSegment hab hs ht hst hsecond hxs
  -- Each piece's near end lies at or before the other's, so they agree.
  have hsu : dist a s ≤ dist a u :=
    dist_le_left_of_notMem_openSegment hab hu hv hs hsout (hsx.trans hxv)
  have hus : dist a u ≤ dist a s :=
    dist_le_left_of_notMem_openSegment hab hs ht hu huout (hux.trans hxt)
  -- And the same on the far side.
  have hvt : dist a v ≤ dist a t :=
    le_dist_right_of_notMem_openSegment hab hu hv ht htout (hux.trans hxt)
  have htv : dist a t ≤ dist a v :=
    le_dist_right_of_notMem_openSegment hab hs ht hv hvout (hsx.trans hxv)
  exact ⟨eq_of_dist_left_eq hab hu hs (le_antisymm hus hsu),
    eq_of_dist_left_eq hab hv ht (le_antisymm hvt htv)⟩

/-! ### The same two, asking the caller nothing about orientation

A piece is a pair of ends, and which of them is nearer `a` is none of the caller's business —
`segment` and `openSegment` do not care. The oriented forms above are near-end-first because
that is what the arithmetic wants; these decide the orientation themselves. Every hypothesis
is restated in both spellings first, so each of the four cases is just "which way round, then
cite". -/

/-- A piece that meets an overlap and keeps the overlap's two ends out of its interior lies
inside the overlap.

Collinearity is not optional: every point named is a point of one ambient `segment ℝ a b`. A
piece crossing the overlap transversally would meet it and avoid both its ends without lying
inside it. -/
theorem segment_inside_of_ends_outside (hab : a ≠ b) {u v s t x : Plane}
    (hu : u ∈ segment ℝ a b) (hv : v ∈ segment ℝ a b)
    (hs : s ∈ segment ℝ a b) (ht : t ∈ segment ℝ a b)
    (hxp : x ∈ openSegment ℝ u v) (hxo : x ∈ openSegment ℝ s t)
    (hsout : s ∉ openSegment ℝ u v) (htout : t ∉ openSegment ℝ u v) :
    segment ℝ u v ⊆ segment ℝ s t := by
  have hxp' : x ∈ openSegment ℝ v u := by rwa [openSegment_symm ℝ v u]
  have hsout' : s ∉ openSegment ℝ v u := by rwa [openSegment_symm ℝ v u]
  have htout' : t ∉ openSegment ℝ v u := by rwa [openSegment_symm ℝ v u]
  have hxo' : x ∈ openSegment ℝ t s := by rwa [openSegment_symm ℝ t s]
  have hrevPiece : segment ℝ v u = segment ℝ u v := segment_symm ℝ v u
  have hrevOverlap : segment ℝ t s = segment ℝ s t := segment_symm ℝ t s
  rcases le_total (dist a u) (dist a v) with hp | hp <;>
    rcases le_total (dist a s) (dist a t) with ho | ho
  · exact segment_inside_of_ends_outside_oriented hab hu hv hp hs ht ho hxp hxo hsout htout
  · rw [← hrevOverlap]
    exact segment_inside_of_ends_outside_oriented hab hu hv hp ht hs ho hxp hxo' htout hsout
  · rw [← hrevPiece]
    exact segment_inside_of_ends_outside_oriented hab hv hu hp hs ht ho hxp' hxo hsout' htout'
  · rw [← hrevPiece, ← hrevOverlap]
    exact segment_inside_of_ends_outside_oriented hab hv hu hp ht hs ho hxp' hxo' htout' hsout'

/-- Two pieces of one ambient segment whose interiors meet, each keeping the other's ends out
of its interior, are the same pair of points — in one order or the other.

This is the separation the deduplication clause is for: overlapping collinear pieces cannot
be pulled apart by cutting, and after enough cuts they coincide instead. -/
theorem same_ends_of_meeting_interiors (hab : a ≠ b) {u v s t x : Plane}
    (hu : u ∈ segment ℝ a b) (hv : v ∈ segment ℝ a b)
    (hs : s ∈ segment ℝ a b) (ht : t ∈ segment ℝ a b)
    (hxu : x ∈ openSegment ℝ u v) (hxs : x ∈ openSegment ℝ s t)
    (hsout : s ∉ openSegment ℝ u v) (htout : t ∉ openSegment ℝ u v)
    (huout : u ∉ openSegment ℝ s t) (hvout : v ∉ openSegment ℝ s t) :
    (u = s ∧ v = t) ∨ (u = t ∧ v = s) := by
  have hxu' : x ∈ openSegment ℝ v u := by rwa [openSegment_symm ℝ v u]
  have hxs' : x ∈ openSegment ℝ t s := by rwa [openSegment_symm ℝ t s]
  have hsout' : s ∉ openSegment ℝ v u := by rwa [openSegment_symm ℝ v u]
  have htout' : t ∉ openSegment ℝ v u := by rwa [openSegment_symm ℝ v u]
  have huout' : u ∉ openSegment ℝ t s := by rwa [openSegment_symm ℝ t s]
  have hvout' : v ∉ openSegment ℝ t s := by rwa [openSegment_symm ℝ t s]
  rcases le_total (dist a u) (dist a v) with hp | hp <;>
    rcases le_total (dist a s) (dist a t) with ho | ho
  · exact Or.inl (same_ends_of_meeting_interiors_oriented hab hu hv hp hs ht ho hxu hxs
      hsout htout huout hvout)
  · exact Or.inr (same_ends_of_meeting_interiors_oriented hab hu hv hp ht hs ho hxu hxs'
      htout hsout huout' hvout')
  · obtain ⟨h₁, h₂⟩ := same_ends_of_meeting_interiors_oriented hab hv hu hp hs ht ho hxu' hxs
      hsout' htout' hvout huout
    exact Or.inr ⟨h₂, h₁⟩
  · obtain ⟨h₁, h₂⟩ := same_ends_of_meeting_interiors_oriented hab hv hu hp ht hs ho hxu' hxs'
      htout' hsout' hvout' huout'
    exact Or.inl ⟨h₂, h₁⟩

end Schoenflies

end BundlePart397

section BundlePart398
/- Source: dev/planar_search/schoenflies_port/Schoenflies/Subdivide.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/



/-!
# Subdividing a list of segments

A polygonal edge **is** its pair of endpoints: a straight segment is determined by its ends,
so naming one by anything else names a distinction that does not exist. `Piece := Plane ×
Plane`, and the blueprint's "represent every duplicate geometric subsegment only once"
becomes deduplication of a list of *names*, with no geometry in it.

**The subdivision recurses on the POINT list, not on the segment.** `subdivide pieces points`
cuts every current piece at the head point and recurses with the rest. Read literally the
blueprint wants the cut points as data, which would need a choice operator (the meets are
existential) and then a sort (to order them along each segment). Neither is required: order
does not matter, because cutting at a point that has already become an endpoint is a no-op.

Three facts about one cut, each lifted across the piece list and then across the point list:

* `subdivide_cover` — cutting loses nothing, so a subdivision occupies what it came from;
* `subdivide_ne` — no piece degenerates, so the drawing condition's invariant survives;
* `subdivide_interior_subset` — every piece's interior lies inside the interior of a piece
  it came from. This is what makes a cut **permanent**: nothing later can put a removed point
  back into an interior.

## Blueprint

* `Piece`, `cover` — the segment representation and what a list of them occupies.
* `subdivide` and its three properties — the cutting half of Lemma 3.7 (polygonal overlay).
-/

open Metric Set

namespace Schoenflies

/-- A polygonal edge is its pair of endpoints. -/
abbrev Piece := Plane × Plane

namespace Piece

/-- The closed segment a piece occupies. -/
def seg (P : Piece) : Set Plane := segment ℝ P.1 P.2

/-- The interior of a piece. -/
def interior (P : Piece) : Set Plane := openSegment ℝ P.1 P.2

/-- A piece is nondegenerate when its two ends differ. -/
def Nondeg (P : Piece) : Prop := P.1 ≠ P.2

end Piece

/-- What a list of pieces occupies. -/
def cover (pieces : List Piece) : Set Plane := ⋃ P ∈ pieces, P.seg

@[simp] theorem cover_nil : cover [] = ∅ := by simp [cover]

@[simp] theorem cover_cons (P : Piece) (ps : List Piece) :
    cover (P :: ps) = P.seg ∪ cover ps := by
  simp [cover]

theorem cover_append (ps qs : List Piece) : cover (ps ++ qs) = cover ps ∪ cover qs := by
  induction ps with
  | nil => simp
  | cons P ps ih => rw [List.cons_append, cover_cons, cover_cons, ih, union_assoc]

theorem cover_flatMap (f : Piece → List Piece) (ps : List Piece) :
    cover (ps.flatMap f) = ⋃ P ∈ ps, cover (f P) := by
  induction ps with
  | nil => simp
  | cons P ps ih => rw [List.flatMap_cons, cover_append, ih]; simp

/-! ### One cut -/

open scoped Classical in
/-- Cut one piece at one point: two pieces if the point is interior to it, and the piece
unchanged otherwise. Cutting at a point that is already an endpoint is a no-op. -/
noncomputable def splitAt (p : Plane) (P : Piece) : List Piece :=
  if p ∈ P.interior then [(P.1, p), (p, P.2)] else [P]

theorem splitAt_cover (p : Plane) (P : Piece) : cover (splitAt p P) = P.seg := by
  classical
  unfold splitAt
  split_ifs with h
  · have hp : p ∈ P.seg := openSegment_subset_segment ℝ _ _ h
    simp only [cover_cons, cover_nil, union_empty]
    exact (segment_split hp).symm
  · simp

/-- Cutting at an interior point leaves both halves nondegenerate: an interior point differs
from both ends. -/
theorem splitAt_ne (p : Plane) {P : Piece} (hP : P.Nondeg) :
    ∀ Q ∈ splitAt p P, Q.Nondeg := by
  classical
  unfold splitAt
  split_ifs with h
  · intro Q hQ
    -- `p` is strictly inside, so it is neither end.
    have h1 : P.1 ≠ p := by
      rintro rfl
      exact hP (left_mem_openSegment_iff.1 h)
    have h2 : p ≠ P.2 := by
      rintro rfl
      exact hP (right_mem_openSegment_iff.1 h)
    rcases List.mem_cons.1 hQ with rfl | hQ
    · exact h1
    · rcases List.mem_singleton.1 hQ with rfl
      exact h2
  · intro Q hQ
    rcases List.mem_singleton.1 hQ with rfl
    exact hP

/-- Cutting is permanent: each half's interior lies inside the whole's. -/
theorem splitAt_interior_subset (p : Plane) (P : Piece) :
    ∀ Q ∈ splitAt p P, Q.interior ⊆ P.interior := by
  classical
  unfold splitAt
  split_ifs with h
  · intro Q hQ
    rcases List.mem_cons.1 hQ with rfl | hQ
    · exact openSegment_left_subset h
    · rcases List.mem_singleton.1 hQ with rfl
      exact openSegment_right_subset h
  · intro Q hQ
    rcases List.mem_singleton.1 hQ with rfl
    exact subset_rfl

/-- After cutting at `p`, no piece has `p` in its interior.

Nondegeneracy is needed: a degenerate piece `(p, p)` has `p` in its interior and cutting it
produces two more copies of itself. -/
theorem splitAt_avoids (p : Plane) {P : Piece} (hP : P.Nondeg) :
    ∀ Q ∈ splitAt p P, p ∉ Q.interior := by
  classical
  unfold splitAt
  split_ifs with h
  · have h1 : P.1 ≠ p := by
      rintro rfl
      exact hP (left_mem_openSegment_iff.1 h)
    have h2 : p ≠ P.2 := by
      rintro rfl
      exact hP (right_mem_openSegment_iff.1 h)
    intro Q hQ
    rcases List.mem_cons.1 hQ with rfl | hQ
    · exact fun hmem => h1 (right_mem_openSegment_iff.1 hmem)
    · rcases List.mem_singleton.1 hQ with rfl
      exact fun hmem => h2 (left_mem_openSegment_iff.1 hmem)
  · intro Q hQ
    rcases List.mem_singleton.1 hQ with rfl
    exact h

/-! ### One cut, across the whole list -/

/-- Cut every piece of the list at one point. -/
noncomputable def splitAllAt (p : Plane) (pieces : List Piece) : List Piece :=
  pieces.flatMap (splitAt p)

theorem splitAllAt_cover (p : Plane) (pieces : List Piece) :
    cover (splitAllAt p pieces) = cover pieces := by
  rw [splitAllAt, cover_flatMap]
  simp only [splitAt_cover]
  rfl

theorem splitAllAt_ne (p : Plane) {pieces : List Piece} (h : ∀ P ∈ pieces, P.Nondeg) :
    ∀ Q ∈ splitAllAt p pieces, Q.Nondeg := by
  intro Q hQ
  obtain ⟨P, hP, hQP⟩ := List.mem_flatMap.1 hQ
  exact splitAt_ne p (h P hP) Q hQP

theorem splitAllAt_interior_subset (p : Plane) (pieces : List Piece) :
    ∀ Q ∈ splitAllAt p pieces, ∃ P ∈ pieces, Q.interior ⊆ P.interior := by
  intro Q hQ
  obtain ⟨P, hP, hQP⟩ := List.mem_flatMap.1 hQ
  exact ⟨P, hP, splitAt_interior_subset p P Q hQP⟩

theorem splitAllAt_avoids (p : Plane) {pieces : List Piece} (h : ∀ P ∈ pieces, P.Nondeg) :
    ∀ Q ∈ splitAllAt p pieces, p ∉ Q.interior := by
  intro Q hQ
  obtain ⟨P, hP, hQP⟩ := List.mem_flatMap.1 hQ
  exact splitAt_avoids p (h P hP) Q hQP

/-! ### The subdivision -/

/-- Subdivide a list of pieces at a list of points, recursing on the POINT list: cut every
current piece at the head, then carry on with the tail. -/
noncomputable def subdivide (pieces : List Piece) : List Plane → List Piece
  | [] => pieces
  | p :: ps => subdivide (splitAllAt p pieces) ps

@[simp] theorem subdivide_nil (pieces : List Piece) : subdivide pieces [] = pieces := rfl

@[simp] theorem subdivide_cons (pieces : List Piece) (p : Plane) (ps : List Plane) :
    subdivide pieces (p :: ps) = subdivide (splitAllAt p pieces) ps := rfl

/-- Cutting loses nothing: a subdivision occupies exactly what it came from. -/
theorem subdivide_cover (pieces : List Piece) (points : List Plane) :
    cover (subdivide pieces points) = cover pieces := by
  induction points generalizing pieces with
  | nil => rfl
  | cons p ps ih => rw [subdivide_cons, ih, splitAllAt_cover]

/-- No piece degenerates. -/
theorem subdivide_ne {pieces : List Piece} (points : List Plane)
    (h : ∀ P ∈ pieces, P.Nondeg) : ∀ Q ∈ subdivide pieces points, Q.Nondeg := by
  induction points generalizing pieces with
  | nil => exact h
  | cons p ps ih => exact ih (splitAllAt_ne p h)

/-- Every piece's interior lies inside the interior of a piece it came from. This is what
makes a cut permanent. -/
theorem subdivide_interior_subset (pieces : List Piece) (points : List Plane) :
    ∀ Q ∈ subdivide pieces points, ∃ P ∈ pieces, Q.interior ⊆ P.interior := by
  induction points generalizing pieces with
  | nil => exact fun Q hQ => ⟨Q, hQ, subset_rfl⟩
  | cons p ps ih =>
    intro Q hQ
    obtain ⟨R, hR, hQR⟩ := ih (pieces := splitAllAt p pieces) Q hQ
    obtain ⟨P, hP, hRP⟩ := splitAllAt_interior_subset p pieces R hR
    exact ⟨P, hP, hQR.trans hRP⟩

/-- After subdividing, no cut point is interior to any piece. Permanence is what makes this
work: a later cut only shrinks interiors, so a point removed early stays removed. -/
theorem subdivide_avoids {pieces : List Piece} (points : List Plane)
    (hnd : ∀ P ∈ pieces, P.Nondeg) :
    ∀ p ∈ points, ∀ Q ∈ subdivide pieces points, p ∉ Q.interior := by
  induction points generalizing pieces with
  | nil => simp
  | cons p ps ih =>
    intro q hq Q hQ
    rcases List.mem_cons.1 hq with rfl | hq
    · -- `q` was cut out at this step; permanence keeps it out of every later piece.
      obtain ⟨R, hR, hQR⟩ := subdivide_interior_subset (splitAllAt q pieces) ps Q hQ
      exact fun hmem => splitAllAt_avoids q hnd R hR (hQR hmem)
    · exact ih (pieces := splitAllAt p pieces) (splitAllAt_ne p hnd) q hq Q hQ

end Schoenflies

end BundlePart398

section BundlePart399
/- Source: dev/planar_search/schoenflies_port/Schoenflies/SegmentMeet.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/


/-!
# How two segments meet

Two segments meet in nothing, or in a segment. The blueprint says "the empty set, one
point, or one closed interval" (Lemma 3.7, polygonal overlay); a point *is* a segment with
equal endpoints, so the statement folds to a dichotomy, and that is the form the overlay
wants — it subdivides at the endpoints of whatever the meet turns out to be, and a
degenerate meet contributes one subdivision point.

No case analysis on whether the segments are parallel, and no determinant. The meet is
compact and convex, so its preimage under the parametrization `lineMap a b` is a compact
convex subset of `ℝ`, hence a closed interval; pushing that interval forward is a segment.

## Blueprint

* `segment_inter_segment` — the meet dichotomy used by Lemma 3.7.
-/

open Metric Set

namespace Schoenflies

/-- Two segments meet in nothing, or in a segment. -/
theorem segment_inter_segment (a b c d : Plane)
    (hne : (segment ℝ a b ∩ segment ℝ c d).Nonempty) :
    ∃ p q : Plane, segment ℝ a b ∩ segment ℝ c d = segment ℝ p q := by
  set S : Set Plane := segment ℝ a b ∩ segment ℝ c d with hSdef
  have hScompact : IsCompact S := (isCompact_segment a b).inter (isCompact_segment c d)
  have hSconvex : Convex ℝ S := (convex_segment a b).inter (convex_segment c d)
  -- Pull the meet back along the parametrization of the first segment.
  set f : ℝ →ᵃ[ℝ] Plane := AffineMap.lineMap a b with hfdef
  set T : Set ℝ := Icc 0 1 ∩ f ⁻¹' S with hTdef
  -- `T` carries `S` forward. Note this needs no injectivity of `f`, so the degenerate case
  -- `a = b` is not a separate case.
  have himage : f '' T = S := by
    refine subset_antisymm (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨t, ht, rfl⟩ := hx
      exact ht.2
    · have : x ∈ segment ℝ a b := hx.1
      rw [segment_eq_image_lineMap] at this
      obtain ⟨t, ht, rfl⟩ := this
      exact ⟨t, ⟨ht, hx⟩, rfl⟩
  have hTne : T.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    have : x ∈ f '' T := by rw [himage]; exact hx
    obtain ⟨t, ht, -⟩ := this
    exact ⟨t, ht⟩
  have hTcompact : IsCompact T :=
    isCompact_Icc.of_isClosed_subset
      (isClosed_Icc.inter (hScompact.isClosed.preimage AffineMap.lineMap_continuous))
      inter_subset_left
  have hTconvex : Convex ℝ T := (convex_Icc 0 1).inter (hSconvex.affine_preimage f)
  -- A nonempty compact convex subset of `ℝ` is a closed interval.
  obtain ⟨t₀, t₁, hTIcc⟩ : ∃ t₀ t₁, T = Icc t₀ t₁ :=
    ⟨_, _, eq_Icc_of_connected_compact ⟨hTne, hTconvex.isPreconnected⟩ hTcompact⟩
  have hle : t₀ ≤ t₁ := by
    rw [hTIcc] at hTne
    exact nonempty_Icc.1 hTne
  exact ⟨f t₀, f t₁, by rw [← himage, hTIcc, ← segment_eq_Icc hle, image_segment]⟩

end Schoenflies

end BundlePart399

section BundlePart400
/- Source: dev/planar_search/schoenflies_port/Schoenflies/Overlay.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/






/-!
# The polygonal overlay

Finitely many segments become a plane graph once they are subdivided at their meets and each
duplicated subsegment is named once (`lem:polygonal-overlay`).

## Blueprint

* `polygonal_overlay` — Lemma 3.7 (polygonal overlay).
-/

open Metric Set

namespace Schoenflies

/-! ### Two more properties of `subdivide`

Both belong in `Schoenflies/Subdivide.lean` beside the other four; they are here because that
module is on `main`.

`subdivide_subset` is `subdivide_interior_subset` with the **closed** inclusion carried
alongside the open one, in one existential: separation reads a piece's ends off its source
segment and its interior off the source's interior, and it needs both at the same source.

`subdivide_ends` is the endpoint criterion — an end of a piece that is not a cut point was an
end all along. Without it the case of two pieces from different sources does not close: two
different subpieces can both sit inside one long overlap. -/

/-- Cutting one piece keeps each half inside the whole, closed and open at once. -/
theorem splitAt_subset (p : Plane) (P : Piece) :
    ∀ Q ∈ splitAt p P, Q.seg ⊆ P.seg ∧ Q.interior ⊆ P.interior := by
  classical
  unfold splitAt
  split_ifs with h
  · have hp : p ∈ P.seg := openSegment_subset_segment ℝ _ _ h
    intro Q hQ
    rcases List.mem_cons.1 hQ with rfl | hQ
    · exact ⟨(convex_segment P.1 P.2).segment_subset (left_mem_segment ℝ _ _) hp,
        openSegment_left_subset h⟩
    · rcases List.mem_singleton.1 hQ with rfl
      exact ⟨(convex_segment P.1 P.2).segment_subset hp (right_mem_segment ℝ _ _),
        openSegment_right_subset h⟩
  · intro Q hQ
    rcases List.mem_singleton.1 hQ with rfl
    exact ⟨subset_rfl, subset_rfl⟩

theorem splitAllAt_subset (p : Plane) (pieces : List Piece) :
    ∀ Q ∈ splitAllAt p pieces, ∃ P ∈ pieces, Q.seg ⊆ P.seg ∧ Q.interior ⊆ P.interior := by
  intro Q hQ
  obtain ⟨P, hP, hQP⟩ := List.mem_flatMap.1 hQ
  exact ⟨P, hP, splitAt_subset p P Q hQP⟩

/-- Every piece of a subdivision lies inside a piece it came from, both as a segment and as an
interior — and at the **same** source. -/
theorem subdivide_subset (pieces : List Piece) (points : List Plane) :
    ∀ Q ∈ subdivide pieces points, ∃ P ∈ pieces, Q.seg ⊆ P.seg ∧ Q.interior ⊆ P.interior := by
  induction points generalizing pieces with
  | nil => exact fun Q hQ => ⟨Q, hQ, subset_rfl, subset_rfl⟩
  | cons p ps ih =>
    intro Q hQ
    obtain ⟨R, hR, hQR, hQR'⟩ := ih (pieces := splitAllAt p pieces) Q hQ
    obtain ⟨P, hP, hRP, hRP'⟩ := splitAllAt_subset p pieces R hR
    exact ⟨P, hP, hQR.trans hRP, hQR'.trans hRP'⟩

/-- Cutting one piece introduces only the cut point as a new end. -/
theorem splitAt_ends (p : Plane) (P : Piece) :
    ∀ Q ∈ splitAt p P, ∀ z, (z = Q.1 ∨ z = Q.2) → z = p ∨ (z = P.1 ∨ z = P.2) := by
  classical
  unfold splitAt
  split_ifs with h
  · intro Q hQ z hz
    rcases List.mem_cons.1 hQ with rfl | hQ
    · rcases hz with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
    · rcases List.mem_singleton.1 hQ with rfl
      rcases hz with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr rfl)
  · intro Q hQ z hz
    rcases List.mem_singleton.1 hQ with rfl
    exact Or.inr hz

theorem splitAllAt_ends (p : Plane) (pieces : List Piece) :
    ∀ Q ∈ splitAllAt p pieces, ∀ z, (z = Q.1 ∨ z = Q.2) →
      z = p ∨ ∃ P ∈ pieces, (z = P.1 ∨ z = P.2) := by
  intro Q hQ z hz
  obtain ⟨P, hP, hQP⟩ := List.mem_flatMap.1 hQ
  rcases splitAt_ends p P Q hQP z hz with h | h
  · exact Or.inl h
  · exact Or.inr ⟨P, hP, h⟩

/-- **The endpoint criterion.** An end of a piece of the subdivision is either a cut point or
was an end of a source piece all along. -/
theorem subdivide_ends (pieces : List Piece) (points : List Plane) :
    ∀ Q ∈ subdivide pieces points, ∀ z, (z = Q.1 ∨ z = Q.2) →
      z ∈ points ∨ ∃ P ∈ pieces, (z = P.1 ∨ z = P.2) := by
  induction points generalizing pieces with
  | nil => exact fun Q hQ z hz => Or.inr ⟨Q, hQ, hz⟩
  | cons p ps ih =>
    intro Q hQ z hz
    rcases ih (pieces := splitAllAt p pieces) Q hQ z hz with h | ⟨R, hR, hzR⟩
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · rcases splitAllAt_ends p pieces R hR z hzR with rfl | ⟨P, hP, hzP⟩
      · exact Or.inl (List.mem_cons_self ..)
      · exact Or.inr ⟨P, hP, hzP⟩

/-! ### What the cut points have to cover

Two conditions, and between them they are the blueprint's "subdivide at all old endpoints,
isolated intersections, and endpoints of overlapping intervals". The second asks for **some**
pair of ends of each meet rather than every pair, because that is what a construction can
supply: a meet is `segment ℝ u v` and `segment ℝ v u` alike, and that a nondegenerate
segment's ends are determined by its point set is a theorem this development does not have and
does not need. -/

/-- Where two pieces meet. -/
def meetOf (P Q : Piece) : Set Plane := P.seg ∩ Q.seg

theorem meetOf_comm (P Q : Piece) : meetOf P Q = meetOf Q P := inter_comm _ _

/-- Every end of every source piece is a cut point. -/
def EndsAreCut (pieces : List Piece) (points : List Plane) : Prop :=
  ∀ P ∈ pieces, ∀ z, (z = P.1 ∨ z = P.2) → z ∈ points

/-- For every pair of distinct source pieces that meet, some pair of ends of the meet is
cut. -/
def MeetsAreCut (pieces : List Piece) (points : List Plane) : Prop :=
  ∀ P ∈ pieces, ∀ Q ∈ pieces, P ≠ Q → (meetOf P Q).Nonempty →
    ∃ u v, meetOf P Q = segment ℝ u v ∧ u ∈ points ∧ v ∈ points

/-- With the source ends cut too, the endpoint criterion says outright that every end of every
piece of the subdivision is a cut point. -/
theorem subdivide_ends_are_cuts {pieces : List Piece} {points : List Plane}
    (h : EndsAreCut pieces points) :
    ∀ Q ∈ subdivide pieces points, ∀ z, (z = Q.1 ∨ z = Q.2) → z ∈ points := by
  intro Q hQ z hz
  rcases subdivide_ends pieces points Q hQ z hz with h' | ⟨P, hP, hzP⟩
  · exact h'
  · exact h P hP z hzP

/-! ### Producing the cut points

Nothing computes them. The overlay is stated existentially, so the list is built by the
induction that proves it exists, and `segment_inter_segment` hands over the ends of a meet the
moment the meet is known to be nonempty. That is what keeps the choice operator out: the
witnesses of `segment_inter_segment` are not unique, so there is nothing to name. -/

/-- One piece against a list: a point list holding both ends of every meet. -/
theorem exists_meet_points (P : Piece) (others : List Piece) :
    ∃ points : List Plane, ∀ Q ∈ others, (meetOf P Q).Nonempty →
      ∃ u v, meetOf P Q = segment ℝ u v ∧ u ∈ points ∧ v ∈ points := by
  induction others with
  | nil => exact ⟨[], by simp⟩
  | cons R rs ih =>
    obtain ⟨tailPoints, htail⟩ := ih
    by_cases hR : (meetOf P R).Nonempty
    · obtain ⟨u, v, huv⟩ := segment_inter_segment P.1 P.2 R.1 R.2 hR
      refine ⟨u :: v :: tailPoints, fun Q hQ hne => ?_⟩
      rcases List.mem_cons.1 hQ with rfl | hQ
      · exact ⟨u, v, huv, by simp, by simp⟩
      · obtain ⟨s, t, hst, hs, ht⟩ := htail Q hQ hne
        exact ⟨s, t, hst, by simp [hs], by simp [ht]⟩
    · refine ⟨tailPoints, fun Q hQ hne => ?_⟩
      rcases List.mem_cons.1 hQ with rfl | hQ
      · exact absurd hne hR
      · exact htail Q hQ hne

/-- The whole list: the ends of each piece, and both ends of each meet. No sort and no choice
operator — the point list is existential throughout. -/
theorem exists_cut_points (pieces : List Piece) :
    ∃ points : List Plane, EndsAreCut pieces points ∧ MeetsAreCut pieces points := by
  induction pieces with
  | nil => exact ⟨[], by simp [EndsAreCut], by simp [MeetsAreCut]⟩
  | cons R rs ih =>
    obtain ⟨tailPoints, hEnds, hMeets⟩ := ih
    obtain ⟨meetPoints, hHead⟩ := exists_meet_points R rs
    refine ⟨R.1 :: R.2 :: (meetPoints ++ tailPoints), fun P hP z hz => ?_,
      fun P hP Q hQ hPQ hne => ?_⟩
    · -- The head's two ends open the list; the tail's ends are already in `tailPoints`.
      rcases List.mem_cons.1 hP with rfl | hPt
      · rcases hz with rfl | rfl <;> simp
      · have := hEnds P hPt z hz
        simp [this]
    · -- A pair involving the head is covered by `meetPoints`, in whichever order it is asked
      -- for; a pair inside the tail was covered already.
      rcases List.mem_cons.1 hP with hPh | hPt
      · rcases List.mem_cons.1 hQ with hQh | hQt
        · exact absurd (hPh.trans hQh.symm) hPQ
        · subst hPh
          obtain ⟨u, v, huv, hu, hv⟩ := hHead Q hQt hne
          exact ⟨u, v, huv, by simp [hu], by simp [hv]⟩
      · rcases List.mem_cons.1 hQ with hQh | hQt
        · subst hQh
          have hne' : (meetOf Q P).Nonempty := by rwa [meetOf_comm]
          obtain ⟨u, v, huv, hu, hv⟩ := hHead P hPt hne'
          exact ⟨u, v, by rw [meetOf_comm]; exact huv, by simp [hu], by simp [hv]⟩
        · obtain ⟨u, v, huv, hu, hv⟩ := hMeets P hPt Q hQt hPQ hne
          exact ⟨u, v, huv, by simp [hu], by simp [hv]⟩

/-! ### Separation

Cut at every end of every source piece and at both ends of every meet, and two pieces of the
subdivision that share an interior point are the **same** segment — equal, not disjoint.
Overlapping collinear pieces cannot be pulled apart by cutting; after enough cuts they
coincide, which is what the blueprint's deduplication clause is for. -/

/-- Collinearity: two pieces of the subdivision that share an interior point lie inside one
nondegenerate segment. If they came from the same source piece, that piece; if from different
ones, the sources' overlap — nondegenerate because the shared point is interior to it, the
overlap's ends being cut points and so interior to nothing. -/
theorem subdivide_common_segment {pieces : List Piece} {points : List Plane}
    (hnd : ∀ P ∈ pieces, P.Nondeg) (hMeets : MeetsAreCut pieces points)
    {P Q : Piece} (hP : P ∈ subdivide pieces points) (hQ : Q ∈ subdivide pieces points)
    {x : Plane} (hxP : x ∈ P.interior) (hxQ : x ∈ Q.interior) :
    ∃ A : Piece, A.Nondeg ∧ P.seg ⊆ A.seg ∧ Q.seg ⊆ A.seg := by
  obtain ⟨p, hp, hPseg, hPint⟩ := subdivide_subset pieces points P hP
  obtain ⟨q, hq, hQseg, hQint⟩ := subdivide_subset pieces points Q hQ
  by_cases hpq : p = q
  · subst hpq
    exact ⟨p, hnd p hp, hPseg, hQseg⟩
  -- The sources meet at `x`, so their meet is a segment with both ends cut.
  have hxp : x ∈ p.seg := openSegment_subset_segment ℝ _ _ (hPint hxP)
  have hxq : x ∈ q.seg := openSegment_subset_segment ℝ _ _ (hQint hxQ)
  obtain ⟨u, v, huv, hu, hv⟩ := hMeets p hp q hq hpq ⟨x, hxp, hxq⟩
  have hux : u ∉ P.interior := subdivide_avoids points hnd u hu P hP
  have hvx : v ∉ P.interior := subdivide_avoids points hnd v hv P hP
  have huy : u ∉ Q.interior := subdivide_avoids points hnd u hu Q hQ
  have hvy : v ∉ Q.interior := subdivide_avoids points hnd v hv Q hQ
  -- `x` is interior to the meet: it lies on it, and it is neither of its ends.
  have hxuv : x ∈ segment ℝ u v := huv ▸ ⟨hxp, hxq⟩
  have hxu : u ≠ x := fun h => hux (h ▸ hxP)
  have hxv : v ≠ x := fun h => hvx (h ▸ hxP)
  have hxopen : x ∈ openSegment ℝ u v := mem_openSegment_of_ne_left_right hxu hxv hxuv
  have huvne : u ≠ v := by
    rintro rfl
    rw [openSegment_same, mem_singleton_iff] at hxopen
    exact hxu hxopen.symm
  -- Both ends of the meet lie on both sources, so each one-dimensional citation has its
  -- ambient segment.
  have hsubp : segment ℝ u v ⊆ p.seg := huv ▸ inter_subset_left
  have hsubq : segment ℝ u v ⊆ q.seg := huv ▸ inter_subset_right
  refine ⟨(u, v), huvne, ?_, ?_⟩
  · exact segment_inside_of_ends_outside (hnd p hp)
      (hPseg (left_mem_segment ℝ _ _)) (hPseg (right_mem_segment ℝ _ _))
      (hsubp (left_mem_segment ℝ _ _)) (hsubp (right_mem_segment ℝ _ _))
      hxP hxopen hux hvx
  · exact segment_inside_of_ends_outside (hnd q hq)
      (hQseg (left_mem_segment ℝ _ _)) (hQseg (right_mem_segment ℝ _ _))
      (hsubq (left_mem_segment ℝ _ _)) (hsubq (right_mem_segment ℝ _ _))
      hxQ hxopen huy hvy

/-- **Separation.** Two pieces of the subdivision that share an interior point are the same
segment, in one order or the other. -/
theorem subdivide_separated {pieces : List Piece} {points : List Plane}
    (hnd : ∀ P ∈ pieces, P.Nondeg) (hEnds : EndsAreCut pieces points)
    (hMeets : MeetsAreCut pieces points)
    {P Q : Piece} (hP : P ∈ subdivide pieces points) (hQ : Q ∈ subdivide pieces points)
    {x : Plane} (hxP : x ∈ P.interior) (hxQ : x ∈ Q.interior) :
    P = Q ∨ P = (Q.2, Q.1) := by
  -- Every end of every piece is a cut point, hence interior to nothing.
  have cut : ∀ R ∈ subdivide pieces points, ∀ z, (z = R.1 ∨ z = R.2) → z ∈ points :=
    subdivide_ends_are_cuts hEnds
  have h₁ : Q.1 ∉ P.interior :=
    subdivide_avoids points hnd _ (cut Q hQ _ (Or.inl rfl)) P hP
  have h₂ : Q.2 ∉ P.interior :=
    subdivide_avoids points hnd _ (cut Q hQ _ (Or.inr rfl)) P hP
  have h₃ : P.1 ∉ Q.interior :=
    subdivide_avoids points hnd _ (cut P hP _ (Or.inl rfl)) Q hQ
  have h₄ : P.2 ∉ Q.interior :=
    subdivide_avoids points hnd _ (cut P hP _ (Or.inr rfl)) Q hQ
  obtain ⟨A, hA, hPA, hQA⟩ := subdivide_common_segment hnd hMeets hP hQ hxP hxQ
  rcases same_ends_of_meeting_interiors hA
      (hPA (left_mem_segment ℝ _ _)) (hPA (right_mem_segment ℝ _ _))
      (hQA (left_mem_segment ℝ _ _)) (hQA (right_mem_segment ℝ _ _))
      hxP hxQ h₁ h₂ h₃ h₄ with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
  · exact Or.inl (Prod.ext e₁ e₂)
  · exact Or.inr (Prod.ext e₁ e₂)

end Schoenflies

end BundlePart400

section BundlePart401
/- Source: dev/planar_search/schoenflies_port/Schoenflies/OverlayGraph.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/


/-!
# The polygonal overlay, assembled into a plane graph

`Schoenflies/Overlay.lean` does the separating half of `lem:polygonal-overlay`: after cutting
at the right points, two pieces of the subdivision whose interiors meet are the **same
segment**, in one order or the other. This module turns that into a plane graph.

The only thing standing between "the same segment" and "the same edge" is that a segment has
two names, `(a, b)` and `(b, a)`. `orientPiece` removes the choice by fixing a total order on
plane points — `Precedes`, lexicographic in the coordinates — and putting the smaller end
first. Two names for one segment then orient to the *same* name, so "represent each duplicated
subsegment once" stops being deduplication up to reversal and becomes deduplication up to
equality, which `List.dedup` does without knowing any geometry. Nothing geometric rests on
which order it is: only `precedes_total` and `eq_of_precedes_of_precedes` are ever used.

The graph is `overlayGraph`, a `Graph Plane Piece`: its edges are the oriented, deduplicated
pieces, and its vertices are their ends. `IsLink P x y` says that `P` is an edge and that `x`
and `y` are its two ends in one order or the other — which is why
`eq_or_eq_of_isLink_of_isLink` is a two-line case split rather than an argument.

The three clauses of `Graph.IsDrawing` come out as follows.

* *Each edge is drawn by an arc between its ends* — `isArcBetween_segment`, given
  nondegeneracy, which `subdivide_ne` preserves and orienting does not disturb.
* *An edge's arc meets the vertex set only at its own ends* — a vertex is an end of some
  edge, hence a cut point, and `subdivide_avoids` says a cut point is interior to nothing.
* *Distinct edges meet only at shared vertices* — a common point that is an end of neither
  would be interior to both, and `subdivide_separated` would make the two pieces the same
  segment, hence (after orienting) the same name. Once it is an end of one it is a cut point,
  so it cannot be interior to the other either, and it is an end of both.

## Blueprint

* `Precedes`, `orientPiece` — the canonical orientation of a segment.
* `overlayPieces`, `overlayGraph`, `segmentDrawing` — the graph of Lemma 3.7.
* `polygonal_overlay` — Lemma 3.7 (polygonal overlay), the whole statement.
-/

open Metric Set
open scoped Graph

namespace Schoenflies

/-! ### A total order on plane points

It exists to pick one of two points canonically. Only two facts about it are used: that it
compares any two points, and that it cannot rank two distinct points both ways round. -/

/-- The lexicographic order on plane points: first coordinate, then second. -/
def Precedes (p q : Plane) : Prop := p 0 < q 0 ∨ (p 0 = q 0 ∧ p 1 ≤ q 1)

theorem precedes_total (p q : Plane) : Precedes p q ∨ Precedes q p := by
  rcases lt_trichotomy (p 0) (q 0) with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases le_total (p 1) (q 1) with h' | h'
    · exact Or.inl (Or.inr ⟨h, h'⟩)
    · exact Or.inr (Or.inr ⟨h.symm, h'⟩)
  · exact Or.inr (Or.inl h)

theorem eq_of_precedes_of_precedes {p q : Plane} (h : Precedes p q) (h' : Precedes q p) :
    p = q := by
  -- Both coordinates are pinned: the first by trichotomy, the second by antisymmetry of `≤`.
  have key : p 0 = q 0 ∧ p 1 = q 1 := by
    rcases h with h | ⟨ha, hb⟩ <;> rcases h' with h' | ⟨ha', hb'⟩
    · exact absurd h (asymm h')
    · exact absurd h (by rw [ha']; exact lt_irrefl _)
    · exact absurd h' (by rw [ha]; exact lt_irrefl _)
    · exact ⟨ha, le_antisymm hb hb'⟩
  ext i
  fin_cases i
  · exact key.1
  · exact key.2

/-! ### The canonical orientation of a piece -/

open scoped Classical in
/-- A piece with its ends in lexicographic order. Two names for one segment orient to the
same name; that is the whole purpose. -/
noncomputable def orientPiece (P : Piece) : Piece :=
  if Precedes P.1 P.2 then P else (P.2, P.1)

theorem orientPiece_of_precedes {P : Piece} (h : Precedes P.1 P.2) : orientPiece P = P := by
  classical
  exact if_pos h

theorem orientPiece_of_not_precedes {P : Piece} (h : ¬ Precedes P.1 P.2) :
    orientPiece P = (P.2, P.1) := by
  classical
  exact if_neg h

/-- Orienting does not move the segment. -/
@[simp] theorem orientPiece_seg (P : Piece) : (orientPiece P).seg = P.seg := by
  by_cases h : Precedes P.1 P.2
  · rw [orientPiece_of_precedes h]
  · rw [orientPiece_of_not_precedes h]; exact segment_symm ℝ _ _

/-- Nor the interior. -/
@[simp] theorem orientPiece_interior (P : Piece) : (orientPiece P).interior = P.interior := by
  by_cases h : Precedes P.1 P.2
  · rw [orientPiece_of_precedes h]
  · rw [orientPiece_of_not_precedes h]; exact openSegment_symm ℝ _ _

/-- Nor which points are its ends. -/
theorem orientPiece_ends (P : Piece) (z : Plane) :
    (z = (orientPiece P).1 ∨ z = (orientPiece P).2) ↔ (z = P.1 ∨ z = P.2) := by
  by_cases h : Precedes P.1 P.2
  · rw [orientPiece_of_precedes h]
  · rw [orientPiece_of_not_precedes h]; exact or_comm

theorem orientPiece_nondeg {P : Piece} (h : P.Nondeg) : (orientPiece P).Nondeg := by
  by_cases hp : Precedes P.1 P.2
  · rw [orientPiece_of_precedes hp]; exact h
  · rw [orientPiece_of_not_precedes hp]; exact fun e => h e.symm

/-- The output is oriented — which is what makes `orientPiece` idempotent. -/
theorem precedes_orientPiece (P : Piece) : Precedes (orientPiece P).1 (orientPiece P).2 := by
  by_cases h : Precedes P.1 P.2
  · rw [orientPiece_of_precedes h]; exact h
  · rw [orientPiece_of_not_precedes h]
    exact (precedes_total P.1 P.2).resolve_left h

@[simp] theorem orientPiece_idem (P : Piece) : orientPiece (orientPiece P) = orientPiece P :=
  orientPiece_of_precedes (precedes_orientPiece P)

/-- **Orienting forgets the name it was given.** This is the fact that makes deduplication
carry no geometry. -/
@[simp] theorem orientPiece_swap (P : Piece) : orientPiece (P.2, P.1) = orientPiece P := by
  by_cases h : Precedes P.1 P.2
  · rw [orientPiece_of_precedes h]
    by_cases h' : Precedes P.2 P.1
    · -- Each end precedes the other, so they are the same point and the pair is its own
      -- reversal.
      have he : P.1 = P.2 := eq_of_precedes_of_precedes h h'
      rw [orientPiece_of_precedes (P := (P.2, P.1)) h']
      exact Prod.ext he.symm he
    · rw [orientPiece_of_not_precedes (P := (P.2, P.1)) h']
  · rw [orientPiece_of_not_precedes h,
      orientPiece_of_precedes (P := (P.2, P.1)) ((precedes_total P.1 P.2).resolve_left h)]

/-! ### Deduplication

`cover` only sees which pieces are in the list, so both steps of the assembly — orienting and
deduplicating — leave it alone. -/

theorem cover_eq_of_mem_iff {l₁ l₂ : List Piece} (h : ∀ P, P ∈ l₁ ↔ P ∈ l₂) :
    cover l₁ = cover l₂ := by
  ext x
  simp only [cover, mem_iUnion, exists_prop]
  exact ⟨fun ⟨P, hP, hx⟩ => ⟨P, (h P).1 hP, hx⟩, fun ⟨P, hP, hx⟩ => ⟨P, (h P).2 hP, hx⟩⟩

theorem cover_map_orientPiece (l : List Piece) : cover (l.map orientPiece) = cover l := by
  ext x
  simp only [cover, mem_iUnion, exists_prop, List.mem_map]
  constructor
  · rintro ⟨P, ⟨Q, hQ, rfl⟩, hx⟩
    exact ⟨Q, hQ, by rwa [orientPiece_seg] at hx⟩
  · rintro ⟨Q, hQ, hx⟩
    exact ⟨orientPiece Q, ⟨Q, hQ, rfl⟩, by rwa [orientPiece_seg]⟩

open scoped Classical in
/-- The edges of the overlay: the pieces of the subdivision, oriented and then deduplicated.
Orienting is what makes the deduplication a plain list operation. -/
noncomputable def overlayPieces (pieces : List Piece) (points : List Plane) : List Piece :=
  ((subdivide pieces points).map orientPiece).dedup

theorem mem_overlayPieces {pieces : List Piece} {points : List Plane} {P : Piece} :
    P ∈ overlayPieces pieces points ↔ ∃ Q ∈ subdivide pieces points, orientPiece Q = P := by
  rw [overlayPieces, List.mem_dedup, List.mem_map]

/-- The list of edges has no duplicates. -/
theorem overlayPieces_nodup (pieces : List Piece) (points : List Plane) :
    (overlayPieces pieces points).Nodup :=
  List.nodup_dedup _

/-- Neither orienting nor deduplicating changes what the pieces occupy. -/
theorem overlayPieces_cover (pieces : List Piece) (points : List Plane) :
    cover (overlayPieces pieces points) = cover pieces := by
  rw [overlayPieces,
    cover_eq_of_mem_iff (l₂ := (subdivide pieces points).map orientPiece) fun _ => List.mem_dedup,
    cover_map_orientPiece, subdivide_cover]

theorem overlayPieces_nondeg {pieces : List Piece} (points : List Plane)
    (hnd : ∀ P ∈ pieces, P.Nondeg) : ∀ P ∈ overlayPieces pieces points, P.Nondeg := by
  intro P hP
  obtain ⟨Q, hQ, rfl⟩ := mem_overlayPieces.1 hP
  exact orientPiece_nondeg (subdivide_ne points hnd Q hQ)

/-- Every end of every edge is a cut point: orienting does not change which points are ends,
and `subdivide_ends_are_cuts` covers the subdivision. -/
theorem overlayPieces_ends_cut {pieces : List Piece} {points : List Plane}
    (hEnds : EndsAreCut pieces points) :
    ∀ P ∈ overlayPieces pieces points, ∀ z, (z = P.1 ∨ z = P.2) → z ∈ points := by
  intro P hP z hz
  obtain ⟨Q, hQ, rfl⟩ := mem_overlayPieces.1 hP
  exact subdivide_ends_are_cuts hEnds Q hQ z ((orientPiece_ends Q z).1 hz)

/-- And a cut point is interior to no edge. -/
theorem overlayPieces_avoids {pieces : List Piece} {points : List Plane}
    (hnd : ∀ P ∈ pieces, P.Nondeg) :
    ∀ p ∈ points, ∀ P ∈ overlayPieces pieces points, p ∉ P.interior := by
  intro p hp P hP
  obtain ⟨Q, hQ, rfl⟩ := mem_overlayPieces.1 hP
  rw [orientPiece_interior]
  exact subdivide_avoids points hnd p hp Q hQ

/-- **Distinct edges have disjoint interiors.** This is where separation is spent: two pieces
sharing an interior point are the same segment, so after orienting they are the same *name*,
and a deduplicated list holds a name once. -/
theorem overlayPieces_disjoint_interiors {pieces : List Piece} {points : List Plane}
    (hnd : ∀ P ∈ pieces, P.Nondeg) (hEnds : EndsAreCut pieces points)
    (hMeets : MeetsAreCut pieces points) {P Q : Piece}
    (hP : P ∈ overlayPieces pieces points) (hQ : Q ∈ overlayPieces pieces points)
    (hPQ : P ≠ Q) {x : Plane} (hxP : x ∈ P.interior) : x ∉ Q.interior := by
  intro hxQ
  obtain ⟨P', hP', rfl⟩ := mem_overlayPieces.1 hP
  obtain ⟨Q', hQ', rfl⟩ := mem_overlayPieces.1 hQ
  rw [orientPiece_interior] at hxP hxQ
  rcases subdivide_separated hnd hEnds hMeets hP' hQ' hxP hxQ with h | h
  · exact hPQ (by rw [h])
  · exact hPQ (by rw [h, orientPiece_swap])

/-! ### The graph -/

/-- The ends of a list of pieces. -/
def endSet (edges : List Piece) : Set Plane := {v | ∃ P ∈ edges, v = P.1 ∨ v = P.2}

/-- The overlay graph: the oriented deduplicated pieces as edges, their ends as vertices.

An edge links `x` and `y` exactly when they are its two ends in one order or the other, which
is what makes `eq_or_eq_of_isLink_of_isLink` a case split with no content. -/
noncomputable def overlayGraph (pieces : List Piece) (points : List Plane) :
    Graph Plane Piece where
  vertexSet := endSet (overlayPieces pieces points)
  IsLink P x y := P ∈ overlayPieces pieces points ∧
    ((x = P.1 ∧ y = P.2) ∨ (x = P.2 ∧ y = P.1))
  edgeSet := {P | P ∈ overlayPieces pieces points}
  isLink_symm := fun _ _ => ⟨fun _ _ h => ⟨h.1, by tauto⟩⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro P x y v w ⟨-, hxy⟩ ⟨-, hvw⟩
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hvw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  edge_mem_iff_exists_isLink := by
    intro P
    simp only [mem_setOf_eq]
    exact ⟨fun hP => ⟨P.1, P.2, hP, Or.inl ⟨rfl, rfl⟩⟩, fun ⟨_, _, hP, _⟩ => hP⟩
  left_mem_of_isLink := by
    rintro P x y ⟨hP, h⟩
    exact ⟨P, hP, by tauto⟩

variable {pieces : List Piece} {points : List Plane} {P : Piece} {x y v : Plane}

@[simp] theorem overlayGraph_vertexSet :
    V(overlayGraph pieces points) = endSet (overlayPieces pieces points) := rfl

@[simp] theorem overlayGraph_mem_edgeSet :
    P ∈ E(overlayGraph pieces points) ↔ P ∈ overlayPieces pieces points := Iff.rfl

@[simp] theorem overlayGraph_isLink :
    (overlayGraph pieces points).IsLink P x y ↔
      P ∈ overlayPieces pieces points ∧ ((x = P.1 ∧ y = P.2) ∨ (x = P.2 ∧ y = P.1)) := Iff.rfl

theorem overlayGraph_mem_vertexSet :
    v ∈ V(overlayGraph pieces points) ↔ ∃ P ∈ overlayPieces pieces points, v = P.1 ∨ v = P.2 :=
  Iff.rfl

/-- An end of an edge is a vertex. -/
theorem overlayGraph_inc (hP : P ∈ overlayPieces pieces points) (h : v = P.1 ∨ v = P.2) :
    (overlayGraph pieces points).Inc P v := by
  rcases h with rfl | rfl
  · exact ⟨P.2, hP, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨P.1, hP, Or.inr ⟨rfl, rfl⟩⟩

/-! ### The drawing

A straight edge is drawn by the affine parametrization of its segment, so the arc clause of
`IsDrawing` is `isArcBetween_segment` and nothing else. -/

/-- Every piece is drawn by the affine parametrization of its segment. -/
noncomputable def segmentDrawing (P : Piece) : ℝ → Plane := AffineMap.lineMap P.1 P.2

@[simp] theorem edgeArc_segmentDrawing (P : Piece) :
    Graph.edgeArc segmentDrawing P = P.seg :=
  (segment_eq_image_lineMap ℝ P.1 P.2).symm

/-- **The overlay graph is a plane graph.** -/
theorem overlayGraph_isDrawing (pieces : List Piece) (points : List Plane)
    (hnd : ∀ P ∈ pieces, P.Nondeg) (hEnds : EndsAreCut pieces points)
    (hMeets : MeetsAreCut pieces points) :
    Graph.IsDrawing (overlayGraph pieces points) segmentDrawing := by
  refine ⟨?_, ?_, ?_⟩
  · -- An edge is a nondegenerate segment, and `segmentDrawing` IS its parametrization.
    intro P hP
    have hne : P.Nondeg := overlayPieces_nondeg points hnd P (by simpa using hP)
    refine ⟨AffineMap.lineMap_continuous.continuousOn, injOn_lineMap hne, ?_⟩
    have h0 : segmentDrawing P 0 = P.1 := by simp [segmentDrawing]
    have h1 : segmentDrawing P 1 = P.2 := by simp [segmentDrawing]
    rw [h0, h1]
    exact ⟨by simpa using hP, Or.inl ⟨rfl, rfl⟩⟩
  · -- A vertex is an end of some edge, hence a cut point, hence interior to nothing; and a
    -- point of a segment that is not interior to it is one of its ends.
    rintro P a b w ⟨hP, h⟩ hw hwarc
    rw [edgeArc_segmentDrawing] at hwarc
    obtain ⟨R, hR, hwR⟩ := hw
    have hwint : w ∉ P.interior :=
      overlayPieces_avoids hnd w (overlayPieces_ends_cut hEnds R hR w hwR) P hP
    have hend : w = P.1 ∨ w = P.2 := by
      by_contra hcon
      push Not at hcon
      exact hwint (mem_openSegment_of_ne_left_right (Ne.symm hcon.1) (Ne.symm hcon.2) hwarc)
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hend
    · exact hend.symm
  · -- A common point is an end of both edges: if it were an end of neither it would be
    -- interior to both, and if it were an end of just one it would be a cut point, hence not
    -- interior to the other.
    rintro P Q hP hQ hPQ p hpP hpQ
    rw [overlayGraph_mem_edgeSet] at hP hQ
    rw [edgeArc_segmentDrawing] at hpP hpQ
    have key : ∀ A B : Piece, A ∈ overlayPieces pieces points →
        B ∈ overlayPieces pieces points → A ≠ B → p ∈ A.seg → p ∈ B.seg →
        (p = A.1 ∨ p = A.2) := by
      intro A B hA hB hAB hpA hpB
      by_contra hcon
      push Not at hcon
      have hintA : p ∈ A.interior :=
        mem_openSegment_of_ne_left_right (Ne.symm hcon.1) (Ne.symm hcon.2) hpA
      by_cases hendB : p = B.1 ∨ p = B.2
      · exact overlayPieces_avoids hnd p (overlayPieces_ends_cut hEnds B hB p hendB) A hA hintA
      · push Not at hendB
        have hintB : p ∈ B.interior :=
          mem_openSegment_of_ne_left_right (Ne.symm hendB.1) (Ne.symm hendB.2) hpB
        exact overlayPieces_disjoint_interiors hnd hEnds hMeets hA hB hAB hintA hintB
    have hendP := key P Q hP hQ hPQ hpP hpQ
    have hendQ := key Q P hQ hP (Ne.symm hPQ) hpQ hpP
    exact ⟨⟨P, hP, hendP⟩, overlayGraph_inc hP hendP, overlayGraph_inc hQ hendQ⟩

/-- What the graph occupies is what its edges occupy: every vertex is an end of an edge, so
the vertices add nothing. -/
theorem overlayGraph_pointSet (pieces : List Piece) (points : List Plane) :
    Graph.pointSet (overlayGraph pieces points) segmentDrawing = cover pieces := by
  rw [← overlayPieces_cover pieces points]
  ext z
  simp only [Graph.pointSet, mem_union, mem_iUnion, exists_prop, overlayGraph_vertexSet,
    endSet, mem_setOf_eq, overlayGraph_mem_edgeSet, edgeArc_segmentDrawing, cover]
  constructor
  · rintro (⟨P, hP, hzP⟩ | ⟨P, hP, hzP⟩)
    · refine ⟨P, hP, ?_⟩
      rcases hzP with rfl | rfl
      · exact left_mem_segment ℝ _ _
      · exact right_mem_segment ℝ _ _
    · exact ⟨P, hP, hzP⟩
  · rintro ⟨P, hP, hzP⟩
    exact Or.inr ⟨P, hP, hzP⟩

/-! ### Finiteness

Without this the whole face and outer-face machinery of `Schoenflies/Graph/Drawing.lean` and
`Schoenflies/Graph/OuterFace.lean` is inapplicable to the overlay, since every statement there
carries a `[G.Finite]` instance. Both sets come from one finite list, so it is immediate — but
it has to be said, and the instance has to be found by typeclass search at the call site. -/

theorem finite_endSet (edges : List Piece) : (endSet edges).Finite := by
  -- The end set is the image of a finite list under the two projections.
  have : endSet edges ⊆ (fun P : Piece => P.1) '' {P | P ∈ edges}
      ∪ (fun P : Piece => P.2) '' {P | P ∈ edges} := by
    rintro v ⟨P, hP, rfl | rfl⟩
    · exact Or.inl ⟨P, hP, rfl⟩
    · exact Or.inr ⟨P, hP, rfl⟩
  exact Set.Finite.subset
    ((edges.finite_toSet.image _).union (edges.finite_toSet.image _)) this

instance overlayGraph_finite (pieces : List Piece) (points : List Plane) :
    Graph.Finite (overlayGraph pieces points) where
  finite_vertexSet := finite_endSet _
  finite_edgeSet := (overlayPieces pieces points).finite_toSet

/-- **Lemma 3.7 (polygonal overlay).** Finitely many nondegenerate segments are the point set
of a *finite* plane graph.

The finiteness clause is not decoration. Every statement about faces and about the outer face
carries a `[G.Finite]` instance, and an existential that produced only `IsDrawing` would hide
the graph behind a binder with no way to recover the instance — so the overlay could not be
fed to the face machinery at all. -/
theorem polygonal_overlay (pieces : List Piece) (hnd : ∀ P ∈ pieces, P.Nondeg) :
    ∃ G : Graph Plane Piece, Graph.Finite G ∧ Graph.IsDrawing G segmentDrawing ∧
      Graph.pointSet G segmentDrawing = cover pieces := by
  obtain ⟨points, hEnds, hMeets⟩ := exists_cut_points pieces
  exact ⟨overlayGraph pieces points, overlayGraph_finite pieces points,
    overlayGraph_isDrawing pieces points hnd hEnds hMeets,
    overlayGraph_pointSet pieces points⟩

end Schoenflies

end BundlePart401

section BundlePart402
/- Source: dev/planar_search/schoenflies_port/Schoenflies/SimpleArc.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/



/-!
# Simple polygonal arcs

`Schoenflies/PolyPath.lean` joins two points of a region by a polygonal *path* — a vertex list
whose carrier stays inside the region. A path may cross itself, so it is not an arc. This
module supplies the missing half of Lemma 1.1 and, with it, Lemma 1.2, by running the
blueprint's recipe: *subdivide at all intersections, delete duplicate subsegments, and take a
simple path in the resulting finite graph.*

The three steps are already available.

* Subdividing and deduplicating is `Schoenflies.overlayGraph`: a finite list of nondegenerate
  segments becomes a finite plane graph whose point set is exactly their union
  (`Schoenflies.overlayGraph_pointSet`).
* A simple path in that graph is `Graph.IsPath`, produced by `Graph.Reaches.exists_isPath`.
* Its realisation is an arc between its ends, by `Graph.IsDrawing.path_isArcBetween`.

## What actually has to be proved here

Two things, and neither is in the list above.

**The graph is connected when the union is.** The overlay is built from geometry, so nothing
so far says that two points joined *in the plane* are joined *along edges*. The argument is a
clopen one: for a vertex `a`, the points carried by the edges the walk relation can reach from
`a` form a compact set, the points carried by the other edges form another, the two are
disjoint — a common point would be a vertex incident with edges from both classes, by the
drawing condition — and together they are the whole union. Preconnectedness then forces the
second class to carry nothing.

**The realisation of a path is `poly` of a vertex list.** `Graph.IsDrawing.path_isArcBetween`
delivers `Graph.edgesCover`, a union of edge arcs with no order in it, while `IsPolygonal` and
every polygonal consumer downstream want a vertex list. `Schoenflies.exists_poly_eq_edgesCover`
recovers one by induction along the walk. Its statement returns the list, not the bare
existence of *some* polygonal set, so a consumer that needs the vertices — the redrawing
argument does — still has them.

Both endpoints have to be vertices of the overlay, which is arranged by putting them on the
list of cut points: `EndsAreCut` and `MeetsAreCut` only ask that certain points *occur* in
that list, so lengthening it is free.

## Blueprint

* `Schoenflies.segsOf`, `Schoenflies.cover_segsOf` — a vertex list read as a list of
  nondegenerate segments, the input format the overlay wants.
* `Schoenflies.overlayGraph_reaches` — the overlay graph of a connected union is connected.
* `Schoenflies.exists_simple_poly_of_cover` — Lemma 1.2 (finite polygonal unions), for a union
  given as a finite list of nondegenerate segments.
* `Schoenflies.exists_simple_poly_of_poly`, `Schoenflies.exists_simple_poly_of_isPolygonal` —
  Lemma 1.2 for a set presented as a polygonal carrier.
* `Schoenflies.exists_simple_poly_of_biUnion`, `Schoenflies.exists_simple_poly_of_union` —
  Lemma 1.2 as the blueprint states it, for a finite union of polygonal sets.
* `Schoenflies.exists_simple_poly_of_isPreconnected`,
  `Schoenflies.exists_simple_arc_of_isPreconnected` — Lemma 1.1 (polygonal connectedness), in
  full: any two points of a region are joined in it by a *simple* polygonal arc.

## Two lemmas that belong elsewhere

`Schoenflies.cover_flatMap_list` generalises `Schoenflies.cover_flatMap` to an arbitrary index
list and belongs beside it in `Schoenflies/Subdivide.lean`; `Schoenflies.subset_of_finite_diff`
is a general fact about preconnected sets. Both are here only because their homes are on
`main`.
-/

open Metric Set
open scoped Graph

namespace Schoenflies

variable {pieces : List Piece} {points : List Plane} {Ω : Set Plane} {a b x y : Plane}

/-! ### One more shape of `poly`

`poly_cons_cons` peels a segment off a list of length at least two. The overlay's induction
peels one off a list known only to be nonempty, so it needs the head as a term rather than as
a pattern. -/

/-- Prepending a vertex to a nonempty list adds the segment to its head. -/
theorem poly_cons_of_ne_nil {vs : List Plane} (h : vs ≠ []) (u : Plane) :
    poly (u :: vs) = segment ℝ u (vs.head h) ∪ poly vs := by
  match vs, h with
  | _ :: _, _ => rfl

/-! ### The segments of a vertex list

`poly` is a *chain*: consecutive vertices, with repetitions allowed. The overlay takes a list
of pieces and insists that each be nondegenerate, so a repetition has to be dropped rather
than passed on. Dropping one is harmless — a degenerate segment is a single point, and that
point is an end of the neighbouring segment — except when the whole chain degenerates to a
point, which is the second disjunct of `cover_segsOf`. -/

open scoped Classical in
/-- The nondegenerate segments of a polygonal chain, in order. A repeated vertex contributes
nothing. -/
noncomputable def segsOf : List Plane → List Piece
  | [] => []
  | [_] => []
  | u :: v :: rest => if u = v then segsOf (v :: rest) else (u, v) :: segsOf (v :: rest)

@[simp] theorem segsOf_nil : segsOf [] = [] := rfl

@[simp] theorem segsOf_singleton (v : Plane) : segsOf [v] = [] := rfl

open scoped Classical in
theorem segsOf_cons_cons (u v : Plane) (rest : List Plane) :
    segsOf (u :: v :: rest) =
      if u = v then segsOf (v :: rest) else (u, v) :: segsOf (v :: rest) := rfl

/-- Every segment produced is nondegenerate — which is the whole point of the definition. -/
theorem segsOf_nondeg (vs : List Plane) : ∀ P ∈ segsOf vs, P.Nondeg := by
  classical
  induction vs with
  | nil => simp
  | cons u tl ih =>
    match tl, ih with
    | [], _ => simp
    | v :: rest, ih =>
      rw [segsOf_cons_cons]
      split_ifs with huv
      · exact ih
      · intro P hP
        rcases List.mem_cons.1 hP with rfl | hP
        · exact huv
        · exact ih P hP

/-- The segments of a chain occupy the chain — unless the chain has collapsed to a point (or
to nothing), in which case there are no segments at all. -/
theorem cover_segsOf (vs : List Plane) :
    cover (segsOf vs) = poly vs ∨ (segsOf vs = [] ∧ (poly vs).Subsingleton) := by
  classical
  induction vs with
  | nil => exact Or.inr ⟨rfl, by simp⟩
  | cons u tl ih =>
    match tl, ih with
    | [], _ => exact Or.inr ⟨rfl, by simp [Set.Subsingleton]⟩
    | v :: rest, ih =>
      rw [segsOf_cons_cons, poly_cons_cons]
      by_cases huv : u = v
      · -- A repeated vertex contributes the point `u`, which the rest of the chain already
        -- holds.
        subst huv
        rw [if_pos rfl, segment_same]
        have hmem : u ∈ poly (u :: rest) := mem_poly_of_mem (List.mem_cons_self ..)
        rcases ih with h | ⟨h1, h2⟩
        · exact Or.inl (by rw [h, union_eq_self_of_subset_left (singleton_subset_iff.2 hmem)])
        · refine Or.inr ⟨h1, ?_⟩
          rw [union_eq_self_of_subset_left (singleton_subset_iff.2 hmem)]
          exact h2
      · rw [if_neg huv, cover_cons]
        refine Or.inl ?_
        rcases ih with h | ⟨h1, h2⟩
        · rw [h]; rfl
        · -- The rest of the chain is the single point `v`, already an end of the new segment.
          rw [h1, cover_nil, union_empty,
            h2.eq_singleton_of_mem (mem_poly_of_mem (List.mem_cons_self ..)),
            union_eq_self_of_subset_right (singleton_subset_iff.2 (right_mem_segment ℝ u v))]
          rfl

/-- When a chain carries two distinct points it has not collapsed, so its segments occupy
exactly it. -/
theorem cover_segsOf_eq {vs : List Plane} (ha : a ∈ poly vs) (hb : b ∈ poly vs)
    (hab : a ≠ b) : cover (segsOf vs) = poly vs := by
  rcases cover_segsOf vs with h | ⟨-, h⟩
  · exact h
  · exact absurd (h ha hb) hab

/-! ### The realisation of a walk is a polygonal chain

`Graph.edgesCover` is a union with no order in it. The walk supplies the order, and the
induction reads the vertex list off it. -/

/-- **The realisation of a nonempty walk of the overlay graph is the carrier of a vertex
list**, running from the walk's source to its target.

The list is returned rather than an unnamed polygonal set: the consumers of Lemma 1.1 that
overlay the arc with something else need its vertices. -/
theorem exists_poly_eq_edgesCover {u v : Plane} {W : List Piece}
    (hW : (overlayGraph pieces points).IsWalk u W v) (hne : W ≠ []) :
    ∃ vs : List Plane, ∃ h : vs ≠ [], vs.head h = u ∧ vs.getLast h = v ∧
      poly vs = Graph.edgesCover segmentDrawing W := by
  induction hW with
  | nil => exact absurd rfl hne
  | @cons u w v e W hl hW ih =>
    -- The edge's arc is the segment from the source to the waypoint, in whichever order the
    -- edge names its ends.
    have hedge : Graph.edgeArc segmentDrawing e = segment ℝ u w := by
      rw [edgeArc_segmentDrawing]
      rcases (overlayGraph_isLink.1 hl).2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact segment_symm ℝ _ _
    rcases eq_or_ne W [] with rfl | hWne
    · have hwv : w = v := hW.eq_of_nil
      subst hwv
      refine ⟨[u, w], by simp, rfl, by simp, ?_⟩
      rw [poly_pair, Graph.edgesCover_cons, Graph.edgesCover_nil, union_empty, hedge]
    · obtain ⟨vs, hvs, hhead, hlast, hpoly⟩ := ih hWne
      refine ⟨u :: vs, by simp, rfl, ?_, ?_⟩
      · rw [List.getLast_cons hvs]; exact hlast
      · rw [poly_cons_of_ne_nil hvs, hhead, hpoly, Graph.edgesCover_cons, hedge]

/-! ### The overlay graph of a connected union is connected

Nothing built so far relates the plane topology of the union to the walk relation of the
graph. This is where they meet. -/

/-- Both ends of an edge reach the same vertices. -/
theorem overlayGraph_reaches_end {P : Piece} (hP : P ∈ overlayPieces pieces points)
    (hz : x = P.1 ∨ x = P.2) :
    (overlayGraph pieces points).Reaches a P.1 ↔ (overlayGraph pieces points).Reaches a x := by
  have hlink : (overlayGraph pieces points).IsLink P P.1 P.2 :=
    overlayGraph_isLink.2 ⟨hP, Or.inl ⟨rfl, rfl⟩⟩
  rcases hz with rfl | rfl
  · exact Iff.rfl
  · exact ⟨fun h => h.trans (Graph.Reaches.of_isLink hlink),
      fun h => h.trans (Graph.Reaches.of_isLink hlink).symm⟩

/-- A cut point on the union is a vertex: it lies on some edge, and a cut point is interior to
no edge, so it is one of that edge's two ends. -/
theorem overlayGraph_mem_vertexSet_of_mem_cover (hnd : ∀ P ∈ pieces, P.Nondeg)
    (hxp : x ∈ points) (hx : x ∈ cover pieces) : x ∈ V(overlayGraph pieces points) := by
  rw [← overlayPieces_cover pieces points] at hx
  simp only [cover, mem_iUnion, exists_prop] at hx
  obtain ⟨P, hP, hxP⟩ := hx
  have hint : x ∉ P.interior := overlayPieces_avoids hnd x hxp P hP
  refine ⟨P, hP, ?_⟩
  by_contra hcon
  push Not at hcon
  exact hint (mem_openSegment_of_ne_left_right (Ne.symm hcon.1) (Ne.symm hcon.2) hxP)

/-- **The overlay graph of a connected union is connected**, in the form the construction
needs: any vertex reaches any other.

The proof is a clopen argument in the plane. Split the edges into those whose ends the walk
relation reaches from `a` and those it does not; each class carries a compact set, the two
carried sets cover the union, and they are disjoint — a common point would, by the drawing
condition, be a vertex incident with an edge of each class, and incidence is reachability.
Preconnectedness then leaves the second class carrying nothing. -/
theorem overlayGraph_reaches (hnd : ∀ P ∈ pieces, P.Nondeg)
    (hconn : IsPreconnected (cover pieces))
    (hEnds : EndsAreCut pieces points) (hMeets : MeetsAreCut pieces points)
    (hap : a ∈ points) (hbp : b ∈ points) (ha : a ∈ cover pieces) (hb : b ∈ cover pieces) :
    (overlayGraph pieces points).Reaches a b := by
  classical
  have hdraw : Graph.IsDrawing (overlayGraph pieces points) segmentDrawing :=
    overlayGraph_isDrawing pieces points hnd hEnds hMeets
  have haV : a ∈ V(overlayGraph pieces points) :=
    overlayGraph_mem_vertexSet_of_mem_cover hnd hap ha
  have hbV : b ∈ V(overlayGraph pieces points) :=
    overlayGraph_mem_vertexSet_of_mem_cover hnd hbp hb
  -- Every edge carries a link between its two ends; this is the only fact about the graph
  -- used below beyond the drawing condition.
  have hlink : ∀ P ∈ overlayPieces pieces points,
      (overlayGraph pieces points).IsLink P P.1 P.2 := fun P hP =>
    overlayGraph_isLink.2 ⟨hP, Or.inl ⟨rfl, rfl⟩⟩
  -- The two classes of edges, and the point sets they carry.
  set S : Set Plane :=
    ⋃ P ∈ {P | P ∈ overlayPieces pieces points ∧
      (overlayGraph pieces points).Reaches a P.1}, P.seg with hS
  set T : Set Plane :=
    ⋃ P ∈ {P | P ∈ overlayPieces pieces points ∧
      ¬ (overlayGraph pieces points).Reaches a P.1}, P.seg with hT
  have hSclosed : IsClosed S :=
    ((Set.Finite.subset (overlayPieces pieces points).finite_toSet
      fun _ hP => hP.1).isCompact_biUnion fun P _ => isCompact_segment P.1 P.2).isClosed
  have hTclosed : IsClosed T :=
    ((Set.Finite.subset (overlayPieces pieces points).finite_toSet
      fun _ hP => hP.1).isCompact_biUnion fun P _ => isCompact_segment P.1 P.2).isClosed
  -- The two classes carry the whole union between them.
  have hunion : ∀ z ∈ cover pieces, z ∈ S ∨ z ∈ T := by
    intro z hz
    rw [← overlayPieces_cover pieces points] at hz
    simp only [cover, mem_iUnion, exists_prop] at hz
    obtain ⟨P, hP, hzP⟩ := hz
    by_cases hr : (overlayGraph pieces points).Reaches a P.1
    · exact Or.inl (mem_biUnion (show P ∈ _ from ⟨hP, hr⟩) hzP)
    · exact Or.inr (mem_biUnion (show P ∈ _ from ⟨hP, hr⟩) hzP)
  -- And they carry disjoint sets: a common point is a vertex incident with an edge of each.
  have hdisj : ∀ z, z ∈ S → z ∈ T → False := by
    intro z hzS hzT
    simp only [hS, hT, mem_iUnion, mem_setOf_eq, exists_prop] at hzS hzT
    obtain ⟨P, ⟨hP, hPr⟩, hzP⟩ := hzS
    obtain ⟨Q, ⟨hQ, hQr⟩, hzQ⟩ := hzT
    have hPQ : P ≠ Q := by rintro rfl; exact hQr hPr
    obtain ⟨-, hincP, hincQ⟩ := hdraw.edge_inter (overlayGraph_mem_edgeSet.2 hP)
      (overlayGraph_mem_edgeSet.2 hQ) hPQ
      (by rwa [edgeArc_segmentDrawing]) (by rwa [edgeArc_segmentDrawing])
    have hzendP : z = P.1 ∨ z = P.2 := hincP.eq_or_eq_of_isLink (hlink P hP)
    have hzendQ : z = Q.1 ∨ z = Q.2 := hincQ.eq_or_eq_of_isLink (hlink Q hQ)
    exact hQr ((overlayGraph_reaches_end hQ hzendQ).2
      ((overlayGraph_reaches_end hP hzendP).1 hPr))
  -- `a` is carried by the reachable class, so that class is nonempty.
  have haS : a ∈ S := by
    obtain ⟨P, hP, hend⟩ := id haV
    refine mem_biUnion (show P ∈ _ from
      ⟨hP, (overlayGraph_reaches_end hP hend).2 (Graph.Reaches.refl haV)⟩) ?_
    rcases hend with rfl | rfl
    exacts [left_mem_segment ℝ _ _, right_mem_segment ℝ _ _]
  -- Preconnectedness: the far class carries nothing that the union contains.
  have hbS : b ∈ S := by
    by_contra hbnot
    have hbT : b ∈ T := (hunion b hb).resolve_left hbnot
    have hsub : cover pieces ⊆ Tᶜ ∪ Sᶜ := by
      intro w hw
      rcases hunion w hw with h | h
      · exact Or.inl fun h' => hdisj w h h'
      · exact Or.inr fun h' => hdisj w h' h
    obtain ⟨z, hzc, hzT, hzS⟩ := hconn Tᶜ Sᶜ hTclosed.isOpen_compl hSclosed.isOpen_compl
      hsub ⟨a, ha, fun h => hdisj a haS h⟩ ⟨b, hb, fun h => hdisj b h hbT⟩
    exact (hunion z hzc).elim hzS hzT
  -- `b` is a vertex on an edge of the reachable class, hence an end of it.
  simp only [hS, mem_iUnion, mem_setOf_eq, exists_prop] at hbS
  obtain ⟨P, ⟨hP, hPr⟩, hbP⟩ := hbS
  have hbend : b = P.1 ∨ b = P.2 :=
    hdraw.vertex_mem_edgeArc (hlink P hP) hbV (by rwa [edgeArc_segmentDrawing])
  exact (overlayGraph_reaches_end hP hbend).1 hPr

/-! ### Lemma 1.2, and then Lemma 1.1 -/

/-- **Lemma 1.2 (finite polygonal unions).** If a finite union of nondegenerate segments is
connected, any two distinct points of it are joined inside it by a *simple* polygonal arc.

The arc is returned as a vertex list, not merely as a set: the consumers that overlay it with
another polygonal object need its vertices, and an existential over sets would not give them
back. -/
theorem exists_simple_poly_of_cover (hnd : ∀ P ∈ pieces, P.Nondeg)
    (hconn : IsPreconnected (cover pieces)) (hab : a ≠ b)
    (ha : a ∈ cover pieces) (hb : b ∈ cover pieces) :
    ∃ vs : List Plane, ∃ h : vs ≠ [], vs.head h = a ∧ vs.getLast h = b ∧
      poly vs ⊆ cover pieces ∧ IsArcBetween (poly vs) a b := by
  classical
  -- Put the two endpoints on the cut list, so that they become vertices of the overlay. The
  -- two cut conditions ask only that certain points occur in the list, so this is free.
  obtain ⟨pts₀, hEnds₀, hMeets₀⟩ := exists_cut_points pieces
  set pts : List Plane := a :: b :: pts₀ with hpts
  have hEnds : EndsAreCut pieces pts := fun P hP z hz => by
    simp [hpts, hEnds₀ P hP z hz]
  have hMeets : MeetsAreCut pieces pts := by
    intro P hP Q hQ hPQ hne
    obtain ⟨u, v, huv, hu, hv⟩ := hMeets₀ P hP Q hQ hPQ hne
    exact ⟨u, v, huv, by simp [hpts, hu], by simp [hpts, hv]⟩
  have hdraw : Graph.IsDrawing (overlayGraph pieces pts) segmentDrawing :=
    overlayGraph_isDrawing pieces pts hnd hEnds hMeets
  -- A walk from `a` to `b`, thinned to a path.
  have hreach : (overlayGraph pieces pts).Reaches a b :=
    overlayGraph_reaches hnd hconn hEnds hMeets (by simp [hpts]) (by simp [hpts]) ha hb
  obtain ⟨W, hpath⟩ := hreach.exists_isPath
  have hWne : W ≠ [] := by
    rintro rfl
    exact hab hpath.isWalk.eq_of_nil
  -- Its realisation is an arc, and it is the carrier of a vertex list.
  have harc : IsArcBetween (Graph.edgesCover segmentDrawing W) a b :=
    hdraw.path_isArcBetween hpath hWne
  obtain ⟨vs, hvs, hhead, hlast, hpoly⟩ := exists_poly_eq_edgesCover hpath.isWalk hWne
  refine ⟨vs, hvs, hhead, hlast, ?_, ?_⟩
  · rw [hpoly, ← overlayGraph_pointSet pieces pts]
    exact Graph.edgesCover_subset_pointSet fun e he => hpath.edge_mem he
  · rw [hpoly]; exact harc

/-- **Lemma 1.2**, for a set presented as a polygonal chain. -/
theorem exists_simple_poly_of_poly {vs : List Plane} (hconn : IsPreconnected (poly vs))
    (hab : a ≠ b) (ha : a ∈ poly vs) (hb : b ∈ poly vs) :
    ∃ ws : List Plane, ∃ h : ws ≠ [], ws.head h = a ∧ ws.getLast h = b ∧
      poly ws ⊆ poly vs ∧ IsArcBetween (poly ws) a b := by
  have hcov : cover (segsOf vs) = poly vs := cover_segsOf_eq ha hb hab
  have := exists_simple_poly_of_cover (segsOf_nondeg vs) (hcov ▸ hconn) hab
    (hcov ▸ ha) (hcov ▸ hb)
  rwa [hcov] at this

/-- **Lemma 1.2**, for a set given only as polygonal. -/
theorem exists_simple_poly_of_isPolygonal {A : Set Plane} (hA : IsPolygonal A)
    (hconn : IsPreconnected A) (hab : a ≠ b) (ha : a ∈ A) (hb : b ∈ A) :
    ∃ ws : List Plane, ∃ h : ws ≠ [], ws.head h = a ∧ ws.getLast h = b ∧
      poly ws ⊆ A ∧ IsArcBetween (poly ws) a b := by
  obtain ⟨vs, rfl⟩ := hA
  exact exists_simple_poly_of_poly hconn hab ha hb

/-! ### A finite union of polygonal arcs

The blueprint states Lemma 1.2 for a finite union, which `Schoenflies.cover` already is. The
only thing standing between the two readings is that a member of the union may have collapsed
to a single point, contributing no segment at all. A collapsed member is harmless: were its
point missing from the segments, it would be clopen in the union, which a connected set with
more than one point does not tolerate. -/

/-- Peeling the head off a union indexed by a list. -/
theorem biUnion_list_cons {α : Type*} (f : α → Set Plane) (x : α) (l : List α) :
    (⋃ y ∈ x :: l, f y) = f x ∪ ⋃ y ∈ l, f y := by
  ext z
  simp only [mem_iUnion, exists_prop, List.mem_cons, mem_union]
  constructor
  · rintro ⟨y, rfl | hy, hz⟩
    · exact Or.inl hz
    · exact Or.inr ⟨y, hy, hz⟩
  · rintro (hz | ⟨y, hy, hz⟩)
    · exact ⟨x, Or.inl rfl, hz⟩
    · exact ⟨y, Or.inr hy, hz⟩

/-- `Schoenflies.cover_flatMap`, over an arbitrary index list rather than a list of pieces.
Belongs beside it in `Schoenflies/Subdivide.lean`; it is here because that module is on
`main`. -/
theorem cover_flatMap_list {α : Type*} (f : α → List Piece) (l : List α) :
    cover (l.flatMap f) = ⋃ x ∈ l, cover (f x) := by
  induction l with
  | nil => simp
  | cons x l ih => rw [List.flatMap_cons, cover_append, ih, biUnion_list_cons]

/-- A preconnected set with two distinct points absorbs finitely many stray points: it cannot
be a closed set together with finitely many extra points, since each extra point would be
clopen in it. -/
theorem subset_of_finite_diff {U C : Set Plane} (hU : IsPreconnected U) (hC : IsClosed C)
    (hfin : (U \ C).Finite) (ha : a ∈ U) (hb : b ∈ U) (hab : a ≠ b) : U ⊆ C := by
  intro z hz
  by_contra hzC
  -- `D` meets `U` in exactly `U \ {z}`, and it is closed.
  set D : Set Plane := C ∪ ((U \ C) \ {z}) with hD
  have hDclosed : IsClosed D := hC.union ((hfin.subset Set.sdiff_subset).isClosed)
  have hzD : z ∉ D := fun h => h.elim hzC fun h' => h'.2 rfl
  have hmemD : ∀ w ∈ U, w ≠ z → w ∈ D := fun w hw hwz =>
    (em (w ∈ C)).elim Or.inl fun h => Or.inr ⟨⟨hw, h⟩, hwz⟩
  -- `{z}` is clopen in `U`, so `U = {z}` — which two distinct points forbid.
  obtain ⟨w, hwU, hwD, hwz⟩ := hU Dᶜ ({z} : Set Plane)ᶜ hDclosed.isOpen_compl
    isClosed_singleton.isOpen_compl
    (fun w hw => (em (w = z)).elim (fun h => Or.inl (h ▸ hzD)) fun h => Or.inr h)
    ⟨z, hz, hzD⟩
    ((em (a = z)).elim (fun h => ⟨b, hb, fun hbz => hab (h.trans (mem_singleton_iff.1 hbz).symm)⟩)
      fun h => ⟨a, ha, h⟩)
  exact hwD (hmemD w hwU hwz)

/-- **Lemma 1.2 (finite polygonal unions).** A connected finite union of polygonal chains joins
any two of its distinct points by a simple polygonal arc inside it. -/
theorem exists_simple_poly_of_biUnion {L : List (List Plane)}
    (hconn : IsPreconnected (⋃ vs ∈ L, poly vs)) (hab : a ≠ b)
    (ha : a ∈ ⋃ vs ∈ L, poly vs) (hb : b ∈ ⋃ vs ∈ L, poly vs) :
    ∃ ws : List Plane, ∃ h : ws ≠ [], ws.head h = a ∧ ws.getLast h = b ∧
      poly ws ⊆ (⋃ vs ∈ L, poly vs) ∧ IsArcBetween (poly ws) a b := by
  classical
  have hnd : ∀ P ∈ L.flatMap segsOf, P.Nondeg := by
    intro P hP
    obtain ⟨vs, -, hPvs⟩ := List.mem_flatMap.1 hP
    exact segsOf_nondeg vs P hPvs
  have hcovsub : ∀ vs : List Plane, cover (segsOf vs) ⊆ poly vs := by
    intro vs
    rcases cover_segsOf vs with h | ⟨h, -⟩
    · exact h.subset
    · rw [h, cover_nil]; exact empty_subset _
  have hflat : cover (L.flatMap segsOf) = ⋃ vs ∈ L, cover (segsOf vs) :=
    cover_flatMap_list segsOf L
  have hsub : cover (L.flatMap segsOf) ⊆ ⋃ vs ∈ L, poly vs := by
    rw [hflat]
    exact iUnion₂_mono fun vs _ => hcovsub vs
  -- What the segments miss is finitely many collapsed members.
  have hdiff : ((⋃ vs ∈ L, poly vs) \ cover (L.flatMap segsOf)).Finite := by
    have hsmall : ∀ vs : List Plane, (poly vs \ cover (segsOf vs)).Subsingleton := by
      intro vs
      rcases cover_segsOf vs with h | ⟨-, h⟩
      · rw [h]; simp
      · exact h.anti Set.sdiff_subset
    refine (Set.Finite.biUnion L.finite_toSet
      fun vs _ => (hsmall vs).finite).subset ?_
    rintro z ⟨hzU, hzC⟩
    simp only [mem_iUnion, exists_prop] at hzU
    obtain ⟨vs, hvs, hz⟩ := hzU
    refine mem_biUnion hvs ⟨hz, fun hmem => hzC ?_⟩
    rw [hflat]
    exact mem_biUnion hvs hmem
  have hclosed : IsClosed (cover (L.flatMap segsOf)) :=
    Set.Finite.isClosed_biUnion (L.flatMap segsOf).finite_toSet fun P _ =>
      (isCompact_segment P.1 P.2).isClosed
  have heq : cover (L.flatMap segsOf) = ⋃ vs ∈ L, poly vs :=
    subset_antisymm hsub (subset_of_finite_diff hconn hclosed hdiff ha hb hab)
  have := exists_simple_poly_of_cover hnd (heq ▸ hconn) hab (heq ▸ ha) (heq ▸ hb)
  rwa [heq] at this

/-- A list of polygonal sets is a list of polygonal chains. -/
theorem exists_lists_of_isPolygonal : ∀ {L : List (Set Plane)}, (∀ A ∈ L, IsPolygonal A) →
    ∃ M : List (List Plane), (⋃ vs ∈ M, poly vs) = ⋃ A ∈ L, A
  | [], _ => ⟨[], by simp⟩
  | A :: L, h => by
    obtain ⟨vs, rfl⟩ := h A (List.mem_cons_self ..)
    obtain ⟨M, hM⟩ := exists_lists_of_isPolygonal fun B hB => h B (List.mem_cons_of_mem _ hB)
    refine ⟨vs :: M, ?_⟩
    rw [biUnion_list_cons (fun ws : List Plane => poly ws),
      biUnion_list_cons (fun B : Set Plane => B), hM]

/-- **Lemma 1.2 (finite polygonal unions)**, at the level of sets: if a connected set is the
union of finitely many polygonal sets, any two of its distinct points are joined in it by a
simple polygonal arc. -/
theorem exists_simple_poly_of_union {L : List (Set Plane)} (hL : ∀ A ∈ L, IsPolygonal A)
    (hconn : IsPreconnected (⋃ A ∈ L, A)) (hab : a ≠ b)
    (ha : a ∈ ⋃ A ∈ L, A) (hb : b ∈ ⋃ A ∈ L, A) :
    ∃ ws : List Plane, ∃ h : ws ≠ [], ws.head h = a ∧ ws.getLast h = b ∧
      poly ws ⊆ (⋃ A ∈ L, A) ∧ IsArcBetween (poly ws) a b := by
  obtain ⟨M, hM⟩ := exists_lists_of_isPolygonal hL
  have := exists_simple_poly_of_biUnion (L := M) (hM ▸ hconn) hab (hM ▸ ha) (hM ▸ hb)
  rwa [hM] at this

/-- **Lemma 1.1 (polygonal connectedness), in full.** Any two distinct points of a region are
joined in it by a *simple* polygonal arc.

`Schoenflies.exists_poly_of_isPreconnected` supplies a polygonal path; Lemma 1.2 extracts a
simple arc from its carrier. -/
theorem exists_simple_poly_of_isPreconnected (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hx : x ∈ Ω) (hy : y ∈ Ω) (hxy : x ≠ y) :
    ∃ vs : List Plane, ∃ h : vs ≠ [], vs.head h = x ∧ vs.getLast h = y ∧
      poly vs ⊆ Ω ∧ IsArcBetween (poly vs) x y := by
  obtain ⟨us, hus, hsub, hhead, hlast⟩ := exists_poly_of_isPreconnected hΩ hconn hx hy
  have hxu : x ∈ poly us := hhead ▸ head_mem_poly hus
  have hyu : y ∈ poly us := hlast ▸ getLast_mem_poly hus
  obtain ⟨vs, hvs, h1, h2, h3, h4⟩ :=
    exists_simple_poly_of_poly (isConnected_poly hus).2 hxy hxu hyu
  exact ⟨vs, hvs, h1, h2, h3.trans hsub, h4⟩

/-- **Lemma 1.1**, in set form: a simple polygonal arc inside the region between any two of
its points. -/
theorem exists_simple_arc_of_isPreconnected (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hx : x ∈ Ω) (hy : y ∈ Ω) (hxy : x ≠ y) :
    ∃ A ⊆ Ω, IsPolygonal A ∧ IsArcBetween A x y := by
  obtain ⟨vs, -, -, -, hsub, harc⟩ := exists_simple_poly_of_isPreconnected hΩ hconn hx hy hxy
  exact ⟨poly vs, hsub, ⟨vs, rfl⟩, harc⟩

end Schoenflies

end BundlePart402
