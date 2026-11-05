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

public import verified.parts.part033
import all verified.parts.part033

@[expose] public section

set_option debug.skipKernelTC false
set_option linter.all false
set_option Elab.async false
set_option internal.cmdlineSnapshots true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

section BundlePart411
/- Source: dev/planar_search/schoenflies_port/Schoenflies/PolygonalJordan.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/





/-!
# The polygonal Jordan curve theorem

Theorem 2.3: the complement of a simple closed polygon has exactly two regions, one bounded and
one unbounded, and each has the polygon as its frontier. Moreover the crossing parity of §2 is
`1` on the bounded region and `0` on the unbounded one.

## The three inputs, and where each is spent

* **Lemma 1.8, the collar** (`Schoenflies.StripData`, `StripData.local_two_sided`,
  `StripData.carrier_subset_closure_sideL`). It supplies the two *tracks* `N_L`, `N_R`: connected,
  disjoint, off the curve, together filling `N ∖ C`, and each with the whole curve in its closure.
* **Lemma 1.3, the nearest-point segment** (`Plane.notMem_of_mem_segment_of_isMinOn`). It gets an
  arbitrary point of the complement onto a track: walk from it to a nearest point of the curve;
  the walk misses the curve, and its final stretch is inside the collar.
* **Lemma 2.2, crossing parity** (`ClosedPolygon.parity_eq_of_mem_connectedComponentIn_carrier`,
  `ClosedPolygon.parity_flip_carrier`). It keeps the two tracks apart: they cannot be joined
  inside the complement, because a point just before and a point just after an edge differ in
  parity and parity is constant on a connected subset of the complement.

## Blueprint

* `Schoenflies.ClosedPolygon.exists_opposite_parity_sides`,
  `…parity_ne_of_mem_sides`, `…connectedComponentIn_ne_of_mem_sides` — the two tracks of the
  collar carry different parities, hence lie in different components. The "at least two" half.
* `Schoenflies.ClosedPolygon.exists_mem_sides_connectedComponentIn`,
  `…connectedComponentIn_eq_of_notMem` — every point of the complement lies in the component of a
  point of a track. The "at most two" half.
* `Schoenflies.ClosedPolygon.isSeparating_carrier` — **Theorem 2.3**, in the form Definition 2.4
  asks for: `IsSeparating P.carrier`. With it come `inside P.carrier` and `outside P.carrier` as
  the blueprint's `Int(C)` and `Ext(C)`, and the whole `IsSeparating` API of
  `Schoenflies/CrosscutCells.lean`.
* `Schoenflies.ClosedPolygon.connectedComponentIn_eq_inside_or_outside` — "exactly two regions",
  explicitly: the component of any point off the polygon is one of the two named regions.
* `Schoenflies.ClosedPolygon.parity_eq_one_of_mem_inside`,
  `…parity_eq_zero_of_mem_outside` — the last sentence of Theorem 2.3, `π_C = 1` inside and
  `π_C = 0` outside, for **every** admissible ray direction, not just for one chosen at the start.
* `Schoenflies.ClosedPolygon.polygonal_jordan` — the same theorem with `IsSeparating` unfolded,
  for a reader who wants the statement without the definition.
* `Schoenflies.isSeparating_unitTriangle` — non-vacuity: the whole chain applies to the one
  polygon the development constructs.

## Two facts restated

`isBounded_closedSquare` and `not_isBounded_beyondSquare` below are stated `private`. They are
*not* new: they exist as `Graph.isBounded_closedSquare` and `Graph.not_isBounded_beyondSquare` in
`Schoenflies/Graph/OuterFace.lean`. Neither has any graph content — they are plane facts about
`Schoenflies.Plane.closedSquare` whose home is `Schoenflies/Bounded.lean` — and importing the
whole plane-graph layer into the polygonal Jordan curve theorem, which every later graph
argument depends on, would invert the layering. They are `private` so that the duplicate names
cannot collide when the integrator hoists the originals.
-/

open Bornology Metric Set

namespace Schoenflies

open Plane

variable {m : ℕ}

/-! ### Two plane facts about squares

See the module docstring: these belong in `Schoenflies/Bounded.lean` and are restated here only
to keep the graph layer out of the import graph of Theorem 2.3. -/

/-- A closed axis-parallel square is bounded. -/
private theorem isBounded_closedSquare (r : ℝ) : IsBounded (Plane.closedSquare 0 r) := by
  refine (Metric.isBounded_closedBall (x := (0 : Plane)) (r := Real.sqrt 2 * r)).subset ?_
  intro x hx
  have hsup : Plane.supNorm x ≤ r := by simpa [Plane.closedSquare] using hx
  have : ‖x‖ ≤ Real.sqrt 2 * r :=
    le_trans (Plane.norm_le_sqrt_two_mul_supNorm x)
      (mul_le_mul_of_nonneg_left hsup (Real.sqrt_nonneg 2))
  simpa [Metric.mem_closedBall, dist_eq_norm] using this

/-- The outside of a square is unbounded: it contains points of every size. -/
private theorem not_isBounded_beyondSquare (r : ℝ) : ¬ IsBounded (Plane.beyondSquare r) := by
  intro hb
  obtain ⟨s, -, hs⟩ := Plane.exists_closedSquare_of_isBounded hb
  set t : ℝ := max (max r s) 0 + 1 with ht
  have ht0 : 0 ≤ t := by have := le_max_right (max r s) 0; simp only [ht]; linarith
  have htr : r < t := by
    have h1 := le_max_left r s
    have h2 := le_max_left (max r s) 0
    simp only [ht]; linarith
  have hts : s < t := by
    have h1 := le_max_right r s
    have h2 := le_max_left (max r s) 0
    simp only [ht]; linarith
  have hmem : Plane.mk t 0 ∈ Plane.beyondSquare r :=
    Or.inl (show r < |t| by rw [abs_of_nonneg ht0]; exact htr)
  have hin : Plane.supDist (Plane.mk t 0) 0 ≤ s := hs hmem
  rw [Plane.supDist_zero] at hin
  have h1 : |t| ≤ Plane.supNorm (Plane.mk t 0) := by
    simp only [Plane.supNorm]; exact le_max_left _ _
  rw [abs_of_nonneg ht0] at h1
  linarith

/-- **A point far out along the ray direction, and outside a prescribed square.** One coordinate
of a unit vector always exceeds `1/2` in absolute value, so a long enough multiple of the ray
direction leaves every square — which is how "far along the ray" and "in the unbounded region" are
arranged at one and the same point. -/
private theorem exists_beyond_of_fwd_lt {u : Plane} (hu : Plane.IsDirection u) (r M : ℝ) :
    ∃ q : Plane, q ∈ Plane.beyondSquare r ∧ M < fwd u q := by
  have hnorm : u 0 ^ 2 + u 1 ^ 2 = 1 := norm_sq_one hu
  have hcoord : 1 / 2 < |u 0| ∨ 1 / 2 < |u 1| := by
    by_contra hc
    push Not at hc
    obtain ⟨hc0, hc1⟩ := hc
    nlinarith [sq_abs (u 0), sq_abs (u 1), abs_nonneg (u 0), abs_nonneg (u 1)]
  set s : ℝ := max (max (2 * r) M) 0 + 1 with hs
  have hs0 : 0 < s := by have := le_max_right (max (2 * r) M) 0; simp only [hs]; linarith
  have hsr : 2 * r < s := by
    have h1 := le_max_left (2 * r) M
    have h2 := le_max_left (max (2 * r) M) 0
    simp only [hs]; linarith
  have hsM : M < s := by
    have h1 := le_max_right (2 * r) M
    have h2 := le_max_left (max (2 * r) M) 0
    simp only [hs]; linarith
  have hfwd : fwd u (s • u) = s := by
    rw [fwd_eq]
    simp only [Plane.smul_apply]
    linear_combination s * hnorm
  have habs : ∀ i : Fin 2, |(s • u) i| = s * |u i| := fun i => by
    rw [Plane.smul_apply, abs_mul, abs_of_pos hs0]
  refine ⟨s • u, ?_, by rw [hfwd]; exact hsM⟩
  rcases hcoord with h | h
  · exact Or.inl (by rw [habs 0]; nlinarith [mul_lt_mul_of_pos_left h hs0])
  · exact Or.inr (by rw [habs 1]; nlinarith [mul_lt_mul_of_pos_left h hs0])

/-! ### Small arithmetic and topology helpers -/

/-- In `ZMod 2` nothing is its own successor; this is what "the parities differ" comes down to. -/
private theorem zmod_two_ne_add_one (x : ZMod 2) : x ≠ x + 1 := by revert x; decide

/-- The only two values, named. -/
private theorem zmod_two_eq_one_of_ne_zero {x : ZMod 2} (h : x ≠ 0) : x = 1 := by
  revert h; revert x; decide

/-- Two points joined by a preconnected subset of `F` have the same component of `F`. -/
private theorem comp_eq_of_isPreconnected {F S : Set Plane} (hS : IsPreconnected S) (hSF : S ⊆ F)
    {x y : Plane} (hx : x ∈ S) (hy : y ∈ S) :
    connectedComponentIn F x = connectedComponentIn F y :=
  connectedComponentIn_eq (hS.subset_connectedComponentIn hx hSF hy)

/-- Distinct components are disjoint. -/
private theorem comp_disjoint {F : Set Plane} {x y : Plane}
    (h : connectedComponentIn F x ≠ connectedComponentIn F y) :
    Disjoint (connectedComponentIn F x) (connectedComponentIn F y) := by
  rw [Set.disjoint_left]
  intro z hzx hzy
  exact h ((connectedComponentIn_eq hzx).trans (connectedComponentIn_eq hzy).symm)

namespace ClosedPolygon

variable {P : ClosedPolygon m}

theorem isClosed_carrier (P : ClosedPolygon m) : IsClosed P.carrier :=
  P.isCompact_carrier.isClosed

theorem isOpen_compl_carrier (P : ClosedPolygon m) : IsOpen P.carrierᶜ :=
  P.isClosed_carrier.isOpen_compl

theorem carrier_nonempty (P : ClosedPolygon m) : P.carrier.Nonempty :=
  ⟨P.vertex 0, vertex_mem_carrier⟩

theorem sideL_subset_compl (D : StripData P) : D.sideL ⊆ P.carrierᶜ :=
  fun _ hz => Set.disjoint_left.1 D.sideL_disjoint_carrier hz

theorem sideR_subset_compl (D : StripData P) : D.sideR ⊆ P.carrierᶜ :=
  fun _ hz => Set.disjoint_left.1 D.sideR_disjoint_carrier hz

/-- **No edge is parallel to an admissible ray direction.** "No edge is horizontal" says exactly
that the two ends of an edge are at different heights, which is that the edge's tangent and the
ray direction span the plane. -/
theorem det_tang_ne_zero {u : Plane} (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2)
    (i : ZMod (m + 3)) : det (P.tang i) u ≠ 0 := by
  have hne : hgt u (P.vertex i) ≠ hgt u (P.vertex (i + 1)) := hL _ (P.mem_pieces i)
  have hsub : det u (P.vertex (i + 1) - P.vertex i) ≠ 0 := by
    rw [show det u (P.vertex (i + 1) - P.vertex i) = hgt u (P.vertex (i + 1) - P.vertex i) from rfl,
      hgt_sub, sub_ne_zero]
    exact Ne.symm hne
  rw [← len_smul_tang, det_smul_right] at hsub
  intro hz
  exact hsub (by rw [det_comm, hz, neg_zero, mul_zero])

/-! ### At least two regions: the two tracks are separated by one crossing

The blueprint: "Choose a sufficiently small disk `B` around an interior point of an edge, and
reference points `z_L ∈ B ∩ N_L`, `z_R ∈ B ∩ N_R` in its two components. The two reference points
have opposite parity."

The disk is the one of `StripData.local_two_sided`; the two reference points are the two points
just before and just after the midpoint of the edge *in the ray direction*, which is what makes
`parity_flip_carrier` applicable to them. That they land in the two different tracks is read off
the sign of their transverse coordinate `det (tang i) (· - vertex i)`, and the two signs are
opposite and nonzero because `det (tang i) u ≠ 0` — the edge is not parallel to the ray. -/

/-- **The two tracks of the collar carry different parities.** The witnesses are a point just
before and a point just after the midpoint of the edge `i` in the ray direction: they lie in the
two different tracks, and the crossing count changes by one between them. -/
theorem exists_opposite_parity_sides (P : ClosedPolygon m) (D : StripData P)
    (i : ZMod (m + 3)) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) :
    ∃ zL ∈ D.sideL, ∃ zR ∈ D.sideR, parity u P.pieces zL ≠ parity u P.pieces zR := by
  have h4 := D.four_lam_lt_len i
  have hlam := D.lam_pos
  have hlen : 0 < P.len i := len_pos
  have hlow : 2 * D.lam ≤ P.len i / 2 := by linarith
  have hhigh : P.len i / 2 ≤ P.len i - 2 * D.lam := by linarith
  have hηpos : 0 < min D.lam D.rho := lt_min hlam D.rho_pos
  obtain ⟨-, hsides, -, -⟩ := D.local_two_sided (i := i) hlow hhigh hηpos le_rfl
  -- the midpoint of the edge is an interior point of it
  have hmid : P.vertex i + ((P.len i / 2) / P.len i) • (P.vertex (i + 1) - P.vertex i)
      = P.pt i (P.len i / 2) := by
    rw [← len_smul_tang, smul_smul, div_mul_cancel₀ _ hlen.ne', pt_eq]
  have hp : P.pt i (P.len i / 2) ∈ openSegment ℝ (P.vertex i) (P.vertex (i + 1)) := by
    rw [openSegment_eq_image' ℝ]
    exact ⟨(P.len i / 2) / P.len i,
      ⟨div_pos (by linarith) hlen, by rw [div_lt_one hlen]; linarith⟩, hmid⟩
  obtain ⟨δ, hδ, hflip⟩ := P.parity_flip_carrier hu hL i hp
  have ht0 : 0 < min (δ / 2) (min D.lam D.rho / 2) := lt_min (by linarith) (by linarith)
  have htδ : min (δ / 2) (min D.lam D.rho / 2) < δ :=
    lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have htη : min (δ / 2) (min D.lam D.rho / 2) < min D.lam D.rho :=
    lt_of_le_of_lt (min_le_right _ _) (by linarith)
  set t : ℝ := min (δ / 2) (min D.lam D.rho / 2)
  obtain ⟨hbef, haft, hpar⟩ := hflip t ht0 htδ
  -- both test points lie in the disk of `local_two_sided`
  have hball : ∀ r : ℝ, |r| < min D.lam D.rho →
      P.pt i (P.len i / 2) + r • u ∈ ball (P.pt i (P.len i / 2)) (min D.lam D.rho) := by
    intro r hr
    rw [mem_ball, dist_eq_norm,
      show P.pt i (P.len i / 2) + r • u - P.pt i (P.len i / 2) = r • u by abel,
      norm_smul, Real.norm_eq_abs, hu.norm, mul_one]
    exact hr
  have hbaft := hball t (by rw [abs_of_pos ht0]; exact htη)
  have hbbef : P.pt i (P.len i / 2) - t • u ∈ ball (P.pt i (P.len i / 2)) (min D.lam D.rho) := by
    have h := hball (-t) (by rw [abs_of_neg (by linarith), neg_neg]; exact htη)
    rwa [neg_smul, ← sub_eq_add_neg] at h
  -- the transverse coordinate of a point offset from the edge in the ray direction
  have hkey : ∀ r : ℝ, coordAcross (P.vertex i) (P.tang i) (P.pt i (P.len i / 2) + r • u)
      = r * det (P.tang i) u := by
    intro r
    rw [coordAcross, show P.pt i (P.len i / 2) + r • u - P.vertex i
        = (P.len i / 2) • P.tang i + r • u by rw [pt_eq]; module,
      det_add_right, det_smul_right, det_self, mul_zero, zero_add, det_smul_right]
  have hcaaft := hkey t
  have hcabef : coordAcross (P.vertex i) (P.tang i) (P.pt i (P.len i / 2) - t • u)
      = -(t * det (P.tang i) u) := by
    have h := hkey (-t)
    rw [neg_smul, ← sub_eq_add_neg] at h
    rw [h]; ring
  have hsaft := hsides _ hbaft haft
  have hsbef := hsides _ hbbef hbef
  rcases lt_or_gt_of_ne (det_tang_ne_zero hL i) with hneg | hpos
  · -- the ray points to the right of the edge: the earlier test point is on the left
    have hlt : t * det (P.tang i) u < 0 := mul_neg_of_pos_of_neg ht0 hneg
    refine ⟨P.pt i (P.len i / 2) - t • u, ?_, P.pt i (P.len i / 2) + t • u, ?_, ?_⟩
    · rcases hsbef with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · rw [hcabef] at h; linarith
    · rcases hsaft with ⟨h, -⟩ | ⟨-, h⟩
      · rw [hcaaft] at h; linarith
      · exact h
    · rw [hpar]; exact Ne.symm (zmod_two_ne_add_one _)
  · have hgt0 : 0 < t * det (P.tang i) u := mul_pos ht0 hpos
    refine ⟨P.pt i (P.len i / 2) + t • u, ?_, P.pt i (P.len i / 2) - t • u, ?_, ?_⟩
    · rcases hsaft with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · rw [hcaaft] at h; linarith
    · rcases hsbef with ⟨h, -⟩ | ⟨-, h⟩
      · rw [hcabef] at h; linarith
      · exact h
    · rw [hpar]; exact zmod_two_ne_add_one _

/-- The crossing parity is constant on the left track: it is connected and misses the polygon. -/
theorem parity_eq_of_mem_sideL (P : ClosedPolygon m) (D : StripData P) {u : Plane}
    (hu : Plane.IsDirection u) (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) {x y : Plane}
    (hx : x ∈ D.sideL) (hy : y ∈ D.sideL) : parity u P.pieces x = parity u P.pieces y :=
  parity_eq_of_isPreconnected hu hL P.isClosedChain_pieces D.isConnected_sideL.isPreconnected
    (fun z hz => by rw [P.cover_pieces]; exact sideL_subset_compl D hz) hx hy

/-- The crossing parity is constant on the right track. -/
theorem parity_eq_of_mem_sideR (P : ClosedPolygon m) (D : StripData P) {u : Plane}
    (hu : Plane.IsDirection u) (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) {x y : Plane}
    (hx : x ∈ D.sideR) (hy : y ∈ D.sideR) : parity u P.pieces x = parity u P.pieces y :=
  parity_eq_of_isPreconnected hu hL P.isClosedChain_pieces D.isConnected_sideR.isPreconnected
    (fun z hz => by rw [P.cover_pieces]; exact sideR_subset_compl D hz) hx hy

/-- **The two tracks of the collar have opposite parity**, whichever points of them are chosen.
This is the "at least two regions" half of Theorem 2.3: no connected subset of the complement
meets both tracks, since parity is constant on such a subset. -/
theorem parity_ne_of_mem_sides (P : ClosedPolygon m) (D : StripData P) {u : Plane}
    (hu : Plane.IsDirection u) (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) {x y : Plane}
    (hx : x ∈ D.sideL) (hy : y ∈ D.sideR) : parity u P.pieces x ≠ parity u P.pieces y := by
  obtain ⟨zL, hzL, zR, hzR, hne⟩ := P.exists_opposite_parity_sides D 0 hu hL
  rw [P.parity_eq_of_mem_sideL D hu hL hx hzL, P.parity_eq_of_mem_sideR D hu hL hy hzR]
  exact hne

/-- The two tracks lie in different components of the complement. -/
theorem connectedComponentIn_ne_of_mem_sides (P : ClosedPolygon m) (D : StripData P) {x y : Plane}
    (hx : x ∈ D.sideL) (hy : y ∈ D.sideR) :
    connectedComponentIn P.carrierᶜ x ≠ connectedComponentIn P.carrierᶜ y := by
  obtain ⟨u, hu, hL⟩ := P.exists_direction_pieces
  intro heq
  refine P.parity_ne_of_mem_sides D hu hL hx hy ?_
  have hxc : x ∈ connectedComponentIn P.carrierᶜ y := by
    rw [← heq]; exact mem_connectedComponentIn (sideL_subset_compl D hx)
  exact P.parity_eq_of_mem_connectedComponentIn_carrier hu hL (sideR_subset_compl D hy) hxc

/-! ### At most two regions: walk to the nearest point of the polygon

The blueprint: "Let `x ∉ C`, and choose a nearest point `a ∈ C`. By Lemma 1.3, `[x, a)` avoids
`C`. Its final portion lies in `N_L` or `N_R`, and that track is connected. Hence `x` lies in the
component of either `z_L` or `z_R`." -/

/-- **At most two regions.** Every point of the complement lies in the component of a point of one
of the two tracks: walk towards a nearest point of the polygon — Lemma 1.3 says the walk misses
the polygon — and stop just short of it, inside the collar. -/
theorem exists_mem_sides_connectedComponentIn (P : ClosedPolygon m) (D : StripData P) {x : Plane}
    (hx : x ∉ P.carrier) :
    ∃ y ∈ D.sideL ∪ D.sideR,
      connectedComponentIn P.carrierᶜ x = connectedComponentIn P.carrierᶜ y := by
  -- a nearest point of the polygon, and the segment towards it
  obtain ⟨a, haC, hmin⟩ := P.isCompact_carrier.exists_isMinOn P.carrier_nonempty
    (continuous_const.dist continuous_id).continuousOn
  have hmin' : ∀ b ∈ P.carrier, dist x a ≤ dist x b := isMinOn_iff.1 hmin
  have hax : a ≠ x := fun h => hx (h ▸ haC)
  have hvne : a - x ≠ 0 := sub_ne_zero.2 hax
  have hvpos : 0 < ‖a - x‖ := norm_pos_iff.2 hvne
  have hcont : Continuous (fun θ : ℝ => x + θ • (a - x)) :=
    continuous_const.add (continuous_id.smul continuous_const)
  -- Lemma 1.3: the half-open segment misses the polygon
  have hoff : ∀ θ : ℝ, θ ∈ Ico (0 : ℝ) 1 → x + θ • (a - x) ∉ P.carrier := by
    intro θ hθ
    refine Plane.notMem_of_mem_segment_of_isMinOn haC hx hmin' ?_ ?_
    · rw [segment_eq_image' ℝ x a]; exact ⟨θ, ⟨hθ.1, hθ.2.le⟩, rfl⟩
    · intro h
      have h0 : (θ - 1) • (a - x) = 0 := by linear_combination (norm := module) h
      rcases smul_eq_zero.1 h0 with h1 | h1
      · have := hθ.2; linarith
      · exact hvne h1
  have hSΩ : (fun θ : ℝ => x + θ • (a - x)) '' Ico 0 1 ⊆ P.carrierᶜ := by
    rintro z ⟨θ, hθ, rfl⟩
    exact hoff θ hθ
  have hSpre : IsPreconnected ((fun θ : ℝ => x + θ • (a - x)) '' Ico 0 1) :=
    isPreconnected_Ico.image _ hcont.continuousOn
  -- the collar is a neighbourhood of the nearest point, so the final stretch lies in it
  obtain ⟨ε, hε, hεball⟩ := Metric.isOpen_iff.1 D.isOpen_nbhd a (D.carrier_subset_nbhd haC)
  have hmpos : 0 < min (1 / 2 : ℝ) (ε / (2 * ‖a - x‖)) := lt_min (by norm_num) (by positivity)
  have hmhalf : min (1 / 2 : ℝ) (ε / (2 * ‖a - x‖)) ≤ 1 / 2 := min_le_left _ _
  have hθmem : (1 - min (1 / 2 : ℝ) (ε / (2 * ‖a - x‖))) ∈ Ico (0 : ℝ) 1 :=
    ⟨by linarith, by linarith⟩
  have hprod : ε / (2 * ‖a - x‖) * ‖a - x‖ = ε / 2 := by
    field_simp
  have hdist : dist (x + (1 - min (1 / 2 : ℝ) (ε / (2 * ‖a - x‖))) • (a - x)) a < ε := by
    rw [dist_eq_norm, show x + (1 - min (1 / 2 : ℝ) (ε / (2 * ‖a - x‖))) • (a - x) - a
        = (-(min (1 / 2 : ℝ) (ε / (2 * ‖a - x‖)))) • (a - x) by module,
      norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hmpos]
    calc min (1 / 2 : ℝ) (ε / (2 * ‖a - x‖)) * ‖a - x‖
        ≤ ε / (2 * ‖a - x‖) * ‖a - x‖ := mul_le_mul_of_nonneg_right (min_le_right _ _) hvpos.le
      _ = ε / 2 := hprod
      _ < ε := by linarith
  set y : Plane := x + (1 - min (1 / 2 : ℝ) (ε / (2 * ‖a - x‖))) • (a - x) with hy
  have hyLR : y ∈ D.sideL ∪ D.sideR := by
    rw [← D.nbhd_diff_carrier]
    exact ⟨hεball (mem_ball.2 hdist), hoff _ hθmem⟩
  exact ⟨y, hyLR, comp_eq_of_isPreconnected hSpre hSΩ ⟨0, ⟨le_rfl, one_pos⟩, by simp⟩
    ⟨_, hθmem, hy.symm⟩⟩

/-- Every point of the complement lies in the component of one of two fixed reference points,
one on each track. This is `exists_mem_sides_connectedComponentIn` with the track collapsed to a
point, which is possible because each track is connected. -/
theorem connectedComponentIn_eq_of_notMem (P : ClosedPolygon m) (D : StripData P)
    {zL zR : Plane} (hzL : zL ∈ D.sideL) (hzR : zR ∈ D.sideR) {x : Plane} (hx : x ∉ P.carrier) :
    connectedComponentIn P.carrierᶜ x = connectedComponentIn P.carrierᶜ zL ∨
      connectedComponentIn P.carrierᶜ x = connectedComponentIn P.carrierᶜ zR := by
  obtain ⟨y, hy, hyx⟩ := P.exists_mem_sides_connectedComponentIn D hx
  rcases hy with hy | hy
  · exact Or.inl (hyx.trans (comp_eq_of_isPreconnected D.isConnected_sideL.isPreconnected
      (sideL_subset_compl D) hy hzL))
  · exact Or.inr (hyx.trans (comp_eq_of_isPreconnected D.isConnected_sideR.isPreconnected
      (sideR_subset_compl D) hy hzR))

end ClosedPolygon

/-! ### Packaging: from "exactly two components" to `IsSeparating`

`Schoenflies/CrosscutCells.lean` defines `inside C` and `outside C` as the union of the bounded
and of the unbounded components of `Cᶜ`, *without* any separation hypothesis, and Definition 2.4
is the assertion that each of the two is a single region with boundary `C`. So the last step of
Theorem 2.3 is to identify the two components found above with `inside C` and `outside C`, and
that identification needs no case analysis on which of them is which: the one that swallows the
outside of a containing square is the unbounded one by definition, and the other is caught inside
the square. -/

/-- With exactly two components and the outside of a square inside the second, the first is the
bounded part of the complement and the second the unbounded part. -/
private theorem inside_outside_of_two_components {C : Set Plane} {r : ℝ} {z₁ z₂ : Plane}
    (hne : connectedComponentIn Cᶜ z₁ ≠ connectedComponentIn Cᶜ z₂)
    (hall : ∀ x ∉ C, connectedComponentIn Cᶜ x = connectedComponentIn Cᶜ z₁ ∨
      connectedComponentIn Cᶜ x = connectedComponentIn Cᶜ z₂)
    (hbey : Plane.beyondSquare r ⊆ connectedComponentIn Cᶜ z₂) :
    inside C = connectedComponentIn Cᶜ z₁ ∧ outside C = connectedComponentIn Cᶜ z₂ := by
  have hdisj := comp_disjoint hne
  -- the first component misses the outside of the square, hence sits inside it
  have h1sq : connectedComponentIn Cᶜ z₁ ⊆ Plane.closedSquare 0 r := by
    intro w hw
    by_contra hwq
    exact Set.disjoint_left.1 hdisj hw (hbey (by rw [Plane.beyondSquare_eq_compl]; exact hwq))
  have h1bdd : IsBounded (connectedComponentIn Cᶜ z₁) := (isBounded_closedSquare r).subset h1sq
  have h2unb : ¬ IsBounded (connectedComponentIn Cᶜ z₂) := fun hb =>
    not_isBounded_beyondSquare r (hb.subset hbey)
  constructor
  · ext w
    refine ⟨fun hw => ?_, fun hw => ?_⟩
    · rcases hall w hw.1 with h | h
      · rw [← h]; exact mem_connectedComponentIn hw.1
      · exact absurd (h ▸ hw.2) h2unb
    · refine ⟨connectedComponentIn_subset _ _ hw, ?_⟩
      rw [← connectedComponentIn_eq hw]
      exact h1bdd
  · ext w
    refine ⟨fun hw => ?_, fun hw => ?_⟩
    · rcases hall w hw.1 with h | h
      · exact absurd (h ▸ h1bdd) hw.2
      · rw [← h]; exact mem_connectedComponentIn hw.1
    · refine ⟨connectedComponentIn_subset _ _ hw, ?_⟩
      rw [← connectedComponentIn_eq hw]
      exact h2unb

/-- A component of the complement of a closed set has that set as its frontier as soon as the set
is in its closure: one inclusion is Appendix C item 5, the other is that the component misses the
set altogether. -/
private theorem frontier_connectedComponentIn_eq {C : Set Plane} (hC : IsClosed C) (z : Plane)
    (hcl : C ⊆ closure (connectedComponentIn Cᶜ z)) :
    frontier (connectedComponentIn Cᶜ z) = C := by
  refine Set.Subset.antisymm (Plane.frontier_connectedComponentIn_compl_subset hC z) fun w hw => ?_
  rw [(Plane.isOpen_connectedComponentIn hC.isOpen_compl).frontier_eq]
  exact ⟨hcl hw, fun hmem => connectedComponentIn_subset _ _ hmem hw⟩

/-- The packaging step: two distinct components exhausting the complement, each with the curve in
its closure, and the outside of a containing square inside the second, make the curve
separating. -/
private theorem isSeparating_of_two_components {C : Set Plane} (hJ : IsJordanCurve C)
    (hC : IsClosed C) {r : ℝ} {z₁ z₂ : Plane} (h₁ : z₁ ∉ C) (h₂ : z₂ ∉ C)
    (hne : connectedComponentIn Cᶜ z₁ ≠ connectedComponentIn Cᶜ z₂)
    (hall : ∀ x ∉ C, connectedComponentIn Cᶜ x = connectedComponentIn Cᶜ z₁ ∨
      connectedComponentIn Cᶜ x = connectedComponentIn Cᶜ z₂)
    (hcl₁ : C ⊆ closure (connectedComponentIn Cᶜ z₁))
    (hcl₂ : C ⊆ closure (connectedComponentIn Cᶜ z₂))
    (hbey : Plane.beyondSquare r ⊆ connectedComponentIn Cᶜ z₂) :
    IsSeparating C := by
  obtain ⟨hin, hout⟩ := inside_outside_of_two_components hne hall hbey
  refine ⟨hJ, ?_, ?_, ?_, ?_⟩
  · rw [hin]; exact ⟨⟨z₁, mem_connectedComponentIn h₁⟩, isPreconnected_connectedComponentIn⟩
  · rw [hout]; exact ⟨⟨z₂, mem_connectedComponentIn h₂⟩, isPreconnected_connectedComponentIn⟩
  · rw [hin]; exact frontier_connectedComponentIn_eq hC z₁ hcl₁
  · rw [hout]; exact frontier_connectedComponentIn_eq hC z₂ hcl₂

namespace ClosedPolygon

variable {P : ClosedPolygon m}

/-- **The polygonal Jordan curve theorem** (Theorem 2.3), in the form Definition 2.4 asks for.
The complement of a simple closed polygon has exactly two regions, one bounded and one unbounded,
and each has the polygon as its frontier.

The bounded region is `Schoenflies.inside P.carrier` and the unbounded one
`Schoenflies.outside P.carrier`; everything the blueprint writes `Int(C)` and `Ext(C)` for, and
the whole `IsSeparating` API of `Schoenflies/CrosscutCells.lean`, comes with this statement. -/
theorem isSeparating_carrier (P : ClosedPolygon m) : IsSeparating P.carrier := by
  obtain ⟨D⟩ := exists_stripData P
  obtain ⟨zL, hzL⟩ := D.isConnected_sideL.nonempty
  obtain ⟨zR, hzR⟩ := D.isConnected_sideR.nonempty
  have hzLC : zL ∉ P.carrier := sideL_subset_compl D hzL
  have hzRC : zR ∉ P.carrier := sideR_subset_compl D hzR
  have hne := P.connectedComponentIn_ne_of_mem_sides D hzL hzR
  have hall : ∀ x ∉ P.carrier, connectedComponentIn P.carrierᶜ x =
      connectedComponentIn P.carrierᶜ zL ∨
      connectedComponentIn P.carrierᶜ x = connectedComponentIn P.carrierᶜ zR :=
    fun x hx => P.connectedComponentIn_eq_of_notMem D hzL hzR hx
  -- each track is inside the component of its reference point, so the curve is in its closure
  have hsubL : D.sideL ⊆ connectedComponentIn P.carrierᶜ zL :=
    D.isConnected_sideL.isPreconnected.subset_connectedComponentIn hzL (sideL_subset_compl D)
  have hsubR : D.sideR ⊆ connectedComponentIn P.carrierᶜ zR :=
    D.isConnected_sideR.isPreconnected.subset_connectedComponentIn hzR (sideR_subset_compl D)
  have hclL : P.carrier ⊆ closure (connectedComponentIn P.carrierᶜ zL) :=
    subset_trans D.carrier_subset_closure_sideL (closure_mono hsubL)
  have hclR : P.carrier ⊆ closure (connectedComponentIn P.carrierᶜ zR) :=
    subset_trans D.carrier_subset_closure_sideR (closure_mono hsubR)
  -- a square containing the polygon; its outside lies in one of the two components
  obtain ⟨r, -, hrC⟩ := Plane.IsCompact.exists_closedSquare P.isCompact_carrier
  have hbeyC : Plane.beyondSquare r ⊆ P.carrierᶜ := by
    rw [Plane.beyondSquare_eq_compl]; exact compl_subset_compl.2 hrC
  obtain ⟨w, hw⟩ := (Plane.isConnected_beyondSquare r).nonempty
  have hbeysub : Plane.beyondSquare r ⊆ connectedComponentIn P.carrierᶜ w :=
    (Plane.isConnected_beyondSquare r).isPreconnected.subset_connectedComponentIn hw hbeyC
  rcases hall w (hbeyC hw) with hcw | hcw
  · exact isSeparating_of_two_components P.isJordanCurve_carrier P.isClosed_carrier hzRC hzLC
      (Ne.symm hne) (fun x hx => (hall x hx).symm) hclR hclL (hcw ▸ hbeysub)
  · exact isSeparating_of_two_components P.isJordanCurve_carrier P.isClosed_carrier hzLC hzRC
      hne hall hclL hclR (hcw ▸ hbeysub)

/-- Exactly two regions, explicitly: the component of any point off the polygon is one of the two
named regions. -/
theorem connectedComponentIn_eq_inside_or_outside (P : ClosedPolygon m) {x : Plane}
    (hx : x ∉ P.carrier) :
    connectedComponentIn P.carrierᶜ x = inside P.carrier ∨
      connectedComponentIn P.carrierᶜ x = outside P.carrier := by
  have h : x ∈ inside P.carrier ∪ outside P.carrier := by rw [inside_union_outside]; exact hx
  rcases h with h | h
  · exact Or.inl (P.isSeparating_carrier.connectedComponentIn_eq_inside h)
  · exact Or.inr (P.isSeparating_carrier.connectedComponentIn_eq_outside h)

/-! ### The parity values

The blueprint: "take a point `q` whose coordinate along the ray exceeds that of every point of the
compact set `C`. No edge crosses the level line through `q` beyond `q`, so `π_C(q) = 0`; and `q`
lies in the unbounded region." Here `q` is chosen to be beyond a containing *square* as well, so
that it visibly lies in the unbounded region: the outside of that square is connected, misses the
polygon, and is unbounded. -/

/-- **`π_C = 0` on the unbounded region.** Every admissible ray direction gives the same answer. -/
theorem parity_eq_zero_of_mem_outside (P : ClosedPolygon m) {u : Plane}
    (hu : Plane.IsDirection u) (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2)
    {x : Plane} (hx : x ∈ outside P.carrier) : parity u P.pieces x = 0 := by
  obtain ⟨r, -, hrC⟩ := Plane.IsCompact.exists_closedSquare P.isCompact_carrier
  obtain ⟨R, hR⟩ := P.isCompact_carrier.isBounded.subset_closedBall (0 : Plane)
  obtain ⟨q, hqbey, hqfwd⟩ := exists_beyond_of_fwd_lt hu r R
  have hbeyC : Plane.beyondSquare r ⊆ P.carrierᶜ := by
    rw [Plane.beyondSquare_eq_compl]; exact compl_subset_compl.2 hrC
  -- the crossing count vanishes at `q`: no edge reaches the level line beyond it
  have hq0 : parity u P.pieces q = 0 := by
    refine parity_eq_zero_of_lt hL fun z hz => ?_
    rw [P.cover_pieces] at hz
    have h1 : ‖z‖ ≤ R := by simpa using hR hz
    have h2 : fwd u z ≤ R := le_trans (le_trans (le_abs_self _) (abs_fwd_le_norm hu z)) h1
    linarith
  -- and `q` is in the unbounded region, since the outside of the square is
  have hqout : q ∈ outside P.carrier :=
    ⟨hbeyC hqbey, fun hb => not_isBounded_beyondSquare r (hb.subset
      ((Plane.isConnected_beyondSquare r).isPreconnected.subset_connectedComponentIn
        hqbey hbeyC))⟩
  rw [← hq0]
  exact parity_eq_of_isPreconnected hu hL P.isClosedChain_pieces
    P.isSeparating_carrier.isConnected_outside.isPreconnected
    (fun z hz => by rw [P.cover_pieces]; exact hz.1) hx hqout

/-- **`π_C = 1` on the bounded region.** The two tracks of the collar have opposite parity and lie
in the two different regions, so the region that is not the unbounded one carries the parity that
is not `0`. -/
theorem parity_eq_one_of_mem_inside (P : ClosedPolygon m) {u : Plane}
    (hu : Plane.IsDirection u) (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2)
    {x : Plane} (hx : x ∈ inside P.carrier) : parity u P.pieces x = 1 := by
  obtain ⟨D⟩ := exists_stripData P
  obtain ⟨zL, hzL⟩ := D.isConnected_sideL.nonempty
  obtain ⟨zR, hzR⟩ := D.isConnected_sideR.nonempty
  have hpne := P.parity_ne_of_mem_sides D hu hL hzL hzR
  have hconst : ∀ y ∈ inside P.carrier, parity u P.pieces y = parity u P.pieces x :=
    fun y hy => parity_eq_of_isPreconnected hu hL P.isClosedChain_pieces
      P.isSeparating_carrier.isConnected_inside.isPreconnected
      (fun z hz => by rw [P.cover_pieces]; exact hz.1) hy hx
  have hmemL : zL ∈ inside P.carrier ∪ outside P.carrier := by
    rw [inside_union_outside]; exact sideL_subset_compl D hzL
  have hmemR : zR ∈ inside P.carrier ∪ outside P.carrier := by
    rw [inside_union_outside]; exact sideR_subset_compl D hzR
  refine zmod_two_eq_one_of_ne_zero ?_
  rcases hmemL with h | h <;> rcases hmemR with h' | h'
  · exact absurd ((hconst zL h).trans (hconst zR h').symm) hpne
  · rw [← hconst zL h, ← P.parity_eq_zero_of_mem_outside hu hL h']
    exact hpne
  · rw [← hconst zR h', ← P.parity_eq_zero_of_mem_outside hu hL h]
    exact Ne.symm hpne
  · exact absurd ((P.parity_eq_zero_of_mem_outside hu hL h).trans
      (P.parity_eq_zero_of_mem_outside hu hL h').symm) hpne

/-! ### The theorem, unpacked -/

/-- **The polygonal Jordan curve theorem** (Theorem 2.3), spelled out. The complement of a simple
closed polygon is the disjoint union of two nonempty connected open sets, one bounded and one
unbounded, each a connected component of the complement and each with the polygon as its
frontier. -/
theorem polygonal_jordan (P : ClosedPolygon m) :
    IsJordanCurve P.carrier ∧ IsPolygonal P.carrier ∧
      IsOpen (inside P.carrier) ∧ IsOpen (outside P.carrier) ∧
      IsConnected (inside P.carrier) ∧ IsConnected (outside P.carrier) ∧
      Disjoint (inside P.carrier) (outside P.carrier) ∧
      inside P.carrier ∪ outside P.carrier = P.carrierᶜ ∧
      IsBounded (inside P.carrier) ∧ ¬ IsBounded (outside P.carrier) ∧
      (∀ x ∉ P.carrier, connectedComponentIn P.carrierᶜ x = inside P.carrier ∨
        connectedComponentIn P.carrierᶜ x = outside P.carrier) ∧
      frontier (inside P.carrier) = P.carrier ∧ frontier (outside P.carrier) = P.carrier :=
  ⟨P.isJordanCurve_carrier, P.isPolygonal_carrier,
    P.isSeparating_carrier.isOpen_inside, P.isSeparating_carrier.isOpen_outside,
    P.isSeparating_carrier.isConnected_inside, P.isSeparating_carrier.isConnected_outside,
    disjoint_inside_outside, inside_union_outside _,
    P.isSeparating_carrier.isBounded_inside, P.isSeparating_carrier.not_isBounded_outside,
    fun _ hx => P.connectedComponentIn_eq_inside_or_outside hx,
    P.isSeparating_carrier.frontier_inside, P.isSeparating_carrier.frontier_outside⟩

end ClosedPolygon

/-- **Non-vacuity.** The triangle with vertices `(0,0)`, `(1,0)`, `(0,1)` separates the plane.

`Schoenflies.unitTriangle` is the one `ClosedPolygon` the development exhibits, and this is the
check that the whole chain applies to it: the collar constants `exists_stripData`, the collar
itself, the crossing parity, and the separation above. Without it every statement in this file
would formally be a statement about a structure with no known inhabitant. -/
theorem isSeparating_unitTriangle : IsSeparating unitTriangle.carrier :=
  unitTriangle.isSeparating_carrier

end Schoenflies

end BundlePart411

section BundlePart412
/- Source: dev/planar_search/schoenflies_port/Schoenflies/ParitySplitting.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/



/-!
# Parity splitting: a crosscut adds the two crossing counts

Lemma 2.7. A crosscut `P` of a simple closed polygon `C` cuts it into two arcs `A₁, A₂`, and
the two closed curves `Jᵢ = Aᵢ ∪ P` satisfy `π_C = π_{J₁} + π_{J₂}` off `C ∪ P`. The blueprint
calls this identity "the whole of the polygonal crosscut theorem": Lemma 2.6 exhibits two cells
of `Ω ∖ P`, and this is what says there are no others.

## Where the split is made, and why

The crossing count of `Schoenflies/Parity.lean` is a function of a `List Piece`, not of a set,
and not of a `ClosedPolygon`. Two edge lists with the same carrier can have different parity —
a list that traverses one segment twice is the obvious example — so the identity cannot be
stated for the sets `Aᵢ ∪ P`. It is stated, and proved, for **edge lists**:

    the edge list of `C` is `A₁ ++ A₂`, that of `Jᵢ` is `Aᵢ ++ K`,

where `K` is the edge list of the crosscut. Then `π_{J₁} + π_{J₂} = π_{A₁} + π_{A₂} + 2 π_K`
and the crosscut's contribution cancels mod `2`. That is `parity_split`, and it needs no
geometry at all — no simplicity, no direction, no separation. Everything the blueprint's
picture contributes is in the *hypothesis* that the lists decompose that way.

Two mismatches between "the edge list of `Jᵢ` is `Aᵢ` together with `K`" and literal list
equality have to be absorbed, because a consumer building `Jᵢ` as a `ClosedPolygon` controls
neither:

* the edges come in some cyclic order of that polygon's own choosing, and
* one of the two curves must traverse the crosscut backwards, so its pieces are the *reversed*
  pairs.

`SameEdges` is the equivalence that forgives exactly these two: a permutation of the lists
after each piece has been put in canonical order by `Schoenflies.orientPiece`. Parity, carrier,
closedness and non-levelness are all invariant under it (`SameEdges.parity_eq`,
`SameEdges.cover_eq`, `SameEdges.isChainFrom`, `SameEdges.hgt_ne`), so a consumer may hand over
its edge list in whatever order and orientation it happens to have —
`sameEdges_of_perm_reverse_swap` absorbs both mismatches in one step.

Nothing is assumed about the *sets*: `ClosedPolygon.carrier_eq_of_sameEdges` derives
`Jᵢ.carrier = Aᵢ ∪ P` from the edge lists alone, so the geometric hypothesis a consumer has to
discharge is only ever combinatorial.

## The construction

`ClosedPolygon.arcPieces C a k` is the edge list of the arc of `C` that leaves vertex `a` and
runs forward through `k` edges — the object the split produces, exported as an object rather
than hidden behind an existential. Its two governing facts are

* `ClosedPolygon.arcPieces_split_perm`: `arcPieces C a k ++ arcPieces C (a + k) (m + 3 - k)` is
  a permutation of `C.pieces` — the arcs really do partition the edges; and
* `ClosedPolygon.isChainFrom_arcPieces`: the arc's mod-`2` boundary is its two end vertices,
  which is what makes `Aᵢ ++ K` a *closed* chain and hence eligible for every parity theorem.

`IsChainFrom` is the open-path companion of `Schoenflies.IsClosedChain`, stated by the same
duality; `IsChainFrom.isClosedChain_append` is the one-line reason that an arc and a crosscut
with the same two ends close up. `pathPieces` turns a polyline into such a chain, which is how
the crosscut itself is normally presented.

The endpoints of the crosscut are taken to be **vertices** of `C`; the blueprint's opening
move, "subdivide `C` at `p` and `q`", is what puts them there, and is `parity_subdivide`
(Lemma 2.1) applied before any of this. Nothing below re-proves it. A consumer whose crosscut
lands in the interiors of edges rewrites with `parity_subdivide` first and then applies
`parity_split` to the subdivided list, whose hypotheses are about lists and not about polygons;
what such a consumer must supply for itself is the decomposition of the *subdivided* list into
two arcs, which `arcPieces` does not provide — `arcPieces` splits `C.pieces` at vertices.

## Blueprint

* `SameEdges`, `IsChainFrom`, `pathPieces`, `ClosedPolygon.arcPieces` — the definition of the
  split. "After the subdivision the edge set of `C` is the disjoint union of the edge sets of
  `A₁` and `A₂`, and the edge set of `Jᵢ` is that of `Aᵢ` together with that of `P`."
* `parity_split`, `ClosedPolygon.parity_splitting` — Lemma 2.7, equation (2.2)
  `π_C = π_{J₁} + π_{J₂}`.
* `ClosedPolygon.crosscut_inside_exactly_one`, `ClosedPolygon.crosscut_outside_agree` — the
  "Consequently" of Lemma 2.7, which is where Theorem 2.3 enters: a point of `Int(C)` off `P`
  lies inside exactly one of `J₁, J₂`, and a point of `Ext(C)` off `P` lies inside both or
  inside neither.
* `ClosedPolygon.parity_eq_one_iff` — the two halves of the last sentence of Theorem 2.3, read
  as a single criterion.
* `ClosedPolygon.carrier_eq_of_sameEdges`, `ClosedPolygon.notMem_carrier_of_sameEdges` — the
  bridge back to the sets: `Jᵢ` occupies `Aᵢ ∪ P`, so "off `C` and off `P`" is "off `Jᵢ`".

One lemma here strengthens one on `main`: `mark_swap'` drops the non-levelness hypothesis of
`Schoenflies.mark_swap`, because a level edge is crossed from nowhere and so contributes `0`
under either name. Its home is `Schoenflies/Parity.lean`.
-/

open Metric Set

namespace Schoenflies

variable {u p q r : Plane} {L L₁ L₂ L₃ : List Piece} {m : ℕ}

/-! ## Edge lists up to order and orientation

Parity, carrier and closedness are all functions of the *multiset of unoriented* edges. This
section says so, so that a consumer may present the edge list of a curve in any order and with
either name for each edge. -/

/-- A level edge is crossed from nowhere: the ray from `q` would have to leave at a height both
`≥` and `<` the common height of the two ends. -/
theorem not_crosses_of_level {c d : Plane} (h : hgt u c = hgt u d) (q : Plane) :
    ¬ Crosses u (c, d) q := by
  intro hcr
  obtain ⟨h1, h2, -⟩ := hcr
  have e1 : ((c, d) : Piece).1 = c := rfl
  have e2 : ((c, d) : Piece).2 = d := rfl
  rw [e1, e2, h, min_self] at h1
  rw [e1, e2, h, max_self] at h2
  linarith

/-- **The contribution of an edge does not depend on which end is named first.** This is
`Schoenflies.mark_swap` with its non-levelness hypothesis removed: a level edge contributes `0`
under either name. -/
theorem mark_swap' (u : Plane) (P : Piece) (q : Plane) : mark u (P.2, P.1) q = mark u P q := by
  obtain ⟨a, b⟩ := P
  by_cases h : hgt u a = hgt u b
  · rw [mark, mark, if_neg (not_crosses_of_level h.symm q), if_neg (not_crosses_of_level h q)]
  · exact mark_swap h q

/-- Reordering the edges does not change the count. -/
theorem parity_perm (h : L₁.Perm L₂) (u q : Plane) : parity u L₁ q = parity u L₂ q :=
  (h.map fun P => mark u P q).sum_eq

/-- Reordering the edges does not change what they occupy. -/
theorem cover_perm (h : L₁.Perm L₂) : cover L₁ = cover L₂ := by
  ext z
  simp only [cover, mem_iUnion, exists_prop]
  exact ⟨fun ⟨P, hP, hz⟩ => ⟨P, h.mem_iff.1 hP, hz⟩, fun ⟨P, hP, hz⟩ => ⟨P, h.mem_iff.2 hP, hz⟩⟩

/-- `orientPiece` either leaves a piece alone or reverses it; that is all this file uses. -/
theorem orientPiece_eq_or (P : Piece) : orientPiece P = P ∨ orientPiece P = (P.2, P.1) := by
  by_cases h : Precedes P.1 P.2
  · exact Or.inl (orientPiece_of_precedes h)
  · exact Or.inr (orientPiece_of_not_precedes h)

theorem mark_orientPiece (u : Plane) (P : Piece) (q : Plane) :
    mark u (orientPiece P) q = mark u P q := by
  rcases orientPiece_eq_or P with h | h
  · rw [h]
  · rw [h, mark_swap']

theorem parity_map_orientPiece (u : Plane) (L : List Piece) (q : Plane) :
    parity u (L.map orientPiece) q = parity u L q := by
  simp only [parity, List.map_map]
  exact congrArg List.sum (List.map_congr_left fun P _ => mark_orientPiece u P q)

theorem hgt_ne_orientPiece {P : Piece} (h : hgt u P.1 ≠ hgt u P.2) :
    hgt u (orientPiece P).1 ≠ hgt u (orientPiece P).2 := by
  rcases orientPiece_eq_or P with e | e
  · rw [e]; exact h
  · rw [e]; exact fun hh => h hh.symm

theorem hgt_ne_of_orientPiece {P : Piece} (h : hgt u (orientPiece P).1 ≠ hgt u (orientPiece P).2) :
    hgt u P.1 ≠ hgt u P.2 := by
  rcases orientPiece_eq_or P with e | e
  · rw [e] at h; exact h
  · rw [e] at h; exact fun hh => h hh.symm

/-- Orienting a piece does not change its mod-`2` boundary. -/
theorem chainSum_map_orientPiece (f : Plane → ZMod 2) (L : List Piece) :
    ((L.map orientPiece).map fun P => f P.1 + f P.2).sum
      = (L.map fun P => f P.1 + f P.2).sum := by
  simp only [List.map_map]
  refine congrArg List.sum (List.map_congr_left fun P _ => ?_)
  rcases orientPiece_eq_or P with e | e
  · rw [Function.comp_apply, e]
  · rw [Function.comp_apply, e]; exact add_comm _ _

/-- **Two edge lists carry the same edges**: they agree after reordering, each edge being free
to be named by either of its two ends first. This is the relation under which "the edge list of
`Jᵢ` is that of `Aᵢ` together with that of `P`" is true — a `ClosedPolygon` built on `Aᵢ ∪ P`
lists its edges in its own cyclic order, and traverses one of the two pieces backwards. -/
def SameEdges (L₁ L₂ : List Piece) : Prop := (L₁.map orientPiece).Perm (L₂.map orientPiece)

@[refl] theorem SameEdges.refl (L : List Piece) : SameEdges L L := List.Perm.refl _

theorem SameEdges.symm (h : SameEdges L₁ L₂) : SameEdges L₂ L₁ := List.Perm.symm h

theorem SameEdges.trans (h₁ : SameEdges L₁ L₂) (h₂ : SameEdges L₂ L₃) : SameEdges L₁ L₃ :=
  List.Perm.trans h₁ h₂

/-- A reordering is in particular the same edges. -/
theorem SameEdges.of_perm (h : L₁.Perm L₂) : SameEdges L₁ L₂ := h.map _

theorem SameEdges.append {L₁' L₂' : List Piece} (h₁ : SameEdges L₁ L₁') (h₂ : SameEdges L₂ L₂') :
    SameEdges (L₁ ++ L₂) (L₁' ++ L₂') := by
  simpa only [SameEdges, List.map_append] using List.Perm.append h₁ h₂

theorem sameEdges_reverse (L : List Piece) : SameEdges L.reverse L :=
  SameEdges.of_perm (List.reverse_perm L)

/-- **Reversing every edge changes nothing.** This is the clause a consumer needs when its
second curve traverses the crosscut backwards. -/
theorem sameEdges_map_swap (L : List Piece) : SameEdges (L.map fun P => (P.2, P.1)) L := by
  have : (L.map fun P => (P.2, P.1)).map orientPiece = L.map orientPiece := by
    rw [List.map_map]
    exact List.map_congr_left fun P _ => orientPiece_swap P
  rw [SameEdges, this]

/-- **The shape a consumer arrives with.** A `ClosedPolygon` built on `Aᵢ ∪ P` lists its edges
in a cyclic order of its own choosing — any permutation — and one of the two must run the
crosscut backwards, which reverses the list and names every piece the other way round. All of
that is forgiven at once. -/
theorem sameEdges_of_perm_reverse_swap {L A K : List Piece}
    (h : L.Perm (A ++ (K.map fun P => (P.2, P.1)).reverse)) : SameEdges L (A ++ K) :=
  (SameEdges.of_perm h).trans
    (SameEdges.append (SameEdges.refl A) ((sameEdges_reverse _).trans (sameEdges_map_swap K)))

theorem SameEdges.parity_eq (h : SameEdges L₁ L₂) (u q : Plane) :
    parity u L₁ q = parity u L₂ q := by
  rw [← parity_map_orientPiece u L₁ q, ← parity_map_orientPiece u L₂ q]
  exact parity_perm h u q

theorem SameEdges.cover_eq (h : SameEdges L₁ L₂) : cover L₁ = cover L₂ := by
  rw [← cover_map_orientPiece L₁, ← cover_map_orientPiece L₂]
  exact cover_perm h

/-- Every edge of `L₁` is an edge of `L₂`, up to the naming of its two ends. -/
theorem SameEdges.exists_mem (h : SameEdges L₁ L₂) {Q : Piece} (hQ : Q ∈ L₁) :
    ∃ R ∈ L₂, orientPiece R = orientPiece Q := by
  have hmem : orientPiece Q ∈ L₂.map orientPiece :=
    h.mem_iff.1 (List.mem_map_of_mem (f := orientPiece) hQ)
  obtain ⟨R, hR, hRQ⟩ := List.mem_map.1 hmem
  exact ⟨R, hR, hRQ⟩

/-- Non-levelness for a direction transfers: it is a property of the unoriented edge. -/
theorem SameEdges.hgt_ne (h : SameEdges L₁ L₂) (hL : ∀ Q ∈ L₂, hgt u Q.1 ≠ hgt u Q.2) :
    ∀ Q ∈ L₁, hgt u Q.1 ≠ hgt u Q.2 := by
  intro Q hQ
  obtain ⟨R, hR, hRQ⟩ := h.exists_mem hQ
  exact hgt_ne_of_orientPiece (hRQ ▸ hgt_ne_orientPiece (hL R hR))

theorem hgt_ne_append (h₁ : ∀ Q ∈ L₁, hgt u Q.1 ≠ hgt u Q.2)
    (h₂ : ∀ Q ∈ L₂, hgt u Q.1 ≠ hgt u Q.2) : ∀ Q ∈ L₁ ++ L₂, hgt u Q.1 ≠ hgt u Q.2 := by
  intro Q hQ
  rcases List.mem_append.1 hQ with h | h
  · exact h₁ Q h
  · exact h₂ Q h

/-! ## Chains with two ends

`Schoenflies.IsClosedChain` says the mod-`2` boundary of an edge list vanishes. An arc and a
crosscut are not closed; each has a boundary, namely its two ends, and closing them up is the
statement that the two boundaries agree. Stated by the same duality as `IsClosedChain`, so that
the two definitions compose with nothing but `List.sum_append`. -/

/-- `L` is a **chain from `p` to `q`**: its mod-`2` boundary is `p` together with `q`. Stated by
duality, exactly as `Schoenflies.IsClosedChain` is. -/
def IsChainFrom (L : List Piece) (p q : Plane) : Prop :=
  ∀ f : Plane → ZMod 2, (L.map fun P => f P.1 + f P.2).sum = f p + f q

/-- A chain whose two ends coincide is a closed chain, and conversely. -/
theorem isChainFrom_self_iff : IsChainFrom L p p ↔ IsClosedChain L := by
  constructor <;> intro h f
  · rw [h f]; exact add_self_zmod_two _
  · rw [h f]; exact (add_self_zmod_two _).symm

theorem isChainFrom_nil (p : Plane) : IsChainFrom [] p p := fun f => by
  simp [(add_self_zmod_two (f p)).symm]

/-- Chains compose end to end. -/
theorem IsChainFrom.append (h₁ : IsChainFrom L₁ p q) (h₂ : IsChainFrom L₂ q r) :
    IsChainFrom (L₁ ++ L₂) p r := by
  intro f
  rw [List.map_append, List.sum_append, h₁ f, h₂ f]
  linear_combination add_self_zmod_two (f q)

/-- **Two chains with the same two ends close up.** This is the whole reason `Aᵢ ∪ P` is a
closed curve as far as the crossing count is concerned. -/
theorem IsChainFrom.isClosedChain_append (h₁ : IsChainFrom L₁ p q) (h₂ : IsChainFrom L₂ p q) :
    IsClosedChain (L₁ ++ L₂) := by
  intro f
  rw [List.map_append, List.sum_append, h₁ f, h₂ f]
  exact add_self_zmod_two _

theorem SameEdges.isChainFrom (h : SameEdges L₁ L₂) (h₂ : IsChainFrom L₂ p q) :
    IsChainFrom L₁ p q := by
  intro f
  rw [← chainSum_map_orientPiece f L₁, (h.map fun P => f P.1 + f P.2).sum_eq,
    chainSum_map_orientPiece, h₂ f]

theorem SameEdges.isClosedChain (h : SameEdges L₁ L₂) (h₂ : IsClosedChain L₂) :
    IsClosedChain L₁ := by
  intro f
  rw [← chainSum_map_orientPiece f L₁, (h.map fun P => f P.1 + f P.2).sum_eq,
    chainSum_map_orientPiece, h₂ f]

/-! ### The edges of a polyline

How a crosscut is normally presented: a list of points. `pathPieces` reads off its edges, and
`isChainFrom_pathPieces` says its boundary is the two ends of the list. -/

/-- The edges of the polyline `v₀, v₁, …, v_k`. -/
def pathPieces : List Plane → List Piece
  | [] => []
  | [_] => []
  | v :: w :: rest => (v, w) :: pathPieces (w :: rest)

@[simp] theorem pathPieces_nil : pathPieces [] = [] := rfl

@[simp] theorem pathPieces_singleton (v : Plane) : pathPieces [v] = [] := rfl

@[simp] theorem pathPieces_cons_cons (v w : Plane) (rest : List Plane) :
    pathPieces (v :: w :: rest) = (v, w) :: pathPieces (w :: rest) := rfl

/-- **A polyline is a chain from its first point to its last.** -/
theorem isChainFrom_pathPieces (p : Plane) (mid : List Plane) (q : Plane) :
    IsChainFrom (pathPieces (p :: (mid ++ [q]))) p q := by
  induction mid generalizing p with
  | nil =>
    intro f
    simp
  | cons w ws ih =>
    intro f
    rw [List.cons_append, pathPieces_cons_cons, List.map_cons, List.sum_cons, ih w f]
    linear_combination add_self_zmod_two (f w)

/-- The edges of a polyline occupy the polyline. -/
theorem cover_pathPieces (p : Plane) (mid : List Plane) (q : Plane) :
    cover (pathPieces (p :: (mid ++ [q]))) = poly (p :: (mid ++ [q])) := by
  induction mid generalizing p with
  | nil =>
    rw [List.nil_append, pathPieces_cons_cons, pathPieces_singleton, cover_cons, cover_nil,
      poly_cons_cons, poly_singleton, union_empty]
    exact (union_eq_self_of_subset_right
      (singleton_subset_iff.2 (right_mem_segment ℝ p q))).symm
  | cons w ws ih =>
    rw [List.cons_append, pathPieces_cons_cons, cover_cons, ih w, poly_cons_cons]
    rfl

/-! ## The two arcs of a polygon

`arcPieces C a k` is the edge list of the arc of `C` that leaves vertex `a` and runs forward
through `k` edges. Its two ends are vertices `a` and `a + k`, and for `k ≤ m + 3` the two arcs
`arcPieces C a k` and `arcPieces C (a + k) (m + 3 - k)` between them use each edge of `C`
exactly once. -/

namespace ClosedPolygon

variable {C : ClosedPolygon m} {a : ZMod (m + 3)} {k : ℕ}

/-- The edge list of the arc of `C` that leaves vertex `a` and runs forward through `k` edges.
For `k ≤ m + 3` this is one of the two arcs a crosscut with endpoints `C.vertex a` and
`C.vertex (a + k)` cuts `C` into; the other is `arcPieces C (a + k) (m + 3 - k)`. -/
def arcPieces (C : ClosedPolygon m) (a : ZMod (m + 3)) (k : ℕ) : List Piece :=
  (List.range k).map fun t : ℕ => (C.vertex (a + t), C.vertex (a + t + 1))

@[simp] theorem arcPieces_zero (C : ClosedPolygon m) (a : ZMod (m + 3)) :
    C.arcPieces a 0 = [] := rfl

/-- Running through `k + l` edges is running through `k` and then through `l`. -/
theorem arcPieces_add (C : ClosedPolygon m) (a : ZMod (m + 3)) (k l : ℕ) :
    C.arcPieces a (k + l) = C.arcPieces a k ++ C.arcPieces (a + k) l := by
  rw [arcPieces, arcPieces, arcPieces, List.range_add, List.map_append, List.map_map]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  simp only [Function.comp_apply, Nat.cast_add, ← add_assoc]

/-- Running through all `m + 3` edges from vertex `0` is the whole edge list. -/
theorem arcPieces_full (C : ClosedPolygon m) : C.arcPieces 0 (m + 3) = C.pieces := by
  rw [arcPieces, pieces]
  exact List.map_congr_left fun t _ => by rw [zero_add]

/-- Every edge of an arc is an edge of the polygon; non-levelness and nondegeneracy follow. -/
theorem mem_pieces_of_mem_arcPieces {Q : Piece} (hQ : Q ∈ C.arcPieces a k) : Q ∈ C.pieces := by
  obtain ⟨t, -, rfl⟩ := List.mem_map.1 hQ
  exact C.mem_pieces _

theorem arcPieces_nondeg (C : ClosedPolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    ∀ Q ∈ C.arcPieces a k, Q.Nondeg :=
  fun _ hQ => C.pieces_nondeg _ (mem_pieces_of_mem_arcPieces hQ)

theorem arcPieces_hgt_ne (hL : ∀ Q ∈ C.pieces, hgt u Q.1 ≠ hgt u Q.2) :
    ∀ Q ∈ C.arcPieces a k, hgt u Q.1 ≠ hgt u Q.2 :=
  fun _ hQ => hL _ (mem_pieces_of_mem_arcPieces hQ)

/-- **An arc is a chain from its first vertex to its last.** The telescoping sum of the
blueprint's "counting edge by edge", read off `Schoenflies.sum_range_boundary`. -/
theorem isChainFrom_arcPieces (C : ClosedPolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    IsChainFrom (C.arcPieces a k) (C.vertex a) (C.vertex (a + k)) := by
  intro f
  have hmap : ((C.arcPieces a k).map fun P => f P.1 + f P.2)
      = (List.range k).map fun j : ℕ =>
          f (C.vertex (a + (j : ZMod (m + 3))))
            + f (C.vertex (a + ((j + 1 : ℕ) : ZMod (m + 3)))) := by
    rw [arcPieces, List.map_map]
    refine List.map_congr_left fun t _ => ?_
    simp only [Function.comp_apply, natCast_succ, ← add_assoc]
  have key := sum_range_boundary (fun i : ℕ => f (C.vertex (a + (i : ZMod (m + 3))))) k
  rw [hmap, key]
  simp

/-- **The two arcs from a vertex use every edge exactly once.** Cutting the cycle at `a` is a
rotation, and a rotation is a permutation: the list is `X ++ Y` and `C.pieces` is `Y ++ X`. -/
theorem arcPieces_full_perm (C : ClosedPolygon m) (a : ZMod (m + 3)) :
    (C.arcPieces a (m + 3)).Perm C.pieces := by
  have hlt : a.val < m + 3 := ZMod.val_lt a
  have hcast : ((a.val : ℕ) : ZMod (m + 3)) = a := ZMod.natCast_rightInverse a
  -- the tail of the cycle, from `a` back round to `0`
  have hzero : a + ((m + 3 - a.val : ℕ) : ZMod (m + 3)) = 0 := by
    rw [Nat.cast_sub hlt.le, hcast]
    simp
  have hsplit1 : C.arcPieces a (m + 3)
      = C.arcPieces a (m + 3 - a.val) ++ C.arcPieces 0 a.val := by
    have h1 : (m + 3 - a.val) + a.val = m + 3 := by omega
    have h2 := arcPieces_add C a (m + 3 - a.val) a.val
    rwa [h1, hzero] at h2
  have hsplit2 : C.pieces = C.arcPieces 0 a.val ++ C.arcPieces a (m + 3 - a.val) := by
    have h1 : a.val + (m + 3 - a.val) = m + 3 := by omega
    have h2 := arcPieces_add C 0 a.val (m + 3 - a.val)
    rw [h1, arcPieces_full, zero_add, hcast] at h2
    exact h2
  rw [hsplit1, hsplit2]
  exact List.perm_append_comm

/-- **The split.** For `k ≤ m + 3` the two arcs at `a` and `a + k` between them use every edge
of `C` exactly once. -/
theorem arcPieces_split_perm (C : ClosedPolygon m) (a : ZMod (m + 3)) (hk : k ≤ m + 3) :
    (C.arcPieces a k ++ C.arcPieces (a + k) (m + 3 - k)).Perm C.pieces := by
  rw [← arcPieces_add, Nat.add_sub_cancel' hk]
  exact arcPieces_full_perm C a

theorem sameEdges_arcPieces_split (C : ClosedPolygon m) (a : ZMod (m + 3)) (hk : k ≤ m + 3) :
    SameEdges C.pieces (C.arcPieces a k ++ C.arcPieces (a + k) (m + 3 - k)) :=
  SameEdges.of_perm (arcPieces_split_perm C a hk).symm

/-- The two arcs between them carry the polygon. -/
theorem cover_arcPieces_union (C : ClosedPolygon m) (a : ZMod (m + 3)) (hk : k ≤ m + 3) :
    cover (C.arcPieces a k) ∪ cover (C.arcPieces (a + k) (m + 3 - k)) = C.carrier := by
  rw [← cover_append, cover_perm (arcPieces_split_perm C a hk), cover_pieces]

theorem cover_arcPieces_subset (C : ClosedPolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    cover (C.arcPieces a k) ⊆ C.carrier := by
  intro z hz
  obtain ⟨R, hR, hzR⟩ := exists_of_mem_cover hz
  rw [← cover_pieces]
  exact mem_cover (mem_pieces_of_mem_arcPieces hR) hzR

/-- **The two curves of the split are closed chains.** An arc from `C.vertex a` to
`C.vertex (a + k)` and a crosscut with the same two ends close up. -/
theorem isClosedChain_arcPieces_append {K : List Piece}
    (hK : IsChainFrom K (C.vertex a) (C.vertex (a + k))) :
    IsClosedChain (C.arcPieces a k ++ K) :=
  (isChainFrom_arcPieces C a k).isClosedChain_append hK

theorem arcPieces_append_hgt_ne {K : List Piece}
    (hC : ∀ Q ∈ C.pieces, hgt u Q.1 ≠ hgt u Q.2) (hK : ∀ Q ∈ K, hgt u Q.1 ≠ hgt u Q.2) :
    ∀ Q ∈ C.arcPieces a k ++ K, hgt u Q.1 ≠ hgt u Q.2 :=
  hgt_ne_append (arcPieces_hgt_ne hC) hK

/-- **A curve of the split occupies its arc together with the crosscut.** Only the edge list of
`J` is assumed related to the split; its carrier then is what the blueprint calls `Aᵢ ∪ P`. -/
theorem carrier_eq_of_sameEdges {m' : ℕ} {J : ClosedPolygon m'} {K : List Piece}
    (h : SameEdges J.pieces (C.arcPieces a k ++ K)) :
    J.carrier = cover (C.arcPieces a k) ∪ cover K := by
  rw [← cover_pieces, h.cover_eq, cover_append]

/-- Hence a point off `C` and off the crosscut is off `J`: the blueprint's "a point of
`Int(C)` off `P`" needs nothing else. -/
theorem notMem_carrier_of_sameEdges {m' : ℕ} {J : ClosedPolygon m'} {K : List Piece}
    (h : SameEdges J.pieces (C.arcPieces a k ++ K)) {x : Plane} (hxC : x ∉ C.carrier)
    (hxK : x ∉ cover K) : x ∉ J.carrier := by
  rw [carrier_eq_of_sameEdges h]
  rintro (hx | hx)
  · exact hxC (cover_arcPieces_subset C a k hx)
  · exact hxK hx

end ClosedPolygon

/-! ## The identity

Everything above was the definition. The identity itself is one line of `ZMod 2` arithmetic:
the crosscut is counted once in each of `π_{J₁}` and `π_{J₂}`, so its contribution cancels. -/

/-- **Parity splitting** (Lemma 2.7), in edge-list form and with no geometry whatever. If the
edge list of `C` is the two arcs `A₁, A₂` and the edge list of `Jᵢ` is `Aᵢ` together with the
crosscut's list `K` — in each case up to reordering and up to reversing individual edges — then
`π_{J₁} + π_{J₂} = π_C` at *every* point of the plane.

The hypotheses carry all of the blueprint's picture; the proof is that `K` is counted twice. -/
theorem parity_split (u : Plane) {LC A₁ A₂ K : List Piece}
    (hC : SameEdges LC (A₁ ++ A₂)) (h₁ : SameEdges L₁ (A₁ ++ K)) (h₂ : SameEdges L₂ (A₂ ++ K))
    (q : Plane) : parity u L₁ q + parity u L₂ q = parity u LC q := by
  rw [h₁.parity_eq u q, h₂.parity_eq u q, hC.parity_eq u q, parity_append, parity_append,
    parity_append]
  linear_combination add_self_zmod_two (parity u K q)

namespace ClosedPolygon

variable {C : ClosedPolygon m} {a : ZMod (m + 3)} {k : ℕ}

/-- **Parity splitting** (Lemma 2.7) for a simple closed polygon cut at two of its vertices.
`K` is the edge list of the crosscut, `L₁` and `L₂` the edge lists of the two curves
`Jᵢ = Aᵢ ∪ P`; each is required only to carry the right edges, in any order and with either
name for each edge.

No hypothesis on `K` is needed: whatever it is, it is counted once on each side and cancels. -/
theorem parity_splitting (C : ClosedPolygon m) (u : Plane) (a : ZMod (m + 3)) (hk : k ≤ m + 3)
    {K : List Piece} (h₁ : SameEdges L₁ (C.arcPieces a k ++ K))
    (h₂ : SameEdges L₂ (C.arcPieces (a + k) (m + 3 - k) ++ K)) (q : Plane) :
    parity u L₁ q + parity u L₂ q = parity u C.pieces q :=
  parity_split u (sameEdges_arcPieces_split C a hk) h₁ h₂ q

/-! ### What the identity says about the regions

Theorem 2.3 fixes the two values of `π` for each of the three curves — `1` on the bounded
region, `0` on the unbounded one — and the identity then reads off the blueprint's
"consequently". -/

/-- **The crossing count decides the region** (Theorem 2.3, last sentence, as a criterion).
Off the polygon, `π_C = 1` exactly on the bounded region. -/
theorem parity_eq_one_iff (C : ClosedPolygon m) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ C.pieces, hgt u Q.1 ≠ hgt u Q.2) {x : Plane} (hx : x ∉ C.carrier) :
    parity u C.pieces x = 1 ↔ x ∈ inside C.carrier := by
  have hmem : x ∈ inside C.carrier ∪ outside C.carrier := by
    rw [inside_union_outside]; exact hx
  refine ⟨fun h => ?_, C.parity_eq_one_of_mem_inside hu hL⟩
  rcases hmem with h' | h'
  · exact h'
  · rw [C.parity_eq_zero_of_mem_outside hu hL h'] at h
    exact absurd h (by decide)

/-- **A point inside `C` and off the crosscut is inside exactly one of `J₁, J₂`** — the first
half of the "Consequently" of Lemma 2.7. The left side of the splitting identity is `1`, so
exactly one of the two right-hand terms is.

"Off the crosscut" is `x ∉ cover K`; that `x` is off `J₁` and off `J₂` as well is not assumed
but derived, by `notMem_carrier_of_sameEdges`. -/
theorem crosscut_inside_exactly_one {m₁ m₂ : ℕ} (C : ClosedPolygon m) (J₁ : ClosedPolygon m₁)
    (J₂ : ClosedPolygon m₂) {u : Plane} (hu : Plane.IsDirection u)
    (hC : ∀ Q ∈ C.pieces, hgt u Q.1 ≠ hgt u Q.2) {K : List Piece}
    (hK : ∀ Q ∈ K, hgt u Q.1 ≠ hgt u Q.2) (hk : k ≤ m + 3)
    (h₁ : SameEdges J₁.pieces (C.arcPieces a k ++ K))
    (h₂ : SameEdges J₂.pieces (C.arcPieces (a + k) (m + 3 - k) ++ K))
    {x : Plane} (hx : x ∈ inside C.carrier) (hxK : x ∉ cover K) :
    x ∈ inside J₁.carrier ↔ x ∉ inside J₂.carrier := by
  have hJ₁ := h₁.hgt_ne (arcPieces_append_hgt_ne hC hK)
  have hJ₂ := h₂.hgt_ne (arcPieces_append_hgt_ne hC hK)
  have hsum := C.parity_splitting u a hk h₁ h₂ x
  rw [C.parity_eq_one_of_mem_inside hu hC hx] at hsum
  have harith : ∀ s t : ZMod 2, s + t = 1 → (s = 1 ↔ ¬ t = 1) := by decide
  rw [← J₁.parity_eq_one_iff hu hJ₁ (notMem_carrier_of_sameEdges h₁ hx.1 hxK),
    ← J₂.parity_eq_one_iff hu hJ₂ (notMem_carrier_of_sameEdges h₂ hx.1 hxK)]
  exact harith _ _ hsum

/-- **A point outside `C` and off the crosscut is inside both of `J₁, J₂` or inside neither** —
the second half of the "Consequently" of Lemma 2.7. The left side of the splitting identity is
`0`, so the two right-hand terms agree. -/
theorem crosscut_outside_agree {m₁ m₂ : ℕ} (C : ClosedPolygon m) (J₁ : ClosedPolygon m₁)
    (J₂ : ClosedPolygon m₂) {u : Plane} (hu : Plane.IsDirection u)
    (hC : ∀ Q ∈ C.pieces, hgt u Q.1 ≠ hgt u Q.2) {K : List Piece}
    (hK : ∀ Q ∈ K, hgt u Q.1 ≠ hgt u Q.2) (hk : k ≤ m + 3)
    (h₁ : SameEdges J₁.pieces (C.arcPieces a k ++ K))
    (h₂ : SameEdges J₂.pieces (C.arcPieces (a + k) (m + 3 - k) ++ K))
    {x : Plane} (hx : x ∈ outside C.carrier) (hxK : x ∉ cover K) :
    x ∈ inside J₁.carrier ↔ x ∈ inside J₂.carrier := by
  have hJ₁ := h₁.hgt_ne (arcPieces_append_hgt_ne hC hK)
  have hJ₂ := h₂.hgt_ne (arcPieces_append_hgt_ne hC hK)
  have hsum := C.parity_splitting u a hk h₁ h₂ x
  rw [C.parity_eq_zero_of_mem_outside hu hC hx] at hsum
  have harith : ∀ s t : ZMod 2, s + t = 0 → (s = 1 ↔ t = 1) := by decide
  rw [← J₁.parity_eq_one_iff hu hJ₁ (notMem_carrier_of_sameEdges h₁ hx.1 hxK),
    ← J₂.parity_eq_one_iff hu hJ₂ (notMem_carrier_of_sameEdges h₂ hx.1 hxK)]
  exact harith _ _ hsum

end ClosedPolygon

end Schoenflies

end BundlePart412
