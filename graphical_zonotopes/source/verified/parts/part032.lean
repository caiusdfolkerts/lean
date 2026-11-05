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

public import verified.parts.part031
import all verified.parts.part031

@[expose] public section

set_option debug.skipKernelTC false
set_option linter.all false
set_option Elab.async false
set_option internal.cmdlineSnapshots true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

section BundlePart405
/- Source: dev/planar_search/schoenflies_port/Schoenflies/Parity.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/





/-!
# The crossing count of a polygon, and its parity

This is the arithmetic half of the polygonal Jordan curve theorem. A closed polygon is a
list of edges; a point off it gets a number, the count of edges the ray leaving the point
meets; and the whole separation statement follows from the fact that this number changes by
one exactly when the ray's foot sweeps across an edge.

## The frame

The blueprint rotates the coordinate system so that no edge is horizontal. Rotating a curve
is a change of the curve, which would have to be transported back at the end, so instead the
*ray direction* is carried as a parameter. A direction `u` (a unit vector,
`Plane.IsDirection`) fixes an orthonormal frame through

* `fwd u z` — how far along `u` the point `z` lies,
* `hgt u z` — how far across `u` it lies, positive on the counterclockwise side.

"Horizontal" becomes "level for `u`", i.e. `hgt u a = hgt u b`, and
`exists_direction_hgt_ne` — a one-line consequence of `Plane.exists_isDirection_det_ne_zero`
— supplies a `u` for which no edge of a finite list is level. Nothing below needs the
direction to be produced that way: `hgt u P.1 ≠ hgt u P.2` for every piece is carried as a
hypothesis, so no curve is ever moved and nothing has to be transported back.

## The count

An edge is a `Piece`, i.e. its pair of ends, and a polygon is a `List Piece` — the same
representation the overlay uses, so a subdivision produced by `Schoenflies.subdivide` can be
fed straight in. `Crosses u P q` says that the level line through `q` meets `P` strictly
beyond `q`, with the blueprint's half-open convention at the lower end, which is what makes
the count well defined with no genericity assumption. `crossings` counts and `parity`
reduces mod `2`.

Closedness of the polygon enters through `IsClosedChain`: the boundary of the edge list
vanishes mod `2`, stated by duality as "every `ZMod 2`-valued function of the ends sums to
zero over the list". `edgesOf` builds a closed chain from a cyclic vertex list, and
`IsClosedChain` survives `subdivide`.

## Blueprint

* `crossings`, `parity` — the count `π_C` of the section "The polygonal Jordan and crosscut
  theorems".
* `exists_direction_hgt_ne` — the setup of that section: a ray direction level for no edge.
* `crossings_subdivide`, `parity_subdivide` — Lemma 2.1 (subdivision invariance). Proved for
  the *count*, not only its parity, and for the whole `subdivide` operation of
  `Schoenflies.Subdivide`, not only for a single cut.
* `parity_eq_of_mem_ball`, `parity_eq_of_isPreconnected`,
  `parity_eq_of_mem_connectedComponentIn` — the first half of Lemma 2.2 (crossing parity):
  `π_C` is locally constant off the polygon, hence constant on each component of the
  complement.
* `parity_flip` — the second half of Lemma 4.4: the two local sides of an edge have opposite
  parity.
* `parity_eq_zero_of_lt` — `π_C = 0` beyond the polygon in the ray direction; the value on
  the unbounded region.
* `IsClosedChain`, `edgesOf`, `isClosedChain_subdivide` — the closedness hypothesis, its
  supply from a cyclic vertex list, and its survival of subdivision.
-/

open Metric Set

namespace Schoenflies

variable {u a b c p q z w : Plane} {s t : ℝ} {L : List Piece}

/-! ### The frame attached to a direction -/

/-- How far across the direction `u` the point `z` lies. Edges on which this is constant are
the blueprint's horizontal edges. -/
def hgt (u z : Plane) : ℝ := Plane.det u z

/-- How far along the direction `u` the point `z` lies. The ray from `q` is the set of points
of the same `hgt` and larger `fwd`. -/
noncomputable def fwd (u z : Plane) : ℝ := inner ℝ z u

theorem hgt_eq (u z : Plane) : hgt u z = u 0 * z 1 - u 1 * z 0 := rfl

theorem fwd_eq (u z : Plane) : fwd u z = z 0 * u 0 + z 1 * u 1 := Plane.inner_eq z u

namespace Plane

theorem add_apply (x y : Plane) (i : Fin 2) : (x + y) i = x i + y i := rfl

theorem smul_apply (r : ℝ) (x : Plane) (i : Fin 2) : (r • x) i = r * x i := rfl

end Plane

/-- The coordinate rewriting used throughout: every claim about `hgt` and `fwd` of an affine
combination is a polynomial identity in the four coordinates. -/
theorem hgt_lin (u a b : Plane) (t : ℝ) :
    hgt u (a + t • (b - a)) = hgt u a + t * (hgt u b - hgt u a) := by
  simp only [hgt_eq, Plane.add_apply, Plane.smul_apply, Plane.sub_apply]; ring

theorem fwd_lin (u a b : Plane) (t : ℝ) :
    fwd u (a + t • (b - a)) = fwd u a + t * (fwd u b - fwd u a) := by
  simp only [fwd_eq, Plane.add_apply, Plane.smul_apply, Plane.sub_apply]; ring

theorem hgt_sub (u x y : Plane) : hgt u (x - y) = hgt u x - hgt u y := by
  simp only [hgt_eq, Plane.sub_apply]; ring

theorem fwd_sub (u x y : Plane) : fwd u (x - y) = fwd u x - fwd u y := by
  simp only [fwd_eq, Plane.sub_apply]; ring

theorem hgt_add_smul (u v x : Plane) (t : ℝ) :
    hgt u (x + t • v) = hgt u x + t * hgt u v := by
  simp only [hgt_eq, Plane.add_apply, Plane.smul_apply]; ring

theorem fwd_add_smul (u v x : Plane) (t : ℝ) :
    fwd u (x + t • v) = fwd u x + t * fwd u v := by
  simp only [fwd_eq, Plane.add_apply, Plane.smul_apply]; ring

/-- `hgt` against `u` is `fwd` against the turned direction. This is how the two coordinates
of the frame are bounded by the norm. -/
theorem hgt_eq_fwd_perp (u z : Plane) : hgt u z = fwd (Plane.perp u) z := by
  simp only [hgt_eq, fwd_eq, Plane.perp_zero, Plane.perp_one]; ring

section Direction

variable (hu : Plane.IsDirection u)
include hu

theorem norm_sq_one : u 0 ^ 2 + u 1 ^ 2 = 1 := by
  rw [← Plane.norm_sq_eq, hu, one_pow]

omit hu in
@[simp] theorem hgt_self : hgt u u = 0 := by simp only [hgt_eq]; ring

theorem fwd_self : fwd u u = 1 := by rw [fwd_eq, ← norm_sq_one hu]; ring

theorem hgt_perp : hgt u (Plane.perp u) = 1 := by
  rw [hgt_eq, ← norm_sq_one hu]; simp only [Plane.perp_zero, Plane.perp_one]; ring

omit hu in
theorem fwd_perp : fwd u (Plane.perp u) = 0 := by
  simp only [fwd_eq, Plane.perp_zero, Plane.perp_one]; ring

/-- The frame is a basis: every vector is its two coordinates. -/
theorem decomp (v : Plane) : v = fwd u v • u + hgt u v • Plane.perp u := by
  have h1 := norm_sq_one hu
  ext i
  fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one, Plane.add_apply, Plane.smul_apply, Plane.perp_zero,
      Plane.perp_one, hgt_eq, fwd_eq]
  · linear_combination (-(v 0)) * h1
  · linear_combination (-(v 1)) * h1

/-- Two points with the same frame coordinates are equal. -/
theorem eq_of_coords (h1 : fwd u z = fwd u w) (h2 : hgt u z = hgt u w) : z = w := by
  have hz := decomp hu z
  have hw := decomp hu w
  rw [h1, h2] at hz
  exact hz.trans hw.symm

theorem abs_fwd_le_norm (v : Plane) : |fwd u v| ≤ ‖v‖ := by
  have h := abs_real_inner_le_norm v u
  rw [hu, mul_one] at h
  exact h

theorem abs_hgt_le_norm (v : Plane) : |hgt u v| ≤ ‖v‖ := by
  have hp : Plane.IsDirection (Plane.perp u) := by
    rw [Plane.IsDirection, Plane.norm_perp]; exact hu
  rw [hgt_eq_fwd_perp]
  exact abs_fwd_le_norm hp v

end Direction

/-! ### Where an edge meets a level line -/

/-- The point of the line through `a` and `b` at height `t`. Only used when the line is not
level, i.e. `hgt u a ≠ hgt u b`. -/
noncomputable def meet (u a b : Plane) (t : ℝ) : Plane :=
  a + ((t - hgt u a) / (hgt u b - hgt u a)) • (b - a)

theorem hgt_meet (h : hgt u a ≠ hgt u b) (t : ℝ) : hgt u (meet u a b t) = t := by
  have hne : hgt u b - hgt u a ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  rw [meet, hgt_lin]
  field_simp
  ring

theorem fwd_meet (u a b : Plane) (t : ℝ) :
    fwd u (meet u a b t) =
      fwd u a + ((t - hgt u a) / (hgt u b - hgt u a)) * (fwd u b - fwd u a) :=
  fwd_lin u a b _

/-- Below the top and above the bottom, the meeting point is on the edge. -/
theorem meet_mem_segment (h : hgt u a < hgt u b) (h1 : hgt u a ≤ t) (h2 : t ≤ hgt u b) :
    meet u a b t ∈ segment ℝ a b := by
  have hne : (0:ℝ) < hgt u b - hgt u a := by linarith
  rw [segment_eq_image' ℝ a b]
  exact ⟨_, ⟨div_nonneg (by linarith) hne.le, (div_le_one hne).2 (by linarith)⟩, rfl⟩

/-- The meeting point is the only point of the edge at its height. -/
theorem eq_meet (h : hgt u a ≠ hgt u b) (hz : z ∈ segment ℝ a b) :
    z = meet u a b (hgt u z) := by
  have hne : hgt u b - hgt u a ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  rw [segment_eq_image' ℝ a b] at hz
  obtain ⟨r, -, rfl⟩ := hz
  have : (hgt u (a + r • (b - a)) - hgt u a) / (hgt u b - hgt u a) = r := by
    rw [hgt_lin]; field_simp; ring
  rw [meet, this]

/-- Reversing an edge does not move its meeting point. -/
theorem meet_swap (h : hgt u a ≠ hgt u b) (t : ℝ) : meet u b a t = meet u a b t := by
  have hne : hgt u b - hgt u a ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  have h2 : (t - hgt u b) / (hgt u a - hgt u b)
      = 1 - (t - hgt u a) / (hgt u b - hgt u a) := by field_simp; ring
  rw [meet, meet, h2, sub_smul, one_smul, smul_sub, smul_sub]
  abel

/-! ### The crossing count -/

/-- The edge `P` meets the level line through `q` strictly beyond `q`.

The height test is half-open at the bottom: an edge whose lower end is exactly at the height
of `q` counts, one whose upper end is counts not. That convention is what makes the count
well defined at every `q` off the polygon, with no genericity assumption. -/
def Crosses (u : Plane) (P : Piece) (q : Plane) : Prop :=
  min (hgt u P.1) (hgt u P.2) ≤ hgt u q ∧ hgt u q < max (hgt u P.1) (hgt u P.2) ∧
    fwd u q < fwd u (meet u P.1 P.2 (hgt u q))

/-- Crossing is decided classically; the count is a `noncomputable` definition. -/
noncomputable instance decidableCrosses (u : Plane) (P : Piece) (q : Plane) :
    Decidable (Crosses u P q) := Classical.dec _

theorem crosses_swap (h : hgt u a ≠ hgt u b) (q : Plane) :
    Crosses u (b, a) q ↔ Crosses u (a, b) q := by
  simp only [Crosses, meet_swap h, min_comm (hgt u b) (hgt u a), max_comm (hgt u b) (hgt u a)]

/-- How many edges of `L` the ray from `q` crosses. -/
noncomputable def crossings (u : Plane) (L : List Piece) (q : Plane) : ℕ :=
  (L.map (fun P => if Crosses u P q then 1 else 0)).sum

/-- The contribution of one edge to the parity. -/
noncomputable def mark (u : Plane) (P : Piece) (q : Plane) : ZMod 2 :=
  if Crosses u P q then 1 else 0

/-- The crossing parity `π_C(q)`. -/
noncomputable def parity (u : Plane) (L : List Piece) (q : Plane) : ZMod 2 :=
  (L.map (fun P => mark u P q)).sum

@[simp] theorem crossings_nil (u q : Plane) : crossings u [] q = 0 := rfl

@[simp] theorem crossings_cons (u : Plane) (P : Piece) (L : List Piece) (q : Plane) :
    crossings u (P :: L) q = (if Crosses u P q then 1 else 0) + crossings u L q := by
  classical
  simp [crossings]

theorem crossings_append (u : Plane) (L₁ L₂ : List Piece) (q : Plane) :
    crossings u (L₁ ++ L₂) q = crossings u L₁ q + crossings u L₂ q := by
  classical
  simp [crossings, List.sum_append]

@[simp] theorem parity_nil (u q : Plane) : parity u [] q = 0 := rfl

@[simp] theorem parity_cons (u : Plane) (P : Piece) (L : List Piece) (q : Plane) :
    parity u (P :: L) q = mark u P q + parity u L q := by
  simp [parity]

theorem parity_append (u : Plane) (L₁ L₂ : List Piece) (q : Plane) :
    parity u (L₁ ++ L₂) q = parity u L₁ q + parity u L₂ q := by
  simp [parity, List.sum_append]

theorem parity_eq_crossings (u : Plane) (L : List Piece) (q : Plane) :
    parity u L q = (crossings u L q : ZMod 2) := by
  classical
  induction L with
  | nil => simp
  | cons P L ih =>
    rw [parity_cons, ih, crossings_cons, Nat.cast_add, mark]
    split_ifs <;> simp

/-! ### Subdivision invariance -/

/-- A piece with distinct end heights is nondegenerate: this is the hypothesis the
subdivision machinery of `Schoenflies.Subdivide` asks for. -/
theorem nondeg_of_hgt_ne {P : Piece} (h : hgt u P.1 ≠ hgt u P.2) : P.Nondeg := by
  intro hEq
  exact h (by rw [hEq])

/-- An interior point of a non-level edge is strictly between its ends in height. -/
theorem hgt_lt_of_mem_openSegment (hab : hgt u a < hgt u b) (hc : c ∈ openSegment ℝ a b) :
    hgt u a < hgt u c ∧ hgt u c < hgt u b := by
  rw [openSegment_eq_image' ℝ a b] at hc
  obtain ⟨r, ⟨hr0, hr1⟩, rfl⟩ := hc
  rw [hgt_lin]
  constructor
  · nlinarith
  · nlinarith

theorem hgt_ne_of_mem_openSegment (hab : hgt u a ≠ hgt u b) (hc : c ∈ openSegment ℝ a b) :
    hgt u a ≠ hgt u c ∧ hgt u c ≠ hgt u b := by
  rcases lt_or_gt_of_ne hab with h | h
  · obtain ⟨h1, h2⟩ := hgt_lt_of_mem_openSegment h hc
    exact ⟨ne_of_lt h1, ne_of_lt h2⟩
  · obtain ⟨h1, h2⟩ := hgt_lt_of_mem_openSegment h (by rwa [openSegment_symm] at hc)
    exact ⟨ne_of_gt h2, ne_of_gt h1⟩

/-- Cutting an edge keeps both halves non-level. -/
theorem splitAt_hgt_ne {P : Piece} (hP : hgt u P.1 ≠ hgt u P.2) (c : Plane) :
    ∀ Q ∈ splitAt c P, hgt u Q.1 ≠ hgt u Q.2 := by
  classical
  obtain ⟨a, b⟩ := P
  unfold splitAt
  split_ifs with hcc
  · simp only [Piece.interior] at hcc
    obtain ⟨h1, h2⟩ := hgt_ne_of_mem_openSegment hP hcc
    intro Q hQ
    rcases List.mem_cons.1 hQ with rfl | hQ
    · exact h1
    · rcases List.mem_singleton.1 hQ with rfl
      exact h2
  · intro Q hQ
    rcases List.mem_singleton.1 hQ with rfl
    exact hP

theorem splitAllAt_hgt_ne (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2) (c : Plane) :
    ∀ Q ∈ splitAllAt c L, hgt u Q.1 ≠ hgt u Q.2 := by
  intro Q hQ
  obtain ⟨P, hP, hQP⟩ := List.mem_flatMap.1 hQ
  exact splitAt_hgt_ne (hL P hP) c Q hQP

theorem subdivide_hgt_ne (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2) (points : List Plane) :
    ∀ Q ∈ subdivide L points, hgt u Q.1 ≠ hgt u Q.2 := by
  induction points generalizing L with
  | nil => exact hL
  | cons c cs ih => exact ih (splitAllAt_hgt_ne hL c)

/-- The meeting point does not move when the edge is cut: both halves lie on the same line,
and a non-level line meets a level line only once. -/
theorem eq_meet_of_smul (hab : hgt u a ≠ hgt u b) (r : ℝ) (hz : z = a + r • (b - a)) :
    z = meet u a b (hgt u z) := by
  have hne : hgt u b - hgt u a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  have hr : (hgt u z - hgt u a) / (hgt u b - hgt u a) = r := by
    rw [hz, hgt_lin]; field_simp; ring
  rw [meet, hr, hz]

theorem meet_left_eq (hab : hgt u a ≠ hgt u b) (hac : hgt u a ≠ hgt u c)
    {r : ℝ} (hc : c = a + r • (b - a)) (t : ℝ) : meet u a c t = meet u a b t := by
  have hca : c - a = r • (b - a) := by rw [hc]; abel
  have hz : meet u a c t = a + (((t - hgt u a) / (hgt u c - hgt u a)) * r) • (b - a) := by
    rw [meet, hca, smul_smul]
  rw [eq_meet_of_smul hab _ hz, hgt_meet hac]

theorem meet_right_eq (hab : hgt u a ≠ hgt u b) (hcb : hgt u c ≠ hgt u b)
    {r : ℝ} (hc : c = a + r • (b - a)) (t : ℝ) : meet u c b t = meet u a b t := by
  have hbc : b - c = (1 - r) • (b - a) := by rw [hc, sub_smul, one_smul]; abel
  have key : ∀ k : ℝ, c + k • (b - c) = a + (r + k * (1 - r)) • (b - a) := by
    intro k
    rw [hbc, smul_smul, hc, add_smul]
    abel
  have hz : meet u c b t = a + (r + ((t - hgt u c) / (hgt u b - hgt u c)) * (1 - r)) • (b - a) := by
    rw [meet]; exact key _
  rw [eq_meet_of_smul hab _ hz, hgt_meet hcb]

private theorem crossings_split_aux (hab : hgt u a < hgt u b) (hc : c ∈ openSegment ℝ a b)
    (q : Plane) :
    (if Crosses u (a, c) q then 1 else 0) + (if Crosses u (c, b) q then 1 else 0)
      = (if Crosses u (a, b) q then (1 : ℕ) else 0) := by
  obtain ⟨hac, hcb⟩ := hgt_lt_of_mem_openSegment hab hc
  obtain ⟨r, -, hr⟩ := (openSegment_eq_image' ℝ a b).subset hc
  -- the three edges meet the level line through `q` in one and the same point
  have hm1 : meet u a c (hgt u q) = meet u a b (hgt u q) :=
    meet_left_eq (ne_of_lt hab) (ne_of_lt hac) hr.symm _
  have hm2 : meet u c b (hgt u q) = meet u a b (hgt u q) :=
    meet_right_eq (ne_of_lt hab) (ne_of_lt hcb) hr.symm _
  simp only [Crosses, hm1, hm2, min_eq_left hab.le, max_eq_right hab.le,
    min_eq_left hac.le, max_eq_right hac.le, min_eq_left hcb.le, max_eq_right hcb.le]
  by_cases hD : fwd u q < fwd u (meet u a b (hgt u q))
  · by_cases h1 : hgt u a ≤ hgt u q
    · by_cases h2 : hgt u q < hgt u c
      · rw [if_pos ⟨h1, h2, hD⟩, if_neg (by rintro ⟨g, -, -⟩; linarith),
          if_pos ⟨h1, by linarith, hD⟩]
      · push Not at h2
        by_cases h3 : hgt u q < hgt u b
        · rw [if_neg (by rintro ⟨-, g, -⟩; linarith), if_pos ⟨h2, h3, hD⟩,
            if_pos ⟨h1, h3, hD⟩]
        · rw [if_neg (by rintro ⟨-, g, -⟩; linarith), if_neg (by rintro ⟨-, g, -⟩; linarith),
            if_neg (by rintro ⟨-, g, -⟩; linarith)]
    · push Not at h1
      rw [if_neg (by rintro ⟨g, -, -⟩; linarith), if_neg (by rintro ⟨g, -, -⟩; linarith),
        if_neg (by rintro ⟨g, -, -⟩; linarith)]
  · rw [if_neg (by rintro ⟨-, -, g⟩; exact hD g), if_neg (by rintro ⟨-, -, g⟩; exact hD g),
      if_neg (by rintro ⟨-, -, g⟩; exact hD g)]

private theorem crossings_split (hab : hgt u a ≠ hgt u b) (hc : c ∈ openSegment ℝ a b)
    (q : Plane) :
    (if Crosses u (a, c) q then 1 else 0) + (if Crosses u (c, b) q then 1 else 0)
      = (if Crosses u (a, b) q then (1 : ℕ) else 0) := by
  obtain ⟨hac, hcb⟩ := hgt_ne_of_mem_openSegment hab hc
  rcases lt_or_gt_of_ne hab with h | h
  · exact crossings_split_aux h hc q
  · have hc' : c ∈ openSegment ℝ b a := by rwa [openSegment_symm]
    have key := crossings_split_aux h hc' q
    simp only [crosses_swap hcb, crosses_swap hac, crosses_swap hab] at key
    rw [add_comm]
    exact key

/-- Cutting one edge does not change the crossing count. -/
theorem crossings_splitAt {P : Piece} (hP : hgt u P.1 ≠ hgt u P.2) (c q : Plane) :
    crossings u (splitAt c P) q = crossings u [P] q := by
  classical
  obtain ⟨a, b⟩ := P
  unfold splitAt
  split_ifs with hcc
  · simp only [Piece.interior] at hcc
    simp only [crossings_cons, crossings_nil, add_zero]
    exact crossings_split hP hcc q
  · rfl

/-- Cutting the whole list at one point does not change the crossing count. -/
theorem crossings_splitAllAt (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2) (c q : Plane) :
    crossings u (splitAllAt c L) q = crossings u L q := by
  induction L with
  | nil => rfl
  | cons P L ih =>
    have hP : hgt u P.1 ≠ hgt u P.2 := hL P (by simp)
    have hL' : ∀ Q ∈ L, hgt u Q.1 ≠ hgt u Q.2 := fun Q hQ => hL Q (by simp [hQ])
    rw [splitAllAt, List.flatMap_cons, crossings_append, ← splitAllAt, ih hL',
      crossings_splitAt hP c q, crossings_cons, crossings_cons, crossings_nil, add_zero]

/-- **Subdivision invariance** (Lemma 2.1). Subdividing changes no crossing count — not even
its parity is needed here; the count itself is unchanged. -/
theorem crossings_subdivide (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2) (points : List Plane)
    (q : Plane) : crossings u (subdivide L points) q = crossings u L q := by
  induction points generalizing L with
  | nil => rfl
  | cons c cs ih =>
    rw [subdivide_cons, ih (splitAllAt_hgt_ne hL c), crossings_splitAllAt hL c q]

/-- **Subdivision invariance**, in the form the crosscut theorem uses. -/
theorem parity_subdivide (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2) (points : List Plane)
    (q : Plane) : parity u (subdivide L points) q = parity u L q := by
  rw [parity_eq_crossings, parity_eq_crossings, crossings_subdivide hL]

/-! ### Closed chains -/

theorem sum_map_add {α : Type*} (l : List α) (F G : α → ZMod 2) :
    (l.map (fun x => F x + G x)).sum = (l.map F).sum + (l.map G).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem sum_map_flatMap {α β : Type*} (l : List α) (g : α → List β) (F : β → ZMod 2) :
    ((l.flatMap g).map F).sum = (l.map (fun x => ((g x).map F).sum)).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.flatMap_cons, List.map_append, List.sum_append, ih,
      List.map_cons, List.sum_cons]

theorem add_self_zmod_two (x : ZMod 2) : x + x = 0 := by
  revert x; decide

/-- The edge list is a **closed chain**: its boundary vanishes mod `2`. Stated by duality —
every `ZMod 2`-valued function of the ends sums to zero over the list — which is exactly what
the parity argument consumes, and which `isClosedChain_edgesOf` supplies for a cyclic vertex
list. -/
def IsClosedChain (L : List Piece) : Prop :=
  ∀ f : Plane → ZMod 2, (L.map (fun P => f P.1 + f P.2)).sum = 0

theorem isClosedChain_nil : IsClosedChain [] := fun _ => by simp

/-- The closed edge list of a cyclic vertex list: `[v₀v₁, v₁v₂, …, v_{n-1}v₀]`. -/
def edgesOf (vs : List Plane) : List Piece := vs.zip (vs.rotate 1)

theorem isClosedChain_edgesOf (vs : List Plane) : IsClosedChain (edgesOf vs) := by
  intro f
  have h1 : (edgesOf vs).map Prod.fst = vs :=
    List.map_fst_zip (by simp)
  have h2 : (edgesOf vs).map Prod.snd = vs.rotate 1 :=
    List.map_snd_zip (by simp)
  have e1 : ((edgesOf vs).map (fun P => f P.1)).sum = (vs.map f).sum := by
    calc ((edgesOf vs).map (fun P => f P.1)).sum
        = (((edgesOf vs).map Prod.fst).map f).sum := by rw [List.map_map]; rfl
      _ = (vs.map f).sum := by rw [h1]
  have e2 : ((edgesOf vs).map (fun P => f P.2)).sum = ((vs.rotate 1).map f).sum := by
    calc ((edgesOf vs).map (fun P => f P.2)).sum
        = (((edgesOf vs).map Prod.snd).map f).sum := by rw [List.map_map]; rfl
      _ = ((vs.rotate 1).map f).sum := by rw [h2]
  have e3 : ((vs.rotate 1).map f).sum = (vs.map f).sum :=
    List.Perm.sum_eq (List.Perm.map f (vs.rotate_perm 1))
  rw [sum_map_add, e1, e2, e3]
  exact add_self_zmod_two _

/-- Cutting an edge in two does not disturb the boundary: the cut point is added twice. -/
theorem isClosedChain_splitAllAt (h : IsClosedChain L) (c : Plane) :
    IsClosedChain (splitAllAt c L) := by
  classical
  intro f
  have step : ∀ P : Piece, (((splitAt c P).map (fun Q => f Q.1 + f Q.2)).sum) = f P.1 + f P.2 := by
    intro P
    obtain ⟨a, b⟩ := P
    unfold splitAt
    split_ifs
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      linear_combination add_self_zmod_two (f c)
    · simp
  rw [splitAllAt, sum_map_flatMap, List.map_congr_left (fun P _ => step P)]
  exact h f

theorem isClosedChain_subdivide (h : IsClosedChain L) (points : List Plane) :
    IsClosedChain (subdivide L points) := by
  induction points generalizing L with
  | nil => exact h
  | cons c cs ih => exact ih (isClosedChain_splitAllAt h c)

/-! ### What a list of edges occupies -/

theorem mem_cover {P : Piece} (hP : P ∈ L) (hz : z ∈ P.seg) : z ∈ cover L :=
  Set.mem_biUnion hP hz

theorem isCompact_cover (L : List Piece) : IsCompact (cover L) := by
  induction L with
  | nil => rw [cover_nil]; exact isCompact_empty
  | cons P L ih => rw [cover_cons]; exact (isCompact_segment P.1 P.2).union ih

theorem isClosed_cover (L : List Piece) : IsClosed (cover L) := (isCompact_cover L).isClosed

/-- Where an edge meets the level line, when it does. -/
theorem meet_mem_seg {P : Piece} (h : hgt u P.1 ≠ hgt u P.2)
    (h1 : min (hgt u P.1) (hgt u P.2) ≤ t) (h2 : t ≤ max (hgt u P.1) (hgt u P.2)) :
    meet u P.1 P.2 t ∈ P.seg := by
  rcases lt_or_gt_of_ne h with hlt | hlt
  · rw [min_eq_left hlt.le] at h1
    rw [max_eq_right hlt.le] at h2
    exact meet_mem_segment hlt h1 h2
  · rw [min_eq_right hlt.le] at h1
    rw [max_eq_left hlt.le] at h2
    have hmem := meet_mem_segment hlt h1 h2
    rwa [meet_swap h, segment_symm] at hmem

/-! ### Moving the base point -/

section Moves

variable (hu : Plane.IsDirection u)
include hu

omit hu in
theorem hgt_along (q : Plane) (s : ℝ) : hgt u (q + s • u) = hgt u q := by
  rw [hgt_add_smul, hgt_self]; ring

theorem fwd_along (q : Plane) (s : ℝ) : fwd u (q + s • u) = fwd u q + s := by
  rw [fwd_add_smul, fwd_self hu]; ring

theorem hgt_across (q : Plane) (s : ℝ) : hgt u (q + s • Plane.perp u) = hgt u q + s := by
  rw [hgt_add_smul, hgt_perp hu]; ring

omit hu in
theorem fwd_across (q : Plane) (s : ℝ) : fwd u (q + s • Plane.perp u) = fwd u q := by
  rw [fwd_add_smul, fwd_perp]; ring

/-- The segment from `q` in the ray direction is exactly the points at the same height with
`fwd` in between. -/
theorem mem_segment_along {q y : Plane} {s : ℝ} (hs : 0 ≤ s) (h1 : hgt u y = hgt u q)
    (h2 : fwd u q ≤ fwd u y) (h3 : fwd u y ≤ fwd u q + s) :
    y ∈ segment ℝ q (q + s • u) := by
  rcases eq_or_lt_of_le hs with rfl | hspos
  · have hy : y = q := eq_of_coords hu (by linarith) h1
    rw [hy, zero_smul, add_zero]
    exact left_mem_segment ℝ q q
  · rw [segment_eq_image' ℝ q (q + s • u)]
    refine ⟨(fwd u y - fwd u q) / s,
      ⟨div_nonneg (by linarith) hs, (div_le_one hspos).2 (by linarith)⟩, ?_⟩
    simp only []
    have hsub : q + s • u - q = s • u := by abel
    rw [hsub, smul_smul, div_mul_cancel₀ _ (ne_of_gt hspos)]
    exact eq_of_coords hu (by rw [fwd_add_smul, fwd_self hu]; ring)
      (by rw [hgt_add_smul, hgt_self, h1]; ring)

/-- The segment from `q` across the ray direction is exactly the points with the same `fwd`
and height in between. -/
theorem mem_segment_across {q y : Plane} {s : ℝ} (hs : 0 ≤ s) (h1 : fwd u y = fwd u q)
    (h2 : hgt u q ≤ hgt u y) (h3 : hgt u y ≤ hgt u q + s) :
    y ∈ segment ℝ q (q + s • Plane.perp u) := by
  rcases eq_or_lt_of_le hs with rfl | hspos
  · have hy : y = q := eq_of_coords hu h1 (by linarith)
    rw [hy, zero_smul, add_zero]
    exact left_mem_segment ℝ q q
  · rw [segment_eq_image' ℝ q (q + s • Plane.perp u)]
    refine ⟨(hgt u y - hgt u q) / s,
      ⟨div_nonneg (by linarith) hs, (div_le_one hspos).2 (by linarith)⟩, ?_⟩
    simp only []
    have hsub : q + s • Plane.perp u - q = s • Plane.perp u := by abel
    rw [hsub, smul_smul, div_mul_cancel₀ _ (ne_of_gt hspos)]
    exact eq_of_coords hu (by rw [fwd_add_smul, fwd_perp, h1]; ring)
      (by rw [hgt_add_smul, hgt_perp hu]; ring)

omit hu in
/-- A connected piece of an edge that stays between two heights and never meets the level
line `fwd = ξ` stays on one side of it. -/
theorem side_const {lo hi ξ : ℝ}
    (hmiss : ∀ y ∈ segment ℝ a b, fwd u y = ξ → lo ≤ hgt u y → hgt u y ≤ hi → False)
    (hz : z ∈ segment ℝ a b) (hw : w ∈ segment ℝ a b)
    (hzl : lo ≤ hgt u z) (hzh : hgt u z ≤ hi) (hwl : lo ≤ hgt u w) (hwh : hgt u w ≤ hi) :
    (ξ < fwd u z ↔ ξ < fwd u w) := by
  have key : ∀ z w : Plane, z ∈ segment ℝ a b → w ∈ segment ℝ a b →
      lo ≤ hgt u z → hgt u z ≤ hi → lo ≤ hgt u w → hgt u w ≤ hi →
      ξ < fwd u z → ξ < fwd u w := by
    intro z w hz hw hzl hzh hwl hwh hlt
    by_contra hcon
    push Not at hcon
    have hpos : 0 < fwd u z - fwd u w := by linarith
    set r := (fwd u z - ξ) / (fwd u z - fwd u w) with hr
    have hr0 : 0 ≤ r := div_nonneg (by linarith) hpos.le
    have hr1 : r ≤ 1 := (div_le_one hpos).2 (by linarith)
    have hy : z + r • (w - z) ∈ segment ℝ a b :=
      (convex_segment a b).segment_subset hz hw
        (by rw [segment_eq_image' ℝ z w]; exact ⟨r, ⟨hr0, hr1⟩, rfl⟩)
    refine hmiss _ hy ?_ ?_ ?_
    · rw [fwd_lin, hr]; field_simp; ring
    · rw [hgt_lin]
      linarith [mul_nonneg hr0 (sub_nonneg.2 hwl), mul_nonneg (sub_nonneg.2 hr1) (sub_nonneg.2 hzl)]
    · rw [hgt_lin]
      linarith [mul_nonneg hr0 (sub_nonneg.2 hwh), mul_nonneg (sub_nonneg.2 hr1) (sub_nonneg.2 hzh)]
  exact ⟨fun h => key z w hz hw hzl hzh hwl hwh h, fun h => key w z hw hz hwl hwh hzl hzh h⟩

/-- Moving the base point along the ray direction, without meeting the polygon, changes no
crossing. -/
theorem parity_move_along (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2) {q : Plane} {s : ℝ}
    (hs : 0 ≤ s) (hmiss : ∀ y ∈ segment ℝ q (q + s • u), y ∉ cover L) :
    parity u L (q + s • u) = parity u L q := by
  refine congrArg List.sum (List.map_congr_left ?_)
  intro P hP
  have hPne := hL P hP
  have hiff : Crosses u P (q + s • u) ↔ Crosses u P q := by
    simp only [Crosses, hgt_along, fwd_along hu]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, by linarith⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, ?_⟩
      by_contra hcon
      push Not at hcon
      exact hmiss _ (mem_segment_along hu hs (hgt_meet hPne _) h3.le hcon)
        (mem_cover hP (meet_mem_seg hPne h1 h2.le))
  simp only [mark, hiff]

end Moves

/-! ### Sweeping across the ray direction -/

/-- The marker attached to a vertex when the base point is swept across by `s`: the vertex
counts when its height lies in the half-open band swept out and it lies beyond the base
point. Summed over both ends of every edge this vanishes, because the polygon is closed;
that is the whole content of crossing parity. -/
noncomputable def fmark (u q : Plane) (s : ℝ) (v : Plane) : ZMod 2 :=
  if hgt u q < hgt u v ∧ hgt u v ≤ hgt u q + s ∧ fwd u q < fwd u v then 1 else 0

theorem mark_swap (h : hgt u a ≠ hgt u b) (q : Plane) : mark u (b, a) q = mark u (a, b) q := by
  simp only [mark, crosses_swap h]

section Across

variable (hu : Plane.IsDirection u)
include hu

/-- One edge, swept across. The crossings gained or lost are exactly the ends whose heights
the sweep passes, on the far side of the base point. -/
private theorem mark_step {q : Plane} {s : ℝ} (hs : 0 ≤ s) (hab : hgt u a < hgt u b)
    (hmiss : ∀ y ∈ segment ℝ a b, fwd u y = fwd u q → hgt u q ≤ hgt u y →
      hgt u y ≤ hgt u q + s → False) :
    mark u (a, b) q + mark u (a, b) (q + s • Plane.perp u)
      = fmark u q s a + fmark u q s b := by
  have hne : hgt u a ≠ hgt u b := ne_of_lt hab
  have hha : ∀ t : ℝ, hgt u (meet u a b t) = t := fun t => hgt_meet hne t
  have hma : ∀ t : ℝ, hgt u a ≤ t → t ≤ hgt u b → meet u a b t ∈ segment ℝ a b :=
    fun t h1 h2 => meet_mem_segment hab h1 h2
  have haseg : a ∈ segment ℝ a b := left_mem_segment ℝ a b
  have hbseg : b ∈ segment ℝ a b := right_mem_segment ℝ a b
  have hside : ∀ z, z ∈ segment ℝ a b → ∀ w, w ∈ segment ℝ a b →
      hgt u q ≤ hgt u z → hgt u z ≤ hgt u q + s →
      hgt u q ≤ hgt u w → hgt u w ≤ hgt u q + s →
      (fwd u q < fwd u z ↔ fwd u q < fwd u w) :=
    fun z hz w hw h1 h2 h3 h4 => side_const hmiss hz hw h1 h2 h3 h4
  simp only [mark, fmark, Crosses, min_eq_left hab.le, max_eq_right hab.le,
    hgt_across hu, fwd_across]
  rcases le_or_gt (hgt u a) (hgt u q) with hA | hA
  · rcases lt_or_ge (hgt u q + s) (hgt u b) with hB | hB
    · -- the sweep stays strictly below the upper end: no end is passed
      have e := hside (meet u a b (hgt u q)) (hma _ hA (by linarith))
        (meet u a b (hgt u q + s)) (hma _ (by linarith) hB.le)
        (hha _).ge (by rw [hha]; linarith) (by rw [hha]; linarith) (hha _).le
      by_cases hD : fwd u q < fwd u (meet u a b (hgt u q))
      · rw [if_pos ⟨hA, by linarith, hD⟩, if_pos ⟨by linarith, hB, e.1 hD⟩,
          if_neg (by rintro ⟨g, -, -⟩; linarith), if_neg (by rintro ⟨-, g, -⟩; linarith)]
        decide
      · rw [if_neg (by rintro ⟨-, -, g⟩; exact hD g),
          if_neg (by rintro ⟨-, -, g⟩; exact hD (e.2 g)),
          if_neg (by rintro ⟨g, -, -⟩; linarith), if_neg (by rintro ⟨-, g, -⟩; linarith)]
    · rcases lt_or_ge (hgt u q) (hgt u b) with hB2 | hB2
      · -- the sweep passes the upper end
        have e := hside (meet u a b (hgt u q)) (hma _ hA hB2.le) b hbseg
          (hha _).ge (by rw [hha]; linarith) (by linarith) hB
        by_cases hD : fwd u q < fwd u (meet u a b (hgt u q))
        · rw [if_pos ⟨hA, hB2, hD⟩, if_neg (by rintro ⟨-, g, -⟩; linarith),
            if_neg (by rintro ⟨g, -, -⟩; linarith), if_pos ⟨hB2, hB, e.1 hD⟩]
          decide
        · rw [if_neg (by rintro ⟨-, -, g⟩; exact hD g),
            if_neg (by rintro ⟨-, g, -⟩; linarith),
            if_neg (by rintro ⟨g, -, -⟩; linarith),
            if_neg (by rintro ⟨-, -, g⟩; exact hD (e.2 g))]
      · -- the edge is entirely below the sweep
        rw [if_neg (by rintro ⟨-, g, -⟩; linarith), if_neg (by rintro ⟨-, g, -⟩; linarith),
          if_neg (by rintro ⟨g, -, -⟩; linarith), if_neg (by rintro ⟨g, -, -⟩; linarith)]
  · rcases le_or_gt (hgt u a) (hgt u q + s) with hA2 | hA2
    · rcases lt_or_ge (hgt u q + s) (hgt u b) with hB | hB
      · -- the sweep passes the lower end only
        have e := hside (meet u a b (hgt u q + s)) (hma _ hA2 hB.le) a haseg
          (by rw [hha]; linarith) (hha _).le (by linarith) hA2
        by_cases hD : fwd u q < fwd u a
        · rw [if_neg (by rintro ⟨g, -, -⟩; linarith), if_pos ⟨hA2, hB, e.2 hD⟩,
            if_pos ⟨hA, hA2, hD⟩, if_neg (by rintro ⟨-, g, -⟩; linarith)]
          decide
        · rw [if_neg (by rintro ⟨g, -, -⟩; linarith),
            if_neg (by rintro ⟨-, -, g⟩; exact hD (e.1 g)),
            if_neg (by rintro ⟨-, -, g⟩; exact hD g),
            if_neg (by rintro ⟨-, g, -⟩; linarith)]
      · -- the sweep passes both ends
        have e := hside a haseg b hbseg (by linarith) hA2 (by linarith) hB
        by_cases hD : fwd u q < fwd u a
        · rw [if_neg (by rintro ⟨g, -, -⟩; linarith), if_neg (by rintro ⟨-, g, -⟩; linarith),
            if_pos ⟨hA, hA2, hD⟩, if_pos ⟨by linarith, hB, e.1 hD⟩]
          decide
        · rw [if_neg (by rintro ⟨g, -, -⟩; linarith), if_neg (by rintro ⟨-, g, -⟩; linarith),
            if_neg (by rintro ⟨-, -, g⟩; exact hD g),
            if_neg (by rintro ⟨-, -, g⟩; exact hD (e.2 g))]
    · -- the edge is entirely above the sweep
      rw [if_neg (by rintro ⟨g, -, -⟩; linarith), if_neg (by rintro ⟨g, -, -⟩; linarith),
        if_neg (by rintro ⟨-, g, -⟩; linarith), if_neg (by rintro ⟨-, g, -⟩; linarith)]

/-- Sweeping the base point across the ray direction, without meeting the polygon, does not
change the parity. This is where the polygon has to be closed. -/
theorem parity_move_across (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2) (hC : IsClosedChain L)
    {q : Plane} {s : ℝ} (hs : 0 ≤ s)
    (hmiss : ∀ y ∈ segment ℝ q (q + s • Plane.perp u), y ∉ cover L) :
    parity u L (q + s • Plane.perp u) = parity u L q := by
  have key : ∀ P ∈ L, mark u P q + mark u P (q + s • Plane.perp u)
      = fmark u q s P.1 + fmark u q s P.2 := by
    intro P hP
    obtain ⟨a, b⟩ := P
    have hne := hL (a, b) hP
    have hmiss' : ∀ y ∈ segment ℝ a b, fwd u y = fwd u q → hgt u q ≤ hgt u y →
        hgt u y ≤ hgt u q + s → False := fun y hy h1 h2 h3 =>
      hmiss y (mem_segment_across hu hs h1 h2 h3) (mem_cover hP hy)
    rcases lt_or_gt_of_ne hne with h | h
    · exact mark_step hu hs h hmiss'
    · have hmiss'' : ∀ y ∈ segment ℝ b a, fwd u y = fwd u q → hgt u q ≤ hgt u y →
          hgt u y ≤ hgt u q + s → False := by
        intro y hy
        exact hmiss' y (by rwa [segment_symm] at hy)
      have hstep := mark_step hu hs h hmiss''
      rw [mark_swap hne, mark_swap hne] at hstep
      rw [hstep]
      exact add_comm _ _
  have hzero : parity u L q + parity u L (q + s • Plane.perp u) = 0 := by
    rw [parity, parity, ← sum_map_add, List.map_congr_left key]
    exact hC (fun v => fmark u q s v)
  have harith : ∀ x y : ZMod 2, x + y = 0 → y = x := by decide
  exact harith _ _ hzero

/-- The two moves, for a shift of either sign. -/
theorem parity_move_along' (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2) {q q' : Plane} (s : ℝ)
    (hq' : q' = q + s • u) (hmiss : ∀ y ∈ segment ℝ q q', y ∉ cover L) :
    parity u L q' = parity u L q := by
  rcases le_or_gt 0 s with hs | hs
  · subst hq'; exact parity_move_along hu hL hs hmiss
  · have hq : q = q' + (-s) • u := by rw [hq', neg_smul, add_neg_cancel_right]
    have hmiss' : ∀ y ∈ segment ℝ q' (q' + (-s) • u), y ∉ cover L := by
      intro y hy
      rw [← hq] at hy
      exact hmiss y (by rwa [segment_symm] at hy)
    have hmove := parity_move_along hu hL (by linarith : (0:ℝ) ≤ -s) hmiss'
    rw [← hq] at hmove
    exact hmove.symm

theorem parity_move_across' (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2) (hC : IsClosedChain L)
    {q q' : Plane} (s : ℝ) (hq' : q' = q + s • Plane.perp u)
    (hmiss : ∀ y ∈ segment ℝ q q', y ∉ cover L) :
    parity u L q' = parity u L q := by
  rcases le_or_gt 0 s with hs | hs
  · subst hq'; exact parity_move_across hu hL hC hs hmiss
  · have hq : q = q' + (-s) • Plane.perp u := by rw [hq', neg_smul, add_neg_cancel_right]
    have hmiss' : ∀ y ∈ segment ℝ q' (q' + (-s) • Plane.perp u), y ∉ cover L := by
      intro y hy
      rw [← hq] at hy
      exact hmiss y (by rwa [segment_symm] at hy)
    have hmove := parity_move_across hu hL hC (by linarith : (0:ℝ) ≤ -s) hmiss'
    rw [← hq] at hmove
    exact hmove.symm

end Across

/-! ### Crossing parity -/

theorem exists_ball_avoiding {z : Plane} (h : z ∉ cover L) :
    ∃ ε > 0, ∀ y ∈ ball z ε, y ∉ cover L := by
  have hopen := (isClosed_cover L).isOpen_compl
  rw [Metric.isOpen_iff] at hopen
  obtain ⟨ε, hε, hsub⟩ := hopen z h
  exact ⟨ε, hε, fun y hy => hsub hy⟩

section Constancy

variable (hu : Plane.IsDirection u)
include hu

/-- The parity is constant on a ball that misses the polygon: reach any nearby point by a
move along the ray direction followed by a move across it. -/
theorem parity_eq_of_mem_ball (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2) (hC : IsClosedChain L)
    {q q' : Plane} {ε : ℝ} (hq' : q' ∈ ball q ε) (hmiss : ∀ y ∈ ball q ε, y ∉ cover L) :
    parity u L q' = parity u L q := by
  have hεpos : 0 < ε := lt_of_le_of_lt dist_nonneg (mem_ball.1 hq')
  have hqb : q ∈ ball q ε := mem_ball_self hεpos
  obtain ⟨w, hw⟩ : ∃ w : Plane, w = q + (fwd u (q' - q)) • u := ⟨_, rfl⟩
  have hwball : w ∈ ball q ε := by
    have hsub : q + (fwd u (q' - q)) • u - q = (fwd u (q' - q)) • u := by abel
    rw [mem_ball, dist_eq_norm, hw, hsub, norm_smul, Real.norm_eq_abs, hu, mul_one]
    calc |fwd u (q' - q)| ≤ ‖q' - q‖ := abs_fwd_le_norm hu _
      _ = dist q' q := (dist_eq_norm q' q).symm
      _ < ε := mem_ball.1 hq'
  have hq'w : q' = w + (hgt u (q' - q)) • Plane.perp u := by
    have hd := decomp hu (q' - q)
    rw [hw, add_assoc, ← hd]
    abel
  have h1 : parity u L w = parity u L q :=
    parity_move_along' hu hL _ hw
      (fun y hy => hmiss y ((convex_ball q ε).segment_subset hqb hwball hy))
  have h2 : parity u L q' = parity u L w :=
    parity_move_across' hu hL hC _ hq'w
      (fun y hy => hmiss y ((convex_ball q ε).segment_subset hwball hq' hy))
  rw [h2, h1]

/-- **Crossing parity** (Lemma 2.2). `π_C` is constant on every preconnected subset of the
complement of the polygon — in particular on every component. -/
theorem parity_eq_of_isPreconnected (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2)
    (hC : IsClosedChain L) {S : Set Plane} (hS : IsPreconnected S)
    (hSC : ∀ z ∈ S, z ∉ cover L) {x y : Plane} (hx : x ∈ S) (hy : y ∈ S) :
    parity u L x = parity u L y := by
  by_contra hne
  have hopen : ∀ c : ZMod 2, IsOpen {z : Plane | z ∉ cover L ∧ parity u L z = c} := by
    intro c
    rw [Metric.isOpen_iff]
    rintro z ⟨hz1, hz2⟩
    obtain ⟨ε, hε, hball⟩ := exists_ball_avoiding hz1
    exact ⟨ε, hε, fun t ht => ⟨hball t ht,
      by rw [parity_eq_of_mem_ball hu hL hC ht hball, hz2]⟩⟩
  have htwo : ∀ e : ZMod 2, e = parity u L x ∨ e = parity u L y := by
    revert hne
    generalize parity u L x = c
    generalize parity u L y = d
    revert c d
    decide
  obtain ⟨z, -, hzA, hzB⟩ :=
    hS _ _ (hopen (parity u L x)) (hopen (parity u L y))
      (fun t ht => (htwo (parity u L t)).imp (fun h => ⟨hSC t ht, h⟩) (fun h => ⟨hSC t ht, h⟩))
      ⟨x, hx, hSC x hx, rfl⟩ ⟨y, hy, hSC y hy, rfl⟩
  exact hne (hzA.2 ▸ hzB.2)

/-- The parity is constant on the component of the complement containing a point. -/
theorem parity_eq_of_mem_connectedComponentIn (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2)
    (hC : IsClosedChain L) {x y : Plane} (hx : x ∉ cover L)
    (hy : y ∈ connectedComponentIn (cover L)ᶜ x) : parity u L y = parity u L x :=
  parity_eq_of_isPreconnected hu hL hC isPreconnected_connectedComponentIn
    (fun _ ht => connectedComponentIn_subset _ _ ht) hy (mem_connectedComponentIn hx)

end Constancy

/-! ### The value far along the ray, and the jump across an edge -/

/-- Beyond the polygon in the ray direction the count is zero. -/
theorem parity_eq_zero_of_lt (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2) {q : Plane}
    (h : ∀ z ∈ cover L, fwd u z < fwd u q) : parity u L q = 0 := by
  refine List.sum_eq_zero ?_
  intro x hx
  obtain ⟨P, hP, rfl⟩ := List.mem_map.1 hx
  refine if_neg ?_
  rintro ⟨h1, h2, h3⟩
  exact absurd (h _ (mem_cover hP (meet_mem_seg (hL P hP) h1 h2.le))) (not_lt.2 h3.le)

section Flip

variable (hu : Plane.IsDirection u)
include hu

/-- **Opposite sides of an edge** (Lemma 2.2, second half). At an interior point `p` of one
edge of the list which no other edge of the list passes through, the two points just before
and just after `p` in the ray direction lie off the polygon and have opposite parity: the
count changes by one as the base point sweeps across the edge. -/
theorem parity_flip {L₁ L₂ : List Piece} {a b p : Plane}
    (hL : ∀ P ∈ L₁ ++ (a, b) :: L₂, hgt u P.1 ≠ hgt u P.2)
    (hp : p ∈ openSegment ℝ a b) (h1 : p ∉ cover L₁) (h2 : p ∉ cover L₂) :
    ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ →
      p - t • u ∉ cover (L₁ ++ (a, b) :: L₂) ∧
      p + t • u ∉ cover (L₁ ++ (a, b) :: L₂) ∧
      parity u (L₁ ++ (a, b) :: L₂) (p - t • u)
        = parity u (L₁ ++ (a, b) :: L₂) (p + t • u) + 1 := by
  have hab : hgt u a ≠ hgt u b := hL (a, b) (by simp)
  have hpK : p ∉ cover (L₁ ++ L₂) := by
    rw [cover_append]
    rintro (h | h)
    · exact h1 h
    · exact h2 h
  obtain ⟨ε, hε, hball⟩ := exists_ball_avoiding hpK
  refine ⟨ε, hε, fun t ht htε => ?_⟩
  -- the two test points and their frame coordinates
  have hneg : p - t • u = p + (-t) • u := by rw [neg_smul]; abel
  have hgm : hgt u (p - t • u) = hgt u p := by rw [hneg, hgt_along]
  have hgp : hgt u (p + t • u) = hgt u p := hgt_along p t
  have hfm : fwd u (p - t • u) = fwd u p - t := by rw [hneg, fwd_along hu]; ring
  have hfp : fwd u (p + t • u) = fwd u p + t := fwd_along hu p t
  have hdist : ∀ r : ℝ, |r| < ε → p + r • u ∈ ball p ε := by
    intro r hr
    have hsub : p + r • u - p = r • u := by abel
    rw [mem_ball, dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, hu, mul_one]
    exact hr
  have habsm : |(-t)| < ε := by rw [abs_neg, abs_of_pos ht]; exact htε
  have habsp : |t| < ε := by rw [abs_of_pos ht]; exact htε
  -- the only point of the edge at the height of `p` is `p` itself
  have hpseg : p ∈ segment ℝ a b := openSegment_subset_segment ℝ a b hp
  have hmeetp : meet u a b (hgt u p) = p := (eq_meet hab hpseg).symm
  have hnotseg : ∀ r : ℝ, r ≠ 0 → p + r • u ∉ segment ℝ a b := by
    intro r hr hmem
    have heq : p + r • u = p := by
      rw [eq_meet hab hmem, hgt_along, hmeetp]
    have hf : fwd u (p + r • u) = fwd u p + r := fwd_along hu p r
    rw [heq] at hf
    exact hr (by linarith)
  have hcov : ∀ r : ℝ, r ≠ 0 → |r| < ε → p + r • u ∉ cover (L₁ ++ (a, b) :: L₂) := by
    intro r hr hrε hmem
    rw [cover_append, cover_cons] at hmem
    rcases hmem with h | h | h
    · exact hball _ (hdist r hrε) (by rw [cover_append]; exact Or.inl h)
    · exact hnotseg r hr h
    · exact hball _ (hdist r hrε) (by rw [cover_append]; exact Or.inr h)
  -- an edge other than `(a, b)` meets the level line far from `p`, so it is not affected
  have hfar : ∀ P ∈ L₁ ++ L₂, hgt u P.1 ≠ hgt u P.2 →
      min (hgt u P.1) (hgt u P.2) ≤ hgt u p → hgt u p ≤ max (hgt u P.1) (hgt u P.2) →
      ε ≤ |fwd u (meet u P.1 P.2 (hgt u p)) - fwd u p| := by
    intro P hP hPne g1 g2
    have hmcov : meet u P.1 P.2 (hgt u p) ∈ cover (L₁ ++ L₂) :=
      mem_cover hP (meet_mem_seg hPne g1 g2)
    have hmnb : ¬ (dist (meet u P.1 P.2 (hgt u p)) p < ε) := fun h =>
      hball _ (mem_ball.2 h) hmcov
    push Not at hmnb
    rw [dist_eq_norm] at hmnb
    have hh : hgt u (meet u P.1 P.2 (hgt u p) - p) = 0 := by
      rw [hgt_sub, hgt_meet hPne]; ring
    have hd := decomp hu (meet u P.1 P.2 (hgt u p) - p)
    rw [hh, zero_smul, add_zero] at hd
    have hnorm : ‖meet u P.1 P.2 (hgt u p) - p‖
        = |fwd u (meet u P.1 P.2 (hgt u p) - p)| := by
      conv_lhs => rw [hd]
      rw [norm_smul, Real.norm_eq_abs, hu, mul_one]
    rw [hnorm, fwd_sub] at hmnb
    exact hmnb
  have hother : ∀ P ∈ L₁ ++ L₂, mark u P (p - t • u) + mark u P (p + t • u) = 0 := by
    intro P hP
    have hPne : hgt u P.1 ≠ hgt u P.2 := by
      rcases List.mem_append.1 hP with h | h
      · exact hL P (by simp [h])
      · exact hL P (by simp [h])
    have hiff : Crosses u P (p - t • u) ↔ Crosses u P (p + t • u) := by
      simp only [Crosses, hgm, hgp, hfm, hfp]
      constructor
      · rintro ⟨g1, g2, g3⟩
        refine ⟨g1, g2, ?_⟩
        rcases le_abs.1 (hfar P hP hPne g1 g2.le) with hcase | hcase
        · linarith
        · linarith
      · rintro ⟨g1, g2, g3⟩
        exact ⟨g1, g2, by linarith⟩
    simp only [mark, hiff]
    exact add_self_zmod_two _
  -- the edge `(a, b)` itself is crossed from exactly one of the two points
  have hbtw : min (hgt u a) (hgt u b) < hgt u p ∧ hgt u p < max (hgt u a) (hgt u b) := by
    rcases lt_or_gt_of_ne hab with h | h
    · obtain ⟨g1, g2⟩ := hgt_lt_of_mem_openSegment h hp
      rw [min_eq_left h.le, max_eq_right h.le]
      exact ⟨g1, g2⟩
    · obtain ⟨g1, g2⟩ := hgt_lt_of_mem_openSegment h (by rwa [openSegment_symm] at hp)
      rw [min_eq_right h.le, max_eq_left h.le]
      exact ⟨g1, g2⟩
  have hedge : mark u (a, b) (p - t • u) + mark u (a, b) (p + t • u) = 1 := by
    have hm1 : Crosses u (a, b) (p - t • u) := by
      refine ⟨?_, ?_, ?_⟩
      · rw [hgm]; exact hbtw.1.le
      · rw [hgm]; exact hbtw.2
      · rw [hgm, hfm, hmeetp]; linarith
    have hm2 : ¬ Crosses u (a, b) (p + t • u) := by
      rintro ⟨-, -, g⟩
      rw [hgp, hfp, hmeetp] at g
      linarith
    rw [mark, mark, if_pos hm1, if_neg hm2, add_zero]
  refine ⟨by rw [hneg]; exact hcov (-t) (by linarith) habsm, hcov t (ne_of_gt ht) habsp, ?_⟩
  have hz1 : (L₁.map (fun P => mark u P (p - t • u) + mark u P (p + t • u))).sum = 0 := by
    refine List.sum_eq_zero ?_
    intro x hx
    obtain ⟨P, hP, rfl⟩ := List.mem_map.1 hx
    exact hother P (List.mem_append_left _ hP)
  have hz2 : (L₂.map (fun P => mark u P (p - t • u) + mark u P (p + t • u))).sum = 0 := by
    refine List.sum_eq_zero ?_
    intro x hx
    obtain ⟨P, hP, rfl⟩ := List.mem_map.1 hx
    exact hother P (List.mem_append_right _ hP)
  have hsum : parity u (L₁ ++ (a, b) :: L₂) (p - t • u)
      + parity u (L₁ ++ (a, b) :: L₂) (p + t • u) = 1 := by
    rw [parity, parity, ← sum_map_add, List.map_append, List.map_cons, List.sum_append,
      List.sum_cons, hz1, hz2, hedge]
    ring
  have harith : ∀ x y : ZMod 2, x + y = 1 → x = y + 1 := by decide
  exact harith _ _ hsum

end Flip

/-! ### Choosing the ray direction -/

/-- The blueprint's opening move — "rotate so that no edge is horizontal" — without rotating
anything: finitely many edge directions rule out only finitely many rays, so some direction
is level for none of them. -/
theorem exists_direction_hgt_ne (L : List Piece) (hnd : ∀ P ∈ L, P.Nondeg) :
    ∃ u : Plane, Plane.IsDirection u ∧ ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2 := by
  obtain ⟨u, hu, hdet⟩ :=
    Plane.exists_isDirection_det_ne_zero (L.finite_toSet.image (fun P : Piece => P.2 - P.1))
  refine ⟨u, hu, fun P hP heq => ?_⟩
  have hne : P.2 - P.1 ≠ 0 := sub_ne_zero.2 fun h => hnd P hP h.symm
  have hzero : hgt u (P.2 - P.1) = 0 := by rw [hgt_sub, heq]; ring
  exact hdet _ ⟨P, hP, rfl⟩ hne hzero

end Schoenflies

end BundlePart405

section BundlePart406
/- Source: dev/planar_search/schoenflies_port/Schoenflies/PolygonBridge.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/





/-!
# The polygon bridge

Two independent representations of a closed polygon had grown up side by side and never met.
`Schoenflies/Strip.lean` carries `ClosedPolygon m`, a cyclic vertex list indexed by
`ZMod (m + 3)`, and everything the collar of Lemma 1.8 says is said about it.
`Schoenflies/Parity.lean` carries `List Piece` together with `IsClosedChain`, and everything
the crossing count of Lemma 2.1 and Lemma 2.2 says is said about *that*. Neither knew about
the other, and — worse — nothing anywhere produced a `ClosedPolygon`, so every theorem about
one was formally a theorem about a structure that might have been empty.

This module closes the three gaps.

## Non-vacuity

`Schoenflies.triangle` builds a `ClosedPolygon 0` out of any three points with nonzero
orientation determinant, and `Schoenflies.unitTriangle` is the concrete instance with vertices
`(0,0)`, `(1,0)`, `(0,1)`. The only real work is `edges_meet`: two edges of a triangle share
exactly one endpoint, and `Schoenflies.segment_inter_shared` says two segments meeting at an
endpoint whose far ends are off the shared line meet nowhere else. That lemma is proved by
taking the orientation form against the first segment's direction, which kills the first
segment's own parameter and forces the second's to vanish.

## The representation bridge

`ClosedPolygon.pieces` lists the `m + 3` edges as pairs of endpoints, in cyclic order.
It is a closed chain (`ClosedPolygon.isClosedChain_pieces`), every piece is nondegenerate
(`ClosedPolygon.pieces_nondeg`), and — the point of the exercise —
`ClosedPolygon.cover_pieces` says it occupies exactly the polygon's carrier. Closedness is a
telescoping sum: `Schoenflies.sum_range_boundary` evaluates the mod-`2` boundary of the chain
`0 → 1 → ⋯ → n` as the sum of its two ends, and the two ends of `0 → ⋯ → m + 3` are the same
vertex because `m + 3` is `0` in `ZMod (m + 3)`.

## The curve bridge

`ClosedPolygon.isJordanCurve_carrier` and `ClosedPolygon.isPolygonal_carrier` say the carrier
is a simple closed polygonal curve in the blueprint's sense, which is what the polygonal Jordan
curve theorem (Theorem 2.3) takes as its hypothesis. The loop is built by concatenating edge
parametrizations around the cycle: `ClosedPolygon.chain k` is the union of the edges leaving
vertices `0, …, k`, and `ClosedPolygon.isArcBetween_chain` grows it one edge at a time by
`IsArcBetween.concatenate`. The hypothesis that concatenation needs — the new edge meets what
came before only at the vertex they share — is exactly `edges_meet` twice over: once to place
the meeting point among the new edge's own two endpoints, and once more to rule out the far
one, which would otherwise let the polygon close early. The last edge closes the loop through
`IsJordanCurve.of_two_arcs`, and there the far endpoint is *not* ruled out: it is the second
shared point that makes the two arcs a curve rather than an arc.

## Both halves at once

The last section is what the bridge is for: the two statements of Lemma 2.2 — parity is
constant on a component of the complement, and it flips across an edge — restated for the
*carrier* of a `ClosedPolygon` rather than for the cover of an anonymous list. The flip needs
the edge list split around the edge being crossed, which is `List.append_of_mem` together with
`ClosedPolygon.pieces_nodup`; that the two remaining fragments miss the crossing point is
`edges_meet` a third time.

## Blueprint

* `Schoenflies.triangle`, `Schoenflies.unitTriangle` — witnesses that §1's "simple closed
  polygonal curve" is not vacuous.
* `ClosedPolygon.pieces`, `ClosedPolygon.cover_pieces`, `ClosedPolygon.isClosedChain_pieces` —
  the edge list the crossing count of §2 is defined on, and that it carries the polygon.
* `ClosedPolygon.isJordanCurve_carrier`, `ClosedPolygon.isPolygonal_carrier` — §1, "a simple
  closed polygonal curve"; jointly the hypothesis of Theorem 2.3.
* `ClosedPolygon.parity_eq_of_mem_connectedComponentIn_carrier`,
  `ClosedPolygon.parity_flip_carrier` — the two halves of Lemma 2.2, read off a
  `ClosedPolygon`. These are the statements Theorem 2.3 consumes.

One general lemma is stated here that does not belong here: `Schoenflies.exists_of_mem_cover`,
the destructor matching `Schoenflies.mem_cover`, whose home is `Schoenflies/Parity.lean`.
-/

open Metric Set

namespace Schoenflies

open Plane

variable {m : ℕ}

/-! ## Two segments that share an endpoint

The one piece of plane geometry this module needs. `Schoenflies/SegmentMeet.lean` describes
the intersection of two arbitrary segments; here the two are known to share an endpoint, and
the conclusion is sharper and the proof shorter. -/

/-- Two segments sharing the endpoint `b`, whose far ends are off the line through the other,
meet only at `b`. Taking the orientation form against `b - a` annihilates the first segment's
own parameter, so the second segment's parameter must vanish. -/
theorem segment_inter_shared {a b c : Plane} (h : det (b - a) (c - b) ≠ 0) :
    segment ℝ a b ∩ segment ℝ b c ⊆ {b} := by
  rintro z ⟨hz1, hz2⟩
  rw [segment_eq_image' ℝ a b] at hz1
  rw [segment_eq_image' ℝ b c] at hz2
  obtain ⟨s, -, hs⟩ := hz1
  obtain ⟨t, -, ht⟩ := hz2
  simp only at hs ht
  have hvec : t • (c - b) = (s - 1) • (b - a) := by
    have hz := ht.trans hs.symm
    linear_combination (norm := module) hz
  have key : t * det (b - a) (c - b) = 0 := by
    have h2 : det (b - a) (t • (c - b)) = det (b - a) ((s - 1) • (b - a)) := by rw [hvec]
    rw [det_smul_right, det_smul_right, det_self, mul_zero] at h2
    exact h2
  have ht0 : t = 0 := by
    rcases mul_eq_zero.1 key with h0 | h0
    · exact h0
    · exact absurd h0 h
  simp only [mem_singleton_iff]
  rw [← ht, ht0, zero_smul, add_zero]

/-! ## Non-vacuity: a triangle is a closed polygon

Nothing in the strip development ever built a `ClosedPolygon`, so `polygonal_collar` and every
theorem beside it was formally a theorem about a structure with no known inhabitant. A triangle
is the smallest witness, and no coordinates are needed: any three points with nonzero
orientation determinant will do. -/

section Triangle

variable {a b c : Plane}

/-- The orientation of a triple, read at its first corner and at its second, is the same. -/
private theorem det_rot₁ (a b c : Plane) : det (b - a) (c - b) = det (b - a) (c - a) := by
  simp only [Plane.det, Plane.sub_apply]; ring

/-- The same, one corner further round. -/
private theorem det_rot₂ (a b c : Plane) : det (c - b) (a - c) = det (b - a) (c - a) := by
  simp only [Plane.det, Plane.sub_apply]; ring

/-- And once more; the orientation form is invariant under cycling the triple. -/
private theorem det_rot₃ (a b c : Plane) : det (a - c) (b - a) = det (b - a) (c - a) := by
  simp only [Plane.det, Plane.sub_apply]; ring

/-- **A triangle is a simple closed polygon.** Any three points that are not collinear, taken
in that cyclic order. `edges_meet` holds because two of the three edges always share exactly
one endpoint, and `corner` because the orientation form is what nonzero says. -/
def triangle (h : det (b - a) (c - a) ≠ 0) : ClosedPolygon 0 where
  vertex := ![a, b, c]
  vertex_inj := by
    have hab : a ≠ b := by
      rintro rfl
      exact h (by simp [Plane.det])
    have hbc : b ≠ c := by
      rintro rfl
      exact h (det_self _)
    have hac : a ≠ c := by
      rintro rfl
      exact h (by simp [Plane.det])
    intro i j hij
    have hi : ∀ i : ZMod 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
    rcases hi i with rfl | rfl | rfl <;> rcases hi j with rfl | rfl | rfl
    · rfl
    · exact absurd (show a = b from hij) hab
    · exact absurd (show a = c from hij) hac
    · exact absurd (show a = b from hij.symm) hab
    · rfl
    · exact absurd (show b = c from hij) hbc
    · exact absurd (show a = c from hij.symm) hac
    · exact absurd (show b = c from hij.symm) hbc
    · rfl
  edges_meet := by
    have mab : segment ℝ a b ∩ segment ℝ b c ⊆ {b} :=
      segment_inter_shared (by rw [det_rot₁]; exact h)
    have mbc : segment ℝ b c ∩ segment ℝ c a ⊆ {c} :=
      segment_inter_shared (by rw [det_rot₂]; exact h)
    have mca : segment ℝ c a ∩ segment ℝ a b ⊆ {a} :=
      segment_inter_shared (by rw [det_rot₃]; exact h)
    intro i j hij
    have hi : ∀ i : ZMod 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
    rcases hi i with rfl | rfl | rfl <;> rcases hi j with rfl | rfl | rfl
    · exact absurd rfl hij
    · change segment ℝ a b ∩ segment ℝ b c ⊆ {a, b}
      exact subset_trans mab (by simp)
    · change segment ℝ a b ∩ segment ℝ c a ⊆ {a, b}
      rw [Set.inter_comm]
      exact subset_trans mca (by simp)
    · change segment ℝ b c ∩ segment ℝ a b ⊆ {b, c}
      rw [Set.inter_comm]
      exact subset_trans mab (by simp)
    · exact absurd rfl hij
    · change segment ℝ b c ∩ segment ℝ c a ⊆ {b, c}
      exact subset_trans mbc (by simp)
    · change segment ℝ c a ∩ segment ℝ a b ⊆ {c, a}
      exact subset_trans mca (by simp)
    · change segment ℝ c a ∩ segment ℝ b c ⊆ {c, a}
      rw [Set.inter_comm]
      exact subset_trans mbc (by simp)
    · exact absurd rfl hij
  corner := by
    intro i
    have hi : ∀ i : ZMod 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
    rcases hi i with rfl | rfl | rfl
    · change det (c - a) (b - a) ≠ 0
      intro hc
      apply h
      simp only [Plane.det, Plane.sub_apply] at hc ⊢
      linarith
    · change det (a - b) (c - b) ≠ 0
      intro hc
      apply h
      simp only [Plane.det, Plane.sub_apply] at hc ⊢
      linarith
    · change det (b - c) (a - c) ≠ 0
      intro hc
      apply h
      simp only [Plane.det, Plane.sub_apply] at hc ⊢
      linarith

@[simp] theorem triangle_vertex_zero (h : det (b - a) (c - a) ≠ 0) :
    (triangle h).vertex 0 = a := rfl

@[simp] theorem triangle_vertex_one (h : det (b - a) (c - a) ≠ 0) :
    (triangle h).vertex 1 = b := rfl

@[simp] theorem triangle_vertex_two (h : det (b - a) (c - a) ≠ 0) :
    (triangle h).vertex 2 = c := rfl

end Triangle

/-- A concrete simple closed polygon: the triangle with vertices `(0,0)`, `(1,0)` and
`(0,1)`. -/
def unitTriangle : ClosedPolygon 0 :=
  triangle (a := mk 0 0) (b := mk 1 0) (c := mk 0 1)
    (by norm_num [Plane.det, Plane.sub_apply])

/-! ## A telescoping sum mod two -/

/-- The mod-`2` boundary of the chain `0 → 1 → ⋯ → n` is the sum of its two ends: every
interior vertex is counted twice. This is the whole content of "a cycle is a closed chain". -/
theorem sum_range_boundary (g : ℕ → ZMod 2) :
    ∀ n : ℕ, ((List.range n).map fun j => g j + g (j + 1)).sum = g 0 + g n
  | 0 => by simpa using (add_self_zmod_two (g 0)).symm
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_range_boundary g n]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    linear_combination add_self_zmod_two (g n)

namespace ClosedPolygon

/-! ## Natural-number indices

Both bridges run over the vertices with a natural number and cast into `ZMod (m + 3)`. Below
the modulus the cast is injective, which is what turns "these two indices are different
naturals" into "these are different edges" and back. -/

/-- Below the modulus, casting a natural number into `ZMod (m + 3)` is injective. -/
theorem natCast_inj {j k : ℕ} (hj : j < m + 3) (hk : k < m + 3)
    (h : (j : ZMod (m + 3)) = (k : ZMod (m + 3))) : j = k := by
  have hval := congrArg ZMod.val h
  rwa [ZMod.val_cast_of_lt hj, ZMod.val_cast_of_lt hk] at hval

/-- The successor, pushed through the cast. -/
theorem natCast_succ (j : ℕ) : ((j + 1 : ℕ) : ZMod (m + 3)) = (j : ZMod (m + 3)) + 1 := by
  push_cast; ring

variable {P : ClosedPolygon m}

/-- Distinct indices below the modulus name distinct vertices. -/
theorem vertex_natCast_ne {j k : ℕ} (hj : j < m + 3) (hk : k < m + 3) (hjk : j ≠ k) :
    P.vertex (j : ZMod (m + 3)) ≠ P.vertex (k : ZMod (m + 3)) :=
  fun heq => hjk (natCast_inj hj hk (P.vertex_inj heq))

/-- **An edge meets an earlier edge only at its own initial vertex.** `edges_meet` puts the
meeting point at one of the two ends of the later edge; the far end is ruled out by applying
`edges_meet` the other way round, which would put the later edge's *terminal* vertex on the
earlier edge and hence make it one of two vertices it cannot be. This is what stops the
polygon from closing before it has run through all its vertices. -/
theorem edge_meet_earlier {j k : ℕ} (hjk : j < k) (hk : k + 1 < m + 3) {z : Plane}
    (hzj : z ∈ P.edge (j : ZMod (m + 3))) (hzk : z ∈ P.edge (k : ZMod (m + 3))) :
    z = P.vertex (k : ZMod (m + 3)) := by
  have hjn : j < m + 3 := by omega
  have hkn : k < m + 3 := by omega
  have hne : (k : ZMod (m + 3)) ≠ (j : ZMod (m + 3)) :=
    fun heq => (by omega : k ≠ j) (natCast_inj hkn hjn heq)
  have hmem := P.edges_meet _ _ hne (Set.mem_inter hzk hzj)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with hmem | hmem
  · exact hmem
  -- The far end: it would have to be one of the earlier edge's two ends as well.
  exfalso
  have hmem2 := P.edges_meet _ _ (Ne.symm hne) (Set.mem_inter hzj hzk)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem2
  rw [← natCast_succ] at hmem
  rcases hmem2 with hmem2 | hmem2
  · have : k + 1 = j := natCast_inj hk hjn (P.vertex_inj (hmem ▸ hmem2))
    omega
  · rw [← natCast_succ] at hmem2
    have : k + 1 = j + 1 := natCast_inj hk (by omega) (P.vertex_inj (hmem ▸ hmem2))
    omega

/-- **The last edge meets every earlier edge only at a vertex it shares with the cycle's ends.**
Here the far end is *not* excluded: the last edge runs back to vertex `0`, so both of its ends
are legitimate meeting points, and that is precisely what makes the carrier a closed curve
rather than an arc. -/
theorem edge_meet_last {j : ℕ} (hj : j < m + 2) {z : Plane}
    (hzj : z ∈ P.edge (j : ZMod (m + 3)))
    (hz : z ∈ P.edge ((m + 2 : ℕ) : ZMod (m + 3))) :
    z = P.vertex 0 ∨ z = P.vertex ((m + 2 : ℕ) : ZMod (m + 3)) := by
  have hne : ((m + 2 : ℕ) : ZMod (m + 3)) ≠ (j : ZMod (m + 3)) :=
    fun heq => (by omega : m + 2 ≠ j) (natCast_inj (by omega) (by omega) heq)
  have hlast : ((m + 2 : ℕ) : ZMod (m + 3)) + 1 = 0 := by
    rw [← natCast_succ]
    exact ZMod.natCast_self (m + 3)
  have hmem := P.edges_meet _ _ hne (Set.mem_inter hz hzj)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with hmem | hmem
  · exact Or.inr hmem
  · rw [hlast] at hmem
    exact Or.inl hmem

/-! ## The representation bridge

`Schoenflies/Parity.lean` counts crossings of a `List Piece`; `ClosedPolygon.pieces` is the
list it should be handed. The four obligations below are exactly what every parity statement
asks for: a list, closedness, nondegeneracy, and — the one that carries the geometry — that
the list occupies the polygon. -/

/-- The `m + 3` edges of the polygon, as a list of pieces in cyclic order. This is the form
the crossing count of §2 is defined on. -/
def pieces (P : ClosedPolygon m) : List Piece :=
  (List.range (m + 3)).map fun j : ℕ =>
    (P.vertex (j : ZMod (m + 3)), P.vertex ((j : ZMod (m + 3)) + 1))

/-- Every edge of the polygon is on the list. -/
theorem mem_pieces (P : ClosedPolygon m) (i : ZMod (m + 3)) :
    (P.vertex i, P.vertex (i + 1)) ∈ P.pieces := by
  refine List.mem_map.2 ⟨i.val, List.mem_range.2 (ZMod.val_lt i), ?_⟩
  rw [ZMod.natCast_rightInverse i]

/-- Every piece on the list is an edge of the polygon. -/
theorem exists_of_mem_pieces {P : ClosedPolygon m} {Q : Piece} (hQ : Q ∈ P.pieces) :
    ∃ i : ZMod (m + 3), Q = (P.vertex i, P.vertex (i + 1)) := by
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hQ
  exact ⟨(j : ZMod (m + 3)), rfl⟩

/-- No edge of a simple closed polygon is degenerate: consecutive vertices are distinct. -/
theorem pieces_nondeg (P : ClosedPolygon m) : ∀ Q ∈ P.pieces, Q.Nondeg := by
  intro Q hQ
  obtain ⟨i, rfl⟩ := exists_of_mem_pieces hQ
  exact P.vertex_ne i

/-- **The edge list is a closed chain.** Each vertex is the terminal end of one edge and the
initial end of the next, so it is counted twice; the cycle closes because `m + 3` is `0` in
`ZMod (m + 3)`, which makes the two ends of the telescoping sum the same vertex. -/
theorem isClosedChain_pieces (P : ClosedPolygon m) : IsClosedChain P.pieces := by
  intro f
  have hmap : (P.pieces.map fun Q => f Q.1 + f Q.2)
      = (List.range (m + 3)).map fun j : ℕ =>
        f (P.vertex (j : ZMod (m + 3))) + f (P.vertex ((j + 1 : ℕ) : ZMod (m + 3))) := by
    rw [pieces, List.map_map]
    refine List.map_congr_left fun j _ => ?_
    simp only [Function.comp_apply, natCast_succ]
  rw [hmap]
  have key := sum_range_boundary (fun k : ℕ => f (P.vertex (k : ZMod (m + 3)))) (m + 3)
  rw [key, Nat.cast_zero, ZMod.natCast_self]
  exact add_self_zmod_two _

/-- **The edge list carries the polygon.** Without this equation no parity statement says
anything about a `ClosedPolygon`: the crossing count is defined against `cover`, and the collar
against `carrier`. -/
theorem cover_pieces (P : ClosedPolygon m) : cover P.pieces = P.carrier := by
  apply Set.Subset.antisymm
  · rw [cover]
    refine Set.iUnion₂_subset fun Q hQ => ?_
    obtain ⟨i, rfl⟩ := exists_of_mem_pieces hQ
    exact Set.subset_iUnion (fun i => P.edge i) i
  · refine Set.iUnion_subset fun i => ?_
    exact fun z hz => mem_cover (P.mem_pieces i) hz

/-! ## The curve bridge

`chain k` is the union of the edges leaving vertices `0, …, k`. Each is an arc from vertex `0`
to vertex `k + 1`, obtained from its predecessor by `IsArcBetween.concatenate`; the whole
carrier is the last of them plus the edge that runs back to vertex `0`. -/

/-- The union of the edges leaving vertices `0, 1, …, k`. -/
def chain (P : ClosedPolygon m) : ℕ → Set Plane
  | 0 => P.edge 0
  | k + 1 => chain P k ∪ P.edge ((k + 1 : ℕ) : ZMod (m + 3))

theorem mem_chain_iff {z : Plane} {k : ℕ} :
    z ∈ P.chain k ↔ ∃ j ≤ k, z ∈ P.edge (j : ZMod (m + 3)) := by
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

/-- Running through all `m + 3` edges exhausts the carrier. -/
theorem chain_eq_carrier (P : ClosedPolygon m) : P.chain (m + 2) = P.carrier := by
  ext z
  rw [mem_chain_iff]
  constructor
  · rintro ⟨j, -, hzj⟩
    exact Set.mem_iUnion.2 ⟨_, hzj⟩
  · intro hz
    obtain ⟨i, hzi⟩ := Set.mem_iUnion.1 hz
    refine ⟨i.val, ?_, ?_⟩
    · have := ZMod.val_lt i
      omega
    · rwa [ZMod.natCast_rightInverse i]

/-- **The partial chains are arcs.** One edge at a time, glued at the vertex they share:
`edge_meet_earlier` is exactly the hypothesis `IsArcBetween.concatenate` asks for. The bound
`k + 1 < m + 3` is what keeps the growing arc from meeting its own start. -/
theorem isArcBetween_chain (P : ClosedPolygon m) :
    ∀ k : ℕ, k + 1 < m + 3 →
      IsArcBetween (P.chain k) (P.vertex 0) (P.vertex ((k + 1 : ℕ) : ZMod (m + 3))) := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [natCast_succ]
    exact isArcBetween_segment (P.vertex_ne 0)
  | succ k ih =>
    intro hk
    have hA := ih (by omega)
    have hB : IsArcBetween (P.edge ((k + 1 : ℕ) : ZMod (m + 3)))
        (P.vertex ((k + 1 : ℕ) : ZMod (m + 3)))
        (P.vertex ((k + 1 + 1 : ℕ) : ZMod (m + 3))) := by
      rw [natCast_succ (k + 1)]
      exact isArcBetween_segment (P.vertex_ne _)
    have hmeet : ∀ z ∈ P.chain k, z ∈ P.edge ((k + 1 : ℕ) : ZMod (m + 3)) →
        z = P.vertex ((k + 1 : ℕ) : ZMod (m + 3)) := by
      intro z hz hze
      obtain ⟨j, hj, hzj⟩ := mem_chain_iff.1 hz
      exact edge_meet_earlier (by omega) (by omega) hzj hze
    exact hA.concatenate hB hmeet

/-- **The carrier of a simple closed polygon is a Jordan curve.** The arc through all but the
last edge, and the last edge running back to where it started, meet exactly at their two
shared endpoints. -/
theorem isJordanCurve_carrier (P : ClosedPolygon m) : IsJordanCurve P.carrier := by
  have hlast : ((m + 2 : ℕ) : ZMod (m + 3)) + 1 = 0 := by
    rw [← natCast_succ]
    exact ZMod.natCast_self (m + 3)
  have hA : IsArcBetween (P.chain (m + 1)) (P.vertex 0)
      (P.vertex ((m + 2 : ℕ) : ZMod (m + 3))) := P.isArcBetween_chain (m + 1) (by omega)
  have hedge : P.edge ((m + 2 : ℕ) : ZMod (m + 3))
      = segment ℝ (P.vertex ((m + 2 : ℕ) : ZMod (m + 3))) (P.vertex 0) := by
    rw [edge, hlast]
  have hB : IsArcBetween (P.edge ((m + 2 : ℕ) : ZMod (m + 3)))
      (P.vertex ((m + 2 : ℕ) : ZMod (m + 3))) (P.vertex 0) := by
    rw [hedge]
    refine isArcBetween_segment ?_
    rw [← hlast]
    exact P.vertex_ne _
  have hmeet : ∀ z ∈ P.chain (m + 1), z ∈ P.edge ((m + 2 : ℕ) : ZMod (m + 3)) →
      z = P.vertex 0 ∨ z = P.vertex ((m + 2 : ℕ) : ZMod (m + 3)) := by
    intro z hz hze
    obtain ⟨j, hj, hzj⟩ := mem_chain_iff.1 hz
    exact edge_meet_last (by omega) hzj hze
  have hcurve := IsJordanCurve.of_two_arcs hA hB hmeet
  have hsplit : P.chain (m + 2)
      = P.chain (m + 1) ∪ P.edge ((m + 2 : ℕ) : ZMod (m + 3)) := rfl
  rwa [← hsplit, chain_eq_carrier] at hcurve

/-! ### The carrier is polygonal

`IsPolygonal` asks for a vertex list whose `poly` carrier is the set. Cycling once round the
polygon and coming back to the first vertex is that list. -/

/-- The vertex list `v₀, v₁, …, v_{k+1}`, which walks the first `k + 1` edges. -/
def vlist (P : ClosedPolygon m) : ℕ → List Plane
  | 0 => [P.vertex 0, P.vertex ((1 : ℕ) : ZMod (m + 3))]
  | k + 1 => vlist P k ++ [P.vertex ((k + 1 + 1 : ℕ) : ZMod (m + 3))]

theorem vlist_ne_nil (P : ClosedPolygon m) (k : ℕ) : P.vlist k ≠ [] := by
  cases k <;> simp [vlist]

theorem getLast_vlist (P : ClosedPolygon m) (k : ℕ) :
    (P.vlist k).getLast (P.vlist_ne_nil k) = P.vertex ((k + 1 : ℕ) : ZMod (m + 3)) := by
  cases k with
  | zero => simp [vlist]
  | succ k => simp [vlist]

theorem poly_vlist (P : ClosedPolygon m) (k : ℕ) : poly (P.vlist k) = P.chain k := by
  induction k with
  | zero =>
    rw [vlist, poly_pair, chain, edge, natCast_succ]
    norm_num
  | succ k ih =>
    rw [vlist, poly_concat (P.vlist_ne_nil k), getLast_vlist, ih, chain, edge,
      natCast_succ (k + 1)]

/-- **The carrier of a simple closed polygon is polygonal**: it is the carrier of the vertex
list that runs once round the cycle and back to its first vertex. -/
theorem isPolygonal_carrier (P : ClosedPolygon m) : IsPolygonal P.carrier :=
  ⟨P.vlist (m + 2), by rw [poly_vlist, chain_eq_carrier]⟩

/-! ## The bridge in use

With both halves in place a parity statement can be read off a `ClosedPolygon` directly. -/

/-- A ray direction level for no edge of the polygon; the blueprint's "rotate the coordinate
system so that no edge is horizontal", with nothing rotated. -/
theorem exists_direction_pieces (P : ClosedPolygon m) :
    ∃ u : Plane, Plane.IsDirection u ∧ ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2 :=
  exists_direction_hgt_ne P.pieces P.pieces_nondeg

/-- **Crossing parity for a closed polygon** (Lemma 2.2): `π_C` is constant on the component
of the complement of the *carrier* containing a given point. -/
theorem parity_eq_of_mem_connectedComponentIn_carrier (P : ClosedPolygon m) {u : Plane}
    (hu : Plane.IsDirection u) (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) {x y : Plane}
    (hx : x ∉ P.carrier) (hy : y ∈ connectedComponentIn P.carrierᶜ x) :
    parity u P.pieces y = parity u P.pieces x := by
  rw [← P.cover_pieces] at hx hy
  exact parity_eq_of_mem_connectedComponentIn hu hL P.isClosedChain_pieces hx hy

/-! ### The flip across an edge

The second half of Lemma 2.2 is stated for the edge list split around the edge being crossed,
`L₁ ++ (a, b) :: L₂`. Splitting is `List.append_of_mem`; what has to be checked is that the two
remaining fragments miss the point being crossed, and that is `edges_meet` again — another edge
can reach an interior point of this one only at one of this one's two ends, which an interior
point is not. -/

/-- What a list of pieces occupies, taken apart. The counterpart of `Schoenflies.mem_cover`,
which only builds; **this belongs next to it in `Schoenflies/Parity.lean`.** -/
theorem exists_of_mem_cover {L : List Piece} {z : Plane} (hz : z ∈ cover L) :
    ∃ R ∈ L, z ∈ R.seg := by
  rw [cover] at hz
  simpa using hz

/-- An interior point of one edge lies on no other edge: `edges_meet` puts any other edge's
meeting point at an end of this one, and an interior point is neither end. -/
theorem notMem_edge_of_mem_openSegment {i j : ZMod (m + 3)} (hij : j ≠ i) {p : Plane}
    (hp : p ∈ openSegment ℝ (P.vertex i) (P.vertex (i + 1))) : p ∉ P.edge j := by
  intro hpj
  have hmem := P.edges_meet i j (Ne.symm hij)
    (Set.mem_inter (openSegment_subset_segment ℝ _ _ hp) hpj)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with rfl | rfl
  · exact P.vertex_ne i (left_mem_openSegment_iff.1 hp)
  · exact P.vertex_ne i (right_mem_openSegment_iff.1 hp)

/-- The edge list has no repeated entry: distinct indices name distinct initial vertices. -/
theorem pieces_nodup (P : ClosedPolygon m) : P.pieces.Nodup := by
  rw [pieces]
  refine List.Nodup.map_on (fun j hj k hk heq => ?_) List.nodup_range
  exact natCast_inj (List.mem_range.1 hj) (List.mem_range.1 hk)
    (P.vertex_inj (congrArg Prod.fst heq))

/-- **Opposite sides of an edge, for a closed polygon** (Lemma 2.2, second half). Just before
and just after an interior point of an edge, in the ray direction, the base point is off the
carrier and the crossing parity differs by one. -/
theorem parity_flip_carrier (P : ClosedPolygon m) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) (i : ZMod (m + 3)) {p : Plane}
    (hp : p ∈ openSegment ℝ (P.vertex i) (P.vertex (i + 1))) :
    ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ →
      p - t • u ∉ P.carrier ∧ p + t • u ∉ P.carrier ∧
        parity u P.pieces (p - t • u) = parity u P.pieces (p + t • u) + 1 := by
  obtain ⟨L₁, L₂, hsplit⟩ := List.append_of_mem (P.mem_pieces i)
  -- the edge being crossed occurs only once, so it is on neither fragment
  have hnodup := P.pieces_nodup
  rw [hsplit, List.nodup_append] at hnodup
  obtain ⟨-, hnd2, hdisj⟩ := hnodup
  have hQ₁ : (P.vertex i, P.vertex (i + 1)) ∉ L₁ := fun hmem => hdisj _ hmem _ (by simp) rfl
  have hQ₂ : (P.vertex i, P.vertex (i + 1)) ∉ L₂ := (List.nodup_cons.1 hnd2).1
  have hmiss : ∀ R ∈ L₁ ++ L₂, p ∉ Piece.seg R := by
    intro R hR
    have hRne : R ≠ (P.vertex i, P.vertex (i + 1)) := by
      rcases List.mem_append.1 hR with h | h
      · exact fun heq => hQ₁ (heq ▸ h)
      · exact fun heq => hQ₂ (heq ▸ h)
    have hRmem : R ∈ P.pieces := by
      rw [hsplit]
      rcases List.mem_append.1 hR with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
    obtain ⟨j, rfl⟩ := exists_of_mem_pieces hRmem
    exact notMem_edge_of_mem_openSegment (fun heq => hRne (by rw [heq])) hp
  have h1 : p ∉ cover L₁ := by
    intro hmem
    obtain ⟨R, hR, hpR⟩ := exists_of_mem_cover hmem
    exact hmiss R (List.mem_append_left _ hR) hpR
  have h2 : p ∉ cover L₂ := by
    intro hmem
    obtain ⟨R, hR, hpR⟩ := exists_of_mem_cover hmem
    exact hmiss R (List.mem_append_right _ hR) hpR
  have hL' : ∀ R ∈ L₁ ++ (P.vertex i, P.vertex (i + 1)) :: L₂, hgt u R.1 ≠ hgt u R.2 := by
    rw [← hsplit]; exact hL
  obtain ⟨δ, hδ, hmain⟩ := parity_flip hu hL' hp h1 h2
  refine ⟨δ, hδ, fun t ht htδ => ?_⟩
  obtain ⟨ha, hb, hc⟩ := hmain t ht htδ
  rw [← hsplit] at ha hb hc
  rw [P.cover_pieces] at ha hb
  exact ⟨ha, hb, hc⟩

end ClosedPolygon

end Schoenflies

end BundlePart406

section BundlePart407
/- Source: dev/planar_search/schoenflies_port/Schoenflies/StripConstants.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/



/-!
# The constants of a polygonal collar exist

`Schoenflies.StripData` names the three numbers the two-sided strip lemma runs on — a cone
radius `R`, a trim `lam` and a half-width `rho` — together with the separation hypotheses they
have to satisfy. Everything in `Schoenflies/Strip.lean` is stated *for a given* `StripData`;
this module produces one, removing that parameter from the resulting theorem.

The recipe is the blueprint's own, in the blueprint's order:

1. `R` from three sources — the pairwise vertex separations, the distance from each vertex to
   each nonincident edge, and the prescribed open set — each an instance of Lemma 1.4, plus
   `R ≤ len i` so that a sector cannot run past the far end of an incident edge. The vertex
   separations are asked for with a factor `2` of slack, which is what the block-versus-sector
   estimates of `Strip.lean` spend.
2. `lam := R / 5`, which gives `2 * lam < R` and, through `R ≤ len i`, also `4 * lam < len i`.
3. `rho` from the distance of each *trimmed* edge to every other edge, and from the germ
   threshold `rho * (1 + |⟪r₁, r₂⟫|) ≤ lam * |det r₁ r₂|` at every vertex. The determinant is
   nonzero at a corner, so the threshold is a positive upper bound on `rho` and is met by
   shrinking; `rho < lam` is one more shrinking.

Steps 1 and 3 are finite families of positive bounds, combined by
`Schoenflies.exists_pos_forall_of_finite`.

## What simplicity is used for

Two of the separations are *false* for a self-touching closed polygonal curve, and each is the
exact point where `ClosedPolygon.edges_meet` is consumed:

* `ClosedPolygon.vertex_notMem_edge` — a vertex lies on no edge but the two incident to it.
  This is what makes `{vertex i}` and `edge j` disjoint compact sets.
* `ClosedPolygon.trimmed_disjoint_edge` — the trimmed core of an edge misses every other edge.
  Here the two endpoints allowed by `edges_meet` are excluded by the trim itself, since a point
  of the core is at distance at least `lam` from both.

`edges_meet` as stated is one-sided (`edge i ∩ edge j ⊆ {vertex i, vertex (i + 1)}`), but it is
quantified over all ordered pairs, so the symmetric instance is available and both proofs below
use whichever side is convenient. It carries enough simplicity for both statements.

## Blueprint

* `Schoenflies.exists_stripData_subset` — the constants of Lemma 1.8 (Two-sided polygonal
  strips), chosen inside a prescribed open set containing the curve; this is the "Lemma 1.4 (a)
  lets all disks and strips be chosen inside the prescribed open set" of the last paragraph of
  the proof.
* `Schoenflies.exists_stripData` — the same without a prescribed open set.
* `Schoenflies.ClosedPolygon.exists_cone_radius`,
  `Schoenflies.ClosedPolygon.exists_half_width` — steps 1 and 3 of the recipe, which are the
  instances of Lemma 1.4 that Lemma 1.8 consumes.
* `Schoenflies.StripData.nbhd_subset_thickening` — the collar of Lemma 1.8 lies in the
  `R`-neighbourhood of the curve, which is how the prescribed open set is honoured.
-/

open Metric Set

namespace Schoenflies

open Plane

variable {m : ℕ}

namespace ClosedPolygon

variable {P : ClosedPolygon m} {i j : ZMod (m + 3)} {c lam : ℝ}

/-! ### Compactness of the pieces -/

theorem isCompact_edge : IsCompact (P.edge i) := isCompact_segment _ _

theorem isCompact_carrier (P : ClosedPolygon m) : IsCompact P.carrier :=
  isCompact_iUnion fun _ => isCompact_edge

theorem continuous_pt (P : ClosedPolygon m) (i : ZMod (m + 3)) : Continuous (P.pt i) := by
  have h : P.pt i = fun c : ℝ => P.vertex i + c • P.tang i := funext fun _ => pt_eq
  rw [h]
  exact continuous_const.add (continuous_id.smul continuous_const)

/-! ### What simplicity gives

The two statements below are the only consumers of `ClosedPolygon.edges_meet` in the whole
choice of constants, and neither is true without it. -/

/-- **Simplicity, first form.** A vertex lies on no edge but the two edges incident to it.
Without this the "a vertex is `2R` away from every nonincident edge" hypothesis of `StripData`
would be unsatisfiable, since the vertex would sit *on* one of those edges. -/
theorem vertex_notMem_edge (hj1 : j ≠ i - 1) (hj2 : j ≠ i) : P.vertex i ∉ P.edge j := by
  intro hx
  -- Use `edges_meet` in the order that puts the *other* edge's endpoints on the right.
  have hmem : P.vertex i ∈ P.edge j ∩ P.edge i := ⟨hx, vertex_mem_edge⟩
  have hsub := P.edges_meet j i hj2 hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hsub
  rcases hsub with h | h
  · exact hj2 (P.vertex_inj h).symm
  · exact hj1 (by rw [P.vertex_inj h]; ring)

/-- The trimmed core of edge `i`: the points of the edge at distance at least `lam` from both
of its endpoints. An edge block of `StripData` hugs this core. -/
def trimmed (P : ClosedPolygon m) (i : ZMod (m + 3)) (lam : ℝ) : Set Plane :=
  P.pt i '' Set.Icc lam (P.len i - lam)

theorem pt_mem_trimmed (hc : c ∈ Set.Icc lam (P.len i - lam)) : P.pt i c ∈ P.trimmed i lam :=
  ⟨c, hc, rfl⟩

theorem isCompact_trimmed : IsCompact (P.trimmed i lam) :=
  isCompact_Icc.image (P.continuous_pt i)

/-- **Simplicity, second form.** The trimmed core of an edge misses every other edge. The two
common points `edges_meet` allows are the endpoints of the edge, and the trim removes them: a
core point is at distance at least `lam` from either endpoint. No lower bound on the edge
length is needed: if the trim eats the whole edge the core is empty. -/
theorem trimmed_disjoint_edge (hlam : 0 < lam) (hij : j ≠ i) :
    Disjoint (P.trimmed i lam) (P.edge j) := by
  rw [Set.disjoint_left]
  rintro x ⟨c, hc, rfl⟩ hx
  have hc0 : (0 : ℝ) ≤ c := le_trans hlam.le hc.1
  have hcl : c ≤ P.len i := le_trans hc.2 (by linarith)
  have hmem : P.pt i c ∈ P.edge i ∩ P.edge j := ⟨pt_mem_edge ⟨hc0, hcl⟩, hx⟩
  have hsub := P.edges_meet i j (Ne.symm hij) hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hsub
  rcases hsub with h | h
  · -- The core point is the initial vertex, so its progress is `0`, below the trim.
    have h0 : |c| = 0 := by rw [← dist_pt_vertex (P := P) (i := i) (c := c), h, dist_self]
    rw [abs_of_nonneg hc0] at h0
    linarith [hc.1]
  · -- The core point is the terminal vertex, so its progress is `len i`, above the trim.
    have h0 : |c| = P.len i := by
      rw [← dist_pt_vertex (P := P) (i := i) (c := c), h, len, dist_eq_norm]
    rw [abs_of_nonneg hc0] at h0
    linarith [hc.2]

end ClosedPolygon

/-! ## Where the collar lives

The collar sits inside the `R`-neighbourhood of the curve: a sector is inside a ball of radius
`R` about a point of the curve, and a block is within `rho < R` of the foot of its
perpendicular, which is on the curve. This is the whole content of "the neighbourhoods may be
chosen inside any prescribed open set containing the curve". -/

namespace StripData

variable {P : ClosedPolygon m} (D : StripData P)

/-- The collar of `Strip.lean` lies in the `R`-neighbourhood of the polygon. -/
theorem nbhd_subset_thickening : D.nbhd ⊆ thickening D.R P.carrier := by
  intro x hx
  have hx' : x ∈ D.sideL ∪ D.sideR ∪ P.carrier := hx
  rcases hx' with (hL | hR) | hc
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hL
    rcases hi with hi | hi
    · exact mem_thickening_iff.2 ⟨P.vertex i, ClosedPolygon.vertex_mem_carrier, hi.2⟩
    · obtain ⟨c, hcmem, hd⟩ := D.exists_foot (Or.inl hi)
      exact mem_thickening_iff.2 ⟨P.pt i c,
        ClosedPolygon.edge_subset_carrier (D.pt_mem_edge_of_trim hcmem), lt_trans hd D.rho_lt_R⟩
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hR
    rcases hi with hi | hi
    · exact mem_thickening_iff.2 ⟨P.vertex i, ClosedPolygon.vertex_mem_carrier, hi.2⟩
    · obtain ⟨c, hcmem, hd⟩ := D.exists_foot (Or.inr hi)
      exact mem_thickening_iff.2 ⟨P.pt i c,
        ClosedPolygon.edge_subset_carrier (D.pt_mem_edge_of_trim hcmem), lt_trans hd D.rho_lt_R⟩
  · exact self_subset_thickening D.R_pos _ hc

end StripData

/-! ## Choosing the constants -/

namespace ClosedPolygon

/-- **Step 1: the cone radius.** One positive `R` that is below every edge length, that
separates the vertices pairwise with a factor `2` to spare, that keeps every vertex `2R` away
from every nonincident edge, and whose neighbourhood of the curve stays inside the prescribed
open set. -/
theorem exists_cone_radius (P : ClosedPolygon m) {U : Set Plane} (hU : IsOpen U)
    (hPU : P.carrier ⊆ U) :
    ∃ R > 0, (∀ i, R ≤ P.len i) ∧
      (∀ i j, i ≠ j → 2 * R ≤ dist (P.vertex i) (P.vertex j)) ∧
      (∀ i j, j ≠ i - 1 → j ≠ i → ∀ y ∈ P.edge j, 2 * R ≤ dist (P.vertex i) y) ∧
      thickening R P.carrier ⊆ U := by
  -- (1) below every edge length
  obtain ⟨e₁, he₁, hlen⟩ :=
    exists_pos_le_of_finite (Set.finite_univ (α := ZMod (m + 3))) (f := fun i => P.len i)
      (fun _ _ => len_pos)
  -- (2) the pairwise vertex separations: distinct vertices are distinct points
  have h₂ : ∃ ε > 0, ∀ p : ZMod (m + 3) × ZMod (m + 3), p ∈ (Set.univ : Set _) →
      (p.1 ≠ p.2 → ε ≤ dist (P.vertex p.1) (P.vertex p.2)) := by
    refine exists_pos_forall_of_finite Set.finite_univ ?_ ?_
    · intro _ δ ε _ hδε h hne
      exact le_trans hδε (h hne)
    · rintro ⟨i, j⟩ -
      by_cases hij : i = j
      · exact ⟨1, one_pos, fun h => absurd hij h⟩
      · exact ⟨dist (P.vertex i) (P.vertex j),
          dist_pos.2 fun h => hij (P.vertex_inj h), fun _ => le_refl _⟩
  -- (3) a vertex against the edges it is not incident to: simplicity makes them disjoint
  have h₃ : ∃ ε > 0, ∀ p : ZMod (m + 3) × ZMod (m + 3), p ∈ (Set.univ : Set _) →
      (p.2 ≠ p.1 - 1 → p.2 ≠ p.1 → ∀ y ∈ P.edge p.2, ε ≤ dist (P.vertex p.1) y) := by
    refine exists_pos_forall_of_finite Set.finite_univ ?_ ?_
    · intro _ δ ε _ hδε h h1 h2 y hy
      exact le_trans hδε (h h1 h2 y hy)
    · rintro ⟨i, j⟩ -
      by_cases hj1 : j = i - 1
      · exact ⟨1, one_pos, fun h => absurd hj1 h⟩
      by_cases hj2 : j = i
      · exact ⟨1, one_pos, fun _ h => absurd hj2 h⟩
      · obtain ⟨ρ, hρ, hsep⟩ := Plane.exists_dist_pos isCompact_singleton isCompact_edge
          (Set.disjoint_singleton_left.2 (vertex_notMem_edge hj1 hj2))
        exact ⟨ρ, hρ, fun _ _ y hy => hsep _ rfl y hy⟩
  -- (4) the prescribed open set
  obtain ⟨e₄, he₄, hthick⟩ := Plane.exists_thickening_subset (isCompact_carrier P) hU hPU
  obtain ⟨e₂, he₂, hvv⟩ := h₂
  obtain ⟨e₃, he₃, hve⟩ := h₃
  refine ⟨min (min e₁ (e₂ / 2)) (min (e₃ / 2) e₄),
    lt_min (lt_min he₁ (by linarith)) (lt_min (by linarith) he₄), fun i => ?_, ?_, ?_, ?_⟩
  · exact le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (hlen i (Set.mem_univ i))
  · intro i j hij
    have h := hvv (i, j) (Set.mem_univ _) hij
    have : min (min e₁ (e₂ / 2)) (min (e₃ / 2) e₄) ≤ e₂ / 2 :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    linarith
  · intro i j hj1 hj2 y hy
    have h := hve (i, j) (Set.mem_univ _) hj1 hj2 y hy
    have : min (min e₁ (e₂ / 2)) (min (e₃ / 2) e₄) ≤ e₃ / 2 :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  · exact subset_trans
      (thickening_mono (le_trans (min_le_right _ _) (min_le_right _ _)) _) hthick

/-- The germ threshold at a single vertex. The corner condition makes `det ≠ 0`, so the right
side is positive and the inequality is a genuine upper bound on the half-width. -/
theorem exists_germ_bound (P : ClosedPolygon m) (i : ZMod (m + 3)) {lam : ℝ} (hlam : 0 < lam) :
    ∃ ε > 0, ε * (1 + |inner ℝ (P.rayIn i) (P.tang i)|) ≤
      lam * |det (P.rayIn i) (P.tang i)| := by
  have hb : 0 < |det (P.rayIn i) (P.tang i)| := abs_pos.2 det_rays_ne_zero
  have ha : 0 < 1 + |inner ℝ (P.rayIn i) (P.tang i)| := by
    have := abs_nonneg (inner ℝ (P.rayIn i) (P.tang i)); linarith
  refine ⟨lam * |det (P.rayIn i) (P.tang i)| / (1 + |inner ℝ (P.rayIn i) (P.tang i)|),
    div_pos (mul_pos hlam hb) ha, le_of_eq ?_⟩
  field_simp

/-- **Step 3: the half-width.** One positive `rho` below `lam`, separating each trimmed edge
from every other edge with a factor `2` to spare, and meeting the germ threshold at every
vertex. Only `0 < lam` is needed: if `lam` were so large that a trimmed edge came out empty,
its separation clause would be vacuous. -/
theorem exists_half_width (P : ClosedPolygon m) {lam : ℝ} (hlam : 0 < lam) :
    ∃ rho > 0, rho < lam ∧
      (∀ i j, j ≠ i → ∀ c ∈ Set.Icc lam (P.len i - lam), ∀ y ∈ P.edge j,
        2 * rho ≤ dist (P.pt i c) y) ∧
      (∀ i, rho * (1 + |inner ℝ (P.rayIn i) (P.tang i)|) ≤
        lam * |det (P.rayIn i) (P.tang i)|) := by
  -- (1) each trimmed edge against every other edge: two disjoint compact sets
  have h₁ : ∃ ε > 0, ∀ p : ZMod (m + 3) × ZMod (m + 3), p ∈ (Set.univ : Set _) →
      (p.2 ≠ p.1 → ∀ x ∈ P.trimmed p.1 lam, ∀ y ∈ P.edge p.2, ε ≤ dist x y) := by
    refine exists_pos_forall_of_finite Set.finite_univ ?_ ?_
    · intro _ δ ε _ hδε h hne x hx y hy
      exact le_trans hδε (h hne x hx y hy)
    · rintro ⟨i, j⟩ -
      by_cases hij : j = i
      · exact ⟨1, one_pos, fun h => absurd hij h⟩
      · obtain ⟨ρ, hρ, hsep⟩ := Plane.exists_dist_pos isCompact_trimmed isCompact_edge
          (trimmed_disjoint_edge hlam hij)
        exact ⟨ρ, hρ, fun _ => hsep⟩
  -- (2) the germ threshold at every vertex
  have h₂ : ∃ ε > 0, ∀ i : ZMod (m + 3), i ∈ (Set.univ : Set _) →
      ε * (1 + |inner ℝ (P.rayIn i) (P.tang i)|) ≤ lam * |det (P.rayIn i) (P.tang i)| := by
    refine exists_pos_forall_of_finite Set.finite_univ ?_ ?_
    · intro i δ ε _ hδε h
      have hnn : (0 : ℝ) ≤ 1 + |inner ℝ (P.rayIn i) (P.tang i)| := by
        have := abs_nonneg (inner ℝ (P.rayIn i) (P.tang i)); linarith
      nlinarith
    · intro i _
      exact P.exists_germ_bound i hlam
  obtain ⟨ε₁, hε₁, htrim⟩ := h₁
  obtain ⟨ε₂, hε₂, hgerm⟩ := h₂
  refine ⟨min (min (ε₁ / 2) ε₂) (lam / 2),
    lt_min (lt_min (by linarith) hε₂) (by linarith), ?_, ?_, ?_⟩
  · exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  · intro i j hij c hc y hy
    have h := htrim (i, j) (Set.mem_univ _) hij _ (pt_mem_trimmed hc) y hy
    have hm : min (min (ε₁ / 2) ε₂) (lam / 2) ≤ ε₁ / 2 :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  · intro i
    have h := hgerm i (Set.mem_univ _)
    have hnn : (0 : ℝ) ≤ 1 + |inner ℝ (P.rayIn i) (P.tang i)| := by
      have := abs_nonneg (inner ℝ (P.rayIn i) (P.tang i)); linarith
    have hm : min (min (ε₁ / 2) ε₂) (lam / 2) ≤ ε₂ :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    nlinarith

end ClosedPolygon

open ClosedPolygon

/-- **Lemma 1.8, the constants.** Every simple closed polygon carries a `StripData`, and its
collar can be put inside any prescribed open set containing the curve. This is what makes
`Schoenflies/Strip.lean` with the required constants supplied. -/
theorem exists_stripData_subset (P : ClosedPolygon m) {U : Set Plane} (hU : IsOpen U)
    (hPU : P.carrier ⊆ U) : ∃ D : StripData P, D.nbhd ⊆ U := by
  obtain ⟨R, hR, hRlen, hRvv, hRve, hRU⟩ := P.exists_cone_radius hU hPU
  have hlam : (0 : ℝ) < R / 5 := by linarith
  have hlen4 : ∀ i, 4 * (R / 5) < P.len i := fun i => by have := hRlen i; linarith
  obtain ⟨rho, hrho, hrl, htrim, hgerm⟩ := P.exists_half_width hlam
  refine ⟨⟨R, R / 5, rho, hrho, hrl, by linarith, hlen4, hRlen, hRvv, hRve, htrim, hgerm⟩, ?_⟩
  exact subset_trans (StripData.nbhd_subset_thickening _) hRU

/-- Every simple closed polygon carries a `StripData`. -/
theorem exists_stripData (P : ClosedPolygon m) : Nonempty (StripData P) :=
  ⟨(exists_stripData_subset P isOpen_univ (subset_univ _)).choose⟩

end Schoenflies

end BundlePart407
