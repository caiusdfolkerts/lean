module

public import canonical_main.PalomarPart007
import all canonical_main.PalomarPart007
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

section BundlePart413
/- Source: dev/planar_search/schoenflies_port/Schoenflies/PolygonalCrosscut.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/


/-!
# Theorem 2.8: two-sided polygonal crosscuts

A crosscut `P` of a simple closed polygon `C` cuts one of the two regions of `ℝ² ∖ C` into
exactly two, bounded by the two curves `Jᵢ = Aᵢ ∪ P`; and `ℝ² ∖ (C ∪ P)` then has exactly three
regions, with boundaries `C, J₁, J₂`.

## One theorem, not two

The blueprint splits the statement into case (a), the crosscut inside `C`, and case (b), the
crosscut outside. The two cases differ only in *which* region of `ℝ² ∖ Jᵢ` is the new cell: in
case (a) it is `Int(Jᵢ)` for both `i`, while in case (b) it is `Ext(J₁)` for one index and
`Int(J₂)` for the other, and which is which is not determined by the data. What *is* uniform is
the description "the region of `ℝ² ∖ Jᵢ` on the far side from a point `y` of the region of
`ℝ² ∖ C` that the crosscut does not enter". So the whole theorem is proved once, for

    farRegion J y  =  the region of `ℝ² ∖ J` that does not contain `y`,

and the two cases of the blueprint are then read off by identifying `farRegion` with `inside`
or with `outside` (`IsSeparating.farRegion_eq_inside`, `…_eq_outside`). A reference point `y`
in the untouched region is the one extra datum this costs, and it is exactly the datum the
blueprint hides in the phrase "let `Ω` be the region containing `P ∖ {p, q}`".

## Exhaustion is pure parity, in both cases at once

Lemma 2.6 (`Schoenflies.crosscut_cells`) already exhibits the two cells as components of
`Ω ∖ P`. All that Theorem 2.8 adds is that there are no others, and the blueprint reads this
off Lemma 2.7. Here the reading is uniform. Write `πJ` for the crossing count of a curve `J`.
For points `x, y` off `J` — Theorem 2.3 —

    `x` and `y` lie in different regions of `ℝ² ∖ J`  ↔  `πJ(x) ≠ πJ(y)`,

which is `ClosedPolygon.parity_ne_iff_mem_farRegion`. Lemma 2.7 gives
`πJ₁ + πJ₂ = πC` at every point, so subtracting the identity at `y` from the identity at `x`
turns "`x` is separated from `y` by `C`" into "`x` is separated from `y` by exactly one of
`J₁, J₂`" — `IsPolygonalCrosscut.separates_xor`, whose entire proof is sixteen cases of `ZMod 2`
arithmetic. No case distinction on inside/outside is made anywhere.

## The hypotheses, bundled

`IsPolygonalCrosscut C J₁ J₂ K a k y` collects the seven hypotheses of the theorem: the two
curves of the split carry the right edges (`Schoenflies.SameEdges`, from Lemma 2.7), the
crosscut meets `C` only in points common to both arcs, and the reference point `y` lies off `C`
in a region the crosscut does not enter. It is closed under swapping the two arcs
(`IsPolygonalCrosscut.symm`), which is why every statement below is proved for index `1` only.

Realizing `J₁` and `J₂` as `ClosedPolygon`s is the consumer's job, exactly as in Lemma 2.7 —
see the note there about the `corner` field. Nothing in this file inspects `corner`.

## Blueprint

* `farRegion`, `IsSeparating.isRegionPair_farRegion`, `IsSeparating.farRegion_eq_inside`,
  `IsSeparating.farRegion_eq_outside` — the blueprint's `Ω`, `Ω†`, `Vᵢ` and `Wᵢ` named as
  functions of a reference point instead of by an existential.
* `ClosedPolygon.arc` — the arcs `A₁, A₂` of Theorem 2.8, as sets; `…vertex_mem_arc`,
  `…vertex_add_mem_arc`, `…endpoints_subset_arc`, `…endpoints_subset_arc'` — the two cut
  vertices lie on both arcs, which is what "the crosscut meets `C` only in its endpoints" has
  to say to be usable.
* `ClosedPolygon.parity_ne_iff_mem_farRegion` — Theorem 2.3 read as a separation criterion.
* `IsPolygonalCrosscut` — the hypotheses of Theorem 2.8; `IsPolygonalCrosscut.of_endpoints` is
  the constructor a consumer should use, and `IsPolygonalCrosscut.symm` swaps the two arcs.
* `IsPolygonalCrosscut.separates_xor` — Lemma 2.7's "consequently", in the uniform form.
* `IsPolygonalCrosscut.region_eq`, `…cells_disjoint`, `…cells_ne`, `…cell_isComponent₁/₂`,
  `…frontier_cell₁/₂`, `…closure_cell_inter₁/₂` — the two cells of `Ω ∖ P`.
* `IsPolygonalCrosscut.inside_diff_eq` — Theorem 2.8(a).
* `IsPolygonalCrosscut.outside_diff_eq`, `…inside_exactly_one` — Theorem 2.8(b).
* `IsPolygonalCrosscut.compl_eq`, `…isComponent`, `…near_isComponent`,
  `…cell_isComponent_compl₁/₂`, `…cell_ne_near₁/₂`, `…frontier_near` — "in either case
  `ℝ² ∖ (C ∪ P)` has exactly three regions, with boundaries `C, J₁, J₂`".
* `polygonal_crosscut` — Theorem 2.8, bundled.
-/

open Bornology Set

namespace Schoenflies

variable {C J P Ω Ω' W V : Set Plane} {x y z : Plane}

/-! ## The region on the far side of a point

The blueprint names the four regions in play — `Ω`, `Ω†`, `Wᵢ`, `Vᵢ` — by their relation to one
another: `Ω†` is the region of `ℝ² ∖ C` the crosscut does not enter, and `Vᵢ` is the region of
`ℝ² ∖ Jᵢ` on the other side of `Jᵢ` from `Ω†`. Fixing a point `y ∈ Ω†` turns all four into
functions of the data. -/

/-- The region of `ℝ² ∖ C` that does **not** contain `y`: everything off `C` except the
component of `y`. For a separating curve this really is the other region
(`IsSeparating.isRegionPair_farRegion`); no hypothesis is needed to define it. -/
def farRegion (C : Set Plane) (y : Plane) : Set Plane := Cᶜ \ connectedComponentIn Cᶜ y

theorem mem_farRegion_iff : x ∈ farRegion C y ↔ x ∉ C ∧ x ∉ connectedComponentIn Cᶜ y := Iff.rfl

theorem farRegion_subset_compl : farRegion C y ⊆ Cᶜ := fun _ hx => hx.1

theorem notMem_farRegion_self (hy : y ∉ C) : y ∉ farRegion C y :=
  fun h => h.2 (mem_connectedComponentIn hy)

/-- Off the curve, being in the far region is exactly being in another component. -/
theorem mem_farRegion_iff_connectedComponentIn_ne (hx : x ∉ C) :
    x ∈ farRegion C y ↔ connectedComponentIn Cᶜ x ≠ connectedComponentIn Cᶜ y := by
  refine ⟨fun h hEq => h.2 (hEq ▸ mem_connectedComponentIn hx), fun h => ⟨hx, fun hmem => ?_⟩⟩
  exact h (connectedComponentIn_eq hmem).symm

/-- The crosscut misses the region of `y`, so all of it off the curve is in the far region. -/
theorem diff_subset_farRegion (hdis : Disjoint P (connectedComponentIn Cᶜ y)) :
    P \ C ⊆ farRegion C y :=
  fun _ hz => ⟨hz.2, fun hmem => Set.disjoint_left.1 hdis hz.1 hmem⟩

theorem compl_diff_inside (C : Set Plane) : Cᶜ \ inside C = outside C := by
  ext w
  constructor
  · rintro ⟨hw, hwin⟩
    have hcov : w ∈ inside C ∪ outside C := by rw [inside_union_outside]; exact hw
    exact hcov.resolve_left hwin
  · exact fun hw => ⟨hw.1, fun h => Set.disjoint_left.1 disjoint_inside_outside h hw⟩

theorem compl_diff_outside (C : Set Plane) : Cᶜ \ outside C = inside C := by
  ext w
  constructor
  · rintro ⟨hw, hwout⟩
    have hcov : w ∈ inside C ∪ outside C := by rw [inside_union_outside]; exact hw
    exact hcov.resolve_right hwout
  · exact fun hw => ⟨hw.1, fun h => Set.disjoint_left.1 disjoint_inside_outside hw h⟩

/-- The component of `y` and the far region are *the* two regions of `ℝ² ∖ C`. -/
theorem IsSeparating.isRegionPair_farRegion (hC : IsSeparating C) (hy : y ∉ C) :
    IsRegionPair C (connectedComponentIn Cᶜ y) (farRegion C y) := by
  rcases hC.isRegionOf_connectedComponentIn hy with hc | hc
  · exact Or.inl ⟨hc, by rw [farRegion, hc, compl_diff_inside]⟩
  · exact Or.inr ⟨hc, by rw [farRegion, hc, compl_diff_outside]⟩

theorem IsSeparating.isRegionOf_farRegion (hC : IsSeparating C) (hy : y ∉ C) :
    IsRegionOf C (farRegion C y) := (hC.isRegionPair_farRegion hy).right

/-- Seen from the unbounded region, the far region is the bounded one — the blueprint's case
(a), where `Vᵢ = Int(Jᵢ)`. -/
theorem IsSeparating.farRegion_eq_inside (hC : IsSeparating C) (hy : y ∈ outside C) :
    farRegion C y = inside C := by
  rw [farRegion, hC.connectedComponentIn_eq_outside hy, compl_diff_outside]

/-- Seen from the bounded region, the far region is the unbounded one. -/
theorem IsSeparating.farRegion_eq_outside (hC : IsSeparating C) (hy : y ∈ inside C) :
    farRegion C y = outside C := by
  rw [farRegion, hC.connectedComponentIn_eq_inside hy, compl_diff_inside]

/-! ## The three regions of `ℝ² ∖ (C ∪ P)`, abstractly

Lemma 2.6 places the two cells inside `Ω ∖ P`; the last paragraph of the proof of Theorem 2.8
places all three regions inside `ℝ² ∖ (C ∪ P)`, and the argument is the same each time: an open
connected set whose frontier misses the ambient open set is a component of it (Lemma 1.7). -/

/-- `ℝ² ∖ (C ∪ P)` is `Ω ∖ P` together with the untouched region `Ω'`. -/
theorem compl_union_eq_of_isRegionPair (hΩ : IsRegionPair C Ω Ω') (hdis : Disjoint P Ω') :
    (C ∪ P)ᶜ = (Ω \ P) ∪ Ω' := by
  ext w
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_sdiff, not_or]
  constructor
  · rintro ⟨hwC, hwP⟩
    have hcov : w ∈ Ω ∪ Ω' := by rw [hΩ.union_eq]; exact hwC
    exact hcov.imp (fun h => ⟨h, hwP⟩) id
  · rintro (⟨hwΩ, hwP⟩ | hwΩ')
    · exact ⟨hΩ.left.subset_compl hwΩ, hwP⟩
    · exact ⟨hΩ.right.subset_compl hwΩ', fun hwP => Set.disjoint_left.1 hdis hwP hwΩ'⟩

/-- The untouched region is a component of `ℝ² ∖ (C ∪ P)`: its frontier is `C`. -/
theorem far_isComponent (hC : IsSeparating C) (hΩ : IsRegionPair C Ω Ω')
    (hdis : Disjoint P Ω') (hz : z ∈ Ω') : connectedComponentIn (C ∪ P)ᶜ z = Ω' := by
  refine Plane.connectedComponentIn_eq_of_frontier_disjoint (hΩ.right.isOpen hC)
    (hΩ.right.isConnected hC).isPreconnected (fun w hw => ?_) ?_ hz
  · rintro (h | h)
    · exact hΩ.right.subset_compl hw h
    · exact Set.disjoint_left.1 hdis h hw
  · rw [hΩ.right.frontier_eq hC]
    refine Set.eq_empty_iff_forall_notMem.2 ?_
    rintro w ⟨hwC, hw⟩
    exact hw (Or.inl hwC)

/-- A cell is a component of `ℝ² ∖ (C ∪ P)`: its frontier is `J ⊆ C ∪ P`. -/
theorem cell_isComponent_compl (hJ : IsSeparating J) (hWV : IsRegionPair J W V)
    (hJCP : J ⊆ C ∪ P) (hV : V ⊆ (C ∪ P)ᶜ) (hz : z ∈ V) :
    connectedComponentIn (C ∪ P)ᶜ z = V := by
  refine Plane.connectedComponentIn_eq_of_frontier_disjoint (hWV.right.isOpen hJ)
    (hWV.right.isConnected hJ).isPreconnected hV ?_ hz
  rw [hWV.right.frontier_eq hJ]
  refine Set.eq_empty_iff_forall_notMem.2 ?_
  rintro w ⟨hwJ, hw⟩
  exact hw (hJCP hwJ)

/-! ## The arcs of a polygon, and parity as a separation criterion -/

/-- Going `k` steps forward and then the remaining `m + 3 - k` returns to where one started:
the second arc of a split ends at the first arc's starting vertex. -/
theorem zmod_add_sub_cancel {m k : ℕ} (hk : k ≤ m + 3) (a : ZMod (m + 3)) :
    a + (k : ZMod (m + 3)) + ((m + 3 - k : ℕ) : ZMod (m + 3)) = a := by
  have hcast : ((k : ℕ) : ZMod (m + 3)) + ((m + 3 - k : ℕ) : ZMod (m + 3)) = 0 := by
    rw [← Nat.cast_add, show k + (m + 3 - k) = m + 3 by omega]
    exact ZMod.natCast_self _
  rw [add_assoc, hcast, add_zero]

namespace ClosedPolygon

variable {m : ℕ} {C : ClosedPolygon m} {a : ZMod (m + 3)} {k : ℕ}

/-- The arc of `C` that leaves vertex `a` and runs forward through `k` edges, as a set: the
blueprint's `A₁` for `k` edges and `A₂` for the remaining `m + 3 - k`. -/
def arc (C : ClosedPolygon m) (a : ZMod (m + 3)) (k : ℕ) : Set Plane := cover (C.arcPieces a k)

theorem arc_subset_carrier (C : ClosedPolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    C.arc a k ⊆ C.carrier := cover_arcPieces_subset C a k

/-- The two arcs cover the polygon. -/
theorem arc_union (C : ClosedPolygon m) (a : ZMod (m + 3)) (hk : k ≤ m + 3) :
    C.arc a k ∪ C.arc (a + k) (m + 3 - k) = C.carrier := cover_arcPieces_union C a hk

/-- A curve of the split occupies its arc together with the crosscut. -/
theorem carrier_eq_arc_union {m' : ℕ} {J : ClosedPolygon m'} {K : List Piece}
    (h : SameEdges J.pieces (C.arcPieces a k ++ K)) : J.carrier = C.arc a k ∪ cover K :=
  carrier_eq_of_sameEdges h

/-- **The crossing count separates points exactly as the polygon does** (Theorem 2.3, read as a
criterion). Two points off the polygon lie in different regions precisely when their crossing
counts differ: equal components force equal counts by Lemma 2.2, and different components are
the bounded and the unbounded one, whose counts are `1` and `0`. -/
theorem parity_ne_iff_mem_farRegion (C : ClosedPolygon m) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ C.pieces, hgt u Q.1 ≠ hgt u Q.2) {x y : Plane}
    (hx : x ∉ C.carrier) (hy : y ∉ C.carrier) :
    parity u C.pieces x ≠ parity u C.pieces y ↔ x ∈ farRegion C.carrier y := by
  rw [mem_farRegion_iff_connectedComponentIn_ne hx]
  constructor
  · intro hne heq
    exact hne (C.parity_eq_of_mem_connectedComponentIn_carrier hu hL hy
      (heq ▸ mem_connectedComponentIn hx))
  · intro hne
    rcases C.connectedComponentIn_eq_inside_or_outside hx with hxr | hxr <;>
      rcases C.connectedComponentIn_eq_inside_or_outside hy with hyr | hyr
    · exact absurd (hxr.trans hyr.symm) hne
    · rw [C.parity_eq_one_of_mem_inside hu hL (hxr ▸ mem_connectedComponentIn hx),
        C.parity_eq_zero_of_mem_outside hu hL (hyr ▸ mem_connectedComponentIn hy)]
      decide
    · rw [C.parity_eq_zero_of_mem_outside hu hL (hxr ▸ mem_connectedComponentIn hx),
        C.parity_eq_one_of_mem_inside hu hL (hyr ▸ mem_connectedComponentIn hy)]
      decide
    · exact absurd (hxr.trans hyr.symm) hne

/-- The first vertex of a nonempty arc lies on it. -/
theorem vertex_mem_arc (C : ClosedPolygon m) (a : ZMod (m + 3)) (hk : 1 ≤ k) :
    C.vertex a ∈ C.arc a k := by
  have h0 : a + ((0 : ℕ) : ZMod (m + 3)) = a := by rw [Nat.cast_zero, add_zero]
  refine mem_cover (P := (C.vertex a, C.vertex (a + 1))) ?_ ?_
  · exact List.mem_map.2 ⟨0, List.mem_range.2 hk, by rw [h0]⟩
  · exact left_mem_segment ℝ _ _

/-- The last vertex of a nonempty arc lies on it. -/
theorem vertex_add_mem_arc (C : ClosedPolygon m) (a : ZMod (m + 3)) (hk : 1 ≤ k) :
    C.vertex (a + k) ∈ C.arc a k := by
  have hlast : a + ((k - 1 : ℕ) : ZMod (m + 3)) + 1 = a + (k : ZMod (m + 3)) := by
    have : ((k - 1 : ℕ) : ZMod (m + 3)) + 1 = ((k : ℕ) : ZMod (m + 3)) := by
      rw [show ((k : ℕ) : ZMod (m + 3)) = (((k - 1) + 1 : ℕ) : ZMod (m + 3)) by
        congr 1; omega, Nat.cast_add, Nat.cast_one]
    rw [add_assoc, this]
  refine mem_cover (P := (C.vertex (a + ((k - 1 : ℕ) : ZMod (m + 3))),
    C.vertex (a + ((k - 1 : ℕ) : ZMod (m + 3)) + 1))) ?_ ?_
  · exact List.mem_map.2 ⟨k - 1, List.mem_range.2 (by omega), rfl⟩
  · rw [Piece.seg, hlast]
    exact right_mem_segment ℝ _ _

/-- **The two cut vertices lie on both arcs.** This is what turns the blueprint's "the crosscut
meets `C` only in its two endpoints" into the hypotheses `meets₁` and `meets₂`. -/
theorem endpoints_subset_arc (C : ClosedPolygon m) (a : ZMod (m + 3)) (hk : 1 ≤ k) :
    ({C.vertex a, C.vertex (a + k)} : Set Plane) ⊆ C.arc a k := by
  rintro w (rfl | rfl)
  · exact C.vertex_mem_arc a hk
  · exact C.vertex_add_mem_arc a hk

/-- The same for the complementary arc, whose two ends are the same two vertices in the other
order. -/
theorem endpoints_subset_arc' (C : ClosedPolygon m) (a : ZMod (m + 3)) (hk2 : k ≤ m + 2) :
    ({C.vertex a, C.vertex (a + k)} : Set Plane) ⊆ C.arc (a + k) (m + 3 - k) := by
  have hpos : 1 ≤ m + 3 - k := by omega
  have hwrap := zmod_add_sub_cancel (k := k) (by omega) a
  rintro w (rfl | rfl)
  · have hm := C.vertex_add_mem_arc (a + k) hpos
    rwa [hwrap] at hm
  · exact C.vertex_mem_arc (a + k) hpos

end ClosedPolygon

/-! ## The hypotheses of Theorem 2.8 -/

variable {m m₁ m₂ : ℕ} {C : ClosedPolygon m} {J₁ : ClosedPolygon m₁} {J₂ : ClosedPolygon m₂}
  {K : List Piece} {a : ZMod (m + 3)} {k : ℕ}

/-- **The setting of Theorem 2.8.** `K` is the edge list of a polygonal crosscut of the polygon
`C`, cutting it at the vertices `a` and `a + k`; `J₁` and `J₂` are the two closed curves formed
by the crosscut with each of the two arcs; and `y` is a point of the region of `ℝ² ∖ C` that the
crosscut does not enter, which is what fixes which side of `C` the crosscut is on.

The blueprint's "`P` is a simple arc meeting `C` exactly in its two endpoints" appears here in
two pieces: `meets₁` and `meets₂` say that whatever the crosscut has in common with `C` lies on
*both* arcs, which for a genuine crosscut is the two cut vertices (`ClosedPolygon.vertex_mem_arc`,
`ClosedPolygon.vertex_add_mem_arc`); and simplicity is carried by the assumption that `J₁` and
`J₂` really are `ClosedPolygon`s. Nothing else about `K` is assumed — not even that its pieces
are nondegenerate, which follows from `edges₁`. -/
structure IsPolygonalCrosscut (C : ClosedPolygon m) (J₁ : ClosedPolygon m₁)
    (J₂ : ClosedPolygon m₂) (K : List Piece) (a : ZMod (m + 3)) (k : ℕ) (y : Plane) : Prop where
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
its two endpoints, and that those endpoints are the two cut vertices; `meets₁` and `meets₂`
follow, because both cut vertices lie on both arcs. The bound `k ≤ m + 2` says the second arc is
nonempty, as `1 ≤ k` says the first one is. -/
theorem IsPolygonalCrosscut.of_endpoints {y : Plane} (hk1 : 1 ≤ k) (hk2 : k ≤ m + 2)
    (edges₁ : SameEdges J₁.pieces (C.arcPieces a k ++ K))
    (edges₂ : SameEdges J₂.pieces (C.arcPieces (a + k) (m + 3 - k) ++ K))
    (meets : cover K ∩ C.carrier ⊆ ({C.vertex a, C.vertex (a + k)} : Set Plane))
    (notMem : y ∉ C.carrier)
    (avoids : Disjoint (cover K) (connectedComponentIn C.carrierᶜ y)) :
    IsPolygonalCrosscut C J₁ J₂ K a k y :=
  ⟨by omega, edges₁, edges₂, meets.trans (C.endpoints_subset_arc a hk1),
    meets.trans (C.endpoints_subset_arc' a hk2), notMem, avoids⟩

namespace IsPolygonalCrosscut

variable {y : Plane} (h : IsPolygonalCrosscut C J₁ J₂ K a k y)
include h

/-- **The two arcs may be swapped.** Every statement below is therefore proved for `J₁` only. -/
theorem symm : IsPolygonalCrosscut C J₂ J₁ K (a + k) (m + 3 - k) y := by
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
  ClosedPolygon.carrier_eq_arc_union h.edges₁

theorem notMem_carrier₁ : y ∉ J₁.carrier :=
  ClosedPolygon.notMem_carrier_of_sameEdges h.edges₁ h.notMem h.notMem_cover

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

/-! ### The two cells

Lemma 2.6 applies with `Ω = farRegion C.carrier y`, `Ω' = connectedComponentIn C.carrierᶜ y`,
`Wᵢ = connectedComponentIn Jᵢ.carrierᶜ y` and `Vᵢ = farRegion Jᵢ.carrier y`. The inclusion
`Ω' ⊆ Wᵢ` — the blueprint's "being connected it lies in one region of `ℝ² ∖ Jᵢ`" — is
`near_subset₁`, and needs no separation hypothesis at all. -/

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
  exact ClosedPolygon.notMem_carrier_of_sameEdges h.edges₁ hwC hwK

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

/-- The cell has `J₁` as its frontier. -/
theorem frontier_cell₁ : frontier (farRegion J₁.carrier y) = J₁.carrier :=
  h.regionPair₁.right.frontier_eq J₁.isSeparating_carrier

theorem frontier_cell₂ : frontier (farRegion J₂.carrier y) = J₂.carrier :=
  h.symm.frontier_cell₁

theorem cell_nonempty₁ : (farRegion J₁.carrier y).Nonempty :=
  (h.regionPair₁.right.isConnected J₁.isSeparating_carrier).nonempty

/-! ### Exhaustion: the crossing counts add up

This is the whole of Theorem 2.8 beyond Lemma 2.6, and it is one `ZMod 2` computation. -/

/-- **A point off `C ∪ P` is separated from `y` by `C` exactly when it is separated from `y` by
exactly one of `J₁, J₂`.** Lemma 2.7 gives `πJ₁ + πJ₂ = πC` at every point; evaluating it at `x`
and at `y` and subtracting turns the three "different region" statements — which Theorem 2.3
reads off the three crossing counts — into the exclusive disjunction. -/
theorem separates_xor {x : Plane} (hxC : x ∉ C.carrier) (hxK : x ∉ cover K) :
    x ∈ farRegion C.carrier y ↔
      (x ∈ farRegion J₁.carrier y ↔ ¬ x ∈ farRegion J₂.carrier y) := by
  obtain ⟨u, hu, hlevC, hlevK⟩ := h.exists_direction
  have hlev₁ := h.edges₁.hgt_ne (ClosedPolygon.arcPieces_append_hgt_ne hlevC hlevK)
  have hlev₂ := h.edges₂.hgt_ne (ClosedPolygon.arcPieces_append_hgt_ne hlevC hlevK)
  have hxJ₁ := ClosedPolygon.notMem_carrier_of_sameEdges h.edges₁ hxC hxK
  have hxJ₂ := ClosedPolygon.notMem_carrier_of_sameEdges h.edges₂ hxC hxK
  rw [← C.parity_ne_iff_mem_farRegion hu hlevC hxC h.notMem,
    ← J₁.parity_ne_iff_mem_farRegion hu hlev₁ hxJ₁ h.notMem_carrier₁,
    ← J₂.parity_ne_iff_mem_farRegion hu hlev₂ hxJ₂ h.symm.notMem_carrier₁]
  have hsx := C.parity_splitting u a h.le h.edges₁ h.edges₂ x
  have hsy := C.parity_splitting u a h.le h.edges₁ h.edges₂ y
  have key : ∀ s₁ s₂ s t₁ t₂ t : ZMod 2, s₁ + s₂ = s → t₁ + t₂ = t →
      (s ≠ t ↔ ((s₁ ≠ t₁) ↔ ¬ (s₂ ≠ t₂))) := by decide
  exact key _ _ _ _ _ _ hsx hsy

/-- **Theorem 2.8, the two cells.** The region the crosscut enters, with the crosscut removed,
is the disjoint union of the two cells. -/
theorem region_eq :
    farRegion C.carrier y \ cover K = farRegion J₁.carrier y ∪ farRegion J₂.carrier y := by
  refine Set.Subset.antisymm ?_ (Set.union_subset h.cell_subset₁ h.cell_subset₂)
  rintro w ⟨hwΩ, hwK⟩
  by_cases hw₁ : w ∈ farRegion J₁.carrier y
  · exact Or.inl hw₁
  · refine Or.inr ?_
    by_contra hw₂
    exact hw₁ (((h.separates_xor hwΩ.1 hwK).1 hwΩ).2 hw₂)

theorem cells_disjoint : Disjoint (farRegion J₁.carrier y) (farRegion J₂.carrier y) := by
  rw [Set.disjoint_left]
  intro w hw₁ hw₂
  obtain ⟨hwΩ, hwK⟩ := h.cell_subset₁ hw₁
  exact ((h.separates_xor hwΩ.1 hwK).1 hwΩ).1 hw₁ hw₂

theorem cells_ne : farRegion J₁.carrier y ≠ farRegion J₂.carrier y := by
  intro heq
  obtain ⟨w, hw⟩ := h.cell_nonempty₁
  exact Set.disjoint_left.1 h.cells_disjoint hw (heq ▸ hw)

/-- A cell is not the untouched region: it lies on the other side of `C`. -/
theorem cell_ne_near₁ : farRegion J₁.carrier y ≠ connectedComponentIn C.carrierᶜ y := by
  intro heq
  obtain ⟨w, hw⟩ := h.cell_nonempty₁
  exact Set.disjoint_left.1 h.regionPairC.disjoint (h.cell_subset₁ hw).1 (heq ▸ hw)

theorem cell_ne_near₂ : farRegion J₂.carrier y ≠ connectedComponentIn C.carrierᶜ y :=
  h.symm.cell_ne_near₁

/-! ### The three regions of `ℝ² ∖ (C ∪ P)` -/

theorem cell_subset_compl₁ : farRegion J₁.carrier y ⊆ (C.carrier ∪ cover K)ᶜ := by
  intro w hw
  obtain ⟨hwΩ, hwK⟩ := h.cell_subset₁ hw
  rintro (hw' | hw')
  · exact hwΩ.1 hw'
  · exact hwK hw'

/-- The three regions together are the whole of `ℝ² ∖ (C ∪ P)`. -/
theorem compl_eq : (C.carrier ∪ cover K)ᶜ =
    (farRegion J₁.carrier y ∪ farRegion J₂.carrier y) ∪ connectedComponentIn C.carrierᶜ y := by
  rw [← h.region_eq]
  exact compl_union_eq_of_isRegionPair h.regionPairC h.avoids

/-- The untouched region is a component of `ℝ² ∖ (C ∪ P)`, with frontier `C`. -/
theorem near_isComponent {z : Plane} (hz : z ∈ connectedComponentIn C.carrierᶜ y) :
    connectedComponentIn (C.carrier ∪ cover K)ᶜ z = connectedComponentIn C.carrierᶜ y :=
  far_isComponent C.isSeparating_carrier h.regionPairC h.avoids hz

theorem frontier_near :
    frontier (connectedComponentIn C.carrierᶜ y) = C.carrier :=
  h.regionPairC.right.frontier_eq C.isSeparating_carrier

/-- The first cell is a component of `ℝ² ∖ (C ∪ P)`, with frontier `J₁`. -/
theorem cell_isComponent_compl₁ {z : Plane} (hz : z ∈ farRegion J₁.carrier y) :
    connectedComponentIn (C.carrier ∪ cover K)ᶜ z = farRegion J₁.carrier y :=
  cell_isComponent_compl J₁.isSeparating_carrier h.regionPair₁ h.carrier₁_subset
    h.cell_subset_compl₁ hz

theorem cell_isComponent_compl₂ {z : Plane} (hz : z ∈ farRegion J₂.carrier y) :
    connectedComponentIn (C.carrier ∪ cover K)ᶜ z = farRegion J₂.carrier y :=
  h.symm.cell_isComponent_compl₁ hz

/-- **"`ℝ² ∖ (C ∪ P)` has exactly three regions."** Every component is one of the three named
sets, and each of the three is a component (`cell_isComponent_compl₁`, `…₂`,
`near_isComponent`). Their frontiers are `J₁`, `J₂` and `C`. -/
theorem isComponent {z : Plane} (hz : z ∉ C.carrier ∪ cover K) :
    connectedComponentIn (C.carrier ∪ cover K)ᶜ z = farRegion J₁.carrier y ∨
      connectedComponentIn (C.carrier ∪ cover K)ᶜ z = farRegion J₂.carrier y ∨
      connectedComponentIn (C.carrier ∪ cover K)ᶜ z = connectedComponentIn C.carrierᶜ y := by
  have hmem : z ∈ (C.carrier ∪ cover K)ᶜ := hz
  rw [h.compl_eq] at hmem
  rcases hmem with (h₁ | h₂) | h₃
  · exact Or.inl (h.cell_isComponent_compl₁ h₁)
  · exact Or.inr (Or.inl (h.cell_isComponent_compl₂ h₂))
  · exact Or.inr (Or.inr (h.near_isComponent h₃))

/-! ### The blueprint's two cases -/

/-- Seen from the unbounded region of `C`, `J₁` too has `y` outside it: otherwise the unbounded
`Ext(C)` would sit inside the bounded `Int(J₁)`. -/
theorem mem_outside₁ (hy : y ∈ outside C.carrier) : y ∈ outside J₁.carrier := by
  rcases J₁.isSeparating_carrier.isRegionOf_connectedComponentIn h.notMem_carrier₁ with hc | hc
  · refine absurd ?_ C.isSeparating_carrier.not_isBounded_outside
    refine J₁.isSeparating_carrier.isBounded_inside.subset ?_
    rw [← hc, ← C.isSeparating_carrier.connectedComponentIn_eq_outside hy]
    exact h.near_subset₁
  · exact hc ▸ mem_connectedComponentIn h.notMem_carrier₁

theorem cell₁_eq_inside (hy : y ∈ outside C.carrier) :
    farRegion J₁.carrier y = inside J₁.carrier :=
  J₁.isSeparating_carrier.farRegion_eq_inside (h.mem_outside₁ hy)

theorem cell₂_eq_inside (hy : y ∈ outside C.carrier) :
    farRegion J₂.carrier y = inside J₂.carrier :=
  h.symm.cell₁_eq_inside hy

/-- **Theorem 2.8(a).** If the crosscut runs inside `C` — that is, if the reference point `y`
lies in `Ext(C)` — then `Int(C) ∖ P` is exactly the union of the two bounded regions of `J₁` and
`J₂`, and those two are disjoint. -/
theorem inside_diff_eq (hy : y ∈ outside C.carrier) :
    inside C.carrier \ cover K = inside J₁.carrier ∪ inside J₂.carrier := by
  rw [← C.isSeparating_carrier.farRegion_eq_inside hy, ← h.cell₁_eq_inside hy,
    ← h.cell₂_eq_inside hy]
  exact h.region_eq

/-- **Theorem 2.8(b).** If the crosscut runs outside `C` — that is, if `y ∈ Int(C)` — then
`Ext(C) ∖ P` has exactly the two regions `farRegion Jᵢ.carrier y`, whose frontiers are `J₁` and
`J₂` (`frontier_cell₁`, `frontier_cell₂`) and which are components of it
(`cell_isComponent₁`, `…₂`). Which of the two is `Int(Jᵢ)` and which `Ext(Jᵢ)` is settled by
`inside_exactly_one`. -/
theorem outside_diff_eq (hy : y ∈ inside C.carrier) :
    outside C.carrier \ cover K = farRegion J₁.carrier y ∪ farRegion J₂.carrier y := by
  rw [← C.isSeparating_carrier.farRegion_eq_outside hy]
  exact h.region_eq

/-- In case (b), `Int(C)` lies inside exactly one of `J₁, J₂` — the blueprint's "relabel so that
it lies inside `J₁`". -/
theorem inside_exactly_one (hy : y ∈ inside C.carrier) :
    y ∈ inside J₁.carrier ↔ y ∉ inside J₂.carrier := by
  obtain ⟨u, hu, hlevC, hlevK⟩ := h.exists_direction
  exact C.crosscut_inside_exactly_one J₁ J₂ hu hlevC hlevK h.le h.edges₁ h.edges₂ hy
    h.notMem_cover

end IsPolygonalCrosscut

/-- **Theorem 2.8 (two-sided polygonal crosscuts).** Let `C` be a simple closed polygon, `K` the
edge list of a polygonal crosscut cutting it at the vertices `a` and `a + k`, and `J₁, J₂` the
two closed polygons formed by the crosscut with the two arcs. Let `y` be a point of the region
of `ℝ² ∖ C` that the crosscut does not enter, and write `Ω = farRegion C.carrier y` for the
other region and `Vᵢ = farRegion Jᵢ.carrier y` for the region of `ℝ² ∖ Jᵢ` on the far side from
`y`. Then

* `Ω ∖ P` is the disjoint union of `V₁` and `V₂`, which are its two connected components;
* their frontiers are `J₁` and `J₂`, and the closure of `Vᵢ` meets `C` exactly in the arc `Aᵢ`;
* `ℝ² ∖ (C ∪ P)` has exactly three regions, `V₁`, `V₂` and the region of `y`.

Case (a) of the blueprint is `IsPolygonalCrosscut.inside_diff_eq`, which rewrites `Ω` as
`Int(C)` and `Vᵢ` as `Int(Jᵢ)`; case (b) is `IsPolygonalCrosscut.outside_diff_eq`. -/
theorem polygonal_crosscut {y : Plane} (h : IsPolygonalCrosscut C J₁ J₂ K a k y) :
    farRegion C.carrier y \ cover K = farRegion J₁.carrier y ∪ farRegion J₂.carrier y ∧
      Disjoint (farRegion J₁.carrier y) (farRegion J₂.carrier y) ∧
      (∀ z ∈ farRegion J₁.carrier y,
        connectedComponentIn (farRegion C.carrier y \ cover K) z = farRegion J₁.carrier y) ∧
      (∀ z ∈ farRegion J₂.carrier y,
        connectedComponentIn (farRegion C.carrier y \ cover K) z = farRegion J₂.carrier y) ∧
      frontier (farRegion J₁.carrier y) = J₁.carrier ∧
      frontier (farRegion J₂.carrier y) = J₂.carrier ∧
      closure (farRegion J₁.carrier y) ∩ C.carrier = C.arc a k ∧
      closure (farRegion J₂.carrier y) ∩ C.carrier = C.arc (a + k) (m + 3 - k) ∧
      (∀ z ∉ C.carrier ∪ cover K,
        connectedComponentIn (C.carrier ∪ cover K)ᶜ z = farRegion J₁.carrier y ∨
          connectedComponentIn (C.carrier ∪ cover K)ᶜ z = farRegion J₂.carrier y ∨
          connectedComponentIn (C.carrier ∪ cover K)ᶜ z = connectedComponentIn C.carrierᶜ y) :=
  ⟨h.region_eq, h.cells_disjoint, h.cell_isComponent₁, h.cell_isComponent₂, h.frontier_cell₁,
    h.frontier_cell₂, h.closure_cell_inter₁, h.closure_cell_inter₂, fun _ hz => h.isComponent hz⟩

end Schoenflies

end BundlePart413

section BundlePart414
/- Source: dev/planar_search/schoenflies_port/Schoenflies/TwoArcs.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/



/-!
# Two points cut a Jordan curve into two arcs

Two distinct points of a Jordan curve cut it into two arcs between them, which cover the
curve and meet in exactly those two points. This is the converse of
`IsJordanCurve.of_two_arcs`, and the harder direction.

The whole argument is carried by the loop's **parameters**; the circle never appears. Pull the
two points back to parameters `s` and `t` short of the finish — `parameter_before_finish`,
which replaces a parameter at the finish by the start, the only use the closing condition gets
— and order them, say `s < t`. Then the two pieces are what the loop makes of the parameters
*between* `s` and `t` and of the parameters *outside* them:

* the middle piece `f '' Icc s t` is a subarc, produced by `Subarc.lean`'s
  `isArcBetween_subarc`, whose injectivity hypothesis is confined to the traversed interval
  and so survives a loop;
* the outside piece `f '' Icc 0 s ∪ f '' Icc t 1` is two end intervals glued where the loop
  closes up, produced by `Concatenate.lean`'s `IsArcBetween.concatenate`.

That asymmetry — one subarc and one concatenation — is inherent to a parameter interval with
a seam in it, and is not worth fighting. It costs one case split, at `s = 0`, where the front
interval degenerates to a point that the back piece already carries at its far end.

Both halves of the conclusion are then facts about intervals of reals. Covering is the
three-way split of `[0,1]` around two parameters, which is the linearity of the order and
nothing else. Meeting is injectivity off the finish, applied on each of the three pieces; the
one case that needs the loop rather than an arc is an outside parameter *at* the finish, which
carries the same point as the start and so lands back on `s`.

## Blueprint

* `lem:jordan-circle` — "any two distinct points of `C` divide it into two simple arcs having
  exactly those points in common". `IsJordanCurve.two_arcs` is that clause, proved directly
  from the parametrisation instead of through the model curve, so it does not wait on the
  loop-to-circle bridge.
* `IsLoop.two_arcs_at_parameters` — the parameter-level form the clause is assembled from.
-/

open Set unitInterval

namespace Schoenflies

namespace IsLoop

variable {f : ℝ → Plane} {s t : ℝ}

/-! ### Parameters short of the finish

A loop is injective on `[0, 1)` only, so every statement below has to keep its parameters
away from `1`. These two lemmas are the interface to that: one says injectivity holds as soon
as neither parameter is the finish, the other says the finish can always be avoided. -/

/-- Two parameters short of the finish carrying the same point are equal. This is `IsLoop.injOn`
with the half-open interval spelled as "in `[0,1]` and not `1`", which is the form every use
below produces. -/
theorem injective_before_finish (hf : IsLoop f) {u v : ℝ} (hu : u ∈ I) (hv : v ∈ I)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) (h : f u = f v) : u = v :=
  hf.injOn ⟨hu.1, hu.2.lt_of_ne hu1⟩ ⟨hv.1, hv.2.lt_of_ne hv1⟩ h

/-- **Every point of the curve has a parameter short of the finish.** A parameter at the finish
is replaced by the start, which carries the same point. This is the only use the closing
condition gets. -/
theorem parameter_before_finish (hf : IsLoop f) {p : Plane} (hp : p ∈ f '' I) :
    ∃ u ∈ I, u ≠ 1 ∧ f u = p := by
  obtain ⟨u, hu, rfl⟩ := hp
  rcases eq_or_ne u 1 with rfl | hu1
  · exact ⟨0, zero_mem_I, one_ne_zero.symm, hf.closes⟩
  · exact ⟨u, hu, hu1, rfl⟩

/-- The start and the finish are the same point of the curve; recorded in the direction the
proofs below read it. -/
theorem finish_eq_start (hf : IsLoop f) : f 1 = f 0 := hf.closes.symm

/-! ### The three pieces of parameters

Two parameters `s < t` cut `[0, 1]` into the middle interval `[s, t]` and the two end
intervals `[0, s]` and `[t, 1]`. Each piece needs the loop to be injective on its own
parameters. On the middle and the front that is injectivity off the finish, since neither
contains it; the back piece *does* contain the finish, and there the extra argument is that
the only other parameter carrying `f 1` is the start, which lies strictly before `t`. -/

theorem front_subset_I (hs : s ∈ I) : Icc 0 s ⊆ I := Icc_subset_Icc le_rfl hs.2

theorem middle_subset_I (hs : s ∈ I) (ht : t ∈ I) : Icc s t ⊆ I := Icc_subset_Icc hs.1 ht.2

theorem back_subset_I (ht : t ∈ I) : Icc t 1 ⊆ I := Icc_subset_Icc ht.1 le_rfl

/-- Injectivity on the front piece: no parameter of `[0, s]` is the finish, because `s` is
not. -/
theorem injective_on_front (hf : IsLoop f) (hs : s ∈ I) (hs1 : s ≠ 1) : InjOn f (Icc 0 s) := by
  have hs' : s < 1 := hs.2.lt_of_ne hs1
  intro u hu v hv h
  exact hf.injective_before_finish (front_subset_I hs hu) (front_subset_I hs hv)
    (ne_of_lt (lt_of_le_of_lt hu.2 hs')) (ne_of_lt (lt_of_le_of_lt hv.2 hs')) h

/-- Injectivity on the middle piece: no parameter of `[s, t]` is the finish, because `t` is
not. -/
theorem injective_on_middle (hf : IsLoop f) (hs : s ∈ I) (ht : t ∈ I) (ht1 : t ≠ 1) :
    InjOn f (Icc s t) := by
  have ht' : t < 1 := ht.2.lt_of_ne ht1
  intro u hu v hv h
  exact hf.injective_before_finish (middle_subset_I hs ht hu) (middle_subset_I hs ht hv)
    (ne_of_lt (lt_of_le_of_lt hu.2 ht')) (ne_of_lt (lt_of_le_of_lt hv.2 ht')) h

/-- On the back piece the finish is the *only* parameter carrying `f 1`. A second one would be
the start, by injectivity off the finish and the closing condition — but the start lies
strictly before `t`. -/
theorem back_at_finish (hf : IsLoop f) (ht : t ∈ I) (ht0 : 0 < t) {w : ℝ} (hw : w ∈ Icc t 1)
    (h : f w = f 1) : w = 1 := by
  by_contra hw1
  have : w = 0 :=
    hf.injective_before_finish (back_subset_I ht hw) zero_mem_I hw1 one_ne_zero.symm
      (h.trans hf.finish_eq_start)
  exact absurd (this ▸ hw.1) (not_le.mpr ht0)

/-- Injectivity on the back piece. Unlike the other two this piece contains the finish, so
injectivity off the finish is not enough on its own; `back_at_finish` supplies the rest. -/
theorem injective_on_back (hf : IsLoop f) (ht : t ∈ I) (ht0 : 0 < t) : InjOn f (Icc t 1) := by
  intro u hu v hv h
  rcases eq_or_ne u 1 with rfl | hu1
  · exact (hf.back_at_finish ht ht0 hv h.symm).symm
  · rcases eq_or_ne v 1 with rfl | hv1
    · exact hf.back_at_finish ht ht0 hu h
    · exact hf.injective_before_finish (back_subset_I ht hu) (back_subset_I ht hv) hu1 hv1 h

/-! ### The three pieces are arcs -/

/-- The middle piece is an arc between the two cut points. -/
theorem middle_IsArcBetween (hf : IsLoop f) (hs : s ∈ I) (ht : t ∈ I) (ht1 : t ≠ 1)
    (hst : s < t) : IsArcBetween (f '' Icc s t) (f s) (f t) := by
  rw [← uIcc_of_le hst.le]
  refine isArcBetween_subarc hf.continuousOn ?_ hs ht (ne_of_lt hst)
  rw [uIcc_of_le hst.le]
  exact hf.injective_on_middle hs ht ht1

/-- The front piece is an arc from the start to the first cut point. -/
theorem front_IsArcBetween (hf : IsLoop f) (hs : s ∈ I) (hs1 : s ≠ 1) (hs0 : 0 < s) :
    IsArcBetween (f '' Icc 0 s) (f 0) (f s) := by
  rw [← uIcc_of_le hs0.le]
  refine isArcBetween_subarc hf.continuousOn ?_ zero_mem_I hs (ne_of_lt hs0)
  rw [uIcc_of_le hs0.le]
  exact hf.injective_on_front hs hs1

/-- The back piece is an arc from the second cut point to the finish. -/
theorem back_IsArcBetween (hf : IsLoop f) (ht : t ∈ I) (ht1 : t ≠ 1) (ht0 : 0 < t) :
    IsArcBetween (f '' Icc t 1) (f t) (f 1) := by
  rw [← uIcc_of_le ht.2]
  refine isArcBetween_subarc hf.continuousOn ?_ ht one_mem_I ht1
  rw [uIcc_of_le ht.2]
  exact hf.injective_on_back ht ht0

/-! ### The outside piece

The parameters outside `[s, t]` are two intervals, glued at the point where the loop closes
up: walk from `t` to the finish, then from the start to `s`. When `s` *is* the start the front
interval degenerates to a single parameter, and the outside is the back piece alone — its far
end already carries the point the front piece would have contributed. -/

/-- The back and front pieces meet only where the loop closes up. A point on both comes from a
parameter at or past `t` and from one at or before `s`; two distinct parameters short of the
finish cannot carry the same point, and `t ≤ s` is false, so the back parameter is the
finish. -/
theorem back_meet_front (hf : IsLoop f) (hs : s ∈ I) (ht : t ∈ I) (hs1 : s ≠ 1) (hst : s < t)
    {z : Plane} (hzb : z ∈ f '' Icc t 1) (hzf : z ∈ f '' Icc 0 s) : z = f 1 := by
  obtain ⟨b, hb, rfl⟩ := hzb
  obtain ⟨a, ha, hab⟩ := hzf
  have ha1 : a ≠ 1 := ne_of_lt (lt_of_le_of_lt ha.2 (hs.2.lt_of_ne hs1))
  rcases eq_or_ne b 1 with rfl | hb1
  · rfl
  · -- Otherwise both parameters are short of the finish, so they coincide — impossible,
    -- since one is at least `t` and the other at most `s < t`.
    have : b = a :=
      hf.injective_before_finish (back_subset_I ht hb) (front_subset_I hs ha) hb1 ha1 hab.symm
    exact absurd (this ▸ hb.1) (not_le.mpr (lt_of_le_of_lt ha.2 hst))

/-- **The outside piece is an arc between the two cut points.** -/
theorem outside_IsArcBetween (hf : IsLoop f) (hs : s ∈ I) (ht : t ∈ I) (hs1 : s ≠ 1)
    (ht1 : t ≠ 1) (hst : s < t) :
    IsArcBetween (f '' Icc 0 s ∪ f '' Icc t 1) (f t) (f s) := by
  have ht0 : 0 < t := lt_of_le_of_lt hs.1 hst
  have hback : IsArcBetween (f '' Icc t 1) (f t) (f 1) := hf.back_IsArcBetween ht ht1 ht0
  rcases eq_or_lt_of_le hs.1 with hs0 | hs0
  · -- `s` is the start: the front interval is the single parameter `0`, whose point the back
    -- piece already carries at its far end, so the outside is the back piece alone.
    have hfront : f '' Icc 0 s = {f 1} := by
      rw [← hs0, Icc_self, image_singleton, hf.finish_eq_start]
    have hone : f 1 ∈ f '' Icc t 1 := ⟨1, ⟨ht.2, le_rfl⟩, rfl⟩
    rw [hfront, singleton_union, insert_eq_self.mpr hone, ← hs0, ← hf.finish_eq_start]
    exact hback
  · -- Otherwise the two end intervals are genuine arcs, glued where the loop closes up.
    have hfront : IsArcBetween (f '' Icc 0 s) (f 1) (f s) := by
      rw [hf.finish_eq_start]
      exact hf.front_IsArcBetween hs hs1 hs0
    have := hback.concatenate hfront (fun z hzb hzf => hf.back_meet_front hs ht hs1 hst hzb hzf)
    rwa [union_comm] at this

/-! ### Covering, and where the pieces meet -/

/-- The parameter interval splits three ways around any two of its points. Linearity of the
order, and nothing else — the split does not even need the two points ordered, since when they
are not the middle interval is empty and the two end intervals already overlap. -/
theorem parameters_split (hs : s ∈ I) (ht : t ∈ I) :
    I = Icc s t ∪ (Icc 0 s ∪ Icc t 1) := by
  ext x
  constructor
  · rintro ⟨h0, h1⟩
    rcases le_total x s with h | h
    · exact Or.inr (Or.inl ⟨h0, h⟩)
    · rcases le_total x t with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr (Or.inr ⟨h', h1⟩)
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨hs.1.trans h1, h2.trans ht.2⟩
    · exact ⟨h1, h2.trans hs.2⟩
    · exact ⟨ht.1.trans h1, h2⟩

/-- The loop's images of the middle and of the outside cover the curve. -/
theorem pieces_cover (hs : s ∈ I) (ht : t ∈ I) :
    f '' Icc s t ∪ (f '' Icc 0 s ∪ f '' Icc t 1) = f '' I := by
  rw [parameters_split hs ht, image_union, image_union]

/-- **The two pieces meet in exactly the two cut points.**

Three cases, one for each way an outside parameter can be placed. The one that matters is the
outside parameter being the finish: it carries the same point as the start, so the middle
parameter is the start, which forces `s` to be it. That case is why the argument needs a loop
rather than an arc. -/
theorem pieces_meet_at_ends (hf : IsLoop f) (hs : s ∈ I) (ht : t ∈ I) (hs1 : s ≠ 1)
    (ht1 : t ≠ 1) (hst : s < t) :
    f '' Icc s t ∩ (f '' Icc 0 s ∪ f '' Icc t 1) = {f s, f t} := by
  have ht' : t < 1 := ht.2.lt_of_ne ht1
  apply Subset.antisymm
  · rintro z ⟨⟨m, hm, rfl⟩, hzout⟩
    have hmI : m ∈ I := middle_subset_I hs ht hm
    have hm1 : m ≠ 1 := ne_of_lt (lt_of_le_of_lt hm.2 ht')
    rcases hzout with ⟨a, ha, hazm⟩ | ⟨b, hb, hbzm⟩
    · -- A front parameter: it is at most `s`, and the middle parameter is at least `s`.
      have ha1 : a ≠ 1 := ne_of_lt (lt_of_le_of_lt ha.2 (hs.2.lt_of_ne hs1))
      have : m = a :=
        hf.injective_before_finish hmI (front_subset_I hs ha) hm1 ha1 hazm.symm
      rw [le_antisymm (this ▸ ha.2) hm.1]
      exact mem_insert _ _
    · rcases eq_or_ne b 1 with rfl | hb1
      · -- The far end carries the same point as the start, and the start is short of the
        -- finish, so the middle parameter is the start — which forces `s` to be it.
        have : m = 0 :=
          hf.injective_before_finish hmI zero_mem_I hm1 one_ne_zero.symm
            (hbzm.symm.trans hf.finish_eq_start)
        have hs0 : s = 0 := le_antisymm (this ▸ hm.1) hs.1
        rw [hs0, ← this]
        exact mem_insert _ _
      · -- Otherwise the outside parameter is at least `t`, and the middle one is at most `t`.
        have : m = b :=
          hf.injective_before_finish hmI (back_subset_I ht hb) hm1 hb1 hbzm.symm
        rw [le_antisymm hm.2 (this ▸ hb.1)]
        exact mem_insert_of_mem _ rfl
  · rintro z (rfl | rfl)
    · exact ⟨⟨s, ⟨le_rfl, hst.le⟩, rfl⟩, Or.inl ⟨s, ⟨hs.1, le_rfl⟩, rfl⟩⟩
    · exact ⟨⟨t, ⟨hst.le, le_rfl⟩, rfl⟩, Or.inr ⟨t, ⟨le_rfl, ht.2⟩, rfl⟩⟩

/-! ### The two arcs, at chosen parameters -/

/-- **Two parameters short of the finish cut the loop's image into two arcs between the points
they carry, which cover it and meet in exactly those two points.**

The pieces are named by the parameters, not chosen: the first is the middle interval's image,
the second the outside's. -/
theorem two_arcs_at_parameters (hf : IsLoop f) (hs : s ∈ I) (ht : t ∈ I) (hs1 : s ≠ 1)
    (ht1 : t ≠ 1) (hst : s < t) :
    ∃ A B, IsArcBetween A (f s) (f t) ∧ IsArcBetween B (f t) (f s) ∧
      A ∪ B = f '' I ∧ A ∩ B = {f s, f t} :=
  ⟨f '' Icc s t, f '' Icc 0 s ∪ f '' Icc t 1,
    hf.middle_IsArcBetween hs ht ht1 hst,
    hf.outside_IsArcBetween hs ht hs1 ht1 hst,
    pieces_cover hs ht,
    hf.pieces_meet_at_ends hs ht hs1 ht1 hst⟩

end IsLoop

/-! ### The theorem -/

/-- **Two distinct points of a Jordan curve cut it into two arcs between them, which cover the
curve and meet in exactly those two points.**

The parameters carrying the two points come in one order or the other, and the conclusion is
symmetric in the two pieces, so the second case is the first with the roles exchanged: the
union and the intersection commute, and the unordered pair does too.

This is the exact converse of `IsJordanCurve.of_two_arcs`: that theorem's hypotheses are two
arcs between the same two points meeting only there, which is what the two pieces produced
here are — see `IsJordanCurve.two_arcs_of_two_arcs`. -/
theorem IsJordanCurve.two_arcs {C : Set Plane} (hC : IsJordanCurve C) {p q : Plane}
    (hp : p ∈ C) (hq : q ∈ C) (hpq : p ≠ q) :
    ∃ A B, IsArcBetween A p q ∧ IsArcBetween B p q ∧ A ∪ B = C ∧ A ∩ B = {p, q} := by
  obtain ⟨f, hf, rfl⟩ := hC
  obtain ⟨s, hs, hs1, rfl⟩ := hf.parameter_before_finish hp
  obtain ⟨t, ht, ht1, rfl⟩ := hf.parameter_before_finish hq
  -- Distinct points, so distinct parameters, so one of the two orders holds.
  rcases lt_or_gt_of_ne (fun h : s = t => hpq (by rw [h])) with hst | hts
  · obtain ⟨A, B, hA, hB, hcov, hmeet⟩ := hf.two_arcs_at_parameters hs ht hs1 ht1 hst
    exact ⟨A, B, hA, hB.reverse, hcov, hmeet⟩
  · -- The middle piece now runs from `f t` to `f s`, so it is the *second* piece here.
    obtain ⟨A, B, hA, hB, hcov, hmeet⟩ := hf.two_arcs_at_parameters ht hs ht1 hs1 hts
    refine ⟨B, A, hB, hA.reverse, ?_, ?_⟩
    · rw [union_comm]; exact hcov
    · rw [inter_comm, hmeet, pair_comm]

/-- The composition check: the two arcs `IsJordanCurve.two_arcs` produces are exactly what
`IsJordanCurve.of_two_arcs` consumes, and glue back to the curve one started from. -/
theorem IsJordanCurve.two_arcs_of_two_arcs {A B : Set Plane} {p q : Plane}
    (hA : IsArcBetween A p q) (hB : IsArcBetween B p q) (hmeet : A ∩ B = {p, q}) :
    IsJordanCurve (A ∪ B) :=
  IsJordanCurve.of_two_arcs hA hB.reverse fun z hzA hzB => by
    have : z ∈ ({p, q} : Set Plane) := hmeet ▸ ⟨hzA, hzB⟩
    exact this

end Schoenflies

end BundlePart414

section BundlePart415
/- Source: dev/planar_search/schoenflies_port/Schoenflies/Realization.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/




/-!
# Realizing a polygonal Jordan curve as a `ClosedPolygon`

The blueprint's "simple closed polygonal curve" is set-theoretic: an `IsJordanCurve` that is
also `IsPolygonal`, with no condition on vertices at all. The development works instead with
`Schoenflies.ClosedPolygon`, a cyclic vertex list carrying a `corner` field — no three
consecutive vertices collinear. That field is a *presentation* condition, strictly stronger than
the blueprint's notion, and until now nothing said that a set-level polygonal Jordan curve
admits such a presentation. This module proves it.

## How the vertex list is found

The curve is *not* read off the vertex list `IsPolygonal` hands over: that list may retrace
itself, cross itself, and repeat segments, and it carries no order along the curve. Two
structures are laid over the point set instead and then matched.

* **From the plane side**, the overlay of `Schoenflies/OverlayGraph.lean`, with the graph
  discarded: `Schoenflies.IsClean` is a finite list of nondegenerate segments occupying the
  curve, with pairwise disjoint interiors and no end interior to any of them. Around an interior
  point of a piece the curve *is* that piece (`IsClean.exists_ball_subset_seg`), so the piece
  interiors are separated by honest open sets of the plane (`Schoenflies.nearPiece`) and a
  connected subset of the curve away from the ends lies inside a single piece.
* **From the curve side**, the loop's parameters at which it reaches an end of a piece. They
  form a finite subset of `[0, 1)` containing `0` — `0` because the loop's start is put on the
  cut list, so that the last gap is the one that closes the curve — and, listed in increasing
  order, they cut `[0, 1)` into gaps.

The two match: a gap image is connected and misses the ends, so it lies in one piece interior;
and the interior is connected and covered by the *closed* gap images, so it lies in that one
gap. Gaps and pieces therefore correspond one to one, the ends of a gap are the ends of its
piece, and the ends listed in the loop's order are a cyclic vertex list whose edges are the
pieces. That list satisfies `vertex_inj` and `edges_meet` but not `corner`, which is what
`Schoenflies.PrePolygon` is for; `corner` is then arranged by deleting redundant vertices.

## Blueprint

* `Schoenflies.PrePolygon` — a `ClosedPolygon` less the `corner` field: the blueprint's simple
  closed polygonal curve *presented by a vertex list*, redundant vertices allowed.
* `Schoenflies.PrePolygon.deleteLast`, `Schoenflies.PrePolygon.exists_closedPolygon_of_prePolygon`
  — the blueprint's opening move in Lemma 1.8, "delete redundant vertices at which two
  consecutive edges are collinear", as an operation rather than an invariant.
* `Schoenflies.IsClean`, `Schoenflies.exists_isClean` — Lemma 3.7 (polygonal overlay) with the
  combinatorics dropped: what the overlay says about the point set alone.
* `Schoenflies.par`, `Schoenflies.parNext`, `Schoenflies.exists_mem_gap` — the parameters in
  increasing order, and that their gaps tile `[0, 1)`.
* `Schoenflies.exists_prePolygon_of_isJordanCurve`, `Schoenflies.exists_closedPolygon` — §1:
  every simple closed polygonal curve, in the blueprint's set-level sense, is the carrier of a
  `ClosedPolygon`.
* `Schoenflies.IsStraightAt`, `Schoenflies.IsCornerAt`,
  `Schoenflies.ClosedPolygon.exists_vertex_eq_of_isCornerAt`,
  `Schoenflies.ClosedPolygon.isCornerAt_vertex` — the vertex set of a realization is *exactly*
  the set of points at which the curve does not run straight. So a named point can be required
  to be a vertex precisely when it is a corner, and no realization has any choice about it.
* `Schoenflies.ClosedPolygon.rotate`, `…isArcBetween_arc`, `…arc_inter` — the two arcs of a
  splitting, as arcs between the two cut vertices meeting exactly there.
* `Schoenflies.two_arcs_unique` — two points cut a Jordan curve into two arcs in only one way.
* `Schoenflies.exists_closedPolygon_corners`, `Schoenflies.exists_closedPolygon_split`,
  `Schoenflies.exists_closedPolygon_arcs`, `Schoenflies.exists_closedPolygon_arcs_ordered` — the
  realization with named corners, with the splitting indices, and with the two arcs identified.
  The last is the shape `Graph.IsHexRealization` asks for.

## The corner hypothesis is not an artefact

`exists_closedPolygon_arcs` requires the two cut points to be corners.
`ClosedPolygon.isCornerAt_vertex` shows that this cannot be dropped: every vertex of every
realization is a corner, so a cut point at which the curve runs straight is a vertex of *no*
realization, and no `ClosedPolygon` with that carrier has an arc ending there. A consumer that
needs to cut at a straight point has to change the curve — bend it there — which is a different
theorem, and is exactly the freedom `Graph.IsK33Config.not_isDrawing` reserves for itself.
-/

open Metric Set unitInterval

namespace Schoenflies

open Plane

/-! ## Polygons before normalization

`PrePolygon` is `ClosedPolygon` with the `corner` field removed. Everything the curve bridge of
`Schoenflies/PolygonBridge.lean` proves about a `ClosedPolygon` — that its carrier is a Jordan
curve, that it is polygonal — uses only `vertex_inj` and `edges_meet`, so it is already true
here; what `corner` buys is the germ argument of the strip lemma, and nothing else. -/

/-- A simple closed polygonal curve presented by its cyclic vertex list, with redundant
vertices allowed: `ClosedPolygon` less its `corner` field. -/
structure PrePolygon (m : ℕ) where
  /-- The vertices, in cyclic order. -/
  vertex : ZMod (m + 3) → Plane
  /-- The vertices are distinct. -/
  vertex_inj : Function.Injective vertex
  /-- Simplicity: an edge meets any other edge only at one of its own endpoints. -/
  edges_meet : ∀ i j : ZMod (m + 3), i ≠ j →
    segment ℝ (vertex i) (vertex (i + 1)) ∩ segment ℝ (vertex j) (vertex (j + 1)) ⊆
      {vertex i, vertex (i + 1)}

namespace PrePolygon

variable {m : ℕ} (P : PrePolygon m)

/-- The edge leaving vertex `i`. -/
def edge (i : ZMod (m + 3)) : Set Plane := segment ℝ (P.vertex i) (P.vertex (i + 1))

/-- The carrier: the union of the edges. -/
def carrier : Set Plane := ⋃ i, P.edge i

variable {P}

theorem edge_subset_carrier (i : ZMod (m + 3)) : P.edge i ⊆ P.carrier := Set.subset_iUnion _ i

theorem vertex_mem_carrier (i : ZMod (m + 3)) : P.vertex i ∈ P.carrier :=
  edge_subset_carrier i (left_mem_segment ℝ _ _)

theorem vertex_ne_succ (i : ZMod (m + 3)) : P.vertex i ≠ P.vertex (i + 1) := fun h =>
  ClosedPolygon.succ_ne_self i (P.vertex_inj h).symm

end PrePolygon

/-- A `ClosedPolygon` read as a `PrePolygon`: forget the `corner` field. -/
def ClosedPolygon.toPre {m : ℕ} (P : ClosedPolygon m) : PrePolygon m :=
  ⟨P.vertex, P.vertex_inj, P.edges_meet⟩

@[simp] theorem ClosedPolygon.carrier_toPre {m : ℕ} (P : ClosedPolygon m) :
    P.toPre.carrier = P.carrier := rfl

/-! ## Small facts about the cyclic index

`ZMod (m + 3)` has at least three elements; `0`, `1` and `2` are distinct, which is what makes
a vertex, its successor and its predecessor three different vertices. -/

namespace PrePolygon

variable {m : ℕ}

theorem two_ne_zero' : (2 : ZMod (m + 3)) ≠ 0 := by
  intro h
  rw [show (2 : ZMod (m + 3)) = ((2 : ℕ) : ZMod (m + 3)) by norm_num,
    ZMod.natCast_eq_zero_iff] at h
  have := Nat.le_of_dvd (by norm_num) h
  omega

theorem pred_ne_succ (i : ZMod (m + 3)) : i - 1 ≠ i + 1 := fun h =>
  two_ne_zero' (m := m) (by linear_combination -h)

theorem val_one_eq : (1 : ZMod (m + 3)).val = 1 := by
  rw [show (1 : ZMod (m + 3)) = ((1 : ℕ) : ZMod (m + 3)) by norm_num]
  exact ZMod.val_cast_of_lt (by omega)

/-- The successor of a non-final index is the next one. -/
theorem val_succ_of_lt {j : ZMod (m + 3)} (h : j.val + 1 < m + 3) : (j + 1).val = j.val + 1 := by
  rw [ZMod.val_add, val_one_eq, Nat.mod_eq_of_lt h]

/-- The successor of the final index wraps to `0`. -/
theorem val_succ_last {j : ZMod (m + 3)} (h : j.val + 1 = m + 3) : (j + 1).val = 0 := by
  rw [ZMod.val_add, val_one_eq, h, Nat.mod_self]

/-! ## Rotation

Reading the same cyclic list from a different starting vertex. It is used once, to bring the
vertex that is about to be deleted to the end of the list. -/

/-- The same closed polygon, read from vertex `a` onwards. -/
def rotate (P : PrePolygon m) (a : ZMod (m + 3)) : PrePolygon m where
  vertex j := P.vertex (a + j)
  vertex_inj i j h := add_left_cancel (P.vertex_inj h)
  edges_meet i j hij := by
    have hi : a + (i + 1) = a + i + 1 := by ring
    have hj : a + (j + 1) = a + j + 1 := by ring
    simp only [hi, hj]
    exact P.edges_meet _ _ fun h => hij (add_left_cancel h)

@[simp] theorem rotate_vertex (P : PrePolygon m) (a j : ZMod (m + 3)) :
    (P.rotate a).vertex j = P.vertex (a + j) := rfl

/-- Rotating does not move the curve: the edges are the same, listed from elsewhere. -/
theorem carrier_rotate (P : PrePolygon m) (a : ZMod (m + 3)) :
    (P.rotate a).carrier = P.carrier := by
  have hedge : ∀ j : ZMod (m + 3), (P.rotate a).edge j = P.edge (a + j) := by
    intro j
    rw [edge, edge, rotate_vertex, rotate_vertex, show a + (j + 1) = a + j + 1 by ring]
  refine Set.Subset.antisymm (Set.iUnion_subset fun j => ?_) (Set.iUnion_subset fun i => ?_)
  · rw [hedge]; exact edge_subset_carrier _
  · refine le_trans (le_of_eq ?_) (edge_subset_carrier (P := P.rotate a) (i - a))
    rw [hedge, add_sub_cancel]

/-! ## Deleting the last vertex

The blueprint's opening move in the strip lemma. The vertex to be deleted is brought to the end
of the list by `rotate`, so only that one case has to be treated. `emb` is the inclusion of the
shortened index set into the old one: the same numeral, one modulus smaller. -/

section Delete

variable {m : ℕ}

/-- An index of the shortened list, read in the original one: the same numeral. -/
def emb (j : ZMod (m + 3)) : ZMod (m + 1 + 3) := ((j.val : ℕ) : ZMod (m + 1 + 3))

theorem neg_one_eq_cast : (-1 : ZMod (m + 1 + 3)) = ((m + 3 : ℕ) : ZMod (m + 1 + 3)) := by
  have h0 : ((m + 1 + 3 : ℕ) : ZMod (m + 1 + 3)) = 0 := ZMod.natCast_self _
  push_cast at h0 ⊢
  linear_combination -h0

theorem neg_two_eq_cast : (-1 - 1 : ZMod (m + 1 + 3)) = ((m + 2 : ℕ) : ZMod (m + 1 + 3)) := by
  have h0 : ((m + 1 + 3 : ℕ) : ZMod (m + 1 + 3)) = 0 := ZMod.natCast_self _
  push_cast at h0 ⊢
  linear_combination -h0

theorem emb_injective : Function.Injective (emb (m := m)) := fun i j h =>
  ZMod.val_injective _ (ClosedPolygon.natCast_inj (m := m + 1)
    (by have := ZMod.val_lt i; omega) (by have := ZMod.val_lt j; omega) h)

theorem emb_succ_of_lt {j : ZMod (m + 3)} (h : j.val + 1 < m + 3) : emb (j + 1) = emb j + 1 := by
  rw [emb, emb, val_succ_of_lt h, Nat.cast_add, Nat.cast_one]

theorem emb_succ_last {j : ZMod (m + 3)} (h : j.val + 1 = m + 3) : emb (j + 1) = 0 := by
  rw [emb, val_succ_last h, Nat.cast_zero]

theorem emb_eq_last {j : ZMod (m + 3)} (h : j.val + 1 = m + 3) : emb j = -1 - 1 := by
  rw [emb, neg_two_eq_cast, show j.val = m + 2 by omega]

/-- Below the last index, `emb` misses both the deleted vertex and its predecessor. -/
theorem emb_ne_of_lt {j : ZMod (m + 3)} (h : j.val + 1 < m + 3) :
    emb j ≠ -1 ∧ emb j ≠ -1 - 1 := by
  have hj := ZMod.val_lt j
  constructor
  · rw [neg_one_eq_cast]
    exact fun he => (by omega : j.val ≠ m + 3)
      (ClosedPolygon.natCast_inj (m := m + 1) (by omega) (by omega) he)
  · rw [neg_two_eq_cast]
    exact fun he => (by omega : j.val ≠ m + 2)
      (ClosedPolygon.natCast_inj (m := m + 1) (by omega) (by omega) he)

/-- Every index other than the deleted vertex and its predecessor is hit by `emb`. -/
theorem exists_emb_eq {i : ZMod (m + 1 + 3)} (h1 : i ≠ -1) (h2 : i ≠ -1 - 1) :
    ∃ j : ZMod (m + 3), j.val + 1 < m + 3 ∧ emb j = i := by
  have hi := ZMod.val_lt i
  have hne1 : i.val ≠ m + 3 := by
    rintro he
    exact h1 (by rw [neg_one_eq_cast, ← he, ZMod.natCast_rightInverse i])
  have hne2 : i.val ≠ m + 2 := by
    rintro he
    exact h2 (by rw [neg_two_eq_cast, ← he, ZMod.natCast_rightInverse i])
  refine ⟨(i.val : ZMod (m + 3)), ?_, ?_⟩
  · rw [ZMod.val_cast_of_lt (show i.val < m + 3 by omega)]; omega
  · rw [emb, ZMod.val_cast_of_lt (show i.val < m + 3 by omega), ZMod.natCast_rightInverse i]

variable (P : PrePolygon (m + 1))

/-- The vertex list with its last entry dropped. -/
def dropVertex (j : ZMod (m + 3)) : Plane := P.vertex (emb j)

variable {P}

theorem dropVertex_injective : Function.Injective P.dropVertex :=
  fun _ _ h => emb_injective (P.vertex_inj h)

/-- Away from the deleted vertex the edges are unchanged. -/
theorem dropVertex_edge_of_lt {j : ZMod (m + 3)} (h : j.val + 1 < m + 3) :
    segment ℝ (P.dropVertex j) (P.dropVertex (j + 1)) = P.edge (emb j) := by
  rw [dropVertex, dropVertex, emb_succ_of_lt h, edge]

/-- The final edge of the shortened list is the union of the two edges at the deleted vertex —
which is a segment precisely because the deleted vertex is interior to it. -/
theorem dropVertex_edge_last
    (hcol : P.vertex (-1) ∈ openSegment ℝ (P.vertex (-1 - 1)) (P.vertex 0))
    {j : ZMod (m + 3)} (h : j.val + 1 = m + 3) :
    segment ℝ (P.dropVertex j) (P.dropVertex (j + 1)) = P.edge (-1 - 1) ∪ P.edge (-1) := by
  have e1 : (-1 - 1 : ZMod (m + 1 + 3)) + 1 = -1 := by ring
  have e2 : (-1 : ZMod (m + 1 + 3)) + 1 = 0 := by ring
  rw [dropVertex, dropVertex, emb_succ_last h, emb_eq_last h, edge, edge, e1, e2]
  exact segment_split (openSegment_subset_segment ℝ _ _ hcol)

/-- The deleted vertex lies on no edge but its own two: `edges_meet` puts a meeting point at an
end of the other edge, and the deleted vertex is an end only of the two edges at it. -/
theorem vertex_last_notMem_edge {i : ZMod (m + 1 + 3)} (h1 : i ≠ -1) (h2 : i ≠ -1 - 1) :
    P.vertex (-1) ∉ P.edge i := by
  intro hmem
  have hself : P.vertex (-1) ∈ P.edge (-1) := left_mem_segment ℝ _ _
  have hme := P.edges_meet i (-1) h1 (Set.mem_inter hmem hself)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hme
  rcases hme with he | he
  · exact h1 (P.vertex_inj he).symm
  · exact h2 (by linear_combination -P.vertex_inj he)

/-- **Simplicity survives the deletion.** The only new edge is the merged one, and the point
that has to be kept out of it — the deleted vertex — lies on no other edge at all. -/
theorem dropVertex_edges_meet
    (hcol : P.vertex (-1) ∈ openSegment ℝ (P.vertex (-1 - 1)) (P.vertex 0))
    (j k : ZMod (m + 3)) (hjk : j ≠ k) :
    segment ℝ (P.dropVertex j) (P.dropVertex (j + 1)) ∩
      segment ℝ (P.dropVertex k) (P.dropVertex (k + 1)) ⊆
      {P.dropVertex j, P.dropVertex (j + 1)} := by
  have e1 : (-1 - 1 : ZMod (m + 1 + 3)) + 1 = -1 := by ring
  have e2 : (-1 : ZMod (m + 1 + 3)) + 1 = 0 := by ring
  have hjv : j.val + 1 ≤ m + 3 := ZMod.val_lt j
  have hkv : k.val + 1 ≤ m + 3 := ZMod.val_lt k
  rcases eq_or_lt_of_le hjv with hj | hj
  · -- `j` is the last index, so its edge is the merged one.
    have hdj : P.dropVertex j = P.vertex (-1 - 1) := by rw [dropVertex, emb_eq_last hj]
    have hdj1 : P.dropVertex (j + 1) = P.vertex 0 := by rw [dropVertex, emb_succ_last hj]
    rcases eq_or_lt_of_le hkv with hk | hk
    · exact absurd (ZMod.val_injective _ (by omega : j.val = k.val)) hjk
    obtain ⟨hk1, hk2⟩ := emb_ne_of_lt hk
    have hout := vertex_last_notMem_edge (P := P) hk1 hk2
    rw [dropVertex_edge_last hcol hj, dropVertex_edge_of_lt hk, hdj, hdj1]
    rintro x ⟨hx1 | hx1, hx2⟩
    · have hme := P.edges_meet _ _ (fun h => hk2 h.symm) (Set.mem_inter hx1 hx2)
      rw [e1] at hme
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hme ⊢
      exact hme.imp id fun h => absurd (h ▸ hx2) hout
    · have hme := P.edges_meet _ _ (fun h => hk1 h.symm) (Set.mem_inter hx1 hx2)
      rw [e2] at hme
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hme ⊢
      exact Or.inr (hme.resolve_left fun h => absurd (h ▸ hx2) hout)
  · -- `j` is an ordinary index, so its edge is unchanged.
    obtain ⟨hj1, hj2⟩ := emb_ne_of_lt hj
    have hdj : P.dropVertex j = P.vertex (emb j) := rfl
    have hdj1 : P.dropVertex (j + 1) = P.vertex (emb j + 1) := by
      rw [dropVertex, emb_succ_of_lt hj]
    rw [dropVertex_edge_of_lt hj, hdj, hdj1]
    rcases eq_or_lt_of_le hkv with hk | hk
    · rw [dropVertex_edge_last hcol hk]
      rintro x ⟨hx1, hx2 | hx2⟩
      · exact P.edges_meet _ _ hj2 (Set.mem_inter hx1 hx2)
      · exact P.edges_meet _ _ hj1 (Set.mem_inter hx1 hx2)
    · rw [dropVertex_edge_of_lt hk]
      exact fun x hx => P.edges_meet _ _ (fun h => hjk (emb_injective h)) hx

/-- **The polygon with a redundant vertex deleted.** -/
def deleteLast (P : PrePolygon (m + 1))
    (hcol : P.vertex (-1) ∈ openSegment ℝ (P.vertex (-1 - 1)) (P.vertex 0)) : PrePolygon m where
  vertex := P.dropVertex
  vertex_inj := dropVertex_injective
  edges_meet := dropVertex_edges_meet hcol

/-- **Deleting a redundant vertex does not move the curve.** -/
theorem carrier_deleteLast
    (hcol : P.vertex (-1) ∈ openSegment ℝ (P.vertex (-1 - 1)) (P.vertex 0)) :
    (deleteLast P hcol).carrier = P.carrier := by
  refine Set.Subset.antisymm (Set.iUnion_subset fun j => ?_) (Set.iUnion_subset fun i => ?_)
  · have hjv : j.val + 1 ≤ m + 3 := ZMod.val_lt j
    rcases eq_or_lt_of_le hjv with hj | hj
    · rw [show (deleteLast P hcol).edge j = _ from dropVertex_edge_last hcol hj]
      exact Set.union_subset (edge_subset_carrier _) (edge_subset_carrier _)
    · rw [show (deleteLast P hcol).edge j = _ from dropVertex_edge_of_lt hj]
      exact edge_subset_carrier _
  · by_cases hi : i = -1 ∨ i = -1 - 1
    · -- The two edges at the deleted vertex are both inside the merged one.
      set j : ZMod (m + 3) := ((m + 2 : ℕ) : ZMod (m + 3)) with hjdef
      have hj : j.val + 1 = m + 3 := by rw [hjdef, ZMod.val_cast_of_lt (by omega)]
      have hmerge : (deleteLast P hcol).edge j = P.edge (-1 - 1) ∪ P.edge (-1) :=
        dropVertex_edge_last hcol hj
      refine le_trans ?_ (le_trans (le_of_eq hmerge.symm) (edge_subset_carrier j))
      rcases hi with rfl | rfl
      · exact Set.subset_union_right
      · exact Set.subset_union_left
    · push Not at hi
      obtain ⟨j, hj, hemb⟩ := exists_emb_eq hi.1 hi.2
      have : (deleteLast P hcol).edge j = P.edge i := by
        rw [show (deleteLast P hcol).edge j = _ from dropVertex_edge_of_lt hj, hemb]
      exact le_trans (le_of_eq this.symm) (edge_subset_carrier j)

end Delete

/-! ## Recognising a redundant vertex

The `corner` field is `det ≠ 0` at every vertex. Where it fails the vertex is *interior* to the
segment joining its two neighbours, never an endpoint of it. That is the geometric content of
`edges_meet`: two edges leaving a vertex in the *same* direction would overlap in a
nondegenerate segment, and `edges_meet` would then put a whole segment inside a two-point
set. -/

/-- A nondegenerate segment is not contained in the pair of its own endpoints. -/
theorem exists_mem_segment_ne {a b : Plane} (hab : a ≠ b) :
    ∃ p ∈ segment ℝ a b, p ≠ a ∧ p ≠ b := by
  have hmem : (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b ∈ openSegment ℝ a b :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  refine ⟨_, openSegment_subset_segment ℝ a b hmem, ?_, ?_⟩
  · intro h
    rw [h] at hmem
    exact hab (left_mem_openSegment_iff.1 hmem)
  · intro h
    rw [h] at hmem
    exact hab (right_mem_openSegment_iff.1 hmem)

/-- **Three collinear points meeting only at the shared one are in the order that makes the
middle one interior.** The alternative — the two segments running the same way out of `b` —
makes them overlap in a nondegenerate segment, which the meeting hypothesis forbids. -/
theorem mem_openSegment_of_det_eq_zero' {a b c : Plane} (hab : a ≠ b) (hcb : c ≠ b)
    (hmeet : segment ℝ a b ∩ segment ℝ b c ⊆ {a, b})
    (h : det (a - b) (c - b) = 0) : b ∈ openSegment ℝ a c := by
  have hab' : a - b ≠ 0 := sub_ne_zero.2 hab
  obtain ⟨r, hr⟩ := (det_eq_zero_iff_smul _ _ hab').1 h
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [zero_smul, sub_eq_zero] at hr
    exact hcb hr
  have hcexp : c = b + r • (a - b) := by linear_combination (norm := module) hr
  have hrneg : r < 0 := by
    rcases lt_trichotomy r 0 with hlt | heq | hgt
    · exact hlt
    · exact absurd heq hr0
    exfalso
    -- A short step out of `b` towards `a` is then also a step towards `c`.
    have hμpos : 0 < min 1 r / 2 := by positivity
    set μ : ℝ := min 1 r / 2 with hμdef
    have hμ1 : μ < 1 := by
      have h1 : min 1 r ≤ 1 := min_le_left _ _
      rw [hμdef]; linarith
    have hμler : μ / r < 1 := by
      rw [div_lt_one hgt]
      have h1 : min 1 r ≤ r := min_le_right _ _
      rw [hμdef]; linarith
    have hμr : μ / r * r = μ := div_mul_cancel₀ _ (ne_of_gt hgt)
    have hz₁ : μ • a + (1 - μ) • b ∈ segment ℝ a b :=
      ⟨μ, 1 - μ, hμpos.le, by linarith, by ring, rfl⟩
    have hz₂ : μ • a + (1 - μ) • b ∈ segment ℝ b c := by
      refine ⟨1 - μ / r, μ / r, by linarith, by positivity, by ring, ?_⟩
      have expand : (1 - μ / r) • b + (μ / r) • (b + r • (a - b))
          = (μ / r * r) • a + (1 - μ / r * r) • b := by module
      rw [hcexp, expand, hμr]
    have hmem := hmeet ⟨hz₁, hz₂⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with he | he
    · have hkey : (1 - μ) • (a - b) = 0 := by linear_combination (norm := module) -he
      rcases smul_eq_zero.1 hkey with h' | h'
      · exact (by linarith : (0 : ℝ) < 1 - μ).ne' h'
      · exact hab' h'
    · have hkey : μ • (a - b) = 0 := by linear_combination (norm := module) he
      rcases smul_eq_zero.1 hkey with h' | h'
      · exact hμpos.ne' h'
      · exact hab' h'
  -- Opposite directions: the vertex is a strict convex combination of its neighbours.
  have hden : (0 : ℝ) < 1 - r := by linarith
  refine ⟨-r / (1 - r), 1 / (1 - r), div_pos (by linarith) hden, div_pos one_pos hden,
    by field_simp; ring, ?_⟩
  have expand : (-r / (1 - r)) • a + (1 / (1 - r)) • (b + r • (a - b))
      = (-r / (1 - r) + 1 / (1 - r) * r) • a + (1 / (1 - r) - 1 / (1 - r) * r) • b := by module
  rw [hcexp, expand, show -r / (1 - r) + 1 / (1 - r) * r = 0 by field_simp; ring,
    show (1 : ℝ) / (1 - r) - 1 / (1 - r) * r = 1 by field_simp, zero_smul, one_smul, zero_add]

variable {m : ℕ} {P : PrePolygon m}

/-- **A redundant vertex is interior to the segment joining its neighbours.** -/
theorem mem_openSegment_of_det_eq_zero (i : ZMod (m + 3))
    (h : det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) = 0) :
    P.vertex i ∈ openSegment ℝ (P.vertex (i - 1)) (P.vertex (i + 1)) := by
  have hpred : i - 1 + 1 = i := sub_add_cancel i 1
  have hne : i - 1 ≠ i := fun he =>
    ClosedPolygon.succ_ne_self (i - 1) (by rw [hpred]; exact he.symm)
  have hmeet := P.edges_meet (i - 1) i hne
  rw [hpred] at hmeet
  exact mem_openSegment_of_det_eq_zero' (fun he => hne (P.vertex_inj he))
    (fun he => ClosedPolygon.succ_ne_self i (P.vertex_inj he)) hmeet h

/-! ## Normalization

Delete redundant vertices until none is left. Each deletion shortens the list by one, and the
list can never shrink below three vertices: a triangle with a redundant vertex would have one
edge inside another, which `edges_meet` forbids. -/

/-- A three-vertex polygon has no redundant vertex: were the last one interior to the segment
joining the other two, the edge before it would lie inside the edge opposite it. -/
theorem not_collinear_triangle (P : PrePolygon 0) :
    P.vertex (-1) ∉ openSegment ℝ (P.vertex (-1 - 1)) (P.vertex 0) := by
  intro hcol
  have e1 : (-1 - 1 : ZMod (0 + 3)) + 1 = -1 := by decide
  have e2 : (-1 : ZMod (0 + 3)) ≠ -1 - 1 := by decide
  have hsplit : segment ℝ (P.vertex (-1 - 1)) (P.vertex 0)
      = segment ℝ (P.vertex (-1 - 1)) (P.vertex (-1)) ∪ segment ℝ (P.vertex (-1)) (P.vertex 0) :=
    segment_split (openSegment_subset_segment ℝ _ _ hcol)
  -- The edge before the redundant vertex sits inside the edge opposite it.
  have hsub : P.edge (-1 - 1) ⊆ P.edge (-1 - 1 - 1) := by
    have e3 : (-1 - 1 - 1 : ZMod (0 + 3)) = 0 := by decide
    have e4 : (0 : ZMod (0 + 3)) + 1 = -1 - 1 := by decide
    rw [edge, edge, e1, e3, e4, segment_symm ℝ (P.vertex 0) (P.vertex (-1 - 1)), hsplit]
    exact Set.subset_union_left
  obtain ⟨p, hp, hp1, hp2⟩ := exists_mem_segment_ne (P.vertex_ne_succ (-1 - 1))
  rcases P.edges_meet (-1 - 1) (-1 - 1 - 1) (by decide) ⟨hp, hsub hp⟩ with h | h
  exacts [hp1 h, hp2 h]

/-- **Every `PrePolygon` normalizes to a `ClosedPolygon` with the same carrier.** This is the
blueprint's "delete redundant vertices at which two consecutive edges are collinear", run to
completion; the induction is on the number of vertices, which each deletion lowers by one. -/
theorem exists_closedPolygon_of_prePolygon :
    ∀ (m : ℕ) (P : PrePolygon m), ∃ (m' : ℕ) (P' : ClosedPolygon m'), P'.carrier = P.carrier := by
  intro m
  induction m with
  | zero =>
    intro P
    by_cases hc : ∀ i : ZMod (0 + 3),
        det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) ≠ 0
    · exact ⟨0, ⟨P.vertex, P.vertex_inj, P.edges_meet, hc⟩, rfl⟩
    · push Not at hc
      obtain ⟨i, hi⟩ := hc
      refine absurd ?_ (not_collinear_triangle (P.rotate (i + 1)))
      have e1 : i + 1 + (-1 : ZMod (0 + 3)) = i := by ring
      have e2 : i + 1 + (-1 - 1 : ZMod (0 + 3)) = i - 1 := by ring
      have e3 : i + 1 + (0 : ZMod (0 + 3)) = i + 1 := by ring
      rw [rotate_vertex, rotate_vertex, rotate_vertex, e1, e2, e3]
      exact mem_openSegment_of_det_eq_zero i hi
  | succ m ih =>
    intro P
    by_cases hc : ∀ i : ZMod (m + 1 + 3),
        det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) ≠ 0
    · exact ⟨m + 1, ⟨P.vertex, P.vertex_inj, P.edges_meet, hc⟩, rfl⟩
    · push Not at hc
      obtain ⟨i, hi⟩ := hc
      have hcol : (P.rotate (i + 1)).vertex (-1) ∈
          openSegment ℝ ((P.rotate (i + 1)).vertex (-1 - 1)) ((P.rotate (i + 1)).vertex 0) := by
        have e1 : i + 1 + (-1 : ZMod (m + 1 + 3)) = i := by ring
        have e2 : i + 1 + (-1 - 1 : ZMod (m + 1 + 3)) = i - 1 := by ring
        have e3 : i + 1 + (0 : ZMod (m + 1 + 3)) = i + 1 := by ring
        rw [rotate_vertex, rotate_vertex, rotate_vertex, e1, e2, e3]
        exact mem_openSegment_of_det_eq_zero i hi
      obtain ⟨m', P', hP'⟩ := ih (deleteLast (P.rotate (i + 1)) hcol)
      exact ⟨m', P', by rw [hP', carrier_deleteLast, carrier_rotate]⟩

/-- Assembling a cyclic vertex family into a `PrePolygon`. The index type is `ZMod n` for an
`n` known only to be at least three, which is what `PrePolygon` asks for after `n` is written
`m + 3`. -/
theorem exists_prePolygon {n : ℕ} (hn : 3 ≤ n) (w : ZMod n → Plane) (hinj : Function.Injective w)
    (hmeet : ∀ i j : ZMod n, i ≠ j →
      segment ℝ (w i) (w (i + 1)) ∩ segment ℝ (w j) (w (j + 1)) ⊆ {w i, w (i + 1)}) :
    ∃ (m : ℕ) (P : PrePolygon m), P.carrier = ⋃ i, segment ℝ (w i) (w (i + 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  exact ⟨m, ⟨w, hinj, hmeet⟩, rfl⟩

end PrePolygon

/-! ## Clean pieces

The overlay of `Schoenflies/OverlayGraph.lean`, stripped of the graph. All that is wanted from
it is a finite list of segments occupying the curve whose interiors are pairwise disjoint and
none of whose ends is interior to any of them — the geometric content of `lem:polygonal-overlay`
with the combinatorics left out. -/

/-- A finite list of segments presenting a polygonal set as a plane graph would: occupying it,
nondegenerate, with pairwise disjoint interiors, and with no end interior to any piece. -/
structure IsClean (Q : List Piece) (C : Set Plane) : Prop where
  /-- The pieces occupy the set. -/
  cover_eq : cover Q = C
  /-- No piece is a point. -/
  nondeg : ∀ R ∈ Q, R.Nondeg
  /-- No end of any piece is interior to any piece. -/
  ends : ∀ R ∈ Q, ∀ S ∈ Q, ∀ z, (z = R.1 ∨ z = R.2) → z ∉ S.interior
  /-- Distinct pieces have disjoint interiors. -/
  interiors : ∀ R ∈ Q, ∀ S ∈ Q, R ≠ S → ∀ x ∈ R.interior, x ∉ S.interior

/-- **Every polygonal set with two points in it has a clean presentation**, and any finite list
of points of it may be required to be among the ends. Lengthening the cut list is free: both
`EndsAreCut` and `MeetsAreCut` only ask that certain points *occur* in it. -/
theorem exists_isClean {C : Set Plane} (hC : IsPolygonal C) {a b : Plane} (ha : a ∈ C)
    (hb : b ∈ C) (hab : a ≠ b) (extra : List Plane) :
    ∃ Q : List Piece, IsClean Q C ∧ ∀ p ∈ extra, p ∈ C → ∃ R ∈ Q, p = R.1 ∨ p = R.2 := by
  obtain ⟨vs, rfl⟩ := hC
  have hnd : ∀ P ∈ segsOf vs, P.Nondeg := segsOf_nondeg vs
  have hcov : cover (segsOf vs) = poly vs := cover_segsOf_eq ha hb hab
  obtain ⟨pts, hEnds, hMeets⟩ := exists_cut_points (segsOf vs)
  refine ⟨overlayPieces (segsOf vs) (pts ++ extra), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [overlayPieces_cover, hcov]
  · exact overlayPieces_nondeg _ hnd
  · intro R hR S hS z hz
    exact overlayPieces_avoids hnd z
      (overlayPieces_ends_cut (fun P hP y hy => List.mem_append_left _ (hEnds P hP y hy)) R hR z hz)
      S hS
  · intro R hR S hS hRS x hx
    refine overlayPieces_disjoint_interiors hnd
      (fun P hP y hy => List.mem_append_left _ (hEnds P hP y hy)) (fun P hP Q hQ hPQ hne => ?_)
      hR hS hRS hx
    obtain ⟨u, v, huv, hu, hv⟩ := hMeets P hP Q hQ hPQ hne
    exact ⟨u, v, huv, List.mem_append_left _ hu, List.mem_append_left _ hv⟩
  · -- A required point lies on some piece and is interior to none, hence is an end of one.
    intro p hp hpC
    have hpts : p ∈ pts ++ extra := List.mem_append_right _ hp
    have hpcov : p ∈ cover (overlayPieces (segsOf vs) (pts ++ extra)) := by
      rw [overlayPieces_cover, hcov]; exact hpC
    obtain ⟨R, hR, hpR⟩ := ClosedPolygon.exists_of_mem_cover hpcov
    refine ⟨R, hR, ?_⟩
    by_contra hcon
    push Not at hcon
    exact overlayPieces_avoids hnd p hpts R hR
      (mem_openSegment_of_ne_left_right (Ne.symm hcon.1) (Ne.symm hcon.2) hpR)

/-- A point of a piece is interior to it or one of its ends. -/
theorem mem_interior_or_end {R : Piece} {x : Plane} (hx : x ∈ R.seg) :
    x ∈ R.interior ∨ x = R.1 ∨ x = R.2 := by
  by_cases hcon : x = R.1 ∨ x = R.2
  · exact Or.inr hcon
  · push Not at hcon
    exact Or.inl (mem_openSegment_of_ne_left_right (Ne.symm hcon.1) (Ne.symm hcon.2) hx)

/-- The open set that isolates one piece from the others: the union of the balls in which the
curve is that piece alone. -/
def nearPiece (C : Set Plane) (R : Piece) : Set Plane :=
  {y | ∃ x ∈ R.interior, ∃ r > 0, y ∈ ball x r ∧ ball x r ∩ C ⊆ R.seg}

theorem isOpen_nearPiece {C : Set Plane} {R : Piece} : IsOpen (nearPiece C R) := by
  rw [isOpen_iff_forall_mem_open]
  rintro y ⟨x, hx, r, hr, hyb, hsub⟩
  exact ⟨ball x r, fun z hz => ⟨x, hx, r, hr, hz, hsub⟩, isOpen_ball, hyb⟩

namespace IsClean

variable {Q : List Piece} {C : Set Plane} {R S : Piece} {x : Plane} (h : IsClean Q C)
include h

/-- **Two distinct clean pieces meet only at ends of the first.** This is `edges_meet`, before
the pieces have been put in cyclic order. -/
theorem seg_inter_subset (hR : R ∈ Q) (hS : S ∈ Q) (hRS : R ≠ S) :
    R.seg ∩ S.seg ⊆ {R.1, R.2} := by
  rintro z ⟨hzR, hzS⟩
  rcases mem_interior_or_end hzR with hz | hz
  · exfalso
    rcases mem_interior_or_end hzS with hz' | hz'
    · exact h.interiors R hR S hS hRS z hz hz'
    · exact h.ends S hS R hR z hz' hz
  · exact hz

theorem seg_subset (hR : R ∈ Q) : R.seg ⊆ C := by
  rw [← h.cover_eq]
  exact fun z hz => mem_cover hR hz

theorem endSet_subset : endSet Q ⊆ C := by
  rintro z ⟨R, hR, hz⟩
  rcases hz with rfl | rfl
  exacts [h.seg_subset hR (left_mem_segment ℝ _ _), h.seg_subset hR (right_mem_segment ℝ _ _)]

theorem mem_cover_of_mem (hz : x ∈ C) : x ∈ cover Q := by rw [h.cover_eq]; exact hz

/-- **The curve minus the ends is the disjoint union of the piece interiors.** -/
theorem diff_endSet_eq : C \ endSet Q = ⋃ R ∈ Q, R.interior := by
  refine Set.Subset.antisymm (fun z hz => ?_) (fun z hz => ?_)
  · obtain ⟨R, hR, hzR⟩ := ClosedPolygon.exists_of_mem_cover (h.mem_cover_of_mem hz.1)
    refine Set.mem_iUnion₂.2 ⟨R, hR, ?_⟩
    rcases mem_interior_or_end hzR with hz' | hz'
    · exact hz'
    · exact absurd (show z ∈ endSet Q from ⟨R, hR, hz'⟩) hz.2
  · obtain ⟨R, hR, hzR⟩ := Set.mem_iUnion₂.1 hz
    exact ⟨h.seg_subset hR (openSegment_subset_segment ℝ _ _ hzR),
      fun ⟨S, hS, hz'⟩ => h.ends S hS R hR z hz' hzR⟩

/-- **Near an interior point the curve is that piece alone.** The other pieces are finitely many
closed sets missing the point: interior points are not shared, and an end of another piece
cannot be interior to this one. -/
theorem exists_ball_subset_seg (hR : R ∈ Q) (hx : x ∈ R.interior) :
    ∃ r > 0, ball x r ∩ C ⊆ R.seg := by
  have hmiss : ∀ S ∈ Q, S ≠ R → x ∉ S.seg := by
    intro S hS hSR hxS
    rcases mem_interior_or_end hxS with hz | hz
    · exact h.interiors S hS R hR hSR x hz hx
    · exact h.ends S hS R hR x hz hx
  obtain ⟨r, hr, hball⟩ := exists_pos_forall_of_finite
    (S := {S : Piece | S ∈ Q ∧ S ≠ R}) (Q.finite_toSet.subset fun _ hS => hS.1)
    (P := fun S ε => ∀ y ∈ ball x ε, y ∉ S.seg)
    (fun _ _ _ _ hδε hP y hy => hP y (ball_subset_ball hδε hy))
    (fun S hS => by
      obtain ⟨ρ, hρ, hsub⟩ := Metric.isOpen_iff.1
        (isCompact_segment S.1 S.2).isClosed.isOpen_compl x (hmiss S hS.1 hS.2)
      exact ⟨ρ, hρ, fun y hy => hsub hy⟩)
  refine ⟨r, hr, ?_⟩
  rintro z ⟨hzb, hzC⟩
  obtain ⟨S, hS, hzS⟩ := ClosedPolygon.exists_of_mem_cover (h.mem_cover_of_mem hzC)
  by_cases hSR : S = R
  · exact hSR ▸ hzS
  · exact absurd hzS (hball S ⟨hS, hSR⟩ z hzb)

theorem interior_subset_nearPiece (hR : R ∈ Q) : R.interior ⊆ nearPiece C R := by
  intro y hy
  obtain ⟨r, hr, hsub⟩ := h.exists_ball_subset_seg hR hy
  exact ⟨y, hy, r, hr, mem_ball_self hr, hsub⟩

omit h in
theorem nearPiece_inter_diff (hR : R ∈ Q) : nearPiece C R ∩ (C \ endSet Q) ⊆ R.interior := by
  rintro z ⟨⟨y, hy, r, hr, hzb, hsub⟩, hzC, hzV⟩
  rcases mem_interior_or_end (hsub ⟨hzb, hzC⟩) with hz | hz
  · exact hz
  · exact absurd (show z ∈ endSet Q from ⟨R, hR, hz⟩) hzV

/-- **A connected piece of the curve away from the ends lies inside a single piece.** The
`nearPiece` sets are honest open sets of the plane that trace out the pieces on the curve, so
`IsPreconnected` can be applied to them directly. -/
theorem preconnected_subset_interior {A : Set Plane} (hA : IsPreconnected A) (hA0 : A.Nonempty)
    (hAsub : A ⊆ C \ endSet Q) : ∃ R ∈ Q, A ⊆ R.interior := by
  obtain ⟨x₀, hx₀⟩ := hA0
  have hAint : A ⊆ ⋃ R ∈ Q, R.interior := by rw [← h.diff_endSet_eq]; exact hAsub
  obtain ⟨R, hR, hx₀R⟩ := Set.mem_iUnion₂.1 (hAint hx₀)
  refine ⟨R, hR, ?_⟩
  set W : Set Plane := ⋃ S ∈ {S : Piece | S ∈ Q ∧ S ≠ R}, nearPiece C S with hW
  have hWopen : IsOpen W := isOpen_biUnion fun _ _ => isOpen_nearPiece
  have hcover : A ⊆ nearPiece C R ∪ W := by
    intro z hz
    obtain ⟨S, hS, hzS⟩ := Set.mem_iUnion₂.1 (hAint hz)
    by_cases hSR : S = R
    · exact Or.inl (h.interior_subset_nearPiece hR (hSR ▸ hzS))
    · exact Or.inr (Set.mem_iUnion₂.2 ⟨S, ⟨hS, hSR⟩, h.interior_subset_nearPiece hS hzS⟩)
  have hempty : ¬ (A ∩ (nearPiece C R ∩ W)).Nonempty := by
    rintro ⟨z, hzA, hzR, hzW⟩
    obtain ⟨S, hS, hzS⟩ := Set.mem_iUnion₂.1 hzW
    exact h.interiors R hR S hS.1 (Ne.symm hS.2) z (nearPiece_inter_diff hR ⟨hzR, hAsub hzA⟩)
      (nearPiece_inter_diff hS.1 ⟨hzS, hAsub hzA⟩)
  have hnotW : ¬ (A ∩ W).Nonempty := fun hv =>
    hempty (hA _ _ isOpen_nearPiece hWopen hcover ⟨x₀, hx₀, h.interior_subset_nearPiece hR hx₀R⟩ hv)
  intro z hz
  refine nearPiece_inter_diff hR ⟨?_, hAsub hz⟩
  exact (hcover hz).resolve_right fun hzW => hnotW ⟨z, hz, hzW⟩

end IsClean

/-! ## The gaps between the parameters

The loop's parameters at which it visits an end of a piece form a finite subset of `[0, 1)`
containing `0`. Listed in increasing order they cut `[0, 1)` into gaps, one per piece; the last
gap runs to `1`, where the loop closes. This section is pure order theory on `ℝ`. -/

section Gaps

variable {n : ℕ} {T : Finset ℝ} (hcard : T.card = n)

/-- The `i`-th parameter, in increasing order. -/
noncomputable def par (T : Finset ℝ) (hcard : T.card = n) (i : Fin n) : ℝ :=
  T.orderEmbOfFin hcard i

/-- The right end of the `i`-th gap: the next parameter, or `1` for the last gap. -/
noncomputable def parNext (T : Finset ℝ) (hcard : T.card = n) (i : Fin n) : ℝ :=
  if h : (i : ℕ) + 1 < n then T.orderEmbOfFin hcard ⟨(i : ℕ) + 1, h⟩ else 1

theorem par_mem (i : Fin n) : par T hcard i ∈ T := T.orderEmbOfFin_mem hcard i

theorem par_lt_par {i j : Fin n} (h : i < j) : par T hcard i < par T hcard j :=
  (T.orderEmbOfFin hcard).strictMono h

theorem par_lt_iff {i j : Fin n} : par T hcard i < par T hcard j ↔ i < j :=
  (T.orderEmbOfFin hcard).lt_iff_lt

theorem par_le_par {i j : Fin n} (h : i ≤ j) : par T hcard i ≤ par T hcard j :=
  (T.orderEmbOfFin hcard).monotone h

theorem exists_par_eq {s : ℝ} (hs : s ∈ T) : ∃ i : Fin n, par T hcard i = s := by
  have := T.range_orderEmbOfFin hcard
  rw [Set.ext_iff] at this
  exact (this s).2 hs

variable (hT : ∀ s ∈ T, s ∈ Ico (0 : ℝ) 1) (h0 : (0 : ℝ) ∈ T)
include hcard hT h0

omit hT in
theorem par_card_pos : 0 < n := by
  rw [← hcard]
  exact Finset.card_pos.2 ⟨0, h0⟩

/-- The first parameter is `0`: the loop is at a vertex when it starts. -/
theorem par_zero : par T hcard ⟨0, par_card_pos hcard h0⟩ = 0 := by
  rw [par, Finset.orderEmbOfFin_zero hcard (par_card_pos hcard h0)]
  exact le_antisymm (Finset.min'_le _ _ h0)
    (Finset.le_min' _ _ _ fun s hs => (hT s hs).1)

omit h0 in
theorem parNext_le_one (i : Fin n) : parNext T hcard i ≤ 1 := by
  rw [parNext]
  split_ifs with hi
  · exact le_of_lt (hT _ (T.orderEmbOfFin_mem hcard _)).2
  · exact le_refl 1

omit h0 in
theorem par_lt_parNext (i : Fin n) : par T hcard i < parNext T hcard i := by
  rw [parNext]
  split_ifs with hi
  · exact par_lt_par hcard (by exact Fin.mk_lt_mk.2 (Nat.lt_succ_self _) : i < ⟨(i : ℕ) + 1, hi⟩)
  · exact (hT _ (par_mem hcard i)).2

omit hT h0 in
/-- No parameter lies strictly inside a gap. -/
theorem notMem_of_mem_gap {i : Fin n} {s : ℝ} (hs : s ∈ Ioo (par T hcard i) (parNext T hcard i)) :
    s ∉ T := by
  intro hsT
  obtain ⟨j, rfl⟩ := exists_par_eq hcard hsT
  have hij : i < j := (par_lt_iff hcard).1 hs.1
  rw [parNext] at hs
  split_ifs at hs with hi
  · exact absurd hs.2 (not_lt.2 (par_le_par hcard (by exact Fin.mk_le_of_le_val hij)))
  · exact absurd j.isLt (by omega)

omit hT h0 in
/-- Distinct gaps are disjoint. -/
theorem gap_disjoint {i j : Fin n} (hij : i ≠ j) :
    Disjoint (Ioo (par T hcard i) (parNext T hcard i))
      (Ioo (par T hcard j) (parNext T hcard j)) := by
  -- One of the two comes first; its right end is at most the other's left end.
  have key : ∀ a b : Fin n, a < b → parNext T hcard a ≤ par T hcard b := by
    intro a b hab
    rw [parNext]
    split_ifs with ha
    · exact par_le_par hcard (Fin.mk_le_of_le_val hab)
    · exact absurd b.isLt (by omega)
  rw [Set.disjoint_left]
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact fun x hx hx' => absurd (lt_of_lt_of_le hx.2 (key i j hlt)) (not_lt.2 hx'.1.le)
  · exact fun x hx hx' => absurd (lt_of_lt_of_le hx'.2 (key j i hlt)) (not_lt.2 hx.1.le)

omit h0 in
theorem gap_subset_Ico (i : Fin n) :
    Ioo (par T hcard i) (parNext T hcard i) ⊆ Ico (0 : ℝ) 1 := fun _ hs =>
  ⟨le_of_lt (lt_of_le_of_lt (hT _ (par_mem hcard i)).1 hs.1),
    lt_of_lt_of_le hs.2 (parNext_le_one hcard hT i)⟩

omit h0 in
theorem gapClosure_subset_I (i : Fin n) :
    Icc (par T hcard i) (parNext T hcard i) ⊆ I := by
  intro s hs
  exact ⟨le_trans (hT _ (par_mem hcard i)).1 hs.1, le_trans hs.2 (parNext_le_one hcard hT i)⟩

/-- **The gaps cover `[0, 1)` minus the parameters.** The gap containing `s` starts at the
largest parameter below `s`. -/
theorem exists_mem_gap {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) (hsT : s ∉ T) :
    ∃ i : Fin n, s ∈ Ioo (par T hcard i) (parNext T hcard i) := by
  classical
  have hn : 0 < n := par_card_pos hcard h0
  -- The gap containing `s` starts at the largest parameter below it.
  obtain ⟨i₀, hi₀le, hi₀max⟩ : ∃ i₀ : Fin n, par T hcard i₀ ≤ s ∧
      ∀ j : Fin n, par T hcard j ≤ s → j ≤ i₀ := by
    have hSne : (Finset.univ.filter fun i : Fin n => par T hcard i ≤ s).Nonempty :=
      ⟨⟨0, hn⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _,
        by rw [par_zero hcard hT h0]; exact hs.1⟩⟩
    exact ⟨_, (Finset.mem_filter.1 (Finset.max'_mem _ hSne)).2,
      fun j hj => Finset.le_max' _ j (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩)⟩
  refine ⟨i₀, lt_of_le_of_ne hi₀le fun he => hsT (he ▸ par_mem hcard _), ?_⟩
  rw [parNext]
  split_ifs with hi
  · by_contra hcon
    push Not at hcon
    exact absurd (hi₀max ⟨(i₀ : ℕ) + 1, hi⟩ hcon)
      (not_le.2 (Fin.lt_def.2 (Nat.lt_succ_self _)))
  · exact hs.2

end Gaps

/-- A closed interval is its interior together with its two ends. -/
theorem Icc_eq_Ioo_union_ends {a b : ℝ} (hab : a ≤ b) : Icc a b = Ioo a b ∪ {a, b} := by
  ext x
  simp only [mem_Icc, mem_union, mem_Ioo, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    rcases eq_or_lt_of_le h1 with rfl | h1'
    · exact Or.inr (Or.inl rfl)
    · rcases eq_or_lt_of_le h2 with rfl | h2'
      · exact Or.inr (Or.inr rfl)
      · exact Or.inl ⟨h1', h2'⟩
  · rintro (⟨h1, h2⟩ | rfl | rfl)
    · exact ⟨h1.le, h2.le⟩
    · exact ⟨le_refl _, hab⟩
    · exact ⟨hab, le_refl _⟩

/-- Two points of a nondegenerate pair, each known to be one of two given points, exhaust
them. -/
theorem pair_eq_of_mem_pair {a b p q : Plane} (hab : a ≠ b) (ha : a = p ∨ a = q)
    (hb : b = p ∨ b = q) : (a = p ∧ b = q) ∨ (a = q ∧ b = p) := by
  rcases ha with rfl | rfl
  · rcases hb with rfl | rfl
    · exact absurd rfl hab
    · exact Or.inl ⟨rfl, rfl⟩
  · rcases hb with rfl | rfl
    · exact Or.inr ⟨rfl, rfl⟩
    · exact absurd rfl hab

/-- The successor in `ZMod n`, read as a numeral below `n`. -/
theorem zmod_val_succ {n : ℕ} (hn : 1 < n) (j : ZMod n) :
    (j + 1).val = if j.val + 1 < n then j.val + 1 else 0 := by
  haveI : NeZero n := ⟨by omega⟩
  have h1 : (1 : ZMod n).val = 1 := by
    rw [show (1 : ZMod n) = ((1 : ℕ) : ZMod n) by norm_num]
    exact ZMod.val_cast_of_lt hn
  rw [ZMod.val_add, h1]
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · have hj : j.val + 1 = n := by have := ZMod.val_lt j; omega
    rw [hj, Nat.mod_self]

/-! ## From a clean presentation to a cyclic vertex list

The loop reaches an end of a piece at finitely many parameters. Between two consecutive ones it
runs through one whole piece interior — the gap image is connected and misses the ends, so it
lies in one interior; and the interior, being connected and covered by the closed gap images,
lies in that one gap. So the ends, listed in the order the loop reaches them, are the cyclic
vertex list of a `PrePolygon` whose edges are the pieces. -/

/-- **A polygonal Jordan curve is the carrier of a cyclic vertex list.** -/
theorem exists_prePolygon_of_isJordanCurve {C : Set Plane} (hJ : IsJordanCurve C)
    (hP : IsPolygonal C) : ∃ (m : ℕ) (P : PrePolygon m), P.carrier = C := by
  classical
  obtain ⟨f, hf, hfC⟩ := hJ
  -- Two distinct points of `C`, so that the clean presentation does not collapse.
  have hmemC : ∀ s ∈ I, f s ∈ C := fun s hs => hfC ▸ ⟨s, hs, rfl⟩
  have h0C : f 0 ∈ C := hmemC 0 zero_mem_I
  have hhC : f (1 / 2) ∈ C := hmemC _ ⟨by norm_num, by norm_num⟩
  have hne : f 0 ≠ f (1 / 2) := fun he =>
    absurd (hf.injOn ⟨le_refl 0, by norm_num⟩ ⟨by norm_num, by norm_num⟩ he) (by norm_num)
  obtain ⟨Q, hQ, hextra⟩ := exists_isClean hP h0C hhC hne [f 0]
  obtain ⟨R₀, hR₀, hR₀end⟩ := hextra (f 0) (List.mem_singleton_self _) h0C
  have hV₀ : f 0 ∈ endSet Q := ⟨R₀, hR₀, hR₀end⟩
  -- Every point of the curve is reached before the loop closes.
  have hsurj : ∀ z ∈ C, ∃ s ∈ Ico (0 : ℝ) 1, f s = z := by
    intro z hz
    rw [← hfC] at hz
    obtain ⟨s, hs, rfl⟩ := hz
    rcases eq_or_lt_of_le hs.2 with rfl | hlt
    · exact ⟨0, ⟨le_refl 0, by norm_num⟩, hf.closes⟩
    · exact ⟨s, ⟨hs.1, hlt⟩, rfl⟩
  -- The parameters at which the loop is at an end of a piece.
  have hTfin : {t : ℝ | t ∈ Ico (0 : ℝ) 1 ∧ f t ∈ endSet Q}.Finite := by
    refine Set.Finite.of_finite_image (f := f) ((finite_endSet Q).subset ?_)
      (hf.injOn.mono fun t ht => ht.1)
    rintro x ⟨t, ht, rfl⟩
    exact ht.2
  obtain ⟨n, hcard⟩ : ∃ n, hTfin.toFinset.card = n := ⟨_, rfl⟩
  set TF : Finset ℝ := hTfin.toFinset with hTFdef
  have hmemTF : ∀ t : ℝ, t ∈ TF ↔ (t ∈ Ico (0 : ℝ) 1 ∧ f t ∈ endSet Q) := by
    intro t; rw [hTFdef, Set.Finite.mem_toFinset]; exact Iff.rfl
  have hTle : ∀ s ∈ TF, s ∈ Ico (0 : ℝ) 1 := fun s hs => ((hmemTF s).1 hs).1
  have h0TF : (0 : ℝ) ∈ TF := (hmemTF 0).2 ⟨⟨le_refl 0, by norm_num⟩, hV₀⟩
  set tp : Fin n → ℝ := par TF hcard with htp
  set nx : Fin n → ℝ := parNext TF hcard with hnx
  -- Both ends of every gap are ends of pieces.
  have htpV : ∀ i : Fin n, f (tp i) ∈ endSet Q := fun i =>
    ((hmemTF _).1 (par_mem hcard i)).2
  have hnxV : ∀ i : Fin n, f (nx i) ∈ endSet Q := by
    intro i
    rw [hnx, parNext]
    split_ifs with hi
    · exact ((hmemTF _).1 (Finset.orderEmbOfFin_mem _ _ _)).2
    · rw [← hf.closes]; exact hV₀
  have hlt : ∀ i : Fin n, tp i < nx i := fun i => par_lt_parNext hcard hTle i
  have hIcc : ∀ i : Fin n, Icc (tp i) (nx i) ⊆ I := fun i => gapClosure_subset_I hcard hTle i
  have hIoo : ∀ i : Fin n, Ioo (tp i) (nx i) ⊆ Ico (0 : ℝ) 1 := fun i =>
    gap_subset_Ico hcard hTle i
  set G : Fin n → Set Plane := fun i => f '' Ioo (tp i) (nx i) with hG
  set Z : Fin n → Set Plane := fun i => f '' Icc (tp i) (nx i) with hZ
  have hGne : ∀ i, (G i).Nonempty := fun i =>
    ((Set.nonempty_Ioo.2 (hlt i)).image f)
  have hGconn : ∀ i, IsPreconnected (G i) := fun i =>
    isPreconnected_Ioo.image f (hf.continuousOn.mono (fun s hs => hIcc i (Ioo_subset_Icc_self hs)))
  have hGdiff : ∀ i, G i ⊆ C \ endSet Q := by
    rintro i z ⟨s, hs, rfl⟩
    refine ⟨hmemC s (hIcc i (Ioo_subset_Icc_self hs)), fun hzV => ?_⟩
    exact notMem_of_mem_gap hcard hs ((hmemTF s).2 ⟨hIoo i hs, hzV⟩)
  have hZcompact : ∀ i, IsCompact (Z i) := fun i =>
    isCompact_image_of_subset_I hf.continuousOn (hIcc i) isClosed_Icc
  have hZeq : ∀ i, Z i = G i ∪ {f (tp i), f (nx i)} := by
    intro i
    simp only [hZ, hG]
    rw [Icc_eq_Ioo_union_ends (hlt i).le, Set.image_union, Set.image_pair]
  have hZdiff : ∀ i, Z i ∩ (C \ endSet Q) = G i := by
    intro i
    refine Set.Subset.antisymm ?_ (fun z hz => ⟨(hZeq i) ▸ Or.inl hz, hGdiff i hz⟩)
    rintro z ⟨hzZ, hzC, hzV⟩
    rcases (hZeq i) ▸ hzZ with hz | hz
    · exact hz
    · rcases hz with rfl | rfl
      exacts [absurd (htpV i) hzV, absurd (hnxV i) hzV]
  have hGdisj : ∀ i j : Fin n, i ≠ j → G i ∩ G j = ∅ := by
    intro i j hij
    refine Set.eq_empty_of_forall_notMem ?_
    rintro z ⟨⟨s, hs, rfl⟩, t, ht, hts⟩
    have := hf.injOn (hIoo j ht) (hIoo i hs) hts
    exact Set.disjoint_left.1 (gap_disjoint hcard hij) hs (this ▸ ht)
  -- The gaps cover the curve away from the ends of the pieces.
  have hcov : (⋃ i, G i) = C \ endSet Q := by
    refine Set.Subset.antisymm (Set.iUnion_subset hGdiff) (fun z hz => ?_)
    obtain ⟨s, hs, rfl⟩ := hsurj z hz.1
    obtain ⟨i, hi⟩ := exists_mem_gap hcard hTle h0TF hs
      (fun hsT => hz.2 ((hmemTF s).1 hsT).2)
    exact Set.mem_iUnion.2 ⟨i, ⟨s, hi, rfl⟩⟩
  -- Each gap image lies in one piece interior.
  have hchoose : ∀ i, ∃ R ∈ Q, G i ⊆ R.interior := fun i =>
    hQ.preconnected_subset_interior (hGconn i) (hGne i) (hGdiff i)
  choose pc hpcQ hpcsub using hchoose
  -- And is the whole of it: the interior is connected and covered by the closed gap images.
  have hpceq : ∀ i, (pc i).interior = G i := by
    intro i
    refine Set.Subset.antisymm ?_ (hpcsub i)
    set W : Set Plane := ⋃ j ∈ ({i}ᶜ : Set (Fin n)), Z j with hW
    have hWclosed : IsClosed W :=
      Set.Finite.isClosed_biUnion (Set.toFinite _) fun j _ => (hZcompact j).isClosed
    have hAdiff : (pc i).interior ⊆ C \ endSet Q := by
      rw [hQ.diff_endSet_eq]
      exact fun z hz => Set.mem_iUnion₂.2 ⟨pc i, hpcQ i, hz⟩
    have hAZ : (pc i).interior ⊆ Z i ∪ W := by
      intro z hz
      obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hcov.symm ▸ hAdiff hz)
      by_cases hji : j = i
      · exact Or.inl ((hZeq i) ▸ Or.inl (hji ▸ hj))
      · exact Or.inr (Set.mem_iUnion₂.2 ⟨j, hji, (hZeq j) ▸ Or.inl hj⟩)
    have hGW : ∀ z ∈ G i, z ∉ W := by
      intro z hz hzW
      obtain ⟨j, hji, hzj⟩ := Set.mem_iUnion₂.1 hzW
      have : z ∈ G j := (hZdiff j) ▸ ⟨hzj, hGdiff i hz⟩
      exact Set.eq_empty_iff_forall_notMem.1 (hGdisj i j (Ne.symm hji)) z ⟨hz, this⟩
    have hcover2 : (pc i).interior ⊆ Wᶜ ∪ (Z i)ᶜ := by
      intro z hz
      by_cases hzW : z ∈ W
      · refine Or.inr fun hzZ => ?_
        exact hGW z ((hZdiff i) ▸ ⟨hzZ, hAdiff hz⟩) hzW
      · exact Or.inl hzW
    have hnone : ¬ ((pc i).interior ∩ (Wᶜ ∩ (Z i)ᶜ)).Nonempty := by
      rintro ⟨z, hz, hzW, hzZ⟩
      rcases hAZ hz with h | h
      exacts [hzZ h, hzW h]
    have hconv : IsPreconnected ((pc i).interior) :=
      (convex_openSegment _ _).isPreconnected
    obtain ⟨z₀, hz₀⟩ := hGne i
    have hAu : ((pc i).interior ∩ Wᶜ).Nonempty := ⟨z₀, hpcsub i hz₀, hGW z₀ hz₀⟩
    have hnotv : ¬ ((pc i).interior ∩ (Z i)ᶜ).Nonempty := fun hv =>
      hnone (hconv _ _ hWclosed.isOpen_compl (hZcompact i).isClosed.isOpen_compl hcover2 hAu hv)
    intro z hz
    have hzZ : z ∈ Z i := by
      by_contra hzZ
      exact hnotv ⟨z, hz, hzZ⟩
    exact (hZdiff i) ▸ ⟨hzZ, hAdiff hz⟩
  -- The correspondence between gaps and pieces is a bijection.
  have hpcinj : Function.Injective pc := by
    intro i j hij
    by_contra hne'
    obtain ⟨z, hz⟩ := hGne i
    have hzj : z ∈ G j := by rw [← hpceq j, ← hij, hpceq i]; exact hz
    exact Set.eq_empty_iff_forall_notMem.1 (hGdisj i j hne') z ⟨hz, hzj⟩
  have hpcsurj : ∀ R ∈ Q, ∃ i, pc i = R := by
    intro R hR
    have hx : (1 / 2 : ℝ) • R.1 + (1 / 2 : ℝ) • R.2 ∈ R.interior :=
      ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
    have hxd : (1 / 2 : ℝ) • R.1 + (1 / 2 : ℝ) • R.2 ∈ C \ endSet Q := by
      rw [hQ.diff_endSet_eq]; exact Set.mem_iUnion₂.2 ⟨R, hR, hx⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcov.symm ▸ hxd)
    refine ⟨i, ?_⟩
    by_contra hne'
    exact hQ.interiors (pc i) (hpcQ i) R hR hne' _ (hpceq i ▸ hi) hx
  -- The ends of the piece are the two ends of the gap.
  have hends : ∀ i, ((pc i).1 = f (tp i) ∧ (pc i).2 = f (nx i)) ∨
      ((pc i).1 = f (nx i) ∧ (pc i).2 = f (tp i)) := by
    intro i
    have hnd : (pc i).1 ≠ (pc i).2 := hQ.nondeg _ (hpcQ i)
    have hclosure : (pc i).seg ⊆ Z i := by
      have hcl : closure ((pc i).interior) ⊆ Z i := by
        rw [hpceq i]
        exact closure_minimal (fun z hz => (hZeq i) ▸ Or.inl hz) (hZcompact i).isClosed
      rwa [Piece.interior, closure_openSegment] at hcl
    have hmem : ∀ z, z = (pc i).1 ∨ z = (pc i).2 → z = f (tp i) ∨ z = f (nx i) := by
      intro z hz
      have hzseg : z ∈ (pc i).seg := by
        rcases hz with rfl | rfl
        exacts [left_mem_segment ℝ _ _, right_mem_segment ℝ _ _]
      rcases (hZeq i) ▸ hclosure hzseg with hzG | hzE
      · exfalso
        rw [← hpceq i] at hzG
        rcases hz with rfl | rfl
        exacts [hnd (left_mem_openSegment_iff.1 hzG), hnd (right_mem_openSegment_iff.1 hzG)]
      · simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hzE
    exact pair_eq_of_mem_pair hnd (hmem _ (Or.inl rfl)) (hmem _ (Or.inr rfl))
  have hpcseg : ∀ i, (pc i).seg = segment ℝ (f (tp i)) (f (nx i)) := by
    intro i
    rcases hends i with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [Piece.seg, h1, h2]
    · rw [Piece.seg, h1, h2, segment_symm]
  have hfne : ∀ i, f (tp i) ≠ f (nx i) := by
    intro i he
    refine hQ.nondeg _ (hpcQ i) ?_
    rcases hends i with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact he
    · rw [h1, h2]; exact he.symm
  -- There are at least three parameters.
  have hn0 : 0 < n := par_card_pos hcard h0TF
  have htp0 : tp ⟨0, hn0⟩ = 0 := par_zero hcard hTle h0TF
  have hn2 : 2 ≤ n := by
    rcases Nat.lt_or_ge n 2 with hlt2 | hge
    · exfalso
      have hcond : ¬ ((⟨0, hn0⟩ : Fin n) : ℕ) + 1 < n :=
        fun hc => absurd (lt_of_le_of_lt (Nat.le_add_left 1 _) hc) (by omega)
      have hnx0 : nx ⟨0, hn0⟩ = 1 := by rw [hnx, parNext, dif_neg hcond]
      exact hfne ⟨0, hn0⟩ (by rw [htp0, hnx0]; exact hf.closes)
    · exact hge
  haveI : NeZero n := ⟨by omega⟩
  -- The cyclic vertex list: the ends, in the order the loop reaches them.
  set w : ZMod n → Plane := fun j => f (tp ⟨j.val, ZMod.val_lt j⟩) with hw
  have hwsucc : ∀ j : ZMod n, w (j + 1) = f (nx ⟨j.val, ZMod.val_lt j⟩) := by
    intro j
    have hjlt := ZMod.val_lt j
    by_cases hj : j.val + 1 < n
    · have hval : (j + 1).val = j.val + 1 := by rw [zmod_val_succ (by omega) j, if_pos hj]
      have hfin : (⟨(j + 1).val, ZMod.val_lt (j + 1)⟩ : Fin n) = ⟨j.val + 1, hj⟩ :=
        Fin.val_injective hval
      simp only [hw, hfin]
      rw [hnx, parNext, dif_pos (show (⟨j.val, hjlt⟩ : Fin n).val + 1 < n from hj)]
      rfl
    · have hval : (j + 1).val = 0 := by rw [zmod_val_succ (by omega) j, if_neg hj]
      have hfin : (⟨(j + 1).val, ZMod.val_lt (j + 1)⟩ : Fin n) = ⟨0, hn0⟩ :=
        Fin.val_injective hval
      simp only [hw, hfin]
      rw [htp0, hnx, parNext, dif_neg (show ¬ ((⟨j.val, hjlt⟩ : Fin n).val + 1 < n) from hj)]
      exact hf.closes
  have hedgeq : ∀ j : ZMod n,
      segment ℝ (w j) (w (j + 1)) = (pc ⟨j.val, ZMod.val_lt j⟩).seg := by
    intro j
    rw [hwsucc j, hpcseg]
  have hwinj : Function.Injective w := by
    intro j k hjk
    simp only [hw] at hjk
    have h1 := hf.injOn (hTle _ (par_mem hcard ⟨j.val, ZMod.val_lt j⟩))
      (hTle _ (par_mem hcard ⟨k.val, ZMod.val_lt k⟩)) hjk
    exact ZMod.val_injective _ (congrArg Fin.val ((TF.orderEmbOfFin hcard).injective h1))
  have hwmeet : ∀ i j : ZMod n, i ≠ j →
      segment ℝ (w i) (w (i + 1)) ∩ segment ℝ (w j) (w (j + 1)) ⊆ {w i, w (i + 1)} := by
    intro i j hij
    rw [hedgeq i, hedgeq j]
    have hne' : pc ⟨i.val, ZMod.val_lt i⟩ ≠ pc ⟨j.val, ZMod.val_lt j⟩ := fun he =>
      hij (ZMod.val_injective _ (congrArg Fin.val (hpcinj he)))
    refine le_trans (hQ.seg_inter_subset (hpcQ _) (hpcQ _) hne') ?_
    have hwi : w i = f (tp ⟨i.val, ZMod.val_lt i⟩) := rfl
    rcases hends ⟨i.val, ZMod.val_lt i⟩ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2, ← hwi, ← hwsucc i]
    · rw [h1, h2, ← hwi, ← hwsucc i, Set.pair_comm]
  have hn3 : 3 ≤ n := by
    rcases Nat.lt_or_ge n 3 with hlt3 | hge
    · exfalso
      have hn2' : n = 2 := by omega
      have hone : (1 : ZMod n).val = 1 := by
        rw [show (1 : ZMod n) = ((1 : ℕ) : ZMod n) by norm_num]
        exact ZMod.val_cast_of_lt (by omega)
      have h01 : (0 : ZMod n) ≠ 1 := by
        intro he
        have hv : (0 : ZMod n).val = (1 : ZMod n).val := by rw [he]
        rw [ZMod.val_zero, hone] at hv
        omega
      have hsucc1 : (1 : ZMod n) + 1 = 0 := by
        refine ZMod.val_injective _ ?_
        rw [zmod_val_succ (by omega) 1, hone, if_neg (by omega), ZMod.val_zero]
      have hw01 : w 0 ≠ w 1 := fun he => h01 (hwinj he)
      obtain ⟨p, hp, hp1, hp2⟩ := PrePolygon.exists_mem_segment_ne hw01
      have hmem := hwmeet 0 1 h01
        ⟨by rw [zero_add]; exact hp, by rw [hsucc1, segment_symm]; exact hp⟩
      rw [zero_add] at hmem
      rcases hmem with h | h
      exacts [hp1 h, hp2 h]
    · exact hge
  -- Assemble.
  refine (PrePolygon.exists_prePolygon hn3 w hwinj hwmeet).imp fun m hm => hm.imp fun P hP => ?_
  rw [hP, ← hQ.cover_eq]
  refine Set.Subset.antisymm (Set.iUnion_subset fun j => ?_) ?_
  · rw [hedgeq j]
    exact fun z hz => mem_cover (hpcQ _) hz
  · rw [cover]
    refine Set.iUnion₂_subset fun R hR => ?_
    obtain ⟨i, rfl⟩ := hpcsurj R hR
    have hfin : (⟨((i.val : ℕ) : ZMod n).val, ZMod.val_lt _⟩ : Fin n) = i :=
      Fin.val_injective (ZMod.val_cast_of_lt i.isLt)
    refine le_trans (le_of_eq ?_)
      (Set.subset_iUnion (fun j : ZMod n => segment ℝ (w j) (w (j + 1))) ((i.val : ℕ) : ZMod n))
    rw [hedgeq, hfin]

/-! ## The realization theorem -/

/-- **Every simple closed polygonal curve is the carrier of a `ClosedPolygon`.** This is the
blueprint's set-level notion — `IsJordanCurve` together with `IsPolygonal`, no condition on
vertices — matched with the presentation the development works with. -/
theorem exists_closedPolygon {C : Set Plane} (hJ : IsJordanCurve C) (hP : IsPolygonal C) :
    ∃ (m : ℕ) (P : ClosedPolygon m), P.carrier = C := by
  obtain ⟨m, P, hcar⟩ := exists_prePolygon_of_isJordanCurve hJ hP
  obtain ⟨m', P', hcar'⟩ := PrePolygon.exists_closedPolygon_of_prePolygon m P
  exact ⟨m', P', by rw [hcar', hcar]⟩

/-! ## Corners

A realization cannot put a vertex wherever it likes: `corner` forbids a vertex at which the
curve runs straight through. The points that *must* be vertices are exactly the ones at which
it does not, and this is what a consumer needing a named point to be a vertex has to check. -/

/-- `C` runs **straight** through `p` when, near `p`, it lies inside a segment having `p` in its
interior. -/
def IsStraightAt (C : Set Plane) (p : Plane) : Prop :=
  ∃ a b : Plane, p ∈ openSegment ℝ a b ∧ ∃ r > 0, ball p r ∩ C ⊆ segment ℝ a b

/-- A **corner** of `C`: a point of it at which it does not run straight. -/
def IsCornerAt (C : Set Plane) (p : Plane) : Prop := p ∈ C ∧ ¬ IsStraightAt C p

/-- **Every corner is a vertex.** A point interior to an edge lies on no other edge, so a small
ball meets the curve only in that edge — and then the curve runs straight through it. -/
theorem ClosedPolygon.exists_vertex_eq_of_isCornerAt {m : ℕ} (P : ClosedPolygon m) {p : Plane}
    (hp : IsCornerAt P.carrier p) : ∃ i : ZMod (m + 3), P.vertex i = p := by
  obtain ⟨i, hpi⟩ := Set.mem_iUnion.1 hp.1
  by_cases hend : p = P.vertex i ∨ p = P.vertex (i + 1)
  · rcases hend with rfl | rfl
    exacts [⟨i, rfl⟩, ⟨i + 1, rfl⟩]
  · exfalso
    push Not at hend
    have hopen : p ∈ openSegment ℝ (P.vertex i) (P.vertex (i + 1)) :=
      mem_openSegment_of_ne_left_right (Ne.symm hend.1) (Ne.symm hend.2) hpi
    -- The other edges are finitely many closed sets missing `p`.
    obtain ⟨r, hr, hball⟩ := exists_pos_forall_of_finite
      (S := {j : ZMod (m + 3) | j ≠ i}) (Set.toFinite _)
      (P := fun j ε => ∀ y ∈ ball p ε, y ∉ P.edge j)
      (fun _ _ _ _ hδε hQ y hy => hQ y (ball_subset_ball hδε hy))
      (fun j hj => by
        obtain ⟨ρ, hρ, hsub⟩ := Metric.isOpen_iff.1
          (isCompact_segment (P.vertex j) (P.vertex (j + 1))).isClosed.isOpen_compl p
          (ClosedPolygon.notMem_edge_of_mem_openSegment hj hopen)
        exact ⟨ρ, hρ, fun y hy => hsub hy⟩)
    refine hp.2 ⟨P.vertex i, P.vertex (i + 1), hopen, r, hr, ?_⟩
    rintro z ⟨hzb, hzC⟩
    obtain ⟨j, hzj⟩ := Set.mem_iUnion.1 hzC
    by_cases hji : j = i
    · exact hji ▸ hzj
    · exact absurd hzj (hball j hji z hzb)

/-- Two points of a segment differ by a multiple of its direction. -/
theorem sub_eq_smul_of_mem_segment {a b x y : Plane} (hx : x ∈ segment ℝ a b)
    (hy : y ∈ segment ℝ a b) : ∃ c : ℝ, x - y = c • (a - b) := by
  obtain ⟨α, β, -, -, hαβ, rfl⟩ := hx
  obtain ⟨γ, δ, -, -, hγδ, rfl⟩ := hy
  have hb : β = 1 - α := by linarith
  have hd : δ = 1 - γ := by linarith
  subst hb; subst hd
  exact ⟨α - γ, by module⟩

/-- Three points of one segment are collinear. -/
theorem det_eq_zero_of_mem_segment {a b x y z : Plane} (hx : x ∈ segment ℝ a b)
    (hy : y ∈ segment ℝ a b) (hz : z ∈ segment ℝ a b) : det (x - z) (y - z) = 0 := by
  obtain ⟨c, hc⟩ := sub_eq_smul_of_mem_segment hx hz
  obtain ⟨d, hd⟩ := sub_eq_smul_of_mem_segment hy hz
  rw [hc, hd, det_smul_left, det_smul_right, det_self, mul_zero, mul_zero]

/-- **Every vertex is a corner.** With `ClosedPolygon.exists_vertex_eq_of_isCornerAt` this says
that the vertex set of a realization is *exactly* the corner set of the curve — so any two
realizations of one curve have the same vertices, and a point can be required to be a vertex
precisely when it is a corner. -/
theorem ClosedPolygon.isCornerAt_vertex {m : ℕ} (P : ClosedPolygon m) (i : ZMod (m + 3)) :
    IsCornerAt P.carrier (P.vertex i) := by
  refine ⟨P.vertex_mem_carrier, ?_⟩
  rintro ⟨a, b, hvab, r, hr, hsub⟩
  refine P.corner i ?_
  set u : Plane := P.vertex (i + 1) - P.vertex i with hu
  set w : Plane := P.vertex (i - 1) - P.vertex i with hw
  set t : ℝ := min 1 (r / (2 * (‖u‖ + ‖w‖ + 1))) with ht
  have hM : (0 : ℝ) < ‖u‖ + ‖w‖ + 1 := by positivity
  have htpos : 0 < t := lt_min one_pos (by positivity)
  have htle : t ≤ 1 := min_le_left _ _
  -- A short step along either edge stays inside the ball.
  have key : ∀ v : Plane, ‖v‖ ≤ ‖u‖ + ‖w‖ + 1 → t * ‖v‖ < r := by
    intro v hv
    calc t * ‖v‖ ≤ (r / (2 * (‖u‖ + ‖w‖ + 1))) * ‖v‖ :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg v)
      _ < r := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [norm_nonneg v]
  have hstep : ∀ v : Plane, ‖v‖ ≤ ‖u‖ + ‖w‖ + 1 →
      P.vertex i + t • v ∈ ball (P.vertex i) r := by
    intro v hv
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos htpos]
    exact key v hv
  have hxmem : P.vertex i + t • u ∈ segment ℝ a b := by
    refine hsub ⟨hstep u (by linarith [norm_nonneg w]), ?_⟩
    refine ClosedPolygon.edge_subset_carrier (i := i)
      ⟨1 - t, t, by linarith, htpos.le, by ring, ?_⟩
    rw [hu]; module
  have hymem : P.vertex i + t • w ∈ segment ℝ a b := by
    refine hsub ⟨hstep w (by linarith [norm_nonneg u]), ?_⟩
    refine ClosedPolygon.edge_subset_carrier (i := i - 1)
      ⟨t, 1 - t, htpos.le, by linarith, by ring, ?_⟩
    rw [hw, sub_add_cancel]; module
  have hvmem : P.vertex i ∈ segment ℝ a b := openSegment_subset_segment ℝ _ _ hvab
  have hdet := det_eq_zero_of_mem_segment hymem hxmem hvmem
  rw [add_sub_cancel_left, add_sub_cancel_left, det_smul_left, det_smul_right] at hdet
  have hne : t * (t * det w u) = 0 := hdet
  rcases mul_eq_zero.1 hne with h | h
  · exact absurd h htpos.ne'
  · rcases mul_eq_zero.1 h with h' | h'
    · exact absurd h' htpos.ne'
    · exact h'

/-- **The realization theorem, with named corners.** Any finite list of corners of the curve can
be required to be among the vertices — and by `ClosedPolygon.exists_vertex_eq_of_isCornerAt`,
being a corner is exactly what a point must be for that to be possible. -/
theorem exists_closedPolygon_corners {C : Set Plane} (hJ : IsJordanCurve C) (hP : IsPolygonal C)
    (S : List Plane) (hS : ∀ p ∈ S, IsCornerAt C p) :
    ∃ (m : ℕ) (P : ClosedPolygon m), P.carrier = C ∧
      ∀ p ∈ S, ∃ i : ZMod (m + 3), P.vertex i = p := by
  obtain ⟨m, P, hcar⟩ := exists_closedPolygon hJ hP
  exact ⟨m, P, hcar, fun p hp => P.exists_vertex_eq_of_isCornerAt (by rw [hcar]; exact hS p hp)⟩

/-- **The realization theorem, tracking a splitting.** Two distinct corners of the curve become
two vertices `a` and `a + k` of the realization, which is what names the two arcs
`P.arc a k` and `P.arc (a + k) (m + 3 - k)` that they cut it into.

The corner hypothesis is not an artefact: `ClosedPolygon.corner` forbids a vertex where the
curve runs straight through, so a splitting point that is *not* a corner cannot be a vertex of
any realization. -/
theorem exists_closedPolygon_split {C : Set Plane} (hJ : IsJordanCurve C) (hP : IsPolygonal C)
    {p q : Plane} (hp : IsCornerAt C p) (hq : IsCornerAt C q) (hpq : p ≠ q) :
    ∃ (m : ℕ) (P : ClosedPolygon m) (a : ZMod (m + 3)) (k : ℕ), P.carrier = C ∧
      P.vertex a = p ∧ P.vertex (a + (k : ZMod (m + 3))) = q ∧ 1 ≤ k ∧ k ≤ m + 2 := by
  obtain ⟨m, P, hcar, hvert⟩ := exists_closedPolygon_corners hJ hP [p, q]
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

/-! ## The two arcs of a splitting

`ClosedPolygon.arc a k` and `ClosedPolygon.arc (a + k) (m + 3 - k)` are what a consumer tracking
a decomposition of the curve has to be handed. This section says what they are: two arcs between
the two cut vertices, covering the curve and meeting exactly there. -/

namespace ClosedPolygon

variable {m : ℕ}

/-- The same closed polygon, read from vertex `a` onwards. -/
def rotate (P : ClosedPolygon m) (a : ZMod (m + 3)) : ClosedPolygon m where
  vertex j := P.vertex (a + j)
  vertex_inj i j h := add_left_cancel (P.vertex_inj h)
  edges_meet i j hij := by
    have hi : a + (i + 1) = a + i + 1 := by ring
    have hj : a + (j + 1) = a + j + 1 := by ring
    simp only [hi, hj]
    exact P.edges_meet _ _ fun h => hij (add_left_cancel h)
  corner i := by
    have h1 : a + (i - 1) = a + i - 1 := by ring
    have h2 : a + (i + 1) = a + i + 1 := by ring
    simp only [h1, h2]
    exact P.corner (a + i)

@[simp] theorem rotate_vertex (P : ClosedPolygon m) (a j : ZMod (m + 3)) :
    (P.rotate a).vertex j = P.vertex (a + j) := rfl

theorem rotate_edge (P : ClosedPolygon m) (a j : ZMod (m + 3)) :
    (P.rotate a).edge j = P.edge (a + j) := by
  rw [edge, edge, rotate_vertex, rotate_vertex, show a + (j + 1) = a + j + 1 by ring]

variable {P : ClosedPolygon m} {a : ZMod (m + 3)} {k : ℕ} {z : Plane}

/-- An arc is the union of the `k` edges leaving vertices `a, a + 1, …`. -/
theorem mem_arc_iff : z ∈ P.arc a k ↔ ∃ t < k, z ∈ P.edge (a + (t : ZMod (m + 3))) := by
  constructor
  · intro hz
    obtain ⟨R, hR, hzR⟩ := exists_of_mem_cover hz
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hR
    exact ⟨t, List.mem_range.1 ht, hzR⟩
  · rintro ⟨t, ht, hz⟩
    exact mem_cover (List.mem_map.2 ⟨t, List.mem_range.2 ht, rfl⟩) hz

/-- An arc of `P` is a chain of the polygon read from its first vertex. -/
theorem arc_eq_chain (P : ClosedPolygon m) (a : ZMod (m + 3)) (hk : 1 ≤ k) :
    P.arc a k = (P.rotate a).chain (k - 1) := by
  ext z
  rw [mem_arc_iff, mem_chain_iff]
  constructor
  · rintro ⟨t, ht, hz⟩
    exact ⟨t, by omega, by rw [rotate_edge]; exact hz⟩
  · rintro ⟨j, hj, hz⟩
    rw [rotate_edge] at hz
    exact ⟨j, by omega, hz⟩

/-- **An arc of a splitting is an arc between the two cut vertices.** -/
theorem isArcBetween_arc (P : ClosedPolygon m) (a : ZMod (m + 3)) (hk1 : 1 ≤ k)
    (hk2 : k ≤ m + 2) : IsArcBetween (P.arc a k) (P.vertex a) (P.vertex (a + k)) := by
  have h := (P.rotate a).isArcBetween_chain (k - 1) (by omega)
  rw [← arc_eq_chain P a hk1, show ((k - 1 + 1 : ℕ) : ZMod (m + 3)) = (k : ZMod (m + 3)) by
    congr 1; omega] at h
  simpa using h

/-- Distinct index numerals below the modulus name distinct vertices, after any shift. -/
theorem natCast_shift_inj (P : ClosedPolygon m) (a : ZMod (m + 3)) {x y : ℕ} (hx : x < m + 3)
    (hy : y < m + 3) (he : P.vertex (a + (x : ZMod (m + 3))) = P.vertex (a + (y : ZMod (m + 3)))) :
    x = y :=
  natCast_inj hx hy (add_left_cancel (P.vertex_inj he))

/-- **The two arcs of a splitting meet exactly at the two cut vertices.** A point on both lies
on an edge of each; `edges_meet`, read in both directions, puts it at a vertex shared by the two
edges, and the only shared vertices are the two ends of the split. -/
theorem arc_inter (P : ClosedPolygon m) (a : ZMod (m + 3)) (hk1 : 1 ≤ k) (hk2 : k ≤ m + 2) :
    P.arc a k ∩ P.arc (a + k) (m + 3 - k) = {P.vertex a, P.vertex (a + k)} := by
  refine Set.Subset.antisymm ?_ (Set.subset_inter (P.endpoints_subset_arc a hk1)
    (P.endpoints_subset_arc' a hk2))
  rintro z ⟨hz1, hz2⟩
  obtain ⟨s, hs, hzs⟩ := mem_arc_iff.1 hz1
  obtain ⟨t, ht, hzt⟩ := mem_arc_iff.1 hz2
  have hkt : k + t < m + 3 := by omega
  rw [show a + (k : ZMod (m + 3)) + (t : ZMod (m + 3)) = a + ((k + t : ℕ) : ZMod (m + 3)) by
    push_cast; ring] at hzt
  -- The two edges are different, so each traps `z` among its own two ends.
  have hij : a + (s : ZMod (m + 3)) ≠ a + ((k + t : ℕ) : ZMod (m + 3)) := fun he =>
    absurd (natCast_inj (by omega) hkt (add_left_cancel he)) (by omega)
  have hsucc₁ : a + (s : ZMod (m + 3)) + 1 = a + ((s + 1 : ℕ) : ZMod (m + 3)) := by
    push_cast; ring
  have hsucc₂ : a + ((k + t : ℕ) : ZMod (m + 3)) + 1 = a + ((k + t + 1 : ℕ) : ZMod (m + 3)) := by
    push_cast; ring
  have hA := P.edges_meet _ _ hij (Set.mem_inter hzs hzt)
  have hB := P.edges_meet _ _ (Ne.symm hij) (Set.mem_inter hzt hzs)
  rw [hsucc₁] at hA
  rw [hsucc₂] at hB
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA hB ⊢
  -- The wrap-around: `k + t + 1` is either below the modulus or exactly it.
  have hzero : k + t + 1 = m + 3 → ((k + t + 1 : ℕ) : ZMod (m + 3)) = ((0 : ℕ) : ZMod (m + 3)) := by
    intro he
    rw [he, Nat.cast_zero, ZMod.natCast_self]
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · exact absurd (hA.symm.trans hB) fun he => hij (P.vertex_inj he)
  · -- `s ≡ k + t + 1`: possible only by wrapping round, and then `s = 0`.
    rcases Nat.lt_or_ge (k + t + 1) (m + 3) with hlt | hge
    · exact absurd (P.natCast_shift_inj a (by omega) hlt (hA.symm.trans hB)) (by omega)
    · have he : k + t + 1 = m + 3 := by omega
      have hs0 : s = 0 := P.natCast_shift_inj a (by omega) (by omega)
        ((hA.symm.trans hB).trans (by rw [hzero he]))
      exact Or.inl (by rw [hA, hs0, Nat.cast_zero, add_zero])
  · -- `s + 1 ≡ k + t`: forces `s + 1 = k` and `t = 0`.
    have hst : s + 1 = k + t := P.natCast_shift_inj a (by omega) hkt (hA.symm.trans hB)
    exact Or.inr (by rw [hA, show s + 1 = k by omega])
  · exfalso
    rcases Nat.lt_or_ge (k + t + 1) (m + 3) with hlt | hge
    · exact absurd (P.natCast_shift_inj a (by omega) hlt (hA.symm.trans hB)) (by omega)
    · have he : k + t + 1 = m + 3 := by omega
      have := P.natCast_shift_inj a (show s + 1 < m + 3 by omega) (show 0 < m + 3 by omega)
        ((hA.symm.trans hB).trans (by rw [hzero he]))
      omega

end ClosedPolygon

/-! ## The two-arc decomposition is unique

Two points cut a Jordan curve into two arcs, and *only* into those two: the interior of any arc
of the curve between them is connected and misses both, so it lies on one side of any other such
splitting. Without this a realization could name two arcs and still not be known to name the two
arcs a consumer started from. -/

/-- The interior of an arc — the arc less its two endpoints — is connected and nonempty. The
paired form the uniqueness argument below destructures; both halves are in
`Schoenflies/Subarc.lean`, which is where the shared set identity `A ∖ {p, q} = f '' Ioo 0 1`
lives. -/
theorem IsArcBetween.preconnected_diff {A : Set Plane} {p q : Plane} (h : IsArcBetween A p q) :
    IsPreconnected (A \ {p, q}) ∧ (A \ {p, q}).Nonempty :=
  ⟨h.isPreconnected_diff, h.nonempty_diff⟩

/-- **The two arcs a pair of points cuts a curve into are determined.** -/
theorem two_arcs_unique {C A₁ A₂ D₁ D₂ : Set Plane} {p q : Plane}
    (hA : A₁ ∪ A₂ = C) (hAi : A₁ ∩ A₂ = {p, q})
    (hD : D₁ ∪ D₂ = C) (hDi : D₁ ∩ D₂ = {p, q})
    (hA1 : IsArcBetween A₁ p q) (hA2 : IsArcBetween A₂ p q)
    (hD1 : IsArcBetween D₁ p q) (hD2 : IsArcBetween D₂ p q) :
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
      intro z hz
      by_cases h1 : z ∈ D₁
      · by_cases h2 : z ∈ D₂
        · exact absurd (show z ∈ ({p, q} : Set Plane) by rw [← hDi]; exact ⟨h1, h2⟩) hz.2
        · exact Or.inr h2
      · exact Or.inl h1
    have hnone : ¬ ((A \ {p, q}) ∩ (D₁ᶜ ∩ D₂ᶜ)).Nonempty := by
      rintro ⟨z, hz, h1, h2⟩
      have hzC : z ∈ C := hAC hz.1
      rw [← hD] at hzC
      exact hzC.elim h1 h2
    -- Whichever side the interior meets, it stays there; the two endpoints are on both.
    have hends : ∀ D : Set Plane, p ∈ D → q ∈ D → A \ {p, q} ⊆ D → A ⊆ D := by
      intro D hpD' hqD' hsub' z hz
      by_cases hzpq : z ∈ ({p, q} : Set Plane)
      · rcases hzpq with rfl | rfl
        exacts [hpD', hqD']
      · exact hsub' ⟨hz, hzpq⟩
    by_cases hcase : ((A \ {p, q}) ∩ D₁ᶜ).Nonempty
    · refine Or.inr (hends D₂ hpD.2 hqD.2 fun z hz => ?_)
      by_contra hzD2
      exact hnone (hconn _ _ (hD1.isArc.isClosed).isOpen_compl (hD2.isArc.isClosed).isOpen_compl
        hsub hcase ⟨z, hz, hzD2⟩)
    · refine Or.inl (hends D₁ hpD.1 hqD.1 fun z hz => ?_)
      by_contra hzD1
      exact hcase ⟨z, hz, hzD1⟩
  -- Both arcs cannot land on the same side: the other side would be just the two points.
  have hthird : ∀ D : Set Plane, IsArcBetween D p q → ¬ D ⊆ ({p, q} : Set Plane) := by
    intro D hDar hsub
    obtain ⟨-, z, hz⟩ := hDar.preconnected_diff
    exact hz.2 (hsub hz.1)
  have hnotboth : ∀ D D' : Set Plane, D ∪ D' = C → D ∩ D' = {p, q} → IsArcBetween D' p q →
      A₁ ⊆ D → A₂ ⊆ D → False := by
    intro D D' hDD hDDi hD'ar h1 h2
    refine hthird D' hD'ar ?_
    rw [← hDDi]
    intro z hz
    have hzC : z ∈ C := by rw [← hDD]; exact Or.inr hz
    rw [← hA] at hzC
    exact hzC.elim (fun h => ⟨h1 h, hz⟩) fun h => ⟨h2 h, hz⟩
  -- On opposite sides, the inclusions are equalities.
  have heq : ∀ X Y X' Y' : Set Plane, X ∪ Y = C → X' ∪ Y' = C → X' ∩ Y' = {p, q} →
      p ∈ X → q ∈ X → X ⊆ X' → Y ⊆ Y' → X = X' := by
    intro X Y X' Y' hXY hX'Y' hX'Y'i hpX hqX hXX hYY
    refine Set.Subset.antisymm hXX fun z hz => ?_
    have hzC : z ∈ C := by rw [← hX'Y']; exact Or.inl hz
    rw [← hXY] at hzC
    rcases hzC with h | h
    · exact h
    · have hzpq : z ∈ ({p, q} : Set Plane) := by rw [← hX'Y'i]; exact ⟨hz, hYY h⟩
      rcases hzpq with rfl | rfl
      exacts [hpX, hqX]
  have hAC₁ : A₁ ⊆ C := by rw [← hA]; exact Set.subset_union_left
  have hAC₂ : A₂ ⊆ C := by rw [← hA]; exact Set.subset_union_right
  rcases key A₁ hA1 hAC₁ with h1 | h1 <;> rcases key A₂ hA2 hAC₂ with h2 | h2
  · exact absurd (hnotboth D₁ D₂ hD hDi hD2 h1 h2) (by simp)
  · exact Or.inl ⟨heq A₁ A₂ D₁ D₂ hA hD hDi hpA.1 hqA.1 h1 h2,
      heq A₂ A₁ D₂ D₁ (by rw [Set.union_comm]; exact hA) (by rw [Set.union_comm]; exact hD)
        (by rw [Set.inter_comm]; exact hDi) hpA.2 hqA.2 h2 h1⟩
  · exact Or.inr ⟨heq A₁ A₂ D₂ D₁ hA (by rw [Set.union_comm]; exact hD)
      (by rw [Set.inter_comm]; exact hDi) hpA.1 hqA.1 h1 h2,
      heq A₂ A₁ D₁ D₂ (by rw [Set.union_comm]; exact hA) hD hDi hpA.2 hqA.2 h2 h1⟩
  · exact absurd (hnotboth D₂ D₁ (by rw [Set.union_comm]; exact hD)
      (by rw [Set.inter_comm]; exact hDi) hD1 h1 h2) (by simp)

/-- **The realization theorem, tracking a splitting.** A polygonal Jordan curve decomposed into
two arcs meeting at two of its corners is the carrier of a `ClosedPolygon` whose two arcs at the
corresponding vertices are those two arcs.

This is the form the plane-graph layer wants — compare `Graph.IsHexRealization`. The corner
hypothesis on the two cut points is not an artefact of the proof:
`ClosedPolygon.isCornerAt_vertex` says every vertex of a realization is a corner, so a cut point
that is *not* one cannot be a vertex of any realization at all. -/
theorem exists_closedPolygon_arcs {C A₁ A₂ : Set Plane} (hJ : IsJordanCurve C)
    (hP : IsPolygonal C) {p q : Plane} (hp : IsCornerAt C p) (hq : IsCornerAt C q) (hpq : p ≠ q)
    (hA1 : IsArcBetween A₁ p q) (hA2 : IsArcBetween A₂ p q) (hunion : A₁ ∪ A₂ = C)
    (hinter : A₁ ∩ A₂ = {p, q}) :
    ∃ (m : ℕ) (P : ClosedPolygon m) (a : ZMod (m + 3)) (k : ℕ), P.carrier = C ∧
      1 ≤ k ∧ k ≤ m + 2 ∧ P.vertex a = p ∧ P.vertex (a + (k : ZMod (m + 3))) = q ∧
      ((P.arc a k = A₁ ∧ P.arc (a + (k : ZMod (m + 3))) (m + 3 - k) = A₂) ∨
        (P.arc a k = A₂ ∧ P.arc (a + (k : ZMod (m + 3))) (m + 3 - k) = A₁)) := by
  obtain ⟨m, P, a, k, hcar, hpa, hqa, hk1, hk2⟩ := exists_closedPolygon_split hJ hP hp hq hpq
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

/-- **The realization theorem, with the two arcs in the order they were given.** The same as
`Schoenflies.exists_closedPolygon_arcs` with the disjunction moved off the arcs and onto the two
cut vertices: reading the polygon from the other cut point exchanges the two arcs, so exactly
one of the two starting vertices makes `P.arc a k` the *first* arc. This is the shape
`Graph.IsHexRealization` asks for. -/
theorem exists_closedPolygon_arcs_ordered {C A₁ A₂ : Set Plane} (hJ : IsJordanCurve C)
    (hP : IsPolygonal C) {p q : Plane} (hp : IsCornerAt C p) (hq : IsCornerAt C q) (hpq : p ≠ q)
    (hA1 : IsArcBetween A₁ p q) (hA2 : IsArcBetween A₂ p q) (hunion : A₁ ∪ A₂ = C)
    (hinter : A₁ ∩ A₂ = {p, q}) :
    ∃ (m : ℕ) (P : ClosedPolygon m) (a : ZMod (m + 3)) (k : ℕ), P.carrier = C ∧
      1 ≤ k ∧ k ≤ m + 2 ∧
      P.arc a k = A₁ ∧ P.arc (a + (k : ZMod (m + 3))) (m + 3 - k) = A₂ ∧
      ((P.vertex a = p ∧ P.vertex (a + (k : ZMod (m + 3))) = q) ∨
        (P.vertex a = q ∧ P.vertex (a + (k : ZMod (m + 3))) = p)) := by
  obtain ⟨m, P, a, k, hcar, hk1, hk2, hpa, hqa, hcase⟩ :=
    exists_closedPolygon_arcs hJ hP hp hq hpq hA1 hA2 hunion hinter
  rcases hcase with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact ⟨m, P, a, k, hcar, hk1, hk2, e1, e2, Or.inl ⟨hpa, hqa⟩⟩
  · refine ⟨m, P, a + (k : ZMod (m + 3)), m + 3 - k, hcar, by omega, by omega, e2, ?_, ?_⟩
    · rw [zmod_add_sub_cancel (by omega) a, show m + 3 - (m + 3 - k) = k by omega]
      exact e1
    · rw [zmod_add_sub_cancel (by omega) a]
      exact Or.inr ⟨hqa, hpa⟩

end Schoenflies

end BundlePart415

section BundlePart416
/- Source: dev/planar_search/schoenflies_port/Schoenflies/FaceCyclesProof.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/



/-!
# Face cycles: the proof

`lem:face-cycles` — *every face of a finite 2-connected polygonal plane graph has a cycle as its
boundary and is one of the two complementary regions of that cycle*. `Schoenflies/FaceCycles.lean`
built the base cycle, its 2-connectivity, and the topology of adding an ear; this module runs
the induction of the blueprint's proof on top of them.

## READ THIS FIRST: what is assumed

`Graph.face_cycles` **carries a hypothesis, `Schoenflies.CrosscutSplitsRegion`, which nothing
proves.** It is the exhaustion clause of `thm:polygonal-crosscut` — "the crosscut replaces `F`
by exactly two regions" — stated for a crosscut whose two endpoints are *arbitrary points of
the curve*. Everything else in the blueprint's proof is discharged here without hypotheses, and
each of those pieces is a standalone theorem below.

`main`'s Theorem 2.8 does **not** discharge it, and the obstruction is not a missing bridge.
`Schoenflies.IsPolygonalCrosscut` states its two splitting hypotheses against
`ClosedPolygon.arcPieces C a k`, which cuts the polygon's edge list at two of *its vertices*;
and `Schoenflies.ClosedPolygon.isCornerAt_vertex` says every vertex of every realization of a
curve is a corner of it. In the induction below the two cut points are the ear's endpoints —
graph vertices at which the two cycle edges may leave along opposite rays, so that the boundary
curve runs *straight* through the cut point. Such a point is a vertex of no `ClosedPolygon`
with that carrier, and `Schoenflies.exists_closedPolygon_split` (whose `IsCornerAt` hypotheses
are therefore not an artefact) cannot be applied.

There is a **second, independent** reason, and it bites even when both cut points *are*
corners. `IsPolygonalCrosscut.edges₁` asks for `SameEdges J₁.pieces (C.arcPieces a k ++ K)`,
a multiset equality of unoriented segments. The list on the right has two pieces ending at the
cut point `q` — the arc's last and the crosscut's first. If those two are collinear, the curve
`J₁ = A₁ ∪ P` runs straight through `q`, so `q` is a vertex of no `ClosedPolygon` with that
carrier and *no* piece of `J₁.pieces` ends there: the multiset equality is unsatisfiable. Since
the crosscut may perfectly well leave a cut vertex along the ray opposite the arriving arc edge,
`edges₁` and `edges₂` are not dischargeable as stated. Deleting the redundant vertex —
`Schoenflies.PrePolygon.deleteLast` — repairs the *realization* and breaks `SameEdges` in the
same move.

Closing the gap therefore means restating Theorem 2.8 with the edge lists related by *parity*
rather than by `SameEdges`, for a split made at arbitrary points of the curve. The tools exist:
`Schoenflies.parity_split` is already stated for arbitrary lists, and
`Schoenflies.parity_subdivide` (Lemma 2.1) absorbs the difference between a merged piece and its
two halves. What is missing is the parity theory of presentations carrying redundant vertices —
`Schoenflies.parity_eq_one_iff` for `Schoenflies.PrePolygon` rather than only for
`ClosedPolygon`, obtained by carrying the parity along the normalization induction of
`Schoenflies.PrePolygon.exists_closedPolygon_of_prePolygon`. That is a separate module.

## Main results

* **The realisation of a cycle is a separating curve** (`Graph.IsDrawing.cycle_isSeparating`),
  which is what the base case needed and what `main` could not say. It composes
  `Graph.IsDrawing.cycle_isJordanCurve` with `Schoenflies.exists_closedPolygon` and
  `Schoenflies.ClosedPolygon.isSeparating_carrier`. The polygonality half needed a bridge that
  `main` did not have: `Schoenflies.IsPolygonal` is the carrier of *one* vertex list, so a union
  of edge arcs is polygonal only once each arc is known to be a polyline running from one of its
  ends to the other (`Schoenflies.IsArcBetween.exists_poly_eq`, which rests on the arc
  uniqueness `Schoenflies.IsArcBetween.eq_of_subset`).
* **The base case** (`Graph.IsDrawing.hasFaceCycles_cycleGraph`): the cycle subgraph occupies
  exactly the cycle's realisation, so its faces are the two regions of that curve.
* **Cutting a cycle at two of its vertices** (`Graph.IsCycleThrough.split_at`) and **splicing an
  ear onto an arc** (`Graph.exists_spliced_cycle`) — the combinatorics of "both bounded by
  cycles" — together with the geometric reading of the split
  (`Graph.IsDrawing.arcs_of_split`).
* **The step's topology**: the enlarged exterior is the old one minus the ear
  (`Graph.IsDrawing.pointSet_pathGraphOf`), a face the ear misses survives with its cycle
  (`Graph.IsFaceCycle.mono`), and the face the ear cuts is cut only inside itself
  (`Schoenflies.connectedComponentIn_diff`).

## For the integrator

`Graph.IsPath.append`, `Graph.IsPath.split_meet`, `Graph.IsWalk.walkVertices_eq_covered`,
`Graph.IsWalk.walkVertices_reverse_eq`, `Graph.coveredVertices_congr_of_le`,
`Graph.walkVertices_congr_of_le` and `Graph.edgesCover_append` / `…_perm` / `…_reverse` are
general and belong in `Schoenflies/Graph/Walk.lean` and `Schoenflies/Graph/CycleJordan.lean`.
`Schoenflies.IsArcBetween.eq_of_subset` belongs in `Schoenflies/Subarc.lean` and
`Schoenflies.poly_append_join` in `Schoenflies/PolyPath.lean`.

## Blueprint

* `Schoenflies.IsArcBetween.eq_of_subset`, `Schoenflies.IsArcBetween.exists_poly_eq`,
  `Graph.IsDrawing.exists_poly_eq_edgesCover`, `Graph.IsDrawing.isPolygonal_edgesCover` — §1,
  the polygonality of what a walk draws.
* `Graph.IsDrawing.cycle_isSeparating` — `thm:polygonal-jordan` for the realisation of a cycle:
  "This is true for the initial cycle by Theorem `thm:polygonal-jordan`."
* `Graph.IsFaceCycle`, `Graph.HasFaceCycles` — the conclusion of `lem:face-cycles`, at one face
  and at all of them.
* `Graph.IsDrawing.hasFaceCycles_cycleGraph` — the base case.
* `Graph.IsCycleThrough.split_at`, `Graph.IsDrawing.arcs_of_split`,
  `Graph.exists_spliced_cycle` — "Theorem `thm:polygonal-crosscut` replaces `F` by exactly two
  regions, both bounded by cycles", combinatorially.
* `Schoenflies.CrosscutSplitsRegion` — **the assumed** exhaustion clause of
  `thm:polygonal-crosscut` at arbitrary cut points.
* `Graph.IsDrawing.hasFaceCycles_union` — one ear.
* `Graph.face_cycles` — `lem:face-cycles`, modulo `Schoenflies.CrosscutSplitsRegion`.
-/

open Metric Set unitInterval
open scoped Graph

namespace Schoenflies

/-! ## An arc inside an arc with the same ends is the whole of it -/

/-- **An arc between two points contained in an arc between the same two points is all of
it.** Removing an interior point of the ambient arc splits it into two relatively open halves;
a connected subset containing both ends would have to meet both and therefore their empty
intersection. -/
theorem IsArcBetween.eq_of_subset {A B : Set Plane} {p q : Plane}
    (hA : IsArcBetween A p q) (hB : IsArcBetween B p q) (hBA : B ⊆ A) : B = A := by
  obtain ⟨f, hc, hi, hAim, hf0, hf1⟩ := hA
  refine Set.Subset.antisymm hBA fun x hx => ?_
  by_contra hxB
  obtain ⟨t, ht, rfl⟩ : ∃ t ∈ I, f t = x := by rw [← hAim] at hx; exact hx
  -- The parameter is strictly inside, since both ends belong to `B`.
  have ht0 : (0 : ℝ) < t := by
    rcases eq_or_lt_of_le ht.1 with rfl | h
    · exact absurd (hf0 ▸ hB.left_mem) hxB
    · exact h
  have ht1 : t < 1 := by
    rcases eq_or_lt_of_le ht.2 with rfl | h
    · exact absurd (hf1 ▸ hB.right_mem) hxB
    · exact h
  obtain ⟨V₁, hV₁open, hV₁⟩ := image_isRelOpen hc hi (U := Iio t) isOpen_Iio
  obtain ⟨V₂, hV₂open, hV₂⟩ := image_isRelOpen hc hi (U := Ioi t) isOpen_Ioi
  rw [hAim] at hV₁ hV₂
  -- The two halves are disjoint, by injectivity of the parametrisation.
  have hdisj : (A ∩ (V₁ ∩ V₂)) = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun z ⟨hzA, hz₁, hz₂⟩ => ?_
    obtain ⟨s, hs, rfl⟩ : z ∈ f '' (Iio t ∩ I) := by rw [hV₁]; exact ⟨hz₁, hzA⟩
    obtain ⟨r, hr, hrs⟩ : f s ∈ f '' (Ioi t ∩ I) := by rw [hV₂]; exact ⟨hz₂, hzA⟩
    have hrs' : r = s := hi hr.2 hs.2 hrs
    have h1 : t < r := hr.1
    have h2 : s < t := hs.1
    rw [hrs'] at h1
    linarith
  -- `B` misses the removed point, so it lies in the union of the two halves.
  have hsub : B ⊆ V₁ ∪ V₂ := by
    intro z hz
    obtain ⟨s, hs, rfl⟩ : ∃ s ∈ I, f s = z := by
      have := hBA hz; rw [← hAim] at this; exact this
    have hst : s ≠ t := by rintro rfl; exact hxB hz
    rcases lt_or_gt_of_ne hst with h | h
    · exact Or.inl (by
        have : f s ∈ V₁ ∩ A := by rw [← hV₁]; exact ⟨s, ⟨h, hs⟩, rfl⟩
        exact this.1)
    · exact Or.inr (by
        have : f s ∈ V₂ ∩ A := by rw [← hV₂]; exact ⟨s, ⟨h, hs⟩, rfl⟩
        exact this.1)
  have hp₁ : (B ∩ V₁).Nonempty := by
    refine ⟨p, hB.left_mem, ?_⟩
    have : f 0 ∈ V₁ ∩ A := by rw [← hV₁]; exact ⟨0, ⟨ht0, zero_mem_I⟩, rfl⟩
    exact hf0 ▸ this.1
  have hq₂ : (B ∩ V₂).Nonempty := by
    refine ⟨q, hB.right_mem, ?_⟩
    have : f 1 ∈ V₂ ∩ A := by rw [← hV₂]; exact ⟨1, ⟨ht1, one_mem_I⟩, rfl⟩
    exact hf1 ▸ this.1
  obtain ⟨z, hzB, hz⟩ :=
    hB.isArc.isConnected.isPreconnected V₁ V₂ hV₁open hV₂open hsub hp₁ hq₂
  rw [Set.eq_empty_iff_forall_notMem] at hdisj
  exact hdisj z ⟨hBA hzB, hz⟩

/-! ## Concatenating polylines -/

/-- **Appending two vertex lists joins their carriers by one segment.** The segment runs from
the last vertex of the first list to the first vertex of the second, and is degenerate — hence
contributes nothing — exactly when the two lists already share that vertex. -/
theorem poly_append_join : ∀ {as : List Plane} (h₁ : as ≠ []) {bs : List Plane} (h₂ : bs ≠ []),
    poly (as ++ bs) = poly as ∪ segment ℝ (as.getLast h₁) (bs.head h₂) ∪ poly bs
  | [], h₁, _, _ => absurd rfl h₁
  | [x], _, bs, h₂ => by
    rw [List.singleton_append, poly_cons_of_ne_nil h₂, poly_singleton,
      List.getLast_singleton]
    rw [Set.union_assoc, Set.singleton_union]
    exact (Set.insert_eq_self.2
      (Set.mem_union_left _ (left_mem_segment ℝ x (bs.head h₂)))).symm
  | x :: y :: as, _, bs, h₂ => by
    have hne : (y :: as) ≠ [] := List.cons_ne_nil _ _
    rw [List.cons_append, poly_cons_of_ne_nil (by simp), poly_cons_cons,
      poly_append_join hne h₂, List.head_append_of_ne_nil hne,
      List.getLast_cons hne]
    ac_rfl

/-- **Two polylines meeting end to head concatenate.** The joining segment collapses to the
shared vertex. -/
theorem poly_append_of_eq {as bs : List Plane} (h₁ : as ≠ []) (h₂ : bs ≠ [])
    (h : as.getLast h₁ = bs.head h₂) : poly (as ++ bs) = poly as ∪ poly bs := by
  rw [poly_append_join h₁ h₂, h, segment_same, Set.union_assoc, Set.singleton_union,
    Set.insert_eq_self.2 (head_mem_poly h₂)]

/-! ## A component survives the removal of a set

The face of the enlarged graph through a point of an old face is a component of *that old
face* with the ear removed — not merely of the whole old exterior with the ear removed. No
topology is needed: a component of the small set is preconnected inside the big one, and back
again. -/

/-- **Cutting inside one component.** The component of `z` in `S ∖ P` sees only the component
of `z` in `S`. -/
theorem connectedComponentIn_diff (S P : Set Plane) (z : Plane) :
    connectedComponentIn (S \ P) z = connectedComponentIn (connectedComponentIn S z \ P) z := by
  by_cases hz : z ∈ S \ P
  · have hcomp : connectedComponentIn (S \ P) z ⊆ connectedComponentIn S z :=
      isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn hz) ((connectedComponentIn_subset _ _).trans Set.sdiff_subset)
    have hzR : z ∈ connectedComponentIn (connectedComponentIn S z \ P) z :=
      mem_connectedComponentIn ⟨mem_connectedComponentIn hz.1, hz.2⟩
    refine Set.Subset.antisymm
      (isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn hz) fun w hw =>
          ⟨hcomp hw, (connectedComponentIn_subset _ _ hw).2⟩)
      (isPreconnected_connectedComponentIn.subset_connectedComponentIn hzR fun w hw => ?_)
    have hw' : w ∈ connectedComponentIn S z \ P := connectedComponentIn_subset _ _ hw
    exact ⟨connectedComponentIn_subset _ _ hw'.1, hw'.2⟩
  · rw [connectedComponentIn_eq_empty hz, connectedComponentIn_eq_empty]
    rintro ⟨hw, hwP⟩
    exact hz ⟨connectedComponentIn_subset _ _ hw, hwP⟩

/-! ## A polygonal arc is a polyline running from one end to the other -/

/-- **A polygonal arc is `poly` of a vertex list running from one of its ends to the other.**
`Schoenflies.exists_simple_poly_of_isPolygonal` produces a simple polygonal arc *inside* the
set between the two points; being an arc between the same two ends it is the whole of it, by
`Schoenflies.IsArcBetween.eq_of_subset`. -/
theorem IsArcBetween.exists_poly_eq {A : Set Plane} {p q : Plane} (harc : IsArcBetween A p q)
    (hpoly : IsPolygonal A) (hpq : p ≠ q) :
    ∃ vs : List Plane, ∃ h : vs ≠ [], vs.head h = p ∧ vs.getLast h = q ∧ poly vs = A := by
  obtain ⟨vs, hvs, hhead, hlast, hsub, hsubarc⟩ :=
    exists_simple_poly_of_isPolygonal hpoly harc.isArc.isConnected.isPreconnected hpq
      harc.left_mem harc.right_mem
  exact ⟨vs, hvs, hhead, hlast, harc.eq_of_subset hsubarc hsub⟩

end Schoenflies

namespace Graph

/-! ## Cutting and joining paths

Two general facts about paths that `Schoenflies/Graph/Walk.lean` does not have, and that the
splitting of a cycle at two of its vertices runs on. **The integrator should hoist both into
`Schoenflies/Graph/Walk.lean`**, next to `Graph.IsPath.split`, which is the weaker form of the
second. -/

section GeneralWalk

variable {α β : Type*} {G : Graph α β} {u v w x y : α} {e : β} {W W₁ W₂ : List β}

/-- **Two paths meeting only at the junction concatenate.** The freshness clause of the joined
path is the freshness of the first together with the meeting condition: a vertex the second
half visits and the first half departs from would be the junction, which the first half has
already arrived at. -/
theorem IsPath.append : ∀ {u w v : α} {W₁ W₂ : List β}, G.IsPath u W₁ w → G.IsPath w W₂ v →
    (∀ y ∈ G.walkVertices u W₁, y ∈ G.walkVertices w W₂ → y = w) → G.IsPath u (W₁ ++ W₂) v := by
  intro u w v W₁ W₂ h₁
  induction h₁ with
  | nil hx => intro h₂ _; simpa using h₂
  | @cons u w₀ w e W hl hW hfresh ih =>
    intro h₂ hmeet
    refine List.cons_append .. ▸ IsPath.cons hl
      (ih h₂ fun y hy hy₂ => hmeet y (mem_walkVertices_cons_of_mem hl hy) hy₂) fun hmem => ?_
    -- The departure vertex is fresh: the only new vertices are those of the second half, and
    -- one of those shared with the first half would be the junction, already visited.
    rcases mem_walkVertices_iff.1 hmem with rfl | hcov
    · exact hfresh mem_walkVertices_self
    rw [coveredVertices_append] at hcov
    rcases hcov with hcov | hcov
    · exact hfresh (mem_walkVertices_of_mem_covered hcov)
    · have := hmeet u mem_walkVertices_self (mem_walkVertices_of_mem_covered hcov)
      exact hfresh (this ▸ hW.target_mem_walkVertices)

/-- **A path splits at any vertex it visits, and the two halves meet only there.** This is
`Graph.IsPath.split` with the meeting condition in place of its weaker last clause. -/
theorem IsPath.split_meet (h : G.IsPath u W v) (hx : x ∈ G.walkVertices u W) :
    ∃ W₁ W₂, W = W₁ ++ W₂ ∧ G.IsPath u W₁ x ∧ G.IsPath x W₂ v ∧
      ∀ y ∈ G.walkVertices u W₁, y ∈ G.walkVertices x W₂ → y = x := by
  induction h with
  | nil hx' =>
    rw [walkVertices_nil] at hx
    obtain rfl := hx
    exact ⟨[], [], rfl, .nil hx', .nil hx', fun y hy _ => by simpa using hy⟩
  | @cons u w v e W hl hW hfresh ih =>
    rcases mem_walkVertices_cons hl hx with rfl | hx'
    · exact ⟨[], e :: W, rfl, .nil hl.left_mem, .cons hl hW hfresh,
        fun y hy _ => by simpa using hy⟩
    obtain ⟨W₁, W₂, rfl, h₁, h₂, hmeet⟩ := ih hx'
    have hsub₁ : W₁ ⊆ W₁ ++ W₂ := List.subset_append_left _ _
    have hsub₂ : W₂ ⊆ W₁ ++ W₂ := List.subset_append_right _ _
    refine ⟨e :: W₁, W₂, rfl, .cons hl h₁ fun hmem => hfresh (walkVertices_mono hsub₁ hmem),
      h₂, fun y hy hy₂ => ?_⟩
    -- A vertex of the extended prefix is either the new source — which the far half never
    -- visits, by freshness — or one the induction hypothesis already handles.
    rcases mem_walkVertices_cons hl hy with rfl | hy'
    · exfalso
      rcases mem_walkVertices_iff.1 hy₂ with rfl | hcov
      · exact hfresh (walkVertices_mono hsub₁ h₁.target_mem_walkVertices)
      · exact hfresh (mem_walkVertices_of_mem_covered (coveredVertices_mono hsub₂ hcov))
    · exact hmeet y hy' hy₂

/-- The source of a nonempty walk is an end of its first edge, so a nonempty walk visits no
vertex its edges do not cover. -/
theorem IsWalk.walkVertices_eq_covered (h : G.IsWalk u W v) (hne : W ≠ []) :
    G.walkVertices u W = G.coveredVertices W := by
  refine Set.insert_eq_self.2 ?_
  cases h with
  | nil => exact absurd rfl hne
  | cons hl _ => exact mem_coveredVertices List.mem_cons_self hl.inc_left

/-- Running a nonempty walk backwards changes neither the edges nor the vertices it visits. -/
theorem IsWalk.walkVertices_reverse_eq (h : G.IsWalk u W v) (hne : W ≠ []) :
    G.walkVertices v W.reverse = G.walkVertices u W := by
  rw [h.reverse.walkVertices_eq_covered (by simpa using hne), coveredVertices_reverse,
    h.walkVertices_eq_covered hne]

/-! ### Cutting a cycle at two of its vertices

The cycle is `X ++ Y ++ Z` closed up by the edge `e`, cut at the two vertices `c` (between `X`
and `Y`) and `d` (between `Y` and `Z`). One arc is `Y`; the other runs `Z`, then the closing
edge, then `X`. Both cases of "which of the two named vertices comes first along the detour"
feed this one lemma. -/

/-- **The complementary arc of a cut cycle**, together with the two facts a geometric consumer
needs: that the two arcs between them use every edge of the cycle exactly once, and that they
visit no common vertex but the two cut points. -/
theorem IsCycleThrough.split_aux {G : Graph α β} {e : β} {u v c d : α} {D X Y Z : List β}
    (hc : G.IsCycleThrough e u v D) (hD : D = X ++ (Y ++ Z)) (hX : G.IsPath u X c)
    (hY : G.IsPath c Y d) (hZ : G.IsPath d Z v) (hcd : c ≠ d)
    (hM1 : ∀ y ∈ G.walkVertices u X, y ∈ G.walkVertices c (Y ++ Z) → y = c)
    (hM2 : ∀ y ∈ G.walkVertices c Y, y ∈ G.walkVertices d Z → y = d) :
    G.IsPath d (Z ++ e :: X) c ∧ (Y ++ (Z ++ e :: X)).Perm (e :: D) ∧
      ∀ y ∈ G.walkVertices c Y, y ∈ G.walkVertices d (Z ++ e :: X) → y = c ∨ y = d := by
  have hZsub : G.walkVertices d Z ⊆ G.walkVertices c (Y ++ Z) := by
    intro y hy
    rcases mem_walkVertices_iff.1 hy with rfl | hcov
    · exact walkVertices_mono (List.subset_append_left _ _) hY.target_mem_walkVertices
    · exact mem_walkVertices_of_mem_covered (coveredVertices_mono
        (List.subset_append_right _ _) hcov)
  -- A vertex of the first stretch that the last stretch also reaches would merge the two cuts.
  have hclash : ∀ y ∈ G.walkVertices u X, y ∈ G.walkVertices d Z → False := by
    intro y hy hyZ
    obtain rfl : y = c := hM1 y hy (hZsub hyZ)
    exact hcd (hM2 y mem_walkVertices_self hyZ)
  have hvZ : v ∈ G.walkVertices d Z := hZ.target_mem_walkVertices
  have hvX : v ∉ G.walkVertices u X := fun hh => hclash v hh hvZ
  -- The closing edge, then the first stretch, is a path from the far end back to the first cut.
  have hePath : G.IsPath v (e :: X) c := IsPath.cons hc.isLink.symm hX hvX
  -- Its vertices, other than `v` itself, are those of the first stretch.
  have hcons : ∀ y ∈ G.walkVertices v (e :: X), y = v ∨ y ∈ G.walkVertices u X := by
    intro y hy
    rcases mem_walkVertices_iff.1 hy with rfl | ⟨g, hg, hinc⟩
    · exact Or.inl rfl
    rcases List.mem_cons.1 hg with rfl | hg'
    · rcases hinc.eq_or_eq_of_isLink hc.isLink with rfl | rfl
      · exact Or.inr mem_walkVertices_self
      · exact Or.inl rfl
    · exact Or.inr (mem_walkVertices_of_mem_covered ⟨g, hg', hinc⟩)
  refine ⟨hZ.append hePath fun y hy hy' => ?_, ?_, fun y hy hy' => ?_⟩
  · rcases hcons y hy' with rfl | hyX
    · rfl
    · exact absurd hyX fun hh => hclash y hh hy
  · subst hD
    rw [show Y ++ (Z ++ e :: X) = (Y ++ Z) ++ (e :: X) by rw [List.append_assoc]]
    exact List.perm_middle.trans (List.Perm.cons _ List.perm_append_comm)
  · -- A vertex on both arcs is on the last stretch — hence the second cut — or on the first,
    -- hence the first cut.
    rcases mem_walkVertices_iff.1 hy' with rfl | hcov
    · exact Or.inr rfl
    rw [coveredVertices_append] at hcov
    rcases hcov with hcovZ | hcovE
    · exact Or.inr (hM2 y hy (mem_walkVertices_of_mem_covered hcovZ))
    · rcases hcons y (mem_walkVertices_of_mem_covered hcovE) with rfl | hyX
      · exact Or.inr (hM2 y hy hvZ)
      · exact Or.inl (hM1 y hyX (walkVertices_mono (List.subset_append_left _ _) hy))

/-- **A cycle cut at two of its vertices is two paths between them.** The two arcs use every
edge of the cycle exactly once — that is what the permutation says — and they have no vertex in
common but the two cut points. This is the combinatorial half of "the ear is a crosscut of the
face": the geometric half reads the two arcs of the Jordan curve off it. -/
theorem IsCycleThrough.split_at {G : Graph α β} {e : β} {u v a b : α} {D : List β}
    (hc : G.IsCycleThrough e u v D) (ha : a ∈ G.walkVertices u D) (hb : b ∈ G.walkVertices u D)
    (hab : a ≠ b) :
    ∃ D₁ D₂ : List β, G.IsPath a D₁ b ∧ G.IsPath b D₂ a ∧ (D₁ ++ D₂).Perm (e :: D) ∧
      ∀ y ∈ G.walkVertices a D₁, y ∈ G.walkVertices b D₂ → y = a ∨ y = b := by
  obtain ⟨P, Q, hPQ, hP, hQ, hM1⟩ := hc.isPath.split_meet ha
  -- The second cut point lies on one of the two stretches the first one made.
  have hcases : b ∈ G.walkVertices a Q ∨ b ∈ G.walkVertices u P := by
    rw [hPQ] at hb
    rcases mem_walkVertices_iff.1 hb with rfl | hcov
    · exact Or.inr mem_walkVertices_self
    rw [coveredVertices_append] at hcov
    rcases hcov with h | h
    · exact Or.inr (mem_walkVertices_of_mem_covered h)
    · exact Or.inl (mem_walkVertices_of_mem_covered h)
  rcases hcases with hbQ | hbP
  · -- `b` comes after `a`: cut the far stretch at `b`.
    obtain ⟨Q₁, Q₂, hQ12, hQ1, hQ2, hM2⟩ := hQ.split_meet hbQ
    obtain ⟨hpath, hperm, hmeet⟩ := hc.split_aux (X := P) (Y := Q₁) (Z := Q₂)
      (by rw [hPQ, hQ12]) hP hQ1 hQ2 hab (by rw [← hQ12]; exact hM1) hM2
    exact ⟨Q₁, Q₂ ++ e :: P, hQ1, hpath, hperm, hmeet⟩
  · -- `b` comes before `a`: cut the near stretch at `b`, and the two roles are exchanged.
    obtain ⟨P₁, P₂, hP12, hP1, hP2, hM2⟩ := hP.split_meet hbP
    have hP1sub : G.walkVertices u P₁ ⊆ G.walkVertices u P :=
      walkVertices_mono (by rw [hP12]; exact List.subset_append_left _ _)
    have hP2sub : G.walkVertices b P₂ ⊆ G.walkVertices u P := by
      intro y hy
      rcases mem_walkVertices_iff.1 hy with rfl | hcov
      · exact hbP
      · exact mem_walkVertices_of_mem_covered
          (coveredVertices_mono (by rw [hP12]; exact List.subset_append_right _ _) hcov)
    have hM1' : ∀ y ∈ G.walkVertices u P₁, y ∈ G.walkVertices b (P₂ ++ Q) → y = b := by
      intro y hy hy'
      rcases mem_walkVertices_iff.1 hy' with rfl | hcov
      · rfl
      rw [coveredVertices_append] at hcov
      rcases hcov with h | h
      · exact hM2 y hy (mem_walkVertices_of_mem_covered h)
      · -- A vertex both stretches of the near half and the far half reach merges the two cuts.
        exfalso
        obtain rfl : y = a := hM1 y (hP1sub hy) (mem_walkVertices_of_mem_covered h)
        exact hab (hM2 y hy hP2.target_mem_walkVertices)
    obtain ⟨hpath, hperm, hmeet⟩ := hc.split_aux (X := P₁) (Y := P₂) (Z := Q)
      (by rw [hPQ, hP12, List.append_assoc]) hP1 hP2 hQ (Ne.symm hab) hM1'
      fun y hy hy' => hM1 y (hP2sub hy) hy'
    refine ⟨Q ++ e :: P₁, P₂, hpath, hP2, List.perm_append_comm.trans hperm, fun y hy hy' => ?_⟩
    exact (hmeet y hy' hy).symm

/-! ### Splicing an ear onto an arc

The blueprint's "the crosscut replaces `F` by exactly two regions, both bounded by cycles": the
two new cycles are the two arcs of the old one, each closed up by the ear. This is the
combinatorial construction of one of them. -/

/-- Incidence along edges of a subgraph is the same in the subgraph as in the graph, so the
vertices a walk visits do not depend on which of the two it is read in. -/
theorem coveredVertices_congr_of_le {H G : Graph α β} (hHG : H ≤ G) (hW : ∀ f ∈ W, f ∈ E(H)) :
    G.coveredVertices W = H.coveredVertices W := by
  ext x
  constructor
  · rintro ⟨g, hg, y, hy⟩
    exact ⟨g, hg, y, (hHG.isLink_iff (hW g hg)).2 hy⟩
  · rintro ⟨g, hg, y, hy⟩
    exact ⟨g, hg, y, hy.mono hHG⟩

theorem walkVertices_congr_of_le {H G : Graph α β} (hHG : H ≤ G) (hW : ∀ f ∈ W, f ∈ E(H)) :
    G.walkVertices u W = H.walkVertices u W := by
  rw [walkVertices, walkVertices, coveredVertices_congr_of_le hHG hW]

/-- **The cycle an ear splices onto an arc of the old cycle.** The closed walk runs along the
arc and back along the ear; presented as `Graph.IsCycleThrough`, its named edge is the ear's
first, and its detour is the arc followed by the rest of the ear reversed. -/
theorem exists_spliced_cycle {B G : Graph α β} (hBG : B ≤ G) {a b : α} {D₁ D' : List β}
    (hD1 : B.IsPath a D₁ b) (hear : G.IsPath a D' b) (hab : a ≠ b)
    (hnew : ∀ g ∈ D', g ∉ E(B))
    (hint : ∀ y ∈ G.walkVertices a D', y ≠ a → y ≠ b → y ∉ V(B)) :
    ∃ (f : β) (x y : α) (T : List β),
      (B.union (G.pathGraphOf a D')).IsCycleThrough f x y T ∧ (f :: T).Perm (D₁ ++ D') := by
  obtain ⟨f, T, rfl⟩ : ∃ f T, D' = f :: T := by
    cases D' with
    | nil => exact absurd hear.isWalk.eq_of_nil hab
    | cons f T => exact ⟨f, T, rfl⟩
  obtain ⟨w, hl, hT, hfresh⟩ :
      ∃ w, G.IsLink f a w ∧ G.IsPath w T b ∧ a ∉ G.walkVertices w T := by
    cases hear with
    | cons hl hT hfr => exact ⟨_, hl, hT, hfr⟩
  set P := G.pathGraphOf a (f :: T) with hP
  have hPG : P ≤ G := pathGraphOf_le hear.isWalk
  have hcompat : B.Compatible P := Compatible.of_le_le hBG hPG
  have hPB : P ≤ B.union P := hcompat.right_le_union
  have hBB : B ≤ B.union P := left_le_union _ _
  have hedges : ∀ g ∈ T, g ∈ E(P) := fun g hg => by
    rw [pathGraphOf_edgeSet hear.isWalk]; exact List.mem_cons_of_mem _ hg
  -- The ear's tail, run backwards, is a path of the enlarged graph from the far end.
  have hTrev : (B.union P).IsPath b T.reverse w := by
    refine ((hT.reverse.anti hPG ?_ ?_).mono hPB)
    · rw [pathGraphOf_vertexSet]; exact hear.isWalk.target_mem_walkVertices
    · intro g hg; exact hedges g (List.mem_reverse.1 hg)
  have hD1' : (B.union P).IsPath a D₁ b := hD1.mono hBB
  have hTedges : ∀ g ∈ T.reverse, g ∈ E(P) := fun g hg => hedges g (List.mem_reverse.1 hg)
  have hcovP : ∀ W' : List β, (∀ g ∈ W', g ∈ E(P)) →
      (B.union P).coveredVertices W' = G.coveredVertices W' := by
    intro W' hW'
    rw [coveredVertices_congr_of_le hPB hW', ← coveredVertices_congr_of_le hPG hW']
  -- The arc and the ear's tail meet only at the ear's far end: a common vertex lies in the old
  -- subgraph, so the ear's freshness clause makes it one of the ear's two ends, and the source
  -- is not one the rest of the ear visits.
  have hmeet : ∀ y ∈ (B.union P).walkVertices a D₁, y ∈ (B.union P).walkVertices b T.reverse →
      y = b := by
    intro y hy hy'
    have hyB : y ∈ V(B) := by
      rw [walkVertices_congr_of_le hBB (fun g hg => hD1.edge_mem hg)] at hy
      exact hD1.isWalk.walkVertices_subset hy
    have hy'' : y = b ∨ y ∈ G.coveredVertices T := by
      rcases mem_walkVertices_iff.1 hy' with rfl | hcov
      · exact Or.inl rfl
      · rw [hcovP _ hTedges, coveredVertices_reverse] at hcov
        exact Or.inr hcov
    rcases hy'' with rfl | hcov
    · rfl
    have hyD : y ∈ G.walkVertices a (f :: T) :=
      mem_walkVertices_of_mem_covered (coveredVertices_mono (List.subset_cons_self _ _) hcov)
    by_contra hyb
    obtain rfl : y = a := by
      by_contra hya
      exact hint y hyD hya hyb hyB
    exact hfresh (mem_walkVertices_of_mem_covered hcov)
  refine ⟨f, a, w, D₁ ++ T.reverse, ⟨?_, hD1'.append hTrev hmeet, ?_⟩, ?_⟩
  · exact (pathGraphOf_isLink.2 ⟨List.mem_cons_self, hl, mem_walkVertices_self,
      mem_walkVertices_of_mem_covered ⟨f, List.mem_cons_self, hl.inc_right⟩⟩).mono hPB
  · -- The ear's first edge is on neither the arc — it is not an edge of the old subgraph at
    -- all — nor the rest of the ear, which is a path.
    intro hmem
    rcases List.mem_append.1 hmem with h | h
    · exact hnew f List.mem_cons_self (hD1.edge_mem h)
    · exact (List.nodup_cons.1 hear.nodup).1 (List.mem_reverse.1 h)
  · exact ((List.reverse_perm T).append_left D₁).cons f |>.trans List.perm_middle.symm

end GeneralWalk

open Schoenflies

variable {β : Type*} {G B : Graph Plane β} {drawing : β → ℝ → Plane}
variable {e f : β} {u v w z a b : Plane} {W D : List β}

/-! ## What a walk of a polygonal plane graph draws -/

/-- **The realisation of a walk with polygonal edges is a polyline from its source to its
target.** The induction is along the walk: the first edge contributes its own vertex list, and
the two lists are joined at the waypoint, which is the last vertex of the first and the first
vertex of the rest. -/
theorem IsDrawing.exists_poly_eq_edgesCover (h : IsDrawing G drawing)
    (hpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc drawing e)) (hW : G.IsWalk u W v) (hne : W ≠ []) :
    ∃ vs : List Plane, ∃ hv : vs ≠ [], vs.head hv = u ∧ vs.getLast hv = v ∧
      poly vs = edgesCover drawing W := by
  induction hW with
  | nil => exact absurd rfl hne
  | @cons u w v e W hl hW ih =>
    have hedge : ∃ vs : List Plane, ∃ hv : vs ≠ [], vs.head hv = u ∧ vs.getLast hv = w ∧
        poly vs = edgeArc drawing e :=
      (h.edge_isArcBetween hl).exists_poly_eq (hpoly e hl.edge_mem) (h.ne_of_isLink hl)
    obtain ⟨es, hes, heshead, heslast, hespoly⟩ := hedge
    rcases eq_or_ne W [] with rfl | hWne
    · obtain rfl : w = v := hW.eq_of_nil
      exact ⟨es, hes, heshead, heslast, by
        rw [hespoly, edgesCover_cons, edgesCover_nil, Set.union_empty]⟩
    · obtain ⟨vs, hvs, hhead, hlast, hpolyv⟩ := ih hWne
      -- The two lists share the waypoint, so their carriers join there.
      refine ⟨es ++ vs, by simp [hes], ?_, ?_, ?_⟩
      · rw [List.head_append_of_ne_nil hes]; exact heshead
      · rw [List.getLast_append_of_ne_nil _ hvs]; exact hlast
      · rw [poly_append_of_eq hes hvs (by rw [heslast, hhead]), hespoly, hpolyv,
          edgesCover_cons]

/-! ## The realisation of a cycle is a separating curve

This is the composition the base case of `lem:face-cycles` needs, and the one thing that was
missing from it: `Graph.IsDrawing.cycle_isJordanCurve` says the realisation is a Jordan curve
and `Graph.IsDrawing.isPolygonal_edgesCover` says it is polygonal, and
`Schoenflies.exists_closedPolygon` — the realization theorem — turns that pair into a
`Schoenflies.ClosedPolygon`, whose carrier `Schoenflies.ClosedPolygon.isSeparating_carrier`
knows to separate the plane. Nothing here inspects the polygon; it is used and discarded. -/

/-- Going round the cycle the other way: the edge, then the detour, is a closed walk at the
edge's far end. This is the walk whose edge list is `e :: D`, the list every statement about
the realisation of a cycle is phrased with. -/
theorem IsCycleThrough.isWalk_cons {α : Type*} {G : Graph α β} {e : β} {u v : α} {D : List β}
    (hc : G.IsCycleThrough e u v D) : G.IsWalk v (e :: D) v :=
  IsWalk.cons hc.isLink.symm hc.isPath.isWalk

/-- **The realisation of a cycle of a polygonal plane graph is a separating Jordan curve.**
`Schoenflies.IsSeparating` is Definition 2.4: the complement has exactly two regions, one
bounded and one unbounded, each with the curve as its boundary. -/
theorem IsDrawing.cycle_isSeparating (h : IsDrawing G drawing)
    (hpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc drawing e)) {e : β} {u v : Plane} {D : List β}
    (hc : G.IsCycleThrough e u v D) : IsSeparating (edgesCover drawing (e :: D)) := by
  obtain ⟨m, P, hP⟩ := exists_closedPolygon (h.cycle_isJordanCurve hc)
    (h.isPolygonal_edgesCover hpoly hc.isWalk_cons (List.cons_ne_nil _ _))
  exact hP ▸ P.isSeparating_carrier

/-! ## What a subgraph spanned by a walk occupies -/

/-- An end of an edge lies on that edge's arc. -/
theorem IsDrawing.inc_mem_edgeArc (h : IsDrawing G drawing) {x : Plane} (hinc : G.Inc e x) :
    x ∈ edgeArc drawing e := by
  obtain ⟨y, hy⟩ := hinc
  exact (h.edge_isArcBetween hy).left_mem

/-- **The subgraph spanned by a nonempty walk occupies exactly what the walk draws.** Its
vertices are ends of its edges, so they add nothing to the union of the edge arcs. -/
theorem IsDrawing.pointSet_pathGraphOf (h : IsDrawing G drawing) (hW : G.IsWalk u W v)
    (hne : W ≠ []) : pointSet (G.pathGraphOf u W) drawing = edgesCover drawing W := by
  obtain ⟨f, T, rfl⟩ : ∃ f T, W = f :: T := by
    cases W with
    | nil => exact absurd rfl hne
    | cons f T => exact ⟨f, T, rfl⟩
  refine Set.Subset.antisymm (Set.union_subset ?_ ?_) ?_
  · -- Every vertex the walk visits is an end of one of its edges.
    intro x hx
    rw [pathGraphOf_vertexSet] at hx
    rcases mem_walkVertices_iff.1 hx with rfl | ⟨g, hg, hinc⟩
    · cases hW with
      | cons hl _ => exact mem_edgesCover List.mem_cons_self (h.inc_mem_edgeArc hl.inc_left)
    · exact mem_edgesCover hg (h.inc_mem_edgeArc hinc)
  · refine Set.iUnion₂_subset fun g hg => ?_
    rw [pathGraphOf_edgeSet hW] at hg
    exact fun z hz => mem_edgesCover hg hz
  · intro z hz
    obtain ⟨g, hg, hzg⟩ := mem_edgesCover_iff.1 hz
    refine edgeArc_subset_pointSet ?_ hzg
    rw [pathGraphOf_edgeSet hW]
    exact hg

/-- **The cycle subgraph occupies exactly what the cycle draws.** -/
theorem IsDrawing.pointSet_cycleGraph (h : IsDrawing G drawing) {e : β} {u v : Plane}
    {D : List β} (hc : G.IsCycleThrough e u v D) :
    pointSet (G.cycleGraph u e D) drawing = edgesCover drawing (e :: D) := by
  have hround := h.pointSet_pathGraphOf hc.isWalk_round (by simp)
  rw [cycleGraph, hround]
  refine Set.Subset.antisymm (edgesCover_mono fun g hg => ?_) (edgesCover_mono fun g hg => ?_)
  · rcases List.mem_append.1 hg with hg' | hg'
    · exact List.mem_cons_of_mem _ hg'
    · obtain rfl : g = e := by simpa using hg'
      exact List.mem_cons_self
  · rcases List.mem_cons.1 hg with rfl | hg'
    · exact List.mem_append_right _ List.mem_cons_self
    · exact List.mem_append_left _ hg'

/-! ## The conclusion of `lem:face-cycles`, at one face -/

/-- **A face bounded by a named cycle.** The face `face G drawing z` is one of the two regions
of the complement of the realisation of the cycle `e :: D` — which is the blueprint's "every
face … has a cycle as its boundary *and is one of the two complementary regions of that
cycle*". The cycle is a parameter rather than an existential so that a consumer that has
produced one keeps it. -/
structure IsFaceCycle (G : Graph Plane β) (drawing : β → ℝ → Plane) (z : Plane)
    (e : β) (u v : Plane) (D : List β) : Prop where
  /-- The named data really is a cycle of the graph. -/
  isCycle : G.IsCycleThrough e u v D
  /-- Its realisation separates the plane into exactly two regions. -/
  isSeparating : IsSeparating (edgesCover drawing (e :: D))
  /-- The face is one of those two. -/
  isRegionOf : IsRegionOf (edgesCover drawing (e :: D)) (face G drawing z)

namespace IsFaceCycle

variable {e : β} {u v : Plane} {D : List β}

/-- **"has a cycle as its boundary"**: the frontier of the face is the realisation. -/
theorem frontier_eq (h : IsFaceCycle G drawing z e u v D) :
    frontier (face G drawing z) = edgesCover drawing (e :: D) :=
  h.isRegionOf.frontier_eq h.isSeparating

/-- The face is the interior or the exterior of its boundary cycle. -/
theorem eq_inside_or_outside (h : IsFaceCycle G drawing z e u v D) :
    face G drawing z = inside (edgesCover drawing (e :: D)) ∨
      face G drawing z = outside (edgesCover drawing (e :: D)) := h.isRegionOf

/-- **"In particular, every bounded face is the interior of its boundary cycle."** The other
region of a separating curve is the unbounded one. -/
theorem eq_inside_of_isBounded (h : IsFaceCycle G drawing z e u v D)
    (hbdd : Bornology.IsBounded (face G drawing z)) :
    face G drawing z = inside (edgesCover drawing (e :: D)) := by
  rcases h.isRegionOf with hin | hout
  · exact hin
  · exact absurd (hout ▸ hbdd) h.isSeparating.not_isBounded_outside

/-- A face bounded by a cycle of a subgraph is bounded by the same cycle of the whole graph,
*provided the face itself is unchanged* — which is the shape the induction step needs when it
carries a face past an ear that does not touch it. -/
theorem mono (h : IsFaceCycle B drawing z e u v D) (hBG : B ≤ G)
    (hface : face G drawing z = face B drawing z) : IsFaceCycle G drawing z e u v D where
  isCycle := ⟨h.isCycle.isLink.mono hBG, h.isCycle.isPath.mono hBG, h.isCycle.notMem⟩
  isSeparating := h.isSeparating
  isRegionOf := hface ▸ h.isRegionOf

end IsFaceCycle

/-- **`lem:face-cycles`, as a property of a plane graph**: every face has a cycle as its
boundary and is one of the two complementary regions of that cycle. -/
def HasFaceCycles (G : Graph Plane β) (drawing : β → ℝ → Plane) : Prop :=
  ∀ z ∈ exterior G drawing, ∃ (e : β) (u v : Plane) (D : List β), IsFaceCycle G drawing z e u v D

/-! ## The base case: the faces of a single cycle

"This is true for the initial cycle by Theorem `thm:polygonal-jordan`." The cycle subgraph
occupies exactly the cycle's realisation, so its faces are literally the components of the
complement of that curve, and the curve is separating. -/

/-- **The base case of `lem:face-cycles`.** Both faces of the graph consisting of one cycle
are regions of that cycle. -/
theorem IsDrawing.hasFaceCycles_cycleGraph (h : IsDrawing G drawing)
    (hpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc drawing e)) {e : β} {u v : Plane} {D : List β}
    (hc : G.IsCycleThrough e u v D) : HasFaceCycles (G.cycleGraph u e D) drawing := by
  have hsep : IsSeparating (edgesCover drawing (e :: D)) := h.cycle_isSeparating hpoly hc
  -- The same cycle, read inside the subgraph it spans.
  have hcyc : (G.cycleGraph u e D).IsCycleThrough e u v D :=
    ⟨hc.cycleGraph_isLink,
      hc.isPath.anti hc.cycleGraph_le hc.left_mem_cycleGraph fun g hg => by
        rw [hc.cycleGraph_edgeSet]; exact List.mem_append_left _ hg,
      hc.notMem⟩
  intro z hz
  refine ⟨e, u, v, D, hcyc, hsep, ?_⟩
  rw [face, exterior, h.pointSet_cycleGraph hc]
  refine hsep.isRegionOf_connectedComponentIn ?_
  rw [exterior, h.pointSet_cycleGraph hc] at hz
  exact hz

/-! ## The two arcs a cycle is cut into, as sets

The combinatorial split of `Graph.IsCycleThrough.split_at` becomes the geometric one: the two
arcs of the Jordan curve between the two cut vertices. The drawing condition is used once, to
turn "the two edge lists are disjoint" into "the two arcs meet only at vertices". -/

/-- A vertex of the graph lying on the realisation of a cycle is a vertex of that cycle. -/
theorem IsDrawing.mem_walkVertices_of_mem_edgesCover (h : IsDrawing G drawing) {e : β}
    {u v z : Plane} {D : List β} (hc : G.IsCycleThrough e u v D) (hzV : z ∈ V(G))
    (hz : z ∈ edgesCover drawing (e :: D)) : z ∈ G.walkVertices u D := by
  obtain ⟨g, hg, hzg⟩ := mem_edgesCover_iff.1 hz
  rcases List.mem_cons.1 hg with rfl | hg'
  · rcases h.vertex_mem_edgeArc hc.isLink hzV hzg with rfl | rfl
    · exact mem_walkVertices_self
    · exact hc.isPath.target_mem_walkVertices
  · obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet (hc.isPath.edge_mem hg')
    rcases h.vertex_mem_edgeArc hxy hzV hzg with rfl | rfl
    · exact mem_walkVertices_of_mem_covered ⟨g, hg', hxy.inc_left⟩
    · exact mem_walkVertices_of_mem_covered ⟨g, hg', hxy.inc_right⟩

/-- **The realisation of a cycle, cut at two of its vertices, is two arcs meeting exactly
there.** The hypotheses are the output of `Graph.IsCycleThrough.split_at`, read in the plane. -/
theorem IsDrawing.arcs_of_split (h : IsDrawing G drawing) {a b : Plane} {D₁ D₂ : List β}
    (h₁ : G.IsPath a D₁ b) (h₂ : G.IsPath b D₂ a) (hab : a ≠ b)
    (hdisj : ∀ g ∈ D₁, g ∉ D₂)
    (hmeet : ∀ y ∈ G.walkVertices a D₁, y ∈ G.walkVertices b D₂ → y = a ∨ y = b) :
    IsArcBetween (edgesCover drawing D₁) a b ∧ IsArcBetween (edgesCover drawing D₂) b a ∧
      edgesCover drawing D₁ ∩ edgesCover drawing D₂ = {a, b} := by
  have harc₁ : IsArcBetween (edgesCover drawing D₁) a b :=
    h.path_isArcBetween h₁ (h₁.ne_nil hab)
  have harc₂ : IsArcBetween (edgesCover drawing D₂) b a :=
    h.path_isArcBetween h₂ (h₂.ne_nil (Ne.symm hab))
  refine ⟨harc₁, harc₂, Set.Subset.antisymm (fun z ⟨hz₁, hz₂⟩ => ?_) ?_⟩
  · -- A common point lies on an edge of each, and the two edges are distinct.
    obtain ⟨g₁, hg₁, hzg₁⟩ := mem_edgesCover_iff.1 hz₁
    obtain ⟨g₂, hg₂, hzg₂⟩ := mem_edgesCover_iff.1 hz₂
    have hne : g₁ ≠ g₂ := fun hh => hdisj g₁ hg₁ (hh ▸ hg₂)
    obtain ⟨-, hinc₁, hinc₂⟩ :=
      h.edge_inter (h₁.edge_mem hg₁) (h₂.edge_mem hg₂) hne hzg₁ hzg₂
    exact hmeet z (mem_walkVertices_of_mem_covered ⟨g₁, hg₁, hinc₁⟩)
      (mem_walkVertices_of_mem_covered ⟨g₂, hg₂, hinc₂⟩)
  · rintro z (rfl | rfl)
    exacts [⟨harc₁.left_mem, harc₂.right_mem⟩, ⟨harc₁.right_mem, harc₂.left_mem⟩]

end Graph

namespace Schoenflies

/-! ## The obligation this module does not discharge

**Read this before using `Graph.face_cycles`.** Everything below the base case is proved
*modulo* one hypothesis, `Schoenflies.CrosscutSplitsRegion`, and the final theorem carries it
as an argument. It is the exhaustion clause of `thm:polygonal-crosscut` — Theorem 2.8, in the
shape `Schoenflies.IsPolygonalCrosscut.region_eq` and
`Schoenflies.IsPolygonalCrosscut.cell_isComponent₁` already have it — at a crosscut whose two
endpoints are **arbitrary points of the curve**.

`main`'s Theorem 2.8 cannot be applied here, and the reason is not a missing bridge. Its
hypotheses `edges₁`/`edges₂` are stated against `ClosedPolygon.arcPieces C a k`, which splits
the polygon's edge list **at two of its vertices**; and by
`Schoenflies.ClosedPolygon.isCornerAt_vertex` every vertex of every realization of a curve is a
*corner* of it. In the induction below the two cut points are the ear's endpoints, which are
graph vertices at which the two cycle edges may perfectly well leave along opposite rays — the
curve then runs straight through the cut point, which is therefore a vertex of no
`ClosedPolygon` with that carrier, and no realization theorem can supply one. Discharging this
hypothesis needs Theorem 2.8 restated for an edge-list split made at arbitrary points, which in
turn needs the parity theory for polygon presentations carrying redundant vertices
(`Schoenflies.PrePolygon`) rather than only for `ClosedPolygon`. That is a separate module. -/

/-- **The exhaustion clause of the polygonal crosscut theorem, at arbitrary cut points.**
`J` is a separating polygonal curve cut by the points `p, q` into the arcs `A₁, A₂`; `P` is a
polygonal crosscut from `p` to `q` meeting `J` only there and running inside the region `Ω`.
The claim is that every component of `Ω ∖ P` is a region of `A₁ ∪ P` or of `A₂ ∪ P` — the
blueprint's "Theorem 2.8 replaces `F` by exactly two regions, both bounded by cycles".

This is **assumed**, not proved; see the section docstring for why `main`'s Theorem 2.8 does
not apply. -/
def CrosscutSplitsRegion : Prop :=
  ∀ (J A₁ A₂ P Ω : Set Plane) (p q : Plane),
    IsSeparating J → IsPolygonal J → IsPolygonal P →
    IsArcBetween A₁ p q → IsArcBetween A₂ p q → A₁ ∪ A₂ = J → A₁ ∩ A₂ = {p, q} →
    IsArcBetween P p q → P ∩ J = {p, q} → IsRegionOf J Ω → P \ {p, q} ⊆ Ω →
    ∀ z ∈ Ω \ P, IsRegionOf (A₁ ∪ P) (connectedComponentIn (Ω \ P) z) ∨
      IsRegionOf (A₂ ∪ P) (connectedComponentIn (Ω \ P) z)

end Schoenflies

namespace Graph

open Schoenflies

variable {β : Type*} {G B : Graph Plane β} {drawing : β → ℝ → Plane}
variable {e f : β} {u v w z a b : Plane} {W D : List β}

/-! ## What a list of edges draws depends only on which edges are on it -/

theorem edgesCover_append (drawing : β → ℝ → Plane) (W₁ W₂ : List β) :
    edgesCover drawing (W₁ ++ W₂) = edgesCover drawing W₁ ∪ edgesCover drawing W₂ := by
  refine Set.Subset.antisymm (fun z hz => ?_)
    (Set.union_subset (edgesCover_mono (List.subset_append_left _ _))
      (edgesCover_mono (List.subset_append_right _ _)))
  obtain ⟨g, hg, hzg⟩ := mem_edgesCover_iff.1 hz
  exact (List.mem_append.1 hg).imp (fun h => mem_edgesCover h hzg) fun h => mem_edgesCover h hzg

theorem edgesCover_perm {W₁ W₂ : List β} (hp : W₁.Perm W₂) :
    edgesCover drawing W₁ = edgesCover drawing W₂ :=
  Set.Subset.antisymm (edgesCover_mono fun _ hg => hp.mem_iff.1 hg)
    (edgesCover_mono fun _ hg => hp.mem_iff.2 hg)

theorem edgesCover_reverse (drawing : β → ℝ → Plane) (W : List β) :
    edgesCover drawing W.reverse = edgesCover drawing W := edgesCover_perm (List.reverse_perm W)

/-! ## The induction step: one ear

"Suppose it holds for the current graph and add the next geometric ear. Its interior is
connected and disjoint from the current graph, so it lies in one current face `F` … the ear is
therefore a crosscut of that side, and Theorem `thm:polygonal-crosscut` replaces `F` by exactly
two regions, both bounded by cycles; all other faces are unchanged."

Everything here is proved, except that the appeal to Theorem 2.8 is to the hypothesis
`Schoenflies.CrosscutSplitsRegion` instead. -/

/-- **One ear.** Given `lem:face-cycles` for the current subgraph, it holds for the subgraph
enlarged by an ear — modulo `Schoenflies.CrosscutSplitsRegion`. -/
theorem IsDrawing.hasFaceCycles_union [G.Finite] (h : IsDrawing G drawing)
    (hobl : CrosscutSplitsRegion) (hpoly : ∀ g ∈ E(G), IsPolygonal (edgeArc drawing g))
    (hBG : B ≤ G) (hmot : HasFaceCycles B drawing) {D' : List β}
    (hpath : G.IsPath a D' b) (hab : a ≠ b) (ha : a ∈ V(B)) (hb : b ∈ V(B))
    (hint : ∀ y ∈ G.walkVertices a D', y ≠ a → y ≠ b → y ∉ V(B))
    (hnew : ∀ g ∈ D', g ∉ E(B)) :
    HasFaceCycles (B.union (G.pathGraphOf a D')) drawing := by
  haveI : B.Finite := Finite.of_le hBG
  have hB : IsDrawing B drawing := h.mono hBG
  have hne : D' ≠ [] := hpath.ne_nil hab
  have hPG : G.pathGraphOf a D' ≤ G := pathGraphOf_le hpath.isWalk
  have hB'G : B.union (G.pathGraphOf a D') ≤ G := union_le hBG hPG
  have hBB' : B ≤ B.union (G.pathGraphOf a D') := left_le_union _ _
  have hB' : IsDrawing (B.union (G.pathGraphOf a D')) drawing := h.mono hB'G
  have hpoly' : ∀ g ∈ E(B.union (G.pathGraphOf a D')), IsPolygonal (edgeArc drawing g) :=
    fun g hg => hpoly g (hB'G.edgeSet_mono hg)
  have hQarc : IsArcBetween (edgesCover drawing D') a b := h.path_isArcBetween hpath hne
  have hQpoly : IsPolygonal (edgesCover drawing D') :=
    h.isPolygonal_edgesCover hpoly hpath.isWalk hne
  have hext : exterior (B.union (G.pathGraphOf a D')) drawing =
      exterior B drawing \ edgesCover drawing D' := by
    rw [exterior_union, h.pointSet_pathGraphOf hpath.isWalk hne]
  -- The ear lies in one face of the old subgraph.
  obtain ⟨z₀, hz₀, hsub₀⟩ := h.exists_face_of_ear hBG hpath hab hint hnew
  have hQinter : ∀ w ∈ edgesCover drawing D', w ∈ exterior B drawing →
      w ∈ face B drawing z₀ := by
    intro w hw hwe
    refine hsub₀ ⟨hw, fun hcon => hwe ?_⟩
    rcases hcon with rfl | rfl
    exacts [vertexSet_subset_pointSet ha, vertexSet_subset_pointSet hb]
  intro z hz
  rw [hext] at hz
  obtain ⟨hzB, hzQ⟩ := hz
  obtain ⟨e, u, v, D, hface⟩ := hmot z hzB
  by_cases hsame : face B drawing z = face B drawing z₀
  · -- The face the ear cuts.
    have hopenF : IsOpen (face B drawing z₀) := hB.isOpen_face z₀
    obtain ⟨haF, hbF⟩ := h.ends_mem_frontier_face hopenF hpath hab ha hb hsub₀
    have hfr : frontier (face B drawing z₀) = edgesCover drawing (e :: D) := by
      rw [← hsame]; exact hface.frontier_eq
    have haW : a ∈ B.walkVertices u D :=
      hB.mem_walkVertices_of_mem_edgesCover hface.isCycle ha (hfr ▸ haF)
    have hbW : b ∈ B.walkVertices u D :=
      hB.mem_walkVertices_of_mem_edgesCover hface.isCycle hb (hfr ▸ hbF)
    obtain ⟨D₁, D₂, hD1, hD2, hperm, hmeet⟩ := hface.isCycle.split_at haW hbW hab
    -- The two arcs use disjoint edge lists, because the cycle's own list repeats nothing.
    have hnodup : (e :: D).Nodup := List.nodup_cons.2 ⟨hface.isCycle.notMem,
      hface.isCycle.isPath.nodup⟩
    have hdisj : ∀ g ∈ D₁, g ∉ D₂ := fun g hg hg₂ =>
      (List.nodup_append.1 (hperm.nodup_iff.2 hnodup)).2.2 g hg g hg₂ rfl
    obtain ⟨harc₁, harc₂, hinter⟩ := hB.arcs_of_split hD1 hD2 hab hdisj hmeet
    have hunion : edgesCover drawing D₁ ∪ edgesCover drawing D₂ = edgesCover drawing (e :: D) := by
      rw [← edgesCover_append, edgesCover_perm hperm]
    -- The ear meets the cycle exactly in its own two ends.
    have hJsub : edgesCover drawing (e :: D) ⊆ pointSet B drawing :=
      edgesCover_subset_pointSet fun g hg => by
        rcases List.mem_cons.1 hg with rfl | hg'
        exacts [hface.isCycle.isLink.edge_mem, hface.isCycle.isPath.edge_mem hg']
    have hmeetJ : edgesCover drawing D' ∩ edgesCover drawing (e :: D) = {a, b} := by
      refine Set.Subset.antisymm (fun w hw =>
        h.edgesCover_inter_pointSet hBG hpath hint hnew ⟨hw.1, hJsub hw.2⟩) ?_
      rintro w (rfl | rfl)
      exacts [⟨hQarc.left_mem, hfr ▸ haF⟩, ⟨hQarc.right_mem, hfr ▸ hbF⟩]
    -- The crosscut hypothesis.
    have hzF : z ∈ face B drawing z \ edgesCover drawing D' := ⟨mem_face hzB, hzQ⟩
    have hfaceEq : face (B.union (G.pathGraphOf a D')) drawing z =
        connectedComponentIn (face B drawing z \ edgesCover drawing D') z := by
      have hstep : face (B.union (G.pathGraphOf a D')) drawing z =
          connectedComponentIn (exterior B drawing \ edgesCover drawing D') z := by
        rw [face, hext]
      rw [hstep, connectedComponentIn_diff]
      rfl
    have hcross := hobl (edgesCover drawing (e :: D)) (edgesCover drawing D₁)
      (edgesCover drawing D₂) (edgesCover drawing D') (face B drawing z) a b
      hface.isSeparating
      (h.isPolygonal_edgesCover hpoly (hface.isCycle.isWalk_cons.mono hBG)
        (List.cons_ne_nil _ _))
      hQpoly harc₁ harc₂.reverse hunion hinter hQarc hmeetJ hface.isRegionOf
      (by rw [hsame]; exact hsub₀) z hzF
    -- Either way, the new face is a region of the arc closed up by the ear.
    rcases hcross with hreg | hreg
    · obtain ⟨f, x, y, T, hcyc, hpermT⟩ := exists_spliced_cycle hBG hD1 hpath hab hnew hint
      have hcov : edgesCover drawing (f :: T) =
          edgesCover drawing D₁ ∪ edgesCover drawing D' := by
        rw [edgesCover_perm hpermT, edgesCover_append]
      exact ⟨f, x, y, T, hcyc, hB'.cycle_isSeparating hpoly' hcyc,
        by rw [hcov, hfaceEq]; exact hreg⟩
    · obtain ⟨f, x, y, T, hcyc, hpermT⟩ :=
        exists_spliced_cycle hBG hD2.reverse hpath hab hnew hint
      have hcov : edgesCover drawing (f :: T) =
          edgesCover drawing D₂ ∪ edgesCover drawing D' := by
        rw [edgesCover_perm hpermT, edgesCover_append, edgesCover_reverse]
      exact ⟨f, x, y, T, hcyc, hB'.cycle_isSeparating hpoly' hcyc,
        by rw [hcov, hfaceEq]; exact hreg⟩
  · -- The ear misses this face, which therefore survives unchanged.
    have hdis : Disjoint (face B drawing z) (pointSet (G.pathGraphOf a D') drawing) := by
      rw [h.pointSet_pathGraphOf hpath.isWalk hne, Set.disjoint_left]
      intro w hw hwQ
      refine absurd ?_ hsame
      refine (face_eq_or_disjoint (G := B) (drawing := drawing) z z₀).resolve_right fun hd => ?_
      exact Set.disjoint_left.1 hd hw (hQinter w hwQ (face_subset_exterior _ _ _ hw))
    exact ⟨e, u, v, D, hface.mono hBB' (face_union_eq_of_disjoint hzB hdis)⟩

/-! ## `lem:face-cycles`

"The cycle `C` is 2-connected, so Lemma `lem:relative-ear` builds the graph from `C`. We prove
by induction that every face is exactly one of the two regions bounded by its boundary cycle." -/

/-- **`lem:face-cycles` (face cycles).** Every face of a finite 2-connected polygonal plane
graph has a cycle as its boundary and is one of the two complementary regions of that cycle.

**The statement carries the hypothesis `Schoenflies.CrosscutSplitsRegion`**, which is *not*
proved anywhere: it is the exhaustion clause of `thm:polygonal-crosscut` at a crosscut whose
endpoints need not be corners of the curve, and `main`'s Theorem 2.8 cannot supply it — see the
docstring of `Schoenflies.CrosscutSplitsRegion`. Everything else in the blueprint's proof is
discharged here: the base cycle and its 2-connectivity (`Schoenflies/FaceCycles.lean`), that
its realisation separates the plane (`Graph.IsDrawing.cycle_isSeparating`), that the ear lies in
one face and is a crosscut of it, that all other faces are unchanged, and that the two new
faces are bounded by the two cycles the ear splices onto the two arcs of the old one. -/
theorem face_cycles [G.Finite] (hobl : CrosscutSplitsRegion) (h : IsDrawing G drawing)
    (hpoly : ∀ g ∈ E(G), IsPolygonal (edgeArc drawing g)) (hG : G.IsTwoConnected) :
    HasFaceCycles G drawing := by
  have hnl : ∀ ⦃g x⦄, ¬ G.IsLoopAt g x := fun g x => h.not_isLoopAt g x
  obtain ⟨e, u, v, D, w, hcyc⟩ := hG.exists_long_cycle hnl
  refine hG.ear_decomposition (motive := fun B => HasFaceCycles B drawing) hnl
    hcyc.isTwoConnected hcyc.isCycle.cycleGraph_le
    (h.hasFaceCycles_cycleGraph hpoly hcyc.isCycle) ?_
  intro B a b D' _ _ hBG hmot hpathD hab haB hbB hintB
  -- Either the ear is genuinely new, or it is an edge the subgraph already had and adding it
  -- changes nothing.
  rcases ear_edges_notMem_or_union_eq hBG hpathD hab haB hbB hintB with hnew | heq
  · exact h.hasFaceCycles_union hobl hpoly hBG hmot hpathD hab haB hbB hintB hnew
  · rw [heq]; exact hmot

end Graph

end BundlePart416

section BundlePart417
/- Source: dev/planar_search/schoenflies_port/Schoenflies/PrePolygonSep.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/


/-!
# Separation and crossing parity before normalization

`Schoenflies.ClosedPolygon` carries a `corner` field — no three consecutive vertices collinear —
and `Schoenflies.ClosedPolygon.isCornerAt_vertex` shows that field is not slack: a point at which
the curve runs straight is a vertex of *no* `ClosedPolygon` presentation of it. So a consumer that
must present a curve with vertices at prescribed points cannot use `ClosedPolygon` at all, and the
plane-graph arguments are exactly such consumers: the branch points of a drawing land wherever the
drawing puts them.

`Schoenflies.PrePolygon` is the presentation without that field, and vertices may be put anywhere.
This module gives it everything the crosscut chain asks of a simple closed polygon: an edge list
for the crossing count, the curve statements, the polygonal Jordan curve theorem, and the two
parity values.

## Everything transports across normalization, except the parity

`Schoenflies.PrePolygon.exists_closedPolygon_of_prePolygon` deletes redundant vertices and returns
a genuine `ClosedPolygon` **with the same carrier**. Any property of the carrier *as a set* is
therefore free: `isJordanCurve_carrier`, `isPolygonal_carrier` and `isSeparating_carrier` below are
each three lines, and none of them needs a word about vertices.

The crossing parity is not a property of the carrier. It is computed from a *list of edges*, and
normalization changes that list: it merges collinear edges, so `P.pieces` is a subdivision of the
normalized polygon's. Lemma 2.1 (`Schoenflies.parity_subdivide`) says subdivision does not change
the parity, which is why one *expects* the parity to transport — but the normalization theorem is
an existence statement and keeps no record of which points were deleted, so there is no
subdivision in hand to feed it. See the note at the end of this docstring.

The parity is therefore re-derived here, and the derivation turns out not to need the collar at
all. Once the curve is known to separate, the two values are forced:

* far along the ray direction the count is zero, and the half-plane where it is zero is convex and
  unbounded, hence lies in the unbounded region — so `π_C = 0` on the outside;
* across an interior point of any one edge the count jumps by one (Lemma 2.2), and the two test
  points lie off the curve, so they lie in different regions — so the other region carries `1`.

Both steps are stated for an arbitrary closed chain whose cover separates the plane
(`Schoenflies.parity_eq_zero_of_mem_outside_cover`, `…parity_eq_one_of_mem_inside_cover`); the
`PrePolygon` statements are instances. **The `ClosedPolygon` versions in
`Schoenflies/PolygonalJordan.lean` are instances too** — `ClosedPolygon.parity_eq_one_of_mem_inside`
currently goes through `StripData`, and does not have to.

## Blueprint

* `Schoenflies.PrePolygon.pieces`, `…cover_pieces`, `…isClosedChain_pieces`, `…pieces_nondeg` —
  the edge list the crossing count of §2 is defined on, for a vertex list that has not been
  normalized. Same list as `ClosedPolygon.pieces`; `PrePolygon.pieces_toPre` is `rfl`.
* `Schoenflies.PrePolygon.isJordanCurve_carrier`, `…isPolygonal_carrier` — §1, "a simple closed
  polygonal curve"; jointly the hypothesis of Theorem 2.3.
* `Schoenflies.PrePolygon.isSeparating_carrier` — **Theorem 2.3** in the form Definition 2.4 asks
  for, for a polygon presented with redundant vertices.
* `Schoenflies.PrePolygon.parity_flip_carrier` — Lemma 2.2, second half.
* `Schoenflies.parity_eq_zero_of_mem_outside_cover`,
  `Schoenflies.parity_eq_one_of_mem_inside_cover` — the last sentence of Theorem 2.3, for an
  arbitrary closed chain whose cover separates.
* `Schoenflies.PrePolygon.parity_eq_zero_of_mem_outside`, `…parity_eq_one_of_mem_inside`,
  `…parity_eq_zero_iff`, `…parity_eq_one_iff` — the same, read off a `PrePolygon`.

## Two notes for the integrator

**`PrePolygon.pieces` duplicates `ClosedPolygon.pieces`.** The two definitions are literally the
same expression and `PrePolygon.pieces_toPre` proves them equal by `rfl`. The right arrangement is
to define `ClosedPolygon.pieces P := P.toPre.pieces` and to keep only the `PrePolygon` proofs — the
proofs of `cover_pieces`, `isClosedChain_pieces`, `pieces_nondeg`, `pieces_nodup`,
`notMem_edge_of_mem_openSegment` and `parity_flip_carrier` in `Schoenflies/PolygonBridge.lean` use
`vertex_inj` and `edges_meet` and nothing else, so they are the proofs below with `ClosedPolygon`
written for `PrePolygon`. That refactor cannot happen inside this module: `PrePolygon` is declared
in `Schoenflies/Realization.lean`, which is *downstream* of `PolygonBridge`. It needs `PrePolygon`
moved up beside `ClosedPolygon` in `Schoenflies/Strip.lean`.

**Merging collinear edges is a subdivision, but not one this development can point at.** Deleting
a redundant vertex `v` replaces the two edges at `v` by their union, which is exactly undoing
`Schoenflies.splitAt v` on the merged edge; iterating, `P.pieces` is `subdivide P'.pieces vs` for
the list `vs` of deleted vertices — *up to the order of the list*, which `rotate` disturbs. So two
things are missing before `parity_subdivide` could be used here: `Schoenflies.parity` invariance
under `List.Perm` (immediate, `parity` is a sum over the list), and a strengthening of
`exists_closedPolygon_of_prePolygon` to
`∃ m' (P' : ClosedPolygon m') (vs : List Plane), P'.carrier = P.carrier ∧
  P.pieces ~ subdivide P'.pieces vs`, carried through the induction. The direct argument below is
shorter than either.
-/

open Bornology Metric Set

namespace Schoenflies

open Plane

/-! ## Small arithmetic helpers

Copies of two `private` facts of `Schoenflies/PolygonalJordan.lean`; they are `private` there and
so are these. -/

/-- In `ZMod 2` nothing is its own successor: this is what "the parities differ" comes down to. -/
private theorem ne_add_one_zmod_two (x : ZMod 2) : x ≠ x + 1 := by revert x; decide

/-- The only two values, named. -/
private theorem eq_one_of_ne_zero_zmod_two {x : ZMod 2} (h : x ≠ 0) : x = 1 := by
  revert h; revert x; decide

/-! ## The two parity values from separation alone

The blueprint reads the two values off a point far along the ray direction and off a point either
side of an edge. Neither step knows anything about vertices, so both are stated here for an
arbitrary closed chain whose cover separates the plane. -/

section GeneralParity

variable {L : List Piece} {u : Plane}

/-- The forward coordinate is linear. This is all that is needed to see that a half-plane is
convex. -/
private theorem isLinearMap_fwd (u : Plane) : IsLinearMap ℝ (fwd u) where
  map_add x y := by simp only [fwd_eq, Plane.add_apply]; ring
  map_smul c x := by simp only [fwd_eq, Plane.smul_apply, smul_eq_mul]; ring

/-- The half-plane of points more than `R` along the ray direction. Beyond a bound on the polygon
it is the region in which the crossing count is visibly zero, and it is unbounded, which is what
places it in the unbounded region. -/
private def farSide (u : Plane) (R : ℝ) : Set Plane := {z | R < fwd u z}

private theorem convex_farSide (u : Plane) (R : ℝ) : Convex ℝ (farSide u R) :=
  convex_halfSpace_gt (isLinearMap_fwd u) R

/-- The forward coordinate of a multiple of the direction is the multiple. -/
private theorem fwd_smul_self (hu : Plane.IsDirection u) (s : ℝ) : fwd u (s • u) = s := by
  have h : fwd u (s • u) = s * fwd u u := by simp only [fwd_eq, Plane.smul_apply]; ring
  rw [h, fwd_self hu, mul_one]

/-- The half-plane is unbounded: it contains points of every size along the direction. -/
private theorem not_isBounded_farSide (hu : Plane.IsDirection u) (R : ℝ) :
    ¬ IsBounded (farSide u R) := by
  intro hb
  obtain ⟨R', hR'⟩ := hb.subset_closedBall (0 : Plane)
  set t : ℝ := max (max R R') 0 + 1 with htdef
  have h0 : 0 ≤ max (max R R') 0 := le_max_right _ _
  have hpos : 0 < t := by rw [htdef]; linarith
  have hR1 : R < t := by
    have := le_trans (le_max_left R R') (le_max_left (max R R') 0)
    rw [htdef]; linarith
  have hR2 : R' < t := by
    have := le_trans (le_max_right R R') (le_max_left (max R R') 0)
    rw [htdef]; linarith
  have hmem : t • u ∈ farSide u R := by
    change R < fwd u (t • u)
    rw [fwd_smul_self hu]; exact hR1
  have hnorm : ‖t • u‖ = t := by
    rw [norm_smul, Real.norm_eq_abs, hu, mul_one, abs_of_pos hpos]
  have := mem_closedBall_zero_iff.1 (hR' hmem)
  rw [hnorm] at this
  linarith

/-- **`π_C = 0` on the unbounded region** (Theorem 2.3, last sentence), for any closed chain whose
cover separates the plane.

The blueprint's argument: a point far enough along the ray direction is crossed by no edge, and the
whole half-plane of such points is convex — hence connected — and unbounded, so it lies in the
unbounded region. Parity is constant there (Lemma 2.2), and the value is the one read off the far
point. -/
theorem parity_eq_zero_of_mem_outside_cover (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ L, hgt u Q.1 ≠ hgt u Q.2) (hC : IsClosedChain L)
    (hsep : IsSeparating (cover L)) {x : Plane} (hx : x ∈ outside (cover L)) :
    parity u L x = 0 := by
  obtain ⟨R, hR⟩ := (isCompact_cover L).isBounded.subset_closedBall (0 : Plane)
  have hcov : ∀ z ∈ cover L, fwd u z ≤ R := fun z hz =>
    le_trans (le_trans (le_abs_self _) (abs_fwd_le_norm hu z)) (mem_closedBall_zero_iff.1 (hR hz))
  have hdisj : farSide u R ⊆ (cover L)ᶜ := fun z hz hzc => absurd (hcov z hzc) (not_le.2 hz)
  have hqf : fwd u ((R + 1) • u) = R + 1 := fwd_smul_self hu (R + 1)
  have hqmem : (R + 1) • u ∈ farSide u R := by
    change R < fwd u ((R + 1) • u)
    rw [hqf]; linarith
  -- the far point is in the unbounded region, because the whole half-plane is
  have hqout : (R + 1) • u ∈ outside (cover L) := by
    refine ⟨hdisj hqmem, fun hb => not_isBounded_farSide hu R (hb.subset ?_)⟩
    exact (convex_farSide u R).isPreconnected.subset_connectedComponentIn hqmem hdisj
  have hq0 : parity u L ((R + 1) • u) = 0 :=
    parity_eq_zero_of_lt hL fun z hz => lt_of_le_of_lt (hcov z hz) (by rw [hqf]; linarith)
  rw [← hq0]
  exact parity_eq_of_isPreconnected hu hL hC hsep.isConnected_outside.isPreconnected
    (fun z hz => hz.1) hx hqout

/-- **`π_C = 1` on the bounded region** (Theorem 2.3, last sentence), for any closed chain whose
cover separates the plane and which has *some* two points of the complement with different
parities.

Those two points cannot be in the same region, since parity is constant on a region; so one of them
is inside and the other outside. The outside carries `0`, hence the inside does not.

For a polygon the two points are supplied by Lemma 2.2: just before and just after an interior
point of any single edge. -/
theorem parity_eq_one_of_mem_inside_cover (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ L, hgt u Q.1 ≠ hgt u Q.2) (hC : IsClosedChain L)
    (hsep : IsSeparating (cover L)) {a b : Plane} (ha : a ∉ cover L) (hb : b ∉ cover L)
    (hab : parity u L a ≠ parity u L b) {x : Plane} (hx : x ∈ inside (cover L)) :
    parity u L x = 1 := by
  have hzero : ∀ y ∈ outside (cover L), parity u L y = 0 := fun y hy =>
    parity_eq_zero_of_mem_outside_cover hu hL hC hsep hy
  have hconst : ∀ y ∈ inside (cover L), parity u L y = parity u L x := fun y hy =>
    parity_eq_of_isPreconnected hu hL hC hsep.isConnected_inside.isPreconnected
      (fun z hz => hz.1) hy hx
  have hma : a ∈ inside (cover L) ∪ outside (cover L) := by rw [inside_union_outside]; exact ha
  have hmb : b ∈ inside (cover L) ∪ outside (cover L) := by rw [inside_union_outside]; exact hb
  refine eq_one_of_ne_zero_zmod_two ?_
  rcases hma with h | h <;> rcases hmb with h' | h'
  · exact absurd ((hconst a h).trans (hconst b h').symm) hab
  · rw [hzero b h'] at hab
    rw [← hconst a h]
    exact hab
  · rw [hzero a h] at hab
    rw [← hconst b h']
    exact Ne.symm hab
  · exact absurd ((hzero a h).trans (hzero b h').symm) hab

end GeneralParity

namespace PrePolygon

variable {m : ℕ}

/-! ## The edge list

Verbatim `Schoenflies.ClosedPolygon.pieces` with the structure changed; `pieces_toPre` records
that the two are the same list. -/

/-- The `m + 3` edges of the polygon, as a list of pieces in cyclic order. This is the form the
crossing count of §2 is defined on. -/
def pieces (P : PrePolygon m) : List Piece :=
  (List.range (m + 3)).map fun j : ℕ =>
    (P.vertex (j : ZMod (m + 3)), P.vertex ((j : ZMod (m + 3)) + 1))

/-- Forgetting the `corner` field does not change the edge list. -/
@[simp] theorem pieces_toPre (P : ClosedPolygon m) : P.toPre.pieces = P.pieces := rfl

/-- Every edge of the polygon is on the list. -/
theorem mem_pieces (P : PrePolygon m) (i : ZMod (m + 3)) :
    (P.vertex i, P.vertex (i + 1)) ∈ P.pieces := by
  refine List.mem_map.2 ⟨i.val, List.mem_range.2 (ZMod.val_lt i), ?_⟩
  rw [ZMod.natCast_rightInverse i]

/-- Every piece on the list is an edge of the polygon. -/
theorem exists_of_mem_pieces {P : PrePolygon m} {Q : Piece} (hQ : Q ∈ P.pieces) :
    ∃ i : ZMod (m + 3), Q = (P.vertex i, P.vertex (i + 1)) := by
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hQ
  exact ⟨(j : ZMod (m + 3)), rfl⟩

/-- No edge is degenerate: consecutive vertices are distinct. Redundant vertices are allowed, but
repeated ones are not. -/
theorem pieces_nondeg (P : PrePolygon m) : ∀ Q ∈ P.pieces, Q.Nondeg := by
  intro Q hQ
  obtain ⟨i, rfl⟩ := exists_of_mem_pieces hQ
  exact vertex_ne_succ i

/-- **The edge list is a closed chain.** Each vertex ends one edge and starts the next, so it is
counted twice; the cycle closes because `m + 3` is `0` in `ZMod (m + 3)`. -/
theorem isClosedChain_pieces (P : PrePolygon m) : IsClosedChain P.pieces := by
  intro f
  have hmap : (P.pieces.map fun Q => f Q.1 + f Q.2)
      = (List.range (m + 3)).map fun j : ℕ =>
        f (P.vertex (j : ZMod (m + 3))) + f (P.vertex ((j + 1 : ℕ) : ZMod (m + 3))) := by
    rw [pieces, List.map_map]
    refine List.map_congr_left fun j _ => ?_
    simp only [Function.comp_apply, ClosedPolygon.natCast_succ]
  rw [hmap]
  have key := sum_range_boundary (fun k : ℕ => f (P.vertex (k : ZMod (m + 3)))) (m + 3)
  rw [key, Nat.cast_zero, ZMod.natCast_self]
  exact add_self_zmod_two _

/-- **The edge list carries the polygon.** This is the equation that turns every parity statement,
which is about `cover`, into a statement about the carrier. -/
theorem cover_pieces (P : PrePolygon m) : cover P.pieces = P.carrier := by
  apply Set.Subset.antisymm
  · rw [cover]
    refine Set.iUnion₂_subset fun Q hQ => ?_
    obtain ⟨i, rfl⟩ := exists_of_mem_pieces hQ
    exact Set.subset_iUnion (fun i => P.edge i) i
  · refine Set.iUnion_subset fun i => ?_
    exact fun z hz => mem_cover (P.mem_pieces i) hz

/-- The edge list has no repeated entry: distinct indices name distinct initial vertices. -/
theorem pieces_nodup (P : PrePolygon m) : P.pieces.Nodup := by
  rw [pieces]
  refine List.Nodup.map_on (fun j hj k hk heq => ?_) List.nodup_range
  exact ClosedPolygon.natCast_inj (List.mem_range.1 hj) (List.mem_range.1 hk)
    (P.vertex_inj (congrArg Prod.fst heq))

/-! ## The curve statements, and separation

All three are properties of the carrier as a set, and normalization keeps the carrier, so all three
come across from the `ClosedPolygon` versions with nothing to check. -/

/-- The carrier is compact: it is what a finite list of segments occupies. -/
theorem isCompact_carrier (P : PrePolygon m) : IsCompact P.carrier := by
  rw [← P.cover_pieces]; exact isCompact_cover _

theorem isClosed_carrier (P : PrePolygon m) : IsClosed P.carrier := P.isCompact_carrier.isClosed

/-- **The carrier is a Jordan curve**, redundant vertices and all. Deleting them does not move the
curve, and the normalized polygon's carrier is a Jordan curve. -/
theorem isJordanCurve_carrier (P : PrePolygon m) : IsJordanCurve P.carrier := by
  obtain ⟨m', P', hP'⟩ := exists_closedPolygon_of_prePolygon m P
  rw [← hP']
  exact P'.isJordanCurve_carrier

/-- **The carrier is polygonal.** -/
theorem isPolygonal_carrier (P : PrePolygon m) : IsPolygonal P.carrier := by
  obtain ⟨m', P', hP'⟩ := exists_closedPolygon_of_prePolygon m P
  rw [← hP']
  exact P'.isPolygonal_carrier

/-- **The polygonal Jordan curve theorem** (Theorem 2.3) for a polygon presented with redundant
vertices, in the form Definition 2.4 asks for.

This is the statement the crosscut machinery of `Schoenflies/CrosscutCells.lean` onwards consumes,
and `IsSeparating` speaks only of the carrier, so normalizing and quoting
`ClosedPolygon.isSeparating_carrier` is the whole proof. -/
theorem isSeparating_carrier (P : PrePolygon m) : IsSeparating P.carrier := by
  obtain ⟨m', P', hP'⟩ := exists_closedPolygon_of_prePolygon m P
  rw [← hP']
  exact P'.isSeparating_carrier

/-- Exactly two regions: the component of any point off the polygon is one of the two named
ones. -/
theorem connectedComponentIn_eq_inside_or_outside (P : PrePolygon m) {x : Plane}
    (hx : x ∉ P.carrier) :
    connectedComponentIn P.carrierᶜ x = inside P.carrier ∨
      connectedComponentIn P.carrierᶜ x = outside P.carrier := by
  have h : x ∈ inside P.carrier ∪ outside P.carrier := by rw [inside_union_outside]; exact hx
  rcases h with h | h
  · exact Or.inl (P.isSeparating_carrier.connectedComponentIn_eq_inside h)
  · exact Or.inr (P.isSeparating_carrier.connectedComponentIn_eq_outside h)

/-! ## The crossing parity

The list-level statements of `Schoenflies/Parity.lean`, read off a `PrePolygon`. -/

/-- A ray direction level for no edge of the polygon; the blueprint's "rotate the coordinate system
so that no edge is horizontal", with nothing rotated. -/
theorem exists_direction_pieces (P : PrePolygon m) :
    ∃ u : Plane, Plane.IsDirection u ∧ ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2 :=
  exists_direction_hgt_ne P.pieces P.pieces_nondeg

/-- **Crossing parity** (Lemma 2.2): `π_C` is constant on the component of the complement of the
carrier containing a given point. -/
theorem parity_eq_of_mem_connectedComponentIn_carrier (P : PrePolygon m) {u : Plane}
    (hu : Plane.IsDirection u) (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) {x y : Plane}
    (hx : x ∉ P.carrier) (hy : y ∈ connectedComponentIn P.carrierᶜ x) :
    parity u P.pieces y = parity u P.pieces x := by
  rw [← P.cover_pieces] at hx hy
  exact parity_eq_of_mem_connectedComponentIn hu hL P.isClosedChain_pieces hx hy

/-- An interior point of one edge lies on no other edge: `edges_meet` puts any other edge's meeting
point at an end of this one, and an interior point is neither end. -/
theorem notMem_edge_of_mem_openSegment {P : PrePolygon m} {i j : ZMod (m + 3)} (hij : j ≠ i)
    {p : Plane} (hp : p ∈ openSegment ℝ (P.vertex i) (P.vertex (i + 1))) : p ∉ P.edge j := by
  intro hpj
  have hmem := P.edges_meet i j (Ne.symm hij)
    (Set.mem_inter (openSegment_subset_segment ℝ _ _ hp) hpj)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with rfl | rfl
  · exact vertex_ne_succ i (left_mem_openSegment_iff.1 hp)
  · exact vertex_ne_succ i (right_mem_openSegment_iff.1 hp)

/-- **Opposite sides of an edge** (Lemma 2.2, second half). Just before and just after an interior
point of an edge, in the ray direction, the base point is off the carrier and the crossing parity
differs by one.

The edge being crossed is split out of the list by `List.append_of_mem`; that the two remaining
fragments miss the crossing point is `edges_meet`, through
`PrePolygon.notMem_edge_of_mem_openSegment`. -/
theorem parity_flip_carrier (P : PrePolygon m) {u : Plane} (hu : Plane.IsDirection u)
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
  -- `exists_of_mem_cover` is the destructor matching `Schoenflies.mem_cover`; it lives, by
  -- accident, inside the `ClosedPolygon` namespace in `Schoenflies/PolygonBridge.lean`.
  have h1 : p ∉ cover L₁ := by
    intro hmem
    obtain ⟨R, hR, hpR⟩ := ClosedPolygon.exists_of_mem_cover hmem
    exact hmiss R (List.mem_append_left _ hR) hpR
  have h2 : p ∉ cover L₂ := by
    intro hmem
    obtain ⟨R, hR, hpR⟩ := ClosedPolygon.exists_of_mem_cover hmem
    exact hmiss R (List.mem_append_right _ hR) hpR
  have hL' : ∀ R ∈ L₁ ++ (P.vertex i, P.vertex (i + 1)) :: L₂, hgt u R.1 ≠ hgt u R.2 := by
    rw [← hsplit]; exact hL
  obtain ⟨δ, hδ, hmain⟩ := parity_flip hu hL' hp h1 h2
  refine ⟨δ, hδ, fun t ht htδ => ?_⟩
  obtain ⟨ha, hb, hc⟩ := hmain t ht htδ
  rw [← hsplit] at ha hb hc
  rw [P.cover_pieces] at ha hb
  exact ⟨ha, hb, hc⟩

/-- Two points off the curve at which the parity differs: just before and just after the midpoint
of the first edge. This is what turns the separation theorem into the two parity *values*. -/
theorem exists_parity_ne (P : PrePolygon m) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) :
    ∃ a b : Plane, a ∉ P.carrier ∧ b ∉ P.carrier ∧
      parity u P.pieces a ≠ parity u P.pieces b := by
  have hpmem : (1 / 2 : ℝ) • P.vertex 0 + (1 / 2 : ℝ) • P.vertex 1
      ∈ openSegment ℝ (P.vertex 0) (P.vertex (0 + 1)) := by
    rw [zero_add]
    exact ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  obtain ⟨δ, hδ, hmain⟩ := P.parity_flip_carrier hu hL 0 hpmem
  obtain ⟨h1, h2, h3⟩ := hmain (δ / 2) (by linarith) (by linarith)
  refine ⟨_, _, h1, h2, fun hh => ?_⟩
  rw [h3] at hh
  exact ne_add_one_zmod_two _ hh.symm

/-- **`π_C = 0` on the unbounded region** (Theorem 2.3), for a polygon presented with redundant
vertices. -/
theorem parity_eq_zero_of_mem_outside (P : PrePolygon m) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) {x : Plane} (hx : x ∈ outside P.carrier) :
    parity u P.pieces x = 0 := by
  have hcov := P.cover_pieces
  refine parity_eq_zero_of_mem_outside_cover hu hL P.isClosedChain_pieces ?_ ?_
  · rw [hcov]; exact P.isSeparating_carrier
  · rw [hcov]; exact hx

/-- **`π_C = 1` on the bounded region** (Theorem 2.3), for a polygon presented with redundant
vertices. -/
theorem parity_eq_one_of_mem_inside (P : PrePolygon m) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) {x : Plane} (hx : x ∈ inside P.carrier) :
    parity u P.pieces x = 1 := by
  obtain ⟨a, b, ha, hb, hab⟩ := P.exists_parity_ne hu hL
  have hcov := P.cover_pieces
  refine parity_eq_one_of_mem_inside_cover (a := a) (b := b) hu hL P.isClosedChain_pieces
    ?_ ?_ ?_ hab ?_
  · rw [hcov]; exact P.isSeparating_carrier
  · rw [hcov]; exact ha
  · rw [hcov]; exact hb
  · rw [hcov]; exact hx

/-- **The crossing parity decides the region** (Theorem 2.3): off the curve, `π_C = 1` says
"inside". -/
theorem parity_eq_one_iff (P : PrePolygon m) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) {x : Plane} (hx : x ∉ P.carrier) :
    parity u P.pieces x = 1 ↔ x ∈ inside P.carrier := by
  have hmem : x ∈ inside P.carrier ∪ outside P.carrier := by
    rw [inside_union_outside]; exact hx
  refine ⟨fun h1 => ?_, P.parity_eq_one_of_mem_inside hu hL⟩
  rcases hmem with h | h
  · exact h
  · rw [P.parity_eq_zero_of_mem_outside hu hL h] at h1
    exact absurd h1 (by decide)

/-- **The crossing parity decides the region**, the other way round. -/
theorem parity_eq_zero_iff (P : PrePolygon m) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) {x : Plane} (hx : x ∉ P.carrier) :
    parity u P.pieces x = 0 ↔ x ∈ outside P.carrier := by
  have hmem : x ∈ inside P.carrier ∪ outside P.carrier := by
    rw [inside_union_outside]; exact hx
  refine ⟨fun h0 => ?_, P.parity_eq_zero_of_mem_outside hu hL⟩
  rcases hmem with h | h
  · rw [P.parity_eq_one_of_mem_inside hu hL h] at h0
    exact absurd h0 (by decide)
  · exact h

end PrePolygon

/-! ## The `ClosedPolygon` parity values are instances

A machine check of the claim made in this module's docstring. `Schoenflies/PolygonalJordan.lean`
proves `ClosedPolygon.parity_eq_one_of_mem_inside` from a `StripData` — the collar of Lemma 1.8,
which is where `corner` is used. The collar is needed for Theorem 2.3 itself, but *not* a second
time for the parity value: given separation, the two values follow from the general lemmas above.
The two `example`s below are the same statements, re-proved that way. -/

example {m : ℕ} (P : ClosedPolygon m) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) {x : Plane} (hx : x ∈ outside P.carrier) :
    parity u P.pieces x = 0 := by
  have hcov := P.cover_pieces
  refine parity_eq_zero_of_mem_outside_cover hu hL P.isClosedChain_pieces ?_ ?_
  · rw [hcov]; exact P.isSeparating_carrier
  · rw [hcov]; exact hx

example {m : ℕ} (P : ClosedPolygon m) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) {x : Plane} (hx : x ∈ inside P.carrier) :
    parity u P.pieces x = 1 := by
  -- the two points of opposite parity come from an edge, not from a track of the collar
  obtain ⟨a, b, ha, hb, hab⟩ := P.toPre.exists_parity_ne hu hL
  have hcov := P.cover_pieces
  refine parity_eq_one_of_mem_inside_cover (a := a) (b := b) hu hL P.isClosedChain_pieces
    ?_ ?_ ?_ hab ?_
  · rw [hcov]; exact P.isSeparating_carrier
  · rw [hcov]; exact ha
  · rw [hcov]; exact hb
  · rw [hcov]; exact hx

end Schoenflies

end BundlePart417

