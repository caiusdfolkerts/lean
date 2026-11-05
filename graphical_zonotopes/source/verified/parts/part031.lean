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

public import verified.parts.part030
import all verified.parts.part030

@[expose] public section

set_option debug.skipKernelTC false
set_option linter.all false
set_option Elab.async false
set_option internal.cmdlineSnapshots true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

section BundlePart403
/- Source: dev/planar_search/schoenflies_port/Schoenflies/Direction.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/


/-!
# Directions, and the two arcs cut out by a pair of rays

This module supplies the *direction facts* that the two-sided strip lemma runs on. Everything
here is stated through the sign of the orientation form `Plane.det`: no angle is named, no
inverse trigonometric function appears, and no case distinction on the sense of a turn is
ever made.

A *direction* is a unit vector (`Plane.IsDirection`). What actually matters about a direction
is its ray — the set of its positive multiples — because every predicate below is invariant
under positive scaling (`Plane.smul_mem_arcCCW`). So the arcs are defined on all nonzero
vectors and the unit-vector normalisation `Plane.dir` is only a convenience.

## The two arcs

Two directions `u` and `w` that are neither equal nor opposite are exactly two directions with
`det u w ≠ 0` (`Plane.det_ne_zero_iff`). They cut the circle of directions into two open arcs.
The arc traversed counterclockwise from `u` to `w` is `Plane.arcCCW u w`, defined by Sedgewick's
`ccw` predicate on the triple `(u, d, w)`: at least two of the three consecutive orientation
forms are positive. This definition is manifestly invariant under rotating the triple, and — this
is the point — it is correct for *both* arcs at once, the short one and the long one, with no
sign hypothesis in the definition itself.

`Plane.mem_ray_or_mem_arcCCW` and `Plane.arcCCW_disjoint` say that the two arcs and the two
bounding rays partition the nonzero vectors.

## The transfer fact

`Plane.same_arc_of_det_neg_of_det_pos` is Appendix C's transfer fact: *a direction with negative
`det` against the first ray lies on the same arc as a direction with positive `det` against the
second*. Note that no nearness hypothesis is needed for it — see the module note below.

## Blueprint

* `Plane.IsDirection`, `Plane.dir`, `Plane.arcCCW`, `Plane.det_ne_zero_iff`,
  `Plane.mem_ray_or_mem_arcCCW`, `Plane.arcCCW_disjoint` — Appendix C, item 1, "two distinct,
  non-opposite unit vectors bound two open arcs of directions".
* `Plane.same_arc_of_det_neg_of_det_pos` — Appendix C, item 1, the transfer fact.
* `Plane.exists_isDirection_det_ne_zero`, `Plane.exists_isDirection_det_and_inner_ne_zero` —
  Appendix C, item 1, "the existence of a unit vector avoiding any prescribed finite set of
  directions".
* `Plane.germs_split`, `Plane.exists_germ_threshold` — the vertex matching inside Lemma 1.8
  (Two-sided polygonal strips): the two left half-strip germs land on one arc and the two right
  ones on the other.

## A note on "near"

Appendix C states the transfer fact for directions *near* the two bounding rays. The nearness is
not needed: `Plane.mem_arcCCW_rev_iff` shows that the arc counterclockwise from `w` to `u` is cut
out by a *disjunction* of two sign conditions, so a single sign suffices to land on it. The
mirror statement — a direction with positive `det` against `u` and one with negative `det`
against `w` both lie on `arcCCW u w` — is *not* available from one sign each, because that arc is
cut out by the *conjunction* (`Plane.mem_arcCCW_iff`). Lemma 1.8 needs the mirror statement too,
for the two right germs, and there the missing second sign is exactly what "`s/t` small" buys:
`Plane.exists_germ_threshold` supplies it, with an explicit threshold.
-/

open Set

namespace Schoenflies

namespace Plane

variable {u w d d₁ d₂ r₁ r₂ v : Plane} {r t s : ℝ}

/-! ### Directions -/

/-- A *direction* is a unit vector. Only the ray a direction spans ever matters below, but
normalising to unit length gives a canonical representative of that ray. -/
def IsDirection (u : Plane) : Prop := ‖u‖ = 1

theorem IsDirection.ne_zero (hu : IsDirection u) : u ≠ 0 := by
  intro h
  rw [IsDirection, h, norm_zero] at hu
  exact zero_ne_one hu

theorem IsDirection.norm (hu : IsDirection u) : ‖u‖ = 1 := hu

/-- The unit vector along a nonzero vector. -/
noncomputable def dir (u : Plane) : Plane := ‖u‖⁻¹ • u

theorem isDirection_dir (hu : u ≠ 0) : IsDirection (dir u) := by
  have hpos : 0 < ‖u‖ := norm_pos_iff.2 hu
  rw [IsDirection, dir, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos,
    inv_mul_cancel₀ hpos.ne']

theorem dir_ne_zero (hu : u ≠ 0) : dir u ≠ 0 := (isDirection_dir hu).ne_zero

/-- `dir u` is a positive multiple of `u`, which is why every sign-of-`det` predicate is blind
to the difference. -/
theorem dir_eq_smul (hu : u ≠ 0) : ∃ c : ℝ, 0 < c ∧ dir u = c • u :=
  ⟨‖u‖⁻¹, inv_pos.2 (norm_pos_iff.2 hu), rfl⟩

/-! ### Nonvanishing of `det` -/

theorem ne_zero_left_of_det_ne_zero (h : det u w ≠ 0) : u ≠ 0 := by
  rintro rfl
  exact h (by simp [det])

theorem ne_zero_right_of_det_ne_zero (h : det u w ≠ 0) : w ≠ 0 := by
  rintro rfl
  exact h (by simp [det])

/-- Two directions are neither equal nor opposite exactly when the orientation form does not
kill them. This is the angle-free reading of "two distinct, non-opposite unit vectors". -/
theorem det_ne_zero_iff (hu : IsDirection u) (hw : IsDirection w) :
    det u w ≠ 0 ↔ w ≠ u ∧ w ≠ -u := by
  constructor
  · intro h
    refine ⟨fun he => h (by rw [he]; simp), fun he => h ?_⟩
    rw [he, show (-u : Plane) = (-1 : ℝ) • u by module, det_smul_right, det_self, mul_zero]
  · rintro ⟨hne, hopp⟩ h
    -- `det u w = 0` makes `w` a multiple of `u`; unit length pins the factor to `±1`.
    obtain ⟨c, rfl⟩ := (det_eq_zero_iff_smul u w hu.ne_zero).1 h
    have hc : |c| = 1 := by
      have := hw.norm
      rwa [norm_smul, Real.norm_eq_abs, hu.norm, mul_one] at this
    rcases abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.1 hc with rfl | rfl
    · exact hne (one_smul ℝ u)
    · exact hopp (by module)

/-! ### The two arcs -/

/-- The open arc of directions traversed counterclockwise from `u` to `w`.

A nonzero `d` lies on it when at least two of the three consecutive orientation forms of the
triple `(u, d, w)` are positive. The definition is a cyclic condition, so it is correct for the
short arc and for the long arc alike, with no hypothesis on the sign of `det u w`. -/
def arcCCW (u w : Plane) : Set Plane :=
  {d | (0 < det u d ∧ 0 < det d w) ∨ (0 < det d w ∧ 0 < det w u) ∨ (0 < det w u ∧ 0 < det u d)}

/-- Fix the orientation by `0 < det u w`, so that `w` is counterclockwise of `u` by less than a
half turn. Then the arc counterclockwise from `u` to `w` is the *short* one, and membership is
the conjunction of two sign conditions. -/
theorem mem_arcCCW_iff (h : 0 < det u w) : d ∈ arcCCW u w ↔ 0 < det u d ∧ 0 < det d w := by
  have hwu : det w u < 0 := by rw [det_comm w u]; linarith
  refine ⟨?_, Or.inl⟩
  rintro (h1 | ⟨_, h2⟩ | ⟨h2, _⟩)
  · exact h1
  · linarith
  · linarith

/-- With the same orientation `0 < det u w`, the arc counterclockwise from `w` back to `u` is the
*long* one — more than a half turn — and membership is a **disjunction**. This asymmetry is the
whole content of the transfer fact: one sign suffices here, two are needed on the short arc. -/
theorem mem_arcCCW_rev_iff (h : 0 < det u w) :
    d ∈ arcCCW w u ↔ det u d < 0 ∨ det d w < 0 := by
  have e1 : det w d = -det d w := det_comm w d
  have e2 : det d u = -det u d := det_comm d u
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h2, _⟩ | ⟨_, h1⟩)
    · exact Or.inl (by rw [e2] at h2; linarith)
    · exact Or.inl (by rw [e2] at h2; linarith)
    · exact Or.inr (by rw [e1] at h1; linarith)
  · rintro (h1 | h2)
    · exact Or.inr (Or.inl ⟨by rw [e2]; linarith, h⟩)
    · exact Or.inr (Or.inr ⟨h, by rw [e1]; linarith⟩)

/-- The two arcs are disjoint. -/
theorem arcCCW_disjoint (h : 0 < det u w) : Disjoint (arcCCW u w) (arcCCW w u) := by
  rw [Set.disjoint_left]
  intro d hd hd'
  rw [mem_arcCCW_iff h] at hd
  rw [mem_arcCCW_rev_iff h] at hd'
  rcases hd' with h' | h' <;> linarith [hd.1, hd.2]

/-- Every sign-of-`det` condition is blind to positive rescaling, so the arcs really are sets of
*rays*, not of vectors. -/
theorem smul_mem_arcCCW (hr : 0 < r) : r • d ∈ arcCCW u w ↔ d ∈ arcCCW u w := by
  have key : ∀ x : ℝ, 0 < r * x ↔ 0 < x := by
    intro x
    constructor <;> intro hx <;> nlinarith
  simp only [arcCCW, mem_setOf_eq, det_smul_left, det_smul_right, key]

theorem dir_mem_arcCCW_iff (hd : d ≠ 0) : dir d ∈ arcCCW u w ↔ d ∈ arcCCW u w := by
  obtain ⟨c, hc, hcd⟩ := dir_eq_smul hd
  rw [hcd, smul_mem_arcCCW hc]

/-- The two rays and the two arcs exhaust the nonzero vectors. Together with
`Plane.arcCCW_disjoint` this is the statement that two distinct, non-opposite directions bound
two arcs. -/
theorem mem_ray_or_mem_arcCCW (h : 0 < det u w) (hd : d ≠ 0) :
    (∃ c : ℝ, 0 < c ∧ d = c • u) ∨ (∃ c : ℝ, 0 < c ∧ d = c • w) ∨
      d ∈ arcCCW u w ∨ d ∈ arcCCW w u := by
  have hu : u ≠ 0 := ne_zero_left_of_det_ne_zero h.ne'
  have hw : w ≠ 0 := ne_zero_right_of_det_ne_zero h.ne'
  by_cases hneg : det u d < 0 ∨ det d w < 0
  · exact Or.inr (Or.inr (Or.inr ((mem_arcCCW_rev_iff h).2 hneg)))
  push Not at hneg
  obtain ⟨h1, h2⟩ := hneg
  rcases lt_or_eq_of_le h1 with h1' | h1'
  · rcases lt_or_eq_of_le h2 with h2' | h2'
    · exact Or.inr (Or.inr (Or.inl ((mem_arcCCW_iff h).2 ⟨h1', h2'⟩)))
    · -- `det d w = 0`: `d` lies along the line of `w`, and `det u d ≥ 0` fixes the sign.
      obtain ⟨c, rfl⟩ := (det_eq_zero_iff_smul w d hw).1 (by rw [det_comm w d, ← h2']; ring)
      refine Or.inr (Or.inl ⟨c, ?_, rfl⟩)
      rw [det_smul_right] at h1'
      nlinarith
  · -- `det u d = 0`: `d` lies along the line of `u`, and `det d w ≥ 0` fixes the sign.
    obtain ⟨c, rfl⟩ := (det_eq_zero_iff_smul u d hu).1 h1'.symm
    refine Or.inl ⟨c, ?_, rfl⟩
    rw [det_smul_left] at h2
    rcases lt_or_eq_of_le h2 with h2' | h2'
    · nlinarith
    · exfalso
      have : c = 0 := by
        rcases mul_eq_zero.1 h2'.symm with hc | hd'
        · exact hc
        · exact absurd hd' h.ne'
      exact hd (by rw [this, zero_smul])

/-! ### The transfer fact -/

/-- A direction with **negative** `det` against `u` lies on the arc counterclockwise from `w`
to `u`. No nearness hypothesis is needed. -/
theorem mem_arcCCW_rev_of_det_neg (h : 0 < det u w) (hd : det u d < 0) : d ∈ arcCCW w u :=
  (mem_arcCCW_rev_iff h).2 (Or.inl hd)

/-- A direction with **positive** `det` against `w` lies on the arc counterclockwise from `w`
to `u`. No nearness hypothesis is needed. -/
theorem mem_arcCCW_rev_of_det_pos (h : 0 < det u w) (hd : 0 < det w d) : d ∈ arcCCW w u :=
  (mem_arcCCW_rev_iff h).2 (Or.inr (by rw [det_comm d w]; linarith))

/-- **Appendix C, transfer.** A direction with negative `det` against the first ray lies on the
same arc as a direction with positive `det` against the second: both lie on the arc traversed
counterclockwise from the second ray to the first. -/
theorem same_arc_of_det_neg_of_det_pos (h : 0 < det u w) (h₁ : det u d₁ < 0) (h₂ : 0 < det w d₂) :
    d₁ ∈ arcCCW w u ∧ d₂ ∈ arcCCW w u :=
  ⟨mem_arcCCW_rev_of_det_neg h h₁, mem_arcCCW_rev_of_det_pos h h₂⟩

/-- The mirror form, for the other pair of germs: a direction with positive `det` against `u`
**and** negative `det` against `w` lies on the arc counterclockwise from `u` to `w`. Here both
signs are genuinely needed; see the module note. -/
theorem mem_arcCCW_of_det_pos_of_det_neg (h : 0 < det u w) (h₁ : 0 < det u d) (h₂ : det w d < 0) :
    d ∈ arcCCW u w :=
  (mem_arcCCW_iff h).2 ⟨h₁, by rw [det_comm d w]; linarith⟩

/-! ### Half-strip germs

Fix a vertex with incoming unit tangent `u` and outgoing unit tangent `w`, and let `r₁ = -u`,
`r₂ = w` be the two rays leaving the vertex, so that `perp r₁ = -u^⊥` and `perp r₂ = w^⊥`.
Then the four half-strip germs of Lemma 1.8 are, in the blueprint's own notation,

* incoming left, `-t u + s u^⊥ = t • r₁ - s • perp r₁`;
* outgoing left, `t w + s w^⊥ = t • r₂ + s • perp r₂`;
* incoming right, `-t u - s u^⊥ = t • r₁ + s • perp r₁`;
* outgoing right, `t w - s w^⊥ = t • r₂ - s • perp r₂`,

each with `t, s > 0`. The four computations below place them on the two arcs. -/

/-- The orientation form of a germ against its own tangent sees only the transverse
coefficient: this is the blueprint's `det(r₁, d) = -s` and `det(r₂, d) = s`. -/
theorem det_germ_self (r : Plane) (t s : ℝ) :
    det r (t • r + s • perp r) = s * ‖r‖ ^ 2 := by
  rw [det_add_right, det_smul_right, det_smul_right, det_self, det_perp_self]
  ring

theorem det_germ_self' (r : Plane) (t s : ℝ) :
    det (t • r + s • perp r) r = -(s * ‖r‖ ^ 2) := by
  rw [det_comm, det_germ_self]

/-- The orientation form of a germ at `r₁` against the *other* ray. The inner-product term is
what makes the transverse coefficient have to be small relative to the longitudinal one. -/
theorem det_germ (r₁ r₂ : Plane) (t s : ℝ) :
    det (t • r₁ + s • perp r₁) r₂ = t * det r₁ r₂ - s * inner ℝ r₁ r₂ := by
  rw [det_add_left, det_smul_left, det_smul_left, det_perp_left]
  ring

/-- The orientation form of a germ at `r₂` against the other ray. -/
theorem det_germ' (r₁ r₂ : Plane) (t s : ℝ) :
    det r₁ (t • r₂ + s • perp r₂) = t * det r₁ r₂ + s * inner ℝ r₁ r₂ := by
  rw [det_add_right, det_smul_right, det_smul_right, det_perp_right]

private theorem sq_norm_pos_left (h : 0 < det r₁ r₂) : 0 < ‖r₁‖ ^ 2 :=
  pow_pos (norm_pos_iff.2 (ne_zero_left_of_det_ne_zero h.ne')) 2

private theorem sq_norm_pos_right (h : 0 < det r₁ r₂) : 0 < ‖r₂‖ ^ 2 :=
  pow_pos (norm_pos_iff.2 (ne_zero_right_of_det_ne_zero h.ne')) 2

/-- The **incoming left** germ lands on the arc counterclockwise from `r₂` to `r₁`, for *every*
longitudinal coefficient `t`: this is the half of the vertex matching that costs nothing,
because that arc is cut out by a disjunction. -/
theorem germ_mem_arcCCW_rev_of_left (h : 0 < det r₁ r₂) (hs : 0 < s) (t : ℝ) :
    t • r₁ - s • perp r₁ ∈ arcCCW r₂ r₁ := by
  refine mem_arcCCW_rev_of_det_neg h ?_
  have e : t • r₁ - s • perp r₁ = t • r₁ + (-s) • perp r₁ := by module
  rw [e, det_germ_self]
  nlinarith [sq_norm_pos_left h]

/-- The **outgoing left** germ lands on the same arc, again for every `t`. -/
theorem germ_mem_arcCCW_rev_of_right (h : 0 < det r₁ r₂) (hs : 0 < s) (t : ℝ) :
    t • r₂ + s • perp r₂ ∈ arcCCW r₂ r₁ := by
  refine mem_arcCCW_rev_of_det_pos h ?_
  rw [det_germ_self]
  exact mul_pos hs (sq_norm_pos_right h)

/-- The **incoming right** germ lands on the arc counterclockwise from `r₁` to `r₂` provided the
transverse coefficient is small enough against the longitudinal one. The inequality
`s ⟪r₁, r₂⟫ < t det(r₁, r₂)` is exactly "`s/t` small", written without a division. -/
theorem germ_mem_arcCCW_of_left (h : 0 < det r₁ r₂) (hs : 0 < s)
    (hsmall : s * inner ℝ r₁ r₂ < t * det r₁ r₂) :
    t • r₁ + s • perp r₁ ∈ arcCCW r₁ r₂ := by
  refine (mem_arcCCW_iff h).2 ⟨?_, ?_⟩
  · rw [det_germ_self]
    exact mul_pos hs (sq_norm_pos_left h)
  · rw [det_germ]
    linarith

/-- The **outgoing right** germ lands on the same arc, under the same smallness condition. -/
theorem germ_mem_arcCCW_of_right (h : 0 < det r₁ r₂) (hs : 0 < s)
    (hsmall : s * inner ℝ r₁ r₂ < t * det r₁ r₂) :
    t • r₂ - s • perp r₂ ∈ arcCCW r₁ r₂ := by
  have e : t • r₂ - s • perp r₂ = t • r₂ + (-s) • perp r₂ := by module
  refine (mem_arcCCW_iff h).2 ⟨?_, ?_⟩
  · rw [e, det_germ']
    linarith
  · rw [e, det_germ_self']
    nlinarith [sq_norm_pos_right h]

/-- **The vertex matching of Lemma 1.8.** With the strips narrow enough — `s ⟪r₁, r₂⟫` under
`t det(r₁, r₂)` — the two left germs lie on one arc and the two right germs on the other. No
angle is named and no case distinction on the sense of the turn arises: the two cases of the
turn are the two orders in which `r₁` and `r₂` may be presented, and `det_comm` exchanges
them. -/
theorem germs_split (h : 0 < det r₁ r₂) (hs : 0 < s)
    (hsmall : s * inner ℝ r₁ r₂ < t * det r₁ r₂) :
    (t • r₁ - s • perp r₁ ∈ arcCCW r₂ r₁ ∧ t • r₂ + s • perp r₂ ∈ arcCCW r₂ r₁) ∧
      (t • r₁ + s • perp r₁ ∈ arcCCW r₁ r₂ ∧ t • r₂ - s • perp r₂ ∈ arcCCW r₁ r₂) :=
  ⟨⟨germ_mem_arcCCW_rev_of_left h hs t, germ_mem_arcCCW_rev_of_right h hs t⟩,
    ⟨germ_mem_arcCCW_of_left h hs hsmall, germ_mem_arcCCW_of_right h hs hsmall⟩⟩

/-- The quantitative form: there is a slope threshold below which the vertex matching holds.
This is what "make the strips narrow enough that this side matching holds in every vertex disk"
means in Lemma 1.8, and it is the one place where a size condition, rather than a bare sign of
`det`, is unavoidable. -/
theorem exists_germ_threshold (h : 0 < det r₁ r₂) :
    ∃ ε > 0, ∀ t s : ℝ, 0 < t → 0 < s → s < ε * t →
      (t • r₁ - s • perp r₁ ∈ arcCCW r₂ r₁ ∧ t • r₂ + s • perp r₂ ∈ arcCCW r₂ r₁) ∧
        (t • r₁ + s • perp r₁ ∈ arcCCW r₁ r₂ ∧ t • r₂ - s • perp r₂ ∈ arcCCW r₁ r₂) := by
  set A : ℝ := |inner ℝ r₁ r₂| with hA
  have hA0 : (0 : ℝ) < 1 + A := by positivity
  refine ⟨det r₁ r₂ / (1 + A), by positivity, fun t s _ hs hlt => germs_split h hs ?_⟩
  -- Clear the denominator in `s < (det r₁ r₂ / (1 + A)) * t`.
  have hmul := mul_lt_mul_of_pos_right hlt hA0
  have hclear : det r₁ r₂ / (1 + A) * t * (1 + A) = det r₁ r₂ * t := by
    field_simp
  rw [hclear] at hmul
  have hle : inner ℝ r₁ r₂ ≤ A := le_abs_self _
  nlinarith

/-! ### A direction avoiding finitely many others

The argument is a counting one, with no measure and no trigonometry: the one-parameter family
`a ↦ (1, a)` meets the line of any fixed nonzero vector at most once, so finitely many vectors
rule out only finitely many parameters, and `ℝ` has more than finitely many. -/

/-- The family used to dodge finitely many directions. -/
private theorem mk_one_ne_zero (a : ℝ) : mk 1 a ≠ 0 := by
  intro h
  have h0 : mk 1 a 0 = (0 : Plane) 0 := by rw [h]
  simp at h0

private theorem det_mk_one (a : ℝ) (v : Plane) : det (mk 1 a) v = v 1 - a * v 0 := by
  simp [det]

/-- **Appendix C.** There is a unit vector not parallel to any of a prescribed finite set of
nonzero vectors. This is what lets one rotate coordinates so that no edge of a finite polygonal
figure is horizontal. -/
theorem exists_isDirection_det_ne_zero {S : Set Plane} (hS : S.Finite) :
    ∃ u : Plane, IsDirection u ∧ ∀ v ∈ S, v ≠ 0 → det u v ≠ 0 := by
  -- The parameters ruled out by `S` are the slopes of its members, hence at most as many as `S`.
  have hbad : {a : ℝ | ∃ v ∈ S, v ≠ 0 ∧ det (mk 1 a) v = 0}.Finite := by
    refine Set.Finite.subset (hS.image fun v => v 1 / v 0) ?_
    rintro a ⟨v, hv, hv0, hdet⟩
    rw [det_mk_one] at hdet
    have h0 : v 0 ≠ 0 := by
      intro h
      refine hv0 ?_
      have h1 : v 1 = 0 := by rw [h] at hdet; linarith
      ext i
      fin_cases i <;> simp [h, h1]
    exact ⟨v, hv, by field_simp; linarith⟩
  obtain ⟨a, ha⟩ := hbad.infinite_compl.nonempty
  refine ⟨dir (mk 1 a), isDirection_dir (mk_one_ne_zero a),
    fun v hv hv0 hdet => ha ⟨v, hv, hv0, ?_⟩⟩
  -- `dir` only rescales, so it cannot create a vanishing orientation form.
  obtain ⟨c, hc, hcd⟩ := dir_eq_smul (mk_one_ne_zero a)
  rw [hcd, det_smul_left] at hdet
  rcases mul_eq_zero.1 hdet with h | h
  · exact absurd h hc.ne'
  · exact h

/-- The same, dodging the perpendicular directions too: a unit vector `u` for which no member of
a prescribed finite set of nonzero vectors is either parallel or perpendicular to `u`. In the
rotated coordinates this says that no edge is horizontal and none is vertical. -/
theorem exists_isDirection_det_and_inner_ne_zero {S : Set Plane} (hS : S.Finite) :
    ∃ u : Plane, IsDirection u ∧ ∀ v ∈ S, v ≠ 0 → det u v ≠ 0 ∧ inner ℝ u v ≠ 0 := by
  obtain ⟨u, hu, hdet⟩ := exists_isDirection_det_ne_zero (hS.union (hS.image perp))
  refine ⟨u, hu, fun v hv hv0 => ⟨hdet v (Or.inl hv) hv0, ?_⟩⟩
  -- `det u (perp v) = ⟪u, v⟫`, so dodging `perp v` is dodging the perpendicular.
  have hpv : perp v ≠ 0 := by
    intro h
    exact hv0 (by have := norm_perp v; rw [h, norm_zero] at this; exact norm_eq_zero.1 this.symm)
  have := hdet (perp v) (Or.inr ⟨v, hv, rfl⟩) hpv
  rwa [det_perp_right] at this

/-! ### The arcs are open

Not needed by Lemma 1.8, which uses only the partition, but it justifies the word "open" in
"two open arcs of directions". -/

theorem continuous_det_right (u : Plane) : Continuous fun d : Plane => det u d := by
  refine Continuous.sub (Continuous.mul continuous_const ?_) (Continuous.mul continuous_const ?_)
  · exact PiLp.continuous_apply _ _ 1
  · exact PiLp.continuous_apply _ _ 0

theorem continuous_det_left (w : Plane) : Continuous fun d : Plane => det d w := by
  refine Continuous.sub (Continuous.mul ?_ continuous_const) (Continuous.mul ?_ continuous_const)
  · exact PiLp.continuous_apply _ _ 0
  · exact PiLp.continuous_apply _ _ 1

theorem isOpen_arcCCW (u w : Plane) : IsOpen (arcCCW u w) := by
  have h1 : IsOpen {d : Plane | 0 < det u d} := isOpen_lt continuous_const (continuous_det_right u)
  have h2 : IsOpen {d : Plane | 0 < det d w} := isOpen_lt continuous_const (continuous_det_left w)
  by_cases h : 0 < det w u
  · have : arcCCW u w = {d : Plane | 0 < det u d} ∪ {d : Plane | 0 < det d w} := by
      ext d
      simp only [arcCCW, mem_setOf_eq, mem_union]
      constructor
      · rintro (⟨h1, _⟩ | ⟨h2, _⟩ | ⟨_, h1⟩) <;> tauto
      · rintro (hx | hx)
        · exact Or.inr (Or.inr ⟨h, hx⟩)
        · exact Or.inr (Or.inl ⟨hx, h⟩)
    rw [this]
    exact h1.union h2
  · have : arcCCW u w = {d : Plane | 0 < det u d} ∩ {d : Plane | 0 < det d w} := by
      ext d
      simp only [arcCCW, mem_setOf_eq, mem_inter_iff]
      constructor
      · rintro (hx | ⟨_, hx⟩ | ⟨hx, _⟩) <;> [exact hx; exact absurd hx h; exact absurd hx h]
      · exact Or.inl
    rw [this]
    exact h1.inter h2

end Plane

end Schoenflies

end BundlePart403

section BundlePart404
/- Source: dev/planar_search/schoenflies_port/Schoenflies/Strip.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/




/-!
# Two-sided polygonal strips

This module builds the *collar* of Lemma 1.8: an open neighbourhood `N` of a simple closed
polygon `P` whose complement in `N` splits into two connected open sets, the two local sides.

The blueprint's construction is "a small closed disk about every vertex, a thin rectangular
block about every edge, chosen so that consecutive blocks overlap and nonadjacent closures are
disjoint". The blocks here are

* `Plane.cone v A R` — the open sector of radius `R` about a vertex `v` cut out by an arc `A`
  of directions, and
* `Plane.strip a u t₁ t₂ s₁ s₂` — the open rectangle around a directed edge, written in the
  edge's own coordinates `t = ⟪u, x - a⟫` (along) and `s = det u (x - a)` (across).

Everything about the *side matching at a vertex* comes from `Schoenflies/Direction.lean`
through the orientation form; no angle is named. The one new direction fact needed here is the
sign-free repackaging `Plane.germs_split'`: the blueprint's `germs_split` assumes
`0 < det r₁ r₂`, but a polygon turns both ways, and it turns out that *which* named arc carries
the left germs does not depend on the sense of the turn — it is always `arcCCW r₂ r₁`. Only the
side of the smallness hypothesis moves.

## The constants

The blueprint says "the blocks may be chosen so that consecutive edge and vertex blocks overlap
in the prescribed small rectangles around the radial segments, while the closures of all
nonadjacent blocks are disjoint" without naming the constants. `Schoenflies.StripData` names
them: a cone radius `R`, a trim `lam` by which each edge block stops short of its endpoints, and
a half-width `rho`. They should be chosen in this order (this is the recipe the unproved
`exists_stripData` has to follow):

1. `R` from the vertex separations, from the distance of each vertex to the nonincident edges
   (with a factor `2` of slack, spent in `dist_core_vertex`), and from the prescribed open set;
2. `lam := R / 5`, which makes `2 * lam < R` (the cones reach past the ends of the blocks they
   must overlap) and `4 * lam < ‖edge‖` (the blocks are nonempty);
3. `rho` from the distance of each trimmed edge to the other edges, and from the *germ
   threshold* `rho * (1 + |⟪r₁, r₂⟫|) ≤ lam * |det r₁ r₂|` at every vertex — this last is the
   quantitative form of "make the strips narrow enough that this side matching holds in every
   vertex disk", and it is the only inequality in the list that is not a separation of compact
   sets.

## Blueprint

* `Plane.germs_split'` — the sign-free vertex matching inside Lemma 1.8.
* `Schoenflies.ClosedPolygon` — a simple closed polygonal curve presented by its cyclic vertex
  list.
* `Schoenflies.StripData` — the choice of constants, as a hypothesis.
* `Schoenflies.StripData.sideL`, `.sideR`, `.nbhd`, `.sideL_disjoint_sideR` — the two labelled
  sides of the collar, and that they are disjoint.

## Where the rest of Lemma 1.8 lives

This module builds the apparatus and proves the hard half: the germ matching at a corner and
the disjointness of the two labelled sides. The other two obligations are discharged next door,
and were split out only because they were built concurrently:

* `Schoenflies/StripConstants.lean` — `exists_stripData` and `exists_stripData_subset`, which
  produce the constants, the latter with the collar inside a prescribed open set.
* `Schoenflies/StripConnected.lean` — that each side is connected, and
  `nbhd \ carrier = sideL ∪ sideR`.

`Schoenflies.polygonal_collar` in `Schoenflies/Compose.lean` is the three composed into the
blueprint's Lemma 1.8 (a). `ClosedPolygon.collar` below is a *definition*, not the theorem.

What is still missing from Lemma 1.8 as a whole: the **local two-sidedness** clause (every
sufficiently small disk about a point of the curve meets the complement in exactly two
components, one in each side), and part **(b)**, the arc case.
-/

open Metric Set

namespace Schoenflies

namespace Plane

variable {u w d r₁ r₂ a x : Plane} {r t s c ρ : ℝ}

/-! ### A sign-free vertex matching

`Plane.germs_split` fixes the orientation with `0 < det r₁ r₂`. A polygon turns both ways, so
the collar needs the statement without that hypothesis. The content of the repackaging is that
the *conclusion* does not move: the two left germs always land on `arcCCW r₂ r₁` and the two
right germs on `arcCCW r₁ r₂`. What moves is which pair needs the smallness hypothesis, so the
sign-free form simply imposes it on both, with absolute values. -/

/-- **The vertex matching, sign-free.** With `r₁` the ray back along the incoming edge and `r₂`
the ray out along the outgoing edge, the two *left* half-strip germs lie on `arcCCW r₂ r₁` and
the two *right* ones on `arcCCW r₁ r₂`, whichever way the polygon turns. The hypothesis
`s * |⟪r₁, r₂⟫| < t * |det r₁ r₂|` is the blueprint's "`s/t` small", written without a division
and without a sign. -/
theorem germs_split' (h : det r₁ r₂ ≠ 0) (hs : 0 < s)
    (hsmall : s * |inner ℝ r₁ r₂| < t * |det r₁ r₂|) :
    (t • r₁ - s • perp r₁ ∈ arcCCW r₂ r₁ ∧ t • r₂ + s • perp r₂ ∈ arcCCW r₂ r₁) ∧
      (t • r₁ + s • perp r₁ ∈ arcCCW r₁ r₂ ∧ t • r₂ - s • perp r₂ ∈ arcCCW r₁ r₂) := by
  have hle : inner ℝ r₁ r₂ ≤ |inner ℝ r₁ r₂| := le_abs_self _
  have hle' : inner ℝ r₂ r₁ ≤ |inner ℝ r₁ r₂| := by
    rw [real_inner_comm]; exact hle
  rcases lt_or_gt_of_ne h with hneg | hpos
  · -- The turn is the other way: exchange the roles of the two rays in `germs_split`.
    have h' : 0 < det r₂ r₁ := by rw [det_comm r₂ r₁]; linarith
    have habs : |det r₁ r₂| = det r₂ r₁ := by rw [abs_of_neg hneg, det_comm r₁ r₂]; ring
    have hsmall' : s * inner ℝ r₂ r₁ < t * det r₂ r₁ := by
      rw [habs] at hsmall
      nlinarith
    have H := germs_split h' hs hsmall'
    exact ⟨⟨H.2.2, H.2.1⟩, ⟨H.1.2, H.1.1⟩⟩
  · have habs : |det r₁ r₂| = det r₁ r₂ := abs_of_pos hpos
    have hsmall' : s * inner ℝ r₁ r₂ < t * det r₁ r₂ := by
      rw [habs] at hsmall
      nlinarith
    exact germs_split hpos hs hsmall'

/-! ### The two arcs, without a sign hypothesis -/

/-- The two arcs bounded by a pair of rays are disjoint, whichever the sign of `det r₁ r₂`. -/
theorem arcCCW_disjoint' (h : det r₁ r₂ ≠ 0) : Disjoint (arcCCW r₁ r₂) (arcCCW r₂ r₁) := by
  rcases lt_or_gt_of_ne h with hneg | hpos
  · have h' : 0 < det r₂ r₁ := by rw [det_comm r₂ r₁]; linarith
    exact (arcCCW_disjoint h').symm
  · exact arcCCW_disjoint hpos

/-- The two rays and the two arcs exhaust the nonzero vectors, whichever the sign of
`det r₁ r₂`. -/
theorem mem_ray_or_mem_arcCCW' (h : det r₁ r₂ ≠ 0) (hd : d ≠ 0) :
    (∃ c : ℝ, 0 < c ∧ d = c • r₁) ∨ (∃ c : ℝ, 0 < c ∧ d = c • r₂) ∨
      d ∈ arcCCW r₁ r₂ ∨ d ∈ arcCCW r₂ r₁ := by
  rcases lt_or_gt_of_ne h with hneg | hpos
  · have h' : 0 < det r₂ r₁ := by rw [det_comm r₂ r₁]; linarith
    rcases mem_ray_or_mem_arcCCW h' hd with h1 | h1 | h1 | h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inl h1
    · exact Or.inr (Or.inr (Or.inr h1))
    · exact Or.inr (Or.inr (Or.inl h1))
  · exact mem_ray_or_mem_arcCCW hpos hd

/-- A nonnegative multiple of a bounding ray lies on neither arc: the arcs are *open*, and `0`
is on neither. This is what keeps the two incident edges out of the vertex sectors. -/
theorem notMem_arcCCW_smul (u w : Plane) (hc : 0 ≤ c) :
    c • u ∉ arcCCW u w ∧ c • u ∉ arcCCW w u := by
  have e1 : det u (c • u) = 0 := by rw [det_smul_right, det_self, mul_zero]
  have e2 : det (c • u) u = 0 := by rw [det_smul_left, det_self, mul_zero]
  have e3 : det (c • u) w = c * det u w := det_smul_left _ _ _
  have e4 : det w (c • u) = c * det w u := det_smul_right _ _ _
  have e5 : det w u = -det u w := det_comm w u
  constructor
  · rintro (⟨h1, _⟩ | ⟨h1, h2⟩ | ⟨_, h2⟩)
    · rw [e1] at h1; exact lt_irrefl 0 h1
    · rw [e3] at h1; rw [e5] at h2; nlinarith
    · rw [e1] at h2; exact lt_irrefl 0 h2
  · rintro (⟨_, h2⟩ | ⟨h2, _⟩ | ⟨h1, h2⟩)
    · rw [e2] at h2; exact lt_irrefl 0 h2
    · rw [e2] at h2; exact lt_irrefl 0 h2
    · rw [e4, e5] at h2; nlinarith

/-- Half-spaces through the origin are convex; `det u ·` is linear. -/
theorem isLinearMap_det_right (u : Plane) : IsLinearMap ℝ fun d : Plane => det u d :=
  ⟨fun x y => det_add_right u x y, fun c x => by rw [det_smul_right, smul_eq_mul]⟩

theorem isLinearMap_det_left (w : Plane) : IsLinearMap ℝ fun d : Plane => det d w :=
  ⟨fun x y => det_add_left x y w, fun c x => by rw [det_smul_left, smul_eq_mul]⟩

theorem convex_det_right_pos (u : Plane) : Convex ℝ {d : Plane | 0 < det u d} :=
  convex_halfSpace_gt (isLinearMap_det_right u) 0

theorem convex_det_right_neg (u : Plane) : Convex ℝ {d : Plane | det u d < 0} :=
  convex_halfSpace_lt (isLinearMap_det_right u) 0

theorem convex_det_left_pos (w : Plane) : Convex ℝ {d : Plane | 0 < det d w} :=
  convex_halfSpace_gt (isLinearMap_det_left w) 0

theorem convex_det_left_neg (w : Plane) : Convex ℝ {d : Plane | det d w < 0} :=
  convex_halfSpace_lt (isLinearMap_det_left w) 0

/-- An arc met with a ball about the origin is connected. When the arc is the short one it is an
intersection of two half-planes, hence convex; when it is the long one it is a *union* of two
half-planes, and `-(u + w)` lies in both. -/
theorem isConnected_arcCCW_ball (h : det u w ≠ 0) (hρ : 0 < ρ) :
    IsConnected (arcCCW u w ∩ ball (0 : Plane) ρ) := by
  -- A scaling factor small enough to put the witness inside the ball.
  have hne : u + w ≠ 0 := by
    intro hz
    have hw : w = -u := by linear_combination (norm := module) hz
    rw [hw, show (-u : Plane) = (-1 : ℝ) • u by module, det_smul_right, det_self,
      mul_zero] at h
    exact h rfl
  have hnpos : 0 < ‖u + w‖ := norm_pos_iff.2 hne
  obtain ⟨ε, hε, hεball⟩ : ∃ ε : ℝ, 0 < ε ∧ ε * ‖u + w‖ < ρ := by
    refine ⟨ρ / (2 * ‖u + w‖), by positivity, ?_⟩
    have : ρ / (2 * ‖u + w‖) * ‖u + w‖ = ρ / 2 := by field_simp
    rw [this]; linarith
  have hball : ∀ σ : ℝ, |σ| = ε → σ • (u + w) ∈ ball (0 : Plane) ρ := by
    intro σ hσ
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, hσ]
    exact hεball
  rcases lt_or_gt_of_ne h with hneg | hpos
  · -- The long arc: `{det w d < 0} ∪ {det d u < 0}`, glued at `-(u + w)`.
    have h' : 0 < det w u := by rw [det_comm w u]; linarith
    have harc : arcCCW u w = {d : Plane | det w d < 0} ∪ {d : Plane | det d u < 0} := by
      ext d
      rw [mem_arcCCW_rev_iff h']
      simp only [mem_union, mem_setOf_eq]
    have hd0 : (-ε) • (u + w) ∈ ball (0 : Plane) ρ :=
      hball _ (by rw [abs_of_neg (neg_neg_iff_pos.2 hε), neg_neg])
    have hA : (-ε) • (u + w) ∈ {d : Plane | det w d < 0} := by
      change det w ((-ε) • (u + w)) < 0
      rw [det_smul_right, det_add_right, det_self, add_zero]
      nlinarith
    have hB : (-ε) • (u + w) ∈ {d : Plane | det d u < 0} := by
      change det ((-ε) • (u + w)) u < 0
      rw [det_smul_left, det_add_left, det_self, zero_add]
      nlinarith
    refine ⟨⟨_, by rw [harc]; exact ⟨Or.inl hA, hd0⟩⟩, ?_⟩
    rw [harc, union_inter_distrib_right]
    exact IsPreconnected.union _ ⟨hA, hd0⟩ ⟨hB, hd0⟩
      ((convex_det_right_neg w).inter (convex_ball _ _)).isPreconnected
      ((convex_det_left_neg u).inter (convex_ball _ _)).isPreconnected
  · -- The short arc: an intersection of two half-planes, hence convex.
    have harc : arcCCW u w = {d : Plane | 0 < det u d} ∩ {d : Plane | 0 < det d w} := by
      ext d
      rw [mem_arcCCW_iff hpos]
      simp only [mem_inter_iff, mem_setOf_eq]
    have hmem : ε • (u + w) ∈ arcCCW u w ∩ ball (0 : Plane) ρ := by
      refine ⟨?_, hball _ (abs_of_pos hε)⟩
      rw [harc]
      constructor
      · change 0 < det u (ε • (u + w))
        rw [det_smul_right, det_add_right, det_self, zero_add]
        positivity
      · change 0 < det (ε • (u + w)) w
        rw [det_smul_left, det_add_left, det_self, add_zero]
        positivity
    refine ⟨⟨_, hmem⟩, ?_⟩
    rw [harc]
    exact (((convex_det_right_pos u).inter (convex_det_left_pos w)).inter
      (convex_ball _ _)).isPreconnected

/-! ### Vertex sectors

The "small closed disk about a vertex" of the blueprint is replaced by an open *sector*: the
part of a ball about the vertex lying in a prescribed arc of directions. The two sectors cut out
by the two arcs are exactly the two components of the ball minus the two incident radial
segments, which is what makes the labelling at a vertex well defined. -/

/-- The open sector of radius `ρ` about `v` spanned by the set `A` of directions. -/
def cone (v : Plane) (A : Set Plane) (ρ : ℝ) : Set Plane := {x | x - v ∈ A} ∩ ball v ρ

theorem mem_cone_iff {v : Plane} {A : Set Plane} :
    x ∈ cone v A ρ ↔ x - v ∈ A ∧ dist x v < ρ := Iff.rfl

theorem cone_subset_ball {v : Plane} {A : Set Plane} : cone v A ρ ⊆ ball v ρ := inter_subset_right

theorem isOpen_cone {v : Plane} {A : Set Plane} (hA : IsOpen A) : IsOpen (cone v A ρ) :=
  (hA.preimage (continuous_id.sub continuous_const)).inter isOpen_ball

/-- A sector is the translate of an arc met with a ball at the origin, so it inherits its
connectedness from `Plane.isConnected_arcCCW_ball`. -/
theorem cone_eq_image (v : Plane) (A : Set Plane) (ρ : ℝ) :
    cone v A ρ = (fun d => v + d) '' (A ∩ ball (0 : Plane) ρ) := by
  ext y
  constructor
  · rintro ⟨hy, hb⟩
    refine ⟨y - v, ⟨hy, ?_⟩, ?_⟩
    · rw [mem_ball, dist_zero_right, ← dist_eq_norm]
      exact hb
    · change v + (y - v) = y
      module
  · rintro ⟨d, ⟨hd, hb⟩, rfl⟩
    have he : v + d - v = d := by module
    refine ⟨by rw [mem_setOf_eq, he]; exact hd, ?_⟩
    rw [mem_ball, dist_eq_norm, he]
    rw [mem_ball, dist_zero_right] at hb
    exact hb

theorem isConnected_cone_arcCCW (v : Plane) (h : det u w ≠ 0) (hρ : 0 < ρ) :
    IsConnected (cone v (arcCCW u w) ρ) := by
  rw [cone_eq_image]
  have hc : Continuous fun d : Plane => v + d := continuous_const.add continuous_id
  exact (isConnected_arcCCW_ball h hρ).image _ hc.continuousOn

/-! ### Edge blocks

The block around a directed edge is described in the edge's own frame: `coordAlong` is the
progress along the edge and `coordAcross` the signed distance to its line. Both are affine, so
the block is an intersection of four open half-planes — open and convex at a glance. -/

/-- Progress along the directed edge that starts at `a` with unit tangent `u`. -/
noncomputable def coordAlong (a u x : Plane) : ℝ := inner ℝ u (x - a)

/-- Signed distance from `x` to the line of the directed edge that starts at `a` with unit
tangent `u`; positive on the left. -/
def coordAcross (a u x : Plane) : ℝ := det u (x - a)

/-- The orientation form is the inner product against the turned vector. -/
theorem det_eq_inner_perp (u v : Plane) : det u v = inner ℝ (perp u) v := by
  rw [inner_eq, det]
  simp [perp]
  ring

theorem abs_det_le (u v : Plane) : |det u v| ≤ ‖u‖ * ‖v‖ := by
  rw [det_eq_inner_perp]
  calc |inner ℝ (perp u) v| ≤ ‖perp u‖ * ‖v‖ := abs_real_inner_le_norm _ _
    _ = ‖u‖ * ‖v‖ := by rw [norm_perp]

@[simp] theorem coordAlong_param (hu : IsDirection u) (a : Plane) (t s : ℝ) :
    coordAlong a u (a + t • u + s • perp u) = t := by
  have h : a + t • u + s • perp u - a = t • u + s • perp u := by module
  rw [coordAlong, h, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, inner_perp_self, hu.norm]
  ring

@[simp] theorem coordAcross_param (hu : IsDirection u) (a : Plane) (t s : ℝ) :
    coordAcross a u (a + t • u + s • perp u) = s := by
  have h : a + t • u + s • perp u - a = t • u + s • perp u := by module
  rw [coordAcross, h, det_germ_self, hu.norm]
  ring

/-- The frame is complete: every point is recovered from its two coordinates. -/
theorem frame_decomp (hu : IsDirection u) (a x : Plane) :
    x = a + (coordAlong a u x) • u + (coordAcross a u x) • perp u := by
  have hnorm : u 0 ^ 2 + u 1 ^ 2 = 1 := by
    have := hu.norm
    rw [EuclideanSpace.norm_eq] at this
    have h2 : Real.sqrt (∑ i, ‖u i‖ ^ 2) ^ 2 = 1 ^ 2 := by rw [this]
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)] at h2
    simpa [Fin.sum_univ_two, sq_abs] using h2
  have hal : coordAlong a u x = u 0 * (x 0 - a 0) + u 1 * (x 1 - a 1) := by
    rw [coordAlong, inner_eq]; simp
  have hac : coordAcross a u x = u 0 * (x 1 - a 1) - u 1 * (x 0 - a 0) := by
    rw [coordAcross, det]; simp
  ext i
  fin_cases i
  · simp only [hal, hac]
    simp [perp]
    linear_combination (a 0 - x 0) * hnorm
  · simp only [hal, hac]
    simp [perp]
    linear_combination (a 1 - x 1) * hnorm

/-- Both coordinates are `1`-Lipschitz, which is how a small ball about a point of the edge
stays inside the block. -/
theorem abs_coordAlong_sub_le (hu : IsDirection u) (a x y : Plane) :
    |coordAlong a u x - coordAlong a u y| ≤ dist x y := by
  have h : coordAlong a u x - coordAlong a u y = inner ℝ u (x - y) := by
    rw [coordAlong, coordAlong, ← inner_sub_right]
    congr 1
    module
  rw [h, dist_eq_norm]
  calc |inner ℝ u (x - y)| ≤ ‖u‖ * ‖x - y‖ := abs_real_inner_le_norm _ _
    _ = ‖x - y‖ := by rw [hu.norm, one_mul]

theorem abs_coordAcross_sub_le (hu : IsDirection u) (a x y : Plane) :
    |coordAcross a u x - coordAcross a u y| ≤ dist x y := by
  have h : coordAcross a u x - coordAcross a u y = det u (x - y) := by
    simp only [coordAcross, det]
    simp
    ring
  rw [h, dist_eq_norm]
  calc |det u (x - y)| ≤ ‖u‖ * ‖x - y‖ := abs_det_le _ _
    _ = ‖x - y‖ := by rw [hu.norm, one_mul]

/-- The open block around the directed edge from `a` with unit tangent `u`: the points whose
progress lies in `(t₁, t₂)` and whose signed distance lies in `(s₁, s₂)`. -/
def strip (a u : Plane) (t₁ t₂ s₁ s₂ : ℝ) : Set Plane :=
  {x | t₁ < coordAlong a u x ∧ coordAlong a u x < t₂ ∧
    s₁ < coordAcross a u x ∧ coordAcross a u x < s₂}

theorem mem_strip_iff {t₁ t₂ s₁ s₂ : ℝ} :
    x ∈ strip a u t₁ t₂ s₁ s₂ ↔ t₁ < coordAlong a u x ∧ coordAlong a u x < t₂ ∧
      s₁ < coordAcross a u x ∧ coordAcross a u x < s₂ := Iff.rfl

theorem continuous_coordAlong (a u : Plane) : Continuous (coordAlong a u) :=
  (continuous_const.inner (continuous_id.sub continuous_const))

theorem continuous_coordAcross (a u : Plane) : Continuous (coordAcross a u) :=
  (continuous_det_right u).comp (continuous_id.sub continuous_const)

theorem isOpen_strip (a u : Plane) (t₁ t₂ s₁ s₂ : ℝ) : IsOpen (strip a u t₁ t₂ s₁ s₂) := by
  have key : strip a u t₁ t₂ s₁ s₂ =
      ({x : Plane | t₁ < coordAlong a u x} ∩ {x : Plane | coordAlong a u x < t₂}) ∩
        ({x : Plane | s₁ < coordAcross a u x} ∩ {x : Plane | coordAcross a u x < s₂}) := by
    ext y
    simp only [mem_strip_iff, mem_inter_iff, mem_setOf_eq]
    tauto
  rw [key]
  exact ((isOpen_lt continuous_const (continuous_coordAlong a u)).inter
      (isOpen_lt (continuous_coordAlong a u) continuous_const)).inter
    ((isOpen_lt continuous_const (continuous_coordAcross a u)).inter
      (isOpen_lt (continuous_coordAcross a u) continuous_const))

theorem convex_strip (a u : Plane) (t₁ t₂ s₁ s₂ : ℝ) : Convex ℝ (strip a u t₁ t₂ s₁ s₂) := by
  have key : strip a u t₁ t₂ s₁ s₂ =
      ({x : Plane | t₁ + inner ℝ u a < inner ℝ u x} ∩ {x : Plane | inner ℝ u x < t₂ + inner ℝ u a})
        ∩ ({x : Plane | s₁ + det u a < det u x} ∩ {x : Plane | det u x < s₂ + det u a}) := by
    ext y
    have h1 : coordAlong a u y = inner ℝ u y - inner ℝ u a := by
      rw [coordAlong, inner_sub_right]
    have h2 : coordAcross a u y = det u y - det u a := by
      simp only [coordAcross, det]
      simp
      ring
    simp only [mem_strip_iff, mem_inter_iff, mem_setOf_eq, h1, h2]
    constructor
    · rintro ⟨a1, a2, a3, a4⟩; exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    · rintro ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩; exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  rw [key]
  have hlin : IsLinearMap ℝ fun x : Plane => inner ℝ u x :=
    ⟨fun x y => inner_add_right _ _ _, fun c x => by rw [real_inner_smul_right, smul_eq_mul]⟩
  exact ((convex_halfSpace_gt hlin _).inter (convex_halfSpace_lt hlin _)).inter
    ((convex_halfSpace_gt (isLinearMap_det_right u) _).inter
      (convex_halfSpace_lt (isLinearMap_det_right u) _))

theorem mem_strip_param (hu : IsDirection u) (a : Plane) {t s t₁ t₂ s₁ s₂ : ℝ} :
    a + t • u + s • perp u ∈ strip a u t₁ t₂ s₁ s₂ ↔ t₁ < t ∧ t < t₂ ∧ s₁ < s ∧ s < s₂ := by
  rw [mem_strip_iff, coordAlong_param hu, coordAcross_param hu]

/-- A point of a block is at distance `|coordAcross|` from the foot of its perpendicular on the
edge line, which is the point of the edge with the same progress. -/
theorem dist_foot (hu : IsDirection u) (a x : Plane) :
    dist x (a + (coordAlong a u x) • u) = |coordAcross a u x| := by
  have h := frame_decomp hu a x
  rw [dist_eq_norm]
  have hx : x - (a + (coordAlong a u x) • u) = (coordAcross a u x) • perp u := by
    nth_rewrite 1 [h]
    module
  rw [hx, norm_smul, Real.norm_eq_abs, norm_perp, hu.norm, mul_one]

end Plane

/-! ## Simple closed polygons

A polygon is presented by its cyclic vertex list. Indexing by `ZMod (m + 3)` builds in both the
cyclic successor and the requirement that there are at least three vertices, and it makes
`NeZero` available without a side hypothesis. -/

open Plane

variable {m : ℕ}

/-- A simple closed polygonal curve, presented by its cyclic vertex list. -/
structure ClosedPolygon (m : ℕ) where
  /-- The vertices, in cyclic order. -/
  vertex : ZMod (m + 3) → Plane
  /-- The vertices are distinct. -/
  vertex_inj : Function.Injective vertex
  /-- Simplicity: an edge meets any other edge only at one of its own endpoints. -/
  edges_meet : ∀ i j : ZMod (m + 3), i ≠ j →
    segment ℝ (vertex i) (vertex (i + 1)) ∩ segment ℝ (vertex j) (vertex (j + 1)) ⊆
      {vertex i, vertex (i + 1)}
  /-- No redundant vertex: the two edges at a vertex are not collinear. The blueprint deletes
  such vertices before starting, and the vertex matching needs `det ≠ 0` there. -/
  corner : ∀ i : ZMod (m + 3), det (vertex (i - 1) - vertex i) (vertex (i + 1) - vertex i) ≠ 0

namespace ClosedPolygon

variable (P : ClosedPolygon m) (i j : ZMod (m + 3)) (c t s : ℝ)

theorem one_ne_zero' : (1 : ZMod (m + 3)) ≠ 0 := by
  intro h
  rw [show (1 : ZMod (m + 3)) = ((1 : ℕ) : ZMod (m + 3)) by norm_num,
    ZMod.natCast_eq_zero_iff] at h
  have := Nat.le_of_dvd one_pos h
  omega

theorem succ_ne_self : i + 1 ≠ i := fun h => one_ne_zero' (m := m) (by linear_combination h)

theorem vertex_ne : P.vertex i ≠ P.vertex (i + 1) := fun h =>
  succ_ne_self i (P.vertex_inj h).symm

/-! ### Edges, in their own frame -/

/-- The length of the edge leaving vertex `i`. -/
noncomputable def len : ℝ := ‖P.vertex (i + 1) - P.vertex i‖

/-- The unit tangent of the edge leaving vertex `i`, which is also the outgoing ray at `i`. -/
noncomputable def tang : Plane := dir (P.vertex (i + 1) - P.vertex i)

/-- The incoming ray at vertex `i`: the direction back along the edge that arrives there. -/
noncomputable def rayIn : Plane := dir (P.vertex (i - 1) - P.vertex i)

/-- The point of the plane at progress `t` and signed offset `s` in the frame of edge `i`. -/
noncomputable def off : Plane := P.vertex i + t • P.tang i + s • perp (P.tang i)

/-- The point of edge `i` at distance `c` from its initial vertex. -/
noncomputable def pt : Plane := P.off i c 0

/-- The edge leaving vertex `i`. -/
def edge : Set Plane := segment ℝ (P.vertex i) (P.vertex (i + 1))

/-- The carrier of the polygon: the union of its edges. -/
def carrier : Set Plane := ⋃ i, P.edge i

variable {P i j c t s}

theorem sub_ne_zero_of_edge : P.vertex (i + 1) - P.vertex i ≠ 0 :=
  sub_ne_zero.2 (P.vertex_ne i).symm

theorem len_pos : 0 < P.len i := norm_pos_iff.2 sub_ne_zero_of_edge

theorem isDirection_tang : IsDirection (P.tang i) := isDirection_dir sub_ne_zero_of_edge

theorem len_smul_tang : (P.len i) • P.tang i = P.vertex (i + 1) - P.vertex i := by
  rw [tang, dir, smul_smul, len, mul_inv_cancel₀ (norm_ne_zero_iff.2 sub_ne_zero_of_edge),
    one_smul]

theorem off_zero_zero : P.off i 0 0 = P.vertex i := by rw [off]; module

theorem pt_zero : P.pt i 0 = P.vertex i := off_zero_zero

theorem pt_len : P.pt i (P.len i) = P.vertex (i + 1) := by
  rw [pt, off, zero_smul, add_zero, len_smul_tang]
  module

theorem off_sub_vertex : P.off i t s - P.vertex i = t • P.tang i + s • perp (P.tang i) := by
  rw [off]; module

theorem pt_sub_vertex : P.pt i c - P.vertex i = c • P.tang i := by
  rw [pt, off_sub_vertex, zero_smul, add_zero]

theorem dist_pt_vertex : dist (P.pt i c) (P.vertex i) = |c| := by
  rw [dist_eq_norm, pt_sub_vertex, norm_smul, Real.norm_eq_abs, isDirection_tang.norm, mul_one]

theorem dist_off_vertex_le : dist (P.off i t s) (P.vertex i) ≤ |t| + |s| := by
  rw [dist_eq_norm, off_sub_vertex]
  calc ‖t • P.tang i + s • perp (P.tang i)‖ ≤ ‖t • P.tang i‖ + ‖s • perp (P.tang i)‖ :=
        norm_add_le _ _
    _ = |t| + |s| := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, norm_perp,
          isDirection_tang.norm, mul_one, mul_one]

@[simp] theorem coordAlong_off : coordAlong (P.vertex i) (P.tang i) (P.off i t s) = t :=
  coordAlong_param isDirection_tang _ _ _

@[simp] theorem coordAcross_off : coordAcross (P.vertex i) (P.tang i) (P.off i t s) = s :=
  coordAcross_param isDirection_tang _ _ _

/-- Every point is the point of some frame position, so the two coordinates identify it. -/
theorem off_coord (P : ClosedPolygon m) (i : ZMod (m + 3)) (x : Plane) :
    x = P.off i (coordAlong (P.vertex i) (P.tang i) x) (coordAcross (P.vertex i) (P.tang i) x) :=
  frame_decomp isDirection_tang _ _

theorem off_injective (h : P.off i t s = P.off i t' s') : t = t' ∧ s = s' := by
  constructor
  · have := congrArg (coordAlong (P.vertex i) (P.tang i)) h
    simpa using this
  · have := congrArg (coordAcross (P.vertex i) (P.tang i)) h
    simpa using this

theorem mem_edge_iff {x : Plane} :
    x ∈ P.edge i ↔ ∃ c ∈ Set.Icc (0 : ℝ) (P.len i), x = P.pt i c := by
  rw [edge, segment_eq_image' ℝ]
  constructor
  · rintro ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩
    refine ⟨θ * P.len i, ⟨mul_nonneg hθ0 len_pos.le, ?_⟩, ?_⟩
    · nlinarith [len_pos (P := P) (i := i)]
    · rw [pt, off, zero_smul, add_zero, ← len_smul_tang]
      simp [smul_smul]
  · rintro ⟨c, ⟨hc0, hc1⟩, rfl⟩
    refine ⟨c / P.len i, ⟨div_nonneg hc0 len_pos.le, ?_⟩, ?_⟩
    · rw [div_le_one len_pos]; exact hc1
    · rw [pt, off, zero_smul, add_zero, ← len_smul_tang]
      simp [smul_smul, div_mul_cancel₀ _ (len_pos (P := P) (i := i)).ne']

theorem pt_mem_edge (hc : c ∈ Set.Icc (0 : ℝ) (P.len i)) : P.pt i c ∈ P.edge i :=
  mem_edge_iff.2 ⟨c, hc, rfl⟩

theorem vertex_mem_edge : P.vertex i ∈ P.edge i := by
  rw [← pt_zero]; exact pt_mem_edge ⟨le_refl _, len_pos.le⟩

theorem vertex_mem_carrier : P.vertex i ∈ P.carrier := Set.mem_iUnion.2 ⟨i, vertex_mem_edge⟩

theorem edge_subset_carrier : P.edge i ⊆ P.carrier := Set.subset_iUnion _ i

/-- The incoming ray at `i + 1` is the reverse of the tangent of edge `i`. This is the identity
that lets the two germs at a shared vertex be compared. -/
theorem rayIn_succ : P.rayIn (i + 1) = -P.tang i := by
  rw [rayIn, tang, add_sub_cancel_right, dir, dir, norm_sub_rev]
  module

theorem vertex_pred_ne : P.vertex (i - 1) - P.vertex i ≠ 0 := by
  have h := P.vertex_ne (i - 1)
  rw [sub_add_cancel] at h
  exact sub_ne_zero.2 h

theorem det_rays_ne_zero : det (P.rayIn i) (P.tang i) ≠ 0 := by
  obtain ⟨c₁, hc₁, h₁⟩ := dir_eq_smul (vertex_pred_ne (P := P) (i := i))
  obtain ⟨c₂, hc₂, h₂⟩ := dir_eq_smul (sub_ne_zero_of_edge (P := P) (i := i))
  rw [rayIn, tang, h₁, h₂, det_smul_left, det_smul_right]
  exact mul_ne_zero hc₁.ne' (mul_ne_zero hc₂.ne' (P.corner i))

/-- A point of the edge arriving at `i` is a nonnegative multiple of the incoming ray away from
the vertex; a point of the edge leaving `i` is a nonnegative multiple of the outgoing one. This
is what keeps the two incident edges out of both sectors at `i`. -/
theorem mem_edge_pred_sub {x : Plane} (hx : x ∈ P.edge (i - 1)) :
    ∃ c : ℝ, 0 ≤ c ∧ x - P.vertex i = c • P.rayIn i := by
  rw [mem_edge_iff] at hx
  obtain ⟨c, ⟨hc0, hc1⟩, rfl⟩ := hx
  refine ⟨P.len (i - 1) - c, by linarith, ?_⟩
  have hsucc : i - 1 + 1 = i := sub_add_cancel i 1
  have hr : P.rayIn i = -P.tang (i - 1) := by
    have := rayIn_succ (P := P) (i := i - 1)
    rwa [hsucc] at this
  have hv : P.vertex i = P.vertex (i - 1 + 1) := by rw [hsucc]
  have hlen : P.vertex (i - 1 + 1) = P.vertex (i - 1) + (P.len (i - 1)) • P.tang (i - 1) := by
    rw [len_smul_tang]; module
  rw [pt, off, zero_smul, add_zero, hr, hv, hlen]
  module

theorem mem_edge_sub {x : Plane} (hx : x ∈ P.edge i) :
    ∃ c : ℝ, 0 ≤ c ∧ x - P.vertex i = c • P.tang i := by
  rw [mem_edge_iff] at hx
  obtain ⟨c, ⟨hc0, _⟩, rfl⟩ := hx
  exact ⟨c, hc0, pt_sub_vertex⟩

theorem pt_eq : P.pt i c = P.vertex i + c • P.tang i := by rw [pt, off, zero_smul, add_zero]

end ClosedPolygon

/-! ## The constants

`StripData` is the blueprint's "choose the blocks so that consecutive ones overlap and
nonadjacent closures are disjoint", with every constant named. The three numbers are a cone
radius `R`, a trim `lam` and a half-width `rho`; the separation hypotheses are exactly the
instances of Lemma 1.4 (b) that the construction consumes, and `germ` is the vertex-matching
threshold. Producing them is the unproved `exists_stripData`; see the Status section. -/

/-- The constants of the collar of a simple closed polygon. -/
structure StripData (P : ClosedPolygon m) where
  /-- The radius of the vertex sectors. -/
  R : ℝ
  /-- The distance by which an edge block stops short of each endpoint of its edge. -/
  lam : ℝ
  /-- The half-width of an edge block. -/
  rho : ℝ
  rho_pos : 0 < rho
  rho_lt_lam : rho < lam
  /-- The sectors reach past the ends of the blocks they have to overlap. -/
  two_lam_lt_R : 2 * lam < R
  /-- The blocks are nonempty, with room to spare at both ends. -/
  four_lam_lt_len : ∀ i, 4 * lam < P.len i
  /-- A sector does not run past the far end of an incident edge. -/
  R_le_len : ∀ i, R ≤ P.len i
  /-- Distinct vertices are `2R` apart, so distinct sectors are disjoint. -/
  sep_vertex : ∀ i j, i ≠ j → 2 * R ≤ dist (P.vertex i) (P.vertex j)
  /-- A vertex is `2R` away from every nonincident edge. The factor `2` is the slack that a
  block of half-width `rho ≤ R` needs in `notMem_sectorL_of_far`. -/
  sep_vertex_edge : ∀ i j, j ≠ i - 1 → j ≠ i → ∀ y ∈ P.edge j, 2 * R ≤ dist (P.vertex i) y
  /-- The trimmed edge `i` is `2 * rho` away from every other edge. -/
  sep_trim_edge : ∀ i j, j ≠ i → ∀ c ∈ Set.Icc lam (P.len i - lam), ∀ y ∈ P.edge j,
    2 * rho ≤ dist (P.pt i c) y
  /-- **The vertex-matching threshold.** This is the only hypothesis that is not a separation of
  compact sets: it says the blocks are narrow enough, relative to how far they stop short of the
  vertices, for `Plane.germs_split'` to apply at every corner. -/
  germ : ∀ i, rho * (1 + |inner ℝ (P.rayIn i) (P.tang i)|) ≤ lam * |det (P.rayIn i) (P.tang i)|

namespace StripData

variable {P : ClosedPolygon m} (D : StripData P) {i j : ZMod (m + 3)} {x : Plane}

theorem lam_pos : 0 < D.lam := lt_trans D.rho_pos D.rho_lt_lam

theorem R_pos : 0 < D.R := by have := D.lam_pos; linarith [D.two_lam_lt_R]

theorem rho_lt_R : D.rho < D.R := by
  have := D.lam_pos; have := D.rho_lt_lam; linarith [D.two_lam_lt_R]

/-! ### The four families of blocks -/

/-- The left block of edge `i`. -/
def blockL (i : ZMod (m + 3)) : Set Plane :=
  strip (P.vertex i) (P.tang i) D.lam (P.len i - D.lam) 0 D.rho

/-- The right block of edge `i`. -/
def blockR (i : ZMod (m + 3)) : Set Plane :=
  strip (P.vertex i) (P.tang i) D.lam (P.len i - D.lam) (-D.rho) 0

/-- The left sector at vertex `i`: the arc `arcCCW (tang i) (rayIn i)` is the one carrying both
left germs, by `Plane.germs_split'`. -/
def sectorL (i : ZMod (m + 3)) : Set Plane :=
  cone (P.vertex i) (arcCCW (P.tang i) (P.rayIn i)) D.R

/-- The right sector at vertex `i`. -/
def sectorR (i : ZMod (m + 3)) : Set Plane :=
  cone (P.vertex i) (arcCCW (P.rayIn i) (P.tang i)) D.R

/-- The left side of the collar. -/
def sideL : Set Plane := ⋃ i, (D.sectorL i ∪ D.blockL i)

/-- The right side of the collar. -/
def sideR : Set Plane := ⋃ i, (D.sectorR i ∪ D.blockR i)

/-- The collar itself. -/
def nbhd : Set Plane := D.sideL ∪ D.sideR ∪ P.carrier

theorem mem_blockL_iff : x ∈ D.blockL i ↔
    D.lam < coordAlong (P.vertex i) (P.tang i) x ∧
      coordAlong (P.vertex i) (P.tang i) x < P.len i - D.lam ∧
      0 < coordAcross (P.vertex i) (P.tang i) x ∧
      coordAcross (P.vertex i) (P.tang i) x < D.rho := Iff.rfl

theorem mem_blockR_iff : x ∈ D.blockR i ↔
    D.lam < coordAlong (P.vertex i) (P.tang i) x ∧
      coordAlong (P.vertex i) (P.tang i) x < P.len i - D.lam ∧
      -D.rho < coordAcross (P.vertex i) (P.tang i) x ∧
      coordAcross (P.vertex i) (P.tang i) x < 0 := Iff.rfl

theorem mem_blockL_off {t s : ℝ} : P.off i t s ∈ D.blockL i ↔
    D.lam < t ∧ t < P.len i - D.lam ∧ 0 < s ∧ s < D.rho := by
  rw [mem_blockL_iff, ClosedPolygon.coordAlong_off, ClosedPolygon.coordAcross_off]

theorem mem_blockR_off {t s : ℝ} : P.off i t s ∈ D.blockR i ↔
    D.lam < t ∧ t < P.len i - D.lam ∧ -D.rho < s ∧ s < 0 := by
  rw [mem_blockR_iff, ClosedPolygon.coordAlong_off, ClosedPolygon.coordAcross_off]

theorem isOpen_blockL : IsOpen (D.blockL i) := isOpen_strip _ _ _ _ _ _
theorem isOpen_blockR : IsOpen (D.blockR i) := isOpen_strip _ _ _ _ _ _
theorem isOpen_sectorL : IsOpen (D.sectorL i) := isOpen_cone (isOpen_arcCCW _ _)
theorem isOpen_sectorR : IsOpen (D.sectorR i) := isOpen_cone (isOpen_arcCCW _ _)

theorem convex_blockL : Convex ℝ (D.blockL i) := convex_strip _ _ _ _ _ _
theorem convex_blockR : Convex ℝ (D.blockR i) := convex_strip _ _ _ _ _ _

theorem isConnected_sectorL : IsConnected (D.sectorL i) :=
  isConnected_cone_arcCCW _ (by rw [det_comm]; exact neg_ne_zero.2 ClosedPolygon.det_rays_ne_zero)
    D.R_pos

theorem isConnected_sectorR : IsConnected (D.sectorR i) :=
  isConnected_cone_arcCCW _ ClosedPolygon.det_rays_ne_zero D.R_pos

/-! ### Where the blocks live

A block sits inside the `rho`-neighbourhood of the trimmed edge, and a sector inside the ball of
radius `R` about its vertex. Every "nonadjacent blocks are disjoint" step below is one of these
two containments against one of the separation hypotheses. -/

/-- The foot of the perpendicular from a point of a block lies on the trimmed edge, within `rho`
of the point. -/
theorem exists_foot (h : x ∈ D.blockL i ∪ D.blockR i) :
    ∃ c ∈ Set.Icc D.lam (P.len i - D.lam), dist x (P.pt i c) < D.rho := by
  refine ⟨coordAlong (P.vertex i) (P.tang i) x, ?_, ?_⟩
  · rcases h with h | h
    · exact ⟨(D.mem_blockL_iff.1 h).1.le, (D.mem_blockL_iff.1 h).2.1.le⟩
    · exact ⟨(D.mem_blockR_iff.1 h).1.le, (D.mem_blockR_iff.1 h).2.1.le⟩
  · rw [ClosedPolygon.pt_eq, dist_foot ClosedPolygon.isDirection_tang]
    rcases h with h | h
    · obtain ⟨_, _, h1, h2⟩ := D.mem_blockL_iff.1 h
      rw [abs_of_pos h1]; exact h2
    · obtain ⟨_, _, h1, h2⟩ := D.mem_blockR_iff.1 h
      rw [abs_of_neg h2]; linarith

theorem sector_subset_ball : D.sectorL i ⊆ ball (P.vertex i) D.R := cone_subset_ball
theorem sectorR_subset_ball : D.sectorR i ⊆ ball (P.vertex i) D.R := cone_subset_ball

/-! ### The germ argument at a vertex

These four lemmas are the whole content of "at a vertex the left sides of the incoming and
outgoing strips enter the same component of the vertex disk minus the two incident rays". Each
is one projection of `Plane.germs_split'`, applied to the frame decomposition of a point of a
block. -/

/-- The threshold hypothesis, specialised to a point of a block. -/
theorem germ_ineq {t s : ℝ} (ht : D.lam < t) (hs0 : 0 < s) (hs : s < D.rho) :
    s * |inner ℝ (P.rayIn i) (P.tang i)| < t * |det (P.rayIn i) (P.tang i)| := by
  have hd : 0 < |det (P.rayIn i) (P.tang i)| := abs_pos.2 ClosedPolygon.det_rays_ne_zero
  have habs : (0 : ℝ) ≤ |inner ℝ (P.rayIn i) (P.tang i)| := abs_nonneg _
  have h1 : s * |inner ℝ (P.rayIn i) (P.tang i)| ≤ s * (1 + |inner ℝ (P.rayIn i) (P.tang i)|) := by
    nlinarith
  have h2 : s * (1 + |inner ℝ (P.rayIn i) (P.tang i)|) <
      D.rho * (1 + |inner ℝ (P.rayIn i) (P.tang i)|) := by nlinarith
  have h3 := D.germ i
  nlinarith

/-- A point of the left block of edge `i`, seen from the vertex it leaves, is the outgoing left
germ, hence in the left arc there. -/
theorem blockL_sub_mem_arcL_start (h : x ∈ D.blockL i) :
    x - P.vertex i ∈ arcCCW (P.tang i) (P.rayIn i) := by
  obtain ⟨h1, h2, h3, h4⟩ := D.mem_blockL_iff.1 h
  have hx := ClosedPolygon.off_coord P i x
  rw [hx, ClosedPolygon.off_sub_vertex]
  exact (germs_split' ClosedPolygon.det_rays_ne_zero h3 (D.germ_ineq h1 h3 h4)).1.2

/-- The same point, seen from the vertex it arrives at, is the incoming left germ. -/
theorem blockL_sub_mem_arcL_finish (h : x ∈ D.blockL i) :
    x - P.vertex (i + 1) ∈ arcCCW (P.tang (i + 1)) (P.rayIn (i + 1)) := by
  obtain ⟨h1, h2, h3, h4⟩ := D.mem_blockL_iff.1 h
  set t := coordAlong (P.vertex i) (P.tang i) x with ht
  set s := coordAcross (P.vertex i) (P.tang i) x with hs
  have hx : x = P.off i t s := ClosedPolygon.off_coord P i x
  have hr : P.rayIn (i + 1) = -P.tang i := ClosedPolygon.rayIn_succ
  have hkey : x - P.vertex (i + 1) =
      (P.len i - t) • P.rayIn (i + 1) - s • perp (P.rayIn (i + 1)) := by
    have hv : P.vertex (i + 1) = P.vertex i + (P.len i) • P.tang i := by
      rw [ClosedPolygon.len_smul_tang]; module
    rw [hx, ClosedPolygon.off, hv, hr]
    have hp : perp (-P.tang i) = -perp (P.tang i) := by
      ext k; fin_cases k <;> simp [perp]
    rw [hp]
    module
  rw [hkey]
  exact (germs_split' ClosedPolygon.det_rays_ne_zero h3
    (D.germ_ineq (i := i + 1) (by linarith) h3 h4)).1.1

/-- A point of the right block of edge `i`, seen from the vertex it leaves, is the outgoing right
germ, hence in the right arc there. -/
theorem blockR_sub_mem_arcR_start (h : x ∈ D.blockR i) :
    x - P.vertex i ∈ arcCCW (P.rayIn i) (P.tang i) := by
  obtain ⟨h1, h2, h3, h4⟩ := D.mem_blockR_iff.1 h
  set t := coordAlong (P.vertex i) (P.tang i) x with ht
  set s := coordAcross (P.vertex i) (P.tang i) x with hs
  have hx : x = P.off i t s := ClosedPolygon.off_coord P i x
  have hkey : x - P.vertex i = t • P.tang i - (-s) • perp (P.tang i) := by
    rw [hx, ClosedPolygon.off_sub_vertex]; module
  rw [hkey]
  exact (germs_split' ClosedPolygon.det_rays_ne_zero (by linarith)
    (D.germ_ineq h1 (by linarith) (by linarith))).2.2

/-- The same point, seen from the vertex it arrives at, is the incoming right germ. -/
theorem blockR_sub_mem_arcR_finish (h : x ∈ D.blockR i) :
    x - P.vertex (i + 1) ∈ arcCCW (P.rayIn (i + 1)) (P.tang (i + 1)) := by
  obtain ⟨h1, h2, h3, h4⟩ := D.mem_blockR_iff.1 h
  set t := coordAlong (P.vertex i) (P.tang i) x with ht
  set s := coordAcross (P.vertex i) (P.tang i) x with hs
  have hx : x = P.off i t s := ClosedPolygon.off_coord P i x
  have hr : P.rayIn (i + 1) = -P.tang i := ClosedPolygon.rayIn_succ
  have hkey : x - P.vertex (i + 1) =
      (P.len i - t) • P.rayIn (i + 1) + (-s) • perp (P.rayIn (i + 1)) := by
    have hv : P.vertex (i + 1) = P.vertex i + (P.len i) • P.tang i := by
      rw [ClosedPolygon.len_smul_tang]; module
    rw [hx, ClosedPolygon.off, hv, hr]
    have hp : perp (-P.tang i) = -perp (P.tang i) := by
      ext k; fin_cases k <;> simp [perp]
    rw [hp]
    module
  rw [hkey]
  exact (germs_split' ClosedPolygon.det_rays_ne_zero (by linarith)
    (D.germ_ineq (i := i + 1) (by linarith) (by linarith) (by linarith))).2.1

/-! ### Nonadjacent blocks are disjoint

Everything here is one of the separation hypotheses of `StripData` against one of the two
containments `exists_foot` and `sector_subset_ball`. -/

theorem pt_mem_edge_of_trim {c : ℝ} (hc : c ∈ Set.Icc D.lam (P.len i - D.lam)) :
    P.pt i c ∈ P.edge i :=
  ClosedPolygon.pt_mem_edge ⟨le_trans D.lam_pos.le hc.1, le_trans hc.2 (by linarith [D.lam_pos])⟩

/-- A block misses every edge but its own. -/
theorem block_notMem_edge (h : x ∈ D.blockL i ∪ D.blockR i) (hj : j ≠ i) : x ∉ P.edge j := by
  intro hx
  obtain ⟨c, hc, hd⟩ := D.exists_foot h
  have := D.sep_trim_edge i j hj c hc x hx
  rw [dist_comm] at hd
  linarith [D.rho_pos]

/-- A block misses its own edge, because its points have nonzero offset. -/
theorem block_notMem_own_edge (h : x ∈ D.blockL i ∪ D.blockR i) : x ∉ P.edge i := by
  intro hx
  rw [ClosedPolygon.mem_edge_iff] at hx
  obtain ⟨c, _, rfl⟩ := hx
  have hzero : coordAcross (P.vertex i) (P.tang i) (P.pt i c) = 0 := by
    rw [ClosedPolygon.pt]; exact ClosedPolygon.coordAcross_off
  rcases h with h | h
  · have hpos := (D.mem_blockL_iff.1 h).2.2.1
    rw [hzero] at hpos
    exact lt_irrefl 0 hpos
  · have hneg := (D.mem_blockR_iff.1 h).2.2.2
    rw [hzero] at hneg
    exact lt_irrefl 0 hneg

theorem block_notMem_carrier (h : x ∈ D.blockL i ∪ D.blockR i) : x ∉ P.carrier := by
  rintro hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
  by_cases hij : j = i
  · exact D.block_notMem_own_edge h (hij ▸ hj)
  · exact D.block_notMem_edge h hij hj

/-- A block stays out of the sectors at every vertex other than its own two. -/
theorem block_notMem_ball_vertex (h : x ∈ D.blockL i ∪ D.blockR i) (hj1 : j ≠ i)
    (hj2 : j ≠ i + 1) : x ∉ ball (P.vertex j) D.R := by
  intro hx
  obtain ⟨c, hc, hd⟩ := D.exists_foot h
  have hne1 : i ≠ j - 1 := fun he => hj2 (by rw [he]; ring)
  have := D.sep_vertex_edge j i hne1 (Ne.symm hj1) _ (D.pt_mem_edge_of_trim hc)
  have h1 : dist (P.vertex j) (P.pt i c) ≤ dist (P.vertex j) x + dist x (P.pt i c) :=
    dist_triangle _ _ _
  rw [mem_ball] at hx
  rw [dist_comm] at hx
  linarith [D.rho_lt_R]

/-- A sector misses every edge that is not incident to its vertex. -/
theorem sector_notMem_far_edge (h : x ∈ ball (P.vertex i) D.R) (hj1 : j ≠ i - 1) (hj2 : j ≠ i) :
    x ∉ P.edge j := by
  intro hx
  have := D.sep_vertex_edge i j hj1 hj2 x hx
  rw [mem_ball, dist_comm] at h
  linarith [D.R_pos]

/-- A sector misses the two edges incident to its vertex: their points lie on the two bounding
rays, and the arcs are open. -/
theorem sectorL_notMem_carrier (h : x ∈ D.sectorL i) : x ∉ P.carrier := by
  rintro hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
  by_cases hji : j = i
  · rw [hji] at hj
    obtain ⟨c, hc, he⟩ := ClosedPolygon.mem_edge_sub hj
    exact ((notMem_arcCCW_smul (P.tang i) (P.rayIn i) hc).1) (he ▸ h.1)
  by_cases hjp : j = i - 1
  · rw [hjp] at hj
    obtain ⟨c, hc, he⟩ := ClosedPolygon.mem_edge_pred_sub (i := i) hj
    exact ((notMem_arcCCW_smul (P.rayIn i) (P.tang i) hc).2) (he ▸ h.1)
  · exact D.sector_notMem_far_edge (i := i) h.2 hjp hji hj

theorem sectorR_notMem_carrier (h : x ∈ D.sectorR i) : x ∉ P.carrier := by
  rintro hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
  by_cases hji : j = i
  · rw [hji] at hj
    obtain ⟨c, hc, he⟩ := ClosedPolygon.mem_edge_sub hj
    exact ((notMem_arcCCW_smul (P.tang i) (P.rayIn i) hc).2) (he ▸ h.1)
  by_cases hjp : j = i - 1
  · rw [hjp] at hj
    obtain ⟨c, hc, he⟩ := ClosedPolygon.mem_edge_pred_sub (i := i) hj
    exact ((notMem_arcCCW_smul (P.rayIn i) (P.tang i) hc).1) (he ▸ h.1)
  · exact D.sector_notMem_far_edge (i := i) h.2 hjp hji hj

theorem sideL_disjoint_carrier : Disjoint D.sideL P.carrier := by
  rw [Set.disjoint_left]
  rintro y hy hc
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
  rcases hi with hi | hi
  · exact D.sectorL_notMem_carrier hi hc
  · exact D.block_notMem_carrier (Or.inl hi) hc

theorem sideR_disjoint_carrier : Disjoint D.sideR P.carrier := by
  rw [Set.disjoint_left]
  rintro y hy hc
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
  rcases hi with hi | hi
  · exact D.sectorR_notMem_carrier hi hc
  · exact D.block_notMem_carrier (Or.inr hi) hc

/-! ### The two sides are disjoint

Four families times four families. The pairs with distinct indices are settled by distance; the
pairs at a shared index are settled by `Plane.arcCCW_disjoint'` through the germ lemmas. -/

theorem blockL_disjoint_blockR (hL : x ∈ D.blockL i) (hR : x ∈ D.blockR j) : False := by
  by_cases hij : j = i
  · rw [hij] at hR
    exact absurd (D.mem_blockL_iff.1 hL).2.2.1 (asymm (D.mem_blockR_iff.1 hR).2.2.2)
  · obtain ⟨c, hc, hd⟩ := D.exists_foot (Or.inl hL)
    obtain ⟨c', hc', hd'⟩ := D.exists_foot (Or.inr hR)
    have hsep := D.sep_trim_edge i j hij c hc _ (D.pt_mem_edge_of_trim hc')
    have h1 : dist (P.pt i c) (P.pt j c') ≤ dist (P.pt i c) x + dist x (P.pt j c') :=
      dist_triangle _ _ _
    rw [dist_comm] at hd
    linarith

theorem blockL_disjoint_sectorR (hL : x ∈ D.blockL i) (hR : x ∈ D.sectorR j) : False := by
  by_cases hij : j = i
  · subst hij
    exact (arcCCW_disjoint' (ClosedPolygon.det_rays_ne_zero (P := P) (i := j))).ne_of_mem
      hR.1 (D.blockL_sub_mem_arcL_start hL) rfl
  by_cases hij2 : j = i + 1
  · subst hij2
    exact (arcCCW_disjoint' (ClosedPolygon.det_rays_ne_zero (P := P) (i := i + 1))).ne_of_mem
      hR.1 (D.blockL_sub_mem_arcL_finish hL) rfl
  · exact D.block_notMem_ball_vertex (Or.inl hL) hij hij2 hR.2

theorem sectorL_disjoint_blockR (hL : x ∈ D.sectorL i) (hR : x ∈ D.blockR j) : False := by
  by_cases hij : i = j
  · subst hij
    exact (arcCCW_disjoint' (ClosedPolygon.det_rays_ne_zero (P := P) (i := i))).ne_of_mem
      (D.blockR_sub_mem_arcR_start hR) hL.1 rfl
  by_cases hij2 : i = j + 1
  · subst hij2
    exact (arcCCW_disjoint' (ClosedPolygon.det_rays_ne_zero (P := P) (i := j + 1))).ne_of_mem
      (D.blockR_sub_mem_arcR_finish hR) hL.1 rfl
  · exact D.block_notMem_ball_vertex (Or.inr hR) hij hij2 hL.2

theorem sectorL_disjoint_sectorR (hL : x ∈ D.sectorL i) (hR : x ∈ D.sectorR j) : False := by
  by_cases hij : i = j
  · subst hij
    exact (arcCCW_disjoint' (ClosedPolygon.det_rays_ne_zero (P := P) (i := i))).ne_of_mem
      hR.1 hL.1 rfl
  · have hsep := D.sep_vertex i j hij
    have hdL : dist x (P.vertex i) < D.R := hL.2
    have hdR : dist x (P.vertex j) < D.R := hR.2
    have h1 : dist (P.vertex i) (P.vertex j) ≤ dist (P.vertex i) x + dist x (P.vertex j) :=
      dist_triangle _ _ _
    rw [dist_comm (P.vertex i) x] at h1
    linarith

theorem sideL_disjoint_sideR : Disjoint D.sideL D.sideR := by
  rw [Set.disjoint_left]
  rintro y hy hz
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hz
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · exact D.sectorL_disjoint_sectorR hi hj
  · exact D.sectorL_disjoint_blockR hi hj
  · exact D.blockL_disjoint_sectorR hi hj
  · exact D.blockL_disjoint_blockR hi hj

end StripData

end Schoenflies

end BundlePart404
