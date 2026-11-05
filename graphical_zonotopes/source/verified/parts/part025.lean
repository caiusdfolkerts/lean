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

public import verified.parts.part024
import all verified.parts.part024

@[expose] public section

set_option debug.skipKernelTC false
set_option linter.all false
set_option Elab.async false
set_option internal.cmdlineSnapshots true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

section BundlePart363
/- Source: dev/planar_search/schoenflies_port/Schoenflies/Plane.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/




/-!
# The plane, and the compactness toolkit

The plane is `EuclideanSpace ℝ (Fin 2)`. This module fixes that choice, supplies the
orientation form `det` and the right-angle rotation `perp` used to keep track of the two
sides of a polygonal curve, and collects the elementary consequences of compactness and
connectedness that the rest of the development uses without comment.

## Blueprint

* `det`, `perp` — Appendix C, item 1.
* `Plane.notMem_of_mem_segment_of_isMinOn` — Lemma 1.3 (nearest-point segment).
* `Plane.exists_thickening_subset`, `Plane.exists_dist_pos`, `Plane.exists_ball_subset_diff`
  — Lemma 1.4 (a), (b), (c) (compact separation).
* `Plane.eq_singleton_iInter_of_diam_tendsto_zero` — Lemma 1.6 (nested compact singleton).
* `Plane.connectedComponentIn_eq_of_frontier_disjoint` — Lemma 1.7 (recognizing a component).

Lemma 1.5 (closure and diameter) is `Metric.diam_closure` in Mathlib.
-/

open Metric Set

namespace Schoenflies

/-- The plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

namespace Plane

/-- Build a point of the plane from its two coordinates. -/
abbrev mk (x y : ℝ) : Plane := !₂[x, y]

@[simp] theorem mk_zero (x y : ℝ) : mk x y 0 = x := rfl
@[simp] theorem mk_one (x y : ℝ) : mk x y 1 = y := rfl

/-! ### The orientation form and the right-angle rotation -/

/-- The orientation form `det (a, b) = a₁b₂ - a₂b₁`. It is positive exactly when `b` lies
counterclockwise of `a`. -/
def det (a b : Plane) : ℝ := a 0 * b 1 - a 1 * b 0

/-- `u` turned counterclockwise through a right angle. -/
def perp (u : Plane) : Plane := mk (-u 1) (u 0)

@[simp] theorem perp_zero (u : Plane) : perp u 0 = -u 1 := rfl
@[simp] theorem perp_one (u : Plane) : perp u 1 = u 0 := rfl

@[simp] theorem det_self (a : Plane) : det a a = 0 := by simp [det]; ring

theorem det_comm (a b : Plane) : det a b = -det b a := by simp [det]; ring

@[simp] theorem det_smul_left (r : ℝ) (a b : Plane) : det (r • a) b = r * det a b := by
  simp [det]; ring

@[simp] theorem det_smul_right (r : ℝ) (a b : Plane) : det a (r • b) = r * det a b := by
  simp [det]; ring

theorem det_add_left (a b c : Plane) : det (a + b) c = det a c + det b c := by
  simp [det]; ring

theorem det_add_right (a b c : Plane) : det a (b + c) = det a b + det a c := by
  simp [det]; ring

/-- The defining property of `perp`: it is the counterclockwise right-angle rotation, so it
pairs positively with its argument. -/
@[simp] theorem det_perp_self (u : Plane) : det u (perp u) = ‖u‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [det, Fin.sum_univ_two]
  ring

theorem inner_eq (u v : Plane) : inner ℝ u v = u 0 * v 0 + u 1 * v 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

/-- Turning twice reverses. -/
@[simp] theorem perp_perp (u : Plane) : perp (perp u) = -u := by
  ext i; fin_cases i <;> simp

@[simp] theorem inner_perp_self (u : Plane) : inner ℝ u (perp u) = 0 := by
  rw [inner_eq]; simp; ring

/-- Against `perp` on the right, `det` becomes the inner product. Together with
`det_perp_left` this is what lets the strip lemma trade one for the other. -/
@[simp] theorem det_perp_right (u v : Plane) : det u (perp v) = inner ℝ u v := by
  rw [inner_eq]; simp [det]

@[simp] theorem det_perp_left (u v : Plane) : det (perp u) v = -inner ℝ u v := by
  rw [inner_eq]; simp [det]; ring

@[simp] theorem det_perp_perp (u v : Plane) : det (perp u) (perp v) = det u v := by
  simp [det]; ring

@[simp] theorem norm_perp (u : Plane) : ‖perp u‖ = ‖u‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp [Fin.sum_univ_two, sq_abs]
  ring

/-- Two vectors are parallel exactly when the orientation form kills them. This is the
angle-free reading of "`u` and `v` point along one line". -/
theorem det_eq_zero_iff_smul (u v : Plane) (hu : u ≠ 0) :
    det u v = 0 ↔ ∃ r : ℝ, v = r • u := by
  constructor
  · intro h
    -- `u ≠ 0` means some coordinate is nonzero; solve for the ratio there.
    have hcoord : u 0 ≠ 0 ∨ u 1 ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hu (by ext i; fin_cases i <;> simp [hc.1, hc.2])
    simp only [det, sub_eq_zero] at h
    rcases hcoord with h0 | h1
    · refine ⟨v 0 / u 0, ?_⟩
      ext i
      fin_cases i <;> simp <;> field_simp; linarith
    · refine ⟨v 1 / u 1, ?_⟩
      ext i
      fin_cases i <;> simp <;> field_simp; linarith
  · rintro ⟨r, rfl⟩
    simp

/-! ### Compactness -/

variable {K L U V : Set Plane} {x a y : Plane}

/-- Lemma 1.3 (nearest-point segment). If `a` is a point of `K` nearest to `x ∉ K`, then the
half-open segment `[x, a)` misses `K`. -/
theorem notMem_of_mem_segment_of_isMinOn (haK : a ∈ K) (hxK : x ∉ K)
    (hmin : ∀ b ∈ K, dist x a ≤ dist x b) (hy : y ∈ segment ℝ x a) (hya : y ≠ a) :
    y ∉ K := by
  intro hyK
  -- `a ≠ x`, since `a ∈ K` and `x ∉ K`, so the segment is nondegenerate.
  have hax : a ≠ x := fun h => hxK (h ▸ haK)
  have hpos : 0 < dist x a := dist_pos.2 (Ne.symm hax)
  -- Write `y = x + t • (a - x)` with `0 ≤ t ≤ 1`; `t = 1` is excluded by `y ≠ a`.
  rw [segment_eq_image' ℝ x a] at hy
  obtain ⟨t, ht, rfl⟩ := hy
  have ht1 : t < 1 := by
    rcases lt_or_eq_of_le ht.2 with h | h
    · exact h
    · exact absurd (by rw [h]; module) hya
  -- Then `dist x y = t * dist x a < dist x a`, contradicting minimality.
  have hdist : dist x (x + t • (a - x)) = t * dist x a := by
    rw [dist_eq_norm, dist_eq_norm]
    have : x - (x + t • (a - x)) = t • (x - a) := by module
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
  have := hmin _ hyK
  rw [hdist] at this
  nlinarith

/-- Lemma 1.4 (a) (compact separation). A compact set inside an open set has a uniform
neighbourhood inside it. Empty `K` is allowed: `thickening ρ ∅ = ∅`. -/
theorem exists_thickening_subset (hK : IsCompact K) (hU : IsOpen U) (h : K ⊆ U) :
    ∃ ρ > 0, thickening ρ K ⊆ U :=
  hK.exists_thickening_subset_open hU h

/-- Lemma 1.4 (b) (compact separation). Two disjoint nonempty compact sets have positive
distance. -/
theorem exists_dist_pos (hK : IsCompact K) (hL : IsCompact L) (hd : Disjoint K L) :
    ∃ ρ > 0, ∀ p ∈ K, ∀ q ∈ L, ρ ≤ dist p q := by
  obtain ⟨ρ, hρ, hsub⟩ :=
    hK.exists_thickening_subset_open hL.isClosed.isOpen_compl (disjoint_left.1 hd)
  refine ⟨ρ, hρ, fun p hp q hq => ?_⟩
  by_contra hlt
  exact hsub (mem_thickening_iff.2 ⟨p, hp, by rw [dist_comm]; exact not_le.1 hlt⟩) hq

/-- Lemma 1.4 (c) (compact separation). A point of an open set off a compact set has a ball
inside the difference. -/
theorem exists_ball_subset_diff (hU : IsOpen U) (hK : IsCompact K) (hx : x ∈ U \ K) :
    ∃ ρ > 0, ball x ρ ⊆ U \ K := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU x hx.1
  obtain ⟨s, hs, hsK⟩ :=
    (isCompact_singleton (x := x)).exists_thickening_subset_open hK.isClosed.isOpen_compl
      (by simpa using hx.2)
  refine ⟨min r s, lt_min hr hs, fun z hz => ⟨hrU (ball_subset_ball (min_le_left _ _) hz), ?_⟩⟩
  exact hsK (mem_thickening_iff.2 ⟨x, rfl, lt_of_lt_of_le (mem_ball.1 hz) (min_le_right _ _)⟩)

/-- Lemma 1.6 (nested compact singleton). A decreasing sequence of nonempty compact sets whose
diameters tend to `0` has a single point in its intersection. -/
theorem eq_singleton_iInter_of_diam_tendsto_zero {K : ℕ → Set Plane}
    (hne : ∀ n, (K n).Nonempty) (hK : ∀ n, IsCompact (K n)) (hmono : Antitone K)
    (hdiam : Filter.Tendsto (fun n => diam (K n)) Filter.atTop (nhds 0)) :
    ∃ p, ⋂ n, K n = {p} := by
  have hnonempty : (⋂ n, K n).Nonempty :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed _
      (fun n => hmono (Nat.le_succ n)) hne (hK 0) (fun n => (hK n).isClosed)
  obtain ⟨p, hp⟩ := hnonempty
  refine ⟨p, subset_antisymm (fun q hq => ?_) (by simpa using hp)⟩
  -- Any two points of the intersection are within `diam (K n)` of each other, for every `n`.
  rw [mem_singleton_iff]
  have hbdd : ∀ n, dist q p ≤ diam (K n) := fun n =>
    dist_le_diam_of_mem (hK n).isBounded (mem_iInter.1 hq n) (mem_iInter.1 hp n)
  have : dist q p ≤ 0 := le_of_tendsto_of_tendsto' tendsto_const_nhds hdiam hbdd
  exact dist_le_zero.1 this

/-- Lemma 1.7 (recognizing a component). A region inside an open set whose frontier misses that
open set is a connected component of it. -/
theorem connectedComponentIn_eq_of_frontier_disjoint (hU : IsOpen U) (hUconn : IsPreconnected U)
    (hsub : U ⊆ V) (hfr : frontier U ∩ V = ∅) (hx : x ∈ U) :
    connectedComponentIn V x = U := by
  -- `U` is closed in `V`: `closure U ∩ V = (U ∪ ∂U) ∩ V = U`.
  have hclosed : closure U ∩ V ⊆ U := by
    rintro z ⟨hz1, hz2⟩
    by_contra hzU
    have : z ∈ frontier U ∩ V := ⟨by rw [hU.frontier_eq]; exact ⟨hz1, hzU⟩, hz2⟩
    rw [hfr] at this
    exact this
  refine subset_antisymm ?_ (hUconn.subset_connectedComponentIn hx hsub)
  -- The component `C` is covered by the disjoint open sets `U` and `(closure U)ᶜ`, and meets `U`.
  have hcover : connectedComponentIn V x ⊆ U ∪ (closure U)ᶜ := by
    intro z hz
    by_cases h : z ∈ closure U
    · exact Or.inl (hclosed ⟨h, connectedComponentIn_subset V x hz⟩)
    · exact Or.inr h
  have hmeet : (connectedComponentIn V x ∩ U).Nonempty :=
    ⟨x, mem_connectedComponentIn (hsub hx), hx⟩
  have hempty : ¬ (connectedComponentIn V x ∩ (closure U)ᶜ).Nonempty := by
    intro hne
    obtain ⟨z, hz⟩ :=
      isPreconnected_connectedComponentIn U (closure U)ᶜ hU isClosed_closure.isOpen_compl
        hcover hmeet hne
    exact hz.2.2 (subset_closure hz.2.1)
  intro z hz
  by_contra hzU
  exact hempty ⟨z, hz, fun h => hzU (hclosed ⟨h, connectedComponentIn_subset V x hz⟩)⟩

end Plane

end Schoenflies

end BundlePart363

section BundlePart364
/- Source: dev/planar_search/schoenflies_port/Schoenflies/Curve.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/



/-!
# Arcs and Jordan curves

A simple arc is the image of an injective continuous map from `[0, 1]`; a Jordan curve is
the image of a map on `[0, 1]` which is injective before it returns to its start. Those are
the blueprint's definitions verbatim.

The parameter domain is a *subset of `ℝ`*, not a type: an arc is carried by an ordinary
`f : ℝ → Plane` together with `ContinuousOn f unitInterval` and `InjOn f unitInterval`.
Mathlib's `Path` bundles a map out of `↥unitInterval` instead, which is the right choice
when paths are to be composed up to homotopy, and the wrong one here: subarcs are taken at
arbitrary parameter pairs, reparametrisation is composition on `ℝ` with nothing to extract,
and a Jordan curve's theorems are all about *its parameters*. Taking the circle as the
domain would need a traversal of the circle by an interval, which is exactly what a
trigonometry-free development does not have.

`IsArcBetween` is the set-level reading — an arc *between two named points* — and is the
form most of the development speaks, since gluing and cutting are stated about endpoints.

## Blueprint

* `IsArc`, `IsJordanCurve` — §1, the definitions of a simple arc and a Jordan curve.
* `IsArcBetween` — an arc between two named points.
* `IsLoop` — the parametrisation underlying a Jordan curve.
-/

open Set unitInterval

namespace Schoenflies

/-! ### Arcs -/

/-- A simple arc: the image of a continuous injective map on `[0, 1]`. -/
def IsArc (A : Set Plane) : Prop :=
  ∃ f : ℝ → Plane, ContinuousOn f I ∧ InjOn f I ∧ f '' I = A

/-- An arc between two named points: the set-level reading, and the form gluing and cutting
are stated in. -/
def IsArcBetween (A : Set Plane) (p q : Plane) : Prop :=
  ∃ f : ℝ → Plane, ContinuousOn f I ∧ InjOn f I ∧ f '' I = A ∧ f 0 = p ∧ f 1 = q

/-- A loop: continuous on `[0, 1]`, returning to its start, and injective before it does. -/
structure IsLoop (f : ℝ → Plane) : Prop where
  continuousOn : ContinuousOn f I
  closes : f 0 = f 1
  injOn : InjOn f (Ico 0 1)

/-- A Jordan curve: the image of a loop. -/
def IsJordanCurve (C : Set Plane) : Prop :=
  ∃ f : ℝ → Plane, IsLoop f ∧ f '' I = C

/-! ### The unit interval, as a subset of `ℝ` -/

theorem zero_mem_I : (0 : ℝ) ∈ I := ⟨le_refl 0, zero_le_one⟩

theorem one_mem_I : (1 : ℝ) ∈ I := ⟨zero_le_one, le_refl 1⟩

theorem isCompact_I : IsCompact I := isCompact_Icc

theorem isConnected_I : IsConnected I := isConnected_Icc zero_le_one

/-- The image of a relatively closed piece of the parameter interval is compact. This is
what makes a parametrisation a closed map onto its arc, and hence its inverse continuous. -/
theorem isCompact_image_of_subset_I {f : ℝ → Plane} (hf : ContinuousOn f I)
    {S : Set ℝ} (hS : S ⊆ I) (hSc : IsClosed S) : IsCompact (f '' S) :=
  (isCompact_I.of_isClosed_subset hSc hS).image_of_continuousOn (hf.mono hS)

/-! ### Elementary properties -/

namespace IsArcBetween

variable {A : Set Plane} {p q : Plane}

theorem isArc (h : IsArcBetween A p q) : IsArc A := by
  obtain ⟨f, hc, hi, him, -, -⟩ := h
  exact ⟨f, hc, hi, him⟩

theorem left_mem (h : IsArcBetween A p q) : p ∈ A := by
  obtain ⟨f, -, -, rfl, rfl, -⟩ := h
  exact mem_image_of_mem f zero_mem_I

theorem right_mem (h : IsArcBetween A p q) : q ∈ A := by
  obtain ⟨f, -, -, rfl, -, rfl⟩ := h
  exact mem_image_of_mem f one_mem_I

/-- Running a piece the other way round. -/
theorem reverse (h : IsArcBetween A p q) : IsArcBetween A q p := by
  obtain ⟨f, hc, hi, him, hp, hq⟩ := h
  refine ⟨fun t => f (1 - t), ?_, ?_, ?_, by simpa using hq, by simpa using hp⟩
  · -- `t ↦ 1 - t` maps the interval to itself, continuously.
    refine hc.comp (by fun_prop) fun t ht => ?_
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  · intro s hs t ht hst
    have hs' : 1 - s ∈ I := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have ht' : 1 - t ∈ I := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have := hi hs' ht' hst
    linarith
  · rw [← him]
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, by ring_nf⟩

end IsArcBetween

namespace IsArc

variable {A : Set Plane}

theorem isCompact (h : IsArc A) : IsCompact A := by
  obtain ⟨f, hc, -, rfl⟩ := h
  exact isCompact_I.image_of_continuousOn hc

theorem isConnected (h : IsArc A) : IsConnected A := by
  obtain ⟨f, hc, -, rfl⟩ := h
  exact isConnected_I.image f hc

theorem nonempty (h : IsArc A) : A.Nonempty := h.isConnected.nonempty

theorem isClosed (h : IsArc A) : IsClosed A := h.isCompact.isClosed

/-- Every arc is an arc between its two endpoints. -/
theorem exists_isArcBetween (h : IsArc A) : ∃ p q, IsArcBetween A p q := by
  obtain ⟨f, hc, hi, him⟩ := h
  exact ⟨f 0, f 1, f, hc, hi, him, rfl, rfl⟩

end IsArc

namespace IsJordanCurve

variable {C : Set Plane}

theorem isCompact (h : IsJordanCurve C) : IsCompact C := by
  obtain ⟨f, hf, rfl⟩ := h
  exact isCompact_I.image_of_continuousOn hf.continuousOn

theorem isConnected (h : IsJordanCurve C) : IsConnected C := by
  obtain ⟨f, hf, rfl⟩ := h
  exact isConnected_I.image f hf.continuousOn

theorem nonempty (h : IsJordanCurve C) : C.Nonempty := h.isConnected.nonempty

theorem isClosed (h : IsJordanCurve C) : IsClosed C := h.isCompact.isClosed

end IsJordanCurve

end Schoenflies

end BundlePart364

section BundlePart365
/- Source: dev/planar_search/schoenflies_port/Schoenflies/Topology.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/



/-!
# Topology of the plane: the gaps Mathlib leaves

Appendix C of the blueprint lists the topology imported without proof. Almost all of it is in
Mathlib: compactness and Heine–Borel, the compact-to-Hausdorff homeomorphism criterion,
connectedness and its stability under images, unions through a common point, adjoining closure
points (`IsPreconnected.subset_closure`), a connected set inside a disjoint union of two opens
(`IsPreconnected.subset_left_of_subset_union`), `Metric.diam_closure`, thickenings, and the
two-piece pasting lemma (`continuousOn_union_iff_of_isClosed`).

This module collects the few that are not stated in the form the development uses.

## Blueprint

* `isOpen_connectedComponentIn` — Appendix C item 4: components of open subsets of the plane
  are open. The plane is locally connected, so this is Mathlib's, restated at `Plane` so that
  the instance is found once here rather than at every call site.
* `frontier_connectedComponentIn_compl_subset` — Appendix C item 5: the boundary of a component
  of the complement of a closed set lies in that closed set. This is the form Part I uses to
  recognize that a region's frontier sits on the curve.
* `continuousOn_union_of_isClosed` — Appendix C item 6, the pasting lemma, in the two-piece
  form the development pastes with.
-/

open Metric Set

namespace Schoenflies

namespace Plane

variable {U K : Set Plane} {x : Plane}

/-- Components of an open subset of the plane are open. The plane is locally connected. -/
theorem isOpen_connectedComponentIn (hU : IsOpen U) : IsOpen (connectedComponentIn U x) :=
  hU.connectedComponentIn

/-- Appendix C item 5. The frontier of a component of the complement of a closed set lies in
that closed set.

A frontier point off `K` would be a point of the open set `Kᶜ` in the closure of the
component; adjoining it keeps the component connected, so it was in the component already. -/
theorem frontier_connectedComponentIn_compl_subset (hK : IsClosed K) (x : Plane) :
    frontier (connectedComponentIn Kᶜ x) ⊆ K := by
  set C := connectedComponentIn Kᶜ x with hC
  have hCopen : IsOpen C := isOpen_connectedComponentIn hK.isOpen_compl
  intro z hz
  by_contra hzK
  -- `z` is a frontier point of the open set `C`, so it lies in `closure C` but not in `C`.
  rw [hCopen.frontier_eq] at hz
  obtain ⟨hzclosure, hzC⟩ := hz
  -- `C` is nonempty, since it has a frontier point in its closure.
  have hxU : x ∈ Kᶜ := by
    by_contra hx
    rw [hC, connectedComponentIn_eq_empty hx] at hzclosure
    simp at hzclosure
  -- Adjoining `z` keeps it connected and inside `Kᶜ`, so `z` was in the component already.
  have hsub : C ∪ {z} ⊆ Kᶜ := by
    refine union_subset (connectedComponentIn_subset _ _) ?_
    simpa using hzK
  have hconn : IsPreconnected (C ∪ {z}) :=
    (isPreconnected_connectedComponentIn (F := Kᶜ) (x := x)).subset_closure
      subset_union_left (union_subset subset_closure (by simpa using hzclosure))
  have : C ∪ {z} ⊆ C :=
    hconn.subset_connectedComponentIn (Or.inl (mem_connectedComponentIn hxU)) hsub
  exact hzC (this (Or.inr rfl))

/-- Appendix C item 6, the pasting lemma, two closed pieces. -/
theorem continuousOn_union_of_isClosed {f : Plane → Plane} {s t : Set Plane}
    (hs : IsClosed s) (ht : IsClosed t) (hfs : ContinuousOn f s) (hft : ContinuousOn f t) :
    ContinuousOn f (s ∪ t) :=
  (continuousOn_union_iff_of_isClosed hs ht).2 ⟨hfs, hft⟩

end Plane

end Schoenflies

end BundlePart365

section BundlePart366
/- Source: dev/planar_search/schoenflies_port/Schoenflies/Square.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/


/-!
# The sup metric and axis-parallel squares

The blueprint takes the Euclidean norm as primary and uses the sup norm for the
axis-parallel objects the polygonal work is built on: grids of small squares, the vertex
squares of the redrawing argument, and the large square a bounded set is caught inside.
Appendix C item 1 asks for the comparison `‖x‖∞ ≤ ‖x‖ ≤ √2 ‖x‖∞`, which is `supNorm_le_norm`
and `norm_le_sqrt_two_mul_supNorm` here.

The one theorem of substance is `isConnected_beyondSquare`: the plane outside a closed
square is connected. It is a *square* and not a disk on purpose — the outside of a square is
exactly a union of four half-planes, each convex, with consecutive ones sharing a point,
whereas the outside of a disk would need the polar decomposition this development withholds.

## Blueprint

* `supNorm`, `supDist` — Appendix C, item 1 (the sup metric).
* `supNorm_le_norm`, `norm_le_sqrt_two_mul_supNorm` — the comparison, used without comment.
* `closedSquare`, `openSquare` — the axis-parallel square about a point.
* `isConnected_beyondSquare` — the outside of a square is connected; what makes exactly one
  face of a plane graph unbounded.
-/

open Metric Set

namespace Schoenflies

namespace Plane

/-! ### Coordinates -/

theorem sub_apply (x y : Plane) (i : Fin 2) : (x - y) i = x i - y i := rfl

theorem smul_add_apply (a b : ℝ) (x y : Plane) (i : Fin 2) :
    (a • x + b • y) i = a * x i + b * y i := by simp

theorem continuous_coord (i : Fin 2) : Continuous fun x : Plane => x i :=
  PiLp.continuous_apply _ _ i

/-! ### The sup norm -/

/-- The sup norm `‖x‖∞ = max |x₁| |x₂|`. -/
noncomputable def supNorm (x : Plane) : ℝ := max |x 0| |x 1|

/-- The sup distance. -/
noncomputable def supDist (x y : Plane) : ℝ := supNorm (x - y)

theorem supNorm_nonneg (x : Plane) : 0 ≤ supNorm x :=
  le_trans (abs_nonneg _) (le_max_left _ _)

theorem supDist_nonneg (x y : Plane) : 0 ≤ supDist x y := supNorm_nonneg _

@[simp] theorem supDist_self (x : Plane) : supDist x x = 0 := by
  simp [supDist, supNorm]

theorem supDist_comm (x y : Plane) : supDist x y = supDist y x := by
  simp only [supDist, supNorm, sub_apply]
  rw [abs_sub_comm (x 0) (y 0), abs_sub_comm (x 1) (y 1)]

theorem abs_sub_zero_le_supDist (x y : Plane) : |x 0 - y 0| ≤ supDist x y :=
  le_max_left _ _

theorem abs_sub_one_le_supDist (x y : Plane) : |x 1 - y 1| ≤ supDist x y :=
  le_max_right _ _

theorem abs_zero_le_supNorm (x : Plane) : |x 0| ≤ supNorm x := le_max_left _ _

theorem abs_one_le_supNorm (x : Plane) : |x 1| ≤ supNorm x := le_max_right _ _

/-- The sup distance satisfies the triangle inequality, one coordinate at a time. -/
theorem supDist_triangle (x y z : Plane) : supDist x z ≤ supDist x y + supDist y z := by
  simp only [supDist, supNorm, sub_apply]
  refine max_le ?_ ?_
  · calc |x 0 - z 0| ≤ |x 0 - y 0| + |y 0 - z 0| := abs_sub_le _ _ _
      _ ≤ supDist x y + supDist y z :=
          add_le_add (abs_sub_zero_le_supDist x y) (abs_sub_zero_le_supDist y z)
  · calc |x 1 - z 1| ≤ |x 1 - y 1| + |y 1 - z 1| := abs_sub_le _ _ _
      _ ≤ supDist x y + supDist y z :=
          add_le_add (abs_sub_one_le_supDist x y) (abs_sub_one_le_supDist y z)

theorem norm_sq_eq (x : Plane) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]; simp [Fin.sum_univ_two]

/-- Half of Appendix C item 1's comparison: the sup norm is at most the Euclidean norm. -/
theorem supNorm_le_norm (x : Plane) : supNorm x ≤ ‖x‖ := by
  have h0 : |x 0| ≤ ‖x‖ := by
    have : |x 0| ^ 2 ≤ ‖x‖ ^ 2 := by rw [sq_abs, norm_sq_eq]; nlinarith [sq_nonneg (x 1)]
    nlinarith [abs_nonneg (x 0), norm_nonneg x]
  have h1 : |x 1| ≤ ‖x‖ := by
    have : |x 1| ^ 2 ≤ ‖x‖ ^ 2 := by rw [sq_abs, norm_sq_eq]; nlinarith [sq_nonneg (x 0)]
    nlinarith [abs_nonneg (x 1), norm_nonneg x]
  exact max_le h0 h1

/-- The other half: the Euclidean norm is at most `√2` times the sup norm. -/
theorem norm_le_sqrt_two_mul_supNorm (x : Plane) : ‖x‖ ≤ Real.sqrt 2 * supNorm x := by
  have h0 : x 0 ^ 2 ≤ supNorm x ^ 2 := by
    rw [← sq_abs]; nlinarith [abs_zero_le_supNorm x, abs_nonneg (x 0)]
  have h1 : x 1 ^ 2 ≤ supNorm x ^ 2 := by
    rw [← sq_abs]; nlinarith [abs_one_le_supNorm x, abs_nonneg (x 1)]
  have hbound : ‖x‖ ^ 2 ≤ (Real.sqrt 2 * supNorm x) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), norm_sq_eq]
    linarith
  nlinarith [norm_nonneg x, mul_nonneg (Real.sqrt_nonneg 2) (supNorm_nonneg x)]

/-! ### Coordinate half-planes

One convexity proof per direction serves all four sides of a square, and the outside of a
square is four of them. -/

theorem convex_coord_le (i : Fin 2) (r : ℝ) : Convex ℝ {x : Plane | x i ≤ r} := by
  intro x hx y hy a b ha hb hab
  simp only [mem_setOf_eq] at *
  rw [smul_add_apply]
  have hr : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy hb]

theorem convex_coord_ge (i : Fin 2) (r : ℝ) : Convex ℝ {x : Plane | r ≤ x i} := by
  intro x hx y hy a b ha hb hab
  simp only [mem_setOf_eq] at *
  rw [smul_add_apply]
  have hr : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy hb]

theorem convex_coord_lt (i : Fin 2) (r : ℝ) : Convex ℝ {x : Plane | x i < r} := by
  intro x hx y hy a b ha hb hab
  simp only [mem_setOf_eq] at *
  rw [smul_add_apply]
  have hr : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hb1 : b = 1 := by linarith
    subst hb1; nlinarith
  · nlinarith [mul_lt_mul_of_pos_left hx ha', mul_le_mul_of_nonneg_left hy.le hb]

theorem convex_coord_gt (i : Fin 2) (r : ℝ) : Convex ℝ {x : Plane | r < x i} := by
  intro x hx y hy a b ha hb hab
  simp only [mem_setOf_eq] at *
  rw [smul_add_apply]
  have hr : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hb1 : b = 1 := by linarith
    subst hb1; nlinarith
  · nlinarith [mul_lt_mul_of_pos_left hx ha', mul_le_mul_of_nonneg_left hy.le hb]

theorem isOpen_coord_lt (i : Fin 2) (r : ℝ) : IsOpen {x : Plane | x i < r} :=
  isOpen_lt (continuous_coord i) continuous_const

theorem isOpen_coord_gt (i : Fin 2) (r : ℝ) : IsOpen {x : Plane | r < x i} :=
  isOpen_lt continuous_const (continuous_coord i)

/-! ### Axis-parallel squares -/

/-- The closed axis-parallel square of radius `r` about `c`. -/
def closedSquare (c : Plane) (r : ℝ) : Set Plane := {x | supDist x c ≤ r}

/-- The open axis-parallel square of radius `r` about `c`. -/
def openSquare (c : Plane) (r : ℝ) : Set Plane := {x | supDist x c < r}

theorem closedSquare_eq_inter (c : Plane) (r : ℝ) :
    closedSquare c r =
      ({x : Plane | c 0 - r ≤ x 0} ∩ {x : Plane | x 0 ≤ c 0 + r}) ∩
      ({x : Plane | c 1 - r ≤ x 1} ∩ {x : Plane | x 1 ≤ c 1 + r}) := by
  ext x
  simp only [closedSquare, supDist, supNorm, sub_apply, mem_setOf_eq, mem_inter_iff,
    max_le_iff, abs_le]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

theorem openSquare_eq_inter (c : Plane) (r : ℝ) :
    openSquare c r =
      ({x : Plane | c 0 - r < x 0} ∩ {x : Plane | x 0 < c 0 + r}) ∩
      ({x : Plane | c 1 - r < x 1} ∩ {x : Plane | x 1 < c 1 + r}) := by
  ext x
  simp only [openSquare, supDist, supNorm, sub_apply, mem_setOf_eq, mem_inter_iff,
    max_lt_iff, abs_lt]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

theorem convex_closedSquare (c : Plane) (r : ℝ) : Convex ℝ (closedSquare c r) := by
  rw [closedSquare_eq_inter]
  exact ((convex_coord_ge 0 _).inter (convex_coord_le 0 _)).inter
    ((convex_coord_ge 1 _).inter (convex_coord_le 1 _))

theorem convex_openSquare (c : Plane) (r : ℝ) : Convex ℝ (openSquare c r) := by
  rw [openSquare_eq_inter]
  exact ((convex_coord_gt 0 _).inter (convex_coord_lt 0 _)).inter
    ((convex_coord_gt 1 _).inter (convex_coord_lt 1 _))

theorem isOpen_openSquare (c : Plane) (r : ℝ) : IsOpen (openSquare c r) := by
  rw [openSquare_eq_inter]
  exact ((isOpen_coord_gt 0 _).inter (isOpen_coord_lt 0 _)).inter
    ((isOpen_coord_gt 1 _).inter (isOpen_coord_lt 1 _))

theorem isClosed_closedSquare (c : Plane) (r : ℝ) : IsClosed (closedSquare c r) := by
  rw [closedSquare_eq_inter]
  exact ((isClosed_le continuous_const (continuous_coord 0)).inter
      (isClosed_le (continuous_coord 0) continuous_const)).inter
    ((isClosed_le continuous_const (continuous_coord 1)).inter
      (isClosed_le (continuous_coord 1) continuous_const))

/-! ### The outside of a square -/

/-- The plane outside the closed square of radius `r` about the origin. -/
def beyondSquare (r : ℝ) : Set Plane := {x | r < |x 0| ∨ r < |x 1|}

/-- The outside of a square is connected.

Four half-planes, each convex and hence connected, with consecutive ones sharing a corner.
No polar decomposition, and no arbitrary union of connected sets. The radius needs no sign
condition: for `r < 0` the four half-planes already cover the plane. -/
theorem isConnected_beyondSquare (r : ℝ) : IsConnected (beyondSquare r) := by
  set R : Set Plane := {x : Plane | r < x 0} with hR
  set L : Set Plane := {x : Plane | x 0 < -r} with hL
  set T : Set Plane := {x : Plane | r < x 1} with hT
  set B : Set Plane := {x : Plane | x 1 < -r} with hB
  have hcover : beyondSquare r = R ∪ T ∪ L ∪ B := by
    ext x
    simp only [beyondSquare, hR, hL, hT, hB, mem_setOf_eq, mem_union, lt_abs]
    constructor
    · rintro (h | h) <;> rcases h with h | h
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inl (Or.inr (by linarith))
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inr (by linarith)
    · rintro (((h | h) | h) | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl (Or.inr (by linarith))
      · exact Or.inr (Or.inr (by linarith))
  -- Consecutive sides share a corner. Membership unfolds definitionally, so `show` states
  -- the inequality the corner satisfies and `linarith` closes it.
  have hRT : mk (r + 1) (r + 1) ∈ R ∩ T :=
    ⟨show r < r + 1 by linarith, show r < r + 1 by linarith⟩
  have hTL : mk (-r - 1) (r + 1) ∈ T ∩ L :=
    ⟨show r < r + 1 by linarith, show -r - 1 < -r by linarith⟩
  have hLB : mk (-r - 1) (-r - 1) ∈ L ∩ B :=
    ⟨show -r - 1 < -r by linarith, show -r - 1 < -r by linarith⟩
  have cR : IsConnected R :=
    (convex_coord_gt 0 r).isConnected ⟨mk (r + 1) 0, show r < r + 1 by linarith⟩
  have cL : IsConnected L :=
    (convex_coord_lt 0 (-r)).isConnected ⟨mk (-r - 1) 0, show -r - 1 < -r by linarith⟩
  have cT : IsConnected T :=
    (convex_coord_gt 1 r).isConnected ⟨mk 0 (r + 1), show r < r + 1 by linarith⟩
  have cB : IsConnected B :=
    (convex_coord_lt 1 (-r)).isConnected ⟨mk 0 (-r - 1), show -r - 1 < -r by linarith⟩
  have c1 : IsConnected (R ∪ T) := cR.union ⟨mk (r + 1) (r + 1), hRT.1, hRT.2⟩ cT
  have c2 : IsConnected (R ∪ T ∪ L) :=
    c1.union ⟨mk (-r - 1) (r + 1), Or.inr hTL.1, hTL.2⟩ cL
  have c3 : IsConnected (R ∪ T ∪ L ∪ B) :=
    c2.union ⟨mk (-r - 1) (-r - 1), Or.inr hLB.1, hLB.2⟩ cB
  rw [hcover]
  exact c3

end Plane

end Schoenflies

end BundlePart366

section BundlePart367
/- Source: dev/planar_search/schoenflies_port/Schoenflies/Bounded.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/


/-!
# Catching a bounded set inside a square

The outer face of a plane graph is found by catching the whole drawing — finitely many points
and finitely many compact arcs — inside one axis-parallel square, and then observing that the
outside of that square is connected (`isConnected_beyondSquare`) and therefore lies in a single
face. This module is the "catching" half.

The key identity is `beyondSquare_eq_compl`: the outside of a square, as defined by a
coordinate inequality, *is* the complement of the closed square. It is what lets the
connectedness theorem be applied to a complement.

## Blueprint

* `beyondSquare_eq_compl` — the outside of a square is the complement of the closed square.
* `exists_closedSquare_of_isBounded`, `IsCompact.exists_closedSquare` — a bounded set is caught
  inside a square about the origin.
* `isOpen_compl_of_finite_isCompact` — the complement of a finite union of compact sets is
  open; the exterior of a plane graph is open for this reason.
-/

open Metric Set

namespace Schoenflies

namespace Plane

@[simp] theorem supDist_zero (x : Plane) : supDist x 0 = supNorm x := by
  simp [supDist, supNorm]

/-- The outside of a square is exactly the complement of the closed square. -/
theorem beyondSquare_eq_compl (r : ℝ) : beyondSquare r = (closedSquare 0 r)ᶜ := by
  ext x
  simp only [beyondSquare, closedSquare, mem_setOf_eq, mem_compl_iff, supDist_zero, supNorm,
    max_le_iff, not_and_or, not_le]

/-- A bounded set sits inside a closed square about the origin, of nonnegative radius. -/
theorem exists_closedSquare_of_isBounded {s : Set Plane} (hs : Bornology.IsBounded s) :
    ∃ r : ℝ, 0 ≤ r ∧ s ⊆ closedSquare 0 r := by
  obtain ⟨R, hR⟩ := hs.subset_closedBall 0
  refine ⟨max R 0, le_max_right _ _, fun x hx => ?_⟩
  have hnorm : ‖x‖ ≤ R := by simpa using hR hx
  have : supNorm x ≤ R := le_trans (supNorm_le_norm x) hnorm
  simpa [closedSquare, supDist_zero] using le_trans this (le_max_left _ _)

theorem IsCompact.exists_closedSquare {s : Set Plane} (hs : IsCompact s) :
    ∃ r : ℝ, 0 ≤ r ∧ s ⊆ closedSquare 0 r :=
  exists_closedSquare_of_isBounded hs.isBounded

/-- Two squares about the origin merge by taking the larger radius; kept nonnegative so that
callers never split on which is larger. -/
theorem closedSquare_mono {r s : ℝ} (h : r ≤ s) : closedSquare 0 r ⊆ closedSquare 0 s :=
  fun _ hx => le_trans hx h

/-- A finite family of bounded sets is caught inside one square. -/
theorem exists_closedSquare_of_finite {ι : Type*} {S : ι → Set Plane} {t : Set ι}
    (ht : t.Finite) (hS : ∀ i ∈ t, Bornology.IsBounded (S i)) :
    ∃ r : ℝ, 0 ≤ r ∧ (⋃ i ∈ t, S i) ⊆ closedSquare 0 r :=
  exists_closedSquare_of_isBounded ((Bornology.isBounded_biUnion ht).2 hS)

/-- The complement of a finite union of compact sets is open. The exterior of a plane graph —
finitely many vertices and finitely many compact edge arcs — is open for this reason. -/
theorem isOpen_compl_of_finite_isCompact {ι : Type*} {S : ι → Set Plane} {t : Set ι}
    (ht : t.Finite) (hS : ∀ i ∈ t, IsCompact (S i)) : IsOpen (⋃ i ∈ t, S i)ᶜ :=
  (ht.isClosed_biUnion fun i hi => (hS i hi).isClosed).isOpen_compl

end Plane

end Schoenflies

end BundlePart367

section BundlePart368
/- Source: dev/planar_search/schoenflies_port/Schoenflies/Graph/Degree.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/




/-!
# Degree and the handshake lemma

Degree counting on Mathlib's multigraph `Graph α β`, for graphs with finitely many vertices
and finitely many edges.

## Carrying finiteness

`V(G)` and `E(G)` are `Set α` and `Set β`, not types, so finiteness has to be carried
somehow. The choice made here — and inherited by every later graph module — is a
`Prop`-valued class

```
class Graph.Finite (G : Graph α β) : Prop
```

bundling `V(G).Finite` and `E(G).Finite`, with `G.vertexFinset` and `G.edgeFinset` derived
from it. The reasons:

* It is a `Prop`, so it is proof irrelevant. `G.vertexFinset` and `G.degree` therefore do not
  depend on *which* finiteness proof is in scope, and two lemmas proved with different
  instances still compose. A bundled `Finset`-valued structure would not have that property:
  it duplicates the `vertexSet` data and forces a `↑G.vertexFinset = V(G)` side condition at
  every call site.
* It is a class, so it is silent at the call site — the statements below read like ordinary
  graph theory instead of dragging two `Set.Finite` hypotheses through every signature. The
  price is that a subgraph does not get an instance for free; `Graph.Finite.of_le` produces
  one, and `haveI` installs it locally. That is the right trade: in this development
  finiteness is a standing assumption on the ambient graph and subgraphs are formed
  constantly.
* `Finite ↥V(G)` and `Finite ↥E(G)` instances are provided too, so Mathlib's own machinery
  (`Set.Finite.subset`, `Set.toFinite`, ...) fires without help.

Counts are `Set.ncard`. `Set.ncard` is total — it is `0` on an infinite set — so `G.degree`
is defined for every graph and needs no instance argument; finiteness enters only where a
theorem actually needs it.

## Degree

`G.degree x` is the number of *edge ends* at `x`:

```
G.degree x = (G.incidenceSet x).ncard + (G.loopSet x).ncard
```

A non-loop edge at `x` is counted once, by the first summand. A loop at `x` is counted
twice, once by each summand. This is the definition the handshake lemma needs, and it agrees
with `SimpleGraph.degree` on loopless graphs.

## Blueprint

* `Graph.sum_degree_eq_two_mul_ncard_edgeSet` — "the degree sum is twice the number of
  edges", the counting step in the proof of Lemma `lem:three-leaf-tree` (Trees with three
  leaves). The whole content is `Graph.ncard_inc_add_ncard_isLoopAt`: an edge has exactly two
  ends.
* `Graph.IsLeaf` — "the vertices of degree one are the leaves", same lemma.

## Namespace

Everything lives in the root `Graph` namespace rather than in `Schoenflies`, so that dot
notation `G.degree`, `G.IsLeaf`, `G.vertexFinset` works on a `G : Graph α β`. Later graph
modules should do the same.
-/

open scoped Graph

namespace Graph

variable {α β : Type*} {G H : Graph α β} {e f : β} {x y : α}

/-! ### Finiteness -/

/-- `G.Finite` says that the multigraph `G` has finitely many vertices and finitely many
edges. Both halves are needed: the vertex set does not bound the edge set (parallel edges)
and the edge set does not bound the vertex set (isolated vertices). -/
class Finite (G : Graph α β) : Prop where
  /-- A finite graph has finitely many vertices. -/
  finite_vertexSet : V(G).Finite
  /-- A finite graph has finitely many edges. -/
  finite_edgeSet : E(G).Finite

theorem finite_vertexSet (G : Graph α β) [G.Finite] : V(G).Finite := Finite.finite_vertexSet

theorem finite_edgeSet (G : Graph α β) [G.Finite] : E(G).Finite := Finite.finite_edgeSet

instance [G.Finite] : _root_.Finite V(G) := Set.finite_coe_iff.2 (finite_vertexSet G)

instance [G.Finite] : _root_.Finite E(G) := Set.finite_coe_iff.2 (finite_edgeSet G)

/-- A subgraph of a finite graph is finite. This is not an instance — `H` cannot be
recovered from the goal — so install it with `haveI := Graph.Finite.of_le h`. -/
theorem Finite.of_le (h : H ≤ G) [G.Finite] : H.Finite :=
  ⟨(_root_.Graph.finite_vertexSet G).subset h.vertexSet_mono,
   (_root_.Graph.finite_edgeSet G).subset h.edgeSet_mono⟩

/-- The vertex set of a finite graph, as a `Finset`. -/
noncomputable def vertexFinset (G : Graph α β) [G.Finite] : Finset α :=
  (finite_vertexSet G).toFinset

/-- The edge set of a finite graph, as a `Finset`. -/
noncomputable def edgeFinset (G : Graph α β) [G.Finite] : Finset β :=
  (finite_edgeSet G).toFinset

@[simp]
theorem mem_vertexFinset [G.Finite] : x ∈ G.vertexFinset ↔ x ∈ V(G) :=
  Set.Finite.mem_toFinset _

@[simp]
theorem mem_edgeFinset [G.Finite] : e ∈ G.edgeFinset ↔ e ∈ E(G) :=
  Set.Finite.mem_toFinset _

@[simp, norm_cast]
theorem coe_vertexFinset [G.Finite] : (G.vertexFinset : Set α) = V(G) :=
  Set.Finite.coe_toFinset _

@[simp, norm_cast]
theorem coe_edgeFinset [G.Finite] : (G.edgeFinset : Set β) = E(G) :=
  Set.Finite.coe_toFinset _

@[simp]
theorem card_vertexFinset [G.Finite] : G.vertexFinset.card = V(G).ncard := by
  rw [← Set.ncard_coe_finset, coe_vertexFinset]

@[simp]
theorem card_edgeFinset [G.Finite] : G.edgeFinset.card = E(G).ncard := by
  rw [← Set.ncard_coe_finset, coe_edgeFinset]

/-! ### Incidence sets, unfolded -/

theorem incidenceSet_eq_setOf (G : Graph α β) (x : α) : G.incidenceSet x = {e | G.Inc e x} :=
  rfl

theorem loopSet_eq_setOf (G : Graph α β) (x : α) : G.loopSet x = {e | G.IsLoopAt e x} :=
  rfl

theorem finite_incidenceSet [G.Finite] (x : α) : (G.incidenceSet x).Finite :=
  (finite_edgeSet G).subset (G.incidenceSet_subset_edgeSet x)

theorem finite_loopSet [G.Finite] (x : α) : (G.loopSet x).Finite :=
  (finite_incidenceSet x).subset (G.loopSet_subset_incidenceSet x)

/-! ### Degree -/

/-- `G.degree x` is the number of edge ends of `G` at the vertex `x`: a non-loop edge
incident with `x` contributes one, a loop at `x` contributes two. -/
noncomputable def degree (G : Graph α β) (x : α) : ℕ :=
  (G.incidenceSet x).ncard + (G.loopSet x).ncard

theorem degree_def (G : Graph α β) (x : α) :
    G.degree x = (G.incidenceSet x).ncard + (G.loopSet x).ncard := rfl

/-- A vertex outside the graph has no edge ends. -/
@[simp]
theorem degree_eq_zero_of_notMem (h : x ∉ V(G)) : G.degree x = 0 := by
  have h1 : G.incidenceSet x = ∅ := by
    ext e
    simp only [mem_incidenceSet, Set.mem_empty_iff_false, iff_false]
    exact fun hx => h hx.vertex_mem
  have h2 : G.loopSet x = ∅ :=
    Set.eq_empty_of_subset_empty (h1 ▸ G.loopSet_subset_incidenceSet x)
  rw [degree_def, h1, h2]
  simp

/-- Loops are counted among the incident edges as well, so they never make the loop term the
larger of the two. -/
theorem ncard_loopSet_le_ncard_incidenceSet [G.Finite] (x : α) :
    (G.loopSet x).ncard ≤ (G.incidenceSet x).ncard :=
  Set.ncard_le_ncard (G.loopSet_subset_incidenceSet x) (finite_incidenceSet x)

theorem ncard_incidenceSet_le_degree (x : α) : (G.incidenceSet x).ncard ≤ G.degree x :=
  Nat.le_add_right _ _

/-- On a loopless vertex the degree is just the number of incident edges. -/
theorem degree_eq_ncard_incidenceSet (h : ∀ e, ¬ G.IsLoopAt e x) :
    G.degree x = (G.incidenceSet x).ncard := by
  have : G.loopSet x = ∅ := by
    ext e
    simpa using h e
  rw [degree_def, this]
  simp

/-- A loop at `x` contributes two to the degree of `x`. -/
theorem IsLoopAt.two_le_degree [G.Finite] (h : G.IsLoopAt e x) : 2 ≤ G.degree x := by
  have h1 : 1 ≤ (G.loopSet x).ncard :=
    (Set.ncard_pos (finite_loopSet x)).2 ⟨e, h⟩
  have h2 : 1 ≤ (G.incidenceSet x).ncard :=
    (Set.ncard_pos (finite_incidenceSet x)).2 ⟨e, h.inc⟩
  rw [degree_def]
  omega

theorem degree_pos_of_inc [G.Finite] (h : G.Inc e x) : 0 < G.degree x := by
  have : 0 < (G.incidenceSet x).ncard := (Set.ncard_pos (finite_incidenceSet x)).2 ⟨e, h⟩
  rw [degree_def]
  omega

theorem degree_eq_zero_iff [G.Finite] : G.degree x = 0 ↔ ∀ e, ¬ G.Inc e x := by
  refine ⟨fun h e he => ?_, fun h => ?_⟩
  · exact absurd h (degree_pos_of_inc he).ne'
  · have h1 : G.incidenceSet x = ∅ := by
      ext e
      simpa using h e
    have h2 : G.loopSet x = ∅ :=
      Set.eq_empty_of_subset_empty (h1 ▸ G.loopSet_subset_incidenceSet x)
    rw [degree_def, h1, h2]
    simp

/-! ### An edge has exactly two ends

This is the entire content of the handshake lemma: summed over the vertices, the number of
ends an edge has there is two, whether the edge is a loop (two ends at one vertex) or not
(one end at each of two vertices).
-/

/-- An edge of `G` has exactly two ends: the vertices it is incident with, counted again at
the vertex it is a loop at, total two. -/
theorem ncard_inc_add_ncard_isLoopAt (G : Graph α β) (he : e ∈ E(G)) :
    {x | G.Inc e x}.ncard + {x | G.IsLoopAt e x}.ncard = 2 := by
  obtain ⟨u, v, huv⟩ := exists_isLink_of_mem_edgeSet he
  by_cases huv' : u = v
  · -- A loop: one vertex, counted by both summands.
    subst huv'
    have hl : G.IsLoopAt e u := huv
    have h1 : {x | G.Inc e x} = {u} := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      exact ⟨fun h => (hl.eq_of_inc h).symm, fun h => h ▸ hl.inc⟩
    have h2 : {x | G.IsLoopAt e x} = {u} := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      exact ⟨fun h => (hl.eq_of_inc h.inc).symm, fun h => h ▸ hl⟩
    rw [h1, h2]
    simp
  · -- A non-loop: two distinct vertices, one end at each, and no loop anywhere.
    have h1 : {x | G.Inc e x} = {u, v} := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      exact ⟨fun h => h.eq_or_eq_of_isLink huv,
        fun h => h.elim (fun hz => hz ▸ huv.inc_left) (fun hz => hz ▸ huv.inc_right)⟩
    have h2 : {x | G.IsLoopAt e x} = ∅ := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hz
      exact huv' ((hz.eq_of_inc huv.inc_left).symm.trans (hz.eq_of_inc huv.inc_right))
    rw [h1, h2, Set.ncard_pair huv']
    simp

/-! ### The handshake lemma -/

/-- Counting the elements of a set cut out by a predicate, as a sum of indicators over any
`Finset` containing it. This is the bridge between `Set.ncard` and `Finset.sum` used twice in
each direction by the handshake proof. -/
private theorem ncard_setOf_eq_sum_ite {γ : Type*} (s : Finset γ) (p : γ → Prop)
    [DecidablePred p] (hsub : ∀ z, p z → z ∈ s) :
    {z | p z}.ncard = ∑ z ∈ s, if p z then 1 else 0 := by
  rw [← Finset.card_filter p s, ← Set.ncard_coe_finset]
  congr 1
  ext z
  simp only [Finset.coe_filter, Set.mem_setOf_eq]
  exact ⟨fun h => ⟨hsub z h, h⟩, fun h => h.2⟩

/-- **The handshake lemma.** The degrees of the vertices of a finite multigraph add up to
twice the number of edges.

The proof is the double count: `G.degree x` is a sum over the edges of the number of ends
that edge has at `x`, the two sums commute, and each edge contributes exactly two
(`Graph.ncard_inc_add_ncard_isLoopAt`). Loops are allowed — that is exactly what the loop
term in `Graph.degree` buys. -/
theorem sum_degree_eq_two_mul_ncard_edgeSet (G : Graph α β) [G.Finite] :
    ∑ x ∈ G.vertexFinset, G.degree x = 2 * E(G).ncard := by
  classical
  -- `ends e x` is the number of ends of `e` at `x`.
  set ends : β → α → ℕ :=
    fun e x => (if G.Inc e x then 1 else 0) + (if G.IsLoopAt e x then 1 else 0) with hends
  -- Read the degree as a sum over the edges.
  have hdeg : ∀ x, G.degree x = ∑ e ∈ G.edgeFinset, ends e x := by
    intro x
    have h1 : (G.incidenceSet x).ncard = ∑ e ∈ G.edgeFinset, if G.Inc e x then 1 else 0 := by
      rw [incidenceSet_eq_setOf]
      exact ncard_setOf_eq_sum_ite _ _ fun z hz => mem_edgeFinset.2 hz.edge_mem
    have h2 : (G.loopSet x).ncard = ∑ e ∈ G.edgeFinset, if G.IsLoopAt e x then 1 else 0 := by
      rw [loopSet_eq_setOf]
      exact ncard_setOf_eq_sum_ite _ _ fun z hz => mem_edgeFinset.2 hz.edge_mem
    rw [degree_def, h1, h2, hends, ← Finset.sum_add_distrib]
  -- Each edge has exactly two ends among the vertices.
  have hedge : ∀ e ∈ G.edgeFinset, ∑ x ∈ G.vertexFinset, ends e x = 2 := by
    intro e he
    rw [mem_edgeFinset] at he
    have h1 : {x | G.Inc e x}.ncard = ∑ x ∈ G.vertexFinset, if G.Inc e x then 1 else 0 :=
      ncard_setOf_eq_sum_ite _ _ fun z hz => mem_vertexFinset.2 hz.vertex_mem
    have h2 : {x | G.IsLoopAt e x}.ncard
        = ∑ x ∈ G.vertexFinset, if G.IsLoopAt e x then 1 else 0 :=
      ncard_setOf_eq_sum_ite _ _ fun z hz => mem_vertexFinset.2 hz.vertex_mem
    rw [hends, Finset.sum_add_distrib, ← h1, ← h2]
    exact G.ncard_inc_add_ncard_isLoopAt he
  calc ∑ x ∈ G.vertexFinset, G.degree x
      = ∑ x ∈ G.vertexFinset, ∑ e ∈ G.edgeFinset, ends e x := by
        exact Finset.sum_congr rfl fun x _ => hdeg x
    _ = ∑ e ∈ G.edgeFinset, ∑ x ∈ G.vertexFinset, ends e x := Finset.sum_comm
    _ = ∑ _e ∈ G.edgeFinset, 2 := Finset.sum_congr rfl hedge
    _ = 2 * E(G).ncard := by
        rw [Finset.sum_const, card_edgeFinset, smul_eq_mul, Nat.mul_comm]

/-- The handshake lemma, with the edge count as a `Finset` cardinality. -/
theorem sum_degree_eq_two_mul_card_edgeFinset (G : Graph α β) [G.Finite] :
    ∑ x ∈ G.vertexFinset, G.degree x = 2 * G.edgeFinset.card := by
  rw [card_edgeFinset]
  exact G.sum_degree_eq_two_mul_ncard_edgeSet

/-- The degree sum of a finite multigraph is even. -/
theorem even_sum_degree (G : Graph α β) [G.Finite] :
    Even (∑ x ∈ G.vertexFinset, G.degree x) :=
  ⟨E(G).ncard, by rw [G.sum_degree_eq_two_mul_ncard_edgeSet, two_mul]⟩

/-! ### Leaves -/

/-- `G.IsLeaf x` says that `x` is a vertex of `G` with exactly one edge end at it. -/
def IsLeaf (G : Graph α β) (x : α) : Prop := x ∈ V(G) ∧ G.degree x = 1

theorem IsLeaf.mem_vertexSet (h : G.IsLeaf x) : x ∈ V(G) := h.1

theorem IsLeaf.degree_eq_one (h : G.IsLeaf x) : G.degree x = 1 := h.2

theorem isLeaf_iff : G.IsLeaf x ↔ x ∈ V(G) ∧ G.degree x = 1 := Iff.rfl

/-- A leaf carries no loop: a loop would contribute two to the degree. -/
theorem IsLeaf.not_isLoopAt [G.Finite] (h : G.IsLeaf x) (e : β) : ¬ G.IsLoopAt e x := by
  intro hl
  have h2 := hl.two_le_degree
  have hd := h.2
  omega

/-- The one edge end at a leaf comes from one incident edge. -/
theorem IsLeaf.ncard_incidenceSet [G.Finite] (h : G.IsLeaf x) :
    (G.incidenceSet x).ncard = 1 := by
  have hle := ncard_loopSet_le_ncard_incidenceSet (G := G) x
  have hd : (G.incidenceSet x).ncard + (G.loopSet x).ncard = 1 := h.2
  omega

theorem IsLeaf.loopSet_eq_empty [G.Finite] (h : G.IsLeaf x) : G.loopSet x = ∅ := by
  have hle := ncard_loopSet_le_ncard_incidenceSet (G := G) x
  have hd : (G.incidenceSet x).ncard + (G.loopSet x).ncard = 1 := h.2
  have : (G.loopSet x).ncard = 0 := by omega
  exact (Set.ncard_eq_zero (finite_loopSet x)).1 this

/-- A leaf is incident with exactly one edge. -/
theorem IsLeaf.existsUnique_inc [G.Finite] (h : G.IsLeaf x) : ∃! e, G.Inc e x := by
  obtain ⟨e, he⟩ := Set.ncard_eq_one.1 h.ncard_incidenceSet
  refine ⟨e, ?_, fun f hf => ?_⟩
  · have : e ∈ G.incidenceSet x := by rw [he]; rfl
    exact this
  · have : f ∈ G.incidenceSet x := hf
    rw [he] at this
    exact this

/-- The unique edge at a leaf is not a loop, so it has a second, different end. -/
theorem IsLeaf.exists_isLink [G.Finite] (h : G.IsLeaf x) :
    ∃ e y, y ≠ x ∧ G.IsLink e x y := by
  obtain ⟨e, he, -⟩ := h.existsUnique_inc
  obtain ⟨y, hy⟩ := he
  refine ⟨e, y, ?_, hy⟩
  rintro rfl
  exact h.not_isLoopAt e hy

/-- Every edge at a leaf is a non-loop edge there. -/
theorem IsLeaf.isNonloopAt [G.Finite] (h : G.IsLeaf x) (he : G.Inc e x) :
    G.IsNonloopAt e x :=
  he.isLoopAt_or_isNonloopAt.resolve_left (h.not_isLoopAt e)

/-- The converse of the two lemmas above: a vertex of `G` whose only incident edge is `e`,
and for which `e` is not a loop, is a leaf. -/
theorem isLeaf_of_isNonloopAt (hx : x ∈ V(G))
    (h : ∀ f, G.Inc f x ↔ f = e) (hne : G.IsNonloopAt e x) : G.IsLeaf x := by
  refine ⟨hx, ?_⟩
  have h1 : G.incidenceSet x = {e} := by
    ext f
    simpa using h f
  have h2 : G.loopSet x = ∅ := by
    ext f
    simp only [mem_loopSet, Set.mem_empty_iff_false, iff_false]
    intro hf
    exact hne.not_isLoopAt x (((h f).1 hf.inc) ▸ hf)
  rw [degree_def, h1, h2]
  simp

end Graph

end BundlePart368

section BundlePart369
/- Source: dev/planar_search/schoenflies_port/Schoenflies/Graph/Drawing.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/





/-!
# Plane graphs

There is no `PlaneGraph` type. A plane graph is an abstract `G : Graph Plane β` **together
with** a drawing `drawing : β → ℝ → Plane`, related by `IsDrawing G drawing`. The abstract
graph stays itself, so every combinatorial theorem of `Schoenflies/Graph/` applies with
nothing to project through, and "a plane graph realises an abstract finite graph" is true by
construction rather than by a theorem. Bundling would put a record projection inside every
combinatorial citation.

The vertices being plane points is what makes the definition short: that the vertices are
distinct is not a clause, it is what `V(G) : Set Plane` already means.

`IsDrawing` has three clauses. Each edge is drawn by an injective continuous parametrization on
`[0, 1]` whose endpoint values are the two ends of that edge; an edge's arc meets the vertex set
only at those two ends; and two distinct edges meet only at vertices incident with both. The
second and third are the blueprint's "distinct edges of a plane graph meet only at shared
vertices", split so that `unique_edge_at` — away from the vertices a point of the drawing lies
on exactly one edge — falls out directly. That corollary is the form the polygonal overlay
wants.

The first clause names the *parametrization*, not merely its image. The weaker reading — "the
point set of an edge is an arc between its ends" — suffices for everything about faces, and
fails for the polygonal redrawing, which must speak of the last parameter at which an edge is
inside a given square. `edge_isArcBetween` recovers the weaker reading, so consumers needing
only that are unaffected.

## Blueprint

* `IsDrawing` — a plane graph, as an abstract graph plus a drawing.
* `IsDrawing.edge_param`, `IsDrawing.edge_isArcBetween` — the parametrization, and its image.
* `IsDrawing.arcs_meet_at_vertex`, `IsDrawing.unique_edge_at` — distinct edges meet only at
  shared vertices; away from the vertices, a point lies on exactly one edge.
* `pointSet`, `IsDrawing.isCompact_pointSet`, `exterior`, `isOpen_exterior` — what a plane
  graph occupies, and the open set its faces live in.
* `face` — the component of the exterior through a point off the drawing. Named by a point
  rather than indexed, so no face has to be produced before it is spoken about.
-/

open Metric Set Schoenflies unitInterval
open scoped Graph

namespace Graph

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane} {base : Plane}

/-- The point set of a single edge: the image of its parametrization on `[0, 1]`. -/
def edgeArc (drawing : β → ℝ → Plane) (e : β) : Set Plane := drawing e '' I

/-- A drawing of an abstract graph in the plane.

The vertices are already plane points, so a drawing only has to say how the edges run. -/
structure IsDrawing (G : Graph Plane β) (drawing : β → ℝ → Plane) : Prop where
  /-- Each edge is drawn by an injective continuous parametrization on `[0, 1]` whose two
  endpoints are the ends of that edge.

  This says more than "the point set `edgeArc drawing e` is an arc between the ends". That
  weaker clause makes two drawings with the same point sets indistinguishable, which is fine
  for the face theory and useless for the redrawing argument: "the last parameter at which
  this edge is inside the square at `v`" is meaningless unless `drawing e` is itself the
  parametrization. `edge_isArcBetween` below recovers the weaker statement.

  Stated orientation-free — `G.IsLink e (drawing e 0) (drawing e 1)` — because `IsLink` is
  symmetric, so pinning `drawing e 0` to a *named* end of a *given* link would force the two
  ends to coincide. -/
  edge_param : ∀ ⦃e⦄, e ∈ E(G) →
    ContinuousOn (drawing e) I ∧ InjOn (drawing e) I ∧ G.IsLink e (drawing e 0) (drawing e 1)

  /-- An edge's arc meets the vertex set only at its own two ends. -/
  vertex_mem_edgeArc : ∀ ⦃e x y v⦄, G.IsLink e x y → v ∈ V(G) → v ∈ edgeArc drawing e →
    v = x ∨ v = y
  /-- Two distinct edges meet only at vertices incident with both. -/
  edge_inter : ∀ ⦃e f : β⦄, e ∈ E(G) → f ∈ E(G) → e ≠ f →
    ∀ ⦃p⦄, p ∈ edgeArc drawing e → p ∈ edgeArc drawing f →
      p ∈ V(G) ∧ G.Inc e p ∧ G.Inc f p

namespace IsDrawing

/-- The point set of an edge is an arc between its two ends — the weaker reading of
`edge_param`, and the one the face theory uses. -/
theorem edge_isArcBetween (h : IsDrawing G drawing) ⦃e x y⦄ (hl : G.IsLink e x y) :
    IsArcBetween (edgeArc drawing e) x y := by
  obtain ⟨hc, hi, hlink⟩ := h.edge_param hl.edge_mem
  have base : IsArcBetween (edgeArc drawing e) (drawing e 0) (drawing e 1) :=
    ⟨drawing e, hc, hi, rfl, rfl, rfl⟩
  rcases hl.eq_and_eq_or_eq_and_eq hlink with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact base
  · exact base.reverse

theorem isArc_edgeArc (h : IsDrawing G drawing) {e : β} (he : e ∈ E(G)) :
    IsArc (edgeArc drawing e) := by
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
  exact (h.edge_isArcBetween hxy).isArc

theorem isCompact_edgeArc (h : IsDrawing G drawing) {e : β} (he : e ∈ E(G)) :
    IsCompact (edgeArc drawing e) := (h.isArc_edgeArc he).isCompact

/-- The blueprint's "distinct edges of a plane graph meet only at shared vertices". -/
theorem arcs_meet_at_vertex (h : IsDrawing G drawing) {e f : β} (he : e ∈ E(G)) (hf : f ∈ E(G))
    (hef : e ≠ f) {p : Plane} (hpe : p ∈ edgeArc drawing e) (hpf : p ∈ edgeArc drawing f) :
    p ∈ V(G) :=
  (h.edge_inter he hf hef hpe hpf).1

/-- Away from the vertices, a point of the drawing lies on exactly one edge. This is the form
the polygonal overlay wants. -/
theorem unique_edge_at (h : IsDrawing G drawing) {e f : β} (he : e ∈ E(G)) (hf : f ∈ E(G))
    {p : Plane} (hpV : p ∉ V(G)) (hpe : p ∈ edgeArc drawing e) (hpf : p ∈ edgeArc drawing f) :
    e = f := by
  by_contra hef
  exact hpV (h.arcs_meet_at_vertex he hf hef hpe hpf)

end IsDrawing

/-! ### What a plane graph occupies -/

/-- The point set of a plane graph: its vertices together with all of its edge arcs. -/
def pointSet (G : Graph Plane β) (drawing : β → ℝ → Plane) : Set Plane :=
  V(G) ∪ ⋃ e ∈ E(G), edgeArc drawing e

theorem vertexSet_subset_pointSet : V(G) ⊆ pointSet G drawing := subset_union_left

theorem edgeArc_subset_pointSet {e : β} (he : e ∈ E(G)) :
    edgeArc drawing e ⊆ pointSet G drawing :=
  subset_union_of_subset_right (subset_biUnion_of_mem he) _

/-- A finite plane graph occupies a compact set: finitely many points and finitely many
compact arcs. -/
theorem IsDrawing.isCompact_pointSet [G.Finite] (h : IsDrawing G drawing) :
    IsCompact (pointSet G drawing) := by
  refine (Graph.finite_vertexSet (G := G)).isCompact.union ?_
  exact (Graph.finite_edgeSet (G := G)).isCompact_biUnion fun e he => h.isCompact_edgeArc he

theorem IsDrawing.isClosed_pointSet [G.Finite] (h : IsDrawing G drawing) :
    IsClosed (pointSet G drawing) := h.isCompact_pointSet.isClosed

/-- The exterior of a plane graph: everything the drawing does not occupy. -/
def exterior (G : Graph Plane β) (drawing : β → ℝ → Plane) : Set Plane :=
  (pointSet G drawing)ᶜ

theorem IsDrawing.isOpen_exterior [G.Finite] (h : IsDrawing G drawing) :
    IsOpen (exterior G drawing) := h.isClosed_pointSet.isOpen_compl

/-- A face of a plane graph, named by a point of the exterior rather than indexed: no face has
to be produced before it can be spoken about. -/
def face (G : Graph Plane β) (drawing : β → ℝ → Plane) (base : Plane) : Set Plane :=
  connectedComponentIn (exterior G drawing) base

theorem face_subset_exterior (G : Graph Plane β) (drawing : β → ℝ → Plane) (base : Plane) :
    face G drawing base ⊆ exterior G drawing :=
  connectedComponentIn_subset _ _

theorem mem_face (h : base ∈ exterior G drawing) : base ∈ face G drawing base :=
  mem_connectedComponentIn h

theorem IsDrawing.isOpen_face [G.Finite] (h : IsDrawing G drawing) (base : Plane) :
    IsOpen (face G drawing base) :=
  Schoenflies.Plane.isOpen_connectedComponentIn h.isOpen_exterior

theorem isConnected_face (h : base ∈ exterior G drawing) :
    IsConnected (face G drawing base) :=
  ⟨⟨base, mem_face h⟩, isPreconnected_connectedComponentIn⟩

/-- Faces partition the exterior: two faces either coincide or are disjoint. -/
theorem face_eq_or_disjoint (b c : Plane) :
    face G drawing b = face G drawing c ∨ Disjoint (face G drawing b) (face G drawing c) := by
  by_cases h : (face G drawing b ∩ face G drawing c).Nonempty
  · obtain ⟨z, hzb, hzc⟩ := h
    left
    rw [face, face, connectedComponentIn_eq hzb, connectedComponentIn_eq hzc]
  · right
    exact Set.disjoint_iff_inter_eq_empty.2 (not_nonempty_iff_eq_empty.1 h)

end Graph

end BundlePart369

section BundlePart370
/- Source: Papers/GraphicalZonotopes/PlanarDrawing.lean -/








@[expose] public section
noncomputable section
open scoped Classical Graph

namespace Graph.IsDrawing

/-- A genuine drawing restricts to every subgraph, using the same edge arcs. -/
theorem restrictSimpleAdapter {β : Type*} {G H : Graph Schoenflies.Plane β}
    {drawing : β → ℝ → Schoenflies.Plane} (h : Graph.IsDrawing G drawing)
    (hHG : H ≤ G) : Graph.IsDrawing H drawing := by
  constructor
  · intro e he
    obtain ⟨hc,hi,hl⟩ := h.edge_param (hHG.edgeSet_mono he)
    exact ⟨hc,hi,(hHG.isLink_iff he).mpr hl⟩
  · intro e x y v hl hv hve
    exact h.vertex_mem_edgeArc (hl.mono hHG) (hHG.vertexSet_mono hv) hve
  · intro e f he hf hef p hpe hpf
    obtain ⟨_,hie,hif⟩ := h.edge_inter (hHG.edgeSet_mono he)
      (hHG.edgeSet_mono hf) hef hpe hpf
    have hie' : H.Inc e p := (hHG.inc_congr he).mpr hie
    have hif' : H.Inc f p := (hHG.inc_congr hf).mpr hif
    exact ⟨hie'.vertex_mem,hie',hif'⟩

end Graph.IsDrawing

namespace GraphicalZonotopes
namespace PlaneDrawing

variable {V : Type*}

/-- Transport an ordinary simple graph to actual points of the Euclidean plane.
The edge names remain precisely the unordered pairs of the original vertices. -/
def planeGraph (G : SimpleGraph V) (p : V → Schoenflies.Plane) :
    Graph Schoenflies.Plane (Sym2 V) := (Graph.ofSimpleGraph G).map p

@[simp] theorem planeGraph_vertexSet (G : SimpleGraph V) (p : V → Schoenflies.Plane) :
    V(planeGraph G p) = Set.range p := by
  simp [planeGraph]

@[simp] theorem planeGraph_edgeSet (G : SimpleGraph V) (p : V → Schoenflies.Plane) :
    E(planeGraph G p) = G.edgeSet := rfl

@[simp] theorem planeGraph_isLink (G : SimpleGraph V) (p : V → Schoenflies.Plane)
    (hp : Function.Injective p) (e : Sym2 V) (u v : V) :
    (planeGraph G p).IsLink e (p u) (p v) ↔ e = s(u,v) ∧ G.Adj u v := by
  constructor
  · rintro ⟨a,b,⟨he,hE⟩,ha,hb⟩
    have hau : a = u := hp ha
    have hbv : b = v := hp hb
    subst a; subst b
    exact ⟨he,by simpa [he] using hE⟩
  · rintro ⟨rfl,huv⟩
    exact ⟨u,v,⟨rfl,by simpa using huv⟩,rfl,rfl⟩

/-- An injective point placement preserves looplessness and uniqueness of edges. -/
theorem planeGraph_simple (G : SimpleGraph V) (p : V → Schoenflies.Plane)
    (hp : Function.Injective p) : (planeGraph G p).Simple where
  not_isLoopAt e x := by
    rintro ⟨u,v,⟨he,hE⟩,hu,hv⟩
    have huv : u = v := hp (hu.trans hv.symm)
    subst v
    simpa [he] using hE
  eq_of_isLink := by
    rintro e f x y ⟨u,v,⟨he,hE⟩,hu,hv⟩ ⟨a,b,⟨hf,hF⟩,ha,hb⟩
    have hua : u = a := hp (hu.trans ha.symm)
    have hvb : v = b := hp (hv.trans hb.symm)
    subst a; subst b
    exact he.trans hf.symm

instance planeGraph_finite [Finite V] (G : SimpleGraph V)
    (p : V → Schoenflies.Plane) : (planeGraph G p).Finite where
  finite_vertexSet := by rw [planeGraph_vertexSet]; exact Set.finite_range p
  finite_edgeSet := Set.toFinite _

@[simp] theorem planeGraph_vertex_ncard [Fintype V] (G : SimpleGraph V)
    (p : V → Schoenflies.Plane) (hp : Function.Injective p) :
    V(planeGraph G p).ncard = Fintype.card V := by
  rw [planeGraph_vertexSet,Set.ncard_range_of_injective hp,Nat.card_eq_fintype_card]

@[simp] theorem planeGraph_edge_ncard [Fintype V] (G : SimpleGraph V)
    (p : V → Schoenflies.Plane) : E(planeGraph G p).ncard = G.edgeFinset.card := by
  classical
  rw [planeGraph_edgeSet,← G.coe_edgeFinset,Set.ncard_coe_finset]

theorem ofSimpleGraph_mono {G H : SimpleGraph V} (h : G ≤ H) :
    Graph.ofSimpleGraph G ≤ Graph.ofSimpleGraph H := by
  constructor
  · exact Set.Subset.rfl
  · rintro e u v ⟨rfl,he⟩
    exact ⟨rfl,by simpa using h (show G.Adj u v by simpa using he)⟩

theorem planeGraph_mono {G H : SimpleGraph V} (h : G ≤ H)
    (p : V → Schoenflies.Plane) : planeGraph G p ≤ planeGraph H p :=
  (ofSimpleGraph_mono h).map p

end PlaneDrawing

/-- Planarity in its geometric sense: an injective placement of the vertices in
ℝ² and simple continuous edge arcs meeting only at their common endpoints.
This uses the genuine drawing predicate from the Jordan–Schönflies library. -/
def HasPlaneDrawing {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ p : V → Schoenflies.Plane, Function.Injective p ∧
    ∃ drawing : Sym2 V → ℝ → Schoenflies.Plane,
      Graph.IsDrawing (PlaneDrawing.planeGraph G p) drawing

theorem HasPlaneDrawing.mono {V : Type*} {G H : SimpleGraph V}
    (hG : HasPlaneDrawing G) (hHG : H ≤ G) : HasPlaneDrawing H := by
  obtain ⟨p,hp,drawing,hd⟩ := hG
  exact ⟨p,hp,drawing,hd.restrictSimpleAdapter (PlaneDrawing.planeGraph_mono hHG p)⟩

end GraphicalZonotopes

end
end
end BundlePart370

section BundlePart371
/- Source: Papers/GraphicalZonotopes/ArcK5Definitions.lean -/


open Set Schoenflies

namespace Graph

/-- Five distinct points joined pairwise by simple plane arcs that meet only at
common endpoints.  Ordered pairs give the same arc after reversal.  This is an
actual geometric configuration, including when one arc is a subdivided graph path. -/
structure IsArcK5 (x : Fin 5 → Plane) (P : Fin 5 → Fin 5 → Set Plane) : Prop where
  injective : Function.Injective x
  arc : ∀ i j, i ≠ j → IsArcBetween (P i j) (x i) (x j)
  symm : ∀ i j, P i j = P j i
  vertex : ∀ i j k, i ≠ j → x k ∈ P i j → k = i ∨ k = j
  meet : ∀ i j k l, i ≠ j → k ≠ l →
    (i, j) ≠ (k, l) → (i, j) ≠ (l, k) →
    P i j ∩ P k l ⊆ ({x i, x j} : Set Plane) ∩ ({x k, x l} : Set Plane)

end Graph

end BundlePart371

section BundlePart372
/- Source: dev/planar_search/schoenflies_port/Schoenflies/Concatenate.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/


/-!
# Gluing arcs

Two arcs meeting only at the endpoint they share glue to one arc; two arcs meeting at *both*
of their ends glue to a Jordan curve. The glued parametrisation runs the first arc over the
lower half of the parameter interval and the second over the upper half, each at double
speed: `t ↦ f (2 * t)` below the midpoint and `t ↦ g (2 * t - 1)` above it. Since the
parameter here is an honest real number, that is literally what the definition says.

The halves are `[0, 1/2]` and `[1/2, 1]`. They cover the interval, and each is closed, so
continuity is Mathlib's pasting lemma `ContinuousOn.union_of_isClosed`. Injectivity splits
four ways — both parameters below the midpoint, both above, and the two mixed orders — and
only the mixed cases use the hypothesis that the two arcs meet nowhere else: there the common
value lies on both arcs, hence is the shared endpoint, and each arc's own injectivity pins
its parameter to the midpoint.

At the midpoint itself both branches of the `if` are meaningful and they agree, precisely
because the first arc finishes where the second starts. That is what makes the glued map well
defined rather than merely continuous, and it is why `concatenate_upperHalf` — the statement
that the glued map *is* the retimed second arc on the whole closed upper half, midpoint
included — carries the shared-endpoint hypothesis.

For the loop the seam analysis gains a second legitimate meeting point: besides the middle,
where the arcs are glued, there are the outer ends, where the loop is allowed to repeat
itself. Pinning those needs the start/finish counterparts of the midpoint lemmas.

## Blueprint

* `concatenate` — §1, the glued parametrisation.
* `IsArc.concatenate`, `IsArcBetween.concatenate` — two arcs meeting only at the endpoint they
  share glue to an arc.
* `IsLoop.concatenate` — two arcs glued along both of their ends make a loop.
* `IsJordanCurve.of_two_arcs` — two arcs meeting exactly at their two shared endpoints make a
  Jordan curve; the converse of the two-arcs decomposition, and the form every *construction*
  of a curve takes.
-/

open Set unitInterval

namespace Schoenflies

/-! ### The two halves of the parameter interval -/

/-- The lower half of the parameter interval, where the first arc runs. -/
def lowerHalf : Set ℝ := Icc 0 (1 / 2)

/-- The upper half of the parameter interval, where the second arc runs. The two halves
overlap in the midpoint: that is the seam. -/
def upperHalf : Set ℝ := Icc (1 / 2) 1

theorem lowerHalf_subset_I : lowerHalf ⊆ I := Icc_subset_Icc le_rfl (by norm_num)

theorem upperHalf_subset_I : upperHalf ⊆ I := Icc_subset_Icc (by norm_num) le_rfl

theorem halves_union : lowerHalf ∪ upperHalf = I :=
  Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)

theorem isClosed_lowerHalf : IsClosed lowerHalf := isClosed_Icc

theorem isClosed_upperHalf : IsClosed upperHalf := isClosed_Icc

/-- Doubling a parameter below the midpoint reaches at most one. -/
theorem double_mem_I {t : ℝ} (ht : t ∈ lowerHalf) : 2 * t ∈ I :=
  ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- Doubling a parameter above the midpoint and stepping back reaches at least zero. -/
theorem doubleBack_mem_I {t : ℝ} (ht : t ∈ upperHalf) : 2 * t - 1 ∈ I :=
  ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-! ### The glued parametrisation -/

/-- Run `f` over the lower half of the interval and `g` over the upper half, each at double
speed. -/
noncomputable def concatenate (f g : ℝ → Plane) : ℝ → Plane :=
  fun t => if t ≤ 1 / 2 then f (2 * t) else g (2 * t - 1)

variable {f g : ℝ → Plane}

theorem concatenate_of_le {t : ℝ} (ht : t ≤ 1 / 2) : concatenate f g t = f (2 * t) :=
  if_pos ht

theorem concatenate_of_not_le {t : ℝ} (ht : ¬t ≤ 1 / 2) :
    concatenate f g t = g (2 * t - 1) :=
  if_neg ht

theorem concatenate_zero : concatenate f g 0 = f 0 := by
  rw [concatenate_of_le (by norm_num)]
  norm_num

theorem concatenate_one : concatenate f g 1 = g 1 := by
  rw [concatenate_of_not_le (by norm_num)]
  norm_num

/-- On the *closed* upper half the glued map is the retimed second arc — at the midpoint
included, where the `if` still takes the first branch. The two branches agree there only
because the first arc finishes where the second starts, which is what makes the glued map
well defined. -/
theorem concatenate_upperHalf (hmid : f 1 = g 0) {t : ℝ} (ht : t ∈ upperHalf) :
    concatenate f g t = g (2 * t - 1) := by
  by_cases h : t ≤ 1 / 2
  · -- The only parameter of the upper half below the midpoint is the midpoint.
    have : t = 1 / 2 := le_antisymm h ht.1
    subst this
    rw [concatenate_of_le h]
    norm_num
    exact hmid
  · exact concatenate_of_not_le h

/-! ### Continuity -/

/-- Continuity of the glued map: each half carries a composition, and the halves are closed
and cover. -/
theorem continuousOn_concatenate (hf : ContinuousOn f I) (hg : ContinuousOn g I)
    (hmid : f 1 = g 0) : ContinuousOn (concatenate f g) I := by
  rw [← halves_union]
  refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_lowerHalf isClosed_upperHalf
  · -- On the lower half the glued map is `f` doubled.
    have h : ContinuousOn (fun t : ℝ => f (2 * t)) lowerHalf :=
      hf.comp (by fun_prop) fun t ht => double_mem_I ht
    exact h.congr fun t ht => concatenate_of_le ht.2
  · -- On the upper half it is `g`, doubled and stepped back.
    have h : ContinuousOn (fun t : ℝ => g (2 * t - 1)) upperHalf :=
      hg.comp (by fun_prop) fun t ht => doubleBack_mem_I ht
    exact h.congr fun t ht => concatenate_upperHalf hmid ht

/-! ### Pinning a parameter at the seam

At a point where two of the pieces meet, the value is one of the shared points, and the
injectivity of the arc it belongs to pins the parameter. Each half needs its own statement,
since they retime differently; the loop needs the outer ends as well as the middle. -/

theorem lowerHalf_at_finish (hfi : InjOn f I) {t : ℝ} (ht : t ∈ lowerHalf)
    (h : f (2 * t) = f 1) : t = 1 / 2 := by
  have := hfi (double_mem_I ht) one_mem_I h
  linarith

theorem lowerHalf_at_start (hfi : InjOn f I) {t : ℝ} (ht : t ∈ lowerHalf)
    (h : f (2 * t) = f 0) : t = 0 := by
  have := hfi (double_mem_I ht) zero_mem_I h
  linarith

theorem upperHalf_at_start (hgi : InjOn g I) {t : ℝ} (ht : t ∈ upperHalf)
    (h : g (2 * t - 1) = g 0) : t = 1 / 2 := by
  have := hgi (doubleBack_mem_I ht) zero_mem_I h
  linarith

theorem upperHalf_at_finish (hgi : InjOn g I) {t : ℝ} (ht : t ∈ upperHalf)
    (h : g (2 * t - 1) = g 1) : t = 1 := by
  have := hgi (doubleBack_mem_I ht) one_mem_I h
  linarith

/-! ### Injectivity -/

/-- Across the seam: the common value lies on both arcs, so it is the shared endpoint, and
each half's injectivity pins its own parameter to the midpoint. Stated for a parameter of
each half rather than for `x` and `y`, so that the two orderings of the case split are the
same theorem. -/
theorem concatenate_seam (hfi : InjOn f I) (hgi : InjOn g I) (hmid : f 1 = g 0)
    (hmeet : ∀ z ∈ f '' I, z ∈ g '' I → z = f 1) {x y : ℝ}
    (hx : x ∈ lowerHalf) (hy : y ∈ upperHalf)
    (h : concatenate f g x = concatenate f g y) : x = y := by
  rw [concatenate_of_le hx.2, concatenate_upperHalf hmid hy] at h
  have hz : f (2 * x) = f 1 :=
    hmeet _ ⟨2 * x, double_mem_I hx, rfl⟩ ⟨2 * y - 1, doubleBack_mem_I hy, h.symm⟩
  have hy' : g (2 * y - 1) = g 0 := by rw [← h, hz]; exact hmid
  rw [lowerHalf_at_finish hfi hx hz, upperHalf_at_start hgi hy hy']

/-- Two arcs meeting only at the endpoint they share glue to an injective map. -/
theorem injOn_concatenate (hfi : InjOn f I) (hgi : InjOn g I) (hmid : f 1 = g 0)
    (hmeet : ∀ z ∈ f '' I, z ∈ g '' I → z = f 1) : InjOn (concatenate f g) I := by
  intro x hx y hy h
  rcases le_or_gt x (1 / 2) with hxl | hxg
  · rcases le_or_gt y (1 / 2) with hyl | hyg
    · -- Both parameters run the first arc: its own injectivity, doubled.
      rw [concatenate_of_le hxl, concatenate_of_le hyl] at h
      have := hfi (double_mem_I ⟨hx.1, hxl⟩) (double_mem_I ⟨hy.1, hyl⟩) h
      linarith
    · exact concatenate_seam hfi hgi hmid hmeet ⟨hx.1, hxl⟩ ⟨hyg.le, hy.2⟩ h
  · rcases le_or_gt y (1 / 2) with hyl | hyg
    · exact (concatenate_seam hfi hgi hmid hmeet ⟨hy.1, hyl⟩ ⟨hxg.le, hx.2⟩ h.symm).symm
    · -- Both run the second arc.
      rw [concatenate_of_not_le (not_le.2 hxg), concatenate_of_not_le (not_le.2 hyg)] at h
      have := hgi (doubleBack_mem_I ⟨hxg.le, hx.2⟩) (doubleBack_mem_I ⟨hyg.le, hy.2⟩) h
      linarith

/-! ### What the glued map covers -/

/-- Each half retimes *onto* the whole interval, so the glued map's image is exactly the two
arcs together. -/
theorem image_concatenate (hmid : f 1 = g 0) : concatenate f g '' I = f '' I ∪ g '' I := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    rcases le_or_gt t (1 / 2) with h | h
    · exact Or.inl ⟨2 * t, double_mem_I ⟨ht.1, h⟩, (concatenate_of_le h).symm⟩
    · exact Or.inr ⟨2 * t - 1, doubleBack_mem_I ⟨h.le, ht.2⟩,
        (concatenate_of_not_le (not_le.2 h)).symm⟩
  · rintro (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
    · -- Half a parameter is the one that doubles to it.
      refine ⟨u / 2, ⟨by linarith [hu.1], by linarith [hu.2]⟩, ?_⟩
      rw [concatenate_of_le (by linarith [hu.2])]
      congr 1
      ring
    · refine ⟨(u + 1) / 2, ⟨by linarith [hu.1], by linarith [hu.2]⟩, ?_⟩
      rw [concatenate_upperHalf hmid ⟨by linarith [hu.1], by linarith [hu.2]⟩]
      congr 1
      ring

/-! ### The set-level gluing theorems

This is the form the rest of the development speaks: a piece is an arc between two named
points, the parametrisations are chosen inside the proofs and never seen again. -/

/-- Two pieces meeting only at the point where they are joined make one piece. -/
theorem IsArcBetween.concatenate {A B : Set Plane} {a b c : Plane} (hA : IsArcBetween A a b)
    (hB : IsArcBetween B b c) (hmeet : ∀ z ∈ A, z ∈ B → z = b) :
    IsArcBetween (A ∪ B) a c := by
  obtain ⟨f, hfc, hfi, hfim, hf0, hf1⟩ := hA
  obtain ⟨g, hgc, hgi, hgim, hg0, hg1⟩ := hB
  have hmid : f 1 = g 0 := by rw [hf1, hg0]
  have hmeet' : ∀ z ∈ f '' I, z ∈ g '' I → z = f 1 := by
    intro z hz hz'
    rw [hfim] at hz
    rw [hgim] at hz'
    rw [hf1]
    exact hmeet z hz hz'
  refine ⟨_, continuousOn_concatenate hfc hgc hmid, injOn_concatenate hfi hgi hmid hmeet',
    ?_, ?_, ?_⟩
  · rw [image_concatenate hmid, hfim, hgim]
  · rw [concatenate_zero]; exact hf0
  · rw [concatenate_one]; exact hg1

/-- Two arcs meeting only at the endpoint they share glue to an arc. -/
theorem IsArc.concatenate {A B : Set Plane} {a b c : Plane} (hA : IsArcBetween A a b)
    (hB : IsArcBetween B b c) (hmeet : ∀ z ∈ A, z ∈ B → z = b) : IsArc (A ∪ B) :=
  (hA.concatenate hB hmeet).isArc

/-! ### Closing the loop

Two arcs that share *both* of their ends — the second runs back from where the first arrived
to where it set out — glue to a loop rather than to an arc. Everything above carries over
except the seam analysis: a common value now has two ways to be legitimate, at the middle
where the arcs are glued and at the outer ends where the loop closes, and the second of those
is exactly the repetition `IsLoop` allows itself at the finish. -/

/-- Across the seam, when the two arcs also share their outer ends. At the middle the
argument is the one for arcs; at the outer ends the second arc is at its finish, so its
parameter is `1` — which the hypothesis has excluded. -/
theorem concatenate_seam_loop (hfi : InjOn f I) (hgi : InjOn g I) (hmid : f 1 = g 0)
    (hclose : g 1 = f 0)
    (hmeet : ∀ z ∈ f '' I, z ∈ g '' I → z = f 0 ∨ z = f 1) {x y : ℝ}
    (hx : x ∈ lowerHalf) (hy : y ∈ upperHalf) (hy1 : y ≠ 1)
    (h : concatenate f g x = concatenate f g y) : x = y := by
  rw [concatenate_of_le hx.2, concatenate_upperHalf hmid hy] at h
  rcases hmeet _ ⟨2 * x, double_mem_I hx, rfl⟩ ⟨2 * y - 1, doubleBack_mem_I hy, h.symm⟩ with
    hz | hz
  · -- The value is where the loop closes: the second arc is at its finish, so `y = 1`.
    exact absurd (upperHalf_at_finish hgi hy (by rw [← h, hz]; exact hclose.symm)) hy1
  · have hy' : g (2 * y - 1) = g 0 := by rw [← h, hz]; exact hmid
    rw [lowerHalf_at_finish hfi hx hz, upperHalf_at_start hgi hy hy']

/-- Two arcs glued along both of their ends make a loop. -/
theorem IsLoop.concatenate (hfc : ContinuousOn f I) (hfi : InjOn f I) (hgc : ContinuousOn g I)
    (hgi : InjOn g I) (hmid : f 1 = g 0) (hclose : g 1 = f 0)
    (hmeet : ∀ z ∈ f '' I, z ∈ g '' I → z = f 0 ∨ z = f 1) :
    IsLoop (Schoenflies.concatenate f g) where
  continuousOn := continuousOn_concatenate hfc hgc hmid
  closes := by rw [concatenate_zero, concatenate_one]; exact hclose.symm
  injOn := by
    intro x hx y hy h
    have hy1 : y ≠ 1 := ne_of_lt hy.2
    have hx1 : x ≠ 1 := ne_of_lt hx.2
    rcases le_or_gt x (1 / 2) with hxl | hxg
    · rcases le_or_gt y (1 / 2) with hyl | hyg
      · rw [concatenate_of_le hxl, concatenate_of_le hyl] at h
        have := hfi (double_mem_I ⟨hx.1, hxl⟩) (double_mem_I ⟨hy.1, hyl⟩) h
        linarith
      · exact concatenate_seam_loop hfi hgi hmid hclose hmeet ⟨hx.1, hxl⟩
          ⟨hyg.le, hy.2.le⟩ hy1 h
    · rcases le_or_gt y (1 / 2) with hyl | hyg
      · exact (concatenate_seam_loop hfi hgi hmid hclose hmeet ⟨hy.1, hyl⟩
          ⟨hxg.le, hx.2.le⟩ hx1 h.symm).symm
      · rw [concatenate_of_not_le (not_le.2 hxg), concatenate_of_not_le (not_le.2 hyg)] at h
        have := hgi (doubleBack_mem_I ⟨hxg.le, hx.2.le⟩)
          (doubleBack_mem_I ⟨hyg.le, hy.2.le⟩) h
        linarith

/-- Two pieces meeting exactly at their two shared endpoints make a Jordan curve. This is the
converse of the two-arcs decomposition, and the form every construction of a curve takes: a
cycle of a plane graph arrives as a path and one more edge back to where it started. -/
theorem IsJordanCurve.of_two_arcs {A B : Set Plane} {a b : Plane} (hA : IsArcBetween A a b)
    (hB : IsArcBetween B b a) (hmeet : ∀ z ∈ A, z ∈ B → z = a ∨ z = b) :
    IsJordanCurve (A ∪ B) := by
  obtain ⟨f, hfc, hfi, hfim, hf0, hf1⟩ := hA
  obtain ⟨g, hgc, hgi, hgim, hg0, hg1⟩ := hB
  have hmid : f 1 = g 0 := by rw [hf1, hg0]
  have hclose : g 1 = f 0 := by rw [hg1, hf0]
  have hmeet' : ∀ z ∈ f '' I, z ∈ g '' I → z = f 0 ∨ z = f 1 := by
    intro z hz hz'
    rw [hfim] at hz
    rw [hgim] at hz'
    rw [hf0, hf1]
    exact hmeet z hz hz'
  refine ⟨_, IsLoop.concatenate hfc hfi hgc hgi hmid hclose hmeet', ?_⟩
  rw [image_concatenate hmid, hfim, hgim]

end Schoenflies

end BundlePart372
