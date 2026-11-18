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

public import verified.parts.part027
import all verified.parts.part027

@[expose] public section

set_option debug.skipKernelTC false
set_option linter.all false
set_option Elab.async false
set_option internal.cmdlineSnapshots true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

section BundlePart386
/- Source: dev/planar_search/schoenflies_port/Schoenflies/Graph/Redrawing.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/






/-!
# The polygonal redrawing of a finite plane graph

Bricks B7 and B8 of `lem:polygonal-redrawing`, and the headline theorem: every finite plane
graph is drawn again, on the same abstract graph and the same vertices, with polygonal edges.
Since the vertices of a plane graph *are* plane points and the redrawing leaves them where
they are, the blueprint's "isomorphic plane drawing" is the identity isomorphism, and no
`Graph.IsIsomorphism` is built or needed.

## Three things the design did not have, and this module supplies

**Simple polygonal paths.** `Graph.IsDrawing.edge_param` asks for an *injective*
parametrisation, and brick B6 delivers only a `poly` vertex list, which may cross itself. The
blueprint's Lemma 1.1 makes the path simple "by subdividing at self-intersections and taking a
simple path in the resulting finite graph"; `Schoenflies/PolyPath.lean` deferred that half, and
without it brick B8 cannot discharge the drawing condition at all. `IsArcList` and
`PolyReaches.exists_arcList` supply it, by an induction over the inductive relation rather than
by an overlay graph: at each `step` the new segment is run *backwards* from its far end and
stopped the first time it meets the polygon already built, and the old path is truncated
there. That needs no plane geometry beyond `exists_first_mem_Icc`, and in particular no
connectivity theorem for the overlay graph.

**The contact point is on the frame.** `Graph.IsDrawing.exists_core` states that the core meets
the square about a vertex in exactly one point, but not that this point is on the square's
boundary — and if it were interior the core would not lie in the plane minus the open squares,
which is the carrier brick B5 speaks about, nor would the radial segment from the vertex reach
it. `Plane.supDist_eq_of_inter_eq_singleton` closes the gap by connectedness: an interior
contact point would make the core's trace on the square a nonempty proper clopen piece.

**Radial arithmetic.** That two radials of one square meet only at the centre, and that a
radial meets the plane minus the open squares only at its far end, are both the statement that
the sup distance to the centre is a faithful coordinate along a radius
(`Plane.supDist_lt_of_mem_segment`, `Plane.radial_meet`). These are the "distinct radials in
one square meet only at `v`" and "radials meet the replacement paths only at the designated
boundary points" of brick B8's design, and neither is free.

## Blueprint

Bricks B7 and B8 of `lem:polygonal-redrawing` (H6), and the lemma itself.

* `Plane.supNorm_smul`, `Plane.supDist_add_smul`, `Plane.supDist_lt_of_mem_segment`,
  `Plane.segment_subset_closedSquare`, `Plane.radial_meet` — the radial segments of brick B8.
* `Plane.supDist_eq_of_inter_eq_singleton` — a core's contact point lies on the frame of its
  square; the missing clause of brick B4.
* `lastP`, `poly_snoc`, `IsArcList` — a **simple** polygonal path, in the `u :: t`
  presentation that keeps every statement free of dependent nonemptiness proofs.
* `isArcBetween_poly` — the carrier of a simple polygonal path is an arc between its ends.
* `IsArcList.truncate`, `IsArcList.snoc` — cutting one at any of its points, and extending one
  by a segment that touches it only at its last vertex.
* `PolyReaches.exists_arcList` — **every polygonal path contains a simple one**; the deferred
  half of Lemma 1.1.
* `Graph.polygonal_redrawing` — `lem:polygonal-redrawing`, with bricks B7 and B8 inside its
  proof: the `ε` making the tubes about the cores pairwise disjoint, the component `U e` of
  the core inside its tube, and the assembly of radial, replacement path and radial.
-/

open Metric Set unitInterval
open scoped Graph

namespace Schoenflies

/-! ### Radial segments in a square

A segment from the centre of a square to a point of its boundary frame leaves the open square
only at its far end, and two such segments in one square meet only at the centre. Those two
facts are the whole of the "radials" half of brick B8, and both are statements about the sup
distance scaling along a segment. -/

namespace Plane

theorem supNorm_smul (a : ℝ) (x : Plane) : supNorm (a • x) = |a| * supNorm x := by
  have h0 : (a • x) 0 = a * x 0 := by simp
  have h1 : (a • x) 1 = a * x 1 := by simp
  simp only [supNorm, h0, h1, abs_mul]
  exact (mul_max_of_nonneg _ _ (abs_nonneg a)).symm

theorem supDist_add_smul (c u : Plane) (t : ℝ) : supDist (c + t • u) c = |t| * supNorm u := by
  have h : c + t • u - c = t • u := by abel
  rw [supDist, h, supNorm_smul]

/-- Everything on the segment from `c` to `p` except `p` itself is strictly nearer to `c` than
`p` is, in the sup metric. This is why a radial segment meets the frame of its square only at
its far end. -/
theorem supDist_lt_of_mem_segment {c p x : Plane} (hpc : 0 < supDist p c)
    (hx : x ∈ segment ℝ c p) (hne : x ≠ p) : supDist x c < supDist p c := by
  rw [segment_eq_image' ℝ c p] at hx
  obtain ⟨t, ht, hxt⟩ := hx
  have hxt' : c + t • (p - c) = x := hxt
  have hval : supDist x c = t * supDist p c := by
    rw [← hxt', supDist_add_smul, abs_of_nonneg ht.1]; rfl
  have ht1 : t < 1 := by
    rcases eq_or_lt_of_le ht.2 with heq | h
    · refine absurd ?_ hne
      rw [← hxt', heq]
      module
    · exact h
  rw [hval]
  nlinarith

/-- A radial segment stays inside its square. -/
theorem openSquare_subset_closedSquare (c : Plane) (r : ℝ) :
    openSquare c r ⊆ closedSquare c r := fun x hx => show supDist x c ≤ r from le_of_lt hx

theorem segment_subset_closedSquare {c p : Plane} {r : ℝ} (hr : 0 ≤ r)
    (hpc : supDist p c ≤ r) : segment ℝ c p ⊆ closedSquare c r :=
  (convex_closedSquare c r).segment_subset (mem_closedSquare_self c hr) hpc

/-- **Two radials meet only at the centre.** Two segments from the centres of two squares of a
common radius `r` to points of their frames meet only where they can: if the centres are
distinct the squares are disjoint, and if they agree the two far ends are pinned by the sup
distance, which is injective along a radius. -/
theorem radial_meet {c c' p p' z : Plane} {r : ℝ} (hr : 0 < r) (hp : supDist p c = r)
    (hp' : supDist p' c' = r) (hpp' : p ≠ p')
    (hdisj : c ≠ c' → Disjoint (closedSquare c r) (closedSquare c' r))
    (hz : z ∈ segment ℝ c p) (hz' : z ∈ segment ℝ c' p') : z = c := by
  rcases eq_or_ne c c' with rfl | hcc'
  · -- One square: the two representations of `z` have the same parameter, which must be `0`.
    rw [segment_eq_image' ℝ c p] at hz
    rw [segment_eq_image' ℝ c p'] at hz'
    obtain ⟨t, ht, hzt⟩ := hz
    obtain ⟨s, hs, hzs⟩ := hz'
    have hzt' : c + t • (p - c) = z := hzt
    have hzs' : c + s • (p' - c) = z := hzs
    have h₁ : supDist z c = t * r := by
      rw [← hzt', supDist_add_smul, abs_of_nonneg ht.1, ← hp]; rfl
    have h₂ : supDist z c = s * r := by
      rw [← hzs', supDist_add_smul, abs_of_nonneg hs.1, ← hp']; rfl
    have hEq : t = s := mul_right_cancel₀ hr.ne' (h₁.symm.trans h₂)
    subst hEq
    have hsmul : t • (p - c) = t • (p' - c) := add_left_cancel (hzt'.trans hzs'.symm)
    have hkey : t • (p - p') = 0 := by linear_combination (norm := module) hsmul
    rcases smul_eq_zero.1 hkey with ht0 | hpp
    · rw [← hzt', ht0]; module
    · exact absurd (sub_eq_zero.1 hpp) hpp'
  · exact absurd (Set.disjoint_left.1 (hdisj hcc')
      (segment_subset_closedSquare hr.le hp.le hz)
      (segment_subset_closedSquare hr.le hp'.le hz')) not_false

end Plane

/-! ### Simple polygonal paths

`poly vs` is the carrier of a vertex list, and a general vertex list crosses itself. The
drawing condition of a plane graph asks for an *injective* parametrisation, so what brick B8
needs is a vertex list whose carrier is an **arc**. `IsArcList` is exactly the condition that
makes the concatenation of `Schoenflies/Concatenate.lean` apply at every step: consecutive
vertices differ, and each segment meets the rest of the polygon only at the vertex they
share.

The work of this section is `PolyReaches.exists_arcList`: *any* polygonal path inside a set
contains a simple one with the same ends. That is the half of the blueprint's Lemma 1.1 which
`Schoenflies/PolyPath.lean` deferred, and without it nothing downstream can discharge
`Graph.IsDrawing`. The induction is over the inductive relation `PolyReaches`, and the step
takes the *first* point at which the new segment, run backwards from its far end, meets the
polygon already built, truncates there and appends. -/

/-- The last vertex of a nonempty vertex list, with the nonemptiness discharged by the
`cons`. Carrying the list in the form `u :: t` removes every dependent proof argument from
the statements below. -/
def lastP (u : Plane) (t : List Plane) : Plane := (u :: t).getLast (List.cons_ne_nil u t)

@[simp] theorem lastP_nil (u : Plane) : lastP u [] = u := rfl

@[simp] theorem lastP_cons (u v : Plane) (t : List Plane) : lastP u (v :: t) = lastP v t :=
  List.getLast_cons (List.cons_ne_nil v t)

theorem lastP_append : ∀ (u : Plane) (t : List Plane) (z : Plane), lastP u (t ++ [z]) = z
  | _, [], _ => rfl
  | u, v :: t, z => by
    rw [List.cons_append, lastP_cons, lastP_append v t z]

theorem lastP_mem_poly (u : Plane) (t : List Plane) : lastP u t ∈ poly (u :: t) :=
  getLast_mem_poly (List.cons_ne_nil u t)

/-- Appending one vertex, in the `u :: t` presentation. -/
theorem poly_snoc (u : Plane) (t : List Plane) (z : Plane) :
    poly (u :: (t ++ [z])) = poly (u :: t) ∪ segment ℝ (lastP u t) z := by
  rw [← List.cons_append, poly_concat (List.cons_ne_nil u t) z]
  rfl

/-- A **simple** polygonal path: consecutive vertices are distinct, and each segment meets the
rest of the polygon exactly in the vertex where they are joined. That is precisely the
hypothesis `Schoenflies.IsArcBetween.concatenate` asks for, one step at a time. -/
def IsArcList : List Plane → Prop
  | [] => True
  | [_] => True
  | u :: v :: rest => u ≠ v ∧ segment ℝ u v ∩ poly (v :: rest) = {v} ∧ IsArcList (v :: rest)

@[simp] theorem isArcList_nil : IsArcList [] := trivial

@[simp] theorem isArcList_singleton (v : Plane) : IsArcList [v] := trivial

theorem isArcList_cons_cons {u v : Plane} {rest : List Plane} :
    IsArcList (u :: v :: rest) ↔
      u ≠ v ∧ segment ℝ u v ∩ poly (v :: rest) = {v} ∧ IsArcList (v :: rest) := Iff.rfl

/-- The carrier of a simple polygonal path is an arc between its ends. The induction glues one
segment at a time with `Schoenflies.IsArcBetween.concatenate`; the meeting hypothesis is the
second clause of `IsArcList`. -/
theorem isArcBetween_poly : ∀ (u v : Plane) (rest : List Plane), IsArcList (u :: v :: rest) →
    IsArcBetween (poly (u :: v :: rest)) u (lastP v rest)
  | u, v, [], h => by
    rw [poly_cons_cons, poly_singleton]
    have : segment ℝ u v ∪ {v} = segment ℝ u v :=
      union_eq_self_of_subset_right (singleton_subset_iff.2 (right_mem_segment ℝ u v))
    rw [this]
    exact isArcBetween_segment h.1
  | u, v, w :: rest, h => by
    rw [poly_cons_cons, lastP_cons]
    refine (isArcBetween_segment h.1).concatenate (isArcBetween_poly v w rest h.2.2) ?_
    intro z hz hz'
    have : z ∈ segment ℝ u v ∩ poly (v :: w :: rest) := ⟨hz, hz'⟩
    rw [h.2.1] at this
    exact this

/-- **Truncation.** A simple polygonal path may be cut at any point of its carrier: the piece
up to that point is again a simple polygonal path, inside the original one. -/
theorem IsArcList.truncate : ∀ (u : Plane) (t : List Plane), IsArcList (u :: t) →
    ∀ {w : Plane}, w ∈ poly (u :: t) →
      ∃ t' : List Plane, IsArcList (u :: t') ∧ poly (u :: t') ⊆ poly (u :: t) ∧
        lastP u t' = w
  | u, [], _, w, hw => by
    rw [poly_singleton, mem_singleton_iff] at hw
    exact ⟨[], isArcList_singleton u, subset_rfl, hw.symm⟩
  | u, v :: rest, h, w, hw => by
    by_cases hrest : w ∈ poly (v :: rest)
    · obtain ⟨rest', hlist, hsub, hlast⟩ := IsArcList.truncate v rest h.2.2 hrest
      refine ⟨v :: rest', ⟨h.1, ?_, hlist⟩, ?_, by rw [lastP_cons, hlast]⟩
      · refine Subset.antisymm ?_ ?_
        · exact fun z hz => h.2.1 ▸ ⟨hz.1, hsub hz.2⟩
        · rintro z rfl
          exact ⟨right_mem_segment ℝ u z, head_mem_poly (List.cons_ne_nil z rest')⟩
      · rw [poly_cons_cons, poly_cons_cons]
        exact union_subset_union_right _ hsub
    · rw [poly_cons_cons] at hw
      have hseg : w ∈ segment ℝ u v := hw.resolve_right hrest
      rcases eq_or_ne w u with heq | hwu
      · refine ⟨[], isArcList_singleton u, ?_, heq.symm⟩
        rw [poly_singleton, poly_cons_cons]
        exact singleton_subset_iff.2 (Or.inl (left_mem_segment ℝ u v))
      · refine ⟨[w], ⟨Ne.symm hwu, ?_, isArcList_singleton w⟩, ?_, rfl⟩
        · rw [poly_singleton]
          exact Subset.antisymm inter_subset_right
            (singleton_subset_iff.2 ⟨right_mem_segment ℝ u w, rfl⟩)
        · rw [poly_cons_cons, poly_singleton, poly_cons_cons]
          have : segment ℝ u w ∪ {w} = segment ℝ u w :=
            union_eq_self_of_subset_right (singleton_subset_iff.2 (right_mem_segment ℝ u w))
          rw [this]
          exact subset_union_of_subset_left
            ((convex_segment u v).segment_subset (left_mem_segment ℝ u v) hseg) _

/-- **Extension.** A simple polygonal path may be extended by a segment that meets it only at
its own last vertex. -/
theorem IsArcList.snoc : ∀ (u : Plane) (t : List Plane), IsArcList (u :: t) →
    ∀ {z : Plane}, z ≠ lastP u t →
      segment ℝ (lastP u t) z ∩ poly (u :: t) = {lastP u t} →
      IsArcList (u :: (t ++ [z]))
  | u, [], _, z, hz, _ => by
    refine ⟨Ne.symm hz, ?_, isArcList_singleton z⟩
    rw [poly_singleton]
    exact Subset.antisymm inter_subset_right
      (singleton_subset_iff.2 ⟨right_mem_segment ℝ u z, rfl⟩)
  | u, v :: rest, h, z, hz, hmeet => by
    rw [List.cons_append]
    refine ⟨h.1, ?_, ?_⟩
    · -- The first segment still meets the rest only at `v`: the new piece is barred from it
      -- because it meets the whole old polygon only at its last vertex, which lies on the
      -- rest and hence, if it were on the first segment, would have to be `v`.
      rw [lastP_cons] at hz hmeet
      rw [poly_snoc]
      refine Subset.antisymm ?_ ?_
      · rintro y ⟨hy1, hy2 | hy2⟩
        · exact h.2.1 ▸ ⟨hy1, hy2⟩
        · have hylast : y = lastP v rest := by
            have : y ∈ segment ℝ (lastP v rest) z ∩ poly (u :: v :: rest) :=
              ⟨hy2, Or.inl hy1⟩
            rw [hmeet] at this
            exact this
          have : lastP v rest ∈ segment ℝ u v ∩ poly (v :: rest) :=
            ⟨hylast ▸ hy1, lastP_mem_poly v rest⟩
          rw [h.2.1] at this
          rw [hylast]
          exact this
      · rintro y rfl
        exact ⟨right_mem_segment ℝ u y, Or.inl (head_mem_poly (List.cons_ne_nil y rest))⟩
    · rw [lastP_cons] at hz hmeet
      refine IsArcList.snoc v rest h.2.2 hz (Subset.antisymm ?_ ?_)
      · exact fun y hy => hmeet ▸ ⟨hy.1, Or.inr hy.2⟩
      · exact singleton_subset_iff.2
          ⟨left_mem_segment ℝ _ _, lastP_mem_poly v rest⟩

/-- **Every polygonal path contains a simple one.** This is the half of Lemma 1.1 that
`Schoenflies/PolyPath.lean` deferred, and the reason brick B8 can discharge the injectivity
clause of `Graph.IsDrawing`.

The induction is on `PolyReaches`. At a `step` the new segment is run *backwards* from its far
end and stopped the first time it touches the polygon already built — `exists_first_mem_Icc`
of `Schoenflies/Graph/VertexSquares.lean` is exactly that. The old path is truncated there and
the stub appended; the stub meets the truncation only at the join, because everything strictly
before the stopping parameter misses the old polygon altogether. -/
theorem PolyReaches.exists_arcList {S : Set Plane} {x y : Plane} (h : PolyReaches S x y) :
    ∃ t : List Plane, IsArcList (x :: t) ∧ poly (x :: t) ⊆ S ∧ lastP x t = y := by
  induction h with
  | refl hx => exact ⟨[], isArcList_singleton x, by simpa using hx, rfl⟩
  | @step w z _ hseg ih =>
    obtain ⟨t, hlist, hsub, hlast⟩ := ih
    -- The straight run from `z` back to `w`, stopped the first time it meets the old polygon.
    set γ : ℝ → Plane := fun a => z + a • (w - z) with hγ
    have hγc : ContinuousOn γ (Icc 0 1) := (by fun_prop : Continuous γ).continuousOn
    have hγ1 : γ 1 = w := by simp [hγ]
    have hclosed : IsClosed (poly (x :: t)) := (isCompact_poly _).isClosed
    have hmem1 : γ 1 ∈ poly (x :: t) := by
      rw [hγ1, ← hlast]; exact lastP_mem_poly x t
    obtain ⟨s, hs, -, hsmem, hbefore⟩ :=
      exists_first_mem_Icc hγc hclosed (right_mem_Icc.2 zero_le_one) hmem1
    -- Everything on the stub, bar its far end, is before the stopping parameter.
    have himg : segment ℝ (γ s) z ⊆ γ '' Icc 0 s := by
      rw [segment_symm, segment_eq_image' ℝ z (γ s)]
      rintro u ⟨θ, hθ, rfl⟩
      refine ⟨θ * s, ⟨mul_nonneg hθ.1 hs.1, mul_le_of_le_one_left hs.1 hθ.2⟩, ?_⟩
      simp only [hγ]
      module
    have hstub : ∀ u ∈ segment ℝ (γ s) z, u ∈ poly (x :: t) → u = γ s := by
      intro u hu humem
      obtain ⟨a, ha, rfl⟩ := himg hu
      rcases eq_or_lt_of_le ha.2 with heq | hlt
      · rw [heq]
      · exact absurd humem (hbefore a ⟨ha.1, le_trans ha.2 hs.2⟩ hlt)
    -- The stub lies on the new segment, since `γ s` does.
    have hγs_seg : γ s ∈ segment ℝ z w := by
      rw [segment_eq_image' ℝ z w]
      exact ⟨s, hs, rfl⟩
    have hsegzw : segment ℝ z w ⊆ S := by rw [segment_symm]; exact hseg
    have hstubsub : segment ℝ (γ s) z ⊆ S :=
      Subset.trans ((convex_segment z w).segment_subset hγs_seg (left_mem_segment ℝ z w)) hsegzw
    obtain ⟨t', hlist', hsub', hlast'⟩ := IsArcList.truncate x t hlist hsmem
    rcases eq_or_ne z (γ s) with heq | hzne
    · exact ⟨t', hlist', hsub'.trans hsub, by rw [hlast']; exact heq.symm⟩
    · refine ⟨t' ++ [z], ?_, ?_, lastP_append x t' z⟩
      · refine IsArcList.snoc x t' hlist' (by rw [hlast']; exact hzne) ?_
        rw [hlast']
        refine Subset.antisymm (fun u hu => hstub u hu.1 (hsub' hu.2)) ?_
        exact singleton_subset_iff.2 ⟨left_mem_segment ℝ _ _, hlast' ▸ lastP_mem_poly x t'⟩
      · rw [poly_snoc, hlast']
        exact union_subset (hsub'.trans hsub) hstubsub

/-! ### The contact point of a core sits on the frame of its square

`Graph.IsDrawing.exists_core` says the core meets the square about `v` in exactly one point.
That point is on the *frame* of the square and not in its interior, which is what puts the
core in the plane minus the open squares and what makes the radial segment reach the core.
The argument is connectedness, not the parametrisation: were the contact point interior, it
would be a nonempty proper clopen piece of the core. -/

namespace Plane

/-- If a connected set meets a closed square in exactly one point and is not contained in that
square, the meeting point is on the frame: its sup distance to the centre is exactly the
radius. -/
theorem supDist_eq_of_inter_eq_singleton {K : Set Plane} {c p q : Plane} {r : ℝ}
    (hK : IsPreconnected K) (hp : K ∩ closedSquare c r = {p}) (hq : q ∈ K)
    (hqc : q ∉ closedSquare c r) : supDist p c = r := by
  have hpmem : p ∈ K ∩ closedSquare c r := by rw [hp]; rfl
  refine le_antisymm hpmem.2 (le_of_not_gt fun hlt => ?_)
  obtain ⟨w, hwK, hw1, hw2⟩ := hK (openSquare c r) (closedSquare c r)ᶜ
    (isOpen_openSquare c r) (isClosed_closedSquare c r).isOpen_compl
    (fun z hz => by
      by_cases hzc : z ∈ closedSquare c r
      · refine Or.inl ?_
        have hzp : z ∈ K ∩ closedSquare c r := ⟨hz, hzc⟩
        rw [hp, mem_singleton_iff] at hzp
        rw [hzp]
        exact hlt
      · exact Or.inr hzc)
    ⟨p, hpmem.1, hlt⟩ ⟨q, hq, hqc⟩
  exact hw2 (openSquare_subset_closedSquare c r hw1)

end Plane

end Schoenflies

/-! ### Bricks B7 and B8, and the redrawing itself -/

open Schoenflies

namespace Graph

/-- **The polygonal redrawing of a finite plane graph** (`lem:polygonal-redrawing`). A finite
plane graph is drawn again, on the *same* abstract graph and the *same* vertices, with every
edge a polygonal arc. The blueprint speaks of an isomorphic plane drawing; since the vertices
of a plane graph are plane points and the redrawing leaves them where they are, the
isomorphism is the identity and no `Graph.IsIsomorphism` appears.

The construction, in the order the proof takes it.

* **The squares** (brick B2). One radius `r` serves every vertex: the square about a vertex
  meets no other vertex, meets no arc of an edge it is not incident with, and distinct squares
  are disjoint.
* **The cores** (brick B4). Each edge's arc, cut back to what lies between its last exit from
  the square at one end and its first entry into the square at the other. A core carries no
  vertex, so distinct cores are disjoint; and — `Plane.supDist_eq_of_inter_eq_singleton` — its
  two contact points sit on the *frames* of the two squares, so the core lies in the plane `M`
  minus the open squares.
* **The tubes** (brick B7). One `ε` makes the `ε`-tubes about the cores pairwise disjoint, by
  compact separation and the single-bound lemma. `U e` is the connected component, inside
  `M ∩ tube e`, of the core; it is relatively open in `M`, so the strengthened brick B5 joins
  the two contact points by a polygonal path *inside* `U e`.
* **The assembly** (brick B8). The path is straightened to a simple one
  (`Schoenflies.PolyReaches.exists_arcList`), then a radial segment is prepended at each end.
  A radial meets `M` only at its far end and two radials meet only at their common centre, so
  the three pieces glue to an arc; `Schoenflies.isArcBetween_poly` produces the
  parametrisation that `IsDrawing.edge_param` demands. -/
theorem polygonal_redrawing {β : Type*} (G : Graph Plane β) [G.Finite]
    (drawing : β → ℝ → Plane) (h : IsDrawing G drawing) :
    ∃ redrawing : β → ℝ → Plane, IsDrawing G redrawing ∧
      ∀ e ∈ E(G), IsPolygonal (edgeArc redrawing e) := by
  classical
  obtain ⟨r, hr, hvert, hnoninc, hsqdisj⟩ := h.exists_vertexSquares
  -- The core of every edge, with the edge's two ends and the core's two contact points.
  have hdata : ∀ e ∈ E(G), ∃ a b p q : Plane, ∃ Kc : Set Plane,
      G.IsLink e a b ∧ Kc ⊆ edgeArc drawing e ∧ IsCompact Kc ∧ IsArcBetween Kc p q ∧
        Kc ∩ Plane.closedSquare a r = {p} ∧ Kc ∩ Plane.closedSquare b r = {q} ∧
        Disjoint Kc V(G) := by
    intro e he
    obtain ⟨a, b, hl⟩ := G.exists_isLink_of_mem_edgeSet he
    obtain ⟨Kc, p, q, h1, h2, h3, h4, h5, h6⟩ :=
      h.exists_core hr hl (hsqdisj a hl.left_mem b hl.right_mem (h.ne_of_isLink hl))
    exact ⟨a, b, p, q, Kc, hl, h1, h2, h3, h4, h5, h6⟩
  choose! va vb pa pb core hlink hcoresub hcorecpt hcorearc hcoreA hcoreB hcoreV using hdata
  have hvaV : ∀ e ∈ E(G), va e ∈ V(G) := fun e he => (hlink e he).left_mem
  have hvbV : ∀ e ∈ E(G), vb e ∈ V(G) := fun e he => (hlink e he).right_mem
  have hvab : ∀ e ∈ E(G), va e ≠ vb e := fun e he => h.ne_of_isLink (hlink e he)
  have hpamem : ∀ e ∈ E(G), pa e ∈ core e ∩ Plane.closedSquare (va e) r := by
    intro e he; rw [hcoreA e he]; rfl
  have hpbmem : ∀ e ∈ E(G), pb e ∈ core e ∩ Plane.closedSquare (vb e) r := by
    intro e he; rw [hcoreB e he]; rfl
  have hcoreconn : ∀ e ∈ E(G), IsPreconnected (core e) :=
    fun e he => (hcorearc e he).isArc.isConnected.isPreconnected
  -- The contact points sit on the frames of their squares.
  have hpar : ∀ e ∈ E(G), Plane.supDist (pa e) (va e) = r := by
    intro e he
    refine Plane.supDist_eq_of_inter_eq_singleton (hcoreconn e he) (hcoreA e he)
      (hpbmem e he).1 fun hcon => ?_
    exact Set.disjoint_left.1 (hsqdisj (va e) (hvaV e he) (vb e) (hvbV e he) (hvab e he))
      hcon (hpbmem e he).2
  have hpbr : ∀ e ∈ E(G), Plane.supDist (pb e) (vb e) = r := by
    intro e he
    refine Plane.supDist_eq_of_inter_eq_singleton (hcoreconn e he) (hcoreB e he)
      (hpamem e he).1 fun hcon => ?_
    exact Set.disjoint_left.1 (hsqdisj (vb e) (hvbV e he) (va e) (hvaV e he)
      (Ne.symm (hvab e he))) hcon (hpamem e he).2
  -- The plane minus the open squares, and its local polygonal connectedness (brick B5).
  set M : Set Plane := (⋃ c ∈ V(G), Plane.openSquare c r)ᶜ with hMdef
  have hMloc : IsLocallyPolyConn' M :=
    isLocallyPolyConn'_compl_biUnion (Graph.finite_vertexSet (G := G)) (fun _ => r) hsqdisj
  have hMV : ∀ c ∈ V(G), c ∉ M := fun c hc hcM =>
    hcM (mem_biUnion hc (Plane.mem_openSquare_self hr))
  -- The cores avoid the open squares.
  have hcoreM : ∀ e ∈ E(G), core e ⊆ M := by
    intro e he z hz hcon
    obtain ⟨c, hc, hzc⟩ := mem_iUnion₂.1 hcon
    have hzc' : z ∈ Plane.closedSquare c r := Plane.openSquare_subset_closedSquare c r hzc
    rcases eq_or_ne c (va e) with rfl | hca
    · have hzp : z ∈ core e ∩ Plane.closedSquare (va e) r := ⟨hz, hzc'⟩
      rw [hcoreA e he, mem_singleton_iff] at hzp
      rw [hzp] at hzc
      exact absurd (hpar e he) (ne_of_lt hzc)
    · rcases eq_or_ne c (vb e) with rfl | hcb
      · have hzp : z ∈ core e ∩ Plane.closedSquare (vb e) r := ⟨hz, hzc'⟩
        rw [hcoreB e he, mem_singleton_iff] at hzp
        rw [hzp] at hzc
        exact absurd (hpbr e he) (ne_of_lt hzc)
      · exact Set.disjoint_left.1
          (hnoninc c hc e he (not_inc_of_ne (hlink e he) hca hcb)) hzc' (hcoresub e he hz)
  -- Brick B7: one `ε` making the tubes about the cores pairwise disjoint.
  obtain ⟨ε, hε, hεall⟩ : ∃ ε > 0, ∀ e ∈ E(G), ∀ f ∈ E(G), f ≠ e →
      ∀ a ∈ core e, ∀ b ∈ core f, 2 * ε ≤ dist a b := by
    refine exists_pos_forall_of_finite (Graph.finite_edgeSet (G := G))
      (P := fun e ε => ∀ f ∈ E(G), f ≠ e → ∀ a ∈ core e, ∀ b ∈ core f, 2 * ε ≤ dist a b)
      (fun e δ ε _ hδε hP f hf hfe a ha b hb =>
        le_trans (by linarith) (hP f hf hfe a ha b hb)) ?_
    intro e he
    refine exists_pos_forall_of_finite (Graph.finite_edgeSet (G := G))
      (P := fun f ε => f ≠ e → ∀ a ∈ core e, ∀ b ∈ core f, 2 * ε ≤ dist a b)
      (fun f δ ε _ hδε hP hfe a ha b hb => le_trans (by linarith) (hP hfe a ha b hb)) ?_
    intro f hf
    by_cases hfe : f = e
    · exact ⟨1, one_pos, fun hcon => absurd hfe hcon⟩
    · obtain ⟨ρ, hρ, hsep⟩ := Plane.exists_dist_pos (hcorecpt e he) (hcorecpt f hf)
        (h.disjoint_of_subset_edgeArc he hf (Ne.symm hfe) (hcoresub e he) (hcoreV e he)
          (hcoresub f hf))
      exact ⟨ρ / 2, by linarith, fun _ a ha b hb => by have := hsep a ha b hb; linarith⟩
  set tube : β → Set Plane := fun e => ⋃ z ∈ core e, ball z ε with htubedef
  have htubeopen : ∀ e, IsOpen (tube e) := fun _ => isOpen_biUnion fun _ _ => isOpen_ball
  have htubedisj : ∀ e ∈ E(G), ∀ f ∈ E(G), e ≠ f → Disjoint (tube e) (tube f) := by
    intro e he f hf hef
    refine Set.disjoint_left.2 fun z hze hzf => ?_
    obtain ⟨a, ha, hza⟩ := mem_iUnion₂.1 hze
    obtain ⟨b, hb, hzb⟩ := mem_iUnion₂.1 hzf
    have h1 : dist a z < ε := by rw [dist_comm]; exact hza
    have h2 : dist z b < ε := hzb
    have h3 := hεall e he f hf (Ne.symm hef) a ha b hb
    have h4 := dist_triangle a z b
    linarith
  -- `U e` is the component of the core inside the tube, relatively open in `M`.
  set U : β → Set Plane := fun e => connectedComponentIn (M ∩ tube e) (pa e) with hUdef
  have hrel : ∀ e, IsRelOpenIn M (M ∩ tube e) := fun e => ⟨tube e, htubeopen e, rfl⟩
  have hcoreO : ∀ e ∈ E(G), core e ⊆ M ∩ tube e := fun e he z hz =>
    ⟨hcoreM e he hz, mem_iUnion₂.2 ⟨z, hz, mem_ball_self hε⟩⟩
  have hcoreU : ∀ e ∈ E(G), core e ⊆ U e := fun e he =>
    (hcoreconn e he).subset_connectedComponentIn (hpamem e he).1 (hcoreO e he)
  have hUM : ∀ e, U e ⊆ M := fun _ =>
    (connectedComponentIn_subset _ _).trans inter_subset_left
  have hUdisj : ∀ e ∈ E(G), ∀ f ∈ E(G), e ≠ f → Disjoint (U e) (U f) := fun e he f hf hef =>
    Set.disjoint_of_subset ((connectedComponentIn_subset _ _).trans inter_subset_right)
      ((connectedComponentIn_subset _ _).trans inter_subset_right) (htubedisj e he f hf hef)
  have hpaU : ∀ e ∈ E(G), pa e ∈ U e := fun e he => hcoreU e he (hpamem e he).1
  have hpbU : ∀ e ∈ E(G), pb e ∈ U e := fun e he => hcoreU e he (hpbmem e he).1
  have hpath : ∀ e ∈ E(G), PolyReaches (U e) (pa e) (pb e) := fun e he =>
    polyReaches_connectedComponentIn hMloc (hrel e) (hpaU e he) (hpbU e he)
  -- A radial segment meets `M` only at its far end, and stays inside its square.
  have hsegM : ∀ c p : Plane, c ∈ V(G) → Plane.supDist p c = r →
      ∀ z ∈ segment ℝ c p, z ∈ M → z = p := by
    intro c p hc hpc z hz hzM
    by_contra hne
    refine hzM (mem_biUnion hc ?_)
    have hlt := Plane.supDist_lt_of_mem_segment (by rw [hpc]; exact hr) hz hne
    rw [hpc] at hlt
    exact hlt
  have hsegSq : ∀ c p : Plane, Plane.supDist p c = r →
      segment ℝ c p ⊆ Plane.closedSquare c r :=
    fun c p hpc => Plane.segment_subset_closedSquare hr.le hpc.le
  -- The point set of a redrawn edge, before it is built.
  set Sset : β → Set Plane := fun e =>
    segment ℝ (va e) (pa e) ∪ U e ∪ segment ℝ (vb e) (pb e) with hSsetdef
  have hUcase : ∀ e ∈ E(G), ∀ f ∈ E(G), e ≠ f → ∀ z ∈ U e, z ∉ Sset f := by
    intro e he f hf hef z hz hzf
    have hzM : z ∈ M := hUM e hz
    have hdis := Set.disjoint_left.1 (hUdisj e he f hf hef) hz
    rcases hzf with (hzf | hzf) | hzf
    · exact hdis ((hsegM (va f) (pa f) (hvaV f hf) (hpar f hf) z hzf hzM) ▸ hpaU f hf)
    · exact hdis hzf
    · exact hdis ((hsegM (vb f) (pb f) (hvbV f hf) (hpbr f hf) z hzf hzM) ▸ hpbU f hf)
  have hRadial : ∀ e ∈ E(G), ∀ c p : Plane, c ∈ V(G) → Plane.supDist p c = r → p ∈ U e →
      ∀ f ∈ E(G), e ≠ f → ∀ z ∈ segment ℝ c p, z ∈ Sset f → z = c := by
    intro e he c p hc hpc hpU f hf hef z hz hzf
    have hdis := Set.disjoint_left.1 (hUdisj e he f hf hef) hpU
    rcases hzf with (hzf | hzf) | hzf
    · exact Plane.radial_meet hr hpc (hpar f hf)
        (fun hEq => hdis (hEq ▸ hpaU f hf)) (fun hne => hsqdisj c hc _ (hvaV f hf) hne) hz hzf
    · exact absurd (hdis ((hsegM c p hc hpc z hz (hUM f hzf)) ▸ hzf)) not_false
    · exact Plane.radial_meet hr hpc (hpbr f hf)
        (fun hEq => hdis (hEq ▸ hpbU f hf)) (fun hne => hsqdisj c hc _ (hvbV f hf) hne) hz hzf
  have hSmeet : ∀ e ∈ E(G), ∀ f ∈ E(G), e ≠ f → ∀ z ∈ Sset e, z ∈ Sset f →
      z = va e ∨ z = vb e := by
    intro e he f hf hef z hze hzf
    rcases hze with (hze | hze) | hze
    · exact Or.inl (hRadial e he (va e) (pa e) (hvaV e he) (hpar e he) (hpaU e he)
        f hf hef z hze hzf)
    · exact absurd hzf (hUcase e he f hf hef z hze)
    · exact Or.inr (hRadial e he (vb e) (pb e) (hvbV e he) (hpbr e he) (hpbU e he)
        f hf hef z hze hzf)
  have hSvert : ∀ e ∈ E(G), ∀ v ∈ V(G), v ∈ Sset e → v = va e ∨ v = vb e := by
    intro e he v hv hvS
    rcases hvS with (hvS | hvS) | hvS
    · refine Or.inl (by_contra fun hne => ?_)
      exact hvert (va e) (hvaV e he) v hv hne (hsegSq (va e) (pa e) (hpar e he) hvS)
    · exact absurd (hUM e hvS) (hMV v hv)
    · refine Or.inr (by_contra fun hne => ?_)
      exact hvert (vb e) (hvbV e he) v hv hne (hsegSq (vb e) (pb e) (hpbr e he) hvS)
  -- Brick B8: the redrawn edge, as a parametrisation.
  have harc : ∀ e ∈ E(G), ∃ g : ℝ → Plane,
      ContinuousOn g I ∧ InjOn g I ∧ g 0 = va e ∧ g 1 = vb e ∧
        IsPolygonal (g '' I) ∧ g '' I ⊆ Sset e := by
    intro e he
    obtain ⟨t, hlist, hsub, hlast⟩ := (hpath e he).exists_arcList
    have hpaM : ∀ z ∈ poly (pa e :: t), z ∈ M := fun z hz => hUM e (hsub hz)
    have hAP : va e ≠ pa e := by
      intro hEq
      have hx := hpar e he
      rw [← hEq, Plane.supDist_self] at hx
      exact hr.ne' hx.symm
    have hBQ : vb e ≠ pb e := by
      intro hEq
      have hx := hpbr e he
      rw [← hEq, Plane.supDist_self] at hx
      exact hr.ne' hx.symm
    have hpbpoly : pb e ∈ poly (pa e :: t) := hlast ▸ lastP_mem_poly (pa e) t
    -- The far radial meets the straightened path only at the far contact point.
    have hmeetQ : segment ℝ (pb e) (vb e) ∩ poly (pa e :: t) = {pb e} := by
      refine Subset.antisymm (fun z hz => ?_) ?_
      · rw [segment_symm] at hz
        exact hsegM (vb e) (pb e) (hvbV e he) (hpbr e he) z hz.1 (hpaM z hz.2)
      · exact singleton_subset_iff.2 ⟨left_mem_segment ℝ _ _, hpbpoly⟩
    have hlist2 : IsArcList (pa e :: (t ++ [vb e])) :=
      IsArcList.snoc (pa e) t hlist (by rw [hlast]; exact hBQ)
        (by rw [hlast]; exact hmeetQ)
    have hpolysnoc : poly (pa e :: (t ++ [vb e]))
        = poly (pa e :: t) ∪ segment ℝ (pb e) (vb e) := by
      rw [poly_snoc, hlast]
    -- The near radial meets the rest only at the near contact point: the straightened path
    -- lives in `M`, and the far radial lives in the other square.
    have hmeetP : segment ℝ (va e) (pa e) ∩ poly (pa e :: (t ++ [vb e])) = {pa e} := by
      rw [hpolysnoc]
      refine Subset.antisymm ?_ ?_
      · rintro z ⟨hz1, hz2 | hz2⟩
        · exact hsegM (va e) (pa e) (hvaV e he) (hpar e he) z hz1 (hpaM z hz2)
        · rw [segment_symm] at hz2
          exact absurd (Set.disjoint_left.1
            (hsqdisj (va e) (hvaV e he) (vb e) (hvbV e he) (hvab e he))
            (hsegSq (va e) (pa e) (hpar e he) hz1)
            (hsegSq (vb e) (pb e) (hpbr e he) hz2)) not_false
      · exact singleton_subset_iff.2 ⟨right_mem_segment ℝ _ _,
          Or.inl (head_mem_poly (List.cons_ne_nil _ _))⟩
    have hlist3 : IsArcList (va e :: pa e :: (t ++ [vb e])) := ⟨hAP, hmeetP, hlist2⟩
    have harcb := isArcBetween_poly (va e) (pa e) (t ++ [vb e]) hlist3
    rw [lastP_append] at harcb
    obtain ⟨g, hgc, hgi, hgim, hg0, hg1⟩ := harcb
    refine ⟨g, hgc, hgi, hg0, hg1, ⟨_, hgim⟩, ?_⟩
    rw [hgim, poly_cons_cons, hpolysnoc]
    refine union_subset (subset_union_of_subset_left subset_union_left _)
      (union_subset (hsub.trans (subset_union_of_subset_left subset_union_right _)) ?_)
    rw [segment_symm]
    exact subset_union_right
  choose! F hFc hFi hF0 hF1 hFpoly hFsub using harc
  refine ⟨F, ⟨fun e he => ⟨hFc e he, hFi e he, ?_⟩, ?_, ?_⟩, fun e he => hFpoly e he⟩
  · rw [hF0 e he, hF1 e he]; exact hlink e he
  · intro e a b v hl hv hvarc
    have he : e ∈ E(G) := hl.edge_mem
    rcases hSvert e he v hv (hFsub e he hvarc) with hEq | hEq <;>
      rcases hl.eq_and_eq_or_eq_and_eq (hlink e he) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (hEq.trans h1.symm)
    · exact Or.inr (hEq.trans h2.symm)
    · exact Or.inr (hEq.trans h2.symm)
    · exact Or.inl (hEq.trans h1.symm)
  · intro e f he hf hef z hze hzf
    have h1 := hSmeet e he f hf hef z (hFsub e he hze) (hFsub f hf hzf)
    have h2 := hSmeet f hf e he (Ne.symm hef) z (hFsub f hf hzf) (hFsub e he hze)
    refine ⟨?_, ?_, ?_⟩
    · rcases h1 with hEq | hEq
      · rw [hEq]; exact hvaV e he
      · rw [hEq]; exact hvbV e he
    · rcases h1 with hEq | hEq
      · rw [hEq]; exact (hlink e he).inc_left
      · rw [hEq]; exact (hlink e he).inc_right
    · rcases h2 with hEq | hEq
      · rw [hEq]; exact (hlink f hf).inc_left
      · rw [hEq]; exact (hlink f hf).inc_right

end Graph

end BundlePart386

section BundlePart387
/- Source: Papers/GraphicalZonotopes/ArcK5Redrawing.lean -/



noncomputable section
open Set Schoenflies unitInterval
open scoped Graph

namespace Graph

/-- The ten unordered pairs of distinct labels among five vertices. -/
abbrev K5Edge := {q : Fin 5 × Fin 5 // q.1 < q.2}

/-- A finite graph on five named plane points, with exactly one edge for each
unordered pair. It is an ordinary graph with actual plane vertices. -/
def k5ArcGraph (x : Fin 5 → Plane) : Graph Plane K5Edge where
  vertexSet := Set.range x
  edgeSet := Set.univ
  IsLink e u v := (u = x e.1.1 ∧ v = x e.1.2) ∨
    (u = x e.1.2 ∧ v = x e.1.1)
  isLink_symm := by
    intro e _
    constructor
    rintro u v (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · exact Or.inr ⟨rfl,rfl⟩
    · exact Or.inl ⟨rfl,rfl⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro e u v a b (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) <;> simp
  edge_mem_iff_exists_isLink := by
    intro e
    exact ⟨fun _ => ⟨x e.1.1,x e.1.2,Or.inl ⟨rfl,rfl⟩⟩,fun _ => Set.mem_univ _⟩
  left_mem_of_isLink := by
    rintro e u v (⟨rfl,_⟩ | ⟨rfl,_⟩)
    · exact ⟨e.1.1,rfl⟩
    · exact ⟨e.1.2,rfl⟩

instance k5ArcGraph_finite (x : Fin 5 → Plane) : (k5ArcGraph x).Finite where
  finite_vertexSet := Set.finite_range x
  finite_edgeSet := Set.finite_univ

theorem k5ArcGraph_isLink (x : Fin 5 → Plane) (e : K5Edge) :
    (k5ArcGraph x).IsLink e (x e.1.1) (x e.1.2) := Or.inl ⟨rfl,rfl⟩

theorem k5ArcGraph_inc (x : Fin 5 → Plane) (e : K5Edge) {p : Plane}
    (hp : p ∈ ({x e.1.1,x e.1.2} : Set Plane)) : (k5ArcGraph x).Inc e p := by
  rcases hp with rfl | rfl
  · exact (k5ArcGraph_isLink x e).inc_left
  · exact (k5ArcGraph_isLink x e).inc_right

namespace IsArcK5
variable {x : Fin 5 → Plane} {P : Fin 5 → Fin 5 → Set Plane}

noncomputable def arcDrawing (h : IsArcK5 x P) : K5Edge → ℝ → Plane :=
  fun e => (h.arc e.1.1 e.1.2 (ne_of_lt e.2)).choose

theorem edgeArc_eq (h : IsArcK5 x P) (e : K5Edge) :
    edgeArc h.arcDrawing e = P e.1.1 e.1.2 :=
  (h.arc e.1.1 e.1.2 (ne_of_lt e.2)).choose_spec.2.2.1

theorem arcDrawing_zero (h : IsArcK5 x P) (e : K5Edge) :
    h.arcDrawing e 0 = x e.1.1 :=
  (h.arc e.1.1 e.1.2 (ne_of_lt e.2)).choose_spec.2.2.2.1

theorem arcDrawing_one (h : IsArcK5 x P) (e : K5Edge) :
    h.arcDrawing e 1 = x e.1.2 :=
  (h.arc e.1.1 e.1.2 (ne_of_lt e.2)).choose_spec.2.2.2.2

/-- The ten genuine simple arcs supply a finite plane drawing. -/
theorem isDrawing (h : IsArcK5 x P) : IsDrawing (k5ArcGraph x) h.arcDrawing := by
  constructor
  · intro e _
    obtain ⟨hc,hi,_,_,_⟩ := (h.arc e.1.1 e.1.2 (ne_of_lt e.2)).choose_spec
    refine ⟨hc,hi,?_⟩
    rw [h.arcDrawing_zero,h.arcDrawing_one]
    exact k5ArcGraph_isLink x e
  · intro e u v w hl hwV hw
    obtain ⟨k,rfl⟩ := hwV
    have hv := h.vertex e.1.1 e.1.2 k (ne_of_lt e.2) (by rwa [h.edgeArc_eq] at hw)
    rcases hl with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact hv.imp (congrArg x) (congrArg x)
    · exact (hv.imp (congrArg x) (congrArg x)).symm
  · intro e f _ _ hef p hp hq
    rw [h.edgeArc_eq] at hp hq
    have hpairs : e.1 ≠ f.1 := fun hh => hef (Subtype.ext hh)
    have hreverse : e.1 ≠ (f.1.2,f.1.1) := by
      intro hh
      have h1 := congrArg Prod.fst hh
      have h2 := congrArg Prod.snd hh
      have he := e.2
      have hf := f.2
      simp only [Prod.fst,Prod.snd] at h1 h2
      omega
    obtain ⟨hpe,hpf⟩ := h.meet e.1.1 e.1.2 f.1.1 f.1.2
      (ne_of_lt e.2) (ne_of_lt f.2) hpairs hreverse ⟨hp,hq⟩
    refine ⟨?_,k5ArcGraph_inc x e hpe,k5ArcGraph_inc x f hpf⟩
    rcases hpe with rfl | rfl
    · exact ⟨e.1.1,rfl⟩
    · exact ⟨e.1.2,rfl⟩

/-- Restore an ordered-pair notation from the ten edge arcs. Diagonal values
are empty and play no role in the K₅ configuration. -/
def edgeFamily (drawing : K5Edge → ℝ → Plane) (i j : Fin 5) : Set Plane :=
  if hij : i < j then edgeArc drawing ⟨(i,j),hij⟩
  else if hji : j < i then edgeArc drawing ⟨(j,i),hji⟩ else ∅

theorem edgeFamily_eq (drawing : K5Edge → ℝ → Plane) {i j : Fin 5} (hij : i < j) :
    edgeFamily drawing i j = edgeArc drawing ⟨(i,j),hij⟩ := by
  simp only [edgeFamily,dif_pos hij]

theorem edgeFamily_symm (drawing : K5Edge → ℝ → Plane) (i j : Fin 5) :
    edgeFamily drawing i j = edgeFamily drawing j i := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp [edgeFamily,hij,not_lt_of_ge hij.le]
  · rfl
  · simp [edgeFamily,hji,not_lt_of_ge hji.le]

theorem edgeFamily_edge (drawing : K5Edge → ℝ → Plane) (i j : Fin 5) (hij : i ≠ j) :
    ∃ e : K5Edge, edgeFamily drawing i j = edgeArc drawing e ∧
      (e.1 = (i,j) ∨ e.1 = (j,i)) := by
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact ⟨⟨(i,j),hij⟩,edgeFamily_eq drawing hij,Or.inl rfl⟩
  · refine ⟨⟨(j,i),hji⟩,?_,Or.inr rfl⟩
    rw [edgeFamily_symm drawing i j,edgeFamily_eq drawing hji]

theorem isLink_of_pair {e : K5Edge} {i j : Fin 5}
    (he : e.1 = (i,j) ∨ e.1 = (j,i)) : (k5ArcGraph x).IsLink e (x i) (x j) := by
  rcases he with he | he
  · exact Or.inl ⟨by rw [he],by rw [he]⟩
  · exact Or.inr ⟨by rw [he],by rw [he]⟩

/-- A drawing of the ten-edge graph gives the same unrestricted arc interface. -/
theorem of_drawing (hx : Function.Injective x) {drawing : K5Edge → ℝ → Plane}
    (hd : IsDrawing (k5ArcGraph x) drawing) : IsArcK5 x (edgeFamily drawing) := by
  constructor
  · exact hx
  · intro i j hij
    obtain ⟨e,he,hpair⟩ := edgeFamily_edge drawing i j hij
    rw [he]
    exact hd.edge_isArcBetween (isLink_of_pair hpair)
  · exact edgeFamily_symm drawing
  · intro i j k hij hk
    obtain ⟨e,he,hpair⟩ := edgeFamily_edge drawing i j hij
    rw [he] at hk
    have hv : x k ∈ V(k5ArcGraph x) := ⟨k,rfl⟩
    exact (hd.vertex_mem_edgeArc (isLink_of_pair hpair) hv hk).imp
      (fun hh => hx hh) (fun hh => hx hh)
  · intro i j k l hij hkl hpairs hreverse p hp
    obtain ⟨e,he,hepair⟩ := edgeFamily_edge drawing i j hij
    obtain ⟨f,hf,hfpair⟩ := edgeFamily_edge drawing k l hkl
    have hef : e ≠ f := by
      intro hh
      have hval : e.1 = f.1 := congrArg Subtype.val hh
      rcases hepair with hepair | hepair <;>
        rcases hfpair with hfpair | hfpair
      · exact hpairs (hepair.symm.trans (hval.trans hfpair))
      · exact hreverse (hepair.symm.trans (hval.trans hfpair))
      · apply hreverse
        exact congrArg Prod.swap (hepair.symm.trans (hval.trans hfpair))
      · apply hpairs
        exact congrArg Prod.swap (hepair.symm.trans (hval.trans hfpair))
    rw [he,hf] at hp
    obtain ⟨_,hpe,hpf⟩ := hd.edge_inter (Set.mem_univ _) (Set.mem_univ _) hef hp.1 hp.2
    exact ⟨hpe.eq_or_eq_of_isLink (isLink_of_pair hepair),
      hpf.eq_or_eq_of_isLink (isLink_of_pair hfpair)⟩

/-- Every genuine K₅ arc configuration has a polygonal redrawing on exactly
the same five points. No graph realization or edge-straightening assumption
is left in the conclusion. -/
theorem exists_polygonal (h : IsArcK5 x P) :
    ∃ P' : Fin 5 → Fin 5 → Set Plane, IsArcK5 x P' ∧
      ∀ i j,i ≠ j → IsPolygonal (P' i j) := by
  obtain ⟨drawing,hd,hpoly⟩ := polygonal_redrawing (k5ArcGraph x) h.arcDrawing h.isDrawing
  refine ⟨edgeFamily drawing,of_drawing h.injective hd,?_⟩
  intro i j hij
  obtain ⟨e,he,_⟩ := edgeFamily_edge drawing i j hij
  rw [he]
  exact hpoly e (Set.mem_univ _)

end IsArcK5
end Graph

end
end BundlePart387

section BundlePart388
/- Source: dev/planar_search/schoenflies_port/Schoenflies/Graph/TwoConnected.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/




/-!
# Vertex deletion and 2-connectivity

Deleting a vertex from Mathlib's multigraph `Graph α β`, and the blueprint's notion of a
2-connected graph.

## Vertex deletion is Mathlib's

Mathlib already has it: `Graph.deleteVerts G X = G.induce (V(G) \ X)`, in
`Mathlib/Combinatorics/Graph/Delete.lean`, with `V(G.deleteVerts X) = V(G) \ X` and
`E(G.deleteVerts X) = {e | ∃ x y, G.IsLink e x y ∧ x ∉ X ∧ y ∉ X}` — an edge with an end in
`X` is gone, which is exactly what is wanted. Nothing here redefines it; `G.deleteVerts {x}`
is the deletion of one vertex, and what this file adds is the transfer of *walks* across it,
which Mathlib has no notion of.

Two of those transfers are the whole story, and both are corollaries of `Graph.IsWalk.anti`:

* `Graph.IsWalk.deleteVerts_singleton` — a walk that never visits `x` is a walk of `G - x`.
  The edges of such a walk automatically survive, because the ends of an edge of a walk are
  vertices the walk visits.
* `Graph.IsWalk.notMem_of_inc_of_deleteVerts` — a walk **in** `G - x` cannot have used an
  edge at `x`; there are none left to use. This is how an argument that routes around a
  vertex ends up avoiding a named edge, and it is what makes `Graph.IsTwoConnected.no_bridge`
  short.

Deleting a vertex the graph does not have changes nothing — `G.deleteVerts {x} = G` on the
nose (`Graph.deleteVerts_singleton_eq_self`), since `V(G) \ {x} = V(G)`. That equation is
what makes the union lemma's hard case disappear.

## At least three vertices

The counting clause of 2-connectivity is carried by `Graph.HasThreeVertices`, "three pairwise
distinct vertices", rather than by `3 ≤ V(G).ncard`. The two agree on a finite graph, but the
existential form is **monotone with no finiteness hypothesis** (`Graph.HasThreeVertices.mono`),
and monotonicity is precisely what `Graph.IsTwoConnected.union` needs: the union of two graphs
is not known to be finite at the point where its third vertex is produced. `Set.ncard` is `0`
on an infinite set, so `3 ≤ V(G).ncard` would additionally make every infinite graph fail to
be 2-connected, which is not the intent of the convention.

What consumers actually use is never the clause itself but `Graph.HasThreeVertices.exists_ne_ne`
— any two vertices leave a third over. `Graph.hasThreeVertices_iff_ncard` is the bridge back to
the count, for a consumer that has one.

## The convention, verbatim, and what it costs

`Graph.IsTwoConnected` is the blueprint's definition word for word (§"Plane graphs and the
utility graph"): at least three vertices, connected, and still connected after any one vertex
is deleted. Two consequences the blueprint calls out are recorded here as theorems rather
than as prose:

* the one-edge graph is **not** 2-connected, and
* a two-vertex cycle — two parallel edges — is a cycle without being 2-connected.

Both are instances of `Graph.not_isTwoConnected_banana`: `Graph.banana u v F` has only the two
vertices `u` and `v` whatever `F` is, so it fails the counting clause. Two-vertex cycles do
occur in the development, as face boundaries inside a larger 2-connected graph, and this is
the theorem that says they are not themselves 2-connected. (No cycle is *named* here: this
file must not depend on the cycle module.)

## Union

Mathlib's `Mathlib/Combinatorics/Graph/Lattice.lean` provides only the *infimum* of two
graphs — there is no union in this version of Mathlib — so `Graph.union` is defined here. On
an edge belonging to both graphs, `G`'s ends win:

```
(G.union H).IsLink e x y ↔ G.IsLink e x y ∨ (e ∉ E(G) ∧ H.IsLink e x y)
```

which makes the definition total. It has to be resolved somehow: two graphs may disagree
about the ends of a shared edge name, and then no graph has both as subgraphs. When the two
graphs are `Graph.Compatible` — in particular when both are subgraphs of one graph, via
`Graph.Compatible.of_le_le`, which is the only way the plane layer forms unions — the
disjunction collapses to the naive one (`Graph.Compatible.union_isLink`) and both graphs are
subgraphs of the union.

## Blueprint

* `Graph.IsTwoConnected` — the definition in §"Plane graphs and the utility graph": "a finite
  graph is *2-connected* if it has at least three vertices, is connected, and remains
  connected after deletion of any one vertex".
* `Graph.IsTwoConnected.no_cut_vertex` — "with this convention a 2-connected graph has no cut
  vertex".
* `Graph.not_isTwoConnected_banana` — "the one-edge graph is not 2-connected", and the same
  computation for the two-vertex cycle of the next paragraph.
* `Graph.IsTwoConnected.no_bridge` — "A 2-connected graph has no bridge", the step of
  `lem:subdivision-ear-preserve` (a) that the ear decomposition runs on. Stated as "deleting
  the edge leaves its ends connected", which is the form `lem:cycle-criterion` consumes; the
  cycle itself is built elsewhere.
* `Graph.IsTwoConnected.union` — `lem:union-two-connected`, "if two finite 2-connected graphs
  have at least two vertices in common, their union is 2-connected".
-/

open Set

variable {α β : Type*} {G H K G₁ G₂ : Graph α β} {a b s t u v w x y z : α} {e f : β}
  {W : List β} {X : Set α} {F : Set β}

namespace Graph

/-! ### Deleting one vertex -/

theorem mem_deleteVerts_singleton : y ∈ V(G.deleteVerts {x}) ↔ y ∈ V(G) ∧ y ≠ x := by
  simp

theorem mem_deleteVerts_singleton_of_ne (hy : y ∈ V(G)) (hyx : y ≠ x) :
    y ∈ V(G.deleteVerts {x}) :=
  mem_deleteVerts_singleton.2 ⟨hy, hyx⟩

/-- Deleting a vertex the graph does not have leaves the graph alone — on the nose, not merely
up to isomorphism, because `V(G) \ {x}` is literally `V(G)`. -/
theorem deleteVerts_singleton_eq_self (hx : x ∉ V(G)) : G.deleteVerts {x} = G := by
  refine le_antisymm deleteVerts_le ?_
  refine ⟨?_, ?_⟩
  · intro y hy
    rw [vertexSet_deleteVerts]
    refine ⟨hy, ?_⟩
    intro hyx
    exact hx ((Set.mem_singleton_iff.mp hyx) ▸ hy)
  · intro e u v h
    rw [deleteVerts_isLink]
    refine ⟨h, ?_, ?_⟩
    · intro hux
      exact hx ((Set.mem_singleton_iff.mp hux) ▸ h.left_mem)
    · intro hvx
      exact hx ((Set.mem_singleton_iff.mp hvx) ▸ h.right_mem)

/-- Deleting the same vertices from both sides of an inclusion keeps it. -/
theorem deleteVerts_mono (h : G ≤ H) (X : Set α) : G.deleteVerts X ≤ H.deleteVerts X where
  vertexSet_mono := by
    simp only [vertexSet_deleteVerts]
    exact sdiff_subset_sdiff_left h.vertexSet_mono
  isLink_mono e x y hl := by
    rw [deleteVerts_isLink] at hl ⊢
    exact ⟨h.isLink_mono hl.1, hl.2.1, hl.2.2⟩

/-! ### Walks across a vertex deletion -/

/-- **A walk that never visits `x` survives the deletion of `x`.** Its edges need no separate
argument: the two ends of an edge the walk takes are vertices the walk visits. -/
theorem IsWalk.deleteVerts_singleton (h : G.IsWalk u W v) (hx : x ∉ G.walkVertices u W) :
    (G.deleteVerts {x}).IsWalk u W v := by
  have hux : u ≠ x := fun hh ↦ hx (hh ▸ mem_walkVertices_self)
  refine h.anti deleteVerts_le (mem_deleteVerts_singleton_of_ne h.left_mem hux) fun g hg ↦ ?_
  obtain ⟨c, d, hcd⟩ := exists_isLink_of_mem_edgeSet (h.edge_mem hg)
  have hc : c ≠ x := fun hh ↦ hx (hh ▸ mem_walkVertices_of_mem_covered ⟨g, hg, hcd.inc_left⟩)
  have hd : d ≠ x := fun hh ↦ hx (hh ▸ mem_walkVertices_of_mem_covered ⟨g, hg, hcd.inc_right⟩)
  rw [edgeSet_deleteVerts]
  exact ⟨c, d, hcd, by simpa using hc, by simpa using hd⟩

/-- **A walk in `G - x` never takes an edge at `x`** — there are none left to take. -/
theorem IsWalk.notMem_of_inc_of_deleteVerts (h : (G.deleteVerts {x}).IsWalk u W v)
    (hx : G.Inc e x) : e ∉ W := by
  intro he
  have hmem := h.edge_mem he
  rw [edgeSet_deleteVerts] at hmem
  obtain ⟨c, d, hcd, hc, hd⟩ := hmem
  obtain ⟨y, hy⟩ := hx
  rcases hy.left_eq_or_eq hcd with rfl | rfl
  exacts [hc rfl, hd rfl]

/-- The bridge between the two deletions: a walk that routes around a vertex `x` cannot have
used an edge incident to `x`, so it is still there after that edge is deleted. -/
theorem Reaches.deleteEdges_of_deleteVerts (h : (G.deleteVerts {x}).Reaches u v)
    (hx : G.Inc e x) : (G.deleteEdges {e}).Reaches u v := by
  obtain ⟨P, hP⟩ := h
  have he : e ∉ P := hP.notMem_of_inc_of_deleteVerts hx
  exact ⟨P, (hP.mono deleteVerts_le).deleteEdges fun g hg hgF ↦ he (mem_singleton_iff.1 hgF ▸ hg)⟩

/-- Connectedness is unharmed by deleting a vertex the graph does not have. -/
theorem Connected.deleteVerts_singleton_of_notMem (h : G.Connected) (hx : x ∉ V(G)) :
    (G.deleteVerts {x}).Connected := by
  rwa [deleteVerts_singleton_eq_self hx]

/-! ### Cut vertices -/

/-- A vertex whose deletion disconnects the graph. -/
def IsCutVertex (G : Graph α β) (x : α) : Prop :=
  x ∈ V(G) ∧ ¬ (G.deleteVerts {x}).Connected

/-! ### At least three vertices -/

/-- The graph has three pairwise distinct vertices. Stated existentially rather than as
`3 ≤ V(G).ncard` so that it is monotone with no finiteness hypothesis. -/
def HasThreeVertices (G : Graph α β) : Prop :=
  ∃ a ∈ V(G), ∃ b ∈ V(G), ∃ c ∈ V(G), a ≠ b ∧ a ≠ c ∧ b ≠ c

/-- On a graph with finitely many vertices the clause is the count it is named for. Kept so
that a consumer holding a cardinality is not stranded; nothing in this file uses it. -/
theorem hasThreeVertices_iff_ncard (hV : V(G).Finite) : G.HasThreeVertices ↔ 3 ≤ V(G).ncard :=
  (Set.two_lt_ncard hV).symm

theorem HasThreeVertices.mono (h : G.HasThreeVertices) (hV : V(G) ⊆ V(H)) :
    H.HasThreeVertices := by
  obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr⟩ := h
  exact ⟨p, hV hp, q, hV hq, r, hV hr, hpq, hpr, hqr⟩

/-- **Any two vertices leave a third over.** This, and not the counting clause itself, is what
every consumer of 2-connectivity uses; the two named vertices need not even be vertices of the
graph. -/
theorem HasThreeVertices.exists_ne_ne (h : G.HasThreeVertices) (u v : α) :
    ∃ w ∈ V(G), w ≠ u ∧ w ≠ v := by
  obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr⟩ := h
  by_contra hcon
  push Not at hcon
  -- Every vertex is `u` or `v`, so the three distinct ones cannot all fit.
  have key : ∀ z ∈ V(G), z = u ∨ z = v := fun z hz ↦ (em (z = u)).imp id (hcon z hz)
  rcases key p hp with rfl | rfl <;> rcases key q hq with rfl | rfl <;>
    rcases key r hr with rfl | rfl <;> simp_all

/-! ### Two-connectivity -/

/-- **The blueprint's convention, verbatim**: at least three vertices, connected, and still
connected after any one vertex is deleted. -/
structure IsTwoConnected (G : Graph α β) : Prop where
  /-- The graph has at least three vertices. -/
  hasThreeVertices : G.HasThreeVertices
  /-- The graph is connected. -/
  connected : G.Connected
  /-- Deleting any one vertex leaves it connected. -/
  deleteVerts_connected : ∀ ⦃x⦄, x ∈ V(G) → (G.deleteVerts {x}).Connected

/-- The deletion clause with its hypothesis dropped: deleting a vertex the graph does not have
changes nothing, so no consumer has to check membership first. -/
theorem IsTwoConnected.deleteVerts_connected' (h : G.IsTwoConnected) (x : α) :
    (G.deleteVerts {x}).Connected := by
  by_cases hx : x ∈ V(G)
  · exact h.deleteVerts_connected hx
  · exact h.connected.deleteVerts_singleton_of_notMem hx

/-- With this convention a 2-connected graph has no cut vertex. -/
theorem IsTwoConnected.no_cut_vertex (h : G.IsTwoConnected) (x : α) : ¬ G.IsCutVertex x :=
  fun hcut ↦ hcut.2 (h.deleteVerts_connected hcut.1)

/-- **A graph on two vertices is never 2-connected**, whatever edges it carries. Two
consequences of the convention at once: the one-edge graph is not 2-connected, and a
two-vertex cycle — two parallel edges, `F` a pair — is a cycle without being 2-connected.
Such cycles do occur in the development, as face boundaries inside a larger 2-connected
graph. -/
theorem not_isTwoConnected_banana (u v : α) (F : Set β) : ¬ (banana u v F).IsTwoConnected := by
  intro h
  obtain ⟨w, hw, hwu, hwv⟩ := h.hasThreeVertices.exists_ne_ne u v
  -- `V(banana u v F)` is `{u, v}` by definition.
  rcases (hw : w ∈ ({u, v} : Set α)) with rfl | rfl
  exacts [hwu rfl, hwv rfl]

/-- **A 2-connected graph has no bridge**, in the form "deleting an edge leaves its two ends
connected" — the hypothesis of the cycle criterion.

The blueprint's proof names the two components of `G - e` and finds a vertex of one of them
other than its endpoint. This proof routes around instead, and never mentions a component: a
third vertex `w` exists; the graph without `v` still joins `u` to `w`, and the graph without
`u` still joins `w` to `v`; and a walk that survives a vertex deletion cannot have used an
edge there, so neither walk used `e`. A loop needs no argument at all. -/
theorem IsTwoConnected.no_bridge (h : G.IsTwoConnected) (hl : G.IsLink e u v) :
    (G.deleteEdges {e}).Reaches u v := by
  rcases eq_or_ne u v with rfl | huv
  · exact Reaches.refl (by simpa using hl.left_mem)
  obtain ⟨w, hw, hwu, hwv⟩ := h.hasThreeVertices.exists_ne_ne u v
  have h₁ : (G.deleteVerts {v}).Reaches u w :=
    (h.deleteVerts_connected' v).reaches (mem_deleteVerts_singleton_of_ne hl.left_mem huv)
      (mem_deleteVerts_singleton_of_ne hw hwv)
  have h₂ : (G.deleteVerts {u}).Reaches w v :=
    (h.deleteVerts_connected' u).reaches (mem_deleteVerts_singleton_of_ne hw hwu)
      (mem_deleteVerts_singleton_of_ne hl.right_mem (Ne.symm huv))
  exact (h₁.deleteEdges_of_deleteVerts hl.inc_right).trans
    (h₂.deleteEdges_of_deleteVerts hl.inc_left)

/-! ### The union of two graphs -/

/-- The union of two graphs. On an edge belonging to both, `G`'s ends win — a resolution is
needed, since two graphs may disagree about the ends of a shared edge name; for
`Graph.Compatible` graphs, which is the only case the development forms, the disjunction
collapses to the naive one. -/
protected def union (G H : Graph α β) : Graph α β where
  vertexSet := V(G) ∪ V(H)
  edgeSet := E(G) ∪ E(H)
  IsLink e x y := G.IsLink e x y ∨ (e ∉ E(G) ∧ H.IsLink e x y)
  isLink_symm e _ :=
    { symm := by
        rintro x y (hxy | ⟨he, hxy⟩)
        exacts [Or.inl hxy.symm, Or.inr ⟨he, hxy.symm⟩] }
  eq_or_eq_of_isLink_of_isLink := by
    rintro g x y c d (hxy | ⟨hg, hxy⟩) (hcd | ⟨hg', hcd⟩)
    · exact hxy.left_eq_or_eq hcd
    · exact absurd hxy.edge_mem hg'
    · exact absurd hcd.edge_mem hg
    · exact hxy.left_eq_or_eq hcd
  edge_mem_iff_exists_isLink g := by
    constructor
    · rintro (hg | hg)
      · obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet hg
        exact ⟨x, y, Or.inl hxy⟩
      · by_cases hgG : g ∈ E(G)
        · obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet hgG
          exact ⟨x, y, Or.inl hxy⟩
        · obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet hg
          exact ⟨x, y, Or.inr ⟨hgG, hxy⟩⟩
    · rintro ⟨x, y, (hxy | ⟨-, hxy⟩)⟩
      exacts [Or.inl hxy.edge_mem, Or.inr hxy.edge_mem]
  left_mem_of_isLink := by
    rintro g x y (hxy | ⟨-, hxy⟩)
    exacts [Or.inl hxy.left_mem, Or.inr hxy.left_mem]

@[simp]
theorem vertexSet_union (G H : Graph α β) : V(G.union H) = V(G) ∪ V(H) := rfl

@[simp]
theorem edgeSet_union (G H : Graph α β) : E(G.union H) = E(G) ∪ E(H) := rfl

theorem union_isLink :
    (G.union H).IsLink e x y ↔ G.IsLink e x y ∨ (e ∉ E(G) ∧ H.IsLink e x y) := Iff.rfl

theorem left_le_union (G H : Graph α β) : G ≤ G.union H where
  vertexSet_mono := subset_union_left
  isLink_mono _ _ _ h := Or.inl h

/-- Two subgraphs of one graph have their union inside it. -/
theorem union_le (hGK : G ≤ K) (hHK : H ≤ K) : G.union H ≤ K where
  vertexSet_mono := Set.union_subset hGK.vertexSet_mono hHK.vertexSet_mono
  isLink_mono := by
    rintro g p q (h | ⟨-, h⟩)
    exacts [hGK.isLink_mono h, hHK.isLink_mono h]

/-- The right-hand graph is a subgraph of the union only when the two agree about their shared
edges — without that, no graph has both as subgraphs. -/
theorem Compatible.right_le_union (h : G.Compatible H) : H ≤ G.union H where
  vertexSet_mono := subset_union_right
  isLink_mono e x y hxy := by
    by_cases hg : e ∈ E(G)
    · exact Or.inl ((h.isLink_congr hg hxy.edge_mem).2 hxy)
    · exact Or.inr ⟨hg, hxy⟩

/-- For compatible graphs the union is the naive one. -/
theorem Compatible.union_isLink (h : G.Compatible H) :
    (G.union H).IsLink e x y ↔ G.IsLink e x y ∨ H.IsLink e x y := by
  refine ⟨fun hxy ↦ hxy.imp id (·.2), fun hxy ↦ ?_⟩
  rcases hxy with hxy | hxy
  · exact Or.inl hxy
  · exact h.right_le_union.isLink_mono hxy

/-- **Two connected parts covering a graph and sharing a vertex make it connected.** Used
twice below — once for the union itself, once for the union with a vertex deleted — and both
times the two parts are `G` and `H` while the whole is not their union on the nose. -/
theorem Connected.of_two_subgraphs (h₁ : G₁ ≤ K) (h₂ : G₂ ≤ K) (hV : V(K) ⊆ V(G₁) ∪ V(G₂))
    (hc₁ : G₁.Connected) (hc₂ : G₂.Connected) (hs₁ : s ∈ V(G₁)) (hs₂ : s ∈ V(G₂)) :
    K.Connected := by
  refine Connected.of_hub (h₁.vertexSet_mono hs₁) fun z hz ↦ ?_
  rcases hV hz with hz' | hz'
  · exact (hc₁.reaches hs₁ hz').mono h₁
  · exact (hc₂.reaches hs₂ hz').mono h₂

theorem Compatible.union_connected (h : G.Compatible H) (hG : G.Connected) (hH : H.Connected)
    (hs : s ∈ V(G)) (hs' : s ∈ V(H)) : (G.union H).Connected :=
  Connected.of_two_subgraphs (left_le_union G H) h.right_le_union subset_rfl hG hH hs hs'

/-- **`lem:union-two-connected`**: two 2-connected graphs with at least two vertices in common
have 2-connected union.

The blueprint's proof is one sentence — after deleting one vertex, each graph remains
connected and at least one common vertex remains. The work is the case where the deleted
vertex belongs to only one of the two graphs: the other graph never had it, so nothing was
deleted from it, and `Graph.deleteVerts_singleton_eq_self` makes that a rewriting step rather
than an argument. -/
theorem IsTwoConnected.union (hcompat : G.Compatible H) (hG : G.IsTwoConnected)
    (hH : H.IsTwoConnected) (hab : a ≠ b) (haG : a ∈ V(G)) (haH : a ∈ V(H)) (hbG : b ∈ V(G))
    (hbH : b ∈ V(H)) : (G.union H).IsTwoConnected where
  hasThreeVertices := hG.hasThreeVertices.mono (left_le_union G H).vertexSet_mono
  connected := hcompat.union_connected hG.connected hH.connected haG haH
  deleteVerts_connected := by
    intro x _
    -- One of the two common vertices survives the deletion.
    obtain ⟨c, hcG, hcH, hcx⟩ : ∃ c, c ∈ V(G) ∧ c ∈ V(H) ∧ c ≠ x := by
      by_cases ha : a = x
      · exact ⟨b, hbG, hbH, by rintro rfl; exact hab ha⟩
      · exact ⟨a, haG, haH, ha⟩
    refine Connected.of_two_subgraphs (G₁ := G.deleteVerts {x}) (G₂ := H.deleteVerts {x})
      (deleteVerts_mono (left_le_union G H) _) (deleteVerts_mono hcompat.right_le_union _)
      ?_ (hG.deleteVerts_connected' x) (hH.deleteVerts_connected' x)
      (mem_deleteVerts_singleton_of_ne hcG hcx) (mem_deleteVerts_singleton_of_ne hcH hcx)
    simp [union_sdiff_distrib]

end Graph

end BundlePart388

section BundlePart389
/- Source: dev/planar_search/schoenflies_port/Schoenflies/Graph/Component.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/



/-!
# Components and shortest paths

The two prerequisites of the relative ear decomposition (`lem:relative-ear`) that no earlier
module builds: the **component** of a vertex, and a **shortest** walk between two vertices.
Both are then spent on the geometric heart of that lemma — a component of `G - S` has two
distinct neighbours in `S`, and a path between two of them whose interior lies outside `S`.

## The component is a comprehension

`G.component u = {v | G.Reaches u v}`, exactly as `connectedComponentIn` collects the points
a space reaches. Nothing restricts the comprehension to `V(G)`: the empty walk already demands
a vertex of the graph (`Graph.IsWalk.nil`), so `G.Reaches u v` carries `v ∈ V(G)` with it, and
a clause `v ∈ V(G) ∧ …` would be redundant noise at every use site. When `u ∉ V(G)` the
component is empty, which is the convention that makes the covering statement
`Graph.iUnion_component` true with no side condition.

Reachability is an equivalence relation on `V(G)`, so the component is closed under `Reaches`,
two components are equal or disjoint, and the components cover `V(G)`. The one statement that
is not pure equivalence-relation bookkeeping is that the **induced** subgraph on a component
is connected: a walk between two vertices of a component never leaves it
(`Graph.IsWalk.walkVertices_subset_component`), so it is already a walk of the induced
subgraph, by `Graph.IsWalk.anti`.

## Shortest walks need no finiteness

The set of lengths of walks from `u` to `v` is a nonempty set of naturals, so it has a least
element — `Nat.find`, with no `Graph.Finite` hypothesis anywhere. That is worth noticing: the
blueprint says "in a finite graph", but finiteness is used there only to terminate the ear
*process*, never to find one shortest path.

A minimum-length walk is automatically a path (`Graph.IsWalk.isPath_of_minLength`). The proof
is the induction of `Graph.IsWalk.contains_path` run once more, with lengths attached: if the
step's source were revisited later, `Graph.IsPath.from_visited` would cut the tail down to a
strictly shorter walk with the same ends, and a path's edge list repeats nothing
(`Graph.IsPath.nodup`), so the cut piece really is no longer than what it came from
(`List.subperm_of_subset`).

## The two neighbours, without a contradiction

The blueprint argues by contradiction: "otherwise its unique neighbour would be a cut vertex".
Here the two neighbours are *constructed*, in the shape `Graph.IsTwoConnected.no_bridge`
already uses. A walk from the component out to a vertex of `S` crosses the boundary
(`Graph.IsWalk.crossing`), and the crossing edge's far end is in `S` — because a neighbour
outside `S` would still be in the component. That is the first neighbour `c`. For the second,
delete `c`: the big graph is still connected, so the same crossing argument runs inside
`G - c`, and its crossing edge's far end is a neighbour that is not `c`.

Two distinct vertices of `S` are needed, and used exactly once: the walk of the second step
must aim at a vertex of `S` other than `c`. In the application `S` is the vertex set of a
2-connected subgraph, which has three.

## Blueprint

* `Graph.component`, `Graph.induce_component_connected` — "a component `L` of `G - V(H₀)`" in
  the proof of `lem:relative-ear`.
* `Graph.exists_minLength_isPath` — "a shortest path through `L`", same proof.
* `Graph.IsTwoConnected.component_two_neighbors` — "if a component `L` of `G - V(H₀)` contains
  a vertex, it has at least two distinct neighbors in `H₀`; otherwise its unique neighbor
  would be a cut vertex of `G`".
* `Graph.IsTwoConnected.exists_path_through_component` — "a shortest path through `L` between
  two such neighbors is an ear": a path of `G` between two distinct vertices of `S`, whose
  every other vertex is outside `S`, which has at least one such vertex, and each of whose
  edges has an end outside `S`. The word *ear* is not used here and nothing about ears is
  assumed; this is the raw path that a consumer recognises as one.

## Namespace

Root `Graph`, as fixed by `Schoenflies/Graph/Walk.lean`.
-/

open Set
open scoped Graph

namespace Graph

variable {α β : Type*} {G H : Graph α β} {u v w x y z a b c d p q : α} {e f : β}
  {W W' P Q : List β} {S : Set α}

/-! ### Components -/

/-- The component of `u` in `G`: the vertices `u` reaches. A comprehension over the vertices,
not an indexed union of connected subgraphs; the membership test is `Graph.Reaches` itself,
which is why every closure property below is one line of the reachability API.

No `v ∈ V(G)` clause: `Graph.Reaches` already carries it, since the empty walk demands a
vertex of the graph. For `u ∉ V(G)` the component is empty. -/
def component (G : Graph α β) (u : α) : Set α := {v | G.Reaches u v}

theorem mem_component_iff : v ∈ G.component u ↔ G.Reaches u v := Iff.rfl

theorem component_subset_vertexSet : G.component u ⊆ V(G) := fun _ h ↦ Reaches.right_mem h

theorem mem_component_self (hu : u ∈ V(G)) : u ∈ G.component u := Reaches.refl hu

theorem component_nonempty (hu : u ∈ V(G)) : (G.component u).Nonempty :=
  ⟨u, mem_component_self hu⟩

/-- A vertex the graph does not have reaches nothing. -/
theorem component_eq_empty (hu : u ∉ V(G)) : G.component u = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ h ↦ hu (Reaches.left_mem h)

/-- **A component is closed under reachability**, which is the property every consumer uses:
whatever a vertex of the component reaches is in the component. -/
theorem mem_component_of_reaches (hv : v ∈ G.component u) (h : G.Reaches v w) :
    w ∈ G.component u :=
  Reaches.trans hv h

/-- A component is closed under taking an edge. -/
theorem mem_component_of_isLink (hx : x ∈ G.component u) (hl : G.IsLink e x y) :
    y ∈ G.component u :=
  mem_component_of_reaches hx (Reaches.of_isLink hl)

theorem mem_component_comm : v ∈ G.component u ↔ u ∈ G.component v := reaches_comm

/-- A vertex of a component has the same component. -/
theorem component_eq_of_mem (hv : v ∈ G.component u) : G.component v = G.component u :=
  Set.ext fun _ ↦ ⟨fun h ↦ Reaches.trans hv h, fun h ↦ Reaches.trans (Reaches.symm hv) h⟩

/-- **Two components are equal or disjoint.** -/
theorem component_eq_or_disjoint (u v : α) :
    G.component u = G.component v ∨ Disjoint (G.component u) (G.component v) := by
  rcases em (∃ w, w ∈ G.component u ∧ w ∈ G.component v) with ⟨w, hu, hv⟩ | hne
  · exact Or.inl ((component_eq_of_mem hu).symm.trans (component_eq_of_mem hv))
  · exact Or.inr (Set.disjoint_left.2 fun w hw hw' ↦ hne ⟨w, hw, hw'⟩)

/-- **The components cover the vertex set.** -/
theorem iUnion_component (G : Graph α β) : ⋃ u ∈ V(G), G.component u = V(G) :=
  Set.Subset.antisymm (Set.iUnion₂_subset fun _ _ ↦ component_subset_vertexSet)
    fun _ hx ↦ Set.mem_biUnion hx (mem_component_self hx)

/-! ### The subgraph induced on a component -/

theorem induce_component_le : G.induce (G.component u) ≤ G :=
  induce_le component_subset_vertexSet

@[simp]
theorem mem_vertexSet_induce_component : v ∈ V(G.induce (G.component u)) ↔ G.Reaches u v :=
  Iff.rfl

/-- **A walk out of a component stays in it**: every vertex it visits is reachable from the
component's base point, one step at a time. -/
theorem IsWalk.walkVertices_subset_component (h : G.IsWalk x W y) (hx : x ∈ G.component u) :
    G.walkVertices x W ⊆ G.component u := by
  induction h with
  | nil => simpa using hx
  | @cons x' w y e W hl _ ih =>
    intro z hz
    rcases mem_walkVertices_cons hl hz with rfl | hz'
    · exact hx
    · exact ih (mem_component_of_isLink hx hl) hz'

/-- A walk that starts in a component is a walk of the subgraph induced on it. Both ends of
each of its edges are vertices it visits, so the edges survive the induction. -/
theorem IsWalk.induce_component (h : G.IsWalk x W y) (hx : x ∈ G.component u) :
    (G.induce (G.component u)).IsWalk x W y := by
  refine h.anti induce_component_le hx fun g hg ↦ ?_
  obtain ⟨s, t, hst⟩ := exists_isLink_of_mem_edgeSet (h.edge_mem hg)
  exact ⟨s, t, hst,
    h.walkVertices_subset_component hx (mem_walkVertices_of_mem_covered ⟨g, hg, hst.inc_left⟩),
    h.walkVertices_subset_component hx (mem_walkVertices_of_mem_covered ⟨g, hg, hst.inc_right⟩)⟩

/-- **The subgraph induced on a component is connected**, with the base point as hub. -/
theorem induce_component_connected (hu : u ∈ V(G)) : (G.induce (G.component u)).Connected := by
  refine Connected.of_hub (mem_component_self hu) fun z hz ↦ ?_
  obtain ⟨W, hW⟩ := mem_component_iff.1 hz
  exact ⟨W, hW.induce_component (mem_component_self hu)⟩

/-! ### Shortest walks and shortest paths -/

/-- **A shortest walk exists** between any two vertices one of which reaches the other: the
lengths of such walks form a nonempty set of naturals. No finiteness is needed. -/
theorem exists_minLength_isWalk (h : G.Reaches u v) :
    ∃ W, G.IsWalk u W v ∧ ∀ W', G.IsWalk u W' v → W.length ≤ W'.length := by
  classical
  obtain ⟨W₀, hW₀⟩ := h
  have hex : ∃ n, ∃ W, G.IsWalk u W v ∧ W.length = n := ⟨W₀.length, W₀, hW₀, rfl⟩
  obtain ⟨W, hW, hlen⟩ := Nat.find_spec hex
  exact ⟨W, hW, fun W' hW' ↦ hlen ▸ Nat.find_le ⟨W', hW', rfl⟩⟩

/-- **A shortest walk is a path.** If the vertex a step departs from were visited again, the
tail could be cut there (`Graph.IsPath.from_visited`) and the result would be a strictly
shorter walk with the same ends — strictly, because a path repeats no edge and the cut piece
is a sublist-up-to-permutation of what it came from. -/
theorem IsWalk.isPath_of_minLength (h : G.IsWalk u W v)
    (hmin : ∀ W', G.IsWalk u W' v → W.length ≤ W'.length) : G.IsPath u W v := by
  induction h with
  | nil hx => exact .nil hx
  | @cons u w v e W hl hW ih =>
    -- The tail is shortest among walks from the waypoint: prepending `e` to a shorter one
    -- would beat the whole walk.
    have hmin' : ∀ W', G.IsWalk w W' v → W.length ≤ W'.length := fun W' hW' ↦ by
      have := hmin (e :: W') (.cons hl hW')
      simp only [List.length_cons] at this
      omega
    have hP : G.IsPath w W v := ih hmin'
    refine .cons hl hP fun hmem ↦ ?_
    obtain ⟨T, hT, hTW⟩ := hP.from_visited hmem
    have h₁ : T.length ≤ W.length := (List.subperm_of_subset hT.nodup hTW).length_le
    have h₂ := hmin T hT.isWalk
    simp only [List.length_cons] at h₂
    omega

/-- **A shortest path exists**: among all walks between two vertices, one of least length,
and it is a path. This is the blueprint's "shortest path". -/
theorem exists_minLength_isPath (h : G.Reaches u v) :
    ∃ P, G.IsPath u P v ∧ ∀ W, G.IsWalk u W v → P.length ≤ W.length :=
  let ⟨W, hW, hmin⟩ := exists_minLength_isWalk h
  ⟨W, hW.isPath_of_minLength hmin, hmin⟩

theorem Connected.exists_minLength_isPath (h : G.Connected) (hu : u ∈ V(G)) (hv : v ∈ V(G)) :
    ∃ P, G.IsPath u P v ∧ ∀ W, G.IsWalk u W v → P.length ≤ W.length :=
  _root_.Graph.exists_minLength_isPath (h.reaches hu hv)

/-! ### Components of a vertex deletion

From here on `S : Set α` is a set of vertices to be deleted, and the component in question is
one of `G.deleteVerts S`. Only two facts about the deletion are used, and both are about where
its walks can go. -/

/-- A walk of `G - S` visits only vertices of `G` outside `S` — computed in `G`, which is the
form the freshness clause of a path of `G` reads. -/
theorem IsWalk.walkVertices_subset_of_deleteVerts (h : (G.deleteVerts S).IsWalk u W v) :
    G.walkVertices u W ⊆ V(G) \ S := by
  intro z hz
  rcases mem_walkVertices_iff.1 hz with rfl | ⟨g, hg, hinc⟩
  · simpa using h.left_mem
  -- An edge of the walk survives the deletion, so both of its ends do.
  have hgE := h.edge_mem hg
  rw [edgeSet_deleteVerts] at hgE
  obtain ⟨s, t, hst, hs, ht⟩ := hgE
  rcases hinc.eq_or_eq_of_isLink hst with rfl | rfl
  exacts [⟨hst.left_mem, hs⟩, ⟨hst.right_mem, ht⟩]

/-- The component of `G - S` at `x`, seen in `G`: outside `S`, and inside `V(G)`. -/
theorem component_deleteVerts_subset : (G.deleteVerts S).component x ⊆ V(G) \ S := by
  intro z hz
  have := component_subset_vertexSet hz
  rwa [vertexSet_deleteVerts] at this

/-- **A neighbour of a component of `G - S` that is outside `S` is in the component.** The
edge joining them survives the deletion, so it extends the walk. -/
theorem mem_component_deleteVerts_of_isLink (hp : p ∈ (G.deleteVerts S).component x)
    (hl : G.IsLink e p q) (hq : q ∉ S) : q ∈ (G.deleteVerts S).component x :=
  mem_component_of_isLink hp
    ((deleteVerts_isLink G S).2 ⟨hl, (component_deleteVerts_subset hp).2, hq⟩)

/-- **Walking out of a component of `G - S` meets `S` along an edge.** The walk may live in
any subgraph `K` of `G` — it is run inside `G - c` once — but the component is always the one
of `G - S`, which is what makes the conclusion usable twice.

This is `Graph.IsWalk.crossing` plus the previous lemma: the crossing edge's far end is
outside the component, so it cannot be outside `S`. -/
theorem exists_isLink_out_of_component {K : Graph α β} (hKG : K ≤ G)
    (h : K.IsWalk x W v) (hx : x ∈ (G.deleteVerts S).component x) (hv : v ∈ S) :
    ∃ p ∈ (G.deleteVerts S).component x, ∃ g ∈ W, ∃ t ∈ S, K.IsLink g p t := by
  have hvL : v ∉ (G.deleteVerts S).component x := fun hmem ↦
    (component_deleteVerts_subset hmem).2 hv
  obtain ⟨g, hg, s, t, hst, hs, ht⟩ := h.crossing hx hvL
  refine ⟨s, hs, g, hg, t, ?_, hst⟩
  by_contra htS
  exact ht (mem_component_deleteVerts_of_isLink hs (hst.mono hKG) htS)

/-! ### The two neighbours of a component, and the path through it -/

/-- **A component of `G - S` has two distinct neighbours in `S`** — the first half of
`lem:relative-ear`, with the blueprint's contradiction turned into a construction.

`S` must contain two distinct vertices; in the application it is the vertex set of a
2-connected subgraph, which has three. The first neighbour `c` comes from a walk of `G` out of
the component to a vertex of `S`; the second from the same walk run inside `G - c`, which is
still connected because `G` is 2-connected, and aimed at a vertex of `S` other than `c`. -/
theorem IsTwoConnected.component_two_neighbors (hG : G.IsTwoConnected) (hS : S ⊆ V(G))
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) (hx : x ∈ V(G)) (hxS : x ∉ S) :
    ∃ c ∈ S, ∃ d ∈ S, c ≠ d ∧
      (∃ p ∈ (G.deleteVerts S).component x, ∃ g, G.IsLink g p c) ∧
      (∃ q ∈ (G.deleteVerts S).component x, ∃ g, G.IsLink g q d) := by
  have hxD : x ∈ V(G.deleteVerts S) := by rw [vertexSet_deleteVerts]; exact ⟨hx, hxS⟩
  have hxL : x ∈ (G.deleteVerts S).component x := mem_component_self hxD
  -- First neighbour: walk from `x` to `a` in `G` and take the edge where it leaves.
  obtain ⟨W, hW⟩ := hG.connected.reaches hx (hS ha)
  obtain ⟨p, hp, g, -, c, hc, hgpc⟩ := exists_isLink_out_of_component le_rfl hW hxL ha
  -- Second neighbour: aim at a vertex of `S` other than `c`, inside `G - c`.
  obtain ⟨t, ht, htc⟩ : ∃ t ∈ S, t ≠ c := by
    rcases eq_or_ne a c with rfl | hac
    · exact ⟨b, hb, fun h ↦ hab h.symm⟩
    · exact ⟨a, ha, hac⟩
  have hxc : x ∈ V(G.deleteVerts {c}) :=
    mem_deleteVerts_singleton_of_ne hx fun h ↦ hxS (h ▸ hc)
  have htc' : t ∈ V(G.deleteVerts {c}) := mem_deleteVerts_singleton_of_ne (hS ht) htc
  obtain ⟨W', hW'⟩ := (hG.deleteVerts_connected' c).reaches hxc htc'
  obtain ⟨q, hq, g', -, d, hd, hgqd⟩ :=
    exists_isLink_out_of_component deleteVerts_le hW' hxL ht
  -- The second crossing edge lives in `G - c`, so its far end is not `c`.
  have hdc : d ≠ c := by
    have := ((deleteVerts_isLink G {c}).1 hgqd).2.2
    simpa using this
  exact ⟨c, hc, d, hd, fun h ↦ hdc h.symm, ⟨p, hp, g, hgpc⟩, ⟨q, hq, g', hgqd.mono deleteVerts_le⟩⟩

/-- Reading off the vertices of a walk with one edge appended at the far end. Purely about
lists; used to check the freshness clause when a path inside a component is capped with an
edge back into `S`. -/
theorem mem_walkVertices_append_singleton (hy : y ∈ G.walkVertices u (W ++ [e])) :
    y ∈ G.walkVertices u W ∨ G.Inc e y := by
  rcases mem_walkVertices_iff.1 hy with rfl | hcov
  · exact Or.inl mem_walkVertices_self
  rw [coveredVertices_append] at hcov
  rcases hcov with h | ⟨g, hg, hinc⟩
  · exact Or.inl (mem_walkVertices_of_mem_covered h)
  · obtain rfl : g = e := by simpa using hg
    exact Or.inr hinc

/-- **The path through a component** — the second half of `lem:relative-ear`, without the word
*ear*: in a 2-connected `G`, from a vertex outside a set `S` that has two distinct vertices,
one gets a path of `G` whose two endpoints are distinct vertices of `S`, whose every other
vertex is outside `S`, which has at least one vertex outside `S`, and each of whose edges has
an end outside `S`.

The last two clauses are what make the ear process terminate and what make the path *new*: it
really does add a vertex, and none of its edges belongs to a subgraph whose vertices all lie
in `S`.

The path is built from the two neighbours of the component: the edge into the component, a
path across the component (in `G - S`, hence never touching `S`), and the edge back out. -/
theorem IsTwoConnected.exists_path_through_component (hG : G.IsTwoConnected) (hS : S ⊆ V(G))
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) (hx : x ∈ V(G)) (hxS : x ∉ S) :
    ∃ c ∈ S, ∃ d ∈ S, ∃ P, c ≠ d ∧ G.IsPath c P d ∧
      (∀ y ∈ G.walkVertices c P, y ≠ c → y ≠ d → y ∉ S) ∧
      (∃ y ∈ G.walkVertices c P, y ∉ S) ∧
      ∀ f ∈ P, ∃ y, G.Inc f y ∧ y ∉ S := by
  obtain ⟨c, hc, d, hd, hcd, ⟨p, hp, g, hgpc⟩, ⟨q, hq, g', hgqd⟩⟩ :=
    hG.component_two_neighbors hS ha hb hab hx hxS
  have hpS : p ∉ S := (component_deleteVerts_subset hp).2
  have hqS : q ∉ S := (component_deleteVerts_subset hq).2
  -- A path across the component, taken in `G - S` so that it cannot touch `S`.
  obtain ⟨Q, hQ⟩ := Reaches.exists_isPath (Reaches.trans (Reaches.symm hq) hp)
  have hQvert : G.walkVertices q Q ⊆ V(G) \ S :=
    hQ.isWalk.walkVertices_subset_of_deleteVerts
  have hQG : G.IsPath q Q p := hQ.mono deleteVerts_le
  -- Cap it with the edge `p — c`, which is fresh because `c ∈ S`.
  have hcQ : c ∉ G.walkVertices q Q := fun hmem ↦ (hQvert hmem).2 hc
  have hQc : G.IsPath q (Q ++ [g]) c := hQG.extend_at_target hgpc hcQ
  -- Prepend the edge `d — q`, fresh because `d ∈ S` and `d ≠ c`.
  have hdQc : d ∉ G.walkVertices q (Q ++ [g]) := by
    intro hmem
    rcases mem_walkVertices_append_singleton hmem with hmem' | hinc
    · exact (hQvert hmem').2 hd
    · rcases hinc.eq_or_eq_of_isLink hgpc with rfl | rfl
      exacts [hpS hd, hcd rfl]
  have hpath : G.IsPath d (g' :: (Q ++ [g])) c := .cons hgqd.symm hQc hdQc
  refine ⟨d, hd, c, hc, _, fun h ↦ hcd h.symm, hpath, fun y hy hyd hyc ↦ ?_,
    ⟨q, mem_walkVertices_cons_of_mem hgqd.symm mem_walkVertices_self, hqS⟩, fun f hf ↦ ?_⟩
  · -- Every vertex is `d`, `c`, or one that `G - S` reached.
    rcases mem_walkVertices_cons hgqd.symm hy with rfl | hy'
    · exact absurd rfl hyd
    rcases mem_walkVertices_append_singleton hy' with hmem | hinc
    · exact (hQvert hmem).2
    · rcases hinc.eq_or_eq_of_isLink hgpc with rfl | rfl
      exacts [hpS, absurd rfl hyc]
  · -- Every edge touches the component: the two capping edges at `q` and at `p`, the rest at
    -- both of their ends.
    rcases List.mem_cons.1 hf with rfl | hf'
    · exact ⟨q, hgqd.inc_left, hqS⟩
    rcases List.mem_append.1 hf' with hf' | hf'
    · have hfE := hQ.isWalk.edge_mem hf'
      rw [edgeSet_deleteVerts] at hfE
      obtain ⟨s, t, hst, hs, -⟩ := hfE
      exact ⟨s, hst.inc_left, hs⟩
    · obtain rfl : f = g := by simpa using hf'
      exact ⟨p, hgpc.inc_left, hpS⟩

end Graph

end BundlePart389

section BundlePart390
/- Source: dev/planar_search/schoenflies_port/Schoenflies/Graph/PathGraph.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/




/-!
# A path presented as a graph

`Schoenflies/Graph/Walk.lean` says what it means for an edge list to *run* through a graph.
This file says what it means for a graph to *be* a path, and — the point of the file —
constructs one.

## Why the object exists

An ear is a path that gets glued onto a graph, so it has to be a graph itself, not a walk
inside one. `Graph.IsPathGraph P u W v` says that `P`'s own edges, listed in the order `W`,
form a path from `u` to `v` and that `P`'s vertices are exactly the ones that path visits.
The list `W` is an index of the predicate rather than an existential: its **order** is part
of the claim, and it is what lets every later argument cut the path at a vertex without first
having to sort anything.

Mathlib's `Graph α β` carries a `Set β` of edges, not a list, so the correspondence between
the two is a clause of the definition (`Graph.IsPathGraph.edgeSet_eq`) rather than something
a list-based graph would give for free.

## Constructing one

`Graph.pathGraphOf G u W` is the subgraph of `G` spanned by the walk `W` from `u`: the
vertices the walk visits, and its own edges. Everything else in the file is a hypothesis of
the form `IsPathGraph`; this is where one is produced, and it is what an ear decomposition
runs on — a path found inside a big graph has to be turned into a graph before it can be
unioned back in.

## What the ear argument actually asks

Always the same thing: **whatever vertex is deleted, every remaining vertex of the path still
reaches one of the two ends** (`Graph.IsPathGraph.reaches_an_end`). The proof is uniform in
the deleted vertex `c`, with no case split on whether `c` is an end, an interior vertex or
off the path at all:

* if `c` is on the path, cut there (`Graph.IsPath.split`); each remaining vertex lies on one
  of the two halves, and a half runs to its far end without meeting the cut, because the
  split's last clause says the far half never returns to the source;
* if `c` is not on the path, cut at the vertex itself and reverse the near half.

Both branches go through the same two lemmas, `Graph.IsPath.reaches_target_of_ne_source` and
its mirror, so the interior case has no separate content.

## Blueprint

* `Graph.IsPathGraph` — the object called "a path `P`" in Lemma
  `lem:subdivision-ear-preserve` (b) ("if `P` is a path whose distinct endpoints lie in `G`
  … then `G ∪ P` is 2-connected") and "an ear" in Lemma `lem:relative-ear`.
* `Graph.IsPathGraph.reaches_an_end` — the blueprint's "every component of `P - x` is
  attached to `G - x` at one of the two endpoints of `P`; when `x` is an endpoint, the
  remainder of `P` is attached at the other endpoint", both sentences at once.
* `Graph.pathGraphOf` — the "shortest path through `L` between two such neighbors is an ear"
  of `lem:relative-ear`: a path of the ambient graph, presented as a graph.

Nothing here mentions 2-connectivity; the union of a 2-connected graph with an ear is a
later module.

## Namespace

Root `Graph`, as fixed by `Schoenflies/Graph/Walk.lean`, so that `h.reaches_an_end` and
`G.pathGraphOf u W` resolve by dot notation.
-/

open Set
open scoped Graph

namespace Graph

variable {α β : Type*} {G H P : Graph α β} {u v w x y c : α} {e : β} {W W₁ W₂ : List β}

/-! ### Walks and vertex deletion

Mathlib's `Graph.deleteVerts` takes a set; a single deleted vertex is `{c}`. -/

/-- Pushing the visited set down an inclusion: a subgraph's edges have ends the big graph's
edges have too. This is the direction the freshness clause of a path travels in, and the
whole content of `Graph.IsPath.anti`. -/
theorem coveredVertices_anti (hHG : H ≤ G) : H.coveredVertices W ⊆ G.coveredVertices W :=
  fun _ ⟨e, he, y, hy⟩ ↦ ⟨e, he, y, hy.mono hHG⟩

theorem walkVertices_anti (hHG : H ≤ G) : H.walkVertices u W ⊆ G.walkVertices u W :=
  Set.insert_subset_insert (coveredVertices_anti hHG)

/-- **A walk that never visits `c` survives the deletion of `c`.** Every deletion argument in
the ear layer reduces to this. -/
theorem IsWalk.avoiding (h : G.IsWalk u W v) (hc : c ∉ G.walkVertices u W) :
    (G.deleteVerts {c}).IsWalk u W v := by
  induction h with
  | @nil x hx =>
    refine .nil ?_
    rw [vertexSet_deleteVerts]
    exact ⟨hx, by rintro (rfl : x = c); exact hc mem_walkVertices_self⟩
  | @cons u w v e W hl _ ih =>
    have hw : w ∈ G.walkVertices u (e :: W) :=
      mem_walkVertices_cons_of_mem hl mem_walkVertices_self
    have hcw : c ∉ G.walkVertices w W := fun h ↦ hc (mem_walkVertices_cons_of_mem hl h)
    refine .cons ?_ (ih hcw)
    rw [deleteVerts_isLink]
    refine ⟨hl, ?_, ?_⟩
    · rintro (rfl : u ∈ ({c} : Set α))
      exact hc mem_walkVertices_self
    · rintro (rfl : w ∈ ({c} : Set α))
      exact hc hw

/-- Reversal does not change which vertices a walk visits — but it does change the source, so
this is not `Graph.walkVertices_reverse`, which keeps it. -/
theorem IsWalk.reverse_walkVertices (h : G.IsWalk u W v) :
    G.walkVertices v W.reverse = G.walkVertices u W := by
  have h₁ : v ∈ G.walkVertices u W := h.target_mem_walkVertices
  have h₂ : u ∈ G.walkVertices v W := by
    have := h.reverse.target_mem_walkVertices
    rwa [walkVertices_reverse] at this
  rw [walkVertices_reverse]
  refine Set.Subset.antisymm (fun y hy ↦ ?_) (fun y hy ↦ ?_) <;>
    rcases mem_walkVertices_iff.1 hy with rfl | hcov
  exacts [h₁, mem_walkVertices_of_mem_covered hcov, h₂, mem_walkVertices_of_mem_covered hcov]

/-- Splitting the visited set along a concatenation. Purely about lists: no walk is needed,
and the middle vertex `w` is arbitrary. -/
theorem walkVertices_append_subset :
    G.walkVertices u (W₁ ++ W₂) ⊆ G.walkVertices u W₁ ∪ G.walkVertices w W₂ := by
  rintro y hy
  rcases mem_walkVertices_iff.1 hy with rfl | hcov
  · exact Or.inl mem_walkVertices_self
  · rw [coveredVertices_append] at hcov
    exact hcov.imp mem_walkVertices_of_mem_covered mem_walkVertices_of_mem_covered

/-! ### Reaching an end of a path after a deletion -/

/-- A vertex of a path other than its source still reaches the target once the source is
deleted: cut the path at the vertex, and the far half never returns to the source. -/
theorem IsPath.reaches_target_of_ne_source (h : G.IsPath u W v)
    (hx : x ∈ G.walkVertices u W) (hxu : x ≠ u) : (G.deleteVerts {u}).Reaches x v := by
  obtain ⟨-, W₂, -, -, h₂, hback⟩ := h.split hx
  exact ⟨W₂, h₂.isWalk.avoiding (hback.resolve_left hxu)⟩

/-- The mirror image, run on the reversed path. -/
theorem IsPath.reaches_source_of_ne_target (h : G.IsPath u W v)
    (hx : x ∈ G.walkVertices u W) (hxv : x ≠ v) : (G.deleteVerts {v}).Reaches x u :=
  h.reverse.reaches_target_of_ne_source (by rwa [h.isWalk.reverse_walkVertices]) hxv

/-- **Deleting any vertex leaves every other vertex of a path able to reach an end.**
Uniform in the deleted vertex `c`: if `c` is on the path the path is cut there and each
remaining vertex sits on a half that runs to that half's far end; if `c` is off the path the
path is cut at the vertex itself and its near half, reversed, runs to the source. -/
theorem IsPath.reaches_an_end (h : G.IsPath u W v) (hx : x ∈ G.walkVertices u W)
    (hxc : x ≠ c) :
    (G.deleteVerts {c}).Reaches x u ∨ (G.deleteVerts {c}).Reaches x v := by
  by_cases hc : c ∈ G.walkVertices u W
  · obtain ⟨W₁, W₂, rfl, h₁, h₂, -⟩ := h.split hc
    rcases walkVertices_append_subset (w := c) hx with hx₁ | hx₂
    · exact Or.inl (h₁.reaches_source_of_ne_target hx₁ hxc)
    · exact Or.inr (h₂.reaches_target_of_ne_source hx₂ hxc)
  · -- The deletion misses the path entirely, so the near half survives whole.
    obtain ⟨W₁, W₂, rfl, h₁, -, -⟩ := h.split hx
    refine Or.inl ⟨W₁.reverse, h₁.reverse.isWalk.avoiding ?_⟩
    rw [h₁.isWalk.reverse_walkVertices]
    exact fun hmem ↦ hc (walkVertices_mono (List.subset_append_left _ _) hmem)

/-! ### A graph that is a path -/

/-- `P.IsPathGraph u W v` : the graph `P` *is* the path from `u` to `v` along `W`. Its own
edges are exactly the entries of `W`, and its vertices are exactly the ones that path visits.

The edge list is an index rather than an existential because its order is used: an argument
that deletes a vertex cuts `W` in two, and a graph whose edges were only a set would have to
recover the order first. -/
structure IsPathGraph (P : Graph α β) (u : α) (W : List β) (v : α) : Prop where
  /-- The graph's own edges, in the given order, form a path from one end to the other. -/
  isPath : P.IsPath u W v
  /-- The graph has no edges beyond that path's. -/
  edgeSet_eq : E(P) = {e | e ∈ W}
  /-- The graph has no vertices beyond the ones that path visits. -/
  vertexSet_eq : V(P) = P.walkVertices u W

namespace IsPathGraph

theorem isWalk (h : P.IsPathGraph u W v) : P.IsWalk u W v := h.isPath.isWalk

/-- A vertex of a path graph is visited by its path. -/
theorem mem_walkVertices (h : P.IsPathGraph u W v) (hx : x ∈ V(P)) :
    x ∈ P.walkVertices u W := h.vertexSet_eq ▸ hx

/-- Conversely, whatever the path visits is a vertex. -/
theorem mem_vertexSet (h : P.IsPathGraph u W v) (hx : x ∈ P.walkVertices u W) : x ∈ V(P) :=
  h.vertexSet_eq ▸ hx

theorem mem_edgeSet (h : P.IsPathGraph u W v) (he : e ∈ W) : e ∈ E(P) := by
  rw [h.edgeSet_eq]; exact he

theorem mem_list (h : P.IsPathGraph u W v) (he : e ∈ E(P)) : e ∈ W := by
  rw [h.edgeSet_eq] at he; exact he

theorem source_mem (h : P.IsPathGraph u W v) : u ∈ V(P) := h.isPath.left_mem

theorem target_mem (h : P.IsPathGraph u W v) : v ∈ V(P) := h.isPath.right_mem

/-- A path graph read from the other end. -/
theorem reverse (h : P.IsPathGraph u W v) : P.IsPathGraph v W.reverse u where
  isPath := h.isPath.reverse
  edgeSet_eq := by rw [h.edgeSet_eq]; ext e; simp
  vertexSet_eq := by rw [h.isWalk.reverse_walkVertices]; exact h.vertexSet_eq

/-- A path graph is connected: every vertex is visited, so the path's own prefix runs to it
from the source. -/
theorem connected (h : P.IsPathGraph u W v) : P.Connected := by
  refine Connected.of_hub h.source_mem fun x hx ↦ ?_
  obtain ⟨W₁, -, -, h₁, -, -⟩ := h.isPath.split (h.mem_walkVertices hx)
  exact ⟨W₁, h₁.isWalk⟩

/-- **Whatever vertex is deleted, every remaining vertex of a path graph still reaches one of
its two ends.** This is what the ear argument turns on: the ear's two ends are the only
vertices it shares with the graph it is glued to, so a surviving vertex of the ear has to
reach one of them inside the ear itself. -/
theorem reaches_an_end (h : P.IsPathGraph u W v) (hx : x ∈ V(P)) (hxc : x ≠ c) :
    (P.deleteVerts {c}).Reaches x u ∨ (P.deleteVerts {c}).Reaches x v :=
  h.isPath.reaches_an_end (h.mem_walkVertices hx) hxc

end IsPathGraph

/-! ### Constructing a path graph -/

/-- **The subgraph of `G` spanned by the walk `W` from `u`**: the vertices that walk visits,
carrying exactly the walk's own edges.

This is the construction an ear decomposition needs — a path found inside a big graph, turned
into a graph of its own so that it can be unioned back in. It is built from Mathlib's
`Graph.restrict` and `Graph.induce`, so that `Graph.pathGraphOf_le` is almost free. -/
def pathGraphOf (G : Graph α β) (u : α) (W : List β) : Graph α β :=
  (G.restrict {e | e ∈ W}).induce (G.walkVertices u W)

@[simp]
theorem pathGraphOf_vertexSet : V(G.pathGraphOf u W) = G.walkVertices u W := rfl

@[simp]
theorem pathGraphOf_isLink :
    (G.pathGraphOf u W).IsLink e x y ↔
      e ∈ W ∧ G.IsLink e x y ∧ x ∈ G.walkVertices u W ∧ y ∈ G.walkVertices u W := by
  simp only [pathGraphOf, induce_isLink, restrict_isLink, mem_setOf_eq]
  tauto

theorem mem_vertexSet_pathGraphOf_self : u ∈ V(G.pathGraphOf u W) := mem_walkVertices_self

/-- The spanned subgraph really is a subgraph. -/
theorem pathGraphOf_le (h : G.IsWalk u W v) : G.pathGraphOf u W ≤ G :=
  le_trans (induce_le h.walkVertices_subset) restrict_le

/-- Its edges are exactly the walk's. One inclusion is the definition; the other needs the
walk, to know that an entry of `W` is an edge of `G` at all and that its ends are visited. -/
theorem pathGraphOf_edgeSet (h : G.IsWalk u W v) : E(G.pathGraphOf u W) = {e | e ∈ W} := by
  ext f
  rw [edgeSet_eq_setOf_exists_isLink]
  simp only [pathGraphOf_isLink, mem_setOf_eq]
  refine ⟨fun ⟨_, _, hf, _⟩ ↦ hf, fun hf ↦ ?_⟩
  obtain ⟨a, b, hab⟩ := exists_isLink_of_mem_edgeSet (h.edge_mem hf)
  exact ⟨a, b, hf, hab, mem_walkVertices_of_mem_covered ⟨f, hf, hab.inc_left⟩,
    mem_walkVertices_of_mem_covered ⟨f, hf, hab.inc_right⟩⟩

/-- The spanned subgraph visits the same vertices as the ambient graph does along `W`: its
edges are the same edges, joining the same pairs. No walk is needed — an end of an edge of
`W` is visited by definition, so it survives the induced subgraph. -/
theorem coveredVertices_pathGraphOf :
    (G.pathGraphOf u W).coveredVertices W = G.coveredVertices W := by
  refine Set.Subset.antisymm (fun z ⟨f, hf, y, hy⟩ ↦ ⟨f, hf, y, (pathGraphOf_isLink.1 hy).2.1⟩)
    fun z ⟨f, hf, y, hy⟩ ↦ ?_
  · exact ⟨f, hf, y, pathGraphOf_isLink.2 ⟨hf, hy,
      mem_walkVertices_of_mem_covered ⟨f, hf, hy.inc_left⟩,
      mem_walkVertices_of_mem_covered ⟨f, hf, hy.inc_right⟩⟩⟩

theorem walkVertices_pathGraphOf :
    (G.pathGraphOf u W).walkVertices u W = G.walkVertices u W := by
  rw [walkVertices, walkVertices, coveredVertices_pathGraphOf]

/-- The walk runs inside the subgraph it spans. -/
theorem IsWalk.pathGraphOf (h : G.IsWalk u W v) : (G.pathGraphOf u W).IsWalk u W v :=
  h.anti (pathGraphOf_le h) mem_vertexSet_pathGraphOf_self
    fun _ he ↦ (pathGraphOf_edgeSet h) ▸ he

/-- The path runs inside the subgraph it spans. -/
theorem IsPath.pathGraphOf (h : G.IsPath u W v) : (G.pathGraphOf u W).IsPath u W v :=
  h.anti (pathGraphOf_le h.isWalk) mem_vertexSet_pathGraphOf_self
    fun _ he ↦ (pathGraphOf_edgeSet h.isWalk) ▸ he

/-- **A path of `G` spans a path graph.** This is the construction the whole file exists
for: the object every `Graph.IsPathGraph` hypothesis elsewhere is discharged by. -/
theorem IsPath.isPathGraph_pathGraphOf (h : G.IsPath u W v) :
    (G.pathGraphOf u W).IsPathGraph u W v where
  isPath := h.pathGraphOf
  edgeSet_eq := pathGraphOf_edgeSet h.isWalk
  vertexSet_eq := by rw [pathGraphOf_vertexSet, walkVertices_pathGraphOf]

/-! ### Finiteness

A walk visits finitely many vertices and takes finitely many edges, so the graph it spans is
finite with no hypothesis on the ambient graph. -/

/-- A step of a walk adds exactly one vertex to the visited set. -/
theorem walkVertices_cons (hl : G.IsLink e u w) :
    G.walkVertices u (e :: W) = insert u (G.walkVertices w W) := by
  ext x
  constructor
  · intro hx
    rcases mem_walkVertices_cons hl hx with rfl | hx'
    exacts [Set.mem_insert _ _, Set.mem_insert_of_mem _ hx']
  · intro hx
    rcases Set.mem_insert_iff.1 hx with rfl | hx'
    exacts [mem_walkVertices_self, mem_walkVertices_cons_of_mem hl hx']

theorem IsWalk.finite_walkVertices (h : G.IsWalk u W v) : (G.walkVertices u W).Finite := by
  induction h with
  | nil => rw [walkVertices_nil]; exact Set.finite_singleton _
  | @cons u w v e W hl _ ih => rw [walkVertices_cons hl]; exact Set.Finite.insert u ih

/-- The graph spanned by a walk has finitely many vertices, whatever the ambient graph.
Stated as a `Set.Finite` rather than as a `Graph.Finite` instance so that this file does not
have to depend on `Schoenflies/Graph/Degree.lean`; the two halves build one in a line. -/
theorem IsWalk.finite_vertexSet_pathGraphOf (h : G.IsWalk u W v) :
    V(G.pathGraphOf u W).Finite := by
  simpa using h.finite_walkVertices

theorem IsWalk.finite_edgeSet_pathGraphOf (h : G.IsWalk u W v) :
    E(G.pathGraphOf u W).Finite := by
  rw [pathGraphOf_edgeSet h]; exact List.finite_toSet W

end Graph

end BundlePart390
