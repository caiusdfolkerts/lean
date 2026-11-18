module

public import canonical_main.PalomarPart006
import all canonical_main.PalomarPart006
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

section BundlePart382
/- Source: dev/planar_search/schoenflies_port/Schoenflies/Graph/VertexSquares.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/





/-!
# The vertex squares, the last parameter inside a closed set, and the cores

Three of the ordinary bricks of the polygonal redrawing of a finite plane graph.

**The vertex squares.** Around each vertex of a finite plane graph sits a closed axis-parallel
square which meets no other vertex and no edge arc of an edge not incident with that vertex.
One compact separation per other vertex and per non-incident arc, then the single-`ε`-for-all
lemma of `Schoenflies/UniformBound.lean`. Squares rather than disks because the assembly needs
the boundary to be made of segments; convexity, which the radial segments of the last step
want, both shapes have.

Because the choice is made once for all vertices rather than vertex by vertex, halving the
common radius also makes *distinct squares disjoint* — which the cores of the next brick need
and which the per-vertex statement does not give. That is why `exists_vertexSquares` is the
form to consume and `exists_square_at` only its ingredient.

**The last parameter inside a closed set.** The parameters at which an arc lies in a closed
set form a compact subset of the parameter interval; if it is nonempty its supremum is
attained, and past that supremum the arc has left the set for good. The mirror statement about
the infimum is what the far end of an edge wants: the arc leaves the square at `v` for the last
time and enters the square at `w` for the first time.

**The cores.** The subarc of an edge between those two parameters. It meets the square at `v`
in its own first endpoint only, the square at `w` in its own last endpoint only, and — the
clause the assembly really uses — it contains no vertex, which makes distinct cores disjoint
without any further estimate.

## Blueprint

Bricks B2, B3 and B4 of `lem:polygonal-redrawing`.

* `Plane.closedBall_subset_closedSquare`, `Plane.closedSquare_subset_ball` — a square sits
  inside a ball and vice versa, the comparison every separation argument passes through.
* `Plane.supDist_triangle`, `Plane.closedSquare_mono_center`, `Plane.mem_closedSquare_self` —
  square arithmetic missing from `Schoenflies/Square.lean`.
* `exists_last_mem_Icc`, `exists_first_mem_Icc`, `exists_last_mem`, `exists_first_mem` — B3,
  with `isCompact_parameters_mem` behind them.
* `Graph.IsDrawing.exists_square_at` — B2 at one vertex.
* `Graph.IsDrawing.exists_vertexSquares` — B2 as consumed: one radius for every vertex, with
  distinct squares disjoint.
* `Graph.IsDrawing.exists_core` — B4, the core of one edge.
* `Graph.IsDrawing.disjoint_of_subset_edgeArc` — B4's "distinct cores are disjoint".
* `Graph.IsDrawing.closedSquare_disjoint_edgeArc_of_ne` — B4's "meets no other vertex square",
  which is a property of the whole arc.
-/

open Metric Set unitInterval

namespace Schoenflies

namespace Plane

/-! ### Square arithmetic

`Schoenflies/Square.lean` has convexity, openness and closedness of `closedSquare` but no
triangle inequality for `supDist` and no monotonicity at a general centre; both are needed
here. -/

/-- Squares about a common centre grow with the radius. `Bounded.closedSquare_mono` says this
only about the origin. -/
theorem closedSquare_mono_center (c : Plane) {r s : ℝ} (h : r ≤ s) :
    closedSquare c r ⊆ closedSquare c s := fun _ hx => le_trans hx h

/-- The centre lies in its own square. -/
theorem mem_closedSquare_self (c : Plane) {r : ℝ} (hr : 0 ≤ r) : c ∈ closedSquare c r := by
  change supDist c c ≤ r
  rw [supDist_self]; exact hr

theorem supDist_eq_dist_le (x c : Plane) : supDist x c ≤ dist x c := by
  rw [dist_eq_norm]; exact supNorm_le_norm _

/-- The inscribed ball: a ball is inside the square of the same radius, since the sup norm is
at most the Euclidean norm. -/
theorem closedBall_subset_closedSquare (c : Plane) (r : ℝ) :
    closedBall c r ⊆ closedSquare c r := fun _ hx =>
  le_trans (supDist_eq_dist_le _ _) (mem_closedBall.1 hx)

/-- The circumscribed ball, in the form the separations want: a square of *half* a given
radius sits inside the open ball of that radius, because `√2 < 2`. -/
theorem closedSquare_subset_ball {c : Plane} {ρ : ℝ} (hρ : 0 < ρ) :
    closedSquare c (ρ / 2) ⊆ ball c ρ := by
  have hsqrt : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  intro x hx
  have hsup : supDist x c ≤ ρ / 2 := hx
  have hnorm : ‖x - c‖ ≤ Real.sqrt 2 * (ρ / 2) :=
    le_trans (norm_le_sqrt_two_mul_supNorm _)
      (mul_le_mul_of_nonneg_left hsup (Real.sqrt_nonneg 2))
  rw [mem_ball, dist_eq_norm]
  calc ‖x - c‖ ≤ Real.sqrt 2 * (ρ / 2) := hnorm
    _ < 2 * (ρ / 2) := by
        exact mul_lt_mul_of_pos_right hsqrt (by linarith)
    _ = ρ := by ring

end Plane

/-! ### B3 — the last point of an arc inside a closed set -/

/-- The parameters at which a curve lies in a closed set form a compact subset of the
parameter interval: the parametrisation is continuous there and the interval is compact.

Stated over an arbitrary `Icc` and not only over `[0, 1]`, because the *second* use of B3 —
the first entry into the far vertex's square — has to happen after the last exit from the near
one, i.e. on the interval `[a, 1]`. -/
theorem isCompact_parameters_mem {f : ℝ → Plane} {α β : ℝ} (hf : ContinuousOn f (Icc α β))
    {C : Set Plane} (hC : IsClosed C) : IsCompact {t | t ∈ Icc α β ∧ f t ∈ C} := by
  have hset : {t | t ∈ Icc α β ∧ f t ∈ C} = Icc α β ∩ f ⁻¹' C := rfl
  rw [hset]
  exact isCompact_Icc.of_isClosed_subset
    (hf.preimage_isClosed_of_isClosed isClosed_Icc hC) inter_subset_left

/-- The last parameter inside a closed set. Given one parameter whose point lies in `C`, there
is a largest one: the curve is in `C` there, and at every larger parameter of the interval it
has left `C` for good.

This is the supremum of a nonempty compact set of parameters, which is therefore attained. -/
theorem exists_last_mem_Icc {f : ℝ → Plane} {α β : ℝ} (hf : ContinuousOn f (Icc α β))
    {C : Set Plane} (hC : IsClosed C) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc α β) (hmem : f t₀ ∈ C) :
    ∃ s ∈ Icc α β, t₀ ≤ s ∧ f s ∈ C ∧ ∀ t ∈ Icc α β, s < t → f t ∉ C := by
  set S : Set ℝ := {t | t ∈ Icc α β ∧ f t ∈ C} with hS
  have hcpt : IsCompact S := isCompact_parameters_mem hf hC
  have hne : S.Nonempty := ⟨t₀, ht₀, hmem⟩
  obtain ⟨hsI, hsC⟩ : sSup S ∈ S := hcpt.sSup_mem hne
  refine ⟨sSup S, hsI, le_csSup hcpt.bddAbove ⟨ht₀, hmem⟩, hsC, fun t htI hlt htC => ?_⟩
  -- A parameter past the supremum that still lands in `C` would be a member above it.
  exact absurd (le_csSup hcpt.bddAbove ⟨htI, htC⟩) (not_le.2 hlt)

/-- The mirror of `exists_last_mem_Icc`: the first parameter inside a closed set. Before it the
curve has not yet reached `C`. -/
theorem exists_first_mem_Icc {f : ℝ → Plane} {α β : ℝ} (hf : ContinuousOn f (Icc α β))
    {C : Set Plane} (hC : IsClosed C) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc α β) (hmem : f t₀ ∈ C) :
    ∃ s ∈ Icc α β, s ≤ t₀ ∧ f s ∈ C ∧ ∀ t ∈ Icc α β, t < s → f t ∉ C := by
  set S : Set ℝ := {t | t ∈ Icc α β ∧ f t ∈ C} with hS
  have hcpt : IsCompact S := isCompact_parameters_mem hf hC
  have hne : S.Nonempty := ⟨t₀, ht₀, hmem⟩
  obtain ⟨hsI, hsC⟩ : sInf S ∈ S := hcpt.sInf_mem hne
  refine ⟨sInf S, hsI, csInf_le hcpt.bddBelow ⟨ht₀, hmem⟩, hsC, fun t htI hlt htC => ?_⟩
  exact absurd (csInf_le hcpt.bddBelow ⟨htI, htC⟩) (not_le.2 hlt)

/-- B3 on the unit interval: the last parameter at which an arc is inside a closed set. -/
theorem exists_last_mem {f : ℝ → Plane} (hf : ContinuousOn f I) {C : Set Plane}
    (hC : IsClosed C) {t₀ : ℝ} (ht₀ : t₀ ∈ I) (hmem : f t₀ ∈ C) :
    ∃ s ∈ I, t₀ ≤ s ∧ f s ∈ C ∧ ∀ t ∈ I, s < t → f t ∉ C :=
  exists_last_mem_Icc hf hC ht₀ hmem

/-- B3 on the unit interval, at the other end: the first parameter at which an arc is inside a
closed set. -/
theorem exists_first_mem {f : ℝ → Plane} (hf : ContinuousOn f I) {C : Set Plane}
    (hC : IsClosed C) {t₀ : ℝ} (ht₀ : t₀ ∈ I) (hmem : f t₀ ∈ C) :
    ∃ s ∈ I, s ≤ t₀ ∧ f s ∈ C ∧ ∀ t ∈ I, t < s → f t ∉ C :=
  exists_first_mem_Icc hf hC ht₀ hmem

end Schoenflies

/-! ### B2 — the vertex squares -/

open Schoenflies
open scoped Graph

namespace Graph

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}

/-- A vertex lies on no arc of an edge it is not incident with: the arc meets the vertex set
only at its own two ends, and those are the vertices it is incident with. -/
theorem IsDrawing.notMem_edgeArc_of_not_inc (h : IsDrawing G drawing) {e : β} (he : e ∈ E(G))
    {v : Plane} (hv : v ∈ V(G)) (hinc : ¬ G.Inc e v) : v ∉ edgeArc drawing e := by
  intro hmem
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
  rcases h.vertex_mem_edgeArc hxy hv hmem with rfl | rfl
  · exact hinc hxy.inc_left
  · exact hinc hxy.inc_right

/-- B2 at a single vertex: a closed square about `v` meeting no other vertex and no arc of an
edge not incident with `v`.

The two families are separated the same way — one compact separation each, then the common
positive bound of `exists_pos_forall_of_finite` — and the two radii are then merged by taking
the smaller, which is legitimate because shrinking a square preserves "meets nothing". -/
theorem IsDrawing.exists_square_at [G.Finite] (h : IsDrawing G drawing) {v : Plane}
    (hv : v ∈ V(G)) :
    ∃ r > 0, (∀ w ∈ V(G), w ≠ v → w ∉ Plane.closedSquare v r) ∧
      ∀ e ∈ E(G), ¬ G.Inc e v → Disjoint (Plane.closedSquare v r) (edgeArc drawing e) := by
  -- The other vertices.
  obtain ⟨r₁, hr₁, hvert⟩ :
      ∃ r > 0, ∀ w ∈ V(G), w ≠ v → w ∉ Plane.closedSquare v r := by
    refine exists_pos_forall_of_finite (Graph.finite_vertexSet (G := G))
      (P := fun w r => w ≠ v → w ∉ Plane.closedSquare v r) ?_ ?_
    · exact fun w δ ε _ hδε hP hne hmem =>
        hP hne (Plane.closedSquare_mono_center v hδε hmem)
    · intro w hw
      by_cases hwv : w = v
      · exact ⟨1, one_pos, fun hne => absurd hwv hne⟩
      · -- `w` is at positive Euclidean distance from `v`, and a square of half that radius
        -- sits inside the ball of that radius.
        have hpos : 0 < dist w v := dist_pos.2 hwv
        refine ⟨dist w v / 2, by linarith, fun _ hmem => ?_⟩
        exact absurd (mem_ball.1 (Plane.closedSquare_subset_ball hpos hmem)) (by simp)
  -- The non-incident edges.
  obtain ⟨r₂, hr₂, hedge⟩ :
      ∃ r > 0, ∀ e ∈ E(G), ¬ G.Inc e v →
        Disjoint (Plane.closedSquare v r) (edgeArc drawing e) := by
    refine exists_pos_forall_of_finite (Graph.finite_edgeSet (G := G))
      (P := fun e r => ¬ G.Inc e v → Disjoint (Plane.closedSquare v r) (edgeArc drawing e))
      ?_ ?_
    · exact fun e δ ε _ hδε hP hinc =>
        Set.disjoint_of_subset_left (Plane.closedSquare_mono_center v hδε) (hP hinc)
    · intro e he
      by_cases hinc : G.Inc e v
      · exact ⟨1, one_pos, fun h' => absurd hinc h'⟩
      · have hdisj : Disjoint ({v} : Set Plane) (edgeArc drawing e) :=
          Set.disjoint_singleton_left.2 (h.notMem_edgeArc_of_not_inc he hv hinc)
        obtain ⟨ρ, hρ, hsep⟩ :=
          Plane.exists_dist_pos isCompact_singleton (h.isCompact_edgeArc he) hdisj
        refine ⟨ρ / 2, by linarith, fun _ => Set.disjoint_left.2 fun x hx hxe => ?_⟩
        have hclose : dist x v < ρ := mem_ball.1 (Plane.closedSquare_subset_ball hρ hx)
        have hfar : ρ ≤ dist v x := hsep v rfl x hxe
        rw [dist_comm] at hfar
        linarith
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun w hw hne hmem => ?_, fun e he hinc => ?_⟩
  · exact hvert w hw hne (Plane.closedSquare_mono_center v (min_le_left _ _) hmem)
  · exact Set.disjoint_of_subset_left
      (Plane.closedSquare_mono_center v (min_le_right _ _)) (hedge e he hinc)

/-- B2 as its consumers want it: **one** radius serving every vertex at once, with the squares
about distinct vertices disjoint.

Disjointness is not a consequence of the per-vertex statement — a square about `v` avoiding
`w` says nothing about a square about `w` reaching towards `v`. It comes from choosing the
radius once for all vertices and then halving it: two squares of radius `r` that met would put
their centres within `2r` in the sup metric, i.e. each centre in the other's square of radius
`2r`, which the unhalved choice forbids. -/
theorem IsDrawing.exists_vertexSquares [G.Finite] (h : IsDrawing G drawing) :
    ∃ r > 0,
      (∀ v ∈ V(G), ∀ w ∈ V(G), w ≠ v → w ∉ Plane.closedSquare v r) ∧
      (∀ v ∈ V(G), ∀ e ∈ E(G), ¬ G.Inc e v →
        Disjoint (Plane.closedSquare v r) (edgeArc drawing e)) ∧
      ∀ v ∈ V(G), ∀ w ∈ V(G), v ≠ w →
        Disjoint (Plane.closedSquare v r) (Plane.closedSquare w r) := by
  -- One radius for all vertices, by the same monotone-downward bound.
  obtain ⟨r, hr, hall⟩ :
      ∃ r > 0, ∀ v ∈ V(G),
        (∀ w ∈ V(G), w ≠ v → w ∉ Plane.closedSquare v r) ∧
        ∀ e ∈ E(G), ¬ G.Inc e v →
          Disjoint (Plane.closedSquare v r) (edgeArc drawing e) := by
    refine exists_pos_forall_of_finite (Graph.finite_vertexSet (G := G))
      (P := fun v r => (∀ w ∈ V(G), w ≠ v → w ∉ Plane.closedSquare v r) ∧
        ∀ e ∈ E(G), ¬ G.Inc e v →
          Disjoint (Plane.closedSquare v r) (edgeArc drawing e)) ?_ ?_
    · rintro v δ ε _ hδε ⟨hP, hQ⟩
      exact ⟨fun w hw hne hmem => hP w hw hne (Plane.closedSquare_mono_center v hδε hmem),
        fun e he hinc =>
          Set.disjoint_of_subset_left (Plane.closedSquare_mono_center v hδε) (hQ e he hinc)⟩
    · exact fun v hv => h.exists_square_at hv
  refine ⟨r / 2, by linarith, fun v hv w hw hne hmem => ?_, fun v hv e he hinc => ?_,
    fun v hv w hw hne => Set.disjoint_left.2 fun x hxv hxw => ?_⟩
  · exact (hall v hv).1 w hw hne (Plane.closedSquare_mono_center v (by linarith) hmem)
  · exact Set.disjoint_of_subset_left (Plane.closedSquare_mono_center v (by linarith))
      ((hall v hv).2 e he hinc)
  · -- Both centres are within `r/2` of `x`, hence within `r` of each other.
    have hvx : Plane.supDist x v ≤ r / 2 := hxv
    have hwx : Plane.supDist x w ≤ r / 2 := hxw
    have : Plane.supDist w v ≤ r := by
      have := Plane.supDist_triangle w x v
      rw [Plane.supDist_comm w x] at this
      linarith
    exact (hall v hv).1 w hw (Ne.symm hne) this

/-! ### B4 — the cores -/

/-- An edge is incident only with its own two ends. -/
theorem not_inc_of_ne {e : β} {v w u : Plane} (hlink : G.IsLink e v w) (huv : u ≠ v)
    (huw : u ≠ w) : ¬ G.Inc e u := fun hinc => (hinc.eq_or_eq_of_isLink hlink).elim huv huw

/-- "The core meets no other vertex square" is really a statement about the whole arc: the
square about a vertex which is neither end of the edge misses the edge's arc entirely, by B2.
The hypothesis is exactly the second clause of `exists_vertexSquares`. -/
theorem IsDrawing.closedSquare_disjoint_edgeArc_of_ne {e : β} {v w u : Plane} {r : ℝ}
    (hsq : ∀ e ∈ E(G), ¬ G.Inc e u → Disjoint (Plane.closedSquare u r) (edgeArc drawing e))
    (hlink : G.IsLink e v w) (huv : u ≠ v) (huw : u ≠ w) :
    Disjoint (Plane.closedSquare u r) (edgeArc drawing e) :=
  hsq e hlink.edge_mem (not_inc_of_ne hlink huv huw)

/-- **Distinct cores are disjoint.** A subset of one edge's arc containing no vertex meets no
other edge's arc at all, because distinct edges meet only at vertices. Stated for arbitrary
subsets rather than for cores, since that is all the argument uses — and it is why
`exists_core` carries `Disjoint K V(G)` rather than a clause about other edges. -/
theorem IsDrawing.disjoint_of_subset_edgeArc (h : IsDrawing G drawing) {e f : β}
    (he : e ∈ E(G)) (hf : f ∈ E(G)) (hef : e ≠ f) {K L : Set Plane}
    (hK : K ⊆ edgeArc drawing e) (hKV : Disjoint K V(G)) (hL : L ⊆ edgeArc drawing f) :
    Disjoint K L :=
  Set.disjoint_left.2 fun _ hxK hxL =>
    Set.disjoint_left.1 hKV hxK (h.arcs_meet_at_vertex he hf hef (hK hxK) (hL hxL))

/-- **The core of an edge.** Between the last parameter at which the edge's arc is inside the
square about `v` and the first parameter after that at which it is inside the square about `w`
sits a subarc `K` — the core — which meets the square at `v` in its first endpoint only, meets
the square at `w` in its last endpoint only, and contains no vertex at all.

The two squares must be disjoint, which is what the uniform choice of `exists_vertexSquares`
provides; disjointness in particular forces `v ≠ w`, so **this says nothing about a loop
edge** — see the module report.

The "first entry after the last exit" is not the same as "first entry": nothing forbids the
arc from dipping into the far square and coming back, so the second application of B3 is over
`[a, 1]` and not over `[0, 1]`.

That the endpoints of the core are *not* the vertices themselves is where the positivity of
the radius is used: the arc starts at the centre of the square about `v`, so it is still
inside the square just after leaving it, and the last exit therefore happens at a positive
parameter. That fact is what makes `Disjoint K V(G)` true and hence distinct cores disjoint. -/
theorem IsDrawing.exists_core (h : IsDrawing G drawing) {e : β} {v w : Plane} {r : ℝ}
    (hr : 0 < r) (hlink : G.IsLink e v w)
    (hdisj : Disjoint (Plane.closedSquare v r) (Plane.closedSquare w r)) :
    ∃ (K : Set Plane) (p q : Plane),
      K ⊆ edgeArc drawing e ∧ IsCompact K ∧ IsArcBetween K p q ∧
      K ∩ Plane.closedSquare v r = {p} ∧ K ∩ Plane.closedSquare w r = {q} ∧
      Disjoint K V(G) := by
  obtain ⟨f, hcont, hinj, himg, hf0, hf1⟩ := h.edge_isArcBetween hlink
  have hv0 : f 0 ∈ Plane.closedSquare v r := by
    rw [hf0]; exact Plane.mem_closedSquare_self v hr.le
  have hw1 : f 1 ∈ Plane.closedSquare w r := by
    rw [hf1]; exact Plane.mem_closedSquare_self w hr.le
  -- The last exit from the square at `v` …
  obtain ⟨a, haI, -, haD, hafter⟩ :=
    exists_last_mem hcont (Plane.isClosed_closedSquare v r) zero_mem_I hv0
  have hsub : Icc a 1 ⊆ I := fun t ht => ⟨le_trans haI.1 ht.1, ht.2⟩
  -- … and the first entry into the square at `w` after it.
  obtain ⟨b, hbmem, -, hbD, hbefore⟩ :=
    exists_first_mem_Icc (hcont.mono hsub) (Plane.isClosed_closedSquare w r)
      (right_mem_Icc.2 haI.2) hw1
  have hbI : b ∈ I := hsub hbmem
  have hne : a ≠ b := by
    intro hEq
    rw [hEq] at haD
    exact Set.disjoint_left.1 hdisj haD hbD
  have hIccI : Icc a b ⊆ I := fun t ht => ⟨le_trans haI.1 ht.1, le_trans ht.2 hbmem.2⟩
  -- The core does not reach back to `v`: just after `0` the arc is still inside the square.
  have hpv : f a ≠ v := by
    intro hEq
    have ha0 : a = 0 := hinj haI zero_mem_I (by rw [hEq, hf0])
    obtain ⟨δ, hδ, hclose⟩ := Metric.continuousWithinAt_iff.mp (hcont 0 zero_mem_I) r hr
    have ht0 : 0 < min (δ / 2) 1 := lt_min (by linarith) one_pos
    have htI : min (δ / 2) 1 ∈ I := ⟨ht0.le, min_le_right _ _⟩
    have hdist : dist (min (δ / 2) 1) 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos ht0]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    refine hafter _ htI (by rw [ha0]; exact ht0) (Plane.closedBall_subset_closedSquare v r ?_)
    rw [mem_closedBall, ← hf0]
    exact (hclose htI hdist).le
  -- Symmetrically, the core does not reach forward to `w`.
  have hqw : f b ≠ w := by
    intro hEq
    have hb1 : b = 1 := hinj hbI one_mem_I (by rw [hEq, hf1])
    have halt1 : a < 1 := by rw [← hb1]; exact lt_of_le_of_ne hbmem.1 hne
    obtain ⟨δ, hδ, hclose⟩ := Metric.continuousWithinAt_iff.mp (hcont 1 one_mem_I) r hr
    have hmax1 : max (1 - δ / 2) ((a + 1) / 2) < 1 := max_lt (by linarith) (by linarith)
    have hmaxa : a ≤ max (1 - δ / 2) ((a + 1) / 2) :=
      le_trans (by linarith) (le_max_right _ _)
    have htmem : max (1 - δ / 2) ((a + 1) / 2) ∈ Icc a 1 := ⟨hmaxa, hmax1.le⟩
    have hdist : dist (max (1 - δ / 2) ((a + 1) / 2)) 1 < δ := by
      rw [Real.dist_eq, abs_of_nonpos (by linarith), neg_sub]
      have := le_max_left (1 - δ / 2) ((a + 1) / 2)
      linarith
    refine hbefore _ htmem (by rw [hb1]; exact hmax1)
      (Plane.closedBall_subset_closedSquare w r ?_)
    rw [mem_closedBall, ← hf1]
    exact (hclose (hsub htmem) hdist).le
  -- The core itself.
  have harc : IsArcBetween (f '' Icc a b) (f a) (f b) := by
    have hsubarc := isArcBetween_subarc_of_injOn_I hcont hinj haI hbI hne
    rwa [uIcc_of_le hbmem.1] at hsubarc
  have hKsub : f '' Icc a b ⊆ edgeArc drawing e := by
    rw [← himg]; exact image_mono hIccI
  have hKv : f '' Icc a b ∩ Plane.closedSquare v r = {f a} := by
    ext x
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hxD⟩
      rcases eq_or_lt_of_le ht.1 with heq | hlt
      · simp [heq]
      · exact absurd hxD (hafter t (hIccI ht) hlt)
    · rintro rfl
      exact ⟨⟨a, ⟨le_refl a, hbmem.1⟩, rfl⟩, haD⟩
  have hKw : f '' Icc a b ∩ Plane.closedSquare w r = {f b} := by
    ext x
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hxD⟩
      rcases eq_or_lt_of_le ht.2 with heq | hlt
      · simp [heq]
      · exact absurd hxD (hbefore t ⟨ht.1, le_trans ht.2 hbmem.2⟩ hlt)
    · rintro rfl
      exact ⟨⟨b, ⟨hbmem.1, le_refl b⟩, rfl⟩, hbD⟩
  refine ⟨f '' Icc a b, f a, f b, hKsub, harc.isArc.isCompact, harc, hKv, hKw,
    Set.disjoint_left.2 fun x hxK hxV => ?_⟩
  -- A vertex on the core is an end of the edge, and each end is excluded by the two facts
  -- above together with the descriptions of `K ∩ D_v` and `K ∩ D_w`.
  rcases h.vertex_mem_edgeArc hlink hxV (hKsub hxK) with heq | heq
  · have hmem : x ∈ f '' Icc a b ∩ Plane.closedSquare v r :=
      ⟨hxK, by rw [heq]; exact Plane.mem_closedSquare_self v hr.le⟩
    rw [hKv, mem_singleton_iff] at hmem
    exact hpv (hmem ▸ heq)
  · have hmem : x ∈ f '' Icc a b ∩ Plane.closedSquare w r :=
      ⟨hxK, by rw [heq]; exact Plane.mem_closedSquare_self w hr.le⟩
    rw [hKw, mem_singleton_iff] at hmem
    exact hqw (hmem ▸ heq)

end Graph

end BundlePart382

section BundlePart383
/- Source: dev/planar_search/schoenflies_port/Schoenflies/LocallyPolygonal.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/




/-!
# The plane minus finitely many open squares is locally polygonally connected

This is brick B5 of the polygonal-redrawing argument. The redrawing cuts an open axis-parallel
square out of the plane around each vertex of the graph; what the rest of the argument needs of
the leftover set `M` is that it is *locally polygonally connected* — every point of `M` has a
relatively open neighbourhood all of whose points are joined to each other by polygonal paths
running inside `M`. That is what feeds the clopen argument one level up (brick B6), where the
basic open piece is no longer a ball.

The informal description of the three basic shapes — a disk away from every square, a half-disk
against one side, a three-quarter disk at a corner — suggests an angular case analysis. There is
none here. Both the squares and the basic neighbourhoods are axis-parallel, so each shape is an
intersection of a small square with the complement of an open square, and

* the complement of an open square is the union of the four closed coordinate half-planes that
  bound it (`Plane.compl_openSquare_subset_iUnion`);
* intersecting with a small square gives four *rectangles*, each convex;
* if the small square is small enough, each of those rectangles is either empty or contains the
  centre `p` (`Plane.exists_radius_sides`).

A union of convex sets with a common point is polygonally connected by two segments through that
point, which is `isLocallyPolyConnAt_of_star`. The three shapes are then just the three ways the
list of nonempty pieces can come out (one, two adjacent, or two adjacent again with `p` on the
corner) and none of them has to be named.

The passage from one square to finitely many is a shrinking step: since the closed squares are
pairwise disjoint, a point lies in at most one of them, and a small enough neighbourhood of any
point misses all the others outright, so `M` looks locally exactly like the one-square case.

## Blueprint

* `PolyConnIn` — "joined by a polygonal path inside `S`"; the relation Lemma 1.1 produces.
* `IsLocallyPolyConn` — the local form of polygonal connectedness, brick B5's conclusion.
* `polyConnIn_of_convex`, `polyConnIn_union_of_convex` — a rectangle, and two rectangles that
  meet, are polygonally connected.
* `Plane.sideHalfPlane`, `Plane.sideGap` — the four half-planes bounding a square and the room
  between a point and each of them.
* `isLocallyPolyConnAt_compl_openSquare` — the one-square case: the complement of any open
  square is locally polygonally connected, at every point of the plane.
* `isLocallyPolyConn_compl_biUnion` — brick B5: the plane minus finitely many open squares with
  pairwise disjoint closures is locally polygonally connected.
-/

open Metric Set

namespace Schoenflies

open Plane

variable {S T : Set Plane} {x y z : Plane}

/-! ### Two list lemmas about `poly`

`PolyPath.lean` has `poly_concat`, which extends a vertex list by a single vertex. Transitivity
and symmetry of polygonal connectedness need the two-list versions; both are general facts about
`poly` and belong beside `poly_concat` rather than here. -/

/-- Reversing a vertex list does not move its carrier. -/
theorem poly_reverse : ∀ vs : List Plane, poly vs.reverse = poly vs
  | [] => by simp
  | [v] => by simp
  | u :: v :: tl => by
    rw [List.reverse_cons, poly_concat (by simp) u, poly_reverse (v :: tl),
      List.getLast_reverse (by simp), List.head_cons, poly_cons_cons, segment_symm]
    exact union_comm _ _

/-! ### Polygonal connectedness inside a set -/

/-- `x` and `y` are joined by a polygonal path lying inside `S`.

This is the relation `exists_poly_of_isPreconnected` produces; naming it lets the local statement
below be phrased without repeating the vertex-list existential. -/
def PolyConnIn (S : Set Plane) (x y : Plane) : Prop :=
  ∃ vs : List Plane, ∃ h : vs ≠ [], poly vs ⊆ S ∧ vs.head h = x ∧ vs.getLast h = y

theorem PolyConnIn.refl (hx : x ∈ S) : PolyConnIn S x x :=
  ⟨[x], by simp, by simpa using hx, rfl, rfl⟩

/-- A point joined to anything lies in the set: the carrier contains the head. -/
theorem PolyConnIn.left_mem (h : PolyConnIn S x y) : x ∈ S := by
  obtain ⟨vs, hne, hsub, hhead, -⟩ := h
  exact hhead ▸ hsub (head_mem_poly hne)

theorem PolyConnIn.right_mem (h : PolyConnIn S x y) : y ∈ S := by
  obtain ⟨vs, hne, hsub, -, hlast⟩ := h
  exact hlast ▸ hsub (getLast_mem_poly hne)

theorem PolyConnIn.mono (h : PolyConnIn S x y) (hST : S ⊆ T) : PolyConnIn T x y := by
  obtain ⟨vs, hne, hsub, hhead, hlast⟩ := h
  exact ⟨vs, hne, hsub.trans hST, hhead, hlast⟩

theorem PolyConnIn.trans (hxy : PolyConnIn S x y) (hyz : PolyConnIn S y z) :
    PolyConnIn S x z := by
  obtain ⟨vs, hv, hvS, hvh, hvl⟩ := hxy
  obtain ⟨ws, hw, hwS, hwh, hwl⟩ := hyz
  obtain ⟨w, rest, rfl⟩ := List.exists_cons_of_ne_nil hw
  simp only [List.head_cons] at hwh
  subst hwh
  refine ⟨vs ++ w :: rest, by simp, ?_, ?_, ?_⟩
  · rw [poly_append hv w rest hvl]; exact union_subset hvS hwS
  · rw [List.head_append_of_ne_nil hv]; exact hvh
  · rw [List.getLast_append_of_ne_nil _ (List.cons_ne_nil w rest)]; exact hwl

theorem PolyConnIn.symm (h : PolyConnIn S x y) : PolyConnIn S y x := by
  obtain ⟨vs, hv, hvS, hvh, hvl⟩ := h
  refine ⟨vs.reverse, by simpa using hv, ?_, ?_, ?_⟩
  · rw [poly_reverse]; exact hvS
  · rw [List.head_reverse]; exact hvl
  · rw [List.getLast_reverse]; exact hvh

/-- Convexity is the base case: the segment is already a polygonal path. -/
theorem polyConnIn_of_convex {C : Set Plane} (hC : Convex ℝ C) (hCS : C ⊆ S)
    (hx : x ∈ C) (hy : y ∈ C) : PolyConnIn S x y :=
  ⟨[x, y], by simp, by
    rw [poly_cons_cons, poly_singleton]
    exact union_subset ((hC.segment_subset hx hy).trans hCS)
      (singleton_subset_iff.2 (hCS hy)), rfl, rfl⟩

/-- Two convex pieces that meet are polygonally connected in their union — two segments through
a common point. This is the "two rectangles meeting in a rectangle" step, with the shape of the
overlap irrelevant: only that it is inhabited. -/
theorem polyConnIn_union_of_convex {C D : Set Plane} (hC : Convex ℝ C) (hD : Convex ℝ D)
    (hmeet : (C ∩ D).Nonempty) (hx : x ∈ C ∪ D) (hy : y ∈ C ∪ D) : PolyConnIn (C ∪ D) x y := by
  obtain ⟨w, hwC, hwD⟩ := hmeet
  have hxw : PolyConnIn (C ∪ D) x w := by
    rcases hx with hx | hx
    · exact polyConnIn_of_convex hC subset_union_left hx hwC
    · exact polyConnIn_of_convex hD subset_union_right hx hwD
  have hwy : PolyConnIn (C ∪ D) w y := by
    rcases hy with hy | hy
    · exact polyConnIn_of_convex hC subset_union_left hwC hy
    · exact polyConnIn_of_convex hD subset_union_right hwD hy
  exact hxw.trans hwy

/-! ### The local statement -/

/-- `S` is polygonally connected near `p`: some open `U` containing `p` has all the points of
`U ∩ S` joined to each other by polygonal paths *inside `S`*.

`U ∩ S` is the relative neighbourhood; stating it through an ambient open set avoids carrying a
subtype topology. Note the paths are required to lie in `S`, not in the neighbourhood — that is
the form brick B6's clopen argument consumes. -/
def IsLocallyPolyConnAt (S : Set Plane) (p : Plane) : Prop :=
  ∃ U : Set Plane, IsOpen U ∧ p ∈ U ∧ ∀ x ∈ U ∩ S, ∀ y ∈ U ∩ S, PolyConnIn S x y

/-- `S` is locally polygonally connected: polygonally connected near each of its points. -/
def IsLocallyPolyConn (S : Set Plane) : Prop := ∀ p ∈ S, IsLocallyPolyConnAt S p

/-- If the relative neighbourhood is itself convex there is nothing to do. -/
theorem isLocallyPolyConnAt_of_convex {U : Set Plane} {p : Plane} (hU : IsOpen U) (hpU : p ∈ U)
    (hUS : U ⊆ S) (hconv : Convex ℝ U) : IsLocallyPolyConnAt S p :=
  ⟨U, hU, hpU, fun _ hx _ hy => polyConnIn_of_convex hconv hUS hx.1 hy.1⟩

/-- The gluing step, and the whole geometric content of the three shapes: if the relative
neighbourhood is covered by convex pieces each of which is either empty or contains `p`, then
any two of its points are joined by two segments through `p`.

No piece is required to be nonempty and no piece is named, so the same statement covers the
disk, the half-disk and the three-quarter disk at once. -/
theorem isLocallyPolyConnAt_of_star {U : Set Plane} {p : Plane} {ι : Type*} {C : ι → Set Plane}
    (hU : IsOpen U) (hpU : p ∈ U) (hcover : U ∩ S ⊆ ⋃ i, C i) (hsub : ∀ i, C i ⊆ S)
    (hconv : ∀ i, Convex ℝ (C i)) (hstar : ∀ i, ∀ z ∈ C i, p ∈ C i) :
    IsLocallyPolyConnAt S p := by
  refine ⟨U, hU, hpU, fun x hx y hy => ?_⟩
  obtain ⟨i, hxi⟩ := mem_iUnion.1 (hcover hx)
  obtain ⟨j, hyj⟩ := mem_iUnion.1 (hcover hy)
  exact (polyConnIn_of_convex (hconv i) (hsub i) hxi (hstar i x hxi)).trans
    (polyConnIn_of_convex (hconv j) (hsub j) (hstar j y hyj) hyj)

/-! ### The four sides of a square -/

namespace Plane

/-- A coordinate description of the open square: it is the set of points within `r` of the
centre in each coordinate separately. -/
theorem mem_openSquare_iff (c : Plane) (r : ℝ) (x : Plane) :
    x ∈ openSquare c r ↔ ∀ i, |x i - c i| < r := by
  simp only [openSquare, mem_setOf_eq, supDist, supNorm, sub_apply, max_lt_iff,
    Fin.forall_fin_two]

/-- The centre of a square of positive radius is in it. -/
theorem mem_openSquare_self {p : Plane} {s : ℝ} (hs : 0 < s) : p ∈ openSquare p s := by
  simpa [openSquare] using hs

/-- Squares about a point grow with the radius. -/
theorem openSquare_mono {p : Plane} {s t : ℝ} (h : s ≤ t) : openSquare p s ⊆ openSquare p t :=
  fun _ hx => lt_of_lt_of_le hx h

/-- The closed half-plane on the far side of the `i`-th pair of sides of the square about `c` of
radius `r`; `b = true` picks the upper one. The four of them cover the complement of the square,
and each is convex, which is all the argument uses them for. -/
def sideHalfPlane (c : Plane) (r : ℝ) (i : Fin 2) (b : Bool) : Set Plane :=
  cond b {x | c i + r ≤ x i} {x | x i ≤ c i - r}

/-- How much room there is between `p` and the half-plane `sideHalfPlane c r i b`: positive
exactly when `p` is outside it, and an upper bound on a square radius that keeps a neighbourhood
of `p` clear of it. -/
noncomputable def sideGap (c : Plane) (r : ℝ) (p : Plane) (i : Fin 2) (b : Bool) : ℝ :=
  cond b ((c i + r) - p i) (p i - (c i - r))

theorem convex_sideHalfPlane (c : Plane) (r : ℝ) (i : Fin 2) (b : Bool) :
    Convex ℝ (sideHalfPlane c r i b) := by
  cases b
  · exact convex_coord_le i _
  · exact convex_coord_ge i _

/-- Each of the four half-planes misses the open square. -/
theorem sideHalfPlane_subset_compl (c : Plane) (r : ℝ) (i : Fin 2) (b : Bool) :
    sideHalfPlane c r i b ⊆ (openSquare c r)ᶜ := by
  intro x hx hmem
  have hlt := (mem_openSquare_iff c r x).1 hmem i
  rw [abs_lt] at hlt
  cases b
  · exact absurd (show x i ≤ c i - r from hx) (by linarith [hlt.1])
  · exact absurd (show c i + r ≤ x i from hx) (by linarith [hlt.2])

/-- The complement of an open square is covered by the four closed half-planes bounding it. -/
theorem compl_openSquare_subset_iUnion (c : Plane) (r : ℝ) :
    (openSquare c r)ᶜ ⊆ ⋃ ib : Fin 2 × Bool, sideHalfPlane c r ib.1 ib.2 := by
  intro x hx
  rw [mem_compl_iff, mem_openSquare_iff] at hx
  push Not at hx
  obtain ⟨i, hi⟩ := hx
  rcases le_abs.1 hi with h | h
  · exact mem_iUnion.2 ⟨(i, true), show c i + r ≤ x i by linarith⟩
  · exact mem_iUnion.2 ⟨(i, false), show x i ≤ c i - r by linarith⟩

/-- If the radius is at most the room between `p` and a half-plane, the square about `p` of that
radius misses the half-plane. No sign condition on the gap: when it is nonpositive the radius is
too, and the square is empty. -/
theorem openSquare_disjoint_sideHalfPlane {c : Plane} {r s : ℝ} {p : Plane} {i : Fin 2}
    {b : Bool} (hs : s ≤ sideGap c r p i b) :
    ∀ x ∈ openSquare p s, x ∉ sideHalfPlane c r i b := by
  intro x hx hmem
  have hlt := (mem_openSquare_iff p s x).1 hx i
  rw [abs_lt] at hlt
  cases b
  · exact absurd (show x i ≤ c i - r from hmem) (by
      simp only [sideGap, cond_false] at hs; linarith [hlt.1])
  · exact absurd (show c i + r ≤ x i from hmem) (by
      simp only [sideGap, cond_true] at hs; linarith [hlt.2])

/-- If there is no room between `p` and a half-plane, `p` is in it. -/
theorem mem_sideHalfPlane_of_sideGap_nonpos {c : Plane} {r : ℝ} {p : Plane} {i : Fin 2}
    {b : Bool} (h : sideGap c r p i b ≤ 0) : p ∈ sideHalfPlane c r i b := by
  cases b
  · simp only [sideGap, cond_false] at h
    exact show p i ≤ c i - r by linarith
  · simp only [sideGap, cond_true] at h
    exact show c i + r ≤ p i by linarith

/-- Each piece the sides of one square cut a small square into is an axis-parallel rectangle —
an intersection of four coordinate strips with one more coordinate half-plane — and is therefore
convex. This is the only property of the three basic shapes the argument uses. -/
theorem convex_openSquare_inter_sideHalfPlane (p : Plane) (s : ℝ) (c : Plane) (r : ℝ)
    (i : Fin 2) (b : Bool) : Convex ℝ (openSquare p s ∩ sideHalfPlane c r i b) :=
  (convex_openSquare p s).inter (convex_sideHalfPlane c r i b)

end Plane

/-! ### Choosing one radius for finitely many constraints -/

/-- A positive lower bound for whichever members of a finite family happen to be positive.
This is `exists_pos_le_of_finite` with the selection built in; the members that are nonpositive
impose nothing. -/
theorem exists_pos_le_of_pos {ι : Type*} [Finite ι] (d : ι → ℝ) :
    ∃ s > 0, ∀ i, 0 < d i → s ≤ d i := by
  obtain ⟨s, hs, hle⟩ :=
    exists_pos_le_of_finite (S := {i : ι | 0 < d i}) (Set.toFinite _) (f := d) fun _ hi => hi
  exact ⟨s, hs, fun i hi => hle i hi⟩

/-- A radius small enough that the square about `p` misses every side half-plane of the square
about `c` that `p` itself is outside of. -/
theorem Plane.exists_radius_sides (c : Plane) (r : ℝ) (p : Plane) :
    ∃ s > 0, ∀ ib : Fin 2 × Bool,
      ∀ z ∈ openSquare p s ∩ sideHalfPlane c r ib.1 ib.2,
        p ∈ openSquare p s ∩ sideHalfPlane c r ib.1 ib.2 := by
  obtain ⟨s, hs, hle⟩ := exists_pos_le_of_pos fun ib : Fin 2 × Bool => sideGap c r p ib.1 ib.2
  refine ⟨s, hs, fun ib z hz => ⟨?_, ?_⟩⟩
  · -- `p` is the centre of its own square, which is nonempty because `s > 0`.
    exact mem_openSquare_self hs
  · -- If there were room, the square about `p` would already miss this half-plane, and `z`
    -- could not be in it.
    by_contra hp
    exact openSquare_disjoint_sideHalfPlane
      (hle ib (lt_of_not_ge fun hcon => hp (mem_sideHalfPlane_of_sideGap_nonpos hcon))) z hz.1 hz.2

/-! ### The one-square case -/

/-- **The one-square case of brick B5.** The complement of an open axis-parallel square is
polygonally connected near every point of the plane.

The neighbourhood is a small square about `p`; intersected with the complement it becomes the
union of the four rectangles cut off by the sides of the big square, each convex and each either
empty or containing `p`. That is the disk / half-disk / three-quarter-disk trichotomy, with the
cases never distinguished. -/
theorem isLocallyPolyConnAt_compl_openSquare (c : Plane) (r : ℝ) (p : Plane) :
    IsLocallyPolyConnAt (openSquare c r)ᶜ p := by
  obtain ⟨s, hs, hstar⟩ := Plane.exists_radius_sides c r p
  refine isLocallyPolyConnAt_of_star (C := fun ib : Fin 2 × Bool =>
      openSquare p s ∩ sideHalfPlane c r ib.1 ib.2)
    (isOpen_openSquare p s) (mem_openSquare_self hs) ?_ ?_ ?_ hstar
  · rintro x ⟨hxU, hxM⟩
    obtain ⟨ib, hib⟩ := mem_iUnion.1 (compl_openSquare_subset_iUnion c r hxM)
    exact mem_iUnion.2 ⟨ib, hxU, hib⟩
  · exact fun ib => inter_subset_right.trans (sideHalfPlane_subset_compl c r ib.1 ib.2)
  · exact fun ib => convex_openSquare_inter_sideHalfPlane p s c r ib.1 ib.2

/-! ### Finitely many squares -/

/-- **Brick B5.** The plane minus finitely many open axis-parallel squares whose closed squares
are pairwise disjoint is locally polygonally connected.

Two steps. Away from all the closed squares a small square about `p` is convex and already
inside `M`. Otherwise `p` lies in exactly one closed square — exactly one, by disjointness — and
a small enough square about `p` misses all the others, so near `p` the set `M` *is* the
complement of that one open square and the previous theorem's decomposition applies verbatim. -/
theorem isLocallyPolyConn_compl_biUnion {A : Set Plane} (hA : A.Finite) (ρ : Plane → ℝ)
    (hdisj : ∀ c ∈ A, ∀ c' ∈ A, c ≠ c' →
      Disjoint (closedSquare c (ρ c)) (closedSquare c' (ρ c'))) :
    IsLocallyPolyConn ((⋃ c ∈ A, openSquare c (ρ c))ᶜ) := by
  intro p _
  -- The room between `p` and a square it is outside of, as a radius bound.
  have room : ∀ c : Plane, ρ c < supDist p c → ∀ s ≤ supDist p c - ρ c,
      ∀ x ∈ openSquare p s, x ∉ openSquare c (ρ c) := by
    intro c _ s hs x hx hmem
    have h₁ : supDist x p < s := hx
    have h₂ : supDist x c < ρ c := hmem
    have := supDist_triangle p x c
    rw [supDist_comm p x] at this
    linarith
  by_cases hnear : ∃ c₀ ∈ A, p ∈ closedSquare c₀ (ρ c₀)
  · -- `p` is in the closed square about `c₀`, hence outside every other closed square.
    obtain ⟨c₀, hc₀A, hpc₀⟩ := hnear
    have hfar : ∀ c ∈ A \ {c₀}, 0 < supDist p c - ρ c := by
      rintro c ⟨hcA, hcne⟩
      have : p ∉ closedSquare c (ρ c) :=
        Set.disjoint_left.1 (hdisj c₀ hc₀A c hcA fun h => hcne (h ▸ rfl)) hpc₀
      simp only [closedSquare, mem_setOf_eq, not_le] at this
      linarith
    obtain ⟨s₁, hs₁, hs₁le⟩ := exists_pos_le_of_finite (hA.sdiff (t := {c₀}))
      (f := fun c => supDist p c - ρ c) hfar
    obtain ⟨s₂, hs₂, hstar⟩ := Plane.exists_radius_sides c₀ (ρ c₀) p
    set s := min s₁ s₂ with hsdef
    have hs : 0 < s := lt_min hs₁ hs₂
    have hpU : p ∈ openSquare p s := mem_openSquare_self hs
    -- Near `p`, the set `M` is exactly the complement of the one open square about `c₀`.
    have hloc : openSquare p s ∩ (⋃ c ∈ A, openSquare c (ρ c))ᶜ
        ⊆ openSquare p s ∩ (openSquare c₀ (ρ c₀))ᶜ := by
      rintro x ⟨hxU, hxM⟩
      exact ⟨hxU, fun hcon => hxM (mem_biUnion hc₀A hcon)⟩
    have hback : ∀ x ∈ openSquare p s, x ∉ openSquare c₀ (ρ c₀) →
        x ∈ (⋃ c ∈ A, openSquare c (ρ c))ᶜ := by
      intro x hxU hx₀ hcon
      obtain ⟨c, hcA, hxc⟩ := mem_iUnion₂.1 hcon
      rcases eq_or_ne c c₀ with rfl | hcne
      · exact hx₀ hxc
      · exact room c (by linarith [hfar c ⟨hcA, hcne⟩]) s
          (le_trans (min_le_left _ _) (hs₁le c ⟨hcA, hcne⟩)) x hxU hxc
    refine isLocallyPolyConnAt_of_star (C := fun ib : Fin 2 × Bool =>
        openSquare p s ∩ sideHalfPlane c₀ (ρ c₀) ib.1 ib.2)
      (isOpen_openSquare p s) hpU ?_ ?_ ?_ ?_
    · rintro x hx
      obtain ⟨hxU, hx₀⟩ := hloc hx
      obtain ⟨ib, hib⟩ := mem_iUnion.1 (compl_openSquare_subset_iUnion c₀ (ρ c₀) hx₀)
      exact mem_iUnion.2 ⟨ib, hxU, hib⟩
    · rintro ib x ⟨hxU, hxH⟩
      exact hback x hxU (sideHalfPlane_subset_compl c₀ (ρ c₀) ib.1 ib.2 hxH)
    · exact fun ib => convex_openSquare_inter_sideHalfPlane p s c₀ (ρ c₀) ib.1 ib.2
    · -- Shrinking the radius from `s₂` to `s` keeps every nonempty piece through `p`.
      rintro ib z ⟨hzU, hzH⟩
      refine ⟨hpU, ?_⟩
      have : z ∈ openSquare p s₂ ∩ sideHalfPlane c₀ (ρ c₀) ib.1 ib.2 :=
        ⟨openSquare_mono (min_le_right s₁ s₂) hzU, hzH⟩
      exact (hstar ib z this).2
  · -- `p` is outside every closed square, so a small square about `p` lies wholly in `M`.
    push Not at hnear
    have hfar : ∀ c ∈ A, 0 < supDist p c - ρ c := by
      intro c hcA
      have := hnear c hcA
      simp only [closedSquare, mem_setOf_eq, not_le] at this
      linarith
    obtain ⟨s, hs, hsle⟩ := exists_pos_le_of_finite hA (f := fun c => supDist p c - ρ c) hfar
    refine isLocallyPolyConnAt_of_convex (isOpen_openSquare p s)
      (mem_openSquare_self hs) ?_ (convex_openSquare p s)
    intro x hx hcon
    obtain ⟨c, hcA, hxc⟩ := mem_iUnion₂.1 hcon
    exact room c (by linarith [hfar c hcA]) s (hsle c hcA) x hx hxc

end Schoenflies

end BundlePart383

section BundlePart384
/- Source: dev/planar_search/schoenflies_port/Schoenflies/PolygonalCarrier.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/


/-!
# Polygonal connectedness over a carrier

`Schoenflies.exists_poly_of_isPreconnected` joins two points of an *open* connected subset
of the plane by a polygonal path. The redrawing argument needs the same conclusion for a
carrier that is **not** open in the plane: the ambient set there is the plane minus finitely
many open squares, and the basic neighbourhood of a point on a square's boundary is a
half-disk or a three-quarter disk rather than a ball.

This module restates the clopen argument over an arbitrary carrier `C`. The only hypothesis
on `C` is that it is *locally polygonally connected*: every point has a relatively open
neighbourhood all of whose points it reaches by a polygonal path inside `C`. Openness of `C`
is used nowhere; the ball of the classical proof appears only in
`isLocallyPolyConnected_of_isOpen`, which is what recovers the old statement.

## Blueprint

Brick B6 of `lem:polygonal-redrawing` (H6): polygonal connectivity one level up.

* `PolyReaches` — "joined by a polygonal path inside `C`", as an inductive relation.
  **Note for the integrator:** `Schoenflies/LocallyPolygonal.lean` is being written
  concurrently and defines a relation of the same meaning; the two want unifying.
* `IsLocallyPolyConnected` — the hypothesis replacing openness.
* `PolyReaches.of_isPreconnected` — Lemma 1.1 (polygonal connectedness) over a carrier.
* `exists_poly_of_isPreconnected'` — the old `exists_poly_of_isPreconnected` re-derived from
  it, verbatim; the `example` below it is a machine check that the statements agree.
-/

open Metric Set

namespace Schoenflies

variable {C D : Set Plane} {x y z : Plane}

/-! ### Joined by a polygonal path inside a carrier -/

/-- `PolyReaches C x y`: there is a polygonal path from `x` to `y` all of whose segments lie
in `C`. Built at the far end — a path is extended by one segment at a time — because that is
the shape both halves of the clopen argument use. `refl` carries `x ∈ C` so that a constant
path witnesses membership, matching `poly [x] = {x}`. -/
inductive PolyReaches (C : Set Plane) (x : Plane) : Plane → Prop
  | refl (hx : x ∈ C) : PolyReaches C x x
  | step {y z : Plane} (h : PolyReaches C x y) (hseg : segment ℝ y z ⊆ C) : PolyReaches C x z

namespace PolyReaches

/-- A single segment inside `C` is already a polygonal path. -/
theorem of_segment (hseg : segment ℝ x y ⊆ C) : PolyReaches C x y :=
  (PolyReaches.refl (hseg (left_mem_segment ℝ x y))).step hseg

theorem left_mem (h : PolyReaches C x y) : x ∈ C := by
  induction h with
  | refl hx => exact hx
  | step _ _ ih => exact ih

theorem right_mem (h : PolyReaches C x y) : y ∈ C := by
  induction h with
  | refl hx => exact hx
  | @step _ z _ hseg _ => exact hseg (right_mem_segment ℝ _ z)

theorem trans (h₁ : PolyReaches C x y) (h₂ : PolyReaches C y z) : PolyReaches C x z := by
  induction h₂ with
  | refl _ => exact h₁
  | step _ hseg ih => exact ih.step hseg

/-- Symmetry: a path is run backwards one segment at a time, each reversed segment being the
same set. -/
theorem symm (h : PolyReaches C x y) : PolyReaches C y x := by
  induction h with
  | refl hx => exact PolyReaches.refl hx
  | @step y z _ hseg ih =>
    -- The last segment, reversed, joins `z` back to `y`; then follow the shorter path back.
    exact (of_segment (by rwa [segment_symm])).trans ih

theorem mono (hCD : C ⊆ D) (h : PolyReaches C x y) : PolyReaches D x y := by
  induction h with
  | refl hx => exact PolyReaches.refl (hCD hx)
  | step _ hseg ih => exact ih.step (hseg.trans hCD)

end PolyReaches

/-! ### The relation and the vertex-list representation agree -/

/-- A polygonal path in the sense of `PolyReaches` yields a vertex list with the carrier of
its polygon inside `C`. This is `poly_concat` used once per `step`. -/
theorem PolyReaches.exists_poly (h : PolyReaches C x y) :
    ∃ vs : List Plane, ∃ hne : vs ≠ [], poly vs ⊆ C ∧ vs.head hne = x ∧ vs.getLast hne = y := by
  induction h with
  | refl hx => exact ⟨[x], by simp, by simpa using hx, rfl, rfl⟩
  | @step _ z _ hseg ih =>
    obtain ⟨vs, hne, hsub, hhead, hlast⟩ := ih
    refine ⟨vs ++ [z], by simp, ?_, ?_, ?_⟩
    · rw [poly_concat hne z, hlast]
      exact union_subset hsub hseg
    · rw [List.head_append_of_ne_nil hne]; exact hhead
    · simp

/-- Conversely a vertex list whose polygon lies in `C` joins its ends. -/
theorem polyReaches_of_poly_subset : ∀ {vs : List Plane} (hne : vs ≠ []), poly vs ⊆ C →
    PolyReaches C (vs.head hne) (vs.getLast hne)
  | [], hne, _ => absurd rfl hne
  | [v], _, hsub => PolyReaches.refl (hsub (by simp))
  | u :: v :: rest, _, hsub => by
    rw [poly_cons_cons] at hsub
    have hstep : PolyReaches C u v :=
      PolyReaches.of_segment (subset_union_left.trans hsub)
    have hrest := polyReaches_of_poly_subset (List.cons_ne_nil v rest)
      (subset_union_right.trans hsub)
    rw [List.getLast_cons (List.cons_ne_nil v rest)]
    exact hstep.trans hrest

/-! ### Local polygonal connectedness -/

/-- `C` is locally polygonally connected when every point of `C` has a relatively open
neighbourhood in `C` each of whose points it reaches by a polygonal path inside `C`.

The neighbourhood is presented as `V ∩ C` for an ambient open `V`, which is exactly what a
relatively open neighbourhood is; the paths are only required to stay inside `C`, not inside
the neighbourhood, since that is all the clopen argument uses and it is the weaker demand on
a producer. Ball, half-disk and three-quarter disk all qualify. -/
def IsLocallyPolyConnected (C : Set Plane) : Prop :=
  ∀ w ∈ C, ∃ V : Set Plane, IsOpen V ∧ w ∈ V ∧ ∀ z ∈ V ∩ C, PolyReaches C w z

/-- The relative-openness step, stated once because the clopen argument uses it twice — for
the reachable set and, run backwards, for its relative complement.

A subset of `C` closed under "reach one more point of `C` by a polygonal path" is relatively
open in `C`. The witness is the union of all ambient open sets that are polygonally attached
to a point of `S`; no choice is needed to assemble it. -/
theorem isRelOpen_of_polyReaches_stable (hloc : IsLocallyPolyConnected C) {S : Set Plane}
    (hS : S ⊆ C) (hstable : ∀ w ∈ S, ∀ z ∈ C, PolyReaches C w z → z ∈ S) :
    ∃ U : Set Plane, IsOpen U ∧ S ⊆ U ∧ U ∩ C ⊆ S := by
  refine ⟨⋃₀ {V : Set Plane | IsOpen V ∧ ∃ w ∈ S, ∀ z ∈ V ∩ C, PolyReaches C w z},
    isOpen_sUnion fun V hV => hV.1, fun w hw => ?_, ?_⟩
  · obtain ⟨V, hVopen, hwV, hVreach⟩ := hloc w (hS hw)
    exact ⟨V, ⟨hVopen, w, hw, hVreach⟩, hwV⟩
  · rintro z ⟨⟨V, ⟨_, w, hwS, hVreach⟩, hzV⟩, hzC⟩
    exact hstable w hwS z hzC (hVreach z ⟨hzV, hzC⟩)

/-! ### The theorem -/

/-- Lemma 1.1 (polygonal connectedness) over a carrier: in a relatively connected, locally
polygonally connected set, any two points are joined by a polygonal path inside the set.

The proof is the clopen argument. The points reachable from `x` are relatively open in `C`,
and so are the unreachable ones — the same lemma, since "unreachable" is stable under
reaching too, by symmetry. `IsPreconnected C` then forbids the split. -/
theorem PolyReaches.of_isPreconnected (hloc : IsLocallyPolyConnected C)
    (hconn : IsPreconnected C) (hx : x ∈ C) (hy : y ∈ C) : PolyReaches C x y := by
  by_contra hxy
  set R : Set Plane := {w | w ∈ C ∧ PolyReaches C x w} with hRdef
  obtain ⟨U, hUopen, hRU, hUR⟩ :=
    isRelOpen_of_polyReaches_stable hloc (S := R) (fun _ hw => hw.1)
      (fun _ hw _ hzC hreach => ⟨hzC, hw.2.trans hreach⟩)
  obtain ⟨U', hU'open, hRU', hU'R⟩ :=
    isRelOpen_of_polyReaches_stable hloc (S := C \ R) (fun _ hw => hw.1)
      (fun w hw z hzC hreach => ⟨hzC, fun hzR => hw.2 ⟨hw.1, hzR.2.trans hreach.symm⟩⟩)
  obtain ⟨w, hwC, hwU, hwU'⟩ := hconn U U' hUopen hU'open
    (fun v hv => (em (v ∈ R)).imp (fun h => hRU h) (fun h => hRU' ⟨hv, h⟩))
    ⟨x, hx, hRU ⟨hx, PolyReaches.refl hx⟩⟩
    ⟨y, hy, hRU' ⟨hy, fun h => hxy h.2⟩⟩
  exact (hU'R ⟨hwU', hwC⟩).2 (hUR ⟨hwU, hwC⟩)

/-- The vertex-list reading of the carrier theorem, matching the shape `PolyPath` delivers. -/
theorem exists_poly_of_isPreconnected_of_locally (hloc : IsLocallyPolyConnected C)
    (hconn : IsPreconnected C) (hx : x ∈ C) (hy : y ∈ C) :
    ∃ vs : List Plane, ∃ h : vs ≠ [], poly vs ⊆ C ∧ vs.head h = x ∧ vs.getLast h = y :=
  (PolyReaches.of_isPreconnected hloc hconn hx hy).exists_poly

/-! ### Producers of the hypothesis -/

/-- Two convex pieces of `C` that meet make one polygonally connected piece: the bent path
through a common point. This is the shape brick B5 needs for the corner neighbourhood, which
is a disk minus an open quadrant — the union of two half-disks. -/
theorem polyReaches_union_of_convex {S T : Set Plane} (hS : Convex ℝ S) (hT : Convex ℝ T)
    (hST : (S ∩ T).Nonempty) (hsub : S ∪ T ⊆ C) (hx : x ∈ S ∪ T) (hy : y ∈ S ∪ T) :
    PolyReaches C x y := by
  obtain ⟨p, hpS, hpT⟩ := hST
  have hSC : ∀ {a b}, a ∈ S → b ∈ S → PolyReaches C a b := fun ha hb =>
    PolyReaches.of_segment ((hS.segment_subset ha hb).trans (subset_union_left.trans hsub))
  have hTC : ∀ {a b}, a ∈ T → b ∈ T → PolyReaches C a b := fun ha hb =>
    PolyReaches.of_segment ((hT.segment_subset ha hb).trans (subset_union_right.trans hsub))
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact hSC hx hy
  · exact (hSC hx hpS).trans (hTC hpT hy)
  · exact (hTC hx hpT).trans (hSC hpS hy)
  · exact hTC hx hy

/-- An open set is locally polygonally connected: the balls it contains are convex. This is
the only place a ball appears, and it is what recovers the old statement. -/
theorem isLocallyPolyConnected_of_isOpen (hC : IsOpen C) : IsLocallyPolyConnected C := by
  intro w hw
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hC w hw
  exact ⟨ball w r, isOpen_ball, mem_ball_self hr, fun z hz =>
    PolyReaches.of_segment
      (((convex_ball w r).segment_subset (mem_ball_self hr) hz.1).trans hball)⟩

/-- `PolyPath.exists_poly_of_isPreconnected`, re-derived from the carrier version. -/
theorem exists_poly_of_isPreconnected' {Ω : Set Plane} {x y : Plane} (hΩ : IsOpen Ω)
    (hconn : IsPreconnected Ω) (hx : x ∈ Ω) (hy : y ∈ Ω) :
    ∃ vs : List Plane, ∃ h : vs ≠ [], poly vs ⊆ Ω ∧ vs.head h = x ∧ vs.getLast h = y :=
  exists_poly_of_isPreconnected_of_locally (isLocallyPolyConnected_of_isOpen hΩ) hconn hx hy

-- The generalisation is genuine: this `rfl` typechecks only if the statement above is
-- literally the one `PolyPath` proves, proof irrelevance doing the rest.
example : @exists_poly_of_isPreconnected = @exists_poly_of_isPreconnected' := rfl

end Schoenflies

end BundlePart384

section BundlePart385
/- Source: dev/planar_search/schoenflies_port/Schoenflies/PolyLocal.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/



/-!
# Local polygonal connectedness, in the form brick B7 consumes

`Schoenflies/LocallyPolygonal.lean` (brick B5) and `Schoenflies/PolygonalCarrier.lean`
(brick B6) were written independently and each carries its own "joined by a polygonal path
inside a set" relation — `PolyConnIn` as an existential over vertex lists, `PolyReaches` as
an inductive relation — with its own local form. This module makes them one, and then fixes
the shape problem that stops B5 from feeding B7.

## The shape problem

Both local forms ask only that the connecting path lie in `S`:

```
IsLocallyPolyConnAt S p  :  ∃ U open ∋ p, ∀ x y ∈ U ∩ S, PolyConnIn S x y
IsLocallyPolyConnected C :  ∀ w ∈ C, ∃ V open ∋ w, ∀ z ∈ V ∩ C, PolyReaches C w z
```

That is enough for B6 — the clopen argument only needs *some* path — but it is a property
with **no local content whatsoever**: any polygonally connected `S` satisfies it with
`U = univ`. In particular it does not survive intersection with an open set, and that is
exactly what B7 needs: `U_e` is a component of a relatively open piece of `M`, and a
replacement arc has to stay inside the thin tube, not merely inside `M`.

The fix is `IsLocallyPolyConnAt'`: *arbitrarily small* neighbourhoods `U` of `p` such that
any two points of `U ∩ S` are joined **inside `U ∩ S`**. B5's proof already produces this —
its paths are two segments inside convex pieces of the small square about `p`, and the
square's radius may be shrunk freely — so nothing geometric is lost, only misstated.
`isLocallyPolyConn'_compl_openSquare` and `isLocallyPolyConn'_compl_biUnion` are B5 in the
strengthened form, and `IsLocallyPolyConn'.weaken` recovers the original statements.

## Blueprint

Brick B5 ↔ brick B6 of `lem:polygonal-redrawing` (H6), and the interface B7 uses.

* `polyConnIn_iff_polyReaches` — the two relations agree.
* `IsLocallyPolyConn.isLocallyPolyConnected`, `IsLocallyPolyConnected.isLocallyPolyConn` —
  the two weak local forms agree, so B5 as originally stated does feed B6.
* `IsLocallyPolyConnAt'`, `IsLocallyPolyConn'` — the strengthened local form.
* `isLocallyPolyConnAt'_of_convex_cover` — the strengthened star lemma: a square about `p`
  cut by convex pieces, each of which contains `p` as soon as it is nonempty.
* `isLocallyPolyConnAt'_compl_openSquare`, `isLocallyPolyConn'_compl_biUnion` — **brick B5**,
  strengthened.
* `IsLocallyPolyConn'.inter_isOpen` — shrinkability: a relatively open piece of a locally
  polygonally connected set is locally polygonally connected.
* `IsRelOpenIn`, `isRelOpenIn_connectedComponentIn` — components of relatively open subsets
  are relatively open, the fact B7 quotes for `U_e`.
* `polyReaches_of_isPreconnected_of_isRelOpenIn`, `polyReaches_connectedComponentIn` — the
  payoff: two points of a connected relatively open piece are joined *inside that piece*.
-/

open Metric Set

namespace Schoenflies

open Plane

variable {S T A B C W : Set Plane} {p x y z : Plane}

/-! ### The two relations agree

`PolyReaches.exists_poly` and `polyReaches_of_poly_subset` are both on `main`; this is the
one-line packaging that lets a producer of either relation serve a consumer of the other. -/

/-- The vertex-list relation of `LocallyPolygonal.lean` and the inductive relation of
`PolygonalCarrier.lean` are the same relation. -/
theorem polyConnIn_iff_polyReaches : PolyConnIn S x y ↔ PolyReaches S x y := by
  constructor
  · rintro ⟨vs, hne, hsub, hhead, hlast⟩
    have h := polyReaches_of_poly_subset hne hsub
    rwa [hhead, hlast] at h
  · intro h
    obtain ⟨vs, hne, hsub, hhead, hlast⟩ := h.exists_poly
    exact ⟨vs, hne, hsub, hhead, hlast⟩

alias ⟨PolyConnIn.polyReaches, PolyReaches.polyConnIn⟩ := polyConnIn_iff_polyReaches

/-! ### The two weak local forms agree

`IsLocallyPolyConn` quantifies over *pairs* of points of the neighbourhood,
`IsLocallyPolyConnected` only over paths *from the centre*; symmetry and transitivity of the
relation make the two equivalent. -/

/-- Brick B5's conclusion, read as brick B6's hypothesis. -/
theorem IsLocallyPolyConn.isLocallyPolyConnected (h : IsLocallyPolyConn S) :
    IsLocallyPolyConnected S := by
  intro w hw
  obtain ⟨U, hU, hwU, hconn⟩ := h w hw
  exact ⟨U, hU, hwU, fun z hz => (hconn w ⟨hwU, hw⟩ z hz).polyReaches⟩

/-- The converse: a path from the centre to each of two points, run backwards and forwards. -/
theorem IsLocallyPolyConnected.isLocallyPolyConn (h : IsLocallyPolyConnected S) :
    IsLocallyPolyConn S := by
  intro p hp
  obtain ⟨V, hV, hpV, hreach⟩ := h p hp
  exact ⟨V, hV, hpV, fun x hx y hy => ((hreach x hx).symm.trans (hreach y hy)).polyConnIn⟩

/-! ### Squares are a neighbourhood basis

B5 builds its neighbourhoods as axis-parallel squares, and the strengthened local form needs
them arbitrarily small inside a given open set. -/

namespace Plane

/-- A square of half a radius sits inside the ball of that radius, because `√2 < 2`. The open
counterpart of `Plane.closedSquare_subset_ball`, restated here so that this module does not
have to import the graph layer. No sign condition on the radius: for `ε ≤ 0` the square is
already empty. -/
theorem openSquare_subset_ball (p : Plane) (ε : ℝ) : openSquare p (ε / 2) ⊆ ball p ε := by
  have hsqrt : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  intro x hx
  have hsup : supDist x p < ε / 2 := hx
  have hnorm : ‖x - p‖ ≤ Real.sqrt 2 * supDist x p := norm_le_sqrt_two_mul_supNorm _
  rw [mem_ball, dist_eq_norm]
  nlinarith [supDist_nonneg x p]

/-- Inside any open set around `p` there is a square about `p`, of radius at most any
prescribed positive bound. -/
theorem exists_openSquare_subset {W : Set Plane} {p : Plane} (hW : IsOpen W) (hp : p ∈ W)
    {s₀ : ℝ} (hs₀ : 0 < s₀) : ∃ s, 0 < s ∧ s ≤ s₀ ∧ openSquare p s ⊆ W := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hW p hp
  exact ⟨min s₀ (ε / 2), lt_min hs₀ (by linarith), min_le_left _ _,
    (openSquare_mono (min_le_right _ _)).trans ((openSquare_subset_ball p ε).trans hball)⟩

end Plane

/-! ### The strengthened local form -/

/-- `S` is polygonally connected near `p` **inside arbitrarily small neighbourhoods**: for
every open `W` containing `p` there is an open `U ⊆ W` containing `p` such that any two points
of `U ∩ S` are joined by a polygonal path lying in `U ∩ S`.

Two strengthenings over `IsLocallyPolyConnAt`, and both are needed by brick B7. The path is
confined to the neighbourhood, not merely to `S`, because a replacement arc has to stay in its
tube; and the neighbourhoods run through a basis at `p`, because otherwise the property does
not survive intersecting `S` with an open set (`IsLocallyPolyConn'.inter_isOpen`). -/
def IsLocallyPolyConnAt' (S : Set Plane) (p : Plane) : Prop :=
  ∀ W : Set Plane, IsOpen W → p ∈ W →
    ∃ U : Set Plane, IsOpen U ∧ p ∈ U ∧ U ⊆ W ∧
      ∀ x ∈ U ∩ S, ∀ y ∈ U ∩ S, PolyReaches (U ∩ S) x y

/-- `S` is locally polygonally connected in the strengthened sense. -/
def IsLocallyPolyConn' (S : Set Plane) : Prop := ∀ p ∈ S, IsLocallyPolyConnAt' S p

theorem IsLocallyPolyConnAt'.weaken (h : IsLocallyPolyConnAt' S p) :
    IsLocallyPolyConnAt S p := by
  obtain ⟨U, hU, hpU, -, hpath⟩ := h univ isOpen_univ (mem_univ p)
  exact ⟨U, hU, hpU, fun x hx y hy => ((hpath x hx y hy).mono inter_subset_right).polyConnIn⟩

/-- The strengthened form implies the original brick B5 statement, so nothing is lost by
replacing one with the other. -/
theorem IsLocallyPolyConn'.weaken (h : IsLocallyPolyConn' S) : IsLocallyPolyConn S :=
  fun p hp => (h p hp).weaken

/-- What brick B6 consumes. -/
theorem IsLocallyPolyConn'.isLocallyPolyConnected (h : IsLocallyPolyConn' S) :
    IsLocallyPolyConnected S := h.weaken.isLocallyPolyConnected

/-- The property is local: only the trace of `S` on a neighbourhood of `p` matters. This is
what reduces "finitely many squares" to "one square". -/
theorem IsLocallyPolyConnAt'.congr_nhds {V : Set Plane} (h : IsLocallyPolyConnAt' T p)
    (hV : IsOpen V) (hpV : p ∈ V) (heq : S ∩ V = T ∩ V) : IsLocallyPolyConnAt' S p := by
  intro W hW hpW
  obtain ⟨U, hU, hpU, hUsub, hpath⟩ := h (W ∩ V) (hW.inter hV) ⟨hpW, hpV⟩
  have hUV : U ⊆ V := hUsub.trans inter_subset_right
  have hUST : U ∩ S = U ∩ T := by
    ext x
    constructor
    · rintro ⟨hxU, hxS⟩
      exact ⟨hxU, (heq.subset ⟨hxS, hUV hxU⟩).1⟩
    · rintro ⟨hxU, hxT⟩
      exact ⟨hxU, (heq.symm.subset ⟨hxT, hUV hxU⟩).1⟩
  refine ⟨U, hU, hpU, hUsub.trans inter_subset_left, ?_⟩
  rw [hUST]
  exact hpath

/-- A neighbourhood of `p` already inside `S` settles the point: shrink it to a square, which
is convex, so a single segment joins any two of its points. -/
theorem isLocallyPolyConnAt'_of_nbhd_subset {V : Set Plane} (hV : IsOpen V) (hpV : p ∈ V)
    (hVS : V ⊆ S) : IsLocallyPolyConnAt' S p := by
  intro W hW hpW
  obtain ⟨s, hs, -, hsub⟩ := Plane.exists_openSquare_subset (hV.inter hW) ⟨hpV, hpW⟩ one_pos
  refine ⟨openSquare p s, isOpen_openSquare p s, mem_openSquare_self hs,
    hsub.trans inter_subset_right, fun x hx y hy => PolyReaches.of_segment ?_⟩
  exact ((convex_openSquare p s).segment_subset hx.1 hy.1).trans
    fun w hw => ⟨hw, hVS (hsub hw).1⟩

/-- An open set is locally polygonally connected in the strengthened sense. -/
theorem isLocallyPolyConn'_of_isOpen (hS : IsOpen S) : IsLocallyPolyConn' S :=
  fun _ hp => isLocallyPolyConnAt'_of_nbhd_subset hS hp Subset.rfl

/-- **The strengthened star lemma**, and the whole geometric content of brick B5's three
shapes. Suppose that inside one square about `p` the trace of `S` is covered by convex sets
`H i`, that each `H i` meets that square only inside `S`, and that each `H i` which meets the
square contains `p`. Then `S` is locally polygonally connected at `p` in the strengthened
sense.

Two points of a small square about `p` are then joined by two segments through `p`, each
inside one convex piece of that *small* square — which is why the path never leaves the
neighbourhood. No piece is required to be nonempty and none is named, so the disk, the
half-disk and the three-quarter disk are all this statement. -/
theorem isLocallyPolyConnAt'_of_convex_cover {ι : Type*} {H : ι → Set Plane} {s₀ : ℝ}
    (hs₀ : 0 < s₀) (hconv : ∀ i, Convex ℝ (H i))
    (hsub : ∀ i, openSquare p s₀ ∩ H i ⊆ S)
    (hcover : openSquare p s₀ ∩ S ⊆ ⋃ i, H i)
    (hstar : ∀ i, ∀ z ∈ openSquare p s₀ ∩ H i, p ∈ H i) :
    IsLocallyPolyConnAt' S p := by
  intro W hW hpW
  obtain ⟨s, hs, hss₀, hsW⟩ := Plane.exists_openSquare_subset hW hpW hs₀
  have hmono : openSquare p s ⊆ openSquare p s₀ := openSquare_mono hss₀
  have hpiece : ∀ i, openSquare p s ∩ H i ⊆ openSquare p s ∩ S :=
    fun i _ hx => ⟨hx.1, hsub i ⟨hmono hx.1, hx.2⟩⟩
  -- Every point of the small relative square is joined to the centre by one segment.
  have hto : ∀ x ∈ openSquare p s ∩ S, PolyReaches (openSquare p s ∩ S) x p := by
    intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.1 (hcover ⟨hmono hx.1, hx.2⟩)
    refine PolyReaches.of_segment (Subset.trans ?_ (hpiece i))
    exact ((convex_openSquare p s).inter (hconv i)).segment_subset ⟨hx.1, hxi⟩
      ⟨mem_openSquare_self hs, hstar i x ⟨hmono hx.1, hxi⟩⟩
  exact ⟨openSquare p s, isOpen_openSquare p s, mem_openSquare_self hs, hsW,
    fun x hx y hy => (hto x hx).trans (hto y hy).symm⟩

/-! ### Brick B5, strengthened

The two theorems of `LocallyPolygonal.lean`, reproved in the strengthened form. The geometry
is unchanged — `Plane.exists_radius_sides` still does all the work — because the pieces the
old proof used were already inside the neighbourhood; only the statement moves. -/

/-- **The one-square case of brick B5, strengthened.** The complement of an open axis-parallel
square is polygonally connected near every point of the plane, by paths confined to the
neighbourhood. -/
theorem isLocallyPolyConnAt'_compl_openSquare (c : Plane) (r : ℝ) (p : Plane) :
    IsLocallyPolyConnAt' (openSquare c r)ᶜ p := by
  obtain ⟨s, hs, hstar⟩ := Plane.exists_radius_sides c r p
  refine isLocallyPolyConnAt'_of_convex_cover
    (H := fun ib : Fin 2 × Bool => sideHalfPlane c r ib.1 ib.2) hs
    (fun ib => convex_sideHalfPlane c r ib.1 ib.2)
    (fun ib => inter_subset_right.trans (sideHalfPlane_subset_compl c r ib.1 ib.2))
    (fun x hx => compl_openSquare_subset_iUnion c r hx.2)
    (fun ib z hz => (hstar ib z hz).2)

/-- **Brick B5, strengthened.** The plane minus finitely many open axis-parallel squares whose
closed squares are pairwise disjoint is locally polygonally connected, with the connecting
paths confined to the neighbourhood.

The two cases are unchanged. Away from all the closed squares a small square about `p` lies
inside `M` outright. Otherwise `p` lies in exactly one closed square, and a small enough square
about `p` misses all the others, so near `p` the set `M` *is* the complement of that one open
square — which is what `IsLocallyPolyConnAt'.congr_nhds` says suffices. -/
theorem isLocallyPolyConn'_compl_biUnion {Q : Set Plane} (hQ : Q.Finite) (ρ : Plane → ℝ)
    (hdisj : ∀ c ∈ Q, ∀ c' ∈ Q, c ≠ c' →
      Disjoint (closedSquare c (ρ c)) (closedSquare c' (ρ c'))) :
    IsLocallyPolyConn' ((⋃ c ∈ Q, openSquare c (ρ c))ᶜ) := by
  intro p _
  -- The room between `p` and a square it is outside of, as a radius bound.
  have room : ∀ c : Plane, ∀ s ≤ supDist p c - ρ c,
      ∀ x ∈ openSquare p s, x ∉ openSquare c (ρ c) := by
    intro c s hs x hx hmem
    have h₁ : supDist x p < s := hx
    have h₂ : supDist x c < ρ c := hmem
    have := supDist_triangle p x c
    rw [supDist_comm p x] at this
    linarith
  by_cases hnear : ∃ c₀ ∈ Q, p ∈ closedSquare c₀ (ρ c₀)
  · -- `p` is in the closed square about `c₀`, hence outside every other closed square.
    obtain ⟨c₀, hc₀Q, hpc₀⟩ := hnear
    have hfar : ∀ c ∈ Q \ {c₀}, 0 < supDist p c - ρ c := by
      rintro c ⟨hcQ, hcne⟩
      have : p ∉ closedSquare c (ρ c) :=
        Set.disjoint_left.1 (hdisj c₀ hc₀Q c hcQ fun h => hcne (h ▸ rfl)) hpc₀
      simp only [closedSquare, mem_setOf_eq, not_le] at this
      linarith
    obtain ⟨s, hs, hsle⟩ := exists_pos_le_of_finite (hQ.sdiff (t := {c₀}))
      (f := fun c => supDist p c - ρ c) hfar
    refine (isLocallyPolyConnAt'_compl_openSquare c₀ (ρ c₀) p).congr_nhds
      (isOpen_openSquare p s) (mem_openSquare_self hs) ?_
    ext x
    constructor
    · rintro ⟨hxM, hxU⟩
      exact ⟨fun hcon => hxM (mem_biUnion hc₀Q hcon), hxU⟩
    · rintro ⟨hx₀, hxU⟩
      refine ⟨fun hcon => ?_, hxU⟩
      obtain ⟨c, hcQ, hxc⟩ := mem_iUnion₂.1 hcon
      rcases eq_or_ne c c₀ with rfl | hcne
      · exact hx₀ hxc
      · exact room c s (hsle c ⟨hcQ, hcne⟩) x hxU hxc
  · -- `p` is outside every closed square, so a small square about `p` lies wholly in `M`.
    push Not at hnear
    have hfar : ∀ c ∈ Q, 0 < supDist p c - ρ c := by
      intro c hcQ
      have := hnear c hcQ
      simp only [closedSquare, mem_setOf_eq, not_le] at this
      linarith
    obtain ⟨s, hs, hsle⟩ := exists_pos_le_of_finite hQ (f := fun c => supDist p c - ρ c) hfar
    refine isLocallyPolyConnAt'_of_nbhd_subset (isOpen_openSquare p s) (mem_openSquare_self hs)
      fun x hx hcon => ?_
    obtain ⟨c, hcQ, hxc⟩ := mem_iUnion₂.1 hcon
    exact room c s (hsle c hcQ) x hx hxc

-- A machine check that the strengthened form subsumes the original brick B5: this typechecks
-- only if the two statements line up on the nose.
example {Q : Set Plane} (hQ : Q.Finite) (ρ : Plane → ℝ)
    (hdisj : ∀ c ∈ Q, ∀ c' ∈ Q, c ≠ c' →
      Disjoint (closedSquare c (ρ c)) (closedSquare c' (ρ c'))) :
    IsLocallyPolyConn ((⋃ c ∈ Q, openSquare c (ρ c))ᶜ) :=
  (isLocallyPolyConn'_compl_biUnion hQ ρ hdisj).weaken

example (c : Plane) (r : ℝ) (p : Plane) : IsLocallyPolyConnAt (openSquare c r)ᶜ p :=
  (isLocallyPolyConnAt'_compl_openSquare c r p).weaken

/-! ### Shrinkability

The point of the strengthening. `IsLocallyPolyConn` does **not** have this property: it holds
for any polygonally connected `S` with `U = univ`, and the comb space — the segments
`{0} × [0,1]`, `{1/n} × [0,1]` and `[0,1] × {0}` — is polygonally connected while its
intersection with a thin open strip about `y = 1` is not locally polygonally connected at
`(0,1)`. -/

/-- **Shrinkability.** A relatively open piece of a locally polygonally connected set is
locally polygonally connected. Taking the neighbourhood inside `W` is what makes this work,
and it is the reason `IsLocallyPolyConnAt'` quantifies over all open `W ∋ p`. -/
theorem IsLocallyPolyConnAt'.inter_isOpen (h : IsLocallyPolyConnAt' S p) (hW : IsOpen W)
    (hpW : p ∈ W) : IsLocallyPolyConnAt' (S ∩ W) p := by
  intro W' hW' hpW'
  obtain ⟨U, hU, hpU, hUsub, hpath⟩ := h (W ∩ W') (hW.inter hW') ⟨hpW, hpW'⟩
  have hUW : U ⊆ W := hUsub.trans inter_subset_left
  have hUS : U ∩ (S ∩ W) = U ∩ S :=
    Subset.antisymm (fun _ hx => ⟨hx.1, hx.2.1⟩) fun _ hx => ⟨hx.1, hx.2, hUW hx.1⟩
  refine ⟨U, hU, hpU, hUsub.trans inter_subset_right, ?_⟩
  rw [hUS]
  exact hpath

theorem IsLocallyPolyConn'.inter_isOpen (h : IsLocallyPolyConn' S) (hW : IsOpen W) :
    IsLocallyPolyConn' (S ∩ W) :=
  fun _ hp => (h _ hp.1).inter_isOpen hW hp.2

/-! ### Relatively open subsets and their components -/

/-- `A` is relatively open in `S`: cut out of `S` by an ambient open set. -/
def IsRelOpenIn (S A : Set Plane) : Prop := ∃ W : Set Plane, IsOpen W ∧ A = S ∩ W

theorem IsRelOpenIn.subset (h : IsRelOpenIn S A) : A ⊆ S := by
  obtain ⟨W, -, rfl⟩ := h
  exact inter_subset_left

theorem isRelOpenIn_self (S : Set Plane) : IsRelOpenIn S S :=
  ⟨univ, isOpen_univ, (inter_univ S).symm⟩

theorem IsOpen.isRelOpenIn (hA : IsOpen A) (hAS : A ⊆ S) : IsRelOpenIn S A :=
  ⟨A, hA, (inter_eq_self_of_subset_right hAS).symm⟩

/-- The shape `isRelOpen_of_polyReaches_stable` delivers, read as relative openness. -/
theorem isRelOpenIn_of_exists (hAS : A ⊆ S) (h : ∃ U : Set Plane, IsOpen U ∧ A ⊆ U ∧ U ∩ S ⊆ A) :
    IsRelOpenIn S A := by
  obtain ⟨U, hU, hAU, hUA⟩ := h
  exact ⟨U, hU, Subset.antisymm (fun _ hx => ⟨hAS hx, hAU hx⟩) fun _ hx => hUA ⟨hx.2, hx.1⟩⟩

/-- Relative openness is transitive, which is how a component of a relatively open piece is
seen to be relatively open in the ambient set. -/
theorem IsRelOpenIn.trans (hA : IsRelOpenIn S A) (hB : IsRelOpenIn A B) : IsRelOpenIn S B := by
  obtain ⟨W, hW, rfl⟩ := hA
  obtain ⟨W', hW', rfl⟩ := hB
  exact ⟨W ∩ W', hW.inter hW', by rw [inter_assoc]⟩

/-- Shrinkability, phrased for a relatively open piece. -/
theorem IsLocallyPolyConn'.of_isRelOpenIn (h : IsLocallyPolyConn' S) (hA : IsRelOpenIn S A) :
    IsLocallyPolyConn' A := by
  obtain ⟨W, hW, rfl⟩ := hA
  exact h.inter_isOpen hW

/-- **Components of relatively open subsets are relatively open.** For `S` locally polygonally
connected and `A` relatively open in `S`, each connected component of `A` is relatively open
in `S`.

The proof is `isRelOpen_of_polyReaches_stable`: a polygonal path inside `A` is a connected
subset of `A`, so it cannot leave the component it starts in, which is exactly the stability
that lemma asks for. -/
theorem isRelOpenIn_connectedComponentIn (h : IsLocallyPolyConn' S) (hA : IsRelOpenIn S A)
    (x : Plane) : IsRelOpenIn S (connectedComponentIn A x) := by
  refine hA.trans (isRelOpenIn_of_exists (connectedComponentIn_subset A x) ?_)
  refine isRelOpen_of_polyReaches_stable (h.of_isRelOpenIn hA).isLocallyPolyConnected
    (connectedComponentIn_subset A x) fun w hw z _ hreach => ?_
  -- The polygon carrying the path is connected, lies in `A` and starts at `w`.
  obtain ⟨vs, hne, hsubA, hhead, hlast⟩ := hreach.exists_poly
  have hpoly : poly vs ⊆ connectedComponentIn A x := by
    rw [connectedComponentIn_eq hw]
    exact (isConnected_poly hne).isPreconnected.subset_connectedComponentIn
      (hhead ▸ head_mem_poly hne) hsubA
  exact hpoly (hlast ▸ getLast_mem_poly hne)

/-- A component of a relatively open piece is itself locally polygonally connected, so the
whole interface applies again one level down. -/
theorem isLocallyPolyConn'_connectedComponentIn (h : IsLocallyPolyConn' S) (hA : IsRelOpenIn S A)
    (x : Plane) : IsLocallyPolyConn' (connectedComponentIn A x) :=
  h.of_isRelOpenIn (isRelOpenIn_connectedComponentIn h hA x)

/-! ### The payoff -/

/-- **What brick B7 uses.** In a locally polygonally connected `S`, any two points of a
connected relatively open subset are joined by a polygonal path *inside that subset*. -/
theorem polyReaches_of_isPreconnected_of_isRelOpenIn (h : IsLocallyPolyConn' S)
    (hC : IsRelOpenIn S C) (hconn : IsPreconnected C) (hx : x ∈ C) (hy : y ∈ C) :
    PolyReaches C x y :=
  PolyReaches.of_isPreconnected (h.of_isRelOpenIn hC).isLocallyPolyConnected hconn hx hy

/-- The same, as a vertex list. -/
theorem exists_poly_of_isPreconnected_of_isRelOpenIn (h : IsLocallyPolyConn' S)
    (hC : IsRelOpenIn S C) (hconn : IsPreconnected C) (hx : x ∈ C) (hy : y ∈ C) :
    ∃ vs : List Plane, ∃ hne : vs ≠ [], poly vs ⊆ C ∧ vs.head hne = x ∧ vs.getLast hne = y :=
  (polyReaches_of_isPreconnected_of_isRelOpenIn h hC hconn hx hy).exists_poly

/-- The component form, which is how `U_e` arises: a component of a relatively open piece is
both relatively open and polygonally connected in itself. -/
theorem polyReaches_connectedComponentIn (h : IsLocallyPolyConn' S) (hA : IsRelOpenIn S A)
    {w : Plane} (hx : x ∈ connectedComponentIn A w) (hy : y ∈ connectedComponentIn A w) :
    PolyReaches (connectedComponentIn A w) x y :=
  polyReaches_of_isPreconnected_of_isRelOpenIn h (isRelOpenIn_connectedComponentIn h hA w)
    isPreconnected_connectedComponentIn hx hy

end Schoenflies

end BundlePart385

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

section BundlePart391
/- Source: dev/planar_search/schoenflies_port/Schoenflies/Graph/Ear.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/



/-!
# Ears

The ear decomposition: `lem:subdivision-ear-preserve` in both halves, and the step of
`lem:relative-ear` that grows a 2-connected subgraph towards the graph containing it.

## Rerouting is the engine of half (a)

`Graph.Reaches.reroute` says the obvious thing in the one form every consumer wants: if every
edge but `e` survives from `G` into `H`, and whatever `e` joins in `G` is joined in `H` by
other means, then `H` reaches whatever `G` reaches. A walk that took `e` takes the
replacement route instead, and the induction is over the walk.

Its `hends` premise is stated as "**whatever** `e` joins in `G` is joined in `H`", not as "the
two named ends are joined". That is what makes the premise dischargeable in the case where
`e` is not an edge of `G` at all: it is then vacuous. `Graph.Reaches.across_edge_replacement`
is the specialisation the subdivision runs on, and it is where the vacuous case is used — its
`routed` premise carries the three-way choice the blueprint's proof makes in prose:

* reroute along the new path — the deleted vertex is not on it, so the path survives whole;
* reroute around the old graph — the deleted vertex *is* on the path, so the old graph is
  untouched and the replaced edge was not a bridge (`Graph.IsTwoConnected.no_bridge`);
* do not reroute at all — the deleted vertex is an end of the replaced edge, so no surviving
  walk could have taken that edge.

## Half (a) is stated for a path

`Graph.IsTwoConnected.replace_edge_by_path` replaces an edge by a whole path, not by a single
new vertex. Nothing in the argument cares how long the replacement is, and the general form is
what a subdivision needs: subdividing one edge by one vertex is the case where the path has
two edges.

## Half (b) does not need the blueprint's freshness hypothesis

`Graph.IsTwoConnected.ear` attaches an ear, and the blueprint's "whose internal vertices are
new" is **not** assumed — the proof does not use it. What carries the argument is
`Graph.IsPathGraph.reaches_an_end`: whatever vertex is deleted, every remaining vertex of the
path still reaches one of the two ends. The two ends live in a 2-connected graph, at least one
of them survives the deletion, and that survivor is the hub everything routes through.

Half (a) *does* use freshness, and for a real reason: without it the deleted vertex could sit
both on the replacement path and inside the old graph, and then neither of the two routes
between the replaced edge's ends need exist.

## Finding the ear

`Graph.IsTwoConnected.ear_exists` needs neither the components of `G - V(H)` nor a shortest
path, which is what the blueprint's proof reaches for. The ear is *found*: walk out of the
subgraph to a vertex outside it, take the edge where the walk **first** leaves the subgraph
(`Graph.IsWalk.crossing`), and walk back from that edge's outer end to a *different* vertex of
the subgraph inside `G` minus the edge's inner end — a graph that is connected because `G` is
2-connected, and whose walks therefore never touch the inner end. That walk with the crossing
edge in front is a path of `G` between two vertices of the subgraph, and the crossing edge is
one the subgraph did not have.

`Graph.pathGraphOf` turns it into a graph and `Graph.IsTwoConnected.grows_by_ear` glues it on.
Termination — the blueprint's "finiteness terminates the process" — is not here; this is the
single step, and a consumer that counts edges iterates it.

## Looplessness

`Graph.IsTwoConnected.ear_exists` is the one statement here that has to assume the graph has
no loop, and the hypothesis is not bureaucracy: adding a loop to a 2-connected graph leaves it
2-connected, so a 2-connected subgraph missing only a loop grows by no ear at all, and the
conclusion — a path between *distinct* vertices — is false. It is used only in the degenerate
branch where every vertex is already present and the missing object is an edge. A plane
consumer discharges it from its drawing.

## Blueprint

* `Graph.IsTwoConnected.replace_edge_by_path` — `lem:subdivision-ear-preserve` (a), "every
  subdivision of `G` is 2-connected", stated for a replacement path of any length.
* `Graph.IsTwoConnected.ear` — `lem:subdivision-ear-preserve` (b), "if `P` is a path whose
  distinct endpoints lie in `G` … then `G ∪ P` is 2-connected".
* `Graph.IsTwoConnected.ear_exists`, `Graph.IsTwoConnected.grows_by_ear` — the step of
  `lem:relative-ear`, "`G` is obtained from `H` by repeatedly adding paths whose distinct
  endpoints are already present".
* `Graph.Reaches.reroute`, `Graph.Reaches.across_edge_replacement` — the blueprint's "the
  remaining part of the subdivided edge attaches `w` to `u` or `v`" together with "a
  2-connected graph has no bridge", turned into one transfer lemma.
-/

open Set
open scoped Graph

namespace Graph

variable {α β : Type*} {G H K P : Graph α β} {a b c s t u v x y z : α} {e f : β}
  {W D : List β}

/-! ### The union of two subgraphs

`Graph.union` and the two inclusions *into* it live in `Schoenflies/Graph/TwoConnected.lean`;
this is the inclusion *out of* it, which the ear construction needs in order to know that the
enlarged subgraph is still a subgraph. It is general and belongs beside the other two — the
integrator should hoist it. -/

/-! ### Rerouting one edge -/

/-- **One edge swapped for any route between its ends.** If every edge of `G` other than `e`
links the same pair in `H`, and whatever `e` links in `G` is joined in `H` by some other
means, then `H` reaches whatever `G` reaches: a walk that took `e` takes the replacement route
instead.

The premise about `e` is universally quantified over its ends rather than stated for a named
pair, so that it is *vacuous* when `e` is not an edge of `G` — which is the case a vertex
deletion produces, and the reason this is the shape that gets used. -/
theorem Reaches.reroute (hV : V(G) ⊆ V(H))
    (hE : ∀ ⦃g p q⦄, G.IsLink g p q → g ≠ e → H.IsLink g p q)
    (hends : ∀ ⦃p q⦄, G.IsLink e p q → H.Reaches p q)
    (h : G.Reaches s t) : H.Reaches s t := by
  obtain ⟨R, hR⟩ := h
  induction hR with
  | nil hx => exact Reaches.refl (hV hx)
  | @cons p w q g R hl _ ih =>
    -- Either this step took the replaced edge, or it survives verbatim.
    refine Reaches.trans ?_ ih
    by_cases hg : g = e
    · exact hends (hg ▸ hl)
    · exact Reaches.of_isLink (hE hl hg)

/-- **The form a subdivision needs.** A walk of `G - c` transfers to any graph holding the
surviving edges, provided the replaced edge's ends are joined there *or* that edge was
incident to the deleted vertex — in which case no walk of `G - c` could have taken it, and the
`hends` premise of `Graph.Reaches.reroute` is vacuous.

That disjunction is the blueprint's three-way case analysis: route along the replacement,
route around the old graph, or do not route at all. -/
theorem Reaches.across_edge_replacement (hV : V(G.deleteVerts {c}) ⊆ V(H))
    (hl : G.IsLink e u v)
    (hE : ∀ ⦃g p q⦄, (G.deleteVerts {c}).IsLink g p q → g ≠ e → H.IsLink g p q)
    (routed : H.Reaches u v ∨ G.Inc e c)
    (h : (G.deleteVerts {c}).Reaches s t) : H.Reaches s t := by
  refine Reaches.reroute (e := e) hV hE (fun p q hpq ↦ ?_) h
  rw [deleteVerts_isLink] at hpq
  obtain ⟨hpq, hp, hq⟩ := hpq
  have hpc : p ≠ c := fun hh ↦ hp (by simp [hh])
  have hqc : q ≠ c := fun hh ↦ hq (by simp [hh])
  rcases routed with hr | ⟨w, hw⟩
  · -- The ends are joined in `H`; the step ran between them, one way or the other.
    rcases hl.eq_and_eq_or_eq_and_eq hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    exacts [hr, hr.symm]
  · -- The edge met the deleted vertex, so `G - c` does not have it: nothing to prove.
    rcases hw.left_eq_or_eq hpq with hh | hh
    exacts [(hpc hh.symm).elim, (hqc hh.symm).elim]

/-! ### Attaching an ear -/

/-- **`lem:subdivision-ear-preserve` (b): attaching an ear preserves 2-connectivity.** `P` is
a path whose two distinct ends lie in the 2-connected graph `G`; then `G ∪ P` is 2-connected.

The blueprint's hypothesis that the ear's internal vertices are new is **not** needed. Delete
a vertex `c`. One of the ear's two ends survives, and it is the hub: `G - c` is connected and
contains it, and every surviving vertex of the ear reaches one of the two ends inside the ear
(`Graph.IsPathGraph.reaches_an_end`) — an end which, having been reached after the deletion, is
itself not `c`, so it lies in `G - c` too. -/
theorem IsTwoConnected.ear (hG : G.IsTwoConnected) (hcompat : G.Compatible P)
    (hP : P.IsPathGraph u W v) (huv : u ≠ v) (hu : u ∈ V(G)) (hv : v ∈ V(G)) :
    (G.union P).IsTwoConnected where
  hasThreeVertices := hG.hasThreeVertices.mono (left_le_union G P).vertexSet_mono
  connected := hcompat.union_connected hG.connected hP.connected hu hP.source_mem
  deleteVerts_connected := by
    intro c _
    -- One of the ear's two ends survives the deletion; it is the hub.
    obtain ⟨z, hzG, hzc⟩ : ∃ z, z ∈ V(G) ∧ z ≠ c := by
      by_cases hcu : u = c
      · exact ⟨v, hv, fun hh ↦ huv (hcu.trans hh.symm)⟩
      · exact ⟨u, hu, hcu⟩
    have hGle : G.deleteVerts {c} ≤ (G.union P).deleteVerts {c} :=
      deleteVerts_mono (left_le_union G P) _
    have hPle : P.deleteVerts {c} ≤ (G.union P).deleteVerts {c} :=
      deleteVerts_mono hcompat.right_le_union _
    have hGc : (G.deleteVerts {c}).Connected := hG.deleteVerts_connected' c
    -- Every surviving vertex of the graph side reaches the hub inside the graph side.
    have key : ∀ x ∈ V(G), x ≠ c → ((G.union P).deleteVerts {c}).Reaches z x := fun x hx hxc ↦
      (hGc.reaches (mem_deleteVerts_singleton_of_ne hzG hzc)
        (mem_deleteVerts_singleton_of_ne hx hxc)).mono hGle
    refine Connected.of_hub (mem_deleteVerts_singleton_of_ne
      ((left_le_union G P).vertexSet_mono hzG) hzc) fun x hx ↦ ?_
    rw [vertexSet_deleteVerts] at hx
    obtain ⟨hxS, hxc⟩ := hx
    have hxc' : x ≠ c := by simpa using hxc
    rcases (hxS : x ∈ V(G) ∪ V(P)) with hxG | hxP
    · exact key x hxG hxc'
    · -- On the ear, one of the two ends is still reachable, and it survived the deletion.
      rcases hP.reaches_an_end hxP hxc' with hr | hr
      · have hune : u ≠ c := by
          have h₂ := hr.right_mem
          rw [vertexSet_deleteVerts] at h₂
          simpa using h₂.2
        exact (key u hu hune).trans (hr.mono hPle).symm
      · have hvne : v ≠ c := by
          have h₂ := hr.right_mem
          rw [vertexSet_deleteVerts] at h₂
          simpa using h₂.2
        exact (key v hv hvne).trans (hr.mono hPle).symm

/-! ### Replacing an edge by a path -/

/-- **`lem:subdivision-ear-preserve` (a): a subdivision of a 2-connected graph is
2-connected.** Stated for a replacement *path* rather than for a single new vertex, because
nothing in the argument cares how long the replacement is; subdividing one edge by one vertex
is the case where `P` has two edges.

Delete a vertex `c`. One end of the replaced edge survives and is the hub. Everything on the
old side reaches it by `Graph.Reaches.across_edge_replacement`, whose `routed` premise is
discharged by the three-way case analysis: if `c` is an end of the replaced edge there is
nothing to route; if `c` is an old vertex then it is not on the path — this is where the
freshness hypothesis `hnew` is used — and the path itself joins the ends; and if `c` is new
then the old graph is untouched and has no bridge. Everything on the path side reaches an end
of the path, and an end reached after the deletion survived it. -/
theorem IsTwoConnected.replace_edge_by_path (hG : G.IsTwoConnected) (hl : G.IsLink e u v)
    (huv : u ≠ v) (hcompat : (G.deleteEdges {e}).Compatible P) (hP : P.IsPathGraph u W v)
    (hnew : ∀ x ∈ V(P), x ≠ u → x ≠ v → x ∉ V(G)) :
    ((G.deleteEdges {e}).union P).IsTwoConnected := by
  set T := G.deleteEdges {e} with hT
  set S := T.union P with hS
  have hTS : T ≤ S := left_le_union T P
  have hPS : P ≤ S := hcompat.right_le_union
  have hVT : V(T) = V(G) := by rw [hT]; simp
  have hu : u ∈ V(G) := hl.left_mem
  have hv : v ∈ V(G) := hl.right_mem
  -- Every old edge but the replaced one links the same pair in the new graph.
  have hGS : ∀ ⦃g p q⦄, G.IsLink g p q → g ≠ e → S.IsLink g p q := by
    intro g p q hg hge
    refine hTS.isLink_mono (show T.IsLink g p q from ?_)
    rw [hT]
    exact ⟨hg, by simpa using hge⟩
  have hVGS : V(G) ⊆ V(S) := by
    rw [hS, vertexSet_union, hVT]
    exact Set.subset_union_left
  -- The replacement route.
  have hPuv : P.Reaches u v := hP.connected.reaches hP.source_mem hP.target_mem
  refine ⟨hG.hasThreeVertices.mono hVGS, ?_, ?_⟩
  · refine Connected.of_hub (hVGS hu) fun x hx ↦ ?_
    rcases (hx : x ∈ V(T) ∪ V(P)) with hxT | hxP
    · refine Reaches.reroute (e := e) hVGS hGS ?_
        (hG.connected.reaches hu (by rwa [hVT] at hxT))
      intro p q hpq
      rcases hl.eq_and_eq_or_eq_and_eq hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      exacts [hPuv.mono hPS, (hPuv.mono hPS).symm]
    · exact (hP.connected.reaches hP.source_mem hxP).mono hPS
  intro c _
  -- One end of the replaced edge survives; it is the hub.
  obtain ⟨z, hzG, hzc⟩ : ∃ z, z ∈ V(G) ∧ z ≠ c := by
    by_cases hcu : u = c
    · exact ⟨v, hv, fun hh ↦ huv (hcu.trans hh.symm)⟩
    · exact ⟨u, hu, hcu⟩
  have hTle : T.deleteVerts {c} ≤ S.deleteVerts {c} := deleteVerts_mono hTS _
  have hPle : P.deleteVerts {c} ≤ S.deleteVerts {c} := deleteVerts_mono hPS _
  have hGc : (G.deleteVerts {c}).Connected := hG.deleteVerts_connected' c
  -- The replaced edge's ends are still joined, unless the deleted vertex is one of them.
  have routed : (S.deleteVerts {c}).Reaches u v ∨ G.Inc e c := by
    by_cases hcu : c = u
    · exact Or.inr (hcu ▸ hl.inc_left)
    by_cases hcv : c = v
    · exact Or.inr (hcv ▸ hl.inc_right)
    by_cases hcG : c ∈ V(G)
    · -- An old vertex and not an end: the path is untouched, and it joins the ends.
      have hcP : c ∉ V(P) := fun hh ↦ hnew c hh hcu hcv hcG
      have hreach : (P.deleteVerts {c}).Reaches u v := by
        rw [deleteVerts_singleton_eq_self hcP]; exact hPuv
      exact Or.inl (hreach.mono hPle)
    · -- A new vertex: the old graph is untouched, and it has no bridge.
      have hcT : c ∉ V(T) := by rw [hVT]; exact hcG
      have hreach : (T.deleteVerts {c}).Reaches u v := by
        rw [deleteVerts_singleton_eq_self hcT, hT]
        exact hG.no_bridge hl
      exact Or.inl (hreach.mono hTle)
  -- Every surviving old vertex reaches the hub.
  have key : ∀ x ∈ V(G), x ≠ c → (S.deleteVerts {c}).Reaches x z := by
    intro x hx hxc
    refine Reaches.across_edge_replacement (e := e) ?_ hl ?_ routed
      (hGc.reaches (mem_deleteVerts_singleton_of_ne hx hxc)
        (mem_deleteVerts_singleton_of_ne hzG hzc))
    · rw [vertexSet_deleteVerts, vertexSet_deleteVerts]
      exact Set.sdiff_subset_sdiff_left hVGS
    · intro g p q hg hge
      rw [deleteVerts_isLink] at hg ⊢
      exact ⟨hGS hg.1 hge, hg.2.1, hg.2.2⟩
  refine Connected.of_hub (mem_deleteVerts_singleton_of_ne (hVGS hzG) hzc) fun x hx ↦ ?_
  rw [vertexSet_deleteVerts] at hx
  obtain ⟨hxS, hxc⟩ := hx
  have hxc' : x ≠ c := by simpa using hxc
  rcases (hxS : x ∈ V(T) ∪ V(P)) with hxT | hxP
  · exact (key x (by rwa [hVT] at hxT) hxc').symm
  · rcases hP.reaches_an_end hxP hxc' with hr | hr
    · have hune : u ≠ c := by
        have h₂ := hr.right_mem
        rw [vertexSet_deleteVerts] at h₂
        simpa using h₂.2
      exact (key u hu hune).symm.trans (hr.mono hPle).symm
    · have hvne : v ≠ c := by
        have h₂ := hr.right_mem
        rw [vertexSet_deleteVerts] at h₂
        simpa using h₂.2
      exact (key v hv hvne).symm.trans (hr.mono hPle).symm

/-! ### Finding an ear -/

/-- **A 2-connected subgraph that is not all of a 2-connected graph has an ear.** The ear is
found, not chosen: if the subgraph already has every vertex then a missing edge joins two of
them and is an ear by itself; otherwise a walk out of the subgraph crosses its boundary, and
deleting the crossing edge's inner end leaves `G` connected, so the outer end walks back to a
*different* vertex of the subgraph without passing through the first.

The looplessness hypothesis is used only in the first, degenerate branch, and it cannot be
dropped: a 2-connected graph plus a loop is 2-connected, and no ear is missing from it. -/
theorem IsTwoConnected.ear_exists (hG : G.IsTwoConnected) (hK : K.IsTwoConnected) (hKG : K ≤ G)
    (hnl : ∀ ⦃g x⦄, ¬ G.IsLoopAt g x)
    (hproper : (∃ x ∈ V(G), x ∉ V(K)) ∨ (∃ g ∈ E(G), g ∉ E(K))) :
    ∃ a b D g, G.IsPath a D b ∧ a ≠ b ∧ a ∈ V(K) ∧ b ∈ V(K) ∧ g ∈ D ∧ g ∉ E(K) := by
  by_cases hout : ∃ x ∈ V(G), x ∉ V(K)
  · obtain ⟨o, hoG, hoK⟩ := hout
    -- Walk from the subgraph out to `o`; it crosses the boundary along one of its own edges.
    obtain ⟨anchor, hanchor⟩ := hK.connected.nonempty
    obtain ⟨R, hR⟩ := hG.connected.reaches (hKG.vertexSet_mono hanchor) hoG
    obtain ⟨g, hgR, p, q, hlpq, hpK, hqK⟩ := hR.crossing hanchor hoK
    have hpq : p ≠ q := fun hh ↦ hqK (hh ▸ hpK)
    -- The subgraph has a second vertex to come back to.
    obtain ⟨b, hbK, hbp, -⟩ := hK.hasThreeVertices.exists_ne_ne p p
    have hqG : q ∈ V(G) := hlpq.right_mem
    have hbG : b ∈ V(G) := hKG.vertexSet_mono hbK
    -- Deleting the inner end leaves `G` connected, so the outer end walks back to `b`.
    obtain ⟨D, hD⟩ := ((hG.deleteVerts_connected' p).reaches
      (mem_deleteVerts_singleton_of_ne hqG (Ne.symm hpq))
      (mem_deleteVerts_singleton_of_ne hbG hbp)).exists_isPath
    have hfresh : p ∉ G.walkVertices q D := by
      rintro hmem
      rcases mem_walkVertices_iff.1 hmem with rfl | ⟨g', hg', hinc⟩
      · exact hpq rfl
      · exact hD.isWalk.notMem_of_inc_of_deleteVerts hinc hg'
    refine ⟨p, b, g :: D, g, .cons hlpq (hD.mono deleteVerts_le) hfresh, Ne.symm hbp, hpK,
      hbK, List.mem_cons_self, fun hgK ↦ ?_⟩
    -- The crossing edge is not the subgraph's: its outer end would then be a vertex of it.
    exact hqK ((hKG.isLink_iff hgK).2 hlpq).right_mem
  · -- Every vertex is already there, so a missing edge is an ear of length one.
    push Not at hout
    obtain ⟨g, hgG, hgK⟩ := hproper.resolve_left (by rintro ⟨x, hx, hx'⟩; exact hx' (hout x hx))
    obtain ⟨p, q, hpq⟩ := exists_isLink_of_mem_edgeSet hgG
    have hne : p ≠ q := by rintro rfl; exact hnl hpq
    exact ⟨p, q, [g], g, .single hpq hne, hne, hout p hpq.left_mem, hout q hpq.right_mem,
      List.mem_cons_self, hgK⟩

/-- **H5: a 2-connected subgraph of a 2-connected graph grows to it by adding ears.** One
step: the subgraph gains an ear and at least one edge, and is still a 2-connected subgraph of
the big graph. Iterating on the number of missing edges is the caller's business — the
blueprint's "finiteness terminates the process". -/
theorem IsTwoConnected.grows_by_ear (hG : G.IsTwoConnected) (hK : K.IsTwoConnected)
    (hKG : K ≤ G) (hnl : ∀ ⦃g x⦄, ¬ G.IsLoopAt g x)
    (hproper : (∃ x ∈ V(G), x ∉ V(K)) ∨ (∃ g ∈ E(G), g ∉ E(K))) :
    ∃ B : Graph α β, B.IsTwoConnected ∧ K ≤ B ∧ B ≤ G ∧ ∃ g ∈ E(B), g ∉ E(K) := by
  obtain ⟨a, b, D, g, hpath, hab, haK, hbK, hgD, hgK⟩ := hG.ear_exists hK hKG hnl hproper
  -- The path, presented as a graph, is the ear.
  have hearle : G.pathGraphOf a D ≤ G := pathGraphOf_le hpath.isWalk
  have hearP : (G.pathGraphOf a D).IsPathGraph a D b := hpath.isPathGraph_pathGraphOf
  exact ⟨K.union (G.pathGraphOf a D),
    hK.ear (Compatible.of_le_le hKG hearle) hearP hab haK hbK,
    left_le_union _ _, union_le hKG hearle, g,
    Set.mem_union_right _ (hearP.mem_edgeSet hgD), hgK⟩

end Graph

end BundlePart391

section BundlePart392
/- Source: dev/planar_search/schoenflies_port/Schoenflies/Graph/Tree.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/



/-!
# Trees

A tree is a connected graph in which no edge lies on a cycle. What the blueprint asks of a
tree is always about its leaves, and every such question starts the same way: **take a longest
path**. Neither of its ends can carry a second edge — an edge back onto the path would close a
cycle, and an edge off the path would make a longer path — so both ends are leaves.

## The three theorems this file exists for

* deleting a leaf leaves a tree (`Graph.IsTree.delete_leaf`),
* a tree on `n` vertices has `n - 1` edges (`Graph.IsTree.edge_count`), by peeling leaves,
* **a tree with exactly three leaves has one vertex of degree three**
  (`Graph.IsTree.three_leaves`), which is where the handshake lemma finally pays.

## Why a longest path rather than a maximal one

A longest path is produced by `Nat.findGreatest` over the lengths of paths, bounded because a
path repeats no edge (`Graph.IsPath.nodup`) and the graph has finitely many. That needs
`Graph.Finite` and nothing else — in particular no well-founded recursion and no choice of a
maximal element in an order. The bound is the only place finiteness enters the longest-path
argument.

## Vertex deletion

`Graph.deleteVerts` is Mathlib's. What this file adds is the transfer lemma every deletion
argument reduces to — `Graph.IsWalk.deleteVerts`, a walk that never visits a deleted vertex
survives — together with the reason the hypothesis is ever available:
`Graph.IsLeaf.path_avoids`, a path whose two ends are elsewhere never visits a vertex of
degree one. To pass through such a vertex a path would have to arrive and leave along its
single edge, and a path takes no edge twice.

## Blueprint

* `Graph.IsTree.three_leaves` — `lem:three-leaf-tree` ("a finite tree with exactly three
  leaves has exactly one vertex of degree at least three; that vertex has degree exactly
  three, and every other vertex is a leaf or has degree two"), used at the H5 step of
  `lem:two-components` to produce the three internally disjoint branches of each spanning
  tree `T_i`.
* `Graph.IsTree.edge_count` — the same lemma's "a finite tree with `n` vertices has exactly
  `n - 1` edges".
* `Graph.IsTree.has_leaf`, `Graph.IsTree.delete_leaf` — its "a tree with an edge has a leaf,
  since an endpoint of a maximal simple path has no neighbor off the path, and a second
  neighbor on the path would close a cycle; deleting a leaf and its edge leaves a tree".
* `Graph.IsTree` — the trees of `lem:two-components` ("take a minimal connected subgraph
  `T_i` spanning the three terminals. It is a tree").

## Namespace

The root `Graph` namespace, as in `Walk.lean`, `Degree.lean` and `Cycle.lean`.
-/

open Set
open scoped Graph

variable {α β : Type*} {G H : Graph α β} {u v w x y : α} {e f : β} {P W : List β}

namespace Graph

/-! ### Trees -/

/-- `G.IsTree` : a connected graph in which no edge lies on a cycle. Connectedness carries
nonemptiness (`Graph.Connected`), which is what makes the counting statements below true as
stated. -/
def IsTree (G : Graph α β) : Prop := G.Connected ∧ G.IsAcyclic

theorem IsTree.connected (h : G.IsTree) : G.Connected := h.1

theorem IsTree.isAcyclic (h : G.IsTree) : G.IsAcyclic := h.2

theorem isTree_iff : G.IsTree ↔ G.Connected ∧ G.IsAcyclic := Iff.rfl

/-! ### A walk departs along an edge -/

/-- A walk that gets anywhere leaves along an edge at its source. -/
theorem IsWalk.exists_inc_source (h : G.IsWalk u W v) (hW : W ≠ []) : ∃ e ∈ W, G.Inc e u := by
  cases h with
  | nil => exact absurd rfl hW
  | cons hl _ => exact ⟨_, List.mem_cons_self, hl.inc_left⟩

/-- A path between two distinct vertices takes at least one edge. -/
theorem IsPath.ne_nil (h : G.IsPath u P v) (huv : u ≠ v) : P ≠ [] := by
  rintro rfl
  exact huv h.isWalk.eq_of_nil

/-- **In a connected graph on two or more vertices nothing is isolated.** -/
theorem Connected.degree_pos [G.Finite] (hG : G.Connected) (h2 : 2 ≤ V(G).ncard)
    (hx : x ∈ V(G)) : 0 < G.degree x := by
  obtain ⟨b, hb, hbx⟩ := Set.exists_ne_of_one_lt_ncard (s := V(G)) (by omega) x
  obtain ⟨R, hR⟩ := hG.exists_isPath hx hb
  obtain ⟨e, -, hinc⟩ := hR.isWalk.exists_inc_source (hR.ne_nil (Ne.symm hbx))
  exact degree_pos_of_inc hinc

/-! ### A path leaves its source once and for all

Two edges of a path incident with its source are the same edge: the departing step is the
only candidate, since a later edge at the source would put the source back among the vertices
the rest of the path visits. -/

/-- An edge of a path incident with the path's source is the one the path departs along. -/
theorem IsPath.eq_head_of_inc_source (h : G.IsPath u (e :: W) v) (hf : f ∈ e :: W)
    (hinc : G.Inc f u) : f = e := by
  cases h with
  | cons hl hW hfresh =>
    rcases List.mem_cons.1 hf with rfl | hf
    · rfl
    · exact absurd (mem_walkVertices_of_mem_covered ⟨f, hf, hinc⟩) hfresh

/-- **A path has at most one edge at its source.** -/
theorem IsPath.inc_source_unique (h : G.IsPath u P v) (hf : f ∈ P) (he : e ∈ P)
    (hfi : G.Inc f u) (hei : G.Inc e u) : f = e := by
  cases P with
  | nil => simp at hf
  | cons a t => rw [h.eq_head_of_inc_source hf hfi, h.eq_head_of_inc_source he hei]

/-! ### A longest path -/

/-- A path repeats no edge, so it is no longer than the graph has edges. -/
theorem IsPath.length_le_ncard_edgeSet [G.Finite] (h : G.IsPath u P v) :
    P.length ≤ E(G).ncard := by
  classical
  have hsub : P.toFinset ⊆ G.edgeFinset := fun f hf ↦
    mem_edgeFinset.2 (h.edge_mem (List.mem_toFinset.1 hf))
  calc P.length = P.toFinset.card := (List.toFinset_card_of_nodup h.nodup).symm
    _ ≤ G.edgeFinset.card := Finset.card_le_card hsub
    _ = E(G).ncard := card_edgeFinset

/-- **A finite graph with a vertex has a longest path.** The lengths of paths are bounded by
the number of edges, so `Nat.findGreatest` picks the largest length that occurs, and the
witnessing path is longest. -/
theorem exists_longest_path [G.Finite] (hu : u ∈ V(G)) :
    ∃ x y Q, G.IsPath x Q y ∧ ∀ x' y' (Q' : List β), G.IsPath x' Q' y' → Q'.length ≤ Q.length := by
  classical
  -- `p n` : some path has length exactly `n`.
  set p : ℕ → Prop :=
    fun n ↦ ∃ (x : α) (y : α) (Q : List β), G.IsPath x Q y ∧ Q.length = n with hp
  have hp0 : p 0 := ⟨u, u, [], .nil hu, rfl⟩
  obtain ⟨x, y, Q, hQ, hQlen⟩ := Nat.findGreatest_spec (P := p) (Nat.zero_le E(G).ncard) hp0
  refine ⟨x, y, Q, hQ, fun x' y' Q' hQ' ↦ ?_⟩
  have hle := Nat.le_findGreatest (P := p) hQ'.length_le_ncard_edgeSet ⟨x', y', Q', hQ', rfl⟩
  omega

/-! ### Both ends of a longest path are leaves -/

/-- **Every edge at the source of a longest path is one of the path's own edges.** The two
ways out are both closed: an edge onto a vertex the path visits closes a cycle
(`Graph.IsAcyclic.mem_of_isLink_of_mem_walkVertices`), and an edge to a vertex it does not
visit extends the path. -/
theorem IsAcyclic.longest_path_source_edge (hac : G.IsAcyclic) (hP : G.IsPath u P v)
    (hlong : ∀ x' y' (Q : List β), G.IsPath x' Q y' → Q.length ≤ P.length)
    (hinc : G.Inc e u) : e ∈ P := by
  obtain ⟨z, hl⟩ := hinc
  by_cases hz : z ∈ G.walkVertices u P
  · exact hac.mem_of_isLink_of_mem_walkVertices hP hl hz
  · have hlt := hlong z v (e :: P) (.cons hl.symm hP hz)
    rw [List.length_cons] at hlt
    omega

/-- **The source of a longest path in an acyclic graph is a leaf**, as soon as it carries an
edge at all: every edge there is one of the path's, and the path leaves the vertex only once,
so they are all the same edge. -/
theorem IsAcyclic.longest_path_source_is_leaf [G.Finite] (hac : G.IsAcyclic)
    (hP : G.IsPath u P v)
    (hlong : ∀ x' y' (Q : List β), G.IsPath x' Q y' → Q.length ≤ P.length)
    (hinc : G.Inc e u) : G.IsLeaf u := by
  refine isLeaf_of_isNonloopAt hinc.vertex_mem (fun g ↦ ⟨fun hg ↦ ?_, fun hg ↦ hg ▸ hinc⟩)
    (hinc.isLoopAt_or_isNonloopAt.resolve_left (hac.not_isLoopAt e u))
  exact hP.inc_source_unique (hac.longest_path_source_edge hP hlong hg)
    (hac.longest_path_source_edge hP hlong hinc) hg hinc

/-- **The target of a longest path in an acyclic graph is a leaf** too: reversing a path
preserves its length, so the reverse is longest as well. -/
theorem IsAcyclic.longest_path_target_is_leaf [G.Finite] (hac : G.IsAcyclic)
    (hP : G.IsPath u P v)
    (hlong : ∀ x' y' (Q : List β), G.IsPath x' Q y' → Q.length ≤ P.length)
    (hinc : G.Inc e v) : G.IsLeaf v := by
  refine hac.longest_path_source_is_leaf hP.reverse (fun x' y' Q hQ ↦ ?_) hinc
  rw [List.length_reverse]
  exact hlong x' y' Q hQ

/-- **A tree on two or more vertices has a leaf.** Two distinct vertices are joined by a path
that takes an edge, so a longest path takes one too, and its source is a leaf. -/
theorem IsTree.has_leaf [G.Finite] (hT : G.IsTree) (h2 : 2 ≤ V(G).ncard) :
    ∃ x, G.IsLeaf x := by
  obtain ⟨a, ha⟩ := hT.connected.nonempty
  obtain ⟨b, hb, hba⟩ := Set.exists_ne_of_one_lt_ncard (s := V(G)) (by omega) a
  obtain ⟨x, y, Q, hQ, hlong⟩ := exists_longest_path ha
  -- Some path is nonempty, so the longest one is.
  obtain ⟨R, hR⟩ := hT.connected.exists_isPath ha hb
  have hRpos : 1 ≤ R.length := List.length_pos_iff.2 (hR.ne_nil (Ne.symm hba))
  have hQne : Q ≠ [] := by
    intro hQnil
    have hle := hlong a b R hR
    rw [hQnil, List.length_nil] at hle
    omega
  obtain ⟨e, -, hinc⟩ := hQ.isWalk.exists_inc_source hQne
  exact ⟨x, hT.isAcyclic.longest_path_source_is_leaf hQ hlong hinc⟩

/-! ### A path steers clear of a leaf -/

/-- **A path whose two ends are elsewhere never visits a vertex of degree one.** To pass
through such a vertex the path would have to arrive and leave along that vertex's single
edge, and a path takes no edge twice. This is what makes connectivity survive the deletion of
a leaf. -/
theorem IsLeaf.path_avoids [G.Finite] (hx : G.IsLeaf x) (hP : G.IsPath u P v) :
    u ≠ x → v ≠ x → x ∉ G.walkVertices u P := by
  induction hP with
  | nil hy =>
    intro hu _ hmem
    rw [walkVertices_nil] at hmem
    exact hu hmem.symm
  | @cons a w b e W hl hW hfresh ih =>
    intro ha hb hmem
    rcases mem_walkVertices_cons hl hmem with rfl | hmem'
    · exact ha rfl
    by_cases hwx : w = x
    · -- The step arrives at the leaf, so the rest has to leave it — along the leaf's one
      -- edge, which the step has already used.
      subst hwx
      have hWne : W ≠ [] := hW.ne_nil (Ne.symm hb)
      obtain ⟨g, hg, hginc⟩ := hW.isWalk.exists_inc_source hWne
      obtain ⟨e', -, huniq⟩ := hx.existsUnique_inc
      have hge : g = e := (huniq g hginc).trans (huniq e hl.inc_right).symm
      exact hfresh (mem_walkVertices_of_mem_covered ⟨e, hge ▸ hg, hl.inc_left⟩)
    · exact ih hwx hb hmem'

/-! ### Vertex deletion -/

/-- **A walk that visits no deleted vertex survives the deletion.** Both ends of each of its
edges are vertices it visits, so they too survive. -/
theorem IsWalk.deleteVerts {X : Set α} (h : G.IsWalk u W v)
    (hX : ∀ z ∈ G.walkVertices u W, z ∉ X) : (G.deleteVerts X).IsWalk u W v := by
  refine h.anti deleteVerts_le ?_ fun g hg ↦ ?_
  · rw [vertexSet_deleteVerts]
    exact ⟨h.left_mem, hX u mem_walkVertices_self⟩
  · obtain ⟨p, q, hpq⟩ := exists_isLink_of_mem_edgeSet (h.edge_mem hg)
    simp only [edgeSet_deleteVerts, Set.mem_setOf_eq]
    exact ⟨p, q, hpq, hX p (mem_walkVertices_of_mem_covered ⟨g, hg, hpq.inc_left⟩),
      hX q (mem_walkVertices_of_mem_covered ⟨g, hg, hpq.inc_right⟩)⟩

/-- Deleting a vertex removes exactly the edges that meet it. -/
theorem edgeSet_deleteVerts_singleton (G : Graph α β) (x : α) :
    E(G.deleteVerts {x}) = E(G) \ G.incidenceSet x := by
  ext g
  simp only [edgeSet_deleteVerts, Set.mem_setOf_eq, Set.mem_sdiff, mem_incidenceSet,
    Set.mem_singleton_iff]
  refine ⟨fun ⟨p, q, hpq, hp, hq⟩ ↦ ⟨hpq.edge_mem, fun hinc ↦ ?_⟩, fun ⟨hg, hninc⟩ ↦ ?_⟩
  · rcases hinc.eq_or_eq_of_isLink hpq with rfl | rfl
    exacts [hp rfl, hq rfl]
  · obtain ⟨p, q, hpq⟩ := exists_isLink_of_mem_edgeSet hg
    exact ⟨p, q, hpq, fun h ↦ hninc (h ▸ hpq.inc_left), fun h ↦ hninc (h ▸ hpq.inc_right)⟩

/-- **A tree minus a leaf is a tree.** Acyclicity is inherited by every subgraph;
connectedness survives because every path between two surviving vertices already steered
clear of the leaf (`Graph.IsLeaf.path_avoids`). -/
theorem IsTree.delete_leaf [G.Finite] (hT : G.IsTree) (hx : G.IsLeaf x) (h2 : 2 ≤ V(G).ncard) :
    (G.deleteVerts {x}).IsTree := by
  refine ⟨⟨?_, fun a ha b hb ↦ ?_⟩, hT.isAcyclic.anti deleteVerts_le⟩
  · obtain ⟨c, hc, hcx⟩ := Set.exists_ne_of_one_lt_ncard (s := V(G)) (by omega) x
    exact ⟨c, by rw [vertexSet_deleteVerts]; exact ⟨hc, by simpa using hcx⟩⟩
  · rw [vertexSet_deleteVerts] at ha hb
    obtain ⟨R, hR⟩ := hT.connected.exists_isPath ha.1 hb.1
    have havoid := hx.path_avoids hR (by simpa using ha.2) (by simpa using hb.2)
    exact ⟨R, hR.isWalk.deleteVerts fun z hz hzX ↦ havoid (Set.mem_singleton_iff.1 hzX ▸ hz)⟩

/-! ### A tree has one edge fewer than it has vertices -/

/-- The induction behind `Graph.IsTree.edge_count`, with a bound on the number of vertices to
walk down: peel a leaf and recurse on what is left, which is a tree with one vertex and one
edge fewer. -/
private theorem isTree_edge_count_aux :
    ∀ (n : ℕ) (G : Graph α β), G.Finite → V(G).ncard ≤ n → G.IsTree →
      E(G).ncard + 1 = V(G).ncard := by
  intro n
  induction n with
  | zero =>
    intro G hfin hle hT
    haveI := hfin
    obtain ⟨a, ha⟩ := hT.connected.nonempty
    have := (Set.ncard_pos (finite_vertexSet G)).2 ⟨a, ha⟩
    omega
  | succ n ih =>
    intro G hfin hle hT
    haveI := hfin
    by_cases h2 : 2 ≤ V(G).ncard
    · obtain ⟨x, hx⟩ := hT.has_leaf h2
      haveI : (G.deleteVerts {x}).Finite := Finite.of_le deleteVerts_le
      have hT' : (G.deleteVerts {x}).IsTree := hT.delete_leaf hx h2
      have hV : V(G.deleteVerts {x}).ncard = V(G).ncard - 1 := by
        rw [vertexSet_deleteVerts, Set.ncard_sdiff_singleton_of_mem hx.mem_vertexSet]
      -- A leaf sits on exactly one edge, and that edge is what the deletion removes.
      obtain ⟨e₀, he₀⟩ := Set.ncard_eq_one.1 hx.ncard_incidenceSet
      have he₀G : e₀ ∈ E(G) :=
        G.incidenceSet_subset_edgeSet x (he₀ ▸ Set.mem_singleton e₀)
      have hE : E(G.deleteVerts {x}).ncard = E(G).ncard - 1 := by
        rw [edgeSet_deleteVerts_singleton, he₀, Set.ncard_sdiff_singleton_of_mem he₀G]
      have hEpos := (Set.ncard_pos (finite_edgeSet G)).2 ⟨e₀, he₀G⟩
      have := ih _ inferInstance (by omega) hT'
      omega
    · -- A single vertex, and no edge: an edge would be a loop, and no acyclic graph has one.
      obtain ⟨a, ha⟩ := hT.connected.nonempty
      have hpos := (Set.ncard_pos (finite_vertexSet G)).2 ⟨a, ha⟩
      have hV1 : V(G).ncard = 1 := by omega
      obtain ⟨c, hVc⟩ := Set.ncard_eq_one.1 hV1
      have hE : E(G).ncard = 0 := by
        refine (Set.ncard_eq_zero (finite_edgeSet G)).2 (Set.eq_empty_iff_forall_notMem.2 ?_)
        intro g hg
        obtain ⟨p, q, hpq⟩ := exists_isLink_of_mem_edgeSet hg
        have hp : p = c := by have := hpq.left_mem; rw [hVc] at this; exact this
        have hq : q = c := by have := hpq.right_mem; rw [hVc] at this; exact this
        rw [hp, hq] at hpq
        exact hT.isAcyclic.not_isLoopAt g c hpq
      omega

/-- **A tree has one edge fewer than it has vertices.** -/
theorem IsTree.edge_count [G.Finite] (hT : G.IsTree) : E(G).ncard + 1 = V(G).ncard :=
  isTree_edge_count_aux V(G).ncard G inferInstance le_rfl hT

/-! ### A tree with three leaves

The blueprint's `lem:three-leaf-tree`, and the one place the handshake lemma is used. Three
leaves contribute one apiece to the degree sum, every other vertex contributes two plus
whatever it carries above two, and the totals leave exactly one degree to carry. -/

/-- **A tree with exactly three leaves has a vertex of degree three, and every other vertex
has degree at most two** — so it is a leaf or has degree exactly two, and the vertex of degree
three is unique.

The count: with `k` non-leaf vertices the tree has `k + 3` vertices, hence `k + 2` edges
(`Graph.IsTree.edge_count`), hence degree sum `2k + 4` (the handshake lemma). The leaves
contribute `3`, so the non-leaves contribute `2k + 1`; each contributes at least `2`, so
between them they carry exactly one degree above two. -/
theorem IsTree.three_leaves [G.Finite] (hT : G.IsTree)
    (hleaves : {z | G.IsLeaf z}.ncard = 3) :
    ∃ x ∈ V(G), G.degree x = 3 ∧ ∀ z ∈ V(G), z ≠ x → G.degree z ≤ 2 := by
  classical
  set L : Finset α := G.vertexFinset.filter (fun z ↦ G.degree z = 1) with hL
  set I : Finset α := G.vertexFinset.filter (fun z ↦ ¬ G.degree z = 1) with hI
  -- The filter really is the set of leaves.
  have hcoe : (L : Set α) = {z | G.IsLeaf z} := by
    ext z
    simp [hL, isLeaf_iff]
  have hLcard : L.card = 3 := by rw [← Set.ncard_coe_finset, hcoe]; exact hleaves
  -- Three leaves is already three vertices.
  have h2 : 2 ≤ V(G).ncard := by
    have := Finset.card_le_card (Finset.filter_subset (fun z ↦ G.degree z = 1) G.vertexFinset)
    rw [hLcard, card_vertexFinset] at this
    omega
  -- Each leaf contributes one to the degree sum.
  have hsumL : ∑ z ∈ L, G.degree z = 3 := by
    rw [Finset.sum_congr rfl fun z hz ↦ (Finset.mem_filter.1 hz).2, Finset.sum_const, hLcard]
    simp
  -- Each non-leaf is on at least two edges.
  have hdeg2 : ∀ z ∈ I, 2 ≤ G.degree z := by
    intro z hz
    obtain ⟨hzV, hzd⟩ := Finset.mem_filter.1 hz
    have := hT.connected.degree_pos h2 (mem_vertexFinset.1 hzV)
    omega
  -- So it contributes two plus whatever it carries above two.
  have hsumI : ∑ z ∈ I, G.degree z = 2 * I.card + ∑ z ∈ I, (G.degree z - 2) := by
    rw [Finset.sum_congr rfl fun z hz ↦ (Nat.add_sub_cancel' (hdeg2 z hz)).symm,
      Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm]
  -- The two halves are the whole graph, and the handshake lemma reads the total.
  have hsplit : ∑ z ∈ L, G.degree z + ∑ z ∈ I, G.degree z = 2 * E(G).ncard := by
    rw [hL, hI, Finset.sum_filter_add_sum_filter_not]
    exact G.sum_degree_eq_two_mul_ncard_edgeSet
  have hcards : L.card + I.card = V(G).ncard := by
    rw [hL, hI, Finset.card_filter_add_card_filter_not, card_vertexFinset]
  -- The count: the non-leaves carry exactly one degree between them.
  have hexcess : ∑ z ∈ I, (G.degree z - 2) = 1 := by
    have hedges := hT.edge_count
    omega
  -- Whichever non-leaf carries it has degree three, and the others have degree two.
  obtain ⟨x, hxI, hxne⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero (by rw [hexcess]; exact one_ne_zero)
  have hrest : ∑ z ∈ I.erase x, (G.degree z - 2) + (G.degree x - 2) = 1 := by
    rw [Finset.sum_erase_add _ _ hxI]; exact hexcess
  have hx3 : G.degree x = 3 := by
    have := hdeg2 x hxI
    omega
  refine ⟨x, mem_vertexFinset.1 (Finset.mem_filter.1 hxI).1, hx3, fun z hz hzx ↦ ?_⟩
  by_cases hzL : G.degree z = 1
  · omega
  · have hzI : z ∈ I := Finset.mem_filter.2 ⟨mem_vertexFinset.2 hz, hzL⟩
    have hze : z ∈ I.erase x := Finset.mem_erase.2 ⟨hzx, hzI⟩
    have hzero : ∑ z ∈ I.erase x, (G.degree z - 2) = 0 := by omega
    have := (Finset.sum_eq_zero_iff.1 hzero) z hze
    have := hdeg2 z hzI
    omega

end Graph

end BundlePart392

section BundlePart393
/- Source: dev/planar_search/schoenflies_port/Schoenflies/Graph/RelativeEar.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/




/-!
# The relative ear decomposition

`lem:relative-ear`: *if `H` is a 2-connected subgraph of a finite 2-connected graph `G`, then
`G` is obtained from `H` by repeatedly adding paths whose distinct endpoints are already
present and whose internal vertices are new.*

Two things are delivered, and they are different in kind.

* `Graph.IsTwoConnected.relative_ear_exists` — the **relative** ear: the blueprint's own
  construction, through a component of `G - V(K)`, which is what makes the internal vertices
  new. `Graph.IsTwoConnected.ear_exists` in `Schoenflies/Graph/Ear.lean` finds *an* ear by a
  crossing walk, but says nothing about where the ear's interior lies — its path may run back
  and forth through the subgraph. That is enough to make the subgraph grow; it is **not**
  enough for the consumers, which need "whose internal vertices are new" verbatim (the ear's
  interior must be disjoint from the current skeleton, so that it lies in one current face).
* `Graph.IsTwoConnected.ear_decomposition` — the **iterated** form, as an induction principle.
  `Graph.IsTwoConnected.grows_by_ear` is deliberately one step; the finiteness induction the
  blueprint hides behind "finiteness terminates the process" is done here.

## Why the relative form is a different theorem

The blueprint's proof does not walk out of the subgraph and hope. It looks at a component `L`
of `G - V(H₀)`: if `L` has a vertex it has two distinct neighbours in `H₀`, since otherwise
its unique neighbour would be a cut vertex of `G`, and a shortest path through `L` between two
such neighbours is an ear. That path meets `V(H₀)` only at its two ends **by construction**,
because its interior was built inside `G - V(H₀)`.

All of that is already proved: `Graph.IsTwoConnected.exists_path_through_component` in
`Schoenflies/Graph/Component.lean` packages the component argument and the path through it.
What is left here is to feed it `S = V(K)` — the two distinct vertices of `S` it asks for are
two of the three that a 2-connected `K` has — and to read its "every edge has an end outside
`S`" as "no edge of the ear is an edge of `K`".

The degenerate branch is the blueprint's second sentence: if every vertex of `G` is already
present, a missing edge is an ear of length one, and it has no internal vertex at all. As in
`Graph.IsTwoConnected.ear_exists`, that branch — and only that branch — needs `G` to be
loopless: a loop added to a 2-connected graph leaves it 2-connected, and no ear between
*distinct* endpoints can supply it.

## The termination measure

Edges, not vertices: `(E(G) \ E(B)).ncard`, which is finite because `G` is. Every ear
contributes at least one edge that `B` did not have — in the relative form *every* edge of the
ear is new, since each has an end outside `V(B)` — so the measure strictly drops, and the
process stops exactly when `B = G`. The stopping step is `Graph.eq_of_le_of_subset_subset`: a
subgraph with all the vertices and all the edges is the graph.

Note that the measure never needs to see a vertex. It is tempting to stop when `E(B) = E(G)`
and argue that a connected `G` has no isolated vertex; that is true but needs the degree
theory, and is unnecessary: if `V(B) ≠ V(G)` the ear that the first branch produces has an
edge outside `E(B)`, so the measure was not zero after all.

## One import that looks wrong

`Schoenflies/Graph/Tree.lean` is imported for a single two-line fact, `Graph.IsPath.ne_nil` —
a path between distinct vertices has an edge — which happens to live there. Nothing else in
this file has anything to do with trees. The honest fix is for the integrator to hoist
`Graph.IsPath.ne_nil` into `Schoenflies/Graph/Walk.lean`, where it belongs, and drop the
import; it is not restated here.

## What the induction principle gives a consumer

`motive G`, from `motive K` and one step. The step is handed the ear in full — the path `D` of
`G`, its distinct ends in `V(B)`, and the freshness of its interior — together with
`B.IsTwoConnected`, `K ≤ B` and `B ≤ G`, and must produce `motive (B.union (G.pathGraphOf a D))`.
That is exactly the shape of the induction in `lem:face-cycles` ("suppose it holds for the
current graph and add the next geometric ear") and of the finite transfer of Part II.

## Blueprint

* `Graph.IsTwoConnected.relative_ear_exists` — `lem:relative-ear`, the ear itself: "a shortest
  path through `L` between two such neighbours is an ear", plus "if all vertices are already
  present, add a missing edge as an ear of length one".
* `Graph.IsTwoConnected.relative_grows_by_ear` — the same, glued on: one step of "`G` is
  obtained from `H` by repeatedly adding paths".
* `Graph.IsTwoConnected.ear_decomposition` — `lem:relative-ear` in full, including
  "finiteness terminates the process", as an induction principle.

## Namespace

Root `Graph`, as fixed by `Schoenflies/Graph/Walk.lean`.
-/

open Set
open scoped Graph

namespace Graph

variable {α β : Type*} {G K B : Graph α β} {a b x y : α} {e f : β} {D : List β}

/-! ### Two facts about a subgraph inclusion

Both are general and neither is in `Schoenflies/Graph/Walk.lean`; the integrator may want to
hoist them. -/

/-- **An edge of a subgraph has its ends in the subgraph**, even when the incidence is only
known in the big graph. This is what turns "every edge of the ear has an end outside `V(K)`"
into "no edge of the ear is an edge of `K`". -/
theorem mem_vertexSet_of_inc_of_mem_edgeSet (hKG : K ≤ G) (hf : f ∈ E(K)) (h : G.Inc f y) :
    y ∈ V(K) :=
  ((hKG.inc_congr hf).2 h).vertex_mem

/-- **A subgraph with all the vertices and all the edges is the graph.** The termination
condition of the ear process. -/
theorem eq_of_le_of_subset_subset (hKG : K ≤ G) (hV : V(G) ⊆ V(K)) (hE : E(G) ⊆ E(K)) :
    K = G :=
  le_antisymm hKG ((Compatible.of_ge hKG).le_iff.2 ⟨hV, hE⟩)

/-! ### The relative ear -/

/-- **`lem:relative-ear`, the ear.** A 2-connected subgraph `K` of a loopless 2-connected `G`
that is missing a vertex or an edge has a *relative* ear: a path of `G` whose two distinct
endpoints lie in `K`, whose every other vertex lies **outside** `K`, and none of whose edges
belongs to `K`.

This is the blueprint's own construction, and the freshness of the interior is what
distinguishes it from `Graph.IsTwoConnected.ear_exists`. The first branch takes a component
`L` of `G - V(K)` and a path across it between two of its neighbours in `K`
(`Graph.IsTwoConnected.exists_path_through_component`); the two distinct vertices of `V(K)`
that construction needs are supplied by the counting clause of `K.IsTwoConnected`. The second
branch is the blueprint's "if all vertices are already present, add a missing edge as an ear
of length one", and it is the only place looplessness is used. -/
theorem IsTwoConnected.relative_ear_exists (hG : G.IsTwoConnected) (hK : K.IsTwoConnected)
    (hKG : K ≤ G) (hnl : ∀ ⦃g x⦄, ¬ G.IsLoopAt g x)
    (hproper : (∃ x ∈ V(G), x ∉ V(K)) ∨ (∃ g ∈ E(G), g ∉ E(K))) :
    ∃ a b D, G.IsPath a D b ∧ a ≠ b ∧ a ∈ V(K) ∧ b ∈ V(K) ∧ D ≠ [] ∧
      (∀ y ∈ G.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(K)) ∧ (∀ g ∈ D, g ∉ E(K)) := by
  by_cases hout : ∃ x ∈ V(G), x ∉ V(K)
  · obtain ⟨x, hxG, hxK⟩ := hout
    -- The subgraph's three vertices supply the two distinct targets the component needs.
    obtain ⟨p, hp, q, hq, -, -, hpq, -, -⟩ := hK.hasThreeVertices
    obtain ⟨a, ha, b, hb, D, hab, hpath, hint, -, hedge⟩ :=
      hG.exists_path_through_component hKG.vertexSet_mono hp hq hpq hxG hxK
    refine ⟨a, b, D, hpath, hab, ha, hb, hpath.ne_nil hab, hint, fun f hf hfK ↦ ?_⟩
    -- Each edge of the ear has an end outside `V(K)`, so it is not an edge of `K`.
    obtain ⟨y, hy, hyK⟩ := hedge f hf
    exact hyK (mem_vertexSet_of_inc_of_mem_edgeSet hKG hfK hy)
  · -- Every vertex is already present, so a missing edge is an ear of length one.
    push Not at hout
    obtain ⟨f, hfG, hfK⟩ := hproper.resolve_left (by rintro ⟨x, hx, hx'⟩; exact hx' (hout x hx))
    obtain ⟨p, q, hpq⟩ := exists_isLink_of_mem_edgeSet hfG
    have hne : p ≠ q := by rintro rfl; exact hnl hpq
    refine ⟨p, q, [f], .single hpq hne, hne, hout p hpq.left_mem, hout q hpq.right_mem,
      by simp, fun y hy hyp hyq ↦ ?_, fun g hg ↦ ?_⟩
    · -- A one-edge path visits nothing but its two ends, so freshness is vacuous.
      rw [walkVertices_cons hpq, walkVertices_nil] at hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      exacts [absurd rfl hyp, absurd rfl hyq]
    · obtain rfl : g = f := by simpa using hg
      exact hfK

/-- **One step of the relative ear decomposition.** The ear of
`Graph.IsTwoConnected.relative_ear_exists`, glued on with `Graph.IsTwoConnected.ear`: the
enlarged graph is again a 2-connected subgraph of `G` between `K` and `G`, and it has an edge
that `K` did not have.

The ear data is handed back alongside the enlarged graph, because a consumer of the geometric
version needs the *path*, not merely the fact that the subgraph grew. -/
theorem IsTwoConnected.relative_grows_by_ear (hG : G.IsTwoConnected) (hK : K.IsTwoConnected)
    (hKG : K ≤ G) (hnl : ∀ ⦃g x⦄, ¬ G.IsLoopAt g x)
    (hproper : (∃ x ∈ V(G), x ∉ V(K)) ∨ (∃ g ∈ E(G), g ∉ E(K))) :
    ∃ a b D, G.IsPath a D b ∧ a ≠ b ∧ a ∈ V(K) ∧ b ∈ V(K) ∧
      (∀ y ∈ G.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(K)) ∧
      (K.union (G.pathGraphOf a D)).IsTwoConnected ∧
      K ≤ K.union (G.pathGraphOf a D) ∧ K.union (G.pathGraphOf a D) ≤ G ∧
      ∃ g ∈ E(K.union (G.pathGraphOf a D)), g ∉ E(K) := by
  obtain ⟨a, b, D, hpath, hab, ha, hb, hDne, hint, hnew⟩ :=
    hG.relative_ear_exists hK hKG hnl hproper
  have hearle : G.pathGraphOf a D ≤ G := pathGraphOf_le hpath.isWalk
  have hearP : (G.pathGraphOf a D).IsPathGraph a D b := hpath.isPathGraph_pathGraphOf
  obtain ⟨g, hgD⟩ : ∃ g, g ∈ D := by
    cases D with
    | nil => exact absurd rfl hDne
    | cons g t => exact ⟨g, List.mem_cons_self⟩
  exact ⟨a, b, D, hpath, hab, ha, hb, hint,
    hK.ear (Compatible.of_le_le hKG hearle) hearP hab ha hb,
    left_le_union _ _, union_le hKG hearle,
    g, Set.mem_union_right _ (hearP.mem_edgeSet hgD), hnew g hgD⟩

/-! ### Reading the enlarged graph

Two unfoldings a consumer of the induction principle below needs immediately, since the step's
conclusion is about `B.union (G.pathGraphOf a D)`. Both are immediate from the simp lemmas of
`Schoenflies/Graph/TwoConnected.lean` and `Schoenflies/Graph/PathGraph.lean`; they are here
only so that no consumer has to rediscover which two to combine. -/

@[simp]
theorem vertexSet_union_pathGraphOf (B G : Graph α β) (a : α) (D : List β) :
    V(B.union (G.pathGraphOf a D)) = V(B) ∪ G.walkVertices a D := rfl

theorem edgeSet_union_pathGraphOf (h : G.IsWalk a D b) :
    E(B.union (G.pathGraphOf a D)) = E(B) ∪ {e | e ∈ D} := by
  rw [edgeSet_union, pathGraphOf_edgeSet h]

/-! ### Iterating: the decomposition itself -/

/-- **`lem:relative-ear`.** A 2-connected subgraph `K` of a finite loopless 2-connected graph
`G` grows to `G` by repeatedly adding relative ears, stated as the induction principle a
consumer uses: whatever holds of `K` and survives the addition of one ear holds of `G`.

The step is given the whole ear — the path `D` of `G`, its two distinct ends in the current
subgraph `B`, and the fact that its other vertices are outside `B` — together with
`B.IsTwoConnected`, `K ≤ B` and `B ≤ G`.

"Finiteness terminates the process" is the strong induction below on `(E(G) \ E(B)).ncard`:
every ear contributes an edge of `G` that `B` was missing, and the process can only be stuck
when `B` has all of `G`'s vertices and edges, which makes `B = G`. -/
theorem IsTwoConnected.ear_decomposition {motive : Graph α β → Prop} [G.Finite]
    (hG : G.IsTwoConnected) (hnl : ∀ ⦃g x⦄, ¬ G.IsLoopAt g x)
    (hK : K.IsTwoConnected) (hKG : K ≤ G) (base : motive K)
    (step : ∀ (B : Graph α β) (a b : α) (D : List β), B.IsTwoConnected → K ≤ B → B ≤ G →
      motive B → G.IsPath a D b → a ≠ b → a ∈ V(B) → b ∈ V(B) →
      (∀ y ∈ G.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B)) →
      motive (B.union (G.pathGraphOf a D))) :
    motive G := by
  -- One step, packaged with the strict drop of the measure.
  have hstep : ∀ B : Graph α β, B ≠ G → B.IsTwoConnected → K ≤ B → B ≤ G → motive B →
      ∃ B' : Graph α β, B'.IsTwoConnected ∧ K ≤ B' ∧ B' ≤ G ∧ motive B' ∧
        (E(G) \ E(B')).ncard < (E(G) \ E(B)).ncard := by
    intro B hBne hB hKB hBG hmot
    -- A subgraph that is not the graph is missing a vertex or an edge.
    have hproper : (∃ x ∈ V(G), x ∉ V(B)) ∨ (∃ g ∈ E(G), g ∉ E(B)) := by
      by_contra hcon
      push Not at hcon
      exact hBne (eq_of_le_of_subset_subset hBG (fun x hx ↦ hcon.1 x hx) fun g hg ↦ hcon.2 g hg)
    obtain ⟨a, b, D, hpath, hab, ha, hb, hint, hB'two, hBB', hB'G, g, hgB', hgB⟩ :=
      hG.relative_grows_by_ear hB hBG hnl hproper
    refine ⟨_, hB'two, hKB.trans hBB', hB'G,
      step B a b D hB hKB hBG hmot hpath hab ha hb hint, ?_⟩
    -- The new edge is one the old subgraph was missing, and nothing was lost.
    refine Set.ncard_lt_ncard ⟨fun f hf ↦ ⟨hf.1, fun hfB ↦ hf.2 (hBB'.edgeSet_mono hfB)⟩, ?_⟩
      ((finite_edgeSet G).subset sdiff_subset)
    exact fun hcon ↦ (hcon ⟨hB'G.edgeSet_mono hgB', hgB⟩).2 hgB'
  -- Strong induction on the number of edges of `G` the subgraph is still missing.
  have key : ∀ n, ∀ B : Graph α β, (E(G) \ E(B)).ncard ≤ n → B.IsTwoConnected → K ≤ B →
      B ≤ G → motive B → motive G := by
    intro n
    induction n with
    | zero =>
      intro B hcard hB hKB hBG hmot
      by_cases hBne : B = G
      · exact hBne ▸ hmot
      · -- Nothing is missing, yet an ear was found: its edges were missing after all.
        obtain ⟨B', -, -, -, -, hlt⟩ := hstep B hBne hB hKB hBG hmot
        exact absurd (Nat.lt_of_lt_of_le hlt hcard) (Nat.not_lt_zero _)
    | succ n ih =>
      intro B hcard hB hKB hBG hmot
      by_cases hBne : B = G
      · exact hBne ▸ hmot
      · obtain ⟨B', hB', hKB', hB'G, hmot', hlt⟩ := hstep B hBne hB hKB hBG hmot
        exact ih B' (by omega) hB' hKB' hB'G hmot'
  exact key _ K le_rfl hK le_rfl hKG base

end Graph

end BundlePart393

section BundlePart394
/- Source: dev/planar_search/schoenflies_port/Schoenflies/Graph/OuterFace.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/


/-!
# The outer face

Exactly one face of a finite plane graph is unbounded.

The plane fact this needs is not "the exterior of a large disk is connected" but the exterior
of a *square*, and that one is elementary — `Plane.isConnected_beyondSquare`, four convex
half-planes with consecutive ones sharing a corner. The disk version is what would have
needed a traversal of the circle, which a trigonometry-free development withholds.

No face is produced as data: a face is named by a point of it, as `Graph.face` always has
been, so "the outer face" is "the face through any point far enough out".

## Blueprint

* `exists_unbounded_face` — some face is unbounded.
* `unbounded_face_unique` — any two unbounded faces coincide.
* `beyondSquare_subset_face` — an unbounded face swallows the whole outside of any square
  containing the drawing. This is the working form: it is how one proves a given point lies in
  the outer face.
-/

open Metric Set Schoenflies unitInterval
open scoped Graph

namespace Graph

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}

/-- A closed axis-parallel square is bounded: it sits inside a Euclidean ball of radius
`√2 · r`, by the norm comparison. -/
theorem isBounded_closedSquare (r : ℝ) :
    Bornology.IsBounded (Schoenflies.Plane.closedSquare 0 r) := by
  refine (Metric.isBounded_closedBall (x := (0 : Plane)) (r := Real.sqrt 2 * r)).subset ?_
  intro x hx
  have hsup : Schoenflies.Plane.supNorm x ≤ r := by
    simpa [Schoenflies.Plane.closedSquare] using hx
  have : ‖x‖ ≤ Real.sqrt 2 * r := by
    refine le_trans (Schoenflies.Plane.norm_le_sqrt_two_mul_supNorm x) ?_
    exact mul_le_mul_of_nonneg_left hsup (Real.sqrt_nonneg 2)
  simpa [Metric.mem_closedBall, dist_eq_norm] using this

/-- A square containing the whole drawing. -/
theorem IsDrawing.exists_closedSquare [G.Finite] (h : IsDrawing G drawing) :
    ∃ r : ℝ, 0 ≤ r ∧ pointSet G drawing ⊆ Schoenflies.Plane.closedSquare 0 r :=
  Schoenflies.Plane.exists_closedSquare_of_isBounded h.isCompact_pointSet.isBounded

/-- Outside a square containing the drawing, every point is in the exterior. -/
theorem beyondSquare_subset_exterior {r : ℝ}
    (hr : pointSet G drawing ⊆ Schoenflies.Plane.closedSquare 0 r) :
    Schoenflies.Plane.beyondSquare r ⊆ exterior G drawing := by
  rw [Schoenflies.Plane.beyondSquare_eq_compl]
  exact compl_subset_compl.2 hr

/-- The outside of a containing square lies wholly inside one face — the face through any of
its points. This is the working form of "there is an outer face". -/
theorem beyondSquare_subset_face {r : ℝ}
    (hr : pointSet G drawing ⊆ Schoenflies.Plane.closedSquare 0 r) {base : Plane}
    (hbase : base ∈ Schoenflies.Plane.beyondSquare r) :
    Schoenflies.Plane.beyondSquare r ⊆ face G drawing base :=
  (Schoenflies.Plane.isConnected_beyondSquare r).isPreconnected.subset_connectedComponentIn
    hbase (beyondSquare_subset_exterior hr)

/-- The outside of a square is unbounded: it contains points of every size. -/
theorem not_isBounded_beyondSquare (r : ℝ) :
    ¬ Bornology.IsBounded (Schoenflies.Plane.beyondSquare r) := by
  intro hb
  obtain ⟨s, -, hs⟩ := Schoenflies.Plane.exists_closedSquare_of_isBounded hb
  -- A point beyond both radii is in the outside but not in the square that was claimed to
  -- contain it.
  set t : ℝ := max (max r s) 0 + 1 with ht
  have ht0 : 0 ≤ t := by
    have := le_max_right (max r s) 0; simp only [ht]; linarith
  have htr : r < t := by
    have h1 := le_max_left r s
    have h2 := le_max_left (max r s) 0
    simp only [ht]; linarith
  have hts : s < t := by
    have h1 := le_max_right r s
    have h2 := le_max_left (max r s) 0
    simp only [ht]; linarith
  -- `Plane.mk t 0` has first coordinate `t` definitionally, so `show` states the real goal.
  have hmem : Schoenflies.Plane.mk t 0 ∈ Schoenflies.Plane.beyondSquare r :=
    Or.inl (show r < |t| by rw [abs_of_nonneg ht0]; exact htr)
  have hin := hs hmem
  simp only [Schoenflies.Plane.closedSquare, mem_setOf_eq, Schoenflies.Plane.supDist_zero,
    Schoenflies.Plane.supNorm, max_le_iff] at hin
  have h1 : |t| ≤ s := hin.1
  rw [abs_of_nonneg ht0] at h1
  linarith

/-- Some face is unbounded. -/
theorem exists_unbounded_face [G.Finite] (h : IsDrawing G drawing) :
    ∃ base ∈ exterior G drawing, ¬ Bornology.IsBounded (face G drawing base) := by
  obtain ⟨r, hr0, hr⟩ := h.exists_closedSquare
  have hmem : Schoenflies.Plane.mk (r + 1) 0 ∈ Schoenflies.Plane.beyondSquare r :=
    Or.inl (show r < |r + 1| by
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ r + 1)]; linarith)
  refine ⟨Schoenflies.Plane.mk (r + 1) 0, beyondSquare_subset_exterior hr hmem, fun hb => ?_⟩
  exact not_isBounded_beyondSquare r (hb.subset (beyondSquare_subset_face hr hmem))

/-- Any two unbounded faces coincide: an unbounded face escapes every containing square, so it
swallows the whole outside and is named by any point of it. -/
theorem unbounded_face_unique [G.Finite] (h : IsDrawing G drawing) {b c : Plane}
    (hbu : ¬ Bornology.IsBounded (face G drawing b))
    (hcu : ¬ Bornology.IsBounded (face G drawing c)) :
    face G drawing b = face G drawing c := by
  obtain ⟨r, hr0, hr⟩ := h.exists_closedSquare
  -- An unbounded face is not contained in the square, so it meets the outside.
  have escape : ∀ z : Plane, ¬ Bornology.IsBounded (face G drawing z) →
      ∃ w, w ∈ face G drawing z ∧ w ∈ Schoenflies.Plane.beyondSquare r := by
    intro z hz
    by_contra hcon
    push Not at hcon
    refine hz ((isBounded_closedSquare r).subset fun w hw => ?_)
    have hw' : w ∉ Schoenflies.Plane.beyondSquare r := hcon w hw
    rw [Schoenflies.Plane.beyondSquare_eq_compl] at hw'
    simpa using hw'
  obtain ⟨w, hwb, hwout⟩ := escape b hbu
  obtain ⟨v, hvc, hvout⟩ := escape c hcu
  -- Each face therefore swallows the whole outside, so the two share a point.
  have hbeyond_b : Schoenflies.Plane.beyondSquare r ⊆ face G drawing b := by
    have hsub := beyondSquare_subset_face (G := G) (drawing := drawing) hr hwout
    have hwe : face G drawing w = face G drawing b := (connectedComponentIn_eq hwb).symm
    rwa [hwe] at hsub
  have hbeyond_c : Schoenflies.Plane.beyondSquare r ⊆ face G drawing c := by
    have hsub := beyondSquare_subset_face (G := G) (drawing := drawing) hr hvout
    have hve : face G drawing v = face G drawing c := (connectedComponentIn_eq hvc).symm
    rwa [hve] at hsub
  obtain ⟨z, hz⟩ := (Schoenflies.Plane.isConnected_beyondSquare r).nonempty
  have e1 : face G drawing b = face G drawing z := connectedComponentIn_eq (hbeyond_b hz)
  have e2 : face G drawing c = face G drawing z := connectedComponentIn_eq (hbeyond_c hz)
  rw [e1, e2]

end Graph

end BundlePart394

section BundlePart395
/- Source: dev/planar_search/schoenflies_port/Schoenflies/FaceCycles.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/





/-!
# Face cycles: the base cycle, and the faces of a plane graph that grows by ears

`lem:face-cycles` — *every face of a finite 2-connected polygonal plane graph has a cycle as
its boundary and is one of the two complementary regions of that cycle* — is proved by growing
the graph from a cycle by ears (`Graph.IsTwoConnected.ear_decomposition`) and applying
`thm:polygonal-crosscut` at each step. This file supplies everything in that proof that is not
the crosscut application itself. **The lemma is not proved here**; see "What is missing" below,
which says exactly what is in the way.

## The base cycle

The blueprint's first paragraph, in full. *"First choose a cycle of length at least three.
Such a cycle exists: under our convention the graph has at least three vertices, and every
vertex has at least two distinct neighbors. Indeed, if a vertex `v` had only one distinct
neighbor `w`, then deleting `w` would isolate `v` from some third vertex, contrary to
2-connectivity. Now take a maximal simple path. An endpoint has a neighbor on the path other
than its predecessor, and the resulting closed subpath is a cycle of length at least three."*

`Graph.IsTwoConnected.exists_adj_ne` is the two-neighbours sentence; "take a maximal simple
path" is `Graph.exists_longest_path`, already in `Schoenflies/Graph/Tree.lean` and not rebuilt
here; and `Graph.IsTwoConnected.exists_long_cycle` is the conclusion, packaged as
`Graph.IsLongCycle`, a cycle together with a *named* third vertex. Naming the third vertex
rather than counting is what both consumers want: the counting clause of
`Graph.IsTwoConnected`, and — later — the non-degeneracy of the polygon the cycle draws.

`Graph.cycleGraph` is that cycle as a subgraph, and `Graph.IsLongCycle.isTwoConnected` is
*"the cycle `C` is 2-connected, so Lemma `lem:relative-ear` builds the graph from `C`"*. This
is the one place "length at least three" is used: a two-vertex cycle is a `Graph.banana`, and
`Graph.not_isTwoConnected_banana` says it is not 2-connected.

## One step of the induction

Adding an ear removes the ear's own point set from the exterior and changes nothing else:
`Graph.pointSet_union`, `Graph.exterior_union` and `Graph.face_union_eq_of_disjoint` are
*"all other faces are unchanged"*.

`Graph.IsDrawing.exists_face_of_ear` is *"its interior is connected and disjoint from the
current graph, so it lies in one current face `F`"*: the ear's realisation without its two ends
is the interior of an arc, hence connected
(`Schoenflies.IsArcBetween.isConnected_diff`), and it misses the drawing of the current
subgraph altogether (`Graph.IsDrawing.edgesCover_inter_pointSet`).
`Graph.IsDrawing.ends_mem_frontier_face` is the next sentence, *"the ear's two endpoints are
limits of its interior, which lies in `F`, so they lie on `∂F`"* — which is what makes the ear
a crosscut of that face.

`Graph.IsDrawing.mono` — a subgraph of a plane graph is a plane graph, with the same drawing —
is what lets the induction talk about the faces of the current subgraph at all.

## An interface repair

`Graph.IsTwoConnected.ear_decomposition` hands its step the ear's path but **not** the clause
`∀ g ∈ D, g ∉ E(B)`, which `Graph.IsTwoConnected.relative_ear_exists` proves and which
`Graph.IsTwoConnected.relative_grows_by_ear` drops on the way. A geometric consumer needs it:
without it the ear may be drawn right on top of the current subgraph, and
`Graph.IsDrawing.edgesCover_inter_pointSet` is false. `Graph.ear_edges_notMem_or_union_eq`
recovers it in the only form available from the outside — either every edge of the ear is new,
or the ear is a single edge the subgraph already had and the enlarged graph *is* the old graph,
so the step has nothing to prove. The better fix is for the integrator to add the clause to
`relative_grows_by_ear` and to `ear_decomposition`; that would make this lemma unnecessary.

## What is missing

The crosscut application, and therefore `lem:face-cycles` itself. `thm:polygonal-crosscut` is
available as `Schoenflies.IsPolygonalCrosscut` and `Schoenflies.polygonal_crosscut`, whose
hypotheses are stated for `Schoenflies.ClosedPolygon`s: an explicit cyclic vertex list with
`vertex_inj`, `edges_meet` and `corner` (no two consecutive edges collinear). The realisation
of a graph cycle arrives here as a **set** — `Graph.edgesCover drawing (e :: D)` — which
`Graph.IsDrawing.cycle_isJordanCurve` knows to be a Jordan curve and `Graph.polygonal_redrawing`
knows to be polygonal. Turning such a set into a `ClosedPolygon` (enumerate its vertices
cyclically, delete the redundant collinear ones, and derive `vertex_inj` and `edges_meet` from
simplicity) is a construction `main` does not have, and the same construction is needed again
for the two curves `Aᵢ ∪ P` that the crosscut produces. Nothing below pretends to it, and no
statement below is weaker than its blueprint counterpart.

## Namespace

Root `Graph`, as fixed by `Schoenflies/Graph/Walk.lean`. The two arc lemmas are stated in
`Schoenflies`, where the rest of the arc theory lives.

## Blueprint

* `Graph.IsTwoConnected.exists_adj_ne` — "every vertex has at least two distinct neighbors".
* `Graph.IsLongCycle`, `Graph.IsTwoConnected.exists_long_cycle` — "the resulting closed subpath
  is a cycle of length at least three".
* `Graph.cycleGraph`, `Graph.IsLongCycle.isTwoConnected` — "the cycle `C` is 2-connected, so
  Lemma `lem:relative-ear` builds the graph from `C`".
* `Graph.ear_edges_notMem_or_union_eq` — the ear's edges are new, or the ear is not an ear.
* `Graph.pointSet_union`, `Graph.exterior_union`, `Graph.face_union_subset`,
  `Graph.face_union_eq_of_disjoint` — "all other faces are unchanged".
* `Graph.IsDrawing.mono` — the current subgraph is itself a plane graph.
* `Schoenflies.IsArcBetween.isConnected_diff`,
  `Schoenflies.IsArcBetween.left_mem_closure_diff`, `…right_mem_closure_diff`,
  `Graph.IsDrawing.edgesCover_inter_pointSet`, `Graph.IsDrawing.exists_face_of_ear`,
  `Graph.IsDrawing.ends_mem_frontier_face` — "its interior is connected and disjoint from the
  current graph, so it lies in one current face `F` … the ear's two endpoints are limits of its
  interior, which lies in `F`, so they lie on `∂F`; the ear is therefore a crosscut of that
  side".
-/

open Set
open scoped Graph

namespace Graph

variable {α β : Type*} {G H K B : Graph α β} {u v w x y z c : α} {e f g : β} {D W : List β}

/-! ## Two distinct neighbours -/

/-- **A vertex of a loopless 2-connected graph has a neighbour other than any prescribed
vertex** — in particular it has two distinct neighbours, and neither is itself. -/
theorem IsTwoConnected.exists_adj_ne (h : G.IsTwoConnected)
    (hnl : ∀ ⦃g x⦄, ¬ G.IsLoopAt g x) (hv : v ∈ V(G)) (w : α) :
    ∃ x, G.Adj v x ∧ x ≠ w := by
  rcases eq_or_ne v w with rfl | hvw
  · -- Deleting nothing: a walk to any other vertex leaves along a non-loop.
    obtain ⟨z, hz, hzv, -⟩ := h.hasThreeVertices.exists_ne_ne v v
    obtain ⟨T, hT⟩ := h.connected.reaches hv hz
    cases hT with
    | nil => exact absurd rfl hzv
    | @cons _ y _ g _ hl _ => exact ⟨y, ⟨g, hl⟩, fun hh ↦ hnl (hh ▸ hl)⟩
  · -- Deleting `w`: a walk to a third vertex leaves along an edge that survived it.
    obtain ⟨z, hz, hzv, hzw⟩ := h.hasThreeVertices.exists_ne_ne v w
    obtain ⟨T, hT⟩ := (h.deleteVerts_connected' w).reaches
      (mem_deleteVerts_singleton_of_ne hv hvw) (mem_deleteVerts_singleton_of_ne hz hzw)
    cases hT with
    | nil => exact absurd rfl (Ne.symm hzv)
    | @cons _ y _ g _ hl _ =>
      exact ⟨y, ⟨g, hl.mono deleteVerts_le⟩, (mem_deleteVerts_singleton.1 hl.right_mem).2⟩

/-! ## The base cycle

"Take a maximal simple path" is `Graph.exists_longest_path`, already in
`Schoenflies/Graph/Tree.lean` — it is what the three-leaf lemma runs on — so nothing here
rebuilds it. -/

/-- **A path from a vertex back to itself is empty.** The first step would depart from the
vertex the rest of the path arrives at, which the freshness clause forbids. -/
theorem IsPath.eq_nil_of_eq (h : G.IsPath u W u) : W = [] := by
  cases h with
  | nil => rfl
  | cons _ hT hfresh => exact absurd hT.target_mem_walkVertices hfresh

/-- A cycle with at least three vertices — the blueprint's "cycle of length at least three".
The third vertex is named rather than counted, because that is what both consumers want. -/
structure IsLongCycle (G : Graph α β) (e : β) (u v : α) (D : List β) (w : α) : Prop where
  /-- The edge and the detour form a cycle. -/
  isCycle : G.IsCycleThrough e u v D
  /-- The detour visits a third vertex … -/
  mem : w ∈ G.walkVertices u D
  /-- … distinct from the source of the edge … -/
  ne_left : w ≠ u
  /-- … and from its target. -/
  ne_right : w ≠ v

namespace IsLongCycle

variable (h : G.IsLongCycle e u v D w)
include h

theorem isLink : G.IsLink e u v := h.isCycle.isLink

theorem isPath : G.IsPath u D v := h.isCycle.isPath

theorem notMem : e ∉ D := h.isCycle.notMem

/-- The two ends of the edge are distinct: otherwise the detour would be a path from a vertex
to itself, hence empty, and would visit no third vertex. -/
theorem ne : u ≠ v := by
  rintro rfl
  have hnil : D = [] := h.isPath.eq_nil_of_eq
  have hmem := h.mem
  rw [hnil, walkVertices_nil] at hmem
  exact h.ne_left hmem

end IsLongCycle

/-- **"The resulting closed subpath is a cycle of length at least three."** A finite loopless
2-connected graph has a cycle with three distinct vertices.

Take a maximal path `u —W→ v`. Its source `u` has a neighbour `x` other than the vertex `w₀`
the path first steps to (`Graph.IsTwoConnected.exists_adj_ne`), and `x` lies on the path:
otherwise the edge to it could be prepended, contradicting maximality. Cutting the path at `x`
gives a path from `u` to `x` whose first step is still to `w₀`, and the chord closes it into a
cycle through `u`, `w₀` and `x`. The chord is not an edge of that piece: an edge at `u` in the
tail is what the path's freshness clause forbids, and the first edge is not the chord because
their far ends differ. -/
theorem IsTwoConnected.exists_long_cycle [G.Finite] (h : G.IsTwoConnected)
    (hnl : ∀ ⦃g x⦄, ¬ G.IsLoopAt g x) :
    ∃ g u x D w, G.IsLongCycle g u x D w := by
  obtain ⟨p, hp, -⟩ := h.hasThreeVertices
  obtain ⟨u, v, W, hpath, hmax⟩ := exists_longest_path hp
  -- The maximal path is not empty: an edge at its source could otherwise be prepended.
  obtain ⟨f, W', rfl⟩ : ∃ f W', W = f :: W' := by
    cases hW : W with
    | cons f W' => exact ⟨f, W', rfl⟩
    | nil =>
      obtain ⟨y, ⟨g, hl⟩, hyu⟩ := h.exists_adj_ne hnl hpath.left_mem u
      have hle := hmax _ _ _ (IsPath.single hl.symm hyu)
      rw [hW] at hle
      simp at hle
  obtain ⟨w₀, hl₀, hpath', hfresh⟩ : ∃ w₀, G.IsLink f u w₀ ∧ G.IsPath w₀ W' v ∧
      u ∉ G.walkVertices w₀ W' := by
    cases hpath with
    | cons hl hW hfr => exact ⟨_, hl, hW, hfr⟩
  -- A second neighbour of the source, distinct from the vertex the path first steps to.
  obtain ⟨x, ⟨g, hlg⟩, hxw₀⟩ := h.exists_adj_ne hnl hpath.left_mem w₀
  have hxu : x ≠ u := fun hh ↦ hnl (hh ▸ hlg)
  -- It lies on the path: otherwise the chord would prepend to it.
  have hxW : x ∈ G.walkVertices u (f :: W') := by
    by_contra hx
    have hle := hmax _ _ _ (IsPath.cons hlg.symm hpath hx)
    simp at hle
  obtain ⟨W₁, W₂, hsplit, h₁, -, -⟩ := hpath.split hxW
  have hW₁sub : W₁ ⊆ f :: W' := hsplit ▸ List.subset_append_left _ _
  -- The chord is not an edge of the piece: not the first edge, and not one further along.
  have hgW₁ : g ∉ W₁ := by
    intro hg
    rcases List.mem_cons.1 (hW₁sub hg) with rfl | hg'
    · exact hxw₀ (hlg.right_unique hl₀)
    · exact hfresh (mem_walkVertices_of_mem_covered ⟨g, hg', hlg.inc_left⟩)
  -- The piece starts with the first edge, so it visits the vertex the path first stepped to.
  have hfW₁ : f ∈ W₁ := by
    rcases W₁ with _ | ⟨a, T⟩
    · exact absurd h₁.isWalk.eq_of_nil (Ne.symm hxu)
    · obtain ⟨rfl, -⟩ : f = a ∧ W' = T ++ W₂ := by simpa using hsplit
      exact List.mem_cons_self
  exact ⟨g, u, x, W₁, w₀, ⟨hlg, h₁, hgW₁⟩,
    mem_walkVertices_of_mem_covered ⟨f, hfW₁, hl₀.inc_right⟩,
    fun hh ↦ hnl (hh ▸ hl₀), Ne.symm hxw₀⟩

/-! ## The cycle as a subgraph, and its 2-connectivity

`Graph.IsTwoConnected.ear_decomposition` starts from a 2-connected subgraph. The subgraph the
blueprint starts from is the base cycle, and this section builds it and proves it 2-connected.
This is the one place where "length at least three" is used: a two-vertex cycle is a
`Graph.banana`, and `Graph.not_isTwoConnected_banana` says it is not 2-connected. -/

/-- **A path graph grows with its edge list.** General, and not in
`Schoenflies/Graph/PathGraph.lean`; the integrator may want to hoist it. -/
theorem pathGraphOf_mono (h : W ⊆ D) : G.pathGraphOf u W ≤ G.pathGraphOf u D where
  vertexSet_mono := by
    simpa only [pathGraphOf_vertexSet] using walkVertices_mono (u := u) h
  isLink_mono := by
    intro f x y hl
    obtain ⟨hf, hxy, hx, hy⟩ := pathGraphOf_isLink.1 hl
    exact pathGraphOf_isLink.2
      ⟨h hf, hxy, walkVertices_mono h hx, walkVertices_mono h hy⟩

/-- The subgraph of `G` drawn by a cycle: the detour followed by the edge, as a closed walk.
Exported as the object rather than hidden behind an existential — the consumer of
`lem:face-cycles` needs the graph itself, to feed it to the ear decomposition. -/
def cycleGraph (G : Graph α β) (u : α) (e : β) (D : List β) : Graph α β :=
  G.pathGraphOf u (D ++ [e])

/-- The detour spans a path subgraph of the cycle. -/
theorem pathGraphOf_le_cycleGraph : G.pathGraphOf u D ≤ G.cycleGraph u e D :=
  pathGraphOf_mono (List.subset_append_left _ _)

namespace IsCycleThrough

variable (hc : G.IsCycleThrough e u v D)
include hc

/-- Going round: the detour and then the edge is a closed walk at the source. -/
theorem isWalk_round : G.IsWalk u (D ++ [e]) u :=
  hc.isPath.isWalk.append (IsWalk.single hc.isLink.symm)

/-- Closing the cycle adds no vertex: both ends of the edge are already on the detour. -/
theorem walkVertices_round : G.walkVertices u (D ++ [e]) = G.walkVertices u D := by
  refine Set.Subset.antisymm (fun y hy ↦ ?_) (walkVertices_mono (List.subset_append_left _ _))
  rcases mem_walkVertices_iff.1 hy with rfl | hcov
  · exact mem_walkVertices_self
  rw [coveredVertices_append] at hcov
  rcases hcov with hcov | ⟨g, hg, hinc⟩
  · exact mem_walkVertices_of_mem_covered hcov
  obtain rfl : g = e := by simpa using hg
  rcases hinc.eq_or_eq_of_isLink hc.isLink with rfl | rfl
  · exact mem_walkVertices_self
  · exact hc.isPath.target_mem_walkVertices

@[simp]
theorem cycleGraph_vertexSet : V(G.cycleGraph u e D) = G.walkVertices u D := by
  rw [cycleGraph, pathGraphOf_vertexSet, hc.walkVertices_round]

theorem cycleGraph_le : G.cycleGraph u e D ≤ G := pathGraphOf_le hc.isWalk_round

theorem cycleGraph_edgeSet : E(G.cycleGraph u e D) = {f | f ∈ D ++ [e]} :=
  pathGraphOf_edgeSet hc.isWalk_round

theorem left_mem_cycleGraph : u ∈ V(G.cycleGraph u e D) := by
  rw [hc.cycleGraph_vertexSet]; exact mem_walkVertices_self

theorem right_mem_cycleGraph : v ∈ V(G.cycleGraph u e D) := by
  rw [hc.cycleGraph_vertexSet]; exact hc.isPath.target_mem_walkVertices

/-- The edge of the cycle really is an edge of the cycle graph, joining the same two ends. -/
theorem cycleGraph_isLink : (G.cycleGraph u e D).IsLink e u v :=
  pathGraphOf_isLink.2 ⟨by simp, hc.isLink,
    hc.walkVertices_round ▸ mem_walkVertices_self,
    hc.walkVertices_round ▸ hc.isPath.target_mem_walkVertices⟩

/-- The cycle graph is connected: every vertex it has is visited by the detour, and the
detour's own prefix runs there from the source. -/
theorem cycleGraph_connected : (G.cycleGraph u e D).Connected := by
  refine Connected.of_hub hc.left_mem_cycleGraph fun x hx ↦ ?_
  rw [hc.cycleGraph_vertexSet] at hx
  obtain ⟨W₁, W₂, hcat, h₁, -, -⟩ := hc.isPath.split hx
  refine ⟨W₁, h₁.isWalk.anti hc.cycleGraph_le hc.left_mem_cycleGraph fun g hg ↦ ?_⟩
  rw [hc.cycleGraph_edgeSet]
  exact List.mem_append_left _ (hcat ▸ List.mem_append_left _ hg)

end IsCycleThrough

namespace IsLongCycle

variable (h : G.IsLongCycle e u v D w)
include h

theorem mem_cycleGraph : w ∈ V(G.cycleGraph u e D) := by
  rw [h.isCycle.cycleGraph_vertexSet]; exact h.mem

/-- **A cycle with three vertices is 2-connected**, which is what
`Graph.IsTwoConnected.ear_decomposition` asks of its starting subgraph.

Delete a vertex `c`. One of the two ends of the cycle's edge survives, and it is the hub:
every remaining vertex reaches an end of the *detour* inside the detour
(`Graph.IsPathGraph.reaches_an_end`), an end which — having been reached after the deletion —
survived it too, so the cycle's edge is still there to carry it the rest of the way. -/
theorem isTwoConnected : (G.cycleGraph u e D).IsTwoConnected where
  hasThreeVertices :=
    ⟨u, h.isCycle.left_mem_cycleGraph, v, h.isCycle.right_mem_cycleGraph,
      w, h.mem_cycleGraph, h.ne, Ne.symm h.ne_left, Ne.symm h.ne_right⟩
  connected := h.isCycle.cycleGraph_connected
  deleteVerts_connected := by
    intro c _
    set Kc := G.cycleGraph u e D with hKc
    set Pc := G.pathGraphOf u D with hPc
    have hPK : Pc.deleteVerts {c} ≤ Kc.deleteVerts {c} :=
      deleteVerts_mono pathGraphOf_le_cycleGraph _
    have hPpath : Pc.IsPathGraph u D v := h.isPath.isPathGraph_pathGraphOf
    -- The hub is whichever end of the cycle's edge survived; the argument is symmetric in
    -- the two, so it is done once for a named pair and applied twice.
    have main : ∀ a b : α, Kc.IsLink e a b → a ≠ c →
        (∀ x ∈ V(Kc), x ≠ c →
          (Pc.deleteVerts {c}).Reaches x a ∨ (Pc.deleteVerts {c}).Reaches x b) →
        (Kc.deleteVerts {c}).Connected := by
      intro a b hab hac hends
      refine Connected.of_hub (mem_deleteVerts_singleton_of_ne hab.left_mem hac) fun x hx ↦ ?_
      rw [vertexSet_deleteVerts] at hx
      obtain ⟨hxK, hxc⟩ := hx
      have hxc' : x ≠ c := by simpa using hxc
      rcases hends x hxK hxc' with hr | hr
      · exact (hr.mono hPK).symm
      · -- The far end was reached, so it survived; the cycle's edge joins it to the hub.
        have hbc : b ≠ c := (mem_deleteVerts_singleton.1 (hr.mono hPK).right_mem).2
        have hedge : (Kc.deleteVerts {c}).Reaches b a :=
          ⟨[e], IsWalk.single ((deleteVerts_isLink _ _).2 ⟨hab.symm, by simpa using hbc,
            by simpa using hac⟩)⟩
        exact ((hr.mono hPK).trans hedge).symm
    have hV : ∀ x ∈ V(Kc), x ∈ V(Pc) := fun x hx ↦ by
      rw [hKc, h.isCycle.cycleGraph_vertexSet] at hx; exact hx
    by_cases hcu : u = c
    · -- The source is gone, so the target is the hub.
      refine main v u h.isCycle.cycleGraph_isLink.symm (fun hh ↦ h.ne (hh.trans hcu.symm).symm)
        fun x hx hxc ↦ (hPpath.reaches_an_end (hV x hx) hxc).symm
    · exact main u v h.isCycle.cycleGraph_isLink hcu
        fun x hx hxc ↦ hPpath.reaches_an_end (hV x hx) hxc

end IsLongCycle


/-- A machine check that the two halves fit: the base cycle really is a legal starting point
for `Graph.IsTwoConnected.ear_decomposition`, so a consumer that can do the base case on
`G.cycleGraph u e D` and the ear step gets the conclusion for `G`. Nothing but the two
theorems is used. -/
example {motive : Graph α β → Prop} [G.Finite] (hG : G.IsTwoConnected)
    (hnl : ∀ ⦃g x⦄, ¬ G.IsLoopAt g x)
    (base : ∀ (e : β) (u v : α) (D : List β) (w : α), G.IsLongCycle e u v D w →
      motive (G.cycleGraph u e D))
    (step : ∀ (B : Graph α β) (a b : α) (D : List β), B.IsTwoConnected → B ≤ G → motive B →
      G.IsPath a D b → a ≠ b → a ∈ V(B) → b ∈ V(B) →
      (∀ y ∈ G.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B)) →
      motive (B.union (G.pathGraphOf a D))) :
    motive G := by
  obtain ⟨e, u, v, D, w, hcyc⟩ := hG.exists_long_cycle hnl
  exact hG.ear_decomposition hnl hcyc.isTwoConnected hcyc.isCycle.cycleGraph_le
    (base e u v D w hcyc)
    fun B a b D' hB _ hBG hmot hpath hab ha hb hint ↦
      step B a b D' hB hBG hmot hpath hab ha hb hint

/-! ## An ear that is not new

`Graph.IsTwoConnected.ear_decomposition` hands its step the ear's path but **not** the clause
`∀ g ∈ D, g ∉ E(B)` that `Graph.IsTwoConnected.relative_ear_exists` proves and that
`Graph.IsTwoConnected.relative_grows_by_ear` drops. A *geometric* consumer needs it: the ear's
drawing has to miss the drawing of the current subgraph, and an edge shared with `B` would sit
right on it.

It is recoverable, and this section recovers it. An edge of the ear that `B` already has must
join the ear's two ends; the ear is then that single edge, and the enlarged graph is the old
one, so the step has nothing to prove. The integrator may prefer to add the clause to
`relative_grows_by_ear` and to `ear_decomposition` instead — that is the better fix, and it
makes this section unnecessary. -/

/-- **An edge of a path incident to its source is the path's first edge**, in the form that
decomposes the path — `Graph.IsPath.eq_head_of_inc_source` says the same about a list already
known to be a cons, and is what does the work here. -/
theorem IsPath.eq_cons_of_inc_left (h : G.IsPath u D v) (hg : g ∈ D) (hinc : G.Inc g u) :
    ∃ w T, D = g :: T ∧ G.IsLink g u w ∧ G.IsPath w T v := by
  cases D with
  | nil => simp at hg
  | cons a T =>
    obtain rfl : g = a := h.eq_head_of_inc_source hg hinc
    cases h with
    | cons hl hT _ => exact ⟨_, T, rfl, hl, hT⟩

/-- **An edge of an ear that the subgraph already has is the whole ear.** Both ends of such an
edge lie in the subgraph, so the ear's freshness clause makes them the ear's own two ends; the
edge is then the ear's first edge and its far end is the ear's target, so nothing follows it.
-/
theorem IsPath.eq_singleton_of_edge_mem (hBG : B ≤ G) (hpath : G.IsPath u D v) (huv : u ≠ v)
    (hint : ∀ y ∈ G.walkVertices u D, y ≠ u → y ≠ v → y ∉ V(B))
    (hg : g ∈ D) (hgB : g ∈ E(B)) : D = [g] ∧ G.IsLink g u v := by
  -- Both ends of the edge lie in the subgraph, so both are ends of the path.
  have hends : ∀ y, G.Inc g y → y = u ∨ y = v := by
    intro y hy
    by_contra hcon
    push Not at hcon
    exact hint y (mem_walkVertices_of_mem_covered ⟨g, hg, hy⟩) hcon.1 hcon.2
      (mem_vertexSet_of_inc_of_mem_edgeSet hBG hgB hy)
  -- The edge is not a loop, so its two ends are exactly the two ends of the path.
  obtain ⟨p, q, hpq⟩ := exists_isLink_of_mem_edgeSet (hpath.edge_mem hg)
  have hpqne : p ≠ q := by rintro rfl; exact hpath.not_isLoopAt hg p hpq
  have hincu : G.Inc g u := by
    rcases hends p hpq.inc_left with rfl | rfl
    · exact hpq.inc_left
    · rcases hends q hpq.inc_right with rfl | rfl
      · exact hpq.inc_right
      · exact absurd rfl hpqne
  -- So it is the path's first edge, and its far end is the path's target.
  obtain ⟨w, T, rfl, hl, hT⟩ := hpath.eq_cons_of_inc_left hg hincu
  have hwv : w = v := by
    rcases hends w hl.inc_right with rfl | hh
    · exact absurd hl (hpath.not_isLoopAt List.mem_cons_self _)
    · exact hh
  subst hwv
  exact ⟨by rw [hT.eq_nil_of_eq], hl⟩

/-- **Either every edge of the ear is new, or the ear changes nothing.** The disjunction the
step of `Graph.IsTwoConnected.ear_decomposition` has to open before it can do any geometry. -/
theorem ear_edges_notMem_or_union_eq (hBG : B ≤ G) (hpath : G.IsPath u D v) (huv : u ≠ v)
    (hu : u ∈ V(B)) (hv : v ∈ V(B))
    (hint : ∀ y ∈ G.walkVertices u D, y ≠ u → y ≠ v → y ∉ V(B)) :
    (∀ g ∈ D, g ∉ E(B)) ∨ B.union (G.pathGraphOf u D) = B := by
  by_cases hall : ∀ g ∈ D, g ∉ E(B)
  · exact Or.inl hall
  refine Or.inr ?_
  push Not at hall
  obtain ⟨g, hg, hgB⟩ := hall
  obtain ⟨rfl, hl⟩ := hpath.eq_singleton_of_edge_mem hBG huv hint hg hgB
  -- The ear is a single edge the subgraph already carries, joining two of its own vertices.
  refine le_antisymm (union_le le_rfl ?_) (left_le_union _ _)
  refine ⟨fun y hy ↦ ?_, fun f x y hf ↦ ?_⟩
  · rcases mem_walkVertices_iff.1 (pathGraphOf_vertexSet ▸ hy) with rfl | ⟨f, hf, hinc⟩
    · exact hu
    · obtain rfl : f = g := by simpa using hf
      rcases hinc.eq_or_eq_of_isLink hl with rfl | rfl
      exacts [hu, hv]
  · obtain ⟨hfg, hxy, -, -⟩ := pathGraphOf_isLink.1 hf
    obtain rfl : f = g := by simpa using hfg
    exact (hBG.isLink_iff hgB).2 hxy

/-! ## The faces of a graph that grows

Adding an ear removes the ear's own point set from the exterior and changes nothing else. That
is the whole of "all other faces are unchanged", and the half of "its interior is connected and
disjoint from the current graph, so it lies in one current face `F`" that is pure topology. -/

section Plane

open Schoenflies

variable {β : Type*} {G B P : Graph Plane β} {drawing : β → ℝ → Plane} {z a b : Plane}
  {S : Set Plane} {D : List β}

/-- What a union of two plane graphs occupies is what the two of them occupy. -/
@[simp]
theorem pointSet_union (B P : Graph Plane β) (drawing : β → ℝ → Plane) :
    pointSet (B.union P) drawing = pointSet B drawing ∪ pointSet P drawing := by
  simp only [pointSet, vertexSet_union, edgeSet_union, Set.biUnion_union]
  ext w
  simp only [Set.mem_union]
  tauto

/-- Adding a graph removes exactly its own point set from the exterior. -/
theorem exterior_union (B P : Graph Plane β) (drawing : β → ℝ → Plane) :
    exterior (B.union P) drawing = exterior B drawing \ pointSet P drawing := by
  rw [exterior, exterior, pointSet_union, Set.compl_union]
  rfl

/-- A face of the enlarged graph lies inside a face of the old one. -/
theorem face_union_subset : face (B.union P) drawing z ⊆ face B drawing z := by
  by_cases hz : z ∈ exterior (B.union P) drawing
  · refine IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn
      (mem_face hz) fun w hw ↦ ?_
    exact ((exterior_union B P drawing) ▸ face_subset_exterior _ _ _ hw).1
  · rw [face, connectedComponentIn_eq_empty hz]
    exact Set.empty_subset _

/-- **"All other faces are unchanged."** A face the ear does not touch survives the ear. -/
theorem face_union_eq_of_disjoint (hz : z ∈ exterior B drawing)
    (hdis : Disjoint (face B drawing z) (pointSet P drawing)) :
    face (B.union P) drawing z = face B drawing z := by
  refine Set.Subset.antisymm face_union_subset ?_
  refine IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn
    (mem_face hz) fun w hw ↦ ?_
  rw [exterior_union]
  exact ⟨face_subset_exterior _ _ _ hw, fun hwP ↦ Set.disjoint_left.1 hdis hw hwP⟩

/-- **"Its interior is connected and disjoint from the current graph, so it lies in one current
face."** The topological half: a nonempty preconnected subset of the exterior lies in one
face. -/
theorem exists_face_of_isPreconnected (hS : IsPreconnected S) (hSne : S.Nonempty)
    (hsub : S ⊆ exterior B drawing) :
    ∃ z ∈ exterior B drawing, S ⊆ face B drawing z := by
  obtain ⟨z, hz⟩ := hSne
  exact ⟨z, hsub hz, hS.subset_connectedComponentIn hz hsub⟩

/-! ### The ear lies in one face

The blueprint's *"its interior is connected and disjoint from the current graph, so it lies in
one current face `F`"*, in full. -/

/- "An arc without its two endpoints is connected" is
`Schoenflies.IsArcBetween.isConnected_diff`, now in `Schoenflies/Subarc.lean`. -/

/-- **The ear's realisation meets the drawing of the current subgraph only in the ear's two
ends.** Two cases, and both come down to the ear's freshness clause: a point of the ear on a
*vertex* of `B` is an end of the edge of the ear it lies on
(`Graph.IsDrawing.vertex_mem_edgeArc`), and a point of the ear on an *edge* of `B` is a vertex
incident with both (`Graph.IsDrawing.edge_inter`) — the two edges being distinct because no
edge of the ear belongs to `B`. Either way the point is a vertex of `B` that the ear visits,
which the freshness clause makes one of the ear's two ends. -/
theorem IsDrawing.edgesCover_inter_pointSet (hG : IsDrawing G drawing) (hBG : B ≤ G)
    (hpath : G.IsPath a D b)
    (hint : ∀ y ∈ G.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B))
    (hnew : ∀ g ∈ D, g ∉ E(B)) :
    edgesCover drawing D ∩ pointSet B drawing ⊆ {a, b} := by
  -- A vertex of `B` that an edge of the ear is incident with is one of the ear's two ends.
  have key : ∀ p, (∃ f ∈ D, G.Inc f p) → p ∈ V(B) → p = a ∨ p = b := by
    rintro p ⟨f, hf, hinc⟩ hpB
    by_contra hcon
    push Not at hcon
    exact hint p (mem_walkVertices_of_mem_covered ⟨f, hf, hinc⟩) hcon.1 hcon.2 hpB
  rintro p ⟨hpD, hpB⟩
  obtain ⟨f, hf, hpf⟩ := mem_edgesCover_iff.1 hpD
  have hfG : f ∈ E(G) := hpath.edge_mem hf
  rcases hpB with hpV | hpE
  · obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet hfG
    have hinc : G.Inc f p := by
      rcases hG.vertex_mem_edgeArc hxy (hBG.vertexSet_mono hpV) hpf with rfl | rfl
      exacts [hxy.inc_left, hxy.inc_right]
    exact key p ⟨f, hf, hinc⟩ hpV
  · simp only [Set.mem_iUnion, exists_prop] at hpE
    obtain ⟨g, hgB, hpg⟩ := hpE
    have hfg : f ≠ g := fun hh ↦ hnew f hf (hh ▸ hgB)
    obtain ⟨-, hincf, hincg⟩ := hG.edge_inter hfG (hBG.edgeSet_mono hgB) hfg hpf hpg
    exact key p ⟨f, hf, hincf⟩ (mem_vertexSet_of_inc_of_mem_edgeSet hBG hgB hincg)

/-- **"Its interior is connected and disjoint from the current graph, so it lies in one current
face `F`."** The ear's realisation without its two ends is an arc's interior, hence connected,
and it misses the drawing of `B` altogether, so it lies in a single face. -/
theorem IsDrawing.exists_face_of_ear (hG : IsDrawing G drawing) (hBG : B ≤ G)
    (hpath : G.IsPath a D b) (hab : a ≠ b)
    (hint : ∀ y ∈ G.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B))
    (hnew : ∀ g ∈ D, g ∉ E(B)) :
    ∃ z ∈ exterior B drawing, edgesCover drawing D \ {a, b} ⊆ face B drawing z := by
  have harc : IsArcBetween (edgesCover drawing D) a b :=
    hG.path_isArcBetween hpath (hpath.ne_nil hab)
  have hconn := harc.isConnected_diff
  refine exists_face_of_isPreconnected hconn.isPreconnected hconn.nonempty fun w hw hwB ↦ ?_
  exact hw.2 (hG.edgesCover_inter_pointSet hBG hpath hint hnew ⟨hw.1, hwB⟩)

/-! ### A subgraph of a plane graph is a plane graph

The induction speaks of the faces of the *current* subgraph, so every step needs the current
subgraph to be a plane graph in its own right. Nothing has to be redrawn: the same drawing
serves. General, and not in `Schoenflies/Graph/Drawing.lean`; the integrator may want to hoist
it. -/

/-- **A subgraph of a plane graph is a plane graph**, with the same drawing. -/
theorem IsDrawing.mono (hG : IsDrawing G drawing) (hBG : B ≤ G) : IsDrawing B drawing where
  edge_param := fun e he ↦ by
    obtain ⟨hc, hi, hl⟩ := hG.edge_param (hBG.edgeSet_mono he)
    exact ⟨hc, hi, (hBG.isLink_iff he).2 hl⟩
  vertex_mem_edgeArc := fun _ _ _ _ hl hv hmem ↦
    hG.vertex_mem_edgeArc (hl.mono hBG) (hBG.vertexSet_mono hv) hmem
  edge_inter := fun e f he hf hef p hpe hpf ↦ by
    obtain ⟨-, hince, hincf⟩ :=
      hG.edge_inter (hBG.edgeSet_mono he) (hBG.edgeSet_mono hf) hef hpe hpf
    obtain ⟨y, hy⟩ := hince
    obtain ⟨y', hy'⟩ := hincf
    exact ⟨mem_vertexSet_of_inc_of_mem_edgeSet hBG he ⟨y, hy⟩,
      ⟨y, (hBG.isLink_iff he).2 hy⟩, ⟨y', (hBG.isLink_iff hf).2 hy'⟩⟩

/-! ### The ear's ends lie on the boundary of the face its interior lies in -/

/- "An endpoint of an arc is a limit of the arc's interior" is
`Schoenflies.IsArcBetween.left_mem_closure_diff` / `…right_mem_closure_diff`, hoisted into
`Schoenflies/Subarc.lean` alongside `…isConnected_diff`. This module had its own copy, with the
same statement as the one in `Schoenflies/AlternatingCrosscuts.lean`; the two modules do not
import each other, so the build accepted both. -/

/-- **"The ear's two endpoints are limits of its interior, which lies in `F`, so they lie on
`∂F`."** This is the hypothesis `thm:polygonal-crosscut` needs of a crosscut: its two ends are
on the boundary curve of the region it cuts. -/
theorem IsDrawing.ends_mem_frontier_face (hG : IsDrawing G drawing)
    (hopen : IsOpen (face B drawing z)) (hpath : G.IsPath a D b) (hab : a ≠ b)
    (ha : a ∈ V(B)) (hb : b ∈ V(B))
    (hsub : edgesCover drawing D \ {a, b} ⊆ face B drawing z) :
    a ∈ frontier (face B drawing z) ∧ b ∈ frontier (face B drawing z) := by
  have harc : IsArcBetween (edgesCover drawing D) a b :=
    hG.path_isArcBetween hpath (hpath.ne_nil hab)
  have hnot : ∀ y ∈ V(B), y ∉ face B drawing z := fun y hy hyf ↦
    face_subset_exterior _ _ _ hyf (vertexSet_subset_pointSet hy)
  refine ⟨⟨closure_mono hsub harc.left_mem_closure_diff, ?_⟩,
    ⟨closure_mono hsub harc.right_mem_closure_diff, ?_⟩⟩
  · rw [hopen.interior_eq]; exact hnot a ha
  · rw [hopen.interior_eq]; exact hnot b hb

end Plane

end Graph

end BundlePart395

section BundlePart396
/- Source: dev/planar_search/schoenflies_port/Schoenflies/SegmentCut.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/


/-!
# Cutting a segment

Mathlib has no lemma splitting a segment at an interior point, and the polygonal subdivision
of Layer 6 is built entirely out of one: cutting loses nothing (`segment_split`) and cutting
is permanent (`openSegment_left_subset`, `openSegment_right_subset` — each half's interior
stays inside the whole's, so nothing later can put a removed point back into an interior).

Everything here is an identity between convex combinations. The `⊇` half of the split is
convexity; the `⊆` half rescales the parameter, and the only case analysis is on whether the
far coefficient vanishes.

## Blueprint

* `segment_split` — cutting at a point of the segment loses nothing; underneath
  `subdivide_covers`.
* `openSegment_left_subset`, `openSegment_right_subset` — a cut is permanent; underneath
  `subdivide_inside`.
-/

open Set

namespace Schoenflies

variable {a b p : Plane}

/-- Cutting a segment at one of its points loses nothing: the two halves cover it. -/
theorem segment_split (hp : p ∈ segment ℝ a b) :
    segment ℝ a b = segment ℝ a p ∪ segment ℝ p b := by
  refine subset_antisymm ?_ (union_subset
    ((convex_segment a b).segment_subset (left_mem_segment ℝ a b) hp)
    ((convex_segment a b).segment_subset hp (right_mem_segment ℝ a b)))
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hp
  rintro x ⟨u, v, hu, hv, huv, rfl⟩
  rcases le_or_gt v β with hvβ | hvβ
  · -- `x` lies on the near half. Rescale `v` by `β`, unless `β = 0`, when the cut is at `a`.
    left
    rcases eq_or_lt_of_le hβ with rfl | hβpos
    · have hv0 : v = 0 := le_antisymm hvβ hv
      have hu1 : u = 1 := by linarith
      subst hv0; subst hu1
      simp only [zero_smul, add_zero, one_smul]
      exact left_mem_segment ℝ a _
    · refine ⟨1 - v / β, v / β, by
        rw [sub_nonneg]
        exact div_le_one_of_le₀ hvβ hβpos.le, by positivity, by ring, ?_⟩
      have hβne : β ≠ 0 := ne_of_gt hβpos
      have hvβ' : v / β * β = v := div_mul_cancel₀ v hβne
      have hcoef : (1 - v / β) + (v / β) * α = u := by
        have hα' : α = 1 - β := by linarith
        calc (1 - v / β) + (v / β) * α
            = (1 - v / β) + (v / β) * (1 - β) := by rw [hα']
          _ = 1 - v / β * β := by ring
          _ = 1 - v := by rw [hvβ']
          _ = u := by linarith
      rw [smul_add, smul_smul, smul_smul, ← add_assoc, ← add_smul, hcoef, hvβ']
  · -- `x` lies on the far half. Rescale `u` by `α`, which is positive because `v > β`.
    right
    have hαpos : 0 < α := by linarith
    have hαne : α ≠ 0 := ne_of_gt hαpos
    have huα : u ≤ α := by linarith
    refine ⟨u / α, 1 - u / α, by positivity, by
      rw [sub_nonneg]
      exact div_le_one_of_le₀ huα hαpos.le, by ring, ?_⟩
    have huα' : u / α * α = u := div_mul_cancel₀ u hαne
    have hcoef : (u / α) * β + (1 - u / α) = v := by
      have hβ' : β = 1 - α := by linarith
      calc (u / α) * β + (1 - u / α)
          = (u / α) * (1 - α) + (1 - u / α) := by rw [hβ']
        _ = 1 - u / α * α := by ring
        _ = 1 - u := by rw [huα']
        _ = v := by linarith
    rw [smul_add, smul_smul, smul_smul, add_assoc, ← add_smul, hcoef, huα']

/-- Cutting is permanent, near half: the interior of the near piece stays inside the
interior of the whole. -/
theorem openSegment_left_subset (hp : p ∈ openSegment ℝ a b) :
    openSegment ℝ a p ⊆ openSegment ℝ a b := by
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hp
  rintro x ⟨s, t, hs, ht, hst, rfl⟩
  refine ⟨s + t * α, t * β, by positivity, by positivity, by nlinarith, ?_⟩
  rw [smul_add, smul_smul, smul_smul, ← add_assoc, ← add_smul]

/-- Cutting is permanent, far half. -/
theorem openSegment_right_subset (hp : p ∈ openSegment ℝ a b) :
    openSegment ℝ p b ⊆ openSegment ℝ a b := by
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hp
  rintro x ⟨s, t, hs, ht, hst, rfl⟩
  refine ⟨s * α, s * β + t, by positivity, by positivity, by nlinarith, ?_⟩
  rw [smul_add, smul_smul, smul_smul, add_assoc, ← add_smul]

end Schoenflies

end BundlePart396

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

