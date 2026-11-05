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

public import verified.parts.part040
import all verified.parts.part040

@[expose] public section

set_option debug.skipKernelTC false
set_option linter.all false
set_option Elab.async false
set_option internal.cmdlineSnapshots true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

section BundlePart426
/- Source: Papers/GraphicalZonotopes/ArcK5Geometry.lean -/




open Set Schoenflies GraphicalZonotopes.PlanarGeometry

namespace Graph
namespace IsArcK5

variable {x : Fin 5 → Plane} {P : Fin 5 → Fin 5 → Set Plane}
variable (h : IsArcK5 x P)
include h

theorem inter_indices {i j k l : Fin 5} (hij : i ≠ j) (hkl : k ≠ l)
    (hne : (i, j) ≠ (k, l)) (hrev : (i, j) ≠ (l, k))
    {z : Plane} (hz : z ∈ P i j) (hz' : z ∈ P k l) :
    ∃ t : Fin 5, z = x t ∧ (t = i ∨ t = j) ∧ (t = k ∨ t = l) := by
  have hm := (h.meet i j k l hij hkl hne hrev ⟨hz, hz'⟩).1
  rcases hm with rfl | rfl
  · exact ⟨i, rfl, Or.inl rfl, h.vertex k l i hkl hz'⟩
  · exact ⟨j, rfl, Or.inr rfl, h.vertex k l j hkl hz'⟩

theorem disjoint_edges {i j k l : Fin 5} (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    Disjoint (P i j) (P k l) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  obtain ⟨t, _, ht, ht'⟩ := h.inter_indices hij hkl
    (fun e => hik (congrArg Prod.fst e))
    (fun e => hil (congrArg Prod.fst e)) hz hz'
  rcases ht with rfl | rfl <;> rcases ht' with h' | h'
  exacts [hik h', hil h', hjk h', hjl h']

omit h in
def two (P : Fin 5 → Fin 5 → Set Plane) (i j k : Fin 5) : Set Plane :=
  P i j ∪ P j k

theorem two_arc {i j k : Fin 5} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    IsArcBetween (two P i j k) (x i) (x k) := by
  apply (h.arc i j hij).concatenate (h.arc j k hjk)
  intro z hz hz'
  obtain ⟨t, rfl, ht, ht'⟩ := h.inter_indices hij hjk
    (fun e => hij (congrArg Prod.fst e))
    (fun e => hik (congrArg Prod.fst e)) hz hz'
  rcases ht with rfl | rfl
  · rcases ht' with h' | h'
    · exact (hij h').elim
    · exact (hik h').elim
  · rfl

theorem two_poly (hpoly : ∀ i j, i ≠ j → IsPolygonal (P i j))
    {i j k : Fin 5} (hij : i ≠ j) (hjk : j ≠ k) :
    IsPolygonal (two P i j k) :=
  (hpoly i j hij).union (hpoly j k hjk)
    ⟨x j, (h.arc i j hij).right_mem, (h.arc j k hjk).left_mem⟩

theorem vertex_two {i j k t : Fin 5} (hij : i ≠ j) (hjk : j ≠ k)
    (ht : x t ∈ two P i j k) : t = i ∨ t = j ∨ t = k := by
  rcases ht with ht | ht
  · rcases h.vertex i j t hij ht with he | he
    · exact Or.inl he
    · exact Or.inr (Or.inl he)
  · exact Or.inr (h.vertex j k t hjk ht)

omit h in
/-- The four-cycle through the first four branch vertices. -/
def fourCycle (P : Fin 5 → Fin 5 → Set Plane) : Set Plane :=
  two P 0 1 2 ∪ two P 0 3 2

theorem fourCycle_arcs_inter :
    two P 0 1 2 ∩ two P 0 3 2 = ({x 0, x 2} : Set Plane) := by
  apply Set.Subset.antisymm
  · rintro z ⟨hz, hz'⟩
    rcases hz with hz | hz <;> rcases hz' with hz' | hz'
    all_goals
      obtain ⟨t, rfl, ht, ht'⟩ := h.inter_indices
        (by decide) (by decide) (by decide) (by decide) hz hz'
      fin_cases t <;> simp_all
  · rintro z (rfl | rfl)
    · exact ⟨(h.two_arc (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide)).left_mem,
        (h.two_arc (i := 0) (j := 3) (k := 2) (by decide) (by decide) (by decide)).left_mem⟩
    · exact ⟨(h.two_arc (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide)).right_mem,
        (h.two_arc (i := 0) (j := 3) (k := 2) (by decide) (by decide) (by decide)).right_mem⟩

theorem fourCycle_sep (hpoly : ∀ i j, i ≠ j → IsPolygonal (P i j)) :
    IsSeparating (fourCycle P) := by
  apply Schoenflies.isSeparating_of_isJordanCurve
  · apply Schoenflies.isJordanCurve_union
      (h.two_arc (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide))
      (h.two_arc (i := 0) (j := 3) (k := 2) (by decide) (by decide) (by decide))
    intro z hz hz'
    have hm := h.fourCycle_arcs_inter ▸ (show z ∈ two P 0 1 2 ∩ two P 0 3 2 from ⟨hz, hz'⟩)
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hm
  · exact (h.two_poly hpoly (i := 0) (j := 1) (k := 2) (by decide) (by decide)).union
      (h.two_poly hpoly (i := 0) (j := 3) (k := 2) (by decide) (by decide))
      ⟨x 0,
        (h.two_arc (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide)).left_mem,
        (h.two_arc (i := 0) (j := 3) (k := 2) (by decide) (by decide) (by decide)).left_mem⟩

theorem fifth_not_fourCycle : x 4 ∉ fourCycle P := by
  rintro (hm | hm)
  · have := h.vertex_two (by decide : (0 : Fin 5) ≠ 1) (by decide : (1 : Fin 5) ≠ 2) hm
    simp at this
  · have := h.vertex_two (by decide : (0 : Fin 5) ≠ 3) (by decide : (3 : Fin 5) ≠ 2) hm
    simp at this

omit h in
abbrev cycleSide (i j : Fin 5) : Prop :=
  (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 2)

theorem inter_fourCycle_pair {i j : Fin 5} (hij : i ≠ j)
    (hne : ∀ a b, cycleSide a b → (i, j) ≠ (a, b) ∧ (i, j) ≠ (b, a)) :
    P i j ∩ fourCycle P ⊆ ({x i, x j} : Set Plane) := by
  rintro z ⟨hz, hzC⟩
  rcases hzC with (hzC | hzC) | (hzC | hzC)
  · exact (h.meet i j 0 1 hij (by decide) (hne 0 1 (by decide)).1
      (hne 0 1 (by decide)).2 ⟨hz, hzC⟩).1
  · exact (h.meet i j 1 2 hij (by decide) (hne 1 2 (by decide)).1
      (hne 1 2 (by decide)).2 ⟨hz, hzC⟩).1
  · exact (h.meet i j 0 3 hij (by decide) (hne 0 3 (by decide)).1
      (hne 0 3 (by decide)).2 ⟨hz, hzC⟩).1
  · exact (h.meet i j 3 2 hij (by decide) (hne 3 2 (by decide)).1
      (hne 3 2 (by decide)).2 ⟨hz, hzC⟩).1

theorem diagonal_inter_fourCycle :
    P 0 2 ∩ fourCycle P = ({x 0, x 2} : Set Plane) := by
  apply Set.Subset.antisymm (h.inter_fourCycle_pair (by decide) (by decide))
  rintro z (rfl | rfl)
  · exact ⟨(h.arc 0 2 (by decide)).left_mem,
      Or.inl (h.two_arc (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide)).left_mem⟩
  · exact ⟨(h.arc 0 2 (by decide)).right_mem,
      Or.inl (h.two_arc (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide)).right_mem⟩

theorem fourCycle_poly (hpoly : ∀ i j, i ≠ j → IsPolygonal (P i j)) :
    IsPolygonal (fourCycle P) :=
  (h.two_poly hpoly (i := 0) (j := 1) (k := 2) (by decide) (by decide)).union
    (h.two_poly hpoly (i := 0) (j := 3) (k := 2) (by decide) (by decide))
    ⟨x 0,
      (h.two_arc (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide)).left_mem,
      (h.two_arc (i := 0) (j := 3) (k := 2) (by decide) (by decide) (by decide)).left_mem⟩

theorem diagonal_intersects (hpoly : ∀ i j, i ≠ j → IsPolygonal (P i j))
    {Q Ω : Set Plane} (hΩ : IsRegionOf (fourCycle P) Ω)
    (hPΩ : P 0 2 \ {x 0, x 2} ⊆ Ω)
    (hQ : IsArcBetween Q (x 1) (x 3)) (hQΩ : Q \ {x 1, x 3} ⊆ Ω) :
    (Q ∩ P 0 2).Nonempty := by
  apply alternating_arc_inter_nonempty (h.fourCycle_sep hpoly) (h.fourCycle_poly hpoly)
    (h.two_arc (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide))
    (h.two_arc (i := 0) (j := 3) (k := 2) (by decide) (by decide) (by decide))
    (h.two_poly hpoly (i := 0) (j := 1) (k := 2) (by decide) (by decide))
    (h.two_poly hpoly (i := 0) (j := 3) (k := 2) (by decide) (by decide))
    rfl h.fourCycle_arcs_inter (h.arc 0 2 (by decide)) (hpoly 0 2 (by decide))
    h.diagonal_inter_fourCycle hΩ hPΩ hQ hQΩ
  · refine ⟨Or.inl (h.arc 0 1 (by decide)).right_mem, ?_⟩
    rintro (he | he) <;> have := h.injective he <;> norm_num at this
  · refine ⟨Or.inl (h.arc 0 3 (by decide)).right_mem, ?_⟩
    rintro (he | he) <;> have := h.injective he <;> norm_num at this

theorem fifth_path_diff_subset_compl :
    two P 1 4 3 \ {x 1, x 3} ⊆ (fourCycle P)ᶜ := by
  rintro z ⟨hz, hzends⟩ hzC
  rcases hz with hz | hz
  · have hm := h.inter_fourCycle_pair (i := 1) (j := 4) (by decide) (by decide) ⟨hz, hzC⟩
    rcases hm with rfl | rfl
    · exact hzends (Or.inl rfl)
    · exact h.fifth_not_fourCycle hzC
  · have hm := h.inter_fourCycle_pair (i := 4) (j := 3) (by decide) (by decide) ⟨hz, hzC⟩
    rcases hm with rfl | rfl
    · exact h.fifth_not_fourCycle hzC
    · exact hzends (Or.inr rfl)

theorem fifth_mem_path_diff : x 4 ∈ two P 1 4 3 \ {x 1, x 3} := by
  refine ⟨Or.inl (h.arc 1 4 (by decide)).right_mem, ?_⟩
  rintro (he | he) <;> have := h.injective he <;> norm_num at this

/-- A region containing the first diagonal cannot also contain the fifth vertex:
the two incident edges through that vertex give an alternating crosscut. -/
theorem diagonal_fifth_false (hpoly : ∀ i j, i ≠ j → IsPolygonal (P i j))
    {Ω : Set Plane} (hΩ : IsRegionOf (fourCycle P) Ω)
    (hPΩ : P 0 2 \ {x 0, x 2} ⊆ Ω) (hx4 : x 4 ∈ Ω) : False := by
  have hR := h.two_arc (i := 1) (j := 4) (k := 3) (by decide) (by decide) (by decide)
  have hRΩ : two P 1 4 3 \ {x 1, x 3} ⊆ Ω := by
    have hh := hR.isPreconnected_diff.subset_connectedComponentIn
      h.fifth_mem_path_diff h.fifth_path_diff_subset_compl
    rwa [hΩ.connectedComponentIn_eq (h.fourCycle_sep hpoly) hx4] at hh
  obtain ⟨z, hzR, hzP⟩ := h.diagonal_intersects hpoly hΩ hPΩ hR hRΩ
  rcases hzR with hzR | hzR
  · exact Set.disjoint_left.1 (h.disjoint_edges
      (i := 0) (j := 2) (k := 1) (l := 4)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hzP hzR
  · exact Set.disjoint_left.1 (h.disjoint_edges
      (i := 0) (j := 2) (k := 4) (l := 3)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hzP hzR

theorem relabel (e : Fin 5 ≃ Fin 5) :
    IsArcK5 (fun i => x (e i)) (fun i j => P (e i) (e j)) where
  injective := h.injective.comp e.injective
  arc i j hij := h.arc (e i) (e j) (fun h' => hij (e.injective h'))
  symm i j := h.symm (e i) (e j)
  vertex i j k hij hmem := by
    rcases h.vertex (e i) (e j) (e k) (fun h' => hij (e.injective h')) hmem with he | he
    · exact Or.inl (e.injective he)
    · exact Or.inr (e.injective he)
  meet i j k l hij hkl hne hrev := by
    apply h.meet (e i) (e j) (e k) (e l)
      (fun h' => hij (e.injective h')) (fun h' => hkl (e.injective h'))
    · intro he
      exact hne (Prod.ext (e.injective (congrArg Prod.fst he))
        (e.injective (congrArg Prod.snd he)))
    · intro he
      exact hrev (Prod.ext (e.injective (congrArg Prod.fst he))
        (e.injective (congrArg Prod.snd he)))

omit h in
def alternateOrder : Fin 5 ≃ Fin 5 := (Equiv.swap 0 1).trans (Equiv.swap 2 3)

theorem fourCycle_alternate :
    fourCycle (fun i j => P (alternateOrder i) (alternateOrder j)) = fourCycle P := by
  change (P 1 0 ∪ P 0 3) ∪ (P 1 2 ∪ P 2 3) = (P 0 1 ∪ P 1 2) ∪ (P 0 3 ∪ P 3 2)
  rw [h.symm 1 0, h.symm 2 3]
  ext z
  simp only [Set.mem_union]
  tauto

omit h in
private theorem arc_diff_nonempty {A : Set Plane} {a b : Plane}
    (hA : IsArcBetween A a b) : (A \ {a, b}).Nonempty := by
  by_contra hn
  rw [Set.not_nonempty_iff_eq_empty] at hn
  have hh := hA.left_mem_closure_diff
  simpa [hn] using hh

/-- Five pairwise connected branch points cannot be drawn by polygonal arcs
meeting only at their common endpoints. -/
theorem false_of_polygonal (hpoly : ∀ i j, i ≠ j → IsPolygonal (P i j)) : False := by
  classical
  have hC := h.fourCycle_sep hpoly
  have hP := h.arc 0 2 (by decide)
  have hQ := h.arc 1 3 (by decide)
  have hPcomp : P 0 2 \ {x 0, x 2} ⊆ (fourCycle P)ᶜ := by
    rintro z ⟨hz, hzends⟩ hzC
    exact hzends (h.inter_fourCycle_pair (by decide) (by decide) ⟨hz, hzC⟩)
  have hQcomp : P 1 3 \ {x 1, x 3} ⊆ (fourCycle P)ᶜ := by
    rintro z ⟨hz, hzends⟩ hzC
    exact hzends (h.inter_fourCycle_pair (by decide) (by decide) ⟨hz, hzC⟩)
  obtain ⟨Ω, Ω', hpair, hPΩ⟩ := hC.exists_isRegionPair_subset
    hP.isPreconnected_diff (arc_diff_nonempty hP) (Set.disjoint_left.2 hPcomp)
  have hcover : P 1 3 \ {x 1, x 3} ⊆ Ω ∪ Ω' := by
    rw [hpair.union_eq]
    exact hQcomp
  have hQΩ' : P 1 3 \ {x 1, x 3} ⊆ Ω' := by
    intro z hz
    rcases hcover hz with hzΩ | hzΩ'
    · have hQΩ := hQ.isPreconnected_diff.subset_left_of_subset_union
        (hpair.left.isOpen hC) (hpair.right.isOpen hC) hpair.disjoint hcover ⟨z, hz, hzΩ⟩
      obtain ⟨w, hwQ, hwP⟩ := h.diagonal_intersects hpoly hpair.left hPΩ hQ hQΩ
      exact (Set.disjoint_left.1 (h.disjoint_edges
        (i := 0) (j := 2) (k := 1) (l := 3)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hwP hwQ).elim
    · exact hzΩ'
  have hx4 : x 4 ∈ Ω ∪ Ω' := by
    rw [hpair.union_eq]
    exact h.fifth_not_fourCycle
  rcases hx4 with hx4 | hx4
  · exact h.diagonal_fifth_false hpoly hpair.left hPΩ hx4
  · have h' := h.relabel alternateOrder
    have hp' : ∀ i j, i ≠ j → IsPolygonal (P (alternateOrder i) (alternateOrder j)) :=
      fun i j hij => hpoly _ _ (fun he => hij (alternateOrder.injective he))
    apply h'.diagonal_fifth_false hp' (Ω := Ω')
    · rw [h.fourCycle_alternate]
      exact hpair.right
    · change P 1 3 \ {x 1, x 3} ⊆ Ω'
      exact hQΩ'
    · change x 4 ∈ Ω'
      exact hx4

/-- No topological K5 arc configuration exists.  This includes subdivisions:
each branch path is simply the arc joining its two branch vertices. -/
theorem elim : False := by
  obtain ⟨P', hP', hpoly⟩ := h.exists_polygonal
  exact hP'.false_of_polygonal hpoly

end IsArcK5
end Graph

end BundlePart426

section BundlePart427
/- Source: Papers/GraphicalZonotopes/ThreeTreeTriangleApex.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every component left after deleting a triangle of a 3-tree contains
an apex of a tetrahedron on that triangle. The path is an actual graph path
in the complement of the triangle, rather than a clique-incidence path. -/
theorem ThreeTreeOn.triangle_apex_reachable {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (T : Finset V) (hT : T.card = 3) (hcT : G.IsClique T)
    (x : V) (hxS : x ∈ S) (hxT : x ∉ T) :
    ∃ w, w ∈ S ∧ ∃ hwT : w ∉ T,
      (∀ t ∈ T, G.Adj w t) ∧
      (G.induce ((T : Set V)ᶜ)).Reachable ⟨x,hxT⟩ ⟨w,hwT⟩ := by
  induction h generalizing T x with
  | tetrahedron C hC =>
    have hTC := (ThreeTreeOn.tetrahedron C hC).clique_subset_active (by omega) hcT
    refine ⟨x,hxS,hxT,?_,SimpleGraph.Reachable.rfl⟩
    intro t ht
    exact ⟨fun he => hxT (he ▸ ht),hxS,hTC ht⟩
  | @attach S G h u hu A hA hAS hcA ih =>
    by_cases huT : u ∈ T
    · have hTA : T.erase u ⊆ A := by
        intro t ht
        exact (attached_vertex_adj_iff h hu hAS t).mp
          (hcT huT (mem_of_mem_erase ht) (Ne.symm (ne_of_mem_erase ht)))
      have hnot : ¬ A ⊆ T := by
        intro hAT
        have he : A = T := eq_of_subset_of_card_le hAT (by omega)
        exact hu (hAS (he.symm ▸ huT))
      obtain ⟨w,hwA,hwT⟩ := not_subset.mp hnot
      have hxold : x ∈ S := (mem_insert.mp hxS).resolve_left
        (fun he => hxT (he ▸ huT))
      have hxE : x ∉ T.erase u := fun hx => hxT (mem_of_mem_erase hx)
      have hwE : w ∉ T.erase u := fun hw => hwT (mem_of_mem_erase hw)
      let f : activeDelete G S (T.erase u) →g
          (G ⊔ attachmentStar u A).induce ((T : Set V)ᶜ) :=
        { toFun := fun v => ⟨v.1,by
            intro hvT
            exact v.2.2 (mem_erase.mpr
              ⟨fun he => hu (he ▸ v.2.1),hvT⟩)⟩
          map_rel' := fun hab => Or.inl hab }
      have hconn := h.delete_at_most_two_connected (T.erase u)
        (by rw [card_erase_of_mem huT,hT])
      have hp := (hconn.preconnected ⟨x,hxold,hxE⟩ ⟨w,hAS hwA,hwE⟩).map f
      refine ⟨w,mem_insert_of_mem (hAS hwA),hwT,?_,hp⟩
      intro t ht
      by_cases htu : t = u
      · subst t
        exact (G ⊔ attachmentStar u A).adj_symm
          ((attached_vertex_adj_iff h hu hAS w).mpr hwA)
      · exact Or.inl (hcA hwA (hTA (mem_erase.mpr ⟨htu,ht⟩))
          (fun he => hwT (he ▸ ht)))
    · have hcOld : G.IsClique T := clique_before_attachment huT hcT
      have hmono : G.induce ((T : Set V)ᶜ) ≤
          (G ⊔ attachmentStar u A).induce ((T : Set V)ᶜ) :=
        fun _ _ hvw => Or.inl hvw
      by_cases hxu : x = u
      · subst x
        by_cases hAT : A = T
        · refine ⟨u,mem_insert_self _ _,huT,?_,SimpleGraph.Reachable.rfl⟩
          intro t ht
          exact (attached_vertex_adj_iff h hu hAS t).mpr (hAT.symm ▸ ht)
        · have hnot : ¬ A ⊆ T := fun hh => hAT (eq_of_subset_of_card_le hh (by omega))
          obtain ⟨a,haA,haT⟩ := not_subset.mp hnot
          obtain ⟨w,hwS,hwT,hwAdj,hwPath⟩ := ih T hT hcOld a (hAS haA) haT
          refine ⟨w,mem_insert_of_mem hwS,hwT,fun t ht => Or.inl (hwAdj t ht),?_⟩
          have hua : ((G ⊔ attachmentStar u A).induce ((T : Set V)ᶜ)).Adj
              ⟨u,huT⟩ ⟨a,haT⟩ := (attached_vertex_adj_iff h hu hAS a).mpr haA
          exact hua.reachable.trans (hwPath.mono hmono)
      · have hxold : x ∈ S := (mem_insert.mp hxS).resolve_left hxu
        obtain ⟨w,hwS,hwT,hwAdj,hwPath⟩ := ih T hT hcOld x hxold hxT
        exact ⟨w,mem_insert_of_mem hwS,hwT,fun t ht => Or.inl (hwAdj t ht),
          hwPath.mono hmono⟩

/-- A graph-theoretic obstruction forced by a plane drawing: two different
apices over one triangle cannot be joined while avoiding that triangle.
The forbidden configuration consists of a triangle, its six apex spokes,
and an apex-to-apex path, hence is a subdivision of K₅. -/
def TriangleApexSeparated (G : SimpleGraph V) : Prop :=
  ∀ (T : Finset V), T.card = 3 → G.IsClique T →
    ∀ (u w : V) (hu : u ∉ T) (hw : w ∉ T), u ≠ w →
      (∀ t ∈ T, G.Adj u t) → (∀ t ∈ T, G.Adj w t) →
      ¬ (G.induce ((T : Set V)ᶜ)).Reachable ⟨u,hu⟩ ⟨w,hw⟩

theorem TriangleApexSeparated.mono {G H : SimpleGraph V}
    (hH : TriangleApexSeparated H) (hGH : G ≤ H) : TriangleApexSeparated G := by
  intro T hT hcT u w hu hw huw huT hwT hp
  exact hH T hT (fun a ha b hb hab => hGH (hcT ha hb hab)) u w hu hw huw
    (fun t ht => hGH (huT t ht)) (fun t ht => hGH (hwT t ht))
    (hp.mono (fun _ _ hadj => hGH hadj))

theorem TriangleApexSeparated.cliqueFree_five {G : SimpleGraph V}
    (hG : TriangleApexSeparated G) : G.CliqueFree 5 := by
  intro C hC
  obtain ⟨T,hTC,hT⟩ := exists_subset_card_eq (show 3 ≤ C.card by rw [hC.card_eq]; omega)
  have hd : (C \ T).card = 2 := by
    rw [card_sdiff_of_subset hTC,hC.card_eq,hT]
  obtain ⟨u,w,huw,hew⟩ := card_eq_two.mp hd
  have hu : u ∈ C ∧ u ∉ T := mem_sdiff.mp (by rw [hew]; simp)
  have hw : w ∈ C ∧ w ∉ T := mem_sdiff.mp (by rw [hew]; simp)
  apply hG T hT (fun a ha b hb hab => hC.isClique (hTC ha) (hTC hb) hab)
    u w hu.2 hw.2 huw
    (fun t ht => hC.isClique hu.1 (hTC ht) (fun he => hu.2 (he ▸ ht)))
    (fun t ht => hC.isClique hw.1 (hTC ht) (fun he => hw.2 (he ▸ ht)))
  exact SimpleGraph.Adj.reachable (hC.isClique hu.1 hw.1 huw)

/-- Under the actual triangle-apex obstruction, tetrahedral growth never
introduces an extra edge. This is the planar support argument without an
Euler formula or any assumed edge-density inequality. -/
theorem TetrahedralGrowth.induced_threeTree {G : SimpleGraph V} {S : Finset V}
    (h : TetrahedralGrowth G S) (hG : TriangleApexSeparated G) :
    ThreeTreeOn S (inducedOn G S) := by
  induction h with
  | base C hc hcl =>
    rw [inducedOn_clique hcl]
    exact ThreeTreeOn.tetrahedron C hc
  | @attach S h u hu T hT hTS hcT hadj ih =>
    have hcOld : (inducedOn G S).IsClique T :=
      fun a ha b hb hab => ⟨hcT ha hb hab,hTS ha,hTS hb⟩
    have hNT : earlierNeighbors G S u = T := by
      apply subset_antisymm
      · intro x hx
        obtain ⟨hxS,hux⟩ := (mem_earlierNeighbors G S u x).mp hx
        by_contra hxT
        obtain ⟨w,hwS,hwT,hwAdj,hwPath⟩ :=
          ih.triangle_apex_reachable T hT hcOld x hxS hxT
        have huT : u ∉ T := fun ht => hu (hTS ht)
        have huw : u ≠ w := fun he => hu (he ▸ hwS)
        apply hG T hT hcT u w huT hwT huw hadj
          (fun t ht => (hwAdj t ht).1)
        have hux' : (G.induce ((T : Set V)ᶜ)).Adj ⟨u,huT⟩ ⟨x,hxT⟩ := hux
        have hmono : (inducedOn G S).induce ((T : Set V)ᶜ) ≤
            G.induce ((T : Set V)ᶜ) := fun _ _ he => he.1
        exact hux'.reachable.trans (hwPath.mono hmono)
      · intro x hx
        exact (mem_earlierNeighbors G S u x).mpr ⟨hTS hx,hadj x hx⟩
    rw [inducedOn_insert_eq_attach G S T u hu hNT]
    exact ThreeTreeOn.attach ih u hu T hT hTS hcOld

theorem TriangleApexSeparated.connected_family_threeTree {G : SimpleGraph V}
    (hG : TriangleApexSeparated G) (F : Finset (Finset V)) (hne : F.Nonempty)
    (hcl : ∀ C ∈ F, C.card = 4 ∧ G.IsClique C)
    (hconn : (tetrahedronGraph F).Preconnected) :
    ThreeTreeOn (F.biUnion id) (inducedOn G (F.biUnion id)) :=
  (tetrahedralGrowth_of_connected_family G F hne hcl hconn).induced_threeTree hG

end GraphicalZonotopes

end
end
end BundlePart427

section BundlePart428
/- Source: Papers/GraphicalZonotopes/PlanarApexSeparation.lean -/






@[expose] public section
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- In a genuinely drawn planar graph, two distinct apices on one triangle
lie in different components after deleting that triangle. The proof constructs
a K₅ configuration from any alleged avoiding path and uses the complete
Jordan-separation obstruction for arbitrary continuous arcs. -/
theorem HasPlaneDrawing.triangle_apex_separated {G : SimpleGraph V}
    (hG : HasPlaneDrawing G) : TriangleApexSeparated G := by
  intro T hT hcT u w hu hw huw huAdj hwAdj hreach
  obtain ⟨x,P,hK5⟩ := hG.arcK5_of_triangle_apex_path
    T hT hcT u w hu hw huw huAdj hwAdj hreach
  exact hK5.elim

end GraphicalZonotopes

end
end
end BundlePart428

section BundlePart429
/- Source: Papers/GraphicalZonotopes/TriangleApexCount.lean -/





@[expose] public section
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The common neighbors of a triangle, with its own vertices excluded. -/
def commonApices (G : SimpleGraph V) (T : Finset V) : Finset V :=
  univ.filter (fun v => v ∉ T ∧ ∀ t ∈ T, G.Adj v t)

@[simp] theorem mem_commonApices (G : SimpleGraph V) (T : Finset V) (v : V) :
    v ∈ commonApices G T ↔ v ∉ T ∧ ∀ t ∈ T, G.Adj v t := by
  simp [commonApices]

theorem tetrahedra_over_triangle_eq_image {G : SimpleGraph V} {T : Finset V}
    (hT : T.card = 3) (hcT : G.IsClique T) :
    (tetrahedra G).filter (fun C => T ⊆ C) =
      (commonApices G T).image (fun u => insert u T) := by
  ext C
  constructor
  · intro hC
    obtain ⟨hC,hTC⟩ := mem_filter.mp hC
    obtain ⟨hcC,hclC⟩ := (mem_filter.mp hC).2
    have hd : (C \ T).card = 1 := by
      rw [card_sdiff_of_subset hTC,hcC,hT]
    obtain ⟨u,hu⟩ := card_eq_one.mp hd
    have huCT : u ∈ C ∧ u ∉ T := mem_sdiff.mp (by rw [hu]; simp)
    refine mem_image.mpr ⟨u,(mem_commonApices G T u).mpr ⟨huCT.2,?_⟩,?_⟩
    · intro t ht
      exact hclC huCT.1 (hTC ht) (fun he => huCT.2 (he ▸ ht))
    · ext v
      constructor
      · intro hv
        rcases mem_insert.mp hv with rfl | hv
        · exact huCT.1
        · exact hTC hv
      · intro hv
        by_cases hvT : v ∈ T
        · exact mem_insert_of_mem hvT
        · have hvm : v ∈ C \ T := mem_sdiff.mpr ⟨hv,hvT⟩
          rw [hu] at hvm
          exact mem_insert.mpr (Or.inl (mem_singleton.mp hvm))
  · intro hC
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hC
    obtain ⟨huT,huAdj⟩ := (mem_commonApices G T u).mp hu
    apply mem_filter.mpr
    refine ⟨mem_filter.mpr ⟨mem_univ _,?_,?_⟩,subset_insert _ _⟩
    · rw [card_insert_of_notMem huT,hT]
    · intro a ha b hb hab
      rcases mem_insert.mp ha with hau | haT
      · subst a
        exact huAdj b ((mem_insert.mp hb).resolve_left (Ne.symm hab))
      · rcases mem_insert.mp hb with hbu | hbT
        · subst b
          exact G.adj_symm (huAdj a haT)
        · exact hcT haT hbT hab

/-- The paper's tetrahedron multiplicity is literally the number of common
neighbors of its triangle. No maximal-clique or planarity convention enters
this elementary finite-set dictionary. -/
theorem triangleMultiplicity_eq_commonApices_card {G : SimpleGraph V} {T : Finset V}
    (hT : T.card = 3) (hcT : G.IsClique T) :
    triangleMultiplicity G T = (commonApices G T).card := by
  rw [triangleMultiplicity,tetrahedra_over_triangle_eq_image hT hcT]
  apply card_image_of_injOn
  intro u hu v hv he
  change insert u T = insert v T at he
  have huT := ((mem_commonApices G T u).mp hu).1
  have hum : u ∈ insert v T := by rw [← he]; exact mem_insert_self _ _
  exact (mem_insert.mp hum).resolve_right huT

end GraphicalZonotopes

end
end
end BundlePart429

section BundlePart430
/- Source: Papers/GraphicalZonotopes/PlanarK33.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical Graph
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A genuine plane drawing excludes a K₃,₃ subgraph. The imported obstruction
is the closed theorem for arbitrary continuous injective edge arcs. -/
theorem HasPlaneDrawing.no_complete_bipartite_three_three {G : SimpleGraph V}
    (hG : HasPlaneDrawing G) (x y : Fin 3 → V)
    (hx : Function.Injective x) (hy : Function.Injective y)
    (hxy : ∀ i j,x i ≠ y j) (hadj : ∀ i j,G.Adj (x i) (y j)) : False := by
  obtain ⟨p,hp,drawing,hd⟩ := hG
  let e : Fin 3 → Fin 3 → Sym2 V := fun i j => s(x i,y j)
  have hk : Graph.IsK33Config (PlaneDrawing.planeGraph G p) (p ∘ x) (p ∘ y) e := by
    constructor
    · intro i j
      exact (PlaneDrawing.planeGraph_isLink G p hp _ _ _).mpr ⟨rfl,hadj i j⟩
    · exact hp.comp hx
    · exact hp.comp hy
    · intro i j heq
      exact hxy i j (hp heq)
  exact hk.not_exists_isDrawing ⟨drawing,hd⟩

/-- Any three distinct vertices in a planar graph have at most two common
neighbours outside the triple. The three vertices need not themselves form
a triangle; the stronger statement is exactly the K₃,₃ obstruction. -/
theorem HasPlaneDrawing.common_apices_bound {G : SimpleGraph V}
    (hG : HasPlaneDrawing G) (T : Finset V) (hT : T.card = 3) :
    (univ.filter (fun v : V => v ∉ T ∧ ∀ t ∈ T,G.Adj v t)).card ≤ 2 := by
  classical
  by_contra hnot
  have hthree : 2 < (univ.filter
      (fun v : V => v ∉ T ∧ ∀ t ∈ T,G.Adj v t)).card := by omega
  obtain ⟨u,v,w,hu,hv,hw,huv,huw,hvw⟩ := two_lt_card_iff.mp hthree
  have hu' := (mem_filter.mp hu).2
  have hv' := (mem_filter.mp hv).2
  have hw' := (mem_filter.mp hw).2
  obtain ⟨a,b,c,hab,hac,hbc,hTabc⟩ := card_eq_three.mp hT
  let x : Fin 3 → V := ![a,b,c]
  let y : Fin 3 → V := ![u,v,w]
  have hx : Function.Injective x := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [x]
  have hy : Function.Injective y := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [y]
  have hxmem : ∀ i,x i ∈ T := by
    intro i
    fin_cases i <;> simp [x,hTabc]
  have hyoutside : ∀ j,y j ∉ T := by
    intro j
    fin_cases j
    · exact hu'.1
    · exact hv'.1
    · exact hw'.1
  have hyadj : ∀ j,∀ t ∈ T,G.Adj (y j) t := by
    intro j
    fin_cases j
    · exact hu'.2
    · exact hv'.2
    · exact hw'.2
  exact hG.no_complete_bipartite_three_three x y hx hy
    (fun i j heq => hyoutside j (heq ▸ hxmem i))
    (fun i j => G.adj_symm (hyadj j _ (hxmem i)))

/-- Planarity bounds the number of tetrahedra on any triangle by two. -/
theorem HasPlaneDrawing.triangleMultiplicity_le_two {G : SimpleGraph V}
    (hG : HasPlaneDrawing G) (T : Finset V) (hT : T.card = 3)
    (hcT : G.IsClique T) : triangleMultiplicity G T ≤ 2 := by
  rw [triangleMultiplicity_eq_commonApices_card hT hcT]
  exact hG.common_apices_bound T hT

/-- In particular every planar graph satisfies the admissibility bound used
by the full three-tree theorem. -/
theorem HasPlaneDrawing.admissible {G : SimpleGraph V}
    (hG : HasPlaneDrawing G) : Admissible G := by
  intro T hT hcT
  exact (hG.triangleMultiplicity_le_two T hT hcT).trans (by omega)

end GraphicalZonotopes

end
end
end BundlePart430

section BundlePart431
/- Source: Papers/GraphicalZonotopes/PlanarCombinatorics.lean -/






end BundlePart431

section BundlePart432
/- Source: Papers/GraphicalZonotopes/PlanarAnalyticSupport.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical BigOperators Pointwise
namespace GraphicalZonotopes
open Finset RefinedTriangleComponents
variable {V : Type*} [Fintype V] [LinearOrder V]

/-- The support argument needs only the actual forbidden triangle-apex
configuration. Its use for planar graphs is discharged by the independent
continuous-drawing obstruction, rather than an edge-count hypothesis. -/
theorem TriangleApexSeparated.extreme_support {G : SimpleGraph V} (hG : TriangleApexSeparated G)
    {z : SetFunction V} (hz : ExtremeSupermodular z) (hg : Graphical G z)
    (hd : 3 ≤ Module.finrank ℝ (vectorSpan ℝ (basePolytope z))) :
    ∃ U : Finset V,4 ≤ U.card ∧
      actualDirectionGraph (basePolytope z) = inducedOn G U ∧
      ThreeTreeOn U (inducedOn G U) ∧ Admissible (inducedOn G U) ∧
      Module.finrank ℝ (vectorSpan ℝ (basePolytope z)) = U.card-1 := by
  classical
  let F := family (mobius z)
  let U := F.biUnion id
  obtain ⟨hne,hconn,hactual,hdep⟩ := refined_support_of_dimension_ge_three
    hG.cliqueFree_five hz hg hd
  have hy : CliqueSupported G (mobius z) := (mobius_cliqueSupported_iff G z).mpr ⟨hz.1,hg⟩
  have hcl : ∀ C ∈ F,C.card = 4 ∧ G.IsClique C := by
    intro C hC
    obtain ⟨hc,hn⟩ := (mem_family _ C).mp hC
    refine ⟨hc,?_⟩
    by_contra hnot
    exact hn (coefficient_zero_of_not_clique hy C (by rintro ⟨_,hh⟩; exact hnot hh))
  have htree := hG.connected_family_threeTree F hne hcl hconn
  have hU : 4 ≤ U.card := htree.active_card_ge_four
  let H := actualDirectionGraph (basePolytope z)
  have hHU : H ≤ inducedOn G U := by
    intro u v huv
    have he : (edgeGraph (mobius z)).Adj u v := by simpa only [H,hactual] using huv
    obtain ⟨_,C,hC,hu,hv⟩ := he
    exact ⟨actualRootEdge_of_graphical hz.1.1 hz.2.1 hg huv,
      mem_biUnion.mpr ⟨C,hC,hu⟩,mem_biUnion.mpr ⟨C,hC,hv⟩⟩
  have hclH : ∀ C ∈ F,C.card = 4 ∧ H.IsClique C := by
    intro C hC
    refine ⟨(mem_family _ C).mp hC |>.1,?_⟩
    rw [show H = edgeGraph (mobius z) from hactual]
    exact family_subset_edgeGraph_clique hC
  have hHg := tetrahedralGrowth_of_connected_family H F hne hclH hconn
  have hiH : inducedOn H U = H := by
    ext u v
    constructor
    · exact fun h => h.1
    · intro h
      exact ⟨h,(hHU h).2⟩
  have hlow := hHg.edge_bound_and_equality.1
  change 3*U.card-6 ≤ (edgeFamily (inducedOn H U)).card at hlow
  rw [hiH] at hlow
  have heq : H = inducedOn G U := graph_eq_of_le_card_edges hHU
    (by rw [htree.edgeFamily_card]; exact hlow)
  have htreeH : ThreeTreeOn U (actualDirectionGraph (basePolytope z)) := by
    change ThreeTreeOn U H
    rw [heq]
    exact htree
  obtain ⟨hdim,hA⟩ := threeTree_actual_dimension_admissible hz htreeH
  exact ⟨U,hU,heq,htree,heq ▸ hA,hdim⟩

theorem TriangleApexSeparated.polytope_support {G : SimpleGraph V}
    (hG : TriangleApexSeparated G) {Q : Set (V → ℝ)} (hQ : IsFinitePolytope Q)
    (hi : MinkowskiIndecomposable Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope G))
    (hd : 3 ≤ Module.finrank ℝ (vectorSpan ℝ Q)) :
    ∃ U : Finset V,4 ≤ U.card ∧ actualDirectionGraph Q = inducedOn G U ∧
      ThreeTreeOn U (inducedOn G U) ∧ Admissible (inducedOn G U) ∧
      Module.finrank ℝ (vectorSpan ℝ Q) = U.card-1 := by
  obtain ⟨z,hz,he,hdim,hgraph⟩ := weak_summand_normalized_function hQ hi hw
  have hdz : 3 ≤ Module.finrank ℝ (vectorSpan ℝ (basePolytope z.1)) := by rwa [hdim] at hd
  have hext : ExtremeSupermodular z.1 := by
    rcases he with he | he
    · rw [he,basePolytope_zero,_root_.vectorSpan_singleton,finrank_bot] at hdz
      omega
    · exact he
  obtain ⟨U,hU,ha,ht,hA,hD⟩ := hG.extreme_support hext z.2.2 hdz
  exact ⟨U,hU,hgraph.trans ha,ht,hA,hdim.trans hD⟩

/-- The full-support criterion following from the geometric obstruction
and the actual triangle multiplicity bound. The drawing corollary supplies
both graph properties from ordinary plane planarity. -/
theorem TriangleApexSeparated.supports_full_iff_threeTree {G : SimpleGraph V}
    (hG : TriangleApexSeparated G) (hn : 4 ≤ Fintype.card V) (hA : Admissible G) :
    SupportsFullIndecomposable G ↔ IsThreeTree G := by
  constructor
  · rintro ⟨Q,hQ,hi,hd,hw⟩
    have hd3 : 3 ≤ Module.finrank ℝ (vectorSpan ℝ Q) := by
      change Module.finrank ℝ (vectorSpan ℝ Q) = Fintype.card V-1 at hd
      omega
    obtain ⟨U,hU,ha,ht,hUA,hD⟩ := hG.polytope_support hQ hi hw hd3
    have hcard : U.card = Fintype.card V := by
      change Module.finrank ℝ (vectorSpan ℝ Q) = Fintype.card V-1 at hd
      omega
    have hUniv : U = univ := eq_univ_of_card U hcard
    rw [hUniv,inducedOn_univ] at ht
    exact ht
  · intro ht
    obtain ⟨f,hf,hfi,hfd,hfa,hfg⟩ := admissible_threeTree_witness_fintype ht hA
    exact ⟨basePolytope f,(hfi.basePolytope hf.1.1 hf.2.1).finitePolytope,
      hf.minkowskiIndecomposable,hfd,
      (isWeakMinkowskiSummand_graphical_iff hf.1.1 hf.2.1).mpr hfg⟩

end GraphicalZonotopes

end
end
end BundlePart432

section BundlePart433
/- Source: Papers/GraphicalZonotopes/PlanarAnalyticSpectrum.lean -/





/-! # Dimension and lattice spectrum under the triangle-apex obstruction

These lemmas are the analytic part of the planar corollaries. Their graph
hypothesis is independently derived from a genuine noncrossing drawing in
the public planar statements. All intermediate dimensions are attained.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical BigOperators Pointwise
namespace GraphicalZonotopes
open Finset SetFunctionEmbedding
variable {V : Type*} [Fintype V] [LinearOrder V]

theorem IsAdmissibleCliqueCollection.induced_structure_of_apex_separated {G : SimpleGraph V}
    (hG : TriangleApexSeparated G) {F : Finset (Finset V)}
    (hF : IsAdmissibleCliqueCollection G F) :
    ThreeTreeOn (F.biUnion id) (inducedOn G (F.biUnion id)) ∧
      tetrahedra (inducedOn G (F.biUnion id)) = F ∧
      Admissible (inducedOn G (F.biUnion id)) ∧
      (F.biUnion id).card = F.card + 3 := by
  let U := F.biUnion id
  have ht := hG.connected_family_threeTree F hF.nonempty hF.four hF.connected
  have hsub : F ⊆ tetrahedra (inducedOn G U) := by
    intro C hC
    refine mem_filter.mpr ⟨mem_univ _,(hF.four C hC).1,?_⟩
    intro u hu v hv huv
    exact ⟨(hF.four C hC).2 hu hv huv,
      mem_biUnion.mpr ⟨C,hC,hu⟩,mem_biUnion.mpr ⟨C,hC,hv⟩⟩
  have hu := connected_tetrahedra_union_card F hF.nonempty
    (fun C hC => (hF.four C hC).1) hF.connected
  have hfour : 4 ≤ U.card := ht.active_card_ge_four
  have hcard : (tetrahedra (inducedOn G U)).card = U.card - 3 := ht.tetrahedra_card
  have he : tetrahedra (inducedOn G U) = F := by
    apply (eq_of_subset_of_card_le hsub ?_).symm
    rw [hcard]
    change U.card ≤ F.card + 3 at hu
    omega
  refine ⟨ht,he,?_,?_⟩
  · intro T hT hc
    change ((tetrahedra (inducedOn G U)).filter (fun C => T ⊆ C)).card ≤ 3
    rw [he]
    exact hF.thin T hT
  · rw [he] at hcard
    change U.card = F.card + 3
    omega

theorem TriangleApexSeparated.dimension_le_clique_count {G : SimpleGraph V}
    (hG : TriangleApexSeparated G) {Q : Set (V → ℝ)} (hQ : IsFinitePolytope Q)
    (hi : MinkowskiIndecomposable Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope G)) :
    Module.finrank ℝ (vectorSpan ℝ Q) ≤ maximumAdmissibleCliqueCount G+2 := by
  by_cases hd : 3 ≤ Module.finrank ℝ (vectorSpan ℝ Q)
  · obtain ⟨U,hU,ha,ht,hA,hD⟩ := TriangleApexSeparated.polytope_support hG hQ hi hw hd
    have hF := ht.admissibleCliqueCollection hA (inducedOn_le G U)
    have hb := admissibleClique_count_le_maximum hF
    rw [ht.tetrahedra_card] at hb
    omega
  · omega

/-- The maximum admissible clique collection gives an actual lattice witness
for the supremum defining the dimension invariant. -/
theorem TriangleApexSeparated.maximum_witness {G : SimpleGraph V}
    (hG : TriangleApexSeparated G) (hK : (tetrahedra G).Nonempty) :
    ∃ Q : Set (V → ℝ), LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
      Module.finrank ℝ (vectorSpan ℝ Q) = maximumAdmissibleCliqueCount G+2 := by
  obtain ⟨F,hF,hmax⟩ := maximumAdmissibleCliqueCount_attained hK
  obtain ⟨ht,he,hA,hcard⟩ := hF.induced_structure_of_apex_separated hG
  obtain ⟨Q,hQ,hi,hw,ha,hd⟩ := induced_admissible_threeTree_witness ht hA
  exact ⟨Q,hQ,hi,hw,by omega⟩

theorem TriangleApexSeparated.maximum_dimension {G : SimpleGraph V}
    (hG : TriangleApexSeparated G) (hK : (tetrahedra G).Nonempty) :
    maximumIndecomposableDimension G = maximumAdmissibleCliqueCount G+2 := by
  apply le_antisymm
  · apply csSup_le'
    rintro d ⟨Q,hQ,hi,hw,hd⟩
    rw [← hd]
    exact TriangleApexSeparated.dimension_le_clique_count hG hQ hi hw
  · obtain ⟨Q,hQ,hi,hw,hd⟩ := TriangleApexSeparated.maximum_witness hG hK
    rw [← hd]
    exact dimension_le_maximum hQ.finitePolytope hi hw

/-- Every positive integer through the sharp maximum occurs, with no gap and
with a lattice representative. The construction uses an arbitrary prefix of
a maximizing admissible three-tree and actual clique simplices at dimensions
one and two. -/
theorem TriangleApexSeparated.dimension_spectrum {G : SimpleGraph V}
    (hG : TriangleApexSeparated G) (hK : (tetrahedra G).Nonempty)
    (d : ℕ) (hd : 1 ≤ d) (hdM : d ≤ maximumAdmissibleCliqueCount G+2) :
    ∃ Q : Set (V → ℝ), LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
      Module.finrank ℝ (vectorSpan ℝ Q) = d := by
  by_cases hd3 : 3 ≤ d
  · obtain ⟨F,hF,hmax⟩ := maximumAdmissibleCliqueCount_attained hK
    obtain ⟨ht,he,hA,hcard⟩ := hF.induced_structure_of_apex_separated hG
    obtain ⟨U,H,hU,hcardU,hH,htH⟩ := ht.prefix (m := d+1) (by omega) (by omega)
    have hHA : Admissible H := hA.mono hH
    obtain ⟨f,hf,hfi,hfd,hfa,hfg⟩ := admissible_threeTree_active_witness htH hHA
    refine ⟨basePolytope f,hfi.basePolytope hf.1.1 hf.2.1,hf.minkowskiIndecomposable,?_,?_⟩
    · exact (isWeakMinkowskiSummand_graphical_iff hf.1.1 hf.2.1).mpr
        (hfg.mono_graph (hH.trans (inducedOn_le G _)))
    · omega
  · obtain ⟨C,hC⟩ := hK
    obtain ⟨hfour,hcl⟩ := (mem_filter.mp hC).2
    obtain ⟨D,hDC,hD⟩ := exists_subset_card_eq (s := C) (n := d+1) (by omega)
    obtain ⟨Q,hQ,hi,hw,hqdim⟩ := clique_simplex_witness
      (by omega : 2 ≤ D.card) (fun u hu v hv huv => hcl (hDC hu) (hDC hv) huv)
    exact ⟨Q,hQ,hi,hw,by omega⟩

theorem TriangleApexSeparated.no_tetrahedron_dimension_le_two {G : SimpleGraph V}
    (hG : TriangleApexSeparated G) (hK : tetrahedra G = ∅)
    {Q : Set (V → ℝ)} (hQ : IsFinitePolytope Q) (hi : MinkowskiIndecomposable Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope G)) :
    Module.finrank ℝ (vectorSpan ℝ Q) ≤ 2 := by
  by_contra hd
  have hd3 : 3 ≤ Module.finrank ℝ (vectorSpan ℝ Q) := by omega
  obtain ⟨U,hU,ha,ht,hA,hD⟩ := TriangleApexSeparated.polytope_support hG hQ hi hw hd3
  obtain ⟨C,hC⟩ := ht.tetrahedra_nonempty
  have hc := tetrahedra_mono (inducedOn_le G U) hC
  rw [hK] at hc
  exact notMem_empty C hc

theorem TriangleApexSeparated.triangle_maximum {G : SimpleGraph V}
    (hG : TriangleApexSeparated G) (hK : tetrahedra G = ∅)
    (hT : ∃ T : Finset V,T.card = 3 ∧ G.IsClique T) :
    maximumIndecomposableDimension G = 2 := by
  apply le_antisymm
  · apply csSup_le'
    rintro d ⟨Q,hQ,hi,hw,hd⟩
    rw [← hd]
    exact TriangleApexSeparated.no_tetrahedron_dimension_le_two hG hK hQ hi hw
  · obtain ⟨T,hT,hcl⟩ := hT
    obtain ⟨Q,hQ,hi,hw,hd⟩ := clique_simplex_witness (by omega) hcl
    have hb := dimension_le_maximum hQ.finitePolytope hi hw
    rw [hd,hT] at hb
    exact hb

theorem TriangleApexSeparated.piecewise_maximum {G : SimpleGraph V}
    (hG : TriangleApexSeparated G) :
    maximumIndecomposableDimension G = partialThreeTreeDimension G := by
  unfold partialThreeTreeDimension
  by_cases hK : (tetrahedra G).Nonempty
  · rw [if_pos hK]
    exact TriangleApexSeparated.maximum_dimension hG hK
  · rw [if_neg hK]
    have hKe : tetrahedra G = ∅ := not_nonempty_iff_eq_empty.mp hK
    by_cases hT : ∃ T : Finset V,T.card = 3 ∧ G.IsClique T
    · rw [if_pos hT]
      exact TriangleApexSeparated.triangle_maximum hG hKe hT
    · rw [if_neg hT]
      have hcf : G.CliqueFree 3 := fun T h => hT ⟨T,h.card_eq,h.isClique⟩
      by_cases hE : ∃ u v : V,G.Adj u v
      · rw [if_pos hE]
        exact triangleFree_maximum_dimension hcf hE
      · rw [if_neg hE]
        exact edgeless_maximum_dimension (fun u v huv => hE ⟨u,v,huv⟩)

/-- The full positive spectrum, including graphs with no tetrahedron. -/
theorem TriangleApexSeparated.full_dimension_spectrum {G : SimpleGraph V}
    (hG : TriangleApexSeparated G) (d : ℕ) (hd : 1 ≤ d)
    (hmax : d ≤ maximumIndecomposableDimension G) :
    ∃ Q : Set (V → ℝ),LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
      Module.finrank ℝ (vectorSpan ℝ Q) = d := by
  by_cases hK : (tetrahedra G).Nonempty
  · apply TriangleApexSeparated.dimension_spectrum hG hK d hd
    rwa [TriangleApexSeparated.maximum_dimension hG hK] at hmax
  · have hKe : tetrahedra G = ∅ := not_nonempty_iff_eq_empty.mp hK
    by_cases hT : ∃ T : Finset V,T.card = 3 ∧ G.IsClique T
    · rw [TriangleApexSeparated.triangle_maximum hG hKe hT] at hmax
      obtain ⟨T,hT,hcl⟩ := hT
      obtain ⟨C,hCT,hC⟩ := exists_subset_card_eq (s := T) (n := d+1) (by omega)
      obtain ⟨Q,hQ,hi,hw,hqdim⟩ := clique_simplex_witness (by omega : 2 ≤ C.card)
        (fun u hu v hv huv => hcl (hCT hu) (hCT hv) huv)
      exact ⟨Q,hQ,hi,hw,by omega⟩
    · have hcf : G.CliqueFree 3 := fun T h => hT ⟨T,h.card_eq,h.isClique⟩
      by_cases hE : ∃ u v : V,G.Adj u v
      · rw [triangleFree_maximum_dimension hcf hE] at hmax
        have hd1 : d = 1 := by omega
        obtain ⟨u,v,huv⟩ := hE
        have hcl : G.IsClique ({u,v} : Finset V) := by
          intro a ha b hb hab
          change a ∈ ({u,v} : Finset V) at ha
          change b ∈ ({u,v} : Finset V) at hb
          simp only [mem_insert,mem_singleton] at ha hb
          rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
          · exact False.elim (hab rfl)
          · exact huv
          · exact huv.symm
          · exact False.elim (hab rfl)
        obtain ⟨Q,hQ,hi,hw,hqdim⟩ := clique_simplex_witness
          (by rw [card_pair huv.ne]) hcl
        refine ⟨Q,hQ,hi,hw,?_⟩
        simpa only [card_pair huv.ne,hd1] using hqdim
      · have hdim := edgeless_maximum_dimension (fun u v huv => hE ⟨u,v,huv⟩)
        omega

end GraphicalZonotopes

end
end
end BundlePart433

section BundlePart434
/- Source: Papers/GraphicalZonotopes/PlanarComponentDimension.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [LinearOrder V]

namespace TetrahedronComponents

/-- The actual connected components of the graph of all tetrahedra, with
adjacency given by sharing a triangle. -/
abbrev Component (G : SimpleGraph V) :=
  (tetrahedronGraph (tetrahedra G)).ConnectedComponent

def family (G : SimpleGraph V) (c : Component G) : Finset (Finset V) :=
  (tetrahedra G).filter (fun C => ∃ hC : C ∈ tetrahedra G,
    (tetrahedronGraph (tetrahedra G)).connectedComponentMk ⟨C,hC⟩ = c)

@[simp] theorem mem_family (G : SimpleGraph V) (c : Component G) (C : Finset V) :
    C ∈ family G c ↔ ∃ hC : C ∈ tetrahedra G,
      (tetrahedronGraph (tetrahedra G)).connectedComponentMk ⟨C,hC⟩ = c := by
  simp only [family,mem_filter]
  exact ⟨fun h => h.2,fun ⟨hC,h⟩ => ⟨hC,hC,h⟩⟩

theorem family_subset (G : SimpleGraph V) (c : Component G) :
    family G c ⊆ tetrahedra G := filter_subset _ _

theorem family_nonempty (G : SimpleGraph V) (c : Component G) : (family G c).Nonempty := by
  obtain ⟨C,hC⟩ := c.exists_rep
  exact ⟨C.1,(mem_family G c C.1).mpr ⟨C.2,hC⟩⟩

theorem family_connected (G : SimpleGraph V) (c : Component G) :
    (tetrahedronGraph (family G c)).Preconnected := by
  let f : c.toSimpleGraph →g tetrahedronGraph (family G c) :=
    { toFun := fun C => ⟨C.1.1,(mem_family G c C.1.1).mpr ⟨C.1.2,C.2⟩⟩
      map_rel' := by
        intro C D hCD
        change (tetrahedronGraph (tetrahedra G)).Adj C.1 D.1 at hCD
        refine ⟨?_,hCD.2⟩
        intro he
        have heval : C.1.1 = D.1.1 := congrArg
          (fun E : {E : Finset V // E ∈ family G c} => E.1) he
        exact hCD.1 (Subtype.ext heval) }
  intro A B
  obtain ⟨hA,hAc⟩ := (mem_family G c A.1).mp A.2
  obtain ⟨hB,hBc⟩ := (mem_family G c B.1).mp B.2
  exact ((c.connected_toSimpleGraph).preconnected
    ⟨⟨A.1,hA⟩,hAc⟩ ⟨⟨B.1,hB⟩,hBc⟩).map f

/-- Every nonempty connected collection is contained in one actual component
of the graph of all tetrahedra, rather than an arbitrary chosen enlargement. -/
theorem connected_family_subset_component (G : SimpleGraph V) (F : Finset (Finset V))
    (hne : F.Nonempty) (hsub : F ⊆ tetrahedra G)
    (hconn : (tetrahedronGraph F).Preconnected) :
    ∃ c : Component G,F ⊆ family G c := by
  obtain ⟨A,hA⟩ := hne
  let f : tetrahedronGraph F →g tetrahedronGraph (tetrahedra G) :=
    { toFun := fun C => ⟨C.1,hsub C.2⟩
      map_rel' := by
        intro C D hCD
        refine ⟨?_,hCD.2⟩
        intro he
        have heval : C.1 = D.1 := congrArg
          (fun E : {E : Finset V // E ∈ tetrahedra G} => E.1) he
        exact hCD.1 (Subtype.ext heval) }
  let c : Component G := (tetrahedronGraph (tetrahedra G)).connectedComponentMk ⟨A,hsub hA⟩
  refine ⟨c,?_⟩
  intro C hC
  apply (mem_family G c C).mpr
  refine ⟨hsub hC,?_⟩
  exact SimpleGraph.ConnectedComponent.sound ((hconn ⟨C,hC⟩ ⟨A,hA⟩).map f)

theorem family_admissible {G : SimpleGraph V} (hA : Admissible G) (c : Component G) :
    IsAdmissibleCliqueCollection G (family G c) := by
  refine ⟨family_nonempty G c,family_subset G c,family_connected G c,?_⟩
  intro T hT
  by_cases hcT : G.IsClique T
  · exact (card_le_card (filter_subset_filter _ (family_subset G c))).trans (hA T hT hcT)
  · have hempty : (family G c).filter (fun C => T ⊆ C) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro C hC
      obtain ⟨hCF,hTC⟩ := mem_filter.mp hC
      have hcl := (mem_filter.mp (family_subset G c hCF)).2.2
      exact hcT (fun u hu v hv huv => hcl (hTC hu) (hTC hv) huv)
    rw [hempty,card_empty]
    omega

/-- The exact vertex set denoted V(C) in Corollary 6.5. -/
def vertices (G : SimpleGraph V) (c : Component G) : Finset V := (family G c).biUnion id

theorem vertices_card {G : SimpleGraph V} (hG : TriangleApexSeparated G)
    (hA : Admissible G) (c : Component G) :
    (vertices G c).card = (family G c).card + 3 :=
  ((family_admissible hA c).induced_structure_of_apex_separated hG).2.2.2

/-- Maximum of |V(C)|−1 over the actual triangle-adjacency components of
all four-cliques. The empty maximum is zero. -/
def maximumDimension (G : SimpleGraph V) : ℕ :=
  (univ : Finset (Component G)).sup (fun c => (vertices G c).card - 1)

/-- The component formula in the planar corollary is exactly equal to the
admissible-collection formula, with equivalence proved rather than stipulated. -/
theorem maximumDimension_eq {G : SimpleGraph V} (hG : TriangleApexSeparated G)
    (hA : Admissible G) (hK : (tetrahedra G).Nonempty) :
    maximumDimension G = maximumAdmissibleCliqueCount G + 2 := by
  apply le_antisymm
  · apply Finset.sup_le_iff.mpr
    intro c _
    have hc := vertices_card hG hA c
    have hm := admissibleClique_count_le_maximum (family_admissible hA c)
    omega
  · obtain ⟨F,hF,hmax⟩ := maximumAdmissibleCliqueCount_attained hK
    obtain ⟨c,hFc⟩ := connected_family_subset_component G F hF.nonempty hF.included hF.connected
    have hcard := card_le_card hFc
    have hc := vertices_card hG hA c
    have hm : (vertices G c).card - 1 ≤ maximumDimension G := by
      unfold maximumDimension
      exact Finset.le_sup (f := fun c : Component G => (vertices G c).card - 1) (mem_univ c)
    omega

end TetrahedronComponents

/-- The literal piecewise formula of Corollary 6.5, using actual connected
components of the tetrahedron graph, followed by triangles, edges, and zero. -/
def planarComponentDimension (G : SimpleGraph V) : ℕ :=
  if (tetrahedra G).Nonempty then TetrahedronComponents.maximumDimension G
  else if ∃ T : Finset V,T.card = 3 ∧ G.IsClique T then 2
  else if ∃ u v : V,G.Adj u v then 1 else 0

theorem planarComponentDimension_eq_partialThreeTreeDimension {G : SimpleGraph V}
    (hG : TriangleApexSeparated G) (hA : Admissible G) :
    planarComponentDimension G = partialThreeTreeDimension G := by
  unfold planarComponentDimension partialThreeTreeDimension
  split_ifs with hK hT hE
  · exact TetrahedronComponents.maximumDimension_eq hG hA hK
  all_goals rfl

end GraphicalZonotopes

end
end
end BundlePart434

section BundlePart435
/- Source: Papers/GraphicalZonotopes/StackedTriangulation.lean -/






/-! # The boundary-face dictionary for stacked triangulations

The face set is part of the construction. Starting with the four faces of a
tetrahedron, a stacking step removes one available face and inserts its three
cones over the face's edges. The dictionary identifies those actual boundary
faces with triangles contained in exactly one construction tetrahedron.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

def boundaryTriangles (G : SimpleGraph V) : Finset (Finset V) :=
  (triangles G).filter (fun T => triangleMultiplicity G T = 1)

@[simp] theorem mem_boundaryTriangles {G : SimpleGraph V} {T : Finset V} :
    T ∈ boundaryTriangles G ↔ T.card = 3 ∧ G.IsClique T ∧ triangleMultiplicity G T = 1 := by
  simp only [boundaryTriangles,mem_filter,mem_triangles,and_assoc]

theorem triangleMultiplicity_cliqueGraph_of_subset {C T : Finset V}
    (hC : C.card = 4) (hTC : T ⊆ C) : triangleMultiplicity (cliqueGraph C) T = 1 := by
  rw [triangleMultiplicity,tetrahedra_cliqueGraph hC,filter_singleton,if_pos hTC,card_singleton]

theorem boundaryTriangles_cliqueGraph {C : Finset V} (hC : C.card = 4) :
    boundaryTriangles (cliqueGraph C) = C.powersetCard 3 := by
  ext T
  rw [boundaryTriangles,mem_filter,triangles_cliqueGraph hC]
  exact ⟨fun h => h.1,fun h => ⟨h,
    triangleMultiplicity_cliqueGraph_of_subset hC (mem_powersetCard.mp h).1⟩⟩

private theorem old_triangle_subset_attach_iff {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {u : V} (hu : u ∉ S) {A T : Finset V}
    (hA : A.card = 3) (hT : T.card = 3) (hcT : G.IsClique T) :
    T ⊆ insert u A ↔ T = A := by
  constructor
  · intro hsub
    have huT : u ∉ T := fun hm => hu (h.clique_subset_active (by omega) hcT hm)
    apply eq_of_subset_of_card_le
    · intro t ht
      exact (mem_insert.mp (hsub ht)).resolve_left (fun he => huT (he ▸ ht))
    · omega
  · rintro rfl
    exact subset_insert _ _

/-- The boundary update is exactly the usual one-to-three subdivision of a
triangular face. It is proved from actual clique incidences. -/
theorem boundaryTriangles_after_attachment {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {u : V} (hu : u ∉ S) {A : Finset V}
    (hA : A.card = 3) (hAS : A ⊆ S) (hcA : G.IsClique A)
    (hbA : triangleMultiplicity G A = 1) :
    boundaryTriangles (G ⊔ attachmentStar u A) =
      (boundaryTriangles G).erase A ∪ (A.powersetCard 2).image (insert u) := by
  ext T
  constructor
  · intro hT
    obtain ⟨hTc,hTcl,hTm⟩ := mem_boundaryTriangles.mp hT
    by_cases huT : u ∈ T
    · apply mem_union_right
      have ht : T ∈ triangles (G ⊔ attachmentStar u A) := mem_triangles.mpr ⟨hTc,hTcl⟩
      rw [triangles_after_attachment h hu hA hAS hcA] at ht
      refine (mem_union.mp ht).resolve_left ?_
      intro htold
      exact hu (h.clique_subset_active (by omega) (mem_triangles.mp htold).2 huT)
    · have hcOld : G.IsClique T := clique_before_attachment huT hTcl
      have hTA : T ≠ A := by
        rintro rfl
        rw [triangleMultiplicity_after_attachment h hu hA hAS hcA,
          hbA,if_pos (subset_insert _ _)] at hTm
        omega
      have hnot : ¬ T ⊆ insert u A := fun hh => hTA
        ((old_triangle_subset_attach_iff h hu hA hTc hcOld).mp hh)
      rw [triangleMultiplicity_after_attachment h hu hA hAS hcA,if_neg hnot,Nat.add_zero] at hTm
      exact mem_union_left _ (mem_erase.mpr ⟨hTA,mem_boundaryTriangles.mpr ⟨hTc,hcOld,hTm⟩⟩)
  · intro hT
    rcases mem_union.mp hT with hT | hT
    · obtain ⟨hTA,hT⟩ := mem_erase.mp hT
      obtain ⟨hTc,hTcl,hTm⟩ := mem_boundaryTriangles.mp hT
      have hnot : ¬ T ⊆ insert u A := fun hh => hTA
        ((old_triangle_subset_attach_iff h hu hA hTc hTcl).mp hh)
      apply mem_boundaryTriangles.mpr
      refine ⟨hTc,fun a ha b hb hab => Or.inl (hTcl ha hb hab),?_⟩
      rw [triangleMultiplicity_after_attachment h hu hA hAS hcA,if_neg hnot,Nat.add_zero,hTm]
    · obtain ⟨E,hE,rfl⟩ := mem_image.mp hT
      obtain ⟨hEA,hEc⟩ := mem_powersetCard.mp hE
      have huE : u ∉ E := fun hh => hu (hAS (hEA hh))
      have htri : insert u E ∈ triangles (G ⊔ attachmentStar u A) := by
        rw [triangles_after_attachment h hu hA hAS hcA]
        exact mem_union_right _ (mem_image.mpr ⟨E,mem_powersetCard.mpr ⟨hEA,hEc⟩,rfl⟩)
      apply mem_boundaryTriangles.mpr
      refine ⟨(mem_triangles.mp htri).1,(mem_triangles.mp htri).2,?_⟩
      rw [triangleMultiplicity_after_attachment h hu hA hAS hcA,
        h.triangleMultiplicity_eq_zero_of_outside hu (mem_insert_self _ _),
        if_pos (insert_subset_insert u hEA)]

private theorem thin_after_boundary_attachment {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {u : V} (hu : u ∉ S) {A : Finset V}
    (hA : A.card = 3) (hAS : A ⊆ S) (hcA : G.IsClique A)
    (hbA : triangleMultiplicity G A = 1)
    (hthin : ∀ T : Finset V,T.card = 3 → G.IsClique T → triangleMultiplicity G T ≤ 2) :
    ∀ T : Finset V,T.card = 3 → (G ⊔ attachmentStar u A).IsClique T →
      triangleMultiplicity (G ⊔ attachmentStar u A) T ≤ 2 := by
  intro T hT hcT
  rw [triangleMultiplicity_after_attachment h hu hA hAS hcA]
  by_cases huT : u ∈ T
  · rw [h.triangleMultiplicity_eq_zero_of_outside hu huT]
    split_ifs <;> omega
  · have hcOld : G.IsClique T := clique_before_attachment huT hcT
    by_cases hTA : T = A
    · subst T
      rw [hbA]
      split_ifs <;> omega
    · have hnot : ¬ T ⊆ insert u A := fun hh => hTA
        ((old_triangle_subset_attach_iff h hu hA hT hcOld).mp hh)
      rw [if_neg hnot,Nat.add_zero]
      exact hthin T hT hcOld

/-- The ordinary combinatorial definition of a stacked boundary
triangulation, including its explicit evolving triangular face set. -/
inductive StackedTriangulationOn : Finset V → SimpleGraph V → Finset (Finset V) → Prop
  | tetrahedron (C : Finset V) (hC : C.card = 4) :
      StackedTriangulationOn C (cliqueGraph C) (C.powersetCard 3)
  | stack {S : Finset V} {G : SimpleGraph V} {F : Finset (Finset V)}
      (h : StackedTriangulationOn S G F) (u : V) (hu : u ∉ S)
      (T : Finset V) (hT : T.card = 3) (hTS : T ⊆ S) (hcT : G.IsClique T)
      (hface : T ∈ F) :
      StackedTriangulationOn (insert u S) (G ⊔ attachmentStar u T)
        (F.erase T ∪ (T.powersetCard 2).image (insert u))

theorem StackedTriangulationOn.properties {S : Finset V} {G : SimpleGraph V}
    {F : Finset (Finset V)} (h : StackedTriangulationOn S G F) :
    ThreeTreeOn S G ∧
      (∀ T : Finset V,T.card = 3 → G.IsClique T → triangleMultiplicity G T ≤ 2) ∧
      F = boundaryTriangles G := by
  induction h with
  | tetrahedron C hC =>
    refine ⟨ThreeTreeOn.tetrahedron C hC,?_,(boundaryTriangles_cliqueGraph hC).symm⟩
    intro T hT hcT
    rw [triangleMultiplicity_cliqueGraph_of_subset hC
      ((ThreeTreeOn.tetrahedron C hC).clique_subset_active (by omega) hcT)]
    omega
  | @stack S G F h u hu T hT hTS hcT hface ih =>
    obtain ⟨ht,hthin,hF⟩ := ih
    have hb : triangleMultiplicity G T = 1 :=
      (mem_boundaryTriangles.mp (hF ▸ hface)).2.2
    refine ⟨ThreeTreeOn.attach ht u hu T hT hTS hcT,
      thin_after_boundary_attachment ht hu hT hTS hcT hb hthin,?_⟩
    rw [hF,boundaryTriangles_after_attachment ht hu hT hTS hcT hb]

theorem ThreeTreeOn.stacked {S : Finset V} {G : SimpleGraph V} (h : ThreeTreeOn S G) :
    (∀ T : Finset V,T.card = 3 → G.IsClique T → triangleMultiplicity G T ≤ 2) →
      StackedTriangulationOn S G (boundaryTriangles G) := by
  induction h with
  | tetrahedron C hC =>
    intro _
    rw [boundaryTriangles_cliqueGraph hC]
    exact StackedTriangulationOn.tetrahedron C hC
  | @attach S G h u hu T hT hTS hcT ih =>
    intro hthin
    have hOld : ∀ A : Finset V,A.card = 3 → G.IsClique A → triangleMultiplicity G A ≤ 2 := by
      intro A hA hcA
      exact (triangleMultiplicity_mono (show G ≤ G ⊔ attachmentStar u T from le_sup_left) A).trans
        (hthin A hA (fun a ha b hb hab => Or.inl (hcA ha hb hab)))
    have hb : triangleMultiplicity G T = 1 := by
      obtain ⟨C,hC,hTC⟩ := h.triangle_extends hT hcT
      have hpos : 0 < triangleMultiplicity G T :=
        card_pos.mpr ⟨C,mem_filter.mpr ⟨hC,hTC⟩⟩
      have hnew := hthin T hT (fun a ha b hb hab => Or.inl (hcT ha hb hab))
      rw [triangleMultiplicity_after_attachment h hu hT hTS hcT,
        if_pos (subset_insert _ _)] at hnew
      omega
    rw [boundaryTriangles_after_attachment h hu hT hTS hcT hb]
    exact StackedTriangulationOn.stack (ih hOld) u hu T hT hTS hcT
      (mem_boundaryTriangles.mpr ⟨hT,hcT,hb⟩)

def IsStackedTriangulation (G : SimpleGraph V) : Prop :=
  ∃ F : Finset (Finset V),StackedTriangulationOn univ G F

/-- Equivalence with the usual three-tree formulation, with the exact
boundary face set recovered as a theorem. -/
theorem isStackedTriangulation_iff {G : SimpleGraph V} :
    IsStackedTriangulation G ↔ IsThreeTree G ∧
      (∀ T : Finset V,T.card = 3 → G.IsClique T → triangleMultiplicity G T ≤ 2) := by
  constructor
  · rintro ⟨F,hF⟩
    exact ⟨hF.properties.1,hF.properties.2.1⟩
  · rintro ⟨ht,hthin⟩
    exact ⟨boundaryTriangles G,ht.stacked hthin⟩

end GraphicalZonotopes

end
end
end BundlePart435

section BundlePart436
/- Source: Papers/GraphicalZonotopes/PlanarPaperStatements.lean -/









/-! # The planar classification and complete dimension spectrum

Planarity means an injective placement in the Euclidean plane with arbitrary
simple continuous edge arcs meeting only at shared endpoints. The geometric
obstructions are proved from that definition. No Euler inequality, forbidden
minor characterization, or straight-line realization is a premise here.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical Pointwise
namespace GraphicalZonotopes
variable {V : Type*} [Fintype V] [LinearOrder V]

/-- On distinct actual four-cliques, the formal overlap threshold is
exactly the paper's adjacency relation of sharing a triangle. -/
theorem TetrahedronComponents.adj_iff_shared_triangle (G : SimpleGraph V)
    (C D : {C : Finset V // C ∈ tetrahedra G}) :
    (tetrahedronGraph (tetrahedra G)).Adj C D ↔ (C.1 ∩ D.1).card = 3 := by
  have hC : C.1.card = 4 := (Finset.mem_filter.mp C.2).2.1
  have hD : D.1.card = 4 := (Finset.mem_filter.mp D.2).2.1
  constructor
  · intro h
    have hle := Finset.card_le_card (Finset.inter_subset_left : C.1 ∩ D.1 ⊆ C.1)
    have hne : (C.1 ∩ D.1).card ≠ 4 := by
      intro he
      have hleft : C.1 ∩ D.1 = C.1 := Finset.eq_of_subset_of_card_le
        Finset.inter_subset_left (by omega)
      have hright : C.1 ∩ D.1 = D.1 := Finset.eq_of_subset_of_card_le
        Finset.inter_subset_right (by omega)
      exact h.1 (Subtype.ext (hleft.symm.trans hright))
    have hlo := h.2
    omega
  · intro h
    refine ⟨?_,by omega⟩
    intro he
    have hv := congrArg Subtype.val he
    rw [hv,Finset.inter_self,hD] at h
    omega

theorem HasPlaneDrawing.maximum_dimension {G : SimpleGraph V}
    (hG : HasPlaneDrawing G) :
    maximumIndecomposableDimension G = planarComponentDimension G := by
  have hs := hG.triangle_apex_separated
  exact hs.piecewise_maximum.trans
    (planarComponentDimension_eq_partialThreeTreeDimension hs hG.admissible).symm

theorem HasPlaneDrawing.full_polytopal_iff_threeTree {G : SimpleGraph V}
    (hG : HasPlaneDrawing G) (hn : 4 ≤ Fintype.card V) :
    (∃ Q : Set (V → ℝ),IsFinitePolytope Q ∧
      PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G)) ↔ IsThreeTree G := by
  rw [← supportsFullIndecomposable_iff_polytopal_weak]
  exact hG.triangle_apex_separated.supports_full_iff_threeTree hn hG.admissible

theorem HasPlaneDrawing.isStackedTriangulation_iff_threeTree {G : SimpleGraph V}
    (hG : HasPlaneDrawing G) : IsStackedTriangulation G ↔ IsThreeTree G := by
  rw [isStackedTriangulation_iff]
  exact ⟨fun h => h.1,fun h => ⟨h,hG.triangleMultiplicity_le_two⟩⟩

theorem HasPlaneDrawing.lattice_full_witness {G : SimpleGraph V}
    (hG : HasPlaneDrawing G) (ht : IsThreeTree G) :
    ∃ Q : Set (V → ℝ),LatticePolytope Q ∧
      PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧ actualDirectionGraph Q = G := by
  obtain ⟨f,hf,hfi,hfd,hfa,hfg⟩ := admissible_threeTree_witness_fintype ht hG.admissible
  have hQ := hfi.basePolytope hf.1.1 hf.2.1
  have hw := (isWeakMinkowskiSummand_graphical_iff hf.1.1 hf.2.1).mpr hfg
  exact ⟨basePolytope f,hQ,
    (weakSummand_indecomposable_iff_polytopal hQ.finitePolytope hw).mp
      hf.minkowskiIndecomposable,hfd,hw,hfa⟩

theorem HasPlaneDrawing.full_lattice_spectrum {G : SimpleGraph V}
    (hG : HasPlaneDrawing G) (d : ℕ) (hd : 1 ≤ d)
    (hmax : d ≤ planarComponentDimension G) :
    ∃ Q : Set (V → ℝ),LatticePolytope Q ∧
      PolytopalMinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
      Module.finrank ℝ (vectorSpan ℝ Q) = d := by
  obtain ⟨Q,hQ,hi,hw,hD⟩ := hG.triangle_apex_separated.full_dimension_spectrum
    d hd (by rwa [hG.maximum_dimension])
  exact ⟨Q,hQ,(weakSummand_indecomposable_iff_polytopal hQ.finitePolytope hw).mp hi,hw,hD⟩

/-- Corollary 6.4 for every finite simple planar graph on at least four
vertices. The chosen vertex order is internal coordinate infrastructure,
not an additional assumption on the graph or its drawing. -/
theorem paper_corollary_6_4 {W : Type*} [Fintype W] :
    letI : LinearOrder W := Separator.finiteVertexOrder W;
    ∀ G : SimpleGraph W,HasPlaneDrawing G → 4 ≤ Fintype.card W →
      ((∃ Q : Set (W → ℝ),IsFinitePolytope Q ∧
        PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
        IsWeakMinkowskiSummand Q (graphicalZonotope G)) ↔ IsThreeTree G) := by
  letI : LinearOrder W := Separator.finiteVertexOrder W
  exact fun G hG hn => hG.full_polytopal_iff_threeTree hn

/-- The same classification with the paper's explicit stacked-triangulation
formulation: tetrahedral boundary faces are built by repeated one-to-three
face replacements, as certified by the independent boundary dictionary. -/
theorem paper_corollary_6_4_stacked {W : Type*} [Fintype W] :
    letI : LinearOrder W := Separator.finiteVertexOrder W;
    ∀ G : SimpleGraph W,HasPlaneDrawing G → 4 ≤ Fintype.card W →
      ((∃ Q : Set (W → ℝ),IsFinitePolytope Q ∧
        PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
        IsWeakMinkowskiSummand Q (graphicalZonotope G)) ↔ IsStackedTriangulation G) := by
  letI : LinearOrder W := Separator.finiteVertexOrder W
  intro G hG hn
  exact (hG.full_polytopal_iff_threeTree hn).trans hG.isStackedTriangulation_iff_threeTree.symm

/-- The lattice witness in the converse of the planar classification has
exactly the original graph as its actual exposed-edge direction graph. -/
theorem planar_threeTree_lattice_witness_finite {W : Type*} [Fintype W] :
    letI : LinearOrder W := Separator.finiteVertexOrder W;
    ∀ G : SimpleGraph W,HasPlaneDrawing G → IsThreeTree G →
      ∃ Q : Set (W → ℝ),LatticePolytope Q ∧
        PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
        IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧ actualDirectionGraph Q = G := by
  letI : LinearOrder W := Separator.finiteVertexOrder W
  exact fun G hG ht => hG.lattice_full_witness ht

/-- Corollary 6.5 with the literal maximum over the connected components of
the graph of all tetrahedra, and every positive dimension through that maximum.
The fallback values are exactly two for triangles, one for edges, and zero
for edgeless graphs. Both the supremum and witnesses use ordinary polytopal
Minkowski indecomposability. -/
theorem paper_corollary_6_5 {W : Type*} [Fintype W] :
    letI : LinearOrder W := Separator.finiteVertexOrder W;
    ∀ G : SimpleGraph W,HasPlaneDrawing G →
      (sSup {d : ℕ | ∃ Q : Set (W → ℝ),IsFinitePolytope Q ∧
        PolytopalMinkowskiIndecomposable Q ∧
        IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
        Module.finrank ℝ (vectorSpan ℝ Q) = d}) = planarComponentDimension G ∧
      ∀ d : ℕ,1 ≤ d → d ≤ planarComponentDimension G →
        ∃ Q : Set (W → ℝ),LatticePolytope Q ∧
          PolytopalMinkowskiIndecomposable Q ∧
          IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
          Module.finrank ℝ (vectorSpan ℝ Q) = d := by
  letI : LinearOrder W := Separator.finiteVertexOrder W
  intro G hG
  refine ⟨?_,fun d hd hm => hG.full_lattice_spectrum d hd hm⟩
  rw [← maximumIndecomposableDimension_eq_polytopal_supremum]
  exact hG.maximum_dimension

end GraphicalZonotopes

end
end
end BundlePart436

section BundlePart437
/- Source: Papers/GraphicalZonotopes/TriangleFreeSeparatorPaper.lean -/






@[expose] public section
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset

/-- The literal connectivity conclusion includes nonemptiness of every
remaining vertex set. The cardinality hypothesis supplies that fact. -/
theorem SupportsFullIndecomposable.delete_lt_three_connected {n : ℕ} (hn : 4 ≤ n)
    {G : SimpleGraph (Fin n)} (hG : SupportsFullIndecomposable G)
    (B : Finset (Fin n)) (hB : B.card < 3) :
    (G.induce ((B : Set (Fin n))ᶜ)).Connected := by
  classical
  have hout : ∃ v : Fin n,v ∉ B := by
    by_contra h
    push_neg at h
    have he : B = univ := by
      ext v
      simp only [mem_univ,iff_true]
      exact h v
    have hc := congrArg Finset.card he
    simp only [card_univ,Fintype.card_fin] at hc
    omega
  obtain ⟨v,hv⟩ := hout
  letI : Nonempty {w : Fin n // w ∈ (B : Set (Fin n))ᶜ} := ⟨⟨v,hv⟩⟩
  exact ⟨hG.delete_lt_three_preconnected hn B hB⟩

/-- Corollary 5.2 with ordinary polytopal indecomposability and the full
three-vertex-connectivity conclusion, expressed directly by all deletions. -/
theorem paper_corollary_5_2 {n : ℕ} (hn : 4 ≤ n) (G : SimpleGraph (Fin n))
    (hG : ∃ Q : Set (Fin n → ℝ),IsFinitePolytope Q ∧
      PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G)) :
    (∀ B : Finset (Fin n),
      2 ≤ Nat.card ((G.induce ((B : Set (Fin n))ᶜ)).ConnectedComponent) →
      ∃ T : Finset (Fin n),T ⊆ B ∧ T.card = 3 ∧ G.IsClique T) ∧
    (∀ B : Finset (Fin n),B.card < 3 →
      (G.induce ((B : Set (Fin n))ᶜ)).Connected) := by
  have hs := (supportsFullIndecomposable_iff_polytopal_weak G).mpr hG
  exact ⟨fun B hB => hs.separator_contains_triangle (by omega) B hB,
    fun B hB => hs.delete_lt_three_connected hn B hB⟩

/-- The printed extension of Corollary 5.2 to the actual direction graph of
any full-dimensional indecomposable generalized permutahedron. -/
theorem full_generalized_permutahedron_triangle_separators {n : ℕ} (hn : 4 ≤ n)
    {Q : Set (Fin n → ℝ)} (hQ : IsGeneralizedPermutahedron Q)
    (hi : PolytopalMinkowskiIndecomposable Q) (hd : FullDimension Q) :
    (∀ B : Finset (Fin n),
      2 ≤ Nat.card (((actualDirectionGraph Q).induce
        ((B : Set (Fin n))ᶜ)).ConnectedComponent) →
      ∃ T : Finset (Fin n),T ⊆ B ∧ T.card = 3 ∧ (actualDirectionGraph Q).IsClique T) ∧
    (∀ B : Finset (Fin n),B.card < 3 →
      ((actualDirectionGraph Q).induce ((B : Set (Fin n))ᶜ)).Connected) := by
  have hw : IsWeakMinkowskiSummand Q (graphicalZonotope (actualDirectionGraph Q)) := by
    obtain ⟨z,hzn,hzs,rfl⟩ := hQ
    exact (isWeakMinkowskiSummand_graphical_iff hzn hzs).mpr
      (graphical_actualDirectionGraph hzn hzs)
  exact paper_corollary_5_2 hn (actualDirectionGraph Q) ⟨Q,hQ.finitePolytope,hi,hd,hw⟩

end GraphicalZonotopes

end
end
end BundlePart437

section BundlePart438
/- Source: Papers/GraphicalZonotopes/UnitActiveSupport.lean -/








@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical Pointwise BigOperators
namespace GraphicalZonotopes
namespace UnitLatticeGeometry
open Finset RefinedTriangleComponents FourPartGraphRecognition

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- The unit-summand geometry does not need ambient full dimension. In every
actual dimension at least three it produces the Cartesian tetrahedral family
on exactly the active coordinates. -/
theorem active_coefficient_model {G : SimpleGraph V} (hG : G.CliqueFree 5)
    {Q : Set (V → ℝ)} (hQ : LatticePolytope Q)
    (hi : PolytopalMinkowskiIndecomposable Q)
    (hd : 3 ≤ Module.finrank ℝ (vectorSpan ℝ Q))
    (hsum : IsMinkowskiSummand Q (graphicalZonotope G)) :
    ∃ (z : SetFunction V) (A : Fin 4 → Finset V),
      ExtremeSupermodular z ∧
      (∀ i, (A i).card = 1 ∨ (A i).card = 2) ∧
      (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧
      ProductFamily (family (mobius z)) A ∧
      actualDirectionGraph Q = unionGraph (family (mobius z)) ∧
      DependsOn z ((family (mobius z)).biUnion id) ∧
      Module.finrank ℝ (vectorSpan ℝ (basePolytope z)) =
        Module.finrank ℝ (vectorSpan ℝ Q) := by
  obtain ⟨R,hR,hcR,hnR,he⟩ := hsum
  have he' : Q + R = (1 : ℝ) • graphicalZonotope G := by simpa using he
  obtain ⟨hfn,hfs,hbody,hgraph,hbound⟩ := actual_summand_lowerSupport
    hQ.compact hQ.convex hi.1 hR hcR hnR (by norm_num : (0 : ℝ) ≤ 1) he'
  let f := lowerSupport Q
  let z := normalize f
  have hzn : TranslationNormalized z := normalize_translationNormalized hfn
  have hzs : Supermodular z := hfs.normalize
  have hzi : IntegerValued z := (hQ.lowerSupport_integerValued hi.1).normalize
  have hzg : Graphical G z := by
    intro u v huv hnon S hu hv
    rw [delta_normalize f huv hu hv]
    exact hgraph u v huv hnon S hu hv
  have hdim : Module.finrank ℝ (vectorSpan ℝ (basePolytope z)) =
      Module.finrank ℝ (vectorSpan ℝ Q) := by
    rw [vectorSpan_basePolytope_normalize,← hbody]
  have hdim3 : 3 ≤ Module.finrank ℝ (vectorSpan ℝ (basePolytope z)) := by
    rw [hdim]
    exact hd
  have hne : z ≠ 0 := by
    intro hz
    rw [hz,basePolytope_zero] at hdim3
    have hspan : vectorSpan ℝ ({0} : Set (V → ℝ)) =
        (⊥ : Submodule ℝ (V → ℝ)) := _root_.vectorSpan_singleton ℝ (0 : V → ℝ)
    rw [hspan,_root_.finrank_bot] at hdim3
    omega
  have hgp : IsGeneralizedPermutahedron Q := ⟨f,hfn,hfs,hbody⟩
  have hic : MinkowskiIndecomposable Q :=
    (minkowskiIndecomposable_iff_polytopal hgp).mpr hi
  have hext : ExtremeSupermodular z := by
    apply MinkowskiIndecomposable.extremeSupermodular_normalize hfn hfs hne
    rwa [← hbody]
  obtain ⟨hF,hconn,hactual,hdep⟩ :=
    refined_support_of_dimension_ge_three hG hext hzg hdim3
  have hsupported : CliqueSupported G (mobius z) :=
    (mobius_cliqueSupported_iff G z).mpr ⟨hzn,hzg⟩
  have hboolean : ∀ u v : V, u ≠ v → ∀ S : Finset V, u ∉ S → v ∉ S →
      delta (zeta (mobius z)) u v S = 0 ∨ delta (zeta (mobius z)) u v S = 1 := by
    intro u v huv S hu hv
    rw [zeta_mobius]
    by_cases hadj : G.Adj u v
    · apply integer_between_zero_one (integer_delta hzi u v S)
        (hzs.elemental u v huv S hu hv)
      rw [delta_normalize f huv hu hv]
      exact hbound u v huv hadj S hu hv
    · exact Or.inl (hzg u v huv hadj S hu hv)
  have hmem : ∀ D, D ∈ family (mobius z) ↔ D.card = 4 ∧ mobius z D ≠ 0 :=
    mem_family _
  obtain ⟨hthin,hsquare⟩ := UnitFamilyStructure.structure_of_boolean
    hG hsupported hboolean hmem
  obtain ⟨A,hsize,hdis,hprod⟩ := FourPartCompletion.cartesian_completion
    (family (mobius z)) (fun D hD => ((hmem D).mp hD).1) hF hconn hthin hsquare
  refine ⟨z,A,hext,hsize,hdis,hprod,?_,hdep,hdim⟩
  rw [actualDirectionGraph_normalize,← hbody] at hactual
  exact hactual

end UnitLatticeGeometry
end GraphicalZonotopes

end
end
end BundlePart438

section BundlePart439
/- Source: Papers/GraphicalZonotopes/FourPartActiveSupport.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.FourPartGraphRecognition
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A Cartesian tetrahedron family gives the literal complete four-partite
graph on its active vertices. No coverage of the ambient vertex type is
assumed: every vertex outside the four displayed parts is isolated. -/
theorem product_unionGraph_adj_iff {F : Finset (Finset V)} {A : Fin 4 → Finset V}
    (hne : ∀ i,(A i).Nonempty) (hdis : ∀ i j,i ≠ j → Disjoint (A i) (A j))
    (hprod : ProductFamily F A) (u v : V) :
    (unionGraph F).Adj u v ↔ ∃ i j : Fin 4,i ≠ j ∧ u ∈ A i ∧ v ∈ A j := by
  constructor
  · rintro ⟨huv,D,hD,hu,hv⟩
    obtain ⟨w,hw,rfl⟩ := (hprod D).mp hD
    obtain ⟨i,_,hi⟩ := mem_image.mp hu
    obtain ⟨j,_,hj⟩ := mem_image.mp hv
    refine ⟨i,j,?_,hi ▸ hw i,hj ▸ hw j⟩
    intro hij
    subst j
    exact huv (hi.symm.trans hj)
  · rintro ⟨i,j,hij,hu,hv⟩
    let w : Fin 4 → V := fun k =>
      if k = i then u else if k = j then v else Classical.choose (hne k)
    have hw : ∀ k,w k ∈ A k := by
      intro k
      dsimp [w]
      split_ifs with hki hkj
      · simpa only [hki] using hu
      · simpa only [hkj] using hv
      · exact Classical.choose_spec (hne k)
    have hwi : w i = u := by simp [w]
    have hwj : w j = v := by simp [w,Ne.symm hij]
    have huv : u ≠ v := by
      intro he
      exact Finset.disjoint_left.mp (hdis i j hij) hu (he.symm ▸ hv)
    refine ⟨huv,univ.image w,(hprod _).mpr ⟨w,hw,rfl⟩,?_,?_⟩
    · exact mem_image.mpr ⟨i,mem_univ _,hwi⟩
    · exact mem_image.mpr ⟨j,mem_univ _,hwj⟩

/-- The nonisolated vertices are exactly the union of the four parts. This
is the precise dictionary needed when the ambient polytope is not full
dimensional and unused coordinates remain in the ambient type. -/
theorem product_unionGraph_support {F : Finset (Finset V)} {A : Fin 4 → Finset V}
    (hne : ∀ i,(A i).Nonempty) (hdis : ∀ i j,i ≠ j → Disjoint (A i) (A j))
    (hprod : ProductFamily F A) :
    (unionGraph F).support = ((univ.biUnion A : Finset V) : Set V) := by
  ext u
  rw [SimpleGraph.mem_support]
  constructor
  · rintro ⟨v,huv⟩
    obtain ⟨i,j,hij,hu,hv⟩ := (product_unionGraph_adj_iff hne hdis hprod u v).mp huv
    exact mem_biUnion.mpr ⟨i,mem_univ _,hu⟩
  · intro hu
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hu
    obtain ⟨j,hji⟩ := exists_ne i
    obtain ⟨v,hv⟩ := hne j
    exact ⟨v,(product_unionGraph_adj_iff hne hdis hprod u v).mpr ⟨i,j,Ne.symm hji,hi,hv⟩⟩

end GraphicalZonotopes.FourPartGraphRecognition

end
end
end BundlePart439

section BundlePart440
/- Source: Papers/GraphicalZonotopes/UnitActiveClassification.lean -/






/-! # Unit-lattice direction supports without ambient full dimension

This is the active-coordinate formulation stated in the introduction. The
polytope may use only part of the ambient graph. The conclusion classifies its
actual edge directions, including every unused coordinate as an isolated
vertex, rather than imposing full dimension or ambient graph coverage.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical Pointwise BigOperators
namespace GraphicalZonotopes
open Finset RefinedTriangleComponents FourPartGraphRecognition

/-- Every indecomposable lattice summand of an unscaled K5-free graphical
zonotope, in any actual dimension at least three, has a complete four-partite
actual direction graph on its active coordinates. Each part has one or two
vertices. In particular there are at most eight active coordinates and the
affine dimension is at most seven. The finite vertex order is chosen
internally and is not an added hypothesis. -/
theorem unit_lattice_active_classification_finite {V : Type*} [Fintype V] :
    letI : LinearOrder V := Separator.finiteVertexOrder V;
    ∀ (G : SimpleGraph V), G.CliqueFree 5 →
      ∀ (Q : Set (V → ℝ)), LatticePolytope Q →
      PolytopalMinkowskiIndecomposable Q →
      3 ≤ Module.finrank ℝ (vectorSpan ℝ Q) →
      IsMinkowskiSummand Q (graphicalZonotope G) →
      ∃ A : Fin 4 → Finset V,
        (∀ i, (A i).card = 1 ∨ (A i).card = 2) ∧
        (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧
        (∀ u v, (actualDirectionGraph Q).Adj u v ↔
          ∃ i j : Fin 4, i ≠ j ∧ u ∈ A i ∧ v ∈ A j) ∧
        (actualDirectionGraph Q).support =
          ((univ.biUnion A : Finset V) : Set V) ∧
        (actualDirectionGraph Q).support.ncard ≤ 8 ∧
        Module.finrank ℝ (vectorSpan ℝ Q) ≤ 7 := by
  letI : LinearOrder V := Separator.finiteVertexOrder V
  intro G hG Q hQ hi hd hsum
  obtain ⟨z,A,hz,hsize,hdis,hprod,hactual,hdep,hdim⟩ :=
    UnitLatticeGeometry.active_coefficient_model hG hQ hi hd hsum
  have hne : ∀ i, (A i).Nonempty := by
    intro i
    apply card_pos.mp
    rcases hsize i with h | h <;> omega
  have hadj : ∀ u v, (actualDirectionGraph Q).Adj u v ↔
      ∃ i j : Fin 4, i ≠ j ∧ u ∈ A i ∧ v ∈ A j := by
    intro u v
    rw [hactual]
    exact product_unionGraph_adj_iff hne hdis hprod u v
  have hsupport : (actualDirectionGraph Q).support =
      ((univ.biUnion A : Finset V) : Set V) := by
    rw [hactual]
    exact product_unionGraph_support hne hdis hprod
  have hU : (univ.biUnion A).card ≤ 8 := by
    apply card_biUnion_le.trans
    calc
      (∑ i : Fin 4, (A i).card) ≤ ∑ _i : Fin 4, 2 := by
        apply sum_le_sum
        intro i _
        rcases hsize i with h | h <;> omega
      _ = 8 := by norm_num
  have hFsub : (family (mobius z)).biUnion id ⊆ univ.biUnion A := by
    intro v hv
    obtain ⟨D,hD,hvD⟩ := mem_biUnion.mp hv
    obtain ⟨w,hw,rfl⟩ := (hprod D).mp hD
    obtain ⟨i,_,hiv⟩ := mem_image.mp hvD
    exact mem_biUnion.mpr ⟨i,mem_univ _,hiv ▸ hw i⟩
  have hFcard := (card_le_card hFsub).trans hU
  have hdimle := finrank_vectorSpan_le_support hz.1 hz.2.1 hdep
  rw [hdim] at hdimle
  refine ⟨A,hsize,hdis,hadj,hsupport,?_,by omega⟩
  rw [hsupport,Set.ncard_coe_finset]
  exact hU

end GraphicalZonotopes

end
end
end BundlePart440

section BundlePart441
/- Source: Papers/GraphicalZonotopes/PlanarStraightLineAdapter.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical Graph
namespace GraphicalZonotopes

/-- A literal noncrossing straight-line drawing gives an ordinary drawing by
simple continuous arcs. The two real-plane representations are related by an
explicit continuous linear equivalence. -/
theorem HasPlaneStraightLineDrawing.hasPlaneDrawing {V : Type*} {G : SimpleGraph V}
    (hG : HasPlaneStraightLineDrawing G) : HasPlaneDrawing G := by
  obtain ⟨p,hp,hvertex,hcross⟩ := hG
  let L : (Fin 2 → ℝ) ≃L[ℝ] Schoenflies.Plane := (EuclideanSpace.equiv (Fin 2) ℝ).symm
  let q : V → Schoenflies.Plane := fun v => L (p v)
  have hq : Function.Injective q := L.injective.comp hp
  let drawing : Sym2 V → ℝ → Schoenflies.Plane := fun e t =>
    L (AffineMap.lineMap (p e.out.1) (p e.out.2) t)
  have hadj : ∀ e ∈ G.edgeSet,G.Adj e.out.1 e.out.2 := by
    intro e he
    apply G.mem_edgeSet.mp
    rwa [Sym2.mk_fst_out_snd_out]
  have hlink : ∀ e ∈ G.edgeSet,(PlaneDrawing.planeGraph G q).IsLink
      e (q e.out.1) (q e.out.2) := by
    intro e he
    exact (PlaneDrawing.planeGraph_isLink G q hq _ _ _).mpr
      ⟨(Sym2.mk_fst_out_snd_out e).symm,hadj e he⟩
  have himage : ∀ e,Graph.edgeArc drawing e =
      L '' segment ℝ (p e.out.1) (p e.out.2) := by
    intro e
    rw [segment_eq_image_lineMap,Set.image_image]
    rfl
  have hpull : ∀ e (z : Fin 2 → ℝ),L z ∈ Graph.edgeArc drawing e →
      z ∈ segment ℝ (p e.out.1) (p e.out.2) := by
    intro e z hz
    rw [himage] at hz
    obtain ⟨w,hw,he⟩ := hz
    have hzw : w = z := L.injective he
    exact hzw ▸ hw
  refine ⟨q,hq,drawing,?_⟩
  constructor
  · intro e he
    have heG : e ∈ G.edgeSet := he
    have hcont : Continuous (drawing e) := L.continuous.comp AffineMap.lineMap_continuous
    have hinj : Function.Injective (drawing e) := L.injective.comp
      (AffineMap.lineMap_injective ℝ (fun h => (hadj e heG).ne (hp h)))
    refine ⟨hcont.continuousOn,hinj.injOn,?_⟩
    simpa only [drawing,AffineMap.lineMap_apply_zero,AffineMap.lineMap_apply_one] using hlink e heG
  · intro e x y v hl hv hve
    have heG : e ∈ G.edgeSet := hl.edge_mem
    rw [PlaneDrawing.planeGraph_vertexSet] at hv
    obtain ⟨w,rfl⟩ := hv
    have hseg : p w ∈ segment ℝ (p e.out.1) (p e.out.2) := hpull e (p w) hve
    have hw : w = e.out.1 ∨ w = e.out.2 := by
      by_contra hh
      have h₁ : w ≠ e.out.1 := fun he => hh (Or.inl he)
      have h₂ : w ≠ e.out.2 := fun he => hh (Or.inr he)
      exact hvertex _ _ _ (hadj e heG) h₁ h₂ hseg
    have hwq : q w = q e.out.1 ∨ q w = q e.out.2 :=
      hw.imp (congrArg q) (congrArg q)
    rcases hl.eq_and_eq_or_eq_and_eq (hlink e heG) with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact hwq
    · exact hwq.symm
  · intro e f he hf hef x hxe hxf
    have heG : e ∈ G.edgeSet := he
    have hfG : f ∈ G.edgeSet := hf
    rw [himage] at hxe
    obtain ⟨z,hz,hzx⟩ := hxe
    have hzf : z ∈ segment ℝ (p f.out.1) (p f.out.2) := by
      apply hpull f z
      rwa [hzx]
    rcases hcross _ _ _ _ (hadj e heG) (hadj f hfG) z hz hzf with h | h | h
    · obtain ⟨hu,hv⟩ := h
      apply False.elim
      apply hef
      calc
        e = s(e.out.1,e.out.2) := (Sym2.mk_fst_out_snd_out e).symm
        _ = s(f.out.1,f.out.2) := by rw [hu,hv]
        _ = f := Sym2.mk_fst_out_snd_out f
    · obtain ⟨hu,hv⟩ := h
      apply False.elim
      apply hef
      calc
        e = s(e.out.1,e.out.2) := (Sym2.mk_fst_out_snd_out e).symm
        _ = s(f.out.2,f.out.1) := by rw [hu,hv]
        _ = s(f.out.1,f.out.2) := Sym2.eq_swap
        _ = f := Sym2.mk_fst_out_snd_out f
    · obtain ⟨w,hwe,hwf,hzw⟩ := h
      have hxq : x = q w := hzx.symm.trans (congrArg L hzw)
      rw [hxq]
      refine ⟨?_,?_,?_⟩
      · rw [PlaneDrawing.planeGraph_vertexSet]
        exact ⟨w,rfl⟩
      · rcases hwe with hew | hew
        · rw [hew]
          exact (hlink e heG).inc_left
        · rw [hew]
          exact (hlink e heG).inc_right
      · rcases hwf with hfw | hfw
        · rw [hfw]
          exact (hlink f hfG).inc_left
        · rw [hfw]
          exact (hlink f hfG).inc_right

/-- The previously checked explicit straight-line sharpness family is planar
under exactly the same ordinary-arc definition used in the planar corollaries. -/
theorem PathDrawing.path_hasPlaneDrawing (n : ℕ) : HasPlaneDrawing (Path.graph n) :=
  (PathDrawing.path_plane_drawing n).hasPlaneDrawing

end GraphicalZonotopes

end
end
end BundlePart441

section BundlePart442
/- Source: Papers/GraphicalZonotopes/PartialThreeTreeIncidenceForest.lean -/






@[expose] public section
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem triangles_mono_graph {G H : SimpleGraph V} (h : G ≤ H) :
    triangles G ⊆ triangles H := by
  intro T hT
  obtain ⟨hc,hcl⟩ := mem_triangles.mp hT
  exact mem_triangles.mpr ⟨hc,fun u hu v hv huv => h (hcl hu hv huv)⟩

/-- The inclusion of a graph into a supergraph induces an actual injective
map of all its tetrahedron and triangle incidence nodes. -/
def incidenceHomOfLE {G H : SimpleGraph V} (h : G ≤ H) :
    cliqueTriangleIncidence G →g cliqueTriangleIncidence H where
  toFun := Sum.map (fun C => ⟨C.1,tetrahedra_mono h C.2⟩)
    (fun T => ⟨T.1,triangles_mono_graph h T.2⟩)
  map_rel' := by
    intro x y hxy
    cases x <;> cases y <;> exact hxy

theorem incidenceHomOfLE_injective {G H : SimpleGraph V} (h : G ≤ H) :
    Function.Injective (incidenceHomOfLE h) := by
  apply Sum.map_injective.mpr
  constructor
  · intro C D he
    exact Subtype.ext (congrArg (fun E : {E : Finset V // E ∈ tetrahedra H} => E.1) he)
  · intro C D he
    exact Subtype.ext (congrArg (fun E : {E : Finset V // E ∈ triangles H} => E.1) he)

/-- The structural assertion in Corollary 6.8: the intrinsic incidence graph
of every partial three-tree is a forest, including all small-vertex cases.
No tree completion is part of the resulting graph or of its definition. -/
theorem IsPartialThreeTree.incidence_isAcyclic {G : SimpleGraph V}
    (hG : IsPartialThreeTree G) : (cliqueTriangleIncidence G).IsAcyclic := by
  rcases hG with hsmall | ⟨H,hH,hGH⟩
  · have hno : ∀ C : {C : Finset V // C ∈ tetrahedra G},False := by
      intro C
      have hfour : C.1.card = 4 := (mem_filter.mp C.2).2.1
      have hle := card_le_card (subset_univ C.1)
      rw [card_univ,hfour] at hle
      omega
    have hbot : cliqueTriangleIncidence G = ⊥ := by
      ext x y
      cases x with
      | inl C => exact (hno C).elim
      | inr T =>
        cases y with
        | inl C => exact (hno C).elim
        | inr U => rfl
    rw [hbot]
    exact SimpleGraph.isAcyclic_bot
  · exact hH.incidence_isTree.isAcyclic.comap
      (incidenceHomOfLE hGH) (incidenceHomOfLE_injective hGH)

end GraphicalZonotopes

end
end
end BundlePart442
