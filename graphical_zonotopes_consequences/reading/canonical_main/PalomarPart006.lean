module

public import canonical_main.PalomarPart005
import all canonical_main.PalomarPart005
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

section BundlePart329
/- Source: Papers/GraphicalZonotopes/SaturatedBookPrincipal.lean -/









/-! # The minimum number of directions in a saturated clique book

This is the literal quantified lower bound and lattice equality witness of
Theorem 7.12.  Both use actual edges of actual convex polytopes.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.SaturatedDirections
open Finset
open scoped BigOperators Pointwise
attribute [local instance] Classical.propDecidable

theorem small_spoke_attainment (s : ℕ) (hs : s = 2 ∨ s = 3) :
    ∃ f : SetFunction (Fin s ⊕ Fin (cliqueCapacity s)),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s (cliqueCapacity s)) f ∧ FullDimension (basePolytope f) ∧
      LatticePolytope (basePolytope f) ∧
      ∀ a : Fin s,(univ.filter (fun j : Fin (cliqueCapacity s) =>
        ActualRootEdge (basePolytope f) (Sum.inl a) (Sum.inr j))).card =
          saturatedHubNeighbors s := by
  have hs2 : 2 ≤ s := by omega
  have hk : 1 ≤ cliqueCapacity s := by
    rcases hs with rfl | rfl <;> norm_num [cliqueCapacity,Nat.choose]
  have hchoose : cliqueCapacity s ≤ s.choose 2 := by
    rcases hs with rfl | rfl <;> norm_num [cliqueCapacity,Nat.choose]
  have hUs : saturatedHubNeighbors s = cliqueCapacity s := by
    rcases hs with rfl | rfl <;> norm_num [saturatedHubNeighbors,cliqueCapacity,Nat.choose]
  obtain ⟨f,hn,hi,he,hG,hd,hm,hl,R,hR,hRn,hQR⟩ :=
    BooleanModule.small_count_lattice_books s (cliqueCapacity s) hs2 hk hchoose
  have hfinite : IsFinitePolytope (basePolytope f) :=
    IsGeneralizedPermutahedron.finitePolytope ⟨f,hn.1,he.2.1,rfl⟩
  have hweak := (isWeakMinkowskiSummand_graphical_iff hn.1 he.2.1).mpr hG
  obtain ⟨hsub,hh,hsp⟩ := actual_hub_spoke_lower hs2 hfinite hm hd hweak
  refine ⟨f,hn,hi,he,hG,hd,hl,?_⟩
  intro a
  apply le_antisymm
  · rw [hUs]
    exact (card_filter_le _ _).trans (by simp)
  · exact hsp a

theorem all_spoke_attainment (s : ℕ) (hs : 2 ≤ s) :
    ∃ f : SetFunction (Fin s ⊕ Fin (cliqueCapacity s)),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s (cliqueCapacity s)) f ∧ FullDimension (basePolytope f) ∧
      LatticePolytope (basePolytope f) ∧
      ∀ a : Fin s,(univ.filter (fun j : Fin (cliqueCapacity s) =>
        ActualRootEdge (basePolytope f) (Sum.inl a) (Sum.inr j))).card =
          saturatedHubNeighbors s := by
  by_cases hs5 : 5 ≤ s
  · exact BooleanModule.Saturated.spoke_attainment s hs5
  by_cases hs4 : s = 4
  · subst s
    have hc : cliqueCapacity 4 = 14 := by norm_num [cliqueCapacity,Nat.choose]
    have hu : saturatedHubNeighbors 4 = 12 := by
      norm_num [saturatedHubNeighbors,cliqueCapacity,Nat.choose]
    rw [hc,hu]
    exact BooleanModule.SaturatedFour.spoke_attainment
  · exact small_spoke_attainment s (by omega)

/-- The exact minimum is attained by a lattice polytope in every allowed
hub size, with equality at every individual hub. -/
theorem lattice_equality (s : ℕ) (hs : 2 ≤ s) :
    ∃ Q : Set ((Fin s ⊕ Fin (cliqueCapacity s)) → ℝ),
      LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧ FullDimension Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (cliqueBook s (cliqueCapacity s))) ∧
      directionCount Q = s.choose 2 + s*saturatedHubNeighbors s ∧
      ∀ a : Fin s,(univ.filter (fun j : Fin (cliqueCapacity s) =>
        ActualRootEdge Q (Sum.inl a) (Sum.inr j))).card = saturatedHubNeighbors s := by
  obtain ⟨f,hn,hi,he,hG,hd,hl,hsp⟩ := all_spoke_attainment s hs
  have hfinite : IsFinitePolytope (basePolytope f) :=
    IsGeneralizedPermutahedron.finitePolytope ⟨f,hn.1,he.2.1,rfl⟩
  have hm := he.minkowskiIndecomposable
  have hw := (isWeakMinkowskiSummand_graphical_iff hn.1 he.2.1).mpr hG
  obtain ⟨hsub,hh,_⟩ := actual_hub_spoke_lower hs hfinite hm hd hw
  exact ⟨basePolytope f,hl,hm,hd,hw,
    BookEdges.edge_count_eq (actualDirectionGraph (basePolytope f)) hsub hh
      (saturatedHubNeighbors s) hsp,hsp⟩

/-- Theorem 7.12 of the paper, with the universal lower bound and the
unconditional lattice equality witness in one statement. -/
theorem paper_theorem_7_12 :
    ∀ s : ℕ,2 ≤ s →
      (∀ Q : Set ((Fin s ⊕ Fin (cliqueCapacity s)) → ℝ),
        IsFinitePolytope Q → MinkowskiIndecomposable Q → FullDimension Q →
        IsWeakMinkowskiSummand Q (graphicalZonotope (cliqueBook s (cliqueCapacity s))) →
        s.choose 2 + s*saturatedHubNeighbors s ≤ directionCount Q ∧
        (3 ≤ s → ∀ i j : Fin s,i ≠ j → ActualRootEdge Q (Sum.inl i) (Sum.inl j)) ∧
        ∀ i : Fin s,saturatedHubNeighbors s ≤
          (univ.filter (fun j : Fin (cliqueCapacity s) =>
            ActualRootEdge Q (Sum.inl i) (Sum.inr j))).card) ∧
      ∃ Q : Set ((Fin s ⊕ Fin (cliqueCapacity s)) → ℝ),
        LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧ FullDimension Q ∧
        IsWeakMinkowskiSummand Q (graphicalZonotope (cliqueBook s (cliqueCapacity s))) ∧
        directionCount Q = s.choose 2 + s*saturatedHubNeighbors s ∧
        ∀ i : Fin s,(univ.filter (fun j : Fin (cliqueCapacity s) =>
          ActualRootEdge Q (Sum.inl i) (Sum.inr j))).card = saturatedHubNeighbors s := by
  intro s hs
  refine ⟨?_,lattice_equality s hs⟩
  intro Q hQ hi hd hw
  obtain ⟨hsub,hh,hsp⟩ := actual_hub_spoke_lower hs hQ hi hd hw
  exact ⟨direction_lower hs hQ hi hd hw,fun _ => hh,hsp⟩

/-- The same principal theorem with the paper's ordinary definition of
indecomposability, quantifying over polytopal Minkowski decompositions. -/
theorem paper_theorem_7_12_polytopal :
    ∀ s : ℕ,2 ≤ s →
      (∀ Q : Set ((Fin s ⊕ Fin (cliqueCapacity s)) → ℝ),
        IsFinitePolytope Q → PolytopalMinkowskiIndecomposable Q → FullDimension Q →
        IsWeakMinkowskiSummand Q (graphicalZonotope (cliqueBook s (cliqueCapacity s))) →
        s.choose 2 + s*saturatedHubNeighbors s ≤ directionCount Q ∧
        (3 ≤ s → ∀ i j : Fin s,i ≠ j → ActualRootEdge Q (Sum.inl i) (Sum.inl j)) ∧
        ∀ i : Fin s,saturatedHubNeighbors s ≤
          (univ.filter (fun j : Fin (cliqueCapacity s) =>
            ActualRootEdge Q (Sum.inl i) (Sum.inr j))).card) ∧
      ∃ Q : Set ((Fin s ⊕ Fin (cliqueCapacity s)) → ℝ),
        LatticePolytope Q ∧ PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
        IsWeakMinkowskiSummand Q (graphicalZonotope (cliqueBook s (cliqueCapacity s))) ∧
        directionCount Q = s.choose 2 + s*saturatedHubNeighbors s ∧
        ∀ i : Fin s,(univ.filter (fun j : Fin (cliqueCapacity s) =>
          ActualRootEdge Q (Sum.inl i) (Sum.inr j))).card = saturatedHubNeighbors s := by
  intro s hs
  obtain ⟨hlower,Q,hL,hI,hD,hW,hE,hS⟩ := paper_theorem_7_12 s hs
  refine ⟨?_,Q,hL,?_,hD,hW,hE,hS⟩
  · intro Q hQ hi hd hw
    exact hlower Q hQ ((weakSummand_indecomposable_iff_polytopal hQ hw).mpr hi) hd hw
  · exact ⟨hI.1,fun P R hP hR he =>
      hI.2 P R hP.compact hR.compact hP.convex hR.convex he⟩

end GraphicalZonotopes.SaturatedDirections

end
end
end BundlePart329

section BundlePart330
/- Source: Papers/GraphicalZonotopes/SaturatedBookGeometricPrincipal.lean -/





/-! # The saturated-book minimum as a count of geometric lines

Theorem 7.12 is stated here using the actual real lines spanned by exposed
edges. The counting equivalence and finiteness theorem in
`GeometricDirectionCount` identify this formulation with the root-pair
formulation proved in `SaturatedBookPrincipal`.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.SaturatedDirections
open Finset
attribute [local instance] Classical.propDecidable

/-- Theorem 7.12 with ordinary polytopal indecomposability and the literal
cardinality of geometric, unoriented edge-direction lines. -/
theorem paper_theorem_7_12_geometric :
    ∀ s : ℕ,2 ≤ s →
      (∀ Q : Set ((Fin s ⊕ Fin (cliqueCapacity s)) → ℝ),
        IsFinitePolytope Q → PolytopalMinkowskiIndecomposable Q → FullDimension Q →
        IsWeakMinkowskiSummand Q (graphicalZonotope (cliqueBook s (cliqueCapacity s))) →
        s.choose 2 + s*saturatedHubNeighbors s ≤ (actualEdgeDirectionLines Q).ncard ∧
        (3 ≤ s → ∀ i j : Fin s,i ≠ j → ActualRootEdge Q (Sum.inl i) (Sum.inl j)) ∧
        ∀ i : Fin s,saturatedHubNeighbors s ≤
          (univ.filter (fun j : Fin (cliqueCapacity s) =>
            ActualRootEdge Q (Sum.inl i) (Sum.inr j))).card) ∧
      ∃ Q : Set ((Fin s ⊕ Fin (cliqueCapacity s)) → ℝ),
        LatticePolytope Q ∧ PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
        IsWeakMinkowskiSummand Q (graphicalZonotope (cliqueBook s (cliqueCapacity s))) ∧
        (actualEdgeDirectionLines Q).ncard = s.choose 2 + s*saturatedHubNeighbors s ∧
        ∀ i : Fin s,(univ.filter (fun j : Fin (cliqueCapacity s) =>
          ActualRootEdge Q (Sum.inl i) (Sum.inr j))).card = saturatedHubNeighbors s := by
  intro s hs
  obtain ⟨hlower,Q,hL,hI,hD,hW,hE,hS⟩ := paper_theorem_7_12_polytopal s hs
  refine ⟨?_,Q,hL,hI,hD,hW,?_,hS⟩
  · intro Q hQ hi hd hw
    obtain ⟨hc,hh,hn⟩ := hlower Q hQ hi hd hw
    refine ⟨?_,hh,hn⟩
    rw [←directionCount_eq_geometric_line_count hQ hw]
    exact hc
  · rw [←directionCount_eq_geometric_line_count hL.finitePolytope hW]
    exact hE

end GraphicalZonotopes.SaturatedDirections

end
end
end BundlePart330

section BundlePart331
/- Source: Papers/GraphicalZonotopes/CliqueDegreeObstruction.lean -/








@[expose] public section
namespace GraphicalZonotopes
namespace CliqueDegree

open Finset

/-- Every graph on six named vertices containing the two tetrahedra
`0123` and `0124` has exactly these six optional edges.  The parameter
records `34, 05, 15, 25, 35, 45`; all remaining non-loop edges are forced. -/
def sixGraph (b : Fin 6 → Bool) : SimpleGraph (Fin 6) where
  Adj i j := i ≠ j ∧
    (if i = 5 then b (j+1) = true
     else if j = 5 then b (i+1) = true
     else i.val < 3 ∨ j.val < 3 ∨ b 0 = true)
  symm := ⟨by
    intro i j
    by_cases hi : i = 5 <;> by_cases hj : j = 5 <;>
      simp [hi,hj,ne_comm,or_comm,or_left_comm]⟩
  loopless := ⟨by intro i; simp⟩

instance (b : Fin 6 → Bool) : DecidableRel (sixGraph b).Adj :=
  fun i j => inferInstanceAs (Decidable (i ≠ j ∧
    (if i = 5 then b (j+1) = true
     else if j = 5 then b (i+1) = true
     else i.val < 3 ∨ j.val < 3 ∨ b 0 = true)))

def HasSixthAttachment (G : SimpleGraph (Fin 6)) : Prop :=
  ∃ T : Finset (Fin 6), T.card = 3 ∧ 5 ∉ T ∧ G.IsClique T ∧
    ∀ i ∈ T, G.Adj i 5

def EveryTriangleSaturated (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj] : Prop :=
  ∀ T : Finset (Fin 6), T.card = 3 → G.IsClique T → ∃ i ∈ T, 5 ≤ G.degree i

instance (b : Fin 6 → Bool) : Decidable (HasSixthAttachment (sixGraph b)) := by
  unfold HasSixthAttachment
  infer_instance

instance (b : Fin 6 → Bool) : Decidable (EveryTriangleSaturated (sixGraph b)) := by
  unfold EveryTriangleSaturated
  infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The finite local obstruction in Lemma 4.5.  This checks exactly the
64 possible supergraphs of the two initial tetrahedra, with every possible
attachment triangle.  It is used as a local lemma in the arbitrary-graph
argument, not as a bounded version of the paper's theorem.  `decide` builds
a proof checked by reduction in the Lean kernel; no native evaluator is used. -/
theorem six_vertex_obstruction :
    ∀ b : Fin 6 → Bool, HasSixthAttachment (sixGraph b) →
      EveryTriangleSaturated (sixGraph b) := by
  decide

def optionalEdges (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj] : Fin 6 → Bool :=
  ![decide (G.Adj 3 4),decide (G.Adj 0 5),decide (G.Adj 1 5),
    decide (G.Adj 2 5),decide (G.Adj 3 5),decide (G.Adj 4 5)]

/-- The finite certificate represents every supergraph of the two indicated
tetrahedra, rather than a selected collection of examples. -/
theorem eq_sixGraph (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj]
    (h₃ : G.IsClique ({0,1,2,3} : Finset (Fin 6)))
    (h₄ : G.IsClique ({0,1,2,4} : Finset (Fin 6))) :
    G = sixGraph (optionalEdges G) := by
  have h01 : G.Adj 0 1 := h₃ (by decide) (by decide) (by decide)
  have h02 : G.Adj 0 2 := h₃ (by decide) (by decide) (by decide)
  have h03 : G.Adj 0 3 := h₃ (by decide) (by decide) (by decide)
  have h04 : G.Adj 0 4 := h₄ (by decide) (by decide) (by decide)
  have h12 : G.Adj 1 2 := h₃ (by decide) (by decide) (by decide)
  have h13 : G.Adj 1 3 := h₃ (by decide) (by decide) (by decide)
  have h14 : G.Adj 1 4 := h₄ (by decide) (by decide) (by decide)
  have h23 : G.Adj 2 3 := h₃ (by decide) (by decide) (by decide)
  have h24 : G.Adj 2 4 := h₄ (by decide) (by decide) (by decide)
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sixGraph,optionalEdges,h01,h02,h03,h04,h12,h13,h14,h23,h24,
      SimpleGraph.adj_comm] <;> first | exact G.adj_symm h01 | assumption

theorem six_vertex_obstruction_graph (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj]
    (h₃ : G.IsClique ({0,1,2,3} : Finset (Fin 6)))
    (h₄ : G.IsClique ({0,1,2,4} : Finset (Fin 6)))
    (ha : HasSixthAttachment G) : EveryTriangleSaturated G := by
  have he := eq_sixGraph G h₃ h₄
  have ha' : HasSixthAttachment (sixGraph (optionalEdges G)) := by simpa only [he] using ha
  have hs := six_vertex_obstruction (optionalEdges G) ha'
  simpa only [← he] using hs

section Ambient
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- An extra neighbor outside an embedded finite graph raises the ambient
degree by one. This is the arbitrary-size bridge for the six-vertex local
certificate. -/
theorem degree_ge_of_extra_neighbor (f : Fin 6 ↪ V) (i : Fin 6) (w : V)
    (hw : w ∉ Set.range f) (hadj : G.Adj (f i) w) :
    (G.comap f).degree i+1 ≤ G.degree (f i) := by
  classical
  let S := ((G.comap f).neighborFinset i).map f
  have hwS : w ∉ S := by
    intro h
    obtain ⟨j,hj,he⟩ := mem_map.mp h
    exact hw ⟨j,he⟩
  have hsub : insert w S ⊆ G.neighborFinset (f i) := by
    intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · exact (G.mem_neighborFinset _ _).mpr hadj
    · obtain ⟨j,hj,rfl⟩ := mem_map.mp hv
      exact (G.mem_neighborFinset _ _).mpr ((G.comap f).mem_neighborFinset _ _ |>.mp hj)
  calc
    (G.comap f).degree i+1 = (insert w S).card := by
      rw [card_insert_of_notMem hwS]
      simp only [S,card_map,SimpleGraph.card_neighborFinset_eq_degree]
    _ ≤ (G.neighborFinset (f i)).card := card_le_card hsub
    _ = G.degree (f i) := rfl

/-- Once the first six vertices of a triangle-connected tetrahedron family
have appeared, a graph of maximum degree five cannot attach a seventh vertex
to any triangle on those six vertices. The ambient vertex type is unrestricted. -/
theorem no_seventh_triangle_attachment (f : Fin 6 ↪ V)
    (hdeg : ∀ v, G.degree v ≤ 5)
    (h₃ : (G.comap f).IsClique ({0,1,2,3} : Finset (Fin 6)))
    (h₄ : (G.comap f).IsClique ({0,1,2,4} : Finset (Fin 6)))
    (ha : HasSixthAttachment (G.comap f))
    (w : V) (hw : w ∉ Set.range f) (T : Finset (Fin 6))
    (hT : T.card = 3) (hcl : (G.comap f).IsClique T)
    (hneigh : ∀ i ∈ T, G.Adj (f i) w) : False := by
  classical
  obtain ⟨i,hi,hfive⟩ := six_vertex_obstruction_graph (G.comap f) h₃ h₄ ha T hT hcl
  have hsix := degree_ge_of_extra_neighbor G f i w hw (hneigh i hi)
  have hup := hdeg (f i)
  omega

end Ambient

end CliqueDegree
end GraphicalZonotopes

end
end BundlePart331

section BundlePart332
/- Source: Papers/GraphicalZonotopes/GrowthDegree.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem TetrahedralGrowth.four_isClique {G : SimpleGraph V} {S : Finset V}
    (h : TetrahedralGrowth G S) (hS : S.card=4) : G.IsClique S := by
  cases h with
  | base C hc hcl => exact hcl
  | @attach R h u hu T hT hTR hcl ha =>
    have hr := h.card_ge_four
    rw [card_insert_of_notMem hu] at hS
    omega

theorem TetrahedralGrowth.five_structure {G : SimpleGraph V} {S : Finset V}
    (h : TetrahedralGrowth G S) (hS : S.card=5) :
    ∃ C T : Finset V, ∃ e : V, C.card=4 ∧ G.IsClique C ∧
      T.card=3 ∧ T ⊆ C ∧ e ∉ C ∧ (∀ v ∈ T,G.Adj e v) ∧ S=insert e C := by
  cases h with
  | base C hc hcl => omega
  | @attach R h u hu T hT hTR hcl ha =>
    have hr : R.card=4 := by rw [card_insert_of_notMem hu] at hS; omega
    exact ⟨R,T,u,hr,h.four_isClique hr,hT,hTR,hu,ha,rfl⟩

def sixPreimage (f : Fin 6 ↪ V) (T : Finset V) : Finset (Fin 6) :=
  univ.filter (fun i => f i ∈ T)

theorem sixPreimage_image (f : Fin 6 ↪ V) (T : Finset V)
    (hT : ∀ v ∈ T,v ∈ Set.range f) : (sixPreimage f T).map f=T := by
  ext v
  constructor
  · intro hv
    obtain ⟨i,hi,rfl⟩ := mem_map.mp hv
    exact (mem_filter.mp hi).2
  · intro hv
    obtain ⟨i,rfl⟩ := hT v hv
    exact mem_map.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,hv⟩,rfl⟩

theorem sixPreimage_card (f : Fin 6 ↪ V) (T : Finset V)
    (hT : ∀ v ∈ T,v ∈ Set.range f) : (sixPreimage f T).card=T.card := by
  have h := congrArg Finset.card (sixPreimage_image f T hT)
  simpa using h

/-- Every six-vertex growth stage is exactly an embedded instance of the
local six-vertex obstruction. No graph edges are discarded by the pullback. -/
theorem TetrahedralGrowth.six_model {G : SimpleGraph V} {S : Finset V}
    (h : TetrahedralGrowth G S) (hS : S.card=6) :
    ∃ f : Fin 6 ↪ V, Set.range f=(S : Set V) ∧
      (G.comap f).IsClique ({0,1,2,3} : Finset (Fin 6)) ∧
      (G.comap f).IsClique ({0,1,2,4} : Finset (Fin 6)) ∧
      CliqueDegree.HasSixthAttachment (G.comap f) := by
  classical
  cases h with
  | base C hc hcl => omega
  | @attach R h f hf U hU hUR hclU hadj =>
    have hR : R.card=5 := by rw [card_insert_of_notMem hf] at hS; omega
    obtain ⟨C,T,e,hC,hclC,hT,hTC,he,heAdj,hRC⟩ := h.five_structure hR
    have hdiff : (C \ T).card=1 := by rw [card_sdiff_of_subset hTC,hC,hT]
    obtain ⟨d,hd⟩ := card_eq_one.mp hdiff
    have hdmem : d ∈ C \ T := by rw [hd]; simp
    have hdC := (mem_sdiff.mp hdmem).1
    have hdT := (mem_sdiff.mp hdmem).2
    have hCT : C=insert d T := by
      have hu := union_sdiff_of_subset hTC
      rw [hd] at hu
      simpa [union_comm] using hu.symm
    obtain ⟨a,b,c,hab,hac,hbc,hTabc⟩ := card_eq_three.mp hT
    have haC : a ∈ C := hTC (by simp [hTabc])
    have hbC : b ∈ C := hTC (by simp [hTabc])
    have hcC : c ∈ C := hTC (by simp [hTabc])
    have hda : d ≠ a := by intro hda; exact hdT (by simp [hda,hTabc])
    have hdb : d ≠ b := by intro hdb; exact hdT (by simp [hdb,hTabc])
    have hdc : d ≠ c := by intro hdc; exact hdT (by simp [hdc,hTabc])
    have hea : e ≠ a := by
      intro heq
      apply he
      simpa only [heq] using haC
    have heb : e ≠ b := by
      intro heq
      apply he
      simpa only [heq] using hbC
    have hec : e ≠ c := by
      intro heq
      apply he
      simpa only [heq] using hcC
    have hed : e ≠ d := by
      intro heq
      apply he
      simpa only [heq] using hdC
    have hCR : C ⊆ R := by rw [hRC]; exact subset_insert _ _
    have heR : e ∈ R := by rw [hRC]; exact mem_insert_self _ _
    have hfa : f ≠ a := by
      intro heq
      apply hf
      simpa only [heq] using hCR haC
    have hfb : f ≠ b := by
      intro heq
      apply hf
      simpa only [heq] using hCR hbC
    have hfc : f ≠ c := by
      intro heq
      apply hf
      simpa only [heq] using hCR hcC
    have hfd : f ≠ d := by
      intro heq
      apply hf
      simpa only [heq] using hCR hdC
    have hfe : f ≠ e := by
      intro heq
      apply hf
      simpa only [heq] using heR
    let names : Fin 6 → V := ![a,b,c,d,e,f]
    have hinj : Function.Injective names := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp only [names,Matrix.cons_val_zero,Matrix.cons_val_succ,
          Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
          Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] at hij ⊢
      all_goals first | rfl | exact False.elim (hab hij) | exact False.elim (hab hij.symm) |
        exact False.elim (hac hij) | exact False.elim (hac hij.symm) |
        exact False.elim (hbc hij) | exact False.elim (hbc hij.symm) |
        exact False.elim (hda hij) | exact False.elim (hda hij.symm) |
        exact False.elim (hdb hij) | exact False.elim (hdb hij.symm) |
        exact False.elim (hdc hij) | exact False.elim (hdc hij.symm) |
        exact False.elim (hea hij) | exact False.elim (hea hij.symm) |
        exact False.elim (heb hij) | exact False.elim (heb hij.symm) |
        exact False.elim (hec hij) | exact False.elim (hec hij.symm) |
        exact False.elim (hed hij) | exact False.elim (hed hij.symm) |
        exact False.elim (hfa hij) | exact False.elim (hfa hij.symm) |
        exact False.elim (hfb hij) | exact False.elim (hfb hij.symm) |
        exact False.elim (hfc hij) | exact False.elim (hfc hij.symm) |
        exact False.elim (hfd hij) | exact False.elim (hfd hij.symm) |
        exact False.elim (hfe hij) | exact False.elim (hfe hij.symm)
    let emb : Fin 6 ↪ V := ⟨names,hinj⟩
    have hnames : ∀ v,v ∈ insert f R ↔ ∃ i : Fin 6,emb i=v := by
      intro v
      rw [hRC,hCT,hTabc]
      simp only [mem_insert,mem_singleton]
      constructor
      · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
        · exact ⟨5,rfl⟩
        · exact ⟨4,rfl⟩
        · exact ⟨3,rfl⟩
        · exact ⟨0,rfl⟩
        · exact ⟨1,rfl⟩
        · exact ⟨2,rfl⟩
      · rintro ⟨i,rfl⟩
        fin_cases i <;> simp [emb,names]
    have hrange : Set.range emb=((insert f R : Finset V) : Set V) := by
      ext v
      exact (hnames v).symm
    have hfirst : ∀ i ∈ ({0,1,2,3} : Finset (Fin 6)),emb i ∈ C := by
      intro i hi
      simp only [mem_insert,mem_singleton] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact haC
      · exact hbC
      · exact hcC
      · exact hdC
    have hsecond : ∀ i ∈ ({0,1,2,4} : Finset (Fin 6)),emb i ∈ insert e T := by
      intro i hi
      simp only [mem_insert,mem_singleton] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> simp [emb,names,hTabc]
    have hclSecond : G.IsClique (insert e T : Finset V) := by
      intro x hx y hy hxy
      rcases mem_insert.mp hx with hxe | hxT
      · rcases mem_insert.mp hy with hye | hyT
        · exact False.elim (hxy (hxe.trans hye.symm))
        · rw [hxe]
          exact heAdj y hyT
      · rcases mem_insert.mp hy with hye | hyT
        · rw [hye]
          exact G.adj_symm (heAdj x hxT)
        · exact hclC (hTC hxT) (hTC hyT) hxy
    refine ⟨emb,hrange,?_,?_,?_⟩
    · intro i hi j hj hij
      exact hclC (hfirst i hi) (hfirst j hj) (fun he => hij (emb.injective he))
    · intro i hi j hj hij
      exact hclSecond (hsecond i hi) (hsecond j hj) (fun he => hij (emb.injective he))
    · have hUrange : ∀ v ∈ U,v ∈ Set.range emb := by
        intro v hv
        rw [hrange]
        exact mem_insert_of_mem (hUR hv)
      refine ⟨sixPreimage emb U,(sixPreimage_card emb U hUrange).trans hU,?_,?_,?_⟩
      · intro h5
        have hmem := (mem_filter.mp h5).2
        change f ∈ U at hmem
        exact hf (hUR hmem)
      · intro i hi j hj hij
        exact hclU (mem_filter.mp hi).2 (mem_filter.mp hj).2
          (fun he => hij (emb.injective he))
      · intro i hi
        exact G.adj_symm (hadj (emb i) (mem_filter.mp hi).2)

theorem degree_comap_le (G : SimpleGraph V) (f : Fin 6 ↪ V) (i : Fin 6) :
    (G.comap f).degree i ≤ G.degree (f i) := by
  classical
  have hsub : ((G.comap f).neighborFinset i).map f ⊆ G.neighborFinset (f i) := by
    intro v hv
    obtain ⟨j,hj,rfl⟩ := mem_map.mp hv
    exact (G.mem_neighborFinset _ _).mpr ((G.comap f).mem_neighborFinset _ _ |>.mp hj)
  have hcard := card_le_card hsub
  simpa only [card_map,SimpleGraph.card_neighborFinset_eq_degree] using hcard

/-- The local certificate applies to every triangle of every six-vertex
growth stage inside an arbitrary finite ambient graph. -/
theorem TetrahedralGrowth.six_triangle_saturated {G : SimpleGraph V} {S : Finset V}
    (h : TetrahedralGrowth G S) (hS : S.card=6) (T : Finset V)
    (hT : T.card=3) (hTS : T ⊆ S) (hcT : G.IsClique T) :
    ∃ v ∈ T,5 ≤ G.degree v := by
  classical
  obtain ⟨f,hrange,h₃,h₄,ha⟩ := h.six_model hS
  have hTrange : ∀ v ∈ T,v ∈ Set.range f := by
    intro v hv
    rw [hrange]
    exact hTS hv
  have hc : (G.comap f).IsClique (sixPreimage f T) := by
    intro i hi j hj hij
    exact hcT (mem_filter.mp hi).2 (mem_filter.mp hj).2
      (fun he => hij (f.injective he))
  obtain ⟨i,hi,hdeg⟩ := CliqueDegree.six_vertex_obstruction_graph (G.comap f)
    h₃ h₄ ha (sixPreimage f T) ((sixPreimage_card f T hTrange).trans hT) hc
  exact ⟨f i,(mem_filter.mp hi).2,hdeg.trans (degree_comap_le G f i)⟩

theorem TetrahedralGrowth.six_cannot_attach_at_degree_five {G : SimpleGraph V}
    {S : Finset V} (h : TetrahedralGrowth G S) (hS : S.card=6)
    (hdeg : ∀ v,G.degree v ≤ 5) (u : V) (hu : u ∉ S) (T : Finset V)
    (hT : T.card=3) (hTS : T ⊆ S) (hcT : G.IsClique T)
    (hadj : ∀ v ∈ T,G.Adj u v) : False := by
  classical
  obtain ⟨f,hrange,h₃,h₄,ha⟩ := h.six_model hS
  have hTrange : ∀ v ∈ T,v ∈ Set.range f := by
    intro v hv
    rw [hrange]
    exact hTS hv
  apply CliqueDegree.no_seventh_triangle_attachment G f hdeg h₃ h₄ ha u
    (by simpa [hrange] using hu) (sixPreimage f T)
    ((sixPreimage_card f T hTrange).trans hT)
  · intro i hi j hj hij
    exact hcT (mem_filter.mp hi).2 (mem_filter.mp hj).2
      (fun he => hij (f.injective he))
  · intro i hi
    exact G.adj_symm (hadj (f i) (mem_filter.mp hi).2)

theorem clique_degree_lower (G : SimpleGraph V) (C : Finset V)
    (hC : G.IsClique C) (v : V) (hv : v ∈ C) : C.card-1 ≤ G.degree v := by
  classical
  have hsub : C.erase v ⊆ G.neighborFinset v := by
    intro w hw
    have hm := mem_erase.mp hw
    exact (G.mem_neighborFinset _ _).mpr (hC hv hm.2 (Ne.symm hm.1))
  have h := card_le_card hsub
  simpa only [card_erase_of_mem hv,SimpleGraph.card_neighborFinset_eq_degree] using h

theorem TetrahedralGrowth.contains_triangle {G : SimpleGraph V} {S : Finset V}
    (h : TetrahedralGrowth G S) :
    ∃ T : Finset V,T.card=3 ∧ T ⊆ S ∧ G.IsClique T := by
  induction h with
  | base C hc hcl =>
    obtain ⟨T,hTC,hT⟩ := exists_subset_card_eq (show 3 ≤ C.card by omega)
    exact ⟨T,hT,hTC,fun u hu v hv huv => hcl (hTC hu) (hTC hv) huv⟩
  | attach h u hu T hT hsub hcl hadj ih =>
    obtain ⟨A,hA,hAS,hclA⟩ := ih
    exact ⟨A,hA,hAS.trans (subset_insert _ _),hclA⟩

theorem TetrahedralGrowth.five_has_degree_four {G : SimpleGraph V} {S : Finset V}
    (h : TetrahedralGrowth G S) (hS : S.card=5) : ∃ v,4 ≤ G.degree v := by
  classical
  obtain ⟨C,T,e,hC,hclC,hT,hTC,he,heAdj,hSC⟩ := h.five_structure hS
  obtain ⟨v,hv⟩ := card_pos.mp (show 0< T.card by omega)
  have hvC := hTC hv
  have heErase : e ∉ C.erase v := fun h => he (mem_of_mem_erase h)
  have hsub : insert e (C.erase v) ⊆ G.neighborFinset v := by
    intro w hw
    rcases mem_insert.mp hw with rfl | hw
    · exact (G.mem_neighborFinset _ _).mpr (G.adj_symm (heAdj v hv))
    · obtain ⟨hwv,hwC⟩ := mem_erase.mp hw
      exact (G.mem_neighborFinset _ _).mpr (hclC hvC hwC (Ne.symm hwv))
  have hcard := card_le_card hsub
  rw [card_insert_of_notMem heErase,card_erase_of_mem hvC,hC] at hcard
  exact ⟨v,hcard⟩

theorem TetrahedralGrowth.seven_has_degree_six {G : SimpleGraph V} {S : Finset V}
    (h : TetrahedralGrowth G S) (hS : 7 ≤ S.card) : ∃ v,6 ≤ G.degree v := by
  classical
  induction h with
  | base C hc hcl => omega
  | @attach R h u hu T hT hTR hcl hadj ih =>
    by_cases hlarge : 7 ≤ R.card
    · exact ih hlarge
    · have hR : R.card=6 := by rw [card_insert_of_notMem hu] at hS; omega
      by_contra hno
      have hdeg : ∀ v,G.degree v ≤ 5 := by
        intro v
        have hv : ¬6 ≤ G.degree v := fun hv => hno ⟨v,hv⟩
        omega
      exact h.six_cannot_attach_at_degree_five hR hdeg u hu T hT hTR hcl hadj

/-- The complete arbitrary-size degree bound, using the finite certificate
only at the six-to-seven transition of a genuine tetrahedral growth. -/
theorem TetrahedralGrowth.degree_lower {G : SimpleGraph V} {S : Finset V}
    (h : TetrahedralGrowth G S) : ∃ v,min (S.card-1) 6 ≤ G.degree v := by
  classical
  have hmin := h.card_ge_four
  by_cases h4 : S.card=4
  · obtain ⟨v,hv⟩ := card_pos.mp (show 0< S.card by omega)
    have hd := clique_degree_lower G S (h.four_isClique h4) v hv
    exact ⟨v,by simpa [h4] using hd⟩
  · by_cases h5 : S.card=5
    · obtain ⟨v,hv⟩ := h.five_has_degree_four h5
      exact ⟨v,by simpa [h5] using hv⟩
    · by_cases h6 : S.card=6
      · obtain ⟨T,hT,hTS,hclT⟩ := h.contains_triangle
        obtain ⟨v,hv,hdeg⟩ := h.six_triangle_saturated h6 T hT hTS hclT
        exact ⟨v,by simpa [h6] using hdeg⟩
      · obtain ⟨v,hv⟩ := h.seven_has_degree_six (by omega)
        exact ⟨v,(min_le_right _ _).trans hv⟩

theorem maximum_degree_bound_of_connected_tetrahedra (G : SimpleGraph V)
    (F : Finset (Finset V)) (hne : F.Nonempty)
    (hcl : ∀ C ∈ F,C.card=4 ∧ G.IsClique C)
    (hconn : (tetrahedronGraph F).Preconnected) (hcover : F.biUnion id=univ) :
    min (Fintype.card V-1) 6 ≤ G.maxDegree := by
  classical
  have hg := tetrahedralGrowth_of_connected_family G F hne hcl hconn
  rw [hcover] at hg
  obtain ⟨v,hv⟩ := hg.degree_lower
  have h := hv.trans (G.degree_le_maxDegree v)
  simpa using h

end GraphicalZonotopes

end
end
end BundlePart332

section BundlePart333
/- Source: Papers/GraphicalZonotopes/SpanningTetrahedra.lean -/








@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
namespace PositiveDecomposition
variable {V : Type*} [Fintype V] [LinearOrder V]

@[simp] theorem allocation_zero_function : allocation (0 : SetFunction V)=0 := by
  funext C
  by_cases hC : C.card = 2
  · obtain ⟨u,v,huv,rfl⟩ := card_eq_two.mp hC
    rw [allocation_pair _ huv]
    have hm : minimumSlack (0 : SetFunction V) u v=0 :=
      minimumSlack_eq_zero (by intros; simp [delta])
    simp [hm]
  · exact allocation_zero _ hC

@[simp] theorem adjusted_zero : adjusted (0 : SetFunction V)=0 := by
  rw [adjusted,allocation_zero_function]
  change 0+zetaLinear 0=0
  simp

theorem higherClass_right_dependsOn {G : SimpleGraph V} {y : SetFunction V}
    (hy : CliqueSupported G y) (T : Finset V) :
    GraphicalZonotopes.DependsOn
      (higherClass y (TriangleComponents.classOf G) (Sum.inr T)) T := by
  apply zeta_dependsOn
  intro C hC
  by_contra he
  obtain ⟨hc,ha,hyC⟩ := classCoefficients_nonzero he
  obtain ⟨h3,rfl⟩ := TriangleComponents.right_class_is_triangle hy hc hyC ha
  exact hC Subset.rfl

theorem higherClass_right_zero_of_card_ne_three {G : SimpleGraph V} {y : SetFunction V}
    (hy : CliqueSupported G y) {T : Finset V} (hT : T.card ≠ 3) :
    higherClass y (TriangleComponents.classOf G) (Sum.inr T)=0 := by
  apply (zeta_eq_zero_iff _).mpr
  funext C
  by_contra he
  obtain ⟨hc,ha,hyC⟩ := classCoefficients_nonzero he
  obtain ⟨h3,rfl⟩ := TriangleComponents.right_class_is_triangle hy hc hyC ha
  exact hT h3

theorem higherClass_left_dependsOn {G : SimpleGraph V} {y : SetFunction V}
    (hy : CliqueSupported G y) (a : (TriangleComponents.cliqueGraph G).ConnectedComponent) :
    GraphicalZonotopes.DependsOn
      (higherClass y (TriangleComponents.classOf G) (Sum.inl a))
      (TriangleComponents.componentVertices G a) := by
  apply zeta_dependsOn
  intro C hC
  by_contra he
  obtain ⟨hc,ha,hyC⟩ := classCoefficients_nonzero he
  apply hC
  by_cases h3 : C.card = 3
  · exact TriangleComponents.triangle_subset_component h3 ha
  · have h4 : 4 ≤ C.card := by omega
    have hcl : G.IsClique C := by
      intro u hu v hv huv
      by_contra hn
      exact hyC (hy.2.2 C u v hu hv huv hn)
    exact TriangleComponents.higher_subset_component h4 hcl ha

def allPieces (G : SimpleGraph V) (y : SetFunction V) :
    (TriangleComponents.ComponentIndex G ⊕ Finset V) → SetFunction V :=
  Sum.elim (fun a => adjusted (higherClass y (TriangleComponents.classOf G) a))
    (fun C => residual y (higherClass y (TriangleComponents.classOf G)) C • setMonomial C)

theorem allPieces_positive {G : SimpleGraph V} (y : SetFunction V)
    (hy : CliqueSupported G y) (hs : Supermodular (zeta y)) :
    (∀ i, TranslationNormalized (allPieces G y i) ∧ Supermodular (allPieces G y i)) ∧
    (∑ i, allPieces G y i)=zeta y := by
  classical
  obtain ⟨hp,hr,hrn,hrs,he⟩ := compatible_class_decomposition y hy hs
    (TriangleComponents.classOf G) (TriangleComponents.classOf_compatible hy)
  constructor
  · intro i
    cases i with
    | inl a => exact ⟨(hp a).1,(hp a).2.1⟩
    | inr C =>
      have hnonneg := hr C
      refine ⟨?_,(setMonomial_supermodular C).smul hnonneg⟩
      by_cases hC : C.card = 2
      · have hn : TranslationNormalized (setMonomial C) := by
          refine ⟨setMonomial_normalized (card_pos.mp (by omega)),?_⟩
          intro v
          have hnot : ¬ C ⊆ {v} := by
            intro hsub
            have hcard := card_le_card hsub
            simp only [card_singleton] at hcard
            omega
          simp [setMonomial,hnot]
        exact ⟨by change _*setMonomial C ∅=0; rw [hn.1,mul_zero],
          fun v => by change _*setMonomial C {v}=0; rw [hn.2 v,mul_zero]⟩
      · have hz := residual_zero y (higherClass y (TriangleComponents.classOf G)) hC
        simp only [allPieces,Sum.elim_inr,hz,zero_smul]
        exact ⟨rfl,fun _ => rfl⟩
  · rw [Fintype.sum_sum_type]
    change (∑ a,adjusted (higherClass y (TriangleComponents.classOf G) a))+
      (∑ C,residual y (higherClass y (TriangleComponents.classOf G)) C • setMonomial C)=_
    rw [← zeta_eq_sum_monomials]
    exact he

end PositiveDecomposition

theorem graphical_actualDirectionGraph {V : Type*} [Fintype V] [DecidableEq V]
    {z : SetFunction V} (hn : Normalized z) (hs : Supermodular z) :
    Graphical (actualDirectionGraph (basePolytope z)) z := by
  intro u v huv hnon S hu hv
  have hnonneg := hs.elemental u v huv S hu hv
  apply le_antisymm _ hnonneg
  by_contra h
  have hpos : 0 < delta z u v S := lt_of_not_ge h
  exact hnon (exposedSegment_of_positive_delta hn hs huv hu hv hpos)

/-- Lemma4.3: the tetrahedral component is constructed from the actual
positive decomposition. No connectivity or coefficient-sign hypothesis has
been added to the indecomposable polytope. -/
theorem ExtremeSupermodular.spanning_tetrahedra {n : ℕ} (hn : 4 ≤ n)
    {z : SetFunction (Fin n)} (hz : ExtremeSupermodular z)
    (hfull : Module.finrank ℝ (vectorSpan ℝ (basePolytope z))=n-1)
    {G : SimpleGraph (Fin n)} (hG : Graphical G z) :
    ∃ F : Finset (Finset (Fin n)), F.Nonempty ∧
      (∀ C ∈ F,C.card=4 ∧ G.IsClique C) ∧
      (tetrahedronGraph F).Preconnected ∧ F.biUnion id=univ := by
  classical
  let y := mobius z
  have hy : CliqueSupported G y := (mobius_cliqueSupported_iff G z).mpr ⟨hz.1,hG⟩
  have hys : Supermodular (zeta y) := by simpa [y] using hz.2.1
  obtain ⟨hp,he⟩ := PositiveDecomposition.allPieces_positive y hy hys
  have hez : (∑ i,PositiveDecomposition.allPieces G y i)=z := by simpa [y] using he
  have hex : ∃ i,PositiveDecomposition.allPieces G y i ≠ 0 := by
    by_contra h
    push_neg at h
    have hzero : (∑ i,PositiveDecomposition.allPieces G y i)=0 :=
      sum_eq_zero (fun i hi => h i)
    exact hz.2.2.1 (hez.symm.trans hzero)
  obtain ⟨i,hi⟩ := hex
  obtain ⟨a,ha,hscale⟩ := hz.finite_summand (PositiveDecomposition.allPieces G y)
    (fun i => (hp i).1) (fun i => (hp i).2) hez hi
  have hsupport : ∀ S, DependsOn (PositiveDecomposition.allPieces G y i) S → S=univ := by
    intro S hS
    rw [hscale] at hS
    exact fullDimension_dependsOn_eq_univ (by omega) hz.1 hz.2.1 hfull
      (DependsOn.of_smul (ne_of_gt ha) hS)
  cases i with
  | inr C =>
    have hC : C.card=2 := by
      by_contra hnot
      have hzC := PositiveDecomposition.residual_zero y
        (PositiveDecomposition.higherClass y (TriangleComponents.classOf G)) hnot
      exact hi (by simp [PositiveDecomposition.allPieces,hzC])
    have hdep : DependsOn (PositiveDecomposition.allPieces G y (Sum.inr C)) C :=
      (setMonomial_dependsOn C).smul _
    have hcard := congrArg Finset.card (hsupport C hdep)
    simp only [hC,card_univ,Fintype.card_fin] at hcard
    omega
  | inl c =>
    cases c with
    | inr T =>
      have hT : T.card=3 := by
        by_contra hnot
        have hzero := PositiveDecomposition.higherClass_right_zero_of_card_ne_three hy hnot
        apply hi
        change PositiveDecomposition.adjusted
          (PositiveDecomposition.higherClass y (TriangleComponents.classOf G)
            (Sum.inr T)) = 0
        exact (congrArg PositiveDecomposition.adjusted hzero).trans
          PositiveDecomposition.adjusted_zero
      have hdep := PositiveDecomposition.DependsOn.adjusted
        (PositiveDecomposition.higherClass_right_dependsOn hy T)
      have hcard := congrArg Finset.card (hsupport T hdep)
      simp only [hT,card_univ,Fintype.card_fin] at hcard
      omega
    | inl c =>
      have hdep := PositiveDecomposition.DependsOn.adjusted
        (PositiveDecomposition.higherClass_left_dependsOn hy c)
      have hcover := hsupport (TriangleComponents.componentVertices G c) hdep
      refine ⟨TriangleComponents.componentFamily G c,?_,?_,
        TriangleComponents.componentFamily_preconnected G c,hcover⟩
      · have hm : (⟨0,by omega⟩ : Fin n) ∈ TriangleComponents.componentVertices G c := by
          rw [hcover]
          exact mem_univ _
        obtain ⟨C,hC,hv⟩ := mem_biUnion.mp hm
        exact ⟨C,hC⟩
      · intro C hC
        have hc := TriangleComponents.mem_componentFamily.mp hC
        exact ⟨hc.1,hc.2.1⟩

theorem ExtremeSupermodular.direction_count_bound {n : ℕ} (hn : 4 ≤ n)
    {z : SetFunction (Fin n)} (hz : ExtremeSupermodular z)
    (hfull : Module.finrank ℝ (vectorSpan ℝ (basePolytope z))=n-1) :
    3*n-6 ≤ directionCount (basePolytope z) ∧
      (directionCount (basePolytope z)=3*n-6 →
        IsThreeTree (actualDirectionGraph (basePolytope z))) := by
  obtain ⟨F,hne,hcl,hconn,hcover⟩ := hz.spanning_tetrahedra hn hfull
    (graphical_actualDirectionGraph hz.1.1 hz.2.1)
  simpa [directionCount] using edge_bound_of_connected_tetrahedra _ F hne hcl hconn hcover

theorem ExtremeSupermodular.maximum_degree_bound {n : ℕ} (hn : 4 ≤ n)
    {z : SetFunction (Fin n)} (hz : ExtremeSupermodular z)
    (hfull : Module.finrank ℝ (vectorSpan ℝ (basePolytope z))=n-1) :
    min (n-1) 6 ≤ maximumDirectionDegree (basePolytope z) := by
  classical
  obtain ⟨F,hne,hcl,hconn,hcover⟩ := hz.spanning_tetrahedra hn hfull
    (graphical_actualDirectionGraph hz.1.1 hz.2.1)
  simpa [maximumDirectionDegree] using
    maximum_degree_bound_of_connected_tetrahedra _ F hne hcl hconn hcover

end GraphicalZonotopes

end
end
end BundlePart333

section BundlePart334
/- Source: Papers/GraphicalZonotopes/DirectionBounds.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes

/-- Theorem4.1, with all translations and no clique-number restriction.
The matching path-cube attainment is the separate principal family theorem. -/
theorem direction_bounds (n : ℕ) (hn : 4 ≤ n) (Q : Set (Fin n → ℝ))
    (hQ : IsGeneralizedPermutahedron Q) (hi : MinkowskiIndecomposable Q)
    (hd : FullDimension Q) :
    3*n-6 ≤ directionCount Q ∧ min (n-1) 6 ≤ maximumDirectionDegree Q ∧
    (directionCount Q=3*n-6 → IsThreeTree (actualDirectionGraph Q)) := by
  obtain ⟨z,hzn,hzs,rfl⟩ := hQ
  have hdim : Module.finrank ℝ (vectorSpan ℝ (basePolytope (normalize z)))=n-1 := by
    rw [vectorSpan_basePolytope_normalize]
    simpa [FullDimension] using hd
  have hne : normalize z ≠ 0 := by
    intro hz0
    rw [hz0,basePolytope_zero] at hdim
    have hspan : vectorSpan ℝ ({0} : Set (Fin n → ℝ)) =
        (⊥ : Submodule ℝ (Fin n → ℝ)) :=
      _root_.vectorSpan_singleton ℝ (0 : Fin n → ℝ)
    rw [hspan, _root_.finrank_bot] at hdim
    omega
  have hext := hi.extremeSupermodular_normalize hzn hzs hne
  obtain ⟨hedges,heq⟩ := hext.direction_count_bound hn hdim
  have hdegree := hext.maximum_degree_bound hn hdim
  have hgraph := actualDirectionGraph_normalize z
  have hecount : directionCount (basePolytope (normalize z))=directionCount (basePolytope z) := by
    unfold directionCount
    rw [hgraph]
  have hedegree : maximumDirectionDegree (basePolytope (normalize z))=
      maximumDirectionDegree (basePolytope z) := by
    unfold maximumDirectionDegree
    rw [hgraph]
  rw [hecount] at hedges heq
  rw [hedegree] at hdegree
  exact ⟨hedges,hdegree,fun h => by simpa only [hgraph] using heq h⟩

/-- The same theorem with the traditional polytope-summand definition in
its hypothesis. This prevents the stronger-looking compact-convex wording
from concealing a restriction on the paper's class of indecomposable polytopes. -/
theorem direction_bounds_polytopal (n : ℕ) (hn : 4≤ n) (Q : Set (Fin n → ℝ))
    (hQ : IsGeneralizedPermutahedron Q) (hi : PolytopalMinkowskiIndecomposable Q)
    (hd : FullDimension Q) :
    3*n-6≤ directionCount Q ∧ min (n-1) 6≤ maximumDirectionDegree Q ∧
    (directionCount Q=3*n-6 → IsThreeTree (actualDirectionGraph Q)) :=
  direction_bounds n hn Q hQ ((minkowskiIndecomposable_iff_polytopal hQ).mpr hi) hd

end GraphicalZonotopes

end
end
end BundlePart334

section BundlePart335
/- Source: Papers/GraphicalZonotopes/SharpDirectionBounds.lean -/






@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open scoped Pointwise

/-- The root-direction graph counts every geometric edge direction of an
actual generalized permutahedron. This includes arbitrary translations. -/
theorem generalizedPermutahedron_exposed_edge_is_root
    {V : Type*} [Fintype V] [DecidableEq V] {Q : Set (V → ℝ)}
    (hQ : IsGeneralizedPermutahedron Q) {p q : V → ℝ}
    (hex : IsExposedSegment Q p q) :
    ∃ u v : V,u≠ v ∧ ∃ t : ℝ,t≠0 ∧
      q-p=t • (basisVector v-basisVector u) := by
  obtain ⟨z,hn,hs,rfl⟩ := hQ
  have hweak : IsWeakMinkowskiSummand (basePolytope z)
      (graphicalZonotope (⊤ : SimpleGraph V)) := by
    apply (isWeakMinkowskiSummand_graphical_iff hn hs).mpr
    intro u v huv hnon
    exact False.elim (hnon huv)
  obtain ⟨a,ha,R,_,_,_,he⟩ := hweak
  obtain ⟨u,v,huv,t,ht,heq⟩ :=
    basePolytope_summand_exposed_edge hn hs (⊤ : SimpleGraph V) ha.le R he hex
  exact ⟨u,v,huv,t,ht,heq⟩

namespace Path

theorem actualDirectionGraph_eq {n : ℕ} (hn : 4≤ n) :
    actualDirectionGraph (polytope n)=graph n := by
  apply SimpleGraph.ext
  funext u v
  exact propext (actual_direction_graph hn u v)

theorem polytope_generalizedPermutahedron (n : ℕ) :
    IsGeneralizedPermutahedron (polytope n) :=
  ⟨setFunction n,(setFunction_normalized n).1,setFunction_supermodular n,rfl⟩

theorem polytope_polytopalIndecomposable {n : ℕ} (hn : 4≤ n) :
    PolytopalMinkowskiIndecomposable (polytope n) :=
  (minkowskiIndecomposable_iff_polytopal (polytope_generalizedPermutahedron n)).mp
    (polytope_indecomposable hn)

theorem polytope_fullDimension {n : ℕ} (hn : 4≤ n) :
    FullDimension (polytope n) := by
  simpa only [FullDimension,Fintype.card_fin] using polytope_dimension hn

theorem directionCount_eq {n : ℕ} (hn : 4≤ n) :
    directionCount (polytope n)=3*n-6 := by
  rw [directionCount,actualDirectionGraph_eq hn]
  exact graph_edge_count hn

theorem maximumDirectionDegree_eq {n : ℕ} (hn : 4≤ n) :
    maximumDirectionDegree (polytope n)=min (n-1) 6 := by
  classical
  letI : DecidableRel (graph n).Adj := graph_decidableAdj n
  change (actualDirectionGraph (polytope n)).maxDegree=min (n-1) 6
  let e : actualDirectionGraph (polytope n) ≃g graph n :=
    { toEquiv := Equiv.refl _
      map_rel_iff' := by
        intro u v
        exact (actual_direction_graph hn u v).symm }
  exact e.maxDegree_eq.trans (graph_maxDegree hn)

end Path

/-- The full content of Theorem4.1: both universal sharp bounds, the equality
classification, and simultaneous attainment by the paper's explicit Q_n for
every n≥4. The definition uses ordinary polytopal indecomposability. -/
def SharpDirectionBounds : Prop :=
  (∀ n : ℕ,4≤ n → ∀ Q : Set (Fin n → ℝ),
    IsGeneralizedPermutahedron Q → PolytopalMinkowskiIndecomposable Q →
    FullDimension Q →
    3*n-6≤ directionCount Q ∧ min (n-1) 6≤ maximumDirectionDegree Q ∧
    (directionCount Q=3*n-6 → IsThreeTree (actualDirectionGraph Q))) ∧
  ∀ n : ℕ,4≤ n →
    IsGeneralizedPermutahedron (Path.polytope n) ∧
    PolytopalMinkowskiIndecomposable (Path.polytope n) ∧
    FullDimension (Path.polytope n) ∧
    directionCount (Path.polytope n)=3*n-6 ∧
    maximumDirectionDegree (Path.polytope n)=min (n-1) 6

/-- A single audited endpoint is required for the entire sharp theorem,
including the explicit equality witnesses in its final sentence. -/
theorem sharp_direction_bounds : SharpDirectionBounds := by
  refine ⟨direction_bounds_polytopal,?_⟩
  intro n hn
  exact ⟨Path.polytope_generalizedPermutahedron n,
    Path.polytope_polytopalIndecomposable hn,Path.polytope_fullDimension hn,
    Path.directionCount_eq hn,Path.maximumDirectionDegree_eq hn⟩

end GraphicalZonotopes

end
end
end BundlePart335

section BundlePart336
/- Source: Papers/GraphicalZonotopes/TriangularExtensionGeometry.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace BooleanVertexExtension
open Finset BooleanModule
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem andOr_graphical {G : SimpleGraph V} {a b t : V}
    (hT : G.IsClique ({a,b,t} : Finset V)) : Graphical G (andOr a b t) := by
  intro u v huv hnon S hu hv
  by_cases huT : u ∈ ({a,b,t} : Finset V)
  · by_cases hvT : v ∈ ({a,b,t} : Finset V)
    · exact False.elim (hnon (hT huT hvT huv))
    · have hva : v ≠ a := fun he => hvT (by simp [he])
      have hvb : v ≠ b := fun he => hvT (by simp [he])
      have hvt : v ≠ t := fun he => hvT (by simp [he])
      rw [delta_comm]
      exact andOr_delta_outside hva hvb hvt u S
  · have hua : u ≠ a := fun he => huT (by simp [he])
    have hub : u ≠ b := fun he => huT (by simp [he])
    have hut : u ≠ t := fun he => huT (by simp [he])
    exact andOr_delta_outside hua hub hut v S

theorem triangular_append_graphical {G : SimpleGraph V} {z : SetFunction V} {a b t : V}
    (hz : Graphical G z) (hT : G.IsClique ({a,b,t} : Finset V)) :
    Graphical (SingleVertexGraph.graph G {a,b,t}) (append z (andOr a b t)) := by
  intro x y hxy hnon A hx hy
  have hF := andOr_graphical hT
  cases x with
  | inl u =>
    cases y with
    | inl v =>
      have huv : u ≠ v := fun he => hxy (congrArg Sum.inl he)
      have hu : u ∉ hubs A := by simpa using hx
      have hv : v ∉ hubs A := by simpa using hy
      rw [append_delta_old,hz u v huv hnon _ hu hv,hF u v huv hnon _ hu hv]
      split_ifs <;> simp
    | inr j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      change u ∉ ({a,b,t} : Finset V) at hnon
      have hua : u ≠ a := fun he => hnon (by simp [he])
      have hub : u ≠ b := fun he => hnon (by simp [he])
      have hut : u ≠ t := fun he => hnon (by simp [he])
      rw [append_delta_new _ _ _ _ hy,andOr_insert_outside hua hub hut,sub_self]
  | inr i =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    cases y with
    | inl v =>
      change v ∉ ({a,b,t} : Finset V) at hnon
      have hva : v ≠ a := fun he => hnon (by simp [he])
      have hvb : v ≠ b := fun he => hnon (by simp [he])
      have hvt : v ≠ t := fun he => hnon (by simp [he])
      rw [delta_comm,append_delta_new _ _ _ _ hx,andOr_insert_outside hva hvb hvt,sub_self]
    | inr j => exact False.elim (hxy (congrArg Sum.inr (Subsingleton.elim _ _)))

theorem triangular_append_old_positive {z : SetFunction V} {a b t u v : V}
    {S : Finset V} (hu : u ∉ S) (hv : v ∉ S) (hp : 0 < delta z u v S) :
    Sum.inl u ∉ (hubSet (J := Fin 1) S) ∧ Sum.inl v ∉ (hubSet (J := Fin 1) S) ∧
      0 < delta (append z (andOr a b t)) (Sum.inl u) (Sum.inl v) (hubSet S) := by
  refine ⟨by simpa using hu,by simpa using hv,?_⟩
  rw [append_delta_old]
  simpa using hp

theorem triangular_append_spoke_positive {z : SetFunction V} {a b t : V}
    (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) {u : V}
    (hu : u ∈ ({a,b,t} : Finset V)) :
    ∃ A : Finset (Vertex V), Sum.inl u ∉ A ∧ Sum.inr 0 ∉ A ∧
      0 < delta (append z (andOr a b t)) (Sum.inl u) (Sum.inr 0) A := by
  simp only [mem_insert,mem_singleton] at hu
  rcases hu with rfl | rfl | rfl
  · refine ⟨hubSet {b},by simpa using hab,by simp,?_⟩
    rw [append_delta_new _ _ _ _ (by simp)]
    simp [andOr,hab,hat,hbt,Ne.symm hab,Ne.symm hat,Ne.symm hbt]
  · refine ⟨hubSet {a},by simpa using hab.symm,by simp,?_⟩
    rw [append_delta_new _ _ _ _ (by simp)]
    simp [andOr,hab,hat,hbt,Ne.symm hab,Ne.symm hat,Ne.symm hbt]
  · refine ⟨hubSet {b},by simpa using hbt.symm,by simp,?_⟩
    rw [append_delta_new _ _ _ _ (by simp)]
    simp [andOr,hab,hat,hbt,Ne.symm hab,Ne.symm hat,Ne.symm hbt]

theorem triangular_append_positive {G : SimpleGraph V} {z : SetFunction V} {a b t : V}
    (hb : UnitBoundary z a b t)
    (hz : ∀ u v, G.Adj u v → ∃ S : Finset V, u ∉ S ∧ v ∉ S ∧ 0 < delta z u v S) :
    ∀ x y, (SingleVertexGraph.graph G {a,b,t}).Adj x y →
      ∃ A : Finset (Vertex V), x ∉ A ∧ y ∉ A ∧
        0 < delta (append z (andOr a b t)) x y A := by
  intro x y hxy
  cases x with
  | inl u =>
    cases y with
    | inl v =>
      obtain ⟨S,hu,hv,hp⟩ := hz u v hxy
      exact ⟨hubSet S,triangular_append_old_positive hu hv hp⟩
    | inr j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact triangular_append_spoke_positive hb.1 hb.2.1 hb.2.2.1 hxy
  | inr i =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    cases y with
    | inl v =>
      obtain ⟨A,hv,hw,hp⟩ := triangular_append_spoke_positive
        (z := z) hb.1 hb.2.1 hb.2.2.1 hxy
      exact ⟨A,hw,hv,by simpa only [delta_comm] using hp⟩
    | inr j => exact False.elim hxy

theorem append_integerValued {z F : SetFunction V} (hz : IntegerValued z)
    (hF : IsMonotoneBoolean F) : IntegerValued (append z F) := by
  intro A
  obtain ⟨k,hk⟩ := hz (hubs A)
  have he : append z F A = z (hubs A) + if Sum.inr 0 ∈ A then F (hubs A) else 0 := by
    simp [append,assembled,boundaryLift,branchLift,Finset.sum_apply]
  rw [he,hk]
  by_cases hw : Sum.inr 0 ∈ A
  · rw [if_pos hw]
    rcases hF.values (hubs A) with hzero | hone
    · exact ⟨k,by rw [hzero,add_zero]⟩
    · exact ⟨k+1,by rw [hone]; norm_num⟩
  · exact ⟨k,by rw [if_neg hw,add_zero]⟩

theorem triangular_append_triangle {G : SimpleGraph V} {a b t : V}
    (hab : a ≠ b) (hT : G.IsClique ({a,b,t} : Finset V)) :
    (SingleVertexGraph.graph G {a,b,t}).IsClique
      ({Sum.inl b,Sum.inl a,Sum.inr 0} : Finset (Vertex V)) := by
  intro x hx y hy hxy
  change x ∈ ({Sum.inl b,Sum.inl a,Sum.inr 0} : Finset (Vertex V)) at hx
  change y ∈ ({Sum.inl b,Sum.inl a,Sum.inr 0} : Finset (Vertex V)) at hy
  simp only [mem_insert,mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  · exact False.elim (hxy rfl)
  · exact hT (by simp) (by simp) hab.symm
  · exact mem_insert_of_mem (mem_insert_self _ _)
  · exact hT (by simp) (by simp) hab
  · exact False.elim (hxy rfl)
  · exact mem_insert_self _ _
  · exact mem_insert_of_mem (mem_insert_self _ _)
  · exact mem_insert_self _ _
  · exact False.elim (hxy rfl)

end BooleanVertexExtension
end GraphicalZonotopes

end
end
end BundlePart336

section BundlePart337
/- Source: Papers/GraphicalZonotopes/SparseFamilyGeometry.lean -/





/-! # An unbounded family with one edge above the sharp direction bound

The graphs are precisely the graphs `L_(10+m)` in Section 8.2. The polynomial
is an alternative uniform construction: at each step append the Boolean
marginal `b ∧ (a ∨ t)`, then exchange the names of the two hubs. This retains
all old directions and raises the maximum elemental slack by at most one.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace SparseFamily
open Finset BooleanModule BooleanVertexExtension
open scoped BigOperators Pointwise

def Vertex : ℕ → Type
  | 0 => Fin 10
  | m+1 => BooleanVertexExtension.Vertex (Vertex m)

instance vertexFintype (m : ℕ) : Fintype (Vertex m) := by
  induction m with
  | zero => exact inferInstanceAs (Fintype (Fin 10))
  | succ m ih =>
    letI : Fintype (Vertex m) := ih
    exact inferInstanceAs (Fintype (Vertex m ⊕ Fin 1))

instance vertexDecidableEq (m : ℕ) : DecidableEq (Vertex m) := by
  induction m with
  | zero => exact inferInstanceAs (DecidableEq (Fin 10))
  | succ m ih =>
    letI : DecidableEq (Vertex m) := ih
    exact inferInstanceAs (DecidableEq (Vertex m ⊕ Fin 1))

def frame : (m : ℕ) → Vertex m × Vertex m × Vertex m
  | 0 => ((0 : Fin 10),(1 : Fin 10),(6 : Fin 10))
  | m+1 => (Sum.inl (frame m).2.1,Sum.inl (frame m).1,Sum.inr 0)

abbrev first (m : ℕ) : Vertex m := (frame m).1
abbrev second (m : ℕ) : Vertex m := (frame m).2.1
abbrev tip (m : ℕ) : Vertex m := (frame m).2.2

def graph : (m : ℕ) → SimpleGraph (Vertex m)
  | 0 => DiamondGeometry.graph
  | m+1 => SingleVertexGraph.graph (graph m) {first m,second m,tip m}

/-- The distinguished triangle has three different vertices at every step;
this fact depends only on the recursive graph presentation. -/
theorem frame_distinct (m : ℕ) :
    first m ≠ second m ∧ first m ≠ tip m ∧ second m ≠ tip m := by
  induction m with
  | zero =>
    change (0 : Fin 10) ≠ 1 ∧ (0 : Fin 10) ≠ 6 ∧ (1 : Fin 10) ≠ 6
    decide
  | succ m ih =>
    change (Sum.inl (second m) : Vertex m ⊕ Fin 1) ≠ Sum.inl (first m) ∧
      (Sum.inl (second m) : Vertex m ⊕ Fin 1) ≠ Sum.inr 0 ∧
      (Sum.inl (first m) : Vertex m ⊕ Fin 1) ≠ Sum.inr 0
    exact ⟨fun h => ih.1 (Sum.inl_injective h).symm,Sum.inl_ne_inr,Sum.inl_ne_inr⟩

def function : (m : ℕ) → SetFunction (Vertex m)
  | 0 => DiamondGeometry.function
  | m+1 => append (function m) (andOr (first m) (second m) (tip m))

theorem vertex_card (m : ℕ) : Fintype.card (Vertex m) = 10+m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change Fintype.card (Vertex m ⊕ Fin 1) = _
    rw [Fintype.card_sum,Fintype.card_fin,ih]
    omega

/-- The seed boundary is verified from the literal 57-clique polynomial,
using no private-kernel or rigidity premise. -/
theorem base_unit_boundary : UnitBoundary DiamondGeometry.function (0 : Fin 10) 1 6 := by
  refine ⟨by decide,by decide,by decide,?_⟩
  intro S h0 h6 h1
  rw [DiamondGeometry.delta_eq_slackZ (by decide) h0 h6]
  by_cases h2 : (2 : Fin 10) ∈ S <;>
    norm_num [DiamondGeometry.slackZ,DiamondGeometry.cliques,DiamondGeometry.coefficientsZ,
      Fin.sum_univ_succ,Finset.subset_iff,h0,h6,h1,h2]

theorem extreme_and_boundary (m : ℕ) :
    ExtremeSupermodular (function m) ∧ UnitBoundary (function m) (first m) (second m) (tip m) := by
  induction m with
  | zero => exact ⟨DiamondGeometry.extreme,base_unit_boundary⟩
  | succ m ih =>
    exact ⟨triangular_append_extreme ih.1 ih.2,triangular_append_boundary ih.2⟩

theorem extreme (m : ℕ) : ExtremeSupermodular (function m) := (extreme_and_boundary m).1
theorem unit_boundary (m : ℕ) : UnitBoundary (function m) (first m) (second m) (tip m) :=
  (extreme_and_boundary m).2

theorem frame_card (m : ℕ) : ({first m,second m,tip m} : Finset (Vertex m)).card = 3 := by
  have h := frame_distinct m
  simp [h.1,h.2.1,h.2.2]

theorem frame_clique (m : ℕ) : (graph m).IsClique ({first m,second m,tip m} : Finset (Vertex m)) := by
  induction m with
  | zero =>
    change DiamondGeometry.graph.IsClique ({0,1,6} : Finset (Fin 10))
    decide +kernel
  | succ m ih => exact triangular_append_triangle (unit_boundary m).1 ih

theorem graphical (m : ℕ) : Graphical (graph m) (function m) := by
  induction m with
  | zero => exact DiamondGeometry.graphical
  | succ m ih => exact triangular_append_graphical ih (frame_clique m)

theorem integerValued (m : ℕ) : IntegerValued (function m) := by
  induction m with
  | zero => exact DiamondGeometry.integerValued
  | succ m ih => exact append_integerValued ih (andOr_boolean _ _ _)

theorem elemental_upper (m : ℕ) :
    ∀ u v : Vertex m, u ≠ v → ∀ S, u ∉ S → v ∉ S →
      delta (function m) u v S ≤ (m+4 : ℕ) := by
  induction m with
  | zero =>
    intro u v huv S hu hv
    exact (DiamondGeometry.elemental_bounds huv hu hv).2
  | succ m ih =>
    have h := append_delta_upper (andOr_boolean (first m) (second m) (tip m))
      (Nat.cast_nonneg (m+4)) ih
    intro u v huv S hu hv
    have he : ((m+4 : ℕ) : ℝ)+1 = ((m+1+4 : ℕ) : ℝ) := by
      norm_num [Nat.cast_add] <;> ring
    simpa only [function,he] using h u v huv S hu hv

theorem positive_slack (m : ℕ) :
    ∀ u v : Vertex m, (graph m).Adj u v → ∃ S : Finset (Vertex m),
      u ∉ S ∧ v ∉ S ∧ 0 < delta (function m) u v S := by
  induction m with
  | zero => exact fun _ _ h => DiamondGeometry.positive_slack h
  | succ m ih => exact triangular_append_positive (unit_boundary m) ih

theorem connected (m : ℕ) : (graph m).Connected := by
  induction m with
  | zero => exact DiamondGeometry.graph_connected
  | succ m ih => exact SingleVertexGraph.connected ih ⟨first m,by simp⟩

theorem cliqueFree_five (m : ℕ) : (graph m).CliqueFree 5 := by
  induction m with
  | zero =>
    change DiamondGeometry.graph.CliqueFree 5
    intro C hC
    have hc : C.card = 5 := hC.card_eq
    obtain ⟨i,hi⟩ := DiamondGeometry.cliques_complete C ⟨by omega,hC.isClique⟩
    have hfour : ∀ i : Fin 57, (DiamondGeometry.cliques i).card ≤ 4 := by decide +kernel
    have hle := hfour i
    rw [hi] at hle
    omega
  | succ m ih =>
    exact SingleVertexGraph.cliqueFree_five ih
      (by simpa only [frame_card] using (show 3 ≤ 3 from le_rfl))

theorem edge_count (m : ℕ) : (edgeFamily (graph m)).card = 25+3*m := by
  induction m with
  | zero =>
    rw [graph,DiamondGeometry.edge_family_eq]
    decide +kernel
  | succ m ih =>
    rw [graph,SingleVertexGraph.edgeFamily_card,ih,frame_card]
    omega

theorem actual_summand (m : ℕ) : IsMinkowskiSummand (basePolytope (function m))
    (((m+4 : ℕ) : ℝ) • graphicalZonotope (graph m)) := by
  apply (isMinkowskiSummand_graphical_iff (extreme m).1.1 (extreme m).2.1
    (Nat.cast_nonneg (m+4))).mpr
  exact ⟨graphical m,fun u v huv _ S hu hv => elemental_upper m u v huv S hu hv⟩

theorem full_dimension (m : ℕ) : FullDimension (basePolytope (function m)) := by
  exact finrank_vectorSpan_eq_of_connected_slacks (extreme m).1.1 (extreme m).2.1
    (connected m) (fun u v huv => by
      obtain ⟨S,hu,hv,hp⟩ := positive_slack m u v huv
      exact ⟨S,hu,hv,ne_of_gt hp⟩)

theorem actual_direction_graph (m : ℕ) :
    actualDirectionGraph (basePolytope (function m)) = graph m := by
  apply SimpleGraph.ext
  funext u v
  apply propext
  constructor
  · intro he
    obtain ⟨R,hR,hRc,hnR,hQR⟩ := actual_summand m
    exact basePolytope_summand_actualRootEdge (extreme m).1.1 (extreme m).2.1 (graph m)
      (Nat.cast_nonneg (m+4)) R hQR he
  · intro he
    obtain ⟨S,hu,hv,hp⟩ := positive_slack m u v he
    exact exposedSegment_of_positive_delta (extreme m).1.1 (extreme m).2.1 he.ne hu hv hp

theorem lattice (m : ℕ) : LatticePolytope (basePolytope (function m)) :=
  (integerValued m).basePolytope (extreme m).1.1 (extreme m).2.1

end SparseFamily
end GraphicalZonotopes

end
end
end BundlePart337

section BundlePart338
/- Source: Papers/GraphicalZonotopes/TreewidthLowDegree.lean -/




/-! # A degree consequence of an ordinary tree decomposition

The proof prunes redundant leaf bags. A vertex exclusive to a leaf bag has
all its neighbors in that bag. This is the standard degeneracy consequence
of bounded treewidth, with the full connected-occurrence condition used.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem tree_bags_have_low_degree [Nonempty V] (G : SimpleGraph V) (w : ℕ)
    {I : Type} [Fintype I] [DecidableEq I] (T : SimpleGraph I) (bag : I → Finset V)
    (hT : T.IsTree) (hsize : ∀ i, (bag i).card ≤ w+1)
    (hcover : ∀ v, ∃ i, v ∈ bag i)
    (hedge : ∀ u v, G.Adj u v → ∃ i, u ∈ bag i ∧ v ∈ bag i)
    (hconn : ∀ v, (T.induce {i | v ∈ bag i}).Connected) :
    ∃ v : V, G.degree v ≤ w := by
  classical
  have single (I : Type) [Fintype I] [DecidableEq I] (bag : I → Finset V)
      (hs : ∀ i, (bag i).card ≤ w+1)
      (he : ∀ u v, G.Adj u v → ∃ i, u ∈ bag i ∧ v ∈ bag i)
      (r : I) (v : V) (hv : v ∈ bag r)
      (honly : ∀ i, v ∈ bag i → i = r) : ∃ v : V, G.degree v ≤ w := by
    refine ⟨v,?_⟩
    have hsub : G.neighborFinset v ⊆ (bag r).erase v := by
      intro u hu
      have hAdj := (G.mem_neighborFinset v u).mp hu
      obtain ⟨i,hvi,hui⟩ := he v u hAdj
      have hir := honly i hvi
      subst i
      exact mem_erase.mpr ⟨hAdj.ne.symm,hui⟩
    have hc := card_le_card hsub
    rw [SimpleGraph.card_neighborFinset_eq_degree,card_erase_of_mem hv] at hc
    have hb := hs r
    omega
  suffices aux : ∀ n : ℕ, ∀ (J : Type) [Fintype J] [DecidableEq J],
      Fintype.card J = n → ∀ (H : SimpleGraph J) (b : J → Finset V),
      H.IsTree → (∀ i, (b i).card ≤ w+1) →
      (∀ v, ∃ i, v ∈ b i) →
      (∀ u v, G.Adj u v → ∃ i, u ∈ b i ∧ v ∈ b i) →
      (∀ v, (H.induce {i | v ∈ b i}).Connected) → ∃ v : V, G.degree v ≤ w from
    aux _ I rfl T bag hT hsize hcover hedge hconn
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro J _ _ hcard H b htree hs hc he hcon
    by_cases hsub : Subsingleton J
    · letI : Subsingleton J := hsub
      obtain ⟨r⟩ := htree.connected.nonempty
      let v : V := Classical.choice inferInstance
      have hv : v ∈ b r := by
        obtain ⟨i,hi⟩ := hc v
        simpa only [Subsingleton.elim i r] using hi
      exact single J b hs he r v hv (fun i _ => Subsingleton.elim _ _)
    · letI : Nontrivial J := not_subsingleton_iff_nontrivial.mp hsub
      obtain ⟨r,hrdeg⟩ := htree.exists_vert_degree_one_of_nontrivial
      obtain ⟨q,hrq,hqonly⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hrdeg
      have hqr : q ≠ r := hrq.ne.symm
      by_cases hleaf : b r ⊆ b q
      · let J' := {i : J // i ≠ r}
        let H' : SimpleGraph J' := H.induce {r}ᶜ
        let b' : J' → Finset V := fun i => b i.1
        have htree' : H'.IsTree :=
          ⟨htree.connected.induce_compl_singleton_of_degree_eq_one hrdeg,
            htree.isAcyclic.induce _⟩
        have hc' : ∀ v, ∃ i : J', v ∈ b' i := by
          intro v
          obtain ⟨i,hi⟩ := hc v
          by_cases hir : i = r
          · subst i
            exact ⟨⟨q,hqr⟩,hleaf hi⟩
          · exact ⟨⟨i,hir⟩,hi⟩
        have he' : ∀ u v, G.Adj u v → ∃ i : J', u ∈ b' i ∧ v ∈ b' i := by
          intro u v huv
          obtain ⟨i,hu,hv⟩ := he u v huv
          by_cases hir : i = r
          · subst i
            exact ⟨⟨q,hqr⟩,hleaf hu,hleaf hv⟩
          · exact ⟨⟨i,hir⟩,hu,hv⟩
        have hcon' : ∀ v, (H'.induce {i | v ∈ b' i}).Connected := by
          intro v
          let K := H.induce {i | v ∈ b i}
          let S : Set {i : J // v ∈ b i} := {i | i.1 ≠ r}
          have hpre : (K.induce S).Preconnected := by
            apply (hcon v).preconnected.induce_of_degree_eq_one
            intro i hi
            have hir : i.1 = r := by
              by_contra hne
              exact hi hne
            intro j hj k hk
            apply Subtype.ext
            have hj' : H.Adj i.1 j.1 := hj
            have hk' : H.Adj i.1 k.1 := hk
            have hjq : j.1 = q := hqonly j.1 (by simpa only [hir] using hj')
            have hkq : k.1 = q := hqonly k.1 (by simpa only [hir] using hk')
            exact hjq.trans hkq.symm
          let e : (H'.induce {i | v ∈ b' i}) ≃g (K.induce S) :=
            { toFun := fun i => ⟨⟨i.1.1,i.2⟩,i.1.2⟩
              invFun := fun i => ⟨⟨i.1.1,i.2⟩,i.1.2⟩
              left_inv := by intro i; rfl
              right_inv := by intro i; rfl
              map_rel_iff' := by intro i j; rfl }
          have hpre' := e.preconnected_iff.mpr hpre
          obtain ⟨i,hi⟩ := hc' v
          letI : Nonempty ({i : J' | v ∈ b' i} : Set J') := ⟨⟨i,hi⟩⟩
          exact ⟨hpre'⟩
        have hlt : Fintype.card J' < n := by
          rw [← hcard]
          exact Fintype.card_subtype_lt (x := r) (by simp)
        exact ih _ hlt J' rfl H' b' htree' (fun i => hs i.1) hc' he' hcon'
      · obtain ⟨v,hvr,hvq⟩ := not_subset.mp hleaf
        apply single J b hs he r v hvr
        intro i hvi
        by_contra hir
        let r' : {i : J // v ∈ b i} := ⟨r,hvr⟩
        let i' : {i : J // v ∈ b i} := ⟨i,hvi⟩
        have hri : r' ≠ i' := fun hh => hir (congrArg Subtype.val hh).symm
        obtain ⟨j,hj⟩ := ((hcon v) r' i').nonempty_neighborSet_left hri
        have hjq : j.1 = q := hqonly j.1 hj
        exact hvq (hjq ▸ j.2)

theorem HasTreewidthAtMost.exists_degree_le {G : SimpleGraph V} [Nonempty V] {w : ℕ}
    (h : HasTreewidthAtMost G w) : ∃ v : V, G.degree v ≤ w := by
  obtain ⟨m,T,bag,hT,hs,hc,he,hcon⟩ := h
  exact tree_bags_have_low_degree G w T bag hT hs hc he hcon

end GraphicalZonotopes

end
end
end BundlePart338

section BundlePart339
/- Source: Papers/GraphicalZonotopes/TreewidthOperations.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset BooleanModule BooleanVertexExtension
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- Relabeling graph vertices preserves the number of unordered edges.
No order on the vertex types is needed. -/
theorem edgeFamily_card_map (e : V ↪ W) (G : SimpleGraph V) :
    (edgeFamily (G.map e)).card = (edgeFamily G).card := by
  classical
  rw [edgeFamily_eq_image_edgeFinset,
    card_image_of_injective _ sym2_toFinset_injective,
    edgeFamily_eq_image_edgeFinset,
    card_image_of_injective _ sym2_toFinset_injective]
  simpa only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] using
    SimpleGraph.card_edgeFinset_map e G

theorem HasTreewidthAtMost.comap {G : SimpleGraph V} {w : ℕ}
    (h : HasTreewidthAtMost G w) (e : W ↪ V) : HasTreewidthAtMost (G.comap e) w := by
  obtain ⟨m,T,bag,hT,hs,hc,he,hcon⟩ := h
  let b : Fin m → Finset W := fun i => SetFunctionEmbedding.pullSet e (bag i)
  refine ⟨m,T,b,hT,?_,?_,?_,?_⟩
  · intro i
    have hsub : (b i).map e ⊆ bag i := by
      intro v hv
      obtain ⟨u,hu,rfl⟩ := mem_map.mp hv
      exact (SetFunctionEmbedding.mem_pullSet e _ _).mp hu
    have hcard := card_le_card hsub
    rw [card_map] at hcard
    exact hcard.trans (hs i)
  · intro v
    obtain ⟨i,hi⟩ := hc (e v)
    exact ⟨i,(SetFunctionEmbedding.mem_pullSet e _ _).mpr hi⟩
  · intro u v huv
    obtain ⟨i,hu,hv⟩ := he (e u) (e v) huv
    exact ⟨i,(SetFunctionEmbedding.mem_pullSet e _ _).mpr hu,
      (SetFunctionEmbedding.mem_pullSet e _ _).mpr hv⟩
  · intro v
    have hsets : {i | v ∈ b i} = {i | e v ∈ bag i} := by
      ext i
      exact SetFunctionEmbedding.mem_pullSet e _ _
    rw [hsets]
    exact hcon (e v)

/-- A finite tree decomposition with one specified bag containing the
displayed boundary. The index type is only presentation data. -/
structure RootedTreeDecomposition (G : SimpleGraph V) (w : ℕ) (B : Finset V) where
  Index : Type
  [indexFintype : Fintype Index]
  [indexDecidableEq : DecidableEq Index]
  tree : SimpleGraph Index
  bag : Index → Finset V
  root : Index
  isTree : tree.IsTree
  size : ∀ i, (bag i).card ≤ w+1
  cover : ∀ v, ∃ i, v ∈ bag i
  edge : ∀ u v, G.Adj u v → ∃ i, u ∈ bag i ∧ v ∈ bag i
  occurrence : ∀ v, (tree.induce {i | v ∈ bag i}).Connected
  boundary : B ⊆ bag root

attribute [instance] RootedTreeDecomposition.indexFintype RootedTreeDecomposition.indexDecidableEq

theorem RootedTreeDecomposition.hasTreewidthAtMost {G : SimpleGraph V} {w : ℕ}
    {B : Finset V} (d : RootedTreeDecomposition G w B) : HasTreewidthAtMost G w := by
  let e := Fintype.equivFin d.Index
  let T : SimpleGraph (Fin (Fintype.card d.Index)) := d.tree.comap e.symm
  let bag : Fin (Fintype.card d.Index) → Finset V := fun i => d.bag (e.symm i)
  let iso : T ≃g d.tree := { e.symm with map_rel_iff' := by intros; rfl }
  refine ⟨Fintype.card d.Index,T,bag,iso.isTree_iff.mpr d.isTree,
    fun i => d.size (e.symm i),?_,?_,?_⟩
  · intro v
    obtain ⟨i,hi⟩ := d.cover v
    exact ⟨e i,by simpa only [bag,Equiv.symm_apply_apply] using hi⟩
  · intro u v huv
    obtain ⟨i,hu,hv⟩ := d.edge u v huv
    exact ⟨e i,by simpa only [bag,Equiv.symm_apply_apply] using hu,
      by simpa only [bag,Equiv.symm_apply_apply] using hv⟩
  · intro v
    let e' : (T.induce {i | v ∈ bag i}) ≃g (d.tree.induce {i | v ∈ d.bag i}) :=
      { toFun := fun i => ⟨e.symm i.1,i.2⟩
        invFun := fun i => ⟨e i.1,by
          change v ∈ d.bag (e.symm (e i.1))
          simpa only [Equiv.symm_apply_apply] using (show v ∈ d.bag i.1 from i.2)⟩
        left_inv := by intro i; apply Subtype.ext; simp
        right_inv := by intro i; apply Subtype.ext; simp
        map_rel_iff' := by intros; rfl }
    exact e'.connected_iff.mpr (d.occurrence v)

def RootedTreeDecomposition.restrictBoundary {G : SimpleGraph V} {w : ℕ}
    {B C : Finset V} (d : RootedTreeDecomposition G w B) (h : C ⊆ B) :
    RootedTreeDecomposition G w C := { d with boundary := h.trans d.boundary }

theorem edgeFamily_card_eq_edgeFinset_card (G : SimpleGraph V) :
    (edgeFamily G).card = G.edgeFinset.card := by
  rw [edgeFamily_eq_image_edgeFinset,card_image_of_injective _ sym2_toFinset_injective]

theorem SingleVertexGraph.isTree_singleton {G : SimpleGraph V} (hG : G.IsTree) (r : V) :
    (SingleVertexGraph.graph G {r}).IsTree := by
  apply (SimpleGraph.isTree_iff_connected_and_card).mpr
  refine ⟨SingleVertexGraph.connected hG.connected (singleton_nonempty _),?_⟩
  simp only [Nat.card_eq_fintype_card,Fintype.card_sum,Fintype.card_fin]
  rw [← SimpleGraph.edgeFinset_card,← edgeFamily_card_eq_edgeFinset_card,
    SingleVertexGraph.edgeFamily_card,card_singleton,edgeFamily_card_eq_edgeFinset_card,
    hG.card_edgeFinset]

/-- Appending a leaf bag proves the ordinary width bound after attaching a
new graph vertex to vertices already sharing the specified boundary bag. -/
def RootedTreeDecomposition.append {G : SimpleGraph V} {w : ℕ} {B : Finset V}
    (d : RootedTreeDecomposition G w B) (hB : B.card ≤ w) :
    RootedTreeDecomposition (SingleVertexGraph.graph G B) w
      (insert (Sum.inr 0) (hubSet (J := Fin 1) B)) := by
  let I := d.Index
  let T : SimpleGraph (BooleanVertexExtension.Vertex I) :=
    SingleVertexGraph.graph d.tree {d.root}
  let bag : BooleanVertexExtension.Vertex I → Finset (BooleanVertexExtension.Vertex V)
    | Sum.inl i => hubSet (d.bag i)
    | Sum.inr _ => insert (Sum.inr 0) (hubSet B)
  refine {
    Index := BooleanVertexExtension.Vertex I
    tree := T
    bag := bag
    root := Sum.inr 0
    isTree := SingleVertexGraph.isTree_singleton d.isTree d.root
    size := ?_
    cover := ?_
    edge := ?_
    occurrence := ?_
    boundary := Subset.rfl }
  · intro i
    cases i with
    | inl i => simpa only [bag,hubSet,card_map] using d.size i
    | inr j =>
      change (insert (Sum.inr 0) (hubSet (J := Fin 1) B)).card ≤ w+1
      rw [card_insert_of_notMem (notMem_hubSet_outer B (0 : Fin 1)),hubSet,card_map]
      omega
  · intro v
    cases v with
    | inl v =>
      obtain ⟨i,hi⟩ := d.cover v
      exact ⟨Sum.inl i,by simpa only [bag,mem_hubSet_hub] using hi⟩
    | inr j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact ⟨Sum.inr 0,mem_insert_self _ _⟩
  · intro u v huv
    cases u with
    | inl u =>
      cases v with
      | inl v =>
        obtain ⟨i,hu,hv⟩ := d.edge u v huv
        exact ⟨Sum.inl i,by simpa only [bag,mem_hubSet_hub] using hu,
          by simpa only [bag,mem_hubSet_hub] using hv⟩
      | inr j =>
        have hj : j = 0 := Subsingleton.elim _ _
        subst j
        change u ∈ B at huv
        exact ⟨Sum.inr 0,by simpa only [bag,mem_insert,Sum.inl_ne_inr,false_or,
          mem_hubSet_hub] using huv,mem_insert_self _ _⟩
    | inr i =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      cases v with
      | inl v =>
        change v ∈ B at huv
        exact ⟨Sum.inr 0,mem_insert_self _ _,by simpa only [bag,mem_insert,
          Sum.inl_ne_inr,false_or,mem_hubSet_hub] using huv⟩
      | inr j => exact False.elim huv
  · intro v
    cases v with
    | inl v =>
      let f : (d.tree.induce {i | v ∈ d.bag i}) →g (T.induce {i | Sum.inl v ∈ bag i}) :=
        { toFun := fun i => ⟨Sum.inl i.1,by
            change Sum.inl v ∈ hubSet (J := Fin 1) (d.bag i.1)
            exact (mem_hubSet_hub _ _).mpr i.2⟩
          map_rel' := by intro i j hij; exact hij }
      obtain ⟨i,hi⟩ := d.cover v
      apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
      refine ⟨f ⟨i,hi⟩,?_⟩
      intro j
      rcases j with ⟨j,hj⟩
      cases j with
      | inl k =>
        have hk : v ∈ d.bag k := by
          change Sum.inl v ∈ hubSet (J := Fin 1) (d.bag k) at hj
          exact (mem_hubSet_hub _ _).mp hj
        exact ((d.occurrence v) ⟨i,hi⟩ ⟨k,hk⟩).map f
      | inr k =>
        have hk : k = 0 := Subsingleton.elim _ _
        subst k
        have hvB : v ∈ B := by
          change Sum.inl v ∈ insert (Sum.inr 0) (hubSet (J := Fin 1) B) at hj
          simpa only [mem_insert,Sum.inl_ne_inr,false_or,mem_hubSet_hub] using hj
        have hvr : v ∈ d.bag d.root := d.boundary hvB
        refine (((d.occurrence v) ⟨i,hi⟩ ⟨d.root,hvr⟩).map f).trans ?_
        apply SimpleGraph.Adj.reachable
        exact mem_singleton_self _
    | inr v =>
      have hv : v = 0 := Subsingleton.elim _ _
      subst v
      apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
      refine ⟨⟨Sum.inr 0,mem_insert_self _ _⟩,?_⟩
      rintro ⟨i,hi⟩
      cases i with
      | inl i =>
        change Sum.inr (0 : Fin 1) ∈ hubSet (d.bag i) at hi
        exact False.elim (notMem_hubSet_outer _ _ hi)
      | inr i =>
        have hi0 : i = 0 := Subsingleton.elim _ _
        subst i
        exact SimpleGraph.Reachable.rfl

end GraphicalZonotopes

end
end
end BundlePart339

section BundlePart340
/- Source: Papers/GraphicalZonotopes/SparseFamilyTreewidth.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.SparseFamily
open Finset BooleanModule

def baseBags : Fin 6 → Finset (Fin 10) :=
  ![{0,1,2,3,4},{0,1,2,3,5},{0,1,2,3,6},
    {0,1,2,3,7},{0,1,2,3,8},{0,1,2,3,9}]

theorem baseBag_occurrence (v : Fin 10) :
    {i : Fin 6 | v ∈ baseBags i} = Set.univ ∨
      ∃ j : Fin 6, {i : Fin 6 | v ∈ baseBags i} = {j} := by
  fin_cases v
  · left; ext i; fin_cases i <;> simp [baseBags]
  · left; ext i; fin_cases i <;> simp [baseBags]
  · left; ext i; fin_cases i <;> simp [baseBags]
  · left; ext i; fin_cases i <;> simp [baseBags]
  · right; refine ⟨0,?_⟩; ext i; fin_cases i <;> simp [baseBags]
  · right; refine ⟨1,?_⟩; ext i; fin_cases i <;> simp [baseBags]
  · right; refine ⟨2,?_⟩; ext i; fin_cases i <;> simp [baseBags]
  · right; refine ⟨3,?_⟩; ext i; fin_cases i <;> simp [baseBags]
  · right; refine ⟨4,?_⟩; ext i; fin_cases i <;> simp [baseBags]
  · right; refine ⟨5,?_⟩; ext i; fin_cases i <;> simp [baseBags]

def base_decomposition : RootedTreeDecomposition DiamondGeometry.graph 4 ({0,1,6} : Finset (Fin 10)) where
  Index := Fin 6
  tree := SimpleGraph.pathGraph 6
  bag := baseBags
  root := 2
  isTree := SimpleGraph.isTree_pathGraph_add_one 5
  size := by decide +kernel
  cover := by decide +kernel
  edge := by decide +kernel
  occurrence := by
    intro v
    rcases baseBag_occurrence v with h | ⟨i,h⟩
    · rw [h]
      exact (SimpleGraph.induceUnivIso _).connected_iff.mpr
        (SimpleGraph.connected_pathGraph_add_one 5)
    · rw [h,SimpleGraph.induce_singleton_eq_top]
      letI : Nonempty ({i} : Set (Fin 6)) := ⟨⟨i,by simp⟩⟩
      exact SimpleGraph.connected_top
  boundary := by decide +kernel

def rooted_decomposition : (m : ℕ) →
    RootedTreeDecomposition (graph m) 4 ({first m,second m,tip m} : Finset (Vertex m))
  | 0 => base_decomposition
  | m+1 =>
    ((rooted_decomposition m).append (by rw [frame_card]; omega)).restrictBoundary (by
      intro x hx
      simp only [frame,first,second,tip,mem_insert,mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> simp)

theorem width_at_most_four (m : ℕ) : HasTreewidthAtMost (graph m) 4 :=
  (rooted_decomposition m).hasTreewidthAtMost

def coreEmbedding : Fin 6 ↪ Fin 10 where
  toFun := ![0,1,2,3,8,9]
  inj' := by decide +kernel

def coreGraph : SimpleGraph (Fin 6) := DiamondGeometry.graph.comap coreEmbedding

instance coreGraphDecidable : DecidableRel coreGraph.Adj := by
  unfold coreGraph
  infer_instance

/-- The induced six-vertex `K₂ * C₄` core has minimum degree four. -/
theorem core_minimum_degree : ∀ v : Fin 6, 4 ≤ coreGraph.degree v := by
  decide +kernel

theorem base_not_width_three : ¬HasTreewidthAtMost DiamondGeometry.graph 3 := by
  intro h
  have hc : HasTreewidthAtMost coreGraph 3 := h.comap coreEmbedding
  obtain ⟨v,hv⟩ := hc.exists_degree_le
  have hm := core_minimum_degree v
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hv hm
  omega

def baseEmbedding : (m : ℕ) → Fin 10 ↪ Vertex m
  | 0 => Function.Embedding.refl _
  | m+1 => (baseEmbedding m).trans SingleVertexGraph.old

theorem graph_comap_base (m : ℕ) : (graph m).comap (baseEmbedding m) = DiamondGeometry.graph := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have he : (graph (m+1)).comap (baseEmbedding (m+1)) = (graph m).comap (baseEmbedding m) := rfl
    exact he.trans ih

theorem not_width_three (m : ℕ) : ¬HasTreewidthAtMost (graph m) 3 := by
  intro h
  have hb := h.comap (baseEmbedding m)
  rw [graph_comap_base] at hb
  exact base_not_width_three hb

end GraphicalZonotopes.SparseFamily

end
end
end BundlePart340

section BundlePart341
/- Source: Papers/GraphicalZonotopes/ThreeTreePruneExtension.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace SingleVertexGraph
open Finset BooleanModule BooleanVertexExtension SetFunctionEmbedding
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem all_vertices_eq_insert :
    (univ : Finset (BooleanVertexExtension.Vertex V)) =
      insert (Sum.inr 0) (hubSet (J := Fin 1) (univ : Finset V)) := by
  ext x
  cases x with
  | inl v => simp
  | inr j =>
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    simp

/-- A spanning admissible three-tree survives deleting a newly attached
vertex with at most three available neighbors. The proof uses exact edge
counts on arbitrary induced subsets, so no construction order is assumed. -/
theorem admissible_spanning_prune {G : SimpleGraph V} {N : Finset V}
    (hV : 4 ≤ Fintype.card V) (hN : N.card ≤ 3)
    (h : HasAdmissibleSpanningThreeTree (graph G N)) :
    HasAdmissibleSpanningThreeTree G := by
  obtain ⟨H,hHG,hH,hA⟩ := h
  let C : Finset (BooleanVertexExtension.Vertex V) := hubSet (univ : Finset V)
  have hC : C.card = Fintype.card V := by simp [C,hubSet]
  have hw : Sum.inr 0 ∉ C := notMem_hubSet_outer _ _
  have hsize : (edgeFamily H).card = 3*(Fintype.card V+1)-6 := by
    simpa only [card_univ,Fintype.card_sum,Fintype.card_fin] using hH.edgeFamily_card
  have hnb : earlierNeighbors H C (Sum.inr 0) ⊆ hubSet (J := Fin 1) N := by
    intro x hx
    obtain ⟨hxC,hwx⟩ := (mem_earlierNeighbors _ _ _ _).mp hx
    cases x with
    | inl v =>
      exact (mem_hubSet_hub _ _).mpr (hHG hwx)
    | inr j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact False.elim (hw hxC)
  have hnb3 : (earlierNeighbors H C (Sum.inr 0)).card ≤ 3 := by
    have hh := card_le_card hnb
    simp only [hubSet,card_map] at hh
    exact hh.trans hN
  have hsplit : (edgeFamily H).card = (edgeFamily (inducedOn H C)).card +
      (earlierNeighbors H C (Sum.inr 0)).card := by
    have hh := induced_edge_count_insert H C (Sum.inr 0) hw
    have hu : insert (Sum.inr 0) C = univ := all_vertices_eq_insert.symm
    rw [hu,inducedOn_univ] at hh
    exact hh
  have hbound := hH.induced_edge_bound C (subset_univ C) (by omega)
  have he : (edgeFamily (inducedOn H C)).card = 3*C.card-6 := by omega
  have hp : ThreeTreeOn C (inducedOn H C) :=
    hH.induced_equality C (subset_univ C) (by omega) he
  have hrange : ∀ x ∈ C, x ∈ Set.range (old : V ↪ BooleanVertexExtension.Vertex V) := by
    intro x hx
    obtain ⟨v,hv,hvx⟩ := mem_map.mp hx
    exact ⟨v,hvx⟩
  have hcomap : (inducedOn H C).comap old = H.comap old := by
    ext u v
    change (H.Adj (Sum.inl u) (Sum.inl v) ∧ Sum.inl u ∈ C ∧ Sum.inl v ∈ C) ↔ _
    simp [C,old]
  have hset : pullSet old C = univ := by
    ext v
    simp [C,old]
  have htOld : IsThreeTree (H.comap old) := by
    have ht := hp.comap old hrange
    rw [hcomap,hset] at ht
    exact ht
  have hAP : Admissible (inducedOn H C) := by
    intro T hT hcl
    exact (triangleMultiplicity_mono (inducedOn_le H C) T).trans
      (hA T hT (fun u hu v hv huv => (hcl hu hv huv).1))
  have hmap : ((inducedOn H C).comap old).map old = inducedOn H C :=
    map_comap_of_supported old _ (fun u v huv => hrange u huv.2.1)
  have hAO : Admissible (H.comap old) := by
    have hh := Admissible.of_map old (G := (inducedOn H C).comap old) (by rwa [hmap])
    rwa [hcomap] at hh
  exact ⟨H.comap old,fun u v huv => hHG huv,htOld,hAO⟩

end SingleVertexGraph
end GraphicalZonotopes

end
end
end BundlePart341

section BundlePart342
/- Source: Papers/GraphicalZonotopes/SparseFamilyMinimality.lean -/








@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset

namespace SparseFamily

theorem no_admissible_spanning (m : ℕ) : ¬HasAdmissibleSpanningThreeTree (graph m) := by
  induction m with
  | zero =>
    rintro ⟨H,hHG,hH,hA⟩
    exact DiamondBook.no_admissible_spanning_threeTree 6 (by omega)
      ⟨H,hHG.trans DiamondBook.diamond_support_subgraph,hH,hA⟩
  | succ m ih =>
    intro h
    apply ih
    exact SingleVertexGraph.admissible_spanning_prune
      (by rw [vertex_card]; omega)
      (by simpa only [frame_card] using (show 3 ≤ 3 from le_rfl)) h

end SparseFamily

/-- One edge above the absolute lower bound, the absence of an admissible
spanning three-tree makes every actual supporting edge indispensable. -/
theorem edgeMinimalSupporting_of_one_excess {n : ℕ} (hn : 4 ≤ n)
    {G : SimpleGraph (Fin n)} (hc : (edgeFamily G).card = 3*n-5)
    (hno : ¬HasAdmissibleSpanningThreeTree G) (hs : SupportsFullIndecomposable G) :
    EdgeMinimalSupporting G := by
  refine ⟨hs,?_⟩
  intro H hHG hsupport
  obtain ⟨Q,hQ,hi,hd,hw⟩ := hsupport
  obtain ⟨z,hzs,hze,hzd⟩ := weak_summand_extreme_or_zero hQ hi hw
  have hfull : Module.finrank ℝ (vectorSpan ℝ (basePolytope z.1)) = n-1 := by
    rw [← hzd]
    simpa only [FullDimension,Fintype.card_fin] using hd
  have hz : ExtremeSupermodular z.1 := by
    rcases hze with hzero | he
    · rw [hzero,basePolytope_zero,_root_.vectorSpan_singleton,_root_.finrank_bot] at hfull
      omega
    · exact he
  let A := actualDirectionGraph (basePolytope z.1)
  have hAH : A ≤ H := fun u v huv =>
    RefinedTriangleComponents.actualRootEdge_of_graphical hz.1.1 hz.2.1 z.2.2 huv
  have hstrict : edgeFamily H ⊂ edgeFamily G := by
    apply ssubset_iff_subset_ne.mpr
    refine ⟨edgeFamily_mono hHG.le,?_⟩
    intro he
    exact hHG.ne (graph_eq_of_edgeFamily_eq he)
  have hHcount := card_lt_card hstrict
  have hAcount := card_le_card (edgeFamily_mono hAH)
  obtain ⟨hlower,heq⟩ := hz.direction_count_bound hn hfull
  have he : directionCount (basePolytope z.1) = 3*n-6 := by
    change 3*n-6 ≤ (edgeFamily A).card at hlower
    change (edgeFamily A).card = _
    omega
  have htree : IsThreeTree A := heq he
  have hsA : SupportsFullIndecomposable A := by
    refine ⟨basePolytope z.1,?_,hz.minkowskiIndecomposable,?_,?_⟩
    · exact (show IsGeneralizedPermutahedron (basePolytope z.1) from
        ⟨z.1,hz.1.1,hz.2.1,rfl⟩).finitePolytope
    · simpa only [FullDimension,Fintype.card_fin] using hfull
    · exact (isWeakMinkowskiSummand_graphical_iff hz.1.1 hz.2.1).mpr
        (graphical_actualDirectionGraph hz.1.1 hz.2.1)
  have hA := (threeTree_supports_iff_admissible hn htree).mp hsA
  exact hno ⟨A,hAH.trans hHG.le,htree,hA⟩

end GraphicalZonotopes

end
end
end BundlePart342

section BundlePart343
/- Source: Papers/GraphicalZonotopes/SparseFamilyPrincipal.lean -/







/-! # Theorem 8.2 in its complete geometric form

Every order `n ≥ 10` has a genuine graph of treewidth exactly four and a
full-dimensional lattice indecomposable summand in the asserted dilation.
The actual exposed-root direction graph is proved equal to that graph, and
every proper edge-subgraph is excluded from supporting a full-dimensional ray.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.SparseFamily
open Finset SetFunctionEmbedding
open scoped BigOperators Pointwise

theorem complete_family (n : ℕ) (hn : 10 ≤ n) :
    ∃ G : SimpleGraph (Fin n), ∃ Q : Set (Fin n → ℝ),
      G.CliqueFree 5 ∧ (edgeFamily G).card = 3*n-5 ∧
      HasTreewidthAtMost G 4 ∧ ¬HasTreewidthAtMost G 3 ∧
      EdgeMinimalSupporting G ∧ LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
      FullDimension Q ∧ actualDirectionGraph Q = G ∧
      IsMinkowskiSummand Q (((n-6 : ℕ) : ℝ) • graphicalZonotope G) ∧
      ¬∃ H : SimpleGraph (Fin n), H ≤ G ∧ IsThreeTree H ∧ SupportsFullIndecomposable H := by
  let m := n-10
  have hcard : Fintype.card (Vertex m) = n := by rw [vertex_card]; dsimp [m]; omega
  letI : Nonempty (Vertex m) := (connected m).nonempty
  let e : Vertex m ≃ Fin n := Fintype.equivOfCardEq (by simpa only [Fintype.card_fin] using hcard)
  let G : SimpleGraph (Fin n) := (graph m).map e.toEmbedding
  let z : SetFunction (Fin n) := extend e.toEmbedding (function m)
  have hz : ExtremeSupermodular z := extend_extreme e.toEmbedding (extreme m)
  have hzi : IntegerValued z := extend_integer e.toEmbedding (integerValued m)
  have hzg : Graphical G z := by
    apply extend_graphical e.toEmbedding
    change Graphical (((graph m).map e.toEmbedding).comap e.toEmbedding) (function m)
    rw [SimpleGraph.comap_map_eq]
    exact graphical m
  have hM : m+4 = n-6 := by dsimp [m]; omega
  have hbound : ∀ u v : Fin n, u ≠ v → ∀ S, u ∉ S → v ∉ S → delta z u v S ≤ (n-6 : ℕ) := by
    intro u v huv S hu hv
    obtain ⟨a,rfl⟩ := e.surjective u
    obtain ⟨b,rfl⟩ := e.surjective v
    change delta (extend e.toEmbedding (function m)) (e.toEmbedding a) (e.toEmbedding b) S ≤ _
    rw [delta_extend e.toEmbedding (function m) a b S]
    simpa only [hM] using elemental_upper m a b (fun he => huv (congrArg e he))
      (pullSet e.toEmbedding S) (by simpa only [mem_pullSet,Equiv.toEmbedding_apply] using hu)
      (by simpa only [mem_pullSet,Equiv.toEmbedding_apply] using hv)
  have hsum : IsMinkowskiSummand (basePolytope z)
      (((n-6 : ℕ) : ℝ) • graphicalZonotope G) := by
    apply (isMinkowskiSummand_graphical_iff hz.1.1 hz.2.1 (Nat.cast_nonneg (n-6))).mpr
    exact ⟨hzg,fun u v huv _ S hu hv => hbound u v huv S hu hv⟩
  have hdim : FullDimension (basePolytope z) := by
    change Module.finrank ℝ (vectorSpan ℝ (basePolytope (extend e.toEmbedding (function m)))) = _
    rw [finrank_vectorSpan_extend e.toEmbedding (extreme m).1]
    have hd := full_dimension m
    change Module.finrank ℝ (vectorSpan ℝ (basePolytope (function m))) =
      Fintype.card (Vertex m)-1 at hd
    simpa only [hcard,Fintype.card_fin] using hd
  have hactual : actualDirectionGraph (basePolytope z) = G := by
    apply SimpleGraph.ext
    funext u v
    apply propext
    constructor
    · intro he
      obtain ⟨R,hR,hRc,hnR,hQR⟩ := hsum
      exact basePolytope_summand_actualRootEdge hz.1.1 hz.2.1 G
        (Nat.cast_nonneg (n-6)) R hQR he
    · intro he
      obtain ⟨a,b,hab,rfl,rfl⟩ := (SimpleGraph.map_adj e.toEmbedding (graph m) u v).mp he
      obtain ⟨S,ha,hb,hp⟩ := positive_slack m a b hab
      apply exposedSegment_of_positive_delta hz.1.1 hz.2.1
        (fun he => hab.ne (e.injective he)) (S := S.map e.toEmbedding)
        (by simpa using ha) (by simpa using hb)
      change 0 < delta (extend e.toEmbedding (function m))
        (e.toEmbedding a) (e.toEmbedding b) (S.map e.toEmbedding)
      rw [delta_extend e.toEmbedding (function m) a b (S.map e.toEmbedding),pullSet_map]
      exact hp
  have hcf : G.CliqueFree 5 := SimpleGraph.cliqueFree_map_iff.mpr (cliqueFree_five m)
  have hedge : (edgeFamily G).card = 3*n-5 := by
    change (edgeFamily ((graph m).map e.toEmbedding)).card = _
    rw [edgeFamily_card_map,edge_count]
    dsimp [m]
    omega
  have hw4 : HasTreewidthAtMost G 4 := by
    have hh := (width_at_most_four m).comap e.symm.toEmbedding
    rwa [SimpleGraph.comap_symm] at hh
  have hnw3 : ¬HasTreewidthAtMost G 3 := by
    intro hh
    have hback := hh.comap e.toEmbedding
    rw [show G = (graph m).map e.toEmbedding from rfl,SimpleGraph.comap_map_eq] at hback
    exact not_width_three m hback
  have hno : ¬HasAdmissibleSpanningThreeTree G := by
    intro hh
    have hback := hh.map_equiv e.symm
    rw [SimpleGraph.map_symm,show G = (graph m).map e.toEmbedding from rfl,
      SimpleGraph.comap_map_eq] at hback
    exact no_admissible_spanning m hback
  have hsupport : SupportsFullIndecomposable G :=
    ⟨basePolytope z,(show IsGeneralizedPermutahedron (basePolytope z) from
      ⟨z,hz.1.1,hz.2.1,rfl⟩).finitePolytope,hz.minkowskiIndecomposable,hdim,
      (n-6 : ℕ),by exact_mod_cast (show 0 < n-6 by omega),hsum⟩
  refine ⟨G,basePolytope z,hcf,hedge,hw4,hnw3,
    edgeMinimalSupporting_of_one_excess (by omega) hedge hno hsupport,
    hzi.basePolytope hz.1.1 hz.2.1,hz.minkowskiIndecomposable,hdim,hactual,hsum,?_⟩
  rintro ⟨H,hHG,hH,hS⟩
  exact hno ⟨H,hHG,hH,(threeTree_supports_iff_admissible (by omega) hH).mp hS⟩

/-- The exact pinned principal target, discharged by the stronger literal
statement above, including all orders and the asserted dilation. -/
theorem paper_theorem_8_2 : Targets.SparseTreewidthFourFamily := by
  intro n hn
  obtain ⟨G,Q,hcf,he,hw4,hnw3,hmin,hQ,hI,hD,hA,hS,hno⟩ := complete_family n hn
  exact ⟨G,hcf,he,hw4,hnw3,hmin,Q,hQ,hI,hD,hS⟩

/-- The same family using only ordinary polytopal indecomposability. The
proper-subgraph conclusion is expanded explicitly so the convention used
inside `EdgeMinimalSupporting` is not an implicit semantic assumption. -/
theorem paper_theorem_8_2_polytopal (n : ℕ) (hn : 10 ≤ n) :
    ∃ G : SimpleGraph (Fin n), ∃ Q : Set (Fin n → ℝ),
      G.CliqueFree 5 ∧ (edgeFamily G).card = 3*n-5 ∧
      HasTreewidthAtMost G 4 ∧ ¬HasTreewidthAtMost G 3 ∧
      LatticePolytope Q ∧ PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
      actualDirectionGraph Q = G ∧
      IsMinkowskiSummand Q (((n-6 : ℕ) : ℝ) • graphicalZonotope G) ∧
      (∀ H : SimpleGraph (Fin n),H < G →
        ¬∃ R : Set (Fin n → ℝ),IsFinitePolytope R ∧
          PolytopalMinkowskiIndecomposable R ∧ FullDimension R ∧
          IsWeakMinkowskiSummand R (graphicalZonotope H)) ∧
      ¬∃ H : SimpleGraph (Fin n),H ≤ G ∧ IsThreeTree H ∧
        ∃ R : Set (Fin n → ℝ),IsFinitePolytope R ∧
          PolytopalMinkowskiIndecomposable R ∧ FullDimension R ∧
          IsWeakMinkowskiSummand R (graphicalZonotope H) := by
  obtain ⟨G,Q,hcf,he,hw4,hnw3,hmin,hQ,hI,hD,hA,hS,hno⟩ := complete_family n hn
  have hpoly : PolytopalMinkowskiIndecomposable Q :=
    ⟨hI.1,fun P R hP hR hsum => hI.2 P R hP.compact hR.compact hP.convex hR.convex hsum⟩
  refine ⟨G,Q,hcf,he,hw4,hnw3,hQ,hpoly,hD,hA,hS,?_,?_⟩
  · intro H hHG
    rintro ⟨R,hR,hi,hd,hs⟩
    exact hmin.2 H hHG
      ⟨R,hR,(weakSummand_indecomposable_iff_polytopal hR hs).mpr hi,hd,hs⟩
  · rintro ⟨H,hHG,hH,R,hR,hi,hd,hs⟩
    exact hno ⟨H,hHG,hH,
      R,hR,(weakSummand_indecomposable_iff_polytopal hR hs).mpr hi,hd,hs⟩

end GraphicalZonotopes.SparseFamily

end
end
end BundlePart343

section BundlePart344
/- Source: Papers/GraphicalZonotopes/ThreeTreePaperStatements.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
open scoped Pointwise

/-- The existence predicate in Theorem 6.1 is unchanged if indecomposability
is quantified over ordinary polytopes instead of all compact convex bodies.
The generalized-permutahedron presentation is derived from the actual sum. -/
theorem supportsFullIndecomposable_iff_polytopal {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    SupportsFullIndecomposable G ↔
      ∃ Q : Set (V → ℝ), IsFinitePolytope Q ∧ PolytopalMinkowskiIndecomposable Q ∧
        FullDimension Q ∧ IsWeakMinkowskiSummand Q (graphicalZonotope G) := by
  constructor
  · rintro ⟨Q,hQ,hi,hd,hs⟩
    refine ⟨Q,hQ,⟨hi.1,?_⟩,hd,hs⟩
    intro P R hP hR he
    exact hi.2 P R hP.compact hR.compact hP.convex hR.convex he
  · rintro ⟨Q,hQ,hi,hd,a,ha,R,hR,hcR,hnR,he⟩
    obtain ⟨hn,hsm,hbody,_,_⟩ := actual_summand_lowerSupport
      hQ.compact hQ.convex hi.1 hR hcR hnR ha.le he
    have hgp : IsGeneralizedPermutahedron Q := ⟨lowerSupport Q,hn,hsm,hbody⟩
    exact ⟨Q,hQ,(minkowskiIndecomposable_iff_polytopal hgp).mpr hi,hd,
      a,ha,R,hR,hcR,hnR,he⟩

/-- The two equivalences of Theorem 6.1 with the paper's literal maximal-clique
and induced-deletion conditions and its ordinary polytope convention. The
quantitative lattice witness is `admissible_threeTree_lattice_witness`. -/
theorem threeTree_classification_polytopal {n : ℕ} (hn : 4≤ n)
    {G : SimpleGraph (Fin n)} (hG : IsThreeTree G) :
    ((∃ Q : Set (Fin n → ℝ), IsFinitePolytope Q ∧
      PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G)) ↔
      ∀ T : Finset (Fin n),T.card=3 → G.IsClique T →
        (univ.filter (fun C : Finset (Fin n) => C.card=4 ∧
          Maximal G.IsClique (C : Set (Fin n)) ∧ T⊆C)).card≤3) ∧
    ((∃ Q : Set (Fin n → ℝ), IsFinitePolytope Q ∧
      PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G)) ↔
      ∀ T : Finset (Fin n),T.card=3 → G.IsClique T →
        Nat.card (G.induce ((T : Set (Fin n))ᶜ)).ConnectedComponent≤3) := by
  have h := threeTree_classification_literal hn hG
  exact ⟨(supportsFullIndecomposable_iff_polytopal G).symm.trans h.1,
    (supportsFullIndecomposable_iff_polytopal G).symm.trans h.2⟩

end GraphicalZonotopes

end
end
end BundlePart344

section BundlePart345
/- Source: Papers/GraphicalZonotopes/TriangleFreeSeparator.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace Separator
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} {B : Finset V}

/-- The induced boundary contains no triangle. This is expressed directly in
the ambient graph so the vertices outside the boundary are irrelevant. -/
def TriangleFreeBoundary (G : SimpleGraph V) (B : Finset V) : Prop :=
  ∀ T : Finset V, T ⊆ B → T.card = 3 → ¬G.IsClique T

theorem commonNeighbors_boundary_eq_empty (hB : TriangleFreeBoundary G B)
    (e : BoundaryEdge G B) : commonNeighbors G e.1.1.1 e.1.1.2 ∩ B = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro w hw
  obtain ⟨hwN,hwB⟩ := mem_inter.mp hw
  obtain ⟨huw,hvw⟩ := (mem_commonNeighbors G _ _ w).mp hwN
  have ht := (SimpleGraph.is3Clique_triple_iff (G := G)).mpr ⟨e.1.2.2,huw,hvw⟩
  exact hB {e.1.1.1,e.1.1.2,w}
    (by simp only [insert_subset_iff,singleton_subset_iff]; exact ⟨e.2.1,e.2.2,hwB⟩)
    ht.card_eq ht.isClique

def boundaryEdgeClique (e : BoundaryEdge G B) : ↥(boundaryCliques G B) :=
  ⟨{e.1.1.1,e.1.1.2},by
    apply mem_filter.mpr
    refine ⟨mem_powerset.mpr ?_,?_,?_⟩
    · exact insert_subset e.2.1 (singleton_subset_iff.mpr e.2.2)
    · simp [card_pair (ne_of_lt e.1.2.1)]
    · simpa only [Finset.coe_pair] using
        (SimpleGraph.isClique_pair).mpr (fun _ => e.1.2.2)⟩

theorem boundaryEdgeClique_injective :
    Function.Injective (boundaryEdgeClique (G := G) (B := B)) := by
  intro e f hef
  have he : ({e.1.1.1,e.1.1.2} : Finset V) = {f.1.1.1,f.1.1.2} :=
    congrArg Subtype.val hef
  have h₁ : e.1.1.1 = f.1.1.1 ∨ e.1.1.1 = f.1.1.2 := by
    have hh : e.1.1.1 ∈ ({f.1.1.1,f.1.1.2} : Finset V) := by rw [← he]; simp
    simpa only [mem_insert,mem_singleton] using hh
  have h₂ : e.1.1.2 = f.1.1.1 ∨ e.1.1.2 = f.1.1.2 := by
    have hh : e.1.1.2 ∈ ({f.1.1.1,f.1.1.2} : Finset V) := by rw [← he]; simp
    simpa only [mem_insert,mem_singleton] using hh
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · rcases h₁ with h₁ | h₁
    · exact h₁
    · rcases h₂ with h₂ | h₂
      · exact False.elim (lt_asymm e.1.2.1 (by simpa only [h₁,h₂] using f.1.2.1))
      · exact False.elim ((ne_of_lt e.1.2.1) (h₁.trans h₂.symm))
  · rcases h₂ with h₂ | h₂
    · rcases h₁ with h₁ | h₁
      · exact False.elim ((ne_of_lt e.1.2.1) (h₁.trans h₂.symm))
      · exact False.elim (lt_asymm e.1.2.1 (by simpa only [h₁,h₂] using f.1.2.1))
    · exact h₂

/-- A triangle-free boundary has at most one active private block. This is
the exact specialization of Lemma 5.1 used in Corollary 5.2. -/
theorem triangle_free_boundary_capacity (hB : TriangleFreeBoundary G B)
    (z : graphicalFunctionSpace G) (hz : ExtremeSupermodular z.1) :
    Fintype.card (Gluing.ActiveBranch
      (((functionEquiv (componentPartition G B)).symm z).2)) ≤ 1 := by
  have hc := induced_separator_capacity G B z hz
  have hsum : (∑ e : BoundaryEdge G B,
      2^(commonNeighbors G e.1.1.1 e.1.1.2 ∩ B).card) = Fintype.card (BoundaryEdge G B) := by
    simp only [commonNeighbors_boundary_eq_empty hB,card_empty,pow_zero,sum_const,
      card_univ,smul_eq_mul,mul_one]
  have hcard : Fintype.card (BoundaryEdge G B) ≤ (boundaryCliques G B).card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective
      (boundaryEdgeClique (G := G) (B := B)) boundaryEdgeClique_injective
  rw [hsum,Nat.sub_eq_zero_of_le hcard,zero_add] at hc
  exact hc

end Separator

open Finset

/-- Corollary 5.2: deleting a triangle-free boundary leaves at most one
component whenever a full-dimensional indecomposable weak summand exists. -/
theorem SupportsFullIndecomposable.triangle_free_components_le_one {n : ℕ} (hn : 2 ≤ n)
    {G : SimpleGraph (Fin n)} (hG : SupportsFullIndecomposable G)
    (B : Finset (Fin n)) (hB : Separator.TriangleFreeBoundary G B) :
    Nat.card ((G.induce ((B : Set (Fin n))ᶜ)).ConnectedComponent) ≤ 1 := by
  classical
  obtain ⟨z,hz,hd⟩ := hG.exists_extreme_function hn
  let x := (Separator.functionEquiv (Separator.componentPartition G B)).symm z
  have ha : ∀ j,x.2 j ≠ 0 := fun j =>
    Separator.private_block_ne_zero_of_fullDimension hn (Separator.componentPartition G B)
      z hz.2.1 hd j (Separator.componentPart_nonempty G B j)
  let e : Gluing.ActiveBranch x.2 ≃ (Separator.outsideGraph G B).ConnectedComponent := {
    toFun := Subtype.val
    invFun := fun j => ⟨j,ha j⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hc := Separator.triangle_free_boundary_capacity hB z hz
  change Fintype.card (Gluing.ActiveBranch x.2) ≤ 1 at hc
  rw [Fintype.card_congr e] at hc
  change Nat.card ((Separator.outsideGraph G B).ConnectedComponent) ≤ 1
  rw [@Nat.card_eq_fintype_card _ (Separator.componentFintype G B)]
  exact hc

/-- The paper's literal conclusion: every set whose deletion disconnects the
graph contains all three vertices of an actual graph triangle. -/
theorem SupportsFullIndecomposable.separator_contains_triangle {n : ℕ} (hn : 2 ≤ n)
    {G : SimpleGraph (Fin n)} (hG : SupportsFullIndecomposable G)
    (B : Finset (Fin n))
    (hsep : 2 ≤ Nat.card ((G.induce ((B : Set (Fin n))ᶜ)).ConnectedComponent)) :
    ∃ T : Finset (Fin n),T ⊆ B ∧ T.card = 3 ∧ G.IsClique T := by
  by_contra h
  have hB : Separator.TriangleFreeBoundary G B := by
    intro T hTB hT hc
    exact h ⟨T,hTB,hT,hc⟩
  have hb := hG.triangle_free_components_le_one hn B hB
  omega

/-- In particular, deleting fewer than three vertices cannot disconnect a
supporting graph. This quantifies over all such vertex sets. -/
theorem SupportsFullIndecomposable.delete_lt_three_preconnected {n : ℕ} (hn : 4 ≤ n)
    {G : SimpleGraph (Fin n)} (hG : SupportsFullIndecomposable G)
    (B : Finset (Fin n)) (hB : B.card < 3) :
    (G.induce ((B : Set (Fin n))ᶜ)).Preconnected := by
  have ht : Separator.TriangleFreeBoundary G B := by
    intro T hTB hT _
    have hc := card_le_card hTB
    omega
  have hc := hG.triangle_free_components_le_one (by omega) B ht
  letI : Subsingleton ((G.induce ((B : Set (Fin n))ᶜ)).ConnectedComponent) :=
    Fintype.card_le_one_iff_subsingleton.mp
      (by simpa only [Nat.card_eq_fintype_card] using hc)
  intro u v
  exact SimpleGraph.ConnectedComponent.exact (Subsingleton.elim _ _)

end GraphicalZonotopes

end
end
end BundlePart345

section BundlePart346
/- Source: Papers/GraphicalZonotopes/TwoHubGraphMaps.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes.TwoHub
open Finset
variable {I J I' J' : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype I'] [DecidableEq I'] [Fintype J'] [DecidableEq J']

def vertexEmbedding (e : I↪I') (f : J↪J') : ((Bool⊕I)⊕J)↪((Bool⊕I')⊕J') :=
  Function.Embedding.sumMap (Function.Embedding.sumMap (Function.Embedding.refl Bool) e) f

@[simp] theorem vertexEmbedding_color (e : I↪I') (f : J↪J') (x : (Bool⊕I)⊕J) :
    color (vertexEmbedding e f x)=color x := by
  rcases x with (v|i)|j
  · cases v <;> rfl
  · rfl
  · rfl

theorem graph_le_comap (e : I↪I') (f : J↪J') :
    graph (I:=I) (J:=J)≤(graph (I:=I') (J:=J')).comap (vertexEmbedding e f) := by
  intro x y hxy
  change color (vertexEmbedding e f x)≠ color (vertexEmbedding e f y)
  simpa [graph] using hxy

def swapVertex : ((Bool⊕I)⊕J)→((Bool⊕J)⊕I)
  | .inl (.inl v) => .inl (.inl v)
  | .inl (.inr i) => .inr i
  | .inr j => .inl (.inr j)

@[simp] theorem swapVertex_swap (x : (Bool⊕I)⊕J) : swapVertex (swapVertex x)=x := by
  rcases x with (v|i)|j <;> rfl

def swapEquiv : ((Bool⊕I)⊕J)≃((Bool⊕J)⊕I) where
  toFun:=swapVertex
  invFun:=swapVertex
  left_inv:=swapVertex_swap
  right_inv:=swapVertex_swap

def swapGraphIso : graph (I:=I) (J:=J)≃g graph (I:=J) (J:=I) where
  toEquiv:=swapEquiv
  map_rel_iff':=by
    intro x y
    change color (swapVertex x)≠ color (swapVertex y) ↔ color x≠ color y
    rcases x with (v|i)|j <;> rcases y with (w|k)|l
    · cases v <;> cases w <;> simp [swapVertex,color]
    · cases v <;> simp [swapVertex,color]
    · cases v <;> simp [swapVertex,color]
    · cases w <;> simp [swapVertex,color]
    · simp [swapVertex,color]
    · simp [swapVertex,color]
    · cases w <;> simp [swapVertex,color]
    · simp [swapVertex,color]
    · simp [swapVertex,color]

def twoSingletonSwap (p b : ℕ) : twoSingletonGraph p b≃g twoSingletonGraph b p :=
  (finGraphIso p b).symm.trans
    ((swapGraphIso (I:=Fin p) (J:=Fin b)).trans (finGraphIso b p))

theorem maximum_dimension_swap (p b : ℕ) :
    maximumIndecomposableDimension (twoSingletonGraph p b)=
      maximumIndecomposableDimension (twoSingletonGraph b p) :=
  maximumIndecomposableDimension_iso (twoSingletonSwap p b)

end GraphicalZonotopes.TwoHub

end
end
end BundlePart346

section BundlePart347
/- Source: Papers/GraphicalZonotopes/FourColorResource.lean -/







@[expose] public section
noncomputable section
open scoped Classical BigOperators
namespace GraphicalZonotopes.FourColorResource
open Finset Function

def total (a : Fin 4 → ℕ) : ℕ := ∑ i,a i

def Balanced (a : Fin 4 → ℕ) : Prop :=
  (∀ i,0< a i) ∧ ∀ i,3*a i+3≤2*total a

theorem total_ge_four {a : Fin 4 → ℕ} (ha : ∀ i,0< a i) : 4≤ total a := by
  calc
    4=∑ i : Fin 4,(1 : ℕ) := by simp
    _≤ total a := sum_le_sum (fun i _ => ha i)

theorem total_update (a : Fin 4 → ℕ) (i : Fin 4) (k : ℕ) :
    total (update a i k)+a i=total a+k := by
  fin_cases i <;> simp [total,Fin.sum_univ_succ] <;> omega

theorem pair_bound {a : Fin 4 → ℕ} (ha : ∀ i,0< a i)
    (i j : Fin 4) (hij : i≠ j) : a i+a j+2≤ total a := by
  have h0 := ha 0
  have h1 := ha 1
  have h2 := ha 2
  have h3 := ha 3
  fin_cases i <;> fin_cases j <;> simp [total,Fin.sum_univ_succ] at hij ⊢ <;> omega

theorem eq_one_of_total_four {a : Fin 4 → ℕ} (ha : ∀ i,0< a i)
    (hN : total a=4) : a=(fun _ => 1) := by
  have h0 := ha 0
  have h1 := ha 1
  have h2 := ha 2
  have h3 := ha 3
  have hs : a 0+(a 1+(a 2+a 3))=4 := by
    simpa [total,Fin.sum_univ_succ] using hN
  have hall : a 0=1 ∧ a 1=1 ∧ a 2=1 ∧ a 3=1 :=
    ⟨by omega,by omega,by omega,by omega⟩
  funext i
  fin_cases i
  · exact hall.1
  · exact hall.2.1
  · exact hall.2.2.1
  · exact hall.2.2.2

/-- Removing one vertex from a largest part preserves the exact balance
inequalities. Reversing this removal gives strictly positive capacity in the
part to which the vertex is subsequently added. -/
theorem remove_largest {a : Fin 4 → ℕ} (ha : Balanced a) (hN : 4< total a) :
    ∃ i : Fin 4,1< a i ∧
      Balanced (update a i (a i-1)) ∧
      total (update a i (a i-1))+1=total a ∧
      3*(update a i (a i-1) i)+3<2*total (update a i (a i-1)) := by
  obtain ⟨i,_,hmax⟩ := exists_max_image (univ : Finset (Fin 4)) a (by simp)
  have hm : ∀ j,a j≤ a i := fun j => hmax j (mem_univ _)
  have hi : 1< a i := by
    by_contra hni
    have hs : total a≤4 := by
      calc
        total a≤∑ j : Fin 4,(1 : ℕ) := sum_le_sum (fun j _ => by have h := hm j;omega)
        _=4 := by simp
    omega
  let b := update a i (a i-1)
  have htotal : total b+1=total a := by
    have h := total_update a i (a i-1)
    dsimp only [b]
    omega
  have hbi : b i=a i-1 := by simp [b]
  have hb : Balanced b := by
    constructor
    · intro j
      by_cases hji : j=i
      · subst j;rw [hbi];omega
      · simpa [b,update_of_ne hji] using ha.1 j
    · intro j
      by_cases hji : j=i
      · subst j
        have h := ha.2 i
        rw [hbi]
        omega
      · have hp := pair_bound ha.1 i j (Ne.symm hji)
        have hmi := hm j
        have hjpos := ha.1 j
        have hbjeq : b j=a j := by simp [b,update_of_ne hji]
        rw [hbjeq]
        omega
  refine ⟨i,hi,hb,htotal,?_⟩
  have h := ha.2 i
  change 3*b i+3<2*total b
  rw [hbi]
  omega

/-- A finite sequence of color additions, starting with one vertex of each
color and using a color only when its triangle capacity is positive. -/
inductive Schedule : (Fin 4 → ℕ) → Prop
  | initial : Schedule (fun _ => 1)
  | add {a : Fin 4 → ℕ} (h : Schedule a) (i : Fin 4)
      (hcapacity : 3*a i+3<2*total a) : Schedule (update a i (a i+1))

/-- Every positive, balanced four-part size vector has a valid unbounded
attachment schedule. No bound on any part size is imposed. -/
theorem schedule_of_balanced {a : Fin 4 → ℕ} (ha : Balanced a) : Schedule a := by
  suffices ∀ N : ℕ,∀ a : Fin 4 → ℕ,total a=N → Balanced a → Schedule a from
    this (total a) a rfl ha
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro a hN ha
    by_cases hfour : total a=4
    · rw [eq_one_of_total_four ha.1 hfour]
      exact Schedule.initial
    · have hgt : 4< total a := by have h := total_ge_four ha.1;omega
      obtain ⟨i,hi,hb,hbN,hcap⟩ := remove_largest ha hgt
      let b := update a i (a i-1)
      have hs : Schedule b := ih (total b) (by dsimp only [b];omega) b rfl hb
      have hstep := Schedule.add hs i hcap
      have he : update b i (b i+1)=a := by
        funext j
        by_cases hji : j=i
        · subst j
          simp only [b,update_self]
          omega
        · simp [b,update_of_ne hji]
      rwa [he] at hstep

end GraphicalZonotopes.FourColorResource

end
end
end BundlePart347

section BundlePart348
/- Source: Papers/GraphicalZonotopes/FourPartThreeTreeCounts.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace GraphicalZonotopes.FourPartThreeTreeCounts
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

def Proper (c : V → Fin 4) (G : SimpleGraph V) : Prop :=
  ∀ u v,G.Adj u v → c u≠ c v

def Avoids (c : V → Fin 4) (i : Fin 4) (T : Finset V) : Prop :=
  ∀ v∈T,c v≠ i

def missingFacet (c : V → Fin 4) (i : Fin 4) (D : Finset V) : Finset V :=
  D.filter (fun v => c v≠ i)

def avoidingTriangles (G : SimpleGraph V) (c : V → Fin 4) (i : Fin 4) :
    Finset (Finset V) := (triangles G).filter (Avoids c i)

@[simp] theorem mem_avoidingTriangles (G : SimpleGraph V) (c : V → Fin 4)
    (i : Fin 4) (T : Finset V) :
    T∈avoidingTriangles G c i ↔ T.card=3 ∧ G.IsClique T ∧ Avoids c i T := by
  simp only [avoidingTriangles,mem_filter,mem_triangles,and_assoc]

theorem color_injective_on_clique {G : SimpleGraph V} {c : V → Fin 4}
    (hc : Proper c G) {D : Finset V} (hD : G.IsClique D) : Set.InjOn c D := by
  intro u hu v hv he
  by_contra huv
  exact hc u v (hD hu hv huv) he

theorem color_count_tetrahedron {G : SimpleGraph V} {c : V → Fin 4}
    (hc : Proper c G) {D : Finset V} (hD : D.card=4) (hcl : G.IsClique D)
    (i : Fin 4) : (D.filter (fun v => c v=i)).card=1 := by
  have hinj := color_injective_on_clique hc hcl
  have himage : (D.image c).card=4 := (card_image_iff.mpr hinj).trans hD
  have hsurj : D.image c=univ := eq_of_subset_of_card_le (subset_univ _) (by simpa using himage.ge)
  have hi : i∈D.image c := by rw [hsurj]; simp
  obtain ⟨v,hv,hvi⟩ := mem_image.mp hi
  have he : D.filter (fun u => c u=i)={v} := by
    ext u
    simp only [mem_filter,mem_singleton]
    constructor
    · rintro ⟨hu,hui⟩
      exact hinj hu hv (hui.trans hvi.symm)
    · rintro rfl
      exact ⟨hv,hvi⟩
  rw [he,card_singleton]

theorem missingFacet_card {G : SimpleGraph V} {c : V → Fin 4}
    (hc : Proper c G) {D : Finset V} (hD : D.card=4) (hcl : G.IsClique D)
    (i : Fin 4) : (missingFacet c i D).card=3 := by
  have h1 := color_count_tetrahedron hc hD hcl i
  have hsum := card_filter_add_card_filter_not (s := D) (fun v => c v=i)
  change (D.filter (fun v => c v=i)).card+(missingFacet c i D).card=D.card at hsum
  omega

theorem missingFacet_avoids (c : V → Fin 4) (i : Fin 4) (D : Finset V) :
    Avoids c i (missingFacet c i D) := fun v hv => (mem_filter.mp hv).2

theorem missingFacet_subset (c : V → Fin 4) (i : Fin 4) (D : Finset V) :
    missingFacet c i D⊆D := filter_subset _ _

theorem missingFacet_clique {G : SimpleGraph V} {c : V → Fin 4}
    {D : Finset V} (hcl : G.IsClique D) (i : Fin 4) :
    G.IsClique (missingFacet c i D) := by
  intro u hu v hv huv
  exact hcl (missingFacet_subset c i D hu) (missingFacet_subset c i D hv) huv

theorem avoiding_triangle_unique {G : SimpleGraph V} {c : V → Fin 4}
    (hc : Proper c G) {D T : Finset V} (hD : D.card=4) (hcl : G.IsClique D)
    (hT : T.card=3) (hTD : T⊆D) {i : Fin 4} (havoid : Avoids c i T) :
    T=missingFacet c i D := by
  apply eq_of_subset_of_card_le
  · intro v hv
    exact mem_filter.mpr ⟨hTD hv,havoid v hv⟩
  · rw [missingFacet_card hc hD hcl,hT]

theorem avoidingTriangles_mono {G H : SimpleGraph V} (hGH : G≤ H)
    (c : V → Fin 4) (i : Fin 4) :
    avoidingTriangles G c i⊆avoidingTriangles H c i := by
  intro T hT
  obtain ⟨ht,hcl,ha⟩ := (mem_avoidingTriangles _ _ _ _).mp hT
  exact (mem_avoidingTriangles _ _ _ _).mpr
    ⟨ht,fun u hu v hv huv => hGH (hcl hu hv huv),ha⟩

theorem missingFacet_mem {G : SimpleGraph V} {c : V → Fin 4}
    (hc : Proper c G) {D : Finset V} (hD : D.card=4) (hcl : G.IsClique D)
    (i : Fin 4) : missingFacet c i D∈avoidingTriangles G c i :=
  (mem_avoidingTriangles _ _ _ _).mpr
    ⟨missingFacet_card hc hD hcl i,missingFacet_clique hcl i,missingFacet_avoids c i D⟩

theorem avoiding_subsets_singleton {G : SimpleGraph V} {c : V → Fin 4}
    (hc : Proper c G) {D : Finset V} (hD : D.card=4) (hcl : G.IsClique D)
    (i : Fin 4) :
    (avoidingTriangles G c i).filter (fun T => T⊆D)={missingFacet c i D} := by
  ext T
  simp only [mem_filter,mem_singleton]
  constructor
  · rintro ⟨hT,hTD⟩
    obtain ⟨ht,_,ha⟩ := (mem_avoidingTriangles _ _ _ _).mp hT
    exact avoiding_triangle_unique hc hD hcl ht hTD ha
  · rintro rfl
    exact ⟨missingFacet_mem hc hD hcl i,missingFacet_subset c i D⟩

theorem avoidingTriangles_cliqueGraph {D : Finset V} (hD : D.card=4)
    {c : V → Fin 4} (hc : Proper c (cliqueGraph D)) (i : Fin 4) :
    avoidingTriangles (cliqueGraph D) c i={missingFacet c i D} := by
  have hcl : (cliqueGraph D).IsClique D := fun u hu v hv huv => ⟨huv,hu,hv⟩
  rw [← avoiding_subsets_singleton hc hD hcl i]
  symm
  apply filter_eq_self.mpr
  intro T hT
  have hh := (mem_avoidingTriangles _ _ _ _).mp hT
  exact (ThreeTreeOn.tetrahedron D hD).clique_subset_active (by omega) hh.2.1

theorem avoidingTriangles_after_attachment {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {u : V} (hu : u∉S) {T : Finset V}
    (hT : T.card=3) (hTS : T⊆S) (hcl : G.IsClique T)
    {c : V → Fin 4} (hc : Proper c (G⊔attachmentStar u T)) (i : Fin 4) :
    avoidingTriangles (G⊔attachmentStar u T) c i =
      if i=c u then avoidingTriangles G c i
      else insert (missingFacet c i (insert u T)) (avoidingTriangles G c i) := by
  have huT : u∉T := fun hm => hu (hTS hm)
  have hD : (insert u T).card=4 := by rw [card_insert_of_notMem huT,hT]
  have hDcl := attached_tetrahedron_clique h hu hTS hcl
  have hM := missingFacet_mem hc hD hDcl i
  have hold := avoidingTriangles_mono (show G≤ G⊔attachmentStar u T from le_sup_left) c i
  ext A
  by_cases hi : i=c u
  · simp only [if_pos hi]
    constructor
    · intro hA
      obtain ⟨ha,hacl,havoid⟩ := (mem_avoidingTriangles _ _ _ _).mp hA
      have huA : u∉A := fun hm => havoid u hm hi.symm
      exact (mem_avoidingTriangles _ _ _ _).mpr ⟨ha,clique_before_attachment huA hacl,havoid⟩
    · exact fun hA => hold hA
  · simp only [if_neg hi,mem_insert]
    constructor
    · intro hA
      obtain ⟨ha,hacl,havoid⟩ := (mem_avoidingTriangles _ _ _ _).mp hA
      by_cases huA : u∈A
      · left
        apply avoiding_triangle_unique hc hD hDcl ha _ havoid
        intro v hv
        by_cases hvu : v=u
        · exact mem_insert.mpr (Or.inl hvu)
        · exact mem_insert.mpr (Or.inr ((attached_vertex_adj_iff h hu hTS v).mp
            (hacl huA hv (Ne.symm hvu))))
      · right
        exact (mem_avoidingTriangles _ _ _ _).mpr ⟨ha,clique_before_attachment huA hacl,havoid⟩
    · rintro (rfl | hA)
      · exact hM
      · exact hold hA

theorem missingFacet_not_old {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {u : V} (hu : u∉S) {T : Finset V}
    {c : V → Fin 4} {i : Fin 4} (hi : i≠ c u) :
    missingFacet c i (insert u T)∉avoidingTriangles G c i := by
  intro hM
  obtain ⟨hm,hcl,_⟩ := (mem_avoidingTriangles _ _ _ _).mp hM
  have hsub := h.clique_subset_active (by omega) hcl
  exact hu (hsub (mem_filter.mpr ⟨mem_insert_self _ _,Ne.symm hi⟩))

/-- The exact number of triangles missing color i is |S|−n_i−2,
expressed without truncated subtraction. -/
theorem avoiding_triangles_card {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {c : V → Fin 4} (hc : Proper c G) (i : Fin 4) :
    (avoidingTriangles G c i).card+(S.filter (fun v => c v=i)).card+2=S.card := by
  induction h with
  | tetrahedron D hD =>
    have hcl : (cliqueGraph D).IsClique D := fun u hu v hv huv => ⟨huv,hu,hv⟩
    rw [avoidingTriangles_cliqueGraph hD hc,card_singleton,color_count_tetrahedron hc hD hcl,hD]
  | @attach S G h u hu T hT hTS hcl ih =>
    have hcG : Proper c G := fun v w hvw => hc v w (Or.inl hvw)
    have hold := ih hcG
    have htri := avoidingTriangles_after_attachment h hu hT hTS hcl hc i
    rw [htri,card_insert_of_notMem hu]
    by_cases hi : i=c u
    · rw [if_pos hi]
      have hcolor : ((insert u S).filter (fun v => c v=i)).card=
          (S.filter (fun v => c v=i)).card+1 := by
        rw [filter_insert]
        simp [hi,hu]
      rw [hcolor]
      omega
    · rw [if_neg hi,card_insert_of_notMem (missingFacet_not_old h hu hi)]
      have hcolor : (insert u S).filter (fun v => c v=i)=S.filter (fun v => c v=i) := by
        simp [filter_insert,Ne.symm hi]
      rw [hcolor]
      omega

/-- Every tetrahedron contributes exactly one incidence to triangles missing
each fixed color, so this sum is the actual tetrahedron count. -/
theorem incidence_sum {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {c : V → Fin 4} (hc : Proper c G) (i : Fin 4) :
    ∑ T∈avoidingTriangles G c i,triangleMultiplicity G T=S.card-3 := by
  have hcount : (∑ T∈avoidingTriangles G c i,triangleMultiplicity G T)=
      ∑ D∈tetrahedra G,((avoidingTriangles G c i).filter (fun T => T⊆D)).card := by
    simp only [triangleMultiplicity,card_eq_sum_ones,sum_filter]
    rw [sum_comm]
  rw [hcount]
  calc
    (∑ D∈tetrahedra G,((avoidingTriangles G c i).filter (fun T => T⊆D)).card)=
        ∑ _D∈tetrahedra G,1 := by
      apply sum_congr rfl
      intro D hD
      obtain ⟨hd,hcl⟩ := (mem_filter.mp hD).2
      rw [avoiding_subsets_singleton hc hd hcl,card_singleton]
    _ = (tetrahedra G).card := by simp
    _ = S.card-3 := h.tetrahedra_card

theorem capacity_nonnegative {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {c : V → Fin 4} (hc : Proper c G)
    (hA : Admissible G) (i : Fin 4) :
    (0 : ℤ)≤2*(S.card : ℤ)-3*((S.filter (fun v => c v=i)).card : ℤ)-3 := by
  have ht := avoiding_triangles_card h hc i
  have hi := incidence_sum h hc i
  have hN := h.active_card_ge_four
  have hb : (∑ T∈avoidingTriangles G c i,triangleMultiplicity G T)≤
      3*(avoidingTriangles G c i).card := by
    calc
      _ ≤ ∑ _T∈avoidingTriangles G c i,3 := by
        apply sum_le_sum
        intro T hT
        obtain ⟨ht,hcl,_⟩ := (mem_avoidingTriangles _ _ _ _).mp hT
        exact hA T ht hcl
      _ = _ := by simp [Nat.mul_comm]
  omega

theorem free_triangle {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {c : V → Fin 4} (hc : Proper c G)
    (i : Fin 4)
    (hpos : (0 : ℤ)<2*(S.card : ℤ)-3*((S.filter (fun v => c v=i)).card : ℤ)-3) :
    ∃ T : Finset V,T.card=3 ∧ G.IsClique T ∧ Avoids c i T ∧
      triangleMultiplicity G T<3 := by
  have ht := avoiding_triangles_card h hc i
  have hi := incidence_sum h hc i
  have hN := h.active_card_ge_four
  by_contra hn
  have hge : ∀ T∈avoidingTriangles G c i,3≤ triangleMultiplicity G T := by
    intro T hT
    obtain ⟨hcard,hcl,ha⟩ := (mem_avoidingTriangles _ _ _ _).mp hT
    by_contra hlt
    exact hn ⟨T,hcard,hcl,ha,by omega⟩
  have hb : 3*(avoidingTriangles G c i).card≤
      ∑ T∈avoidingTriangles G c i,triangleMultiplicity G T := by
    calc
      _ = ∑ _T∈avoidingTriangles G c i,3 := by simp [Nat.mul_comm]
      _ ≤ _ := sum_le_sum hge
  omega

end GraphicalZonotopes.FourPartThreeTreeCounts

end
end
end BundlePart348

section BundlePart349
/- Source: Papers/GraphicalZonotopes/AdmissibleAttachment.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Adding a tetrahedron at a triangle with a free incidence slot preserves
admissibility on every old and new triangle. -/
theorem ThreeTreeOn.admissible_attach {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (hA : Admissible G) {u : V} (hu : u∉S)
    {T : Finset V} (hT : T.card=3) (hTS : T⊆S) (hcl : G.IsClique T)
    (hfree : triangleMultiplicity G T<3) : Admissible (G⊔attachmentStar u T) := by
  intro U hU hcU
  rw [triangleMultiplicity_after_attachment h hu hT hTS hcl]
  by_cases huU : u∈U
  · rw [h.triangleMultiplicity_eq_zero_of_outside hu huU]
    split_ifs <;> omega
  · have hold : G.IsClique U := clique_before_attachment huU hcU
    have hb := hA U hU hold
    by_cases hsub : U⊆insert u T
    · have hUT : U⊆T := by
        intro v hv
        have hm := hsub hv
        rcases mem_insert.mp hm with he | he
        · exact False.elim (huU (he ▸ hv))
        · exact he
      have heq : U=T := eq_of_subset_of_card_le hUT (by omega)
      subst U
      rw [if_pos hsub]
      omega
    · rw [if_neg hsub]
      omega

theorem proper_attachment {c : V → Fin 4} {G : SimpleGraph V}
    (hc : FourPartThreeTreeCounts.Proper c G) {u : V} {T : Finset V}
    (havoid : FourPartThreeTreeCounts.Avoids c (c u) T) :
    FourPartThreeTreeCounts.Proper c (G⊔attachmentStar u T) := by
  intro v w h
  rcases h with h | h
  · exact hc v w h
  · rcases h.2 with ⟨rfl,hw⟩ | ⟨rfl,hv⟩
    · exact Ne.symm (havoid w hw)
    · exact havoid v hv

theorem sum_color_counts (S : Finset V) (c : V → Fin 4) :
    (∑ i : Fin 4,(S.filter (fun v => c v=i)).card)=S.card := by
  simpa using sum_card_fiberwise_eq_card_filter S (univ : Finset (Fin 4)) c

theorem color_count_insert (S : Finset V) (c : V → Fin 4) {u : V} (hu : u∉S)
    (i : Fin 4) : ((insert u S).filter (fun v => c v=i)).card=
      (S.filter (fun v => c v=i)).card+(if c u=i then 1 else 0) := by
  rw [filter_insert]
  split_ifs with hi
  · rw [card_insert_of_notMem (fun hm => hu (mem_filter.mp hm).1)]
  · simp

end GraphicalZonotopes

end
end
end BundlePart349

section BundlePart350
/- Source: Papers/GraphicalZonotopes/FourPartSpanning.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators
namespace GraphicalZonotopes.FourPartSpanning
open Finset Function FourColorResource FourPartThreeTreeCounts
variable {V : Type*} [Fintype V] [DecidableEq V]

def colorSize (c : V → Fin 4) (i : Fin 4) : ℕ :=
  ((univ : Finset V).filter (fun v => c v=i)).card

/-- Realize a complete color schedule inside any fixed finite ambient vertex
set with enough vertices in each color. All unused vertices remain isolated. -/
theorem realize_schedule (c : V → Fin 4) {a : Fin 4 → ℕ} (hs : Schedule a) :
    (∀ i,a i≤ colorSize c i) →
      ∃ S : Finset V,∃ G : SimpleGraph V,ThreeTreeOn S G ∧ Admissible G ∧ Proper c G ∧
        ∀ i,(S.filter (fun v => c v=i)).card=a i := by
  induction hs with
  | initial =>
    intro hbound
    have hw : ∀ i : Fin 4,∃ v : V,c v=i := by
      intro i
      obtain ⟨v,hv⟩ := card_pos.mp (show 0<((univ : Finset V).filter (fun v => c v=i)).card from
        lt_of_lt_of_le Nat.zero_lt_one (hbound i))
      exact ⟨v,(mem_filter.mp hv).2⟩
    choose w hw using hw
    let S := (univ : Finset (Fin 4)).image w
    have hwinj : Injective w := by
      intro i j he
      have h := congrArg c he
      rwa [hw i,hw j] at h
    have hS : S.card=4 := by simp [S,card_image_of_injective _ hwinj]
    have hc : Proper c (cliqueGraph S) := by
      intro u v h he
      obtain ⟨i,_,hi⟩ := mem_image.mp h.2.1
      obtain ⟨j,_,hj⟩ := mem_image.mp h.2.2
      have hij : i=j := by rw [← hw i,← hw j,hi,hj];exact he
      exact h.1 (hi.symm.trans ((congrArg w hij).trans hj))
    have hcl : (cliqueGraph S).IsClique S := fun u hu v hv huv => ⟨huv,hu,hv⟩
    refine ⟨S,cliqueGraph S,ThreeTreeOn.tetrahedron S hS,?_,hc,?_⟩
    · intro T hT ht
      unfold triangleMultiplicity
      calc
        ((tetrahedra (cliqueGraph S)).filter (fun C => T⊆C)).card≤
            (tetrahedra (cliqueGraph S)).card := card_filter_le _ _
        _=1 := by rw [tetrahedra_cliqueGraph hS,card_singleton]
        _≤3 := by omega
    · exact fun i => color_count_tetrahedron hc hS hcl i
  | @add a hs i hcapacity ih =>
    intro hbound
    have holdbound : ∀ j,a j≤ colorSize c j := by
      intro j
      have h := hbound j
      by_cases hji : j=i
      · subst j;simp only [update_self] at h;omega
      · simpa only [update_of_ne hji] using h
    obtain ⟨S,G,h3,hA,hc,hcounts⟩ := ih holdbound
    have hsize : S.card=total a := by
      rw [← sum_color_counts S c]
      exact sum_congr rfl (fun j _ => hcounts j)
    have hpos : (0 : ℤ)<2*(S.card : ℤ)-3*((S.filter (fun v => c v=i)).card : ℤ)-3 := by
      rw [hcounts i,hsize]
      omega
    obtain ⟨T,hT,hcl,havoid,hfree⟩ := free_triangle h3 hc i hpos
    have hTS : T⊆S := h3.clique_subset_active (by omega) hcl
    have hex : ∃ u : V,c u=i ∧ u∉S := by
      by_contra hn
      have hsub : (univ : Finset V).filter (fun v => c v=i)⊆S.filter (fun v => c v=i) := by
        intro u hu
        have hcu := (mem_filter.mp hu).2
        have huS : u∈S := by
          by_contra hnot
          exact hn ⟨u,hcu,hnot⟩
        exact mem_filter.mpr ⟨huS,hcu⟩
      have hcard := card_le_card hsub
      rw [hcounts i] at hcard
      have hi := hbound i
      simp only [update_self] at hi
      change a i+1≤((univ : Finset V).filter (fun v => c v=i)).card at hi
      omega
    obtain ⟨u,hcu,hu⟩ := hex
    refine ⟨insert u S,G⊔attachmentStar u T,h3.attach u hu T hT hTS hcl,
      h3.admissible_attach hA hu hT hTS hcl hfree,?_,?_⟩
    · apply proper_attachment hc
      simpa only [hcu] using havoid
    · intro j
      rw [color_count_insert S c hu j,hcounts j,hcu]
      by_cases hji : j=i
      · subst j;simp
      · simp [update_of_ne hji,Ne.symm hji]

/-- The exact arithmetic balance condition gives an actual admissible
spanning 3-tree inside the graph of different colors. -/
theorem spanning_of_balanced_colors (c : V → Fin 4)
    (ha : Balanced (colorSize c)) :
    ∃ G : SimpleGraph V,IsThreeTree G ∧ Admissible G ∧ Proper c G := by
  obtain ⟨S,G,h3,hA,hc,hcounts⟩ := realize_schedule c (schedule_of_balanced ha) (fun _ => le_rfl)
  have hcard : S.card=(univ : Finset V).card := by
    rw [← sum_color_counts S c,← sum_color_counts (univ : Finset V) c]
    exact sum_congr rfl (fun i _ => hcounts i)
  have hS : S=univ := eq_of_subset_of_card_le (subset_univ S) hcard.ge
  rw [hS] at h3
  exact ⟨G,h3,hA,hc⟩

theorem sigma_colorSize (a : Fin 4 → ℕ) (i : Fin 4) :
    colorSize (fun v : Σ j : Fin 4,Fin (a j) => v.1) i=a i := by
  let e : {v : (Σ j : Fin 4,Fin (a j)) // v.1=i} ≃ Fin (a i) :=
    { toFun := fun v => by rcases v with ⟨⟨j,b⟩,hj⟩;change j=i at hj;subst j;exact b
      invFun := fun b => ⟨⟨i,b⟩,rfl⟩
      left_inv := by rintro ⟨⟨j,b⟩,hj⟩;change j=i at hj;subst j;rfl
      right_inv := by intro b;rfl }
  have h := Fintype.card_congr e
  simpa [colorSize,Fintype.card_subtype] using h

/-- Spanning existence, with the literal maximum part-size inequality. -/
theorem four_partite_spanning_iff (a : Fin 4 → ℕ) (ha : ∀ i,1≤ a i) :
    HasAdmissibleSpanningThreeTree (fourPartite a) ↔
      3*(univ.sup a)≤2*(∑ i,a i)-3 := by
  have htotal : Fintype.card (Σ i : Fin 4,Fin (a i))=∑ i,a i := by simp
  have hN : 4≤ total a := total_ge_four ha
  constructor
  · rintro ⟨G,hG,h3,hA⟩
    have hc : Proper (fun v : Σ i : Fin 4,Fin (a i) => v.1) G :=
      fun u v huv => hG huv
    have hbounds : ∀ i,3*a i+3≤2*total a := by
      intro i
      have h := capacity_nonnegative h3 hc hA i
      change (0 : ℤ)≤2*((univ : Finset (Σ i : Fin 4,Fin (a i))).card : ℤ)-
        3*(colorSize (fun v : Σ i : Fin 4,Fin (a i) => v.1) i : ℤ)-3 at h
      rw [sigma_colorSize,card_univ,htotal] at h
      dsimp [total]
      omega
    obtain ⟨i,hi,he⟩ := exists_mem_eq_sup (univ : Finset (Fin 4)) (by simp) a
    have hb := hbounds i
    rw [he]
    dsimp [total] at hb
    omega
  · intro hb
    have hbal : Balanced a := by
      refine ⟨ha,?_⟩
      intro i
      have hi : a i≤ univ.sup a := le_sup (mem_univ _)
      dsimp [total] at *
      omega
    have hcolors : Balanced (colorSize (fun v : Σ i : Fin 4,Fin (a i) => v.1)) := by
      have he : colorSize (fun v : Σ i : Fin 4,Fin (a i) => v.1)=a := funext (sigma_colorSize a)
      rwa [he]
    obtain ⟨G,h3,hA,hc⟩ := spanning_of_balanced_colors _ hcolors
    exact ⟨G,fun u v huv => hc u v huv,h3,hA⟩

end GraphicalZonotopes.FourPartSpanning

end
end
end BundlePart350

section BundlePart351
/- Source: Papers/GraphicalZonotopes/FourPartCapacity.lean -/





@[expose] public section
noncomputable section
open scoped Classical BigOperators
namespace GraphicalZonotopes.FourColorResource
open Finset Function

theorem single_plus_three_le_total {a : Fin 4 → ℕ} (ha : ∀ i,0< a i)
    (i : Fin 4) : a i+3≤ total a := by
  have h0 := ha 0
  have h1 := ha 1
  have h2 := ha 2
  have h3 := ha 3
  fin_cases i <;> simp [total,Fin.sum_univ_succ] <;> omega

theorem other_parts_mono {a b : Fin 4 → ℕ} (hba : ∀ i,b i≤ a i) (i : Fin 4) :
    total b-b i≤ total a-a i := by
  have h0 := hba 0
  have h1 := hba 1
  have h2 := hba 2
  have h3 := hba 3
  fin_cases i <;> simp [total,Fin.sum_univ_succ] <;> omega

/-- Every balanced active part vector obeys the exact restricted-dimension
bound, even when its largest part differs from the ambient largest part. -/
theorem balanced_dimension_bound {a b : Fin 4 → ℕ}
    (ha : ∀ i,0< a i) (hb : Balanced b) (hba : ∀ i,b i≤ a i) :
    total b-1≤ min (total a-1) (3*(total a-univ.sup a)-4) := by
  obtain ⟨i,hi,he⟩ := exists_mem_eq_sup (univ : Finset (Fin 4)) (by simp) a
  have htotal : total b≤ total a := sum_le_sum (fun i _ => hba i)
  have hother := other_parts_mono hba i
  have hbi := single_plus_three_le_total hb.1 i
  have hai := single_plus_three_le_total ha i
  have hbal := hb.2 i
  rw [he]
  apply le_min
  · omega
  · omega

/-- Truncating one largest part is always optimal. The vector still has all
four positive parts and admits the complete unbounded attachment schedule. -/
theorem optimal_balanced_subcounts (a : Fin 4 → ℕ) (ha : ∀ i,0< a i) :
    ∃ b : Fin 4 → ℕ,Balanced b ∧ (∀ i,b i≤ a i) ∧
      total b-1=min (total a-1) (3*(total a-univ.sup a)-4) := by
  obtain ⟨i,hi,he⟩ := exists_mem_eq_sup (univ : Finset (Fin 4)) (by simp) a
  have hmax : ∀ j,a j≤ a i := by intro j;rw [← he];exact le_sup (mem_univ _)
  let s := total a-a i
  have hsum : a i+s=total a := by
    have h := single_plus_three_le_total ha i
    dsimp [s]
    omega
  have hs : 3≤ s := by have h := single_plus_three_le_total ha i;dsimp [s];omega
  let k := min (a i) (2*s-3)
  have hkpos : 0< k := by have hi := ha i;dsimp [k];omega
  have hkai : k≤ a i := min_le_left _ _
  have hks : k≤2*s-3 := min_le_right _ _
  let b := update a i k
  have hbi : b i=k := by simp [b]
  have hbtotal : total b=s+k := by
    have h := total_update a i k
    change total b+a i=total a+k at h
    omega
  have hbjmax : ∀ j,b j≤ k := by
    intro j
    by_cases hji : j=i
    · subst j;rw [hbi]
    · have hp := pair_bound ha i j (Ne.symm hji)
      have hm := hmax j
      have hj := ha j
      have hjs : a j≤2*s-3 := by omega
      have hmin : a j≤ k := le_min hm hjs
      simpa [b,update_of_ne hji] using hmin
  have hbal : Balanced b := by
    constructor
    · intro j
      by_cases hji : j=i
      · subst j;rwa [hbi]
      · simpa [b,update_of_ne hji] using ha j
    · intro j
      have h := hbjmax j
      rw [hbtotal]
      omega
  refine ⟨b,hbal,?_,?_⟩
  · intro j
    by_cases hji : j=i
    · subst j;rwa [hbi]
    · simp [b,update_of_ne hji]
  · rw [he,hbtotal]
    change s+k-1=min (total a-1) (3*s-4)
    by_cases hcase : a i≤2*s-3
    · have hk : k=a i := min_eq_left hcase
      rw [hk]
      omega
    · have hk : k=2*s-3 := min_eq_right (by omega)
      rw [hk]
      omega

end GraphicalZonotopes.FourColorResource

end
end
end BundlePart351

section BundlePart352
/- Source: Papers/GraphicalZonotopes/FourPartSpectrum.lean -/







@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical BigOperators Pointwise
namespace GraphicalZonotopes
open Finset FourColorResource FourPartThreeTreeCounts FourPartSpanning

/-- The restricted dimension invariant agrees with the ordinary-polytope
notion of indecomposability. The required GP presentation is derived from the
actual weak Minkowski sum for each individual candidate. -/
theorem maximumThreeTreeSupportDimension_eq_polytopal {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    maximumThreeTreeSupportDimension G=
      sSup {d : ℕ | ∃ Q : Set (V → ℝ),IsFinitePolytope Q ∧
        PolytopalMinkowskiIndecomposable Q ∧
        IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
        (∃ S,ThreeTreeOn S (actualDirectionGraph Q)) ∧
        Module.finrank ℝ (vectorSpan ℝ Q)=d} := by
  unfold maximumThreeTreeSupportDimension
  congr 1
  ext d
  constructor
  · rintro ⟨Q,hQ,hi,hw,hT,hd⟩
    refine ⟨Q,hQ,⟨hi.1,?_⟩,hw,hT,hd⟩
    intro P R hP hR he
    exact hi.2 P R hP.compact hR.compact hP.convex hR.convex he
  · rintro ⟨Q,hQ,hi,hw,hT,hd⟩
    obtain ⟨t,ht,R,hR,hRc,hnR,he⟩ := hw
    obtain ⟨hn,hs,hbody,_,_⟩ := actual_summand_lowerSupport
      hQ.compact hQ.convex hi.1 hR hRc hnR ht.le he
    have hgp : IsGeneralizedPermutahedron Q := ⟨lowerSupport Q,hn,hs,hbody⟩
    exact ⟨Q,hQ,(minkowskiIndecomposable_iff_polytopal hgp).mpr hi,
      ⟨t,ht,R,hR,hRc,hnR,he⟩,hT,hd⟩

/-- The color capacity bound applies to the actual support of every real
indecomposable weak summand. Full dimension on that active support is derived. -/
theorem four_partite_threeTree_dimension_bound (a : Fin 4 → ℕ)
    (ha : ∀ i,1≤ a i) {Q : Set ((Σ i : Fin 4,Fin (a i)) → ℝ)}
    (hQ : IsFinitePolytope Q) (hi : MinkowskiIndecomposable Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope (fourPartite a)))
    {S : Finset (Σ i : Fin 4,Fin (a i))}
    (hT : ThreeTreeOn S (actualDirectionGraph Q)) :
    Module.finrank ℝ (vectorSpan ℝ Q)≤
      min ((∑ i,a i)-1) (3*((∑ i,a i)-univ.sup a)-4) := by
  let o : LinearOrder (Σ i : Fin 4,Fin (a i)) := Separator.finiteVertexOrder _
  letI : LinearOrder (Σ i : Fin 4,Fin (a i)) :=
    { o with
      toDecidableEq := inferInstance
      compare := fun x y => @compareOfLessAndEq _ x y o.toLT (o.toDecidableLT x y) inferInstance
      compare_eq_compareOfLessAndEq := by intros;rfl }
  obtain ⟨t,ht,R,hR,hRc,hnR,he⟩ := hw
  obtain ⟨hfn,hfs,hbody,hgraph,_⟩ := actual_summand_lowerSupport
    hQ.compact hQ.convex hi.1 hR hRc hnR ht.le he
  let f := lowerSupport Q
  let z := normalize f
  have hzn : TranslationNormalized z := normalize_translationNormalized hfn
  have hzs : Supermodular z := hfs.normalize
  have hzg : Graphical (fourPartite a) z := by
    intro u v huv hnon T hu hv
    rw [delta_normalize f huv hu hv]
    exact hgraph u v huv hnon T hu hv
  have hactual : actualDirectionGraph (basePolytope z)=actualDirectionGraph Q := by
    rw [actualDirectionGraph_normalize,← hbody]
  have hTz : ThreeTreeOn S (actualDirectionGraph (basePolytope z)) := by
    rwa [hactual]
  have hne : z≠0 := threeTree_actual_nonzero hzn.1 hzs hTz
  have hz : ExtremeSupermodular z := by
    apply MinkowskiIndecomposable.extremeSupermodular_normalize hfn hfs hne
    rwa [← hbody]
  obtain ⟨hd,hA⟩ := threeTree_actual_dimension_admissible hz hTz
  let c : (Σ i : Fin 4,Fin (a i)) → Fin 4 := fun v => v.1
  have hc : Proper c (actualDirectionGraph (basePolytope z)) := by
    intro u v huv heq
    obtain ⟨huv',T,hu,hv,hd⟩ := (actualRootEdge_iff_nonzero_delta hzn.1 hzs u v).mp huv
    apply hd (hzg u v huv' ?_ T hu hv)
    exact fun h => h heq
  let b : Fin 4 → ℕ := fun i => (S.filter (fun v => c v=i)).card
  have htotal : total b=S.card := sum_color_counts S c
  have hb : Balanced b := by
    constructor
    · obtain ⟨C,hC⟩ := hTz.tetrahedra_nonempty
      have hcard : C.card=4 := (mem_filter.mp hC).2.1
      have hcl : (actualDirectionGraph (basePolytope z)).IsClique C := (mem_filter.mp hC).2.2
      have hCS : C⊆S := hTz.clique_subset_active (by omega) hcl
      intro i
      have hle := card_le_card (filter_subset_filter (p := fun v => c v=i) hCS)
      rw [color_count_tetrahedron hc hcard hcl i] at hle
      exact lt_of_lt_of_le Nat.zero_lt_one hle
    · intro i
      have hcap := capacity_nonnegative hTz hc hA i
      change (0 : ℤ)≤2*(S.card : ℤ)-3*(b i : ℤ)-3 at hcap
      rw [htotal]
      omega
  have hba : ∀ i,b i≤ a i := by
    intro i
    have hle := card_le_card (filter_subset_filter (p := fun v => c v=i) (subset_univ S))
    change b i≤ colorSize c i at hle
    simpa only [c,sigma_colorSize] using hle
  have hbound := balanced_dimension_bound (fun i => by have h := ha i;omega) hb hba
  rw [htotal] at hbound
  have hdQ : Module.finrank ℝ (vectorSpan ℝ Q)=S.card-1 := by
    rw [vectorSpan_basePolytope_normalize,← hbody] at hd
    exact hd
  rw [hdQ]
  exact hbound

/-- Optimal balanced subcounts produce a genuine integral polytope whose
actual direction graph is a 3-tree on exactly the constructed active vertices. -/
theorem four_partite_threeTree_dimension_attained (a : Fin 4 → ℕ)
    (ha : ∀ i,1≤ a i) :
    ∃ Q : Set ((Σ i : Fin 4,Fin (a i)) → ℝ),
      IsFinitePolytope Q ∧ LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (fourPartite a)) ∧
      (∃ S,ThreeTreeOn S (actualDirectionGraph Q)) ∧
      Module.finrank ℝ (vectorSpan ℝ Q)=
        min ((∑ i,a i)-1) (3*((∑ i,a i)-univ.sup a)-4) := by
  let o : LinearOrder (Σ i : Fin 4,Fin (a i)) := Separator.finiteVertexOrder _
  letI : LinearOrder (Σ i : Fin 4,Fin (a i)) :=
    { o with
      toDecidableEq := inferInstance
      compare := fun x y => @compareOfLessAndEq _ x y o.toLT (o.toDecidableLT x y) inferInstance
      compare_eq_compareOfLessAndEq := by intros;rfl }
  obtain ⟨b,hb,hba,hopt⟩ := optimal_balanced_subcounts a (fun i => by have h := ha i;omega)
  let c : (Σ i : Fin 4,Fin (a i)) → Fin 4 := fun v => v.1
  have hcap : ∀ i,b i≤ colorSize c i := by
    intro i
    simpa only [c,sigma_colorSize] using hba i
  obtain ⟨S,G,hT,hA,hc,hcounts⟩ := realize_schedule c (schedule_of_balanced hb) hcap
  have hsize : S.card=total b := by
    rw [← sum_color_counts S c]
    exact sum_congr rfl (fun i _ => hcounts i)
  obtain ⟨f,hf,hint,hd,hactual,hgraph⟩ := admissible_threeTree_active_witness hT hA
  have hgg : Graphical (fourPartite a) f := by
    intro u v huv hnon T hu hv
    exact hgraph u v huv (fun h => hnon (hc u v h)) T hu hv
  have hgp : IsGeneralizedPermutahedron (basePolytope f) := ⟨f,hf.1.1,hf.2.1,rfl⟩
  refine ⟨basePolytope f,hgp.finitePolytope,hint.basePolytope hf.1.1 hf.2.1,
    hf.minkowskiIndecomposable,(isWeakMinkowskiSummand_graphical_iff hf.1.1 hf.2.1).mpr hgg,
    ⟨S,?_⟩,?_⟩
  · rwa [hactual]
  · rw [hd,hsize]
    exact hopt

/-- The exact restricted maximum in Theorem 8.9, including all real weak
summands and without any ambient full-dimension hypothesis. -/
theorem maximum_threeTree_support_fourPartite (a : Fin 4 → ℕ)
    (ha : ∀ i,1≤ a i) :
    maximumThreeTreeSupportDimension (fourPartite a)=
      min ((∑ i,a i)-1) (3*((∑ i,a i)-univ.sup a)-4) := by
  let k := min ((∑ i,a i)-1) (3*((∑ i,a i)-univ.sup a)-4)
  let D : Set ℕ := {d | ∃ Q : Set ((Σ i : Fin 4,Fin (a i)) → ℝ),
    IsFinitePolytope Q ∧ MinkowskiIndecomposable Q ∧
    IsWeakMinkowskiSummand Q (graphicalZonotope (fourPartite a)) ∧
    (∃ S,ThreeTreeOn S (actualDirectionGraph Q)) ∧
    Module.finrank ℝ (vectorSpan ℝ Q)=d}
  have hbound : ∀ d∈D,d≤ k := by
    rintro d ⟨Q,hQ,hi,hw,⟨S,hT⟩,hd⟩
    rw [← hd]
    exact four_partite_threeTree_dimension_bound a ha hQ hi hw hT
  have hk : k∈D := by
    obtain ⟨Q,hQ,hl,hi,hw,hT,hd⟩ := four_partite_threeTree_dimension_attained a ha
    exact ⟨Q,hQ,hi,hw,hT,hd⟩
  change sSup D=k
  exact le_antisymm (csSup_le ⟨k,hk⟩ hbound) (le_csSup ⟨k,hbound⟩ hk)

/-- Both assertions of the printed Theorem 8.9, with every positive part
size and the actual-support definition of its restricted dimension invariant. -/
theorem four_partite_spanning_threeTrees : Targets.FourPartiteSpanningThreeTrees := by
  intro a ha
  exact ⟨four_partite_spanning_iff a ha,maximum_threeTree_support_fourPartite a ha⟩

end GraphicalZonotopes

end
end
end BundlePart352

section BundlePart353
/- Source: Papers/GraphicalZonotopes/TwoHubAttainment.lean -/








@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
open Finset SetFunctionEmbedding
open scoped BigOperators Pointwise
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- An integral graphical extreme function with its genuine affine
dimension. Unlike `LatticeExtremeAt`, this predicate specifies no dilation. -/
def IntegralGraphicalExtremeAt (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∃ f : SetFunction V,TranslationNormalized f ∧ IntegerValued f ∧
    ExtremeSupermodular f ∧ Graphical G f ∧
    Module.finrank ℝ (vectorSpan ℝ (basePolytope f))=d

theorem LatticeExtremeAt.integralGraphical {G : SimpleGraph V} {d M : ℕ}
    (h : LatticeExtremeAt G d M) : IntegralGraphicalExtremeAt G d := by
  obtain ⟨f,hn,hi,he,hG,hd,hb⟩:=h
  exact ⟨f,hn,hi,he,hG,hd⟩

theorem IntegralGraphicalExtremeAt.embed {G : SimpleGraph V} {H : SimpleGraph W} {d : ℕ}
    (h : IntegralGraphicalExtremeAt G d) (e : V↪W) (hGH : G≤ H.comap e) :
    IntegralGraphicalExtremeAt H d := by
  obtain ⟨f,hn,hi,he,hG,hd⟩:=h
  refine ⟨extend e f,extend_translationNormalized e hn,extend_integer e hi,
    extend_extreme e he,extend_graphical e (hG.mono_graph hGH),?_⟩
  rw [finrank_vectorSpan_extend e hn,hd]

theorem IntegralGraphicalExtremeAt.polytope {G : SimpleGraph V} {d : ℕ}
    (h : IntegralGraphicalExtremeAt G d) :
    ∃ Q : Set (V→ℝ),IsFinitePolytope Q ∧ LatticePolytope Q ∧
      MinkowskiIndecomposable Q ∧ IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
      Module.finrank ℝ (vectorSpan ℝ Q)=d := by
  obtain ⟨f,hn,hi,he,hG,hd⟩:=h
  have hgp : IsGeneralizedPermutahedron (basePolytope f):=⟨f,hn.1,he.2.1,rfl⟩
  exact ⟨basePolytope f,hgp.finitePolytope,hi.basePolytope hn.1 he.2.1,
    he.minkowskiIndecomposable,(isWeakMinkowskiSummand_graphical_iff hn.1 he.2.1).mpr hG,hd⟩

theorem IntegralGraphicalExtremeAt.dimension_le {G : SimpleGraph V} {d : ℕ}
    (h : IntegralGraphicalExtremeAt G d) : d≤ maximumIndecomposableDimension G := by
  obtain ⟨Q,hf,hl,hi,hw,hd⟩:=h.polytope
  rw [←hd]
  exact dimension_le_maximum hf hi hw

/-- Extracting the integral normalized support function preserves dimension
and exposes every hypothesis needed to transfer a lattice witness. -/
theorem integralGraphicalExtremeAt_of_polytope {G : SimpleGraph V} {d : ℕ}
    (hdpos : 0< d) {Q : Set (V→ℝ)} (hQ : IsFinitePolytope Q) (hl : LatticePolytope Q)
    (hi : MinkowskiIndecomposable Q) (hw : IsWeakMinkowskiSummand Q (graphicalZonotope G))
    (hd : Module.finrank ℝ (vectorSpan ℝ Q)=d) : IntegralGraphicalExtremeAt G d := by
  obtain ⟨M,hM,R,hR,hRc,hnR,hQR⟩:=hw
  obtain ⟨hfn,hfs,hbody,hgraph,hbound⟩:=actual_summand_lowerSupport
    hQ.compact hQ.convex hi.1 hR hRc hnR hM.le hQR
  let f:=lowerSupport Q
  let z:=normalize f
  have hn : TranslationNormalized z:=normalize_translationNormalized hfn
  have hint : IntegerValued z:=(hl.lowerSupport_integerValued hi.1).normalize
  have hzg : Graphical G z:=by
    intro u v huv hnon S hu hv
    rw [delta_normalize f huv hu hv]
    exact hgraph u v huv hnon S hu hv
  have hzd : Module.finrank ℝ (vectorSpan ℝ (basePolytope z))=d := by
    rw [vectorSpan_basePolytope_normalize,←hbody]
    exact hd
  have hz : z≠0:=by
    intro he
    rw [he,basePolytope_zero,vectorSpan_singleton,finrank_bot] at hzd
    omega
  have he:=MinkowskiIndecomposable.extremeSupermodular_normalize hfn hfs hz (hbody ▸ hi)
  exact ⟨z,hn,hint,he,hzg,hzd⟩

namespace TwoHub

theorem twoSingleton_card (p b : ℕ) :
    Fintype.card (Σ i : Fin 4,Fin (![1,1,p,b] i))=p+b+2 := by
  simp [Fintype.card_sigma,Fin.sum_univ_succ]
  omega

theorem part_sum (p b : ℕ) : (∑ i : Fin 4,(![1,1,p,b] i))=p+b+2 := by
  simp [Fin.sum_univ_succ]
  omega

theorem part_sup (p b : ℕ) (hp : 1≤ p) (hpb : p≤ b) :
    univ.sup (![1,1,p,b])=b := by
  apply le_antisymm
  · apply Finset.sup_le
    intro i hi
    fin_cases i <;> simp <;> omega
  · have h:=le_sup (f:=(![1,1,p,b])) (mem_univ (3 : Fin 4))
    simpa using h

/-- The complete low range is supplied by the already verified four-partite
3-tree spectrum. No finite-parameter enumeration is used. -/
theorem low_range_attainment (p b : ℕ) (hp : 1≤ p) (hpb : p≤ b) (hb : b≤2*p+1) :
    IntegralGraphicalExtremeAt (twoSingletonGraph p b) (p+b+1) := by
  obtain ⟨Q,hQ,hl,hi,hw,hT,hd⟩:=four_partite_threeTree_dimension_attained (![1,1,p,b])
    (by intro i;fin_cases i <;> simp <;> omega)
  rw [part_sum,part_sup p b hp hpb] at hd
  have he : min (p+b+2-1) (3*(p+b+2-b)-4)=p+b+1:=by omega
  rw [he] at hd
  exact integralGraphicalExtremeAt_of_polytope (by omega) hQ hl hi hw hd

/-- A proper partition with k cells yields an integral witness on exactly
k+p vertices in the last independent part. -/
theorem partition_attainment {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (P : PartitionData I) :
    IntegralGraphicalExtremeAt
      (twoSingletonGraph (Fintype.card I) (P.cells.card+Fintype.card I))
      (Fintype.card I+P.cells.card+Fintype.card I+1) := by
  have h : IntegralGraphicalExtremeAt (graph (I:=I) (J:=P.Index))
      (Fintype.card I+P.cells.card+Fintype.card I+1) := by
    refine ⟨P.construction,P.construction_normalized,P.construction_integer,
      P.construction_extreme,P.construction_graphical,?_⟩
    have hd:=P.construction_fullDimension
    change Module.finrank ℝ (vectorSpan ℝ (basePolytope P.construction))=
      Fintype.card (Hub I⊕P.Index)-1 at hd
    rw [hd]
    simp only [Hub,PartitionData.Index,Fintype.card_sum,Fintype.card_bool,Fintype.card_coe]
    omega
  let e:=graphIso (I:=I) (J:=P.Index)
  have hmap : graph (I:=I) (J:=P.Index)≤
      (twoSingletonGraph (Fintype.card I) (Fintype.card P.Index)).comap e := by
    intro x y hxy
    exact e.map_adj_iff.mpr hxy
  have he:=h.embed e.toEquiv.toEmbedding hmap
  have hcard : Fintype.card P.Index=P.cells.card+Fintype.card I := by
    simp [PartitionData.Index]
  exact Eq.mp (congrArg (fun b : ℕ => IntegralGraphicalExtremeAt
    (twoSingletonGraph (Fintype.card I) b)
    (Fintype.card I+P.cells.card+Fintype.card I+1)) hcard) he

theorem intermediate_attainment (p b : ℕ) (hp : 1≤ p)
    (hlo : 2*p+1≤ b) (hhi : b≤2^p+p) :
    IntegralGraphicalExtremeAt (twoSingletonGraph p b) (p+b+1) := by
  letI : Nonempty (Fin p):=⟨⟨0,hp⟩⟩
  obtain ⟨F,hF,hcard,huses,hproper⟩:=CubePartition.exists_proper_card (I:=Fin p) (b-p)
    (by simp only [Fintype.card_fin];omega) (by simp only [Fintype.card_fin];omega)
  let P : PartitionData (Fin p):=⟨F,hF,hproper,huses⟩
  have he:=partition_attainment P
  have hbc : F.card+p=b:=by omega
  have hd : p+F.card+p+1=p+b+1:=by omega
  have hdim : Fintype.card (Fin p)+P.cells.card+Fintype.card (Fin p)+1=p+b+1 := by
    simpa only [Fintype.card_fin,P] using hd
  have hpars : (Fintype.card (Fin p),P.cells.card+Fintype.card (Fin p))=(p,b) := by
    simp only [Fintype.card_fin,P,hbc]
  rw [hdim] at he
  exact Eq.mp (congrArg (fun x : ℕ×ℕ => IntegralGraphicalExtremeAt
    (twoSingletonGraph x.1 x.2) (p+b+1)) hpars) he

/-- Enlarging the last part preserves the saturated integral witness by
adding zero coordinates to its support function. -/
theorem saturated_attainment (p b : ℕ) (hp : 1≤ p) (hb : 2^p+p≤ b) :
    IntegralGraphicalExtremeAt (twoSingletonGraph p b) (2^p+2*p+1) := by
  have h:=(exponential_lattice_summand p hp).integralGraphical
  let e₀:=vertexEmbedding (Function.Embedding.refl (Fin p)) (Fin.castLEEmb hb)
  let e₁:=(finGraphIso p (2^p+p)).symm.toEquiv.toEmbedding
  let e₂:=(finGraphIso p b).toEquiv.toEmbedding
  let e:=e₁.trans (e₀.trans e₂)
  have hmap : twoSingletonGraph p (2^p+p)≤(twoSingletonGraph p b).comap e := by
    intro x y hxy
    have h₁ : (graph (I:=Fin p) (J:=Fin (2^p+p))).Adj (e₁ x) (e₁ y) :=
      (finGraphIso p (2^p+p)).symm.map_adj_iff.mpr hxy
    have h₀:=graph_le_comap (Function.Embedding.refl (Fin p)) (Fin.castLEEmb hb) h₁
    exact (finGraphIso p b).map_adj_iff.mpr h₀
  exact h.embed e hmap

theorem ordered_attainment (p b : ℕ) (hp : 1≤ p) (hpb : p≤ b) :
    IntegralGraphicalExtremeAt (twoSingletonGraph p b) (min (p+b+1) (2^p+2*p+1)) := by
  by_cases hb : b≤2*p+1
  · have he : p+b+1≤2^p+2*p+1 := by
      have hpow : p+1≤2^p:=Nat.lt_two_pow_self (n:=p)
      omega
    rw [min_eq_left he]
    exact low_range_attainment p b hp hpb hb
  · by_cases hs : b≤2^p+p
    · rw [min_eq_left (by omega)]
      exact intermediate_attainment p b hp (by omega) hs
    · rw [min_eq_right (by omega)]
      exact saturated_attainment p b hp (by omega)

theorem all_attainment (p b : ℕ) (hp : 1≤ p) (hb : 1≤ b) :
    IntegralGraphicalExtremeAt (twoSingletonGraph p b)
      (min (p+b+1) (2^(min p b)+2*min p b+1)) := by
  by_cases hpb : p≤ b
  · simpa only [min_eq_left hpb] using ordered_attainment p b hp hpb
  · have hbp : b≤ p:=by omega
    have h:=ordered_attainment b p hb hbp
    let e:=twoSingletonSwap b p
    have hmap : twoSingletonGraph b p≤(twoSingletonGraph p b).comap e:=by
      intro x y hxy
      exact e.map_adj_iff.mpr hxy
    have he:=h.embed e.toEquiv.toEmbedding hmap
    simpa only [min_eq_right hbp,Nat.add_comm b p] using he

end TwoHub
end GraphicalZonotopes

end
end
end BundlePart353

section BundlePart354
/- Source: Papers/GraphicalZonotopes/TwoHubCapacity.lean -/







/-! # The separator upper bound for the two-singleton family

The boundary is the two distinguished vertices together with the first
independent part.  We count its rows exactly and exhibit all the boundary
cliques needed for the sharp capacity estimate.  No assumption is made that
the private coefficients of an extreme summand are nonzero.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
noncomputable section
namespace GraphicalZonotopes.TwoHub.Capacity
open Finset
open scoped BigOperators Classical

abbrev Vertex (p b : ℕ) := (Bool ⊕ Fin p) ⊕ Fin b

local instance vertexOrder (p b : ℕ) : LinearOrder (Vertex p b) :=
  inferInstanceAs (LinearOrder ((Bool ⊕ₗ Fin p) ⊕ₗ Fin b))

local instance vertexLT (p b : ℕ) : LT (Vertex p b) :=
  (vertexOrder p b).toLT

local instance vertexDecidableEq (p b : ℕ) : DecidableEq (Vertex p b) :=
  (vertexOrder p b).toDecidableEq

abbrev G (p b : ℕ) := TwoHub.graph (I := Fin p) (J := Fin b)
def anchor (p b : ℕ) (t : Bool) : Vertex p b := .inl (.inl t)
def a (p b : ℕ) : Vertex p b := anchor p b false
def z (p b : ℕ) : Vertex p b := anchor p b true
def u (p b : ℕ) (i : Fin p) : Vertex p b := .inl (.inr i)
def boundary (p b : ℕ) : Finset (Vertex p b) :=
  univ.image (Sum.inl : Bool ⊕ Fin p → Vertex p b)
def privatePart (p b : ℕ) (j : Fin b) : Finset (Vertex p b) := {Sum.inr j}

@[simp] theorem boundary_card (p b : ℕ) : (boundary p b).card = p+2 := by
  rw [boundary,card_image_of_injective _ Sum.inl_injective]
  simp [Nat.add_comm]

@[simp] theorem mem_boundary_inl (p b : ℕ) (x : Bool ⊕ Fin p) :
    Sum.inl x ∈ boundary p b := by simp [boundary]

@[simp] theorem not_mem_boundary_inr (p b : ℕ) (j : Fin b) :
    Sum.inr j ∉ boundary p b := by simp [boundary]

theorem boundary_order (p b : ℕ) (x y : Bool ⊕ Fin p) :
    (Sum.inl x : Vertex p b) < Sum.inl y ↔
      (toLex x : Bool ⊕ₗ Fin p) < toLex y := Sum.lex_inl_inl

theorem partition (p b : ℕ) :
    Separator.Partition (G p b) (boundary p b) (privatePart p b) where
  boundary_disjoint j := by
    apply disjoint_left.mpr
    intro x hx hp
    have he : x=Sum.inr j := mem_singleton.mp hp
    subst x
    exact not_mem_boundary_inr p b j hx
  private_disjoint := by
    intro i j hij
    exact disjoint_singleton.mpr (fun he => hij (Sum.inr_injective he))
  cover x := by
    cases x with
    | inl x => exact Or.inl (mem_boundary_inl p b x)
    | inr j => exact Or.inr ⟨j,mem_singleton_self _⟩
  no_cross_edge := by
    intro i j x y hx hy hxy
    have hx' : x=Sum.inr i := mem_singleton.mp hx
    have hy' : y=Sum.inr j := mem_singleton.mp hy
    subst x
    subst y
    exact False.elim (hxy rfl)

abbrev EdgeCode (p : ℕ) := Unit ⊕ (Bool × Fin p)

def edgePair (p b : ℕ) : EdgeCode p → Vertex p b × Vertex p b
  | .inl _ => (a p b,z p b)
  | .inr (t,i) => (anchor p b t,u p b i)

theorem edgePair_valid (p b : ℕ) (c : EdgeCode p) :
    (edgePair p b c).1 < (edgePair p b c).2 ∧
      (G p b).Adj (edgePair p b c).1 (edgePair p b c).2 ∧
      (edgePair p b c).1 ∈ boundary p b ∧
      (edgePair p b c).2 ∈ boundary p b := by
  rcases c with c | ⟨t,i⟩
  · simp [edgePair,a,z,anchor,boundary_order,Sum.Lex.toLex_lt_toLex,
      G,TwoHub.graph,TwoHub.color]
  · cases t <;> simp [edgePair,anchor,u,boundary_order,
      Sum.Lex.toLex_lt_toLex,G,TwoHub.graph,TwoHub.color]

def boundaryEdgeOfCode (p b : ℕ) (c : EdgeCode p) :
    Separator.BoundaryEdge (G p b) (boundary p b) :=
  ⟨⟨edgePair p b c,(edgePair_valid p b c).1,(edgePair_valid p b c).2.1⟩,
    (edgePair_valid p b c).2.2⟩

theorem edgePair_injective (p b : ℕ) : Function.Injective (edgePair p b) := by
  intro c d h
  rcases c with c | ⟨t,i⟩ <;> rcases d with d | ⟨s,j⟩
  · exact congrArg Sum.inl (Subsingleton.elim _ _)
  · simp [edgePair,a,z,anchor,u] at h
  · simp [edgePair,a,z,anchor,u] at h
  · simpa [edgePair,anchor,u] using h

theorem boundaryEdgeOfCode_bijective (p b : ℕ) :
    Function.Bijective (boundaryEdgeOfCode p b) := by
  constructor
  · intro c d h
    apply edgePair_injective p b
    exact congrArg (fun e : Separator.BoundaryEdge (G p b) (boundary p b) => e.1.1) h
  · rintro ⟨⟨⟨x,y⟩,hlt,hadj⟩,hx,hy⟩
    obtain ⟨x,_,rfl⟩ := mem_image.mp hx
    obtain ⟨y,_,rfl⟩ := mem_image.mp hy
    rw [boundary_order] at hlt
    rcases x with t | i <;> rcases y with s | j
    · cases t <;> cases s
      all_goals try simp [Sum.Lex.toLex_lt_toLex,Bool.lt_iff] at hlt
      refine ⟨.inl (),?_⟩
      rfl
    · refine ⟨.inr (t,j),?_⟩
      rfl
    · simp [Sum.Lex.toLex_lt_toLex] at hlt
    · exact False.elim (hadj rfl)

def boundaryEdgeEquiv (p b : ℕ) :
    EdgeCode p ≃ Separator.BoundaryEdge (G p b) (boundary p b) :=
  Equiv.ofBijective (boundaryEdgeOfCode p b) (boundaryEdgeOfCode_bijective p b)

theorem common_boundary_az (p b : ℕ) :
    commonNeighbors (G p b) (a p b) (z p b) ∩ boundary p b =
      univ.image (u p b) := by
  ext x
  rcases x with (t | i) | j
  · cases t <;> simp [mem_commonNeighbors,G,TwoHub.graph,TwoHub.color,a,z,anchor,u]
  · simp [mem_commonNeighbors,G,TwoHub.graph,TwoHub.color,a,z,anchor,u]
  · simp [u]

theorem common_boundary_anchor (p b : ℕ) (t : Bool) (i : Fin p) :
    commonNeighbors (G p b) (anchor p b t) (u p b i) ∩ boundary p b =
      {anchor p b (!t)} := by
  ext x
  rcases x with (s | j) | j
  · cases t <;> cases s <;>
      simp [mem_commonNeighbors,G,TwoHub.graph,TwoHub.color,anchor,u]
  · cases t <;> simp [mem_commonNeighbors,G,TwoHub.graph,TwoHub.color,anchor,u]
  · simp [anchor]

theorem u_injective (p b : ℕ) : Function.Injective (u p b) := by
  intro i j h
  exact Sum.inr_injective (Sum.inl_injective h)

/-- The boundary has exactly `2^p + 4*p` elementary rows. -/
theorem boundary_rows_count (p b : ℕ) :
    (∑ e : Separator.BoundaryEdge (G p b) (boundary p b),
      2^(commonNeighbors (G p b) e.1.1.1 e.1.1.2 ∩ boundary p b).card) =
        2^p+4*p := by
  have he := Fintype.sum_equiv (boundaryEdgeEquiv p b)
    (fun c : EdgeCode p =>
      (2 : ℕ)^(commonNeighbors (G p b) (edgePair p b c).1
        (edgePair p b c).2 ∩ boundary p b).card)
    (fun e : Separator.BoundaryEdge (G p b) (boundary p b) =>
      (2 : ℕ)^(commonNeighbors (G p b) e.1.1.1 e.1.1.2 ∩ boundary p b).card)
    (fun _ => rfl)
  rw [←he]
  simp [EdgeCode,Fintype.sum_sum_type,edgePair,common_boundary_az,
    common_boundary_anchor,card_image_of_injective _ (u_injective p b),
    Fintype.sum_prod_type,Fintype.sum_bool,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] <;> omega

abbrev CliqueCode (p : ℕ) := Unit ⊕ (Fin 3 × Fin p)

def cliqueSet (p b : ℕ) : CliqueCode p → Finset (Vertex p b)
  | .inl _ => {a p b,z p b}
  | .inr (t,i) => if t=0 then {a p b,u p b i}
      else if t=1 then {z p b,u p b i} else {a p b,z p b,u p b i}

theorem u_mem_cliqueSet (p b : ℕ) (t : Fin 3) (i : Fin p) :
    u p b i ∈ cliqueSet p b (.inr (t,i)) := by
  fin_cases t <;> simp [cliqueSet]

theorem u_mem_cliqueSet_iff (p b : ℕ) (t : Fin 3) (i j : Fin p) :
    u p b i ∈ cliqueSet p b (.inr (t,j)) ↔ i=j := by
  fin_cases t <;> simp [cliqueSet,a,z,anchor,u]

theorem cliqueSet_injective (p b : ℕ) : Function.Injective (cliqueSet p b) := by
  intro c d h
  rcases c with c | ⟨t,i⟩ <;> rcases d with d | ⟨s,j⟩
  · exact congrArg Sum.inl (Subsingleton.elim _ _)
  · have hj := u_mem_cliqueSet p b s j
    rw [←h] at hj
    simp [cliqueSet,a,z,anchor,u] at hj
  · have hi := u_mem_cliqueSet p b t i
    rw [h] at hi
    simp [cliqueSet,a,z,anchor,u] at hi
  · have hi := u_mem_cliqueSet p b t i
    rw [h,u_mem_cliqueSet_iff] at hi
    subst j
    have ha := congrArg (fun C : Finset (Vertex p b) => a p b ∈ C) h
    have hz := congrArg (fun C : Finset (Vertex p b) => z p b ∈ C) h
    fin_cases t <;> fin_cases s <;> try rfl
    all_goals simp [cliqueSet,a,z,anchor,u] at ha hz

theorem cliqueSet_mem (p b : ℕ) (c : CliqueCode p) :
    cliqueSet p b c ∈ Separator.boundaryCliques (G p b) (boundary p b) := by
  rcases c with c | ⟨t,i⟩
  · simp [Separator.boundaryCliques,cliqueSet,IsCliqueCoordinate,
      SimpleGraph.IsClique,Set.Pairwise,Finset.subset_iff,a,z,anchor,
      G,TwoHub.graph,TwoHub.color]
  · fin_cases t <;>
      simp [Separator.boundaryCliques,cliqueSet,IsCliqueCoordinate,
        SimpleGraph.IsClique,Set.Pairwise,Finset.subset_iff,a,z,anchor,u,
        G,TwoHub.graph,TwoHub.color]

theorem boundary_cliques_lower (p b : ℕ) :
    1+3*p ≤ (Separator.boundaryCliques (G p b) (boundary p b)).card := by
  have h := Fintype.card_le_of_injective
    (fun c : CliqueCode p =>
      (⟨cliqueSet p b c,cliqueSet_mem p b c⟩ :
        ↥(Separator.boundaryCliques (G p b) (boundary p b))))
    (fun c d h => cliqueSet_injective p b (congrArg Subtype.val h))
  simpa only [CliqueCode,Fintype.card_sum,Fintype.card_unit,Fintype.card_prod,
    Fintype.card_fin,Fintype.card_coe] using h

/-- The exact upper capacity bound, without nonzero-branch hypotheses. -/
theorem active_capacity (p b : ℕ) (f : graphicalFunctionSpace (G p b))
    (hf : ExtremeSupermodular f.1) :
    Fintype.card (Gluing.ActiveBranch
      (((Separator.functionEquiv (partition p b)).symm f).2)) ≤ 2^p+p := by
  have h := Separator.separator_capacity_for_function (partition p b) f hf
  rw [boundary_rows_count] at h
  have hc := boundary_cliques_lower p b
  have hp : 0 < (2 : ℕ)^p := pow_pos (by decide) _
  omega

theorem extreme_dimension_bound (p b : ℕ) (f : graphicalFunctionSpace (G p b))
    (hf : ExtremeSupermodular f.1) :
    Module.finrank ℝ (vectorSpan ℝ (basePolytope f.1)) ≤ 2^p+2*p+1 := by
  have h := Separator.finrank_le_boundary_add_active (partition p b)
    (fun j => by simp [privatePart]) f hf.2.1
  rw [boundary_card] at h
  have hc := active_capacity p b f hf
  omega

theorem actual_summand_dimension_bound (p b : ℕ)
    {Q : Set (Vertex p b → ℝ)} (hQ : IsFinitePolytope Q)
    (hi : MinkowskiIndecomposable Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope (G p b))) :
    Module.finrank ℝ (vectorSpan ℝ Q) ≤ min (p+b+1) (2^p+2*p+1) := by
  apply le_min
  · have h := weak_summand_dimension_le hQ hi hw
    simp only [Fintype.card_sum,Fintype.card_bool,Fintype.card_fin] at h
    omega
  · obtain ⟨f,hf,hzero|hext,hd⟩ := weak_summand_extreme_or_zero hQ hi hw
    · rw [hd,hzero,basePolytope_zero,vectorSpan_singleton,finrank_bot]
      exact Nat.zero_le _
    · rw [hd]
      exact extreme_dimension_bound p b f hext

theorem maximum_dimension_upper (p b : ℕ) :
    maximumIndecomposableDimension (G p b) ≤ min (p+b+1) (2^p+2*p+1) := by
  apply csSup_le'
  rintro d ⟨Q,hQ,hi,hw,hd⟩
  rw [←hd]
  exact actual_summand_dimension_bound p b hQ hi hw

end GraphicalZonotopes.TwoHub.Capacity

end
end
end BundlePart354

section BundlePart355
/- Source: Papers/GraphicalZonotopes/TwoHubPrincipal.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.TwoHub
open Finset
open scoped BigOperators Pointwise

theorem maximum_dimension_upper (p b : ℕ) :
    maximumIndecomposableDimension (twoSingletonGraph p b)≤
      min (p+b+1) (2^p+2*p+1) := by
  rw [←maximum_dimension_model_eq]
  exact Capacity.maximum_dimension_upper p b

theorem maximum_dimension_upper_symmetric (p b : ℕ) :
    maximumIndecomposableDimension (twoSingletonGraph p b)≤
      min (p+b+1) (2^(min p b)+2*min p b+1) := by
  by_cases hpb : p≤ b
  · simpa only [min_eq_left hpb] using maximum_dimension_upper p b
  · have hbp : b≤ p:=by omega
    rw [maximum_dimension_swap]
    simpa only [min_eq_right hbp,Nat.add_comm b p] using maximum_dimension_upper b p

/-- The exact dimension formula of Theorem8.7, for all positive part
sizes, with no restriction to the explicit support pattern. -/
theorem maximum_dimension (p b : ℕ) (hp : 1≤ p) (hb : 1≤ b) :
    maximumIndecomposableDimension (twoSingletonGraph p b)=
      min (p+b+1) (2^(min p b)+2*min p b+1) :=
  le_antisymm (maximum_dimension_upper_symmetric p b) (all_attainment p b hp hb).dimension_le

theorem full_dimension_arithmetic (p b : ℕ) :
    p+b+1≤2^(min p b)+2*min p b+1 ↔ max p b≤2^(min p b)+min p b := by
  by_cases h : p≤ b
  · simp only [min_eq_left h,max_eq_right h]
    omega
  · have hh : b≤ p:=by omega
    simp only [min_eq_right hh,max_eq_left hh]
    omega

theorem supports_full_iff (p b : ℕ) (hp : 1≤ p) (hb : 1≤ b) :
    SupportsFullIndecomposable (twoSingletonGraph p b) ↔
      max p b≤2^(min p b)+min p b := by
  constructor
  · rintro ⟨Q,hQ,hi,hd,hw⟩
    have hm:=(dimension_le_maximum hQ hi hw).trans (maximum_dimension_upper_symmetric p b)
    rw [hd,twoSingleton_card] at hm
    have hn : p+b+1≤2^(min p b)+2*min p b+1:=by omega
    exact (full_dimension_arithmetic p b).mp hn
  · intro h
    obtain ⟨Q,hQ,hl,hi,hw,hd⟩:=(all_attainment p b hp hb).polytope
    refine ⟨Q,hQ,hi,?_,hw⟩
    change Module.finrank ℝ (vectorSpan ℝ Q)=_
    rw [hd,min_eq_left ((full_dimension_arithmetic p b).mpr h),twoSingleton_card]
    omega

/-- The dimension formula, exact full-dimensionality criterion, and lattice
attainment in the original coordinate model of the paper. -/
theorem two_singleton_classification : Targets.TwoSingletonClassification := by
  intro p b hp hb
  refine ⟨maximum_dimension p b hp hb,supports_full_iff p b hp hb,?_⟩
  obtain ⟨Q,hQ,hl,hi,hw,hd⟩:=(all_attainment p b hp hb).polytope
  exact ⟨Q,hl,hi,hw,hd⟩

theorem twoSingleton_cliqueFree (p b : ℕ) : (twoSingletonGraph p b).CliqueFree 5 := by
  intro S hS
  have hinj : Function.Injective (fun v : S => v.1.1) := by
    intro x y he
    by_contra hne
    have hxy:=hS.1 x.2 y.2 (fun h => hne (Subtype.ext h))
    exact hxy he
  have hc:=Fintype.card_le_of_injective (fun v : S => v.1.1) hinj
  simp only [Fintype.card_coe,Fintype.card_fin] at hc
  rw [hS.2] at hc
  omega

/-- The whole printed Theorem8.4: an actual lattice summand at the explicit
integral dilation, and stabilization at every larger fourth part. -/
theorem exponential_family (p : ℕ) (hp : 1≤ p) :
    (twoSingletonGraph p (2^p+p)).CliqueFree 5 ∧
    (∃ Q : Set ((Σ i : Fin 4,Fin (![1,1,p,2^p+p] i))→ℝ),
      LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
      Module.finrank ℝ (vectorSpan ℝ Q)=2^p+2*p+1 ∧
      IsMinkowskiSummand Q ((((p-1)*2^p+2 : ℕ) : ℝ) •
        graphicalZonotope (twoSingletonGraph p (2^p+p)))) ∧
    ∀ b : ℕ,2^p+p≤ b →
      maximumIndecomposableDimension (twoSingletonGraph p b)=2^p+2*p+1 := by
  refine ⟨twoSingleton_cliqueFree _ _,(exponential_lattice_summand p hp).polytope,?_⟩
  intro b hb
  have hpb : p≤ b:=(Nat.le_add_left p (2^p)).trans hb
  rw [maximum_dimension p b hp (by omega),min_eq_left hpb,min_eq_right (by omega)]

end GraphicalZonotopes.TwoHub

end
end
end BundlePart355

section BundlePart356
/- Source: Papers/GraphicalZonotopes/TwoHubLiteral.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes.TwoHub
open scoped Pointwise

/-- The supremum in Theorem8.7 uses precisely the paper's convention that
indecomposability tests finite polytopal Minkowski decompositions. -/
theorem classification_polytopal (p b : ℕ) (hp : 1≤ p) (hb : 1≤ b) :
    (sSup {d : ℕ | ∃ Q : Set ((Σ i : Fin 4,Fin (![1,1,p,b] i))→ℝ),
      IsFinitePolytope Q ∧ PolytopalMinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (twoSingletonGraph p b)) ∧
      Module.finrank ℝ (vectorSpan ℝ Q)=d})=
      min (p+b+1) (2^(min p b)+2*min p b+1) := by
  rw [←maximumIndecomposableDimension_eq_polytopal_supremum]
  exact maximum_dimension p b hp hb

theorem full_polytopal_iff (p b : ℕ) (hp : 1≤ p) (hb : 1≤ b) :
    (∃ Q : Set ((Σ i : Fin 4,Fin (![1,1,p,b] i))→ℝ),
      IsFinitePolytope Q ∧ PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (twoSingletonGraph p b))) ↔
      max p b≤2^(min p b)+min p b := by
  rw [←supportsFullIndecomposable_iff_polytopal_weak]
  exact supports_full_iff p b hp hb

theorem lattice_polytopal_attainment (p b : ℕ) (hp : 1≤ p) (hb : 1≤ b) :
    ∃ Q : Set ((Σ i : Fin 4,Fin (![1,1,p,b] i))→ℝ),
      LatticePolytope Q ∧ PolytopalMinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (twoSingletonGraph p b)) ∧
      Module.finrank ℝ (vectorSpan ℝ Q)=min (p+b+1) (2^(min p b)+2*min p b+1) := by
  obtain ⟨Q,hQ,hl,hi,hw,hd⟩:=(all_attainment p b hp hb).polytope
  exact ⟨Q,hl,(weakSummand_indecomposable_iff_polytopal hQ hw).mp hi,hw,hd⟩

/-- The lattice witness in Theorem8.4 has an actual finite polytopal
complement at exactly the stated dilation. -/
theorem exponential_polytopal_summand (p : ℕ) (hp : 1≤ p) :
    ∃ Q : Set ((Σ i : Fin 4,Fin (![1,1,p,2^p+p] i))→ℝ),
      LatticePolytope Q ∧ PolytopalMinkowskiIndecomposable Q ∧
      Module.finrank ℝ (vectorSpan ℝ Q)=2^p+2*p+1 ∧
      ∃ R : Set ((Σ i : Fin 4,Fin (![1,1,p,2^p+p] i))→ℝ),
        IsFinitePolytope R ∧ R.Nonempty ∧
        Q+R=((((p-1)*2^p+2 : ℕ) : ℝ) •
          graphicalZonotope (twoSingletonGraph p (2^p+p))) := by
  obtain ⟨Q,hl,hi,hd,hs⟩:=(exponential_lattice_summand p hp).polytope
  have hM : (0 : ℝ)<(((p-1)*2^p+2 : ℕ) : ℝ):=by positivity
  have hw : IsWeakMinkowskiSummand Q (graphicalZonotope (twoSingletonGraph p (2^p+p))):=
    ⟨_,hM,hs⟩
  refine ⟨Q,hl,(weakSummand_indecomposable_iff_polytopal hl.finitePolytope hw).mp hi,hd,?_⟩
  exact (isMinkowskiSummand_graphical_iff_finite_complement hl.finitePolytope hM.le).mp hs

end GraphicalZonotopes.TwoHub

end
end
end BundlePart356

section BundlePart357
/- Source: Papers/GraphicalZonotopes/TwoHubConsequences.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.TwoHub
open Finset
open scoped BigOperators Pointwise

theorem two_pow_gt_add_one (p : ℕ) (hp : 2 ≤ p) : p+1 < 2^p := by
  induction p,hp using Nat.le_induction with
  | base => decide
  | succ p hp ih =>
    rw [pow_succ]
    omega

/-- The exponential family has no spanning admissible 3-tree. The proof
uses the previously verified exact four-part spanning criterion, with every
part and every vertex retained. -/
theorem exponential_no_admissible_spanning (p : ℕ) (hp : 2 ≤ p) :
    ¬HasAdmissibleSpanningThreeTree (twoSingletonGraph p (2^p+p)) := by
  have hp1 : 1 ≤ p := by omega
  have hpb : p ≤ 2^p+p := Nat.le_add_left p (2^p)
  intro h
  have hbound := (FourPartSpanning.four_partite_spanning_iff (![1,1,p,2^p+p])
    (by intro i; fin_cases i <;> simp <;> omega)).mp h
  rw [part_sum,part_sup p (2^p+p) hp1 hpb] at hbound
  have hpow := two_pow_gt_add_one p hp
  omega

/-- Corollary 8.5, with a lattice witness and the paper's ordinary
polytopal notion of indecomposability. -/
theorem paper_corollary_8_5 (p : ℕ) (hp : 2 ≤ p) :
    (∃ Q : Set ((Σ i : Fin 4,Fin (![1,1,p,2^p+p] i)) → ℝ),
      LatticePolytope Q ∧ PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (twoSingletonGraph p (2^p+p)))) ∧
    ¬HasAdmissibleSpanningThreeTree (twoSingletonGraph p (2^p+p)) := by
  have hp1 : 1 ≤ p := by omega
  obtain ⟨Q,hQ,hi,hd,R,hR,hnR,he⟩ := exponential_polytopal_summand p hp1
  refine ⟨⟨Q,hQ,hi,?_,?_⟩,exponential_no_admissible_spanning p hp⟩
  · unfold FullDimension
    rw [hd,twoSingleton_card]
    have hpow : 0 < (2 : ℕ)^p := by positivity
    omega
  · exact ⟨_,by positivity,R,hR.compact,hR.convex,hnR,he⟩

end GraphicalZonotopes.TwoHub

end
end
end BundlePart357

section BundlePart358
/- Source: Papers/GraphicalZonotopes/Reflection.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The lower-support data of reflection through the origin. -/
def reflectedFunction (z : SetFunction V) (S : Finset V) : ℝ := z Sᶜ-z univ

theorem subsetSum_add_compl (x : V → ℝ) (S : Finset V) :
    subsetSum x S+subsetSum x Sᶜ=subsetSum x univ := by
  exact Finset.sum_add_sum_compl S x

@[simp] theorem subsetSum_neg (x : V → ℝ) (S : Finset V) :
    subsetSum (-x) S= -subsetSum x S := by
  simp [subsetSum]

theorem reflectedFunction_normalized (z : SetFunction V) : Normalized (reflectedFunction z) := by
  simp [Normalized,reflectedFunction]

theorem mem_basePolytope_reflected_iff {z : SetFunction V} (hz : Normalized z) (x : V → ℝ) :
    x∈basePolytope (reflectedFunction z) ↔ -x∈basePolytope z := by
  constructor
  · intro hx
    have htotal : subsetSum x univ= -z univ := by
      have h := hx.1
      simpa [reflectedFunction, show z ∅ = 0 from hz] using h
    refine ⟨by rw [subsetSum_neg,htotal,neg_neg],?_⟩
    intro S
    have h := hx.2 Sᶜ
    change z (Sᶜ)ᶜ-z univ≤ subsetSum x Sᶜ at h
    rw [compl_compl] at h
    have hc := subsetSum_add_compl x S
    rw [htotal] at hc
    rw [subsetSum_neg]
    linarith
  · intro hx
    have htotal : subsetSum x univ= -z univ := by
      have h := hx.1
      rw [subsetSum_neg] at h
      linarith
    refine ⟨?_,?_⟩
    · simpa [reflectedFunction, show z ∅ = 0 from hz] using htotal
    · intro S
      have h := hx.2 Sᶜ
      rw [subsetSum_neg] at h
      have hc := subsetSum_add_compl x S
      rw [htotal] at hc
      change z Sᶜ-z univ≤ subsetSum x S
      linarith

/-- Exact reflection as an equality of ordinary convex-body point sets. -/
theorem basePolytope_reflected {z : SetFunction V} (hz : Normalized z) :
    basePolytope (reflectedFunction z)=(-1 : ℝ) • basePolytope z := by
  ext x
  constructor
  · intro hx
    refine ⟨-x,(mem_basePolytope_reflected_iff hz x).mp hx,?_⟩
    simp
  · rintro ⟨y,hy,rfl⟩
    apply (mem_basePolytope_reflected_iff hz _).mpr
    simpa using hy

/-- An explicit complement identity on set functions yields the exact
translated-reflection identity for the polytopes, without geometric shortcuts. -/
theorem basePolytope_eq_translate_reflection {z w : SetFunction V}
    (hz : Normalized z) (t : V → ℝ)
    (he : reflectedFunction z=w-modular t) :
    basePolytope w=({t} : Set (V → ℝ))+(-1 : ℝ) • basePolytope z := by
  have hw : w=reflectedFunction z+modular t := by rw [he,sub_add_cancel]
  rw [hw,basePolytope_translate,basePolytope_reflected hz]

end GraphicalZonotopes

end
end
end BundlePart358

section BundlePart359
/- Source: Papers/GraphicalZonotopes/DoubledSymmetry.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace DoubledParts
open Finset
open scoped BigOperators Pointwise
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem two_choose_two_int (n : ℕ) :
    2*(n.choose 2 : ℤ)=(n : ℤ)*((n : ℤ)-1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hc : (n+1).choose 2=n.choose 2+n := by
      simpa only [Nat.choose_one_right, Nat.add_comm] using Nat.choose_succ_succ' n 1
    rw [hc]
    push_cast
    nlinarith

@[simp] theorem firstSet_compl (S : Finset (I×Fin 2)) : firstSet Sᶜ=(firstSet S)ᶜ := by
  ext i
  simp
@[simp] theorem secondSet_compl (S : Finset (I×Fin 2)) : secondSet Sᶜ=(secondSet S)ᶜ := by
  ext i
  simp
@[simp] theorem firstSet_univ : firstSet (univ : Finset (I×Fin 2))=univ := by
  ext i
  simp
@[simp] theorem secondSet_univ : secondSet (univ : Finset (I×Fin 2))=univ := by
  ext i
  simp

theorem double_count_compl (S : Finset (I×Fin 2)) :
    ((firstSet Sᶜ∩secondSet Sᶜ).card : ℤ)=
      (Fintype.card I : ℤ)-(S.card : ℤ)+((firstSet S∩secondSet S).card : ℤ) := by
  have hU : firstSet Sᶜ∩secondSet Sᶜ=(firstSet S∪secondSet S)ᶜ := by
    ext i
    simp
  have hcard := card_union_add_card_inter (firstSet S) (secondSet S)
  have hbound := card_le_univ (firstSet S∪secondSet S)
  rw [hU,card_compl,Nat.cast_sub hbound]
  have hc : ((firstSet S∪secondSet S).card : ℤ)+
      ((firstSet S∩secondSet S).card : ℤ)=((firstSet S).card : ℤ)+((secondSet S).card : ℤ) :=
    by exact_mod_cast hcard
  rw [card_eq_first_add_second]
  push_cast
  omega

theorem integerData_univ :
    integerData (univ : Finset (I×Fin 2))=
      2*(Fintype.card I : ℤ)*((Fintype.card I : ℤ)-1)+(Fintype.card I : ℤ) := by
  have h := integerData_count_identity (univ : Finset (I×Fin 2))
  simp only [firstSet_univ,secondSet_univ,inter_self,card_univ,Fintype.card_prod,
    Fintype.card_fin] at h
  have hc := two_choose_two_int (Fintype.card I*2)
  push_cast at h hc
  nlinarith

theorem integerData_compl (S : Finset (I×Fin 2)) :
    integerData Sᶜ=integerData S+integerData (univ : Finset (I×Fin 2))-
      2*(((Fintype.card I : ℤ)-1)*(S.card : ℤ)+((firstSet S).card : ℤ)) := by
  have hS := integerData_count_identity S
  have hC := integerData_count_identity Sᶜ
  have hcard : (Sᶜ.card : ℤ)=2*(Fintype.card I : ℤ)-(S.card : ℤ) := by
    rw [card_compl,Nat.cast_sub (card_le_univ S)]
    simp [Fintype.card_prod,mul_comm]
  have hfirst : ((firstSet Sᶜ).card : ℤ)=
      (Fintype.card I : ℤ)-((firstSet S).card : ℤ) := by
    rw [firstSet_compl,card_compl,Nat.cast_sub (card_le_univ (firstSet S))]
  rw [double_count_compl,hfirst] at hC
  have h2S := two_choose_two_int S.card
  have h2C := two_choose_two_int Sᶜ.card
  rw [hcard] at h2C
  rw [integerData_univ]
  nlinarith

theorem graphFunction_compl (S : Finset (I×Fin 2)) :
    graphFunction (graph I) Sᶜ-graphFunction (graph I) univ=
      graphFunction (graph I) S-2*((Fintype.card I : ℝ)-1)*(S.card : ℝ) := by
  have h := congrArg (fun m : ℤ => (m : ℝ)) (integerData_compl S)
  push_cast at h
  simp only [cast_integerData,modular,subsetSum] at h
  have hs : (∑ v∈S,(firstWeight v : ℝ))=((firstSet S).card : ℝ) := by
    exact_mod_cast firstWeight_sum S
  have hc : (∑ v∈Sᶜ,(firstWeight v : ℝ))=
      (Fintype.card I : ℝ)-((firstSet S).card : ℝ) := by
    have hh := firstWeight_sum Sᶜ
    rw [firstSet_compl,card_compl,Nat.cast_sub (card_le_univ (firstSet S))] at hh
    exact_mod_cast hh
  have hu : (∑ v : I×Fin 2,(firstWeight v : ℝ))=(Fintype.card I : ℝ) := by
    have hh := firstWeight_sum (univ : Finset (I×Fin 2))
    simp only [firstSet_univ,card_univ] at hh
    exact_mod_cast hh
  rw [hs,hc,hu] at h
  linarith

theorem floor_reflection_even (m M d : ℤ) (hM : Even M) :
    (m+M-2*d)/2-M/2=m/2-d := by
  rcases hM with ⟨k,hk⟩
  omega

theorem floor_reflection_odd (m M d : ℤ) (hM : Odd M) :
    (m+M-2*d)/2-M/2=m-m/2-d := by
  rcases hM with ⟨k,hk⟩
  omega

theorem integerData_univ_even (hI : Even (Fintype.card I)) :
    Even (integerData (univ : Finset (I×Fin 2))) := by
  obtain ⟨k,hk⟩ := hI
  have hc : (Fintype.card I : ℤ)=(k : ℤ)+(k : ℤ) := by exact_mod_cast hk
  rw [integerData_univ]
  refine ⟨(Fintype.card I : ℤ)*((Fintype.card I : ℤ)-1)+(k : ℤ),?_⟩
  nlinarith

theorem integerData_univ_odd (hI : Odd (Fintype.card I)) :
    Odd (integerData (univ : Finset (I×Fin 2))) := by
  obtain ⟨k,hk⟩ := hI
  have hc : (Fintype.card I : ℤ)=2*(k : ℤ)+1 := by exact_mod_cast hk
  rw [integerData_univ]
  refine ⟨(Fintype.card I : ℤ)*((Fintype.card I : ℤ)-1)+(k : ℤ),?_⟩
  nlinarith

def firstReflectionVector (v : I×Fin 2) : ℝ :=
  (Fintype.card I : ℝ)-1+(firstWeight v : ℝ)
def secondReflectionVector (v : I×Fin 2) : ℝ :=
  (Fintype.card I : ℝ)-1-(firstWeight v : ℝ)
def differenceReflectionVector (_ : I×Fin 2) : ℝ := (Fintype.card I : ℝ)-1

theorem modular_firstReflectionVector (S : Finset (I×Fin 2)) :
    modular firstReflectionVector S=
      ((Fintype.card I : ℝ)-1)*(S.card : ℝ)+((firstSet S).card : ℝ) := by
  have h := congrArg (fun m : ℤ => (m : ℝ)) (firstWeight_sum S)
  push_cast at h
  simp only [modular,subsetSum,firstReflectionVector,sum_add_distrib,sum_const,
    nsmul_eq_mul,h]
  ring

theorem modular_secondReflectionVector (S : Finset (I×Fin 2)) :
    modular secondReflectionVector S=
      ((Fintype.card I : ℝ)-1)*(S.card : ℝ)-((firstSet S).card : ℝ) := by
  have h := congrArg (fun m : ℤ => (m : ℝ)) (firstWeight_sum S)
  push_cast at h
  simp only [modular,subsetSum,secondReflectionVector,sum_sub_distrib,sum_const,
    nsmul_eq_mul,h]
  ring

theorem modular_differenceReflectionVector (S : Finset (I×Fin 2)) :
    modular differenceReflectionVector S=((Fintype.card I : ℝ)-1)*(S.card : ℝ) := by
  simp [modular,subsetSum,differenceReflectionVector,mul_comm] <;> ring

theorem reflected_setFunction_even (hI : Even (Fintype.card I)) :
    reflectedFunction (setFunction (I := I))=setFunction-modular firstReflectionVector := by
  funext S
  have h := floor_reflection_even (integerData S) (integerData (univ : Finset (I×Fin 2)))
    (((Fintype.card I : ℤ)-1)*(S.card : ℤ)+((firstSet S).card : ℤ))
    (integerData_univ_even hI)
  rw [← integerData_compl S] at h
  have hc := congrArg (fun m : ℤ => (m : ℝ)) h
  push_cast at hc
  simpa only [reflectedFunction,setFunction,Pi.sub_apply,modular_firstReflectionVector] using hc

theorem reflected_complementFunction_even (hI : Even (Fintype.card I)) :
    reflectedFunction (complementFunction (I := I))=
      complementFunction-modular secondReflectionVector := by
  funext S
  have hz := congrFun (reflected_setFunction_even hI) S
  change setFunction Sᶜ-setFunction univ=setFunction S-modular firstReflectionVector S at hz
  have hg := graphFunction_compl S
  simp only [reflectedFunction,complementFunction,Pi.sub_apply]
  rw [modular_firstReflectionVector] at hz
  rw [modular_secondReflectionVector]
  linarith

theorem reflected_setFunction_odd (hI : Odd (Fintype.card I)) :
    reflectedFunction (setFunction (I := I))=
      complementFunction-modular differenceReflectionVector := by
  funext S
  have h := floor_reflection_odd (integerData S) (integerData (univ : Finset (I×Fin 2)))
    (((Fintype.card I : ℤ)-1)*(S.card : ℤ)+((firstSet S).card : ℤ))
    (integerData_univ_odd hI)
  rw [← integerData_compl S] at h
  have hc := congrArg (fun m : ℤ => (m : ℝ)) h
  push_cast at hc
  rw [cast_integerData] at hc
  have hw : modular (fun v : I×Fin 2 => (firstWeight v : ℝ)) S=((firstSet S).card : ℝ) := by
    change (∑ v∈S,(firstWeight v : ℝ))=_
    exact_mod_cast firstWeight_sum S
  rw [hw] at hc
  change setFunction Sᶜ-setFunction univ=
    (graphFunction (graph I) S-setFunction S)-modular differenceReflectionVector S
  rw [modular_differenceReflectionVector]
  change (((integerData Sᶜ/2 : ℤ) : ℝ)-((integerData univ/2 : ℤ) : ℝ))=_
  dsimp only [setFunction]
  linarith

theorem polytope_centrallySymmetric (hI : Even (Fintype.card I)) :
    CentrallySymmetricUpToTranslation (polytope (I := I)) := by
  exact ⟨firstReflectionVector,basePolytope_eq_translate_reflection
    setFunction_translationNormalized.1 firstReflectionVector (reflected_setFunction_even hI)⟩

theorem complementPolytope_centrallySymmetric (hI : Even (Fintype.card I)) :
    CentrallySymmetricUpToTranslation (complementPolytope (I := I)) := by
  exact ⟨secondReflectionVector,basePolytope_eq_translate_reflection
    complementFunction_translationNormalized.1 secondReflectionVector
    (reflected_complementFunction_even hI)⟩

theorem complementPolytope_reflection (hI : Odd (Fintype.card I)) :
    complementPolytope (I := I)=
      ({differenceReflectionVector} : Set ((I×Fin 2) → ℝ))+(-1 : ℝ) • polytope :=
  basePolytope_eq_translate_reflection setFunction_translationNormalized.1
    differenceReflectionVector (reflected_setFunction_odd hI)

end DoubledParts
end GraphicalZonotopes

end
end
end BundlePart359

section BundlePart360
/- Source: Papers/GraphicalZonotopes/DoubledPrincipal.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace DoubledParts
open scoped Pointwise

/-- The full Theorem9.8, with both actual lattice summands, both geometric
indecomposabilities, their full dimensions and complete actual root-direction
graphs, every Boolean elemental slack, and the two parity-specific symmetry
conclusions. -/
def PrincipalBooleanPhaseClaim : Prop :=
  ∀ r : ℕ,4≤ r → ∃ Q R : Set ((Fin r×Fin 2) → ℝ),
    LatticePolytope Q ∧ LatticePolytope R ∧
    MinkowskiIndecomposable Q ∧ MinkowskiIndecomposable R ∧
    FullDimension Q ∧ FullDimension R ∧
    Q+R=graphicalZonotope (doubledPartGraph r) ∧
    actualDirectionGraph Q=doubledPartGraph r ∧ actualDirectionGraph R=doubledPartGraph r ∧
    BooleanElemental Q ∧ BooleanElemental R ∧
    (Even r → CentrallySymmetricUpToTranslation Q ∧ CentrallySymmetricUpToTranslation R) ∧
    (Odd r → ∃ t,R=({t} : Set ((Fin r×Fin 2) → ℝ))+(-1 : ℝ) • Q) ∧
    (Odd r → graphicalZonotope (doubledPartGraph r)=
      Q+(-1 : ℝ) • Q+({fun _ : Fin r×Fin 2 => ((r-1 : ℕ) : ℝ)} : Set ((Fin r×Fin 2) → ℝ)))

/-- A uniform floor-half construction proves all parity cases without a
restriction on r. Its finite four-bit coefficient identity is applied to
every four-clique through the explicit Möbius formula. -/
theorem principal_boolean_phase_theorem : PrincipalBooleanPhaseClaim := by
  intro r hr
  have h4 : 4≤ Fintype.card (Fin r) := by simpa using hr
  have h3 : 3≤ Fintype.card (Fin r) := by simpa using (show 3≤ r by omega)
  have hgraph : graph (Fin r)=doubledPartGraph r := rfl
  refine ⟨polytope (I := Fin r),complementPolytope (I := Fin r),
    polytope_lattice,complementPolytope_lattice,
    polytope_indecomposable h4,complementPolytope_indecomposable h4,
    polytope_fullDimension h3,complementPolytope_fullDimension h3,?_,?_,?_,
    polytope_booleanElemental,complementPolytope_booleanElemental,?_,?_,?_⟩
  · simpa only [hgraph] using (polytope_add_complement (I := Fin r))
  · exact (polytope_actualDirectionGraph h3).trans hgraph
  · exact (complementPolytope_actualDirectionGraph h3).trans hgraph
  · intro he
    have he' : Even (Fintype.card (Fin r)) := by simpa using he
    exact ⟨polytope_centrallySymmetric he',complementPolytope_centrallySymmetric he'⟩
  · intro ho
    exact ⟨differenceReflectionVector,
      complementPolytope_reflection (by simpa using ho)⟩
  · intro ho
    have he := complementPolytope_reflection (I := Fin r) (by simpa using ho)
    have ht : (differenceReflectionVector (I := Fin r))=
        (fun _ : Fin r×Fin 2 => ((r-1 : ℕ) : ℝ)) := by
      funext v
      simp only [differenceReflectionVector,Fintype.card_fin]
      rw [Nat.cast_sub (show 1≤ r by omega),Nat.cast_one]
    rw [ht] at he
    rw [← hgraph,← polytope_add_complement,he]
    ac_rfl

end DoubledParts
end GraphicalZonotopes

end
end
end BundlePart360

section BundlePart361
/- Source: Papers/GraphicalZonotopes/UnitLatticeSharp.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open scoped Pointwise

/-- The entire statement of Theorem 9.5: the unrestricted classification and
its actual seven-dimensional lattice equality witness. -/
theorem unit_lattice_classification_sharp :
    Targets.UnitLatticeClassification ∧
      ∃ Q : Set ((Fin 4×Fin 2) → ℝ),LatticePolytope Q ∧
        MinkowskiIndecomposable Q ∧ Module.finrank ℝ (vectorSpan ℝ Q)=7 ∧
        IsMinkowskiSummand Q (graphicalZonotope (doubledPartGraph 4)) ∧
        actualDirectionGraph Q=doubledPartGraph 4 := by
  obtain ⟨Q,R,hQ,hR,hiQ,hiR,hdQ,hdR,he,hgraph,hgraphR,hrest⟩ :=
    DoubledParts.principal_boolean_phase_theorem 4 (by norm_num)
  exact ⟨unit_lattice_classification,Q,hQ,hiQ,
    by simpa only [FullDimension,Fintype.card_prod,Fintype.card_fin] using hdQ,
    ⟨R,hR.compact,hR.convex,hiR.1,he⟩,hgraph⟩

end GraphicalZonotopes

end
end
end BundlePart361

section BundlePart362
/- Source: Audit/AllResults.lean -/






/-! # Complete principal-result audit entry point

Every import is a genuine mathematical source module. No result is assumed here.
-/



















#print axioms GraphicalZonotopes.Path.principal_path_theorem
#print axioms GraphicalZonotopes.Path.polytope_defining_equations
#print axioms GraphicalZonotopes.Path.polytope_defining_equations_real
#print axioms GraphicalZonotopes.Path.polytope_defining_equations_sums
#print axioms GraphicalZonotopes.Path.setFunction_expansion
#print axioms GraphicalZonotopes.Path.every_exposed_edge_is_graph_direction
#print axioms GraphicalZonotopes.generalizedPermutahedron_iff_weak_complete
#print axioms GraphicalZonotopes.minkowskiIndecomposable_iff_polytopal
#print axioms GraphicalZonotopes.sharp_direction_bounds
#print axioms GraphicalZonotopes.generalizedPermutahedron_exposed_edge_is_root
#print axioms GraphicalZonotopes.root_parallel_pair_eq
#print axioms GraphicalZonotopes.direction_bounds_polytopal
#print axioms GraphicalZonotopes.ExtremeSupermodular.spanning_tetrahedra
#print axioms GraphicalZonotopes.edge_bound_of_connected_tetrahedra
#print axioms GraphicalZonotopes.maximum_degree_bound_of_connected_tetrahedra
#print axioms GraphicalZonotopes.Path.setFunction_eq_booleanFormula
#print axioms GraphicalZonotopes.Path.polytope_boolean_defining_equations
#print axioms GraphicalZonotopes.DoubledParts.principal_boolean_phase_theorem
#print axioms GraphicalZonotopes.BooleanFourier.boolean_face_line
#print axioms GraphicalZonotopes.BooleanFourier.faceKernel_finrank
#print axioms GraphicalZonotopes.threeTree_classification_polytopal
#print axioms GraphicalZonotopes.threeTree_classification
#print axioms GraphicalZonotopes.threeTree_classification_literal
#print axioms GraphicalZonotopes.admissible_threeTree_lattice_witness
#print axioms GraphicalZonotopes.threeTree_lattice_dilation_sharp
#print axioms GraphicalZonotopes.threeTree_lattice_lower_bound_polytopal
#print axioms GraphicalZonotopes.Separator.induced_separator_capacity_finite
#print axioms GraphicalZonotopes.Separator.positive_response_gluing_finite
#print axioms GraphicalZonotopes.Separator.clique_separator_capacity_finite
#print axioms GraphicalZonotopes.unit_lattice_classification_sharp
#print axioms GraphicalZonotopes.unit_lattice_classification_polytopal
#print axioms GraphicalZonotopes.unit_translated_lattice_classification_polytopal
#print axioms GraphicalZonotopes.threeTree_translated_lattice_lower_bound
#print axioms GraphicalZonotopes.FourPartCompletion.cartesian_completion
#print axioms GraphicalZonotopes.four_partite_spanning_threeTrees
#print axioms GraphicalZonotopes.four_partite_threeTree_dimension_attained
#print axioms GraphicalZonotopes.threeTree_actual_dimension_admissible
#print axioms GraphicalZonotopes.admissible_threeTree_active_witness
#print axioms GraphicalZonotopes.maximumThreeTreeSupportDimension_eq_polytopal
#print axioms GraphicalZonotopes.optimal_k5_free_dilation
#print axioms GraphicalZonotopes.optimal_k5_free_dilation_attained
#print axioms GraphicalZonotopes.optimal_k5_free_dilation_lower_bound_polytopal
#print axioms GraphicalZonotopes.DoubledParts.one_singleton_decomposition
#print axioms GraphicalZonotopes.FourSmallParts.four_small_parts_decomposition
#print axioms GraphicalZonotopes.boolean_decomposition_every_dimension
#print axioms GraphicalZonotopes.BooleanModule.small_count_lattice_books
#print axioms GraphicalZonotopes.BooleanModule.one_outer_lattice_book
#print axioms GraphicalZonotopes.BooleanModule.small_count_lattice_books_literal
#print axioms GraphicalZonotopes.DiamondBook.paper_theorem_8_1_literal
#print axioms GraphicalZonotopes.DiamondBook.paper_theorem_8_1
#print axioms GraphicalZonotopes.DiamondBook.maximum_dimension
#print axioms GraphicalZonotopes.DiamondBook.diamond_witness_multipartite
#print axioms GraphicalZonotopes.DiamondBook.no_supporting_spanning_threeTree
#print axioms GraphicalZonotopes.BooleanModule.positive_star_interpolation
#print axioms GraphicalZonotopes.BooleanModule.negative_star_interpolation
#print axioms GraphicalZonotopes.BooleanModule.threshold_book_interval
#print axioms GraphicalZonotopes.BooleanModule.book_upper_interval
#print axioms GraphicalZonotopes.maximumIndecomposableDimension_eq_polytopal
#print axioms GraphicalZonotopes.DiamondBook.paper_theorem_8_1_polytopal
#print axioms GraphicalZonotopes.not_fullLatticeSummandAt_zero
#print axioms GraphicalZonotopes.PathJoin.corollary_nine_four
#print axioms GraphicalZonotopes.PathJoin.appendix_B_one
#print axioms GraphicalZonotopes.clique_book_classification
#print axioms GraphicalZonotopes.clique_book_classification_polytopal
#print axioms GraphicalZonotopes.SaturatedDirections.paper_theorem_7_12
#print axioms GraphicalZonotopes.SaturatedDirections.paper_theorem_7_12_polytopal
#print axioms GraphicalZonotopes.SaturatedDirections.paper_theorem_7_12_geometric
#print axioms GraphicalZonotopes.saturatedHubNeighbors_closed_formula
#print axioms GraphicalZonotopes.SparseFamily.paper_theorem_8_2
#print axioms GraphicalZonotopes.SparseFamily.paper_theorem_8_2_polytopal
#print axioms GraphicalZonotopes.TwoHub.exponential_lattice_summand
#print axioms GraphicalZonotopes.TwoHub.exponential_family
#print axioms GraphicalZonotopes.TwoHub.exponential_polytopal_summand
#print axioms GraphicalZonotopes.TwoHub.two_singleton_classification
#print axioms GraphicalZonotopes.TwoHub.classification_polytopal
#print axioms GraphicalZonotopes.TwoHub.full_polytopal_iff
#print axioms GraphicalZonotopes.TwoHub.lattice_polytopal_attainment
#print axioms GraphicalZonotopes.partial_threeTree_piecewise_maximum
#print axioms GraphicalZonotopes.partial_threeTree_full_dimension_spectrum
#print axioms GraphicalZonotopes.threeTree_dimension_and_spectrum
#print axioms GraphicalZonotopes.partial_threeTree_support_classification_polytopal_finite
#print axioms GraphicalZonotopes.partial_threeTree_piecewise_maximum_finite
#print axioms GraphicalZonotopes.partial_threeTree_full_dimension_spectrum_polytopal_finite
#print axioms GraphicalZonotopes.SupportsFullIndecomposable.triangle_free_components_le_one
#print axioms GraphicalZonotopes.SupportsFullIndecomposable.separator_contains_triangle
#print axioms GraphicalZonotopes.SupportsFullIndecomposable.delete_lt_three_preconnected
#print axioms GraphicalZonotopes.weak_summand_exposed_edge_direction
#print axioms GraphicalZonotopes.weakSummand_indecomposable_iff_polytopal
#print axioms GraphicalZonotopes.isWeakMinkowskiSummand_graphical_iff_finite_complement
#print axioms GraphicalZonotopes.isMinkowskiSummand_graphical_iff_finite_complement
#print axioms GraphicalZonotopes.partial_threeTree_polytope_support
#print axioms GraphicalZonotopes.BooleanModule.cliqueCapacity_int_formula
#print axioms GraphicalZonotopes.TwoHub.paper_corollary_8_5
#print axioms GraphicalZonotopes.HamiltonianDeletion.hamiltonian_component_card_delete_le
#print axioms GraphicalZonotopes.IsThreeTree.admissible_of_hamiltonian
#print axioms GraphicalZonotopes.hamiltonian_threeTree_lattice_polytopal_finite
#print axioms GraphicalZonotopes.actualEdgeDirectionLines_finite
#print axioms GraphicalZonotopes.directionCount_eq_geometric_line_count
#print axioms GraphicalZonotopes.three_hub_book_maximum
#print axioms GraphicalZonotopes.TreeJoin.induced_subcubic_iff_subtree
#print axioms GraphicalZonotopes.TreeJoin.maximum_dimension
#print axioms GraphicalZonotopes.TreeJoin.supports_full_iff
#print axioms GraphicalZonotopes.TreeJoin.paper_corollary_6_9_tree_join
#print axioms GraphicalZonotopes.SparseFamily.complete_family
#print axioms GraphicalZonotopes.TwoHub.CellDecisionTree.root_valid
#print axioms GraphicalZonotopes.TwoHub.CellDecisionTree.leaves_card
#print axioms GraphicalZonotopes.TwoHub.CellDecisionTree.root_proper
#print axioms GraphicalZonotopes.TwoHub.PartitionData.partitionDilation_eq
#print axioms GraphicalZonotopes.TwoHub.decision_tree_lattice_summand
#print axioms GraphicalZonotopes.TwoHub.paper_lemma_8_6

end BundlePart362

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

section BundlePart373
/- Source: dev/planar_search/schoenflies_port/Schoenflies/Graph/Walk.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/




/-!
# Walks and paths in a multigraph

Mathlib's `Graph α β` carries incidence (`G.IsLink e x y`) and nothing that moves along it.
This file is the bottom of the combinatorial layer: walks, paths, reachability and
connectedness, all of which the plane development consumes through one theorem —
`Graph.IsWalk.contains_path`, the blueprint's "shorten an arbitrary walk at repeated
vertices".

## A walk is a list of edges

`G.IsWalk u W v` says the edge list `W` walks from `u` to `v`, each edge taken from the vertex
the previous one arrived at. It names its **edges**, not its vertices. That is forced by
parallel edges: two edges with the same ends are distinguishable only by name, and a walk
along one of them must be able to say which it took — a two-vertex cycle, which the plane
layer builds out of a Jordan curve cut at two points, is exactly such a graph. Nothing is
lost by naming edges, because an edge determines where taking it arrives
(`Graph.IsLink.right_unique` upstream, `Graph.IsWalk.target_unique` here).

It is an **inductive family**, not a recursion over the list. Every consumer argues by
induction along the walk, and the inductive gives that directly, naming the waypoint of each
step; a recursion `fun u (e :: W) v => ∃ w, G.IsLink e u w ∧ IsWalk G w W v` would force
every proof to generalize the source vertex by hand and to destructure an existential at each
step. The relation is built at the **source** end, since that is the end a list is extended
at; concatenation (`Graph.IsWalk.append`) and reversal (`Graph.IsWalk.reverse`) are proved
here once, and after that no argument has to care.

The empty walk demands `x ∈ V(G)`. This buys the whole file: every vertex a walk visits is a
vertex of the graph with *no* side hypothesis, because Mathlib's `Graph` already forces the
ends of an edge into `V(G)`.

## A path carries its own freshness

`G.IsPath u W v` is a walk with one clause added at each step: the vertex the step departs
from is not among those the rest of the path visits. The condition travels with the
induction, instead of being imposed afterwards on a separately computed vertex list — which
would have to be computed, and would need the graph to be loopless before it was even
correct.

## Loops

Mathlib's `Graph` allows an edge with both ends equal; the blueprint's graphs have none.
**Walks tolerate loops and paths exclude them automatically** — no hypothesis on `G` anywhere
in this file. A step of a path from `u` along `e` to `w` requires `u ∉ G.walkVertices w W`,
and `w` is always in that set, so `u ≠ w`: the freshness clause already says a path's step is
not a loop (`Graph.IsPath.not_isLoopAt`). Imposing looplessness on the graph instead would
put a hypothesis on every statement in the layer to rule out something the definitions
already rule out.

## Namespace

Declarations live in the root `Graph` namespace, extending Mathlib's, rather than in
`Schoenflies`: `G.IsWalk`, `hW.append`, `hP.isWalk` are the spellings every consumer wants,
and dot notation on a Mathlib type resolves through the type's own namespace.

## Blueprint

The blueprint uses finite graphs as an imported foundation (§"Imported facts", *Finite
graphs*: "in a finite connected graph, any two vertices are joined by a simple path, obtained
by shortening an arbitrary walk at repeated vertices"). This file supplies that import.

* `Graph.IsWalk.contains_path` — shortening a walk to a path; used at
  `lem:polygonal-connected` ("take a simple path in the resulting finite graph"),
  `lem:finite-polygonal-union` ("a simple graph path has the required realization") and
  `lem:skeleton-crosscuts` ("the resulting finite graph is connected, so it contains a
  simple graph path `P` from `a` to `b`").
* `Graph.Reaches`, `Graph.Connected` — the connectedness those three lemmas invoke.
* `Graph.IsPath.nodup` — a simple path repeats no edge; underneath the finiteness arguments
  that bound a path's length.
* `Graph.IsPath.reverse`, `Graph.IsPath.split` — a path backwards, and a path cut in two at a
  vertex it visits; what `lem:subdivision-ear-preserve` and `lem:relative-ear` run on.
-/

open Set

variable {α β : Type*} {G H : Graph α β} {u v w x y z : α} {e f : β} {W W₁ W₂ P : List β}

namespace Graph

/-! ### The vertices an edge list touches -/

/-- The vertices lying on at least one edge of `W`. -/
def coveredVertices (G : Graph α β) (W : List β) : Set α := {x | ∃ e ∈ W, G.Inc e x}

/-- The vertices a walk from `u` along `W` visits: its source, plus the ends of every edge it
takes. Defined for any edge list, not just for one that walks — the freshness clause of a
path reads it about the *rest* of the path before that rest is known to be a walk at all. -/
def walkVertices (G : Graph α β) (u : α) (W : List β) : Set α := insert u (G.coveredVertices W)

theorem mem_coveredVertices_iff : x ∈ G.coveredVertices W ↔ ∃ e ∈ W, G.Inc e x := Iff.rfl

theorem mem_walkVertices_iff : x ∈ G.walkVertices u W ↔ x = u ∨ x ∈ G.coveredVertices W :=
  Set.mem_insert_iff

@[simp]
theorem coveredVertices_nil : G.coveredVertices ([] : List β) = ∅ := by
  simp [coveredVertices]

@[simp]
theorem walkVertices_nil : G.walkVertices u ([] : List β) = {u} := by
  simp [walkVertices]

theorem mem_coveredVertices (he : e ∈ W) (hx : G.Inc e x) : x ∈ G.coveredVertices W :=
  ⟨e, he, hx⟩

theorem mem_walkVertices_self : u ∈ G.walkVertices u W := Set.mem_insert _ _

theorem mem_walkVertices_of_mem_covered (hx : x ∈ G.coveredVertices W) :
    x ∈ G.walkVertices u W :=
  Set.mem_insert_of_mem _ hx

theorem coveredVertices_mono (h : W₁ ⊆ W₂) : G.coveredVertices W₁ ⊆ G.coveredVertices W₂ :=
  fun _ ⟨e, he, hx⟩ ↦ ⟨e, h he, hx⟩

theorem walkVertices_mono (h : W₁ ⊆ W₂) : G.walkVertices u W₁ ⊆ G.walkVertices u W₂ :=
  Set.insert_subset_insert (coveredVertices_mono h)

@[simp]
theorem coveredVertices_reverse : G.coveredVertices W.reverse = G.coveredVertices W := by
  simp [coveredVertices]

@[simp]
theorem walkVertices_reverse : G.walkVertices u W.reverse = G.walkVertices u W := by
  simp [walkVertices]

theorem coveredVertices_append :
    G.coveredVertices (W₁ ++ W₂) = G.coveredVertices W₁ ∪ G.coveredVertices W₂ := by
  ext x
  simp only [mem_coveredVertices_iff, List.mem_append, Set.mem_union]
  constructor
  · rintro ⟨e, he | he, hx⟩
    exacts [Or.inl ⟨e, he, hx⟩, Or.inr ⟨e, he, hx⟩]
  · rintro (⟨e, he, hx⟩ | ⟨e, he, hx⟩)
    exacts [⟨e, Or.inl he, hx⟩, ⟨e, Or.inr he, hx⟩]

/-- Every vertex on an edge of the graph is a vertex of the graph. -/
theorem coveredVertices_subset_vertexSet : G.coveredVertices W ⊆ V(G) :=
  fun _ ⟨_, _, hx⟩ ↦ hx.vertex_mem

theorem walkVertices_subset_vertexSet (hu : u ∈ V(G)) : G.walkVertices u W ⊆ V(G) :=
  Set.insert_subset hu coveredVertices_subset_vertexSet

/-- Moving the visited set across a first step, forwards: a vertex the walk visits is either
the vertex it departs from or a vertex the rest of it visits. This is where the step lemma is
used — the edge `e` has only the two ends `u` and `w`, so a vertex on `e` is one of them. -/
theorem mem_walkVertices_cons (hl : G.IsLink e u w) (hx : x ∈ G.walkVertices u (e :: W)) :
    x = u ∨ x ∈ G.walkVertices w W := by
  rcases mem_walkVertices_iff.1 hx with rfl | ⟨f, hf, hxf⟩
  · exact Or.inl rfl
  rcases List.mem_cons.1 hf with rfl | hf
  · rcases hxf.eq_or_eq_of_isLink hl with rfl | rfl
    exacts [Or.inl rfl, Or.inr mem_walkVertices_self]
  · exact Or.inr (mem_walkVertices_of_mem_covered ⟨f, hf, hxf⟩)

/-- Moving the visited set across a first step, backwards. -/
theorem mem_walkVertices_cons_of_mem (hl : G.IsLink e u w) (hx : x ∈ G.walkVertices w W) :
    x ∈ G.walkVertices u (e :: W) := by
  rcases mem_walkVertices_iff.1 hx with rfl | hx
  · exact mem_walkVertices_of_mem_covered ⟨e, List.mem_cons_self, hl.inc_right⟩
  · exact mem_walkVertices_of_mem_covered (coveredVertices_mono (List.subset_cons_self _ _) hx)

/-! ### Walks -/

/-- `G.IsWalk u W v` : the edges of `W`, in order, walk from `u` to `v` in `G`. Each edge is
taken from the vertex the previous one arrived at; the list is read at its head, so the
relation is built at the source end. -/
inductive IsWalk (G : Graph α β) : α → List β → α → Prop
  /-- Standing still at a vertex of the graph is a walk. -/
  | nil {x : α} (hx : x ∈ V(G)) : G.IsWalk x [] x
  /-- Taking an edge from the source of a walk prepends it. -/
  | cons {u w v : α} {e : β} {W : List β} (hl : G.IsLink e u w) (hW : G.IsWalk w W v) :
      G.IsWalk u (e :: W) v

theorem IsWalk.single (hl : G.IsLink e u v) : G.IsWalk u [e] v :=
  .cons hl (.nil hl.right_mem)

theorem IsWalk.left_mem (h : G.IsWalk u W v) : u ∈ V(G) := by
  cases h with
  | nil hx => exact hx
  | cons hl _ => exact hl.left_mem

theorem IsWalk.right_mem (h : G.IsWalk u W v) : v ∈ V(G) := by
  induction h with
  | nil hx => exact hx
  | cons _ _ ih => exact ih

/-- The edges of a walk are edges of the graph. -/
theorem IsWalk.edge_mem (h : G.IsWalk u W v) (he : e ∈ W) : e ∈ E(G) := by
  induction h with
  | nil => simp at he
  | cons hl _ ih =>
    rcases List.mem_cons.1 he with rfl | he
    exacts [hl.edge_mem, ih he]

theorem IsWalk.edgeSet_subset (h : G.IsWalk u W v) : ∀ e ∈ W, e ∈ E(G) := fun _ he ↦ h.edge_mem he

theorem IsWalk.target_mem_walkVertices (h : G.IsWalk u W v) : v ∈ G.walkVertices u W := by
  induction h with
  | nil => exact mem_walkVertices_self
  | cons hl _ ih => exact mem_walkVertices_cons_of_mem hl ih

/-- Every vertex a walk visits is a vertex of the graph — with no hypothesis, since the
empty walk already stands at one. -/
theorem IsWalk.walkVertices_subset (h : G.IsWalk u W v) : G.walkVertices u W ⊆ V(G) :=
  walkVertices_subset_vertexSet h.left_mem

@[simp]
theorem isWalk_nil_iff : G.IsWalk u [] v ↔ u = v ∧ u ∈ V(G) := by
  constructor
  · rintro ⟨hx⟩; exact ⟨rfl, hx⟩
  · rintro ⟨rfl, hx⟩; exact .nil hx

theorem IsWalk.eq_of_nil (h : G.IsWalk u [] v) : u = v := (isWalk_nil_iff.1 h).1

/-- The step lemma, run along a whole walk: naming the edges determines the vertices, so a
walk from a given source along a given edge list arrives nowhere else. Its engine is that an
edge has only two ends, `Graph.IsLink.right_unique`, which holds in Mathlib's `Graph` with no
distinctness hypothesis (a loop arrives back where it started, deterministically). -/
theorem IsWalk.target_unique (h : G.IsWalk u W v) (h' : G.IsWalk u W w) : v = w := by
  induction h generalizing w with
  | nil hx => exact h'.eq_of_nil.symm ▸ rfl
  | @cons u w' v e W hl _ ih =>
    cases h' with
    | cons hl' hW' => exact ih (hl.right_unique hl' ▸ hW')

/-- Walks concatenate, with no side condition. -/
theorem IsWalk.append (h₁ : G.IsWalk u W₁ w) (h₂ : G.IsWalk w W₂ v) :
    G.IsWalk u (W₁ ++ W₂) v := by
  induction h₁ with
  | nil => simpa using h₂
  | cons hl _ ih => exact .cons hl (ih h₂)

/-- A walk runs backwards along the reverse of its edge list, with no side condition. -/
theorem IsWalk.reverse (h : G.IsWalk u W v) : G.IsWalk v W.reverse u := by
  induction h with
  | nil hx => simpa using IsWalk.nil hx
  | @cons u w v e W hl _ ih =>
    rw [List.reverse_cons]
    exact ih.append (IsWalk.single hl.symm)

/-- A walk in a subgraph is a walk in the graph. -/
theorem IsWalk.mono (hHG : H ≤ G) (h : H.IsWalk u W v) : G.IsWalk u W v := by
  induction h with
  | nil hx => exact .nil (hHG.vertexSet_mono hx)
  | cons hl _ ih => exact .cons (hl.mono hHG) ih

/-- A walk of a graph whose edges all survive into a subgraph is a walk of that subgraph.
This is the direction a deletion argument needs: an edge is removed, and a walk that never
used it is still there. -/
theorem IsWalk.anti (hHG : H ≤ G) (h : G.IsWalk u W v) (hu : u ∈ V(H))
    (hE : ∀ e ∈ W, e ∈ E(H)) : H.IsWalk u W v := by
  induction h with
  | nil => exact .nil hu
  | @cons u w v e W hl _ ih =>
    have he : e ∈ E(H) := hE e List.mem_cons_self
    have hl' : H.IsLink e u w := (hHG.isLink_iff he).2 hl
    exact .cons hl' (ih hl'.right_mem fun f hf ↦ hE f (List.mem_cons_of_mem _ hf))

/-- A walk that starts inside a set of vertices and ends outside it crosses the boundary
along one of its own edges. -/
theorem IsWalk.crossing {S : Set α} (h : G.IsWalk u W v) (hu : u ∈ S) (hv : v ∉ S) :
    ∃ e ∈ W, ∃ x y, G.IsLink e x y ∧ x ∈ S ∧ y ∉ S := by
  induction h with
  | nil => exact absurd hu hv
  | @cons u w v e W hl _ ih =>
    by_cases hw : w ∈ S
    · obtain ⟨f, hf, x, y, hxy, hx, hy⟩ := ih hw hv
      exact ⟨f, List.mem_cons_of_mem _ hf, x, y, hxy, hx, hy⟩
    · exact ⟨e, List.mem_cons_self, u, w, hl, hu, hw⟩

/-! ### Paths -/

/-- `G.IsPath u W v` : a walk from `u` to `v` that never returns to a vertex it has left.
The condition is carried step by step — the vertex a step departs from is not among those the
rest of the path visits — rather than imposed afterwards on a computed vertex list. -/
inductive IsPath (G : Graph α β) : α → List β → α → Prop
  /-- Standing still at a vertex of the graph is a path. -/
  | nil {x : α} (hx : x ∈ V(G)) : G.IsPath x [] x
  /-- A step onto a path is allowed when the vertex it departs from is fresh. -/
  | cons {u w v : α} {e : β} {W : List β} (hl : G.IsLink e u w) (hW : G.IsPath w W v)
      (hfresh : u ∉ G.walkVertices w W) : G.IsPath u (e :: W) v

theorem IsPath.isWalk (h : G.IsPath u W v) : G.IsWalk u W v := by
  induction h with
  | nil hx => exact .nil hx
  | cons hl _ _ ih => exact .cons hl ih

theorem IsPath.left_mem (h : G.IsPath u W v) : u ∈ V(G) := h.isWalk.left_mem

theorem IsPath.right_mem (h : G.IsPath u W v) : v ∈ V(G) := h.isWalk.right_mem

theorem IsPath.edge_mem (h : G.IsPath u W v) (he : e ∈ W) : e ∈ E(G) := h.isWalk.edge_mem he

/-- One edge between two distinct vertices is a path. -/
theorem IsPath.single (hl : G.IsLink e u v) (huv : u ≠ v) : G.IsPath u [e] v :=
  .cons hl (.nil hl.right_mem) (by simpa using huv)

/-- A path's step never departs from where it arrives: the freshness clause already says so,
because a walk always visits its own source. -/
theorem IsPath.cons_ne (hW : G.IsPath w W v) (hfresh : u ∉ G.walkVertices w W) : u ≠ w := by
  rintro rfl
  exact hfresh mem_walkVertices_self

/-- **A path never takes a loop.** This is why nothing in this file has to assume the graph is
loopless: a step along a loop would depart from the vertex it arrives at, which the freshness
clause forbids. -/
theorem IsPath.not_isLoopAt (h : G.IsPath u W v) (he : e ∈ W) (x : α) : ¬ G.IsLoopAt e x := by
  induction h with
  | nil => simp at he
  | @cons u w v f W hl hW hfresh ih =>
    rcases List.mem_cons.1 he with rfl | he
    · intro hloop
      -- `hloop : G.IsLink e x x` shares an edge with `hl : G.IsLink e u w`, so `u = w`.
      rcases hl.eq_and_eq_or_eq_and_eq hloop with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        exact IsPath.cons_ne hW hfresh rfl
    · exact ih he

/-- A path takes no edge twice: an edge it took again would put the vertex it departed from
back among the ones the rest of the path visits. -/
theorem IsPath.nodup (h : G.IsPath u W v) : W.Nodup := by
  induction h with
  | nil => exact List.nodup_nil
  | @cons u w v e W hl hW hfresh ih =>
    refine List.nodup_cons.2 ⟨fun he ↦ hfresh ?_, ih⟩
    exact mem_walkVertices_of_mem_covered ⟨e, he, hl.inc_left⟩

/-- A path in a subgraph is a path in the graph: the freshness clause reads only which
vertices the remaining edges touch, and a subgraph's edges have the same ends there. -/
theorem IsPath.mono (hHG : H ≤ G) (h : H.IsPath u W v) : G.IsPath u W v := by
  induction h with
  | nil hx => exact .nil (hHG.vertexSet_mono hx)
  | @cons u w v e W hl hW hfresh ih =>
    refine .cons (hl.mono hHG) ih fun hmem ↦ hfresh ?_
    -- Freshness travels because `H`'s edges link the same pairs in `G`.
    rcases mem_walkVertices_iff.1 hmem with rfl | ⟨f, hf, hinc⟩
    · exact mem_walkVertices_self
    · obtain ⟨y, hy⟩ := hinc
      exact mem_walkVertices_of_mem_covered
        ⟨f, hf, ((hHG.isLink_iff (hW.isWalk.edge_mem hf)).2 hy).inc_left⟩

theorem IsPath.target_mem_walkVertices (h : G.IsPath u W v) : v ∈ G.walkVertices u W :=
  h.isWalk.target_mem_walkVertices

/-- A path grows at its **target** end. The relation is built at the source end, so this is
the direction that has to be worked for; it is what reversal runs on. -/
theorem IsPath.extend_at_target (h : G.IsPath u P w) (hl : G.IsLink e w v)
    (hv : v ∉ G.walkVertices u P) : G.IsPath u (P ++ [e]) v := by
  induction h with
  | nil hx =>
    rw [walkVertices_nil] at hv
    exact List.nil_append _ ▸ IsPath.single hl (Ne.symm hv)
  | @cons u w₀ w f P₀ hl₀ hP₀ hfresh ih =>
    have hv₀ : v ∉ G.walkVertices w₀ P₀ := fun hmem ↦ hv (mem_walkVertices_cons_of_mem hl₀ hmem)
    refine List.cons_append .. ▸ .cons hl₀ (ih hl hv₀) fun hmem ↦ ?_
    -- The departure vertex is still fresh: the only new edge is `e`, whose ends are the old
    -- target `w` — already visited — and `v`, which the source is not.
    rcases mem_walkVertices_iff.1 hmem with rfl | hcov
    · exact hfresh mem_walkVertices_self
    rw [coveredVertices_append] at hcov
    rcases hcov with hcov | ⟨f', hf', hinc⟩
    · exact hfresh (mem_walkVertices_of_mem_covered hcov)
    · obtain rfl : f' = e := by simpa using hf'
      rcases hinc.eq_or_eq_of_isLink hl with rfl | rfl
      · exact hfresh hP₀.target_mem_walkVertices
      · exact hv mem_walkVertices_self

/-- A path runs backwards over the same edges. -/
theorem IsPath.reverse (h : G.IsPath u W v) : G.IsPath v W.reverse u := by
  induction h with
  | nil hx => simpa using IsPath.nil hx
  | @cons u w v e W hl hW hfresh ih =>
    rw [List.reverse_cons]
    refine ih.extend_at_target hl.symm fun hmem ↦ hfresh ?_
    -- `u` avoids everything the rest of the path visits, and reversal changes none of that.
    rw [walkVertices_reverse] at hmem
    rcases mem_walkVertices_iff.1 hmem with rfl | hcov
    · exact hW.target_mem_walkVertices
    · exact mem_walkVertices_of_mem_covered hcov

/-- **Cutting a path at a vertex it passes through.** A path through `x` has a piece of itself
running from `x` to its target, and that piece uses only the path's own edges. This is the
engine of `Graph.IsWalk.contains_path`: when the next vertex is already on the path built so
far, the path is cut there instead of extended, so nothing ever gets longer. -/
theorem IsPath.from_visited (h : G.IsPath u W v) (hx : x ∈ G.walkVertices u W) :
    ∃ T, G.IsPath x T v ∧ T ⊆ W := by
  induction h with
  | nil hx' =>
    rw [walkVertices_nil] at hx
    obtain rfl := hx
    exact ⟨[], .nil hx', List.nil_subset _⟩
  | @cons u w v e W hl hW hfresh ih =>
    rcases mem_walkVertices_cons hl hx with rfl | hx'
    · exact ⟨e :: W, .cons hl hW hfresh, List.Subset.refl _⟩
    · obtain ⟨T, hT, hTW⟩ := ih hx'
      exact ⟨T, hT, List.Subset.trans hTW (List.subset_cons_self _ _)⟩

/-- A path splits at any vertex it visits, and the far half never returns to the source.
`Graph.IsPath.from_visited` is the suffix alone; the prefix is the awkward half, since the
relation is built at the source end and the prefix is what the induction has to carry
forward. -/
theorem IsPath.split (h : G.IsPath u W v) (hx : x ∈ G.walkVertices u W) :
    ∃ W₁ W₂, W = W₁ ++ W₂ ∧ G.IsPath u W₁ x ∧ G.IsPath x W₂ v ∧
      (x = u ∨ u ∉ G.walkVertices x W₂) := by
  induction h with
  | nil hx' =>
    rw [walkVertices_nil] at hx
    obtain rfl := hx
    exact ⟨[], [], rfl, .nil hx', .nil hx', Or.inl rfl⟩
  | @cons u w v e W hl hW hfresh ih =>
    rcases mem_walkVertices_cons hl hx with rfl | hx'
    · exact ⟨[], e :: W, rfl, .nil hl.left_mem, .cons hl hW hfresh, Or.inl rfl⟩
    obtain ⟨W₁, W₂, rfl, h₁, h₂, -⟩ := ih hx'
    have hsub₁ : W₁ ⊆ W₁ ++ W₂ := List.subset_append_left _ _
    have hsub₂ : W₂ ⊆ W₁ ++ W₂ := List.subset_append_right _ _
    refine ⟨e :: W₁, W₂, rfl, .cons hl h₁ fun hmem ↦ hfresh (walkVertices_mono hsub₁ hmem),
      h₂, Or.inr fun hmem ↦ hfresh ?_⟩
    -- The far half's edges are among the rest, which the source already avoided.
    rcases mem_walkVertices_iff.1 hmem with rfl | hcov
    · exact hx'
    · exact mem_walkVertices_of_mem_covered (coveredVertices_mono hsub₂ hcov)

/-- **Every walk contains a path** between the same two vertices, using only the walk's own
edges. This is the blueprint's "shorten an arbitrary walk at repeated vertices"; the
induction never lengthens anything, because the only alternative to prepending an edge is to
cut the path already built (`Graph.IsPath.from_visited`). -/
theorem IsWalk.contains_path (h : G.IsWalk u W v) : ∃ P, G.IsPath u P v ∧ P ⊆ W := by
  induction h with
  | nil hx => exact ⟨[], .nil hx, List.Subset.refl _⟩
  | @cons u w v e W hl hW ih =>
    obtain ⟨P, hP, hPW⟩ := ih
    by_cases hu : u ∈ G.walkVertices w P
    · -- The step lands on the path already built: cut it there rather than extend it.
      obtain ⟨T, hT, hTP⟩ := hP.from_visited hu
      exact ⟨T, hT, List.Subset.trans (List.Subset.trans hTP hPW) (List.subset_cons_self _ _)⟩
    · exact ⟨e :: P, .cons hl hP hu, List.cons_subset_cons _ hPW⟩

/-! ### Reachability -/

/-- `G.Reaches u v` : some walk of `G` runs from `u` to `v`. Stated with a walk rather than a
path because walks are what arguments build — they concatenate and reverse with no side
condition — and a path is recovered on demand (`Graph.Reaches.exists_isPath`). -/
def Reaches (G : Graph α β) (u v : α) : Prop := ∃ W, G.IsWalk u W v

theorem Reaches.left_mem (h : G.Reaches u v) : u ∈ V(G) := h.choose_spec.left_mem

theorem Reaches.right_mem (h : G.Reaches u v) : v ∈ V(G) := h.choose_spec.right_mem

@[refl]
theorem Reaches.refl (hu : u ∈ V(G)) : G.Reaches u u := ⟨[], .nil hu⟩

theorem Reaches.symm (h : G.Reaches u v) : G.Reaches v u :=
  let ⟨W, hW⟩ := h; ⟨W.reverse, hW.reverse⟩

theorem Reaches.trans (h₁ : G.Reaches u v) (h₂ : G.Reaches v w) : G.Reaches u w :=
  let ⟨W₁, hW₁⟩ := h₁; let ⟨W₂, hW₂⟩ := h₂; ⟨W₁ ++ W₂, hW₁.append hW₂⟩

theorem reaches_comm : G.Reaches u v ↔ G.Reaches v u := ⟨Reaches.symm, Reaches.symm⟩

theorem Reaches.of_isLink (hl : G.IsLink e u v) : G.Reaches u v := ⟨[e], .single hl⟩

theorem Reaches.of_adj (h : G.Adj u v) : G.Reaches u v :=
  let ⟨_, hl⟩ := h; .of_isLink hl

/-- Whatever a walk reaches, a path reaches. -/
theorem Reaches.exists_isPath (h : G.Reaches u v) : ∃ P, G.IsPath u P v :=
  let ⟨_, hW⟩ := h; let ⟨P, hP, _⟩ := hW.contains_path; ⟨P, hP⟩

theorem Reaches.mono (hHG : H ≤ G) (h : H.Reaches u v) : G.Reaches u v :=
  let ⟨W, hW⟩ := h; ⟨W, hW.mono hHG⟩

/-! ### Connectedness -/

/-- A graph is connected when it has a vertex and every vertex reaches every other. The
nonemptiness clause is not bureaucracy: it is what makes the counting statements about trees
true as stated. -/
def Connected (G : Graph α β) : Prop :=
  V(G).Nonempty ∧ ∀ ⦃u⦄, u ∈ V(G) → ∀ ⦃v⦄, v ∈ V(G) → G.Reaches u v

theorem Connected.nonempty (h : G.Connected) : V(G).Nonempty := h.1

theorem Connected.reaches (h : G.Connected) (hu : u ∈ V(G)) (hv : v ∈ V(G)) : G.Reaches u v :=
  h.2 hu hv

/-- A graph is connected as soon as one vertex reaches all the others: reachability is
symmetric and transitive, so a common hub joins every pair. -/
theorem Connected.of_hub (hu : u ∈ V(G)) (h : ∀ v ∈ V(G), G.Reaches u v) : G.Connected :=
  ⟨⟨u, hu⟩, fun _ hx _ hy ↦ ((h _ hx).symm).trans (h _ hy)⟩

/-- In a connected graph any two vertices are joined by a path — the blueprint's imported
fact about finite graphs, with the finiteness it does not actually need dropped. -/
theorem Connected.exists_isPath (h : G.Connected) (hu : u ∈ V(G)) (hv : v ∈ V(G)) :
    ∃ P, G.IsPath u P v :=
  (h.reaches hu hv).exists_isPath

/-! ### Transferring walks and paths along an inclusion or a deletion

`IsWalk.anti` above pulls a walk down an inclusion. These are its companions, factored here
because both the cycle module and the two-connectivity module reached for them independently.
-/

theorem coveredVertices_mono_of_le (hHG : H ≤ G) : H.coveredVertices W ⊆ G.coveredVertices W :=
  fun _ ⟨f, hf, y, hy⟩ ↦ ⟨f, hf, y, hy.mono hHG⟩

theorem walkVertices_mono_of_le (hHG : H ≤ G) : H.walkVertices u W ⊆ G.walkVertices u W :=
  Set.insert_subset_insert (coveredVertices_mono_of_le hHG)

/-- A path of a graph whose edges all survive into a subgraph is a path of that subgraph —
the companion of `Graph.IsWalk.anti`, which it is otherwise identical to. Freshness comes
down the inclusion because the subgraph's edges touch no vertices the graph's do not. -/
theorem IsPath.anti (hHG : H ≤ G) (h : G.IsPath u W v) (hu : u ∈ V(H))
    (hE : ∀ e ∈ W, e ∈ E(H)) : H.IsPath u W v := by
  induction h with
  | nil => exact .nil hu
  | @cons u w v e W hl hW hfresh ih =>
    have he : e ∈ E(H) := hE e List.mem_cons_self
    have hl' : H.IsLink e u w := (hHG.isLink_iff he).2 hl
    exact .cons hl' (ih hl'.right_mem fun f hf ↦ hE f (List.mem_cons_of_mem _ hf))
      fun hmem ↦ hfresh (walkVertices_mono_of_le hHG hmem)

theorem mem_edgeSet_deleteEdges_iff {F : Set β} {f : β} :
    f ∈ E(G.deleteEdges F) ↔ f ∈ E(G) ∧ f ∉ F := by
  simp

/-- A walk that avoids the deleted names survives the deletion. -/
theorem IsWalk.deleteEdges {F : Set β} (h : G.IsWalk u W v) (hW : ∀ f ∈ W, f ∉ F) :
    (G.deleteEdges F).IsWalk u W v :=
  h.anti deleteEdges_le (by simpa using h.left_mem)
    fun f hf ↦ mem_edgeSet_deleteEdges_iff.2 ⟨h.edge_mem hf, hW f hf⟩

end Graph

end BundlePart373

section BundlePart374
/- Source: dev/planar_search/schoenflies_port/Schoenflies/Graph/Cycle.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/



/-!
# Cycles, acyclicity and bridges

This file sits directly on `Schoenflies/Graph/Walk.lean` and answers one question: which
edges of a multigraph lie on a cycle. Its main theorem is the blueprint's cycle criterion —
an edge lies on a cycle exactly when deleting it leaves its two ends joined — and a bridge is
read off it.

## A cycle is presented through one of its edges

`G.IsCycleThrough e u v D` is an edge `e` linking `u` to `v`, together with a **path** `D`
from `u` to `v` that does not use `e`. The closed walk is never assembled.

This is not a weakening. Every question the blueprint asks about a cycle is asked *at an
edge* — is this edge on a cycle, does deleting it disconnect its ends, is it a bridge, can it
be deleted from a spanning subgraph — so the edge is always available to present the cycle
through. And presenting it this way is what makes the definition short: the blueprint's
"connected subgraph in which every vertex has degree exactly two" would have to rule out, by
hand, every repetition that a closed walk can contain, whereas `Graph.IsPath` already forbids
them. The blueprint's own proof of the criterion runs in exactly this shape ("take a shortest
walk from `x` to `y` avoiding `e`; a shortest walk repeats no vertex, so it is a simple
path").

**Length two is included, and is why edges are names.** Two parallel edges — the same pair of
ends, two different names — are a cycle: one of them is `e`, the other is the one-edge path
`D`. The blueprint needs those ("two-vertex cycles do occur below, as boundaries of faces
created by overlays and by ears parallel to an existing edge"), and a walk that named
vertices could not tell the two apart.

## Loops

Mathlib's `Graph` allows an edge with both ends equal. **A loop is taken to be a cycle of
length one**, which is the usual convention and also what the blueprint's own definition
gives (a loop contributes two to the degree of its vertex, so the subgraph consisting of a
loop and its vertex is connected with every vertex of degree two). It comes out of the
definition here for free: `G.IsLink e x x` together with the empty path at `x`, which does
not use `e`, is a cycle through `e`. So `Graph.liesOnCycle_of_isLoopAt` needs no proof, no
graph is acyclic while carrying a loop, and no bridge is a loop. Nothing in this file
hypothesises looplessness.

## Deletion

Edge deletion is Mathlib's `Graph.deleteEdges`, not a new definition; `G.deleteEdges {e}` is
the graph with the single name `e` removed. What this file adds is the transfer interface —
a walk or a path survives a deletion exactly when it never took a deleted edge — which is the
whole content of a deletion argument, since which vertices an edge joins is not a question a
subgraph can answer differently. `Graph.IsWalk.anti` from `Walk.lean` is the engine;
`Graph.IsPath.anti` is proved here, since freshness has to be carried down too.

## Blueprint

* `Graph.liesOnCycle_iff_deleteEdges_reaches` — `lem:cycle-criterion`, "in a finite graph, an
  edge lies on a cycle if and only if deleting it does not disconnect its endpoints", both
  directions, with the finiteness the proof does not use dropped. The two halves are
  `Graph.LiesOnCycle.deleteEdges_reaches` and `Graph.LiesOnCycle.of_deleteEdges_reaches`.
* `Graph.IsSchoenfliesBridge`, `Graph.isBridge_iff_not_reaches` — the bridges of
  `lem:subdivision-ear-preserve` ("a 2-connected graph has no bridge. Indeed, if `uv` were a
  bridge, the two components of `G - uv` …"), stated as the separation of the two ends.
* `Graph.IsAcyclic`, `Graph.Connected.deleteEdges_singleton` — the acyclicity underneath
  `lem:three-leaf-tree`, and the minimal spanning subgraph of the H5 construction ("take a
  minimal connected subgraph `T_i` spanning the three terminals. It is a tree: an edge of a
  cycle could be deleted"), which is exactly the statement that deleting an edge on a cycle
  keeps the graph connected.
* `Graph.IsPath.chord_liesOnCycle`, `Graph.IsAcyclic.mem_of_isLink_of_mem_walkVertices` — the
  step of `lem:three-leaf-tree`'s proof that says "a second neighbor on the path would close
  a cycle"; the form the tree module's longest-path argument consumes.
-/

open Set

variable {α β : Type*} {G H : Graph α β} {u v w x y : α} {e f : β} {F : Set β} {W P D : List β}

namespace Graph

/-! ### Visited vertices along an inclusion

`Walk.lean` proves `walkVertices` monotone in the edge list. It is also monotone in the
graph, which is what pulling a path *down* into a subgraph needs: the freshness clause of a
path speaks about the subgraph's visited set, and that is the smaller one. -/

/-! ### Edge deletion

`Graph.deleteEdges` is Mathlib's. These are the four transfer lemmas every deletion argument
below reduces to. -/

/-- Deleting edges never removes a vertex, so a walk in the deletion is a walk. -/
theorem IsWalk.of_deleteEdges (h : (G.deleteEdges F).IsWalk u W v) : G.IsWalk u W v :=
  h.mono deleteEdges_le

/-- Conversely, a walk in the deletion could not have used a deleted name. -/
theorem IsWalk.notMem_of_deleteEdges (h : (G.deleteEdges F).IsWalk u W v) (hf : f ∈ W) :
    f ∉ F :=
  (mem_edgeSet_deleteEdges_iff.1 (h.edge_mem hf)).2

theorem IsPath.of_deleteEdges (h : (G.deleteEdges F).IsPath u W v) : G.IsPath u W v :=
  h.mono deleteEdges_le

theorem IsPath.deleteEdges (h : G.IsPath u W v) (hW : ∀ f ∈ W, f ∉ F) :
    (G.deleteEdges F).IsPath u W v :=
  h.anti deleteEdges_le (by simpa using h.left_mem)
    fun f hf ↦ mem_edgeSet_deleteEdges_iff.2 ⟨h.edge_mem hf, hW f hf⟩

theorem IsPath.notMem_of_deleteEdges (h : (G.deleteEdges F).IsPath u W v) (hf : f ∈ W) :
    f ∉ F :=
  h.isWalk.notMem_of_deleteEdges hf

theorem Reaches.of_deleteEdges (h : (G.deleteEdges F).Reaches u v) : G.Reaches u v :=
  h.mono deleteEdges_le

theorem IsWalk.reaches_deleteEdges (h : G.IsWalk u W v) (hW : ∀ f ∈ W, f ∉ F) :
    (G.deleteEdges F).Reaches u v :=
  ⟨W, h.deleteEdges hW⟩

/-! ### Cycles -/

/-- `G.IsCycleThrough e u v D` : the edge `e` links `u` to `v`, and `D` is a path from `u`
back to `v` that does not use `e`. The cycle is `e` together with `D`; it is presented
through `e` because that is the edge every question is asked about. -/
def IsCycleThrough (G : Graph α β) (e : β) (u v : α) (D : List β) : Prop :=
  G.IsLink e u v ∧ G.IsPath u D v ∧ e ∉ D

/-- `G.LiesOnCycle e` : the edge `e` lies on a cycle of `G`. -/
def LiesOnCycle (G : Graph α β) (e : β) : Prop := ∃ u v D, G.IsCycleThrough e u v D

theorem IsCycleThrough.isLink (h : G.IsCycleThrough e u v D) : G.IsLink e u v := h.1

theorem IsCycleThrough.isPath (h : G.IsCycleThrough e u v D) : G.IsPath u D v := h.2.1

theorem IsCycleThrough.notMem (h : G.IsCycleThrough e u v D) : e ∉ D := h.2.2

theorem IsCycleThrough.liesOnCycle (h : G.IsCycleThrough e u v D) : G.LiesOnCycle e :=
  ⟨u, v, D, h⟩

theorem liesOnCycle_iff : G.LiesOnCycle e ↔ ∃ u v D, G.IsCycleThrough e u v D := Iff.rfl

/-- An edge on a cycle is an edge of the graph. There is no converse hypothesis to carry
around: `Graph.IsLink` already forces it. -/
theorem LiesOnCycle.edge_mem (h : G.LiesOnCycle e) : e ∈ E(G) :=
  let ⟨_, _, _, hc⟩ := h; hc.isLink.edge_mem

/-- **A loop is a cycle of length one.** The path back is the empty one, which trivially
avoids the loop. -/
theorem liesOnCycle_of_isLoopAt (h : G.IsLoopAt e x) : G.LiesOnCycle e :=
  ⟨x, x, [], h, .nil h.left_mem, List.not_mem_nil⟩

/-- **Two parallel edges are a cycle**, on both of them. This is the length-two case, and the
reason a walk names its edges. -/
theorem liesOnCycle_of_parallel (h : G.IsLink e u v) (h' : G.IsLink f u v) (hef : e ≠ f) :
    G.LiesOnCycle e := by
  by_cases huv : u = v
  · subst huv
    exact liesOnCycle_of_isLoopAt h
  exact ⟨u, v, [f], h, .single h' huv, by simpa using hef⟩

/-- A cycle of a subgraph is a cycle of the graph. -/
theorem LiesOnCycle.mono (hHG : H ≤ G) (h : H.LiesOnCycle e) : G.LiesOnCycle e :=
  let ⟨u, v, D, hl, hP, hD⟩ := h
  ⟨u, v, D, hl.mono hHG, hP.mono hHG, hD⟩

/-! ### The cycle criterion

The blueprint's `lem:cycle-criterion`. Both directions are one step each, once the deletion
interface above is in place: forwards, the detour of the cycle is a walk that avoided `e`;
backwards, a path in the deletion cannot have used `e` because `e` is not there. -/

/-- **An edge on a cycle is not needed to join its ends**: the rest of the cycle still does.

The ends are given as an arbitrary pair `u, v` that `e` links, not as the pair the cycle was
presented with — an edge has only two ends, so the two presentations agree up to a swap, and
reachability is symmetric. -/
theorem LiesOnCycle.deleteEdges_reaches (hl : G.IsLink e u v) (h : G.LiesOnCycle e) :
    (G.deleteEdges {e}).Reaches u v := by
  obtain ⟨u', v', D, hl', hP, hD⟩ := h
  -- The detour avoids `e` by definition, so it is still there after `e` goes.
  have hR : (G.deleteEdges {e}).Reaches u' v' :=
    hP.isWalk.reaches_deleteEdges fun f hf hmem ↦ hD (Set.mem_singleton_iff.1 hmem ▸ hf)
  rcases hl.eq_and_eq_or_eq_and_eq hl' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [hR, hR.symm]

/-- **An edge whose deletion leaves its ends joined lies on a cycle.** The route that
survives is a walk of the deletion, hence contains a path of the deletion, and a path of the
deletion cannot have used the name that was deleted. -/
theorem LiesOnCycle.of_deleteEdges_reaches (hl : G.IsLink e u v)
    (h : (G.deleteEdges {e}).Reaches u v) : G.LiesOnCycle e := by
  obtain ⟨D, hD⟩ := h.exists_isPath
  exact ⟨u, v, D, hl, hD.of_deleteEdges, fun hmem ↦ hD.notMem_of_deleteEdges hmem rfl⟩

/-- **The cycle criterion**: an edge lies on a cycle if and only if deleting it does not
disconnect its endpoints. -/
theorem liesOnCycle_iff_deleteEdges_reaches (hl : G.IsLink e u v) :
    G.LiesOnCycle e ↔ (G.deleteEdges {e}).Reaches u v :=
  ⟨LiesOnCycle.deleteEdges_reaches hl, LiesOnCycle.of_deleteEdges_reaches hl⟩

/-- **A walk reroutes around an edge that lies on a cycle**: wherever it took `e`, it can go
the long way round instead. Proved by induction along the walk rather than by splicing the
detour into the edge list, so nothing has to be said about what the spliced list looks
like. -/
theorem IsWalk.reaches_deleteEdges_of_liesOnCycle (h : G.LiesOnCycle e) (hW : G.IsWalk u W v) :
    (G.deleteEdges {e}).Reaches u v := by
  induction hW with
  | nil hx => exact .refl (by simpa using hx)
  | @cons u w v f W hl _ ih =>
    refine Reaches.trans ?_ ih
    by_cases hfe : f = e
    · subst hfe
      exact h.deleteEdges_reaches hl
    · refine (IsWalk.single hl).reaches_deleteEdges fun g hg ↦ ?_
      obtain rfl : g = f := by simpa using hg
      simpa using hfe

/-- **Deleting an edge that lies on a cycle keeps the graph connected** — the blueprint's "it
is a tree: an edge of a cycle could be deleted", which is what makes a minimal connected
spanning subgraph acyclic. -/
theorem Connected.deleteEdges_singleton (hG : G.Connected) (h : G.LiesOnCycle e) :
    (G.deleteEdges {e}).Connected := by
  refine ⟨by simpa using hG.nonempty, fun u hu v hv ↦ ?_⟩
  rw [vertexSet_deleteEdges] at hu hv
  exact (hG.reaches hu hv).choose_spec.reaches_deleteEdges_of_liesOnCycle h

/-! ### Chords

An edge from the source of a path to a vertex the path already visits closes a cycle. This
is the shape in which acyclicity is used: it says a path cannot be extended backwards onto
itself. -/

/-- A chord of a path lies on a cycle: the piece of the path from its source to the far end
of the chord is a path avoiding the chord, so the chord closes it. -/
theorem IsPath.chord_liesOnCycle (hP : G.IsPath u P v) (hl : G.IsLink e u x) (hoff : e ∉ P)
    (hx : x ∈ G.walkVertices u P) : G.LiesOnCycle e := by
  obtain ⟨P₁, P₂, rfl, h₁, -, -⟩ := hP.split hx
  exact ⟨u, x, P₁, hl, h₁, fun hmem ↦ hoff (List.mem_append_left _ hmem)⟩

/-! ### Acyclicity -/

/-- `G.IsAcyclic` : no edge of `G` lies on a cycle. Stated over the edges of `G` because that
is how a tree consumes it — every edge is a bridge — while `Graph.IsAcyclic.not_liesOnCycle`
drops the membership hypothesis for the uses that do not have it to hand. -/
def IsAcyclic (G : Graph α β) : Prop := ∀ ⦃e⦄, e ∈ E(G) → ¬ G.LiesOnCycle e

/-- Acyclicity with no membership hypothesis: an edge on a cycle would be an edge. -/
theorem IsAcyclic.not_liesOnCycle (h : G.IsAcyclic) (e : β) : ¬ G.LiesOnCycle e :=
  fun hc ↦ h hc.edge_mem hc

theorem isAcyclic_iff : G.IsAcyclic ↔ ∀ e, ¬ G.LiesOnCycle e :=
  ⟨fun h e ↦ h.not_liesOnCycle e, fun h _ _ ↦ h _⟩

/-- **An acyclic graph has no loop.** No hypothesis is needed anywhere else in this layer
because of this: looplessness is a consequence of acyclicity, not a side condition on it. -/
theorem IsAcyclic.not_isLoopAt (h : G.IsAcyclic) (e : β) (x : α) : ¬ G.IsLoopAt e x :=
  fun hloop ↦ h.not_liesOnCycle e (liesOnCycle_of_isLoopAt hloop)

/-- **An acyclic graph has no parallel edges.** -/
theorem IsAcyclic.eq_of_isLink (h : G.IsAcyclic) (hl : G.IsLink e u v) (hl' : G.IsLink f u v) :
    e = f := by
  by_contra hef
  exact h.not_liesOnCycle e (liesOnCycle_of_parallel hl hl' hef)

/-- A subgraph of an acyclic graph is acyclic. -/
theorem IsAcyclic.anti (hHG : H ≤ G) (h : G.IsAcyclic) : H.IsAcyclic :=
  fun _ _ hc ↦ h.not_liesOnCycle _ (hc.mono hHG)

theorem IsAcyclic.deleteEdges (h : G.IsAcyclic) (F : Set β) : (G.deleteEdges F).IsAcyclic :=
  h.anti deleteEdges_le

/-- **In an acyclic graph, an edge at the source of a path whose far end the path visits is
one of the path's own edges.** This is the blueprint's "a second neighbor on the path would
close a cycle" — the step that makes the end of a longest path a leaf, which is what the tree
module runs on. -/
theorem IsAcyclic.mem_of_isLink_of_mem_walkVertices (hac : G.IsAcyclic) (hP : G.IsPath u P v)
    (hl : G.IsLink e u x) (hx : x ∈ G.walkVertices u P) : e ∈ P := by
  by_contra hoff
  exact hac.not_liesOnCycle e (hP.chord_liesOnCycle hl hoff hx)

/-! ### Bridges -/

/-- `G.IsSchoenfliesBridge e` : an edge of `G` that lies on no cycle. Equivalently — and this is the
form every use wants — an edge whose deletion separates its two ends
(`Graph.isBridge_iff_not_reaches`). -/
def IsSchoenfliesBridge (G : Graph α β) (e : β) : Prop := e ∈ E(G) ∧ ¬ G.LiesOnCycle e

theorem IsSchoenfliesBridge.edge_mem (h : G.IsSchoenfliesBridge e) : e ∈ E(G) := h.1

theorem IsSchoenfliesBridge.not_liesOnCycle (h : G.IsSchoenfliesBridge e) : ¬ G.LiesOnCycle e := h.2

/-- **Deleting a bridge separates its ends.** -/
theorem IsSchoenfliesBridge.not_reaches (h : G.IsSchoenfliesBridge e) (hl : G.IsLink e u v) :
    ¬ (G.deleteEdges {e}).Reaches u v :=
  fun hR ↦ h.not_liesOnCycle (LiesOnCycle.of_deleteEdges_reaches hl hR)

/-- **An edge whose deletion separates its ends is a bridge.** -/
theorem isBridge_of_not_reaches (hl : G.IsLink e u v)
    (h : ¬ (G.deleteEdges {e}).Reaches u v) : G.IsSchoenfliesBridge e :=
  ⟨hl.edge_mem, fun hc ↦ h (hc.deleteEdges_reaches hl)⟩

/-- **A bridge is exactly an edge whose deletion separates its ends** — the cycle criterion,
negated. -/
theorem isBridge_iff_not_reaches (hl : G.IsLink e u v) :
    G.IsSchoenfliesBridge e ↔ ¬ (G.deleteEdges {e}).Reaches u v :=
  ⟨fun h ↦ h.not_reaches hl, isBridge_of_not_reaches hl⟩

/-- A bridge is never a loop: a loop is a cycle. -/
theorem IsSchoenfliesBridge.not_isLoopAt (h : G.IsSchoenfliesBridge e) (x : α) : ¬ G.IsLoopAt e x :=
  fun hloop ↦ h.not_liesOnCycle (liesOnCycle_of_isLoopAt hloop)

/-- **A graph is acyclic exactly when every one of its edges is a bridge.** This is the form
the tree module wants acyclicity in: "it is a tree — an edge of a cycle could be deleted"
reads backwards as "no edge can be deleted without separating its ends". -/
theorem isAcyclic_iff_forall_isBridge : G.IsAcyclic ↔ ∀ e ∈ E(G), G.IsSchoenfliesBridge e :=
  ⟨fun h _ he ↦ ⟨he, h he⟩, fun h _ he ↦ (h _ he).not_liesOnCycle⟩

theorem IsAcyclic.isBridge (h : G.IsAcyclic) (he : e ∈ E(G)) : G.IsSchoenfliesBridge e := ⟨he, h he⟩

end Graph

end BundlePart374

section BundlePart375
/- Source: dev/planar_search/schoenflies_port/Schoenflies/PolyPath.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/



/-!
# Polygonal paths

A polygonal path is carried by a list of vertices; its `poly` carrier is the union of the
segments joining consecutive entries. This is the combinatorial representation the whole
of Part I works with — by the blueprint's polygonal overlay convention only finite
polygonal objects are ever overlaid, so vertex lists, not parametrizations, are the
primitive.

## Blueprint

* `poly` — the carrier of a polygonal path.
* `exists_poly_of_isPreconnected` — Lemma 1.1 (polygonal connectedness), less the passage
  to a *simple* arc, which needs the finite-graph machinery and is proved with Lemma 1.2.
-/

open Metric Set

namespace Schoenflies

variable {Ω : Set Plane} {x y z : Plane}

/-! ### Segments -/

theorem isCompact_segment (x y : Plane) : IsCompact (segment ℝ x y) := by
  rw [segment_eq_image' ℝ x y]
  exact isCompact_Icc.image (by fun_prop)

/-! ### The carrier of a vertex list -/

/-- The carrier of a polygonal path: the union of the segments joining consecutive vertices.
A single vertex carries itself, so that a path may be constant. -/
def poly : List Plane → Set Plane
  | [] => ∅
  | [v] => {v}
  | u :: v :: rest => segment ℝ u v ∪ poly (v :: rest)

@[simp] theorem poly_nil : poly [] = ∅ := rfl

@[simp] theorem poly_singleton (v : Plane) : poly [v] = {v} := rfl

@[simp] theorem poly_cons_cons (u v : Plane) (rest : List Plane) :
    poly (u :: v :: rest) = segment ℝ u v ∪ poly (v :: rest) := rfl

theorem poly_nonempty : ∀ {vs : List Plane}, vs ≠ [] → (poly vs).Nonempty
  | [], h => absurd rfl h
  | [v], _ => ⟨v, rfl⟩
  | _ :: v :: _, _ => ⟨v, Or.inl (right_mem_segment ℝ _ _)⟩

theorem isCompact_poly : ∀ vs : List Plane, IsCompact (poly vs)
  | [] => by simp
  | [v] => by simp
  | u :: v :: rest => by
    rw [poly_cons_cons]
    exact (isCompact_segment u v).union (isCompact_poly (v :: rest))

/-- Every vertex lies on the carrier. -/
theorem mem_poly_of_mem : ∀ {vs : List Plane} {v : Plane}, v ∈ vs → v ∈ poly vs
  | [], _, h => absurd h (by simp)
  | [_], _, h => by simpa using h
  | u :: w :: rest, v, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact Or.inl (left_mem_segment ℝ _ _)
    · exact Or.inr (mem_poly_of_mem h)

theorem head_mem_poly {vs : List Plane} (h : vs ≠ []) : vs.head h ∈ poly vs :=
  mem_poly_of_mem (List.head_mem h)

theorem getLast_mem_poly {vs : List Plane} (h : vs ≠ []) : vs.getLast h ∈ poly vs :=
  mem_poly_of_mem (List.getLast_mem h)

/-- The carrier of a nonempty vertex list is connected: consecutive segments share a vertex. -/
theorem isConnected_poly : ∀ {vs : List Plane}, vs ≠ [] → IsConnected (poly vs)
  | [], h => absurd rfl h
  | [v], _ => by simpa using isConnected_singleton (x := v)
  | u :: v :: rest, _ => by
    rw [poly_cons_cons]
    refine IsConnected.union ⟨v, right_mem_segment ℝ u v, head_mem_poly (by simp)⟩
      ((convex_segment u v).isConnected ⟨u, left_mem_segment ℝ u v⟩)
      (isConnected_poly (List.cons_ne_nil v rest))

/-- Appending one vertex extends the carrier by one segment. -/
theorem poly_concat : ∀ {vs : List Plane} (h : vs ≠ []) (z : Plane),
    poly (vs ++ [z]) = poly vs ∪ segment ℝ (vs.getLast h) z
  | [], h, _ => absurd rfl h
  | [v], _, z => by
    simp only [List.singleton_append, poly_cons_cons, poly_singleton, List.getLast_singleton]
    rw [union_singleton, insert_eq_self.2 (right_mem_segment ℝ v z), singleton_union,
      insert_eq_self.2 (left_mem_segment ℝ v z)]
  | u :: v :: rest, _, z => by
    simp only [List.cons_append, poly_cons_cons]
    rw [← List.cons_append, poly_concat (List.cons_ne_nil v rest) z,
      List.getLast_cons (List.cons_ne_nil v rest)]
    exact (union_assoc _ _ _).symm

/-! ### Polygonal connectedness -/

/-- Lemma 1.1 (polygonal connectedness), existence half. Any two points of a region are
joined in it by a polygonal path.

The blueprint goes on to make the path *simple*, by subdividing at self-intersections and
taking a simple path in the resulting finite graph; that half is deferred to the graph
module, where the subdivision procedure is available. -/
theorem exists_poly_of_isPreconnected (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hx : x ∈ Ω) (hy : y ∈ Ω) :
    ∃ vs : List Plane, ∃ h : vs ≠ [], poly vs ⊆ Ω ∧ vs.head h = x ∧ vs.getLast h = y := by
  -- `R` is the set of points reachable from `x` by a polygonal path inside `Ω`.
  set R : Set Plane :=
    {w ∈ Ω | ∃ vs : List Plane, ∃ h : vs ≠ [], poly vs ⊆ Ω ∧ vs.head h = x ∧ vs.getLast h = w}
    with hR
  -- Extending a path by a segment inside a convex subset of `Ω` keeps it inside `Ω`. Applied
  -- to a ball this makes `R` open, and applied in the other direction makes `Ω \ R` open.
  have key : ∀ C : Set Plane, Convex ℝ C → C ⊆ Ω → ∀ w ∈ C, ∀ z ∈ C,
      (∃ vs : List Plane, ∃ h : vs ≠ [], poly vs ⊆ Ω ∧ vs.head h = x ∧ vs.getLast h = w) →
      ∃ vs : List Plane, ∃ h : vs ≠ [], poly vs ⊆ Ω ∧ vs.head h = x ∧ vs.getLast h = z := by
    rintro C hC hCΩ w hw z hz ⟨vs, hne, hsub, hhead, hlast⟩
    refine ⟨vs ++ [z], by simp, ?_, ?_, ?_⟩
    · rw [poly_concat hne z, hlast]
      exact union_subset hsub ((hC.segment_subset hw hz).trans hCΩ)
    · rw [List.head_append_of_ne_nil hne]; exact hhead
    · simp
  have hRopen : IsOpen R := by
    rw [isOpen_iff_forall_mem_open]
    rintro w ⟨hw, hpath⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hΩ w hw
    exact ⟨ball w r, fun z hz =>
      ⟨hball hz, key _ (convex_ball w r) hball w (mem_ball_self hr) z hz hpath⟩,
      isOpen_ball, mem_ball_self hr⟩
  have hRcompl : IsOpen (Ω \ R) := by
    rw [isOpen_iff_forall_mem_open]
    rintro w ⟨hw, hwR⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hΩ w hw
    refine ⟨ball w r, fun z hz => ⟨hball hz, fun hzR => ?_⟩, isOpen_ball, mem_ball_self hr⟩
    -- A path to `z` runs back to `w` through the same ball, so `w ∈ R` after all.
    exact hwR ⟨hw, key _ (convex_ball w r) hball z hz w (mem_ball_self hr) hzR.2⟩
  -- `R` is nonempty, open and closed in the preconnected `Ω`, so `R = Ω`.
  have hxR : x ∈ R := ⟨hx, [x], by simp, by simpa using hx, rfl, rfl⟩
  have : y ∈ R := by
    by_contra hyR
    obtain ⟨w, _, hw⟩ := hconn R (Ω \ R) hRopen hRcompl
      (fun w hw => (em (w ∈ R)).imp id fun h => ⟨hw, h⟩) ⟨x, hx, hxR⟩ ⟨y, hy, hy, hyR⟩
    exact hw.2.2 hw.1
  exact this.2

/-- Concatenating two vertex lists that agree at the join concatenates their carriers. The
hypothesis is what makes this true: without it `poly [a] ∪ poly [b] = {a, b}` misses the segment
that `poly [a, b]` carries. -/
theorem poly_append : ∀ {vs : List Plane} (h : vs ≠ []) (w : Plane) (rest : List Plane),
    vs.getLast h = w → poly (vs ++ w :: rest) = poly vs ∪ poly (w :: rest)
  | [], h, _, _, _ => absurd rfl h
  | [v], _, w, rest, hvw => by
    simp only [List.getLast_singleton] at hvw
    subst hvw
    simp [segment_same]
  | u :: v :: tl, _, w, rest, hvw => by
    have h' : (v :: tl).getLast (List.cons_ne_nil v tl) = w := by
      rw [← List.getLast_cons (a := u) (List.cons_ne_nil v tl)]; exact hvw
    simp only [List.cons_append, poly_cons_cons]
    rw [← List.cons_append, poly_append (List.cons_ne_nil v tl) w rest h']
    exact (union_assoc _ _ _).symm

end Schoenflies

end BundlePart375

section BundlePart376
/- Source: dev/planar_search/schoenflies_port/Schoenflies/Polygonal.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/



/-!
# Polygonal sets, and segments as arcs

`IsPolygonal` is the blueprint's set-level predicate: a finite union of line segments, which
here is exactly the carrier of some vertex list.

The theorem the plane-graph layer needs from this module is `isArcBetween_segment`: a
*nondegenerate* segment is an arc between its endpoints. It is what makes the drawing
condition free for a polygonal plane graph — an edge's arc obligation is discharged by the
segment itself, and the distinctness of its ends is already part of well-formedness.

## Blueprint

* `IsPolygonal` — §1, "an arc or curve is polygonal if it is a finite union of line segments".
* `isArcBetween_segment` — a nondegenerate segment is an arc between its endpoints.
-/

open Metric Set

namespace Schoenflies

/-- A set is polygonal when it is the carrier of a finite vertex list, that is, a finite union
of line segments. -/
def IsPolygonal (A : Set Plane) : Prop := ∃ vs : List Plane, A = poly vs

theorem IsPolygonal.isCompact {A : Set Plane} (h : IsPolygonal A) : IsCompact A := by
  obtain ⟨vs, rfl⟩ := h
  exact isCompact_poly vs

@[simp] theorem poly_pair (a b : Plane) : poly [a, b] = segment ℝ a b := by
  rw [poly_cons_cons, poly_singleton]
  exact union_eq_self_of_subset_right (singleton_subset_iff.2 (right_mem_segment ℝ a b))

theorem isPolygonal_segment (a b : Plane) : IsPolygonal (segment ℝ a b) :=
  ⟨[a, b], (poly_pair a b).symm⟩

/-- `lineMap a b` is injective on the unit interval exactly when the segment is
nondegenerate: two parameters differ by a multiple of `b - a`. Exposed separately because the
plane-graph drawing condition asks for the parametrization, not just its image. -/
theorem injOn_lineMap {a b : Plane} (hab : a ≠ b) :
    Set.InjOn (AffineMap.lineMap a b : ℝ → Plane) I := by
  intro s _ t _ hst
  have hba : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  have key : (s - t) • (b - a) = 0 := by
    simp only [AffineMap.lineMap_apply_module] at hst
    linear_combination (norm := module) hst
  rcases smul_eq_zero.1 key with h | h
  · linarith
  · exact absurd h hba

/-- A nondegenerate segment is an arc between its endpoints, parametrized by
`AffineMap.lineMap a b`. -/
theorem isArcBetween_segment {a b : Plane} (hab : a ≠ b) :
    IsArcBetween (segment ℝ a b) a b := by
  refine ⟨AffineMap.lineMap a b, AffineMap.lineMap_continuous.continuousOn, ?_, ?_, ?_, ?_⟩
  · exact injOn_lineMap hab
  · rw [segment_eq_image_lineMap]
  · simp
  · simp

theorem isArc_segment {a b : Plane} (hab : a ≠ b) : IsArc (segment ℝ a b) :=
  (isArcBetween_segment hab).isArc

/-- **A polygonal set is carried by a vertex list running from any of its points to any other.**
The list is written with its two ends displayed, so no `List.head`/`List.getLast` obligations
appear. -/
theorem exists_poly_anchored : ∀ (vs : List Plane), vs ≠ [] → ∀ z w : Plane,
    z ∈ poly vs → w ∈ poly vs → ∃ mid : List Plane, poly (z :: (mid ++ [w])) = poly vs := by
  intro vs
  induction vs with
  | nil => exact fun h => absurd rfl h
  | cons u tl ih =>
    rcases tl with _ | ⟨v, rest⟩
    · -- A one-point carrier: both ends are that point.
      intro _ z w hz hw
      rw [poly_singleton, Set.mem_singleton_iff] at hz hw
      subst hz; subst hw
      exact ⟨[], by simp [segment_same]⟩
    · intro _ z w hz hw
      have hne : (v :: rest) ≠ [] := List.cons_ne_nil v rest
      have hv : v ∈ poly (v :: rest) := mem_poly_of_mem (List.mem_cons_self ..)
      rw [poly_cons_cons] at hz hw
      -- `segment z u ⊆ segment u v` for `z` on the first edge, and likewise for `w`.
      have hsub : ∀ p ∈ segment ℝ u v, segment ℝ p u ⊆ segment ℝ u v := fun p hp =>
        (convex_segment u v).segment_subset hp (left_mem_segment ℝ u v)
      have hsub' : ∀ p ∈ segment ℝ u v, segment ℝ u p ⊆ segment ℝ u v := fun p hp =>
        (convex_segment u v).segment_subset (left_mem_segment ℝ u v) hp
      rcases hz with hz | hz
      · rcases hw with hw | hw
        · -- Both ends on the first edge: run out along the rest of the list and back.
          obtain ⟨Z, hZ⟩ := ih hne v v hv hv
          refine ⟨u :: v :: (Z ++ [v, v, u]), ?_⟩
          have hlast : (z :: u :: (v :: (Z ++ [v]))).getLast (by simp) = v := by
            simp
          have hsplit : z :: ((u :: v :: (Z ++ [v, v, u])) ++ [w])
              = (z :: u :: (v :: (Z ++ [v]))) ++ (v :: u :: [w]) := by
            simp
          have h1 : poly (z :: u :: (v :: (Z ++ [v])))
              = segment ℝ z u ∪ (segment ℝ u v ∪ poly (v :: rest)) := by
            rw [poly_cons_cons, poly_cons_cons, hZ]
          have h2 : poly (v :: u :: [w]) = segment ℝ u v ∪ segment ℝ u w := by
            rw [poly_cons_cons, poly_pair, segment_symm ℝ v u]
          have hd1 : segment ℝ z u ⊆ segment ℝ u v ∪ poly (v :: rest) :=
            (hsub z hz).trans Set.subset_union_left
          have hd2 : segment ℝ u v ∪ segment ℝ u w ⊆ segment ℝ u v ∪ poly (v :: rest) :=
            Set.union_subset Set.subset_union_left ((hsub' w hw).trans Set.subset_union_left)
          rw [hsplit, poly_append (by simp) v (u :: [w]) hlast, h1, h2, poly_cons_cons,
            Set.union_eq_self_of_subset_left hd1, Set.union_eq_self_of_subset_right hd2]
        · -- The far end is on the rest: append its list to the first edge.
          obtain ⟨Y, hY⟩ := ih hne v w hv hw
          refine ⟨u :: v :: Y, ?_⟩
          have hsplit : z :: ((u :: v :: Y) ++ [w]) = z :: u :: (v :: (Y ++ [w])) := by simp
          have hd1 : segment ℝ z u ⊆ segment ℝ u v ∪ poly (v :: rest) :=
            (hsub z hz).trans Set.subset_union_left
          rw [hsplit, poly_cons_cons, poly_cons_cons, hY, poly_cons_cons,
            Set.union_eq_self_of_subset_left hd1]
      · rcases hw with hw | hw
        · -- The near end is on the rest: run to `v`, then out along the first edge.
          obtain ⟨X, hX⟩ := ih hne z v hz hv
          refine ⟨X ++ [v, v, u], ?_⟩
          have hlast : (z :: (X ++ [v])).getLast (by simp) = v := by simp
          have hsplit : z :: ((X ++ [v, v, u]) ++ [w]) = (z :: (X ++ [v])) ++ (v :: u :: [w]) := by
            simp
          have h2 : poly (v :: u :: [w]) = segment ℝ u v ∪ segment ℝ u w := by
            rw [poly_cons_cons, poly_pair, segment_symm ℝ v u]
          rw [hsplit, poly_append (by simp) v (u :: [w]) hlast, hX, h2, poly_cons_cons,
            Set.union_eq_self_of_subset_right (hsub' w hw), Set.union_comm]
        · -- Both ends on the rest: run from one to `v`, out and back along the first edge, on.
          obtain ⟨X, hX⟩ := ih hne z v hz hv
          obtain ⟨Y, hY⟩ := ih hne v w hv hw
          refine ⟨X ++ [v, v, u] ++ (v :: Y), ?_⟩
          have hlast : (z :: (X ++ [v])).getLast (by simp) = v := by simp
          have hsplit : z :: ((X ++ [v, v, u] ++ (v :: Y)) ++ [w])
              = (z :: (X ++ [v])) ++ (v :: u :: (v :: (Y ++ [w]))) := by simp
          have h2 : poly (v :: u :: (v :: (Y ++ [w])))
              = segment ℝ u v ∪ (segment ℝ u v ∪ poly (v :: rest)) := by
            rw [poly_cons_cons, poly_cons_cons, hY, segment_symm ℝ v u]
          have hd1 : segment ℝ u v ⊆ segment ℝ u v ∪ poly (v :: rest) := Set.subset_union_left
          have hd2 : poly (v :: rest) ⊆ segment ℝ u v ∪ poly (v :: rest) := Set.subset_union_right
          rw [hsplit, poly_append (by simp) v (u :: (v :: (Y ++ [w]))) hlast, hX, h2,
            poly_cons_cons, Set.union_eq_self_of_subset_left hd1,
            Set.union_eq_self_of_subset_left hd2]

/-- **Two polygonal sets that meet have a polygonal union.** Anchor both lists at a common
point and concatenate. -/
theorem IsPolygonal.union {A B : Set Plane} (hA : IsPolygonal A) (hB : IsPolygonal B)
    (hmeet : (A ∩ B).Nonempty) : IsPolygonal (A ∪ B) := by
  obtain ⟨vs, rfl⟩ := hA
  obtain ⟨ws, rfl⟩ := hB
  obtain ⟨z, hzA, hzB⟩ := hmeet
  have hvs : vs ≠ [] := by rintro rfl; exact hzA
  have hws : ws ≠ [] := by rintro rfl; exact hzB
  obtain ⟨X, hX⟩ := exists_poly_anchored vs hvs z z hzA hzA
  obtain ⟨Y, hY⟩ := exists_poly_anchored ws hws z z hzB hzB
  refine ⟨(z :: (X ++ [z])) ++ (z :: (Y ++ [z])), ?_⟩
  have hlast : (z :: (X ++ [z])).getLast (by simp) = z := by simp
  rw [poly_append (by simp) z (Y ++ [z]) hlast, hX, hY]

end Schoenflies

end BundlePart376

section BundlePart377
/- Source: dev/planar_search/schoenflies_port/Schoenflies/Graph/CycleJordan.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/





/-!
# The realisation of a cycle is a Jordan curve

A cycle of a plane graph arrives as `Schoenflies/Graph/Cycle.lean` presents it: an edge, and a
path between that edge's two ends which does not use it. Its realisation is the set of points
the arcs of those edges occupy, and the claim is that this set is a Jordan curve.

## The argument is set-level; no parametrisation of a walk is built

The obvious approach — a `walkArc` definition folding `Schoenflies.concatenate` along the edge
list — is the wrong shape twice over. The empty-list base case is a *constant* map, which is
not an arc, so the fold cannot be shown injective at the last step; and threading a
parametrisation through the induction buys nothing, since every consumer wants the point set.

Instead **the existence of the arc is what the induction carries**, in
`Schoenflies.IsArcBetween`. The arcs are chosen inside the induction and the concatenation of
them is chosen by the gluing theorem; no parametrisation is ever named.

## Where the geometry enters

Exactly once, in `Graph.IsDrawing.first_edge_meets_rest`: a common point of the first edge's
arc and the rest of the path is a vertex incident with both edges
(`Graph.IsDrawing.arcs_meet_at_vertex`), hence one of the two ends of the first edge, and the
path's own freshness clause — the vertex a step departs from is not one the rest visits —
forbids it being the source. Taking the same edge again is refused by the *same* clause, so a
separate "the edges of a path are distinct" lemma is not needed.

## Loops

Nothing here hypothesises looplessness, and nothing needs to: `Graph.IsDrawing.ne_of_isLink`
derives it. An edge with equal ends would be drawn by an arc whose parametrisation takes the
same value at `0` and at `1`, which its injectivity forbids. That is what rules out the
degenerate cycle `Graph.liesOnCycle_of_isLoopAt` — a loop with an empty detour — whose
realisation is a single arc and not a Jordan curve.

## Blueprint

* `Graph.edgesCover` — what a *list* of edges occupies. `Graph.pointSet` is the vertices
  together with this, taken over all the edges of the graph.
* `Graph.IsDrawing.path_isArcBetween` — the realisation of a path is an arc between its two
  ends.
* `Graph.IsDrawing.cycle_isJordanCurve` — §"Plane graphs and the utility graph": "in a plane
  graph the realization of a cycle is a Jordan curve: its edges are simple arcs with pairwise
  disjoint interiors, and consecutive edges meet exactly at their shared vertices, so the edge
  arcs concatenate injectively into a simple closed curve".
* `Graph.IsDrawing.cycle_inter` — the meeting condition in full: the detour and the edge meet
  in exactly the edge's two ends. `Schoenflies.IsJordanCurve.of_two_arcs` consumes only one
  inclusion of it, but the equality is what the blueprint asserts.
-/

open Set Schoenflies unitInterval
open scoped Graph

namespace Graph

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}
variable {e f : β} {u v w z : Plane} {W D : List β}

/-! ### What a list of edges occupies -/

/-- The point set of a list of edges: the union of their edge arcs. A walk is a list of edges,
so this is what a walk of a plane graph draws. -/
def edgesCover (drawing : β → ℝ → Plane) (W : List β) : Set Plane :=
  ⋃ e ∈ W, edgeArc drawing e

theorem mem_edgesCover_iff :
    z ∈ edgesCover drawing W ↔ ∃ e ∈ W, z ∈ edgeArc drawing e := by
  simp [edgesCover]

theorem mem_edgesCover (he : e ∈ W) (hz : z ∈ edgeArc drawing e) : z ∈ edgesCover drawing W :=
  mem_edgesCover_iff.2 ⟨e, he, hz⟩

@[simp]
theorem edgesCover_nil : edgesCover drawing ([] : List β) = ∅ := by
  simp [edgesCover]

@[simp]
theorem edgesCover_cons :
    edgesCover drawing (e :: W) = edgeArc drawing e ∪ edgesCover drawing W := by
  ext z
  simp [edgesCover]

theorem edgesCover_mono (h : W ⊆ D) : edgesCover drawing W ⊆ edgesCover drawing D :=
  fun _ hz ↦ let ⟨_, he, hze⟩ := mem_edgesCover_iff.1 hz; mem_edgesCover (h he) hze

/-- A list of edges of the graph occupies part of what the graph occupies. -/
theorem edgesCover_subset_pointSet (hW : ∀ e ∈ W, e ∈ E(G)) :
    edgesCover drawing W ⊆ pointSet G drawing := by
  intro z hz
  obtain ⟨e, he, hze⟩ := mem_edgesCover_iff.1 hz
  exact edgeArc_subset_pointSet (hW e he) hze

/-! ### A plane graph has no loops

This is not a hypothesis anywhere in this file; it is a consequence of the drawing condition,
and it is what makes the degenerate cycle — a loop, with the empty path back — impossible. -/

/-- **An edge of a plane graph has two distinct ends.** An edge with equal ends would be drawn
by an arc whose parametrisation returns to its start, which its injectivity forbids. -/
theorem IsDrawing.ne_of_isLink (h : IsDrawing G drawing) (hl : G.IsLink e u v) : u ≠ v := by
  rintro rfl
  obtain ⟨g, -, hinj, -, hg0, hg1⟩ := h.edge_isArcBetween hl
  have : (0 : ℝ) = 1 := hinj zero_mem_I one_mem_I (hg0.trans hg1.symm)
  norm_num at this

theorem IsDrawing.not_isLoopAt (h : IsDrawing G drawing) (e : β) (u : Plane) :
    ¬ G.IsLoopAt e u :=
  fun hloop ↦ h.ne_of_isLink hloop rfl

/-! ### The realisation of a path

The induction carries the *existence* of an arc, not a parametrisation. Its one geometric
step is `Graph.IsDrawing.first_edge_meets_rest`. -/

/-- **The first edge's arc meets the rest of the path only at the waypoint.** Two cases, and
neither is geometric beyond the workhorse `Graph.IsDrawing.arcs_meet_at_vertex`: if the rest
takes the same edge again, the source is one of its ends; if it takes a different one, a
common point is a vertex incident with both, so it is the source or the waypoint. Either way a
point that was the source would put the source among the vertices the rest visits, which is
what the path's freshness clause forbids. -/
theorem IsDrawing.first_edge_meets_rest (h : IsDrawing G drawing) (hl : G.IsLink e u w)
    (hW : ∀ f ∈ W, f ∈ E(G)) (hfresh : u ∉ G.walkVertices w W)
    (hze : z ∈ edgeArc drawing e) (hzW : z ∈ edgesCover drawing W) : z = w := by
  obtain ⟨f, hf, hzf⟩ := mem_edgesCover_iff.1 hzW
  -- Taking the same edge again would put the source among the vertices the rest visits.
  have hef : e ≠ f := by
    rintro rfl
    exact hfresh (mem_walkVertices_of_mem_covered ⟨e, hf, hl.inc_left⟩)
  obtain ⟨-, hinc, hincf⟩ := h.edge_inter hl.edge_mem (hW f hf) hef hze hzf
  rcases hinc.eq_or_eq_of_isLink hl with rfl | rfl
  · exact absurd (mem_walkVertices_of_mem_covered ⟨f, hf, hincf⟩) hfresh
  · rfl

/-- **The realisation of a path is an arc between its two ends.** The path must go somewhere:
the empty path draws the empty set, which is not an arc.

The induction is on the path, at the source end, and what it carries is the existence of the
arc. At each step the first edge's arc and the rest's arc meet only at the waypoint
(`Graph.IsDrawing.first_edge_meets_rest`), so `Schoenflies.IsArcBetween.concatenate` glues
them. -/
theorem IsDrawing.path_isArcBetween (h : IsDrawing G drawing) (hP : G.IsPath u W v)
    (hne : W ≠ []) : IsArcBetween (edgesCover drawing W) u v := by
  induction hP with
  | nil => exact absurd rfl hne
  | @cons u w v e W hl hP hfresh ih =>
    rcases eq_or_ne W [] with rfl | hW
    · -- A single edge: the rest contributes nothing, and the path arrives where the edge does.
      obtain rfl : w = v := hP.isWalk.eq_of_nil
      simpa using h.edge_isArcBetween hl
    · refine edgesCover_cons ▸ (h.edge_isArcBetween hl).concatenate (ih hW) ?_
      exact fun z hze hzW ↦
        h.first_edge_meets_rest hl (fun f hf ↦ hP.edge_mem hf) hfresh hze hzW

/-! ### The realisation of a cycle -/

/-- The detour of a cycle is a path with at least one edge — an empty detour would return to
where it set out, and the edge it is a detour for has two distinct ends — so it is drawn by an
arc between those ends. -/
theorem IsDrawing.detour_isArcBetween (h : IsDrawing G drawing) (hc : G.IsCycleThrough e u v D) :
    IsArcBetween (edgesCover drawing D) u v := by
  refine h.path_isArcBetween hc.isPath fun hD ↦ ?_
  exact h.ne_of_isLink hc.isLink (hD ▸ hc.isPath.isWalk).eq_of_nil

/-- **The detour of a cycle meets the edge only at the edge's two ends.** A common point lies
on the edge and on some edge of the detour, which the detour does not contain, so it is a
vertex incident with the edge — and an edge has only its two ends. -/
theorem IsDrawing.detour_meets_edge (h : IsDrawing G drawing) (hc : G.IsCycleThrough e u v D)
    (hzD : z ∈ edgesCover drawing D) (hze : z ∈ edgeArc drawing e) : z = u ∨ z = v := by
  obtain ⟨f, hf, hzf⟩ := mem_edgesCover_iff.1 hzD
  have hef : e ≠ f := fun hEq ↦ hc.notMem (hEq ▸ hf)
  obtain ⟨-, hinc, -⟩ :=
    h.edge_inter hc.isLink.edge_mem (hc.isPath.edge_mem hf) hef hze hzf
  exact hinc.eq_or_eq_of_isLink hc.isLink

/-- **The detour and the edge meet in exactly the edge's two ends.** The inclusion
`Graph.IsDrawing.detour_meets_edge` is what `Schoenflies.IsJordanCurve.of_two_arcs` consumes;
the reverse one is free, since both ends are endpoints of both arcs. -/
theorem IsDrawing.cycle_inter (h : IsDrawing G drawing) (hc : G.IsCycleThrough e u v D) :
    edgesCover drawing D ∩ edgeArc drawing e = {u, v} := by
  have hD := h.detour_isArcBetween hc
  have hE := h.edge_isArcBetween hc.isLink
  refine Set.eq_of_subset_of_subset (fun z hz ↦ h.detour_meets_edge hc hz.1 hz.2) ?_
  rintro z (rfl | rfl)
  exacts [⟨hD.left_mem, hE.left_mem⟩, ⟨hD.right_mem, hE.right_mem⟩]

/-- **The realisation of a cycle is a Jordan curve.** The detour is drawn by an arc from one
end of the edge to the other, the edge is drawn by an arc back, and the two meet only at those
two ends, so `Schoenflies.IsJordanCurve.of_two_arcs` closes the loop. -/
theorem IsDrawing.cycle_isJordanCurve (h : IsDrawing G drawing)
    (hc : G.IsCycleThrough e u v D) : IsJordanCurve (edgesCover drawing (e :: D)) := by
  have hJ : IsJordanCurve (edgesCover drawing D ∪ edgeArc drawing e) :=
    IsJordanCurve.of_two_arcs (h.detour_isArcBetween hc)
      (h.edge_isArcBetween hc.isLink).reverse fun z hzD hze ↦ h.detour_meets_edge hc hzD hze
  rw [edgesCover_cons, Set.union_comm]
  exact hJ

/-- The source of a nonempty walk lies on what the walk draws. -/
theorem IsWalk.left_mem_edgesCover {u v : Plane} {W : List β} (hW : G.IsWalk u W v)
    (hd : IsDrawing G drawing) (hne : W ≠ []) : u ∈ edgesCover drawing W := by
  cases hW with
  | nil => exact absurd rfl hne
  | cons hl _ => exact mem_edgesCover (List.mem_cons_self ..) (hd.edge_isArcBetween hl).left_mem

/-- **A walk of a polygonal plane graph draws a polygonal set.** Consecutive edges share the
vertex between them, so the union stays a single vertex list. -/
theorem IsDrawing.isPolygonal_edgesCover (hd : IsDrawing G drawing)
    (hpoly : ∀ f ∈ E(G), Schoenflies.IsPolygonal (edgeArc drawing f)) :
    ∀ {u v : Plane} {W : List β}, G.IsWalk u W v → W ≠ [] →
      Schoenflies.IsPolygonal (edgesCover drawing W) := by
  intro u v W hW
  induction hW with
  | nil => exact fun h => absurd rfl h
  | @cons u w v f W hl hW ih =>
    intro _
    rcases eq_or_ne W [] with rfl | hWne
    · simpa using hpoly f hl.edge_mem
    · rw [edgesCover_cons]
      exact ((hpoly f hl.edge_mem).union (ih hWne)
        ⟨w, (hd.edge_isArcBetween hl).right_mem, hW.left_mem_edgesCover hd hWne⟩)

end Graph

end BundlePart377

section BundlePart378
/- Source: Papers/GraphicalZonotopes/ArcK5PathReplacement.lean -/



noncomputable section
open Set Schoenflies
open scoped Graph Classical
namespace Graph

/-- The single edge represented by a possibly subdivided path. -/
def IsApexPair (i j : Fin 5) : Prop := (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3)

@[simp] theorem isApexPair_comm (i j : Fin 5) : IsApexPair i j ↔ IsApexPair j i := by
  simp only [IsApexPair]
  tauto

def apexPathFamily {β : Type*} (drawing : β → ℝ → Plane)
    (e : Fin 5 → Fin 5 → β) (W : List β) (i j : Fin 5) : Set Plane :=
  if IsApexPair i j then edgesCover drawing W else edgeArc drawing (e i j)

/-- A finite drawing with all the edges of K₅ except the last one, together
with a path joining the missing endpoints and avoiding the other three
vertices, gives a genuine ten-arc K₅ configuration. -/
theorem IsDrawing.arcK5_of_apex_path {β : Type*} {G : Graph Plane β}
    {drawing : β → ℝ → Plane} (hd : IsDrawing G drawing)
    (x : Fin 5 → Plane) (hx : Function.Injective x)
    (hvertex : ∀ i,x i ∈ V(G)) (e : Fin 5 → Fin 5 → β)
    (hesymm : ∀ i j,e i j = e j i)
    (helink : ∀ i j,i ≠ j → ¬ IsApexPair i j → G.IsLink (e i j) (x i) (x j))
    (W : List β) (hpath : G.IsPath (x 3) W (x 4))
    (havoid : ∀ i : Fin 3,x ⟨i.1,by omega⟩ ∉ edgesCover drawing W) :
    IsArcK5 x (apexPathFamily drawing e W) := by
  classical
  let A := edgesCover drawing W
  have hA : IsArcBetween A (x 3) (x 4) := by
    apply hd.path_isArcBetween hpath
    intro hnil
    have heq := (hnil ▸ hpath.isWalk).eq_of_nil
    have h34 : (3 : Fin 5) ≠ 4 := by decide
    exact h34 (hx heq)
  have hAV : ∀ k : Fin 5,x k ∈ A → k = 3 ∨ k = 4 := by
    intro k hk
    by_cases hlt : k.1 < 3
    · exact False.elim (havoid ⟨k.1,hlt⟩ hk)
    · have hcases : k.1 = 3 ∨ k.1 = 4 := by omega
      exact hcases.imp Fin.ext Fin.ext
  have htriangleEnd : ∀ i j : Fin 5,i ≠ j → ¬ IsApexPair i j →
      i.1 < 3 ∨ j.1 < 3 := by
    intro i j hij hbad
    by_contra hno
    push_neg at hno
    have hi : i = 3 ∨ i = 4 := by
      have hh : i.1 = 3 ∨ i.1 = 4 := by omega
      exact hh.imp Fin.ext Fin.ext
    have hj : j = 3 ∨ j = 4 := by
      have hh : j.1 = 3 ∨ j.1 = 4 := by omega
      exact hh.imp Fin.ext Fin.ext
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact hij rfl
    · exact hbad (Or.inl ⟨rfl,rfl⟩)
    · exact hbad (Or.inr ⟨rfl,rfl⟩)
    · exact hij rfl
  have hnotW : ∀ i j : Fin 5,∀ hij : i ≠ j,∀ hbad : ¬ IsApexPair i j,e i j ∉ W := by
    intro i j hij hbad heW
    have he := helink i j hij hbad
    have hArc := hd.edge_isArcBetween he
    rcases htriangleEnd i j hij hbad with hi | hj
    · exact havoid ⟨i.1,hi⟩ (mem_edgesCover heW hArc.left_mem)
    · exact havoid ⟨j.1,hj⟩ (mem_edgesCover heW hArc.right_mem)
  have hcross : ∀ i j : Fin 5,i ≠ j → ¬ IsApexPair i j →
      A ∩ edgeArc drawing (e i j) ⊆ ({x 3,x 4} : Set Plane) ∩ {x i,x j} := by
    intro i j hij hbad z hz
    obtain ⟨f,hf,hzf⟩ := mem_edgesCover_iff.mp hz.1
    have he := helink i j hij hbad
    have hef : e i j ≠ f := fun hh => hnotW i j hij hbad (hh.symm ▸ hf)
    obtain ⟨_,hze,_⟩ := hd.edge_inter he.edge_mem (hpath.edge_mem hf) hef hz.2 hzf
    have hends := hze.eq_or_eq_of_isLink he
    refine ⟨?_,hends⟩
    rcases hends with rfl | rfl
    · exact (hAV i hz.1).imp (congrArg x) (congrArg x)
    · exact (hAV j hz.1).imp (congrArg x) (congrArg x)
  have hbadends : ∀ i j,IsApexPair i j → ({x i,x j} : Set Plane) = {x 3,x 4} := by
    intro i j hbad
    rcases hbad with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · rfl
    · exact Set.pair_comm _ _
  constructor
  · exact hx
  · intro i j hij
    by_cases hbad : IsApexPair i j
    · rw [apexPathFamily,if_pos hbad]
      rcases hbad with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hA
      · exact hA.reverse
    · rw [apexPathFamily,if_neg hbad]
      exact hd.edge_isArcBetween (helink i j hij hbad)
  · intro i j
    simp only [apexPathFamily,isApexPair_comm i j,hesymm i j]
  · intro i j k hij hk
    by_cases hbad : IsApexPair i j
    · rw [apexPathFamily,if_pos hbad] at hk
      have hkv := hAV k hk
      rcases hbad with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hkv
      · exact hkv.symm
    · rw [apexPathFamily,if_neg hbad] at hk
      exact (hd.vertex_mem_edgeArc (helink i j hij hbad) (hvertex k) hk).imp
        (fun hh => hx hh) (fun hh => hx hh)
  · intro i j k l hij hkl hpairs hreverse
    by_cases hbad1 : IsApexPair i j
    · by_cases hbad2 : IsApexPair k l
      · rcases hbad1 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
          rcases hbad2 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact False.elim (hpairs rfl)
        · exact False.elim (hreverse rfl)
        · exact False.elim (hreverse rfl)
        · exact False.elim (hpairs rfl)
      · rw [apexPathFamily,if_pos hbad1,apexPathFamily,if_neg hbad2,hbadends i j hbad1]
        exact hcross k l hkl hbad2
    · by_cases hbad2 : IsApexPair k l
      · rw [apexPathFamily,if_neg hbad1,apexPathFamily,if_pos hbad2,hbadends k l hbad2]
        intro z hz
        exact (hcross i j hij hbad1 ⟨hz.2,hz.1⟩).symm
      · rw [apexPathFamily,if_neg hbad1,apexPathFamily,if_neg hbad2]
        intro z hz
        have he1 := helink i j hij hbad1
        have he2 := helink k l hkl hbad2
        have hef : e i j ≠ e k l := by
          intro heq
          have he2' : G.IsLink (e i j) (x k) (x l) := heq.symm ▸ he2
          rcases he1.eq_and_eq_or_eq_and_eq he2' with ⟨h1,h2⟩ | ⟨h1,h2⟩
          · exact hpairs (Prod.ext (hx h1) (hx h2))
          · exact hreverse (Prod.ext (hx h1) (hx h2))
        obtain ⟨_,hze,hzf⟩ := hd.edge_inter he1.edge_mem he2.edge_mem hef hz.1 hz.2
        exact ⟨hze.eq_or_eq_of_isLink he1,hzf.eq_or_eq_of_isLink he2⟩

end Graph

end
end BundlePart378

section BundlePart379
/- Source: Papers/GraphicalZonotopes/PlanarApexArc.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical Graph
namespace GraphicalZonotopes
open Finset Schoenflies
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An actual graph path avoiding a prescribed finite set is realized by a
simple plane arc avoiding the corresponding points. The proof transports
Mathlib walks to the library's edge-list walks, then shortens them without
adding an edge. -/
theorem PlaneDrawing.avoiding_path {G : SimpleGraph V} {p : V → Plane}
    (hp : Function.Injective p) {drawing : Sym2 V → ℝ → Plane}
    (hd : Graph.IsDrawing (planeGraph G p) drawing)
    (T : Finset V) (u w : V) (hu : u ∉ T) (hw : w ∉ T)
    (hreach : (G.induce ((T : Set V)ᶜ)).Reachable ⟨u,hu⟩ ⟨w,hw⟩) :
    ∃ W : List (Sym2 V),(planeGraph G p).IsPath (p u) W (p w) ∧
      ∀ t ∈ T,p t ∉ Graph.edgesCover drawing W := by
  let H := planeGraph G p
  have aux : ∀ {a b : ↥((T : Set V)ᶜ)},(G.induce ((T : Set V)ᶜ)).Walk a b →
      ∃ W : List (Sym2 V),H.IsWalk (p a.1) W (p b.1) ∧
        ∀ e ∈ W,∃ r s : V,r ∉ T ∧ s ∉ T ∧ H.IsLink e (p r) (p s) := by
    intro a b q
    induction q with
    | @nil a =>
      refine ⟨[],Graph.IsWalk.nil ?_,?_⟩
      · change p a.1 ∈ V(planeGraph G p)
        rw [planeGraph_vertexSet]
        exact ⟨a.1,rfl⟩
      · intro e he
        simp at he
    | @cons a b c hab q ih =>
      obtain ⟨W,hW,hends⟩ := ih
      have hl : H.IsLink s(a.1,b.1) (p a.1) (p b.1) :=
        (planeGraph_isLink G p hp _ _ _).mpr ⟨rfl,hab⟩
      refine ⟨s(a.1,b.1)::W,Graph.IsWalk.cons hl hW,?_⟩
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact ⟨a.1,b.1,a.2,b.2,hl⟩
      · exact hends e he
  obtain ⟨W,hW,hends⟩ := aux hreach.some
  obtain ⟨P,hP,hPW⟩ := hW.contains_path
  refine ⟨P,hP,?_⟩
  intro t ht hmem
  obtain ⟨e,he,hte⟩ := Graph.mem_edgesCover_iff.mp hmem
  obtain ⟨r,s,hr,hs,hl⟩ := hends e (hPW he)
  have hv : p t ∈ V(H) := by
    change p t ∈ V(planeGraph G p)
    rw [planeGraph_vertexSet]
    exact ⟨t,rfl⟩
  rcases hd.vertex_mem_edgeArc hl hv hte with htr | hts
  · exact hr (hp htr ▸ ht)
  · exact hs (hp hts ▸ ht)

/-- The forbidden configuration behind the planar triangle-apex separation:
a triangle, two distinct vertices complete to it, and a path joining those
two vertices away from the triangle yield ten genuine noncrossing K₅ arcs. -/
theorem HasPlaneDrawing.arcK5_of_triangle_apex_path {G : SimpleGraph V}
    (hG : HasPlaneDrawing G) (T : Finset V) (hT : T.card = 3) (hcT : G.IsClique T)
    (u w : V) (hu : u ∉ T) (hw : w ∉ T) (huw : u ≠ w)
    (huAdj : ∀ t ∈ T,G.Adj u t) (hwAdj : ∀ t ∈ T,G.Adj w t)
    (hreach : (G.induce ((T : Set V)ᶜ)).Reachable ⟨u,hu⟩ ⟨w,hw⟩) :
    ∃ (x : Fin 5 → Plane) (P : Fin 5 → Fin 5 → Set Plane),Graph.IsArcK5 x P := by
  obtain ⟨p,hp,drawing,hd⟩ := hG
  obtain ⟨W,hpath,havoid⟩ := PlaneDrawing.avoiding_path hp hd T u w hu hw hreach
  obtain ⟨a,b,c,hab,hac,hbc,hTabc⟩ := card_eq_three.mp hT
  have haT : a ∈ T := by rw [hTabc]; simp
  have hbT : b ∈ T := by rw [hTabc]; simp
  have hcT' : c ∈ T := by rw [hTabc]; simp
  have hua : u ≠ a := fun he => hu (he.symm ▸ haT)
  have hub : u ≠ b := fun he => hu (he.symm ▸ hbT)
  have huc : u ≠ c := fun he => hu (he.symm ▸ hcT')
  have hwa : w ≠ a := fun he => hw (he.symm ▸ haT)
  have hwb : w ≠ b := fun he => hw (he.symm ▸ hbT)
  have hwc : w ≠ c := fun he => hw (he.symm ▸ hcT')
  let names : Fin 5 → V := ![a,b,c,u,w]
  let x : Fin 5 → Plane := p ∘ names
  let e : Fin 5 → Fin 5 → Sym2 V := fun i j => s(names i,names j)
  have hnames : Function.Injective names := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [names]
  have hxab := hcT haT hbT hab
  have hxac := hcT haT hcT' hac
  have hxbc := hcT hbT hcT' hbc
  have hxuA := huAdj a haT
  have hxuB := huAdj b hbT
  have hxuC := huAdj c hcT'
  have hxwA := hwAdj a haT
  have hxwB := hwAdj b hbT
  have hxwC := hwAdj c hcT'
  have hadj : ∀ i j : Fin 5,i ≠ j → ¬ Graph.IsApexPair i j → G.Adj (names i) (names j) := by
    intro i j hij hbad
    fin_cases i <;> fin_cases j <;>
      simp_all [names,Graph.IsApexPair,SimpleGraph.adj_comm]
  have hvertex : ∀ i,x i ∈ V(PlaneDrawing.planeGraph G p) := by
    intro i
    rw [PlaneDrawing.planeGraph_vertexSet]
    exact ⟨names i,rfl⟩
  have he : ∀ i j : Fin 5,i ≠ j → ¬ Graph.IsApexPair i j →
      (PlaneDrawing.planeGraph G p).IsLink (e i j) (x i) (x j) := by
    intro i j hij hbad
    exact (PlaneDrawing.planeGraph_isLink G p hp _ _ _).mpr ⟨rfl,hadj i j hij hbad⟩
  have hpath' : (PlaneDrawing.planeGraph G p).IsPath (x 3) W (x 4) := by
    simpa [x,names] using hpath
  have havoid' : ∀ i : Fin 3,x ⟨i.1,by omega⟩ ∉ Graph.edgesCover drawing W := by
    intro i
    apply havoid
    fin_cases i <;> simp [names,hTabc]
  exact ⟨x,Graph.apexPathFamily drawing e W,hd.arcK5_of_apex_path x (hp.comp hnames)
    hvertex e (fun i j => Sym2.eq_swap) he W hpath' havoid'⟩

end GraphicalZonotopes

end
end
end BundlePart379

section BundlePart380
/- Source: dev/planar_search/schoenflies_port/Schoenflies/UniformBound.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/


/-!
# One positive bound for finitely many

Every "choose `ε` small enough for all of them" step in the development is this lemma: a
finite family of positive bounds has a single positive bound below all of them. The
polygonal-redrawing argument alone uses it three times, and the two-sided strip lemma chooses
its vertex disks and edge blocks the same way.

It is stated for a *predicate that is monotone downward in the bound* rather than as a `min`
fold, because no consumer wants the value — only that some positive value works for every
member at once.

## Blueprint

* `exists_pos_le_of_finite` — the numerical form.
* `exists_pos_forall_of_finite` — the form consumers use: a downward-monotone predicate
  holding at some positive bound for each member holds at one common positive bound.
-/

open Set

namespace Schoenflies

variable {ι : Type*}

/-- A finite family of positive reals is bounded below by a positive real. -/
theorem exists_pos_le_of_finite {S : Set ι} (hS : S.Finite) {f : ι → ℝ}
    (hf : ∀ i ∈ S, 0 < f i) : ∃ ε > 0, ∀ i ∈ S, ε ≤ f i := by
  classical
  induction S, hS using Set.Finite.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | @insert a S ha hS ih =>
    obtain ⟨ε, hε, hbound⟩ := ih fun i hi => hf i (mem_insert_of_mem _ hi)
    refine ⟨min ε (f a), lt_min hε (hf a (mem_insert _ _)), fun i hi => ?_⟩
    rcases mem_insert_iff.1 hi with rfl | hi
    · exact min_le_right _ _
    · exact le_trans (min_le_left _ _) (hbound i hi)

/-- The form the geometry uses: if a property that only gets easier as the bound shrinks holds
at *some* positive bound for each member of a finite family, then it holds at *one* positive
bound for all of them at once. -/
theorem exists_pos_forall_of_finite {S : Set ι} (hS : S.Finite) {P : ι → ℝ → Prop}
    (hmono : ∀ i, ∀ ⦃δ ε : ℝ⦄, 0 < δ → δ ≤ ε → P i ε → P i δ)
    (hex : ∀ i ∈ S, ∃ ε > 0, P i ε) :
    ∃ ε > 0, ∀ i ∈ S, P i ε := by
  classical
  -- Pick a witness for each member, then take a positive bound below all the witnesses.
  choose! f hfpos hfP using hex
  obtain ⟨ε, hε, hbound⟩ := exists_pos_le_of_finite hS (f := f) hfpos
  exact ⟨ε, hε, fun i hi => hmono i hε (hbound i hi) (hfP i hi)⟩

end Schoenflies

end BundlePart380

section BundlePart381
/- Source: dev/planar_search/schoenflies_port/Schoenflies/Subarc.lean -/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/


/-!
# Subarcs, open arcs, and the subarc basis

A subarc is the arc restricted to a subinterval of the parameter interval — but an arc is
carried by a map *on* `[0, 1]`, so the restriction has to be reparametrised back onto it.
That reparametrisation is `reparam a b : t ↦ a + t * (b - a)`: pure arithmetic, with no
inverse to construct and no choice to make. With it a subarc is a composition, and the two
things an arc must be — continuous and injective — are the two things a composition inherits.

Injectivity is required only on `uIcc a b`, the parameter interval actually traversed, not on
all of `[0, 1]`. That is what lets the two arcs of a Jordan curve be cut out of a loop, whose
parametrisation is injective on `[0, 1)` only.

The substance of the file is the last two sections. A parametrisation is an **open map onto
its arc**: the image of a relatively open piece of the parameter interval is relatively open
in the arc. This is where the continuity of the inverse earns its keep, and it is proved
without ever constructing that inverse — a continuous injection on a compact set is a closed
map onto its image, and a closed injective map is open onto its image, by complements.
Together with `basic_piece_inside_ball`, which puts such a piece inside any prescribed ball,
these images are a basis of the arc's subspace topology.

Relative openness is stated in the ambient form `∃ V, IsOpen V ∧ W = V ∩ A` rather than
through the subtype `↥A`, since every consumer here works with subsets of the plane.

## Blueprint

The blueprint uses subarcs throughout §1 without a numbered statement of their own; they are
the tool behind, among others, the model-curve parametrization (`lem:jordan-circle`), where
"the relatively open subarcs of `C`" are exactly the images produced by `image_isRelOpen`, and
the density arguments of `lem:accessible-dense`, which need `basic_piece_inside_ball`.

* `subarc`, `isArcBetween_subarc` — a piece of an arc is again an arc.
* `IsArc.exists_isArcBetween_subset` — the set-level reading: two points of an arc bound a
  subarc of it.
* `openArc` — the blueprint's `P°`, an arc without its two endpoints.
* `image_isRelOpen` — a parametrisation is an open map onto its arc; `openArc_isRelOpen` and
  `openArc_subarc_isRelOpen` are the "relatively open subarcs" of `lem:jordan-circle`.
* `basic_piece_inside_ball` — the subarc basis.
-/

open Set unitInterval

namespace Schoenflies

/-! ### Reparametrising `[0, 1]` onto a subinterval -/

/-- The affine map carrying `[0, 1]` onto the parameter interval between `a` and `b`,
running from `a` to `b`. -/
def reparam (a b : ℝ) : ℝ → ℝ := fun t => a + t * (b - a)

variable {a b : ℝ}

@[simp] theorem reparam_zero : reparam a b 0 = a := by simp [reparam]

@[simp] theorem reparam_one : reparam a b 1 = b := by simp [reparam]

theorem continuous_reparam : Continuous (reparam a b) := by unfold reparam; fun_prop

/-- The reparametrisation is injective as soon as it is not constant. -/
theorem reparam_injective (hab : a ≠ b) : Function.Injective (reparam a b) := by
  intro s t hst
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have : s * (b - a) = t * (b - a) := by
    have := hst
    simp only [reparam] at this
    linarith
  exact mul_right_cancel₀ hba this

/-- `reparam a b` carries the unit interval exactly onto `uIcc a b`. This is `segment_eq_image'`
read through the identification of a real segment with an unordered closed interval. -/
theorem image_reparam_I : reparam a b '' I = uIcc a b := by
  have h : (fun θ : ℝ => a + θ • (b - a)) '' Icc (0 : ℝ) 1 = uIcc a b := by
    rw [← segment_eq_image' ℝ a b, segment_eq_uIcc]
  change (fun θ : ℝ => a + θ * (b - a)) '' Icc (0 : ℝ) 1 = uIcc a b
  simpa only [smul_eq_mul] using h

theorem mapsTo_reparam : MapsTo (reparam a b) I (uIcc a b) :=
  mapsTo_iff_image_subset.mpr image_reparam_I.subset

/-- A subinterval of the unit interval stays inside it: `uIcc` is the convex hull of its two
endpoints, and the unit interval is convex. -/
theorem uIcc_subset_I (ha : a ∈ I) (hb : b ∈ I) : uIcc a b ⊆ I :=
  uIcc_subset_Icc ha hb

/-! ### Subarcs -/

/-- The subarc of `f` between the parameters `a` and `b`: the arc traversed from `f a` to
`f b`, reparametrised so that it is again a map on `[0, 1]`. -/
def subarc (f : ℝ → Plane) (a b : ℝ) : ℝ → Plane := fun t => f (reparam a b t)

variable {f : ℝ → Plane}

@[simp] theorem subarc_zero : subarc f a b 0 = f a := by simp [subarc]

@[simp] theorem subarc_one : subarc f a b 1 = f b := by simp [subarc]

/-- The image of a subarc is the arc restricted to the subinterval — which is what "sub"
means, and the form every consumer wants. -/
theorem subarc_image : subarc f a b '' I = f '' uIcc a b := by
  rw [show subarc f a b = f ∘ reparam a b from rfl, image_comp, image_reparam_I]

theorem subarc_image_subset (ha : a ∈ I) (hb : b ∈ I) : subarc f a b '' I ⊆ f '' I := by
  rw [subarc_image]
  exact image_mono (uIcc_subset_I ha hb)

theorem continuousOn_subarc (hc : ContinuousOn f I) (ha : a ∈ I) (hb : b ∈ I) :
    ContinuousOn (subarc f a b) I :=
  hc.comp continuous_reparam.continuousOn
    (mapsTo_reparam.mono_right (uIcc_subset_I ha hb))

/-- Injectivity of the subarc needs injectivity of `f` only where the subarc runs. -/
theorem injOn_subarc (hi : InjOn f (uIcc a b)) (hab : a ≠ b) : InjOn (subarc f a b) I := by
  intro s hs t ht hst
  exact reparam_injective hab (hi (mapsTo_reparam hs) (mapsTo_reparam ht) hst)

/-- A subarc between two distinct parameters is an arc between the two values there. The
injectivity hypothesis is confined to the traversed interval, so this applies to a piece of a
Jordan curve as well as to a piece of an arc. -/
theorem isArcBetween_subarc (hc : ContinuousOn f I) (hi : InjOn f (uIcc a b))
    (ha : a ∈ I) (hb : b ∈ I) (hab : a ≠ b) :
    IsArcBetween (f '' uIcc a b) (f a) (f b) :=
  ⟨subarc f a b, continuousOn_subarc hc ha hb, injOn_subarc hi hab,
    subarc_image, subarc_zero, subarc_one⟩

theorem isArc_subarc (hc : ContinuousOn f I) (hi : InjOn f (uIcc a b))
    (ha : a ∈ I) (hb : b ∈ I) (hab : a ≠ b) : IsArc (f '' uIcc a b) :=
  (isArcBetween_subarc hc hi ha hb hab).isArc

/-- The version for an arc, whose parametrisation is injective everywhere. -/
theorem isArcBetween_subarc_of_injOn_I (hc : ContinuousOn f I) (hi : InjOn f I)
    (ha : a ∈ I) (hb : b ∈ I) (hab : a ≠ b) :
    IsArcBetween (f '' uIcc a b) (f a) (f b) :=
  isArcBetween_subarc hc (hi.mono (uIcc_subset_I ha hb)) ha hb hab

/-- Any two distinct points of an arc are the endpoints of a subarc of it. The set-level
form, for the consumers that never see a parametrisation. -/
theorem IsArc.exists_isArcBetween_subset {A : Set Plane} (h : IsArc A) {p q : Plane}
    (hp : p ∈ A) (hq : q ∈ A) (hpq : p ≠ q) : ∃ B ⊆ A, IsArcBetween B p q := by
  obtain ⟨f, hc, hi, rfl⟩ := h
  obtain ⟨s, hs, rfl⟩ := hp
  obtain ⟨t, ht, rfl⟩ := hq
  refine ⟨f '' uIcc s t, image_mono (uIcc_subset_I hs ht), ?_⟩
  exact isArcBetween_subarc_of_injOn_I hc hi hs ht (fun h => hpq (by rw [h]))

/-! ### The arc without its endpoints -/

/-- The open arc — the blueprint's `P°`: an arc with its two endpoints removed.

Taken on the parameter side, as the image of the open unit interval, because that is the form
the subarc basis argument needs: an open subarc is the image of an open subinterval.
Injectivity then says it is also the arc minus the two endpoint *values*, which is how the
blueprint reads it (`openArc_eq_diff`). -/
def openArc (f : ℝ → Plane) : Set Plane := f '' Ioo 0 1

theorem Ioo_subset_I : Ioo (0 : ℝ) 1 ⊆ I := Ioo_subset_Icc_self

theorem openArc_subset : openArc f ⊆ f '' I := image_mono Ioo_subset_I

/-- On an arc the two readings of "without its endpoints" agree: dropping the endpoints of the
parameter interval drops exactly the two endpoint values, since injectivity means no other
parameter shares them. -/
theorem openArc_eq_diff (hi : InjOn f I) : openArc f = f '' I \ {f 0, f 1} := by
  have hIoo : Ioo (0 : ℝ) 1 = I \ {0, 1} := by
    ext t
    simp only [mem_Ioo, mem_sdiff, mem_Icc, mem_insert_iff, mem_singleton_iff, not_or]
    constructor
    · rintro ⟨h0, h1⟩; exact ⟨⟨h0.le, h1.le⟩, h0.ne', h1.ne⟩
    · rintro ⟨⟨h0, h1⟩, hne0, hne1⟩; exact ⟨h0.lt_of_ne' hne0, h1.lt_of_ne hne1⟩
  have hpair : f '' ({0, 1} : Set ℝ) = {f 0, f 1} := image_pair f 0 1
  rw [openArc, hIoo, hi.image_sdiff_subset (by
        rintro t (rfl | rfl); exacts [zero_mem_I, one_mem_I]), hpair]

/-- The open arc of a subarc is the arc restricted to the *open* subinterval. -/
theorem openArc_subarc (hab : a ≠ b) : openArc (subarc f a b) = f '' uIoo a b := by
  have h : reparam a b '' Ioo 0 1 = uIoo a b := by
    rcases lt_trichotomy a b with hlt | rfl | hgt
    · -- Increasing: the witness for `x` is the fraction of the way from `a` to `b`.
      rw [uIoo_of_lt hlt]
      ext x
      simp only [mem_image, mem_Ioo, reparam]
      refine ⟨?_, fun hx => ⟨(x - a) / (b - a), ⟨?_, ?_⟩, by field_simp; ring⟩⟩
      · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
        constructor <;> nlinarith
      · exact div_pos (by linarith [hx.1]) (by linarith)
      · exact (div_lt_one (by linarith)).mpr (by linarith [hx.2])
    · exact absurd rfl hab
    · -- Decreasing: the same fraction, written with both signs flipped.
      rw [uIoo_of_gt hgt]
      ext x
      simp only [mem_image, mem_Ioo, reparam]
      refine ⟨?_, fun hx => ⟨(a - x) / (a - b), ⟨?_, ?_⟩, by field_simp; ring⟩⟩
      · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
        constructor <;> nlinarith
      · exact div_pos (by linarith [hx.2]) (by linarith)
      · exact (div_lt_one (by linarith)).mpr (by linarith [hx.1])
  rw [openArc, show subarc f a b = f ∘ reparam a b from rfl, image_comp, h]

/-! ### The interior of an arc, set-level

`openArc` is stated for a parametrisation. Three separate modules needed the same facts stated
for the *set* — `IsArcBetween A p q` gives `A ∖ {p, q}` connected, nonempty, and having both
endpoints in its closure — and each proved them again from scratch, one of them twice under two
names. Two of those copies were literally the same statement in modules that do not import each
other, so the build never noticed: alpha-equivalent `Prop`s are defeq under proof irrelevance,
and Lean's import checker accepts them. They live here now. -/

/-- **The interior of an arc is the image of the open parameter interval.** The bridge from
`IsArcBetween`, which is about the set, to `openArc`, which is about a parametrisation. -/
theorem IsArcBetween.diff_eq_openArc {A : Set Plane} {p q : Plane} (h : IsArcBetween A p q) :
    ∃ f : ℝ → Plane, ContinuousOn f I ∧ A \ {p, q} = f '' Ioo 0 1 := by
  obtain ⟨f, hc, hi, himg, h0, h1⟩ := h
  exact ⟨f, hc, by rw [← himg, ← h0, ← h1, ← openArc_eq_diff hi, openArc]⟩

/-- **The interior of an arc is connected.** It is the continuous image of `Ioo 0 1`. -/
theorem IsArcBetween.isPreconnected_diff {A : Set Plane} {p q : Plane} (h : IsArcBetween A p q) :
    IsPreconnected (A \ {p, q}) := by
  obtain ⟨f, hc, hEq⟩ := h.diff_eq_openArc
  rw [hEq]
  exact isPreconnected_Ioo.image _ (hc.mono Ioo_subset_I)

/-- The interior of an arc is nonempty: `Ioo 0 1` is. -/
theorem IsArcBetween.nonempty_diff {A : Set Plane} {p q : Plane} (h : IsArcBetween A p q) :
    (A \ {p, q}).Nonempty := by
  obtain ⟨f, -, hEq⟩ := h.diff_eq_openArc
  rw [hEq]
  exact ⟨f (1 / 2), 1 / 2, by norm_num, rfl⟩

/-- The interior of an arc is connected in the nonempty sense. -/
theorem IsArcBetween.isConnected_diff {A : Set Plane} {p q : Plane} (h : IsArcBetween A p q) :
    IsConnected (A \ {p, q}) :=
  ⟨h.nonempty_diff, h.isPreconnected_diff⟩

/-- **An endpoint of an arc is a limit of its interior.** This is what turns "the closure of a
cell meets the curve in one arc only" into a statement about the *endpoints* of a crosscut, and
it is what says an ear's two ends lie on the boundary of the face its interior lies in. -/
theorem IsArcBetween.left_mem_closure_diff {A : Set Plane} {p q : Plane}
    (h : IsArcBetween A p q) : p ∈ closure (A \ {p, q}) := by
  obtain ⟨f, hc, hi, himg, h0, h1⟩ := h
  have hEq : A \ {p, q} = f '' Ioo 0 1 := by
    rw [← himg, ← h0, ← h1, ← openArc_eq_diff hi, openArc]
  -- The endpoint is the limit of the interior as the parameter tends to `0`.
  rw [hEq, ← h0]
  refine ((hc 0 zero_mem_I).mono Ioo_subset_I).mem_closure_image ?_
  rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
  exact zero_mem_I

theorem IsArcBetween.right_mem_closure_diff {A : Set Plane} {p q : Plane}
    (h : IsArcBetween A p q) : q ∈ closure (A \ {p, q}) := by
  rw [Set.pair_comm]
  exact h.reverse.left_mem_closure_diff

/-! ### A parametrisation is an open map onto its arc -/

/-- **The parametrisation is an open map onto its arc.** The image of a relatively open piece
of the parameter interval is relatively open in the arc.

No inverse is constructed. The complement piece `I \ U` is compact, so its image is compact,
so it is closed; and by injectivity the image of `U ∩ I` is exactly the arc minus that closed
set. Stated for a relatively open *piece* `U ∩ I` rather than for a subarc, because at an
endpoint the basic neighbourhood is half-open — `openArc` of a subarc is the interior case,
and this covers both. -/
theorem image_isRelOpen (hc : ContinuousOn f I) (hi : InjOn f I) {U : Set ℝ} (hU : IsOpen U) :
    ∃ V : Set Plane, IsOpen V ∧ f '' (U ∩ I) = V ∩ f '' I := by
  refine ⟨(f '' (I \ U))ᶜ, ?_, ?_⟩
  · -- The discarded piece is compact, hence closed, so its complement is open.
    exact (isCompact_image_of_subset_I hc sdiff_subset
      (isClosed_Icc.sdiff hU)).isClosed.isOpen_compl
  · -- Injectivity turns "remove the image" into "image of the removal".
    have hdiff : f '' (I \ (I \ U)) = f '' I \ f '' (I \ U) :=
      hi.image_sdiff_subset sdiff_subset
    rw [sdiff_sdiff_right_self, inter_comm I U] at hdiff
    rw [hdiff, sdiff_eq, inter_comm]

/-- The pointwise reading of the previous theorem, and the one consumers use: around every
point of the image of a relatively open piece there is a ball meeting the arc only inside that
image. This is precisely the continuity of the inverse parametrisation. -/
theorem exists_ball_inter_subset_image (hc : ContinuousOn f I) (hi : InjOn f I)
    {U : Set ℝ} (hU : IsOpen U) {x : Plane} (hx : x ∈ f '' (U ∩ I)) :
    ∃ ε > 0, Metric.ball x ε ∩ f '' I ⊆ f '' (U ∩ I) := by
  obtain ⟨V, hVopen, hV⟩ := image_isRelOpen hc hi hU
  have hxV : x ∈ V := (hV ▸ hx).1
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hVopen x hxV
  exact ⟨ε, hε, fun y hy => hV ▸ ⟨hball hy.1, hy.2⟩⟩

/-- The open arc is relatively open in the arc: the blueprint's `P°` is a relatively open
subarc. -/
theorem openArc_isRelOpen (hc : ContinuousOn f I) (hi : InjOn f I) :
    ∃ V : Set Plane, IsOpen V ∧ openArc f = V ∩ f '' I := by
  obtain ⟨V, hVopen, hV⟩ := image_isRelOpen hc hi (isOpen_Ioo (a := (0 : ℝ)) (b := 1))
  exact ⟨V, hVopen, by rwa [inter_eq_self_of_subset_left Ioo_subset_I] at hV⟩

/-- A subarc without its endpoints is relatively open in the arc. These are the "relatively
open subarcs" the blueprint speaks of. -/
theorem openArc_subarc_isRelOpen (hc : ContinuousOn f I) (hi : InjOn f I)
    (ha : a ∈ I) (hb : b ∈ I) :
    ∃ V : Set Plane, IsOpen V ∧ f '' uIoo a b = V ∩ f '' I := by
  obtain ⟨V, hVopen, hV⟩ := image_isRelOpen hc hi (U := uIoo a b) isOpen_Ioo
  refine ⟨V, hVopen, ?_⟩
  rwa [inter_eq_self_of_subset_left
    (uIoo_subset_uIcc_self.trans (uIcc_subset_I ha hb))] at hV

/-! ### The subarc basis -/

/-- **Every neighbourhood of a point of the arc contains the image of an open subinterval
around its parameter.** With `image_isRelOpen`, which says those images are relatively open,
this makes them a basis of the arc's subspace topology.

The piece is the parameter interval cut by an interval around the parameter, which is
half-open exactly when the point is an endpoint. -/
theorem basic_piece_inside_ball (hc : ContinuousOn f I) {x : Plane} (hx : x ∈ f '' I)
    {r : ℝ} (hr : 0 < r) :
    ∃ c d : ℝ, x ∈ f '' (Ioo c d ∩ I) ∧ f '' (Ioo c d ∩ I) ⊆ Metric.ball x r := by
  obtain ⟨s, hs, rfl⟩ := hx
  -- Continuity at the parameter turns the prescribed radius into a parameter radius.
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousWithinAt_iff.mp (hc s hs) r hr
  refine ⟨s - δ, s + δ, ⟨s, ⟨⟨by linarith, by linarith⟩, hs⟩, rfl⟩, ?_⟩
  rintro y ⟨t, ⟨ht, htI⟩, rfl⟩
  have : dist t s < δ := by
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  exact Metric.mem_ball.mpr (hclose htI this)

end Schoenflies

end BundlePart381

