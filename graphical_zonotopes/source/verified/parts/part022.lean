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

public import verified.parts.part021
import all verified.parts.part021

@[expose] public section

set_option debug.skipKernelTC false
set_option linter.all false
set_option Elab.async false
set_option internal.cmdlineSnapshots true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

section BundlePart314
/- Source: Papers/GraphicalZonotopes/SaturatedBookGeometry.lean -/






/-! # The universal geometric lower bound for saturated books

All hypotheses are imposed on the actual polytope.  The normalized graphical
function and its actual direction graph are derived, not supplied as premises.
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

theorem full_weak_direction_model {V : Type*} [Fintype V] [DecidableEq V]
    (hn : 2 ≤ Fintype.card V) {H : SimpleGraph V} {Q : Set (V → ℝ)}
    (hQ : IsFinitePolytope Q) (hi : MinkowskiIndecomposable Q)
    (hd : FullDimension Q) (hw : IsWeakMinkowskiSummand Q (graphicalZonotope H)) :
    ∃ z : graphicalFunctionSpace (actualDirectionGraph Q),ExtremeSupermodular z.1 ∧
      FullDimension (basePolytope z.1) ∧ actualDirectionGraph Q ≤ H := by
  obtain ⟨a,ha,R,hR,hRc,hnR,hQR⟩ := hw
  have hTn : Normalized (a • graphFunction H) := by
    change a*graphFunction H ∅ = 0
    rw [graphFunction_normalized,mul_zero]
  have hTs := (graphFunction_supermodular H).smul ha.le
  have hbase : Q + R = basePolytope (a • graphFunction H) := by
    rw [basePolytope_smul (graphFunction_normalized H) (graphFunction_supermodular H) ha.le,
      baseGraphFunction_eq_graphicalZonotope]
    exact hQR
  let f := lowerSupport Q
  have hfn : Normalized f := lowerSupport_normalized hQ.compact hi.1
  have hfs : Supermodular f := summand_lowerSupport_supermodular hTn hTs
    hQ.compact hR hi.1 hnR hbase
  have hbody : Q = basePolytope f := summand_eq_basePolytope hTn hTs
    hQ.compact hR hQ.convex hi.1 hnR hbase
  let z := normalize f
  have hzn : TranslationNormalized z := normalize_translationNormalized hfn
  have hzs : Supermodular z := hfs.normalize
  have hdim : FullDimension (basePolytope z) := by
    change Module.finrank ℝ (vectorSpan ℝ (basePolytope (normalize f))) = _
    rw [vectorSpan_basePolytope_normalize,← hbody]
    exact hd
  have hne : z ≠ 0 := by
    intro hz
    have hh := hdim
    change Module.finrank ℝ (vectorSpan ℝ (basePolytope z)) = Fintype.card V - 1 at hh
    rw [hz,basePolytope_zero,vectorSpan_singleton,finrank_bot] at hh
    omega
  have hext : ExtremeSupermodular z :=
    MinkowskiIndecomposable.extremeSupermodular_normalize hfn hfs hne (hbody ▸ hi)
  have hactual : actualDirectionGraph (basePolytope z) = actualDirectionGraph Q := by
    rw [actualDirectionGraph_normalize,← hbody]
  have hzg : Graphical (actualDirectionGraph Q) z := by
    rw [← hactual]
    intro u v huv hnon S hu hv
    have hnonneg := hzs.elemental u v huv S hu hv
    apply le_antisymm _ hnonneg
    by_contra h
    have hpos : 0 < delta z u v S := lt_of_not_ge h
    exact hnon (exposedSegment_of_positive_delta hzn.1 hzs huv hu hv hpos)
  refine ⟨⟨z,hzn,hzg⟩,hext,hdim,?_⟩
  intro u v huv
  rw [hbody] at huv
  exact basePolytope_summand_actualRootEdge hfn hfs H ha.le R (hbody ▸ hQR) huv

variable {s : ℕ}
local instance geometricVertexOrder (s k : ℕ) : LinearOrder (Vertex s k) :=
  inferInstanceAs (LinearOrder (Fin s ⊕ₗ Fin k))
local instance geometricVertexDecidableEq (s k : ℕ) : DecidableEq (Vertex s k) :=
  (geometricVertexOrder s k).toDecidableEq

/-- Saturation forces every hub pair to occur and supplies the sharp bound
on the number of actual spokes at every hub. -/
theorem actual_hub_spoke_lower (hs : 2 ≤ s)
    {Q : Set (Vertex s (cliqueCapacity s) → ℝ)}
    (hQ : IsFinitePolytope Q) (hi : MinkowskiIndecomposable Q)
    (hd : FullDimension Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope (cliqueBook s (cliqueCapacity s)))) :
    actualDirectionGraph Q ≤ cliqueBook s (cliqueCapacity s) ∧
    (∀ i j : Fin s,i ≠ j → ActualRootEdge Q (Sum.inl i) (Sum.inl j)) ∧
    ∀ i : Fin s,saturatedHubNeighbors s ≤
      (univ.filter (fun j : Fin (cliqueCapacity s) =>
        ActualRootEdge Q (Sum.inl i) (Sum.inr j))).card := by
  obtain ⟨z,hz,hdz,hsub⟩ := full_weak_direction_model
    (by simp only [Fintype.card_sum,Fintype.card_fin]; omega) hQ hi hd hw
  refine ⟨hsub,?_⟩
  by_cases hs2 : s = 2
  · subst s
    have ht : actualDirectionGraph Q = ⊤ := three_vertex_complete
      (by norm_num [Fintype.card_sum,Fintype.card_fin,cliqueCapacity,Nat.choose]) _ z hz hdz
    constructor
    · intro i j hij
      change (actualDirectionGraph Q).Adj (Sum.inl i) (Sum.inl j)
      rw [ht]
      exact (SimpleGraph.top_adj _ _).mpr (fun he => hij (Sum.inl_injective he))
    · intro i
      have ha : ∀ j : Fin (cliqueCapacity 2),ActualRootEdge Q (Sum.inl i) (Sum.inr j) := by
        intro j
        change (actualDirectionGraph Q).Adj (Sum.inl i) (Sum.inr j)
        rw [ht]
        exact (SimpleGraph.top_adj _ _).mpr Sum.inl_ne_inr
      simp only [ha,filter_true,card_univ,Fintype.card_fin]
      norm_num [saturatedHubNeighbors,cliqueCapacity,Nat.choose]
  · have hs3 : 3 ≤ s := by omega
    have hc := hubs_clique hs3 hsub z hz hdz
    constructor
    · intro i j hij
      exact hc (mem_image.mpr ⟨i,mem_univ _,rfl⟩) (mem_image.mpr ⟨j,mem_univ _,rfl⟩)
        (fun he => hij (Sum.inl_injective he))
    · intro i
      exact outer_neighbors_lower hs3 hsub z hz hdz i

/-- Theorem 7.12, universal actual-direction lower bound. -/
theorem direction_lower (hs : 2 ≤ s)
    {Q : Set (Vertex s (cliqueCapacity s) → ℝ)}
    (hQ : IsFinitePolytope Q) (hi : MinkowskiIndecomposable Q)
    (hd : FullDimension Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope (cliqueBook s (cliqueCapacity s)))) :
    s.choose 2 + s*saturatedHubNeighbors s ≤ directionCount Q := by
  obtain ⟨hsub,hh,hn⟩ := actual_hub_spoke_lower hs hQ hi hd hw
  exact BookEdges.edge_count_lower (actualDirectionGraph Q) hsub hh
    (saturatedHubNeighbors s) hn

end GraphicalZonotopes.SaturatedDirections

end
end
end BundlePart314

section BundlePart315
/- Source: Papers/GraphicalZonotopes/MatchingPureModules.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes.BooleanModule
open Finset
variable {H : Type*} [Fintype H] [LinearOrder H]

def pairVertices {C : Finset H} (e : PairIn C) : Finset H := {e.1.1.1,e.1.1.2}

theorem pairVertices_subset {C : Finset H} (e : PairIn C) : pairVertices e⊆C := by
  simp [pairVertices,insert_subset_iff,singleton_subset_iff,e.2.1,e.2.2]

theorem pairVertices_card {C : Finset H} (e : PairIn C) : (pairVertices e).card=2 :=
  card_pair (ne_of_lt e.1.2.1)

def IsPairMatching {C : Finset H} (A : Finset (PairIn C)) : Prop :=
  ∀ e∈A,∀ f∈A,e≠ f → Disjoint (pairVertices e) (pairVertices f)

def matchingBlocks {C : Finset H} (A : Finset (PairIn C)) : Finset (Finset H) :=
  A.image pairVertices ∪ (C.filter (fun a => ∀ e∈A,a∉pairVertices e)).image singleton

theorem mem_matchingBlocks {C : Finset H} (A : Finset (PairIn C)) (B : Finset H) :
    B∈matchingBlocks A ↔
      (∃ e∈A,B=pairVertices e) ∨
      ∃ a∈C,(∀ e∈A,a∉pairVertices e) ∧ B={a} := by
  simp only [matchingBlocks,mem_union,mem_image,mem_filter]
  constructor
  · rintro (⟨e,he,rfl⟩ | ⟨a,⟨ha,hn⟩,rfl⟩)
    · exact Or.inl ⟨e,he,rfl⟩
    · exact Or.inr ⟨a,ha,hn,rfl⟩
  · rintro (⟨e,he,rfl⟩ | ⟨a,ha,hn,rfl⟩)
    · exact Or.inl ⟨e,he,rfl⟩
    · exact Or.inr ⟨a,⟨ha,hn⟩,rfl⟩

theorem matchingBlocks_cover {C : Finset H} (A : Finset (PairIn C)) {a : H}
    (ha : a∈C) : ∃ B∈matchingBlocks A,a∈B := by
  by_cases he : ∃ e∈A,a∈pairVertices e
  · obtain ⟨e,he,hae⟩ := he
    exact ⟨pairVertices e,(mem_matchingBlocks A _).mpr (Or.inl ⟨e,he,rfl⟩),hae⟩
  · have hn : ∀ e∈A,a∉pairVertices e := by simpa only [not_exists,not_and] using he
    exact ⟨{a},(mem_matchingBlocks A _).mpr (Or.inr ⟨a,ha,hn,rfl⟩),mem_singleton_self _⟩

theorem matchingBlocks_subset {C : Finset H} (A : Finset (PairIn C))
    {B : Finset H} (hB : B∈matchingBlocks A) : B⊆C := by
  rcases (mem_matchingBlocks A B).mp hB with ⟨e,he,rfl⟩ | ⟨a,ha,hn,rfl⟩
  · exact pairVertices_subset e
  · exact singleton_subset_iff.mpr ha

theorem matchingBlocks_card_le_two {C : Finset H} (A : Finset (PairIn C))
    {B : Finset H} (hB : B∈matchingBlocks A) : B.card≤2 := by
  rcases (mem_matchingBlocks A B).mp hB with ⟨e,he,rfl⟩ | ⟨a,ha,hn,rfl⟩
  · rw [pairVertices_card]
  · simp

theorem matchingBlocks_family {C : Finset H} (hC : 3≤ C.card)
    (A : Finset (PairIn C)) (hA : IsPairMatching A) :
    ComplementFamily C (matchingBlocks A) := by
  refine ⟨?_,fun B hB => matchingBlocks_subset A hB,?_,?_⟩
  · by_contra hh
    have hcard : (matchingBlocks A).card≤1 := by omega
    obtain ⟨a,ha⟩ := card_pos.mp (by omega : 0< C.card)
    obtain ⟨B,hB,haB⟩ := matchingBlocks_cover A ha
    have hsub : C⊆B := by
      intro b hb
      obtain ⟨D,hD,hbD⟩ := matchingBlocks_cover A hb
      have he : D=B := (card_le_one.mp hcard) D hD B hB
      exact he ▸ hbD
    have hc := (card_le_card hsub).trans (matchingBlocks_card_le_two A hB)
    omega
  · intro B hB
    rcases (mem_matchingBlocks A B).mp hB with ⟨e,he,rfl⟩ | ⟨a,ha,hn,rfl⟩
    · exact ⟨e.1.1.1,by simp [pairVertices]⟩
    · exact singleton_nonempty _
  · intro B hB D hD hBD
    rcases (mem_matchingBlocks A B).mp hB with ⟨e,he,rfl⟩ | ⟨a,ha,hn,rfl⟩
    · rcases (mem_matchingBlocks A D).mp hD with ⟨f,hf,rfl⟩ | ⟨b,hb,hm,rfl⟩
      · exact hA e he f hf (fun h => hBD (congrArg pairVertices h))
      · exact disjoint_singleton_right.mpr (hm e he)
    · rcases (mem_matchingBlocks A D).mp hD with ⟨f,hf,rfl⟩ | ⟨b,hb,hm,rfl⟩
      · exact disjoint_singleton_left.mpr (hn f hf)
      · exact disjoint_singleton.mpr (fun h => hBD (congrArg singleton h))

theorem pairVertices_membership {C : Finset H} (e f : PairIn C) :
    (e.1.1.1∈pairVertices f ∧ e.1.1.2∈pairVertices f) ↔ e=f := by
  rw [pairVertices,ordered_pair_membership e.1.2.1 f.1.2.1]
  constructor
  · rintro ⟨hu,hv⟩
    exact Subtype.ext (Subtype.ext (Prod.ext hu hv))
  · rintro rfl
    exact ⟨rfl,rfl⟩

theorem crosses_matchingBlocks {C : Finset H} (hC : 3≤ C.card)
    (A : Finset (PairIn C)) (hA : IsPairMatching A) (e : PairIn C) :
    Crosses (matchingBlocks A) e.1.1.1 e.1.1.2 ↔ e∉A := by
  let hf := matchingBlocks_family hC A hA
  constructor
  · rintro ⟨B,hB,D,hD,hBD,hu,hv⟩ he
    have hE := (mem_matchingBlocks A (pairVertices e)).mpr (Or.inl ⟨e,he,rfl⟩)
    have hBE := hf.shared_mem_eq hB hE hu (by simp [pairVertices])
    have hDE := hf.shared_mem_eq hD hE hv (by simp [pairVertices])
    exact hBD (hBE.trans hDE.symm)
  · intro he
    obtain ⟨B,hB,hu⟩ := matchingBlocks_cover A e.2.1
    obtain ⟨D,hD,hv⟩ := matchingBlocks_cover A e.2.2
    refine ⟨B,hB,D,hD,?_,hu,hv⟩
    intro hBD
    have hvB : e.1.1.2∈B := hBD.symm ▸ hv
    rcases (mem_matchingBlocks A B).mp hB with ⟨f,hf,rfl⟩ | ⟨a,ha,hn,rfl⟩
    · have hef := (pairVertices_membership e f).mp ⟨hu,hvB⟩
      exact he (hef.symm ▸ hf)
    · have heq : e.1.1.1=e.1.1.2 := (mem_singleton.mp hu).trans (mem_singleton.mp hvB).symm
      exact (ne_of_lt e.1.2.1) heq

/-- Every matching gives an actual all-essential pure Boolean response equal
to its negative edge indicator, modulo the diagonal clique coefficient. -/
theorem pureRealizable_negative_matching {C : Finset H} (hC : 3≤ C.card)
    (A : Finset (PairIn C)) (hA : IsPairMatching A) :
    PureRealizable C (-pairIndicator A) := by
  classical
  let hf := matchingBlocks_family hC A hA
  refine ⟨complementModule C (matchingBlocks A),hf.module_boolean,
    fun a ha => hf.essential ha,
    fun a ha S => complementModule_ignores_outside C _ ha S,?_⟩
  rw [responseClass_eq_coefficientClass,complementModule_response_coefficients hf]
  have hcoord : (fun r : HubResponseRow H =>
      if rowClique r=C ∧ Crosses (matchingBlocks A) r.1.1.1 r.1.1.2 then (1 : ℝ) else 0)=
      blockCoordinates C (fun e => 1-pairIndicator A e) := by
    funext r
    by_cases hr : rowClique r=C
    · have hc := crosses_matchingBlocks hC A hA (pairAtRow C r hr)
      change (if rowClique r=C ∧ _ then (1 : ℝ) else 0)=
        if h : rowClique r=C then 1-pairIndicator A (pairAtRow C r h) else 0
      rw [dif_pos hr]
      simp only [hr,true_and]
      change (if Crosses (matchingBlocks A) (pairAtRow C r hr).1.1.1
        (pairAtRow C r hr).1.1.2 then (1 : ℝ) else 0)=_
      rw [hc]
      by_cases he : pairAtRow C r hr∈A <;> simp [pairIndicator,he]
    · simp [blockCoordinates,hr]
  rw [hcoord]
  change blockClass C (fun e => 1-pairIndicator A e)=_
  have hfun : (fun e : PairIn C => (1 : ℝ)-pairIndicator A e)=
      (fun _ => (1 : ℝ))+(-pairIndicator A) := by rfl
  have hz : blockClass C (fun _ : PairIn C => (1 : ℝ))=0 := by
    change coefficientClass (blockCoordinates C (fun _ => 1))=0
    have hco : blockCoordinates C (fun _ : PairIn C => (1 : ℝ))=
        fun r : HubResponseRow H => if rowClique r=C then 1 else 0 := by
      funext r
      change (if _h : rowClique r=C then (1 : ℝ) else 0)=_
      split <;> rfl
    rw [hco]
    exact coefficientClass_block_zero C
  rw [hfun,map_add,hz,zero_add]

end GraphicalZonotopes.BooleanModule

end
end
end BundlePart315

section BundlePart316
/- Source: Papers/GraphicalZonotopes/SaturatedBookPartition.lean -/






@[expose] public section
noncomputable section
namespace GraphicalZonotopes.BooleanModule.Saturated
open Finset
open scoped BigOperators

abbrev HubPair (s : ℕ) := PairIn (univ : Finset (Fin s))

def natPair {s : ℕ} (i j : ℕ) (hij : i< j) (hj : j< s) : HubPair s :=
  orderedPair univ ⟨i,lt_trans hij hj⟩ ⟨j,hj⟩ hij (mem_univ _) (mem_univ _)

def pairSum {s : ℕ} (e : HubPair s) : ℕ := e.1.1.1.val+e.1.1.2.val

def Retained {s : ℕ} (e : HubPair s) : Prop :=
  ¬(e.1.1.1.val=0 ∧ e.1.1.2.val=1) ∧
  ¬(e.1.1.1.val=1 ∧ e.1.1.2.val< s-1) ∧
  ¬(e.1.1.1.val=2 ∧ e.1.1.2.val=3)

instance {s : ℕ} (e : HubPair s) : Decidable (Retained e) := inferInstanceAs
  (Decidable (¬(e.1.1.1.val=0 ∧ e.1.1.2.val=1) ∧
    ¬(e.1.1.1.val=1 ∧ e.1.1.2.val< s-1) ∧
    ¬(e.1.1.1.val=2 ∧ e.1.1.2.val=3)))

def retainedPairs (s : ℕ) : Finset (HubPair s) := univ.filter Retained

@[simp] theorem mem_retainedPairs {s : ℕ} {e : HubPair s} :
    e∈retainedPairs s ↔ Retained e := by simp [retainedPairs]

def referencePair {s : ℕ} (hs : 2≤ s) : HubPair s := natPair 0 1 (by omega) (by omega)

theorem pair_eq_reference {s : ℕ} (hs : 2≤ s) (e : HubPair s) :
    e=referencePair hs ↔ e.1.1.1.val=0 ∧ e.1.1.2.val=1 := by
  constructor
  · rintro rfl
    exact ⟨rfl,rfl⟩
  · rintro ⟨hu,hv⟩
    exact Subtype.ext (Subtype.ext (Prod.ext (Fin.ext hu) (Fin.ext hv)))

abbrev ActivePair {s : ℕ} (hs : 2≤ s) := {e : HubPair s // e≠ referencePair hs}

def groupPair {s : ℕ} (hs : 5≤ s) (e : ActivePair (show 2≤ s by omega)) : HubPair s :=
  if h : e.1.1.1.1.val=1 ∧ e.1.1.1.2.val< s-1 then
    natPair 0 (1+e.1.1.1.2.val) (by omega) (by omega)
  else if h : e.1.1.1.1.val=2 ∧ e.1.1.1.2.val=3 then
    if hs6 : 6≤ s then natPair 0 5 (by omega) (by omega)
    else natPair 1 4 (by omega) (by omega)
  else e.1

theorem groupPair_retained {s : ℕ} (hs : 5≤ s)
    (e : ActivePair (show 2≤ s by omega)) : Retained (groupPair hs e) := by
  have huv : e.1.1.1.1.val< e.1.1.1.2.val := e.1.1.2.1
  have hne : ¬(e.1.1.1.1.val=0 ∧ e.1.1.1.2.val=1) := by
    intro h
    exact e.2 ((pair_eq_reference (show 2≤ s by omega) e.1).mpr h)
  unfold groupPair
  split_ifs with h1 h2 h6
  · simp only [Retained,natPair,orderedPair]
    omega
  · simp only [Retained,natPair,orderedPair]
    omega
  · simp only [Retained,natPair,orderedPair]
    omega
  · exact ⟨hne,h1,h2⟩

theorem groupPair_sum {s : ℕ} (hs : 5≤ s)
    (e : ActivePair (show 2≤ s by omega)) : pairSum (groupPair hs e)=pairSum e.1 := by
  unfold groupPair
  split_ifs with h1 h2 h6 <;> simp only [pairSum,natPair,orderedPair] <;> omega

theorem retained_not_reference {s : ℕ} (hs : 2≤ s) {e : HubPair s}
    (he : Retained e) : e≠ referencePair hs := by
  intro h
  exact he.1 ((pair_eq_reference hs e).mp h)

theorem groupPair_of_retained {s : ℕ} (hs : 5≤ s) {e : HubPair s} (he : Retained e) :
    groupPair hs ⟨e,retained_not_reference (by omega) he⟩=e := by
  simp only [groupPair,he.2.1,he.2.2,dite_false]

def group {s : ℕ} (hs : 5≤ s) (r : ↥(retainedPairs s)) : Finset (HubPair s) :=
  univ.filter (fun e => ∃ h : e≠ referencePair (show 2≤ s by omega),groupPair hs ⟨e,h⟩=r.1)

theorem mem_group {s : ℕ} (hs : 5≤ s) (r : ↥(retainedPairs s)) (e : HubPair s) :
    e∈group hs r ↔ ∃ h : e≠ referencePair (show 2≤ s by omega),groupPair hs ⟨e,h⟩=r.1 := by
  classical
  simp only [group,mem_filter,mem_univ,true_and]

theorem group_nonempty {s : ℕ} (hs : 5≤ s) (r : ↥(retainedPairs s)) :
    (group hs r).Nonempty := by
  refine ⟨r.1,(mem_group hs r r.1).mpr ?_⟩
  have hr := mem_retainedPairs.mp r.2
  exact ⟨retained_not_reference (by omega) hr,groupPair_of_retained hs hr⟩

theorem group_reference_not_mem {s : ℕ} (hs : 5≤ s) (r : ↥(retainedPairs s)) :
    referencePair (show 2≤ s by omega)∉group hs r := by
  intro h
  obtain ⟨hn,_⟩ := (mem_group hs r _).mp h
  exact hn rfl

theorem group_pairSum {s : ℕ} (hs : 5≤ s) (r : ↥(retainedPairs s))
    {e : HubPair s} (he : e∈group hs r) : pairSum e=pairSum r.1 := by
  obtain ⟨hn,hg⟩ := (mem_group hs r e).mp he
  rw [←hg,groupPair_sum]

theorem equal_sum_matching {s : ℕ} (A : Finset (HubPair s)) (t : ℕ)
    (hA : ∀ e∈A,pairSum e=t) : IsPairMatching A := by
  intro e he f hf hne
  apply disjoint_left.mpr
  intro a hae haf
  have hsum : e.1.1.1.val+e.1.1.2.val=f.1.1.1.val+f.1.1.2.val :=
    (hA e he).trans (hA f hf).symm
  have heord : e.1.1.1.val< e.1.1.2.val := e.1.2.1
  have hford : f.1.1.1.val< f.1.1.2.val := f.1.2.1
  simp only [pairVertices,mem_insert,mem_singleton] at hae haf
  apply hne
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext
  all_goals rcases hae with hae | hae <;> rcases haf with haf | haf
  all_goals have haev := congrArg Fin.val hae
  all_goals have hafv := congrArg Fin.val haf
  all_goals omega

theorem group_matching {s : ℕ} (hs : 5≤ s) (r : ↥(retainedPairs s)) :
    IsPairMatching (group hs r) :=
  equal_sum_matching _ (pairSum r.1) (fun _ he => group_pairSum hs r he)

theorem group_realizable {s : ℕ} (hs : 5≤ s) (r : ↥(retainedPairs s)) :
    PureRealizable (univ : Finset (Fin s)) (-pairIndicator (group hs r)) :=
  pureRealizable_negative_matching (by simpa using (show 3≤ s by omega)) _
    (group_matching hs r)

theorem group_unique {s : ℕ} (hs : 5≤ s) (r t : ↥(retainedPairs s))
    {e : HubPair s} (hr : e∈group hs r) (ht : e∈group hs t) : r=t := by
  obtain ⟨hn,he⟩ := (mem_group hs r e).mp hr
  obtain ⟨hm,hf⟩ := (mem_group hs t e).mp ht
  exact Subtype.ext (he.symm.trans hf)

theorem group_cover {s : ℕ} (hs : 5≤ s) (e : HubPair s)
    (he : e≠ referencePair (show 2≤ s by omega)) : ∃ r : ↥(retainedPairs s),e∈group hs r := by
  let r : ↥(retainedPairs s) := ⟨groupPair hs ⟨e,he⟩,
    mem_retainedPairs.mpr (groupPair_retained hs ⟨e,he⟩)⟩
  exact ⟨r,(mem_group hs r e).mpr ⟨he,rfl⟩⟩

end GraphicalZonotopes.BooleanModule.Saturated

end
end
end BundlePart316

section BundlePart317
/- Source: Papers/GraphicalZonotopes/SaturatedBookPartitionCount.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes.BooleanModule.Saturated
open Finset
open scoped BigOperators

variable {s : ℕ}

def lastHub (hs : 1≤ s) : Fin s := ⟨s-1,by omega⟩
def oneHub (hs : 2≤ s) : Fin s := ⟨1,by omega⟩

def omittedStar (hs : 5≤ s) : Finset (HubPair s) :=
  starPairs univ (oneHub (by omega))
    (((univ : Finset (Fin s)).erase (oneHub (by omega))).erase (lastHub (by omega)))

theorem mem_omittedStar (hs : 5≤ s) (e : HubPair s) :
    e∈omittedStar hs ↔
      (e.1.1.1.val=0 ∧ e.1.1.2.val=1) ∨
      (e.1.1.1.val=1 ∧ e.1.1.2.val< s-1) := by
  have huv : e.1.1.1.val< e.1.1.2.val := e.1.2.1
  have hub := e.1.1.2.isLt
  have hone : (oneHub (show 2≤ s by omega)).val=1 := rfl
  have hlast : (lastHub (show 1≤ s by omega)).val=s-1 := rfl
  simp only [omittedStar,mem_starPairs,StarPair,mem_erase,mem_univ,and_true,
    Fin.ext_iff,hone,hlast]
  dsimp
  omega

theorem omittedStar_card (hs : 5≤ s) : (omittedStar hs).card=s-2 := by
  rw [omittedStar,starPairs_card _ (mem_univ _) (subset_univ _) (by simp)]
  have hne : lastHub (show 1≤ s by omega)≠ oneHub (show 2≤ s by omega) := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [lastHub,oneHub] at hv
    omega
  rw [card_erase_of_mem (by simp [hne]),card_erase_of_mem (mem_univ _),card_univ]
  simp only [Fintype.card_fin]
  omega

theorem retainedPairs_eq_sdiff (hs : 5≤ s) :
    retainedPairs s=univ\(insert (natPair 2 3 (by omega) (by omega)) (omittedStar hs)) := by
  ext e
  simp only [mem_retainedPairs,mem_sdiff,mem_univ,true_and,mem_insert,mem_omittedStar]
  have heq : e=natPair 2 3 (by omega) (by omega) ↔
      e.1.1.1.val=2 ∧ e.1.1.2.val=3 := by
    constructor
    · rintro rfl
      exact ⟨rfl,rfl⟩
    · rintro ⟨hu,hv⟩
      exact Subtype.ext (Subtype.ext (Prod.ext (Fin.ext hu) (Fin.ext hv)))
  rw [heq]
  unfold Retained
  tauto

theorem retainedPairs_card (hs : 5≤ s) : (retainedPairs s).card=s.choose 2-(s-1) := by
  rw [retainedPairs_eq_sdiff hs,card_sdiff_of_subset (subset_univ _),
    card_insert_of_notMem]
  · rw [omittedStar_card hs,card_univ,pairIn_card,card_univ]
    simp only [Fintype.card_fin]
    congr 1
    omega
  · rw [mem_omittedStar]
    simp only [natPair,orderedPair]
    omega

theorem retained_count_add_anchors (hs : 5≤ s) :
    (s-1)+(retainedPairs s).card=s.choose 2 := by
  rw [retainedPairs_card hs]
  have hchoose : s-1≤ s.choose 2 := by
    rw [Nat.choose_two_right]
    apply (Nat.le_div_iff_mul_le (by decide : 0<2)).mpr
    calc
      (s-1)*2≤(s-1)*s := Nat.mul_le_mul_left _ (by omega)
      _ = s*(s-1) := Nat.mul_comm _ _
  omega

end GraphicalZonotopes.BooleanModule.Saturated

end
end
end BundlePart317

section BundlePart318
/- Source: Papers/GraphicalZonotopes/SaturatedBookRigidity.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes.BooleanModule.Saturated
open Finset
open scoped BigOperators
variable {s : ℕ}

def activeNatPair (hs : 5≤ s) (i j : ℕ) (hij : i< j) (hj : j< s)
    (hne : ¬(i=0 ∧ j=1)) : ActivePair (show 2≤ s by omega) :=
  ⟨natPair i j hij hj,by
    intro h
    exact hne ((pair_eq_reference (show 2≤ s by omega) _).mp h)⟩

theorem groupPair_03_12 (hs : 5≤ s) :
    groupPair hs (activeNatPair hs 0 3 (by omega) (by omega) (by omega))=
    groupPair hs (activeNatPair hs 1 2 (by omega) (by omega) (by omega)) := by
  simp [groupPair,activeNatPair,natPair,orderedPair,(show 2< s-1 by omega)]

theorem groupPair_04_13 (hs : 5≤ s) :
    groupPair hs (activeNatPair hs 0 4 (by omega) (by omega) (by omega))=
    groupPair hs (activeNatPair hs 1 3 (by omega) (by omega) (by omega)) := by
  simp [groupPair,activeNatPair,natPair,orderedPair,(show 3< s-1 by omega)]

theorem groupPair_14_23 (hs : 5≤ s) :
    groupPair hs (activeNatPair hs 1 4 (by omega) (by omega) (by omega))=
    groupPair hs (activeNatPair hs 2 3 (by omega) (by omega) (by omega)) := by
  by_cases hs6 : 6≤ s
  · simp [groupPair,activeNatPair,natPair,orderedPair,hs6,(show 4< s-1 by omega)]
  · have hs5 : s=5 := by omega
    subst s
    simp [groupPair,activeNatPair,natPair,orderedPair]

theorem groupPair_step (hs : 5≤ s) (j : ℕ) (hj : 5≤ j) (hjs : j< s) :
    groupPair hs (activeNatPair hs 0 j (by omega) hjs (by omega))=
    groupPair hs (activeNatPair hs 1 (j-1) (by omega) (by omega) (by omega)) := by
  have he : 1+(j-1)=j := by omega
  simp [groupPair,activeNatPair,natPair,orderedPair,he,(show j≠1 by omega),
    (show j-1< s-1 by omega)]

/-- The matching partition retains exactly the endpoint comparisons needed
for full arithmetic-progression rigidity; all other pair pieces may be split. -/
theorem grouped_endpoint_rigidity (hs : 5≤ s) (d : Fin s → ℝ)
    (h0 : d ⟨0,by omega⟩=0)
    (hgroup : ∀ e f : ActivePair (show 2≤ s by omega),groupPair hs e=groupPair hs f →
      d e.1.1.1.1+d e.1.1.1.2=d f.1.1.1.1+d f.1.1.1.2) :
    ∀ a : Fin s,d a=(a.val : ℝ)*d ⟨1,by omega⟩ := by
  let D : ℕ → ℝ := fun j => if h : j< s then d ⟨j,h⟩ else 0
  have hD : ∀ j : Fin s,D j.val=d j := by
    intro j
    simp only [D,dite_eq_left j.isLt]
  have h03 : D 0+D 3=D 1+D 2 := by
    have h := hgroup _ _ (groupPair_03_12 hs)
    simpa [D,activeNatPair,natPair,orderedPair,(show 0< s by omega),(show 1< s by omega),
      (show 2< s by omega),(show 3< s by omega)] using h
  have h04 : D 0+D 4=D 1+D 3 := by
    have h := hgroup _ _ (groupPair_04_13 hs)
    simpa [D,activeNatPair,natPair,orderedPair,(show 0< s by omega),(show 1< s by omega),
      (show 3< s by omega),(show 4< s by omega)] using h
  have h14 : D 1+D 4=D 2+D 3 := by
    have h := hgroup _ _ (groupPair_14_23 hs)
    simpa [D,activeNatPair,natPair,orderedPair,(show 1< s by omega),(show 2< s by omega),
      (show 3< s by omega),(show 4< s by omega)] using h
  have hstep : ∀ j,5≤ j → j< s → D 0+D j=D 1+D (j-1) := by
    intro j hj hjs
    have h := hgroup _ _ (groupPair_step hs j hj hjs)
    simpa [D,activeNatPair,natPair,orderedPair,(show 0< s by omega),(show 1< s by omega),
      hjs,(show j-1< s by omega)] using h
  have h := quadrilateral_endpoint_rigidity s hs D
    (by simpa [D,(show 0< s by omega)] using h0) h03 h04 h14 hstep
  intro a
  have ha := h a.val a.isLt
  rw [hD a] at ha
  simpa [D,(show 1< s by omega)] using ha

def groupIndex (hs : 5≤ s) (e : ActivePair (show 2≤ s by omega)) : ↥(retainedPairs s) :=
  ⟨groupPair hs e,mem_retainedPairs.mpr (groupPair_retained hs e)⟩

theorem mem_group_iff (hs : 5≤ s) (e : ActivePair (show 2≤ s by omega))
    (r : ↥(retainedPairs s)) : e.1∈group hs r ↔ r=groupIndex hs e := by
  rw [mem_group]
  constructor
  · rintro ⟨hn,hg⟩
    exact Subtype.ext hg.symm
  · rintro rfl
    exact ⟨e.2,rfl⟩

theorem sum_group_indicator (hs : 5≤ s) (w : ↥(retainedPairs s) → ℝ)
    (e : ActivePair (show 2≤ s by omega)) :
    (∑ r : ↥(retainedPairs s),w r*pairIndicator (group hs r) e.1)=w (groupIndex hs e) := by
  simp only [pairIndicator,mem_group_iff,mul_ite,mul_one,mul_zero,
    sum_ite_eq',mem_univ,ite_true]

theorem sum_group_indicator_reference (hs : 5≤ s) (w : ↥(retainedPairs s) → ℝ) :
    (∑ r : ↥(retainedPairs s),w r*pairIndicator (group hs r) (referencePair (show 2≤ s by omega)))=0 := by
  simp only [pairIndicator,group_reference_not_mem,ite_false,mul_zero,sum_const_zero]

/-- Every zero full-block relation has the prescribed positive scales. -/
theorem full_block_unique (hs : 5≤ s) (d : Fin s → ℝ)
    (h0 : d ⟨0,by omega⟩=0) (w : ↥(retainedPairs s) → ℝ)
    (hz : blockClass (univ : Finset (Fin s))
      (endpointCoefficients univ d-∑ r : ↥(retainedPairs s),w r • pairIndicator (group hs r))=0) :
    (∀ a : Fin s,d a=(a.val : ℝ)*d ⟨1,by omega⟩) ∧
    (∀ r : ↥(retainedPairs s),w r=((pairSum r.1 : ℝ)-1)*d ⟨1,by omega⟩) := by
  obtain ⟨c,hc⟩ := (blockClass_eq_zero_iff univ (referencePair (show 2≤ s by omega)) _).mp hz
  have hrow : ∀ e : HubPair s,d e.1.1.1+d e.1.1.2-
      ∑ r : ↥(retainedPairs s),w r*pairIndicator (group hs r) e=c := by
    intro e
    simpa only [Pi.sub_apply,endpointCoefficients,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using hc e
  have hc1 : c=d ⟨1,by omega⟩ := by
    have h := hrow (referencePair (show 2≤ s by omega))
    rw [sum_group_indicator_reference] at h
    change d ⟨0,by omega⟩+d ⟨1,by omega⟩-0=c at h
    simpa only [h0,zero_add,sub_zero] using h.symm
  have hactive : ∀ e : ActivePair (show 2≤ s by omega),
      d e.1.1.1.1+d e.1.1.1.2-w (groupIndex hs e)=c := by
    intro e
    simpa only [sum_group_indicator] using hrow e.1
  have hd := grouped_endpoint_rigidity hs d h0 (by
    intro e f hef
    have hidx : groupIndex hs e=groupIndex hs f := Subtype.ext hef
    have he := hactive e
    have hf := hactive f
    rw [hidx] at he
    linarith)
  refine ⟨hd,?_⟩
  intro r
  have hr := mem_retainedPairs.mp r.2
  let e : ActivePair (show 2≤ s by omega) := ⟨r.1,retained_not_reference (by omega) hr⟩
  have hidx : groupIndex hs e=r := Subtype.ext (groupPair_of_retained hs hr)
  have h := hactive e
  rw [hidx,hc1] at h
  change d r.1.1.1.1+d r.1.1.1.2-w r=d ⟨1,by omega⟩ at h
  simp only [pairSum,Nat.cast_add]
  nlinarith [hd r.1.1.1.1,hd r.1.1.1.2]

end GraphicalZonotopes.BooleanModule.Saturated

end
end
end BundlePart318

section BundlePart319
/- Source: Papers/GraphicalZonotopes/SaturatedPairBases.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes.BooleanModule
open Finset
open scoped BigOperators

/-- Distinct numerical hub labels have a unique largest endpoint sum: the
pair of the two largest vertices of the clique. -/
theorem exists_unique_maximum_label_pair {s : ℕ} (C : Finset (Fin s)) (hC : 3≤ C.card) :
    ∃ e₀ : PairIn C,∀ e : PairIn C,e≠ e₀ → endpointLabels C e< endpointLabels C e₀ := by
  have hne : C.Nonempty := card_pos.mp (by omega)
  let m := C.max' hne
  have hm : m∈C := max'_mem C hne
  have hecard : 2≤(C.erase m).card := by rw [card_erase_of_mem hm]; omega
  have hene : (C.erase m).Nonempty := card_pos.mp (by omega)
  let n := (C.erase m).max' hene
  have hn : n∈C.erase m := max'_mem _ hene
  have hnC := (mem_erase.mp hn).2
  have hnm : n< m := lt_of_le_of_ne (le_max' C n hnC) (mem_erase.mp hn).1
  let e₀ := orderedPair C n m hnm hnC hm
  refine ⟨e₀,?_⟩
  intro e he
  have hv : e.1.1.2≤ m := le_max' C _ e.2.2
  have hu : e.1.1.1< m := lt_of_lt_of_le e.1.2.1 hv
  have huErase : e.1.1.1∈C.erase m := mem_erase.mpr ⟨ne_of_lt hu,e.2.1⟩
  have hun : e.1.1.1≤ n := le_max' _ _ huErase
  have heq : ¬(e.1.1.1=n ∧ e.1.1.2=m) := by
    rintro ⟨hu,hv⟩
    exact he (Subtype.ext (Subtype.ext (Prod.ext hu hv)))
  have hun' : e.1.1.1.val≤ n.val := hun
  have hvm' : e.1.1.2.val≤ m.val := hv
  have heq' : ¬(e.1.1.1.val=n.val ∧ e.1.1.2.val=m.val) := by
    rintro ⟨hu,hv⟩
    exact heq ⟨Fin.ext hu,Fin.ext hv⟩
  have hh : e.1.1.1.val+e.1.1.2.val< n.val+m.val := by omega
  change (e.1.1.1.val : ℝ)+(e.1.1.2.val : ℝ)<(n.val : ℝ)+(m.val : ℝ)
  exact_mod_cast hh

/-- Every clique block admits a full independent signed pair basis cancelling
any signed endpoint-label vector, with positive integral scales. -/
theorem saturated_pair_basis {s : ℕ} (C : Finset (Fin s)) (hC : 3≤ C.card)
    (ε : ℝ) (hε : ε=1 ∨ ε= -1) :
    Nonempty (WeightedPureBlock C (2*s : ℕ) (ε • blockClass C (endpointLabels C))
      (C.card.choose 2-1)) := by
  obtain ⟨e₀,he₀⟩ := exists_unique_maximum_label_pair C hC
  let w : PairIn C → ℤ := fun e =>
    ((e₀.1.1.1.val : ℤ)+(e₀.1.1.2.val : ℤ))-((e.1.1.1.val : ℤ)+(e.1.1.2.val : ℤ))
  have hw0 : w e₀=0 := by simp [w]
  have hwp : ∀ e,e≠ e₀ → 0< w e := by
    intro e he
    dsimp only [w]
    apply sub_pos.mpr
    have hh := he₀ e he
    unfold endpointLabels at hh
    exact_mod_cast hh
  have hwb : ∀ e,w e≤(2*s : ℕ) := by
    intro e
    have h1 := e₀.1.1.1.isLt
    have h2 := e₀.1.1.2.isLt
    dsimp [w,endpointLabels]
    push_cast
    omega
  have hε' : -ε=1 ∨ -ε= -1 := by rcases hε with rfl | rfl <;> norm_num
  let P := signed_pair_basis C hC e₀ (-ε) hε' w hw0 hwp (2*s : ℕ) (fun e _ => hwb e)
  have hfun : (fun e : PairIn C => (w e : ℝ))=
      (fun _ : PairIn C => (endpointLabels C e₀ : ℝ))-
      (fun e : PairIn C => (endpointLabels C e : ℝ)) := by
    funext e
    simp [w,endpointLabels]
  have hz : blockClass C (fun _ : PairIn C => (endpointLabels C e₀ : ℝ))=0 :=
    (blockClass_eq_zero_iff C e₀ _).mpr ⟨_,fun _ => rfl⟩
  have ht : blockClass C ((-ε) • fun e : PairIn C => (w e : ℝ))=
      ε • blockClass C (fun e => (endpointLabels C e : ℝ)) := by
    rw [hfun,map_smul,map_sub,hz,zero_sub]
    simp
  exact ⟨ht ▸ P⟩

end GraphicalZonotopes.BooleanModule

end
end
end BundlePart319

section BundlePart320
/- Source: Papers/GraphicalZonotopes/SaturatedFullBlock.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes.BooleanModule.Saturated
open Finset
open scoped BigOperators
variable {s : ℕ}

def matchingEquiv (s : ℕ) : Fin (retainedPairs s).card ≃ ↥(retainedPairs s) :=
  (finCongr (Fintype.card_coe (retainedPairs s)).symm).trans (Fintype.equivFin _).symm

def matchingWeight (r : ↥(retainedPairs s)) : ℤ := (pairSum r.1 : ℤ)-1

theorem matchingWeight_positive (r : ↥(retainedPairs s)) : 0< matchingWeight r := by
  have hr := mem_retainedPairs.mp r.2
  have huv : r.1.1.1.1.val< r.1.1.1.2.val := r.1.1.2.1
  have hn := hr.1
  dsimp [matchingWeight,pairSum]
  push_cast
  omega

theorem matchingWeight_bound (r : ↥(retainedPairs s)) : matchingWeight r≤(2*s : ℕ) := by
  have hu := r.1.1.1.1.isLt
  have hv := r.1.1.1.2.isLt
  dsimp [matchingWeight,pairSum]
  push_cast
  omega

theorem matching_vectors_independent (hs : 5≤ s) :
    LinearIndependent ℝ (fun r : ↥(retainedPairs s) => -pairIndicator (group hs r)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc r
  have hr := mem_retainedPairs.mp r.2
  have hmem : ∀ t : ↥(retainedPairs s),r.1∈group hs t ↔ t=r := by
    intro t
    let e : ActivePair (show 2≤ s by omega) := ⟨r.1,retained_not_reference (by omega) hr⟩
    have hidx : groupIndex hs e=r := Subtype.ext (groupPair_of_retained hs hr)
    exact (mem_group_iff hs e t).trans (by rw [hidx])
  have h := congrFun hc r.1
  simp only [Finset.sum_apply,Pi.smul_apply,Pi.neg_apply,Pi.zero_apply,smul_eq_mul,
    pairIndicator,hmem,neg_ite,neg_zero,mul_ite,mul_zero,sum_ite_eq',mem_univ,ite_true] at h
  linarith

theorem matching_classes_independent (hs : 5≤ s) :
    LinearIndependent ℝ (fun r : ↥(retainedPairs s) =>
      blockClass univ (-pairIndicator (group hs r))) := by
  apply blockClass_linearIndependent_of_reference univ (referencePair (show 2≤ s by omega))
    _ (matching_vectors_independent hs)
  intro r
  simp [pairIndicator,group_reference_not_mem]

theorem matching_weighted_vector (hs : 5≤ s) :
    (∑ r : ↥(retainedPairs s),(matchingWeight r : ℝ) • (-pairIndicator (group hs r)))=
      (fun _ : HubPair s => (1 : ℝ))-endpointLabels univ := by
  funext e
  simp only [Finset.sum_apply,Pi.smul_apply,Pi.neg_apply,Pi.sub_apply,smul_eq_mul,mul_neg,sum_neg_distrib]
  by_cases he : e=referencePair (show 2≤ s by omega)
  · subst e
    rw [sum_group_indicator_reference]
    norm_num [endpointLabels,referencePair,natPair,orderedPair]
  · let a : ActivePair (show 2≤ s by omega) := ⟨e,he⟩
    rw [show (∑ r : ↥(retainedPairs s),(matchingWeight r : ℝ)*pairIndicator (group hs r) e)=
      (matchingWeight (groupIndex hs a) : ℝ) from sum_group_indicator hs _ a]
    have hsum := groupPair_sum hs a
    change pairSum (groupIndex hs a).1=pairSum e at hsum
    simp only [matchingWeight,Int.cast_sub,Int.cast_natCast,Int.cast_one]
    rw [hsum]
    simp only [pairSum,Nat.cast_add,endpointLabels]
    ring

theorem matching_weighted_class (hs : 5≤ s) :
    (∑ r : ↥(retainedPairs s),(matchingWeight r : ℝ) • blockClass univ (-pairIndicator (group hs r)))=
      -blockClass univ (endpointLabels univ) := by
  simp only [←map_smul,←map_sum]
  rw [matching_weighted_vector,map_sub]
  have hz : blockClass univ (fun _ : HubPair s => (1 : ℝ))=0 :=
    (blockClass_eq_zero_iff univ (referencePair (show 2≤ s by omega)) _).mpr ⟨1,fun _ => rfl⟩
  rw [hz,zero_sub]

def matchingPureBlock (hs : 5≤ s) :
    WeightedPureBlock (univ : Finset (Fin s)) (2*s : ℕ)
      (-blockClass univ (endpointLabels univ)) (retainedPairs s).card where
  column j := -pairIndicator (group hs (matchingEquiv s j))
  realizable j := group_realizable hs (matchingEquiv s j)
  weight j := matchingWeight (matchingEquiv s j)
  positive j := matchingWeight_positive _
  bounded j := matchingWeight_bound _
  independent := (matching_classes_independent hs).comp (matchingEquiv s) (matchingEquiv s).injective
  weighted_sum := ((matchingEquiv s).sum_comp _).trans (matching_weighted_class hs)

theorem matchingPureBlock_rigidity (hs : 5≤ s) (d : Fin s → ℝ)
    (h0 : d ⟨0,by omega⟩=0) (t : Fin (retainedPairs s).card → ℝ)
    (hz : blockClass (univ : Finset (Fin s))
      (endpointCoefficients univ d+∑ j,t j • (matchingPureBlock hs).column j)=0) :
    ∀ a : Fin s,d a=(a.val : ℝ)*d ⟨1,by omega⟩ := by
  let w : ↥(retainedPairs s) → ℝ := fun r => t ((matchingEquiv s).symm r)
  have he : (∑ j,t j • (matchingPureBlock hs).column j)=
      -(∑ r : ↥(retainedPairs s),w r • pairIndicator (group hs r)) := by
    change (∑ j,t j • (-pairIndicator (group hs (matchingEquiv s j))))=_
    simp only [smul_neg,sum_neg_distrib]
    congr 1
    have hh := (matchingEquiv s).sum_comp (fun r => w r • pairIndicator (group hs r))
    simpa only [w,Equiv.symm_apply_apply] using hh
  rw [he,←sub_eq_add_neg] at hz
  exact (full_block_unique hs d h0 w hz).1

end GraphicalZonotopes.BooleanModule.Saturated

end
end
end BundlePart320

section BundlePart321
/- Source: Papers/GraphicalZonotopes/ScopedBookGeometry.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.BooleanModule
open Finset
open scoped BigOperators

variable {H J : Type*} [Fintype H] [LinearOrder H] [Fintype J] [LinearOrder J]

local instance sumOrder : LinearOrder (H⊕J) := inferInstanceAs (LinearOrder (H⊕ₗJ))
local instance sumDecidableEq : DecidableEq (H⊕J) := (sumOrder (H:=H) (J:=J)).toDecidableEq

theorem assembled_actual_spoke_iff {z : SetFunction H} (hz : TranslationNormalized z)
    {F : J → SetFunction H} (hF : ∀ j,IsMonotoneBoolean (F j))
    {w : J → ℝ} (hw : ∀ j,0< w j) (hc : Compatible z F w)
    (scope : J → Finset H) (hessential : ∀ j a,a∈scope j → Essential (F j) a)
    (hignore : ∀ j a,a∉scope j → ∀ X,F j (insert a X)=F j X) (a : H) (j : J) :
    ActualRootEdge (basePolytope (assembled z F w)) (Sum.inl a) (Sum.inr j) ↔ a∈scope j := by
  have hn := assembled_normalized hz F hF w
  have hs := assembled_supermodular z F hF w (fun j => (hw j).le) hc
  rw [actualRootEdge_iff_nonzero_elemental hn.1 hs]
  constructor
  · rintro ⟨hne,X,ha,hj,hd⟩
    by_contra hn
    rw [delta_assembled_spoke _ _ _ _ _ _ hj,hignore j a hn,sub_self,mul_zero] at hd
    exact hd rfl
  · intro ha
    obtain ⟨X,hu,hj,hd⟩ := essential_spoke_slack (z:=z) (F:=F)
      (a:=Sum.inl a) (b:=Sum.inr j) hw (hessential j a ha)
    exact ⟨Sum.inl_ne_inr,X,hu,hj,hd⟩

/-- A finite integral circuit with explicit essential-variable sets gives a
literal clique-book polytope with exactly the specified active spokes. -/
theorem scoped_book_of_finite_circuit
    {J : Type*} [Fintype J] [DecidableEq J] {s k : ℕ} (hs : 0< s)
    (F : J → SetFunction (Fin s)) (hF : ∀ j,IsMonotoneBoolean (F j))
    (scope : J → Finset (Fin s))
    (hessential : ∀ j a,a∈scope j → Essential (F j) a)
    (hignore : ∀ j a,a∉scope j → ∀ X,F j (insert a X)=F j X)
    (j₀ : J) (hanchor : scope j₀=univ) (hbranch : ∀ j,(scope j).Nonempty)
    (w : J → ℤ) (hw : ∀ j,0< w j)
    (hrel : (fun j => (w j : ℝ))∈LinearMap.ker (quotientRelation F))
    (huniq : UniqueIntegrableRelation F (fun j => (w j : ℝ)))
    (hcard : Fintype.card J=k) :
    ∃ f : SetFunction (Fin s⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s k) f ∧ FullDimension (basePolytope f) ∧
      LatticePolytope (basePolytope f) ∧
      ∀ a : Fin s,(univ.filter (fun j : Fin k =>
        ActualRootEdge (basePolytope f) (Sum.inl a) (Sum.inr j))).card=
        (univ.filter (fun j : J => a∈scope j)).card := by
  classical
  letI : Nonempty (Fin s) := ⟨⟨0,hs⟩⟩
  letI : Nonempty J := ⟨j₀⟩
  have hk : 0< k := by rw [←hcard]; exact Fintype.card_pos
  let e : Fin k ≃ J := (finCongr hcard.symm).trans (Fintype.equivFin J).symm
  let F' : Fin k → SetFunction (Fin s) := fun i => F (e i)
  let w' : Fin k → ℤ := fun i => w (e i)
  let C' : Fin k → Finset (Fin s) := fun i => scope (e i)
  have hc : (essentialSpokeGraph F').Connected := by
    apply essentialSpokeGraph_connected_of_anchor F' (e.symm j₀)
    · intro a
      apply hessential
      simp only [e.apply_symm_apply,hanchor,mem_univ]
    · intro i
      obtain ⟨a,ha⟩ := hbranch (e i)
      exact ⟨a,hessential (e i) a ha⟩
  obtain ⟨z,hzn,hzc⟩ := (mem_quotientRelation_ker_iff F _).mp hrel
  have hrel' : (fun i => (w' i : ℝ))∈LinearMap.ker (quotientRelation F') := by
    apply (mem_quotientRelation_ker_iff F' _).mpr
    have hh : Compatible z F (fun j => (w' (e.symm j) : ℝ)) := by
      simpa only [w',e.apply_symm_apply] using hzc
    exact ⟨z,hzn,(compatible_reindex e z F (fun i => (w' i : ℝ))).mpr hh⟩
  have huniq' : UniqueIntegrableRelation F' (fun i => (w' i : ℝ)) := by
    intro t ht
    obtain ⟨u,hun,huc⟩ := ht
    have hold : Compatible u F (fun j => t (e.symm j)) :=
      (compatible_reindex e u F t).mp huc
    obtain ⟨c,hc'⟩ := huniq (fun j => t (e.symm j)) ⟨u,hun,hold⟩
    refine ⟨c,?_⟩
    funext i
    simpa only [e.symm_apply_apply,Pi.smul_apply,w'] using congrFun hc' (e i)
  obtain ⟨u,hun,hui,huc⟩ := integral_compatible_lift F' (fun i => hF (e i)) w' hrel'
  have hw' : ∀ i,0<(w' i : ℝ) := fun i => by exact_mod_cast hw (e i)
  let f := assembled u F' (fun i => (w' i : ℝ))
  have hfn := assembled_normalized hun F' (fun i => hF (e i)) (fun i => (w' i : ℝ))
  have hfi := assembled_integerValued hui F' (fun i => hF (e i)) w'
  have hfe := positive_circuit_extreme hun (fun i => hF (e i))
    (fun i => (hw' i).le) ⟨⟨0,hk⟩,ne_of_gt (hw' ⟨0,hk⟩)⟩ huc huniq'
  refine ⟨f,hfn,hfi,hfe,assembled_graphical u F' _,
    assembled_fullDimension hun (fun i => hF (e i)) hw' huc hc,
    hfi.basePolytope hfn.1 hfe.2.1,?_⟩
  intro a
  have hedge : ∀ i : Fin k,ActualRootEdge (basePolytope f) (Sum.inl a) (Sum.inr i) ↔ a∈scope (e i) := by
    intro i
    exact assembled_actual_spoke_iff hun (fun i => hF (e i)) hw' huc C'
      (fun j a ha => hessential (e j) a ha) (fun j a ha => hignore (e j) a ha) a i
  apply card_bij (fun i _ => e i)
  · intro i hi
    simp only [mem_filter,mem_univ,true_and] at hi ⊢
    exact (hedge i).mp hi
  · intro i hi j hj he
    exact e.injective he
  · intro j hj
    refine ⟨e.symm j,?_,e.apply_symm_apply j⟩
    simp only [mem_filter,mem_univ,true_and] at hj ⊢
    apply (hedge _).mpr
    simpa only [e.apply_symm_apply] using hj

end GraphicalZonotopes.BooleanModule

end
end
end BundlePart321

section BundlePart322
/- Source: Papers/GraphicalZonotopes/ScopedAnchorCircuits.lean -/





@[expose] public section
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.BooleanModule
open Finset
open scoped BigOperators

variable {s : ℕ}

def coefficientExtension (A : Finset (Fin s)) (t : A → ℝ) : Fin s → ℝ :=
  fun a => if h : a∈A then t ⟨a,h⟩ else 0

@[simp] theorem coefficientExtension_subtype (A : Finset (Fin s)) (t : A → ℝ) (a : A) :
    coefficientExtension A t a.1=t a := by simp [coefficientExtension,a.2]

theorem coefficientExtension_not_mem (A : Finset (Fin s)) (t : A → ℝ) {a : Fin s}
    (ha : a∉A) : coefficientExtension A t a=0 := by simp [coefficientExtension,ha]

theorem sum_coefficientExtension {W : Type*} [AddCommMonoid W] [Module ℝ W]
    (A : Finset (Fin s)) (t : A → ℝ) (v : Fin s → W) :
    (∑ a : A,t a • v a.1)=∑ a,coefficientExtension A t a • v a := by
  have hfirst : (∑ a : A,t a • v a.1)=∑ a∈A,coefficientExtension A t a • v a := by
    rw [←sum_coe_sort A (fun a => coefficientExtension A t a • v a)]
    exact sum_congr rfl (fun a _ => by rw [coefficientExtension_subtype])
  rw [hfirst]
  apply sum_subset (subset_univ _)
  intro a ha hn
  rw [coefficientExtension_not_mem A t hn,zero_smul]

abbrev ScopedAnchorIndex (A : Finset (Fin s)) (r : BookBlock (Fin s) → ℕ) :=
  A ⊕ (Σ C : BookBlock (Fin s),Fin (r C))

def scopedAnchorScope (A : Finset (Fin s)) (r : BookBlock (Fin s) → ℕ) :
    ScopedAnchorIndex A r → Finset (Fin s)
  | .inl _ => univ
  | .inr j => j.1.1

section Circuit
variable (A : Finset (Fin s)) (η : ℝ) (FA : A → SetFunction (Fin s))
    (hFA : ∀ a,responseClass (FA a)=η • responseClass (thresholdStar a.1))
    (wA : A → ℤ) (M : ℤ) (r : BookBlock (Fin s) → ℕ)
    (P : ∀ C : BookBlock (Fin s),WeightedPureBlock C.1 M
      (-((η*((-1 : ℝ)^(C.1.card-3))) • blockClass C.1
        (endpointCoefficients C.1 (coefficientExtension A (fun a => (wA a : ℝ)))))) (r C))

def scopedAnchorVector : ScopedAnchorIndex A r → ResponseQuotient (Fin s)
  | .inl a => responseClass (FA a)
  | .inr j => blockClass j.1.1 ((P j.1).column j.2)

def scopedAnchorWeight : ScopedAnchorIndex A r → ℤ
  | .inl a => wA a
  | .inr j => (P j.1).weight j.2

def scopedAnchorCombination (t : ScopedAnchorIndex A r → ℝ) (C : BookBlock (Fin s)) : PairIn C.1 → ℝ :=
  (η*((-1 : ℝ)^(C.1.card-3))) • endpointCoefficients C.1
    (coefficientExtension A (fun a => t (.inl a)))+
    ∑ j : Fin (r C),t (.inr ⟨C,j⟩) • (P C).column j

include hFA in
theorem scopedAnchor_sum_blocks (t : ScopedAnchorIndex A r → ℝ) :
    (∑ j,t j • scopedAnchorVector A η FA wA M r P j)=
      ∑ C : BookBlock (Fin s),blockClass C.1 (scopedAnchorCombination A η wA M r P t C) := by
  rw [Fintype.sum_sum_type,Fintype.sum_sigma]
  change (∑ a : A,t (.inl a) • responseClass (FA a))+
    (∑ C,∑ j : Fin (r C),t (.inr ⟨C,j⟩) • blockClass C.1 ((P C).column j))=_
  simp_rw [hFA]
  have ha : (∑ a : A,t (.inl a) • η • responseClass (thresholdStar a.1))=
      η • (∑ a : A,t (.inl a) • responseClass (thresholdStar a.1)) := by
    rw [smul_sum]
    exact sum_congr rfl (fun a _ => smul_comm _ _ _)
  rw [ha,sum_coefficientExtension A (fun a => t (.inl a))
    (fun a => responseClass (thresholdStar a)),weighted_threshold_response,smul_sum]
  rw [←sum_add_distrib]
  apply sum_congr rfl
  intro C hC
  simp only [scopedAnchorCombination,map_add,map_smul,map_sum,mul_smul]

include hFA in
theorem scopedAnchor_weighted_sum :
    (∑ j,(scopedAnchorWeight A η wA M r P j : ℝ) • scopedAnchorVector A η FA wA M r P j)=0 := by
  rw [scopedAnchor_sum_blocks A η FA hFA wA M r P]
  apply sum_eq_zero
  intro C hC
  simp only [scopedAnchorCombination,map_add,map_smul,map_sum,scopedAnchorWeight]
  rw [(P C).weighted_sum]
  exact add_neg_cancel _

theorem scopedAnchor_pure_independent :
    LinearIndependent ℝ (fun j : Σ C : BookBlock (Fin s),Fin (r C) =>
      blockClass j.1.1 ((P j.1).column j.2)) := by
  have hpair : ∀ C : BookBlock (Fin s),∃ p : PairIn C.1,True := by
    intro C
    obtain ⟨p,hp⟩ := cliquePairs_nonempty C.1 C.1 (Subset.refl _)
      (by have h := (mem_largeBlocks.mp C.2).2; omega)
    exact ⟨p,trivial⟩
  exact block_families_independent Subtype.val Subtype.val_injective
    (fun C => (hpair C).choose) (fun C => (P C).column) (fun C => (P C).independent)

def ScopedAnchorRigidity : Prop :=
  ∀ t : ScopedAnchorIndex A r → ℝ,
    (∀ C : BookBlock (Fin s),blockClass C.1 (scopedAnchorCombination A η wA M r P t C)=0) →
      ∃ c : ℝ,∀ a : A,t (.inl a)=c*(wA a : ℝ)

include hFA in
theorem scopedAnchor_unique (hrigid : ScopedAnchorRigidity A η wA M r P)
    (t : ScopedAnchorIndex A r → ℝ)
    (ht : (∑ j,t j • scopedAnchorVector A η FA wA M r P j)=0) :
    ∃ c : ℝ,t=c • (fun j => (scopedAnchorWeight A η wA M r P j : ℝ)) := by
  rw [scopedAnchor_sum_blocks A η FA hFA wA M r P] at ht
  have hpair : ∀ C : BookBlock (Fin s),∃ p : PairIn C.1,True := by
    intro C
    obtain ⟨p,hp⟩ := cliquePairs_nonempty C.1 C.1 (Subset.refl _)
      (by have h := (mem_largeBlocks.mp C.2).2; omega)
    exact ⟨p,trivial⟩
  have hb := block_sum_zero_component Subtype.val Subtype.val_injective
    (fun C => (hpair C).choose) (scopedAnchorCombination A η wA M r P t) ht
  obtain ⟨c,hc⟩ := hrigid t hb
  have hz : (∑ j : ScopedAnchorIndex A r,
      (t j-c*(scopedAnchorWeight A η wA M r P j : ℝ)) •
        scopedAnchorVector A η FA wA M r P j)=0 := by
    simp only [sub_smul,mul_smul,sum_sub_distrib,←smul_sum]
    rw [scopedAnchor_sum_blocks A η FA hFA wA M r P,ht,
      scopedAnchor_weighted_sum A η FA hFA wA M r P,smul_zero,sub_self]
  rw [Fintype.sum_sum_type] at hz
  have ha : (∑ a : A,(t (.inl a)-c*(scopedAnchorWeight A η wA M r P (.inl a) : ℝ)) •
      scopedAnchorVector A η FA wA M r P (.inl a))=0 := by
    apply sum_eq_zero
    intro a ha
    rw [scopedAnchorWeight,hc,sub_self,zero_smul]
  rw [ha,zero_add] at hz
  have hp := Fintype.linearIndependent_iff.mp (scopedAnchor_pure_independent A η wA M r P)
    (fun j => t (.inr j)-c*(scopedAnchorWeight A η wA M r P (.inr j) : ℝ)) hz
  refine ⟨c,?_⟩
  funext j
  cases j with
  | inl a => exact hc a
  | inr j => exact sub_eq_zero.mp (hp j)

include hFA in
/-- The complete circuit theorem retaining its exact essential-variable
scopes; the final principal constructions supply every algebraic premise. -/
theorem scoped_book_of_anchor_circuit (hs : 3≤ s)
    (hAb : ∀ a,IsMonotoneBoolean (FA a)) (hAe : ∀ a i,Essential (FA a) i)
    (a₀ : A) (hwA : ∀ a,0< wA a)
    (hrigid : ScopedAnchorRigidity A η wA M r P)
    {k : ℕ} (hcard : Fintype.card (ScopedAnchorIndex A r)=k) :
    ∃ f : SetFunction (Fin s⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s k) f ∧ FullDimension (basePolytope f) ∧
      LatticePolytope (basePolytope f) ∧
      ∀ a : Fin s,(univ.filter (fun j : Fin k =>
        ActualRootEdge (basePolytope f) (Sum.inl a) (Sum.inr j))).card=
        (univ.filter (fun j : ScopedAnchorIndex A r => a∈scopedAnchorScope A r j)).card := by
  have hF : ∀ C j,∃ F : SetFunction (Fin s),IsMonotoneBoolean F ∧
      (∀ a,a∈C.1 → Essential F a) ∧
      (∀ a,a∉C.1 → ∀ X,F (insert a X)=F X) ∧
      responseClass F=blockClass C.1 ((P C).column j) := fun C j => (P C).realizable j
  choose F hFb hFe hFi hFc using hF
  let G : ScopedAnchorIndex A r → SetFunction (Fin s)
    | .inl a => FA a
    | .inr j => F j.1 j.2
  have hGb : ∀ j,IsMonotoneBoolean (G j) := by
    intro j
    cases j with
    | inl a => exact hAb a
    | inr j => exact hFb j.1 j.2
  have hGe : ∀ j a,a∈scopedAnchorScope A r j → Essential (G j) a := by
    intro j a ha
    cases j with
    | inl b => exact hAe b a
    | inr j => exact hFe j.1 j.2 a ha
  have hGi : ∀ j a,a∉scopedAnchorScope A r j → ∀ X,G j (insert a X)=G j X := by
    intro j a ha X
    cases j with
    | inl b => exact False.elim (ha (mem_univ _))
    | inr j => exact hFi j.1 j.2 a ha X
  have hGc : ∀ j,responseClass (G j)=scopedAnchorVector A η FA wA M r P j := by
    intro j
    cases j with
    | inl a => rfl
    | inr j => exact hFc j.1 j.2
  have hnon : ∀ j,(scopedAnchorScope A r j).Nonempty := by
    intro j
    cases j with
    | inl a => exact ⟨⟨0,by omega⟩,mem_univ _⟩
    | inr j =>
      change j.1.1.Nonempty
      exact card_pos.mp (by have h := (mem_largeBlocks.mp j.1.2).2; omega)
  have hw : ∀ j,0< scopedAnchorWeight A η wA M r P j := by
    intro j
    cases j with
    | inl a => exact hwA a
    | inr j => exact (P j.1).positive j.2
  have hrel : (fun j => (scopedAnchorWeight A η wA M r P j : ℝ))∈LinearMap.ker (quotientRelation G) := by
    change quotientRelation G _=0
    rw [quotientRelation_apply_eq_sum]
    simp_rw [hGc]
    exact scopedAnchor_weighted_sum A η FA hFA wA M r P
  have huniq : UniqueIntegrableRelation G (fun j => (scopedAnchorWeight A η wA M r P j : ℝ)) := by
    intro t ht
    have ht0 : quotientRelation G t=0 := (mem_quotientRelation_ker_iff G t).mpr ht
    rw [quotientRelation_apply_eq_sum] at ht0
    simp_rw [hGc] at ht0
    exact scopedAnchor_unique A η FA hFA wA M r P hrigid t ht0
  exact scoped_book_of_finite_circuit (by omega) G hGb (scopedAnchorScope A r)
    hGe hGi (.inl a₀) rfl hnon (scopedAnchorWeight A η wA M r P) hw hrel huniq hcard

end Circuit
end GraphicalZonotopes.BooleanModule

end
end
end BundlePart322

section BundlePart323
/- Source: Papers/GraphicalZonotopes/JunctionStar.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes.BooleanModule
open Finset PowersetTransform
variable {H : Type*} [Fintype H] [LinearOrder H]

/-- The second all-essential anchor, `x_a` conjoined with the disjunction of
all other variables. -/
def junctionStar (a : H) : SetFunction H :=
  fun S => if a∈S ∧ 2≤ S.card then 1 else 0

theorem junctionStar_boolean (hs : 2≤ Fintype.card H) (a : H) :
    IsMonotoneBoolean (junctionStar a) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro S T hST
    by_cases hS : a∈S ∧ 2≤ S.card
    · have hT : a∈T ∧ 2≤ T.card := ⟨hST hS.1,hS.2.trans (card_le_card hST)⟩
      simp only [junctionStar,if_pos hS,if_pos hT,le_refl]
    · unfold junctionStar
      rw [if_neg hS]
      split_ifs <;> norm_num
  · intro S
    unfold junctionStar
    split_ifs <;> simp
  · simp [junctionStar]
  · simp [junctionStar,hs]

theorem junctionStar_zero_iff (a : H) (S : Finset H) :
    junctionStar a S=0 ↔ a∉S ∨ S.card<2 := by
  by_cases ha : a∈S <;> simp [junctionStar,ha] <;> omega

theorem junctionStar_one_iff (a : H) (S : Finset H) :
    junctionStar a S=1 ↔ a∈S ∧ 2≤ S.card := by
  by_cases ha : a∈S <;> simp [junctionStar,ha] <;> omega

theorem junctionStar_essential (hs : 2≤ Fintype.card H) (a i : H) :
    Essential (junctionStar a) i := by
  by_cases hi : i=a
  · subst i
    have he : ∃ b : H,b≠ a := by
      by_contra hn
      have hsub : (univ : Finset H)⊆{a} := by
        intro b hb
        simp only [mem_singleton]
        by_contra hba
        exact hn ⟨b,hba⟩
      have hc := card_le_card hsub
      simp only [card_univ,card_singleton] at hc
      omega
    obtain ⟨b,hba⟩ := he
    refine ⟨{b},by simpa only [mem_singleton] using hba.symm,?_⟩
    simp [junctionStar,hba,Ne.symm hba]
  · refine ⟨{a},by simpa only [mem_singleton] using hi,?_⟩
    simp [junctionStar,hi,Ne.symm hi]

theorem junctionStar_negativeResponse (hs : 2≤ Fintype.card H) (a : H)
    {u v : H} (huv : u≠ v) (S : Finset H) (hu : u∉S) (hv : v∉S) :
    negativeResponse (junctionStar a) u v S=
      if a∈S then exactlyOne S else 0 := by
  have hone : negativeResponse (junctionStar a) u v S=1 ↔ a∈S ∧ S.card=1 := by
    rw [negativeResponse_eq_one_iff (junctionStar_boolean hs a),
      junctionStar_zero_iff,junctionStar_one_iff,junctionStar_one_iff]
    simp only [mem_insert,card_insert_of_notMem hu,card_insert_of_notMem hv]
    constructor
    · rintro ⟨hzero,⟨hua,huc⟩,⟨hva,hvc⟩⟩
      have ha : a∈S := by
        by_contra hn
        have hau : a=u := hua.resolve_right hn
        have hav : a=v := hva.resolve_right hn
        exact huv (hau.symm.trans hav)
      have hc : S.card<2 := hzero.resolve_left (not_not.mpr ha)
      exact ⟨ha,by omega⟩
    · rintro ⟨ha,hc⟩
      exact ⟨Or.inr (by omega),⟨Or.inr ha,by omega⟩,⟨Or.inr ha,by omega⟩⟩
  rcases negativeResponse_values (junctionStar_boolean hs a) u v S with hz | ho
  · have hn : ¬(a∈S ∧ S.card=1) := by
      intro h
      have hh := hone.mpr h
      rw [hz] at hh
      norm_num at hh
    by_cases ha : a∈S
    · have hc : S.card≠1 := fun h => hn ⟨ha,h⟩
      simp [hz,ha,exactlyOne,hc]
    · simp [hz,ha]
  · obtain ⟨ha,hc⟩ := hone.mp ho
    simp [ho,ha,exactlyOne,hc]

/-- Both anchor responses are opposite in the actual quotient, in every
clique block simultaneously. -/
theorem junctionStar_response_class (hs : 2≤ Fintype.card H) (a : H) :
    responseClass (junctionStar a)= -responseClass (thresholdStar a) := by
  let x : HubResponseRow H → ℝ := fun r => exactlyOneCoefficient r.2.1.card
  have hvec : responseVector (junctionStar a)+responseVector (thresholdStar a)=
      rowLowerEquiv x := by
    funext r
    have hu : r.1.1.1∉r.2.1 := by
      intro h
      exact not_mem_commonNeighbors_left ⊤ _ _ ((mem_powerset.mp r.2.2) h)
    have hv : r.1.1.2∉r.2.1 := by
      intro h
      exact not_mem_commonNeighbors_right ⊤ _ _ ((mem_powerset.mp r.2.2) h)
    change negativeResponse (junctionStar a) r.1.1.1 r.1.1.2 r.2.1+
      negativeResponse (thresholdStar a) r.1.1.1 r.1.1.2 r.2.1=
      lowerSum (commonNeighbors (⊤ : SimpleGraph H) r.1.1.1 r.1.1.2)
        (fun T => exactlyOneCoefficient T.1.card) r.2
    rw [junctionStar_negativeResponse hs a (ne_of_lt r.1.2.1) _ hu hv,
      thresholdStar_negativeResponse a (ne_of_lt r.1.2.1) _ hu hv,
      lowerSum_restriction _ (fun T : Finset H => exactlyOneCoefficient T.card) r.2]
    change _=zeta (fun T : Finset H => exactlyOneCoefficient T.card) r.2.1
    rw [zeta_exactlyOneCoefficient]
    by_cases ha : a∈r.2.1 <;> simp [ha]
  have hz : coefficientClass x=0 := by
    apply (coefficientClass_eq_zero_iff x).mpr
    intro r t hrt
    have hc := congrArg (fun C : CliqueIndex (⊤ : SimpleGraph H) => C.1.card) hrt
    have hr := rowClique_card_eq_context_add_two r
    have ht := rowClique_card_eq_context_add_two t
    have he : r.2.1.card=t.2.1.card := by
      change (rowClique r).card=(rowClique t).card at hc
      omega
    change exactlyOneCoefficient r.2.1.card=exactlyOneCoefficient t.2.1.card
    rw [he]
  have hsum : responseClass (junctionStar a)+responseClass (thresholdStar a)=0 := by
    change (LinearMap.range (centralCoefficientSlack (H:=H))).mkQ _+
      (LinearMap.range (centralCoefficientSlack (H:=H))).mkQ _=0
    rw [← map_add,hvec]
    exact hz
  exact eq_neg_of_add_eq_zero_left hsum

end GraphicalZonotopes.BooleanModule

end
end
end BundlePart323

section BundlePart324
/- Source: Papers/GraphicalZonotopes/SaturatedGeneralBlocks.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace GraphicalZonotopes.BooleanModule.Saturated
open Finset
open scoped BigOperators
variable {s : ℕ}

abbrev fullBlock (hs : 3≤ s) : BookBlock (Fin s) :=
  ⟨univ,mem_largeBlocks.mpr ⟨subset_univ _,by simpa using hs⟩⟩

def eta (s : ℕ) : ℝ := (-1 : ℝ)^(s-3)

theorem eta_sign (s : ℕ) : eta s=1 ∨ eta s= -1 := neg_one_pow_eq_or ℝ _

theorem eta_full_factor (hs : 3≤ s) : eta s*((-1 : ℝ)^((fullBlock hs).1.card-3))=1 := by
  change eta s*((-1 : ℝ)^((univ : Finset (Fin s)).card-3))=1
  rw [card_univ,Fintype.card_fin]
  change eta s*eta s=1
  rcases eta_sign s with h | h <;> rw [h] <;> norm_num

def anchorFamily (hs : 3≤ s) (a : BookAnchor hs) : SetFunction (Fin s) :=
  if eta s=1 then thresholdStar a.1 else junctionStar a.1

theorem anchorFamily_boolean (hs : 3≤ s) (a : BookAnchor hs) :
    IsMonotoneBoolean (anchorFamily hs a) := by
  unfold anchorFamily
  split_ifs
  · exact thresholdStar_boolean _
  · exact junctionStar_boolean (by simpa using (show 2≤ s by omega)) _

theorem anchorFamily_essential (hs : 3≤ s) (a : BookAnchor hs) (i : Fin s) :
    Essential (anchorFamily hs a) i := by
  unfold anchorFamily
  split_ifs
  · exact thresholdStar_essential (by simpa using hs) _ _
  · exact junctionStar_essential (by simpa using (show 2≤ s by omega)) _ _

theorem anchorFamily_response (hs : 3≤ s) (a : BookAnchor hs) :
    responseClass (anchorFamily hs a)=eta s • responseClass (thresholdStar a.1) := by
  unfold anchorFamily
  by_cases h : eta s=1
  · simp only [h,ite_true,one_smul]
  · have he : eta s= -1 := (eta_sign s).resolve_left h
    rw [if_neg h,junctionStar_response_class (by simpa using (show 2≤ s by omega)),he,neg_one_smul]

def anchorWeights (hs : 3≤ s) (a : BookAnchor hs) : ℤ := (a.1.val : ℤ)

theorem anchorWeights_positive (hs : 3≤ s) (a : BookAnchor hs) : 0< anchorWeights hs a := by
  have h := (mem_erase.mp a.2).1
  have hv : a.1.val≠0 := fun he => h (Fin.ext he)
  change 0<(a.1.val : ℤ)
  omega

theorem coefficientExtension_anchor_labels (hs : 3≤ s) :
    coefficientExtension ((univ : Finset (Fin s)).erase (bookZero hs))
      (fun a => (anchorWeights hs a : ℝ))=(fun a : Fin s => (a.val : ℝ)) := by
  funext a
  by_cases ha : a=bookZero hs
  · subst a
    simp [coefficientExtension,bookZero]
  · have ham : a∈(univ : Finset (Fin s)).erase (bookZero hs) := mem_erase.mpr ⟨ha,mem_univ _⟩
    simp only [coefficientExtension,dif_pos ham,anchorWeights,Int.cast_natCast]

def pureRank (s : ℕ) (C : BookBlock (Fin s)) : ℕ :=
  if C.1=univ then (retainedPairs s).card else C.1.card.choose 2-1

abbrev anchorSet (hs : 3≤ s) : Finset (Fin s) := (univ : Finset (Fin s)).erase (bookZero hs)

theorem pureRank_full (hs : 3≤ s) : pureRank s (fullBlock hs)=(retainedPairs s).card := by
  simp [pureRank,fullBlock]

def pureBlock (hs : 5≤ s) (C : BookBlock (Fin s)) :
    WeightedPureBlock C.1 (2*s : ℕ)
      (-((eta s*((-1 : ℝ)^(C.1.card-3))) • blockClass C.1
        (endpointCoefficients C.1 (coefficientExtension (anchorSet (show 3≤ s by omega))
          (fun a => (anchorWeights (show 3≤ s by omega) a : ℝ)))))) (pureRank s C) := by
  classical
  have hd := coefficientExtension_anchor_labels (show 3≤ s by omega)
  by_cases hC : C=fullBlock (show 3≤ s by omega)
  · subst C
    let e : Fin (pureRank s (fullBlock (show 3≤ s by omega))) ≃
        Fin (retainedPairs s).card := finCongr (pureRank_full (show 3≤ s by omega))
    refine {
      column := fun j => (matchingPureBlock hs).column (e j)
      realizable := fun j => (matchingPureBlock hs).realizable (e j)
      weight := fun j => (matchingPureBlock hs).weight (e j)
      positive := fun j => (matchingPureBlock hs).positive (e j)
      bounded := fun j => (matchingPureBlock hs).bounded (e j)
      independent := (matchingPureBlock hs).independent.comp e e.injective
      weighted_sum := ?_ }
    rw [e.sum_comp (fun j => ((matchingPureBlock hs).weight j : ℝ) •
      blockClass univ ((matchingPureBlock hs).column j)),
      (matchingPureBlock hs).weighted_sum,eta_full_factor,one_smul,hd]
    rfl
  · have hCu : C.1≠ univ := fun h => hC (Subtype.ext h)
    rw [pureRank,if_neg hCu]
    have hε : -(eta s*((-1 : ℝ)^(C.1.card-3)))=1 ∨
        -(eta s*((-1 : ℝ)^(C.1.card-3)))= -1 := by
      rcases eta_sign s with h1 | h1 <;>
        rcases neg_one_pow_eq_or ℝ (C.1.card-3) with h2 | h2 <;> simp [h1,h2]
    let Q := Classical.choice (saturated_pair_basis C.1 (mem_largeBlocks.mp C.2).2 _ hε)
    refine {
      column := Q.column
      realizable := Q.realizable
      weight := Q.weight
      positive := Q.positive
      bounded := Q.bounded
      independent := Q.independent
      weighted_sum := ?_ }
    rw [Q.weighted_sum,hd,neg_smul]
    rfl

theorem pureBlock_full_column (hs : 5≤ s)
    (j : Fin (pureRank s (fullBlock (show 3≤ s by omega)))) :
    (pureBlock hs (fullBlock (show 3≤ s by omega))).column j =
      (matchingPureBlock hs).column (finCongr (pureRank_full (show 3≤ s by omega)) j) := by
  unfold pureBlock
  simp only [dite_true] <;> rfl

theorem pureRank_proper (hs : 3≤ s) (C : BookBlock (Fin s)) (hC : C≠ fullBlock hs) :
    pureRank s C=C.1.card.choose 2-1 := by
  have h : C.1≠ univ := fun he => hC (Subtype.ext he)
  simp only [pureRank,h,ite_false]

-- The checked column identity above supplies the data needed below;
-- elaboration need not expand the Boolean realizations of those columns.
attribute [local irreducible] pureBlock matchingPureBlock

/-- The full-clique matching rows force every all-hub anchor scale before any
proper-clique basis is used. -/
theorem general_scale_rigidity (hs : 5≤ s) :
    ScopedAnchorRigidity (anchorSet (show 3≤ s by omega)) (eta s)
      (anchorWeights (show 3≤ s by omega)) (2*s : ℕ) (pureRank s) (pureBlock hs) := by
  intro t ht
  let d := coefficientExtension (anchorSet (show 3≤ s by omega)) (fun a => t (.inl a))
  have h0 : d ⟨0,by omega⟩=0 := by
    simp [d,coefficientExtension,anchorSet,bookZero]
  have hfull := ht (fullBlock (show 3≤ s by omega))
  dsimp only [scopedAnchorCombination] at hfull
  -- Rewrite the displayed coefficient only. The same coefficient also
  -- occurs in the type of the fixed circuit data, which must stay intact.
  rw (occs := .pos [1]) [eta_full_factor (show 3≤ s by omega)] at hfull
  rw [one_smul] at hfull
  let e : Fin (pureRank s (fullBlock (show 3≤ s by omega))) ≃
      Fin (retainedPairs s).card := finCongr (pureRank_full (show 3≤ s by omega))
  let t' : Fin (retainedPairs s).card → ℝ :=
    fun j => t (.inr ⟨fullBlock (show 3≤ s by omega),e.symm j⟩)
  have hsum : (∑ j,t (.inr ⟨fullBlock (show 3≤ s by omega),j⟩) •
      (pureBlock hs (fullBlock (show 3≤ s by omega))).column j) =
      ∑ j,t' j • (matchingPureBlock hs).column j := by
    calc
      _ = ∑ j,t (.inr ⟨fullBlock (show 3≤ s by omega),j⟩) •
          (matchingPureBlock hs).column (e j) := by
        apply sum_congr rfl
        intro j hj
        exact congrArg (fun v => t (.inr ⟨fullBlock (show 3≤ s by omega),j⟩) • v)
          (pureBlock_full_column hs j)
      _ = _ := by
        have he := e.sum_comp (fun j => t' j • (matchingPureBlock hs).column j)
        simpa only [t',Equiv.symm_apply_apply] using he
  rw [hsum] at hfull
  have hd := matchingPureBlock_rigidity hs d h0 t' hfull
  refine ⟨d ⟨1,by omega⟩,?_⟩
  intro a
  have ha := hd a.1
  change coefficientExtension (anchorSet (show 3≤ s by omega)) (fun a => t (.inl a)) a.1=_ at ha
  rw [coefficientExtension_subtype] at ha
  simpa only [anchorWeights,Int.cast_natCast,mul_comm] using ha

theorem sum_bookBlock_split {W : Type*} [AddCommMonoid W] (hs : 3≤ s)
    (f : BookBlock (Fin s) → W) :
    (∑ C : BookBlock (Fin s),f C)=f (fullBlock hs)+
      ∑ C : {C : BookBlock (Fin s) // C≠ fullBlock hs},f C.1 := by
  have h := (Equiv.optionSubtypeNe (fullBlock hs)).sum_comp f
  rw [Fintype.sum_option] at h
  exact h.symm

theorem general_circuit_card (hs : 5≤ s) :
    Fintype.card (ScopedAnchorIndex (anchorSet (show 3≤ s by omega)) (pureRank s))=cliqueCapacity s := by
  rw [Fintype.card_sum,Fintype.card_sigma]
  simp only [Fintype.card_fin,Fintype.card_coe,anchorSet,card_erase_of_mem (mem_univ _),card_univ]
  rw [sum_bookBlock_split (show 3≤ s by omega),pureRank_full]
  have hproper : ∀ C : {C : BookBlock (Fin s) // C≠ fullBlock (show 3≤ s by omega)},
      pureRank s C.1=C.1.1.card.choose 2-1 := fun C =>
    pureRank_proper (show 3≤ s by omega) C.1 C.2
  simp_rw [hproper]
  have h := BookBlock_dimension_sum (H:=Fin s)
  rw [sum_bookBlock_split (show 3≤ s by omega)] at h
  have hfullcard : (fullBlock (show 3≤ s by omega)).1.card=s := by simp [fullBlock]
  rw [hfullcard,Fintype.card_fin] at h
  have hc := retained_count_add_anchors hs
  have hchoose : 1≤ s.choose 2 := Nat.choose_pos (by omega)
  omega

end GraphicalZonotopes.BooleanModule.Saturated

end
end
end BundlePart324

section BundlePart325
/- Source: Papers/GraphicalZonotopes/SaturatedGeneralAttainment.lean -/





/-! # Exact spoke counts in the saturated matching construction

The proper blocks avoiding a selected hub are exactly the response blocks on
the other hubs.  This identifies the missing spokes with their total dimension.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.BooleanModule.Saturated
open Finset
open scoped BigOperators
variable {s : ℕ}

theorem nonneighbor_count (hs : 5 ≤ s) (a : Fin s) :
    (univ.filter (fun j : ScopedAnchorIndex (anchorSet (show 3 ≤ s by omega)) (pureRank s) =>
      a ∉ scopedAnchorScope (anchorSet (show 3 ≤ s by omega)) (pureRank s) j)).card + 1 =
      cliqueCapacity (s - 1) := by
  classical
  rw [card_eq_sum_ones,sum_filter,Fintype.sum_sum_type]
  simp only [scopedAnchorScope,mem_univ,not_true_eq_false,ite_false,sum_const_zero,zero_add]
  rw [Fintype.sum_sigma]
  have hc : ∀ C : BookBlock (Fin s),
      (∑ j : Fin (pureRank s C),if a ∉ C.1 then (1 : ℕ) else 0) =
        if a ∉ C.1 then C.1.card.choose 2 - 1 else 0 := by
    intro C
    by_cases ha : a ∈ C.1
    · simp only [ha,not_true_eq_false,ite_false,sum_const_zero]
    · have hCu : C.1 ≠ univ := by
        intro he
        apply ha
        rw [he]
        exact mem_univ a
      simp only [ha,not_false_eq_true,ite_true,sum_const,card_univ,Fintype.card_fin,
        smul_eq_mul,mul_one,pureRank,if_neg hCu]
  simp_rw [hc]
  rw [sum_coe_sort (largeBlocks (univ : Finset (Fin s)))
    (fun C => if a ∉ C then C.card.choose 2 - 1 else 0)]
  rw [← sum_filter]
  have hfilter : (largeBlocks (univ : Finset (Fin s))).filter (fun C => a ∉ C) =
      largeBlocks (univ.erase a) := by
    ext C
    simp only [mem_filter,mem_largeBlocks,subset_erase]
    tauto
  rw [hfilter,largeBlocks_dimension_sum,← cliqueCapacity_eq_dimension_sum,
    card_erase_of_mem (mem_univ a),card_univ,Fintype.card_fin]

theorem neighbor_count (hs : 5 ≤ s) (a : Fin s) :
    (univ.filter (fun j : ScopedAnchorIndex (anchorSet (show 3 ≤ s by omega)) (pureRank s) =>
      a ∈ scopedAnchorScope (anchorSet (show 3 ≤ s by omega)) (pureRank s) j)).card =
        saturatedHubNeighbors s := by
  classical
  have hc := card_filter_add_card_filter_not
    (s := (univ : Finset (ScopedAnchorIndex (anchorSet (show 3 ≤ s by omega)) (pureRank s))))
    (p := fun j => a ∈ scopedAnchorScope (anchorSet (show 3 ≤ s by omega)) (pureRank s) j)
  rw [card_univ,general_circuit_card hs] at hc
  have hn := nonneighbor_count hs a
  have hmono := cliqueCapacity_pred_le (show 1 ≤ s by omega)
  unfold saturatedHubNeighbors
  rw [if_neg (by omega : s ≠ 2)]
  omega

/-- For every number of hubs at least five, the matching circuit gives an
actual full-dimensional lattice polytope with exactly the optimal number of
active spokes at each hub. -/
theorem spoke_attainment (s : ℕ) (hs : 5 ≤ s) :
    ∃ f : SetFunction (Fin s ⊕ Fin (cliqueCapacity s)),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s (cliqueCapacity s)) f ∧ FullDimension (basePolytope f) ∧
      LatticePolytope (basePolytope f) ∧
      ∀ a : Fin s,(univ.filter (fun j : Fin (cliqueCapacity s) =>
        ActualRootEdge (basePolytope f) (Sum.inl a) (Sum.inr j))).card =
          saturatedHubNeighbors s := by
  let hs3 : 3 ≤ s := by omega
  let a₀ : anchorSet hs3 := ⟨⟨1,by omega⟩,by
    simp only [anchorSet,mem_erase,mem_univ,and_true,bookZero]
    intro he
    have hv := congrArg Fin.val he
    norm_num at hv⟩
  obtain ⟨f,hn,hi,he,hG,hd,hl,hcount⟩ := scoped_book_of_anchor_circuit
    (anchorSet hs3) (eta s) (anchorFamily hs3) (anchorFamily_response hs3)
    (anchorWeights hs3) (2*s : ℕ) (pureRank s) (pureBlock hs) hs3
    (anchorFamily_boolean hs3) (anchorFamily_essential hs3) a₀
    (anchorWeights_positive hs3) (general_scale_rigidity hs) (general_circuit_card hs)
  exact ⟨f,hn,hi,he,hG,hd,hl,fun a => (hcount a).trans (neighbor_count hs a)⟩

end GraphicalZonotopes.BooleanModule.Saturated

end
end
end BundlePart325

section BundlePart326
/- Source: Papers/GraphicalZonotopes/SaturatedFourBlocks.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.BooleanModule.SaturatedFour
open Finset
open scoped BigOperators
open Saturated

abbrev H := Fin 4
abbrev Cfull : Finset H := univ

def anchors : Finset H := {2,3}

def label (a : H) : ℤ := if a=2 ∨ a=3 then 1 else 0

def column : Fin 4 → PairIn Cfull → ℝ
  | 0 => pairIndicator (starPairs Cfull 2 {0,3})
  | 1 => pairIndicator (starPairs Cfull 2 {1,3})
  | 2 => pairIndicator {natPair 0 3 (by decide) (by decide)}
  | 3 => pairIndicator {natPair 1 3 (by decide) (by decide)}

theorem column_realizable (i : Fin 4) : PureRealizable Cfull (column i) := by
  fin_cases i
  · exact pureRealizable_star Cfull (mem_univ _) (subset_univ _) (by simp) (by decide)
  · exact pureRealizable_star Cfull (mem_univ _) (subset_univ _) (by simp) (by decide)
  · exact pureRealizable_pair Cfull _
  · exact pureRealizable_pair Cfull _

theorem column_reference (i : Fin 4) : column i (natPair 0 1 (by decide) (by decide))=0 := by
  fin_cases i <;> norm_num [column,pairIndicator,mem_starPairs,StarPair,natPair,orderedPair]

theorem column_independent : LinearIndependent ℝ column := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h0 := congrFun hc (natPair 0 2 (by decide) (by decide))
  have h1 := congrFun hc (natPair 1 2 (by decide) (by decide))
  have h2 := congrFun hc (natPair 0 3 (by decide) (by decide))
  have h3 := congrFun hc (natPair 1 3 (by decide) (by decide))
  norm_num [Fin.sum_univ_succ,column,pairIndicator,mem_starPairs,StarPair,natPair,orderedPair] at h0 h1 h2 h3
  fin_cases i <;> assumption

theorem column_sum : (∑ i,column i)=endpointCoefficients Cfull (fun a => (label a : ℝ)) := by
  funext e
  obtain ⟨⟨⟨u,v⟩,huv,hG⟩,hu,hv⟩ := e
  fin_cases u <;> fin_cases v <;> norm_num at huv
  all_goals norm_num [Fin.sum_univ_succ,column,pairIndicator,mem_starPairs,StarPair,
    natPair,orderedPair,endpointCoefficients,label]

theorem full_rigidity (d : H → ℝ) (h0 : d 0=0) (h1 : d 1=0) (t : Fin 4 → ℝ)
    (hz : blockClass Cfull ((-1 : ℝ) • endpointCoefficients Cfull d+∑ i,t i • column i)=0) :
    d 2=d 3 := by
  obtain ⟨c,hc⟩ := (blockClass_eq_zero_iff Cfull (natPair 0 1 (by decide) (by decide)) _).mp hz
  have h01 := hc (natPair 0 1 (by decide) (by decide))
  have h02 := hc (natPair 0 2 (by decide) (by decide))
  have h12 := hc (natPair 1 2 (by decide) (by decide))
  have h23 := hc (natPair 2 3 (by decide) (by decide))
  norm_num [Fin.sum_univ_succ,column,pairIndicator,mem_starPairs,StarPair,natPair,orderedPair,
    endpointCoefficients,h0,h1] at h01 h02 h12 h23
  linarith

def fullPureBlock : WeightedPureBlock Cfull 1
    (blockClass Cfull (endpointCoefficients Cfull (fun a => (label a : ℝ)))) 4 where
  column := column
  realizable := column_realizable
  weight := fun _ => 1
  positive := fun _ => by norm_num
  bounded := fun _ => le_rfl
  independent := blockClass_linearIndependent_of_reference Cfull
    (natPair 0 1 (by decide) (by decide)) column column_independent column_reference
  weighted_sum := by
    simp only [Int.cast_one,one_smul]
    rw [←map_sum,column_sum]

theorem proper_card {C : BookBlock H} (hC : C.1≠ univ) : C.1.card=3 := by
  have h3 := (mem_largeBlocks.mp C.2).2
  have h4 : C.1.card≤4 := by simpa using card_le_card (subset_univ C.1)
  have hlt : C.1.card≠4 := by
    intro he
    apply hC
    exact eq_of_subset_of_card_le (subset_univ _) (by simpa using he.ge)
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem proper_reference_exists :
    ∀ C : BookBlock H,C.1≠ univ → ∃ e₀ : PairIn C.1,
      (label e₀.1.1.1+label e₀.1.1.2=0 ∨ label e₀.1.1.1+label e₀.1.1.2=2) ∧
      ∀ e : PairIn C.1,e≠ e₀ → label e.1.1.1+label e.1.1.2=1 := by
  have hfinite : ∀ C : Finset H,C.card=3 → ∃ u v : H,
      u< v ∧ u∈C ∧ v∈C ∧ (label u+label v=0 ∨ label u+label v=2) ∧
      ∀ a b : H,a< b → a∈C → b∈C → (a≠ u ∨ b≠ v) → label a+label b=1 := by
    decide
  intro C hC
  obtain ⟨u,v,huv,hu,hv,hl,he⟩ := hfinite C.1 (proper_card hC)
  let e₀ : PairIn C.1 := ⟨⟨(u,v),huv,ne_of_lt huv⟩,hu,hv⟩
  refine ⟨e₀,hl,?_⟩
  intro e hne
  apply he e.1.1.1 e.1.1.2 e.1.2.1 e.2.1 e.2.2
  by_contra hn
  push_neg at hn
  apply hne
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext hn.1 hn.2

def properPureBlock (C : BookBlock H) (hC : C.1≠ univ) :
    WeightedPureBlock C.1 1 (-blockClass C.1 (endpointCoefficients C.1 (fun a => (label a : ℝ)))) 2 := by
  let e₀ : PairIn C.1 := (proper_reference_exists C hC).choose
  have hv : label e₀.1.1.1+label e₀.1.1.2=0 ∨ label e₀.1.1.1+label e₀.1.1.2=2 :=
    (proper_reference_exists C hC).choose_spec.1
  have he : ∀ e : PairIn C.1,e≠ e₀ → label e.1.1.1+label e.1.1.2=1 :=
    (proper_reference_exists C hC).choose_spec.2
  let ε : ℝ := if label e₀.1.1.1+label e₀.1.1.2=0 then -1 else 1
  let w : PairIn C.1 → ℤ := fun e => if e=e₀ then 0 else 1
  have hε : ε=1 ∨ ε= -1 := by unfold ε; split_ifs <;> simp
  let P := signed_pair_basis C.1 (mem_largeBlocks.mp C.2).2 e₀ ε hε w
    (by simp [w]) (fun e he => by simp [w,he]) 1 (fun e he => by simp [w,he])
  have htarget : blockClass C.1 (ε • (fun e => (w e : ℝ)))=
      -blockClass C.1 (endpointCoefficients C.1 (fun a => (label a : ℝ))) := by
    have hc : blockClass C.1 ((ε • (fun e => (w e : ℝ)))+
        endpointCoefficients C.1 (fun a => (label a : ℝ)))=0 := by
      apply (blockClass_eq_zero_iff C.1 e₀ _).mpr
      refine ⟨((label e₀.1.1.1+label e₀.1.1.2 : ℤ) : ℝ),?_⟩
      intro e
      by_cases heq : e=e₀
      · subst e
        simp [w,endpointCoefficients]
      · have hh := he e heq
        rcases hv with hv | hv
        · have hh' : (label e.1.1.1 : ℝ)+(label e.1.1.2 : ℝ)=1 := by exact_mod_cast hh
          simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,w,if_neg heq,Int.cast_one,
            mul_one,endpointCoefficients,ε,if_pos hv,Int.cast_add]
          rw [hh']
          exact_mod_cast hv.symm
        · have hn : label e₀.1.1.1+label e₀.1.1.2≠0 := by omega
          have hh' : (label e.1.1.1 : ℝ)+(label e.1.1.2 : ℝ)=1 := by exact_mod_cast hh
          simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,w,if_neg heq,Int.cast_one,
            mul_one,endpointCoefficients,ε,if_neg hn,Int.cast_add]
          rw [hh']
          exact_mod_cast hv.symm
    rw [map_add] at hc
    exact eq_neg_of_add_eq_zero_left hc
  have hr : C.1.card.choose 2-1=2 := by rw [proper_card hC]; decide
  exact hr ▸ htarget ▸ P

abbrev fullBlock : BookBlock H := ⟨univ,by simp [mem_largeBlocks]⟩

def rank (C : BookBlock H) : ℕ := if C=fullBlock then 4 else 2

theorem anchor_extension : coefficientExtension anchors (fun _ => (1 : ℝ))=
    fun a => (label a : ℝ) := by
  funext a
  fin_cases a <;> norm_num [coefficientExtension,anchors,label]

def block (C : BookBlock H) :
    WeightedPureBlock C.1 1 (-((1*((-1 : ℝ)^(C.1.card-3))) • blockClass C.1
      (endpointCoefficients C.1 (coefficientExtension anchors (fun _ => ((1 : ℤ) : ℝ)))))) (rank C) := by
  classical
  by_cases hC : C=fullBlock
  · subst C
    rw [rank,if_pos rfl]
    refine {
      column := fullPureBlock.column
      realizable := fullPureBlock.realizable
      weight := fullPureBlock.weight
      positive := fullPureBlock.positive
      bounded := fullPureBlock.bounded
      independent := fullPureBlock.independent
      weighted_sum := ?_ }
    simp only [Int.cast_one]
    rw [fullPureBlock.weighted_sum,anchor_extension]
    simp [fullBlock]
  · have hCu : C.1≠ univ := fun h => hC (Subtype.ext h)
    rw [rank,if_neg hC]
    let P := properPureBlock C hCu
    refine {
      column := P.column
      realizable := P.realizable
      weight := P.weight
      positive := P.positive
      bounded := P.bounded
      independent := P.independent
      weighted_sum := ?_ }
    simp only [Int.cast_one]
    rw [P.weighted_sum,anchor_extension,proper_card hCu]
    norm_num

theorem block_full_column : (block fullBlock).column=column := by
  unfold block
  simp only [dite_true] <;> rfl

theorem scale_rigidity : ScopedAnchorRigidity anchors 1 (fun _ => 1) 1 rank block := by
  intro t ht
  let d := coefficientExtension anchors (fun a => t (.inl a))
  have h0 : d 0=0 := by simp [d,coefficientExtension,anchors]
  have h1 : d 1=0 := by simp [d,coefficientExtension,anchors]
  have hfull := ht fullBlock
  change blockClass Cfull ((1*((-1 : ℝ)^((fullBlock.1).card-3))) • endpointCoefficients Cfull d+
    ∑ j,t (.inr ⟨fullBlock,j⟩) • (block fullBlock).column j)=0 at hfull
  have hfactor : (1 : ℝ)*(-1)^((fullBlock.1).card-3)= -1 := by norm_num [fullBlock]
  rw [block_full_column,hfactor] at hfull
  have h23 := full_rigidity d h0 h1 (fun j => t (.inr ⟨fullBlock,j⟩)) hfull
  refine ⟨d 2,?_⟩
  intro a
  have ha : a.1=2 ∨ a.1=3 := by simpa only [anchors,mem_insert,mem_singleton] using a.2
  have hd : t (.inl a)=d a.1 :=
    (coefficientExtension_subtype anchors (fun b => t (.inl b)) a).symm
  simp only [Int.cast_one,mul_one]
  rw [hd]
  rcases ha with ha | ha
  · rw [ha]
  · rw [ha,h23]

end GraphicalZonotopes.BooleanModule.SaturatedFour

end
end
end BundlePart326

section BundlePart327
/- Source: Papers/GraphicalZonotopes/SaturatedFourAttainment.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes.BooleanModule.SaturatedFour
open Finset

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem circuit_card : Fintype.card (ScopedAnchorIndex anchors rank)=14 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem neighbor_count : ∀ a : Fin 4,
    (univ.filter (fun j : ScopedAnchorIndex anchors rank => a∈scopedAnchorScope anchors rank j)).card=12 := by
  decide

open scoped Classical

/-- The exceptional saturated four-hub circuit has six all-hub modules,
eight triple modules, and exactly twelve active spokes at each hub. -/
theorem spoke_attainment :
    ∃ f : SetFunction (Fin 4⊕Fin 14),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook 4 14) f ∧ FullDimension (basePolytope f) ∧
      LatticePolytope (basePolytope f) ∧
      ∀ a : Fin 4,(univ.filter (fun j : Fin 14 =>
        ActualRootEdge (basePolytope f) (Sum.inl a) (Sum.inr j))).card=12 := by
  let a₀ : anchors := ⟨2,by simp [anchors]⟩
  obtain ⟨f,hn,hi,he,hG,hd,hl,hcount⟩ := scoped_book_of_anchor_circuit
    anchors 1 (fun a => thresholdStar a.1) (fun a => by simp)
    (fun _ => 1) 1 rank block (by decide)
    (fun a => thresholdStar_boolean a.1)
    (fun a i => thresholdStar_essential (by decide) a.1 i) a₀
    (fun _ => by norm_num) scale_rigidity circuit_card
  exact ⟨f,hn,hi,he,hG,hd,hl,fun a => (hcount a).trans (neighbor_count a)⟩

end GraphicalZonotopes.BooleanModule.SaturatedFour

end
end
end BundlePart327

section BundlePart328
/- Source: Papers/GraphicalZonotopes/SaturatedBookArithmetic.lean -/




/-! # The closed formula for the optimal saturated-book hub degree

The integer-power exponent retains the paper's value (2^{-1}) when there
are three hubs.  The natural-number capacity difference is justified by
the proved monotonicity of clique capacity.
-/

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open BooleanModule

private theorem twice_choose_two_int (n : ℕ) (hn : 1 ≤ n) :
    (2 : ℤ) * (n.choose 2 : ℤ) = (n : ℤ) * ((n : ℤ) - 1) := by
  have h := Nat.add_one_mul_choose_eq (n - 1) 1
  have he : n - 1 + 1 = n := by omega
  have hnat : n * (n - 1) = n.choose 2 * 2 := by
    simpa only [he,Nat.choose_one_right] using h
  have hi : (n : ℤ) * ((n - 1 : ℕ) : ℤ) = (n.choose 2 : ℤ) * 2 := by
    exact_mod_cast hnat
  rw [Nat.cast_sub hn,Nat.cast_one] at hi
  nlinarith

theorem saturatedHubNeighbors_twice_formula {s : ℕ} (hs : 3 ≤ s) :
    (2 : ℤ) * (saturatedHubNeighbors s : ℤ) =
      ((s : ℤ)^2 + (s : ℤ) - 10) * (2 : ℤ)^(s - 3) + 4 := by
  have hmono := cliqueCapacity_pred_le (show 1 ≤ s by omega)
  have hu : (saturatedHubNeighbors s : ℤ) =
      (cliqueCapacity s : ℤ) - (cliqueCapacity (s - 1) : ℤ) + 1 := by
    rw [saturatedHubNeighbors,if_neg (by omega : s ≠ 2),Nat.cast_add,
      Nat.cast_sub hmono,Nat.cast_one]
  have hc := twice_choose_two_int s (by omega)
  have hp := twice_choose_two_int (s - 1) (by omega)
  rw [Nat.cast_sub (show 1 ≤ s by omega),Nat.cast_one] at hp
  have hcoef : 4 * (s.choose 2 : ℤ) - 2 * ((s - 1).choose 2 : ℤ) - 8 =
      (s : ℤ)^2 + (s : ℤ) - 10 := by nlinarith
  have hpow2 : (2 : ℤ)^(s - 2) = 2 * (2 : ℤ)^(s - 3) := by
    rw [show s - 2 = (s - 3) + 1 by omega,pow_add]
    norm_num <;> ring
  have hpow1 : (2 : ℤ)^(s - 1) = 4 * (2 : ℤ)^(s - 3) := by
    rw [show s - 1 = (s - 3) + 2 by omega,pow_add]
    norm_num <;> ring
  have hpow : (2 : ℤ)^s = 8 * (2 : ℤ)^(s - 3) := by
    calc
      (2 : ℤ)^s = (2 : ℤ)^((s - 3) + 3) := congrArg (fun n => (2 : ℤ)^n) (by omega)
      _ = _ := by rw [pow_add]; norm_num; ring
  calc
    (2 : ℤ) * (saturatedHubNeighbors s : ℤ) =
        (4 * (s.choose 2 : ℤ) - 2 * ((s - 1).choose 2 : ℤ) - 8) *
          (2 : ℤ)^(s - 3) + 4 := by
      rw [hu,cliqueCapacity_int_formula,cliqueCapacity_int_formula,
        show s - 1 - 2 = s - 3 by omega,hpow2,hpow1,hpow,
        Nat.cast_sub (show 1 ≤ s by omega),Nat.cast_one]
      ring
    _ = _ := by rw [hcoef]

/-- The numerical identity displayed in Theorem 7.12, including its
three-hub case with exponent (-1). -/
theorem saturatedHubNeighbors_closed_formula {s : ℕ} (hs : 3 ≤ s) :
    (saturatedHubNeighbors s : ℝ) =
      ((s : ℝ)^2 + (s : ℝ) - 10) * (2 : ℝ)^((s : ℤ) - 4) + 2 := by
  by_cases hs3 : s = 3
  · subst s
    norm_num [saturatedHubNeighbors,cliqueCapacity,Nat.choose]
  have hs4 : 4 ≤ s := by omega
  have hi := saturatedHubNeighbors_twice_formula hs
  have hr : (2 : ℝ) * (saturatedHubNeighbors s : ℝ) =
      ((s : ℝ)^2 + (s : ℝ) - 10) * (2 : ℝ)^(s - 3) + 4 := by
    exact_mod_cast hi
  have he : (s : ℤ) - 4 = ((s - 4 : ℕ) : ℤ) := by
    rw [Nat.cast_sub hs4]
    norm_num
  rw [he,zpow_natCast]
  have hp : (2 : ℝ)^(s - 3) = 2 * (2 : ℝ)^(s - 4) := by
    rw [show s - 3 = (s - 4) + 1 by omega,pow_add]
    norm_num <;> ring
  rw [hp] at hr
  nlinarith

end GraphicalZonotopes

end
end
end BundlePart328

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
