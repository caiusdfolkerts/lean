module

public import Papers.GraphicalZonotopes.TreeJoinSubtrees
public import Papers.GraphicalZonotopes.PartialThreeTreeSpectrum
public import Papers.GraphicalZonotopes.PolytopalDimension
public import Mathlib.Order.Basic

/-! # Corollary 6.9: the join of K₂ with an arbitrary finite tree

The maximum is over actual finite polytopes in the ambient coordinate space.
Every nonempty tree is covered, including the one-vertex tree. The invariant
s₃ counts vertices in ordinary connected subtrees of maximum degree three;
the equivalence of induced and arbitrary subtree presentations is proved in
TreeJoinSubtrees. The lower bound supplies an actual lattice witness.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.TreeJoin
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

def vertexOrder (V : Type*) [Fintype V] [DecidableEq V] : LinearOrder (Vertex V) :=
  let o : LinearOrder (Vertex V) :=
    LinearOrder.lift' (Fintype.equivFin (Vertex V)) (Fintype.equivFin (Vertex V)).injective
  { o with
    toDecidableEq := inferInstance
    compare := fun x y => @compareOfLessAndEq _ x y o.toLT (o.toDecidableLT x y) inferInstance
    compare_eq_compareOfLessAndEq := by intros; rfl }

local instance : LinearOrder (Vertex V) := vertexOrder V
local instance : DecidableEq (Vertex V) := (vertexOrder V).toDecidableEq

theorem isPartialThreeTree {T : SimpleGraph V} (hT : T.IsTree) :
    IsPartialThreeTree (graph T) := by
  by_cases hn : 2≤Fintype.card V
  · exact Or.inr ⟨graph T,isThreeTree hT hn,le_rfl⟩
  · apply Or.inl
    simp only [Vertex,Fintype.card_sum,Fintype.card_fin]
    omega

theorem summand_dimension_le {T : SimpleGraph V} (hT : T.IsTree)
    {Q : Set (Vertex V → ℝ)} (hQ : IsFinitePolytope Q)
    (hi : MinkowskiIndecomposable Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope (graph T))) :
    Module.finrank ℝ (vectorSpan ℝ Q)≤s3 T+1 := by
  letI : Nonempty V := hT.connected.nonempty
  by_cases hd : 3≤Module.finrank ℝ (vectorSpan ℝ Q)
  · obtain ⟨S,hcard,hactual,hS,hA,hD⟩ :=
      partial_threeTree_polytope_support (isPartialThreeTree hT) hQ hi hw hd
    obtain ⟨U,hSU,hn,ht,hm⟩ := induced_admissible_subtree hT.isAcyclic hS hA
    have hU := subtree_card_le_s3 ht hm
    rw [hSU,core_card] at hD
    omega
  · have hp := s3_pos T
    omega

theorem lattice_attainment {T : SimpleGraph V} (hT : T.IsTree) :
    ∃ Q : Set (Vertex V → ℝ),LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (graph T)) ∧
      Module.finrank ℝ (vectorSpan ℝ Q)=s3 T+1 := by
  letI : Nonempty V := hT.connected.nonempty
  obtain ⟨U,ht,hm,hU⟩ := s3_attained T
  by_cases hn : 2≤U.card
  · have htr := (induced_core_threeTree_iff hT.isAcyclic U hn).mpr ht
    have hA := (induced_core_admissible_iff hT.isAcyclic U).mpr hm
    obtain ⟨Q,hQ,hi,hw,ha,hd⟩ := induced_admissible_threeTree_witness htr hA
    refine ⟨Q,hQ,hi,hw,?_⟩
    rw [core_card,hU] at hd
    omega
  · have hpos := s3_pos T
    have hcard : U.card=1 := by omega
    obtain ⟨v,hv⟩ := card_eq_one.mp hcard
    have hc : (graph T).IsClique (core U) := by
      apply (core_clique_iff T U).mpr
      rw [hv]
      simp [SimpleGraph.isClique_singleton]
    obtain ⟨Q,hQ,hi,hw,hd⟩ := clique_simplex_witness
      (by rw [core_card]; omega : 2≤(core U).card) hc
    refine ⟨Q,hQ,hi,hw,?_⟩
    rw [core_card,hU] at hd
    omega

theorem maximum_dimension {T : SimpleGraph V} (hT : T.IsTree) :
    maximumIndecomposableDimension (graph T)=s3 T+1 := by
  apply le_antisymm
  · apply csSup_le'
    rintro d ⟨Q,hQ,hi,hw,hd⟩
    rw [←hd]
    exact summand_dimension_le hT hQ hi hw
  · obtain ⟨Q,hQ,hi,hw,hd⟩ := lattice_attainment hT
    have h := dimension_le_maximum hQ.finitePolytope hi hw
    rwa [hd] at h

theorem supports_full_iff {T : SimpleGraph V} (hT : T.IsTree) :
    SupportsFullIndecomposable (graph T) ↔ T.maxDegree≤3 := by
  constructor
  · rintro ⟨Q,hQ,hi,hd,hw⟩
    have h := summand_dimension_le hT hQ hi hw
    have hbound := s3_le_card T
    change Module.finrank ℝ (vectorSpan ℝ Q)=Fintype.card (Vertex V)-1 at hd
    simp only [Vertex,Fintype.card_sum,Fintype.card_fin] at hd
    have hdim : Module.finrank ℝ (vectorSpan ℝ Q)=Fintype.card V+1 := by
      simpa only [Nat.add_sub_cancel] using hd
    rw [hdim] at h
    exact (s3_eq_card_iff hT).mp
      (le_antisymm hbound (Nat.le_of_add_le_add_right h))
  · intro h
    have he := (s3_eq_card_iff hT).mpr h
    obtain ⟨Q,hQ,hi,hw,hd⟩ := lattice_attainment hT
    refine ⟨Q,hQ.finitePolytope,hi,?_,hw⟩
    change Module.finrank ℝ (vectorSpan ℝ Q)=Fintype.card (Vertex V)-1
    simp only [Vertex,Fintype.card_sum,Fintype.card_fin]
    rw [hd,he]
    omega

/-- The complete K₂*tree portion of Corollary 6.9, with the paper's ordinary
polytopal indecomposability convention and lattice attainment of the maximum. -/
theorem paper_corollary_6_9_tree_join (T : SimpleGraph V) (hT : T.IsTree) :
    (sSup {d : ℕ | ∃ Q : Set (Vertex V → ℝ),IsFinitePolytope Q ∧
      PolytopalMinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (graph T)) ∧
      Module.finrank ℝ (vectorSpan ℝ Q)=d})=s3 T+1 ∧
    ((∃ Q : Set (Vertex V → ℝ),IsFinitePolytope Q ∧
      PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (graph T))) ↔ T.maxDegree≤3) ∧
    ∃ Q : Set (Vertex V → ℝ),LatticePolytope Q ∧
      PolytopalMinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (graph T)) ∧
      Module.finrank ℝ (vectorSpan ℝ Q)=s3 T+1 := by
  refine ⟨?_,?_,?_⟩
  · rw [←maximumIndecomposableDimension_eq_polytopal_supremum]
    exact maximum_dimension hT
  · rw [←supportsFullIndecomposable_iff_polytopal_weak]
    exact supports_full_iff hT
  · obtain ⟨Q,hQ,hi,hw,hd⟩ := lattice_attainment hT
    exact ⟨Q,hQ,(weakSummand_indecomposable_iff_polytopal hQ.finitePolytope hw).mp hi,hw,hd⟩

end GraphicalZonotopes.TreeJoin
