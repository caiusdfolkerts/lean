module

public import Papers.GraphicalZonotopes.SaturatedBookLower
public import Papers.GraphicalZonotopes.BookEdgeCounting
public import Papers.GraphicalZonotopes.SummandEdges

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
