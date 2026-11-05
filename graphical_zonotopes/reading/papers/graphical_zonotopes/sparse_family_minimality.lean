module

public import Papers.GraphicalZonotopes.SparseFamilyGeometry
public import Papers.GraphicalZonotopes.ThreeTreePruneExtension
public import Papers.GraphicalZonotopes.ThreeTreeClassification
public import Papers.GraphicalZonotopes.DirectionBounds
public import Papers.GraphicalZonotopes.DiamondBookLargeDimension

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
