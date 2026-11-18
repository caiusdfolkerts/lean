module

public import Papers.GraphicalZonotopes.PlanarCombinatorics
public import Papers.GraphicalZonotopes.PartialThreeTreeSupport
public import Papers.GraphicalZonotopes.ThreeTreeInducedEquality

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
