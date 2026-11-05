module

public import Papers.GraphicalZonotopes.PartialThreeTreeGraph
public import Papers.GraphicalZonotopes.ThreeTreeActiveGeometry
public import Papers.GraphicalZonotopes.WeakSummandReduction
public import Papers.GraphicalZonotopes.PolytopalWeakSummands

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators Pointwise
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [LinearOrder V]

namespace RefinedTriangleComponents
open PositiveDecomposition

private theorem adjusted_zero_function' : adjusted (0 : SetFunction V) = 0 := by
  have ha : allocation (0 : SetFunction V) = 0 := by
    funext C
    by_cases hC : C.card = 2
    · obtain ⟨u,v,huv,rfl⟩ := card_eq_two.mp hC
      rw [allocation_pair _ huv]
      have hm : minimumSlack (0 : SetFunction V) u v = 0 :=
        minimumSlack_eq_zero (by intros; simp [delta])
      simp [hm]
    · exact allocation_zero _ hC
  rw [adjusted,ha]
  change 0+zetaLinear 0=0
  simp

/-- Positive decomposition also identifies the unique interacting clique
class without assuming full ambient dimension. The dimension hypothesis
rules out the segment and isolated-triangle pieces. -/
theorem extreme_has_component_of_dimension_ge_three {z : SetFunction V}
    (hz : ExtremeSupermodular z)
    (hdim : 3 ≤ Module.finrank ℝ (vectorSpan ℝ (basePolytope z)))
    (hdegree : ∀ C,mobius z C ≠ 0 → C.card ≤ 4) :
    ∃ a : Component (mobius z),∃ t : ℝ,0 < t ∧
      adjusted (higherClass (mobius z) (classOf (mobius z)) (Sum.inl a)) = t • z ∧
      DependsOn z ((family (mobius z)).biUnion id) := by
  classical
  let y := mobius z
  have hy : y ∅ = 0 ∧ ∀ v,y {v} = 0 :=
    (zeta_normalized_iff y).mp (by simpa [y] using hz.1)
  obtain ⟨hp,he⟩ := pieces_positive hy hdegree (by simpa [y] using hz.2.1)
  have hez : (∑ i,pieces y i) = z := by simpa [y] using he
  have hex : ∃ i,pieces y i ≠ 0 := by
    by_contra h
    push_neg at h
    have hzero : (∑ i,pieces y i) = 0 := sum_eq_zero (fun i _ => h i)
    exact hz.2.2.1 (hez.symm.trans hzero)
  obtain ⟨i,hi⟩ := hex
  obtain ⟨t,ht,hscale⟩ := hz.finite_summand (pieces y)
    (fun i => (hp i).1) (fun i => (hp i).2) hez hi
  have hsupport : ∀ S,DependsOn (pieces y i) S → 4 ≤ S.card := by
    intro S hS
    rw [hscale] at hS
    have hb := finrank_vectorSpan_le_support hz.1 hz.2.1
      (DependsOn.of_smul (ne_of_gt ht) hS)
    omega
  cases i with
  | inr C =>
    have hC : C.card = 2 := by
      by_contra hnot
      have hzC := residual_zero y (higherClass y (classOf y)) hnot
      exact hi (by simp [pieces,hzC])
    have hdep : DependsOn (pieces y (Sum.inr C)) C := (setMonomial_dependsOn C).smul _
    have hc := hsupport C hdep
    omega
  | inl c =>
    cases c with
    | inr T =>
      have hT : T.card = 3 := by
        by_contra hnot
        have hzero := higher_right_zero_of_card_ne_three hdegree hnot
        exact hi (by simp only [y,pieces,Sum.elim_inl,hzero,adjusted_zero_function'])
      have hdep := PositiveDecomposition.DependsOn.adjusted
        (higher_right_dependsOn hdegree T)
      have hc := hsupport T hdep
      omega
    | inl a =>
      have hdep := PositiveDecomposition.DependsOn.adjusted
        (higher_left_dependsOn hdegree a)
      refine ⟨a,t,ht,hscale,?_⟩
      change DependsOn (pieces y (Sum.inl (Sum.inl a))) ((family y).biUnion id) at hdep
      rw [hscale] at hdep
      exact DependsOn.of_smul (ne_of_gt ht) hdep

/-- Corollary 4.4 in its full, possibly lower-dimensional form: the actual
edge directions are precisely the union of the nonzero tetrahedral
coefficients, and that family is connected through triangles. -/
theorem refined_support_of_dimension_ge_three {G : SimpleGraph V}
    (hG : G.CliqueFree 5) {z : SetFunction V} (hz : ExtremeSupermodular z)
    (hgraph : Graphical G z)
    (hdim : 3 ≤ Module.finrank ℝ (vectorSpan ℝ (basePolytope z))) :
    (family (mobius z)).Nonempty ∧
      (tetrahedronGraph (family (mobius z))).Preconnected ∧
      actualDirectionGraph (basePolytope z) = edgeGraph (mobius z) ∧
      DependsOn z ((family (mobius z)).biUnion id) := by
  classical
  let y := mobius z
  have hy : CliqueSupported G y := (mobius_cliqueSupported_iff G z).mpr ⟨hz.1,hgraph⟩
  have hdegree : ∀ C,y C ≠ 0 → C.card ≤ 4 := fun C hC => nonzero_card_le_four hG hy hC
  obtain ⟨a,t,ht,hscale,hdep⟩ := extreme_has_component_of_dimension_ge_three hz hdim hdegree
  have hcomp := same_component_of_positive_piece a (ne_of_gt ht)
    (by simpa only [zeta_mobius] using hscale)
  have hconnected : (tetrahedronGraph (family y)).Preconnected := by
    intro C D
    exact SimpleGraph.ConnectedComponent.exact ((hcomp C).trans (hcomp D).symm)
  have hne : (family y).Nonempty := by
    obtain ⟨C,hC⟩ := a.exists_rep
    exact ⟨C.1,C.2⟩
  refine ⟨hne,hconnected,?_,hdep⟩
  have hpiece : Graphical (edgeGraph y)
      (adjusted (higherClass y (classOf y) (Sum.inl a))) :=
    adjusted_graphical ((cliqueSupported_iff _ _).mp (left_coefficients_supported hdegree a)).2
  have hzedge : Graphical (edgeGraph y) z := by
    intro u v huv hnon S hu hv
    have h := hpiece u v huv hnon S hu hv
    rw [hscale,delta_smul] at h
    exact mul_left_cancel₀ (ne_of_gt ht) (by simpa using h)
  ext u v
  constructor
  · intro h
    exact actualRootEdge_of_graphical hz.1.1 hz.2.1 hzedge h
  · rintro ⟨huv,C,hC,hu,hv⟩
    exact actualRootEdge_of_nonzero_coefficient hz.1.1 hz.2.1
      ((mem_family y C).mp hC).2 huv hu hv

end RefinedTriangleComponents

open RefinedTriangleComponents

/-- Necessity in Corollary 6.6 on the actual active coordinate set. -/
theorem partial_threeTree_extreme_support {G : SimpleGraph V} (hG : IsPartialThreeTree G)
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
    ((hG.induced_edge_bound U (by omega)).trans hlow)
  have htreeH : ThreeTreeOn U (actualDirectionGraph (basePolytope z)) := by
    change ThreeTreeOn U H
    rw [heq]
    exact htree
  obtain ⟨hdim,hA⟩ := threeTree_actual_dimension_admissible hz htreeH
  exact ⟨U,hU,heq,htree,heq ▸ hA,hdim⟩

/-- Actual weak summands have normalized lower-support functions preserving
both affine dimension and the literal graph of exposed edge directions. -/
theorem weak_summand_normalized_function {G : SimpleGraph V} {Q : Set (V → ℝ)}
    (hQ : IsFinitePolytope Q) (hi : MinkowskiIndecomposable Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope G)) :
    ∃ z : graphicalFunctionSpace G,Supermodular z.1 ∧
      (z.1 = 0 ∨ ExtremeSupermodular z.1) ∧
      Module.finrank ℝ (vectorSpan ℝ Q) = Module.finrank ℝ (vectorSpan ℝ (basePolytope z.1)) ∧
      actualDirectionGraph Q = actualDirectionGraph (basePolytope z.1) := by
  obtain ⟨c,hc,R,hR,hRc,hnR,hQR⟩ := hw
  have hTn : Normalized (c • graphFunction G) := by
    change c*graphFunction G ∅=0
    rw [graphFunction_normalized,mul_zero]
  have hTs := (graphFunction_supermodular G).smul hc.le
  have hbase : Q+R=basePolytope (c • graphFunction G) := by
    rw [basePolytope_smul (graphFunction_normalized G) (graphFunction_supermodular G) hc.le,
      baseGraphFunction_eq_graphicalZonotope]
    exact hQR
  let f := lowerSupport Q
  have hfn : Normalized f := lowerSupport_normalized hQ.compact hi.1
  have hfs : Supermodular f := summand_lowerSupport_supermodular hTn hTs
    hQ.compact hR hi.1 hnR hbase
  have hbody : Q=basePolytope f := summand_eq_basePolytope hTn hTs
    hQ.compact hR hQ.convex hi.1 hnR hbase
  have hgf : Graphical G f := by
    apply ((isMinkowskiSummand_graphical_iff hfn hfs hc.le).mp ?_).1
    rw [← hbody]
    exact ⟨R,hR,hRc,hnR,hQR⟩
  have hgn : Graphical G (normalize f) := by
    intro u v huv hnon S hu hv
    rw [delta_normalize f huv hu hv]
    exact hgf u v huv hnon S hu hv
  refine ⟨⟨normalize f,normalize_translationNormalized hfn,hgn⟩,hfs.normalize,?_,?_,?_⟩
  · by_cases hz : normalize f=0
    · exact Or.inl hz
    · exact Or.inr (MinkowskiIndecomposable.extremeSupermodular_normalize
        hfn hfs hz (hbody ▸ hi))
  · rw [vectorSpan_basePolytope_normalize,← hbody]
  · rw [actualDirectionGraph_normalize,← hbody]

/-- Corollary 6.6, necessity for ordinary polytopes, with no full-dimension
assumption on the ambient coordinate space. -/
theorem partial_threeTree_polytope_support {G : SimpleGraph V}
    (hG : IsPartialThreeTree G) {Q : Set (V → ℝ)} (hQ : IsFinitePolytope Q)
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
  obtain ⟨U,hU,ha,ht,hA,hD⟩ := partial_threeTree_extreme_support hG hext z.2.2 hdz
  exact ⟨U,hU,hgraph.trans ha,ht,hA,hdim.trans hD⟩

/-- The converse in Corollary 6.6 supplies a lattice representative on every
permitted induced support and fixes all coordinates outside that support. -/
theorem induced_admissible_threeTree_witness {G : SimpleGraph V} {U : Finset V}
    (hU : ThreeTreeOn U (inducedOn G U)) (hA : Admissible (inducedOn G U)) :
    ∃ Q : Set (V → ℝ),LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
      actualDirectionGraph Q = inducedOn G U ∧
      Module.finrank ℝ (vectorSpan ℝ Q) = U.card-1 := by
  obtain ⟨f,hf,hi,hd,ha,hg⟩ := admissible_threeTree_active_witness hU hA
  refine ⟨basePolytope f,hi.basePolytope hf.1.1 hf.2.1,hf.minkowskiIndecomposable,?_,ha,hd⟩
  exact (isWeakMinkowskiSummand_graphical_iff hf.1.1 hf.2.1).mpr
    (hg.mono_graph (inducedOn_le G U))

/-- The complete actual-direction-support classification of Corollary 6.6.
The graph on the right is induced on its active vertices; vertices outside
it are isolated. Both implications quantify over arbitrary finite graphs. -/
theorem partial_threeTree_support_classification {G : SimpleGraph V}
    (hG : IsPartialThreeTree G) (H : SimpleGraph V) :
    (∃ Q : Set (V → ℝ),IsFinitePolytope Q ∧ MinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
      3 ≤ Module.finrank ℝ (vectorSpan ℝ Q) ∧ actualDirectionGraph Q = H) ↔
    ∃ U : Finset V,H = inducedOn G U ∧ ThreeTreeOn U H ∧ Admissible H := by
  constructor
  · rintro ⟨Q,hQ,hi,hw,hd,rfl⟩
    obtain ⟨U,hU,ha,ht,hA,hD⟩ := partial_threeTree_polytope_support hG hQ hi hw hd
    exact ⟨U,ha,ha.symm ▸ ht,ha.symm ▸ hA⟩
  · rintro ⟨U,rfl,ht,hA⟩
    obtain ⟨Q,hQ,hi,hw,ha,hd⟩ := induced_admissible_threeTree_witness ht hA
    have hU := ht.active_card_ge_four
    refine ⟨Q,?_,hi,hw,?_,ha⟩
    · exact hQ.finitePolytope
    · omega

end GraphicalZonotopes
