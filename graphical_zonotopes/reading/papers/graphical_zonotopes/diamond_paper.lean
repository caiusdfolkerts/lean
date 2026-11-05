module

public import Papers.GraphicalZonotopes.DiamondPrincipal
public import Papers.GraphicalZonotopes.DiamondBookIsomorphism
public import Papers.GraphicalZonotopes.SetFunctionEmbeddingDirections
public import Papers.GraphicalZonotopes.ThreeTreeEmbedding
public import Papers.GraphicalZonotopes.PrincipalTargets

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.DiamondBook
open Finset SetFunctionEmbedding
open scoped Pointwise

/-- The obstruction survives the exact bijection to the paper's four-part
coordinate type. The transported object is an actual spanning 3-tree. -/
theorem no_spanning_six_multipartite :
    ¬HasAdmissibleSpanningThreeTree (twoSingletonGraph 2 6) := by
  classical
  rintro ⟨H,hH,hTree,hAdm⟩
  let e := (sigmaGraphIso 6).toEquiv.toEmbedding
  have hsub : H.map e≤graph 6 := by
    intro x y hxy
    obtain ⟨a,b,hab,rfl,rfl⟩ := (SimpleGraph.map_adj e H x y).mp hxy
    exact (sigmaGraphIso 6).map_adj_iff.mpr (hH hab)
  have htree : IsThreeTree (H.map e) := by
    change ThreeTreeOn univ (H.map e)
    have ht := hTree.map e
    simpa only [e,Finset.map_univ_equiv] using ht
  exact no_admissible_spanning_threeTree 6 (by norm_num)
    ⟨H.map e,hsub,htree,hAdm.map e⟩

/-- Every geometric property of the diamond witness is transported to the
literal multipartite coordinates used in the paper's statement. -/
theorem diamond_witness_multipartite :
    ∃ Q : Set (MultipartiteVertex 6 → ℝ),
      LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧ FullDimension Q ∧
      IsMinkowskiSummand Q ((4 : ℝ) • graphicalZonotope (twoSingletonGraph 2 6)) ∧
      directionCount Q=25 ∧ ¬HasAdmissibleSpanningThreeTree (twoSingletonGraph 2 6) := by
  classical
  let o : LinearOrder (MultipartiteVertex 6) :=
    LinearOrder.lift' (Fintype.equivFin (MultipartiteVertex 6))
      (Fintype.equivFin (MultipartiteVertex 6)).injective
  letI : LinearOrder (MultipartiteVertex 6) :=
    { o with
      toDecidableEq := inferInstance
      compare := fun x y => @compareOfLessAndEq _ x y o.toLT (o.toDecidableLT x y) inferInstance
      compare_eq_compareOfLessAndEq := by intros;rfl }
  let e := (graphIso 6).toEquiv.toEmbedding
  let z := extend e DiamondGeometry.function
  have hz : ExtremeSupermodular z := extend_extreme e DiamondGeometry.extreme
  have hi : IntegerValued z := extend_integer e DiamondGeometry.integerValued
  have hcomap : (twoSingletonGraph 2 6).comap e=graph 6 := by
    ext a b
    exact (graphIso 6).map_adj_iff
  have hg : Graphical (twoSingletonGraph 2 6) z := by
    apply extend_graphical e
    rw [hcomap]
    exact DiamondGeometry.graphical.mono_graph diamond_support_subgraph
  have hd : FullDimension (basePolytope z) := by
    change Module.finrank ℝ (vectorSpan ℝ (basePolytope z))=
      Fintype.card (MultipartiteVertex 6)-1
    change Module.finrank ℝ (vectorSpan ℝ (basePolytope
      (extend e DiamondGeometry.function)))=_
    rw [finrank_vectorSpan_extend e DiamondGeometry.normalized]
    have hh := DiamondGeometry.full_dimension
    change Module.finrank ℝ (vectorSpan ℝ (basePolytope DiamondGeometry.function))=9 at hh
    rw [hh]
    norm_num [MultipartiteVertex,Fintype.card_sigma,Fin.sum_univ_succ]
  have hsum : IsMinkowskiSummand (basePolytope z)
      ((4 : ℝ) • graphicalZonotope (twoSingletonGraph 2 6)) := by
    apply (isMinkowskiSummand_graphical_iff hz.1.1 hz.2.1
      (by norm_num : (0 : ℝ)≤4)).mpr
    refine ⟨hg,?_⟩
    intro u v huv _ S hu hv
    have heval (x : Vertex 6) : e x=(graphIso 6).toEquiv x := rfl
    have hsurj : Function.Surjective e := by
      intro y
      obtain ⟨x,hx⟩ := (graphIso 6).toEquiv.surjective y
      exact ⟨x,(heval x).trans hx⟩
    obtain ⟨a,rfl⟩ := hsurj u
    obtain ⟨b,rfl⟩ := hsurj v
    change delta (extend e DiamondGeometry.function) (e a) (e b) S≤4
    rw [delta_extend]
    exact (DiamondGeometry.elemental_bounds
      (fun he => huv (congrArg e he))
      (by simpa only [mem_pullSet] using hu)
      (by simpa only [mem_pullSet] using hv)).2
  refine ⟨basePolytope z,hi.basePolytope hz.1.1 hz.2.1,
    hz.minkowskiIndecomposable,hd,hsum,?_,no_spanning_six_multipartite⟩
  change directionCount (basePolytope (extend e DiamondGeometry.function))=25
  rw [directionCount_extend e DiamondGeometry.normalized DiamondGeometry.supermodular]
  exact DiamondGeometry.direction_count

/-- Theorem 8.1 in the paper's exact vertex model, with both the unrestricted
dimension formula and every property of the extremal six-branch witness. -/
theorem paper_theorem_8_1 : Targets.DiamondBookClassification := by
  refine ⟨?_,diamond_witness_multipartite⟩
  intro k hk
  rw [← maximum_dimension_model_eq]
  exact maximum_dimension k hk

end GraphicalZonotopes.DiamondBook
