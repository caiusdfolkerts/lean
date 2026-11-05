module

public import Papers.GraphicalZonotopes.DiamondPaper
public import Papers.GraphicalZonotopes.ThreeTreeClassification

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
open Finset SetFunctionEmbedding
open scoped Pointwise
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- Coordinate relabelling preserves the actual full-dimensional weak-summand
existence assertion. No direction graph is assigned by definition. -/
theorem SupportsFullIndecomposable.map_equiv {G : SimpleGraph V}
    (e : V ≃ W) (hn : 2≤Fintype.card V) (h : SupportsFullIndecomposable G) :
    SupportsFullIndecomposable (G.map e.toEmbedding) := by
  obtain ⟨Q,hQ,hi,hd,hw⟩ := h
  obtain ⟨z,hz,he,hzd⟩ := weak_summand_extreme_or_zero hQ hi hw
  have hdf : Module.finrank ℝ (vectorSpan ℝ (basePolytope z.1))=Fintype.card V-1 := by
    rw [←hzd]
    exact hd
  rcases he with he | he
  · rw [he,basePolytope_zero,_root_.vectorSpan_singleton,_root_.finrank_bot] at hdf
    omega
  · have hfe := extend_extreme e.toEmbedding he
    have hsub : G≤(G.map e.toEmbedding).comap e.toEmbedding := by
      intro u v huv
      exact (SimpleGraph.map_adj e.toEmbedding G (e u) (e v)).mpr ⟨u,v,huv,rfl,rfl⟩
    have hgg : Graphical (G.map e.toEmbedding) (extend e.toEmbedding z.1) :=
      extend_graphical e.toEmbedding (Graphical.mono_graph hsub z.2.2)
    have hp : IsGeneralizedPermutahedron (basePolytope (extend e.toEmbedding z.1)) :=
      ⟨_,hfe.1.1,hfe.2.1,rfl⟩
    refine ⟨_,hp.finitePolytope,hfe.minkowskiIndecomposable,?_,
      (isWeakMinkowskiSummand_graphical_iff hfe.1.1 hfe.2.1).mpr hgg⟩
    change Module.finrank ℝ (vectorSpan ℝ (basePolytope (extend e.toEmbedding z.1)))=
      Fintype.card W-1
    rw [finrank_vectorSpan_extend e.toEmbedding z.2.1,hdf,Fintype.card_congr e]

namespace DiamondBook

/-- The literal geometric obstruction in Theorem 8.1: no spanning 3-tree
contained in the prescribed graph supports a full-dimensional indecomposable
weak Minkowski summand. -/
theorem no_supporting_spanning_threeTree :
    ¬∃ H : SimpleGraph (MultipartiteVertex 6),
      H≤twoSingletonGraph 2 6 ∧ IsThreeTree H ∧ SupportsFullIndecomposable H := by
  classical
  rintro ⟨H,hsub,htree,hsupport⟩
  let e := (sigmaGraphIso 6).toEquiv
  have hm : IsThreeTree (H.map e.toEmbedding) := by
    change ThreeTreeOn univ (H.map e.toEmbedding)
    simpa only [Finset.map_univ_equiv] using htree.map e.toEmbedding
  have hc : 2≤Fintype.card (MultipartiteVertex 6) := by
    norm_num [MultipartiteVertex,Fintype.card_sigma,Fin.sum_univ_succ]
  have hs := hsupport.map_equiv e hc
  have ha := (threeTree_supports_iff_admissible (by decide : 4≤10) hm).mp hs
  exact no_spanning_six_multipartite
    ⟨H,hsub,htree,Admissible.of_map e.toEmbedding ha⟩

/-- Both clauses of Theorem 8.1 with the second clause phrased directly in
terms of actual geometric supporting polytopes, in the paper's vertex model. -/
theorem paper_theorem_8_1_literal :
    (∀ k : ℕ,1≤k → maximumIndecomposableDimension (twoSingletonGraph 2 k)=min (k+3) 9) ∧
    (∃ Q : Set (MultipartiteVertex 6 → ℝ),
      LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧ FullDimension Q ∧
      IsMinkowskiSummand Q ((4 : ℝ) • graphicalZonotope (twoSingletonGraph 2 6)) ∧
      directionCount Q=25) ∧
    ¬∃ H : SimpleGraph (MultipartiteVertex 6),
      H≤twoSingletonGraph 2 6 ∧ IsThreeTree H ∧ SupportsFullIndecomposable H := by
  obtain ⟨Q,hQ,hi,hd,hs,he,_⟩ := diamond_witness_multipartite
  exact ⟨paper_theorem_8_1.1,⟨Q,hQ,hi,hd,hs,he⟩,no_supporting_spanning_threeTree⟩

end DiamondBook
end GraphicalZonotopes
