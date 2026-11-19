module

public import Papers.GraphicalZonotopes.SetFunctionEmbeddingGeometry
public import Papers.GraphicalZonotopes.WeakSummandReduction

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
open SetFunctionEmbedding
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- Adding unused coordinates and then edges cannot lower the maximum
indecomposable-summand dimension. Every input is an actual real polytope. -/
theorem maximumIndecomposableDimension_le_of_embedding (e : V ↪ W)
    {G : SimpleGraph V} {H : SimpleGraph W} (hGH : G.map e≤H) :
    maximumIndecomposableDimension G≤maximumIndecomposableDimension H := by
  unfold maximumIndecomposableDimension
  apply csSup_le'
  rintro d ⟨Q,hQ,hi,hw,hd⟩
  obtain ⟨z,hz,he,hzd⟩ := weak_summand_extreme_or_zero hQ hi hw
  rw [← hd,hzd]
  rcases he with he | he
  · rw [he,basePolytope_zero]
    have hs : vectorSpan ℝ ({0} : Set (V → ℝ))=(⊥ : Submodule ℝ (V → ℝ)) :=
      _root_.vectorSpan_singleton ℝ (0 : V → ℝ)
    rw [hs,_root_.finrank_bot]
    exact Nat.zero_le _
  · have hfe := extend_extreme e he
    have hsub : G≤H.comap e := by
      intro u v huv
      exact hGH ((SimpleGraph.map_adj e G (e u) (e v)).mpr ⟨u,v,huv,rfl,rfl⟩)
    have hgg : Graphical H (extend e z.1) :=
      extend_graphical e (Graphical.mono_graph hsub z.2.2)
    have hgp : IsGeneralizedPermutahedron (basePolytope (extend e z.1)) :=
      ⟨extend e z.1,hfe.1.1,hfe.2.1,rfl⟩
    have hm := dimension_le_maximum hgp.finitePolytope hfe.minkowskiIndecomposable
      ((isWeakMinkowskiSummand_graphical_iff hfe.1.1 hfe.2.1).mpr hgg)
    rw [finrank_vectorSpan_extend e z.2.1] at hm
    exact hm

theorem graph_map_of_iso {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    G.map e.toEquiv.toEmbedding=H := by
  ext u v
  rw [SimpleGraph.map_adj]
  constructor
  · rintro ⟨x,y,hxy,rfl,rfl⟩
    exact e.map_adj_iff.mpr hxy
  · intro huv
    refine ⟨e.symm u,e.symm v,e.symm.map_adj_iff.mpr huv,?_,?_⟩ <;> simp

/-- The paper's dimension invariant is unchanged by an arbitrary graph
isomorphism, including a change of the finite coordinate type. -/
theorem maximumIndecomposableDimension_iso {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) : maximumIndecomposableDimension G=maximumIndecomposableDimension H := by
  apply le_antisymm
  · exact maximumIndecomposableDimension_le_of_embedding e.toEquiv.toEmbedding
      (le_of_eq (graph_map_of_iso e))
  · exact maximumIndecomposableDimension_le_of_embedding e.symm.toEquiv.toEmbedding
      (le_of_eq (graph_map_of_iso e.symm))

end GraphicalZonotopes
