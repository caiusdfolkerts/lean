module

public import Papers.GraphicalZonotopes.ThreeTreeEmbedding
public import Papers.GraphicalZonotopes.SetFunctionEmbeddingDirections
public import Papers.GraphicalZonotopes.ThreeTreeClassification
public import Papers.GraphicalZonotopes.ConnectedDimension
public import Papers.GraphicalZonotopes.ThreeTreeLatticeCoefficients

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical BigOperators Pointwise

namespace GraphicalZonotopes
open Finset SetFunctionEmbedding RefinedTriangleComponents
variable {V : Type*} [Fintype V] [LinearOrder V]

theorem ActualRootEdge.root_mem_vectorSpan {Q : Set (V → ℝ)} {u v : V}
    (h : ActualRootEdge Q u v) : basisVector u-basisVector v∈vectorSpan ℝ Q := by
  obtain ⟨huv,p,q,⟨hpq,l,a,hl,hface⟩,c,hc,hdir⟩ := h
  have hp : p∈Q := by
    have hm := left_mem_segment ℝ p q
    rw [← hface] at hm
    exact hm.1
  have hq : q∈Q := by
    have hm := right_mem_segment ℝ p q
    rw [← hface] at hm
    exact hm.1
  have hv : q-p∈vectorSpan ℝ Q := vsub_mem_vectorSpan ℝ hq hp
  rw [hdir] at hv
  have hh := (vectorSpan ℝ Q).smul_mem c⁻¹ hv
  simpa only [smul_smul,inv_mul_cancel₀ hc,one_smul] using hh

theorem actualGraph_graphical {f : SetFunction V}
    (hn : Normalized f) (hs : Supermodular f) :
    Graphical (actualDirectionGraph (basePolytope f)) f := by
  intro u v huv hnon S hu hv
  by_contra hd
  exact hnon ((actualRootEdge_iff_nonzero_delta hn hs u v).mpr ⟨huv,S,hu,hv,hd⟩)

theorem threeTree_actual_nonzero {S : Finset V} {f : SetFunction V}
    (hn : Normalized f) (hs : Supermodular f)
    (h : ThreeTreeOn S (actualDirectionGraph (basePolytope f))) : f≠0 := by
  intro he
  obtain ⟨u,v,huv⟩ := h.exists_edge
  obtain ⟨_,T,_,_,hd⟩ := (actualRootEdge_iff_nonzero_delta hn hs u v).mp huv
  exact hd (by simp [he,delta])

theorem isThreeTree_comap_equiv {W : Type*} [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} (h : IsThreeTree G) (e : W ≃ V) :
    IsThreeTree (G.comap e.toEmbedding) := by
  have hh := h.comap e.toEmbedding (fun v _ => ⟨e.symm v,e.apply_symm_apply v⟩)
  change ThreeTreeOn univ _
  simpa only [pullSet_univ] using hh

/-- The checked full-dimensional 3-tree theorem transfers to every finite
vertex type by an actual coordinate equivalence. -/
theorem admissible_of_extreme_full {G : SimpleGraph V} (hG : IsThreeTree G)
    {f : SetFunction V} (hf : ExtremeSupermodular f) (hd : FullDimension (basePolytope f))
    (hg : Graphical G f) : Admissible G := by
  let e : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
  have htree : IsThreeTree (G.comap e.toEmbedding) := isThreeTree_comap_equiv hG e
  have hn : 4≤Fintype.card V := by
    simpa only [card_univ] using hG.active_card_ge_four
  have hrange : ∀ u v,G.Adj u v → u∈Set.range e.toEmbedding :=
    fun u _ _ => ⟨e.symm u,e.apply_symm_apply u⟩
  have hrec := reconstruct_of_graphical_supported e.toEmbedding hf.1 hg hrange
  let g := restrict e.toEmbedding f
  have hgext : ExtremeSupermodular g := extreme_restrict_of_reconstruction e.toEmbedding hf hrec
  have hdim : FullDimension (basePolytope g) := by
    have he := finrank_vectorSpan_extend e.toEmbedding (restrict_translationNormalized e.toEmbedding hf.1)
    rw [hrec] at he
    change Module.finrank ℝ (vectorSpan ℝ (basePolytope f))=Fintype.card V-1 at hd
    change Module.finrank ℝ (vectorSpan ℝ (basePolytope g))=Fintype.card (Fin (Fintype.card V))-1
    rw [Fintype.card_fin]
    exact he.symm.trans hd
  have hggraph : Graphical (G.comap e.toEmbedding) g := restrict_graphical e.toEmbedding hg
  have hsupport : SupportsFullIndecomposable (G.comap e.toEmbedding) :=
    ⟨basePolytope g,
      (show IsGeneralizedPermutahedron (basePolytope g) from ⟨g,hgext.1.1,hgext.2.1,rfl⟩).finitePolytope,
      hgext.minkowskiIndecomposable,hdim,
      (isWeakMinkowskiSummand_graphical_iff hgext.1.1 hgext.2.1).mpr hggraph⟩
  have hA := ((threeTree_supports_iff_admissible hn htree).mp hsupport).map e.toEmbedding
  rwa [map_comap_of_supported e.toEmbedding G hrange] at hA

/-- Admissible 3-trees on arbitrary finite coordinate types have integral
extreme witnesses with the exact actual direction graph and full dimension. -/
theorem admissible_threeTree_witness_fintype {G : SimpleGraph V}
    (hG : IsThreeTree G) (hA : Admissible G) :
    ∃ f : SetFunction V,ExtremeSupermodular f ∧ IntegerValued f ∧
      FullDimension (basePolytope f) ∧ actualDirectionGraph (basePolytope f)=G ∧ Graphical G f := by
  let e : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
  have htree := isThreeTree_comap_equiv hG e
  have hn : 4≤Fintype.card V := by simpa only [card_univ] using hG.active_card_ge_four
  have hAfin : Admissible (G.comap e.toEmbedding) := by
    have hh := hA.map e.symm.toEmbedding
    rwa [SimpleGraph.map_symm] at hh
  obtain ⟨g,hg,hint,_,_,hd,hactual,_⟩ := admissible_threeTree_construction hn htree hAfin
  have hgi : IntegerValued g := by
    rw [← zeta_mobius g]
    exact zeta_integerValued hint
  have hgg : Graphical (G.comap e.toEmbedding) g := by
    have hh := actualGraph_graphical hg.1.1 hg.2.1
    rwa [hactual] at hh
  have hrange : ∀ u v,G.Adj u v → u∈Set.range e.toEmbedding :=
    fun u _ _ => ⟨e.symm u,e.apply_symm_apply u⟩
  refine ⟨extend e.toEmbedding g,extend_extreme e.toEmbedding hg,extend_integer e.toEmbedding hgi,
    ?_,?_,extend_graphical e.toEmbedding hgg⟩
  · unfold FullDimension at hd ⊢
    rw [finrank_vectorSpan_extend e.toEmbedding hg.1]
    simpa only [Fintype.card_fin] using hd
  · rw [actualDirectionGraph_extend e.toEmbedding hg.1 hg.2.1,hactual,
      map_comap_of_supported e.toEmbedding G hrange]

/-- The active support is proved full-dimensional. Admissibility is then
deduced by applying the genuine full-dimensional theorem on that support. -/
theorem threeTree_actual_dimension_admissible {S : Finset V} {f : SetFunction V}
    (hf : ExtremeSupermodular f)
    (h : ThreeTreeOn S (actualDirectionGraph (basePolytope f))) :
    Module.finrank ℝ (vectorSpan ℝ (basePolytope f))=S.card-1 ∧
      Admissible (actualDirectionGraph (basePolytope f)) := by
  letI : DecidableEq S := (inferInstance : LinearOrder S).toDecidableEq
  let G := actualDirectionGraph (basePolytope f)
  let e : S ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  have hrange : ∀ u v,G.Adj u v → u∈Set.range e :=
    fun u v huv => ⟨⟨u,(h.edges_supported huv).1⟩,rfl⟩
  have hrec := reconstruct_of_graphical_supported e hf.1
    (actualGraph_graphical hf.1.1 hf.2.1) hrange
  let g := restrict e f
  have hg : ExtremeSupermodular g := extreme_restrict_of_reconstruction e hf hrec
  have hactual : actualDirectionGraph (basePolytope g)=G.comap e :=
    actualDirectionGraph_restrict e hf.1 hf.2.1 hrec
  have htree : IsThreeTree (actualDirectionGraph (basePolytope g)) := by
    rw [hactual]
    exact h.induce
  have hdim : FullDimension (basePolytope g) :=
    finrank_vectorSpan_eq_of_connected_roots (basePolytope_nonempty hg.1.1 hg.2.1)
      htree.connected (fun u v he =>
        ActualRootEdge.root_mem_vectorSpan (show ActualRootEdge (basePolytope g) u v from he))
  have hAr := admissible_of_extreme_full htree hg hdim
    (actualGraph_graphical hg.1.1 hg.2.1)
  have hA := hAr.map e
  rw [hactual,map_comap_of_supported e G hrange] at hA
  refine ⟨?_,hA⟩
  have he := finrank_vectorSpan_extend e hg.1
  rw [hrec] at he
  have hd : Module.finrank ℝ (vectorSpan ℝ (basePolytope g))=S.card-1 := by
    simpa only [FullDimension,Fintype.card_coe] using hdim
  exact he.trans hd

/-- The converse on an arbitrary active subset, preserving the literal
ambient graph and leaving every outside coordinate zero. -/
theorem admissible_threeTree_active_witness {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (hA : Admissible G) :
    ∃ f : SetFunction V,ExtremeSupermodular f ∧ IntegerValued f ∧
      Module.finrank ℝ (vectorSpan ℝ (basePolytope f))=S.card-1 ∧
      actualDirectionGraph (basePolytope f)=G ∧ Graphical G f := by
  letI : DecidableEq S := (inferInstance : LinearOrder S).toDecidableEq
  let e : S ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  have hrange : ∀ u v,G.Adj u v → u∈Set.range e :=
    fun u v huv => ⟨⟨u,(h.edges_supported huv).1⟩,rfl⟩
  have hmap := map_comap_of_supported e G hrange
  have hAr : Admissible (G.comap e) := Admissible.of_map e (by rwa [hmap])
  have htr : IsThreeTree (G.comap e) := h.induce
  obtain ⟨g,hg,hgi,hd,hactual,hgraph⟩ :=
    admissible_threeTree_witness_fintype (V := S) htr hAr
  refine ⟨extend e g,extend_extreme e hg,extend_integer e hgi,?_,?_,extend_graphical e hgraph⟩
  · rw [finrank_vectorSpan_extend e hg.1]
    simpa only [FullDimension,Fintype.card_coe] using hd
  · rw [actualDirectionGraph_extend e hg.1 hg.2.1,hactual,hmap]

end GraphicalZonotopes
