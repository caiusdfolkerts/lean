import cubical.polytope.vertex_slice_simplicial
import cubical.polytope.facet_geometry
import cubical.simplicial_embedding

/-! # Simplicial vertex figures and exact boundary-link identification -/

open Set Classical

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope Cubical.Simplicial

variable {n : ℕ} {P : ConvexPolytope n}

theorem simplex_face_adj {F : Set (E n)} (hF : P.IsFace F)
    (hi : AffineIndependent ℝ (fun v : VertexType (facePolytope P hF) => v.val))
    (u v : VertexType P) (huF : u.val ∈ F) (hvF : v.val ∈ F) (hne : u ≠ v) :
    (polytopeGraph P).Adj u v := by
  let uF : VertexType (facePolytope P hF) := ⟨u.val, Finset.mem_filter.mpr ⟨u.property, huF⟩⟩
  let vF : VertexType (facePolytope P hF) := ⟨v.val, Finset.mem_filter.mpr ⟨v.property, hvF⟩⟩
  have hneF : uF ≠ vF := by
    intro h
    exact hne (Subtype.ext
      (congrArg (fun q : VertexType (facePolytope P hF) => q.val) h))
  exact (facePolytope_graph_adj_iff P hF uF vF).mp
    (simplex_graph_adj _ hi uF vF hneF)

def simplexFaceNeighborEquiv {F : Set (E n)} (hF : P.IsFace F)
    (hi : AffineIndependent ℝ (fun v : VertexType (facePolytope P hF) => v.val))
    (v : VertexType P) (hvF : v.val ∈ F) :
    {a : VertexType P // a.val ∈ F ∧ (polytopeGraph P).Adj v a} ≃
      ↥((faceVertices P F).erase v) where
  toFun a := ⟨a.val, Finset.mem_erase.mpr
    ⟨a.property.2.ne.symm, (mem_faceVertices P F a.val).mpr a.property.1⟩⟩
  invFun a := ⟨a.val, (mem_faceVertices P F a.val).mp (Finset.mem_erase.mp a.property).2,
    simplex_face_adj hF hi v a.val hvF
      ((mem_faceVertices P F a.val).mp (Finset.mem_erase.mp a.property).2)
      (Finset.mem_erase.mp a.property).1.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem simplexFace_neighbor_card {F : Set (E n)} (hF : P.IsFace F)
    (hi : AffineIndependent ℝ (fun v : VertexType (facePolytope P hF) => v.val))
    (v : VertexType P) (hvF : v.val ∈ F) :
    Fintype.card {a : VertexType P // a.val ∈ F ∧ (polytopeGraph P).Adj v a} = faceDim F := by
  have h := Fintype.card_congr (simplexFaceNeighborEquiv hF hi v hvF)
  rw [Fintype.card_coe, Finset.card_erase_of_mem ((mem_faceVertices P F v).mpr hvF),
    faceVertices_card P hF] at h
  have hc := (vertices_affineIndependent_iff (facePolytope P hF)).mp hi
  rw [facePolytope_dim] at hc
  omega

namespace DatiFetta

variable {v : VertexType P} (D : DatiFetta P v.val)

/-- Reindex a slice vertex by the original edge's other endpoint. -/
def neighborEmbedding : VertexType D.politopo ↪ VertexType P where
  toFun q := (D.neighborEquiv.symm q).val
  inj' := by
    intro q r h
    apply D.neighborEquiv.symm.injective
    exact Subtype.ext h

theorem neighborEmbedding_ne_base (q : VertexType D.politopo) : D.neighborEmbedding q ≠ v :=
  (D.neighborEquiv.symm q).property.ne.symm

theorem map_slice_faceVertices {F : Set (E n)} (hF : P.IsFace F)
    (hvF : v.val ∈ F) (_hdF : 1 ≤ faceDim F)
    (hi : AffineIndependent ℝ (fun v : VertexType (facePolytope P hF) => v.val)) :
    (faceVertices D.politopo (F ∩ {x | D.l x = D.c})).map D.neighborEmbedding =
      (faceVertices P F).erase v := by
  ext a
  rw [Finset.mem_map, Finset.mem_erase, mem_faceVertices]
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨D.neighborEmbedding_ne_base q, ?_⟩
    apply (D.neighborEquiv_mem_slice_iff hF hvF (D.neighborEquiv.symm q)).mp
    simpa only [Equiv.apply_symm_apply] using
      ((mem_faceVertices D.politopo _ q).mp hq)
  · rintro ⟨hav, haF⟩
    have hva := simplex_face_adj hF hi v a hvF haF hav.symm
    let b : NeighborOf v := ⟨a, hva⟩
    refine ⟨D.neighborEquiv b, ?_, ?_⟩
    · exact (mem_faceVertices D.politopo _ _).mpr
        ((D.neighborEquiv_mem_slice_iff hF hvF b).mpr haF)
    · change (D.neighborEquiv.symm (D.neighborEquiv b)).val = a
      simp only [Equiv.symm_apply_apply]
      rfl

/-- Simpliciality is preserved by genuine geometric vertex figures. -/
theorem isSimplicial_of_simplicial (hs : IsSimplicial P) (hdim : 2 ≤ P.dim) :
    IsSimplicial D.politopo := by
  apply (isSimplicial_iff_facet_vertices_card D.politopo).mpr
  intro G hG hdG
  obtain ⟨F, hF, hvF, hdF, hslice⟩ := D.faccia_dalla_fetta hG
  have hdimension := D.fetta_faceDim hF hvF hdF
  rw [hslice] at hdimension
  have hdimFigure := D.politopo_dim_add_one (by omega)
  have hdFP : faceDim F + 1 = P.dim := by omega
  have hcount := Fintype.card_congr (D.neighborFaceSliceEquiv hF hvF hdF)
  rw [simplexFace_neighbor_card hF (hs F hF hdFP) v hvF] at hcount
  have hslice_count :
      (facePolytope D.politopo (D.faccia_fetta hF hvF hdF)).vertices.card = faceDim F := by
    simpa only [VertexType, Fintype.card_coe] using hcount.symm
  simpa only [hslice, show faceDim F = D.politopo.dim by omega] using hslice_count

/-- The boundary of the actual vertex figure is exactly the link in the
original simplicial boundary, under the geometric neighbor identification. -/
theorem boundary_mapFamily_eq_link (hs : IsSimplicial P) (hdim : 2 ≤ P.dim) :
    mapFamily D.neighborEmbedding (boundaryFacets D.politopo) =
      link (boundaryFacets P) {v} := by
  have hdimFigure := D.politopo_dim_add_one (by omega)
  ext r
  constructor
  · intro hr
    obtain ⟨t, ht, rfl⟩ := (mem_mapFamily D.neighborEmbedding _ r).mp hr
    obtain ⟨G, rfl⟩ := (mem_boundaryFacets D.politopo t).mp ht
    obtain ⟨F, hF, hvF, hdF, hslice⟩ := D.faccia_dalla_fetta G.val.property
    have hdimension := D.fetta_faceDim hF hvF hdF
    rw [hslice] at hdimension
    have hdG := G.property
    have hdFP : faceDim F + 1 = P.dim := by omega
    let f : FacetType P := ⟨⟨F, hF⟩, hdFP⟩
    have hmap := D.map_slice_faceVertices hF hvF hdF (hs F hF hdFP)
    rw [hslice] at hmap
    rw [hmap]
    apply Finset.mem_image.mpr
    refine ⟨faceVertices P F, Finset.mem_filter.mpr
      ⟨(mem_boundaryFacets P _).mpr ⟨f, rfl⟩, ?_⟩, ?_⟩
    · simpa using (mem_faceVertices P F v).mpr hvF
    · exact Finset.sdiff_singleton_eq_erase _ _
  · intro hr
    obtain ⟨t, ht, htr⟩ := Finset.mem_image.mp hr
    obtain ⟨htP, hvt⟩ := Finset.mem_filter.mp ht
    obtain ⟨F, rfl⟩ := (mem_boundaryFacets P t).mp htP
    have hvF : v.val ∈ F.val.val :=
      (mem_faceVertices P _ v).mp (hvt (Finset.mem_singleton_self v))
    have hdF := F.property
    have hdFpos : 1 ≤ faceDim F.val.val := by omega
    have hG := D.faccia_fetta F.val.property hvF hdFpos
    have hdimG := D.fetta_faceDim F.val.property hvF hdFpos
    let G : FacetType D.politopo := ⟨⟨_, hG⟩, by
      change faceDim (F.val.val ∩ {x | D.l x = D.c}) + 1 = D.politopo.dim
      omega⟩
    apply (mem_mapFamily D.neighborEmbedding _ r).mpr
    refine ⟨faceVertices D.politopo G.val.val,
      (mem_boundaryFacets D.politopo _).mpr ⟨G, rfl⟩, ?_⟩
    have hmap := D.map_slice_faceVertices F.val.property hvF hdFpos
      (hs F.val.val F.val.property F.property)
    exact hmap.trans ((Finset.sdiff_singleton_eq_erase _ _).symm.trans htr)

end DatiFetta

end LeanEval.Geometry.PlatonicClassification
