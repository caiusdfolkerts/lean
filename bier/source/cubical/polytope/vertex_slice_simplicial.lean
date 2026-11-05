import cubical.polytope.vertex_slice_counts
import cubical.polytope.cube_face_counts
import cubical.polytope.simplicial_polytope

/-! # Vertex figures of cubical polytopes are geometrically simplicial -/

open Set
open Classical

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ} {P : ConvexPolytope n}

namespace DatiFetta

variable {v : VertexType P} (D : DatiFetta P v.val)

theorem neighborEquiv_mem_slice_iff {F : Set (E n)} (hF : P.IsFace F)
    (hvF : v.val ∈ F) (a : NeighborOf v) :
    (D.neighborEquiv a).val ∈ F ∩ {x | D.l x = D.c} ↔ a.val.val ∈ F := by
  constructor
  · intro ha
    obtain ⟨e, he, hde, hve, hae⟩ := a.property.2
    have hes := (D.edge_slice_data he hde hve a.val.property hae (neighbor_ne_base a)).1
    have heF : e ⊆ F := D.fetta_mono he hve hF hvF (by
      rw [hes]
      exact Set.singleton_subset_iff.mpr ha)
    exact heF hae
  · intro haF
    exact ⟨D.attra_mem_face hF hvF a.val.property haF (neighbor_ne_base a),
      D.attra_level (D.hsep _ a.val.property (neighbor_ne_base a))⟩

/-- Vertices of a slice-face are exactly edges of the original face at the
cut-off vertex. This is a bijection of actual geometric points. -/
def neighborFaceSliceEquiv {F : Set (E n)} (hF : P.IsFace F)
    (hvF : v.val ∈ F) (hdF : 1 ≤ faceDim F) :
    {a : VertexType P // a.val ∈ F ∧ (polytopeGraph P).Adj v a} ≃
      VertexType (facePolytope D.politopo (D.faccia_fetta hF hvF hdF)) := by
  let e : {a : VertexType P // a.val ∈ F ∧ (polytopeGraph P).Adj v a} ≃
      {a : NeighborOf v // a.val.val ∈ F} :=
    { toFun := fun a => ⟨⟨a.val, a.property.2⟩, a.property.1⟩
      invFun := fun a => ⟨a.val.val, a.property, a.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact e.trans ((D.neighborEquiv.subtypeEquiv
    (fun a => (D.neighborEquiv_mem_slice_iff hF hvF a).symm)).trans
      (faceVertexEquiv D.politopo (D.faccia_fetta hF hvF hdF)).symm)

theorem face_vertices_card_of_cubical (hc : IsCubical P) (hdim : 2 ≤ P.dim)
    {G : Set (E n)} (hG : D.politopo.IsFace G) (hdG : faceDim G < D.politopo.dim) :
    (facePolytope D.politopo hG).vertices.card = faceDim G + 1 := by
  obtain ⟨F, hF, hvF, hdF, hslice⟩ := D.faccia_dalla_fetta hG
  have hdimension := D.fetta_faceDim hF hvF hdF
  rw [hslice] at hdimension
  have hdimFigure := D.politopo_dim_add_one (by omega)
  have hdFP : faceDim F < P.dim := by omega
  have hcount := Fintype.card_congr (D.neighborFaceSliceEquiv hF hvF hdF)
  rw [hc.face_neighbor_card P hdim hF hdFP v hvF] at hcount
  have hslice_count :
      (facePolytope D.politopo (D.faccia_fetta hF hvF hdF)).vertices.card = faceDim F := by
    simpa [VertexType] using hcount.symm
  simpa only [hslice, hdimension] using hslice_count

/-- A vertex figure of a cubical polytope is simplicial in the usual geometric sense. -/
theorem isSimplicial_of_cubical (hc : IsCubical P) (hdim : 2 ≤ P.dim) :
    IsSimplicial D.politopo := by
  apply (isSimplicial_iff_facet_vertices_card D.politopo).mpr
  intro G hG hdG
  rw [D.face_vertices_card_of_cubical hc hdim hG (by omega)]
  exact hdG

end DatiFetta

end LeanEval.Geometry.PlatonicClassification
