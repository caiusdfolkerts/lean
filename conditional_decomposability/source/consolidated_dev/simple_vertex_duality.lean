module
public import consolidated.deletion_geometry
public import consolidated_dev.intrinsic_figure_geometry

set_option Elab.async false

section BundlePart0
/- Source: Papers/SimpleFourFaces.lean -/





@[expose] public section

/-!
# The actual faces of a simplex and a simple vertex figure

All types in this file are ordinary exposed faces or actual extreme
vertices.  The finite subset description of a simplex is proved from its
geometric affine independence.  In particular, the local dual tetrahedron
at a simple vertex is a consequence of the genuine hyperplane-slice
vertex figure, including for polytopes of non-full ambient dimension.
-/

noncomputable section
namespace Papers.SimpleFour

open Set Module
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical

variable {n : ℕ}

abbrev Facet (P : ConvexPolytope n) :=
  {F : FaceType P // faceDim F.val + 1 = P.dim}

instance (P : ConvexPolytope n) : Fintype (Facet P) := Fintype.ofFinite _

def vertexSet (P : ConvexPolytope n) (F : Set (E n)) : Finset (VertexType P) :=
  Finset.univ.filter (fun v => v.val ∈ F)

@[simp] theorem mem_vertexSet (P : ConvexPolytope n) (F : Set (E n))
    (v : VertexType P) : v ∈ vertexSet P F ↔ v.val ∈ F := by
  simp [vertexSet]

def vertexHull (P : ConvexPolytope n) (s : Finset (VertexType P)) : Set (E n) :=
  convexHull ℝ ((s.image Subtype.val : Finset (E n)) : Set (E n))

theorem vertexSet_image (P : ConvexPolytope n) {F : Set (E n)} (hF : P.IsFace F) :
    (vertexSet P F).image Subtype.val = (facePolytope P hF).vertices := by
  ext x
  simp only [Finset.mem_image, mem_vertexSet, facePolytope, Finset.mem_filter]
  exact ⟨fun ⟨v,hv,hvx⟩ => hvx ▸ ⟨v.property,hv⟩,
    fun ⟨hx,hF⟩ => ⟨⟨x,hx⟩,hF,rfl⟩⟩

theorem vertexSet_card (P : ConvexPolytope n) {F : Set (E n)} (hF : P.IsFace F) :
    (vertexSet P F).card = (facePolytope P hF).vertices.card := by
  rw [← vertexSet_image P hF, Finset.card_image_of_injective _ Subtype.val_injective]

@[simp] theorem vertexHull_vertexSet (P : ConvexPolytope n) {F : Set (E n)}
    (hF : P.IsFace F) : vertexHull P (vertexSet P F) = F := by
  rw [vertexHull,vertexSet_image P hF]
  exact (face_eq_hull_vertices P hF).symm

@[simp] theorem vertexSet_vertexHull (P : ConvexPolytope n) (s : Finset (VertexType P)) :
    vertexSet P (vertexHull P s) = s := by
  have hsub : s.image Subtype.val ⊆ P.vertices := by
    rintro x hx
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hx
    exact v.property
  have h := vertices_filter_convexHull_subset P _ hsub
  ext v
  rw [mem_vertexSet]
  have hv := congrArg (fun t : Finset (E n) => v.val ∈ t) h
  simp only [Finset.mem_filter,v.property,true_and] at hv
  change v.val ∈ convexHull ℝ ((s.image Subtype.val : Finset (E n)) : Set (E n)) ↔ _
  rw [hv]
  constructor
  · rintro h
    obtain ⟨w,hw,heq⟩ := Finset.mem_image.mp h
    exact (Subtype.ext heq : w = v) ▸ hw
  · exact Finset.mem_image_of_mem _

theorem vertexSet_injective (P : ConvexPolytope n) :
    Function.Injective (fun F : FaceType P => vertexSet P F.val) := by
  intro F G h
  apply Subtype.ext
  change vertexSet P F.val = vertexSet P G.val at h
  rw [← vertexHull_vertexSet P F.property,← vertexHull_vertexSet P G.property,h]

theorem vertexSet_subset_iff (P : ConvexPolytope n) {F G : Set (E n)}
    (hF : P.IsFace F) (hG : P.IsFace G) :
    vertexSet P F ⊆ vertexSet P G ↔ F ⊆ G := by
  constructor
  · intro h
    rw [← vertexHull_vertexSet P hF,← vertexHull_vertexSet P hG]
    exact convexHull_mono (Finset.coe_subset.mpr (Finset.image_subset_image h))
  · intro h v hv
    exact (mem_vertexSet P G v).mpr (h ((mem_vertexSet P F v).mp hv))

theorem simplex_vertexHull_face (P : ConvexPolytope n)
    (hi : AffineIndependent ℝ (fun v : VertexType P => v.val))
    (s : Finset (VertexType P)) (hs : s.Nonempty) :
    P.IsFace (vertexHull P s) := by
  apply simplex_subset_isFace P hi _ _ (hs.image _)
  rintro x hx
  obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hx
  exact v.property

theorem simplex_vertexHull_dim (P : ConvexPolytope n)
    (hi : AffineIndependent ℝ (fun v : VertexType P => v.val))
    (s : Finset (VertexType P)) (hs : s.Nonempty) :
    faceDim (vertexHull P s) + 1 = s.card := by
  have h := simplex_subset_dimension P hi (s.image Subtype.val)
    (by rintro x hx; obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hx; exact v.property)
    (hs.image _)
  simpa only [Finset.card_image_of_injective _ Subtype.val_injective,vertexHull] using h

theorem simplex_facet_complement_singleton (P : ConvexPolytope n)
    (hi : AffineIndependent ℝ (fun v : VertexType P => v.val))
    (F : Facet P) : ∃ v : VertexType P, (vertexSet P F.val.val)ᶜ = {v} := by
  have hP := (vertices_affineIndependent_iff P).mp hi
  have hF := simplex_face_vertices_card P hi F.val.property
  rw [← vertexSet_card P F.val.property] at hF
  have htotal : Fintype.card (VertexType P) = P.dim + 1 := by
    simpa only [VertexType,Fintype.card_coe] using hP
  have hc : ((vertexSet P F.val.val)ᶜ).card = 1 := by
    rw [Finset.card_compl,htotal]
    have hd := F.property
    omega
  exact Finset.card_eq_one.mp hc

def facetMissingVertex (P : ConvexPolytope n)
    (hi : AffineIndependent ℝ (fun v : VertexType P => v.val))
    (F : Facet P) : VertexType P :=
  (simplex_facet_complement_singleton P hi F).choose

theorem facetMissingVertex_spec (P : ConvexPolytope n)
    (hi : AffineIndependent ℝ (fun v : VertexType P => v.val)) (F : Facet P) :
    vertexSet P F.val.val = Finset.univ.erase (facetMissingVertex P hi F) := by
  have h := (simplex_facet_complement_singleton P hi F).choose_spec
  change (vertexSet P F.val.val)ᶜ = {facetMissingVertex P hi F} at h
  ext v
  have hv := congrArg (fun s : Finset (VertexType P) => v ∈ s) h
  simp only [Finset.mem_compl,Finset.mem_singleton] at hv
  simp only [Finset.mem_erase,Finset.mem_univ,and_true]
  exact not_iff_not.mp (by simpa using hv)

theorem mem_facet_iff_ne_missing (P : ConvexPolytope n)
    (hi : AffineIndependent ℝ (fun v : VertexType P => v.val))
    (F : Facet P) (v : VertexType P) :
    v.val ∈ F.val.val ↔ v ≠ facetMissingVertex P hi F := by
  rw [← mem_vertexSet,facetMissingVertex_spec P hi F]
  simp

def simplexOppositeFacet (P : ConvexPolytope n)
    (hi : AffineIndependent ℝ (fun v : VertexType P => v.val))
    (hd : 1 ≤ P.dim) (v : VertexType P) : Facet P := by
  let s := (Finset.univ : Finset (VertexType P)).erase v
  have htotal : Fintype.card (VertexType P) = P.dim + 1 := by
    simpa only [VertexType,Fintype.card_coe] using (vertices_affineIndependent_iff P).mp hi
  have hs : s.Nonempty := by
    apply Finset.card_pos.mp
    simp only [s,Finset.card_erase_of_mem (Finset.mem_univ v),Finset.card_univ]
    omega
  refine ⟨⟨vertexHull P s,simplex_vertexHull_face P hi s hs⟩,?_⟩
  have h := simplex_vertexHull_dim P hi s hs
  simpa only [s,Finset.card_erase_of_mem (Finset.mem_univ v),Finset.card_univ,
    htotal,Nat.add_sub_cancel] using h

theorem oppositeFacet_vertexSet (P : ConvexPolytope n)
    (hi : AffineIndependent ℝ (fun v : VertexType P => v.val))
    (hd : 1 ≤ P.dim) (v : VertexType P) :
    vertexSet P (simplexOppositeFacet P hi hd v).val.val = Finset.univ.erase v :=
  vertexSet_vertexHull P _

def simplexFacetEquiv (P : ConvexPolytope n)
    (hi : AffineIndependent ℝ (fun v : VertexType P => v.val))
    (hd : 1 ≤ P.dim) : Facet P ≃ VertexType P where
  toFun := facetMissingVertex P hi
  invFun := simplexOppositeFacet P hi hd
  left_inv F := by
    apply Subtype.ext
    apply vertexSet_injective P
    change vertexSet P (simplexOppositeFacet P hi hd (facetMissingVertex P hi F)).val.val =
      vertexSet P F.val.val
    rw [oppositeFacet_vertexSet,facetMissingVertex_spec]
  right_inv v := by
    have h := facetMissingVertex_spec P hi (simplexOppositeFacet P hi hd v)
    rw [oppositeFacet_vertexSet] at h
    have hv : v ∉ (Finset.univ : Finset (VertexType P)).erase v := by simp
    rw [h] at hv
    have hv' : v = facetMissingVertex P hi (simplexOppositeFacet P hi hd v) := by
      simpa using hv
    exact hv'.symm

def facetStar (P : ConvexPolytope n) (v : VertexType P) : Finset (Facet P) :=
  Finset.univ.filter (fun F => v.val ∈ F.val.val)

@[simp] theorem mem_facetStar (P : ConvexPolytope n) (v : VertexType P) (F : Facet P) :
    F ∈ facetStar P v ↔ v.val ∈ F.val.val := by simp [facetStar]

def simpleFigure (P : ConvexPolytope n) (v : VertexType P) (hd : 1 ≤ P.dim) :
    DatiFetta P v.val := Classical.choice (esiste_datiFetta P v.property hd)

theorem simpleFigure_independent (P : ConvexPolytope n) (v : VertexType P)
    (hd : 1 ≤ P.dim) (hs : (polytopeGraph P).degree v = P.dim) :
    AffineIndependent ℝ (fun q : VertexType (simpleFigure P v hd).politopo => q.val) := by
  apply (vertices_affineIndependent_iff _).mpr
  rw [DatiFetta.vertices_card_eq_degree,hs]
  exact ((simpleFigure P v hd).politopo_dim_add_one hd).symm

end Papers.SimpleFour

end
end
end BundlePart0

section BundlePart1
/- Source: Papers/SimpleVertexDuality.lean -/



@[expose] public section

/-! # The genuine local dual simplex at a simple vertex -/

noncomputable section
namespace Papers.SimpleFour

open Set Module
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical

variable {n : ℕ} {P : ConvexPolytope n} {v : VertexType P}

def facetStarSliceEquiv (D : DatiFetta P v.val) (hd : 2 ≤ P.dim) :
    facetStar P v ≃ Facet D.politopo where
  toFun F :=
    let S : PositiveFaceStar P v :=
      ⟨F.val.val,(mem_facetStar P v F.val).mp F.property,
        by have h := F.val.property; omega⟩
    ⟨D.sliceFaceOrderIso S,by
      have h := D.sliceFaceOrderIso_dimension S
      have hD := D.politopo_dim_add_one (by omega)
      have hF := F.val.property
      change faceDim (D.sliceFaceOrderIso S).val + 1 = D.politopo.dim
      change faceDim (D.sliceFaceOrderIso S).val + 1 = faceDim F.val.val.val at h
      omega⟩
  invFun G :=
    let S := D.sliceFaceOrderIso.symm G.val
    let F : Facet P := ⟨S.val,by
      have h := D.sliceFaceOrderIso_dimension S
      have hD := D.politopo_dim_add_one (by omega)
      have hG := G.property
      rw [D.sliceFaceOrderIso.apply_symm_apply] at h
      omega⟩
    ⟨F,(mem_facetStar P v F).mpr S.property.1⟩
  left_inv F := by
    apply Subtype.ext
    apply Subtype.ext
    change (D.sliceFaceOrderIso.symm (D.sliceFaceOrderIso _)).val = _
    rw [D.sliceFaceOrderIso.symm_apply_apply]
  right_inv G := by
    apply Subtype.ext
    change D.sliceFaceOrderIso (D.sliceFaceOrderIso.symm G.val) = G.val
    exact D.sliceFaceOrderIso.apply_symm_apply G.val

@[simp] theorem facetStarSliceEquiv_carrier (D : DatiFetta P v.val)
    (hd : 2 ≤ P.dim) (F : facetStar P v) :
    (facetStarSliceEquiv D hd F).val.val = F.val.val.val ∩ {x | D.l x = D.c} := rfl

theorem figure_independent (D : DatiFetta P v.val) (hd : 1 ≤ P.dim)
    (hs : (polytopeGraph P).degree v = P.dim) :
    AffineIndependent ℝ (fun q : VertexType D.politopo => q.val) := by
  apply (vertices_affineIndependent_iff _).mpr
  rw [D.vertices_card_eq_degree,hs]
  exact (D.politopo_dim_add_one hd).symm

def cornerEquiv (D : DatiFetta P v.val) (hd : 2 ≤ P.dim)
    (hs : (polytopeGraph P).degree v = P.dim) :
    facetStar P v ≃ VertexType D.politopo :=
  (facetStarSliceEquiv D hd).trans
    (simplexFacetEquiv D.politopo (figure_independent D (by omega) hs)
      (by have h := D.politopo_dim_add_one (by omega); omega))

theorem facetStar_card (D : DatiFetta P v.val) (hd : 2 ≤ P.dim)
    (hs : (polytopeGraph P).degree v = P.dim) : (facetStar P v).card = P.dim := by
  have h := Fintype.card_congr (cornerEquiv D hd hs)
  simp only [Fintype.card_coe,VertexType] at h
  rw [D.vertices_card_eq_degree,hs] at h
  exact h

theorem slice_facet_vertex_iff (D : DatiFetta P v.val) (hd : 2 ≤ P.dim)
    (hs : (polytopeGraph P).degree v = P.dim) (F : facetStar P v)
    (q : VertexType D.politopo) :
    q.val ∈ F.val.val.val ∩ {x | D.l x = D.c} ↔ q ≠ cornerEquiv D hd hs F := by
  exact mem_facet_iff_ne_missing D.politopo (figure_independent D (by omega) hs)
    (facetStarSliceEquiv D hd F) q

theorem neighbor_slice_mem_iff (D : DatiFetta P v.val)
    {F : Set (E n)} (hF : P.IsFace F) (hvF : v.val ∈ F) (w : NeighborOf v) :
    (D.neighborEquiv w).val ∈ F ∩ {x | D.l x = D.c} ↔ w.val.val ∈ F := by
  constructor
  · intro hw
    obtain ⟨e,he,hde,hve,hwe⟩ := w.property.2
    have hes := (D.edge_slice_data he hde hve w.val.property hwe
      (DatiFetta.neighbor_ne_base w)).1
    have hsub : e ⊆ F := D.fetta_mono he hve hF hvF (by
      rw [hes]
      exact Set.singleton_subset_iff.mpr hw)
    exact hsub hwe
  · intro hw
    exact ⟨D.attra_mem_face hF hvF w.val.property hw (DatiFetta.neighbor_ne_base w),
      D.attra_level (D.hsep _ w.val.property (DatiFetta.neighbor_ne_base w))⟩

theorem neighbor_mem_facet_iff (D : DatiFetta P v.val) (hd : 2 ≤ P.dim)
    (hs : (polytopeGraph P).degree v = P.dim) (F : facetStar P v)
    (w : NeighborOf v) :
    w.val.val ∈ F.val.val.val ↔ D.neighborEquiv w ≠ cornerEquiv D hd hs F := by
  rw [← neighbor_slice_mem_iff D F.val.val.property
    ((mem_facetStar P v F.val).mp F.property) w]
  exact slice_facet_vertex_iff D hd hs F (D.neighborEquiv w)

def commonFacetEquiv (D : DatiFetta P v.val) (hd : 2 ≤ P.dim)
    (hs : (polytopeGraph P).degree v = P.dim) (w : NeighborOf v) :
    ↥(facetStar P v ∩ facetStar P w.val) ≃
      ((Finset.univ : Finset (VertexType D.politopo)).erase (D.neighborEquiv w)) where
  toFun F :=
    let f : facetStar P v := ⟨F.val,(Finset.mem_inter.mp F.property).1⟩
    ⟨cornerEquiv D hd hs f,Finset.mem_erase.mpr ⟨by
      have hw := (mem_facetStar P w.val F.val).mp (Finset.mem_inter.mp F.property).2
      exact ((neighbor_mem_facet_iff D hd hs f w).mp hw).symm,
      Finset.mem_univ _⟩⟩
  invFun q :=
    let F := (cornerEquiv D hd hs).symm q.val
    ⟨F.val,Finset.mem_inter.mpr ⟨F.property,(mem_facetStar P w.val F.val).mpr (by
      apply (neighbor_mem_facet_iff D hd hs F w).mpr
      rw [(cornerEquiv D hd hs).apply_symm_apply]
      exact (Finset.mem_erase.mp q.property).1.symm)⟩⟩
  left_inv F := by
    apply Subtype.ext
    change ((cornerEquiv D hd hs).symm
      (cornerEquiv D hd hs ⟨F.val,(Finset.mem_inter.mp F.property).1⟩)).val = F.val
    exact congrArg Subtype.val ((cornerEquiv D hd hs).symm_apply_apply
      ⟨F.val,(Finset.mem_inter.mp F.property).1⟩)
  right_inv q := by
    apply Subtype.ext
    exact (cornerEquiv D hd hs).apply_symm_apply _

theorem commonFacet_card (D : DatiFetta P v.val) (hd : 2 ≤ P.dim)
    (hs : (polytopeGraph P).degree v = P.dim) (w : NeighborOf v) :
    (facetStar P v ∩ facetStar P w.val).card + 1 = P.dim := by
  have h := Fintype.card_congr (commonFacetEquiv D hd hs w)
  simp only [Fintype.card_coe,Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ,VertexType] at h
  rw [D.vertices_card_eq_degree,hs] at h
  omega

end Papers.SimpleFour

end
end
end BundlePart1
