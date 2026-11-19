module
public import Papers.ActualEdgeSupports
public import Papers.IncidentTwoFacesCount
public import Cubical.Polytope.FiguraAlVertice
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# The actual incident two-face lower bound

A genuine vertex figure is constructed by vertexFigure_galois_exists.
The chosen edge becomes a vertex of that figure. Every neighboring vertex
of the figure lifts to a distinct actual two-face containing the original
edge. Thus the ordinary vertex-degree bound supplies the required count.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

/-- A zero-dimensional actual face is the singleton of an actual vertex. -/
theorem actual_zeroFace_is_vertex
    (P : ConvexPolytope d) (F : Set (E d))
    (hF : P.IsFace F) (hdim : faceDim F = 0) :
    ∃ x ∈ P.vertices, F = {x} := by
  obtain ⟨x,hFx⟩ := faccia_dim0_singoletto hF.2 hdim
  have hxext : x ∈ P.toSet.extremePoints ℝ := by
    have hs : IsExposed ℝ P.toSet ({x} : Set (E d)) := by
      simpa only [hFx] using hF.1
    exact hs.isExtreme.mem_extremePoints
  have hxV : x ∈ P.vertices := by
    change x ∈ (P.vertices : Set (E d))
    rw [P.vertices_eq_extremePoints]
    exact hxext
  exact ⟨x,hxV,hFx⟩

theorem incidentTwoFaces_card_actual
    (P : ConvexPolytope d) {x y : E d}
    (hx : x ∈ P.vertices) (hxy : GeneralVertexStep P x y) :
    P.dim ≤ (incidentTwoFaces P x y).card + 1 := by
  have he : P.IsFace (segment ℝ x y) :=
    segment_isFace_of_generalVertexStep P hx hxy
  have hedim : faceDim (segment ℝ x y) = 1 :=
    segment_faceDim_of_generalVertexStep P hx hxy
  have hxT : x ∈ P.toSet := vertex_mem_body_of_mem_vertices P hx
  have hPpos : 1 ≤ faceDim P.toSet := by
    have hle := Submodule.finrank_mono
      (vectorSpan_mono ℝ (face_subset_toSet P he))
    change faceDim (segment ℝ x y) ≤ faceDim P.toSet at hle
    rwa [hedim] at hle
  have hxFacePolytope : x ∈ (facePolytope P (toSet_isFace P)).vertices := by
    change x ∈ P.vertices.filter (· ∈ P.toSet)
    exact Finset.mem_filter.mpr ⟨hx,hxT⟩
  obtain ⟨D⟩ := vertexFigure_galois_exists P P.toSet (toSet_isFace P)
    x hxFacePolytope hPpos
  let Q := D.figure
  let edge : PositiveVertexStarFace P P.toSet x :=
    { carrier := segment ℝ x y
      isFace := he
      subset_base := face_subset_toSet P he
      mem_vertex := left_mem_segment ℝ _ _
      dim_pos := by rw [hedim] }
  have himage_dim : faceDim (D.faceEquiv edge).carrier = 0 := by
    have h := D.map_dim edge
    change faceDim (D.faceEquiv edge).carrier + 1 =
      faceDim (segment ℝ x y) at h
    rw [hedim] at h
    omega
  obtain ⟨q,hq,himage⟩ := actual_zeroFace_is_vertex Q
    (D.faceEquiv edge).carrier (D.faceEquiv edge).isFace himage_dim
  have hQdim : Q.dim + 1 = P.dim :=
    D.figure_dim_add_one (toSet_isFace P) hxT hPpos
  have hzStep (z : Papers.PolytopeVertexCone.actualNeighbors Q q) : GeneralVertexStep Q q z.val := by
    exact (Finset.mem_filter.mp z.property).2
  let liftFace (z : Papers.PolytopeVertexCone.actualNeighbors Q q) : PositiveVertexStarFace P P.toSet x :=
    D.faceEquiv.symm
      { carrier := segment ℝ q z.val
        isFace := segment_isFace_of_generalVertexStep Q hq (hzStep z) }
  have lift_image (z : Papers.PolytopeVertexCone.actualNeighbors Q q) :
      (D.faceEquiv (liftFace z)).carrier = segment ℝ q z.val := by
    simp only [liftFace,D.faceEquiv.apply_symm_apply]
  have lift_dim (z : Papers.PolytopeVertexCone.actualNeighbors Q q) : faceDim (liftFace z).carrier = 2 := by
    have h := D.map_dim (liftFace z)
    rw [lift_image,segment_faceDim_of_generalVertexStep Q hq (hzStep z)] at h
    omega
  have edge_subset_lift (z : Papers.PolytopeVertexCone.actualNeighbors Q q) :
      edge.carrier ⊆ (liftFace z).carrier := by
    apply (D.map_subset_iff edge (liftFace z)).mpr
    rw [himage,lift_image]
    exact Set.singleton_subset_iff.mpr (left_mem_segment ℝ _ _)
  let lift : (Papers.PolytopeVertexCone.actualNeighbors Q q) → incidentTwoFaces P x y := fun z =>
    ⟨⟨(liftFace z).carrier,(liftFace z).isFace⟩,by
      change (⟨(liftFace z).carrier,(liftFace z).isFace⟩ : ActualFaceType P) ∈
        Finset.univ.filter (fun F : ActualFaceType P =>
          faceDim F.val = 2 ∧ x ∈ F.val ∧ y ∈ F.val)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ (α := ActualFaceType P) _,
        lift_dim z,(liftFace z).mem_vertex,
        edge_subset_lift z (right_mem_segment ℝ _ _)⟩⟩
  have hlift : Function.Injective lift := by
    intro z w hzw
    have hcar : (liftFace z).carrier = (liftFace w).carrier :=
      congrArg (fun F : incidentTwoFaces P x y => F.val.val) hzw
    have hstar : liftFace z = liftFace w := PositiveVertexStarFace.ext hcar
    have hsegments : segment ℝ q z.val = segment ℝ q w.val := by
      have hh := congrArg (fun F : PositiveVertexStarFace P P.toSet x =>
        (D.faceEquiv F).carrier) hstar
      simpa only [lift_image] using hh
    have hwseg : w.val ∈ segment ℝ q z.val := by
      rw [hsegments]
      exact right_mem_segment ℝ _ _
    have hends := ExposedEdgeCenters.extreme_point_on_segment Q.toSet
      (vertex_mem_body_extremePoints Q (hzStep w).1)
      (vertex_mem_body_of_mem_vertices Q hq)
      (vertex_mem_body_of_mem_vertices Q (hzStep z).1) hwseg
    rcases hends with hwq | hwz
    · exact ((hzStep w).2.1 hwq.symm).elim
    · exact Subtype.ext hwz.symm
  exact incidentTwoFaces_card_from_vertexFigure P x y Q q hq hQdim lift hlift

theorem incidentTwoFaces_card_actual_fullDim
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    {x y : E d} (hx : x ∈ P.vertices) (hxy : GeneralVertexStep P x y) :
    d - 1 ≤ (incidentTwoFaces P x y).card := by
  have h := incidentTwoFaces_card_actual P hx hxy
  change P.dim = d at hP
  omega

end Papers.Polytopes

