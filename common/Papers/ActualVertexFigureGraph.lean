module
public import Papers.IncidentTwoFacesActual

@[expose] public section

/-!
# Vertices and edges of a genuine vertex figure

The figure is the actual polytope supplied by the proved Galois construction.
Its vertices are in bijection with actual neighbors of the base vertex.
Its edges correspond precisely to actual two-faces through that vertex.
-/

noncomputable section
namespace Papers.Polytopes.ActualVertexFigure

open Set Module
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem exists_figure (P : ConvexPolytope d) {x : E d}
    (hx : x ∈ P.vertices) (hpos : 1 ≤ P.dim) :
    Nonempty (VertexFigureGaloisData P P.toSet x) := by
  have hxT := vertex_mem_body_of_mem_vertices P hx
  have hxF : x ∈ (facePolytope P (toSet_isFace P)).vertices := by
    change x ∈ P.vertices.filter (· ∈ P.toSet)
    exact Finset.mem_filter.mpr ⟨hx,hxT⟩
  exact vertexFigure_galois_exists P P.toSet (toSet_isFace P) x hxF hpos

theorem neighbor_step (P : ConvexPolytope d) (x : E d)
    (y : Papers.PolytopeVertexCone.actualNeighbors P x) : GeneralVertexStep P x y.val :=
  (Finset.mem_filter.mp y.property).2

def neighborVertex (P : ConvexPolytope d) (x : E d)
    (y : Papers.PolytopeVertexCone.actualNeighbors P x) : P.vertices :=
  ⟨y.val,(neighbor_step P x y).1⟩

def asNeighbor (P : ConvexPolytope d) {x : E d} (y : P.vertices)
    (hxy : GeneralVertexStep P x y.val) : Papers.PolytopeVertexCone.actualNeighbors P x :=
  ⟨y.val,Finset.mem_filter.mpr ⟨y.property,hxy⟩⟩

theorem neighborVertex_asNeighbor (P : ConvexPolytope d) {x : E d}
    (y : P.vertices) (hxy : GeneralVertexStep P x y.val) :
    neighborVertex P x (asNeighbor P y hxy) = y := rfl

def neighborStarFace (P : ConvexPolytope d) {x : E d}
    (hx : x ∈ P.vertices) (y : Papers.PolytopeVertexCone.actualNeighbors P x) :
    PositiveVertexStarFace P P.toSet x where
  carrier := segment ℝ x y.val
  isFace := segment_isFace_of_generalVertexStep P hx (neighbor_step P x y)
  subset_base := face_subset_toSet P
    (segment_isFace_of_generalVertexStep P hx (neighbor_step P x y))
  mem_vertex := left_mem_segment ℝ _ _
  dim_pos := by
    rw [segment_faceDim_of_generalVertexStep P hx (neighbor_step P x y)]

variable {P : ConvexPolytope d} {x : E d}

theorem neighbor_image_exists (D : VertexFigureGaloisData P P.toSet x)
    (hx : x ∈ P.vertices) (y : Papers.PolytopeVertexCone.actualNeighbors P x) :
    ∃ q ∈ D.figure.vertices, (D.faceEquiv (neighborStarFace P hx y)).carrier = {q} := by
  apply actual_zeroFace_is_vertex D.figure _ (D.faceEquiv (neighborStarFace P hx y)).isFace
  have h := D.map_dim (neighborStarFace P hx y)
  change faceDim (D.faceEquiv (neighborStarFace P hx y)).carrier + 1 =
    faceDim (segment ℝ x y.val) at h
  rw [segment_faceDim_of_generalVertexStep P hx (neighbor_step P x y)] at h
  omega

def neighborImage (D : VertexFigureGaloisData P P.toSet x)
    (hx : x ∈ P.vertices) (y : Papers.PolytopeVertexCone.actualNeighbors P x) : D.figure.vertices :=
  ⟨Classical.choose (neighbor_image_exists D hx y),
    (Classical.choose_spec (neighbor_image_exists D hx y)).1⟩

theorem neighborImage_face (D : VertexFigureGaloisData P P.toSet x)
    (hx : x ∈ P.vertices) (y : Papers.PolytopeVertexCone.actualNeighbors P x) :
    (D.faceEquiv (neighborStarFace P hx y)).carrier = {(neighborImage D hx y).val} :=
  (Classical.choose_spec (neighbor_image_exists D hx y)).2

theorem neighborImage_injective (D : VertexFigureGaloisData P P.toSet x)
    (hx : x ∈ P.vertices) : Function.Injective (neighborImage D hx) := by
  intro y z hyz
  have himages : D.faceEquiv (neighborStarFace P hx y) =
      D.faceEquiv (neighborStarFace P hx z) := by
    apply PolytopeFace.ext
    rw [neighborImage_face,neighborImage_face,hyz]
  have hstars := D.faceEquiv.injective himages
  have hsegments : segment ℝ x y.val = segment ℝ x z.val :=
    congrArg PositiveVertexStarFace.carrier hstars
  have hzseg : z.val ∈ segment ℝ x y.val := by
    rw [hsegments]
    exact right_mem_segment ℝ _ _
  have hends := ExposedEdgeCenters.extreme_point_on_segment P.toSet
    (vertex_mem_body_extremePoints P (neighbor_step P x z).1)
    (vertex_mem_body_of_mem_vertices P hx)
    (vertex_mem_body_of_mem_vertices P (neighbor_step P x y).1) hzseg
  rcases hends with hzx | hzy
  · exact ((neighbor_step P x z).2.1 hzx.symm).elim
  · exact Subtype.ext hzy.symm

theorem neighborImage_surjective (D : VertexFigureGaloisData P P.toSet x)
    (hx : x ∈ P.vertices) : Function.Surjective (neighborImage D hx) := by
  intro q
  let S : PositiveVertexStarFace P P.toSet x :=
    D.faceEquiv.symm
      { carrier := {q.val}
        isFace := vertex_isFace D.figure q.property }
  have himage : (D.faceEquiv S).carrier = {q.val} := by
    simp only [S,D.faceEquiv.apply_symm_apply]
  have hdim : faceDim S.carrier = 1 := by
    have h := D.map_dim S
    rw [himage,faceDim_singleton] at h
    omega
  obtain ⟨y,hy,hyS,hyx,hseg⟩ := spigolo_segmento P S.isFace hdim hx S.mem_vertex
  have hxy : GeneralVertexStep P x y :=
    ⟨hy,hyx.symm,S.carrier,S.isFace,hdim,S.mem_vertex,hyS⟩
  let y' : Papers.PolytopeVertexCone.actualNeighbors P x :=
    ⟨y,Finset.mem_filter.mpr ⟨hy,hxy⟩⟩
  refine ⟨y',?_⟩
  have hstar : neighborStarFace P hx y' = S := by
    apply PositiveVertexStarFace.ext
    exact hseg.symm
  have hsingle : {(neighborImage D hx y').val} = ({q.val} : Set (E d)) := by
    calc
      {(neighborImage D hx y').val} =
          (D.faceEquiv (neighborStarFace P hx y')).carrier :=
        (neighborImage_face D hx y').symm
      _ = (D.faceEquiv S).carrier := by rw [hstar]
      _ = {q.val} := himage
  exact Subtype.ext (Set.singleton_injective hsingle)

def neighborEquiv (D : VertexFigureGaloisData P P.toSet x)
    (hx : x ∈ P.vertices) : Papers.PolytopeVertexCone.actualNeighbors P x ≃ D.figure.vertices :=
  Equiv.ofBijective (neighborImage D hx)
    ⟨neighborImage_injective D hx,neighborImage_surjective D hx⟩

theorem figure_edge_iff_twoFace (D : VertexFigureGaloisData P P.toSet x)
    (hx : x ∈ P.vertices) (y z : Papers.PolytopeVertexCone.actualNeighbors P x) (hyz : y ≠ z) :
    GeneralVertexStep D.figure (neighborImage D hx y).val (neighborImage D hx z).val ↔
      ∃ F : Set (E d), P.IsFace F ∧ faceDim F = 2 ∧
        x ∈ F ∧ y.val ∈ F ∧ z.val ∈ F := by
  constructor
  · intro hstep
    obtain ⟨A,hA,hAdim,hyA,hzA⟩ := hstep.2.2
    let S : PositiveVertexStarFace P P.toSet x :=
      D.faceEquiv.symm { carrier := A, isFace := hA }
    have himage : (D.faceEquiv S).carrier = A := by
      simp only [S,D.faceEquiv.apply_symm_apply]
    have hdim : faceDim S.carrier = 2 := by
      have h := D.map_dim S
      rw [himage,hAdim] at h
      omega
    have hyS : (neighborStarFace P hx y).carrier ⊆ S.carrier := by
      apply (D.map_subset_iff _ _).mpr
      rw [neighborImage_face,himage]
      exact Set.singleton_subset_iff.mpr hyA
    have hzS : (neighborStarFace P hx z).carrier ⊆ S.carrier := by
      apply (D.map_subset_iff _ _).mpr
      rw [neighborImage_face,himage]
      exact Set.singleton_subset_iff.mpr hzA
    exact ⟨S.carrier,S.isFace,hdim,S.mem_vertex,
      hyS (right_mem_segment ℝ _ _),hzS (right_mem_segment ℝ _ _)⟩
  · rintro ⟨F,hF,hdim,hxF,hyF,hzF⟩
    let S : PositiveVertexStarFace P P.toSet x :=
      { carrier := F
        isFace := hF
        subset_base := face_subset_toSet P hF
        mem_vertex := hxF
        dim_pos := by omega }
    have hFconv : Convex ℝ F := hF.1.convex (convex_convexHull ℝ _)
    have hyS : (neighborStarFace P hx y).carrier ⊆ S.carrier :=
      hFconv.segment_subset hxF hyF
    have hzS : (neighborStarFace P hx z).carrier ⊆ S.carrier :=
      hFconv.segment_subset hxF hzF
    have hiy : (neighborImage D hx y).val ∈ (D.faceEquiv S).carrier := by
      apply (D.map_subset_iff _ _).mp hyS
      rw [neighborImage_face]
      exact Set.mem_singleton _
    have hiz : (neighborImage D hx z).val ∈ (D.faceEquiv S).carrier := by
      apply (D.map_subset_iff _ _).mp hzS
      rw [neighborImage_face]
      exact Set.mem_singleton _
    have hidim : faceDim (D.faceEquiv S).carrier = 1 := by
      have h := D.map_dim S
      change faceDim (D.faceEquiv S).carrier + 1 = faceDim F at h
      rw [hdim] at h
      omega
    refine ⟨(neighborImage D hx z).property,?_,(D.faceEquiv S).carrier,
      (D.faceEquiv S).isFace,hidim,hiy,hiz⟩
    intro h
    exact hyz (neighborImage_injective D hx (Subtype.ext h))

end Papers.Polytopes.ActualVertexFigure

