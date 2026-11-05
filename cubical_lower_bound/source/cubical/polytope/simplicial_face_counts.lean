import cubical.polytope.simplicial_boundary
import cubical.polytope.simplicial_boundary_links
import cubical.polytope.face_incidence
import cubical.simplicial_lower_bound
import cubical.simplicial_embedding

/-! # Equality of geometric and simplicial face numbers -/

open Set Classical

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope
open Cubical.Simplicial

variable {n : ℕ}

/-- Every finite simplex in the boundary is exactly one geometric face,
and every proper geometric face of a simplicial polytope occurs this way. -/
def simplicialFacesEquiv (P : ConvexPolytope n) (hs : IsSimplicial P)
    (i : ℕ) (hi : i < P.dim) :
    ↥(faces (boundaryFacets P) (i + 1)) ≃ DimFaceType P i where
  toFun a := by
    have h : P.IsFace (vertexHull P a.val) ∧ faceDim (vertexHull P a.val) = i := by
      obtain ⟨hcard, t, ht, hat⟩ := (mem_faces _ _ _).mp a.property
      have hne : a.val.Nonempty := Finset.card_pos.mp (by omega)
      have hF := boundary_subsimplex_isFace P hs ht hat hne
      have hdim := boundary_subsimplex_dimension P hs ht hat hne
      exact ⟨hF, by omega⟩
    exact ⟨⟨vertexHull P a.val, h.1⟩, h.2⟩
  invFun F := by
    refine ⟨faceVertices P F.val.val, ?_⟩
    have hFi : faceDim F.val.val < P.dim := by rw [F.property]; exact hi
    obtain ⟨K, hK, hdK, hFK⟩ := face_contained_in_facet P F.val.property hFi
    let k : FacetType P := ⟨⟨K, hK⟩, hdK⟩
    have hcard := simplicial_ridge_vertices_card P hs F.val.property k hFK
    refine (mem_faces _ _ _).mpr ⟨?_, faceVertices P K, ?_, ?_⟩
    · simpa only [F.property] using hcard
    · exact (mem_boundaryFacets P _).mpr ⟨k, rfl⟩
    · exact faceVertices_mono P hFK
  left_inv a := by
    apply Subtype.ext
    exact faceVertices_vertexHull P a.val
  right_inv F := by
    apply Subtype.ext
    apply Subtype.ext
    exact vertexHull_faceVertices P F.val.property

theorem faces_boundary_card (P : ConvexPolytope n) (hs : IsSimplicial P)
    (i : ℕ) (hi : i < P.dim) :
    (faces (boundaryFacets P) (i + 1)).card = faceNumber P i := by
  have h := Fintype.card_congr (simplicialFacesEquiv P hs i hi)
  simpa only [Fintype.card_coe, card_dimFaceType] using h

theorem vertices_boundaryFacets_eq_univ (P : ConvexPolytope n) (hdim : 1 ≤ P.dim) :
    vertices id (boundaryFacets P) = Finset.univ := by
  ext v
  simp only [Finset.mem_univ, iff_true]
  obtain ⟨F, hvF⟩ := vertex_in_facet P hdim v
  exact (mem_vertices id (boundaryFacets P) v).mpr
    ⟨faceVertices P F.val.val, (mem_boundaryFacets P _).mpr ⟨F, rfl⟩,
      (mem_faceVertices P _ v).mpr hvF⟩

theorem vertices_boundaryFacets_card (P : ConvexPolytope n) (hdim : 1 ≤ P.dim) :
    (vertices id (boundaryFacets P)).card = P.vertices.card := by
  rw [vertices_boundaryFacets_eq_univ P hdim, Finset.card_univ]
  exact Fintype.card_coe _

theorem boundaryFacets_card_eq_faceNumber (P : ConvexPolytope n) (hs : IsSimplicial P)
    (hdim : 1 ≤ P.dim) : (boundaryFacets P).card = faceNumber P (P.dim - 1) := by
  have h := faces_boundary_card P hs (P.dim - 1) (by omega)
  have hd : P.dim - 1 + 1 = P.dim := by omega
  rw [hd, faces_top (boundaryFacets_pure P hs)] at h
  exact h

/-- The simplicial lower bound expressed using the actual exposed faces
of a geometric polytope. The all-links hypothesis is supplied by the
geometric vertex-figure theorem in the final application. -/
theorem simplicial_face_lower_bound_of_links (P : ConvexPolytope n) (hs : IsSimplicial P)
    (hdim : 3 ≤ P.dim) (hlinks : HasCircuitLinks P.dim (boundaryFacets P))
    (i : ℕ) (hi : i ≤ P.dim - 2) :
    P.dim.choose i * P.vertices.card ≤ faceNumber P i + i * (P.dim + 1).choose (i + 1) := by
  have h := simplicial_lower_bound hdim (boundaryFacets_nonempty P (by omega))
    (boundaryFacets_pure P hs) hlinks (r := i + 1) (by omega) (by omega)
  rw [faces_boundary_card P hs i (by omega), vertices_boundaryFacets_card P (by omega)] at h
  simpa using h

theorem simplicial_facet_lower_bound_of_links (P : ConvexPolytope n) (hs : IsSimplicial P)
    (hdim : 3 ≤ P.dim) (hlinks : HasCircuitLinks P.dim (boundaryFacets P)) :
    (P.dim - 1) * P.vertices.card ≤
      faceNumber P (P.dim - 1) + (P.dim - 2) * (P.dim + 1) := by
  have h := simplicial_facet_lower_bound hdim (boundaryFacets_nonempty P (by omega))
    (boundaryFacets_pure P hs) hlinks (boundaryFacets_ridgeDegreeTwo P hs (by omega))
  rw [vertices_boundaryFacets_card P (by omega), boundaryFacets_card_eq_faceNumber P hs (by omega)] at h
  exact h

/-- Barnette's simplicial lower bound for the actual exposed faces of any
simplicial convex polytope. Every rigidity and link hypothesis has been proved. -/
theorem IsSimplicial.face_lower_bound (P : ConvexPolytope n) (hs : IsSimplicial P)
    (hdim : 3 ≤ P.dim) (i : ℕ) (hi : i ≤ P.dim - 2) :
    P.dim.choose i * P.vertices.card ≤
      faceNumber P i + i * (P.dim + 1).choose (i + 1) :=
  simplicial_face_lower_bound_of_links P hs hdim (hs.boundary_hasCircuitLinks P) i hi

/-- The facet case of the full simplicial lower-bound theorem. -/
theorem IsSimplicial.facet_lower_bound (P : ConvexPolytope n) (hs : IsSimplicial P)
    (hdim : 3 ≤ P.dim) :
    (P.dim - 1) * P.vertices.card ≤
      faceNumber P (P.dim - 1) + (P.dim - 2) * (P.dim + 1) :=
  simplicial_facet_lower_bound_of_links P hs hdim (hs.boundary_hasCircuitLinks P)

end LeanEval.Geometry.PlatonicClassification
