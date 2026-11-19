module

public import ActualFacetCatalogueTransport
public import MatroidChecked.FacetBoundaryCompatibility
public import Papers.FiniteProjectionBoundary

@[expose] public section

/-!
# Exact boundary-search output supplies the projection realization interface

A successful finite classification identifies the selected family of
complete facet cells. The theorem below turns that equality into
`RealizesBoundary`, including both directions of the facet and polygon
correspondences. Projection certificates therefore receive actual
geometric face families, not just an abstract candidate boundary.
-/

noncomputable section
namespace Papers.RationalityTen.ActualFacetCatalogueTransport

open Finset Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting
open Papers.PolytopeIncidenceConfiguration
open MatroidChecked.FacetBoundaryEncoding
open ChirotopeDensity ChirotopeDensity.FiniteProjection

variable {n c : ℕ}

/-- Boundary masks extracted from a complete literal cell family. -/
def encodedBoundary (cells : Fin c → Cell (n + 1)) (S : Finset (Fin c)) : Boundary n where
  facets := S.image (fun i => (cells i).vertices)
  polygons := S.biUnion (fun i => (cells i).ridges)

def facetOfThreeFace (P : ConvexPolytope 4) (hP : P.dim = 4) (F : Face P 3) :
    FacetType P :=
  ⟨⟨F.val.carrier, F.val.isFace⟩, F.val.isFace, by rw [F.property, hP]⟩

def threeFaceOfFacet (P : ConvexPolytope 4) (hP : P.dim = 4) (F : FacetType P) :
    Face P 3 :=
  ⟨⟨F.val.val, F.val.property⟩, by
    have h := F.property.2
    change faceDim F.val.val + 1 = P.dim at h
    rw [hP] at h
    change faceDim F.val.val = 3
    omega⟩

theorem facet_labels_agree (P : ConvexPolytope 4) (hP : P.dim = 4)
    (lab : P.vertices ≃ Fin (n + 1)) (F : Face P 3) :
    ChirotopeDensity.FiniteProjection.faceLabels P lab.symm (facetOfThreeFace P hP F).val =
      MatroidChecked.FacetBoundaryEncoding.faceLabels P lab F := by
  ext i
  rw [ChirotopeDensity.FiniteProjection.mem_faceLabels,
    MatroidChecked.FacetBoundaryEncoding.mem_faceLabels_iff]
  rfl

theorem polygon_labels_agree (P : ConvexPolytope 4)
    (lab : P.vertices ≃ Fin (n + 1)) (R : Face P 2) :
    actualFaceLabels P lab.symm R.val =
      MatroidChecked.FacetBoundaryEncoding.faceLabels P lab R := by
  ext i
  rw [mem_actualFaceLabels,
    MatroidChecked.FacetBoundaryEncoding.mem_faceLabels_iff]

/-- The complete actual encoding gives the exact geometric boundary in
both directions, for all facets and all polygonal two-faces. -/
theorem encoding_realizes_boundary (P : ConvexPolytope 4) (hP : P.dim = 4)
    (lab : P.vertices ≃ Fin (n + 1)) (cells : Fin c → Cell (n + 1))
    (E : MatroidChecked.FacetBoundaryEncoding.Encoding P lab cells) :
    RealizesBoundary P lab.symm (encodedBoundary cells E.family) := by
  constructor
  · intro S
    constructor
    · intro hS
      obtain ⟨i, hi, hiS⟩ := Finset.mem_image.mp hS
      obtain ⟨F, hFi⟩ := (E.mem_family i).mp hi
      refine ⟨facetOfThreeFace P hP F, ?_⟩
      rw [facet_labels_agree]
      rw [← hFi, E.index_spec] at hiS
      exact hiS
    · rintro ⟨F, hFS⟩
      let G := threeFaceOfFacet P hP F
      apply Finset.mem_image.mpr
      refine ⟨E.index G, (E.mem_family _).mpr ⟨G, rfl⟩, ?_⟩
      rw [E.index_spec]
      change MatroidChecked.FacetBoundaryEncoding.faceLabels P lab G = S
      rw [← facet_labels_agree P hP lab G]
      exact hFS
  · intro S
    change S ∈ E.family.biUnion (fun i => (cells i).ridges) ↔ _
    rw [E.ridges_eq_actual hP]
    constructor
    · intro hS
      obtain ⟨R, _, hRS⟩ := Finset.mem_image.mp hS
      exact ⟨R, (polygon_labels_agree P lab R).trans hRS⟩
    · rintro ⟨R, hRS⟩
      exact Finset.mem_image.mpr ⟨R, Finset.mem_univ _,
        (polygon_labels_agree P lab R).symm.trans hRS⟩

/-- A literal terminal family certified by a finite search supplies the
projection certificate's complete actual-boundary premise. -/
theorem realizes_literal_boundary_of_family_eq (P : ConvexPolytope 4) (hP : P.dim = 4)
    (lab : P.vertices ≃ Fin (n + 1)) (cells : Fin c → Cell (n + 1))
    (E : MatroidChecked.FacetBoundaryEncoding.Encoding P lab cells)
    (S : Finset (Fin c)) (hS : E.family = S) :
    RealizesBoundary P lab.symm (encodedBoundary cells S) := by
  rw [← hS]
  exact encoding_realizes_boundary P hP lab cells E

end Papers.RationalityTen.ActualFacetCatalogueTransport
