import cubical.polytope.face_incidence
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Geometric simplices and simplicial convex polytopes

Simpliciality means affine independence of the actual extreme vertices of
every facet. Its equivalent vertex-count characterization is derived from
the affine dimension, rather than included as an unrelated hypothesis.
-/

open Set
open Classical

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

theorem dim_eq_vertices_span (P : ConvexPolytope n) :
    P.dim = Module.finrank ℝ (vectorSpan ℝ (P.vertices : Set (E n))) := by
  unfold ConvexPolytope.dim ConvexPolytope.toSet
  rw [← direction_affineSpan, affineSpan_convexHull, direction_affineSpan]

theorem facePolytope_dim (P : ConvexPolytope n) {F : Set (E n)} (hF : P.IsFace F) :
    (facePolytope P hF).dim = faceDim F := by
  change faceDim (facePolytope P hF).toSet = faceDim F
  rw [facePolytope_toSet]

theorem vertices_affineIndependent_iff (P : ConvexPolytope n) :
    AffineIndependent ℝ (fun v : VertexType P => v.val) ↔
      P.vertices.card = P.dim + 1 := by
  have hrange : Set.range (fun v : VertexType P => v.val) = (P.vertices : Set (E n)) :=
    Subtype.range_coe
  have hdim : Module.finrank ℝ (vectorSpan ℝ
      (Set.range (fun v : VertexType P => v.val))) = P.dim := by
    rw [hrange, ← dim_eq_vertices_span]
  constructor
  · intro hi
    letI : Nonempty (VertexType P) := by
      obtain ⟨v, hv⟩ := P.vertices_nonempty
      exact ⟨⟨v, hv⟩⟩
    have h := hi.finrank_vectorSpan_add_one
    rw [hdim] at h
    simpa [VertexType] using h.symm
  · intro hc
    have hc' : Fintype.card (VertexType P) = P.dim + 1 := by
      simpa [VertexType] using hc
    exact (affineIndependent_iff_finrank_vectorSpan_eq ℝ _ hc').mpr hdim

/-- Every facet is the convex hull of an affinely independent vertex family. -/
def IsSimplicial (P : ConvexPolytope n) : Prop :=
  ∀ (F : Set (E n)) (hF : P.IsFace F), faceDim F + 1 = P.dim →
    AffineIndependent ℝ (fun v : VertexType (facePolytope P hF) => v.val)

theorem isSimplicial_iff_facet_vertices_card (P : ConvexPolytope n) :
    IsSimplicial P ↔ ∀ (F : Set (E n)) (hF : P.IsFace F),
      faceDim F + 1 = P.dim → (facePolytope P hF).vertices.card = P.dim := by
  constructor
  · intro hs F hF hdF
    have hcard := (vertices_affineIndependent_iff (facePolytope P hF)).mp (hs F hF hdF)
    rwa [facePolytope_dim P hF, hdF] at hcard
  · intro hs F hF hdF
    apply (vertices_affineIndependent_iff (facePolytope P hF)).mpr
    rw [facePolytope_dim, hdF]
    exact hs F hF hdF

end LeanEval.Geometry.PlatonicClassification
