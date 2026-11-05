import cubical.polytope.faces
import cubical.polytope.due_vertici
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# The actual edge graph of a finite convex polytope

Vertices are precisely the extreme points listed by the geometric polytope.
Two distinct vertices are adjacent when they lie on a common exposed face
of affine dimension one.
-/

open Set

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- The nonempty geometric face poset, ordered by inclusion. -/
abbrev FaceType (P : ConvexPolytope n) := {F : Set (E n) // P.IsFace F}

noncomputable instance faceTypeFintype (P : ConvexPolytope n) :
    Fintype (FaceType P) := (finite_isFace P).fintype

/-- Vertices of a geometric convex polytope. -/
abbrev VertexType (P : ConvexPolytope n) := {v : E n // v ∈ P.vertices}

/-- The ordinary graph of vertices and edges of a convex polytope. -/
def polytopeGraph (P : ConvexPolytope n) : SimpleGraph (VertexType P) where
  Adj u v := u ≠ v ∧ ∃ F : Set (E n),
    P.IsFace F ∧ faceDim F = 1 ∧ u.val ∈ F ∧ v.val ∈ F
  symm := by
    constructor
    rintro u v ⟨hne, F, hF, hdF, hu, hv⟩
    exact ⟨hne.symm, F, hF, hdF, hv, hu⟩
  loopless := by
    constructor
    intro u h
    exact h.1 rfl

/-- Counting zero-dimensional faces agrees with counting extreme vertices. -/
theorem faceNumber_zero (P : ConvexPolytope n) :
    faceNumber P 0 = P.vertices.card := by
  classical
  have hfaces : (faceSet P).filter (fun F => faceDim F = 0) =
      P.vertices.image (fun v : E n => ({v} : Set (E n))) := by
    ext F
    simp only [Finset.mem_filter, mem_faceSet, Finset.mem_image]
    constructor
    · rintro ⟨hF, hd⟩
      obtain ⟨v, rfl, hv⟩ := punto_di_faccia0_e_vertice P hF hd
      exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨vertex_isFace P hv, faceDim_singleton v⟩
  unfold faceNumber
  rw [hfaces]
  exact Finset.card_image_of_injective _ (fun _ _ h => Set.singleton_injective h)

/-- An exposed edge is the segment joining any two distinct vertices on it. -/
theorem edge_eq_segment (P : ConvexPolytope n)
    {F : Set (E n)} (hF : P.IsFace F) (hdF : faceDim F = 1)
    {u v : E n} (hu : u ∈ P.vertices) (hv : v ∈ P.vertices)
    (huF : u ∈ F) (hvF : v ∈ F) (hne : u ≠ v) :
    F = segment ℝ u v := by
  obtain ⟨w, hw, hwF, hwu, hseg⟩ := spigolo_segmento P hF hdF hu huF
  have hvend : v = u ∨ v = w :=
    vertice_in_segmento_estremo_generico P hF hseg hv hvF
  rcases hvend with hvu | hvw
  · exact (hne hvu.symm).elim
  · simpa only [← hvw] using hseg

/-- The geometric edge containing two distinct vertices is unique. -/
theorem edge_unique (P : ConvexPolytope n)
    {F G : Set (E n)} (hF : P.IsFace F) (hG : P.IsFace G)
    (hdF : faceDim F = 1) (hdG : faceDim G = 1)
    {u v : E n} (hu : u ∈ P.vertices) (hv : v ∈ P.vertices)
    (huF : u ∈ F) (hvF : v ∈ F) (huG : u ∈ G) (hvG : v ∈ G)
    (hne : u ≠ v) : F = G := by
  rw [edge_eq_segment P hF hdF hu hv huF hvF hne,
    edge_eq_segment P hG hdG hu hv huG hvG hne]

end LeanEval.Geometry.PlatonicClassification
