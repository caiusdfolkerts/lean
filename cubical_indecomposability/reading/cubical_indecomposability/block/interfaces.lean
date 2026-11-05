import cubical_indecomposability.block.cube_realization

/-!
# The three distinguished facets of the auxiliary block

The normalized block has facets F, H and G from Proposition 5. Their
intersection and separation are proved for actual geometric faces, using
exact vertex membership and the exposed-face hull theorem. The common
face Q is a two-dimensional polytope with exactly four extreme vertices.
-/

noncomputable section

namespace CubicalIndecomposability.Block

open Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

/-- The facet whose deformation restrictions have dimension at most two. -/
def F : Set (E 4) := facet 5
/-- The first determining facet. -/
def H : Set (E 4) := facet 21
/-- The disjoint determining facet, already a geometric parallelepiped. -/
def G : Set (E 4) := facet 1
/-- The common quadrilateral of F and H. -/
def Q : Set (E 4) := indexedFace 180

def FLabels : Finset (Fin 32) := {24, 25, 26, 27, 28, 29, 30, 31}
def HLabels : Finset (Fin 32) := {8, 10, 12, 14, 24, 26, 28, 30}
def GLabels : Finset (Fin 32) := {1, 3, 5, 7, 9, 11, 13, 15}
def QLabels : Finset (Fin 32) := {24, 26, 28, 30}

theorem F_labels : facetLabels 5 = FLabels := by decide
theorem H_labels : facetLabels 21 = HLabels := by decide
theorem G_labels : facetLabels 1 = GLabels := by decide
theorem Q_labels : faceMask 180 = QLabels := by decide

theorem F_isFace : polytope.IsFace F := facet_isFace 5
theorem H_isFace : polytope.IsFace H := facet_isFace 21
theorem G_isFace : polytope.IsFace G := facet_isFace 1
theorem Q_isFace : polytope.IsFace Q := indexedFace_isFace 180

@[simp] theorem vertex_mem_F (v : Fin 32) : p v ∈ F ↔ v ∈ FLabels := by
  rw [F, vertex_mem_facet_iff, incident, F_labels]
@[simp] theorem vertex_mem_H (v : Fin 32) : p v ∈ H ↔ v ∈ HLabels := by
  rw [H, vertex_mem_facet_iff, incident, H_labels]
@[simp] theorem vertex_mem_G (v : Fin 32) : p v ∈ G ↔ v ∈ GLabels := by
  rw [G, vertex_mem_facet_iff, incident, G_labels]
@[simp] theorem vertex_mem_Q (v : Fin 32) : p v ∈ Q ↔ v ∈ QLabels := by
  rw [Q, vertex_mem_indexedFace, Q_labels]

theorem F_dimension : faceDim F = 3 := facet_dimension 5
theorem H_dimension : faceDim H = 3 := facet_dimension 21
theorem G_dimension : faceDim G = 3 := facet_dimension 1
theorem Q_dimension : faceDim Q = 2 := by
  rw [Q, indexedFace_dimension]
  rfl

def F_facet : FacetType polytope :=
  ⟨⟨F, F_isFace⟩, by simp only [F_dimension, polytope_dimension]⟩
def H_facet : FacetType polytope :=
  ⟨⟨H, H_isFace⟩, by simp only [H_dimension, polytope_dimension]⟩
def G_facet : FacetType polytope :=
  ⟨⟨G, G_isFace⟩, by simp only [G_dimension, polytope_dimension]⟩

theorem vertex_mem_F_inter_H (v : Fin 32) :
    p v ∈ F ∩ H ↔ v ∈ QLabels := by
  rw [Set.mem_inter_iff, vertex_mem_F, vertex_mem_H, ← Finset.mem_inter]
  rw [show FLabels ∩ HLabels = QLabels by decide]

/-- The listed common quadrilateral is the actual intersection of the facets. -/
theorem F_inter_H : F ∩ H = Q := by
  have h24 : p 24 ∈ F ∩ H :=
    (vertex_mem_F_inter_H 24).mpr (by decide)
  have hI : polytope.IsFace (F ∩ H) :=
    isFace_inter polytope F_isFace H_isFace ⟨p 24, h24⟩
  exact (face_eq_iff_labels polytope p polytope_vertices hI Q_isFace
    QLabels QLabels vertex_mem_F_inter_H vertex_mem_Q).mpr rfl

/-- Disjoint vertex masks imply disjoint actual faces of this polytope. -/
theorem disjoint_faces_of_disjoint_labels {A B : Set (E 4)}
    (hA : polytope.IsFace A) (hB : polytope.IsFace B)
    (s t : Finset (Fin 32))
    (hs : ∀ v, p v ∈ A ↔ v ∈ s) (ht : ∀ v, p v ∈ B ↔ v ∈ t)
    (hst : Disjoint s t) : Disjoint A B := by
  classical
  apply Set.disjoint_left.mpr
  intro x hxA hxB
  have hI : polytope.IsFace (A ∩ B) :=
    isFace_inter polytope hA hB ⟨x, hxA, hxB⟩
  have hmask : ∀ v, p v ∈ A ∩ B ↔ v ∈ (∅ : Finset (Fin 32)) := by
    intro v
    constructor
    · intro hv
      exact False.elim ((Finset.disjoint_left.mp hst)
        ((hs v).mp hv.1) ((ht v).mp hv.2))
    · intro hv
      exact False.elim (Finset.notMem_empty v hv)
  have hempty := face_eq_label_hull polytope p polytope_vertices hI ∅ hmask
  simp only [Finset.coe_empty, Set.image_empty, convexHull_empty] at hempty
  have hx : x ∈ A ∩ B := ⟨hxA, hxB⟩
  rw [hempty] at hx
  exact hx

theorem G_disjoint_F : Disjoint G F :=
  disjoint_faces_of_disjoint_labels G_isFace F_isFace GLabels FLabels
    vertex_mem_G vertex_mem_F (by decide)

theorem G_disjoint_H : Disjoint G H :=
  disjoint_faces_of_disjoint_labels G_isFace H_isFace GLabels HLabels
    vertex_mem_G vertex_mem_H (by decide)

/-- The third distinguished facet misses both facets at the common ridge. -/
theorem G_disjoint_F_union_H : Disjoint G (F ∪ H) := by
  apply Set.disjoint_left.mpr
  intro x hxG hx
  rcases hx with hxF | hxH
  · exact Set.disjoint_left.mp G_disjoint_F hxG hxF
  · exact Set.disjoint_left.mp G_disjoint_H hxG hxH

/-- The vertices of a face are precisely the labelled vertices that it contains. -/
theorem facePolytope_vertices_labels {A : Set (E 4)} (hA : polytope.IsFace A)
    (s : Finset (Fin 32)) (hs : ∀ v, p v ∈ A ↔ v ∈ s) :
    (facePolytope polytope hA).vertices = s.image p := by
  classical
  change polytope.vertices.filter (· ∈ A) = s.image p
  ext x
  simp only [polytope_vertices, Finset.mem_filter, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨v, rfl⟩, hv⟩
    exact ⟨v, (hs v).mp hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨⟨v, rfl⟩, (hs v).mpr hv⟩

/-- Q is a genuine quadrilateral: a two-dimensional face with four vertices. -/
theorem Q_vertices_card : (facePolytope polytope Q_isFace).vertices.card = 4 := by
  rw [facePolytope_vertices_labels Q_isFace QLabels vertex_mem_Q,
    Finset.card_image_of_injective _ p_injective]
  decide

theorem Q_quadrilateral :
    faceDim Q = 2 ∧ (facePolytope polytope Q_isFace).vertices.card = 4 :=
  ⟨Q_dimension, Q_vertices_card⟩

end CubicalIndecomposability.Block
