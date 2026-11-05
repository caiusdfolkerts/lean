import cubical_indecomposability.realization
import cubical_indecomposability.face_data_checks
import cubical_indecomposability.labelled_faces
import cubical_indecomposability.indexed_face_catalogue

/-!
# The complete geometric face lattice of the explicit polytope

Each finite mask is realized by intersecting supporting hyperplanes.  Exact
vertex membership identifies its convex hull.  Five-element incidence flags
prove all dimensions.  Finally the rank-two pairing certificate proves
that every ordinary exposed face is in the catalogue.
-/

noncomputable section

namespace CubicalIndecomposability

open Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes

private theorem support_bound_on_vertices (f : Fin 130) (x : E 4)
    (hx : x ∈ polytope.vertices) : offset f ≤ form f x := by
  rw [polytope_vertices] at hx
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
  exact support_nonneg f v

/-- The exposed face associated with a mask in the finite catalogue. -/
def indexedFace (i : Fin 1069) : Set (E 4) :=
  supportIntersection polytope form offset (supportRows i)

theorem indexedFace_isFace (i : Fin 1069) : polytope.IsFace (indexedFace i) := by
  apply supportIntersection_isFace polytope form offset (supportRows i)
    support_bound_on_vertices
  obtain ⟨v, hv⟩ := faceMask_nonempty i
  refine ⟨p v, vertex_mem v, ?_⟩
  intro f hf
  apply (support_eq_iff f v).mpr
  exact (supportRows_identity i v).mp hv f hf

@[simp] theorem vertex_mem_indexedFace (i : Fin 1069) (v : Fin 144) :
    p v ∈ indexedFace i ↔ v ∈ faceMask i := by
  rw [indexedFace, vertex_mem_supportIntersection polytope form offset
    (supportRows i) support_bound_on_vertices (p v) (vertex_mem v)]
  constructor
  · intro h
    apply (supportRows_identity i v).mpr
    intro f hf
    exact (support_eq_iff f v).mp (h f hf)
  · intro h f hf
    exact (support_eq_iff f v).mpr ((supportRows_identity i v).mp h f hf)

theorem indexedFace_eq_hull (i : Fin 1069) :
    indexedFace i = convexHull ℝ (p '' (faceMask i : Set (Fin 144))) :=
  face_eq_label_hull polytope p polytope_vertices (indexedFace_isFace i)
    (faceMask i) (vertex_mem_indexedFace i)

theorem indexedFace_subset_iff (i j : Fin 1069) :
    indexedFace i ⊆ indexedFace j ↔ faceMask i ⊆ faceMask j :=
  face_subset_iff_labels polytope p polytope_vertices
    (indexedFace_isFace i) (indexedFace_isFace j)
    (faceMask i) (faceMask j) (vertex_mem_indexedFace i) (vertex_mem_indexedFace j)

theorem indexedFace_ssubset_iff (i j : Fin 1069) :
    indexedFace i ⊂ indexedFace j ↔ faceMask i ⊂ faceMask j :=
  face_ssubset_iff_labels polytope p polytope_vertices
    (indexedFace_isFace i) (indexedFace_isFace j)
    (faceMask i) (faceMask j) (vertex_mem_indexedFace i) (vertex_mem_indexedFace j)

theorem indexedFace_injective : Function.Injective indexedFace := by
  intro i j hij
  apply faceMask_injective
  exact (face_eq_iff_labels polytope p polytope_vertices
    (indexedFace_isFace i) (indexedFace_isFace j)
    (faceMask i) (faceMask j) (vertex_mem_indexedFace i) (vertex_mem_indexedFace j)).mp hij

theorem indexedFace_top : indexedFace 1068 = polytope.toSet := by
  rw [indexedFace_eq_hull, faceMask_top]
  change convexHull ℝ (p '' (Finset.univ : Finset (Fin 144))) =
    convexHull ℝ (polytope.vertices : Set (E 4))
  rw [polytope_vertices, Finset.coe_image]

theorem indexedFace_vertex (v : Fin 144) :
    indexedFace (v.castLE (by decide)) = {p v} := by
  rw [indexedFace_eq_hull, faceMask_vertex, Finset.coe_singleton,
    Set.image_singleton, convexHull_singleton]

/-- All 1,069 dimensions follow from strict geometric face flags. -/
theorem indexedFace_dimension (i : Fin 1069) :
    faceDim (indexedFace i) = (faceRank i : ℕ) := by
  have h := dimension_of_five_face_flag polytope
    (fun k => indexedFace (faceFlag i k))
    (fun k => indexedFace_isFace (faceFlag i k))
    ((indexedFace_ssubset_iff _ _).mpr (faceFlag_strict i 0))
    ((indexedFace_ssubset_iff _ _).mpr (faceFlag_strict i 1))
    ((indexedFace_ssubset_iff _ _).mpr (faceFlag_strict i 2))
    ((indexedFace_ssubset_iff _ _).mpr (faceFlag_strict i 3))
  simpa only [faceFlag_self] using h (faceRank i)

theorem polytope_dimension : polytope.dim = 4 := by
  have h := indexedFace_dimension 1068
  rw [indexedFace_top] at h
  exact h

/-- The finite catalogue, now interpreted as actual geometric faces. -/
def geometricFaceCatalogue : IndexedFaceCatalogue polytope (Fin 1069) where
  face i := ⟨indexedFace i, indexedFace_isFace i⟩
  rank i := faceRank i
  dimension := indexedFace_dimension
  injective := by
    intro i j hij
    exact indexedFace_injective (congrArg Subtype.val hij)
  top := ⟨1068, indexedFace_top⟩
  vertices := by
    intro x hx
    rw [polytope_vertices] at hx
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨v.castLE (by decide), indexedFace_vertex v⟩
  facet := by
    intro a ha
    obtain ⟨b, hb⟩ := lowerFacets_nonempty a (by omega)
    obtain ⟨hrank, hsub⟩ := (lowerFacets_iff a b).mp hb
    exact ⟨b, (indexedFace_subset_iff b a).mpr hsub, hrank⟩
  ridgePartner := by
    intro a b r hba hrb hdb hdr
    have hb : b ∈ lowerFacets a := (lowerFacets_iff a b).mpr
      ⟨hdb, (indexedFace_subset_iff b a).mp hba⟩
    have hr : r ∈ lowerFacets b := (lowerFacets_iff b r).mpr
      ⟨by omega, (indexedFace_subset_iff r b).mp hrb⟩
    obtain ⟨c, hc, hcb, hrc⟩ := lowerFacets_pairing a b hb r hr
    obtain ⟨hdc, hca⟩ := (lowerFacets_iff a c).mp hc
    obtain ⟨_hdr', hrc'⟩ := (lowerFacets_iff c r).mp hrc
    exact ⟨c, (indexedFace_subset_iff c a).mpr hca,
      (indexedFace_subset_iff r c).mpr hrc', hdc, hcb⟩

/-- Every nonempty exposed face occurs, with no missing geometric faces. -/
theorem indexedFace_complete {F : Set (E 4)} (hF : polytope.IsFace F) :
    ∃ i, indexedFace i = F := by
  obtain ⟨i, hi⟩ := geometricFaceCatalogue.surjective ⟨F, hF⟩
  exact ⟨i, congrArg Subtype.val hi⟩

theorem faceNumber_eq_rank_card (k : ℕ) :
    faceNumber polytope k =
      Fintype.card {i : Fin 1069 // (faceRank i : ℕ) = k} :=
  geometricFaceCatalogue.faceNumber_eq k

/-- Count every rank, including the whole polytope in rank four. -/
theorem faceNumber_eq_catalogue_count (k : Fin 5) :
    faceNumber polytope k.val = (![144, 404, 390, 130, 1] : Fin 5 → ℕ) k := by
  rw [faceNumber_eq_rank_card, Fintype.card_subtype]
  simpa only [Fin.ext_iff] using faceRank_cardinality k

/-- The paper's complete face vector, counting ordinary geometric faces. -/
theorem face_vector :
    faceNumber polytope 0 = 144 ∧ faceNumber polytope 1 = 404 ∧
    faceNumber polytope 2 = 390 ∧ faceNumber polytope 3 = 130 := by
  exact ⟨faceNumber_eq_catalogue_count 0, faceNumber_eq_catalogue_count 1,
    faceNumber_eq_catalogue_count 2, faceNumber_eq_catalogue_count 3⟩

end CubicalIndecomposability
