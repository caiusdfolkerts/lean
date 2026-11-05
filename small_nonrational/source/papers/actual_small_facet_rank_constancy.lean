module
public import Papers.SmallFacetRelationRankConstancy
public import Papers.SupportSpanRank
public import Consolidated.LargeFacetRelations

@[expose] public section
noncomputable section

open Matrix Module Set
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeRelationBudget Papers.PolytopeFacetSurplus
open Papers.PolytopeDiagonalShapes Papers.PolytopeFaceRestriction
open Papers.PolytopeNonedgeAllocation Papers.PolytopeSmallFacetBounds

namespace Papers.RationalityTen.ChirotopeDensity

/-- Every actual face has an exact strict homogeneous supporting form. -/
theorem actualFaceLabels_has_strictSupport {d n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices) (F : PolytopeFace P) :
    ∃ a, StrictSupport (vertexCoordinates P e) (actualFaceLabels P e F) a := by
  obtain ⟨f, hf⟩ := exists_supportsFace P F.isFace
  refine ⟨Papers.PolytopeIncidenceConfiguration.coefficientVector f, ?_⟩
  constructor
  · intro i hi
    rw [vertexCoordinates, Papers.PolytopeIncidenceConfiguration.coefficient_dot_homogeneous]
    exact hf.eq_zero ((mem_actualFaceLabels P e F i).mp hi)
  · intro i hi
    rw [vertexCoordinates, Papers.PolytopeIncidenceConfiguration.coefficient_dot_homogeneous]
    have hm : (e i).val ∈ P.toSet := subset_convexHull ℝ _ (e i).property
    have hn := hf.1 (e i).val hm
    have hz : f (e i).val ≠ 0 := by
      intro hz
      exact hi ((mem_actualFaceLabels P e F i).mpr ((hf.mem_iff _).mpr ⟨hm, hz⟩))
    exact lt_of_le_of_ne hn (Ne.symm hz)

/-- Two distinct polygon faces of one three-dimensional facet span that
facet's entire four-dimensional homogeneous space. -/
theorem actual_two_polygon_union_rank {d n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices) (F : Face P 3)
    (R S : FaceBelow P F.val.carrier 2) (hRS : R ≠ S) :
    subsetRank (vertexCoordinates P e)
      (actualFaceLabels P e R.val.val ∪ actualFaceLabels P e S.val.val) = 4 := by
  have hnot : ¬ actualFaceLabels P e S.val.val ⊆ actualFaceLabels P e R.val.val := by
    intro h
    have hsub := (actualFaceLabels_subset_iff P e S.val.val R.val.val).mp h
    have heq := face_eq_of_subset_equal_dimension P S.val.val.isFace R.val.val.isFace
      hsub (S.val.property.trans R.val.property.symm)
    apply hRS
    apply Subtype.ext
    apply Subtype.ext
    exact PolytopeFace.ext heq.symm
  obtain ⟨a, ha⟩ := actualFaceLabels_has_strictSupport P e R.val.val
  have hlo := strictSupport_union_rank_gt (vertexCoordinates P e)
    (actualFaceLabels P e R.val.val) (actualFaceLabels P e S.val.val) a ha hnot
  have hsub : actualFaceLabels P e R.val.val ∪ actualFaceLabels P e S.val.val ⊆
      actualFaceLabels P e F.val :=
    Finset.union_subset (actualFaceLabels_mono P e R.property)
      (actualFaceLabels_mono P e S.property)
  have hhi := subsetRank_mono_labels (vertexCoordinates P e) hsub
  rw [actualFaceLabels_rank, R.val.property] at hlo
  rw [actualFaceLabels_rank, F.property] at hhi
  omega

/-- All span hypotheses in the abstract constancy theorem are actual face
geometry; none is an input certificate. -/
theorem actual_facet_polygon_spans {d n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices) (F : Face P 3) :
    FacetPolygonSpans (vertexCoordinates P e) (actualFaceLabels P e F.val)
      (polygonLabelsBelow P e F) := by
  constructor
  · rw [actualFaceLabels_rank, F.property]
  · intro S hS
    obtain ⟨R, _, rfl⟩ := Finset.mem_image.mp hS
    exact actualFaceLabels_mono P e R.property
  · exact polygonLabelsBelow_rank P e F
  · intro S hS T hT hST
    obtain ⟨R, _, rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨Q, _, rfl⟩ := Finset.mem_image.mp hT
    exact actual_two_polygon_union_rank P e F R Q (fun h =>
      hST (congrArg (fun R : FaceBelow P F.val.carrier 2 => actualFaceLabels P e R.val.val) h))

/-- The finite labelled polygon excess is the actual geometric excess. -/
theorem polygonLabelsBelow_excess {d n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices) (F : Face P 3) :
    ((∑ S ∈ polygonLabelsBelow P e F, (S.card - 3) : ℕ) : ℤ) =
      facetPolygonExcess P F := by
  rw [polygonLabelsBelow, Finset.sum_image]
  · rw [Nat.cast_sum, facetPolygonExcess_eq_sum_faceBelow]
    apply Finset.sum_congr rfl
    intro R hR
    have hlo := face_vertices_card_ge_dim_add_one P 2 R.val
    rw [actualFaceLabels_card, Nat.cast_sub (by omega : 3 ≤ Nat.card (VerticesOn P R.val.val.carrier))]
    norm_num
  · intro R _ S _ h
    exact polygonLabelsBelow_injective P e F h

/-- The local polygon-relation rank is preserved between any two actual
realizations of a labelled facet with at most seven vertices. -/
theorem actual_small_facet_polygon_rank_eq {n : ℕ}
    (P Q : ConvexPolytope 4) (hP : P.IsFullDim) (hQ : Q.IsFullDim)
    (eP : Fin n ≃ P.vertices) (eQ : Fin n ≃ Q.vertices)
    (F : Face P 3) (G : Face Q 3) (hF : facetVertexCount P F ≤ 7)
    (hlabels : actualFaceLabels P eP F.val = actualFaceLabels Q eQ G.val)
    (hpolygons : polygonLabelsBelow P eP F = polygonLabelsBelow Q eQ G) :
    actualPolygonRelationRank P eP F = actualPolygonRelationRank Q eQ G := by
  have hPcard : 3 ≤ P.vertices.card := by
    have h := vertices_card_ge_dim_add_one P
    rw [hP] at h
    omega
  have hQcard : 3 ≤ Q.vertices.card := by
    have h := vertices_card_ge_dim_add_one Q
    rw [hQ] at h
    omega
  have hFcard : (actualFaceLabels P eP F.val).card ≤ 7 := by
    rw [actualFaceLabels_card]
    exact hF
  have hq : FacetPolygonSpans (vertexCoordinates Q eQ)
      (actualFaceLabels P eP F.val) (polygonLabelsBelow P eP F) := by
    rw [hlabels, hpolygons]
    exact actual_facet_polygon_spans Q eQ G
  have hsize : ∀ S ∈ polygonLabelsBelow P eP F, 3 ≤ S.card := by
    intro S hS
    obtain ⟨R, _, rfl⟩ := Finset.mem_image.mp hS
    rw [actualFaceLabels_card]
    exact face_vertices_card_ge_dim_add_one P 2 R.val
  have hinter : ∀ S ∈ polygonLabelsBelow P eP F, ∀ T ∈ polygonLabelsBelow P eP F,
      S ≠ T → (S ∩ T).card ≤ 2 := by
    intro S hS T hT hST
    obtain ⟨R, _, rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨W, _, rfl⟩ := Finset.mem_image.mp hT
    apply actual_two_face_labels_inter_card_le_two P eP R.val W.val
    intro h
    exact hST (congrArg (fun H : Face P 2 => actualFaceLabels P eP H.val) h)
  have hbudget : ∑ S ∈ polygonLabelsBelow P eP F, (S.card - 3) ≤ 4 := by
    have hg := twice_facet_polygon_excess_le_three_vertices_sub_twelve P F
    have hs := polygonLabelsBelow_excess P eP F
    omega
  have h := small_facet_all_polygon_rank_constancy (vertexCoordinates P eP)
    (vertexCoordinates Q eQ) (vertexCoordinates_small_independent P eP hPcard)
    (vertexCoordinates_small_independent Q eQ hQcard)
    (actualFaceLabels P eP F.val) (polygonLabelsBelow P eP F) hFcard
    (actual_facet_polygon_spans P eP F) hq hsize hinter hbudget
  unfold actualPolygonRelationRank
  rw [← hpolygons]
  exact h

/-- The same constancy statement needs no vertex bound when the facet has
at most three nonsimplicial polygons. -/
theorem actual_few_polygon_rank_eq {n : ℕ}
    (P Q : ConvexPolytope 4) (hP : P.IsFullDim) (hQ : Q.IsFullDim)
    (eP : Fin n ≃ P.vertices) (eQ : Fin n ≃ Q.vertices)
    (F : Face P 3) (G : Face Q 3)
    (hlabels : actualFaceLabels P eP F.val = actualFaceLabels Q eQ G.val)
    (hpolygons : polygonLabelsBelow P eP F = polygonLabelsBelow Q eQ G)
    (hfew : ((polygonLabelsBelow P eP F).filter fun S => 4 ≤ S.card).card ≤ 3) :
    actualPolygonRelationRank P eP F = actualPolygonRelationRank Q eQ G := by
  have hPcard : 3 ≤ P.vertices.card := by
    have h := vertices_card_ge_dim_add_one P
    rw [hP] at h
    omega
  have hQcard : 3 ≤ Q.vertices.card := by
    have h := vertices_card_ge_dim_add_one Q
    rw [hQ] at h
    omega
  have hq : FacetPolygonSpans (vertexCoordinates Q eQ)
      (actualFaceLabels P eP F.val) (polygonLabelsBelow P eP F) := by
    rw [hlabels, hpolygons]
    exact actual_facet_polygon_spans Q eQ G
  have hsize : ∀ S ∈ polygonLabelsBelow P eP F, 3 ≤ S.card := by
    intro S hS
    obtain ⟨R, _, rfl⟩ := Finset.mem_image.mp hS
    rw [actualFaceLabels_card]
    exact face_vertices_card_ge_dim_add_one P 2 R.val
  have hinter : ∀ S ∈ polygonLabelsBelow P eP F, ∀ T ∈ polygonLabelsBelow P eP F,
      S ≠ T → (S ∩ T).card ≤ 2 := by
    intro S hS T hT hST
    obtain ⟨R, _, rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨W, _, rfl⟩ := Finset.mem_image.mp hT
    apply actual_two_face_labels_inter_card_le_two P eP R.val W.val
    intro h
    exact hST (congrArg (fun H : Face P 2 => actualFaceLabels P eP H.val) h)
  have h := few_nonsimplicial_polygon_rank_constancy (vertexCoordinates P eP)
    (vertexCoordinates Q eQ) (vertexCoordinates_small_independent P eP hPcard)
    (vertexCoordinates_small_independent Q eQ hQcard)
    (actualFaceLabels P eP F.val) (polygonLabelsBelow P eP F)
    (actual_facet_polygon_spans P eP F) hq hsize hinter hfew
  unfold actualPolygonRelationRank
  rw [← hpolygons]
  exact h

/-- A change of the local polygon-relation rank requires at least eight
vertices and at least four nonsimplicial polygon faces in that facet. -/
theorem actual_rank_change_facet_size_and_polygon_count {n : ℕ}
    (P Q : ConvexPolytope 4) (hP : P.IsFullDim) (hQ : Q.IsFullDim)
    (eP : Fin n ≃ P.vertices) (eQ : Fin n ≃ Q.vertices)
    (F : Face P 3) (G : Face Q 3)
    (hlabels : actualFaceLabels P eP F.val = actualFaceLabels Q eQ G.val)
    (hpolygons : polygonLabelsBelow P eP F = polygonLabelsBelow Q eQ G)
    (hne : actualPolygonRelationRank P eP F ≠ actualPolygonRelationRank Q eQ G) :
    8 ≤ facetVertexCount P F ∧
      4 ≤ ((polygonLabelsBelow P eP F).filter fun S => 4 ≤ S.card).card := by
  constructor
  · by_contra h
    exact hne (actual_small_facet_polygon_rank_eq P Q hP hQ eP eQ F G
      (by omega) hlabels hpolygons)
  · by_contra h
    exact hne (actual_few_polygon_rank_eq P Q hP hQ eP eQ F G hlabels hpolygons
      (by omega))

#print axioms actual_small_facet_polygon_rank_eq

end Papers.RationalityTen.ChirotopeDensity
