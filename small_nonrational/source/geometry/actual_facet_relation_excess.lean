module
public import SevenFacetTemplateProfiles
public import Consolidated.LargeFacetRelations
public import Consolidated.SmallFacetEncoding

@[expose] public section

/-!
# Relation excess of actual six- and seven-vertex facets

All bounds concern the actual polygon relation spaces at the given realization.
No invariance of their rank across the realization space is assumed. An exact
template match identifies the only possible positive local excess: the
six-vertex triangular prism or the seven-vertex capped prism, respectively.
-/

noncomputable section
namespace Papers.RationalityTen.ActualFacetRelationExcess

open Finset Set
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeSmallFacetBounds Papers.PolytopeFacetSurplus
open Papers.PolytopeRelationBudget Papers.PolytopeNonedgeAllocation
open ChirotopeDensity MatroidChecked.FacetBoundaryEncoding
open ActualFacetCatalogueTransport CellFacetInvariants
open SevenFacetTemplateProfiles FiniteCycleCandidates

/-- Rank one already forces small polygons, hence polygon excess one. -/
theorem rank_one_excess_one {d n : Nat} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (hPcard : 3 ≤ P.vertices.card) (F : Face P 3)
    (hone : actualPolygonRelationRank P e F = 1) : facetPolygonExcess P F = 1 := by
  apply six_facet_rank_one_excess_one P e hPcard F _ hone
  intro R
  have h := actual_polygon_card_le_relation_rank_add_three P e F R
  omega

/-- At the two smallest ranks there is no local excess. At all other ranks,
the polygon-excess bound loses at least two. -/
theorem relation_excess_le {d n : Nat} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (hPcard : 3 ≤ P.vertices.card) (F : Face P 3)
    (b : Int) (hb : 0 ≤ b) (hg : facetPolygonExcess P F ≤ b + 2) :
    facetPolygonExcess P F - (actualPolygonRelationRank P e F : Int) ≤ b := by
  by_cases hz : actualPolygonRelationRank P e F = 0
  · have hg0 := (actualPolygonRelationRank_eq_zero_iff P e F).mp hz
    omega
  by_cases ho : actualPolygonRelationRank P e F = 1
  · have hg1 := rank_one_excess_one P e hPcard F ho
    omega
  omega

/-- The only rank-two, polygon-excess-three possibility has no pentagon.
A pentagon would be the unique nontriangle, with five diagonals; the actual
diagonal identity would instead give seven. -/
theorem excess_one_forces_small_polygons {n : Nat}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (F : Face P 3) (hg : facetPolygonExcess P F ≤ 3)
    (he : facetPolygonExcess P F - (actualPolygonRelationRank P e F : Int) = 1) :
    ∀ R : FaceBelow P F.val.carrier 2,
      Nat.card (VerticesOn P R.val.val.carrier) ≤ 4 := by
  have hPcard : 3 ≤ P.vertices.card := by
    have h := vertices_card_ge_dim_add_one P
    rw [hP] at h
    omega
  have hrank : actualPolygonRelationRank P e F = 2 := by
    by_cases hz : actualPolygonRelationRank P e F = 0
    · have hg0 := (actualPolygonRelationRank_eq_zero_iff P e F).mp hz
      omega
    by_cases ho : actualPolygonRelationRank P e F = 1
    · have hg1 := rank_one_excess_one P e hPcard F ho
      omega
    omega
  have hg3 : facetPolygonExcess P F = 3 := by omega
  intro R
  by_contra hlarge
  have hbound := actual_polygon_card_le_relation_rank_add_three P e F R
  have hR : Nat.card (VerticesOn P R.val.val.carrier) = 5 := by omega
  have hother (S : FaceBelow P F.val.carrier 2) (hSR : S ≠ R) :
      Nat.card (VerticesOn P S.val.val.carrier) = 3 := by
    have hlo := face_vertices_card_ge_dim_add_one P 2 S.val
    have hsum := actual_distinct_polygon_relations_rank_add P hP e F R S hSR.symm
    omega
  have hd := facet_diagonal_count_unique_polygon P F R hother
  have hdiag := Papers.PolytopeFaceNonedges.polygon_nonedge_count P R.val
  rw [hR] at hdiag
  norm_num only [Nat.choose] at hdiag
  have hd' := facet_diagonal_count_one_pentagon P F R hR
    (fun S hSR => (hother S hSR).le.trans (by decide))
  omega

theorem seven_polygon_excess_le_three {d : Nat} (P : ConvexPolytope d)
    (F : Face P 3) (hF : facetVertexCount P F = 7)
    (hfaces : 7 ≤ Nat.card (FaceBelow P F.val.carrier 2)) :
    facetPolygonExcess P F ≤ 3 := by
  have h := facet_polygon_excess_face_formula P F
  rw [hF] at h
  omega

theorem seven_relation_excess_le_one {n : Nat}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (F : Face P 3) (hF : facetVertexCount P F = 7)
    (hfaces : 7 ≤ Nat.card (FaceBelow P F.val.carrier 2)) :
    facetPolygonExcess P F - (actualPolygonRelationRank P e F : Int) ≤ 1 := by
  have hPcard : 3 ≤ P.vertices.card := by
    have h := vertices_card_ge_dim_add_one P
    rw [hP] at h
    omega
  exact relation_excess_le P e hPcard F 1 (by decide)
    (seven_polygon_excess_le_three P F hF hfaces)

/-- The equality branch has the exact capped-prism signature, without any
assumption excluding pentagons or hexagons. -/
theorem seven_excess_one_signature {n : Nat}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (F : Face P 3) (hF : facetVertexCount P F = 7)
    (hfaces : 7 ≤ Nat.card (FaceBelow P F.val.carrier 2))
    (he : facetPolygonExcess P F - (actualPolygonRelationRank P e F : Int) = 1) :
    (facetQuadrilateralFaces P F).card = 3 ∧
      (facetQuadrilateralLabels P e F).card = 6 :=
  seven_facet_excess_one_quad_signature P hP e F hF hfaces
    (excess_one_forces_small_polygons P hP e F
      (seven_polygon_excess_le_three P F hF hfaces) he) he

theorem seven_excess_zero_of_large_polygon {n : Nat}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (F : Face P 3) (hF : facetVertexCount P F = 7)
    (hfaces : 7 ≤ Nat.card (FaceBelow P F.val.carrier 2))
    (R : FaceBelow P F.val.carrier 2)
    (hR : 5 ≤ Nat.card (VerticesOn P R.val.val.carrier)) :
    facetPolygonExcess P F - (actualPolygonRelationRank P e F : Int) = 0 := by
  have hlo := actualPolygonRelationRank_le P e F
  have hhi := seven_relation_excess_le_one P hP e F hF hfaces
  by_contra hne
  have he : facetPolygonExcess P F - (actualPolygonRelationRank P e F : Int) = 1 := by
    omega
  have hsmall := excess_one_forces_small_polygons P hP e F
    (seven_polygon_excess_le_three P F hF hfaces) he R
  omega

theorem seven_excess_zero_of_few_quadrilaterals {n : Nat}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (F : Face P 3) (hF : facetVertexCount P F = 7)
    (hfaces : 7 ≤ Nat.card (FaceBelow P F.val.carrier 2))
    (hq : (facetQuadrilateralFaces P F).card ≤ 2) :
    facetPolygonExcess P F - (actualPolygonRelationRank P e F : Int) = 0 := by
  have hlo := actualPolygonRelationRank_le P e F
  have hhi := seven_relation_excess_le_one P hP e F hF hfaces
  by_contra hne
  have he : facetPolygonExcess P F - (actualPolygonRelationRank P e F : Int) = 1 := by
    omega
  have hq3 := (seven_excess_one_signature P hP e F hF hfaces he).1
  omega

theorem faceLabels_eq_actualFaceLabels {d n k : Nat} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (R : Face P k) :
    faceLabels P e.symm R = actualFaceLabels P e R.val := by
  ext i
  simp only [mem_faceLabels_iff, mem_actualFaceLabels, Equiv.symm_symm]

/-- The encoded quadrilateral ridges are precisely the actual quadrilateral
faces, including their full vertex labels. -/
theorem actual_quadrilateral_ridges {d n : Nat} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (F : Face P 3) :
    ((actualCell P e.symm F).ridges.filter fun S => S.card = 4) =
      (facetQuadrilateralFaces P F).image (fun R => actualFaceLabels P e R.val.val) := by
  ext S
  constructor
  · intro hS
    obtain ⟨hmem, hcard⟩ := Finset.mem_filter.mp hS
    obtain ⟨R, hRF, hR⟩ := (actualCell_ridge_iff P e.symm F S).mp hmem
    refine Finset.mem_image.mpr ⟨⟨R, hRF⟩, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [← ActualFaceTransport.labels_card P e.symm R]
      change (faceLabels P e.symm R).card = 4
      rw [hR]
      exact hcard
    · exact (faceLabels_eq_actualFaceLabels P e R).symm.trans hR
  · intro hS
    obtain ⟨R, hR, hRS⟩ := Finset.mem_image.mp hS
    apply Finset.mem_filter.mpr
    refine ⟨(actualCell_ridge_iff P e.symm F S).mpr
      ⟨R.val, R.property, (faceLabels_eq_actualFaceLabels P e R.val).trans hRS⟩, ?_⟩
    rw [← hRS, actualFaceLabels_card]
    exact (Finset.mem_filter.mp hR).2

theorem actual_quadrilateral_count {d n : Nat} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (F : Face P 3) :
    cellRidgeSizeCount (actualCell P e.symm F) 4 = (facetQuadrilateralFaces P F).card := by
  unfold cellRidgeSizeCount
  rw [actual_quadrilateral_ridges]
  apply Finset.card_image_of_injective
  intro R S h
  apply Subtype.ext
  apply Subtype.ext
  exact actualFaceLabels_injective P e h

theorem actual_quadrilateral_vertices {d n : Nat} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (F : Face P 3) :
    quadrilateralVertices (actualCell P e.symm F) = facetQuadrilateralLabels P e F := by
  unfold quadrilateralVertices
  rw [actual_quadrilateral_ridges, Finset.image_biUnion]
  rfl

theorem mapCell_quadrilateral_vertices {m n : Nat}
    (f : Fin m ↪ Fin n) (C : Cell m) :
    quadrilateralVertices (mapCell f C) = (quadrilateralVertices C).image f := by
  unfold quadrilateralVertices
  change (((C.ridges.image fun S => S.image f).filter fun S => S.card = 4).biUnion id) = _
  rw [Finset.filter_image]
  simp only [Finset.card_image_of_injective _ f.injective]
  rw [Finset.image_biUnion, Finset.biUnion_image]
  rfl

/-- Exact local template matching gives the six-vertex contribution used in
the finite budget: only canonical type 6 can contribute one. -/
theorem six_relation_excess_of_cell {n : Nat}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (F : Face P 3) (i : Fin 7) (f : Fin 6 ↪ Fin n)
    (hcell : actualCell P e.symm F = mapCell f (cellOfBoundary (N6.templates i))) :
    facetPolygonExcess P F - (actualPolygonRelationRank P e F : Int) ≤
      (if i = 6 then 1 else 0) := by
  have hPcard : 3 ≤ P.vertices.card := by
    have h := vertices_card_ge_dim_add_one P
    rw [hP] at h
    omega
  have hg := congrArg cellExcess hcell
  rw [actualCell_excess, mapCell_excess] at hg
  have hb := six_excess_bound i
  rw [← hg] at hb
  by_cases hi : i = 6
  · simp only [if_pos hi] at hb ⊢
    exact relation_excess_le P e hPcard F 1 (by decide) hb
  · simp only [if_neg hi] at hb ⊢
    exact relation_excess_le P e hPcard F 0 (by decide) hb

/-- For a seven-vertex facet with at least seven polygon faces, only canonical
type 13 can contribute a positive local relation excess. -/
theorem seven_relation_excess_of_cell {n : Nat}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (F : Face P 3) (i : Fin 34) (f : Fin 7 ↪ Fin n)
    (hcell : actualCell P e.symm F = mapCell f (cellOfBoundary (N7.templates i)))
    (hfaces : 7 ≤ Nat.card (FaceBelow P F.val.carrier 2)) :
    facetPolygonExcess P F - (actualPolygonRelationRank P e F : Int) ≤
      (if i = 13 then 1 else 0) := by
  have hF : facetVertexCount P F = 7 := by
    have h := congrArg (fun C => C.vertices.card) hcell
    rw [actualCell_vertex_card, mapCell_vertex_card] at h
    simpa only [cellOfBoundary, Finset.card_univ, Fintype.card_fin] using h
  have hle := seven_relation_excess_le_one P hP e F hF hfaces
  by_cases hi : i = 13
  · simpa only [if_pos hi] using hle
  · rw [if_neg hi]
    by_contra hpos
    have he : facetPolygonExcess P F - (actualPolygonRelationRank P e F : Int) = 1 := by
      omega
    obtain ⟨hq, hu⟩ := seven_excess_one_signature P hP e F hF hfaces he
    have hqc := congrArg (fun C => cellRidgeSizeCount C 4) hcell
    rw [actual_quadrilateral_count, mapCell_ridge_size_count, hq] at hqc
    have huc := congrArg (fun C => (quadrilateralVertices C).card) hcell
    rw [actual_quadrilateral_vertices, mapCell_quadrilateral_vertices,
      Finset.card_image_of_injective _ f.injective, hu] at huc
    exact hi (cell_signature_identifies i hqc.symm huc.symm)

theorem actual_seven_relation_excess_of_template {n : Nat}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hn : P.vertices.card = 10) (hN : 10 ≤ (nonsimplicialFacets P).card)
    (F : Face P 3) (i : Fin 34)
    (loc : (facePolytope P F.val.isFace).vertices ≃ Fin 7)
    (h : polygonBoundary (facePolytope P F.val.isFace) loc = N7.templates i) :
    facetPolygonExcess P F - (actualPolygonRelationRank P e F : Int) ≤
      (if i = 13 then 1 else 0) := by
  have hcell := actualCell_of_template P e.symm F loc (N7.templates i) h
  have hF : facetVertexCount P F = 7 := by
    have hv := congrArg (fun C => C.vertices.card) hcell
    rw [actualCell_vertex_card, mapCell_vertex_card] at hv
    simpa only [cellOfBoundary, Finset.card_univ, Fintype.card_fin] using hv
  exact seven_relation_excess_of_cell P hP e F i _ hcell
    (seven_vertex_facet_has_at_least_seven_ridges P hP e hn hN F hF)

end Papers.RationalityTen.ActualFacetRelationExcess
