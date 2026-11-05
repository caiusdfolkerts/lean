module
public import Consolidated.LargeFacetRelations
public import Consolidated.GraphBoundarySemantics
public import Consolidated.SmallFacetEncoding

@[expose] public section

/-!
# Exact counts with one seven-vertex facet

The counts in this file are intrinsic to an actual convex four-polytope.
The distinguished facet has seven vertices; every other facet has at most six.
The identities retain all pentagons and all six-vertex facet types.
-/

noncomputable section
namespace Papers.RationalityTen.SevenFacetBudgetIdentities

open Finset Set
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeSmallFacetBounds Papers.PolytopeFacetSurplus
open Papers.PolytopeRelationBudget Papers.PolytopeNonedgeAllocation
open Papers.PolytopeMasterBudget
open Papers.PolytopeFaceNonedges Papers.PolytopeFaceRestriction
open ChirotopeDensity

local instance faceFintype {d : Nat} (P : ConvexPolytope d) (k : Nat) :
    Fintype (Face P k) := Fintype.ofFinite _
local instance belowFintype {d : Nat} (P : ConvexPolytope d)
    (A : Set (E d)) (k : Nat) : Fintype (FaceBelow P A k) := Fintype.ofFinite _

/-- Tetrahedral facets, defined by their actual number of vertices. -/
def tetrahedralFacets {d : Nat} (P : ConvexPolytope d) : Finset (Face P 3) :=
  Finset.univ.filter fun F => facetVertexCount P F = 4

/-- The square-pyramid class among the five-vertex facets. -/
def smallSquareFacets {d : Nat} (P : ConvexPolytope d) : Finset (Face P 3) :=
  Finset.univ.filter fun F => facetVertexCount P F = 5 ∧ facetPolygonExcess P F = 1

/-- The triangular-bipyramid class among the five-vertex facets. -/
def smallBipyramidFacets {d : Nat} (P : ConvexPolytope d) : Finset (Face P 3) :=
  Finset.univ.filter fun F => facetVertexCount P F = 5 ∧ facetPolygonExcess P F = 0

theorem facet_count_eq_tetrahedra_add_nonsimplicial {d : Nat} (P : ConvexPolytope d) :
    Nat.card (Face P 3) =
      (tetrahedralFacets P).card + (nonsimplicialFacets P).card := by
  have hpoint (F : Face P 3) : (1 : Nat) =
      (if facetVertexCount P F = 4 then 1 else 0) +
        (if 4 < facetVertexCount P F then 1 else 0) := by
    have hmin : 4 ≤ facetVertexCount P F := face_vertices_card_ge_dim_add_one P 3 F
    split_ifs <;> omega
  have h := Finset.sum_congr (s₁ := (Finset.univ : Finset (Face P 3)))
    rfl (fun F _ => hpoint F)
  simpa [Finset.sum_add_distrib, tetrahedralFacets, nonsimplicialFacets,
    Nat.card_eq_fintype_card] using h

theorem facet_excess_eq {d : Nat} (P : ConvexPolytope d)
    (F₀ : Face P 3) (hF₀ : facetVertexCount P F₀ = 7)
    (hother : ∀ F : Face P 3, F ≠ F₀ → facetVertexCount P F ≤ 6) :
    facetExcess P =
      (nonsimplicialFacets P).card + (sixVertexFacets P).card + (2 : Int) := by
  have hpoint (F : Face P 3) : (facetVertexCount P F : Int) - 4 =
      (if 4 < facetVertexCount P F then 1 else 0) +
        (if facetVertexCount P F = 6 then 1 else 0) +
          (if F = F₀ then 2 else 0) := by
    by_cases hF : F = F₀
    · subst F
      simp [hF₀]
    · have hmin : 4 ≤ facetVertexCount P F := face_vertices_card_ge_dim_add_one P 3 F
      have hmax := hother F hF
      rw [if_neg hF]
      split_ifs <;> omega
  change (∑ F : Face P 3, ((facetVertexCount P F : Int) - 4)) = _
  simp_rw [hpoint]
  simp [Finset.sum_add_distrib, nonsimplicialFacets, sixVertexFacets]

/-- Exact allocated nonedge weight, including the half-weight contribution
of every local pentagon. Every polygon is incident to exactly two facets. -/
theorem allocated_weight_sum {d : Nat} (P : ConvexPolytope d) (hP : P.dim = 4)
    (F₀ : Face P 3) (hF₀ : facetVertexCount P F₀ = 7)
    (hother : ∀ F : Face P 3, F ≠ F₀ → facetVertexCount P F ≤ 6)
    (hpolygons : ∀ R : Face P 2, Nat.card (VerticesOn P R.val.carrier) ≤ 5) :
    (∑ F : Face P 3, allocatedFacetWeight P F) =
      (facetExcess P : Rat) + (sixVertexFacets P).card + 3 -
        (pentagonalFaces P).card := by
  have hpoint (F : Face P 3) : allocatedFacetWeight P F =
      ((facetVertexCount P F : Rat) - 4) +
        (if F ∈ sixVertexFacets P then 1 else 0) +
          (if F = F₀ then 3 else 0) - (facetPolygonSizeCount P F 5 : Rat) / 2 := by
    rw [allocatedFacetWeight_of_polygon_card_le_five P F (fun R => hpolygons R.val)]
    have hmem : F ∈ sixVertexFacets P ↔ facetVertexCount P F = 6 := by
      simp [sixVertexFacets]
    by_cases hF : F = F₀
    · subst F
      simp [hmem, hF₀] <;> ring
    · have hmin : 4 ≤ facetVertexCount P F := face_vertices_card_ge_dim_add_one P 3 F
      have hmax := hother F hF
      have hc : facetVertexCount P F = 4 ∨ facetVertexCount P F = 5 ∨
          facetVertexCount P F = 6 := by omega
      rcases hc with hc | hc | hc <;> simp [hmem, hF, hc] <;> ring
  have hE : (∑ F : Face P 3, ((facetVertexCount P F : Rat) - 4)) =
      (facetExcess P : Rat) := by
    unfold facetExcess facetVertexCount
    push_cast
    rfl
  have hpZ := sum_facet_polygon_size_counts P hP 5
  have hpQ : (∑ F : Face P 3, (facetPolygonSizeCount P F 5 : Rat)) =
      2 * (pentagonalFaces P).card := by exact_mod_cast hpZ
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    hE, ← Finset.sum_div, hpQ]
  simp

/-- Two potentially exceptional facets account for every local redundancy;
all other facets have at most five vertices and hence zero local redundancy. -/
theorem two_large_facets_shared_count {d n : Nat}
    (P : ConvexPolytope d) (hP : P.dim = 4) (e : Fin n ≃ P.vertices)
    (F₀ G₀ : Face P 3) (hne : F₀ ≠ G₀)
    (hother : ∀ F : Face P 3, F ≠ F₀ → F ≠ G₀ → facetVertexCount P F ≤ 5) :
    sharedRelationCount P (actualPolygonRelationRank P e) =
      facetExcess P - polygonExcess P +
        (facetPolygonExcess P F₀ - (actualPolygonRelationRank P e F₀ : Int)) +
        (facetPolygonExcess P G₀ - (actualPolygonRelationRank P e G₀ : Int)) := by
  let ε₀ := facetPolygonExcess P F₀ - (actualPolygonRelationRank P e F₀ : Int)
  let ε₁ := facetPolygonExcess P G₀ - (actualPolygonRelationRank P e G₀ : Int)
  have hpoint (F : Face P 3) : (actualPolygonRelationRank P e F : Int) =
      facetPolygonExcess P F - (if F = F₀ then ε₀ else 0) -
        (if F = G₀ then ε₁ else 0) := by
    by_cases hF : F = F₀
    · subst F
      simp only [ite_true, if_neg hne, sub_zero, ε₀]
      ring
    · by_cases hG : F = G₀
      · subst F
        simp only [if_neg hne.symm, ite_true, sub_zero, ε₁]
        ring
      · rw [if_neg hF, if_neg hG, sub_zero, sub_zero]
        exact actualPolygonRelationRank_eq_excess_of_card_le_five P e F (hother F hF hG)
  have hsum : (∑ F : Face P 3, (actualPolygonRelationRank P e F : Int)) =
      2 * polygonExcess P - ε₀ - ε₁ := by
    simp_rw [hpoint]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, sum_facet_polygon_excess P hP]
    simp
  unfold sharedRelationCount
  rw [hsum]
  dsimp only [ε₀, ε₁]
  ring

theorem small_facet_pentagons_zero {d : Nat} (P : ConvexPolytope d)
    (F : Face P 3) (hF : facetVertexCount P F ≤ 5) : facetPolygonSizeCount P F 5 = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro R hR
  have heq := (Finset.mem_filter.mp hR).2
  have hlt := polygon_card_lt_containing_facet P R.val F R.property
  omega

theorem local_polygon_count_zero_of_lt {d : Nat} (P : ConvexPolytope d)
    (F : Face P 3) (k : Nat)
    (h : ∀ R : FaceBelow P F.val.carrier 2,
      Nat.card (VerticesOn P R.val.val.carrier) < k) : facetPolygonSizeCount P F k = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro R hR
  have heq := (Finset.mem_filter.mp hR).2
  have hlt := h R
  omega

theorem local_excess_eq_quad_add_twice_pentagons {d : Nat} (P : ConvexPolytope d)
    (F : Face P 3)
    (hpolygons : ∀ R : FaceBelow P F.val.carrier 2,
      Nat.card (VerticesOn P R.val.val.carrier) ≤ 5) :
    facetPolygonExcess P F =
      (facetPolygonSizeCount P F 4 : Int) + 2 * facetPolygonSizeCount P F 5 := by
  have hpoint (R : FaceBelow P F.val.carrier 2) :
      (Nat.card (VerticesOn P R.val.val.carrier) : Int) - 3 =
        (if Nat.card (VerticesOn P R.val.val.carrier) = 4 then 1 else 0) +
          2 * (if Nat.card (VerticesOn P R.val.val.carrier) = 5 then 1 else 0) := by
    have hlo := face_vertices_card_ge_dim_add_one P 2 R.val
    have hhi := hpolygons R
    split_ifs <;> omega
  rw [facetPolygonExcess_eq_sum_faceBelow]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_boole, facetPolygonSizeCount]

theorem small_facet_excess_eq_quadrilaterals {d : Nat} (P : ConvexPolytope d)
    (F : Face P 3) (hF : facetVertexCount P F ≤ 5) :
    facetPolygonExcess P F = facetPolygonSizeCount P F 4 := by
  have hpoint (R : FaceBelow P F.val.carrier 2) :
      (Nat.card (VerticesOn P R.val.val.carrier) : Int) - 3 =
        if Nat.card (VerticesOn P R.val.val.carrier) = 4 then 1 else 0 := by
    have hlo := face_vertices_card_ge_dim_add_one P 2 R.val
    have hlt := polygon_card_lt_containing_facet P R.val F R.property
    split_ifs <;> omega
  rw [facetPolygonExcess_eq_sum_faceBelow]
  simp_rw [hpoint]
  simp [facetPolygonSizeCount]

theorem small_facet_quad_indicator {d : Nat} (P : ConvexPolytope d)
    (F : Face P 3) (hF : facetVertexCount P F ≤ 5) :
    facetPolygonSizeCount P F 4 = if F ∈ smallSquareFacets P then 1 else 0 := by
  have hg := small_facet_excess_eq_quadrilaterals P F hF
  have hmax := facetPolygonExcess_le_one_of_card_le_five P F hF
  have hmin := twice_facet_polygon_excess_le_three_vertices_sub_twelve P F
  have hvmin : 4 ≤ facetVertexCount P F := face_vertices_card_ge_dim_add_one P 3 F
  simp only [smallSquareFacets, Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs <;> omega

theorem local_polygon_count_le_global {d : Nat} (P : ConvexPolytope d)
    (F : Face P 3) (k : Nat) : facetPolygonSizeCount P F k ≤ (polygonSizeFaces P k).card := by
  unfold facetPolygonSizeCount polygonSizeFaces
  apply Finset.card_le_card_of_injOn (fun R => R.val)
  · intro R hR
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hR).2⟩
  · intro R hR S hS h
    exact Subtype.ext h

theorem nonsimplicial_count_eq {d : Nat} (P : ConvexPolytope d)
    (F₀ : Face P 3) (hF₀ : facetVertexCount P F₀ = 7)
    (hother : ∀ F : Face P 3, F ≠ F₀ → facetVertexCount P F ≤ 6) :
    (nonsimplicialFacets P).card = (smallBipyramidFacets P).card +
      (smallSquareFacets P).card + (sixVertexFacets P).card + 1 := by
  have hpoint (F : Face P 3) :
      (if 4 < facetVertexCount P F then (1 : Nat) else 0) =
        (if F ∈ smallBipyramidFacets P then 1 else 0) +
          (if F ∈ smallSquareFacets P then 1 else 0) +
            (if F ∈ sixVertexFacets P then 1 else 0) +
              (if F = F₀ then 1 else 0) := by
    by_cases hF : F = F₀
    · subst F
      simp [smallBipyramidFacets, smallSquareFacets, sixVertexFacets, hF₀]
    · have hmin : 4 ≤ facetVertexCount P F := face_vertices_card_ge_dim_add_one P 3 F
      have hmax := hother F hF
      have hc : facetVertexCount P F = 4 ∨ facetVertexCount P F = 5 ∨
          facetVertexCount P F = 6 := by omega
      rcases hc with h4 | h5 | h6
      · simp [smallBipyramidFacets, smallSquareFacets, sixVertexFacets, hF, h4]
      · have hgmin : 0 ≤ facetPolygonExcess P F :=
          polygonExcess_nonnegative (facePolytope P F.val.isFace)
        have hgmax := facetPolygonExcess_le_one_of_card_le_five P F (by omega)
        have hg : facetPolygonExcess P F = 0 ∨ facetPolygonExcess P F = 1 := by omega
        rcases hg with hg | hg <;>
          simp [smallBipyramidFacets, smallSquareFacets, sixVertexFacets, hF, h5, hg]
      · simp [smallBipyramidFacets, smallSquareFacets, sixVertexFacets, hF, h6]
  have h := Finset.sum_congr (s₁ := (Finset.univ : Finset (Face P 3)))
    rfl (fun F _ => hpoint F)
  simpa [Finset.sum_add_distrib, nonsimplicialFacets] using h

/-- The quadrilaterals contributed by small facets are exactly one per
square pyramid. The remaining contribution belongs to the distinguished facet. -/
theorem quadrilateral_incidence_one_large {d : Nat}
    (P : ConvexPolytope d) (hP : P.dim = 4)
    (F₀ : Face P 3) (hF₀ : 5 < facetVertexCount P F₀)
    (hother : ∀ F : Face P 3, F ≠ F₀ → facetVertexCount P F ≤ 5) :
    2 * (quadrilateralFaces P).card =
      (smallSquareFacets P).card + facetPolygonSizeCount P F₀ 4 := by
  have hpoint (F : Face P 3) : (facetPolygonSizeCount P F 4 : Int) =
      (if F ∈ smallSquareFacets P then 1 else 0) +
        (if F = F₀ then (facetPolygonSizeCount P F₀ 4 : Int) else 0) := by
    by_cases hF : F = F₀
    · subst F
      have hn : F₀ ∉ smallSquareFacets P := by
        simp only [smallSquareFacets, Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      simp [hn]
    · have hq := small_facet_quad_indicator P F (hother F hF)
      rw [hq, if_neg hF, add_zero]
      split_ifs <;> rfl
  have hsum := sum_facet_polygon_size_counts P hP 4
  have hpointSum := Finset.sum_congr (s₁ := (Finset.univ : Finset (Face P 3)))
    rfl (fun F _ => hpoint F)
  rw [hpointSum] at hsum
  have h : ((smallSquareFacets P).card : Int) + facetPolygonSizeCount P F₀ 4 =
      2 * (quadrilateralFaces P).card := by
    simpa [Finset.sum_add_distrib, polygonSizeFaces, quadrilateralFaces] using hsum
  exact_mod_cast h.symm

theorem quadrilateral_incidence_two_large {d : Nat}
    (P : ConvexPolytope d) (hP : P.dim = 4)
    (F₀ G₀ : Face P 3) (hne : F₀ ≠ G₀)
    (hF₀ : 5 < facetVertexCount P F₀) (hG₀ : 5 < facetVertexCount P G₀)
    (hother : ∀ F : Face P 3, F ≠ F₀ → F ≠ G₀ → facetVertexCount P F ≤ 5) :
    2 * (quadrilateralFaces P).card = (smallSquareFacets P).card +
      facetPolygonSizeCount P F₀ 4 + facetPolygonSizeCount P G₀ 4 := by
  have hnot (F : Face P 3) (hF : 5 < facetVertexCount P F) :
      F ∉ smallSquareFacets P := by
    simp only [smallSquareFacets, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hpoint (F : Face P 3) : (facetPolygonSizeCount P F 4 : Int) =
      (if F ∈ smallSquareFacets P then 1 else 0) +
        (if F = F₀ then (facetPolygonSizeCount P F₀ 4 : Int) else 0) +
          (if F = G₀ then (facetPolygonSizeCount P G₀ 4 : Int) else 0) := by
    by_cases hF : F = F₀
    · subst F
      simp [hnot F₀ hF₀, hne]
    · by_cases hG : F = G₀
      · subst F
        simp [hnot G₀ hG₀, hne.symm]
      · have hq := small_facet_quad_indicator P F (hother F hF hG)
        rw [hq, if_neg hF, if_neg hG, add_zero, add_zero]
        split_ifs <;> rfl
  have hsum := sum_facet_polygon_size_counts P hP 4
  have hpointSum := Finset.sum_congr (s₁ := (Finset.univ : Finset (Face P 3)))
    rfl (fun F _ => hpoint F)
  rw [hpointSum] at hsum
  have h : ((smallSquareFacets P).card : Int) + facetPolygonSizeCount P F₀ 4 +
      facetPolygonSizeCount P G₀ 4 = 2 * (quadrilateralFaces P).card := by
    simpa [Finset.sum_add_distrib, polygonSizeFaces, quadrilateralFaces] using hsum
  exact_mod_cast h.symm

/-- Every pentagon is accounted for in the two large facets; small facets
contain no pentagon. This identity is needed even when the global count is zero. -/
theorem pentagon_incidence_two_large {d : Nat}
    (P : ConvexPolytope d) (hP : P.dim = 4)
    (F₀ G₀ : Face P 3) (hne : F₀ ≠ G₀)
    (hother : ∀ F : Face P 3, F ≠ F₀ → F ≠ G₀ → facetVertexCount P F ≤ 5) :
    2 * (pentagonalFaces P).card =
      facetPolygonSizeCount P F₀ 5 + facetPolygonSizeCount P G₀ 5 := by
  have hpoint (F : Face P 3) : (facetPolygonSizeCount P F 5 : Int) =
      (if F = F₀ then (facetPolygonSizeCount P F₀ 5 : Int) else 0) +
        (if F = G₀ then (facetPolygonSizeCount P G₀ 5 : Int) else 0) := by
    by_cases hF : F = F₀
    · subst F
      simp [hne]
    · by_cases hG : F = G₀
      · subst F
        simp [hne.symm]
      · rw [small_facet_pentagons_zero P F (hother F hF hG), if_neg hF, if_neg hG]
        norm_num
  have hsum := sum_facet_polygon_size_counts P hP 5
  have hpointSum := Finset.sum_congr (s₁ := (Finset.univ : Finset (Face P 3)))
    rfl (fun F _ => hpoint F)
  rw [hpointSum] at hsum
  have h : (facetPolygonSizeCount P F₀ 5 : Int) + facetPolygonSizeCount P G₀ 5 =
      2 * (pentagonalFaces P).card := by
    simpa [Finset.sum_add_distrib, pentagonalFaces] using hsum
  exact_mod_cast h.symm

end Papers.RationalityTen.SevenFacetBudgetIdentities
