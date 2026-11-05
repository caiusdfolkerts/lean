module
public import Consolidated.SmallPolytopeBudgets

@[expose] public section
noncomputable section

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeRelationBudget Papers.PolytopeMasterBudget
open Papers.PolytopeFacetSurplus

namespace Papers.RationalityTen.ChirotopeDensity

/-- The polygon rows are part of the shared sparse relation matrix. -/
theorem polygon_excess_le_sparse_row_count {d n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices) :
    polygonExcess P ≤ (Fintype.card (SparseSharedRowIndex P e) : ℤ) := by
  have hc : (Fintype.card (SparseSharedRowIndex P e) : ℤ) =
      (∑ R : Face P 2, ((actualPolygonSparseBasis P e R).count : ℤ)) +
      (∑ F : Face P 3, ((actualFacetSparseSupplement P e F).count : ℤ)) := by
    simp only [SparseSharedRowIndex, Fintype.card_sum, Fintype.card_sigma,
      Fintype.card_fin, Nat.cast_add, Nat.cast_sum]
  have hg : (∑ R : Face P 2, ((actualPolygonSparseBasis P e R).count : ℤ)) =
      polygonExcess P := by
    simp only [actualPolygonSparseBasis_count, polygonExcess]
  have hs : (0 : ℤ) ≤ ∑ F : Face P 3,
      ((actualFacetSparseSupplement P e F).count : ℤ) :=
    Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _
  omega

/-- Each polygon belongs to two facets, so the local polygon ranks sum
 to at most twice the global polygon excess. -/
theorem facet_excess_sub_polygon_le_sparse_row_count {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices) :
    facetExcess P - polygonExcess P ≤
      (Fintype.card (SparseSharedRowIndex P e) : ℤ) := by
  have hs : (∑ F : Face P 3, (actualPolygonRelationRank P e F : ℤ)) ≤
      2 * polygonExcess P := by
    calc
      _ ≤ ∑ F : Face P 3, facetPolygonExcess P F :=
        Finset.sum_le_sum fun F _ => actualPolygonRelationRank_le P e F
      _ = _ := sum_facet_polygon_excess P hP
  have hc := sparseSharedRowIndex_card P e
  unfold sharedRelationCount at hc
  omega

/-- The total facet excess is controlled by the selected relation count. -/
theorem facet_excess_le_twice_sparse_row_count {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices) :
    facetExcess P ≤ 2 * (Fintype.card (SparseSharedRowIndex P e) : ℤ) := by
  have hg := polygon_excess_le_sparse_row_count P e
  have hE := facet_excess_sub_polygon_le_sparse_row_count P hP e
  omega

def largeFacets {d : ℕ} (P : ConvexPolytope d) : Finset (Face P 3) :=
  Finset.univ.filter fun F => 8 ≤ facetVertexCount P F

@[simp] theorem mem_largeFacets {d : ℕ} (P : ConvexPolytope d) (F : Face P 3) :
    F ∈ largeFacets P ↔ 8 ≤ facetVertexCount P F := by
  simp [largeFacets]

private theorem facet_excess_weight_le {d : ℕ} (P : ConvexPolytope d)
    (F : Face P 3) :
    (if F ∈ nonsimplicialFacets P then (1 : ℤ) else 0) +
      3 * (if F ∈ largeFacets P then (1 : ℤ) else 0) ≤
      (facetVertexCount P F : ℤ) - 4 := by
  have hmin := Nat.succ_le_iff.mpr
    (Papers.PolytopeThreeIncidences.face_vertex_card_gt_dimension P 3 F)
  change 4 ≤ facetVertexCount P F at hmin
  by_cases hN : F ∈ nonsimplicialFacets P <;>
    by_cases hL : F ∈ largeFacets P
  · have hn := (mem_nonsimplicialFacets P F).mp hN
    have hl := (mem_largeFacets P F).mp hL
    simp only [if_pos hN, if_pos hL]
    omega
  · have hn := (mem_nonsimplicialFacets P F).mp hN
    simp only [if_pos hN, if_neg hL]
    omega
  · have hl := (mem_largeFacets P F).mp hL
    have hn := mt (mem_nonsimplicialFacets P F).mpr hN
    omega
  · simp only [if_neg hN, if_neg hL]
    omega

/-- A nonsimplicial facet uses one unit of excess, and a large facet
 uses three further units. -/
theorem nonsimplicial_add_three_large_le_excess {d : ℕ} (P : ConvexPolytope d) :
    ((nonsimplicialFacets P).card : ℤ) + 3 * (largeFacets P).card ≤ facetExcess P := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun F _ => facet_excess_weight_le P F)
  change (∑ F : Face P 3, ((if F ∈ nonsimplicialFacets P then (1 : ℤ) else 0) +
    3 * (if F ∈ largeFacets P then (1 : ℤ) else 0))) ≤ facetExcess P at h
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole,
    Finset.filter_mem_eq_inter, Finset.univ_inter] using h

/-- The only facets whose polygon rank can vary number at most two. -/
theorem large_facets_card_le_two {n : ℕ} (P : ConvexPolytope 4)
    (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hc : Fintype.card (SparseSharedRowIndex P e) ≤ 8)
    (hN : 10 ≤ (nonsimplicialFacets P).card) :
    (largeFacets P).card ≤ 2 := by
  have hE := facet_excess_le_twice_sparse_row_count P hP e
  have hcount := nonsimplicial_add_three_large_le_excess P
  omega

/-- Two large facets exhaust the excess budget, forcing the exact sizes
 needed for the two-exceptional-facet case. -/
theorem two_large_facets_equality {n : ℕ} (P : ConvexPolytope 4)
    (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hc : Fintype.card (SparseSharedRowIndex P e) ≤ 8)
    (hN : 10 ≤ (nonsimplicialFacets P).card)
    (hL : 2 ≤ (largeFacets P).card) :
    (nonsimplicialFacets P).card = 10 ∧ (largeFacets P).card = 2 ∧
      facetExcess P = 16 ∧ polygonExcess P = 8 ∧
      Fintype.card (SparseSharedRowIndex P e) = 8 ∧
      (∀ F ∈ largeFacets P, facetVertexCount P F = 8) ∧
      (∀ F ∈ nonsimplicialFacets P, F ∉ largeFacets P → facetVertexCount P F = 5) := by
  have hE := facet_excess_le_twice_sparse_row_count P hP e
  have hcount := nonsimplicial_add_three_large_le_excess P
  have hg := polygon_excess_le_sparse_row_count P e
  have hEg := facet_excess_sub_polygon_le_sparse_row_count P hP e
  have hN' : (nonsimplicialFacets P).card = 10 := by omega
  have hL' : (largeFacets P).card = 2 := by omega
  have hE' : facetExcess P = 16 := by omega
  have hg' : polygonExcess P = 8 := by omega
  have hc' : Fintype.card (SparseSharedRowIndex P e) = 8 := by omega
  have hsum : (∑ F : Face P 3,
      ((if F ∈ nonsimplicialFacets P then (1 : ℤ) else 0) +
        3 * (if F ∈ largeFacets P then (1 : ℤ) else 0))) =
      ∑ F : Face P 3, ((facetVertexCount P F : ℤ) - 4) := by
    change _ = facetExcess P
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole,
      Finset.filter_mem_eq_inter, Finset.univ_inter, hN', hL', hE']
    norm_num
  have heq := (Finset.sum_eq_sum_iff_of_le
    (fun F _ => facet_excess_weight_le P F)).mp hsum
  refine ⟨hN', hL', hE', hg', hc', ?_, ?_⟩
  · intro F hF
    have hNF : F ∈ nonsimplicialFacets P := by
      have hl := (mem_largeFacets P F).mp hF
      exact (mem_nonsimplicialFacets P F).mpr (by omega)
    have h := heq F (Finset.mem_univ _)
    rw [if_pos hNF, if_pos hF] at h
    omega
  · intro F hNF hF
    have h := heq F (Finset.mem_univ _)
    rw [if_pos hNF, if_neg hF] at h
    omega

/-- In the equality case all facets are already spanned by their polygon
 relation spaces, and every local polygon row is independent. -/
theorem two_large_facets_no_supplements {n : ℕ} (P : ConvexPolytope 4)
    (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hc : Fintype.card (SparseSharedRowIndex P e) ≤ 8)
    (hN : 10 ≤ (nonsimplicialFacets P).card)
    (hL : 2 ≤ (largeFacets P).card) :
    (∀ F : Face P 3, (actualFacetSparseSupplement P e F).count = 0) ∧
      (∀ F : Face P 3, (actualPolygonRelationRank P e F : ℤ) = facetPolygonExcess P F) := by
  obtain ⟨_, _, hE, hg, hc', _⟩ := two_large_facets_equality P hP e hc hN hL
  have hsum : (∑ F : Face P 3,
      ((actualFacetSparseSupplement P e F).count : ℤ)) = 0 := by
    have hcard : (Fintype.card (SparseSharedRowIndex P e) : ℤ) =
        polygonExcess P + ∑ F : Face P 3,
          ((actualFacetSparseSupplement P e F).count : ℤ) := by
      simp only [SparseSharedRowIndex, Fintype.card_sum, Fintype.card_sigma,
        Fintype.card_fin, Nat.cast_add, Nat.cast_sum, actualPolygonSparseBasis_count,
        polygonExcess]
    rw [hc', hg] at hcard
    omega
  have hsupp (F : Face P 3) : (actualFacetSparseSupplement P e F).count = 0 := by
    have h := Finset.single_le_sum
      (s := (Finset.univ : Finset (Face P 3)))
      (fun G _ => Int.natCast_nonneg (actualFacetSparseSupplement P e G).count)
      (Finset.mem_univ F)
    rw [hsum] at h
    omega
  refine ⟨hsupp, ?_⟩
  have hsumrank := sparseSharedRowIndex_card P e
  unfold sharedRelationCount at hsumrank
  rw [hc', hg, hE] at hsumrank
  have hsumg := sum_facet_polygon_excess P hP
  rw [hg] at hsumg
  have heqsum : (∑ F : Face P 3, (actualPolygonRelationRank P e F : ℤ)) =
      ∑ F : Face P 3, facetPolygonExcess P F := by omega
  exact fun F => (Finset.sum_eq_sum_iff_of_le
    (fun G _ => actualPolygonRelationRank_le P e G)).mp heqsum F (Finset.mem_univ F)

end Papers.RationalityTen.ChirotopeDensity
