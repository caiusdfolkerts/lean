module
public import SevenFacetProfileTransport
public import ActualFacetRelationExcess
public import FacetAdjacencyBudget
public import SevenFacetBudgetArithmetic

@[expose] public section

/-!
# The complete seven-vertex, no-six-vertex numerical case

This is a statement about an actual ten-vertex four-polytope. Every input to
the finite 69-row budget lookup is derived from its geometry. The exact facet
template is retained separately; its numerical profile is used only to select
the row and the numbers of small facets.
-/

noncomputable section
namespace Papers.RationalityTen.ActualSevenNoSixBudget

open Finset
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeSmallFacetBounds Papers.PolytopeFacetSurplus
open Papers.PolytopeRelationBudget Papers.PolytopeNonedgeAllocation
open Papers.PolytopeFaceNonedges Papers.PolytopeMasterBudget
open ChirotopeDensity MatroidChecked.FacetBoundaryEncoding
open ActualFacetCatalogueTransport CellFacetInvariants FiniteCycleCandidates
open SevenFacetBudgetIdentities SevenFacetProfileTransport ActualFacetRelationExcess
open MatroidChecked.SevenBudgetCoverage

local instance faceFintype {d : Nat} (P : ConvexPolytope d) (k : Nat) :
    Fintype (Face P k) := Fintype.ofFinite _

theorem actual_no_six_covered
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin 10 ≃ P.vertices)
    (hn : P.vertices.card = 10)
    (hN : 10 ≤ (nonsimplicialFacets P).card)
    (hc : 9 ≤ Fintype.card (SparseSharedRowIndex P e))
    (F₀ : Face P 3) (i : Fin 34) (f : Fin 7 ↪ Fin 10)
    (hcell : actualCell P e.symm F₀ = mapCell f (cellOfBoundary (N7.templates i)))
    (hother : ∀ F : Face P 3, F ≠ F₀ → facetVertexCount P F ≤ 5) :
    facetExcess P = 12 ∧
      ∃ B, B ∈ noSixCases ∧
        NoSixMatches i (Nat.card (Face P 3)) (quadrilateralFaces P).card B ∧
        B.SP = (smallSquareFacets P).card ∧
        B.BP = (smallBipyramidFacets P).card ∧
        B.T = (tetrahedralFacets P).card := by
  let m := Nat.card (Face P 3)
  let N := (nonsimplicialFacets P).card
  let q := (quadrilateralFaces P).card
  let c := Fintype.card (SparseSharedRowIndex P e)
  let D := Nat.card (Nonedge P)
  let r := facetPolygonSizeCount P F₀ 4
  let SP := (smallSquareFacets P).card
  let BP := (smallBipyramidFacets P).card
  let T := (tetrahedralFacets P).card
  let ε := facetPolygonExcess P F₀ - (actualPolygonRelationRank P e F₀ : Int)
  let eps := ε.toNat
  have hF₀ : facetVertexCount P F₀ = 7 := by
    have h := congrArg (fun C => C.vertices.card) hcell
    rw [actualCell_vertex_card, mapCell_vertex_card] at h
    simpa only [cellOfBoundary, Finset.card_univ, Fintype.card_fin] using h
  have hother6 (F : Face P 3) (hF : F ≠ F₀) : facetVertexCount P F ≤ 6 :=
    (hother F hF).trans (by decide)
  have hL : (sixVertexFacets P).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro F hF
    have hsix : facetVertexCount P F = 6 := (Finset.mem_filter.mp hF).2
    by_cases heq : F = F₀
    · subst F
      omega
    · have hb := hother F heq
      omega
  have hEZ : facetExcess P = ((N + 2 : Nat) : Int) := by
    simpa [N, hL] using facet_excess_eq P F₀ hF₀ hother6
  have hpoly4 := polygon_card_le_four_of_one_large_facet P hP F₀ hother
  have hpoly5 (R : Face P 2) : Nat.card (VerticesOn P R.val.carrier) ≤ 5 :=
    (hpoly4 R).trans (by decide)
  have hp0 : (pentagonalFaces P).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro R hR
    have hfive : Nat.card (VerticesOn P R.val.carrier) = 5 := (Finset.mem_filter.mp hR).2
    have hfour := hpoly4 R
    omega
  have hg : polygonExcess P = (q : Int) := by
    have h := polygonExcess_eq_quadrilaterals_add_twice_pentagons P hpoly5
    simpa [q, hp0] using h
  have hpF : facetPolygonSizeCount P F₀ 5 = 0 :=
    local_polygon_count_zero_of_lt P F₀ 5 (fun R => by have h := hpoly4 R.val; omega)
  have hhF : facetPolygonSizeCount P F₀ 6 = 0 :=
    local_polygon_count_zero_of_lt P F₀ 6 (fun R => by have h := hpoly4 R.val; omega)
  have hgF : facetPolygonExcess P F₀ = (r : Int) := by
    have h := local_excess_eq_quad_add_twice_pentagons P F₀ (fun R => hpoly5 R.val)
    simpa [r, hpF] using h
  have heps_nonneg : 0 ≤ ε := sub_nonneg.mpr (actualPolygonRelationRank_le P e F₀)
  have hepsZ : (eps : Int) = ε := Int.toNat_of_nonneg heps_nonneg
  have hfaces := seven_vertex_facet_has_at_least_seven_ridges P hP e hn hN F₀ hF₀
  have heps_bound : eps ≤ epsilonSeven i := by
    have h := seven_relation_excess_of_cell P hP e F₀ i f hcell hfaces
    change ε ≤ (if i = 13 then 1 else 0) at h
    by_cases hi : i = 13 <;> simp only [epsilonSeven, hi, ite_true, ite_false] at h ⊢ <;> omega
  have heps_small : r ≤ 2 → eps = 0 := by
    intro hr
    have hqF : (facetQuadrilateralFaces P F₀).card ≤ 2 := hr
    have hzero := seven_excess_zero_of_few_quadrilaterals P hP e F₀ hF₀ hfaces hqF
    change ε = 0 at hzero
    omega
  have hrowsZ := one_large_facet_shared_count P hP e F₀ hother
  rw [← sparseSharedRowIndex_card P e, hEZ, hg] at hrowsZ
  change (c : Int) = ((N + 2 : Nat) : Int) - q + ε at hrowsZ
  have hrows : c + q = N + 2 + eps := by omega
  have heulerZ := ten_vertex_excess_identity P hP hn
  rw [hEZ, hg] at heulerZ
  change ((N + 2 : Nat) : Int) = 35 - (m : Int) - D + q at heulerZ
  have heuler : m + (N + 2) + D = 35 + q := by omega
  have hweightQ := allocated_weights_le_nonedge_card P hP
  rw [allocated_weight_sum P hP F₀ hF₀ hother6 hpoly5, hEZ, hL, hp0] at hweightQ
  have hweight : (N + 2) + 3 ≤ D := by
    norm_num only [Nat.cast_zero, add_zero, sub_zero, Int.cast_natCast] at hweightQ
    exact_mod_cast hweightQ
  have hface_formula := facet_polygon_excess_face_formula P F₀
  rw [hF₀, hgF] at hface_formula
  have hadj := seven_vertex_facet_nonsimplicial_count_le_ridges_add_three P hP e hn F₀ hF₀
  have hridges := facet_ridge_count_add_one_le_facets P hP e F₀
  have hridge : 11 ≤ m + r := by dsimp only [m]; omega
  have hneighbors : N + r ≤ 13 := by dsimp only [N]; omega
  have hrglobal : r ≤ q := by
    simpa only [r, q, polygonSizeFaces, quadrilateralFaces] using
      local_polygon_count_le_global P F₀ 4
  have hquad : SP + r = 2 * q :=
    (quadrilateral_incidence_one_large P hP F₀ (by omega) hother).symm
  have hcountN := nonsimplicial_count_eq P F₀ hF₀ hother6
  rw [hL] at hcountN
  change N = BP + SP + 0 + 1 at hcountN
  have hnonsimp : SP + BP + 1 = N := by omega
  have hcountm := facet_count_eq_tetrahedra_add_nonsimplicial P
  change m = T + N at hcountm
  have hNm : N ≤ m := by omega
  have hnum := SevenFacetBudgetArithmetic.no_six m N (N + 2) q c D r eps
    (epsilonSeven i) SP BP T hN hNm rfl hc hrows heps_bound (epsilonSeven_le i)
    heps_small heuler hweight hridge hneighbors hrglobal hquad hnonsimp hcountm.symm
  obtain ⟨hE12, hN10, hmlo, hmhi, hrlo, hrhi, hrq, hmq, hqcap,
    hr2q, h2qr, hSP, hBP, hT⟩ := hnum
  have hp := polygon_counts_of_seven_cell P e.symm F₀ i f hcell
  have hqr : (seven i).quads = r := hp.2.1.symm
  have hpent : (seven i).pentagons = 0 := hp.2.2.1.symm.trans hpF
  have hhex : (seven i).hexagons = 0 := hp.2.2.2.symm.trans hhF
  have hadmissible : NoSixAdmissible i m q := by
    refine ⟨hpent, hhex, hmlo, hmhi, ?_⟩
    simpa only [hqr] using
      (show 11 - m ≤ r ∧ r ≤ 3 ∧ r ≤ q ∧ m - 8 ≤ q ∧
        q ≤ 3 + epsilonSeven i ∧ r ≤ 2 * q ∧ 2 * q ≤ 9 + r from
        ⟨hrlo, hrhi, hrq, hmq, hqcap, hr2q, h2qr⟩)
  obtain ⟨B, hB, hmatch⟩ := no_six_covered i m q hadmissible
  have hmatch' := hmatch
  obtain ⟨_, _, _, _, _, hBSP, hBBP, hBT, _⟩ := hmatch
  refine ⟨by rw [hEZ, hE12]; rfl, B, hB, hmatch', ?_, ?_, ?_⟩
  · exact (hBSP.trans (by rw [hqr])).trans hSP.symm
  · exact (hBBP.trans (by rw [hqr])).trans hBP.symm
  · exact hBT.trans hT.symm

end Papers.RationalityTen.ActualSevenNoSixBudget
