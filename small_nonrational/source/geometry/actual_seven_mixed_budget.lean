module
public import SevenFacetProfileTransport
public import ActualFacetRelationExcess
public import FacetAdjacencyBudget
public import SevenFacetBudgetArithmetic

@[expose] public section

/-!
# The complete seven-vertex / six-vertex numerical case

The hypotheses retain both exact facet templates. All numerical assumptions
of the finite budget lookup are consequences of the actual face incidences,
Euler identity, allocated nonedge weights, and actual relation ranks.
In particular, the pentagon branch is derived from double counting; it is
not imposed as an extra restriction on the polytope.
-/

noncomputable section
namespace Papers.RationalityTen.ActualSevenMixedBudget

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

theorem actual_one_six_covered
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin 10 ≃ P.vertices)
    (hn : P.vertices.card = 10)
    (hN : 10 ≤ (nonsimplicialFacets P).card)
    (hc : 9 ≤ Fintype.card (SparseSharedRowIndex P e))
    (F₀ G₀ : Face P 3) (i : Fin 34) (j : Fin 7)
    (f : Fin 7 ↪ Fin 10) (g : Fin 6 ↪ Fin 10)
    (hcellF : actualCell P e.symm F₀ = mapCell f (cellOfBoundary (N7.templates i)))
    (hcellG : actualCell P e.symm G₀ = mapCell g (cellOfBoundary (N6.templates j)))
    (hother : ∀ F : Face P 3, F ≠ F₀ → F ≠ G₀ → facetVertexCount P F ≤ 5) :
    facetExcess P = 13 ∧
      ∃ B, B ∈ oneSixCases ∧ B.template = i.val ∧ B.sixTemplate = some j.val ∧
        B.m = Nat.card (Face P 3) ∧ B.E = 13 ∧
        B.q = (quadrilateralFaces P).card ∧
        B.SP = (smallSquareFacets P).card ∧
        B.BP = (smallBipyramidFacets P).card ∧
        B.T = (tetrahedralFacets P).card ∧ B.pentagons = (pentagonalFaces P).card := by
  let m := Nat.card (Face P 3)
  let N := (nonsimplicialFacets P).card
  let q := (quadrilateralFaces P).card
  let p := (pentagonalFaces P).card
  let c := Fintype.card (SparseSharedRowIndex P e)
  let D := Nat.card (Nonedge P)
  let r := facetPolygonSizeCount P F₀ 4
  let s := facetPolygonSizeCount P G₀ 4
  let pF := facetPolygonSizeCount P F₀ 5
  let pG := facetPolygonSizeCount P G₀ 5
  let SP := (smallSquareFacets P).card
  let BP := (smallBipyramidFacets P).card
  let T := (tetrahedralFacets P).card
  let εF := facetPolygonExcess P F₀ - (actualPolygonRelationRank P e F₀ : Int)
  let εG := facetPolygonExcess P G₀ - (actualPolygonRelationRank P e G₀ : Int)
  let epsF := εF.toNat
  let epsG := εG.toNat
  have hF₀ : facetVertexCount P F₀ = 7 := by
    have h := congrArg (fun C => C.vertices.card) hcellF
    rw [actualCell_vertex_card, mapCell_vertex_card] at h
    simpa only [cellOfBoundary, Finset.card_univ, Fintype.card_fin] using h
  have hG₀ : facetVertexCount P G₀ = 6 := by
    have h := congrArg (fun C => C.vertices.card) hcellG
    rw [actualCell_vertex_card, mapCell_vertex_card] at h
    simpa only [cellOfBoundary, Finset.card_univ, Fintype.card_fin] using h
  have hne : F₀ ≠ G₀ := by intro h; rw [h] at hF₀; omega
  have hother6 (F : Face P 3) (hF : F ≠ F₀) : facetVertexCount P F ≤ 6 := by
    by_cases hG : F = G₀
    · simpa only [hG, hG₀] using (Nat.le_refl 6)
    · exact (hother F hF hG).trans (by decide)
  have hL : (sixVertexFacets P).card = 1 := by
    have hset : sixVertexFacets P = {G₀} := by
      ext F
      simp only [sixVertexFacets, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · intro hF
        by_contra hG
        have hnF : F ≠ F₀ := by intro h; rw [h] at hF; omega
        have hb := hother F hnF hG
        omega
      · rintro rfl
        exact hG₀
    rw [hset, Finset.card_singleton]
  have hEZ : facetExcess P = ((N + 3 : Nat) : Int) := by
    have h := facet_excess_eq P F₀ hF₀ hother6
    rw [hL] at h
    dsimp only [N]
    push_cast
    omega
  have hpoly5 := polygon_card_le_five_of_one_large_facet P hP F₀ hother6
  have hg : polygonExcess P = (q : Int) + 2 * p :=
    polygonExcess_eq_quadrilaterals_add_twice_pentagons P hpoly5
  have hhF : facetPolygonSizeCount P F₀ 6 = 0 :=
    local_polygon_count_zero_of_lt P F₀ 6 (fun R => by have h := hpoly5 R.val; omega)
  have hhG : facetPolygonSizeCount P G₀ 6 = 0 :=
    local_polygon_count_zero_of_lt P G₀ 6 (fun R => by have h := hpoly5 R.val; omega)
  have hgF : facetPolygonExcess P F₀ = (r : Int) + 2 * pF :=
    local_excess_eq_quad_add_twice_pentagons P F₀ (fun R => hpoly5 R.val)
  have hpcounts := pentagon_incidence_two_large P hP F₀ G₀ hne hother
  change 2 * p = pF + pG at hpcounts
  have hprofF := polygon_counts_of_seven_cell P e.symm F₀ i f hcellF
  have hprofG := polygon_counts_of_six_cell P e.symm G₀ j g hcellG
  have hrF : (seven i).quads = r := hprofF.2.1.symm
  have hrG : (six j).quads = s := hprofG.2.1.symm
  have hpF : (seven i).pentagons = pF := hprofF.2.2.1.symm
  have hpG : (six j).pentagons = pG := hprofG.2.2.1.symm
  have hhexF : (seven i).hexagons = 0 := hprofF.2.2.2.symm.trans hhF
  have hhexG : (six j).hexagons = 0 := hprofG.2.2.2.symm.trans hhG
  have hpFle : pF ≤ 1 := by rw [← hpF]; exact pentagon_profile_bounds.1 i
  have hpGle : pG ≤ 1 := by rw [← hpG]; exact pentagon_profile_bounds.2.1 j
  have hp_le : p ≤ 1 := by omega
  have hepsF_nonneg : 0 ≤ εF := sub_nonneg.mpr (actualPolygonRelationRank_le P e F₀)
  have hepsG_nonneg : 0 ≤ εG := sub_nonneg.mpr (actualPolygonRelationRank_le P e G₀)
  have hepsFZ : (epsF : Int) = εF := Int.toNat_of_nonneg hepsF_nonneg
  have hepsGZ : (epsG : Int) = εG := Int.toNat_of_nonneg hepsG_nonneg
  have hfaces := seven_vertex_facet_has_at_least_seven_ridges P hP e hn hN F₀ hF₀
  have hepsF : epsF ≤ epsilonSeven i := by
    have h := seven_relation_excess_of_cell P hP e F₀ i f hcellF hfaces
    change εF ≤ (if i = 13 then 1 else 0) at h
    by_cases hi : i = 13 <;> simp only [epsilonSeven, hi, ite_true, ite_false] at h ⊢ <;> omega
  have hepsG : epsG ≤ epsilonSix j := by
    have h := six_relation_excess_of_cell P hP e G₀ j g hcellG
    change εG ≤ (if j = 6 then 1 else 0) at h
    by_cases hj : j = 6 <;> simp only [epsilonSix, hj, ite_true, ite_false] at h ⊢ <;> omega
  have hrowsZ := two_large_facets_shared_count P hP e F₀ G₀ hne hother
  rw [← sparseSharedRowIndex_card P e, hEZ, hg] at hrowsZ
  change (c : Int) = ((N + 3 : Nat) : Int) - ((q : Int) + 2 * p) + εF + εG at hrowsZ
  have hrows : c + q + 2 * p = N + 3 + epsF + epsG := by omega
  have heulerZ := ten_vertex_excess_identity P hP hn
  rw [hEZ, hg] at heulerZ
  change ((N + 3 : Nat) : Int) = 35 - (m : Int) - D + ((q : Int) + 2 * p) at heulerZ
  have heuler : m + (N + 3) + D = 35 + q + 2 * p := by omega
  have hweightQ := allocated_weights_le_nonedge_card P hP
  rw [allocated_weight_sum P hP F₀ hF₀ hother6 hpoly5, hEZ, hL] at hweightQ
  have hweight : (N + 3) + 4 ≤ D + p := by
    have hQ : ((N + 3 : Nat) : Rat) + 4 ≤ (D : Rat) + p := by
      norm_num only [Nat.cast_one, Int.cast_natCast] at hweightQ
      linarith
    exact_mod_cast hQ
  have hface_formula := facet_polygon_excess_face_formula P F₀
  rw [hF₀, hgF] at hface_formula
  have hadj := seven_vertex_facet_nonsimplicial_count_le_ridges_add_three P hP e hn F₀ hF₀
  have hridges := facet_ridge_count_add_one_le_facets P hP e F₀
  have hridge : 11 ≤ m + r + 2 * pF := by dsimp only [m]; omega
  have hneighbors : N + r + 2 * pF ≤ 13 := by dsimp only [N]; omega
  have hquad : SP + r + s = 2 * q :=
    (quadrilateral_incidence_two_large P hP F₀ G₀ hne (by omega) (by omega) hother).symm
  have hcountN := nonsimplicial_count_eq P F₀ hF₀ hother6
  rw [hL] at hcountN
  change N = BP + SP + 1 + 1 at hcountN
  have hnonsimp : SP + BP + 2 = N := by omega
  have hcountm := facet_count_eq_tetrahedra_add_nonsimplicial P
  change m = T + N at hcountm
  have hNm : N ≤ m := by omega
  by_cases hpzero : p = 0
  · have hpFzero : pF = 0 := by omega
    have hpGzero : pG = 0 := by omega
    have hnum := SevenFacetBudgetArithmetic.one_six_no_pentagon
      m N (N + 3) q c D r s epsF epsG (epsilonSeven i) (epsilonSix j) SP BP T
      hN hNm rfl hc (by omega) hepsF (epsilonSeven_le i) hepsG (epsilonSix_le j)
      (by omega) (by omega) (by omega) hquad hnonsimp hcountm.symm
    obtain ⟨hE13, _, hrlo, hcases, hlow, hupp, hSP, hBP, hT⟩ := hnum
    have hadmissible : OneSixAdmissible i j m q := by
      refine ⟨hpF.trans hpFzero, hhexF, hpG.trans hpGzero, hhexG, ?_⟩
      simpa only [hrF, hrG] using ⟨hrlo, hcases, hlow, hupp⟩
    obtain ⟨B, hB, hm⟩ := one_six_covered i j m q hadmissible
    obtain ⟨hBi, hBj, hBm, hBE, hBq, hBSP, hBBP, hBT, hBp⟩ := hm
    refine ⟨by rw [hEZ, hE13]; rfl, B, hB, hBi, hBj, hBm, hBE, hBq, ?_, ?_, ?_, ?_⟩
    · exact (hBSP.trans (by rw [hrF, hrG])).trans hSP.symm
    · exact (hBBP.trans (by rw [hrF, hrG])).trans hBP.symm
    · exact hBT.trans hT.symm
    · exact hBp.trans hpzero.symm
  · have hpone : p = 1 := by omega
    have hpFone : pF = 1 := by omega
    have hpGone : pG = 1 := by omega
    have hj : j = 4 := pentagon_profile_bounds.2.2 j (hpG.trans hpGone)
    have hs : s = 0 := by rw [← hrG, hj]; rfl
    have hepsGzero : epsG = 0 := by
      have hcap : epsilonSix j = 0 := by rw [hj]; rfl
      omega
    have hepsFzero : epsF = 0 := by
      have hnonempty : (Finset.univ.filter fun R : FaceBelow P F₀.val.carrier 2 =>
          Nat.card (VerticesOn P R.val.val.carrier) = 5).Nonempty := by
        apply Finset.card_pos.mp
        change 0 < pF
        omega
      obtain ⟨R, hR⟩ := hnonempty
      have hRcard := (Finset.mem_filter.mp hR).2
      have hzero := seven_excess_zero_of_large_polygon P hP e F₀ hF₀ hfaces R (by omega)
      change εF = 0 at hzero
      omega
    have hnum := SevenFacetBudgetArithmetic.one_six_with_pentagon
      m N (N + 3) q c D r SP BP T hN hNm rfl hc (by omega)
      (by omega) (by omega) (by omega) (by omega) hnonsimp hcountm.symm
    obtain ⟨hm10, hE13, _, hq2, hr1, hSP, hBP, hT⟩ := hnum
    have hadmissible : PentagonAdmissible i :=
      ⟨hpF.trans hpFone, hhexF, by rw [hrF]; exact hr1⟩
    obtain ⟨B, hB, hm⟩ := pentagon_covered i hadmissible
    obtain ⟨hBi, hBj, hBm, hBE, hBq, hBSP, hBBP, hBT, hBp⟩ := hm
    refine ⟨by rw [hEZ, hE13]; rfl, B, hB, hBi, ?_, hBm.trans hm10.symm,
      hBE, hBq.trans hq2.symm, ?_, ?_, hBT.trans hT.symm, hBp.trans hpone.symm⟩
    · simpa [hj] using hBj
    · exact (hBSP.trans (by rw [hrF])).trans hSP.symm
    · exact (hBBP.trans (by rw [hrF])).trans hBP.symm

end Papers.RationalityTen.ActualSevenMixedBudget
