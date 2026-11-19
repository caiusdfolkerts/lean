module

public import ActualSevenTwoSixBudget
public import ActualFacetRelationExcess
public import SevenFacetProfileTransport
public import FacetAdjacencyBudget

/-!
# The equality case with one seven-vertex and two six-vertex facets

The residual hypotheses imply that the total local surplus is at most two.
The seven-vertex template must therefore be the capped prism.  The argument
uses the actual relation ranks of the given realization and the complete
facet templates, rather than assuming that these ranks are type invariants.
-/

@[expose] public section

noncomputable section

namespace Papers.RationalityTen.CompletedSeven.TwoSixNarrowing

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

local instance faceFintype {d : Nat} (P : ConvexPolytope d) (k : Nat) :
    Fintype (Face P k) := Fintype.ofFinite _

/-- With polygons of size at most five, the diagonal formula expresses
surplus directly in terms of relation excess and pentagons. -/
theorem surplus_eq_excess_and_pentagons {d n : Nat}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices) (F : Face P 3)
    (hpoly : ∀ R : FaceBelow P F.val.carrier 2,
      Nat.card (VerticesOn P R.val.val.carrier) ≤ 5) :
    rankSurplus P F (actualPolygonRelationRank P e F) =
      ((facetVertexCount P F : Rat) - 4) * ((facetVertexCount P F : Rat) - 5) / 2 -
        ((facetPolygonExcess P F - (actualPolygonRelationRank P e F : Int) : Int) : Rat) -
          (facetPolygonSizeCount P F 5 : Rat) / 2 := by
  have hd := facet_diagonal_count_of_polygon_card_le_five P F hpoly
  have hdQ : (facetDiagonalCount P F : Rat) =
      2 * (facetPolygonExcess P F : Rat) + facetPolygonSizeCount P F 5 := by
    exact_mod_cast hd
  unfold rankSurplus
  push_cast
  linarith

/-- The complete residual hypotheses force canonical seven-vertex template
13.  Every other template would contribute surplus at least five halves. -/
theorem seven_template_eq_thirteen
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin 10 ≃ P.vertices)
    (hn : P.vertices.card = 10)
    (hN : 10 ≤ (nonsimplicialFacets P).card)
    (hc : 9 ≤ Fintype.card (SparseSharedRowIndex P e))
    (F : Face P 3) (i : Fin 34) (f : Fin 7 ↪ Fin 10)
    (hcell : actualCell P e.symm F = mapCell f (cellOfBoundary (N7.templates i)))
    (G : Fin 2 → Face P 3) (hG : Function.Injective G)
    (hGsix : ∀ j, facetVertexCount P (G j) = 6) : i = 13 := by
  have hF : facetVertexCount P F = 7 := by
    have h := congrArg (fun C => C.vertices.card) hcell
    rw [actualCell_vertex_card, mapCell_vertex_card] at h
    simpa only [cellOfBoundary, Finset.card_univ, Fintype.card_fin] using h
  have hres := actual_seven_and_two_six_residual_budget P hP e hn hN hc F hF G hG hGsix
  have hsum := hres.2.2.2.2
  have hsingle := actual_surplus_le_sum P hP e F
  have hother := (actual_ten_vertex_residual_unique_seven P hP e hn hN hc F hF).1
  have hpoly := polygon_card_le_five_of_one_large_facet P hP F hother
  have hid := surplus_eq_excess_and_pentagons P e F (fun R => hpoly R.val)
  rw [hF] at hid
  norm_num only [Nat.cast_ofNat] at hid
  have hprofile := polygon_counts_of_seven_cell P e.symm F i f hcell
  have hp : facetPolygonSizeCount P F 5 ≤ 1 := by
    rw [hprofile.2.2.1]
    exact pentagon_profile_bounds.1 i
  have hpQ : (facetPolygonSizeCount P F 5 : Rat) ≤ 1 := by exact_mod_cast hp
  by_contra hi
  have he := seven_relation_excess_of_cell P hP e F i f hcell
    (seven_vertex_facet_has_at_least_seven_ridges P hP e hn hN F hF)
  rw [if_neg hi] at he
  have heQ :
      ((facetPolygonExcess P F - (actualPolygonRelationRank P e F : Int) : Int) : Rat) ≤ 0 := by
    exact_mod_cast he
  linarith

end Papers.RationalityTen.CompletedSeven.TwoSixNarrowing

#print axioms Papers.RationalityTen.CompletedSeven.TwoSixNarrowing.seven_template_eq_thirteen
