module
public import SevenFacetTemplateProfiles
public import SevenFacetBudgetIdentities
public import MatroidChecked.SevenBudgetCoverage

@[expose] public section

/-!
# From exact facet templates to the Appendix C.3 descriptors

The numerical table used by the final budget lookup is compared with the
complete polygon templates. Exact matching of a facet's entire boundary then
transports each polygon-size count. The profile does not replace the complete
template when constructing the geometric encoding.
-/

noncomputable section
namespace Papers.RationalityTen.SevenFacetProfileTransport

open Finset
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeFacetSurplus
open ChirotopeDensity MatroidChecked.FacetBoundaryEncoding
open ActualFacetCatalogueTransport CellFacetInvariants FiniteCycleCandidates
open SevenFacetTemplateProfiles

local instance faceFintype {d : Nat} (P : ConvexPolytope d) (k : Nat) :
    Fintype (Face P k) := Fintype.ofFinite _

namespace Budget
abbrev seven := MatroidChecked.SevenBudgetCoverage.seven
abbrev six := MatroidChecked.SevenBudgetCoverage.six
end Budget

theorem seven_fields : ∀ i : Fin 34,
    (literal i).triangles = (Budget.seven i).triangles ∧
    (literal i).quadrilaterals = (Budget.seven i).quads ∧
    (literal i).pentagons = (Budget.seven i).pentagons ∧
    (literal i).hexagons = (Budget.seven i).hexagons := by
  decide +kernel

theorem six_fields : ∀ i : Fin 7,
    cellRidgeSizeCount (cellOfBoundary (N6.templates i)) 3 = (Budget.six i).triangles ∧
    cellRidgeSizeCount (cellOfBoundary (N6.templates i)) 4 = (Budget.six i).quads ∧
    cellRidgeSizeCount (cellOfBoundary (N6.templates i)) 5 = (Budget.six i).pentagons ∧
    cellRidgeSizeCount (cellOfBoundary (N6.templates i)) 6 = (Budget.six i).hexagons := by
  decide +kernel

theorem pentagon_profile_bounds :
    (∀ i : Fin 34, (Budget.seven i).pentagons ≤ 1) ∧
    (∀ i : Fin 7, (Budget.six i).pentagons ≤ 1) ∧
    (∀ i : Fin 7, (Budget.six i).pentagons = 1 → i = 4) := by
  decide +kernel

/-- The complete decoded facet cell counts each genuine polygon once. -/
theorem actual_cell_polygon_size_count {d n : Nat} (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin n) (F : Face P 3) (k : Nat) :
    cellRidgeSizeCount (actualCell P lab F) k = facetPolygonSizeCount P F k := by
  unfold cellRidgeSizeCount
  change ((((Finset.univ : Finset (Face P 2)).filter fun R =>
    R.val.carrier ⊆ F.val.carrier).image (faceLabels P lab)).filter fun S => S.card = k).card = _
  rw [Finset.filter_image, Finset.card_image_of_injective _ (faceLabels_injective P lab),
    Finset.filter_filter]
  have hcard (R : Face P 2) : (faceLabels P lab R).card =
      Nat.card (VerticesOn P R.val.carrier) := ActualFaceTransport.labels_card P lab R
  simp_rw [hcard]
  symm
  unfold facetPolygonSizeCount
  apply Finset.card_bij (fun R _ => R.val)
  · intro R hR
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hR ⊢
    exact ⟨R.property, hR⟩
  · intro R _ S _ h
    exact Subtype.ext h
  · intro R hR
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hR
    exact ⟨⟨R, hR.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hR.2⟩, rfl⟩

theorem polygon_counts_of_seven_cell {d n : Nat} (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin n) (F : Face P 3) (i : Fin 34) (f : Fin 7 ↪ Fin n)
    (hcell : actualCell P lab F = mapCell f (cellOfBoundary (N7.templates i))) :
    facetPolygonSizeCount P F 3 = (Budget.seven i).triangles ∧
    facetPolygonSizeCount P F 4 = (Budget.seven i).quads ∧
    facetPolygonSizeCount P F 5 = (Budget.seven i).pentagons ∧
    facetPolygonSizeCount P F 6 = (Budget.seven i).hexagons := by
  have hcounts (k : Nat) : facetPolygonSizeCount P F k =
      cellRidgeSizeCount (cellOfBoundary (N7.templates i)) k := by
    rw [← actual_cell_polygon_size_count P lab F k, hcell, mapCell_ridge_size_count]
  have hp := (profile_exact i).2
  have h3 := congrArg Profile.triangles hp
  have h4 := congrArg Profile.quadrilaterals hp
  have h5 := congrArg Profile.pentagons hp
  have h6 := congrArg Profile.hexagons hp
  change cellRidgeSizeCount _ 3 = _ at h3
  change cellRidgeSizeCount _ 4 = _ at h4
  change cellRidgeSizeCount _ 5 = _ at h5
  change cellRidgeSizeCount _ 6 = _ at h6
  have ht := seven_fields i
  exact ⟨(hcounts 3).trans (h3.trans ht.1),
    (hcounts 4).trans (h4.trans ht.2.1),
    (hcounts 5).trans (h5.trans ht.2.2.1),
    (hcounts 6).trans (h6.trans ht.2.2.2)⟩

theorem polygon_counts_of_six_cell {d n : Nat} (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin n) (F : Face P 3) (i : Fin 7) (f : Fin 6 ↪ Fin n)
    (hcell : actualCell P lab F = mapCell f (cellOfBoundary (N6.templates i))) :
    facetPolygonSizeCount P F 3 = (Budget.six i).triangles ∧
    facetPolygonSizeCount P F 4 = (Budget.six i).quads ∧
    facetPolygonSizeCount P F 5 = (Budget.six i).pentagons ∧
    facetPolygonSizeCount P F 6 = (Budget.six i).hexagons := by
  have hcounts (k : Nat) : facetPolygonSizeCount P F k =
      cellRidgeSizeCount (cellOfBoundary (N6.templates i)) k := by
    rw [← actual_cell_polygon_size_count P lab F k, hcell, mapCell_ridge_size_count]
  have h := six_fields i
  exact ⟨(hcounts 3).trans h.1, (hcounts 4).trans h.2.1,
    (hcounts 5).trans h.2.2.1, (hcounts 6).trans h.2.2.2⟩

end Papers.RationalityTen.SevenFacetProfileTransport
