module

public import CompletedSeven.TwoSixNarrowing
public import Consolidated.SixActualAssembly

/-!
# The template-13 conclusion for the complete residual case record

The global vertex labels remain the labels in the row-count hypothesis.
The record's local facet labels are embedded into those global labels by
the checked actual-cell transport theorem.
-/

@[expose] public section

noncomputable section

namespace Papers.RationalityTen.CompletedSeven.TwoSixNarrowing

open Finset
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeFacetSurplus
open ChirotopeDensity MatroidChecked.FacetBoundaryEncoding
open ActualFacetCatalogueTransport

/-- The numerical residual record is strengthened using the actual geometric
row-count hypothesis already present in the residual-coverage interface. -/
theorem case_template_eq_thirteen
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin 10 ≃ P.vertices)
    (hN : 10 ≤ (nonsimplicialFacets P).card)
    (hc : 9 ≤ Fintype.card (SparseSharedRowIndex P e))
    (C : ActualResidualPartition.SevenTwoSixCase P) : C.template = 13 := by
  obtain ⟨G, hG⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin 2) (s := sixVertexFacets P) (by
      rw [Fintype.card_fin, C.six_count])
  have hGsix (j : Fin 2) : facetVertexCount P (G j) = 6 :=
    (Finset.mem_filter.mp (hG ⟨j, rfl⟩)).2
  exact seven_template_eq_thirteen P hP e C.vertices hN hc C.facet C.template _
    (actualCell_of_template P e.symm C.facet C.labels
      (FiniteCycleCandidates.N7.templates C.template) C.boundary)
    G G.injective hGsix

end Papers.RationalityTen.CompletedSeven.TwoSixNarrowing

#print axioms Papers.RationalityTen.CompletedSeven.TwoSixNarrowing.case_template_eq_thirteen
