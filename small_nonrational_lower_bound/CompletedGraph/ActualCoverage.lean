module
public import GraphActualRowAssembly
public import GraphVerifiedRows

/-!
# Actual polytopes in the graph families

The finite graph certificates enter only through `GraphFiniteDispatch`.
The geometric conversion was proved separately for an arbitrary actual
polytope and an arbitrary labeling of its ten vertices. These two theorems
therefore discharge the graph branches without a catalogue-coverage premise.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section
namespace Papers.RationalityTen.CompletedGraph

open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeFacetSurplus Papers.PolytopeRelationBudget
open ChirotopeDensity
open ActualFacetTemplateAssignment SixFacetProfileRefinement ActualResidualPartition

/-- Every actual small-facet polytope in the eleven graph budget rows has a
verified terminal boundary. All graph catalogues and search certificates have been
discharged by `GraphFiniteDispatch.small_verified`. -/
theorem small_hasTerminal
    (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hnonsimple : ∀ v : P.vertices, ¬ IsSimpleVertex P v)
    (C : SmallCase P)
    (hB : SmallFacetBudget.mk (Nat.card (Face P 3)) (nonsimplicialFacets P).card
      (quadrilateralFaces P).card ∈ SmallBudgetFamilyAssembly.graphBudgets) :
    ActualLeafTargetCoverage.HasTerminal P :=
  GraphActualRowAssembly.small_hasTerminal_of_verified
    GraphFiniteDispatch.small_verified P hP hnonsimple C hB

/-- The sole exceptional six-facet budget row also yields a verified terminal
boundary, with its full actual template assignment retained. -/
theorem exceptional_six_hasTerminal
    (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hnonsimple : ∀ v : P.vertices, ¬ IsSimpleVertex P v)
    (C : SixCase P)
    (hrow : (countsOf P C.assignment.kind).toRow (actualAllSixFacetBudget P) =
      CompletedSix.exceptionalRow) : ActualLeafTargetCoverage.HasTerminal P :=
  GraphActualRowAssembly.six_hasTerminal_of_verified
    GraphFiniteDispatch.verified32 P hP hnonsimple C hrow

#print axioms small_hasTerminal
#print axioms exceptional_six_hasTerminal
end Papers.RationalityTen.CompletedGraph
