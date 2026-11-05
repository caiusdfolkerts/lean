module

public import CompletedSix.Dispatch
public import CompletedGraph.ActualCoverage

@[expose] public section

/-!
# Complete actual six-facet coverage

The 477 rooted rows and the single exceptional graph row exhaust the exact
numerical catalogue. Both branches retain the full boundary of the actual
polytope; all finite classification inputs are supplied by proved theorems.
-/

noncomputable section
set_option autoImplicit false
namespace Papers.RationalityTen.CompletedSix

open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes
open ActualResidualPartition ActualLeafTargetCoverage

/-- The independent induced-graph classification closes the unique row
excluded from the rooted searches. -/
theorem graphRowCoverage : GraphRowCoverage := by
  intro P hP hnonsimple C hrow
  apply CompletedGraph.exceptional_six_hasTerminal P hP hnonsimple C
  simpa only [graphRow, RowData.graphRow, exceptionalRow] using hrow

/-- Every actual six-facet residual case has a completely checked terminal
boundary. There is no remaining finite-coverage or graph-catalogue premise. -/
theorem hasTerminal (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hnonsimple : ∀ v : VertexType P, ¬ IsSimpleVertex P v)
    (C : SixCase P) : HasTerminal P :=
  hasTerminal_of_graphRow graphRowCoverage P hP hnonsimple C

#print axioms graphRowCoverage
#print axioms hasTerminal

end Papers.RationalityTen.CompletedSix
