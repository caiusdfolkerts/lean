module

public import CompletedSmall.BudgetClosure
public import CompletedSmall.ActualAssembly
public import CompletedGraph.ActualCoverage

/-!
# Complete coverage of actual small-facet polytopes

The numerical partition has two geometrically impossible rows, nineteen
rooted rows and eleven graph rows. The two finite inputs to the general
assembly are supplied here by their complete checked classifications.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace Papers.RationalityTen.CompletedSmall

open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes
open ActualResidualPartition ActualLeafTargetCoverage

/-- Every actual residual small-facet case has a complete terminal boundary. -/
theorem hasTerminal (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hnonsimple : ∀ v : P.vertices, ¬ IsSimpleVertex P v)
    (C : SmallCase P) : HasTerminal P :=
  SmallBudgetFamilyAssembly.hasTerminal_of_families
    rooted_complete CompletedGraph.small_hasTerminal P hP hnonsimple C

#print axioms hasTerminal

end Papers.RationalityTen.CompletedSmall
