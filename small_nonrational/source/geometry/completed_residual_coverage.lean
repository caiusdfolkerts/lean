module

public import CompletedSmall.ActualCoverage
public import CompletedSix.ActualCoverage
public import CompletedSeven.NarrowDispatch
public import CompletedSeven.TwoSixNarrowingCase

/-!
# Complete residual coverage

The geometric partition applies to every actual ten-vertex residual
polytope. Its row-count hypothesis is retained when the two-six-facet
branch is narrowed to the capped-prism template. All eight possible
small-facet counts are then discharged by their complete classifications.
No catalogue-completeness or finite-search premise remains in this result.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace Papers.RationalityTen.CompletedResidualCoverage

open ActualResidualTargetAssembly

/-- The complete geometric coverage input used by Theorem 2 and Proposition 9. -/
theorem complete : TenVertexResidualTargetCoverage := by
  intro P hP e hn hnonsimple hN hc
  cases ActualResidualPartition.partition P hP e hn hN hc with
  | small C =>
    exact CompletedSmall.hasTerminal P hP hnonsimple C
  | six C =>
    exact CompletedSix.hasTerminal P hP hnonsimple C
  | sevenPure C =>
    exact hasTerminal_of_classifiedEncoding P hP hnonsimple
      (CompletedSeven.pure_complete P hP C)
  | sevenMixed C =>
    exact hasTerminal_of_classifiedEncoding P hP hnonsimple
      (CompletedSeven.mixed_complete P hP C)
  | sevenTwoSix C =>
    have htemplate :=
      CompletedSeven.TwoSixNarrowing.case_template_eq_thirteen P hP e hN hc C
    exact hasTerminal_of_classifiedEncoding P hP hnonsimple
      (CompletedSeven.two_six_thirteen_complete P hP C htemplate)

#print axioms complete

end Papers.RationalityTen.CompletedResidualCoverage
