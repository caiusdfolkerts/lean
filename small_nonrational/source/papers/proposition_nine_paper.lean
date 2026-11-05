module

public import Papers.PropositionNineHypotheses
public import PaperProjectionAlternative

@[expose] public section

/-!
# Proposition 9 with its literal geometric hypothesis and conclusion

These theorems are parameterized by complete residual target coverage,
instantiated in `Papers.SmallNonrational`. No labels, finite-universe membership,
facet-size restriction, or numerical row bound is supplied by the caller. The conclusion retains the full projection criterion
or an ordinary face-order isomorphism with an explicit Appendix B polytope.
-/

noncomputable section
set_option autoImplicit false

namespace Papers.RationalityTen.PaperResidualInterface

open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open ActualResidualTargetAssembly
open Nonrational.TerminalVerification

/-- Proposition 9 parameterized by complete residual target coverage.
`Papers.SmallNonrational` supplies this input via `CompletedResidualCoverage.complete`.
All geometric and numerical bridges are proved. -/
theorem proposition_nine_of_coverage
    (hcoverage : TenVertexResidualTargetCoverage)
    (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hn : P.vertices.card = 10) (h : RemainsAfterEarlyReductions P) :
    SatisfiesPaperProjectionCriterion P ∨ IsExplicitAppendixConfiguration P := by
  obtain ⟨j, hj, lab, hB⟩ := hasTerminal_of_coverage hcoverage P hP hn h
  exact paper_projection_or_explicit_appendix_of_target P lab hP j hj hB

/-- The same statement written directly as failure of the earlier
applicability conditions. The equivalence with the residual structure is
kernel checked, including both alternatives of Proposition 8(ii). -/
theorem proposition_nine_of_not_removed
    (hcoverage : TenVertexResidualTargetCoverage)
    (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hn : P.vertices.card = 10) (h : ¬ EarlierReductionsApply P) :
    SatisfiesPaperProjectionCriterion P ∨ IsExplicitAppendixConfiguration P :=
  proposition_nine_of_coverage hcoverage P hP hn ((remains_iff_not_removed P hn).mpr h)

#print axioms proposition_nine_of_coverage
#print axioms proposition_nine_of_not_removed

end Papers.RationalityTen.PaperResidualInterface
