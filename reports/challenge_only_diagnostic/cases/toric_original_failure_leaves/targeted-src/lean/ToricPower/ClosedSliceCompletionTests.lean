module

public import ToricPower.ArrangementClosedRestrictionTest
public import ToricPower.ArrangementNormalSliceTests
public import ToricPower.ToricFiniteLinearCohomology
public import ToricPower.LinearTestFiniteness

/-! # All normal scalar tests from the paper's literal cohomology criterion

The genuine whole-chart closed-subtorus augmentation gives the exact
normalized closed-row test. The complete normal-space reduction then
supplies every scalar slice test used by the sufficiency assembly.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory TauCeti.Toric

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  [nonempty : Nonempty fan.cones] (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local instance closedSliceTestsIntegral : IsIntegral fan.algebraicRealization :=
  toricSchemeIntegral fan nonempty

/-- Every original normal scalar slice test follows from actual
nonzero cohomology on the paper's toric linear subvarieties. -/
theorem normal_scalar_slice_tests_of_linearCohomology
    (complete : fan.IsComplete) (b : fan.Ray → ℤ)
    (cohomology : toricLineBundleLinearCohomologyCriterion fan
      (invariantCartierDivisor fan nonempty regular b).sheaf) :
    ∀ c : NormalCoveredNormalizedCell fan regular basis rays,
      ∃ m : Fin n → ℤ, NormalizedScalarSliceTest fan regular basis rays b c m := by
  apply normal_scalar_slice_tests_of_closed_rows fan regular basis rays complete b
  intro σ covered
  let W := linearSubspaceOfCompleteCover fan (Submodule.span ℝ (σ.val : Set V)) covered
  exact normalizedClosedRowsTest_of_restrictionNonzero fan regular basis rays σ W rfl b
    (cohomology W)

end ToricPower

end
