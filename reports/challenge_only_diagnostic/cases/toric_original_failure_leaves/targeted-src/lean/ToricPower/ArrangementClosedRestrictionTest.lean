module

public import ToricPower.ArrangementClosedScalarAugmentationQuasiIso
public import ToricPower.ArrangementClosedSectionTest
public import ToricPower.ToricClosedTargetCohomology

/-! # The normalized closed-subtorus test from actual linear restriction

The source is the actual constant coefficient diagram of the closed
subtorus.  Nonzero cohomology of the original Cartier sheaf pulled back
to the genuine toric linear subvariety gives a nonzero derived map
from this source into the actual normalized Hom image.

The map-level argument uses the whole scalar affine chart augmentation,
the original complete component chains, and actual derived global
sections.  It imposes no bound on characters and retains all parallel
components of the lifted subtorus.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric
open ToricPower.IntegralArrangement
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i) [nonempty : Nonempty fan.cones]
  (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local instance closedRestrictionTestIntegral : IsIntegral fan.algebraicRealization :=
  toricSchemeIntegral fan nonempty

/-- Exact normalized closed-row detection from the literal restriction
of the original line bundle to the linear toric subvariety. -/
theorem normalizedClosedRowsTest_of_restrictionNonzero
    (σ : fan.cones) (W : LinearSubspace fan)
    (spans : Submodule.span ℝ (σ.val : Set V) = W.space)
    (b : fan.Ray → ℤ)
    (cohomology : ∃ q : ℕ, Nontrivial (Cohomology
      ((Scheme.Modules.pullback (linearToricInclusion fan W)).obj
        (invariantCartierDivisor fan nonempty regular b).sheaf) q)) :
    NormalizedClosedRowsTest fan regular basis rays b (fanConeSliceRows fan rays σ) := by
  apply normalizedClosedRowsTest_of_sectionAugmentation fan regular basis rays b
    (fanConeSliceRows fan rays σ) (closedDualTargetQuasicoherent fan W regular b)
    (arrangementClosedScalarAugmentation fan regular basis rays σ W spans b)
  obtain ⟨q,nonzero⟩ := cohomology
  exact ⟨q,(closedDualTargetCohomology_nontrivial_iff fan regular W b q).mpr nonzero⟩

end ToricPower

end
