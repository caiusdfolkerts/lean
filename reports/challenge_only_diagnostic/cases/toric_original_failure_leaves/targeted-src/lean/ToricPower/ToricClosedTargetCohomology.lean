module

public import ToricPower.ToricClosedScalarChartDiagrams

/-! # Nonvanishing for the genuine closed-slice target

The coefficient is the actual closed pushforward of the canonical
restricted Cartier line.  Its ordinary cohomology is identified with
the literal pullback of the original line to the linear toric subvariety.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory TauCeti.Toric
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i) [nonempty : Nonempty fan.cones]
  (regular : fan.IsRegular)

local instance closedTargetCohomologyIntegral : IsIntegral fan.algebraicRealization :=
  toricSchemeIntegral fan nonempty

theorem closedDualTargetCohomology_nontrivial_iff
    (W : LinearSubspace fan) (b : fan.Ray → ℤ) (q : ℕ) :
    Nontrivial (Cohomology (closedDualTargetQuasicoherent fan W regular b).obj q) ↔
      Nontrivial (Cohomology
        ((Scheme.Modules.pullback (linearToricInclusion fan W)).obj
          (invariantCartierDivisor fan nonempty regular b).sheaf) q) :=
  (toricLinearInvariantPushforwardCohomologyIso fan W nonempty regular b q).toLinearEquiv.toEquiv.nontrivial_congr

end ToricPower

end
