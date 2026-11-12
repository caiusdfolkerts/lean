module

public import ToricPower.ArrangementNormalizedRHom

/-!
# The actual normalized right adjoint commutes with toric powers

This is the full unbounded functor identity. The isomorphism retains
the genuine pullback, all residue sheets and carry characters, the
boundary Cartier normalization, and the prescribed dimension shift.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "Q" => QCoh fan.algebraicRealization
local instance normalizedPowerComparison_derivedQCoh : HasDerivedCategory.{1} Q := HasDerivedCategory.standard _
local instance normalizedPowerComparison_derivedCells : HasDerivedCategory.{1} (IncidenceObject A ⥤ ModuleCat.{0} ℂ) :=
  HasDerivedCategory.standard _

/-- The normalized unbounded Hom diagram of a power pullback is the
actual finite-sheet direct image of the original normalized diagram. -/
def arrangementNormalizedPowerComparison (ell : ℕ) (positive : 0 < ell) :
    letI := nonempty
    letI := toricPowerMap_finite fan regular ell positive
    letI := toricPowerPullback_preservesFiniteLimits fan regular ell positive
    (quasicoherentPullback (toricPowerMap fan ell)).mapDerivedCategory ⋙
        arrangementNormalizedDerivedHom fan regular basis rays ≅
      arrangementNormalizedDerivedHom fan regular basis rays ⋙
        powerDerivedPushdown A ell positive ℂ := by
  letI := nonempty
  letI := toricPowerMap_finite fan regular ell positive
  letI := toricPowerPullback_preservesFiniteLimits fan regular ell positive
  let F := (quasicoherentPullback (toricPowerMap fan ell)).mapDerivedCategory
  let M := normalizedCartierFiniteModel fan nonempty regular basis rays
  let e := arrangementNormalizedHomFiniteModelIso fan nonempty regular basis rays
  exact Functor.isoWhiskerLeft F e ≪≫
    Functor.isoWhiskerRight (F.commShiftIso (n : ℤ)).symm M ≪≫
    Functor.isoWhiskerLeft (shiftFunctor (DerivedCategory Q) (n : ℤ))
      (normalizedCartierPowerDerivedIso fan nonempty regular basis rays ell positive).symm ≪≫
    Functor.isoWhiskerRight e.symm (powerDerivedPushdown A ell positive ℂ)

end ToricPower

end
