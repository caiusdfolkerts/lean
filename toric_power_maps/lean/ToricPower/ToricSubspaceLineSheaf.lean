module

public import ToricPower.ToricPulledCartierSheaf
public import ToricPower.RestrictedCartierAtlas
public import ToricPower.ToricRestrictionCohomology

/-! # The literal line-sheaf restriction to a rational toric subspace

The target is the actual module-sheaf pullback along the saturated
lattice inclusion. This is a global sheaf isomorphism, independent of
any cohomology calculation or dominance assumption.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory TauCeti.Toric

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

/-- The restricted fan of a nonempty fan is nonempty. This spelling is
shared with the full chart-section comparison. -/
theorem restrictedFanConesNonempty (fan : Fan i) (nonempty : Nonempty fan.cones)
    (W : Submodule ℝ V) (rational : IsRationalSubspace i W) :
    Nonempty (restrictedFan fan W rational).cones :=
  restrictedFan_cones_nonempty fan nonempty W rational

def toricSubspaceInvariantSheafIso (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (W : Submodule ℝ V) (rational : IsRationalSubspace i W) (b : fan.Ray → ℤ) :
    letI := toricSchemeIntegral fan nonempty
    let localNonempty := restrictedFan_cones_nonempty fan nonempty W rational
    letI := toricSchemeIntegral (restrictedFan fan W rational) localNonempty
    (invariantCartierDivisor (restrictedFan fan W rational) localNonempty
      (restrictedFan_isRegular fan regular W rational)
      (restrictedFanRayCoefficients fan W rational b)).sheaf ≅
      (Scheme.Modules.pullback (restrictedFanInclusion fan W rational).algebraicMap).obj
        (invariantCartierDivisor fan nonempty regular b).sheaf := by
  letI := toricSchemeIntegral fan nonempty
  let localNonempty := restrictedFan_cones_nonempty fan nonempty W rational
  letI := toricSchemeIntegral (restrictedFan fan W rational) localNonempty
  exact eqToIso (congrArg (fun divisor => divisor.sheaf)
      (restrictedInvariantCartierAtlas_eq fan regular W rational localNonempty b).symm) ≪≫
    (invariantDivisorCharacterAtlas fan regular b).pullbackSheafIso
      localNonempty nonempty (restrictedFanInclusion fan W rational)

end ToricPower

end
