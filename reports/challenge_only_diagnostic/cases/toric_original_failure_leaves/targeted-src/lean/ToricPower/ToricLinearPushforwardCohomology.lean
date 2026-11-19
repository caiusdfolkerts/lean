module

public import ToricPower.CechMeetPushforward
public import ToricPower.LinearSubspaceChartPreimage
public import ToricPower.ToricCohomologyBound
public import ToricPower.ToricSubspaceLineSheaf

/-! # Actual cohomology of the closed toric linear inclusion

The original inclusion is a closed immersion. Its affine inverse-image
Čech cover gives a scalar-linear comparison in every ordinary degree.
For an invariant Cartier line the last isomorphism is the genuine
pullback sheaf comparison, not a replacement restriction predicate.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory TauCeti.Toric
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i) (W : LinearSubspace fan)

local instance linearPushforwardSourceNoetherian :
    IsNoetherian (restrictedFan fan W.space W.rational).algebraicRealization :=
  toricScheme_isNoetherian _
local instance linearPushforwardTargetNoetherian : IsNoetherian fan.algebraicRealization :=
  toricScheme_isNoetherian _
local instance linearPushforwardSourceSeparated :
    (restrictedFan fan W.space W.rational).algebraicRealization.IsSeparated :=
  Fan.algebraicRealization_isSeparated _
local instance linearPushforwardTargetSeparated : fan.algebraicRealization.IsSeparated :=
  fan.algebraicRealization_isSeparated
local instance linearPushforwardClosed : IsClosedImmersion (linearToricInclusion fan W) :=
  linearToricInclusion_isClosedImmersion fan W
local instance linearPushforwardOver :
    (linearToricInclusion fan W).IsOver (Spec (.of ℂ)) := by
  unfold linearToricInclusion
  infer_instance

/-- Every actual quasicoherent coefficient, in every ordinary degree. -/
def toricLinearPushforwardCohomologyIso
    (M : (restrictedFan fan W.space W.rational).algebraicRealization.Modules)
    [M.IsQuasicoherent] (q : ℕ) :
    ModuleCat.of ℂ (Cohomology ((Scheme.Modules.pushforward (linearToricInclusion fan W)).obj M) q) ≅
      ModuleCat.of ℂ (Cohomology M q) :=
  FiniteCech.affinePushforwardCohomologyIso ℂ (linearToricInclusion fan W)
    (toricMeetChartOpenFunctor fan) (toricMeetChartOpen_tupleMeet fan)
    (toricMeetChartOpen_covers fan)
    (fun c => isAffineOpen_opensRange (fan.affineToricChartι (toricMeetChartEquiv fan c))) M q

/-- For a Cartier coefficient, the target is its literal pullback
along the original toric linear inclusion. -/
def toricLinearInvariantPushforwardCohomologyIso
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (b : fan.Ray → ℤ) (q : ℕ) :
    letI := toricSchemeIntegral fan nonempty
    let Y := restrictedFan fan W.space W.rational
    let hY := restrictedFanConesNonempty fan nonempty W.space W.rational
    letI := toricSchemeIntegral Y hY
    let L := (invariantCartierDivisor Y hY
      (restrictedFan_isRegular fan regular W.space W.rational)
      (restrictedFanRayCoefficients fan W.space W.rational b)).sheaf
    ModuleCat.of ℂ (Cohomology
      ((Scheme.Modules.pushforward (linearToricInclusion fan W)).obj L) q) ≅
    ModuleCat.of ℂ (Cohomology
      ((Scheme.Modules.pullback (linearToricInclusion fan W)).obj
        (invariantCartierDivisor fan nonempty regular b).sheaf) q) := by
  letI := toricSchemeIntegral fan nonempty
  let Y := restrictedFan fan W.space W.rational
  let hY := restrictedFanConesNonempty fan nonempty W.space W.rational
  letI := toricSchemeIntegral Y hY
  let D := invariantCartierDivisor Y hY
    (restrictedFan_isRegular fan regular W.space W.rational)
    (restrictedFanRayCoefficients fan W.space W.rational b)
  letI : D.sheaf.IsQuasicoherent := by
    letI := D.isInvertible_sheaf
    infer_instance
  exact toricLinearPushforwardCohomologyIso fan W D.sheaf q ≪≫
    (cohomologyBaseFunctor ℂ Y.algebraicRealization q).mapIso
      (toricSubspaceInvariantSheafIso fan nonempty regular W.space W.rational b)

end ToricPower

end
