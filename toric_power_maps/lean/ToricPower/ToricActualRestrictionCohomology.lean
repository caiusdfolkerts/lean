module

public import ToricPower.ToricPulledCartierCohomology
public import ToricPower.RestrictedCartierAtlas
public import ToricPower.ToricRestrictionCohomology

/-!
# The literal subspace pullback and the finite ray-span reduction

The sheaf here is the literal pullback of the original toric line sheaf
along the actual saturated-subspace toric inclusion. Its cohomology is
compared with the invariant Cartier sheaf with the retained original ray
coefficients. The previously verified character-profile argument then
shows that total nonvanishing is unchanged upon replacing the subspace
by the span of its retained fan rays.

This is a cohomological theorem. The generation equivalence in the paper
also requires its principal categorical theorem.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 400000

open AlgebraicGeometry CategoryTheory TauCeti.Toric
open TauCeti.AlgebraicGeometry.Scheme.Modules
namespace ToricPower
variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

/-- The actual pullback cohomology, without replacing its coefficient sheaf. -/
abbrev toricSubspacePullbackCohomology (fan : Fan i) (F : fan.algebraicRealization.Modules)
    (W : Submodule ℝ V) (hW : IsRationalSubspace i W) (degree : ℕ) :=
  Cohomology ((Scheme.Modules.pullback (restrictedFanInclusion fan W hW).algebraicMap).obj F)
    degree

/-- Retaining the original ray coefficients computes the actual subspace
pullback in every cohomological degree. -/
def toricSubspaceInvariantCohomologyIso (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (W : Submodule ℝ V) (hW : IsRationalSubspace i W) (b : fan.Ray → ℤ) (degree : ℕ) :
    letI := toricSchemeIntegral fan nonempty
    AddCommGrpCat.of (invariantDivisorCohomology (restrictedFan fan W hW)
      (restrictedFan_cones_nonempty fan nonempty W hW)
      (restrictedFan_isRegular fan regular W hW)
      (restrictedFanRayCoefficients fan W hW b) degree) ≅
    AddCommGrpCat.of (toricSubspacePullbackCohomology fan
      (invariantCartierDivisor fan nonempty regular b).sheaf W hW degree) := by
  letI := toricSchemeIntegral fan nonempty
  let localNonempty := restrictedFan_cones_nonempty fan nonempty W hW
  letI := toricSchemeIntegral (restrictedFan fan W hW) localNonempty
  let atlas := invariantDivisorCharacterAtlas fan regular b
  have exactDivisor := restrictedInvariantCartierAtlas_eq fan regular W hW localNonempty b
  exact (cohomologyFunctor (restrictedFan fan W hW).algebraicRealization degree).mapIso
      (eqToIso (congrArg (fun divisor => divisor.sheaf) exactDivisor.symm)) ≪≫
    atlas.pullbackCohomologyIso localNonempty nonempty (restrictedFanInclusion fan W hW) degree

/-- Exact all-degree nonvanishing comparison for the literal subspace pullback. -/
theorem toricSubspacePullback_nonzero_iff_invariant (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (W : Submodule ℝ V) (hW : IsRationalSubspace i W) (b : fan.Ray → ℤ) :
    letI := toricSchemeIntegral fan nonempty
    (∃ degree, Nontrivial (toricSubspacePullbackCohomology fan
      (invariantCartierDivisor fan nonempty regular b).sheaf W hW degree)) ↔
    ∃ degree, Nontrivial (invariantDivisorCohomology (restrictedFan fan W hW)
      (restrictedFan_cones_nonempty fan nonempty W hW)
      (restrictedFan_isRegular fan regular W hW)
      (restrictedFanRayCoefficients fan W hW b) degree) := by
  letI := toricSchemeIntegral fan nonempty
  apply exists_congr
  intro degree
  exact (toricSubspaceInvariantCohomologyIso fan nonempty regular W hW b degree).addCommGroupIsoToAddEquiv.toEquiv.nontrivial_congr.symm

/-- The literal pullback has nonzero cohomology on a rational subspace
exactly when it has nonzero cohomology on that subspace's retained ray span. -/
theorem toricSubspacePullback_nonzero_iff_rayCore (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (W : Submodule ℝ V) (hW : IsRationalSubspace i W) (b : fan.Ray → ℤ) :
    letI := toricSchemeIntegral fan nonempty
    (∃ degree, Nontrivial (toricSubspacePullbackCohomology fan
      (invariantCartierDivisor fan nonempty regular b).sheaf W hW degree)) ↔
    ∃ degree, Nontrivial (toricSubspacePullbackCohomology fan
      (invariantCartierDivisor fan nonempty regular b).sheaf (linearRayCore fan W)
      (fanRaySpan_rational fan (fanRaysIn fan W)) degree) := by
  letI := toricSchemeIntegral fan nonempty
  exact (toricSubspacePullback_nonzero_iff_invariant fan nonempty regular W hW b).trans
    ((restrictedInvariantCohomology_nonzero_iff_rayCore fan nonempty regular W hW b).trans
      (toricSubspacePullback_nonzero_iff_invariant fan nonempty regular (linearRayCore fan W)
        (fanRaySpan_rational fan (fanRaysIn fan W)) b).symm)

end ToricPower
