module

public import ToricPower.CechToricCohomology
public import ToricPower.RestrictedFanWeightComplex
public import ToricPower.RestrictedFanRegular

/-!
# Cohomology on a rational subspace and its ray span

The objects compared here are the actual invariant Cartier line sheaves on
the two literal restricted fans, with the transported original ray
coefficients. A separate pullback isomorphism is still needed to identify
them with the restrictions used in the principal categorical criterion.

Reconstructed development source: awaits ordinary pinned Lean compilation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory
open TauCeti.Toric
open scoped Classical

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

theorem restrictedFan_cones_nonempty (fan : Fan i) (nonempty : Nonempty fan.cones)
    (W : Submodule ℝ V) (hW : IsRationalSubspace i W) :
    Nonempty (restrictedFan fan W hW).cones := by
  obtain ⟨cone⟩ := nonempty
  obtain ⟨restrictedCone, present⟩ :=
    restrictedFan_nonempty fan ⟨cone.val, cone.property⟩ W hW
  exact ⟨⟨restrictedCone, present⟩⟩

abbrev invariantDivisorCohomology (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b : fan.Ray → ℤ) (degree : ℕ) :=
  letI := toricSchemeIntegral fan nonempty
  TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology
    (invariantCartierDivisor fan nonempty regular b).sheaf degree

theorem restrictedInvariantCohomology_nonzero_iff_rayCore (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (W : Submodule ℝ V) (hW : IsRationalSubspace i W) (b : fan.Ray → ℤ) :
    (∃ degree : ℕ, Nontrivial
      (invariantDivisorCohomology (restrictedFan fan W hW)
        (restrictedFan_cones_nonempty fan nonempty W hW)
        (restrictedFan_isRegular fan regular W hW)
        (restrictedFanRayCoefficients fan W hW b) degree)) ↔
    (∃ degree : ℕ, Nontrivial
      (invariantDivisorCohomology (rayCoreFan fan W)
        (restrictedFan_cones_nonempty fan nonempty (linearRayCore fan W)
          (fanRaySpan_rational fan (fanRaysIn fan W)))
        (restrictedFan_isRegular fan regular (linearRayCore fan W)
          (fanRaySpan_rational fan (fanRaysIn fan W)))
        (restrictedFanRayCoefficients fan (linearRayCore fan W)
          (fanRaySpan_rational fan (fanRaysIn fan W)) b) degree)) := by
  have larger := toricCartierCohomologyWeight_nonzero_iff
    (restrictedFan fan W hW) (restrictedFan_cones_nonempty fan nonempty W hW)
    (restrictedFan_isRegular fan regular W hW)
    (linearRayCoreFiniteCharts fan W hW)
    (linearRayCoreFiniteCharts_surjective fan W hW)
    (restrictedFanRayCoefficients fan W hW b)
  have smaller := toricCartierCohomologyWeight_nonzero_iff
    (rayCoreFan fan W)
    (restrictedFan_cones_nonempty fan nonempty (linearRayCore fan W)
      (fanRaySpan_rational fan (fanRaysIn fan W)))
    (restrictedFan_isRegular fan regular (linearRayCore fan W)
      (fanRaySpan_rational fan (fanRaysIn fan W)))
    (rayCoreFanFiniteCharts fan W hW)
    (rayCoreFanFiniteCharts_surjective fan W hW)
    (restrictedFanRayCoefficients fan (linearRayCore fan W)
      (fanRaySpan_rational fan (fanRaysIn fan W)) b)
  exact larger.trans
    ((restrictedWeightHomology_nonzero_iff_rayCore ℂ fan W hW b).trans smaller.symm)

end ToricPower
