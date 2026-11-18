module

public import ToricPower.ToricFiniteLinearCohomology
public import ToricPower.SchemeCore

/-!
# The literal all-subspace criterion and its finite reformulation

These wrappers identify the cohomological condition used in the principal
statement with the finite ray-span and integral-pattern criterion. The
left side is the original `linearCohomologyCriterion`: actual pullback of
the actual Cartier sheaf along every rational linear inclusion, followed
by ordinary sheaf cohomology in every degree.

The invariant statement retains the given coefficients. The arbitrary
Cartier statement uses the proved invariant representative of its actual
line bundle. Neither statement asserts the generation equivalence of
Theorem 1.1; that additional theorem is needed for the generation claim
in Theorem 5.2.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 500000

open AlgebraicGeometry CategoryTheory TauCeti.Toric
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

/-- The literal Cartier sheaf in the principal statement is invertible. -/
theorem toricDivisorSheaf_invertible (fan : Fan i) (hne : fan.cones.Nonempty)
    (D : toricCartierDivisor fan hne) :
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible fan.algebraicRealization
      (toricDivisorSheaf fan hne D) := by
  letI := toricScheme_isIntegral fan hne
  exact D.isInvertible_sheaf

/-- The full cohomological criterion for the given invariant coefficients
is equivalent to the finite ray-span and exact integral-pattern tests. -/
theorem linearCohomologyCriterion_invariant_iff_finitePattern (fan : Fan i)
    (hne : fan.cones.Nonempty) (regular : fan.IsRegular) (b : fan.Ray → ℤ) :
    let nonempty : Nonempty fan.cones := ⟨⟨hne.choose, hne.choose_spec⟩⟩
    letI := toricSchemeIntegral fan nonempty
    linearCohomologyCriterion fan hne (invariantCartierDivisor fan nonempty regular b) ↔
      ∀ W ∈ rayGeneratedLinearTests fan,
        toricFiniteCohomologyPatternCriterion (restrictedFan fan W.space W.rational)
          (restrictedFanRayCoefficients fan W.space W.rational b) := by
  let nonempty : Nonempty fan.cones := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  letI := toricSchemeIntegral fan nonempty
  letI := (invariantCartierDivisor fan nonempty regular b).isInvertible_sheaf
  change toricLineBundleLinearCohomologyCriterion fan
    (invariantCartierDivisor fan nonempty regular b).sheaf ↔ _
  rw [toricLinearCohomologyCriterion_iff_rayGenerated fan nonempty regular]
  exact forall_congr' fun W => forall_congr' fun _ =>
    (toricSubspacePullback_nonzero_iff_invariant fan nonempty regular W.space W.rational b).trans
      (toricCartierCohomology_nonzero_iff_finitePattern (restrictedFan fan W.space W.rational)
        (restrictedFan_cones_nonempty fan nonempty W.space W.rational)
        (restrictedFan_isRegular fan regular W.space W.rational)
        (restrictedFanRayCoefficients fan W.space W.rational b))

/-- The same exact criterion for an arbitrary Cartier divisor. The
invariant coefficient vector is obtained from its actual line bundle by
the proved classification, with no supplied linearization hypothesis. -/
theorem linearCohomologyCriterion_cartier_iff_finitePattern (fan : Fan i)
    (hne : fan.cones.Nonempty) (regular : fan.IsRegular)
    (D : toricCartierDivisor fan hne) :
    let nonempty : Nonempty fan.cones := ⟨⟨hne.choose, hne.choose_spec⟩⟩
    letI := toricDivisorSheaf_invertible fan hne D
    linearCohomologyCriterion fan hne D ↔
      ∀ W ∈ rayGeneratedLinearTests fan,
        toricFiniteCohomologyPatternCriterion (restrictedFan fan W.space W.rational)
          (restrictedFanRayCoefficients fan W.space W.rational
            (toricLineBundleInvariantCoefficients fan nonempty regular
              (toricDivisorSheaf fan hne D))) := by
  let nonempty : Nonempty fan.cones := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  letI := toricDivisorSheaf_invertible fan hne D
  exact toricLinearCohomologyCriterion_iff_finitePattern fan nonempty regular
    (toricDivisorSheaf fan hne D)

end ToricPower
