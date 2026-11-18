module

public import ToricPower.CartierTensorPairing

/-!
# Actual monomial maps and Cartier duality

Multiplication by a character from `O(b)` to `O(c)` induces multiplication
by the same character from `O(-c)` to `O(-b)`. The negative coefficient
sheaves are identified with the actual inverse Cartier sheaves by the
proved additivity of the invariant divisor. Rational-value computations
then identify this concrete map with the mate of the tensor adjunction.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
open TauCeti.Toric TauCeti.AlgebraicGeometry.Scheme

namespace ToricPower

universe u v
variable {N : Type u} {V : Type v} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

/-- The inverse-divisor map has exactly the original regularity
inequality, with source and target interchanged and negated. -/
theorem toricMonomialNonnegative_dual (fan : Fan i) (b c : fan.Ray → ℤ)
    (character : N →+ ℤ)
    (nonnegative : ∀ ρ, 0 ≤ c ρ - b ρ + character (fanRayPrimitiveGenerator fan ρ)) :
    ∀ ρ, 0 ≤ (-b) ρ - (-c) ρ + character (fanRayPrimitiveGenerator fan ρ) := by
  intro ρ
  have h := nonnegative ρ
  simp only [Pi.neg_apply]
  omega

/-- The concrete reverse map on the actual inverse Cartier sheaves. -/
def toricCartierMonomialDualMap (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b c : fan.Ray → ℤ) (character : N →+ ℤ)
    (nonnegative : ∀ ρ, 0 ≤ c ρ - b ρ + character (fanRayPrimitiveGenerator fan ρ)) :
    letI := toricSchemeIntegral fan nonempty
    (-(invariantCartierDivisor fan nonempty regular c)).sheaf ⟶
      (-(invariantCartierDivisor fan nonempty regular b)).sheaf := by
  letI := toricSchemeIntegral fan nonempty
  exact (eqToIso (congrArg CartierDivisor.sheaf
      (invariantCartierDivisor_neg fan nonempty regular c).symm)).hom ≫
    toricCartierMonomialMap fan nonempty regular (-c) (-b) character
      (toricMonomialNonnegative_dual fan b c character nonnegative) ≫
    (eqToIso (congrArg CartierDivisor.sheaf
      (invariantCartierDivisor_neg fan nonempty regular b))).hom

/-- The concrete reverse map multiplies actual rational sections by
the same character as the original source map. -/
theorem toricCartierMonomialDualMap_value (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b c : fan.Ray → ℤ) (character : N →+ ℤ)
    (nonnegative : ∀ ρ, 0 ≤ c ρ - b ρ + character (fanRayPrimitiveGenerator fan ρ))
    (U : fan.algebraicRealization.Opens) [Nonempty U]
    (t : letI := toricSchemeIntegral fan nonempty;
      Γ((-(invariantCartierDivisor fan nonempty regular c)).sheaf, U)) :
    letI := toricSchemeIntegral fan nonempty
    rationalFunctionsEquiv U
      (Scheme.Modules.Hom.app (-(invariantCartierDivisor fan nonempty regular b)).sheafι U
        (Scheme.Modules.Hom.app
          (toricCartierMonomialDualMap fan nonempty regular b c character nonnegative) U t)) =
      (rationalCharacterUnit fan nonempty character : fan.algebraicRealization.functionField) *
        rationalFunctionsEquiv U
          (Scheme.Modules.Hom.app (-(invariantCartierDivisor fan nonempty regular c)).sheafι U t) := by
  letI := toricSchemeIntegral fan nonempty
  simp only [toricCartierMonomialDualMap, schemeHom_comp_apply]
  rw [cartierEqToIso_value (invariantCartierDivisor_neg fan nonempty regular b),
    toricCartierMonomialMap_value,
    cartierEqToIso_value (invariantCartierDivisor_neg fan nonempty regular c).symm]

/-- The actual conjugate transformation of the exact Cartier tensor
adjunction is tensoring the explicit same-character reverse map. -/
theorem toricCartierMonomialMap_dualTwist (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b c : fan.Ray → ℤ) (character : N →+ ℤ)
    (nonnegative : ∀ ρ, 0 ≤ c ρ - b ρ + character (fanRayPrimitiveGenerator fan ρ)) :
    letI := toricSchemeIntegral fan nonempty
    cartierDualTwistMap fan.algebraicRealization
      (toricCartierMonomialMap fan nonempty regular b c character nonnegative) =
      (tensoringLeft fan.algebraicRealization.Modules).map
        (toricCartierMonomialDualMap fan nonempty regular b c character nonnegative) := by
  letI := toricSchemeIntegral fan nonempty
  exact cartierDualTwistMap_eq_of_rationalMultiplier
    (toricCartierMonomialMap fan nonempty regular b c character nonnegative)
    (toricCartierMonomialDualMap fan nonempty regular b c character nonnegative)
    (rationalCharacterUnit fan nonempty character : fan.algebraicRealization.functionField)
    (toricCartierMonomialMap_value fan nonempty regular b c character nonnegative)
    (toricCartierMonomialDualMap_value fan nonempty regular b c character nonnegative)

end ToricPower
