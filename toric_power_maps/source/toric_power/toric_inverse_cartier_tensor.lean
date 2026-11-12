module

public import ToricPower.ToricCartierMonomialDuality

/-!
# The literal coefficient sheaf of a Cartier inverse twist

The inverse tensor twist of `O(d)` by `O(b)` is the genuine invariant
Cartier sheaf `O(d-b)`. Its comparison is multiplication of actual rational
sections. Under a monomial map `O(b) → O(c)`, the contravariant twist map
becomes the same-character map `O(d-c) → O(d-b)`. This identifies actual
maps of sheaves, rather than only their cohomology groups.
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

/-- The actual divisor equality underlying the inverse tensor twist. -/
theorem invariantCartierDivisor_inverse_add (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (b d : fan.Ray → ℤ) :
    letI := toricSchemeIntegral fan nonempty;
    -invariantCartierDivisor fan nonempty regular b +
        invariantCartierDivisor fan nonempty regular d =
      invariantCartierDivisor fan nonempty regular (d - b) := by
  letI := toricSchemeIntegral fan nonempty
  rw [invariantCartierDivisor_sub]
  abel

/-- Actual rational multiplication identifies the inverse tensor twist
with the invariant Cartier sheaf of the difference coefficients. -/
def invariantInverseTensorIso (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b d : fan.Ray → ℤ) :
    letI := toricSchemeIntegral fan nonempty
    (-(invariantCartierDivisor fan nonempty regular b)).sheaf ⊗
        (invariantCartierDivisor fan nonempty regular d).sheaf ≅
      (invariantCartierDivisor fan nonempty regular (d - b)).sheaf := by
  letI := toricSchemeIntegral fan nonempty
  exact CartierDivisor.tensorSheafIso
      (-(invariantCartierDivisor fan nonempty regular b))
      (invariantCartierDivisor fan nonempty regular d) ≪≫
    eqToIso (congrArg CartierDivisor.sheaf
      (invariantCartierDivisor_inverse_add fan nonempty regular b d))

/-- The inverse-tensor comparison is actual multiplication in the
function field, with no scalar or character renormalization. -/
theorem invariantInverseTensorIso_value (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (b d : fan.Ray → ℤ) (U : fan.algebraicRealization.Opens) [Nonempty U]
    (s : letI := toricSchemeIntegral fan nonempty;
      Γ((-(invariantCartierDivisor fan nonempty regular b)).sheaf, U))
    (t : letI := toricSchemeIntegral fan nonempty;
      Γ((invariantCartierDivisor fan nonempty regular d).sheaf, U)) :
    letI := toricSchemeIntegral fan nonempty
    rationalFunctionsEquiv U
      (Scheme.Modules.Hom.app (invariantCartierDivisor fan nonempty regular (d-b)).sheafι U
        (Scheme.Modules.Hom.app (invariantInverseTensorIso fan nonempty regular b d).hom U
          (schemeTensorSection _ _ U s t))) =
      rationalFunctionsEquiv U
          (Scheme.Modules.Hom.app (-(invariantCartierDivisor fan nonempty regular b)).sheafι U s) *
        rationalFunctionsEquiv U
          (Scheme.Modules.Hom.app (invariantCartierDivisor fan nonempty regular d).sheafι U t) := by
  letI := toricSchemeIntegral fan nonempty
  unfold invariantInverseTensorIso
  rw [Iso.trans_hom, schemeHom_comp_apply,
    cartierEqToIso_value (invariantCartierDivisor_inverse_add fan nonempty regular b d)]
  exact cartierTensorSheafIso_value _ _ U s t

/-- Subtracting a source label reverses its regularity inequality. -/
theorem toricMonomialNonnegative_inverseTwist (fan : Fan i)
    (b c d : fan.Ray → ℤ) (character : N →+ ℤ)
    (nonnegative : ∀ ρ, 0 ≤ c ρ - b ρ + character (fanRayPrimitiveGenerator fan ρ)) :
    ∀ ρ, 0 ≤ (d-b) ρ - (d-c) ρ + character (fanRayPrimitiveGenerator fan ρ) := by
  intro ρ
  have h := nonnegative ρ
  simp only [Pi.sub_apply]
  omega

/-- The genuine same-character reverse map of inverse Cartier sheaves
becomes the same-character map between the literal difference sheaves. -/
@[reassoc]
theorem toricCartierMonomialDualMap_tensor (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (b c d : fan.Ray → ℤ) (character : N →+ ℤ)
    (nonnegative : ∀ ρ, 0 ≤ c ρ - b ρ + character (fanRayPrimitiveGenerator fan ρ)) :
    letI := toricSchemeIntegral fan nonempty
    (toricCartierMonomialDualMap fan nonempty regular b c character nonnegative ⊗ₘ
      𝟙 (invariantCartierDivisor fan nonempty regular d).sheaf) ≫
        (invariantInverseTensorIso fan nonempty regular b d).hom =
      (invariantInverseTensorIso fan nonempty regular c d).hom ≫
        toricCartierMonomialMap fan nonempty regular (d-c) (d-b) character
          (toricMonomialNonnegative_inverseTwist fan b c d character nonnegative) := by
  letI := toricSchemeIntegral fan nonempty
  apply cartierTensorHom_ext_nonempty (invariantCartierDivisor fan nonempty regular (d-b))
  intro U hU s t
  simp only [schemeHom_comp_apply]
  rw [schemeTensorSection_naturality, invariantInverseTensorIso_value,
    toricCartierMonomialDualMap_value, toricCartierMonomialMap_value,
    invariantInverseTensorIso_value]
  exact mul_assoc _ _ _

/-- The actual mate of the tensor adjunction, evaluated at `O(d)`, is
identified with the literal monomial map on `O(d-c) → O(d-b)`. -/
@[reassoc]
theorem toricCartierMonomialMap_inverseTwist (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (b c d : fan.Ray → ℤ) (character : N →+ ℤ)
    (nonnegative : ∀ ρ, 0 ≤ c ρ - b ρ + character (fanRayPrimitiveGenerator fan ρ)) :
    letI := toricSchemeIntegral fan nonempty
    (cartierDualTwistMap fan.algebraicRealization
      (toricCartierMonomialMap fan nonempty regular b c character nonnegative)).app
        (invariantCartierDivisor fan nonempty regular d).sheaf ≫
          (invariantInverseTensorIso fan nonempty regular b d).hom =
      (invariantInverseTensorIso fan nonempty regular c d).hom ≫
        toricCartierMonomialMap fan nonempty regular (d-c) (d-b) character
          (toricMonomialNonnegative_inverseTwist fan b c d character nonnegative) := by
  letI := toricSchemeIntegral fan nonempty
  rw [toricCartierMonomialMap_dualTwist]
  change (toricCartierMonomialDualMap fan nonempty regular b c character nonnegative ▷
      (invariantCartierDivisor fan nonempty regular d).sheaf) ≫ _ = _
  simpa only [tensorHom_id] using
    toricCartierMonomialDualMap_tensor fan nonempty regular b c d character nonnegative

end ToricPower
