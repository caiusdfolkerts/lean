module

public import ToricPower.DivisorWeightGlobalSplitting
public import ToricPower.DivisorWeightMonomialMaps

/-!
# Naturality of the full power-residue decomposition

Multiplication by a character permutes residue classes and produces an
integral carry.  The following identities hold for the actual global
Cartier sheaf maps, rather than just their divisor classes or affine
matrix dimensions.  They retain arbitrary characters, all fan cones,
and every positive exponent.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace TauCeti.Toric
open TauCeti.AlgebraicGeometry.Scheme

namespace ToricPower

universe u v

/-- Equality into an actual Cartier direct image is checked in its
function field on nonempty opens; the empty open is treated separately. -/
theorem cartierPushforwardHom_ext_nonempty {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ X) (generic : f (genericPoint X) = genericPoint X)
    (D : CartierDivisor X) {M : X.Modules}
    {a b : M ⟶ (Scheme.Modules.pushforward f).obj D.sheaf}
    (same : ∀ (U : X.Opens) [Nonempty U] [Nonempty (f ⁻¹ᵁ U)] (s : Γ(M,U)),
      rationalFunctionsEquiv (f ⁻¹ᵁ U)
        (Scheme.Modules.Hom.app D.sheafι (f ⁻¹ᵁ U) (Scheme.Modules.Hom.app a U s)) =
      rationalFunctionsEquiv (f ⁻¹ᵁ U)
        (Scheme.Modules.Hom.app D.sheafι (f ⁻¹ᵁ U) (Scheme.Modules.Hom.app b U s))) :
    a = b := by
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  apply D.sheafι_app_injective (f ⁻¹ᵁ U)
  rcases isEmpty_or_nonempty U with empty | nonempty
  · have equality : U = ⊥ := Opens.coe_eq_empty.mp (Set.isEmpty_coe_sort.mp empty)
    have preimage : f ⁻¹ᵁ U = ⊥ := by rw [equality, Scheme.Hom.preimage_bot]
    letI := subsingleton_rationalFunctions (f ⁻¹ᵁ U) preimage
    exact Subsingleton.elim _ _
  · letI := nonempty
    letI := rationalPullback_nonempty_preimage f generic U
    exact (rationalFunctionsEquiv (f ⁻¹ᵁ U)).injective (same U s)

variable {N : Type u} {V : Type v} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

/-- The exact section formula for an actual global residue inclusion. -/
theorem toricResidueSheafMap_value (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b : fan.Ray → ℤ) (ell : ℕ) (positive : 0 < ell)
    (character : N →+ ℤ) (U : fan.algebraicRealization.Opens)
    [Nonempty U] [Nonempty ((toricPowerMap fan ell) ⁻¹ᵁ U)]
    (s : letI := toricSchemeIntegral fan nonempty;
      Γ((invariantCartierDivisor fan nonempty regular
        (toricResidueCoefficients fan b ell character)).sheaf,U)) :
    letI := toricSchemeIntegral fan nonempty
    rationalFunctionsEquiv ((toricPowerMap fan ell) ⁻¹ᵁ U)
      (Scheme.Modules.Hom.app (invariantCartierDivisor fan nonempty regular b).sheafι
        ((toricPowerMap fan ell) ⁻¹ᵁ U)
        (Scheme.Modules.Hom.app
          (toricResidueSheafMap fan nonempty regular b ell positive character) U s)) =
      (rationalCharacterUnit fan nonempty character : fan.algebraicRealization.functionField) *
        toricPowerFunctionField fan nonempty regular ell positive
          (rationalFunctionsEquiv U (Scheme.Modules.Hom.app
            (invariantCartierDivisor fan nonempty regular
              (toricResidueCoefficients fan b ell character)).sheafι U s)) := by
  letI := toricSchemeIntegral fan nonempty
  have factor := toricResidueSheafMap_rational fan nonempty regular b ell positive character
  have pointwise := ConcreteCategory.congr_hom
    (congrArg (fun h => Scheme.Modules.Hom.app h U) factor) s
  change Scheme.Modules.Hom.app (invariantCartierDivisor fan nonempty regular b).sheafι
      ((toricPowerMap fan ell) ⁻¹ᵁ U)
      (Scheme.Modules.Hom.app
        (toricResidueSheafMap fan nonempty regular b ell positive character) U s) =
    Scheme.Modules.Hom.app (cartierRationalMap (toricPowerMap fan ell)
      (toricPower_genericPoint fan nonempty regular ell positive)
      (invariantCartierDivisor fan nonempty regular
        (toricResidueCoefficients fan b ell character))
      (rationalCharacterUnit fan nonempty character : fan.algebraicRealization.functionField)) U s
    at pointwise
  rw [pointwise]
  exact cartierRationalMap_value _ _ _ _ U s

/-- The carried monomial is regular on every residue summand. -/
theorem toricResidueMonomial_nonnegative (fan : Fan i)
    (b c : fan.Ray → ℤ) (ell : ℕ) (positive : 0 < ell)
    (a u v t : N →+ ℤ) (carry : u + a = v + ell • t)
    (regularity : ∀ ρ, 0 ≤ c ρ - b ρ + a (fanRayPrimitiveGenerator fan ρ)) :
    ∀ ρ, 0 ≤ toricResidueCoefficients fan c ell v ρ -
      toricResidueCoefficients fan b ell u ρ + t (fanRayPrimitiveGenerator fan ρ) := by
  intro ρ
  have positiveInt : (0 : ℤ) < ell := by exact_mod_cast positive
  have equality := congrArg (fun m : N →+ ℤ => m (fanRayPrimitiveGenerator fan ρ)) carry
  simp only [AddMonoidHom.add_apply, AddMonoidHom.smul_apply, nsmul_eq_mul] at equality
  have bound : b ρ + u (fanRayPrimitiveGenerator fan ρ) ≤
      c ρ + v (fanRayPrimitiveGenerator fan ρ) +
        (ell : ℤ) * t (fanRayPrimitiveGenerator fan ρ) := by
    have h := regularity ρ
    omega
  have divided := Int.ediv_le_ediv positiveInt bound
  rw [Int.add_mul_ediv_left _ _ (ne_of_gt positiveInt)] at divided
  unfold toricResidueCoefficients
  omega

/-- The full residue splitting is natural under actual character maps.
The carry equation is the literal equality of lattice characters. -/
theorem toricResidueSheafMap_monomial (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b c : fan.Ray → ℤ) (ell : ℕ) (positive : 0 < ell)
    (a u v t : N →+ ℤ) (carry : u + a = v + ell • t)
    (regularity : ∀ ρ, 0 ≤ c ρ - b ρ + a (fanRayPrimitiveGenerator fan ρ)) :
    letI := toricSchemeIntegral fan nonempty
    toricResidueSheafMap fan nonempty regular b ell positive u ≫
      (Scheme.Modules.pushforward (toricPowerMap fan ell)).map
        (toricCartierMonomialMap fan nonempty regular b c a regularity) =
    toricCartierMonomialMap fan nonempty regular
      (toricResidueCoefficients fan b ell u) (toricResidueCoefficients fan c ell v) t
      (toricResidueMonomial_nonnegative fan b c ell positive a u v t carry regularity) ≫
        toricResidueSheafMap fan nonempty regular c ell positive v := by
  letI := toricSchemeIntegral fan nonempty
  apply cartierPushforwardHom_ext_nonempty (toricPowerMap fan ell)
    (toricPower_genericPoint fan nonempty regular ell positive)
    (invariantCartierDivisor fan nonempty regular c)
  intro U hU hpre sectionValue
  change rationalFunctionsEquiv ((toricPowerMap fan ell) ⁻¹ᵁ U)
      (Scheme.Modules.Hom.app (invariantCartierDivisor fan nonempty regular c).sheafι _
        (Scheme.Modules.Hom.app (toricCartierMonomialMap fan nonempty regular b c a regularity) _
          (Scheme.Modules.Hom.app
            (toricResidueSheafMap fan nonempty regular b ell positive u) U sectionValue))) =
    rationalFunctionsEquiv ((toricPowerMap fan ell) ⁻¹ᵁ U)
      (Scheme.Modules.Hom.app (invariantCartierDivisor fan nonempty regular c).sheafι _
        (Scheme.Modules.Hom.app (toricResidueSheafMap fan nonempty regular c ell positive v) U
          (Scheme.Modules.Hom.app (toricCartierMonomialMap fan nonempty regular
            (toricResidueCoefficients fan b ell u) (toricResidueCoefficients fan c ell v) t
            (toricResidueMonomial_nonnegative fan b c ell positive a u v t carry regularity))
            U sectionValue)))
  rw [toricCartierMonomialMap_value, toricResidueSheafMap_value,
    toricResidueSheafMap_value, toricCartierMonomialMap_value, map_mul]
  have power := congrArg Units.val
    (toricPowerFunctionField_character fan nonempty regular ell positive t)
  change toricPowerFunctionField fan nonempty regular ell positive
      (rationalCharacterUnit fan nonempty t : fan.algebraicRealization.functionField) =
    (rationalCharacterUnit fan nonempty (ell • t) : fan.algebraicRealization.functionField)
    at power
  rw [power]
  have coefficients := congrArg
    (fun m : N →+ ℤ => (rationalCharacterUnit fan nonempty m :
      fan.algebraicRealization.functionField)) carry
  simp only [rationalCharacterUnit_add, Units.val_mul] at coefficients
  rw [← mul_assoc, mul_comm
    (rationalCharacterUnit fan nonempty a : fan.algebraicRealization.functionField),
    coefficients]
  ring

end ToricPower

end
