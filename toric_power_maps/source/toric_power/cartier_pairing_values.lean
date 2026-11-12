module

public import ToricPower.CartierTensorPairing

/-!
# Actual regular values of the Cartier inverse pairing

The specified zero-divisor identification preserves the actual rational
inclusion. Consequently the inverse Cartier pairing has its literal
product as a regular section; no scalar normalization is suppressed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
open TauCeti.AlgebraicGeometry.Scheme
open TauCeti.AlgebraicGeometry.Scheme.CartierDivisor

namespace ToricPower

universe u
variable {X : Scheme.{u}} [IsIntegral X]

/-- Equality transport retains the actual rational inclusion. -/
theorem cartierEqToIso_inv_inclusion {D E : CartierDivisor X} (h : D = E) :
    (eqToIso (congrArg CartierDivisor.sheaf h)).inv ≫ D.sheafι = E.sheafι := by
  subst E
  simp

/-- The actual inverse zero-divisor frame preserves the rational
inclusion of regular functions. -/
@[reassoc]
theorem unitIsoSheafZero_inv_inclusion :
    (unitIsoSheafZero X).inv ≫ toRationalFunctions X = (0 : CartierDivisor X).sheafι := by
  unfold unitIsoSheafZero
  rw [Iso.trans_inv, Category.assoc,
    unitIsoSheafPrincipalCartierDivisor_inv_toRationalFunctions,
    Units.val_one, rationalFunctionsMul_one, Category.comp_id]
  exact cartierEqToIso_inv_inclusion (principalCartierDivisor_one X)

@[reassoc]
theorem unitIsoSheafZero_hom_inclusion :
    (unitIsoSheafZero X).hom ≫ (0 : CartierDivisor X).sheafι = toRationalFunctions X := by
  rw [← unitIsoSheafZero_inv_inclusion, ← Category.assoc,
    Iso.hom_inv_id, Category.id_comp]

/-- Evaluation of an actual inserted tensor has exactly the product
of its two rational values, as a regular function. -/
theorem cartierTensorNegIsoUnit_value (D : CartierDivisor X)
    (U : X.Opens) [Nonempty U] (s : Γ(D.sheaf,U)) (t : Γ((-D).sheaf,U)) :
    X.germToFunctionField U
      (Scheme.Modules.Hom.app (cartierTensorNegIsoUnit D).hom U
        (schemeTensorSection D.sheaf (-D).sheaf U s t)) =
      rationalFunctionsEquiv U (Scheme.Modules.Hom.app D.sheafι U s) *
        rationalFunctionsEquiv U (Scheme.Modules.Hom.app (-D).sheafι U t) := by
  have value := cartierTensorNegIsoUnit_rationalValue D U s t
  rw [← schemeHom_comp_apply, Category.assoc,
    unitIsoSheafZero_hom_inclusion] at value
  rw [schemeHom_comp_apply] at value
  exact (rationalFunctionsEquiv_toRationalFunctions_app U _).symm.trans value

/-- A product equal to one evaluates to the actual unit section. -/
theorem cartierTensorNegIsoUnit_eq_one_of_values (D : CartierDivisor X)
    (U : X.Opens) [Nonempty U] (s : Γ(D.sheaf,U)) (t : Γ((-D).sheaf,U))
    (product : rationalFunctionsEquiv U (Scheme.Modules.Hom.app D.sheafι U s) *
      rationalFunctionsEquiv U (Scheme.Modules.Hom.app (-D).sheafι U t) = 1) :
    Scheme.Modules.Hom.app (cartierTensorNegIsoUnit D).hom U
      (schemeTensorSection D.sheaf (-D).sheaf U s t) = (1 : Γ(X,U)) := by
  apply X.germToFunctionField_injective U
  rw [cartierTensorNegIsoUnit_value, product, map_one]

end ToricPower

end
