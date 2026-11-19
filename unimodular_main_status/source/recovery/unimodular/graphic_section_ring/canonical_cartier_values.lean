module

public import Recovery.Unimodular.GraphicSectionRing.CanonicalTensorPowers
public import Recovery.Unimodular.GraphicSectionRing.CartierFrameExt

/-!
# Rational values of canonical pure powers

The comparison with Cartier powers is computed on actual ordinary local
pure tensors, including the degree-zero unit. Local Cartier frames then
supply genuine generators of every tensor power.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

universe u
namespace Unimodular.GraphicSectionRing.CanonicalPowers

open AlgebraicGeometry CategoryTheory Opposite
open PaperVerification.ToricSchemes
open scoped TensorProduct

variable {X : Scheme.{u}} [IsIntegral X]

/-- Degree zero sends the ordinary structure-sheaf unit to the rational unit. -/
theorem cocyclePowerIso_zero_value (C : RationalCartierCocycle X)
    (U : X.Opens) [Nonempty U] :
    (C.pow 0).toCartierData.sectionValue U
      ((C.tensorSheafPowerIso 0).hom.app U (1 : Γ(X, U))) = 1 := by
  let P := RationalCartierCocycle.principal (X := X) 1
  change rationalValue X U ((P.localCoordinates PUnit.unit U le_top).symm 1).val = 1
  have h := P.localCoordinates_value PUnit.unit U le_top
    ((P.localCoordinates PUnit.unit U le_top).symm 1)
  rw [LinearEquiv.apply_symm_apply, map_one] at h
  change (1 : X.functionField) =
    rationalValue X U ((P.localCoordinates PUnit.unit U le_top).symm 1).val / 1 at h
  simpa only [div_one] using h.symm

/-- The recursive actual tensor-power comparison takes a pure tensor power
to the same power of the original rational value. -/
theorem cocyclePowerIso_purePower_value (C : RationalCartierCocycle X)
    (U : X.Opens) [Nonempty U] (s : Γ(C.sheaf, U)) (n : ℕ) :
    (C.pow n).toCartierData.sectionValue U
      ((C.tensorSheafPowerIso n).hom.app U (purePower C.sheaf U s n)) =
      (C.toCartierData.sectionValue U s) ^ n := by
  induction n with
  | zero =>
      rw [pow_zero]
      exact cocyclePowerIso_zero_value C U
  | succ n ih =>
      change rationalValue X U
        (((C.pow n).tensorSheafMulIso C).hom.app U
          ((tensorSheafIso (C.tensorSheafPowerIso n) (Iso.refl C.sheaf)).hom.app U
            ((tensorSheafUnit (tensorSheafPower C.sheaf n) C.sheaf).app (op U)
              (purePower C.sheaf U s n ⊗ₜ[Γ(X, U)] s)))).val = _
      rw [tensorSheafIso_pure_sections, RationalCartierCocycle.tensorSheafMulIso_pure_sections]
      change ((C.pow n).mul C).toCartierData.sectionValue U
        ((C.pow n).sectionProduct C U
          ((C.tensorSheafPowerIso n).hom.app U (purePower C.sheaf U s n)) s) = _
      rw [RationalCartierCocycle.sectionProduct_value, ih, pow_succ]

/-- Recovery of an arbitrary fractional Cartier presentation preserves
actual section values. -/
theorem presentationIso_value (D : CartierData X) (U : X.Opens) [Nonempty U]
    (s : Γ(D.sheaf, U)) :
    D.localCocycle.toCartierData.sectionValue U (D.presentationIso.hom.app U s) =
      D.sectionValue U s := rfl

/-- Pure-power values for the original sheaf of an arbitrary Cartier presentation. -/
theorem cartierPowerIso_purePower_value (D : CartierData X)
    (U : X.Opens) [Nonempty U] (s : Γ(D.sheaf, U)) (n : ℕ) :
    (D.localCocycle.pow n).toCartierData.sectionValue U
      ((D.tensorSheafNsmulIso n).hom.app U (purePower D.sheaf U s n)) =
      (D.sectionValue U s) ^ n := by
  change (D.localCocycle.pow n).toCartierData.sectionValue U
    ((D.localCocycle.tensorSheafPowerIso n).hom.app U
      ((tensorSheafPowerIso D.presentationIso n).hom.app U (purePower D.sheaf U s n))) = _
  rw [tensorSheafPowerIso_purePower, cocyclePowerIso_purePower_value, presentationIso_value]

/-- The local frame in the original sheaf obtained from the actual local
Cartier coordinate one. -/
def presentationFrame (D : CartierData X) (a : D.localCocycle.index)
    (V : X.Opens) (hVa : V ≤ D.localCocycle.openSet a) : Γ(D.sheaf, V) :=
  (sectionsIso D.presentationIso V).symm
    ((D.localCocycle.localCoordinates a V hVa).symm 1)

/-- The local frame has exactly the original Cartier generator as its value. -/
theorem presentationFrame_value (D : CartierData X) (a : D.localCocycle.index)
    (V : X.Opens) [Nonempty V] (hVa : V ≤ D.localCocycle.openSet a) :
    D.sectionValue V (presentationFrame D a V hVa) =
      (D.localCocycle.generator a : X.functionField) := by
  rw [← presentationIso_value]
  change D.localCocycle.toCartierData.sectionValue V
    ((sectionsIso D.presentationIso V)
      ((sectionsIso D.presentationIso V).symm
        ((D.localCocycle.localCoordinates a V hVa).symm 1))) = _
  rw [LinearEquiv.apply_symm_apply]
  have h := D.localCocycle.localCoordinates_value a V hVa
    ((D.localCocycle.localCoordinates a V hVa).symm 1)
  rw [LinearEquiv.apply_symm_apply, map_one] at h
  apply (div_left_inj' (Units.ne_zero (D.localCocycle.generator a))).mp
  rw [div_self (Units.ne_zero _)]
  exact h.symm

/-- The genuine source isomorphism to the product Cartier power. -/
def sourceCartierIso (D : CartierData X) (i j : ℕ) :
    tensorSheaf (tensorSheafPower D.sheaf i) (tensorSheafPower D.sheaf j) ≅
      (D.localCocycle.pow (i + j)).sheaf :=
  tensorSheafIso (D.tensorSheafNsmulIso i) (D.tensorSheafNsmulIso j) ≪≫
    ActualSections.powerTensorSheafIso D.localCocycle i j

/-- The source comparison multiplies the values of actual pure powers. -/
theorem sourceCartierIso_purePower_value (D : CartierData X) (i j : ℕ)
    (U : X.Opens) [Nonempty U] (s : Γ(D.sheaf, U)) :
    (D.localCocycle.pow (i + j)).toCartierData.sectionValue U
      ((sourceCartierIso D i j).hom.app U
        (pure (tensorSheafPower D.sheaf i) (tensorSheafPower D.sheaf j) U
          (purePower D.sheaf U s i) (purePower D.sheaf U s j))) =
      (D.sectionValue U s) ^ (i + j) := by
  change (D.localCocycle.pow (i + j)).toCartierData.sectionValue U
    ((ActualSections.powerTensorSheafIso D.localCocycle i j).hom.app U
      ((tensorSheafIso (D.tensorSheafNsmulIso i) (D.tensorSheafNsmulIso j)).hom.app U
        ((tensorSheafUnit _ _).app (op U)
          (purePower D.sheaf U s i ⊗ₜ[Γ(X, U)] purePower D.sheaf U s j)))) = _
  rw [tensorSheafIso_pure_sections]
  erw [ActualSections.powerTensorSheafIso_pure_value D.localCocycle i j U]
  rw [cartierPowerIso_purePower_value, cartierPowerIso_purePower_value, pow_add]

#print axioms cocyclePowerIso_zero_value
#print axioms cocyclePowerIso_purePower_value
#print axioms cartierPowerIso_purePower_value
#print axioms presentationFrame_value
#print axioms sourceCartierIso_purePower_value

end Unimodular.GraphicSectionRing.CanonicalPowers

#check Unimodular.GraphicSectionRing.CanonicalPowers.sourceCartierIso_purePower_value
