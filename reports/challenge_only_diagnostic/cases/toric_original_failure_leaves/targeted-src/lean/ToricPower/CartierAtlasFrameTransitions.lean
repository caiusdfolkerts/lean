module

public import ToricPower.SheafChartSections

/-!
# Actual local Cartier frame transitions

The local frames are compared as morphisms of module sheaves. Their
coefficients are ordinary regular units on the overlap, and the comparison
is proved inside the genuine rational-function sheaf.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace ToricPower

universe u v

variable {X : Scheme.{u}}

/-- Restrict a regular function to all opens of the slice site. -/
def overRingSection (U : X.Opens) (scalar : Γ(X, U)) :
    ((SheafOfModules.unit X.ringCatSheaf).over U).sections :=
  PresheafOfModules.sectionsMk
    (fun V => X.presheaf.map V.unop.hom.op scalar) (by
      intro V W f
      change X.presheaf.map f.unop.left.op
        (X.presheaf.map V.unop.hom.op scalar) =
          X.presheaf.map W.unop.hom.op scalar
      rw [← CategoryTheory.Functor.map_comp_apply, ← op_comp, Over.w])

/-- Multiplication by an actual regular function on a slice site. -/
def overScalarHom (U : X.Opens) (scalar : Γ(X, U)) :
    (SheafOfModules.unit X.ringCatSheaf).over U ⟶
      (SheafOfModules.unit X.ringCatSheaf).over U :=
  ((SheafOfModules.unit X.ringCatSheaf).over U).unitHomEquiv.symm
    (overRingSection U scalar)

@[simp]
theorem overScalarHom_apply (U : X.Opens) (scalar : Γ(X, U))
    (V : (Over U)ᵒᵖ) (coefficient : Γ(X, V.unop.left)) :
    (overScalarHom U scalar).val.app V coefficient =
      coefficient * X.presheaf.map V.unop.hom.op scalar := rfl

/-- A map out of the structure sheaf on an open slice is determined by
its value on one over the terminal open. -/
theorem overUnitHom_ext_top (U : X.Opens)
    {M : SheafOfModules (X.ringCatSheaf.over U)}
    {first second : (SheafOfModules.unit X.ringCatSheaf).over U ⟶ M}
    (same : first.val.app (op (Over.mk (𝟙 U))) (1 : Γ(X, U)) =
      second.val.app (op (Over.mk (𝟙 U))) (1 : Γ(X, U))) : first = second := by
  apply M.unitHomEquiv.injective
  apply PresheafOfModules.sections_ext
  intro V
  let restriction : V.unop ⟶ Over.mk (𝟙 U) := Over.homMk V.unop.hom
  have firstRestriction := (M.unitHomEquiv first).property restriction.op
  have secondRestriction := (M.unitHomEquiv second).property restriction.op
  rw [← firstRestriction, ← secondRestriction]
  exact congrArg (M.val.map restriction.op) same

namespace CartierEquationAtlas

variable [IsIntegral X] (atlas : CartierEquationAtlas.{u,v} X)

/-- The chosen frame evaluated on every smaller nonempty open. -/
theorem chartTrivialization_value_on (index : atlas.Index) (U : X.Opens)
    [Nonempty U] (included : U ≤ atlas.chart index) (coefficient : Γ(X, U)) :
    TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv U
      (Scheme.Modules.Hom.app atlas.cartierDivisor.sheafι U
        ((atlas.chartTrivialization index).hom.val.app
          (op (Over.mk (homOfLE included))) coefficient)) =
      (((atlas.equation index)⁻¹ : X.functionFieldˣ) : X.functionField) *
        X.germToFunctionField U coefficient := by
  have frame := congrArg (fun comparison => comparison.val.app
    (op (Over.mk (homOfLE included))) coefficient)
      (atlas.chartTrivialization_hom_ι index)
  change Scheme.Modules.Hom.app atlas.cartierDivisor.sheafι U
    ((atlas.chartTrivialization index).hom.val.app
      (op (Over.mk (homOfLE included))) coefficient) = _ at frame
  rw [frame]
  change TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv U
    (Scheme.Modules.Hom.app (TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsMul X
      (((atlas.equation index)⁻¹ : X.functionFieldˣ) : X.functionField)) U
        (Scheme.Modules.Hom.app (TauCeti.AlgebraicGeometry.Scheme.toRationalFunctions X)
          U coefficient)) = _
  rw [TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv_rationalFunctionsMul_app,
    TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv_toRationalFunctions_app]

/-- The actual atlas frame restricted to an arbitrary smaller open. -/
def frameOn (index : atlas.Index) (U : X.Opens) (included : U ≤ atlas.chart index) :
    (SheafOfModules.unit X.ringCatSheaf).over U ≅ atlas.cartierDivisor.sheaf.over U :=
  ((SheafOfModules.overFunctorMap X.ringCatSheaf (homOfLE included)).app
      (SheafOfModules.unit X.ringCatSheaf)).symm ≪≫
    (SheafOfModules.overMap X.ringCatSheaf (homOfLE included)).mapIso
      (atlas.chartTrivialization index) ≪≫
    ((SheafOfModules.overFunctorMap X.ringCatSheaf (homOfLE included)).app
      atlas.cartierDivisor.sheaf)

@[simp]
theorem frameOn_apply (index : atlas.Index) (U : X.Opens) (included : U ≤ atlas.chart index)
    (V : (Over U)ᵒᵖ) (coefficient : Γ(X, V.unop.left)) :
    (atlas.frameOn index U included).hom.val.app V coefficient =
      (atlas.chartTrivialization index).hom.val.app
        (op (Over.mk (V.unop.hom ≫ homOfLE included))) coefficient := rfl

/-- The ratio of two local Cartier equations is the actual transition
between their frames. -/
theorem frameOn_transition (first second : atlas.Index) (U : X.Opens) [Nonempty U]
    (firstIncluded : U ≤ atlas.chart first) (secondIncluded : U ≤ atlas.chart second)
    (unit : Γ(X, U)ˣ)
    (ratio : TauCeti.AlgebraicGeometry.Scheme.regularUnitToFunctionField X U unit *
      atlas.equation first = atlas.equation second) :
    (atlas.frameOn first U firstIncluded).hom =
      overScalarHom U (unit : Γ(X, U)) ≫ (atlas.frameOn second U secondIncluded).hom := by
  apply overUnitHom_ext_top U
  change (atlas.frameOn first U firstIncluded).hom.val.app (op (Over.mk (𝟙 U))) (1 : Γ(X, U)) =
    (atlas.frameOn second U secondIncluded).hom.val.app (op (Over.mk (𝟙 U)))
      ((overScalarHom U (unit : Γ(X, U))).val.app (op (Over.mk (𝟙 U))) (1 : Γ(X, U)))
  simp only [frameOn_apply, overScalarHom_apply]
  change (atlas.chartTrivialization first).hom.val.app
      (op (Over.mk (𝟙 U ≫ homOfLE firstIncluded))) (1 : Γ(X, U)) =
    (atlas.chartTrivialization second).hom.val.app
      (op (Over.mk (𝟙 U ≫ homOfLE secondIncluded)))
        ((1 : Γ(X, U)) * X.presheaf.map (𝟙 U).op (unit : Γ(X, U)))
  simp only [Category.id_comp, op_id, CategoryTheory.Functor.map_id,
    ConcreteCategory.id_apply, one_mul]
  apply atlas.cartierDivisor.sheafι_app_injective U
  apply (TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv U).injective
  have firstValue := atlas.chartTrivialization_value_on first U firstIncluded (1 : Γ(X, U))
  have secondValue := atlas.chartTrivialization_value_on second U secondIncluded (unit : Γ(X, U))
  have unitEquality : (atlas.equation first)⁻¹ =
      (atlas.equation second)⁻¹ *
        TauCeti.AlgebraicGeometry.Scheme.regularUnitToFunctionField X U unit := by
    rw [← ratio, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
  have equality := congrArg Units.val unitEquality
  have scalarEquality : (((atlas.equation first)⁻¹ : X.functionFieldˣ) : X.functionField) =
      (((atlas.equation second)⁻¹ : X.functionFieldˣ) : X.functionField) *
        X.germToFunctionField U (unit : Γ(X, U)) := by
    simp only [Units.val_mul,
      TauCeti.AlgebraicGeometry.Scheme.regularUnitToFunctionField_apply, Units.coe_map] at equality
    exact equality
  simp only [map_one, mul_one] at firstValue
  exact firstValue.trans (scalarEquality.trans secondValue.symm)

end CartierEquationAtlas

end ToricPower
