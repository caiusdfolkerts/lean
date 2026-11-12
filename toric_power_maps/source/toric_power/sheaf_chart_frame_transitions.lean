module

public import ToricPower.CartierAtlasFrameTransitions
public import ToricPower.SheafFramePullbackNaturality

/-!
# Transition functions on actual open charts

The conversion from frames on an open slice to frames on its chart takes
multiplication by a regular function to multiplication by that function's
ordinary section on the chart.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite
open AlgebraicGeometry.Scheme.Modules

namespace ToricPower

universe u

/-- Transport an actual scalar transition from an open image to its chart. -/
theorem cartierOverToAffineFrame_transition {A X : Scheme.{u}}
    (chart : A ⟶ X) [IsOpenImmersion chart] (M : X.Modules)
    (first second : (𝟙_ X.Modules).over chart.opensRange ≅ M.over chart.opensRange)
    (scalar : Γ(X, chart.opensRange))
    (transition : first.hom = overScalarHom chart.opensRange scalar ≫ second.hom) :
    (cartierOverToAffineFrame chart M first).hom =
      globalSectionsSmul (𝟙_ A.Modules)
        ((chart.appIso ⊤).hom
          (X.presheaf.map (eqToHom chart.image_top_eq_opensRange).op scalar)) ≫
        (cartierOverToAffineFrame chart M second).hom := by
  apply unitSheafHom_ext_top
  have firstValue := cartierOverToAffineFrame_top_sections chart M first
    (1 : Γ(X, chart.opensRange))
  have secondValue := cartierOverToAffineFrame_top_sections chart M second scalar
  simp only [map_one] at firstValue
  have frameValue := congrArg (fun mapping => mapping.val.app
    (op (Over.mk (𝟙 chart.opensRange))) (1 : Γ(X, chart.opensRange))) transition
  change first.hom.val.app (op (Over.mk (𝟙 chart.opensRange))) (1 : Γ(X, chart.opensRange)) =
    second.hom.val.app (op (Over.mk (𝟙 chart.opensRange)))
      ((overScalarHom chart.opensRange scalar).val.app
        (op (Over.mk (𝟙 chart.opensRange))) (1 : Γ(X, chart.opensRange))) at frameValue
  change first.hom.val.app (op (Over.mk (𝟙 chart.opensRange))) (1 : Γ(X, chart.opensRange)) =
    second.hom.val.app (op (Over.mk (𝟙 chart.opensRange)))
      ((1 : Γ(X, chart.opensRange)) * X.presheaf.map (𝟙 chart.opensRange).op scalar) at frameValue
  simp only [op_id, CategoryTheory.Functor.map_id,
    ConcreteCategory.id_apply, one_mul] at frameValue
  have rightValue :
      Hom.app (globalSectionsSmul (𝟙_ A.Modules)
        ((chart.appIso ⊤).hom
          (X.presheaf.map (eqToHom chart.image_top_eq_opensRange).op scalar)) ≫
          (cartierOverToAffineFrame chart M second).hom) ⊤ (1 : Γ(A, ⊤)) =
      Hom.app (cartierOverToAffineFrame chart M second).hom ⊤
        ((chart.appIso ⊤).hom
          (X.presheaf.map (eqToHom chart.image_top_eq_opensRange).op scalar)) := by
    rw [Hom.comp_app, ConcreteCategory.comp_apply, globalSectionsSmul_unit_top, mul_one]
    rfl
  exact firstValue.trans ((congrArg
    (M.presheaf.map (eqToHom chart.image_top_eq_opensRange).op) frameValue).trans
      (secondValue.symm.trans rightValue.symm))

end ToricPower
