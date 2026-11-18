module

public import ToricPower.SheafFramePullbackNaturality

/-!
# Actual sections of a normalized unit-source adjunct

The inverse structure-sheaf comparison normalizes the pullback of a
unit-source map. Its value at one is exactly the original section of
the direct image, on every actual inverse-image open.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory MonoidalCategory

namespace ToricPower

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The entire normalized adjunct is retained in this map identity. -/
theorem normalizedUnitAdjunct_pushforward (M : X.Modules)
    (a : (𝟙_ Y.Modules) ⟶ (Scheme.Modules.pushforward f).obj M) :
    SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
      (Scheme.Modules.pushforward f).map
        ((Scheme.Modules.pullbackObjUnitIso f).inv ≫
          ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ M).symm a) = a := by
  rw [← Scheme.Modules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitIso_hom]
  have naturality := (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_right
    (Scheme.Modules.pullbackObjUnitIso f).hom
    ((Scheme.Modules.pullbackObjUnitIso f).inv ≫
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ M).symm a)
  exact naturality.symm.trans (by simp only [Iso.hom_inv_id_assoc, Equiv.apply_symm_apply])

/-- The value of the actual adjunct is the literal original section,
with no affine or finite-dimensional hypothesis. -/
theorem normalizedUnitAdjunct_section (M : X.Modules)
    (a : (𝟙_ Y.Modules) ⟶ (Scheme.Modules.pushforward f).obj M) (U : Y.Opens) :
    Scheme.Modules.Hom.app
      ((Scheme.Modules.pullbackObjUnitIso f).inv ≫
        ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ M).symm a)
      (f ⁻¹ᵁ U) (1 : Γ(X, f ⁻¹ᵁ U)) =
      Scheme.Modules.Hom.app a U (1 : Γ(Y,U)) := by
  have actual := congrArg (fun b : (𝟙_ Y.Modules) ⟶ (Scheme.Modules.pushforward f).obj M =>
      Scheme.Modules.Hom.app b U (1 : Γ(Y,U)))
    (normalizedUnitAdjunct_pushforward f M a)
  change Scheme.Modules.Hom.app
      ((Scheme.Modules.pullbackObjUnitIso f).inv ≫
        ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ M).symm a)
      (f ⁻¹ᵁ U) (f.app U (1 : Γ(Y,U))) = _ at actual
  rw [map_one] at actual
  exact actual

end ToricPower

end
