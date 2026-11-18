module

public import ToricPower.OpenBaseChangeNaturality

/-!
# The actual pullback unit under open base change

The canonical base-change mate identifies the pullback of the original
unit with the local unit followed by canonical isomorphisms. Invertibility
of the local unit therefore proves invertibility of the pulled-back unit.
The assertion concerns the original adjunction, not an isomorphic map
chosen after localizing.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory

namespace ToricPower

universe u

variable {X X' Y Y' : Scheme.{u}}
  (f : X ⟶ Y) (g : X' ⟶ Y') (j : X' ⟶ X) (k : Y' ⟶ Y)
  [IsOpenImmersion j] [IsOpenImmersion k]
  (square : j ≫ f = g ≫ k)
  (preimage : f ⁻¹ᵁ k.opensRange ≤ j.opensRange)
  (M : Y.Modules)

include j square preimage in
/-- The canonical global unit is invertible on a chart whenever the
actual unit for the base-changed morphism is invertible there. -/
theorem pullbackUnit_isIso_of_openBaseChange
    [IsIso ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
      ((Scheme.Modules.pullback k).obj M))] :
    IsIso ((Scheme.Modules.pullback k).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)) := by
  let target :=
    (pullbackSquareIso f g j k square).hom.app M ≫
      (Scheme.Modules.restrictFunctorIsoPullback j).inv.app
        ((Scheme.Modules.pullback f).obj M)
  let comparison :=
    (Scheme.Modules.restrictFunctorIsoPullback k).inv.app
        ((Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj M)) ≫
      (pushforwardRestrictionIso f g j k square preimage
        ((Scheme.Modules.pullback f).obj M)).hom
  haveI : IsIso target := by dsimp [target]; infer_instance
  haveI : IsIso comparison := by dsimp [comparison]; infer_instance
  have mate :
      (Scheme.Modules.pullback k).map
          ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫ comparison =
        (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
            ((Scheme.Modules.pullback k).obj M) ≫
          (Scheme.Modules.pushforward g).map target := by
    have h := pullback_pushforwardRestrictionMap_homEquiv f g j k square
      (𝟙 ((Scheme.Modules.pullback f).obj M))
    rw [(Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_id M] at h
    simpa only [target, comparison, pushforwardRestrictionIso,
      asIso_hom, Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.id_obj, Category.comp_id, Category.assoc] using h
  haveI : IsIso ((Scheme.Modules.pullback k).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫ comparison) := by
    rw [mate]
    infer_instance
  exact IsIso.of_isIso_comp_right _ comparison

end ToricPower
