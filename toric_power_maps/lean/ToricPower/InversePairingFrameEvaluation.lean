module

public import ToricPower.InversePairingFrames

/-! # Evaluation of the canonical inverse frame

The two prescribed frame sections pair to exactly one. This fixes the
normalization needed to identify the actual inverse frame's character.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MonoidalCategory MonoidalClosed Opposite

namespace ToricPower

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
  {L D : C} (eDL : D ⊗ L ≅ 𝟙_ C) (eLD : L ⊗ D ≅ 𝟙_ C)
  (frame : 𝟙_ C ≅ L)

/-- The actual original and inverse frame evaluate to the specified
unit, not merely to an unspecified invertible scalar. -/
theorem inversePairingFrame_inv_pairing :
    (frame.hom ⊗ₘ (inversePairingFrame eDL eLD frame).inv) ≫ eLD.hom =
      (λ_ (𝟙_ C)).hom := by
  have comparison := congrArg (fun f => f ≫ (internalDualUnitIso C).inv)
    (inversePairingFrame eDL eLD frame).inv_hom_id
  rw [Category.assoc, inversePairingFrame_hom_unit_inv, Category.id_comp] at comparison
  have evaluated := congrArg
    (fun f : 𝟙_ C ⟶ ((ihom (𝟙_ C)).obj (𝟙_ C)) => uncurry f) comparison
  rw [uncurry_natural_left, uncurry_pre_app, uncurry_curry] at evaluated
  change (𝟙_ C) ◁ (inversePairingFrame eDL eLD frame).inv ≫
      frame.hom ▷ D ≫ eLD.hom =
    uncurry (TauCeti.ihomUnitIso (𝟙_ C) (𝟙_ C)).inv at evaluated
  rw [TauCeti.ihomUnitIso_inv, uncurry_curry,
    TauCeti.ExactPairing.unit_evaluation] at evaluated
  rw [← tensorHom_def'_assoc] at evaluated
  exact evaluated.trans unitors_equal.symm

end ToricPower

end
