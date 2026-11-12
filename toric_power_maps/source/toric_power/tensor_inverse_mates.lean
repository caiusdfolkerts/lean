module

public import ToricPower.CartierTensorEquivalence
public import ToricPower.ExtAdjunctionMates

/-!
# Computing conjugate maps for inverse tensor equivalences

A map between two invertible tensor factors is conjugate to a specified
map between their inverse factors when the actual evaluation pairings
commute. The proof uses the actual counits of the tensor equivalences,
including their associators and unitors.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

namespace ToricPower

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The actual counit of the inverse tensor equivalence is evaluation
after the associator, followed by the left unitor. -/
theorem tensorEquivalenceOfInverse_counit_app
    (L M : C) (eML : M ⊗ L ≅ 𝟙_ C) (eLM : L ⊗ M ≅ 𝟙_ C) (X : C) :
    (tensorEquivalenceOfInverse L M eML eLM).toAdjunction.counit.app X =
      (α_ L M X).inv ≫ eLM.hom ▷ X ≫ (λ_ X).hom := by
  rfl

/-- Compatibility with evaluation identifies the entire conjugate
natural transformation, on every coefficient object. -/
theorem tensorEquivalenceOfInverse_conjugate
    {L₁ L₂ M₁ M₂ : C}
    (eM₁L₁ : M₁ ⊗ L₁ ≅ 𝟙_ C) (eL₁M₁ : L₁ ⊗ M₁ ≅ 𝟙_ C)
    (eM₂L₂ : M₂ ⊗ L₂ ≅ 𝟙_ C) (eL₂M₂ : L₂ ⊗ M₂ ≅ 𝟙_ C)
    (f : L₂ ⟶ L₁) (g : M₁ ⟶ M₂)
    (pairing : L₂ ◁ g ≫ eL₂M₂.hom = f ▷ M₁ ≫ eL₁M₁.hom) :
    conjugateEquiv (tensorEquivalenceOfInverse L₁ M₁ eM₁L₁ eL₁M₁).toAdjunction
      (tensorEquivalenceOfInverse L₂ M₂ eM₂L₂ eL₂M₂).toAdjunction
      ((tensoringLeft C).map f) = (tensoringLeft C).map g := by
  apply conjugateEquiv_eq_of_counit
  intro X
  change L₂ ◁ (g ▷ X) ≫ _ = f ▷ (M₁ ⊗ X) ≫ _
  rw [tensorEquivalenceOfInverse_counit_app, tensorEquivalenceOfInverse_counit_app]
  rw [associator_inv_naturality_middle_assoc,
    associator_inv_naturality_left_assoc,
    ← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc, pairing]

end ToricPower
