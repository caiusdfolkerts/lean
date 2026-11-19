module

public import ToricPower.InternalDualTensorInverse
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Tensor products of actual inverse pairings

The evaluation on the product is formed by the literal middle-factor
braiding and the two specified evaluations. Its naturality therefore
retains both original morphisms, including their order.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory BraidedCategory

namespace ToricPower

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- The actual middle-factor interchange, with its specified inverse. -/
def tensorMiddleIso (L₁ L₂ D₁ D₂ : C) :
    (L₁ ⊗ L₂) ⊗ (D₁ ⊗ D₂) ≅ (L₁ ⊗ D₁) ⊗ (L₂ ⊗ D₂) where
  hom := tensorμ L₁ L₂ D₁ D₂
  inv := tensorδ L₁ L₂ D₁ D₂
  hom_inv_id := tensorμ_tensorδ L₁ L₂ D₁ D₂
  inv_hom_id := tensorδ_tensorμ L₁ L₂ D₁ D₂

/-- Product evaluation uses the genuine interchange and evaluations. -/
def tensorProductPairingIso {L₁ L₂ D₁ D₂ : C}
    (e₁ : L₁ ⊗ D₁ ≅ 𝟙_ C) (e₂ : L₂ ⊗ D₂ ≅ 𝟙_ C) :
    (L₁ ⊗ L₂) ⊗ (D₁ ⊗ D₂) ≅ 𝟙_ C :=
  tensorMiddleIso L₁ L₂ D₁ D₂ ≪≫ tensorIso e₁ e₂ ≪≫ λ_ (𝟙_ C)

@[reassoc]
theorem tensorProductPairingIso_naturality
    {L₁ L₂ D₁ D₂ L₁' L₂' D₁' D₂' : C}
    (e₁ : L₁ ⊗ D₁ ≅ 𝟙_ C) (e₂ : L₂ ⊗ D₂ ≅ 𝟙_ C)
    (e₁' : L₁' ⊗ D₁' ≅ 𝟙_ C) (e₂' : L₂' ⊗ D₂' ≅ 𝟙_ C)
    (f₁ : L₁ ⟶ L₁') (f₂ : L₂ ⟶ L₂')
    (g₁ : D₁' ⟶ D₁) (g₂ : D₂' ⟶ D₂)
    (pairing₁ : L₁ ◁ g₁ ≫ e₁.hom = f₁ ▷ D₁' ≫ e₁'.hom)
    (pairing₂ : L₂ ◁ g₂ ≫ e₂.hom = f₂ ▷ D₂' ≫ e₂'.hom) :
    (L₁ ⊗ L₂) ◁ (g₁ ⊗ₘ g₂) ≫ (tensorProductPairingIso e₁ e₂).hom =
      (f₁ ⊗ₘ f₂) ▷ (D₁' ⊗ D₂') ≫ (tensorProductPairingIso e₁' e₂').hom := by
  simp only [tensorProductPairingIso, Iso.trans_hom, tensorIso_hom,
    tensorMiddleIso, Category.assoc]
  rw [tensorμ_natural_right_assoc, tensorμ_natural_left_assoc,
    tensorHom_comp_tensorHom_assoc, pairing₁, pairing₂,
    tensorHom_comp_tensorHom_assoc]

end ToricPower

end
