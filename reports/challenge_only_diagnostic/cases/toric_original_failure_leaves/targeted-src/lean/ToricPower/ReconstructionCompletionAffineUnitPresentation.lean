module

public import ToricPower.AffineRankOneSections

/-! # The underlying affine unit in the actual tensor evaluation

The quasicoherent affine direct image and the literal sheaf direct image
have the same underlying object. Their entire tensor-evaluation composite
is identified before any actual Cartier label or coefficient is inserted.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory MonoidalCategory

namespace ToricPower

universe u

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsAffineHom j]

/-- The original coefficient and top map give the identical whole
evaluation composite in the two affine-unit presentations. -/
theorem reconstructionAffineUnit_tensorEvaluation_presentation
    (L M J : X.Modules)
    (x : 𝟙_ X.Modules ⟶ M ⊗ (quasicoherentAffineUnitImage j).obj)
    (β : L ⊗ M ⟶ J) :
    (ρ_ L).inv ≫ L ◁ x ≫
        (α_ L M (quasicoherentAffineUnitImage j).obj).inv ≫
        β ▷ (quasicoherentAffineUnitImage j).obj =
      (ρ_ L).inv ≫ L ◁ x ≫
        (α_ L M ((Scheme.Modules.pushforward j).obj (𝟙_ U.Modules))).inv ≫
        β ▷ ((Scheme.Modules.pushforward j).obj (𝟙_ U.Modules)) :=
  rfl

end ToricPower

end
