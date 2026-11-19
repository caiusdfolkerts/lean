module

public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Tensor compatibility without a unit condition

Open base change needs compatibility with tensor products.  The following
small interface records exactly that compatibility and proves its stability
under composition, whiskering, and the actual mates construction.  It does
not postulate any compatibility for a particular geometric functor.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MonoidalCategory Functor.LaxMonoidal

namespace ToricPower

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E]
  {E' : Type u₄} [Category.{v₄} E'] [MonoidalCategory E']

/-- Compatibility with the actual lax tensor comparisons. -/
class TensorCompatible {F G : C ⥤ D} [F.LaxMonoidal] [G.LaxMonoidal]
    (α : F ⟶ G) : Prop where
  tensor (X Y : C) : μ F X Y ≫ α.app (X ⊗ Y) =
    (α.app X ⊗ₘ α.app Y) ≫ μ G X Y

namespace TensorCompatible

attribute [reassoc] tensor

instance (priority := 100) of_isMonoidal {F G : C ⥤ D}
    [F.LaxMonoidal] [G.LaxMonoidal] (α : F ⟶ G) [NatTrans.IsMonoidal α] :
    TensorCompatible α := ⟨NatTrans.IsMonoidal.tensor⟩

instance comp {F G H : C ⥤ D} [F.LaxMonoidal] [G.LaxMonoidal] [H.LaxMonoidal]
    (α : F ⟶ G) (β : G ⟶ H) [TensorCompatible α] [TensorCompatible β] :
    TensorCompatible (α ≫ β) where
  tensor X Y := by
    dsimp only [NatTrans.comp_app]
    rw [← Category.assoc, tensor (α := α), Category.assoc,
      tensor (α := β), ← tensorHom_comp_tensorHom_assoc]

instance whiskerRight {F G : C ⥤ D} [F.LaxMonoidal] [G.LaxMonoidal]
    (α : F ⟶ G) [TensorCompatible α] (H : D ⥤ E) [H.LaxMonoidal] :
    TensorCompatible (Functor.whiskerRight α H) where
  tensor X Y := by
    simp only [Functor.comp_obj, comp_μ, Functor.whiskerRight_app, Category.assoc]
    rw [← H.map_comp, tensor, H.map_comp, ← Category.assoc, ← μ_natural]
    simp only [Category.assoc]

instance whiskerLeft (F : C ⥤ D) [F.LaxMonoidal]
    {G H : D ⥤ E} [G.LaxMonoidal] [H.LaxMonoidal]
    (α : G ⟶ H) [TensorCompatible α] :
    TensorCompatible (Functor.whiskerLeft F α) where
  tensor X Y := by
    simp only [Functor.comp_obj, comp_μ, Functor.whiskerLeft_app, Category.assoc]
    rw [α.naturality, ← Category.assoc, tensor]
    simp only [Category.assoc]

/-- Taking the inverse mate preserves tensor compatibility when the units
and counits used in its definition have that compatibility. -/
theorem inverseMate
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ E'} {R₂ : E' ⥤ E}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {G : C ⥤ E} {H : D ⥤ E'}
    [L₁.LaxMonoidal] [R₁.LaxMonoidal] [L₂.LaxMonoidal] [R₂.LaxMonoidal]
    [G.LaxMonoidal] [H.LaxMonoidal]
    [TensorCompatible adj₁.unit] [TensorCompatible adj₂.counit]
    (β : R₁ ⋙ G ⟶ H ⋙ R₂) [TensorCompatible β] :
    TensorCompatible ((mateEquiv adj₁ adj₂).symm β) := by
  dsimp only [mateEquiv, Equiv.coe_fn_symm_mk]
  infer_instance

end TensorCompatible

end ToricPower

end
