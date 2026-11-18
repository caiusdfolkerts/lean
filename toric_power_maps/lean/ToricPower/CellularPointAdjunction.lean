module

public import ToricPower.CellularPointSupport
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Category.ModuleCat.Injective

/-!
# Evaluation and actual coinduced cellular modules

The point coinduction used by the local support model is the actual
right adjoint of evaluation. In particular it carries injective modules
to injective diagrams. These are the terms of the local finite-cover
Čech resolution, not additional acyclicity assumptions.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.Cellular

universe u
variable (R : Type u) [Ring R] {C : Type u} [Category.{u} C] (c : C)

/-- The counit evaluates the actual function on incoming incidences at
the identity incidence. -/
def pointCoinducedCounit :
    pointCoinducedFunctor R c ⋙ (evaluation C (ModuleCat.{u} R)).obj c ⟶
      𝟭 (ModuleCat.{u} R) where
  app M := ModuleCat.ofHom
    { toFun := fun x => x (𝟙 c)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  naturality {_ _} f := rfl

/-- The literal evaluation/coinduction adjunction. -/
def pointCoinducedAdjunction :
    (evaluation C (ModuleCat.{u} R)).obj c ⊣ pointCoinducedFunctor R c where
  unit := pointCoinducedUnit R c
  counit := pointCoinducedCounit R c
  left_triangle_components F := by
    ext x
    change F.map (𝟙 c) x = x
    simp only [CategoryTheory.Functor.map_id, ModuleCat.id_apply]
  right_triangle_components M := by
    apply NatTrans.ext
    funext d
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext g
    change x (g ≫ 𝟙 c) = x g
    rw [Category.comp_id]

instance pointCoinduced_injective (M : ModuleCat.{u} R) [Injective M] :
    Injective (pointCoinduced R c M) :=
  (pointCoinducedAdjunction R c).map_injective M inferInstance

end ToricPower.Cellular

end
