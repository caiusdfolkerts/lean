module

public import Mathlib.CategoryTheory.Monad.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.EssentiallySmall

/-!
# Actual coproducts in a fully faithful right-adjoint image

The reflector applied to a coproduct of the images is an actual
coproduct in the source category. This existence result requires no
assumption that the right adjoint preserves coproducts.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe u v u' v' w
variable {C : Type u} [Category.{v} C]
  {D : Type u'} [Category.{v'} D]
  {A : C ⥤ D} {B : D ⥤ C} (adj : A ⊣ B) [B.Full] [B.Faithful]

include adj in
theorem hasCoproducts_of_fullyFaithful_rightAdjoint [HasCoproducts.{w} C] :
    HasCoproducts.{w} D := by
  letI : Reflective B := { L := A, adj := adj, toFull := inferInstance, toFaithful := inferInstance }
  intro I
  exact hasColimitsOfShape_of_reflective B

end ToricPower
end
