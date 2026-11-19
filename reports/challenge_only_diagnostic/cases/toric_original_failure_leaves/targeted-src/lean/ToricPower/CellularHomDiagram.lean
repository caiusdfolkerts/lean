module

public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# The actual linear Hom diagram

This is the scheme-independent part of `CellularRHomPlus`, extracted with
its complete definitions and proof bodies so the cellular coend can be
checked before the geometric sheaf foundations. Label maps act by actual
precomposition; target maps act by actual postcomposition.

-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace ToricPower.Cellular

universe u v

section HomDiagram

variable (R : Type u) [CommRing R]
  {C : Type u} [Category.{u} C]
  {A : Type v} [Category.{u} A] [Preadditive A] [Linear R A]
  (P : Cᵒᵖ ⥤ A)

/-- The actual Hom diagram. A face-to-coface arrow acts by precomposition
with its contravariant label map. A map of targets acts by postcomposition. -/
def homDiagram : A ⥤ C ⥤ ModuleCat.{u} R where
  obj E :=
    { obj := fun c => ModuleCat.of R (P.obj (op c) ⟶ E)
      map := fun f => ModuleCat.ofHom (Linear.leftComp R E (P.map f.op))
      map_id := by
        intro c
        ext g
        simp
      map_comp := by
        intro c d e f g
        ext h
        simp [Category.assoc] }
  map f :=
    { app := fun c => ModuleCat.ofHom (Linear.rightComp R (P.obj (op c)) f)
      naturality := by
        intro c d g
        ext h
        exact Category.assoc _ _ _ }
  map_id := by
    intro E
    ext c g
    exact Category.comp_id g
  map_comp := by
    intro E F G f g
    ext c h
    exact (Category.assoc h f g).symm

@[simp]
theorem homDiagram_obj_map_apply (E : A) {c d : C} (f : c ⟶ d)
    (g : P.obj (op c) ⟶ E) :
    ((homDiagram R P).obj E).map f g = P.map f.op ≫ g := rfl

@[simp]
theorem homDiagram_map_app_apply {E F : A} (f : E ⟶ F) (c : C)
    (g : P.obj (op c) ⟶ E) :
    ((homDiagram R P).map f).app c g = g ≫ f := rfl

instance homDiagram_additive : (homDiagram R P).Additive where
  map_add {X Y f g} := by
    ext c h
    exact Preadditive.comp_add _ _ _ h f g

instance homDiagram_linear : (homDiagram R P).Linear R where
  map_smul f r := by
    ext c h
    exact Linear.comp_smul _ _ _ _ _ _

/-- Forgetting the scalar structure at one label gives the ordinary
representable Hom functor, with its usual limit-preservation theorem. -/
theorem homDiagram_evaluation_forget (c : C) :
    homDiagram R P ⋙ (evaluation C (ModuleCat R)).obj c ⋙
        forget (ModuleCat R) =
      coyoneda.obj (op (P.obj (op c))) := rfl

instance homDiagram_preservesLimits : PreservesLimits (homDiagram R P) := by
  apply preservesLimits_of_evaluation
  intro c
  let G := homDiagram R P ⋙ (evaluation C (ModuleCat R)).obj c
  letI : PreservesLimits (G ⋙ forget (ModuleCat R)) := by
    change PreservesLimits
      (homDiagram R P ⋙ (evaluation C (ModuleCat R)).obj c ⋙
        forget (ModuleCat R))
    rw [homDiagram_evaluation_forget]
    infer_instance
  exact preservesLimits_of_reflects_of_preserves G (forget (ModuleCat R))

/-- Label maps act contravariantly on the actual Hom-diagram functor. -/
def homDiagramPrecompose {P Q : Cᵒᵖ ⥤ A} (α : P ⟶ Q) :
    homDiagram R Q ⟶ homDiagram R P where
  app E :=
    { app := fun c => ModuleCat.ofHom (Linear.leftComp R E (α.app (op c)))
      naturality := by
        intro c d f
        ext h
        change α.app (op d) ≫ Q.map f.op ≫ h =
          P.map f.op ≫ α.app (op c) ≫ h
        rw [← Category.assoc, ← α.naturality f.op, Category.assoc] }
  naturality {_ _} f := by
    ext c h
    exact (Category.assoc _ _ _).symm

@[simp]
theorem homDiagramPrecompose_id :
    homDiagramPrecompose R (𝟙 P) = 𝟙 (homDiagram R P) := by
  ext E c h
  exact Category.id_comp h

@[simp]
theorem homDiagramPrecompose_comp {P Q S : Cᵒᵖ ⥤ A}
    (α : P ⟶ Q) (β : Q ⟶ S) :
    homDiagramPrecompose R (α ≫ β) =
      homDiagramPrecompose R β ≫ homDiagramPrecompose R α := by
  ext E c h
  exact Category.assoc _ _ _

end HomDiagram

end ToricPower.Cellular

end
