module

public import ToricPower.ElementPushdownAdjunction
public import ToricPower.ExactDerivedFunctorIso

/-!
# Base change for the complete category-of-elements direct image

Pulling a covering back along an arbitrary indexing functor retains
exactly its original fibers. The direct-image comparison is therefore
the identity on each whole coproduct, and it commutes with every
incidence and every coefficient transformation. Exactness gives the
same comparison on unrestricted derived categories.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace ToricPower.ElementPushdown

universe u v
variable {C C' : Type} [SmallCategory C] [SmallCategory C']
  (A : C' ⥤ C) (B : C ⥤ Type)
  {D : Type u} [Category.{v} D] [HasCoproducts.{0} D]

/-- The actual map between the pulled-back and original total categories. -/
def pullbackElements : (A ⋙ B).Elements ⥤ B.Elements where
  obj c := B.elementsMk (A.obj c.obj) c.val
  map f := ⟨A.map f.hom,f.map_val⟩
  map_id c := by
    apply Elements.hom_ext
    exact A.map_id c.obj
  map_comp f g := by
    apply Elements.hom_ext
    exact A.map_comp f.hom g.hom

def pullbackCoefficient : (B.Elements ⥤ D) ⥤ ((A ⋙ B).Elements ⥤ D) :=
  (whiskeringLeft (A ⋙ B).Elements B.Elements D).obj (pullbackElements A B)

def baseRestriction : (C ⥤ D) ⥤ (C' ⥤ D) :=
  (whiskeringLeft C' C D).obj A

/-- Every original sheet is retained, with the literal identity on its
coefficient object. -/
def pullbackObjectIso (E : B.Elements ⥤ D) :
    obj (A ⋙ B) (pullbackElements A B ⋙ E) ≅ A ⋙ obj B E :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro c d f
    simp only [Iso.refl_hom,Category.id_comp,Category.comp_id]
    rfl)

/-- Base change is natural in the entire coefficient diagram. -/
def pullbackIso :
    pullbackCoefficient A B (D := D) ⋙ functor (A ⋙ B) ≅
      functor B ⋙ baseRestriction A :=
  NatIso.ofComponents (pullbackObjectIso A B) (by
    intro E F α
    apply NatTrans.ext
    funext c
    change cellMap (A ⋙ B) (whiskerLeft (pullbackElements A B) α) c ≫ 𝟙 _ =
      𝟙 _ ≫ cellMap B α (A.obj c)
    rw [Category.comp_id,Category.id_comp]
    rfl)

variable [Abelian D] [AB4OfSize.{0} D]

instance pullbackCoefficient_limits :
    PreservesFiniteLimits (pullbackCoefficient A B (D := D)) := by
  unfold pullbackCoefficient
  infer_instance

instance pullbackCoefficient_colimits :
    PreservesFiniteColimits (pullbackCoefficient A B (D := D)) := by
  unfold pullbackCoefficient
  infer_instance

instance pullbackCoefficient_additive : (pullbackCoefficient A B (D := D)).Additive := by
  unfold pullbackCoefficient
  infer_instance

instance baseRestriction_limits : PreservesFiniteLimits (baseRestriction A (D := D)) := by
  unfold baseRestriction
  infer_instance

instance baseRestriction_colimits : PreservesFiniteColimits (baseRestriction A (D := D)) := by
  unfold baseRestriction
  infer_instance

instance baseRestriction_additive : (baseRestriction A (D := D)).Additive := by
  unfold baseRestriction
  infer_instance

variable [HasDerivedCategory (B.Elements ⥤ D)]
  [HasDerivedCategory ((A ⋙ B).Elements ⥤ D)]
  [HasDerivedCategory (C ⥤ D)] [HasDerivedCategory (C' ⥤ D)]

/-- The whole-fiber comparison for arbitrary unbounded complexes. -/
def derivedPullbackIso :
    (pullbackCoefficient A B (D := D)).mapDerivedCategory ⋙
        (functor (A ⋙ B) (D := D)).mapDerivedCategory ≅
      (functor B (D := D)).mapDerivedCategory ⋙
        (baseRestriction A (D := D)).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    exactDerivedFunctorIso (pullbackIso A B) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm

end ToricPower.ElementPushdown

end
