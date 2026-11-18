module

public import ToricPower.ElementProductPushdown

/-!
# Exact product direct image is right adjoint to covering restriction

This is the adjunction used when the compact lifted test is the target
of a derived Hom. Its unit is the diagonal into all sheets and its
counit is the projection to the actual sheet. Exactness of products in
module categories makes the adjunction valid without degree bounds.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace ToricPower.ElementProduct

universe u v

variable {C : Type} [SmallCategory C] (B : C ⥤ Type)
  (bijective : ∀ {c d : C} (f : c ⟶ d), Function.Bijective (B.map f))
  {D : Type u} [Category.{v} D] [HasProducts.{0} D] [HasCoproducts.{0} D]

local notation "R" => ElementPushdown.restriction B (D := D)

def unitCell (F : C ⥤ D) (c : C) : F.obj c ⟶ cell B ((R).obj F) c :=
  Pi.lift (fun _ : B.obj c => 𝟙 (F.obj c))

@[reassoc]
theorem unitCell_projection (F : C ⥤ D) (c : C) (r : B.obj c) :
    unitCell B F c ≫ projection B ((R).obj F) c r = 𝟙 (F.obj c) :=
  Pi.lift_comp_π _ _

def unit : 𝟭 (C ⥤ D) ⟶ R ⋙ functor B bijective where
  app F :=
    { app := unitCell B F
      naturality {c d} f := by
        apply Pi.hom_ext
        intro t
        change (F.map f ≫ unitCell B F d) ≫ projection B ((R).obj F) d t =
          (unitCell B F c ≫ map B bijective ((R).obj F) f) ≫
            projection B ((R).obj F) d t
        rw [Category.assoc,unitCell_projection,Category.comp_id,
          Category.assoc,map_projection,← Category.assoc,unitCell_projection,
          Category.id_comp]
        rfl }
  naturality {F G} α := by
    apply NatTrans.ext
    funext c
    apply Pi.hom_ext
    intro r
    change (α.app c ≫ unitCell B G c) ≫ projection B ((R).obj G) c r =
      (unitCell B F c ≫ cellMap B ((R).map α) c) ≫ projection B ((R).obj G) c r
    rw [Category.assoc,unitCell_projection,Category.comp_id,
      Category.assoc,cellMap_projection,← Category.assoc,unitCell_projection,
      Category.id_comp]
    rfl

def counit : functor B bijective ⋙ R ⟶ 𝟭 (B.Elements ⥤ D) where
  app E :=
    { app c := projection B E c.obj c.val
      naturality {_ _} f := map_projection_lifted B bijective E f }
  naturality {_ _} α := by
    apply NatTrans.ext
    funext c
    exact cellMap_projection B α c.obj c.val

/-- The product over the whole fiber is the genuine right adjoint. -/
def adjunction : R ⊣ functor B bijective where
  unit := unit B bijective
  counit := counit B bijective
  left_triangle_components F := by
    apply NatTrans.ext
    funext c
    change unitCell B F c.obj ≫ projection B ((R).obj F) c.obj c.val = 𝟙 _
    exact unitCell_projection B F c.obj c.val
  right_triangle_components E := by
    apply NatTrans.ext
    funext c
    apply Pi.hom_ext
    intro r
    change (unitCell B ((functor B bijective).obj E) c ≫
        cellMap B ((counit B bijective).app E) c) ≫ projection B E c r =
      𝟙 (cell B E c) ≫ projection B E c r
    erw [Category.assoc,cellMap_projection,← Category.assoc,unitCell_projection]
    simp only [Category.id_comp]
    rfl

/-- Evaluation of the product direct image is the genuine fiber limit. -/
def fiberLimitIso (E : B.Elements ⥤ D) (c : C) :
    cell B E c ≅ limit
      (Discrete.functor (fun r : B.obj c => B.elementsMk c r) ⋙ E) :=
  HasLimit.isoOfNatIso
    (show Discrete.functor (fun r : B.obj c => E.obj (B.elementsMk c r)) ≅
      Discrete.functor (fun r : B.obj c => B.elementsMk c r) ⋙ E from
      Discrete.natIso (fun _ => Iso.refl _))

@[reassoc]
theorem fiberLimitIso_projection (E : B.Elements ⥤ D) (c : C) (r : B.obj c) :
    (fiberLimitIso B E c).hom ≫
        limit.π (Discrete.functor (fun t : B.obj c => B.elementsMk c t) ⋙ E)
          (Discrete.mk r) = projection B E c r := by
  dsimp only [fiberLimitIso,projection,Pi.π]
  rw [HasLimit.isoOfNatIso_hom_π]
  simp

def evaluationIso (c : C) :
    functor B bijective (D := D) ⋙ (evaluation C D).obj c ≅
      (whiskeringLeft (Discrete (B.obj c)) B.Elements D).obj
          (Discrete.functor (fun r => B.elementsMk c r)) ⋙ lim :=
  NatIso.ofComponents (fun E => fiberLimitIso B E c) (by
    intro E F α
    apply limit.hom_ext
    intro r
    cases r with
    | mk r =>
      change (cellMap B α c ≫ (fiberLimitIso B F c).hom) ≫
          limit.π (Discrete.functor (fun t : B.obj c => B.elementsMk c t) ⋙ F) ⟨r⟩ =
      ((fiberLimitIso B E c).hom ≫ limMap
        (whiskerLeft (Discrete.functor (fun t : B.obj c => B.elementsMk c t)) α)) ≫
          limit.π (Discrete.functor (fun t : B.obj c => B.elementsMk c t) ⋙ F) ⟨r⟩
      rw [Category.assoc,fiberLimitIso_projection,cellMap_projection,
        Category.assoc,limMap_π,← Category.assoc,fiberLimitIso_projection]
      rfl)

variable [Abelian D] [AB4OfSize.{0} D] [AB4StarOfSize.{0} D]

instance preservesFiniteLimits : PreservesFiniteLimits (functor B bijective (D := D)) := by
  letI := (adjunction B bijective (D := D)).isRightAdjoint
  infer_instance

instance preservesFiniteColimits : PreservesFiniteColimits (functor B bijective (D := D)) :=
  preservesFiniteColimits_of_evaluation _ (fun c =>
    preservesFiniteColimits_of_natIso (evaluationIso B bijective (D := D) c).symm)

instance additive : (functor B bijective (D := D)).Additive :=
  (functor B bijective (D := D)).additive_of_preserves_binary_products

variable [HasDerivedCategory (C ⥤ D)] [HasDerivedCategory (B.Elements ⥤ D)]

/-- The right adjunction remains valid in the whole unbounded derived category. -/
def derivedAdjunction :
    (R).mapDerivedCategory ⊣ (functor B bijective (D := D)).mapDerivedCategory :=
  exactDerivedAdjunction (adjunction B bijective)

end ToricPower.ElementProduct

end
