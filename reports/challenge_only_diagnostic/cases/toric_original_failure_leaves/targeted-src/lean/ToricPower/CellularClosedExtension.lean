module

public import ToricPower.CellularPointAdjunction
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-! # Actual extension from a downward-closed face subposet -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.Cellular

universe u
variable (R : Type u) [Ring R] {B : Type u} [Preorder B]
  (P : B → Prop) (downward : Antitone P)

def closedFaceInclusion : {b : B // P b} ⥤ B where
  obj b := b.val
  map f := homOfLE f.le

def closedFaceRestriction :
    (B ⥤ ModuleCat.{u} R) ⥤ ({b : B // P b} ⥤ ModuleCat.{u} R) :=
  (Functor.whiskeringLeft _ _ _).obj (closedFaceInclusion P)

instance closedFaceRestriction_additive : (closedFaceRestriction R P).Additive := by
  unfold closedFaceRestriction
  infer_instance

instance closedFaceRestriction_limits : PreservesFiniteLimits (closedFaceRestriction R P) := by
  unfold closedFaceRestriction
  infer_instance

instance closedFaceRestriction_colimits : PreservesFiniteColimits (closedFaceRestriction R P) := by
  unfold closedFaceRestriction
  infer_instance

/-- This is literal extension by zero, represented uniformly by a
function on the lifted proof of membership in the closed subposet. -/
def closedFaceExtension (F : {b : B // P b} ⥤ ModuleCat.{u} R) : B ⥤ ModuleCat.{u} R where
  obj b := ModuleCat.of R ((h : PLift (P b)) → F.obj ⟨b,h.down⟩)
  map {b c} f := ModuleCat.ofHom
    { toFun := fun x hc => F.map (homOfLE f.le :
        (⟨b,downward f.le hc.down⟩ : {b : B // P b}) ⟶ ⟨c,hc.down⟩)
          (x ⟨downward f.le hc.down⟩)
      map_add' := by intros; funext h; exact map_add _ _ _
      map_smul' := by intros; funext h; exact map_smul _ _ _ }
  map_id b := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext h
    change F.map (𝟙 (⟨b,h.down⟩ : {b : B // P b})) (x h) = x h
    rw [CategoryTheory.Functor.map_id,ModuleCat.id_apply]
  map_comp {a b c} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext h
    exact ConcreteCategory.congr_hom
      (F.map_comp (homOfLE f.le) (homOfLE g.le)) _

def closedFaceExtensionFunctor :
    ({b : B // P b} ⥤ ModuleCat.{u} R) ⥤ (B ⥤ ModuleCat.{u} R) where
  obj := closedFaceExtension R P downward
  map {F G} f :=
    { app b := ModuleCat.ofHom
        { toFun := fun x h => f.app ⟨b,h.down⟩ (x h)
          map_add' := by intros; funext h; exact map_add _ _ _
          map_smul' := by intros; funext h; exact map_smul _ _ _ }
      naturality {b c} g := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        funext h
        exact ConcreteCategory.congr_hom (f.naturality (homOfLE g.le)) _ }
  map_id _ := rfl
  map_comp _ _ := rfl

instance closedFaceExtensionFunctor_additive :
    (closedFaceExtensionFunctor R P downward).Additive where
  map_add := by intros; rfl

def closedFaceUnit : 𝟭 (B ⥤ ModuleCat.{u} R) ⟶
    closedFaceRestriction R P ⋙ closedFaceExtensionFunctor R P downward where
  app F :=
    { app b := ModuleCat.ofHom
        { toFun := fun x _ => x
          map_add' := by intros; rfl
          map_smul' := by intros; rfl }
      naturality {_ _} _ := rfl }
  naturality {_ _} _ := rfl

def closedFaceCounit : closedFaceExtensionFunctor R P downward ⋙
    closedFaceRestriction R P ⟶ 𝟭 ({b : B // P b} ⥤ ModuleCat.{u} R) where
  app F :=
    { app b := ModuleCat.ofHom
        { toFun := fun x => x ⟨b.property⟩
          map_add' := by intros; rfl
          map_smul' := by intros; rfl }
      naturality {_ _} _ := rfl }
  naturality {_ _} _ := rfl

def closedFaceAdjunction :
    closedFaceRestriction R P ⊣ closedFaceExtensionFunctor R P downward where
  unit := closedFaceUnit R P downward
  counit := closedFaceCounit R P downward
  left_triangle_components F := by
    apply NatTrans.ext
    funext b
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  right_triangle_components F := by
    apply NatTrans.ext
    funext b
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext h
    rfl

instance closedFaceExtensionFunctor_injectives :
    (closedFaceExtensionFunctor R P downward).PreservesInjectiveObjects where
  injective_obj h := (closedFaceAdjunction R P downward).map_injective _ h

def closedFaceEvaluationEquiv (F : {b : B // P b} ⥤ ModuleCat.{u} R)
    (b : B) (hb : P b) :
    (closedFaceExtension R P downward F).obj b ≃ₗ[R] F.obj ⟨b,hb⟩ where
  toFun x := x ⟨hb⟩
  invFun x _ := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def closedFaceEvaluationIso (b : B) (hb : P b) :
    closedFaceExtensionFunctor R P downward ⋙ (evaluation B (ModuleCat.{u} R)).obj b ≅
      (evaluation {b : B // P b} (ModuleCat.{u} R)).obj ⟨b,hb⟩ :=
  NatIso.ofComponents (fun F => (closedFaceEvaluationEquiv R P downward F b hb).toModuleIso)
    (by intros; rfl)

theorem closedFaceExtension_isZero (F : {b : B // P b} ⥤ ModuleCat.{u} R)
    (b : B) (hb : ¬ P b) : IsZero ((closedFaceExtension R P downward F).obj b) := by
  letI : IsEmpty (PLift (P b)) := ⟨fun h => hb h.down⟩
  change IsZero (ModuleCat.of R ((h : PLift (P b)) → F.obj ⟨b,h.down⟩))
  exact ModuleCat.isZero_of_subsingleton _

end ToricPower.Cellular

end
