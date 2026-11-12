module

public import ToricPower.CellularClosedExtension
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.CategoryTheory.Linear.FunctorCategory

/-! # Exact closed extension and its genuine scalar-linear section comparison -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace ToricPower.Cellular

universe u
variable (R : Type u) [Ring R] {B : Type u} [Preorder B]
  (P : B → Prop) (downward : Antitone P)

instance closedFaceExtensionFunctor_limits :
    PreservesFiniteLimits (closedFaceExtensionFunctor R P downward) := by
  letI := (closedFaceAdjunction R P downward).isRightAdjoint
  infer_instance

instance closedFaceExtensionFunctor_colimits :
    PreservesFiniteColimits (closedFaceExtensionFunctor R P downward) := by
  apply preservesFiniteColimits_of_evaluation
  intro b
  by_cases hb : P b
  · exact preservesFiniteColimits_of_natIso (closedFaceEvaluationIso R P downward b hb).symm
  · let G := closedFaceExtensionFunctor R P downward ⋙ (evaluation B (ModuleCat.{u} R)).obj b
    have zeroG : IsZero G := G.isZero (fun F => closedFaceExtension_isZero R P downward F b hb)
    letI := G.preservesColimitsOfSize_of_isZero.{0,0} zeroG
    infer_instance

end ToricPower.Cellular

namespace ToricPower.Cellular

universe u
variable (k : Type u) [CommRing k] {B : Type u} [Preorder B]
  (P : B → Prop) (downward : Antitone P)

instance closedFaceRestriction_linear : (closedFaceRestriction k P).Linear k where
  map_smul _ _ := rfl

instance closedFaceExtensionFunctor_linear : (closedFaceExtensionFunctor k P downward).Linear k where
  map_smul _ _ := rfl

def closedFaceSectionEquiv (F : {b : B // P b} ⥤ ModuleCat.{u} k) :
    ((Functor.const B).obj (ModuleCat.of k k) ⟶ closedFaceExtension k P downward F) ≃ₗ[k]
      ((Functor.const {b : B // P b}).obj (ModuleCat.of k k) ⟶ F) where
  toAddEquiv := ((closedFaceAdjunction k P downward).homAddEquiv
    ((Functor.const B).obj (ModuleCat.of k k)) F).symm
  map_smul' a f := by
    change ((closedFaceAdjunction k P downward).homEquiv _ _).symm (a • f) =
      a • ((closedFaceAdjunction k P downward).homEquiv _ _).symm f
    simp only [Adjunction.homEquiv_symm_apply,Functor.map_smul,
      CategoryTheory.Linear.smul_comp]

def closedFaceSectionNatIso :
    closedFaceExtensionFunctor k P downward ⋙
      (linearCoyoneda k (B ⥤ ModuleCat.{u} k)).obj
        (op ((Functor.const B).obj (ModuleCat.of k k))) ≅
    (linearCoyoneda k ({b : B // P b} ⥤ ModuleCat.{u} k)).obj
      (op ((Functor.const {b : B // P b}).obj (ModuleCat.of k k))) :=
  NatIso.ofComponents (fun F => (closedFaceSectionEquiv k P downward F).toModuleIso)
    (by
      intro F G f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro s
      exact (closedFaceAdjunction k P downward).homEquiv_naturality_right_symm s f)

end ToricPower.Cellular

end
