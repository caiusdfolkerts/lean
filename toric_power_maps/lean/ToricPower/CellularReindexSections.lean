module

public import ToricPower.CellularConstantMap
public import ToricPower.InjectiveResolutionMap
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-! # Actual reindexing of constant sections along an order isomorphism -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace ToricPower.Cellular

universe u
variable (k : Type u) [CommRing k] {C D : Type u} [Preorder C] [Preorder D]
  (e : C ≃o D)

def faceReindexFunctor : (C ⥤ ModuleCat.{u} k) ⥤ (D ⥤ ModuleCat.{u} k) :=
  (e.equivalence.congrLeft (E := ModuleCat.{u} k)).functor

instance faceReindexFunctor_equivalence : (faceReindexFunctor k e).IsEquivalence := by
  unfold faceReindexFunctor
  infer_instance

instance faceReindexFunctor_additive : (faceReindexFunctor k e).Additive where
  map_add := by intros; rfl

instance faceReindexFunctor_linear : (faceReindexFunctor k e).Linear k where
  map_smul _ _ := rfl

instance faceReindexFunctor_limits : PreservesFiniteLimits (faceReindexFunctor k e) := by
  infer_instance

instance faceReindexFunctor_colimits : PreservesFiniteColimits (faceReindexFunctor k e) := by
  infer_instance

def faceReindexHomEquiv (F G : C ⥤ ModuleCat.{u} k) :
    (F ⟶ G) ≃ₗ[k] ((faceReindexFunctor k e).obj F ⟶ (faceReindexFunctor k e).obj G) :=
  LinearEquiv.ofBijective ((faceReindexFunctor k e).mapLinearMap k)
    ((Functor.FullyFaithful.ofFullyFaithful (faceReindexFunctor k e)).map_bijective F G)

def faceReindexSectionEquiv (F : C ⥤ ModuleCat.{u} k) :
    (constantDiagram k D ⟶ (faceReindexFunctor k e).obj F) ≃ₗ[k]
      (constantDiagram k C ⟶ F) :=
  (faceReindexHomEquiv k e (constantDiagram k C) F).symm

theorem faceReindexMap_sectionEquiv (F : C ⥤ ModuleCat.{u} k)
    (s : constantDiagram k D ⟶ (faceReindexFunctor k e).obj F) :
    (faceReindexFunctor k e).map (faceReindexSectionEquiv k e F s) = s :=
  (faceReindexHomEquiv k e (constantDiagram k C) F).apply_symm_apply s

def faceReindexSectionNatIso :
    faceReindexFunctor k e ⋙ constantSections k D ≅ constantSections k C :=
  NatIso.ofComponents (fun F => (faceReindexSectionEquiv k e F).toModuleIso)
    (by
      intro F G f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro s
      apply (faceReindexFunctor k e).map_injective
      change (faceReindexFunctor k e).map
        (faceReindexSectionEquiv k e G (s ≫ (faceReindexFunctor k e).map f)) =
          (faceReindexFunctor k e).map (faceReindexSectionEquiv k e F s ≫ f)
      rw [faceReindexMap_sectionEquiv,CategoryTheory.Functor.map_comp,faceReindexMap_sectionEquiv])

theorem constantScalarMap_reindex :
    constantScalarMap k D ≫ (faceReindexSectionNatIso k e).hom.app (constantDiagram k C) =
      constantScalarMap k C := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  apply (faceReindexFunctor k e).map_injective
  change (faceReindexFunctor k e).map
    (faceReindexSectionEquiv k e (constantDiagram k C) (a • 𝟙 _)) =
      (faceReindexFunctor k e).map (a • 𝟙 _)
  rw [faceReindexMap_sectionEquiv,Functor.map_smul,CategoryTheory.Functor.map_id]
  rfl

def reindexedConstantResolution (J : InjectiveResolution (constantDiagram k C)) :
    InjectiveResolution (constantDiagram k D) :=
  mappedInjectiveResolution (faceReindexFunctor k e) J

theorem reindexedConstantSections_quasiIso
    (J : InjectiveResolution (constantDiagram k C))
    [QuasiIso (mappedSingleAugmentation (constantSections k C) (constantScalarMap k C) J.ι)] :
    QuasiIso (mappedSingleAugmentation (constantSections k D) (constantScalarMap k D)
      (reindexedConstantResolution k e J).ι) :=
  mappedInjectiveSection_quasiIso (faceReindexFunctor k e) J
    (constantSections k D) (constantSections k C) (faceReindexSectionNatIso k e)
    (constantScalarMap k D) (constantScalarMap k C) (constantScalarMap_reindex k e)

end ToricPower.Cellular

namespace ToricPower

def retainedIntersectionOrderIso {B : Type*} [Preorder B] (P Q : B → Prop) :
    {b : {b : B // Q b} // P b.val} ≃o {b : {b : B // P b} // Q b.val} where
  toFun b := ⟨⟨b.val.val,b.property⟩,b.val.property⟩
  invFun b := ⟨⟨b.val.val,b.property⟩,b.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

end ToricPower

end
