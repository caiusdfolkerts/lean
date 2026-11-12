module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.Algebra.Homology.FullSubcategory

/-!
# The actual right-derived unit on injective complexes

This is a thin interface to Mathlib's right-derived functor. It accepts
an ordinary bounded-below complex whose terms are injective, constructs
its lift to the injective-object category, and obtains the canonical
comparison isomorphism and its naturality.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CochainComplex

namespace ToricPower

universe u v u' v' w w'
variable {A : Type u} [Category.{v} A] [Abelian A]
variable {B : Type u'} [Category.{v'} B] [Abelian B]
variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
variable [EnoughInjectives A]

def liftInjectiveComplex (J : CochainComplex A ℤ) [∀ q, Injective (J.X q)] :
    CochainComplex (InjectiveObject A) ℤ :=
  HomologicalComplex.liftObjectProperty (isInjective A) J inferInstance

theorem liftInjectiveComplex_forget (J : CochainComplex A ℤ)
    [∀ q, Injective (J.X q)] :
    ((InjectiveObject.ι A).mapHomologicalComplex (.up ℤ)).obj
      (liftInjectiveComplex J) = J := rfl

def liftInjectivePlusComplex (J : CochainComplex.Plus A)
    [∀ q, Injective (J.obj.X q)] : CochainComplex.Plus (InjectiveObject A) := by
  refine ⟨liftInjectiveComplex J.obj, ?_⟩
  obtain ⟨a, ha⟩ := J.property
  refine ⟨a, ?_⟩
  rw [← CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff _ (InjectiveObject.ι A)]
  exact ha

theorem liftInjectivePlusComplex_forget (J : CochainComplex.Plus A)
    [∀ q, Injective (J.obj.X q)] :
    (InjectiveObject.ι A).mapCochainComplexPlus.obj (liftInjectivePlusComplex J) = J := by
  apply ObjectProperty.FullSubcategory.ext
  exact liftInjectiveComplex_forget J.obj

variable (F : A ⥤ B) [F.Additive]

theorem rightDerivedFunctorPlusUnit_isIso_of_injective
    (J : CochainComplex.Plus A) [∀ q, Injective (J.obj.X q)] :
    IsIso (F.rightDerivedFunctorPlusUnit.app J) := by
  rw [← liftInjectivePlusComplex_forget J]
  infer_instance

def rightDerivedFunctorPlusOnInjective
    (J : CochainComplex.Plus A) [∀ q, Injective (J.obj.X q)] :
    F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj J) ≅
      DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj J) := by
  letI := rightDerivedFunctorPlusUnit_isIso_of_injective F J
  exact (asIso (F.rightDerivedFunctorPlusUnit.app J)).symm

theorem rightDerivedFunctorPlusOnInjective_naturality
    {J K : CochainComplex.Plus A}
    [∀ q, Injective (J.obj.X q)] [∀ q, Injective (K.obj.X q)] (f : J ⟶ K) :
    F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f) ≫
        (rightDerivedFunctorPlusOnInjective F K).hom =
      (rightDerivedFunctorPlusOnInjective F J).hom ≫
        DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map f) := by
  letI := rightDerivedFunctorPlusUnit_isIso_of_injective F J
  letI := rightDerivedFunctorPlusUnit_isIso_of_injective F K
  have naturality := F.rightDerivedFunctorPlusUnit.naturality f
  change DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map f) ≫
      F.rightDerivedFunctorPlusUnit.app K =
    F.rightDerivedFunctorPlusUnit.app J ≫
      F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f) at naturality
  apply (cancel_epi (F.rightDerivedFunctorPlusUnit.app J)).mp
  simp only [rightDerivedFunctorPlusOnInjective, Iso.symm_hom, asIso_inv,
    Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← Category.assoc, ← naturality,
    Category.assoc, IsIso.hom_inv_id, Category.comp_id]

end ToricPower

end
