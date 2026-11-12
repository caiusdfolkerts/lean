module

public import ToricPower.DerivedFunctorOnInjectiveComplex

/-!
# Canonical right-derived comparison for a chosen injective model

The naturality statement retains the actual derived morphism represented
by a chain map between injective models. It does not replace the derived
functor by an unrelated choice of termwise models.
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
variable (F : A ⥤ B) [F.Additive]

def rightDerivedFunctorPlusModelIso
    (J : CochainComplex.Plus A) [∀ q, Injective (J.obj.X q)]
    (X : DerivedCategory.Plus A) (e : DerivedCategory.Plus.Q.obj J ≅ X) :
    F.rightDerivedFunctorPlus.obj X ≅
      DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj J) :=
  F.rightDerivedFunctorPlus.mapIso e.symm ≪≫ rightDerivedFunctorPlusOnInjective F J

/-- The same comparison in the full unbounded derived category. -/
def rightDerivedFunctorPlusModelAmbientIso
    (J : CochainComplex.Plus A) [∀ q, Injective (J.obj.X q)]
    (X : DerivedCategory.Plus A) (e : DerivedCategory.Plus.Q.obj J ≅ X) :
    (F.rightDerivedFunctorPlus.obj X).obj ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj J.obj) :=
  (DerivedCategory.Plus.ι (C := B)).mapIso
    (rightDerivedFunctorPlusModelIso F J X e)

theorem rightDerivedFunctorPlusModelIso_naturality
    (J K : CochainComplex.Plus A)
    [∀ q, Injective (J.obj.X q)] [∀ q, Injective (K.obj.X q)]
    (X Y : DerivedCategory.Plus A)
    (eJ : DerivedCategory.Plus.Q.obj J ≅ X)
    (eK : DerivedCategory.Plus.Q.obj K ≅ Y)
    (a : X ⟶ Y) (h : J ⟶ K)
    (lifts : DerivedCategory.Plus.Q.map h = (eJ.hom ≫ a) ≫ eK.inv) :
    F.rightDerivedFunctorPlus.map a ≫
        (rightDerivedFunctorPlusModelIso F K Y eK).hom =
      (rightDerivedFunctorPlusModelIso F J X eJ).hom ≫
        DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map h) := by
  simp only [rightDerivedFunctorPlusModelIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom]
  calc
    F.rightDerivedFunctorPlus.map a ≫ F.rightDerivedFunctorPlus.map eK.inv ≫
        (rightDerivedFunctorPlusOnInjective F K).hom =
      F.rightDerivedFunctorPlus.map (eJ.inv ≫ DerivedCategory.Plus.Q.map h) ≫
        (rightDerivedFunctorPlusOnInjective F K).hom := by
          simp only [lifts, Category.assoc, Iso.inv_hom_id_assoc,
            CategoryTheory.Functor.map_comp]
    _ = F.rightDerivedFunctorPlus.map eJ.inv ≫
        (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map h) ≫
          (rightDerivedFunctorPlusOnInjective F K).hom) := by
          rw [CategoryTheory.Functor.map_comp, Category.assoc]
    _ = _ := by
      rw [rightDerivedFunctorPlusOnInjective_naturality, Category.assoc]

end ToricPower

end
