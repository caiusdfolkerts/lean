module

public import ToricPower.MappedSingleAugmentation
public import ToricPower.FunctorExtendComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

/-! # The canonical integer-indexed image of a degree-zero augmentation -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

variable {A D : Type*} [Category* A] [Category* D]
  [Preadditive A] [Preadditive D] [HasZeroObject A] [HasZeroObject D]
  {Z : A} {I : CochainComplex A ℕ}

def extendedSingleAugmentation (ι : (CochainComplex.single₀ A).obj Z ⟶ I) :
    (CochainComplex.singleFunctor A 0).obj Z ⟶ I.extend ComplexShape.embeddingUpNat :=
  (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat Z 0 0 rfl).inv ≫
    HomologicalComplex.extendMap ι ComplexShape.embeddingUpNat

theorem extendedSingleAugmentation_zero
    (ι : (CochainComplex.single₀ A).obj Z ⟶ I) :
    (extendedSingleAugmentation ι).f 0 =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Z).hom ≫ ι.f 0 ≫
        (I.extendXIso ComplexShape.embeddingUpNat rfl).inv := by
  simp only [extendedSingleAugmentation,HomologicalComplex.comp_f,
    HomologicalComplex.extendSingleIso_inv_f]
  rw [HomologicalComplex.extendMap_f ι ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl]
  simp only [Category.assoc,Iso.inv_hom_id_assoc]
  change (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Z).hom ≫
    𝟙 Z ≫ ι.f 0 ≫ _ = _
  rw [Category.id_comp]

variable (F : A ⥤ D) [F.Additive] {V : D}

def integerMappedSingleAugmentation (a : V ⟶ F.obj Z)
    (ι : (CochainComplex.single₀ A).obj Z ⟶ I) :
    (CochainComplex.singleFunctor D 0).obj V ⟶
      (F.mapHomologicalComplex (.up ℤ)).obj (I.extend ComplexShape.embeddingUpNat) :=
  (CochainComplex.singleFunctor D 0).map a ≫
    (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app Z ≫
      (F.mapHomologicalComplex (.up ℤ)).map (extendedSingleAugmentation ι)

theorem integerMappedSingleAugmentation_zero (a : V ⟶ F.obj Z)
    (ι : (CochainComplex.single₀ A).obj Z ⟶ I) :
    (integerMappedSingleAugmentation F a ι).f 0 =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 V).hom ≫ a ≫
        F.map (ι.f 0) ≫ F.map (I.extendXIso ComplexShape.embeddingUpNat rfl).inv := by
  simp only [integerMappedSingleAugmentation,HomologicalComplex.comp_f,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    Functor.mapHomologicalComplex_map_f,extendedSingleAugmentation_zero,
    Functor.map_comp,Category.assoc,Iso.inv_hom_id_assoc]
  change ((HomologicalComplex.single D (.up ℤ) 0).map a).f 0 ≫ _ = _
  rw [HomologicalComplex.single_map_f_self]
  simp only [Category.assoc,Iso.inv_hom_id_assoc,← F.map_comp_assoc,
    Iso.inv_hom_id,Functor.map_id,Category.id_comp]

theorem integerMappedSingleAugmentation_comparison (a : V ⟶ F.obj Z)
    (ι : (CochainComplex.single₀ A).obj Z ⟶ I) :
    integerMappedSingleAugmentation F a ι ≫
        (mapExtendIso F I ComplexShape.embeddingUpNat).hom =
      extendedSingleAugmentation (mappedSingleAugmentation F a ι) := by
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f,integerMappedSingleAugmentation_zero,
    extendedSingleAugmentation_zero,mappedSingleAugmentation_zero]
  rw [mapExtendIso_hom_f F I ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl]
  simp only [Category.assoc,← F.map_comp_assoc,Iso.inv_hom_id,
    Functor.map_id,Category.id_comp,Category.comp_id]

end ToricPower

end
