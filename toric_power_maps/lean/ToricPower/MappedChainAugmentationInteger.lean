module

public import ToricPower.FunctorExtendComplex
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

/-!
# A genuine chart-chain augmentation in integer cochain degrees

The coefficient functor commutes with extension by zero. Together with
the canonical single-complex comparisons, this transports the original
natural-chain augmentation without changing its differential or map.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace ToricPower

variable {A D : Type*} [Category* A] [Category* D] [Abelian A] [Abelian D]
  (F : A ⥤ D) [F.Additive] (K : ChainComplex A ℕ) (T : A)
  (augmentation : (F.mapHomologicalComplex (.down ℕ)).obj K ⟶
    (ChainComplex.single₀ D).obj (F.obj T))

/-- The actual chart-chain augmentation after extension to integer degrees. -/
def integerMappedChainAugmentation :
    (F.mapHomologicalComplex (.up ℤ)).obj (K.extend ComplexShape.embeddingDownNat) ⟶
      (F.mapHomologicalComplex (.up ℤ)).obj ((CochainComplex.singleFunctor A 0).obj T) :=
  (mapExtendIso F K ComplexShape.embeddingDownNat).hom ≫
    extendMap augmentation ComplexShape.embeddingDownNat ≫
    (extendSingleIso ComplexShape.embeddingDownNat (F.obj T) 0 0 rfl).hom ≫
    (singleMapHomologicalComplex F (.up ℤ) 0).inv.app T

instance integerMappedChainAugmentation_quasiIso [QuasiIso augmentation] :
    QuasiIso (integerMappedChainAugmentation F K T augmentation) := by
  unfold integerMappedChainAugmentation
  infer_instance

/-- An explicit comparison of whole source complexes retains the chosen
geometric model's original name. -/
def integerMappedChainAugmentationOfModel
    (C : CochainComplex A ℤ) (sourceIso : C ≅ K.extend ComplexShape.embeddingDownNat) :
    (F.mapHomologicalComplex (.up ℤ)).obj C ⟶
      (F.mapHomologicalComplex (.up ℤ)).obj ((CochainComplex.singleFunctor A 0).obj T) :=
  ((F.mapHomologicalComplex (.up ℤ)).mapIso sourceIso).hom ≫
    integerMappedChainAugmentation F K T augmentation

instance integerMappedChainAugmentationOfModel_quasiIso [QuasiIso augmentation]
    (C : CochainComplex A ℤ) (sourceIso : C ≅ K.extend ComplexShape.embeddingDownNat) :
    QuasiIso (integerMappedChainAugmentationOfModel F K T augmentation C sourceIso) := by
  unfold integerMappedChainAugmentationOfModel
  infer_instance

end ToricPower
end
