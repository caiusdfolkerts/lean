module

public import Mathlib.CategoryTheory.NatIso
public import Mathlib.CategoryTheory.Whiskering

/-! # Factoring a shifted model before evaluating its coefficients -/

@[expose] public noncomputable section

open CategoryTheory

namespace ToricPower

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

/-- A normalization, shift comparison and genuine localization factorization
compose as whole natural isomorphisms. All functors remain abstract. -/
def shiftedModelFactorization
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E] {F : Type u₄} [Category.{v₄} F]
    (sourceLocalization : C ⥤ D) (targetLocalization : E ⥤ F)
    (sourceShift : C ⥤ C) (derivedShift : D ⥤ D)
    (rightAdjoint affineModel : D ⥤ F) (complexModel : C ⥤ E)
    (normalization : rightAdjoint ≅ derivedShift ⋙ affineModel)
    (shift : sourceLocalization ⋙ derivedShift ≅ sourceShift ⋙ sourceLocalization)
    (factorization : sourceLocalization ⋙ affineModel ≅ complexModel ⋙ targetLocalization) :
    sourceLocalization ⋙ rightAdjoint ≅ (sourceShift ⋙ complexModel) ⋙ targetLocalization :=
  Functor.isoWhiskerLeft sourceLocalization normalization ≪≫
    (Functor.associator sourceLocalization derivedShift affineModel).symm ≪≫
    Functor.isoWhiskerRight shift affineModel ≪≫
    Functor.associator sourceShift sourceLocalization affineModel ≪≫
    Functor.isoWhiskerLeft sourceShift factorization ≪≫
    (Functor.associator sourceShift complexModel targetLocalization).symm

end ToricPower
end
