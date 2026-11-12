module

public import ToricPower.ReconstructionCompletionTotalPrecompose
public import ToricPower.FiniteTotalEvaluationCriterion
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-! # Factorizations of the original reconstruction comparison

These comparisons are proved with abstract functors.  They retain the
actual cellular top map when the geometric coefficient functors are
substituted.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

section HomotopyFactors

variable {A C D : Type*} [Category* A] [Preadditive A]
  [Category* C] [Abelian C] [HasDerivedCategory C] [Category* D]
  (H : A ⥤ C) [H.Additive]
  (L : DerivedCategory C ⥤ D)
  (F : CochainComplex C ℤ ⥤ D)

/-- An ordinary derived factorization also factors the corresponding
homotopy functor before any source is specialized to sheaves. -/
def homotopyCompositeFactors (e : DerivedCategory.Q ⋙ L ≅ F) :
    HomotopyCategory.quotient A (.up ℤ) ⋙
        (H.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⋙ L) ≅
      H.mapHomologicalComplex (.up ℤ) ⋙ F :=
  Functor.isoWhiskerRight (H.mapHomotopyCategoryFactors (.up ℤ))
      (DerivedCategory.Qh ⋙ L) ≪≫
    Functor.isoWhiskerLeft (H.mapHomologicalComplex (.up ℤ))
      (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso C) L ≪≫ e)

end HomotopyFactors

namespace FunctorTotal

variable {A C B : Type*} [Category* A] [Preadditive A]
  [Category* C] [Preadditive C] [Category* B] [Abelian B]
  [HasFiniteBiproducts B]
  (H : A ⥤ C) [H.Additive]
  (Φ : C ⥤ CochainComplex B ℕ) [Φ.Additive]
  (T : A ⥤ B) [T.Additive]
  (n width : ℕ) (retained : n < width)
  (τ : H ⋙ Φ ⟶ singleCoefficient T n)

/-- The original geometric top augmentation, totalized on the original
Hom complex.  The source has the form used by the actual derived coend. -/
def reconstructionComplexTopComparison :
    H.mapHomologicalComplex (.up ℤ) ⋙ functor Φ width ⟶
      T.mapHomologicalComplex (.up ℤ) ⋙
        shiftFunctor (CochainComplex B ℤ) (-(n : ℤ)) :=
  (precomposeIso H Φ width).hom ≫ topComparison (H ⋙ Φ) T n width retained τ

@[simp]
theorem reconstructionComplexTopComparison_app (K : CochainComplex A ℤ) :
    (reconstructionComplexTopComparison H Φ T n width retained τ).app K =
      (topComparison (H ⋙ Φ) T n width retained τ).app K := by
  simp [reconstructionComplexTopComparison, precomposeIso]

end FunctorTotal

end ToricPower

end
