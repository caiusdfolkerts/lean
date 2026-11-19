module

public import ToricPower.ReconstructionCompletionFactors
public import ToricPower.ReconstructionCompletionDerivedBridge

/-! # Localization of the actual finite total comparison

The source and target factorizations are compared while their coefficient
functors remain abstract. This retains the original augmentation and its
actual finite total without expanding a concrete sheaf presentation.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

variable {A C B : Type*}
  [Category* A] [Abelian A] [HasDerivedCategory A]
  [Category* C] [Abelian C] [HasDerivedCategory C]
  [Category* B] [Abelian B] [HasFiniteBiproducts B] [HasDerivedCategory B]
  (H : A ⥤ C) [H.Additive]
  (Φ : C ⥤ CochainComplex B ℕ) [Φ.Additive]
  (T : A ⥤ B) [T.Additive]
  (n width : ℕ) (retained : n < width)
  (τ : H ⋙ Φ ⟶ FunctorTotal.singleCoefficient T n)
  (R : DerivedCategory A ⥤ DerivedCategory C)
  (L : DerivedCategory C ⥤ DerivedCategory B)
  (E : DerivedCategory A ⥤ DerivedCategory B)
  (S : CochainComplex A ℤ ⥤ CochainComplex A ℤ)

/-- The original finite total, with the displayed factorization on each
side, determines the actual derived reconstruction isomorphism. -/
def derivedTotalReconstructionOfCoresolution
    (objects : ∀ K, QuasiIso
      ((FunctorTotal.reconstructionComplexTopComparison H Φ T n width retained τ).app
        (S.obj K)))
    (sourceFactors : DerivedCategory.Q ⋙ (R ⋙ L) ≅
      S ⋙ H.mapHomologicalComplex (.up ℤ) ⋙
        FunctorTotal.functor Φ width ⋙ DerivedCategory.Q)
    (targetFactors : DerivedCategory.Q ⋙ E ≅
      S ⋙ T.mapHomologicalComplex (.up ℤ) ⋙
        shiftFunctor (CochainComplex B ℤ) (-(n : ℤ)) ⋙ DerivedCategory.Q) :
    R ⋙ L ≅ E :=
  derivedComparisonOfCoresolution (R ⋙ L) E S _ _
    (Functor.whiskerRight
      (FunctorTotal.reconstructionComplexTopComparison H Φ T n width retained τ)
      DerivedCategory.Q)
    (fun K => by
      letI := objects K
      change IsIso (DerivedCategory.Q.map
        ((FunctorTotal.reconstructionComplexTopComparison H Φ T n width retained τ).app
          (S.obj K)))
      infer_instance)
    sourceFactors targetFactors

end ToricPower

end
