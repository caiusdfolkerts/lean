module

public import ToricPower.FiniteTotalEvaluationCriterion

/-! # The original top comparison under additive precomposition

This identity is checked with abstract source functors, before applying
it to affine tilde and direct image.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.FunctorTotal

variable {A C B : Type*} [Category* A] [Preadditive A]
  [Category* C] [Preadditive C] [Category* B] [Abelian B]
  [HasFiniteBiproducts B]
  (H : A ⥤ C) [H.Additive]
  (Φ : C ⥤ CochainComplex B ℕ) [Φ.Additive]
  (T : C ⥤ B) [T.Additive]
  (n width : ℕ) (retained : n < width)
  (τ : Φ ⟶ singleCoefficient T n)

/-- The original top augmentation, with its target association fixed
before any geometric source functor is substituted. -/
def precomposedTopAugmentation : H ⋙ Φ ⟶ singleCoefficient (H ⋙ T) n :=
  Functor.whiskerLeft H τ

/-- Precomposing the actual natural top map is identical to evaluating
the original top comparison on the mapped input complex. -/
theorem topComparison_precompose_quasiIso_iff (K : CochainComplex A ℤ) :
    QuasiIso ((topComparison (H ⋙ Φ) (H ⋙ T) n width retained
      (Functor.whiskerLeft H τ)).app K) ↔
    QuasiIso ((topComparison Φ T n width retained τ).app
      ((H.mapHomologicalComplex (.up ℤ)).obj K)) :=
  Iff.rfl

end ToricPower.FunctorTotal

end
