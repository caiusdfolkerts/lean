module

public import ToricPower.ArrangementMorseNamedCoresolution
public import ToricPower.MorseCategoryPresentations

/-! # Complex coefficients at the actual affine Morse assembly boundary

The general field-valued theorem is specialized while every coefficient
functor is still abstract. Its type therefore already uses the concrete
complex-number category presentation used by the actual geometric model.
All hypotheses and the arbitrary unbounded input are unchanged.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

attribute [local instance 2000] Abelian.toPreadditive
attribute [local instance 2000] Preadditive.preadditiveHasZeroMorphisms

namespace ToricPower.IntegralArrangement

variable {X : Scheme.{0}} {I : Type*}
  (opens : I → X.Opens) [∀ i, IsAffineHom (opens i).ι]
  {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (c : UniversalIncidenceObject A) (region : Set (Fin n → ℝ))
  (F : QCoh X ⥤ UniversalIncidenceObject A ⥤ ModuleCat ℂ) [F.Additive]

theorem universalLocalMorse_affineCoresolution_acyclic_standardComplex
    (localModels : ∀ i : I, QCoh (opens i).toScheme ⥤
      UniversalIncidenceObject A ⥤ ModuleCat ℂ)
    (comparison : ∀ i : I, localModels i ≅
      quasicoherentAffinePushforward (opens i).ι ⋙ F)
    (localVanishing : ∀ (i : I) (M : QCoh (opens i).toScheme),
      ((universalLocalMorse A ℂ c region).obj
        ((CochainComplex.singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat ℂ) 0).obj
          ((localModels i).obj M))).Acyclic)
    (l : List I) (K : CochainComplex (QCoh X) ℤ) :
    ((universalLocalMorse A ℂ c region).obj
      ((F.mapHomologicalComplex (.up ℤ)).obj ((affineConeCoresolution opens l).obj K))).Acyclic := by
  simpa only [morseComplexRingPresentation] using
    (universalLocalMorse_affineCoresolution_acyclic_of_named opens A ℂ c region F
      localModels comparison localVanishing l K)

end ToricPower.IntegralArrangement
end
