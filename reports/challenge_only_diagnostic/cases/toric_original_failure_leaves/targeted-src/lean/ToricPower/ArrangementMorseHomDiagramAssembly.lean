module

public import ToricPower.ArrangementMorseHomDiagramCore
public import ToricPower.ComplexHomDiagramAdditive

/-! # Affine Morse assembly for the original intrinsic Hom diagram

All changes of equal scalar and additive presentations are checked with
an abstract label functor. Geometric labels are substituted only after
this comparison; the conclusion still names the original Hom diagram.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 300000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

attribute [local instance 2000] Abelian.toPreadditive
attribute [local instance 2000] Preadditive.preadditiveHasZeroMorphisms

namespace ToricPower.IntegralArrangement

variable {X : Scheme.{0}} {I : Type*}
  (opens : I → X.Opens) [∀ i, IsAffineHom (opens i).ι]
  {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (c : UniversalIncidenceObject A) (region : Set (Fin n → ℝ))
  [Linear ℂ (QCoh X)]
  (P : (UniversalIncidenceObject A)ᵒᵖ ⥤ QCoh X)

theorem universalLocalMorse_affineCoresolution_acyclic_homDiagram
    (localModels : ∀ i : I, QCoh (opens i).toScheme ⥤
      UniversalIncidenceObject A ⥤ ModuleCat ℂ)
    (comparison : ∀ i : I, localModels i ≅
      quasicoherentAffinePushforward (opens i).ι ⋙ Cellular.complexHomDiagram P)
    (localVanishing : ∀ (i : I) (M : QCoh (opens i).toScheme),
      ((universalLocalMorse A ℂ c region).obj
        ((CochainComplex.singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat ℂ) 0).obj
          ((localModels i).obj M))).Acyclic)
    (l : List I) (K : CochainComplex (QCoh X) ℤ) :
    ((universalLocalMorse A ℂ c region).obj
      (((Cellular.homDiagram ℂ P).mapHomologicalComplex (.up ℤ)).obj
        ((affineConeCoresolution opens l).obj K))).Acyclic := by
  have result := universalLocalMorse_affineCoresolution_acyclic_homDiagram_core
    opens A c region P
    (canonicalAdditive := Cellular.complexHomDiagram_abelian_additive P)
    localModels comparison localVanishing l K
  exact result


end ToricPower.IntegralArrangement
end
