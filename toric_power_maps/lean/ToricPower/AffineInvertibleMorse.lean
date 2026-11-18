module

public import ToricPower.ArrangementMorseRankOneComplex
public import ToricPower.AffineRankOneSections
public import ToricPower.AffineInvertibleHomColimits

/-! # Actual affine invertible-label Hom from its unit calculation

The entire geometric coefficient construction is kept together while
the exactness and unrestricted free-module argument are applied. The
rank-one comparison is the genuine tilde/unit isomorphism.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ToricPower.IntegralArrangement

attribute [local instance 2000] CommRing.toRing
attribute [local instance 2100] Complex.instRing
attribute [local instance 2000] Ring.toAddCommGroup
attribute [local instance 2000] Ring.toSemiring
attribute [local instance 2000] Preadditive.preadditiveHasZeroMorphisms

namespace ToricPower

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (c : UniversalIncidenceObject A) (region : Set (Fin n → ℝ))
  (R : CommRingCat) (X : Scheme) [X.Over (Spec (.of ℂ))] [IsIntegral X]
  [(Spec R).Over (Spec (.of ℂ))] [IsIntegral (Spec R)]
  (j : Spec R ⟶ X) [IsOpenImmersion j] [IsAffineHom j] [j.IsOver (Spec (.of ℂ))]
  (P : (UniversalIncidenceObject A)ᵒᵖ ⥤ QCoh X)
  (invertible : ∀ d, TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X (P.obj (op d)).obj)
  (T : UniversalIncidenceObject A ⥤ ModuleCat ℂ)
  (unit : (Cellular.homDiagram ℂ P).obj (quasicoherentAffineUnitImage j) ≅ T)
  (rankOne : ((universalLocalMorse A ℂ c region).obj
    ((CochainComplex.singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat ℂ) 0).obj T)).Acyclic)

include invertible T unit rankOne

/-- No finite generation or bound on the coefficient module is used. -/
theorem affineOpenInvertible_localMorse_acyclic (M : ModuleCat.{0} R) :
    ((universalLocalMorse A ℂ c region).obj
      ((CochainComplex.singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat ℂ) 0).obj
        (((tildeEquiv (R := R)).functor ⋙ quasicoherentOpenIntrinsicLabelHom ℂ j P).obj M))).Acyclic := by
  let H := (tildeEquiv (R := R)).functor ⋙ quasicoherentOpenIntrinsicLabelHom ℂ j P
  letI := (tildeEquiv (R := R)).functor.additive_of_preserves_binary_products
  letI := (quasicoherentOpenIntrinsicLabelHom_exact ℂ j P invertible).1
  letI := (quasicoherentOpenIntrinsicLabelHom_exact ℂ j P invertible).2
  letI := quasicoherentOpenIntrinsicLabelHom_preservesColimits ℂ X P j invertible
  let e : H.obj (ModuleCat.of R R) ≅ T :=
    quasicoherentAffineRankOneImageIso R j (Cellular.homDiagram ℂ P) ≪≫ unit
  exact universalLocalMorse_affineModules_acyclic_of_rankOneIso_complex A c region R H
    (fun S hs => hs.map_of_exact H) (fun _ => inferInstance) T e rankOne M

end ToricPower

end
