module

public import ToricPower.AffineInvertibleMorse

/-! # Transport the whole actual affine coefficient construction

The ring presentation and equality of entire functors are resolved while
all geometric data are abstract, before evaluating any toric coefficient.
-/

@[expose] public noncomputable section

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

theorem affineOpenInvertible_localMorse_acyclic_of_functor
    {n s : ℕ} (A : Fin s → Fin n → ℤ)
    (c : UniversalIncidenceObject A) (region : Set (Fin n → ℝ))
    (R : Type) [CommRing R] (X : Scheme) [X.Over (Spec (.of ℂ))] [IsIntegral X]
    [(Spec (.of R)).Over (Spec (.of ℂ))] [IsIntegral (Spec (.of R))]
    (j : Spec (.of R) ⟶ X) [IsOpenImmersion j] [IsAffineHom j] [j.IsOver (Spec (.of ℂ))]
    (P : (UniversalIncidenceObject A)ᵒᵖ ⥤ QCoh X)
    (invertible : ∀ d, TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X (P.obj (op d)).obj)
    (F : ModuleCat.{0} R ⥤ UniversalIncidenceObject A ⥤ ModuleCat ℂ)
    (same : F = (tildeEquiv (R := CommRingCat.of R)).functor ⋙
      quasicoherentAffinePushforward j ⋙ Cellular.homDiagram ℂ P)
    (T : UniversalIncidenceObject A ⥤ ModuleCat ℂ)
    (unit : (Cellular.homDiagram ℂ P).obj (quasicoherentAffineUnitImage j) ≅ T)
    (rankOne : ((universalLocalMorse A ℂ c region).obj
      ((CochainComplex.singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat ℂ) 0).obj T)).Acyclic)
    (M : ModuleCat.{0} R) :
    ((universalLocalMorse A ℂ c region).obj
      ((CochainComplex.singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat ℂ) 0).obj
        (F.obj M))).Acyclic := by
  let H : ModuleCat.{0} R ⥤ UniversalIncidenceObject A ⥤ ModuleCat ℂ :=
    (tildeEquiv (R := CommRingCat.of R)).functor ⋙
      quasicoherentOpenIntrinsicLabelHom ℂ j P
  letI := (tildeEquiv (R := CommRingCat.of R)).functor.additive_of_preserves_binary_products
  letI := (quasicoherentOpenIntrinsicLabelHom_exact ℂ j P invertible).1
  letI := (quasicoherentOpenIntrinsicLabelHom_exact ℂ j P invertible).2
  letI := quasicoherentOpenIntrinsicLabelHom_preservesColimits ℂ X P j invertible
  let e : H.obj (ModuleCat.of R R) ≅ T :=
    quasicoherentAffineRankOneComparison R j (Cellular.homDiagram ℂ P) H rfl T unit
  have result := universalLocalMorse_affineModules_acyclic_of_rankOneIso_complex A c region R H
    (fun S hs => hs.map_of_exact H) (fun _ => inferInstance) T e rankOne M
  have equal : F = H := same
  rw [equal]
  exact result

end ToricPower

end
