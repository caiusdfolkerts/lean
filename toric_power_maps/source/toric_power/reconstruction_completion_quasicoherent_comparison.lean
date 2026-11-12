module

public import ToricPower.ReconstructionCompletionMappedComparison
public import ToricPower.QuasicoherentCategory

/-! # The original reconstruction map in the inherited sheaf categories

These interfaces retain the canonical zero morphisms and zero objects
of quasicoherent sheaves. All functors are still abstract when their
comparison maps and affine equivalence transport are checked.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace ToricPower

theorem reconstructionQuasicoherentNatTrans_quasiIso_of_iso
    (X : Scheme.{0}) {C : Type*} [Category* C]
    {F G : C ⥤ CochainComplex (QCoh X) ℕ} (τ : F ⟶ G)
    {M N : C} (e : M ≅ N) [QuasiIso (τ.app N)] : QuasiIso (τ.app M) :=
  reconstructionNatTrans_quasiIso_of_iso τ e

namespace FunctorTotal

variable (X : Scheme.{0}) [HasFiniteBiproducts (QCoh X)]
  {A : Type*} [Category* A] [Preadditive A]
  (H : A ⥤ QCoh X) [H.Additive]
  (Φ : QCoh X ⥤ CochainComplex (QCoh X) ℕ) [Φ.Additive]
  (T : QCoh X ⥤ QCoh X) [T.Additive]
  (n width : ℕ) (retained : n < width)
  (τ : Φ ⟶ singleCoefficient T n)

/-- The original augmentation with its entire target association fixed
in the canonical quasicoherent category. -/
def quasicoherentPrecomposedTopAugmentation : H ⋙ Φ ⟶ singleCoefficient (H ⋙ T) n :=
  Functor.whiskerLeft H τ

/-- The literal original finite-total map after mapping the input. -/
def quasicoherentTopComparisonAfterMap :=
  Functor.whiskerLeft (H.mapHomologicalComplex (.up ℤ))
    (topComparison Φ T n width retained τ)

theorem quasicoherentTopComparisonAfterMap_precompose_quasiIso_iff
    (K : CochainComplex A ℤ) :
    QuasiIso ((topComparison (H ⋙ Φ) (H ⋙ T) n width retained
      (quasicoherentPrecomposedTopAugmentation X H Φ T n τ)).app K) ↔
      QuasiIso ((quasicoherentTopComparisonAfterMap X H Φ T n width retained τ).app K) :=
  Iff.rfl

theorem quasicoherentTopComparisonAfterMap_quasiIso_iff
    (K : CochainComplex A ℤ) :
    QuasiIso ((quasicoherentTopComparisonAfterMap X H Φ T n width retained τ).app K) ↔
      QuasiIso ((topComparison Φ T n width retained τ).app
        ((H.mapHomologicalComplex (.up ℤ)).obj K)) :=
  Iff.rfl

end FunctorTotal

namespace FunctorTotal

variable (R : Type) [CommRing R] (U X : Scheme.{0})
  [HasFiniteBiproducts (QCoh X)]
  (H : QCoh U ⥤ QCoh X) [H.Additive]
  (Φ : QCoh X ⥤ CochainComplex (QCoh X) ℕ) [Φ.Additive]
  (T : QCoh X ⥤ QCoh X) [T.Additive]
  (n width : ℕ) (retained : n < width)
  (τ : Φ ⟶ singleCoefficient T n)
  (E : ModuleCat.{0} R ≌ QCoh U) [E.functor.Additive] [E.inverse.Additive]

/-- Equivalence transport with both original sheaf categories fixed
before any affine chart is substituted. -/
theorem quasicoherentAffineTopComparison_quasiIso_of_equivalence
    (localQuasiIso : ∀ M : CochainComplex (ModuleCat.{0} R) ℤ,
      QuasiIso ((quasicoherentTopComparisonAfterMap X (E.functor ⋙ H)
        Φ T n width retained τ).app M))
    (K : CochainComplex (QCoh U) ℤ) :
    QuasiIso ((quasicoherentTopComparisonAfterMap X H Φ T n width retained τ).app K) :=
  topComparisonAfterMap_quasiIso_of_equivalence H Φ T n width retained τ E localQuasiIso K

/-- The mapped-input form of the same map, with the actual affine
source's inherited complex category fixed as well. -/
theorem quasicoherentAffineTopComparisonAfterMap_quasiIso_iff
    (K : CochainComplex (QCoh U) ℤ) :
    QuasiIso ((quasicoherentTopComparisonAfterMap X H Φ T n width retained τ).app K) ↔
      QuasiIso ((topComparison Φ T n width retained τ).app
        ((H.mapHomologicalComplex (.up ℤ)).obj K)) :=
  Iff.rfl

end FunctorTotal

end ToricPower

end
