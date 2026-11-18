module

public import ToricPower.ReconstructionCompletionLocalConditionTransport

/-! # The native coefficient composition in the affine condition

The inherited zero morphisms on quasicoherent sheaves and their
preadditive presentation give the same coefficient composition.  We
identify the entire affine comparison predicate before specializing its
Hom diagram or tensor functor.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace ToricPower

/-- Compose the coefficient functors in their native complex category,
before imposing the finite total's expected codomain presentation. -/
abbrev reconstructionNativeCoefficientComposition (X : Scheme)
    {D : Type*} [Category.{0} D]
    (H : QCoh X ⥤ D) (Φ : D ⥤ CochainComplex (QCoh X) ℕ) :=
  H ⋙ Φ

variable (X : Scheme) {J : Type} {I : Type*} [Category.{0} J]
  (V : I → X.Opens) [∀ i, IsAffineHom (V i).ι]
  (H : QCoh X ⥤ (J ⥤ @ModuleCat.{0} ℂ Complex.commRing.toRing)) [H.Additive]
  (Φ : (J ⥤ ModuleCat.{0} ℂ) ⥤ CochainComplex (QCoh X) ℕ) [Φ.Additive]
  (T : QCoh X ⥤ QCoh X) [T.Additive]
  (n width : ℕ) (retained : n < width)
  (τ : H ⋙ Φ ⟶ T ⋙ HomologicalComplex.single (QCoh X) (.up ℕ) n)

local instance reconstructionNativeCoefficientConditionBiproducts :
    HasFiniteBiproducts (QCoh X) := HasFiniteBiproducts.of_hasFiniteProducts

/-- The unchanged native top comparison supplies exactly the named
all-affine comparison condition. -/
theorem reconstructionAffineTopCondition_of_nativeComposition
    (localQuasiIso : ∀ (i : I) (K : CochainComplex (QCoh (V i).toScheme) ℤ),
      QuasiIso ((FunctorTotal.topComparison
        (reconstructionNativeCoefficientComposition X H Φ) T n width retained τ).app
        (((quasicoherentAffinePushforward (V i).ι).mapHomologicalComplex (.up ℤ)).obj K))) :
    schemeAffineTopComparisonCondition X V H Φ T n width retained τ :=
  localQuasiIso

end ToricPower

end
