module

public import ToricPower.ReconstructionCompletionSchemeDerivedBridge
public import ToricPower.ReconstructionCompletionFiniteAffine

/-! # Derived reconstruction from the actual affine comparison

The finite affine cone argument and its derived localization are composed
with the scheme and coefficient diagram still abstract.  Thus the original
local comparison is retained without expanding a concrete toric Hom functor
to compare its inherited complex structures.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace ToricPower

variable (X : Scheme) {J : Type} {I : Type*} [Category.{0} J]
  [HasDerivedCategory.{1} (J ⥤ ModuleCat.{0} ℂ)]
  (V : I → X.Opens) [∀ i, IsAffineHom (V i).ι]

local instance schemeAffineReconstructionStandardDerived : HasDerivedCategory.{1} (QCoh X) :=
  HasDerivedCategory.standard _

local instance schemeAffineReconstructionBridgeBiproducts : HasFiniteBiproducts (QCoh X) :=
  HasFiniteBiproducts.of_hasFiniteProducts

variable
  (H : QCoh X ⥤ (J ⥤ @ModuleCat.{0} ℂ Complex.commRing.toRing)) [H.Additive]
  (Φ : (J ⥤ ModuleCat.{0} ℂ) ⥤ CochainComplex (QCoh X) ℕ) [Φ.Additive]
  (T : QCoh X ⥤ QCoh X) [T.Additive]
  (n width : ℕ) (retained : n < width)
  (τ : H ⋙ Φ ⟶ T ⋙ HomologicalComplex.single (QCoh X) (.up ℕ) n)
  (R : DerivedQCoh X ⥤ DerivedCategory (J ⥤ ModuleCat.{0} ℂ))
  (L : DerivedCategory (J ⥤ ModuleCat.{0} ℂ) ⥤ DerivedQCoh X)
  [L.CommShift ℤ] [L.IsTriangulated]
  (E : DerivedQCoh X ⥤ DerivedQCoh X)

/-- The original comparison on all unbounded complexes over each displayed
affine open. Naming this proposition keeps its large concrete coefficient
functors unevaluated when the derived reconstruction is specialized. -/
def schemeAffineLocalReconstructionCondition : Prop :=
  ∀ (i : I) (K : CochainComplex (QCoh (V i).toScheme) ℤ),
    QuasiIso ((FunctorTotal.reconstructionComplexTopComparison H Φ T n width retained τ).app
      (((quasicoherentAffinePushforward (V i).ι).mapHomologicalComplex (.up ℤ)).obj K))

/-- The exact finite affine comparison yields the original derived
reconstruction isomorphism through its displayed source and target factors. -/
def schemeDerivedReconstructionOfAffineComparison
    (factors : DerivedCategory.Q ⋙ L ≅
      FunctorTotal.functor Φ width ⋙ DerivedCategory.Q)
    (l : List I)
    (sourceFactors : DerivedCategory.Q ⋙ (R ⋙ L) ≅
      affineConeCoresolution V l ⋙ H.mapHomologicalComplex (.up ℤ) ⋙
        FunctorTotal.functor Φ width ⋙ DerivedCategory.Q)
    (targetFactors : DerivedCategory.Q ⋙ E ≅
      affineConeCoresolution V l ⋙ T.mapHomologicalComplex (.up ℤ) ⋙
        shiftFunctor (CochainComplex (QCoh X) ℤ) (-(n : ℤ)) ⋙ DerivedCategory.Q)
    (localQuasiIso : schemeAffineLocalReconstructionCondition X V H Φ T n width retained τ) :
    R ⋙ L ≅ E :=
  schemeDerivedTotalReconstructionOfCoresolution X H Φ T n width retained τ R L E
    (affineConeCoresolution V l)
    (fun K => affineCoresolution_reconstructionComparison_quasiIso
      V H Φ T n width retained τ L factors localQuasiIso l K)
    sourceFactors targetFactors

end ToricPower

end
