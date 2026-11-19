module

public import ToricPower.ReconstructionCompletionAffineExtension
public import ToricPower.ReconstructionCompletionMappedCondition

/-! # The original named comparison on an affine chart family

The original affine extension retains its named mapped-input comparison.
That exact map supplies the native condition before any expansion to
an objectwise finite-total formula.
-/

@[expose] public noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open ToricPower.FunctorTotal

namespace ToricPower

/-- Package the unchanged original mapped comparison while its source
and coefficient functors remain abstract. -/
theorem reconstructionMappedCondition_of_components
    (U X : Scheme.{0}) [HasFiniteBiproducts (QCoh X)]
    (A : QCoh U ⥤ QCoh X) [A.Additive]
    (F : QCoh X ⥤ CochainComplex (QCoh X) ℕ) [F.Additive]
    (T : QCoh X ⥤ QCoh X) [T.Additive]
    (n width : ℕ) (retained : n < width)
    (τ : F ⟶ singleCoefficient T n)
    (h : ∀ K : CochainComplex (QCoh U) ℤ,
      QuasiIso ((quasicoherentTopComparisonAfterMap X A F T n width retained τ).app K)) :
    reconstructionMappedTopComparisonCondition U X A F T n width retained τ :=
  h

variable {I : Type*} (R : I → Type) [∀ i, CommRing (R i)]
  (X : Scheme) [X.Over (Spec (.of ℂ))] [IsIntegral X]
  [∀ i, (Spec (.of (R i))).Over (Spec (.of ℂ))]
  [∀ i, IsIntegral (Spec (.of (R i)))]
  (j : ∀ i, Spec (.of (R i)) ⟶ X)
  [∀ i, IsOpenImmersion (j i)] [∀ i, IsAffineHom (j i)]
  [∀ i, IsAffineHom (j i).opensRange.ι]
  [∀ i, (j i).IsOver (Spec (.of ℂ))]
  {C : Type} [Category.{0} C] (P : Cᵒᵖ ⥤ QCoh X)
  (invertible : ∀ c,
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X (P.obj (op c)).obj)
  (Φ : (C ⥤ @ModuleCat.{0} ℂ Complex.commRing.toRing) ⥤ CochainComplex (QCoh X) ℕ) [Φ.Additive]
  [PreservesFiniteLimits Φ] [PreservesColimitsOfSize.{0,0} Φ]
  (L : QCoh X)
  [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X L.obj]
  (n : ℕ) (τ : Cellular.homDiagram ℂ P ⋙ Φ ⟶ singleCoefficient (tensorLeft L) n)
  (above : ∀ M q, n < q → IsZero ((Φ.obj M).X q))
  {A : Type*} (opens : A → X.Opens) (covering : iSup opens = ⊤)
  (affine : ∀ a, IsAffineOpen (opens a))
  (rankOne : ∀ i, QuasiIso (τ.app (quasicoherentAffineUnitImage (j i))))

local instance reconstructionNamedAffineChartFamilyBiproducts :
    HasFiniteBiproducts (QCoh X) := HasFiniteBiproducts.of_hasFiniteProducts

/-- The original rank-one theorem gives the exact named reconstruction
condition on every affine chart, for arbitrary unbounded complexes. -/
def reconstructionAffineFamily_mappedChartCondition
    (width : ℕ) (retained : n < width) :=
  fun i => reconstructionMappedCondition_of_components (Spec (.of (R i))) X
    (quasicoherentAffinePushforward (j i)) (Cellular.homDiagram ℂ P ⋙ Φ)
    (tensorLeft L) n width retained τ
    (reconstructionAffineComparison_quasiIso (R i) X (j i)
      P invertible Φ L n τ above opens covering affine (rankOne i) width retained)

end ToricPower

end


