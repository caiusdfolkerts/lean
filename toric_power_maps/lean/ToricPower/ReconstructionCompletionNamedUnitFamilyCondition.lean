module

public import ToricPower.ReconstructionCompletionAffineFamilyCondition
public import ToricPower.ReconstructionCompletionWitnessCondition
public import ToricPower.ReconstructionCompletionMixedCoefficientComposition
public import ToricPower.ReconstructionCompletionCoefficientNativeScalar
public import ToricPower.ReconstructionCompletionSpecWitnessFamily

/-! # The native augmentation and named affine unit family

The original augmentation retains its native quasicoherent complex
category, and its rank-one hypothesis retains the same generic family
predicate, before specializing to toric charts.
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
  (Φ : (C ⥤ ModuleCat.{0} ℂ) ⥤ CochainComplex (QCoh X) ℕ) [Φ.Additive]
  [PreservesFiniteLimits Φ] [PreservesColimitsOfSize.{0,0} Φ]
  (L : QCoh X)
  [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X L.obj]
  (n : ℕ) (τ : reconstructionMixedCoefficientComposition X
    (Cellular.homDiagram ℂ P) Φ ⟶
    tensorLeft L ⋙ HomologicalComplex.single (QCoh X) (.up ℕ) n)
  (above : ∀ M q, n < q → IsZero ((Φ.obj M).X q))
  {A : Type*} (opens : A → X.Opens) (covering : iSup opens = ⊤)
  (affine : ∀ a, IsAffineOpen (opens a))
  (rankOne : reconstructionAffineUnitFamilyCondition (fun i => Spec (.of (R i))) X j τ)

/-- The original native augmentation and its named unit-family theorem
supply the already-proved exact unbounded reconstruction condition. -/
def reconstructionNamedUnitFamily_topComparisonCondition
    (width : ℕ) (retained : n < width) :=
  let Ψ := reconstructionCoefficientNativeScalar X Φ
  letI : Ψ.Additive := reconstructionCoefficientNativeScalar_additive X Φ
  letI : PreservesFiniteLimits Ψ :=
    reconstructionCoefficientNativeScalar_preservesFiniteLimits X Φ
  letI : PreservesColimitsOfSize.{0, 0} Ψ :=
    reconstructionCoefficientNativeScalar_preservesColimits X Φ
  let β := reconstructionAugmentationNativeScalar X Φ (Cellular.homDiagram ℂ P)
    (tensorLeft L ⋙ HomologicalComplex.single (QCoh X) (.up ℕ) n) τ
  let units := (reconstructionAffineUnitFamily_nativeScalar_iff
    X Φ (Cellular.homDiagram ℂ P)
    (tensorLeft L ⋙ HomologicalComplex.single (QCoh X) (.up ℕ) n) τ
    (fun i => Spec (.of (R i))) j).mp rankOne
  let core := reconstructionAffineFamily_topComparisonCondition R X j P invertible Ψ L n
    (reconstructionAugmentationWitnessMap (F := Cellular.homDiagram ℂ P ⋙ Ψ)
      X (tensorLeft L) n β
      (fun i => Spec (.of (R i))) j units)
    above opens covering affine
    (reconstructionAugmentationWitnessMap_familySpec (F := Cellular.homDiagram ℂ P ⋙ Ψ)
      R X (tensorLeft L) n β j units)
    width retained
  (reconstructionAffineTopCondition_nativeScalar_iff X Φ (Cellular.homDiagram ℂ P)
    (fun i => (j i).opensRange) (tensorLeft L) n width retained τ).mpr
    (reconstructionAffineTopCondition_of_augmentationWitness
      X (fun i => Spec (.of (R i))) j (fun i => (j i).opensRange)
      (Cellular.homDiagram ℂ P) Ψ (tensorLeft L) n width retained β units core)

end ToricPower

end

