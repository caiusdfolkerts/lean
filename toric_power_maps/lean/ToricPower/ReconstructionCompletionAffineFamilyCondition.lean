module

public import ToricPower.ReconstructionCompletionAffineChartFamilyCondition
public import ToricPower.ReconstructionCompletionMappedOpenRange
public import ToricPower.ReconstructionCompletionMappedFamilyCondition

/-! # The original reconstruction condition for an affine chart family

The genuine rank-one calculation is extended to all unbounded complexes
on each chart image before any toric labels or coordinate rings are
substituted. The resulting predicate retains the original top comparison.
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
  (n : ℕ) (τ : Cellular.homDiagram ℂ P ⋙ Φ ⟶ singleCoefficient (tensorLeft L) n)
  (above : ∀ M q, n < q → IsZero ((Φ.obj M).X q))
  {A : Type*} (opens : A → X.Opens) (covering : iSup opens = ⊤)
  (affine : ∀ a, IsAffineOpen (opens a))
  (rankOne : ∀ i, QuasiIso (τ.app (quasicoherentAffineUnitImage (j i))))

local instance reconstructionAffineFamilyConditionBiproducts :
    HasFiniteBiproducts (QCoh X) := HasFiniteBiproducts.of_hasFiniteProducts

/-- The original rank-one family proves the actual all-chart, unbounded
top-comparison condition, with no reconstruction hypothesis added. -/
def reconstructionAffineFamily_topComparisonCondition
    (width : ℕ) (retained : n < width) :=
  reconstructionAffineTopCondition_of_mappedFamily X (fun i => (j i).opensRange)
    (Cellular.homDiagram ℂ P) Φ (tensorLeft L) n width retained τ
    (reconstructionMappedOpenRangeFamilyCondition (fun i => Spec (.of (R i))) X j
      (reconstructionNativeCoefficientComposition X (Cellular.homDiagram ℂ P) Φ)
      (tensorLeft L) n width retained τ
      (reconstructionAffineFamily_mappedChartCondition R X j P invertible Φ L n τ above
        opens covering affine rankOne width retained))

end ToricPower

end
