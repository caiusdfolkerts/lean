module

public import ToricPower.ToricClosedScalarChartDiagrams
public import ToricPower.ClosedContravariantAugmentation
public import ToricPower.ArrangementCellularConstantAugmentation

/-! # The original closed-slice augmentation in the full chart category

The map is defined in the category of all scalar chart-section diagrams.
Consequently every chart restriction, every original cellular incidence,
and every finite biproduct boundary is retained before its
quasi-isomorphism is proved.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i) [nonempty : Nonempty fan.cones]
  (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (σ : fan.cones) (W : LinearSubspace fan)
  (spans : Submodule.span ℝ (σ.val : Set V) = W.space) (b : fan.Ray → ℤ)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "C" => IncidenceObject A
local notation "selected" => fanConeSliceRows fan rays σ
local notation "X" => fan.algebraicRealization
local notation "B" => ToricMeetChartIndex fan
local notation "S" => FiniteCech.quasicoherentMeetSections ℂ X (toricMeetChartOpenFunctor fan)
local notation "Yfan" => restrictedFan fan W.space W.rational
local notation "P" => toricDualDifferenceSectionLabels fan regular basis rays b (toricMeetConeFunctor fan)
local notation "line" => quasicoherentCartierObject X (invariantCartierDivisor fan nonempty regular b)
local notation "targetSections" => toricCartierSectionDiagram (Yfan)
  (linearSubspaceChartFunctor fan W (toricMeetConeFunctor fan))
  (restrictedFan_isRegular fan regular W.space W.rational)
  (restrictedFanRayCoefficients fan W.space W.rational b)

local instance closedScalarAugmentationIntegral : IsIntegral fan.algebraicRealization :=
  toricSchemeIntegral fan nonempty
local instance closedScalarAugmentationRestrictedNonempty :
    Nonempty (restrictedFan fan W.space W.rational).cones :=
  restrictedFanConesNonempty fan nonempty W.space W.rational
local instance closedScalarAugmentationQBiproducts : HasFiniteBiproducts (QCoh fan.algebraicRealization) :=
  HasFiniteBiproducts.of_hasFiniteProducts
local instance closedScalarAugmentationChartBiproducts :
    HasFiniteBiproducts ((ToricMeetChartIndex fan)ᵒᵖ ⥤ ModuleCat.{0} ℂ) :=
  HasFiniteBiproducts.of_hasFiniteProducts

def closedDualSectionCoefficientAugmentation :
    Cellular.closedContravariantLabels (closedIntegralRowsSupport A selected)
      (closedIntegralRowsSupport_incidence A selected) P ⟶
      (Functor.const Cᵒᵖ).obj targetSections :=
  Cellular.closedContravariantAugmentation (closedIntegralRowsSupport A selected)
    (closedIntegralRowsSupport_incidence A selected) P targetSections
    (toricClosedScalarSectionMap fan regular basis rays σ W spans b (toricMeetConeFunctor fan))
    (toricClosedScalarSectionMap_incidence fan regular basis rays σ W spans b (toricMeetConeFunctor fan))

def closedDualSectionSourceIso :
    ((S).mapHomologicalComplex (.down ℕ)).obj
      ((arrangementClosedDualFunctor fan regular basis rays selected).obj line) ≅
    arrangementCellularChainComplex A ℂ
      (Cellular.closedContravariantLabels (closedIntegralRowsSupport A selected)
        (closedIntegralRowsSupport_incidence A selected) P) :=
  cellularChainCoefficientComplexIso A ℂ S
      ((arrangementClosedDualCoefficientFunctor fan regular basis rays selected).obj line) ≪≫
    (arrangementCellularChainFunctor A ℂ).mapIso
      (Cellular.closedContravariantCoefficientIso (closedIntegralRowsSupport A selected)
        (closedIntegralRowsSupport_incidence A selected) S
        ((arrangementDualInverseTensorFunctor fan regular basis rays).flip.obj line)) ≪≫
    (arrangementCellularChainFunctor A ℂ).mapIso
      ((Cellular.closedContravariantLabelEndofunctor (closedIntegralRowsSupport A selected)
        (closedIntegralRowsSupport_incidence A selected)).mapIso
          (closedDualSourceSectionDiagramIso fan regular basis rays b))

/-- The full natural chain map used by the genuine derived Čech calculation. -/
def arrangementClosedScalarAugmentation :
    ((S).mapHomologicalComplex (.down ℕ)).obj
      ((arrangementClosedDualFunctor fan regular basis rays selected).obj line) ⟶
    (ChainComplex.single₀ (Bᵒᵖ ⥤ ModuleCat.{0} ℂ)).obj
      ((S).obj (closedDualTargetQuasicoherent fan W regular b)) :=
  (closedDualSectionSourceIso fan regular basis rays σ b).hom ≫
    cellularConstantAugmentation A ℂ _ targetSections
      (closedDualSectionCoefficientAugmentation fan regular basis rays σ W spans b) ≫
    (ChainComplex.single₀ (Bᵒᵖ ⥤ ModuleCat.{0} ℂ)).map
      (closedDualTargetSectionDiagramIso fan W regular b).inv

end ToricPower

end
