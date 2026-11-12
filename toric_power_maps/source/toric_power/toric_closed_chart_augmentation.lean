module

public import ToricPower.ToricClosedDualAugmentationValue
public import ToricPower.ToricClosedScalarSectionMaps
public import ToricPower.ClosedDualCoefficientCoordinates
public import ToricPower.ClosedContravariantAugmentation
public import ToricPower.ArrangementConstantAugmentationNaturality

/-! # The actual closed-slice chart augmentation is a quasi-isomorphism

The proof identifies the original map on every Laurent vertex with the
complete component augmentation.  All integral affine components are
retained, and the target is the genuine restricted Cartier section
module, with its original character coefficients.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TauCeti.Toric
open ToricPower.IntegralArrangement
open scoped Classical

namespace ToricPower

universe v w

variable {N : Type} {V : Type v} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i) [nonempty : Nonempty fan.cones]
  (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (σ : fan.cones) (W : LinearSubspace fan)
  (spans : Submodule.span ℝ (σ.val : Set V) = W.space) (b : fan.Ray → ℤ)
  {B : Type w} [Preorder B] (charts : B ⥤ fan.cones) (τ : B)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "C" => IncidenceObject A
local notation "selected" => fanConeSliceRows fan rays σ
local notation "S" => fanConeRaySet fan rays (charts.obj τ)
local notation "coeff" => fun r => b (rays r)
local notation "cover" => toricClosedDualCoverage fan regular basis rays σ W spans
local notation "Yfan" => restrictedFan fan W.space W.rational
local notation "regY" => restrictedFan_isRegular fan regular W.space W.rational
local notation "coeffY" => restrictedFanRayCoefficients fan W.space W.rational b
local notation "D" => dualToricSectionsDiagram fan regular basis rays b (charts.obj τ)
local notation "T" => CategoryTheory.Functor.obj (toricCartierSectionDiagram (Yfan)
  (linearSubspaceChartFunctor fan W charts) regY coeffY) (op τ)

local instance closedChartAugmentationSourceIntegral : IsIntegral fan.algebraicRealization :=
  toricSchemeIntegral fan nonempty
local instance closedChartAugmentationTargetNonempty :
    Nonempty (restrictedFan fan W.space W.rational).cones :=
  restrictedFanConesNonempty fan nonempty W.space W.rational
local instance closedChartAugmentationTargetIntegral :
    IsIntegral (restrictedFan fan W.space W.rational).algebraicRealization :=
  toricSchemeIntegral _ (restrictedFanConesNonempty fan nonempty W.space W.rational)
local instance closedChartAugmentationProofFintype (c : IncidenceObject A) :
    Fintype (PLift (closedIntegralRowsSupport A selected c)) := Fintype.ofFinite _

def toricClosedChartCoefficientAugmentation :
    Cellular.closedContravariantLabels (closedIntegralRowsSupport A selected)
      (closedIntegralRowsSupport_incidence A selected) D ⟶
      (Functor.const Cᵒᵖ).obj T :=
  Cellular.closedContravariantAugmentation (closedIntegralRowsSupport A selected)
    (closedIntegralRowsSupport_incidence A selected) D T
    (fun c h => (toricClosedScalarSectionMap fan regular basis rays σ W spans b charts c h).app (op τ))
    (fun f h => by
      have same := NatTrans.congr_app
        (toricClosedScalarSectionMap_incidence fan regular basis rays σ W spans b charts f h) (op τ)
      exact same)

def toricClosedChartCoefficientIso :
    Cellular.closedContravariantLabels (closedIntegralRowsSupport A selected)
      (closedIntegralRowsSupport_incidence A selected) D ≅
      closedDualLaurentDiagram A selected S coeff ℂ :=
  (Cellular.closedContravariantLabelEndofunctor (closedIntegralRowsSupport A selected)
      (closedIntegralRowsSupport_incidence A selected)).mapIso
        (dualToricSectionsDiagramIso fan regular basis rays b (charts.obj τ)).symm ≪≫
    closedDualCoefficientDiagramIso A selected S coeff ℂ

@[reassoc]
theorem toricClosedChartCoefficientAugmentation_inclusion (c : IncidenceObject A)
    (h : closedIntegralRowsSupport A selected c) :
    biproduct.ι (fun _ : PLift (closedIntegralRowsSupport A selected c) => (D).obj (op c)) ⟨h⟩ ≫
      (toricClosedChartCoefficientAugmentation fan regular basis rays σ W spans b charts τ).app (op c) =
      (toricClosedScalarSectionMap fan regular basis rays σ W spans b charts c h).app (op τ) :=
  Cellular.closedContravariantAugmentation_inclusion (closedIntegralRowsSupport A selected)
    (closedIntegralRowsSupport_incidence A selected) D T
    (fun c h => (toricClosedScalarSectionMap fan regular basis rays σ W spans b charts c h).app (op τ))
    (fun f h => NatTrans.congr_app
      (toricClosedScalarSectionMap_incidence fan regular basis rays σ W spans b charts f h) (op τ))
    c h

def toricClosedChartAugmentation :
    arrangementCellularChainComplex A ℂ
      (Cellular.closedContravariantLabels (closedIntegralRowsSupport A selected)
        (closedIntegralRowsSupport_incidence A selected) D) ⟶
      (ChainComplex.single₀ (ModuleCat.{0} ℂ)).obj T :=
  cellularConstantAugmentation A ℂ _ T
    (toricClosedChartCoefficientAugmentation fan regular basis rays σ W spans b charts τ)

theorem toricClosedChartCoefficient_generator (c : IncidenceObject A)
    (p : ClosedDualLaurentCellIndex A selected S coeff c) (r : ℂ) :
    (toricClosedChartCoefficientAugmentation fan regular basis rays σ W spans b charts τ).app (op c)
      ((toricClosedChartCoefficientIso fan regular basis rays σ b charts τ).inv.app (op c)
        (Finsupp.single p r)) =
      toricDivisorSectionCoefficientsEquiv (Yfan)
        (restrictedFanConesNonempty fan nonempty W.space W.rational) regY coeffY
        (linearSubspaceChart fan W (charts.obj τ))
        (Finsupp.single
          (toricClosedScalarWeightMap fan regular basis rays σ W spans b c p.1.down (charts.obj τ)
            (dualToricWeightEquiv fan basis rays b c (charts.obj τ) p.2)) r) := by
  have coordinates :
      (closedDualCoefficientCoordinates A selected S coeff ℂ c).symm (Finsupp.single p r) =
      biproduct.ι (fun _ : PLift (closedIntegralRowsSupport A selected c) =>
        (dualLaurentDiagram A S coeff ℂ).obj (op c)) p.1 (Finsupp.single p.2 r) := by
    apply (closedDualCoefficientCoordinates A selected S coeff ℂ c).injective
    rw [LinearEquiv.apply_symm_apply,closedDualCoefficientCoordinates_inclusion_single]
    rfl
  change (toricClosedChartCoefficientAugmentation fan regular basis rays σ W spans b charts τ).app (op c)
    (biproduct.map (fun _ : PLift (closedIntegralRowsSupport A selected c) =>
      (dualToricSectionsLinearEquiv fan regular basis rays b c (charts.obj τ)).toModuleIso.hom)
      ((closedDualCoefficientCoordinates A selected S coeff ℂ c).symm
        (Finsupp.single p r))) = _
  rw [coordinates]
  erw [← ModuleCat.comp_apply
    (biproduct.ι (fun _ : PLift (closedIntegralRowsSupport A selected c) =>
      (dualLaurentDiagram A S coeff ℂ).obj (op c)) p.1)
    (biproduct.map (fun _ : PLift (closedIntegralRowsSupport A selected c) =>
      (dualToricSectionsLinearEquiv fan regular basis rays b c (charts.obj τ)).toModuleIso.hom))
    (Finsupp.single p.2 r),biproduct.ι_map,ModuleCat.comp_apply]
  erw [← ModuleCat.comp_apply]
  erw [Category.assoc,toricClosedChartCoefficientAugmentation_inclusion
    fan regular basis rays σ W spans b charts τ c p.1.down]
  change (toricClosedScalarSectionMap fan regular basis rays σ W spans b charts c p.1.down).app (op τ)
    (toricDivisorSectionCoefficientsEquiv fan nonempty regular
      (b-arrangementDualLeftCoefficients fan basis rays c) (charts.obj τ)
      ((Finsupp.domLCongr (R := ℂ) (dualToricWeightEquiv fan basis rays b c (charts.obj τ)))
        (Finsupp.single p.2 r))) = _
  rw [Finsupp.domLCongr_single,toricClosedScalarSectionMap_coefficients,Finsupp.mapDomain_single]

theorem toricClosedChartAugmentation_comparison :
    (arrangementCellularChainFunctor A ℂ).map
        (toricClosedChartCoefficientIso fan regular basis rays σ b charts τ).inv ≫
        toricClosedChartAugmentation fan regular basis rays σ W spans b charts τ =
      closedDualCellularAugmentation A selected S coeff cover ℂ ≫
        (ChainComplex.single₀ (ModuleCat.{0} ℂ)).map
          (toricClosedDualAugmentationSectionsIso fan regular basis rays σ W spans b (charts.obj τ)).hom := by
  unfold toricClosedChartAugmentation
  rw [cellularConstantAugmentation_precompose]
  apply (ChainComplex.toSingle₀Equiv _ T).injective
  apply Subtype.ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨p,rfl⟩ := (closedDualCellularCoordinates A selected S coeff ℂ 0).symm.surjective x
  induction p using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add p q hp hq =>
    simpa only [map_add] using congrArg₂ (·+·) hp hq
  | single p r =>
    change (cellularConstantAugmentation A ℂ (closedDualLaurentDiagram A selected S coeff ℂ) T _).f 0
      ((closedDualCellularCoordinates A selected S coeff ℂ 0).symm (Finsupp.single p r)) = _
    refine (cellularConstantAugmentation_free_generator A ℂ
      (closedDualLaurentDiagram A selected S coeff ℂ)
      (ClosedDualLaurentCellIndex A selected S coeff) (fun _ => LinearEquiv.refl ℂ _)
      T ((toricClosedChartCoefficientIso fan regular basis rays σ b charts τ).inv ≫
        toricClosedChartCoefficientAugmentation fan regular basis rays σ W spans b charts τ)
      p.1 p.2 r).trans ?_
    change (toricClosedChartCoefficientAugmentation fan regular basis rays σ W spans b charts τ).app (op ⟨0,p.1⟩)
      ((toricClosedChartCoefficientIso fan regular basis rays σ b charts τ).inv.app (op ⟨0,p.1⟩)
        (Finsupp.single p.2 r)) =
      (toricClosedDualAugmentationSectionsIso fan regular basis rays σ W spans b (charts.obj τ)).hom
        ((closedDualCellularAugmentation A selected S coeff cover ℂ).f 0
          ((closedDualCellularCoordinates A selected S coeff ℂ 0).symm (Finsupp.single p r)))
    exact (toricClosedChartCoefficient_generator fan regular basis rays σ W spans b charts τ
      ⟨0,p.1⟩ p.2 r).trans
        (toricClosedDualAugmentationSectionsIso_generator fan regular basis rays σ W spans b
          (charts.obj τ) p r).symm

instance toricClosedChartAugmentation_quasiIso :
    QuasiIso (toricClosedChartAugmentation fan regular basis rays σ W spans b charts τ) := by
  haveI : QuasiIso
      ((arrangementCellularChainFunctor A ℂ).map
        (toricClosedChartCoefficientIso fan regular basis rays σ b charts τ).inv ≫
        toricClosedChartAugmentation fan regular basis rays σ W spans b charts τ) := by
    rw [toricClosedChartAugmentation_comparison]
    infer_instance
  exact quasiIso_of_comp_left
    ((arrangementCellularChainFunctor A ℂ).map
      (toricClosedChartCoefficientIso fan regular basis rays σ b charts τ).inv) _

end ToricPower

end
