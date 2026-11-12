module

public import ToricPower.ToricClosedDualAugmentationWeights

/-! # The complete closed-slice augmentation on original Laurent vertices

The actual component augmentation, followed by the genuine restricted
Cartier section isomorphism, sends each original vertex to precisely
its original character plus the integral trace of its cell.  This
fixes the scalar map before any quasi-isomorphism is transported.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric
open ToricPower.IntegralArrangement
open scoped Classical

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i) [nonempty : Nonempty fan.cones]
  (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (σ : fan.cones) (W : LinearSubspace fan)
  (spans : Submodule.span ℝ (σ.val : Set V) = W.space) (b : fan.Ray → ℤ)
  (τ : fan.cones)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "selected" => fanConeSliceRows fan rays σ
local notation "S" => fanConeRaySet fan rays τ
local notation "coeff" => fun r => b (rays r)
local notation "cover" => toricClosedDualCoverage fan regular basis rays σ W spans
local notation "Yfan" => restrictedFan fan W.space W.rational
local notation "regY" => restrictedFan_isRegular fan regular W.space W.rational
local notation "coeffY" => restrictedFanRayCoefficients fan W.space W.rational b

local instance closedDualAugmentationValueIntegral :
    IsIntegral (restrictedFan fan W.space W.rational).algebraicRealization :=
  toricSchemeIntegral _ (restrictedFanConesNonempty fan nonempty W.space W.rational)

def toricClosedDualGeneratorComponent {q : ℕ}
    (p : ClosedDualCellularIndex A selected S coeff q) :
    {value : IntegralSliceValue A selected // closedDualAllowedComponent A selected S coeff value} := by
  let component := closedDualLaurentComponentsEquiv A selected S coeff cover q p
  refine ⟨component.1, cellCenter (augmentedForms A) component.2.val, ?_, component.2.property.2⟩
  exact (closedIntegralLevelSlice_cell_iff A selected component.1.val component.2.val
    (cellCenter_mem _ component.2.val)).mpr component.2.property.1

theorem toricClosedDualGeneratorComponent_weight {q : ℕ}
    (p : ClosedDualCellularIndex A selected S coeff q) :
    toricClosedDualSectionWeightEquiv fan regular basis rays σ W spans b τ
      (toricClosedDualGeneratorComponent fan regular basis rays σ W spans b τ p) =
      toricClosedScalarWeightMap fan regular basis rays σ W spans b ⟨q,p.1⟩ p.2.1.down τ
        (dualToricWeightEquiv fan basis rays b ⟨q,p.1⟩ τ p.2.2) := by
  apply Subtype.ext
  change (toricClosedDualComponentCharacterEquiv fan basis rays σ W.space spans)
    (closedDualLaurentComponentsEquiv A selected S coeff cover q p).1 = _
  rw [toricClosedDualComponentCharacterEquiv_apply]
  exact toricClosedDualComponentCharacter_of_generator fan regular basis rays σ W spans b τ q p

theorem toricClosedDualAugmentationSectionsIso_monomial
    (value : {value : IntegralSliceValue A selected //
      closedDualAllowedComponent A selected S coeff value}) (r : ℂ) :
    (toricClosedDualAugmentationSectionsIso fan regular basis rays σ W spans b τ).hom
      ((Finsupp.supportedEquivFinsupp (R := ℂ)
        {value | closedDualAllowedComponent A selected S coeff value}).symm
          (Finsupp.single value r)) =
      toricDivisorSectionCoefficientsEquiv (Yfan)
        (restrictedFanConesNonempty fan nonempty W.space W.rational) regY coeffY
        (linearSubspaceChart fan W τ)
        (Finsupp.single
          (toricClosedDualSectionWeightEquiv fan regular basis rays σ W spans b τ value) r) := by
  change toricDivisorSectionCoefficientsEquiv (Yfan)
    (restrictedFanConesNonempty fan nonempty W.space W.rational) regY coeffY
    (linearSubspaceChart fan W τ)
    ((Finsupp.domLCongr (R := ℂ)
      (toricClosedDualSectionWeightEquiv fan regular basis rays σ W spans b τ))
        ((Finsupp.supportedEquivFinsupp (R := ℂ)
          {value | closedDualAllowedComponent A selected S coeff value})
            ((Finsupp.supportedEquivFinsupp (R := ℂ)
              {value | closedDualAllowedComponent A selected S coeff value}).symm
                (Finsupp.single value r)))) = _
  rw [LinearEquiv.apply_symm_apply,Finsupp.domLCongr_single]

theorem toricClosedDualAugmentationSectionsIso_generator
    (p : ClosedDualCellularIndex A selected S coeff 0) (r : ℂ) :
    (toricClosedDualAugmentationSectionsIso fan regular basis rays σ W spans b τ).hom
      ((closedDualCellularAugmentation A selected S coeff cover ℂ).f 0
        ((closedDualCellularCoordinates A selected S coeff ℂ 0).symm
          (Finsupp.single p r))) =
      toricDivisorSectionCoefficientsEquiv (Yfan)
        (restrictedFanConesNonempty fan nonempty W.space W.rational) regY coeffY
        (linearSubspaceChart fan W τ)
        (Finsupp.single
          (toricClosedScalarWeightMap fan regular basis rays σ W spans b ⟨0,p.1⟩ p.2.1.down τ
            (dualToricWeightEquiv fan basis rays b ⟨0,p.1⟩ τ p.2.2)) r) := by
  have original :
      (closedDualCellularAugmentation A selected S coeff cover ℂ).f 0
        ((closedDualCellularCoordinates A selected S coeff ℂ 0).symm
          (Finsupp.single p r)) =
      (Finsupp.supportedEquivFinsupp (R := ℂ)
        {value | closedDualAllowedComponent A selected S coeff value}).symm
          (Finsupp.single
            (toricClosedDualGeneratorComponent fan regular basis rays σ W spans b τ p) r) := by
    apply Subtype.ext
    rw [Finsupp.supportedEquivFinsupp_symm_single]
    exact closedDualCellularAugmentation_generator A selected S coeff cover ℂ p r
  rw [original,toricClosedDualAugmentationSectionsIso_monomial,
    toricClosedDualGeneratorComponent_weight]

end ToricPower

end
