module

public import ToricPower.ToricClosedDualSectionWeights
public import ToricPower.ToricClosedScalarWeights
public import ToricPower.ClosedDualFullAugmentationCoordinates
public import ToricPower.ArrangementClosedDualCoefficients
public import ToricPower.ToricSubspaceLineSheaf

/-! # Original augmentation components and their genuine restricted weights

Every original Laurent vertex belongs to its actual integral affine
slice. The character of this component is exactly its original Laurent
character plus the supported cell's trace character. This identifies the
canonical augmentation with the original section map, including its
normalization and every parallel component.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i) [nonempty : Nonempty fan.cones]
  (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (σ : fan.cones) (W : LinearSubspace fan)
  (spans : Submodule.span ℝ (σ.val : Set V) = W.space) (b : fan.Ray → ℤ)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "selected" => fanConeSliceRows fan rays σ
local notation "Yfan" => restrictedFan fan W.space W.rational
local notation "regY" => restrictedFan_isRegular fan regular W.space W.rational
local notation "coeff" => restrictedFanRayCoefficients fan W.space W.rational b

include regular spans in
theorem toricClosedDualCoverage {q : ℕ} (c : Cell (augmentedForms A) q)
    (active : selected ⊆ c.val.2) :
    ∃ a : Fin n → ℤ, cellCenter (augmentedForms A) c-latticeLift a ∈
      arrangementZeroSlice (augmentedForms A) selected := by
  have integral : ∀ j ∈ selected, ∃ z : ℤ,
      augmentedForms A j (cellCenter (augmentedForms A) c) = (z : ℝ) := by
    intro j hj
    refine ⟨c.val.1 j,?_⟩
    have value := cellCenter_mem (augmentedForms A) c j
    simpa only [if_pos (active hj)] using value
  obtain ⟨a,ha⟩ := (toricClosedSubtorusPreimage_iff_rows fan basis rays regular σ
    W.space spans (cellCenter (augmentedForms A) c)).mpr integral
  rw [fanCharacterAnnihilator_eq_zeroSlice fan basis rays σ W.space spans] at ha
  exact ⟨a,ha⟩

theorem toricClosedDualComponentValue_of_generator (τ : fan.cones) (q : ℕ)
    (p : ClosedDualCellularIndex A selected (fanConeRaySet fan rays τ)
      (fun r => b (rays r)) q) :
    (closedDualLaurentComponentsEquiv A selected (fanConeRaySet fan rays τ)
      (fun r => b (rays r)) (toricClosedDualCoverage fan regular basis rays σ W spans) q p).1 =
      integralSliceValueOfLattice A selected
        (p.2.2.val + toricClosedRowLift fan regular basis rays σ W.space spans ⟨q,p.1⟩ p.2.1.down) := by
  apply Subtype.ext
  funext j
  change p.1.val.val.1 j.val + augmentedLatticePairing A p.2.2.val j.val =
    augmentedLatticePairing A
      (p.2.2.val + toricClosedRowLift fan regular basis rays σ W.space spans ⟨q,p.1⟩ p.2.1.down) j.val
  rw [augmentedLatticePairing_add,Pi.add_apply,toricClosedRowLift_selected]
  exact add_comm _ _

theorem toricClosedDualComponentCharacter_of_generator (τ : fan.cones) (q : ℕ)
    (p : ClosedDualCellularIndex A selected (fanConeRaySet fan rays τ)
      (fun r => b (rays r)) q) :
    toricClosedDualComponentCharacter fan basis rays σ W.space
      (closedDualLaurentComponentsEquiv A selected (fanConeRaySet fan rays τ)
        (fun r => b (rays r)) (toricClosedDualCoverage fan regular basis rays σ W spans) q p).1 =
      (basis.equivFun.symm p.2.2.val +
        toricClosedRowCharacter fan regular basis rays σ W.space spans ⟨q,p.1⟩ p.2.1.down).comp
          (latticeTrace i W.space).subtype.toAddMonoidHom := by
  rw [toricClosedDualComponentValue_of_generator,
    toricClosedDualComponentCharacter_of_lattice fan basis rays σ W.space spans]
  rw [map_add]
  rfl

local instance closedDualAugmentationSectionIntegral :
    IsIntegral (restrictedFan fan W.space W.rational).algebraicRealization :=
  toricSchemeIntegral _ (restrictedFanConesNonempty fan nonempty W.space W.rational)

def toricClosedDualAugmentationSectionsIso (τ : fan.cones) :
    closedDualAugmentationModule A selected (fanConeRaySet fan rays τ)
      (fun r => b (rays r)) ℂ ≅
      (FiniteCover.schemeBaseSections ℂ (Yfan).algebraicRealization
        ((Yfan).affineToricChartι (linearSubspaceChart fan W τ)).opensRange).obj
        (invariantCartierDivisor (Yfan)
          (restrictedFanConesNonempty fan nonempty W.space W.rational) regY coeff).sheaf :=
  ((Finsupp.supportedEquivFinsupp (R := ℂ)
      {value | closedDualAllowedComponent A selected (fanConeRaySet fan rays τ)
        (fun r => b (rays r)) value}).trans
    ((Finsupp.domLCongr (R := ℂ)
      (toricClosedDualSectionWeightEquiv fan regular basis rays σ W spans b τ)).trans
      (toricDivisorSectionCoefficientsLinearEquiv (Yfan)
        (restrictedFanConesNonempty fan nonempty W.space W.rational) regY coeff
        (linearSubspaceChart fan W τ)))).toModuleIso

end ToricPower

end
