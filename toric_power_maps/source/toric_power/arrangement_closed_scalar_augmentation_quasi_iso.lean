module

public import ToricPower.ArrangementClosedScalarAugmentation
public import ToricPower.ToricClosedChartAugmentation
public import ToricPower.ClosedContravariantAugmentationNaturality
public import Mathlib.Algebra.Homology.Functor

/-! # The whole closed-slice chart augmentation is a quasi-isomorphism

The chain map was constructed in the actual chart-diagram category.
Evaluation carries it to the original complete-component augmentation,
whose quasi-isomorphism retains every integral slice.  Exact evaluation
therefore detects the required quasi-isomorphism of whole diagrams.
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
local notation "selected" => fanConeSliceRows fan rays σ
local notation "B" => ToricMeetChartIndex fan
local notation "charts" => toricMeetConeFunctor fan
local notation "P" => toricDualDifferenceSectionLabels fan regular basis rays b charts
local notation "D" => Cellular.closedContravariantLabels
  (closedIntegralRowsSupport A selected) (closedIntegralRowsSupport_incidence A selected) P
local notation "Yfan" => restrictedFan fan W.space W.rational
local notation "T" => toricCartierSectionDiagram (Yfan)
  (linearSubspaceChartFunctor fan W charts)
  (restrictedFan_isRegular fan regular W.space W.rational)
  (restrictedFanRayCoefficients fan W.space W.rational b)
local notation "α" => closedDualSectionCoefficientAugmentation fan regular basis rays σ W spans b

local instance closedScalarQuasiIsoSourceIntegral : IsIntegral fan.algebraicRealization :=
  toricSchemeIntegral fan nonempty
local instance closedScalarQuasiIsoTargetNonempty :
    Nonempty (restrictedFan fan W.space W.rational).cones :=
  restrictedFanConesNonempty fan nonempty W.space W.rational
local instance closedScalarQuasiIsoChartBiproducts :
    HasFiniteBiproducts ((ToricMeetChartIndex fan)ᵒᵖ ⥤ ModuleCat.{0} ℂ) :=
  HasFiniteBiproducts.of_hasFiniteProducts

theorem closedDualSectionCoefficientAugmentation_evaluation (τ : Bᵒᵖ) :
    cellularConstantCoefficientMap A ((evaluation Bᵒᵖ (ModuleCat.{0} ℂ)).obj τ) D T α =
      (Cellular.closedContravariantCoefficientIso (closedIntegralRowsSupport A selected)
        (closedIntegralRowsSupport_incidence A selected)
        ((evaluation Bᵒᵖ (ModuleCat.{0} ℂ)).obj τ) P).hom ≫
      toricClosedChartCoefficientAugmentation fan regular basis rays σ W spans b charts τ.unop := by
  let E := (evaluation Bᵒᵖ (ModuleCat.{0} ℂ)).obj τ
  apply NatTrans.ext
  funext c
  apply (cancel_epi (Cellular.closedContravariantCoefficientTermIso
    (closedIntegralRowsSupport A selected) (closedIntegralRowsSupport_incidence A selected)
    E P c).inv).mp
  change (Cellular.closedContravariantCoefficientTermIso
    (closedIntegralRowsSupport A selected) (closedIntegralRowsSupport_incidence A selected)
    E P c).inv ≫ E.map ((α).app c) =
      (Cellular.closedContravariantCoefficientTermIso
        (closedIntegralRowsSupport A selected) (closedIntegralRowsSupport_incidence A selected)
        E P c).inv ≫
      (Cellular.closedContravariantCoefficientTermIso
        (closedIntegralRowsSupport A selected) (closedIntegralRowsSupport_incidence A selected)
        E P c).hom ≫
      (toricClosedChartCoefficientAugmentation fan regular basis rays σ W spans b charts τ.unop).app c
  erw [Iso.inv_hom_id_assoc]
  apply biproduct.hom_ext'
  intro h
  simp only [← Category.assoc,Cellular.closedContravariantCoefficientTermIso,
    Functor.mapBiproduct_inv,biproduct.ι_desc]
  erw [← CategoryTheory.Functor.map_comp]
  have original := Cellular.closedContravariantAugmentation_inclusion
    (closedIntegralRowsSupport A selected) (closedIntegralRowsSupport_incidence A selected)
    P T (toricClosedScalarSectionMap fan regular basis rays σ W spans b charts)
    (toricClosedScalarSectionMap_incidence fan regular basis rays σ W spans b charts)
    c.unop h.down
  erw [original]
  exact (toricClosedChartCoefficientAugmentation_inclusion fan regular basis rays σ W spans b
    charts τ.unop c.unop h.down).symm

instance closedDualSectionConstantAugmentation_quasiIso :
    QuasiIso (cellularConstantAugmentation A ℂ D T α) := by
  rw [HomologicalComplex.quasiIso_iff_evaluation]
  intro τ
  let E := (evaluation Bᵒᵖ (ModuleCat.{0} ℂ)).obj τ
  haveI : QuasiIso
      ((E.mapHomologicalComplex (.down ℕ)).map (cellularConstantAugmentation A ℂ D T α) ≫
        (HomologicalComplex.singleMapHomologicalComplex E (.down ℕ) 0).hom.app T) := by
    rw [cellularConstantAugmentation_map]
    rw [closedDualSectionCoefficientAugmentation_evaluation]
    rw [← cellularConstantAugmentation_precompose]
    change QuasiIso
      ((cellularChainCoefficientComplexIso A ℂ E D).hom ≫
        (arrangementCellularChainFunctor A ℂ).map
          (Cellular.closedContravariantCoefficientIso (closedIntegralRowsSupport A selected)
            (closedIntegralRowsSupport_incidence A selected) E P).hom ≫
        toricClosedChartAugmentation fan regular basis rays σ W spans b charts τ.unop)
    infer_instance
  exact quasiIso_of_comp_right _
    ((HomologicalComplex.singleMapHomologicalComplex E (.down ℕ) 0).hom.app T)

/-- The original full chart-section augmentation of the actual dual
Cartier chain, with no omitted component or character. -/
instance arrangementClosedScalarAugmentation_quasiIso :
    QuasiIso (arrangementClosedScalarAugmentation fan regular basis rays σ W spans b) := by
  unfold arrangementClosedScalarAugmentation
  infer_instance

end ToricPower

end
