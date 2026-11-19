module

public import ToricPower.DiagonalTopQuotient
public import ToricPower.DiagonalTopQuotientChart
public import ToricPower.DiagonalInverseCellFrames
public import ToricPower.DiagonalAffineTopQuotient

/-!
# The specified global inverse-cell quotient in an actual affine chart

This is the map-level bridge between the original global top quotient
and the independently computed scalar coefficient of its original cell.
Both frames and every comparison are retained in the displayed equality.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open TauCeti.Toric ToricPower.IntegralArrangement
open scoped Classical

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (σ τ : fan.cones)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "ChartRing" => DiagonalChartRing ℂ A (fanConeRaySet fan rays σ) (fanConeRaySet fan rays τ)
local notation "U" => Spec (CommRingCat.of ChartRing)
local notation "P" => Scheme.Modules.pullback (diagonalProductChartι fan basis rays σ τ)
local notation "M" => diagonalInverseProductSheaf fan nonempty regular basis rays

local instance inverseCellTopChartFintype : Fintype (NormalizedCell A n) := Fintype.ofFinite _
local instance inverseCellTopChartProductBiproducts : HasFiniteBiproducts (toricDiagonalProduct fan).Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts
local instance inverseCellTopChartAffineBiproducts : HasFiniteBiproducts (U).Modules := HasFiniteBiproducts.of_hasFiniteProducts

/-- The actual global map, expressed in its actual source and target
frames, is the tilde of the original computed linear coefficient map. -/
theorem diagonalInverseCellTopChartFrame (c : NormalizedCell A n) :
    (diagonalInverseCellPullbackFrame fan nonempty regular basis rays σ τ n c).hom ≫
      (P).map (diagonalInverseCellTopQuotient fan nonempty regular basis rays c) ≫
        (dualDiagonalTopChartFrame fan nonempty regular basis rays σ τ).hom =
      (tildeSelf (R := CommRingCat.of ChartRing)).inv ≫
        tilde.map (toricDiagonalTopGeneratorMap fan regular basis rays σ τ c) := by
  let inclusion := biproduct.ι (fun d : NormalizedCell A n => M d) c ≫
    (diagonalExteriorDualTermIso fan nonempty regular basis rays n).hom
  have component :
      (diagonalInverseCellPullbackFrame fan nonempty regular basis rays σ τ n c).hom ≫
        (P).map inclusion ≫
          (diagonalGlobalInternalDualChartIso fan nonempty regular basis rays σ τ).hom.f n =
      (tildeSelf (R := CommRingCat.of ChartRing)).inv ≫
        tilde.map (finiteFreeDualGeneratorMap (CommRingCat.of ChartRing) (NormalizedCell A n) c) ≫
          (affineFiniteFreeDualIso (CommRingCat.of ChartRing) (NormalizedCell A n)).hom := by
    rw [finiteFreeDualGeneratorMap_tilde]
    apply (cancel_mono
      (affineInternalDualCoordinates (CommRingCat.of ChartRing) (NormalizedCell A n)).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact diagonalInverseCellPullbackFrame_generator fan nonempty regular basis rays σ τ n c
  have quotient : diagonalInverseCellTopQuotient fan nonempty regular basis rays c =
      inclusion ≫ dualDiagonalTopQuotient fan nonempty regular basis rays := by
    exact (Category.assoc _ _ _).symm
  rw [quotient, (P).map_comp]
  simp only [dualDiagonalTopChartFrame, Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc]
  unfold dualDiagonalTopQuotient
  have chart := congrArg (fun f => f ≫
      (tilde.functor (CommRingCat.of ChartRing)).map
        (toricDualDiagonalBoundaryFrameIso fan regular basis rays σ τ).hom)
    (diagonalGlobalInternalDualTopChartIso_quotient
      fan nonempty regular basis rays σ τ)
  simp only [Category.assoc] at chart
  rw [chart]
  have componentFull := congrArg (fun f => f ≫
      singleAugmentationComponent
        (toricDiagonalInternalDualBoundaryAugmentation fan regular basis rays σ τ) ≫
      (tilde.functor (CommRingCat.of ChartRing)).map
        (toricDualDiagonalBoundaryFrameIso fan regular basis rays σ τ).hom) component
  simp only [Category.assoc] at componentFull
  rw [componentFull]
  have componentQuotient := congrArg (fun f => f ≫
      (tilde.functor (CommRingCat.of ChartRing)).map
        (toricDualDiagonalBoundaryFrameIso fan regular basis rays σ τ).hom)
    (toricDiagonalInternalDualBoundaryAugmentation_component
      fan regular basis rays σ τ)
  simp only [Category.assoc] at componentQuotient
  change (affineFiniteFreeDualIso (CommRingCat.of ChartRing)
      (NormalizedCell A n)).hom ≫
    singleAugmentationComponent
      (toricDiagonalInternalDualBoundaryAugmentation fan regular basis rays σ τ) ≫
    (tilde.functor (CommRingCat.of ChartRing)).map
      (toricDualDiagonalBoundaryFrameIso fan regular basis rays σ τ).hom = _
    at componentQuotient
  rw [componentQuotient]
  change (tildeSelf (R := CommRingCat.of ChartRing)).inv ≫
    (tilde.functor (CommRingCat.of ChartRing)).map
      (finiteFreeDualGeneratorMap (CommRingCat.of ChartRing) (NormalizedCell A n) c) ≫
    (tilde.functor (CommRingCat.of ChartRing)).map
      (diagonalFramedDualTopQuotient ℂ A
        (fanConeRaySet fan rays σ) (fanConeRaySet fan rays τ)
        (toricDiagonalCellFrames fan regular basis rays σ τ)) ≫
    (tilde.functor (CommRingCat.of ChartRing)).map
      (toricDualDiagonalBoundaryFrameIso fan regular basis rays σ τ).hom = _
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

end ToricPower

end
