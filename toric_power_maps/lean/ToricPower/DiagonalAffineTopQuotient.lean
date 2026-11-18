module

public import ToricPower.DualDiagonalToricSheafResolution
public import ToricPower.DualDiagonalFramedTopGenerators
public import ToricPower.AffineFreeDualGeneratorMap
public import ToricPower.AffineTildeAugmentationComponent

/-!
# The original affine dual augmentation on its original free generators

The affine internal-dual augmentation was constructed from the actual
ring-linear dual quotient. The equality below retains that construction
and identifies its original characteristic-cell maps before pullback.
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
  [Module ℝ V] {i : N →+ V} (fan : Fan i) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (σ τ : fan.cones)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "S" => fanConeRaySet fan rays σ
local notation "T" => fanConeRaySet fan rays τ
local notation "R" => DiagonalChartRing ℂ A S T
local notation "U" => Spec (CommRingCat.of R)
local notation "frames" => toricDiagonalCellFrames fan regular basis rays σ τ
local notation "M" => dualDiagonalBoundaryModule A S T ℂ

local instance affineTopQuotientCellsFintype (q : ℕ) : Fintype (NormalizedCell A q) := Fintype.ofFinite _
local instance affineTopQuotientBiproducts : HasFiniteBiproducts (U).Modules := HasFiniteBiproducts.of_hasFiniteProducts

set_option maxHeartbeats 800000 in
/-- The affine sheaf augmentation retains the original ring-linear
quotient, through its specified actual internal-dual comparison. -/
theorem toricDiagonalInternalDualBoundaryAugmentation_component :
    (toricDiagonalFramedDualInternalIso fan regular basis rays σ τ).hom.f n ≫
      singleAugmentationComponent
        (toricDiagonalInternalDualBoundaryAugmentation fan regular basis rays σ τ) =
      tilde.map (diagonalFramedDualTopQuotient ℂ A S T frames) := by
  rw [toricDiagonalInternalDualBoundaryAugmentation,
    singleAugmentationComponent_comp]
  have inverse : (toricDiagonalFramedDualInternalIso fan regular basis rays σ τ).hom.f n ≫
      (toricDiagonalFramedDualInternalIso fan regular basis rays σ τ).inv.f n = 𝟙 _ :=
    congrArg (fun f => f.f n)
      (toricDiagonalFramedDualInternalIso fan regular basis rays σ τ).hom_inv_id
  rw [← Category.assoc
    ((toricDiagonalFramedDualInternalIso fan regular basis rays σ τ).hom.f n),
    inverse, Category.id_comp]
  rw [affineTildeSingleAugmentation_component]
  congr 1
  simp only [singleAugmentationComponent, diagonalFramedDualAugmentation, augmentationOfTopHomology,
    HomologicalComplex.mkHomToSingle_f, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rfl

/-- The actual scalar map contributed by one original inverse cell. -/
def toricDiagonalTopGeneratorMap (c : NormalizedCell A n) :
    ModuleCat.of R R ⟶ diagonalIntersectionModule fan basis rays σ τ :=
  finiteFreeDualGeneratorMap (CommRingCat.of R) (NormalizedCell A n) c ≫
    diagonalFramedDualTopQuotient ℂ A S T frames ≫
      (toricDualDiagonalBoundaryFrameIso fan regular basis rays σ τ).hom

end ToricPower

end
