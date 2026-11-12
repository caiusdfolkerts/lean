module

public import ToricPower.DiagonalInternalDualHomology
public import ToricPower.TopAugmentationChart

/-!
# The actual diagonal top quotient in affine coordinates

The global top-homology frame is defined by the genuine affine
augmentation. The equality below proves that it carries the original
global cochain quotient to the original local augmentation component.
Consequently later characteristic-cell calculations concern the
specified global map, rather than an arbitrary isomorphism of its
source and target.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (σ τ : fan.cones)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "S" => fanConeRaySet fan rays σ
local notation "T" => fanConeRaySet fan rays τ
local notation "U" => Spec (CommRingCat.of (DiagonalChartRing ℂ A S T))
local notation "K" => diagonalGlobalInternalDualComplex fan nonempty regular basis rays
local notation "P" => Scheme.Modules.pullback (diagonalProductChartι fan basis rays σ τ)
local notation "M" => tilde (dualDiagonalBoundaryModule A S T ℂ)

/-- In every genuine product chart, the actual global top quotient has
exactly the coordinates of the independently proved affine augmentation. -/
theorem diagonalGlobalInternalDualTopChartIso_quotient :
    (P).map ((K).pOpcycles n ≫
        ((K).isoHomologyι n (n+1) (by simp)
          (diagonalGlobalInternalDual_top_differential fan nonempty regular basis rays)).inv) ≫
      (diagonalGlobalInternalDualTopChartIso fan nonempty regular basis rays σ τ).hom =
    (diagonalGlobalInternalDualChartIso fan nonempty regular basis rays σ τ).hom.f n ≫
      singleAugmentationComponent
        (toricDiagonalInternalDualBoundaryAugmentation fan regular basis rays σ τ) := by
  letI := toricDiagonalInternalDualBoundaryAugmentation_quasiIso fan regular basis rays σ τ
  exact topAugmentationChartIso_quotient P K
    (diagonalGlobalInternalDualChartIso fan nonempty regular basis rays σ τ)
    (toricDiagonalInternalDualBoundaryAugmentation fan regular basis rays σ τ)
    (diagonalGlobalInternalDual_top_differential fan nonempty regular basis rays)

end ToricPower

end
