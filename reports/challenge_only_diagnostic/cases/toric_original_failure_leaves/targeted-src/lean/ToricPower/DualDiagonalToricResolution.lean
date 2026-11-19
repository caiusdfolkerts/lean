module

public import ToricPower.DualDiagonalToricBoundary
public import ToricPower.DiagonalToricFrames

/-!
# The genuine dual diagonal in each toric Cartier frame

The boundary character below is the literal character used to construct
the invariant Cartier divisor with coefficient one on every ray. Its ray
equations are proved from regularity. Thus the local augmentation has no
unproved choice of a supporting character or extra full-dimension hypothesis.

The target is the ordinary intersection module expressed in this one
boundary frame. The subsequent global comparison must retain the frame
transitions; this file does not trivialize the boundary line globally.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {latticeMap : N →+ V}
  (fan : Fan latticeMap) (regular : fan.IsRegular) {n s : ℕ}
  (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (σ τ : fan.cones)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "S" => fanConeRaySet fan rays σ
local notation "T" => fanConeRaySet fan rays τ
local notation "R" => DiagonalChartRing ℂ A S T
local notation "frames" => toricDiagonalCellFrames fan regular basis rays σ τ

/-- The literal local equation of the boundary divisor on the genuine
intersection chart. -/
def diagonalBoundaryFrameCharacter : N →+ ℤ :=
  coneDivisorCharacter fan regular (fun _ => 1) (σ ⊓ τ)

theorem diagonalBoundaryFrameCharacter_ray (ρ : fan.Ray)
    (hρ : ρ.toCone ≤ σ ⊓ τ) :
    diagonalBoundaryFrameCharacter fan regular σ τ (fanRayPrimitiveGenerator fan ρ) = 1 :=
  coneDivisorCharacter_globalRay fan regular (fun _ => 1) (σ ⊓ τ) ρ hρ

/-- The independently defined boundary-weight module, identified in
the actual invariant Cartier frame. -/
def toricDualDiagonalBoundaryFrameIso :
    dualDiagonalBoundaryModule A S T ℂ ≅ diagonalIntersectionModule fan basis rays σ τ :=
  dualDiagonalBoundaryFrameModuleIso fan regular basis rays σ τ
    (diagonalBoundaryFrameCharacter fan regular σ τ)
    (diagonalBoundaryFrameCharacter_ray fan regular σ τ)

/-- The actual ring-linear dual of the original finite diagonal matrix. -/
def toricDiagonalFramedDualComplex : CochainComplex (ModuleCat R) ℕ :=
  diagonalFramedDualComplex ℂ A S T frames

/-- The actual top quotient followed by the literal boundary Cartier
frame. Every Laurent character and product-chart scalar is retained. -/
def toricDiagonalFramedDualAugmentation :
    toricDiagonalFramedDualComplex fan regular basis rays σ τ ⟶
      (HomologicalComplex.single (ModuleCat R) (.up ℕ) n).obj
        (diagonalIntersectionModule fan basis rays σ τ) :=
  diagonalFramedDualAugmentation ℂ A S T frames ≫
    (HomologicalComplex.single (ModuleCat R) (.up ℕ) n).map
      (toricDualDiagonalBoundaryFrameIso fan regular basis rays σ τ).hom

/-- Full local dual exactness, without any additional character,
completeness, or full-dimensionality hypothesis. -/
theorem toricDiagonalFramedDualAugmentation_quasiIso :
    QuasiIso (toricDiagonalFramedDualAugmentation fan regular basis rays σ τ) := by
  letI := diagonalFramedDualAugmentation_quasiIso ℂ A S T frames
  unfold toricDiagonalFramedDualAugmentation
  infer_instance

end ToricPower
