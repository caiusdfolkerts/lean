module

public import ToricPower.ArrangementOriginalAffineHom
public import ToricPower.SpecifiedIsomorphism

/-!
# Original right-label Hom coefficients on the actual affine unit

The unshifted Cartier Hom diagram on the actual direct image of the
unit is the full affine section diagram of the original inverse-right
labels. All source incidences and actual character maps are retained.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TauCeti.Toric TauCeti.AlgebraicGeometry.Scheme ToricPower.IntegralArrangement


namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "Cells" => IncidenceObject A
local notation "X" => fan.algebraicRealization
local notation "Q" => QCoh X
local notation "P₀" => arrangementRightQuasicoherentDiagram fan nonempty regular basis rays
local notation "R" => arrangementDualRightCartierDiagram fan nonempty regular basis rays

local instance originalAffineUnitHomChart_isAffineHom (τ : fan.cones) :
    IsAffineHom (fan.affineToricChartι τ) :=
  toricChartInclusion_isAffineHom fan τ

/-- Evaluate the complete original Hom comparison before changing
its actual tensor-section target. -/
def arrangementOriginalHomUnitTensorIso (τ : fan.cones) :
    (Cellular.homDiagram ℂ P₀).obj
        (quasicoherentAffineUnitImage (fan.affineToricChartι τ)) ≅
      arrangementDualRightQuasicoherentDiagram fan nonempty regular basis rays ⋙
        tensorRight (quasicoherentAffineUnitImage (fan.affineToricChartι τ)) ⋙
        quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections ℂ X ⊤ :=
  arrangementOriginalCartierHomSectionsComponents fan nonempty regular basis rays
    (quasicoherentAffineUnitImage
      (fan.affineToricChartι τ))

/-- The genuine projection formula on the actual inverse-right diagram. -/
def arrangementInverseRightOpenUnitSectionsIso (τ : fan.cones) :=
  quasicoherentOpenUnitSectionsIso ℂ
    (fan.affineToricChartι τ)
    (arrangementDualRightQuasicoherentDiagram fan nonempty regular basis rays)
    (arrangementDualRightQuasicoherentDiagram_invertible fan nonempty regular basis rays)

/-- Original underlying labels after the actual section functor. -/
def arrangementUnderlyingRightSectionsIso (τ : fan.cones) :=
  Functor.isoWhiskerRight
    (arrangementDualRightQuasicoherentInclusionIso fan nonempty regular basis rays)
    (FiniteCover.schemeBaseSections ℂ X (fan.affineToricChartι τ).opensRange)

/-- On the actual affine-open direct image of the unit, the original
Hom diagram is the full original inverse-right Laurent section diagram. -/
def arrangementOriginalAffineUnitHomSectionsIso (τ : fan.cones) :=
  specifiedIsoTrans
    (arrangementOriginalHomUnitTensorIso fan nonempty regular basis rays τ)
    (specifiedIsoTrans
      (arrangementInverseRightOpenUnitSectionsIso fan nonempty regular basis rays τ)
      (arrangementUnderlyingRightSectionsIso fan nonempty regular basis rays τ))

end ToricPower

end
