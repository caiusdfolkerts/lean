module

public import ToricPower.ArrangementCellularAffineSections
public import ToricPower.ArrangementInverseExteriorLabels
public import ToricPower.ToricCanonicalInverseFrames
public import ToricPower.SchemeTensorFrameSections
public import ToricPower.CellularRealizationCoefficientGenerators

/-!
# Actual affine sections of the represented tensor source

The specified inverse-right Cartier frame removes the original tensor
factor on each affine chart. The genuine coefficient comparison then
identifies the entire source complex with the unrestricted Laurent
cellular complex. No quasi-isomorphism is assumed in this definition.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open TauCeti.Toric TauCeti.AlgebraicGeometry.Scheme ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "Cells" => IncidenceObject A
local notation "X" => fan.algebraicRealization
local notation "R" => arrangementDualRightCartierDiagram fan nonempty regular basis rays
local notation "Φ" => arrangementCellularSheafRealization fan nonempty regular basis rays

/-- The exact inverse of the original right Cartier frame, followed
by the actual inverse-coefficient equality. -/
def arrangementInverseRightAffineFrame (σ : fan.cones) (c : Cells) :
    𝟙_ (fan.affineToricChart σ).Modules ≅
      ((R).obj c).restrict (fan.affineToricChartι σ) := by
  letI := toricSchemeIntegral fan nonempty
  exact toricCartierCanonicalInverseAffineFrame fan nonempty regular
      (diagonalRightCoefficients fan basis rays c.2) σ ≪≫
    (Scheme.Modules.restrictFunctor (fan.affineToricChartι σ)).mapIso
      (ToricMonomial.inverseCoefficientIso fan nonempty regular
        (diagonalRightCoefficients fan basis rays c.2))

/-- Actual scalar sections of the original tensor source are the
full represented Laurent complex, including all differentials. -/
def arrangementRepresentedTensorSectionsIso (σ : fan.cones) (c : Cells) :
    ((FiniteCover.schemeBaseSections ℂ X (fan.affineToricChartι σ).opensRange).mapHomologicalComplex
      (.up ℕ)).obj
        (((tensorRight ((R).obj c)).mapHomologicalComplex (.up ℕ)).obj
          ((Φ).obj (Cellular.representable ℂ c))) ≅
      representableLaurentCellularComplex A (fanConeRaySet fan rays σ) ℂ c :=
  (schemeTensorFrameComplexGlobalSectionsIso (fan.affineToricChartι σ) ((R).obj c)
      (arrangementInverseRightAffineFrame fan nonempty regular basis rays σ c)
      ℂ (.up ℕ)).app ((Φ).obj (Cellular.representable ℂ c)) ≪≫
    ((FiniteCover.schemeBaseSections ℂ X
      (fan.affineToricChartι σ).opensRange).mapHomologicalComplex (.up ℕ)).mapIso
      (arrangementCellularUnderlyingIso fan nonempty regular basis rays
        (Cellular.representable ℂ c)).symm ≪≫
    arrangementRepresentableAffineSectionsIso fan nonempty regular basis rays σ c

end ToricPower

end
