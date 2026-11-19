module

public import ToricPower.ArrangementRightCoefficientFunctor
public import ToricPower.ArrangementQuasicoherentLabels
public import ToricPower.CartierHomTensorSections
public import ToricPower.AffineHomUnderlyingSections
public import ToricPower.ToricAffineLabelHomExact
public import ToricPower.CellularHomAdjunction
public import ToricPower.SpecifiedIsomorphism

/-!
# Original right-label Hom coefficients on an actual affine chart

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

/-- The original inverse-right coefficient category, realized in the
actual quasicoherent category with every original monomial arrow. -/
def arrangementDualRightQuasicoherentDiagram : Cells ⥤ Q :=
  arrangementInverseRightCoefficientDiagram fan basis rays ⋙
    ToricMonomial.quasicoherent fan nonempty regular

local notation "Rq" => arrangementDualRightQuasicoherentDiagram fan nonempty regular basis rays

/-- Its underlying sheaves and maps are the original inverse-right diagram. -/
def arrangementDualRightQuasicoherentInclusionIso :
    Rq ⋙ quasicoherentInclusion X ≅ R :=
  arrangementInverseRightRealizationIso fan basis rays nonempty regular

/-- The original source is factored through its small monomial
category before passing to sheaves. The comparison retains every
specified character map. -/
def arrangementOriginalMonomialSources :
    letI := toricSchemeIntegral fan nonempty
    Cellsᵒᵖ ⥤ CartierSources X := by
  letI := toricSchemeIntegral fan nonempty
  exact arrangementRightCoefficientDiagram fan basis rays ⋙
    ToricMonomial.sources fan nonempty regular

def arrangementOriginalMonomialQuasicoherentIso :
    arrangementRightCoefficientDiagram fan basis rays ⋙
        ToricMonomial.quasicoherent fan nonempty regular ≅ P₀ :=
  Functor.fullyFaithfulCancelRight (quasicoherentInclusion X)
    (arrangementRightCoefficientRealizationIso fan basis rays nonempty regular)

/-- The complete actual inverse-tensor comparison, natural in every
coefficient sheaf and every original source incidence. -/
def arrangementOriginalInverseTensorIso :
    letI := toricSchemeIntegral fan nonempty
    ((arrangementOriginalMonomialSources fan nonempty regular basis rays).rightOp ⋙
        cartierSourcesQuasicoherentInverseTensor X).flip ≅
      (Rq ⋙ tensoringLeft Q).flip := by
  letI := toricSchemeIntegral fan nonempty
  change ((arrangementRightCoefficientDiagram fan basis rays).rightOp ⋙
      (ToricMonomial.sources fan nonempty regular).op ⋙
        cartierSourcesQuasicoherentInverseTensor X).flip ≅
    ((arrangementRightCoefficientDiagram fan basis rays).rightOp ⋙
      ToricMonomial.dual fan ⋙ ToricMonomial.quasicoherent fan nonempty regular ⋙
        tensoringLeft Q).flip
  exact (flipFunctor Cells Q Q).mapIso
    (Functor.isoWhiskerLeft (arrangementRightCoefficientDiagram fan basis rays).rightOp
      (ToricMonomial.inverseTensorQuasicoherentIso fan nonempty regular))

/-- The literal original Hom functor has the original inverse-right
section model, with both naturalities and its actual scalar action. -/
def arrangementOriginalCartierHomSectionsIso :
    Cellular.homDiagram ℂ P₀ ≅
      (Rq ⋙ tensoringLeft Q).flip ⋙
        (Functor.whiskeringRight Cells Q (ModuleCat ℂ)).obj
          (quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections ℂ X ⊤) := by
  letI := toricSchemeIntegral fan nonempty
  exact Cellular.homDiagramPrecomposeIso ℂ
      (arrangementOriginalMonomialQuasicoherentIso fan nonempty regular basis rays).symm ≪≫
    cartierHomTensorSectionsDiagramIso ℂ X
      (arrangementOriginalMonomialSources fan nonempty regular basis rays) ≪≫
    Functor.isoWhiskerRight
      (arrangementOriginalInverseTensorIso fan nonempty regular basis rays)
      ((Functor.whiskeringRight Cells Q (ModuleCat ℂ)).obj
        (quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections ℂ X ⊤))

/-- The whole evaluated family, with the ordinary tensor-section
presentation fixed before inserting an actual affine unit object. -/
def arrangementOriginalCartierHomSectionsComponents :
    ∀ M : Q, (Cellular.homDiagram ℂ P₀).obj M ≅
      Rq ⋙ tensorRight M ⋙ quasicoherentInclusion X ⋙
        FiniteCover.schemeBaseSections ℂ X ⊤ :=
  specifiedFunction (quasicoherentHomTensorSectionsIsoAt ℂ Rq (Cellular.homDiagram ℂ P₀)
    (arrangementOriginalCartierHomSectionsIso fan nonempty regular basis rays))

/-- Every component remains literally the original tensor-adjunction comparison. -/
theorem arrangementOriginalCartierHomSectionsComponents_eq :
    arrangementOriginalCartierHomSectionsComponents fan nonempty regular basis rays =
      quasicoherentHomTensorSectionsIsoAt ℂ Rq (Cellular.homDiagram ℂ P₀)
        (arrangementOriginalCartierHomSectionsIso fan nonempty regular basis rays) :=
  specifiedFunction_eq _

/-- Every inverse-right label is the actual invertible Cartier sheaf. -/
theorem arrangementDualRightQuasicoherentDiagram_invertible (c : Cells) :
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X ((Rq).obj c).obj := by
  letI := toricSchemeIntegral fan nonempty
  change TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X
    (invariantCartierDivisor fan nonempty regular
      (-diagonalRightCoefficients fan basis rays c.2)).sheaf
  exact CartierDivisor.isInvertible_sheaf _

local instance originalAffineHomChart_isAffineHom (τ : fan.cones) :
    IsAffineHom (fan.affineToricChartι τ) :=
  toricChartInclusion_isAffineHom fan τ

end ToricPower

end
