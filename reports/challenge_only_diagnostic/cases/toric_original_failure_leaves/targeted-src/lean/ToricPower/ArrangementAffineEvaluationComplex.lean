module

public import ToricPower.ArrangementOriginalAffineUnitHom
public import ToricPower.DiagonalExteriorSectionDiagram
public import ToricPower.ArrangementCellularSectionGenerators
public import ToricPower.DiagonalInternalDual
public import ToricPower.DiagonalCellularIdentification
public import ToricPower.CellularRealizationCoefficientIso

/-!
# The actual affine evaluation complex is the actual dual diagonal

The original quasicoherent cellular complex on the Hom diagram of an
affine direct image is compared with the full scalar-section complex
of the genuine dual diagonal on the product chart. The comparison uses
all Laurent coefficients and every original incidence, with no support
truncation or boundedness of coefficient spaces.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (σ τ : fan.cones)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "Cells" => IncidenceObject A
local notation "X" => fan.algebraicRealization
local notation "Y" => toricDiagonalProduct fan
local notation "Q" => arrangementDualLeftCartierDiagram fan nonempty regular basis rays
local notation "Qq" => arrangementDualLeftQuasicoherentDiagram fan nonempty regular basis rays
local notation "R" => arrangementDualRightCartierDiagram fan nonempty regular basis rays
local notation "P₀" => arrangementRightQuasicoherentDiagram fan nonempty regular basis rays
local notation "E" => exteriorLabelDiagram fan Q R
local notation "Ring" => CommRingCat.of (DiagonalChartRing ℂ A
  (fanConeRaySet fan rays σ) (fanConeRaySet fan rays τ))
local notation "chart" => diagonalProductChartι fan basis rays σ τ
local notation "Γσ" => FiniteCover.schemeBaseSections ℂ X (Scheme.Hom.opensRange (fan.affineToricChartι σ))
local notation "Γτ" => FiniteCover.schemeBaseSections ℂ X (Scheme.Hom.opensRange (fan.affineToricChartι τ))
local notation "ΓP" => FiniteCover.schemeBaseSections ℂ (Spec Ring) ⊤
local notation "K" => diagonalGlobalInternalDualComplex fan nonempty regular basis rays
local notation "Φ" => arrangementQuasicoherentCellularRealization fan nonempty regular basis rays

local instance affineEvaluationModuleBiproducts : HasFiniteBiproducts (Y).Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts
local instance affineEvaluationChartBiproducts : HasFiniteBiproducts (Spec Ring).Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts
local instance affineEvaluationQcohBiproducts : HasFiniteBiproducts (QCoh X) :=
  HasFiniteBiproducts.of_hasFiniteProducts
local instance affineEvaluationChartAffine (κ : fan.cones) : IsAffineHom (fan.affineToricChartι κ) :=
  toricChartInclusion_isAffineHom fan κ

/-- Both inverse-label factors, with their original morphisms, describe
the entire genuine internal-dual diagonal complex. -/
def diagonalInternalDualExteriorCochainIso :
    K ≅ arrangementCellularCochainComplex A ℂ E :=
  diagonalExteriorDualComplexIso fan nonempty regular basis rays ≪≫
    (arrangementCellularCochainFunctor A ℂ).mapIso
      (diagonalExteriorCoefficientIso fan nonempty regular basis rays)

/-- The original dual diagonal on the literal product chart has the
complete copower coefficient diagram of the two affine section diagrams. -/
def diagonalInternalDualExteriorScalarIso :
    ((ΓP).mapHomologicalComplex (.up ℕ)).obj
        (((Scheme.Modules.pullback chart).mapHomologicalComplex (.up ℕ)).obj K) ≅
      arrangementCellularCochainComplex A ℂ
        (Cellular.covariantCopowerDiagram ℂ (Q ⋙ Γσ) (R ⋙ Γτ)) :=
  ((ΓP).mapHomologicalComplex (.up ℕ)).mapIso
      (((Scheme.Modules.pullback chart).mapHomologicalComplex (.up ℕ)).mapIso
        (diagonalInternalDualExteriorCochainIso fan nonempty regular basis rays)) ≪≫
    cellularCoefficientComplexIso A ℂ (Scheme.Modules.pullback chart ⋙ ΓP) E ≪≫
    (arrangementCellularCochainFunctor A ℂ).mapIso
      (diagonalExteriorSectionDiagramIso fan nonempty regular basis rays σ τ).symm

/-- The genuine cellular evaluation source, with actual affine unit
coefficients, is the actual dual-diagonal section complex. This is an
isomorphism of full complexes, before any top-homology calculation. -/
def arrangementAffineCellularCoefficientIso :
    Φ ⋙ (arrangementAffineSectionFunctor fan σ).mapHomologicalComplex (.up ℕ) ≅
      arrangementCellularRealization A ℂ (Q ⋙ Γσ) :=
  cellularRealizationCoefficientIso A ℂ (arrangementAffineSectionFunctor fan σ)
    Qq (Q ⋙ Γσ) (Iso.refl _)

/-- The entire component family, with its coefficient type fixed before
the affine-unit input is substituted. -/
def arrangementAffineCellularCoefficientComponents :
    ∀ M : Cells ⥤ ModuleCat ℂ,
      ((arrangementAffineSectionFunctor fan σ).mapHomologicalComplex (.up ℕ)).obj
        ((Φ).obj M) ≅ (arrangementCellularRealization A ℂ (Q ⋙ Γσ)).obj M :=
  specifiedFunction (arrangementAffineCellularCoefficientIso fan nonempty regular basis rays σ).app

theorem arrangementAffineCellularCoefficientComponents_eq :
    arrangementAffineCellularCoefficientComponents fan nonempty regular basis rays σ =
      (arrangementAffineCellularCoefficientIso fan nonempty regular basis rays σ).app :=
  specifiedFunction_eq _

/-- Only the original inverse-right coefficient diagram is changed. -/
def arrangementAffineUnitCoefficientCochainIso :
    (arrangementCellularRealization A ℂ (Q ⋙ Γσ)).obj
        ((Cellular.homDiagram ℂ P₀).obj
          (quasicoherentAffineUnitImage (fan.affineToricChartι τ))) ≅
      arrangementCellularCochainComplex A ℂ
        (Cellular.covariantCopowerDiagram ℂ (Q ⋙ Γσ) (R ⋙ Γτ)) :=
  (arrangementCellularRealization A ℂ (Q ⋙ Γσ)).mapIso
    (arrangementOriginalAffineUnitHomSectionsIso fan nonempty regular basis rays τ)

/-- The full affine unit specialization of the original coefficient
comparison, followed by the actual exterior-diagonal comparison. -/
def arrangementAffineEvaluationKernelIso :
    ((arrangementAffineSectionFunctor fan σ).mapHomologicalComplex (.up ℕ)).obj
        ((Φ).obj ((Cellular.homDiagram ℂ P₀).obj
          (quasicoherentAffineUnitImage (fan.affineToricChartι τ)))) ≅
      ((ΓP).mapHomologicalComplex (.up ℕ)).obj
        (((Scheme.Modules.pullback chart).mapHomologicalComplex (.up ℕ)).obj K) := by
  let M := (Cellular.homDiagram ℂ P₀).obj
    (quasicoherentAffineUnitImage (fan.affineToricChartι τ))
  exact arrangementAffineCellularCoefficientComponents fan nonempty regular basis rays σ M ≪≫
    arrangementAffineUnitCoefficientCochainIso fan nonempty regular basis rays σ τ ≪≫
    (diagonalInternalDualExteriorScalarIso fan nonempty regular basis rays σ τ).symm

end ToricPower

end
