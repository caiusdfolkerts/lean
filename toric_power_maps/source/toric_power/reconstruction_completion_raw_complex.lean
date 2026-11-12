module

public import ToricPower.ArrangementAffineEvaluationComplex
public import ToricPower.ReconstructionCompletionAffineCoefficients
public import ToricPower.ReconstructionCompletionRawSections
public import ToricPower.CellularRealizationCoefficientGenerators

/-! # Reconstruction on the actual affine chart spectra

Both section factors are taken on their original pulled-back Cartier
sheaves. This keeps the product-chart comparison free of transports
between equal open subsets.
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

local notation "A" => fanArrangementMatrix fan basis rays
local notation "C" => IncidenceObject A
local notation "X" => fan.algebraicRealization
local notation "Y" => toricDiagonalProduct fan
local notation "Q" => arrangementDualLeftCartierDiagram fan nonempty regular basis rays
local notation "Qq" => arrangementDualLeftQuasicoherentDiagram fan nonempty regular basis rays
local notation "R" => arrangementDualRightCartierDiagram fan nonempty regular basis rays
local notation "P₀" => arrangementRightQuasicoherentDiagram fan nonempty regular basis rays
local notation "Φ" => arrangementQuasicoherentCellularRealization fan nonempty regular basis rays
local notation "Ext" => exteriorLabelDiagram fan Q R

local instance reconstructionRawComplexQCohBiproducts : HasFiniteBiproducts (QCoh X) :=
  HasFiniteBiproducts.of_hasFiniteProducts
local instance reconstructionRawComplexSheafBiproducts : HasFiniteBiproducts (Y).Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts
local instance reconstructionRawComplexChartAffine (κ : fan.cones) : IsAffineHom (fan.affineToricChartι κ) :=
  toricChartInclusion_isAffineHom fan κ

variable (σ τ : fan.cones)

local notation "Qσ" => (Q ⋙ Scheme.Modules.pullback (fan.affineToricChartι σ)) ⋙
  FiniteCover.schemeBaseSections ℂ (Spec (CommRingCat.of (affineCoordinateRing fan.lattice σ.val))) ⊤
local notation "Rτ" => (R ⋙ Scheme.Modules.pullback (fan.affineToricChartι τ)) ⋙
  FiniteCover.schemeBaseSections ℂ (Spec (CommRingCat.of (affineCoordinateRing fan.lattice τ.val))) ⊤
local notation "Ring" => CommRingCat.of (DiagonalChartRing ℂ A
  (fanConeRaySet fan rays σ) (fanConeRaySet fan rays τ))
local notation "ΓP" => FiniteCover.schemeBaseSections ℂ (Spec Ring) ⊤
local notation "Pull" => Scheme.Modules.pullback (diagonalProductChartι fan basis rays σ τ)
local notation "K" => diagonalGlobalInternalDualComplex fan nonempty regular basis rays
local notation "E" => quasicoherentAffineUnitImage (fan.affineToricChartι τ)

/-- The original full diagonal complex, with both raw affine section factors. -/
def reconstructionRawDiagonalScalarIso :
    ((ΓP).mapHomologicalComplex (.up ℕ)).obj
        (((Pull).mapHomologicalComplex (.up ℕ)).obj K) ≅
      arrangementCellularCochainComplex A ℂ (Cellular.covariantCopowerDiagram ℂ Qσ Rτ) :=
  ((ΓP).mapHomologicalComplex (.up ℕ)).mapIso
      (((Pull).mapHomologicalComplex (.up ℕ)).mapIso
        (diagonalInternalDualExteriorCochainIso fan nonempty regular basis rays)) ≪≫
    cellularCoefficientComplexIso A ℂ (Pull ⋙ ΓP) Ext ≪≫
    (arrangementCellularCochainFunctor A ℂ).mapIso
      (Functor.isoWhiskerRight
        (diagonalExteriorChartDiagramIso fan nonempty regular basis rays σ τ) ΓP) ≪≫
    (arrangementCellularCochainFunctor A ℂ).mapIso
      (diagonalAffineExteriorSectionDiagramIso fan nonempty regular basis rays σ τ).symm

/-- The full cellular construction commutes with the actual raw affine sections. -/
def reconstructionRawCellularCoefficientIso :
    Φ ⋙ (reconstructionRawSectionFunctor fan σ).mapHomologicalComplex (.up ℕ) ≅
      arrangementCellularRealization A ℂ Qσ :=
  cellularRealizationCoefficientIso A ℂ (reconstructionRawSectionFunctor fan σ)
    Qq Qσ (Iso.refl _)

/-- The original component family, sealed before specializing its Hom input. -/
def reconstructionRawCellularCoefficientComponents :
    ∀ M : C ⥤ ModuleCat ℂ,
      ((reconstructionRawSectionFunctor fan σ).mapHomologicalComplex (.up ℕ)).obj
        ((Φ).obj M) ≅ (arrangementCellularRealization A ℂ Qσ).obj M :=
  specifiedFunction (fun M => cellularRealizationCoefficientObjectIso A ℂ
    (reconstructionRawSectionFunctor fan σ) Qq Qσ (Iso.refl _) M)

theorem reconstructionRawCellularCoefficientComponents_eq (M : C ⥤ ModuleCat ℂ) :
    reconstructionRawCellularCoefficientComponents fan nonempty regular basis rays σ M =
      cellularRealizationCoefficientObjectIso A ℂ
        (reconstructionRawSectionFunctor fan σ) Qq Qσ (Iso.refl _) M :=
  congrFun (specifiedFunction_eq _) M

/-- The entire original Hom coefficient, through the actual affine projection. -/
def reconstructionRawHomCochainIso :
    (arrangementCellularRealization A ℂ Qσ).obj ((Cellular.homDiagram ℂ P₀).obj E) ≅
      arrangementCellularCochainComplex A ℂ (Cellular.covariantCopowerDiagram ℂ Qσ Rτ) :=
  (arrangementCellularRealization A ℂ Qσ).mapIso
    (reconstructionAffineCoefficientIso fan nonempty regular basis rays τ)

/-- The actual cellular source is the complete original dual diagonal. -/
def reconstructionRawKernelIso :
    ((reconstructionRawSectionFunctor fan σ).mapHomologicalComplex (.up ℕ)).obj
        ((Φ).obj ((Cellular.homDiagram ℂ P₀).obj E)) ≅
      ((ΓP).mapHomologicalComplex (.up ℕ)).obj
        (((Pull).mapHomologicalComplex (.up ℕ)).obj K) :=
  reconstructionRawCellularCoefficientComponents fan nonempty regular basis rays σ
      ((Cellular.homDiagram ℂ P₀).obj E) ≪≫
    reconstructionRawHomCochainIso fan nonempty regular basis rays σ τ ≪≫
    (reconstructionRawDiagonalScalarIso fan nonempty regular basis rays σ τ).symm

end ToricPower

end
