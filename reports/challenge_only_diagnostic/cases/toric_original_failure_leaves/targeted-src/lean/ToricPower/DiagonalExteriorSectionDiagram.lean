module

public import ToricPower.AffineExternalSectionDiagram
public import ToricPower.SchemeExteriorChartDiagram
public import ToricPower.ArrangementInverseExteriorLabels
public import ToricPower.DiagonalCartierFrames
public import ToricPower.SchemeRestrictionBaseSections
public import ToricPower.CovariantCopowerComparison

/-!
# The full scalar exterior diagram on the genuine toric product chart

Both factors are the actual inverse Cartier labels. The comparison is
canonical on all copower generators and retains every translated
incidence map. The freely chosen Cartier frames establish invertibility;
they do not alter the underlying exterior-section map.
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
local notation "R" => arrangementDualRightCartierDiagram fan nonempty regular basis rays
local notation "Rσ" => CommRingCat.of (affineCoordinateRing fan.lattice σ.val)
local notation "Rτ" => CommRingCat.of (affineCoordinateRing fan.lattice τ.val)
local notation "Ring" => CommRingCat.of (DiagonalChartRing ℂ A
  (fanConeRaySet fan rays σ) (fanConeRaySet fan rays τ))
local notation "chart" => diagonalProductChartι fan basis rays σ τ
local notation "Qσ" => Q ⋙ Scheme.Modules.pullback (fan.affineToricChartι σ)
local notation "Rτdiag" => R ⋙ Scheme.Modules.pullback (fan.affineToricChartι τ)
local notation "coordinate" => AlgEquiv.symm (diagonalProductCoordinateEquiv fan basis rays σ τ)
local notation "first" => affineExternalFirstMap ℂ Rσ Rτ Ring coordinate
local notation "second" => affineExternalSecondMap ℂ Rσ Rτ Ring coordinate
local notation "Γσ" => FiniteCover.schemeBaseSections ℂ X (Scheme.Hom.opensRange (fan.affineToricChartι σ))
local notation "Γτ" => FiniteCover.schemeBaseSections ℂ X (Scheme.Hom.opensRange (fan.affineToricChartι τ))
local notation "ΓP" => FiniteCover.schemeBaseSections ℂ (Spec Ring) ⊤


/-- The original two projection squares give the actual exterior
coefficient diagram on the product chart. -/
def diagonalExteriorChartDiagramIso :
    exteriorLabelDiagram fan Q R ⋙ Scheme.Modules.pullback chart ≅
      schemeExteriorDiagram first second Qσ Rτdiag :=
  schemeExteriorChartDiagramIso (toricDiagonalFirst fan) (toricDiagonalSecond fan)
    chart (fan.affineToricChartι σ) (fan.affineToricChartι τ) first second
    (diagonalFirstPullbackComparison fan basis rays σ τ)
    (diagonalSecondPullbackComparison fan basis rays σ τ) Q R

/-- The specified frames prove that the canonical exterior section
map is invertible on every coefficient, naturally in all incidences. -/
def diagonalAffineExteriorSectionDiagramIso :
    Cellular.covariantCopowerDiagram ℂ
        (Qσ ⋙ FiniteCover.schemeBaseSections ℂ (Spec Rσ) ⊤)
        (Rτdiag ⋙ FiniteCover.schemeBaseSections ℂ (Spec Rτ) ⊤) ≅
      schemeExteriorDiagram first second Qσ Rτdiag ⋙ ΓP := by
  letI := toricSchemeIntegral fan nonempty
  exact affineExternalSectionDiagramIso ℂ Rσ Rτ Ring coordinate Qσ Rτdiag
    (fun c => toricCartierPullbackFrame fan nonempty regular
      (arrangementDualLeftCoefficients fan basis rays c) σ)
    (fun c => toricCartierPullbackFrame fan nonempty regular
      (arrangementDualRightCoefficients fan basis rays c) τ)

/-- The whole section diagram, expressed on the original chart opens.
The target is the original exterior sheaf diagram pulled to the
literal product chart, with no replacement of its incidence maps. -/
def diagonalExteriorSectionDiagramIso :
    Cellular.covariantCopowerDiagram ℂ (Q ⋙ Γσ) (R ⋙ Γτ) ≅
      (exteriorLabelDiagram fan Q R ⋙ Scheme.Modules.pullback chart) ⋙ ΓP := by
  let left : Qσ ⋙ FiniteCover.schemeBaseSections ℂ (Spec Rσ) ⊤ ≅ Q ⋙ Γσ :=
    Functor.isoWhiskerLeft Q (pullbackGlobalBaseSectionsIso ℂ (fan.affineToricChartι σ))
  let right : Rτdiag ⋙ FiniteCover.schemeBaseSections ℂ (Spec Rτ) ⊤ ≅ R ⋙ Γτ :=
    Functor.isoWhiskerLeft R (pullbackGlobalBaseSectionsIso ℂ (fan.affineToricChartι τ))
  exact (Cellular.covariantCopowerLabelFunctor ℂ (R ⋙ Γτ)).mapIso left.symm ≪≫
    (Cellular.covariantCopowerFunctor ℂ
      (Qσ ⋙ FiniteCover.schemeBaseSections ℂ (Spec Rσ) ⊤)).mapIso right.symm ≪≫
    diagonalAffineExteriorSectionDiagramIso fan nonempty regular basis rays σ τ ≪≫
    Functor.isoWhiskerRight
      (diagonalExteriorChartDiagramIso fan nonempty regular basis rays σ τ).symm ΓP

end ToricPower

end
