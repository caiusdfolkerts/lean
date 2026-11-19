module

public import ToricPower.DerivedComplexIntertwining
public import ToricPower.PowerProjectiveComplexComparison
public import ToricPower.ArrangementPowerChartDiagram
public import ToricPower.ToricPowerPullbackExact
public import ToricPower.DiagramProjectiveCechDerived
public import ToricPower.LinearHomComplexExact
public import ToricPower.CechPosetContraction

/-!
# The power comparison for the full unbounded finite Čech model

The finite projective chart model is a genuine functor on unbounded
complexes. The natural power comparison is first proved for those
complexes and then lifted through the actual derived localization.
No boundedness or finite-dimensionality condition is imposed on the
input quasicoherent complex.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 600000
set_option maxRecDepth 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "Cells" => IncidenceObject A
local notation "X" => fan.algebraicRealization
local notation "Q" => QCoh X
set_option quotPrecheck false in
local notation "J" => (ToricMeetChartIndex fan)ᵒᵖ ⥤ ModuleCat.{0} ℂ
local notation "H" => normalizedCartierChartDiagram fan nonempty regular basis rays
local notation "P" => (FiniteCech.finiteTupleResolution (B := ToricMeetChartIndex fan) ℂ)

local instance chartCoefficients_AB4 : AB4OfSize.{0} J where
  ofShape _ := inferInstance

/-- The literal signed finite-source Hom complex at every incidence label. -/
def normalizedCartierFiniteComplexModel :
    CochainComplex Q ℤ ⥤ CochainComplex (Cells ⥤ ModuleCat.{0} ℂ) ℤ :=
  diagramProjectiveCoefficientComplexFunctor ℂ H P

/-- The natural comparison on actual unbounded complexes. -/
def normalizedCartierPowerComplexIso (ell : ℕ) (positive : 0 < ell) :
    letI := toricPowerMap_finite fan regular ell positive
    normalizedCartierFiniteComplexModel fan nonempty regular basis rays ⋙
        (powerDiagramPushdown A ell positive (ModuleCat.{0} ℂ)).mapHomologicalComplex (.up ℤ) ≅
      (quasicoherentPullback (toricPowerMap fan ell)).mapHomologicalComplex (.up ℤ) ⋙
        normalizedCartierFiniteComplexModel fan nonempty regular basis rays := by
  letI := toricPowerMap_finite fan regular ell positive
  exact powerProjectiveCoefficientComplexIso A ell positive ℂ H
    (quasicoherentPullback (toricPowerMap fan ell)) P
    (normalizedCartierPowerChartIso fan nonempty regular basis rays ell positive)

local instance normalizedPowerModel_derivedQCoh : HasDerivedCategory.{1} Q := HasDerivedCategory.standard _
local instance normalizedPowerModel_derivedCharts : HasDerivedCategory.{1} J := HasDerivedCategory.standard _
local instance normalizedPowerModel_derivedCells : HasDerivedCategory.{1} (Cells ⥤ ModuleCat.{0} ℂ) := HasDerivedCategory.standard _

local instance normalizedPowerChartLimits : PreservesFiniteLimits H :=
  (normalizedCartierChartDiagram_exact fan nonempty regular basis rays).1
local instance normalizedPowerChartColimits : PreservesFiniteColimits H :=
  (normalizedCartierChartDiagram_exact fan nonempty regular basis rays).2

/-- Localization of the actual full finite-source model. -/
def normalizedCartierFiniteModel :
    DerivedCategory Q ⥤ DerivedCategory (Cells ⥤ ModuleCat.{0} ℂ) :=
  diagramProjectiveCoefficientDerived ℂ H P

def normalizedCartierFiniteModelFactors :
    DerivedCategory.Q ⋙ normalizedCartierFiniteModel fan nonempty regular basis rays ≅
      normalizedCartierFiniteComplexModel fan nonempty regular basis rays ⋙ DerivedCategory.Q :=
  diagramProjectiveCoefficientDerivedFactors ℂ H P

/-- The complete derived power comparison, for every unbounded input. -/
def normalizedCartierPowerDerivedIso (ell : ℕ) (positive : 0 < ell) :
    letI := toricPowerMap_finite fan regular ell positive
    letI := toricPowerPullback_preservesFiniteLimits fan regular ell positive
    normalizedCartierFiniteModel fan nonempty regular basis rays ⋙
        powerDerivedPushdown A ell positive ℂ ≅
      (quasicoherentPullback (toricPowerMap fan ell)).mapDerivedCategory ⋙
        normalizedCartierFiniteModel fan nonempty regular basis rays := by
  letI := toricPowerMap_finite fan regular ell positive
  letI := toricPowerPullback_preservesFiniteLimits fan regular ell positive
  exact derivedComplexIntertwiningIso
    (normalizedCartierFiniteComplexModel fan nonempty regular basis rays)
    (normalizedCartierFiniteModel fan nonempty regular basis rays)
    (normalizedCartierFiniteModelFactors fan nonempty regular basis rays)
    (quasicoherentPullback (toricPowerMap fan ell))
    (powerDiagramPushdown A ell positive (ModuleCat.{0} ℂ))
    (normalizedCartierPowerComplexIso fan nonempty regular basis rays ell positive)


end ToricPower

end
