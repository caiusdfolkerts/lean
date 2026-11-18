module

public import ToricPower.NatDiagramDerivedCohomology
public import ToricPower.CartierMeetSingleCech
public import ToricPower.ToricCoherentCohomologyFinite
public import ToricPower.CartierDerivedTensor

/-!
# Bounded finite cohomology of actual Cartier Čech diagrams

Every label is an actual Cartier divisor and every coefficient is an
actual quasicoherent sheaf. The uniform bound uses the complete finite
cone-chart cover. On complete smooth fans, coherent coefficients give
finite-dimensional complex cohomology, including each inverse Cartier
twist. No finiteness assumption is placed on the chart-section modules.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite TauCeti.Toric
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  [nonempty : Nonempty fan.cones]

local notation "X" => fan.algebraicRealization
local instance cartierCechFiniteInstance1 : IsIntegral X := toricSchemeIntegral fan nonempty
local instance cartierCechFiniteInstance2 : IsNoetherian X := toricScheme_isNoetherian fan
local instance cartierCechFiniteInstance3 : fan.algebraicRealization.IsSeparated := fan.algebraicRealization_isSeparated
local instance cartierCechFiniteInstance4 : Fintype (ToricMeetChartIndex fan) := Fintype.ofFinite _

variable {L : Type} [Category.{0} L]
variable (labels : Lᵒᵖ ⥤ CartierSources fan.algebraicRealization)
local instance cartierCechFiniteInstance5 : HasDerivedCategory.{1} (L ⥤ ModuleCat.{0} ℂ) := HasDerivedCategory.standard _

local notation "opens" => toricMeetChartOpenFunctor fan
local notation "charts" => toricMeetChartEquiv fan

include labels nonempty

theorem toricCartierCechHomology_isZero (M : QCoh X) (degree : ℕ)
    (high : Nat.card fan.cones < degree) (l : L) :
    IsZero (((cartierLabelLinearCechDiagram ℂ X labels opens M).obj l).homology degree) := by
  let twist := ((cartierLabelTwistDiagram X labels).obj M).obj l
  letI : Subsingleton (Cohomology twist.obj degree) :=
    toricQuasicoherentCohomology_subsingleton fan twist.obj degree high
  let e := CechScalar.quasicoherentLinearCechIso ℂ X (toricMeetChartOpenFunctor fan).obj
    (toricMeetChartOpen_covers fan)
    (fun a => isAffineOpen_opensRange (fan.affineToricChartι (charts a))) twist.obj degree
  exact e.isZero_iff.mp (ModuleCat.isZero_of_subsingleton _)

theorem toricCartierCechHomology_finite (regular : fan.IsRegular)
    (complete : fan.IsComplete) (M : QCoh X) [M.obj.IsFinitePresentation]
    (degree : ℕ) (l : L) :
    FiniteDimensional ℂ
      (((cartierLabelLinearCechDiagram ℂ X labels opens M).obj l).homology degree) := by
  let twist := ((cartierLabelTwistDiagram X labels).obj M).obj l
  letI : twist.obj.IsFinitePresentation := by
    change ((-(cartierSourceDivisor X ((labels.rightOp.obj l).unop))).sheaf ⊗ M.obj).IsFinitePresentation
    exact cartierTensor_finitePresentation _ M.obj
  letI := toricCoherentCohomology_finite fan nonempty regular complete twist.obj degree
  let e := CechScalar.quasicoherentLinearCechIso ℂ X (toricMeetChartOpenFunctor fan).obj
    (toricMeetChartOpen_covers fan)
    (fun a => isAffineOpen_opensRange (fan.affineToricChartι (charts a))) twist.obj degree
  exact Module.Finite.equiv e.toLinearEquiv

/-- The entire diagram has the uniform finite-cover cohomology bound. -/
theorem toricCartierCechDerived_bounded (M : QCoh X) :
    DerivedCategory.TStructure.t.bounded
      (natDiagramDerivedObject ℂ (cartierLabelLinearCechDiagram ℂ X labels opens M)) :=
  natDiagramDerived_bounded ℂ _ (Nat.card fan.cones)
    (toricCartierCechHomology_isZero fan labels M)

/-- Coherence and completeness imply pointwise finite-dimensional
homology of the actual full derived diagram. -/
theorem toricCartierCechDerived_pointwiseFinite (regular : fan.IsRegular)
    (complete : fan.IsComplete) (M : QCoh X) [M.obj.IsFinitePresentation] :
    Cellular.pointwiseFiniteDerived ℂ
      (natDiagramDerivedObject ℂ (cartierLabelLinearCechDiagram ℂ X labels opens M)) :=
  natDiagramDerived_pointwiseFinite ℂ _
    (toricCartierCechHomology_finite fan labels regular complete M)

end ToricPower
end
