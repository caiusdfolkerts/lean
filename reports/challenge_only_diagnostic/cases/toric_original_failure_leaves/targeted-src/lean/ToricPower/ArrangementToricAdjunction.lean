module

public import ToricPower.ArrangementQuasicoherentLabels
public import ToricPower.ArrangementDerivedRealization
public import ToricPower.ToricDerivedAffineCover
public import ToricPower.CellularDerivedExactAdjunction

/-!
# An exact unbounded adjunction for the genuine toric Cartier labels

This specializes the proved coend--Hom adjunction to the full translated
incidence category and actual toric quasicoherent sheaves. The fan's own
finite affine cover discharges every local exactness hypothesis, and
cell dimension discharges the finite resolution hypothesis.

The labels here are the unshifted `L(x)`. The paper's fixed boundary
twist and dimension shift are additional normalizations; a reconstruction
equivalence is not asserted in this file.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}
  (fan : Fan i) (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "P" => arrangementRightQuasicoherentDiagram fan nonempty regular basis rays
local notation "U" => toricDerivedChartOpen fan
local notation "l" => toricDerivedChartList fan

local instance arrangementToricHasDerivedCategory :
    HasDerivedCategory.{1} (QCoh fan.algebraicRealization) := HasDerivedCategory.standard _

local instance arrangementToricDiagramHasDerivedCategory :
    HasDerivedCategory.{1} (IncidenceObject A ⥤ ModuleCat.{0} ℂ) :=
  HasDerivedCategory.standard _

local instance toricLabelLocalization_preservesFiniteLimits (cone : fan.cones) :
    PreservesFiniteLimits (quasicoherentOpenLocalization (U cone).ι ⋙ Cellular.homDiagram ℂ P) :=
  (toricDerivedLabelLocalExact fan P (fun _ => inferInstance) cone).1

local instance toricLabelLocalization_preservesFiniteColimits (cone : fan.cones) :
    PreservesFiniteColimits (quasicoherentOpenLocalization (U cone).ι ⋙ Cellular.homDiagram ℂ P) :=
  (toricDerivedLabelLocalExact fan P (fun _ => inferInstance) cone).2

/-- The actual unbounded derived coend with the unreflected Cartier labels. -/
def arrangementToricDerivedRealization :
    DerivedCategory (IncidenceObject A ⥤ ModuleCat.{0} ℂ) ⥤ DerivedQCoh fan.algebraicRealization :=
  arrangementDerivedRealization A ℂ P

/-- The actual unbounded derived Hom diagram, constructed by the fan's
literal affine cover. -/
def arrangementToricDerivedHom :
    DerivedQCoh fan.algebraicRealization ⥤ DerivedCategory (IncidenceObject A ⥤ ModuleCat.{0} ℂ) :=
  Cellular.labelRHomAffine ℂ P U l

/-- All resolution, covering, and local exactness hypotheses are
discharged for the actual fan and genuine incidence category. -/
def arrangementToricDerivedAdjunction :
    arrangementToricDerivedRealization fan nonempty regular basis rays ⊣
      arrangementToricDerivedHom fan nonempty regular basis rays :=
  Cellular.realizationAffineHomAdjunction ℂ P U l
    (mem_toricDerivedChartList fan) (toricDerivedChartOpen_covers fan)
    (n+1) (arrangementFiniteConeResolution_quasiIso A ℂ)

instance arrangementToricDerivedHom_commShift :
    (arrangementToricDerivedHom fan nonempty regular basis rays).CommShift ℤ :=
  Cellular.labelRHomAffineCommShift ℂ P U l
    (mem_toricDerivedChartList fan) (toricDerivedChartOpen_covers fan)

instance arrangementToricDerivedHom_isTriangulated :
    (arrangementToricDerivedHom fan nonempty regular basis rays).IsTriangulated :=
  affineRightDerived_isTriangulated U l
    (mem_toricDerivedChartList fan) (toricDerivedChartOpen_covers fan) (Cellular.homDiagram ℂ P)

instance arrangementToricDerivedRealization_commShift :
    (arrangementToricDerivedRealization fan nonempty regular basis rays).CommShift ℤ :=
  Cellular.realizationAffineCommShift ℂ P U l
    (mem_toricDerivedChartList fan) (toricDerivedChartOpen_covers fan)
    (n+1) (arrangementFiniteConeResolution_quasiIso A ℂ)

instance arrangementToricDerivedAdjunction_commShift :
    (arrangementToricDerivedAdjunction fan nonempty regular basis rays).CommShift ℤ :=
  Cellular.realizationAffineHomAdjunction_commShift ℂ P U l
    (mem_toricDerivedChartList fan) (toricDerivedChartOpen_covers fan)
    (n+1) (arrangementFiniteConeResolution_quasiIso A ℂ)

instance arrangementToricDerivedRealization_isTriangulated :
    (arrangementToricDerivedRealization fan nonempty regular basis rays).IsTriangulated :=
  Cellular.realizationAffine_isTriangulated ℂ P U l
    (mem_toricDerivedChartList fan) (toricDerivedChartOpen_covers fan)
    (n+1) (arrangementFiniteConeResolution_quasiIso A ℂ)

end ToricPower

end
