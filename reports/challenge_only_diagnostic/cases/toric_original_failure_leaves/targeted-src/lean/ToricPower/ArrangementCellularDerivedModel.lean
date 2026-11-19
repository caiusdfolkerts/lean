module

public import ToricPower.ArrangementCellularTotal
public import ToricPower.ComplexFunctorDerived

/-! # The original cellular total on the full unbounded derived category -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i) [nonempty : Nonempty fan.cones]
  (regular : fan.IsRegular) {n s : ℕ}
  (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "Cells" => IncidenceObject A
local notation "X" => fan.algebraicRealization

local notation "Φ" => arrangementQuasicoherentCellularRealization fan nonempty regular basis rays
local instance cellularDerivedModelBiproducts : HasFiniteBiproducts (QCoh X) :=
  HasFiniteBiproducts.of_hasFiniteProducts
local instance cellularDerivedModelTargetDerived : HasDerivedCategory.{1} (QCoh X) :=
  HasDerivedCategory.standard _
local instance cellularDerivedModelSourceDerived :
    HasDerivedCategory.{1} (Cells ⥤ ModuleCat.{0} ℂ) := HasDerivedCategory.standard _

/-- The original finite total descends to all unbounded input objects.
The already constructed ordinary functor stays sealed during localization. -/
def arrangementCellularDerivedFunctor :
    DerivedCategory (Cells ⥤ ModuleCat.{0} ℂ) ⥤ DerivedQCoh X :=
  complexFunctorDerived (arrangementCellularTotalFunctor fan nonempty regular basis rays)
    (fun f hf => by
      letI := hf
      exact arrangementCellularTotalFunctor_map_quasiIso fan nonempty regular basis rays f)

end ToricPower

end
