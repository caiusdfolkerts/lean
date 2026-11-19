module

public import ToricPower.ArrangementCoherentFiniteLift
public import ToricPower.CellularFiniteHomotopyModel

/-! # The genuine ambient inverse-Serre functor on bounded coherent complexes -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  [nonempty : Nonempty fan.cones] (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (complete : fan.IsComplete)

local notation "X" => fan.algebraicRealization
local notation "Cell" => IncidenceObject (fanArrangementMatrix fan basis rays)
local notation "D" => DerivedQCoh fan.algebraicRealization
local notation "Bcell" => arrangementNormalizedDerivedHom fan regular basis rays
local notation "Acell" => arrangementNormalizedDerivedRealization fan regular basis rays
local notation "iCoh" => boundedCoherentToQuasicoherent fan.algebraicRealization

local instance arrangementCoherentInverseFunctorInstance1 : IsNoetherian fan.algebraicRealization := toricScheme_isNoetherian fan
local instance arrangementCoherentInverseFunctorInstance2 : HasDerivedCategory.{1} (Coh fan.algebraicRealization) := HasDerivedCategory.standard _
local instance arrangementCoherentInverseFunctorInstance3 : HasDerivedCategory.{1} (QCoh fan.algebraicRealization) := HasDerivedCategory.standard _
local instance arrangementCoherentInverseFunctorInstance4 : HasDerivedCategory.{1} (Cell ⥤ ModuleCat.{0} ℂ) := HasDerivedCategory.standard _

/-- This is an ambient-valued exact functor on the literal `DbCoh`.
No essential-image or perfect-category identification is assumed. -/
def arrangementCoherentInverseSerre : DbCoh fan.algebraicRealization ⥤ D :=
  (arrangementCoherentFiniteDiagram fan regular basis rays complete ⋙
    Cellular.finiteInverseNakayama ℂ (C := Cell)) ⋙ Acell

instance arrangementCoherentInverseSerre_commShift :
    (arrangementCoherentInverseSerre fan regular basis rays complete).CommShift ℤ := by
  unfold arrangementCoherentInverseSerre
  infer_instance

instance arrangementCoherentInverseSerre_isTriangulated :
    (arrangementCoherentInverseSerre fan regular basis rays complete).IsTriangulated := by
  unfold arrangementCoherentInverseSerre
  infer_instance


end ToricPower
end
