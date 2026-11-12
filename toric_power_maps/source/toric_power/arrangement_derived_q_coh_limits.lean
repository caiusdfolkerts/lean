module

public import ToricPower.ArrangementCoherentInverseFunctor
public import ToricPower.ArrangementDerivedCoproducts
public import ToricPower.ReflectiveCoproducts

/-! # Actual ambient coproducts supplied by geometric reconstruction -/

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

local instance arrangementDerivedQCohLimitsInstance1 : IsNoetherian fan.algebraicRealization := toricScheme_isNoetherian fan
local instance arrangementDerivedQCohLimitsInstance2 : HasDerivedCategory.{1} (Coh fan.algebraicRealization) := HasDerivedCategory.standard _
local instance arrangementDerivedQCohLimitsInstance3 : HasDerivedCategory.{1} (QCoh fan.algebraicRealization) := HasDerivedCategory.standard _
local instance arrangementDerivedQCohLimitsInstance4 : HasDerivedCategory.{1} (Cell ⥤ ModuleCat.{0} ℂ) := HasDerivedCategory.standard _

variable (fullyFaithful : (arrangementNormalizedDerivedHom fan regular basis rays).FullyFaithful)

include regular basis rays fullyFaithful in
/-- The adjunction itself constructs all actual ambient coproducts. -/
theorem arrangementDerivedQCoh_hasCoproducts : HasCoproducts.{0} D := by
  letI : (arrangementNormalizedDerivedHom fan regular basis rays).Full := fullyFaithful.full
  letI : (arrangementNormalizedDerivedHom fan regular basis rays).Faithful := fullyFaithful.faithful
  letI := arrangementDerived_hasCoproducts (fanArrangementMatrix fan basis rays) ℂ
  exact hasCoproducts_of_fullyFaithful_rightAdjoint
    (arrangementNormalizedDerivedAdjunction fan regular basis rays)

include regular basis rays fullyFaithful in
theorem arrangementDerivedQCoh_locallySmall : LocallySmall.{0} D := by
  letI : (arrangementNormalizedDerivedHom fan regular basis rays).Full := fullyFaithful.full
  letI : (arrangementNormalizedDerivedHom fan regular basis rays).Faithful := fullyFaithful.faithful
  letI := arrangementDerived_locallySmall (fanArrangementMatrix fan basis rays) ℂ
  exact locallySmall_of_faithful Bcell


end ToricPower
end
