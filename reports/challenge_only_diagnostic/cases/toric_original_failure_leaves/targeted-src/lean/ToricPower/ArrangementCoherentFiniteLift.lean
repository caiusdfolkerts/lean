module

public import ToricPower.ArrangementCoherentFinite
public import ToricPower.CellularFiniteDerivedCategory

/-! # The actual finite incidence lift of bounded coherent complexes -/

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

local instance arrangementCoherentLiftInstance1 : IsNoetherian fan.algebraicRealization := toricScheme_isNoetherian fan
local instance arrangementCoherentLiftInstance2 : HasDerivedCategory.{1} (Coh fan.algebraicRealization) := HasDerivedCategory.standard _
local instance arrangementCoherentLiftInstance3 : HasDerivedCategory.{1} (QCoh fan.algebraicRealization) := HasDerivedCategory.standard _
local instance arrangementCoherentLiftInstance4 : HasDerivedCategory.{1} (Cell ⥤ ModuleCat.{0} ℂ) := HasDerivedCategory.standard _

/-- The finite-model property is proved by actual coherent cohomology
and actual bounded truncation, for every original coherent complex. -/
def arrangementCoherentFiniteDiagram :
    DbCoh fan.algebraicRealization ⥤ Cellular.FiniteDerivedDiagrams ℂ (C := Cell) :=
  (Cellular.finiteInjectiveModels ℂ).lift (iCoh ⋙ Bcell)
    (arrangementNormalizedCoherent_finiteModel fan regular basis rays complete)

instance arrangementCoherentFiniteDiagram_commShift :
    (arrangementCoherentFiniteDiagram fan regular basis rays complete).CommShift ℤ := by
  unfold arrangementCoherentFiniteDiagram
  infer_instance

instance arrangementCoherentFiniteDiagram_isTriangulated :
    (arrangementCoherentFiniteDiagram fan regular basis rays complete).IsTriangulated := by
  unfold arrangementCoherentFiniteDiagram
  infer_instance

instance arrangementCoherentFiniteDiagram_linear :
    (arrangementCoherentFiniteDiagram fan regular basis rays complete).Linear ℂ where
  map_smul f a := by
    apply ObjectProperty.hom_ext
    exact CategoryTheory.Functor.map_smul (iCoh ⋙ Bcell) a f

/-- The lift retains the original actual derived object and map. This
whole-functor comparison is used when transporting signed pairings. -/
def arrangementCoherentFiniteDiagramInclusionIso :
    arrangementCoherentFiniteDiagram fan regular basis rays complete ⋙
      Cellular.finiteDerivedInclusion ℂ (C := Cell) ≅ iCoh ⋙ Bcell := Iso.refl _


end ToricPower
end
