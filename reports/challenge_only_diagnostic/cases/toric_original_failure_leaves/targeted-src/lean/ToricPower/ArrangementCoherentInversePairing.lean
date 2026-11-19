module

public import ToricPower.ArrangementCoherentInverseFunctor
public import ToricPower.CellularInverseSerreLift
public import ToricPower.InverseSerreAdjunction

/-! # The actual all-unbounded geometric inverse-Serre pairing -/

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

local instance arrangementCoherentPairingInstance1 : IsNoetherian fan.algebraicRealization := toricScheme_isNoetherian fan
local instance arrangementCoherentPairingInstance2 : HasDerivedCategory.{1} (Coh fan.algebraicRealization) := HasDerivedCategory.standard _
local instance arrangementCoherentPairingInstance3 : HasDerivedCategory.{1} (QCoh fan.algebraicRealization) := HasDerivedCategory.standard _
local instance arrangementCoherentPairingInstance4 : HasDerivedCategory.{1} (Cell ⥤ ModuleCat.{0} ℂ) := HasDerivedCategory.standard _

variable (fullyFaithful : (arrangementNormalizedDerivedHom fan regular basis rays).FullyFaithful)


include fullyFaithful in
/-- The exact pairing direction remains valid for every unbounded `E`. -/
def arrangementCoherentInverseSerreEquiv
    (G : DbCoh fan.algebraicRealization) (E : D) :
    (E ⟶ (boundedCoherentToQuasicoherent fan.algebraicRealization).obj G) ≃ₗ[ℂ]
      Module.Dual ℂ ((arrangementCoherentInverseSerre fan regular basis rays complete).obj G ⟶ E) := by
  letI : (arrangementNormalizedDerivedHom fan regular basis rays).Full := fullyFaithful.full
  letI : (arrangementNormalizedDerivedHom fan regular basis rays).Faithful := fullyFaithful.faithful
  exact SerrePairing.adjunctionTransferredPairing ℂ
    (arrangementNormalizedDerivedAdjunction fan regular basis rays) iCoh
    (arrangementCoherentFiniteDiagram fan regular basis rays complete ⋙
      Cellular.finiteInverseNakayama ℂ (C := Cell))
    (fun G E => Cellular.liftedHomotopyInverseSerreEquiv ℂ
      (arrangementCoherentFiniteDiagram fan regular basis rays complete) (iCoh ⋙ Bcell)
      (arrangementCoherentFiniteDiagramInclusionIso fan regular basis rays complete) G E) G E


theorem arrangementCoherentInverseSerreEquiv_source_naturality
    (G : DbCoh fan.algebraicRealization) {E F : D} (a : E ⟶ F)
    (f : F ⟶ (boundedCoherentToQuasicoherent fan.algebraicRealization).obj G)
    (g : (arrangementCoherentInverseSerre fan regular basis rays complete).obj G ⟶ E) :
    arrangementCoherentInverseSerreEquiv fan regular basis rays complete fullyFaithful G E (a ≫ f) g =
      arrangementCoherentInverseSerreEquiv fan regular basis rays complete fullyFaithful G F f (g ≫ a) := by
  letI : (arrangementNormalizedDerivedHom fan regular basis rays).Full := fullyFaithful.full
  letI : (arrangementNormalizedDerivedHom fan regular basis rays).Faithful := fullyFaithful.faithful
  apply SerrePairing.adjunctionTransferredPairing_source_naturality
  intro H Y Z a f g
  exact Cellular.liftedHomotopyInverseSerreEquiv_source_naturality ℂ
    (arrangementCoherentFiniteDiagram fan regular basis rays complete) (iCoh ⋙ Bcell)
    (arrangementCoherentFiniteDiagramInclusionIso fan regular basis rays complete) H a f g


theorem arrangementCoherentInverseSerreEquiv_target_naturality
    {G H : DbCoh fan.algebraicRealization} (a : G ⟶ H) (E : D)
    (f : E ⟶ (boundedCoherentToQuasicoherent fan.algebraicRealization).obj G)
    (g : (arrangementCoherentInverseSerre fan regular basis rays complete).obj H ⟶ E) :
    arrangementCoherentInverseSerreEquiv fan regular basis rays complete fullyFaithful H E
        (f ≫ (boundedCoherentToQuasicoherent fan.algebraicRealization).map a) g =
      arrangementCoherentInverseSerreEquiv fan regular basis rays complete fullyFaithful G E f
        ((arrangementCoherentInverseSerre fan regular basis rays complete).map a ≫ g) := by
  letI : (arrangementNormalizedDerivedHom fan regular basis rays).Full := fullyFaithful.full
  letI : (arrangementNormalizedDerivedHom fan regular basis rays).Faithful := fullyFaithful.faithful
  apply SerrePairing.adjunctionTransferredPairing_target_naturality
  intro G H a Y f g
  exact Cellular.liftedHomotopyInverseSerreEquiv_target_naturality ℂ
    (arrangementCoherentFiniteDiagram fan regular basis rays complete) (iCoh ⋙ Bcell)
    (arrangementCoherentFiniteDiagramInclusionIso fan regular basis rays complete) a Y f g



end ToricPower
end
