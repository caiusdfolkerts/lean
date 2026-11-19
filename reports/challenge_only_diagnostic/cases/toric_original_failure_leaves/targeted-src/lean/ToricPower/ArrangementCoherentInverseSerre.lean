module

public import ToricPower.ArrangementDerivedQCohLimits
public import ToricPower.ArrangementCoherentInversePairing
public import ToricPower.CellularHomotopySerre
public import ToricPower.CellularHomotopyInverseCompact
public import ToricPower.ArrangementDerivedCoproducts
public import ToricPower.ArrangementRightAdjointCoproducts
public import ToricPower.InverseSerreAdjunction
public import ToricPower.InverseSerreGeneration
public import ToricPower.CoproductCompactAdjunction
public import ToricPower.ReflectiveCoproducts
public import ToricPower.ToricCoherentDerivedIdempotents

/-!
# The actual inverse-Serre generation bridge for complete smooth toric varieties

The source is the original bounded derived category of coherent sheaves.
The representing functor is the actual normalized realization of the
finite inverse-Nakayama model of the actual normalized right adjoint.
The pairing tests every unbounded quasicoherent derived object.

The remaining geometric reconstruction input is explicit. Arbitrary
coproduct preservation is proved using the actual finite Čech model.
The generation theorem uses detection in the geometric category;
it does not assert detection throughout the larger incidence category.
-/

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

local instance arrangementCoherentSerreInstance1 : IsNoetherian fan.algebraicRealization := toricScheme_isNoetherian fan
local instance arrangementCoherentSerreInstance2 : HasDerivedCategory.{1} (Coh fan.algebraicRealization) := HasDerivedCategory.standard _
local instance arrangementCoherentSerreInstance3 : HasDerivedCategory.{1} (QCoh fan.algebraicRealization) := HasDerivedCategory.standard _
local instance arrangementCoherentSerreInstance4 : HasDerivedCategory.{1} (Cell ⥤ ModuleCat.{0} ℂ) := HasDerivedCategory.standard _

variable (fullyFaithful : (arrangementNormalizedDerivedHom fan regular basis rays).FullyFaithful)

include regular basis rays complete fullyFaithful in
/-- Genuine finite-dimensional Hom spaces of the original bounded
coherent category, obtained through actual fully faithful embeddings. -/
theorem arrangementDbCoh_hom_finite (G H : DbCoh fan.algebraicRealization) :
    FiniteDimensional ℂ (G ⟶ H) := by
  letI : (arrangementNormalizedDerivedHom fan regular basis rays).Full := fullyFaithful.full
  letI : (arrangementNormalizedDerivedHom fan regular basis rays).Faithful := fullyFaithful.faithful
  let inclusion := toricBoundedCoherentToQuasicoherentFullyFaithful fan nonempty regular
  letI : (boundedCoherentToQuasicoherent fan.algebraicRealization).Faithful := inclusion.faithful
  let F := arrangementCoherentFiniteDiagram fan regular basis rays complete
  haveI : F.Faithful := by unfold F arrangementCoherentFiniteDiagram; infer_instance
  exact FiniteDimensional.of_injective (F.mapLinearMap ℂ) F.map_injective

/-- Compactness transfers through the original adjunction using the
proved arbitrary-coproduct preservation of its actual right adjoint. -/
theorem arrangementCoherentInverseSerre_compact (G : DbCoh fan.algebraicRealization) :
    letI := arrangementDerivedQCoh_hasCoproducts fan regular basis rays fullyFaithful
    CompactExtraction.CoproductCompact.{1,1,0}
      ((arrangementCoherentInverseSerre fan regular basis rays complete).obj G) := by
  letI := arrangementDerived_hasCoproducts (fanArrangementMatrix fan basis rays) ℂ
  letI := arrangementDerivedQCoh_hasCoproducts fan regular basis rays fullyFaithful
  exact CompactExtraction.coproductCompact_leftAdjoint
    (arrangementNormalizedDerivedAdjunction fan regular basis rays)
    (fun I family => by
      letI := arrangementNormalizedDerivedHom_preservesCoproducts
        fan regular basis rays fullyFaithful I
      infer_instance)
    (Cellular.finiteHomotopyInverseNakayama_coproductCompact ℂ (fun c : Cell => c.1)
      (fun f => incidence_dimension_le _ f)
      (fun f h => (incidence_eq_of_dimension_eq _ f h).1) n
      (fun c => cell_dimension_le _ c.2.val)
      ((arrangementCoherentFiniteDiagram fan regular basis rays complete).obj G))

include regular basis rays complete fullyFaithful in
/-- The conclusion is classical generation by the original object in
literal bounded coherent complexes. Left detection ranges over all
unbounded quasicoherent derived objects, with no ambient-diagram shortcut. -/
theorem arrangementDbCoh_generator_of_unbounded_leftDetection
    (G : DbCoh fan.algebraicRealization)
    (leftDetector : ∀ Y : D,
      (∀ (q : ℤ) (f : Y⟦q⟧ ⟶ (boundedCoherentToQuasicoherent fan.algebraicRealization).obj G), f = 0) → IsZero Y) :
    (ObjectProperty.singleton G).IsClassicalTriangulatedGenerator := by
  letI := arrangementDerivedQCoh_hasCoproducts fan regular basis rays fullyFaithful
  letI := arrangementDerivedQCoh_locallySmall fan regular basis rays fullyFaithful
  letI := toricDbCoh_isIdempotentComplete_of_countableCoproducts fan nonempty regular
  let inclusion := toricBoundedCoherentToQuasicoherentFullyFaithful fan nonempty regular
  letI : (boundedCoherentToQuasicoherent fan.algebraicRealization).Full := inclusion.full
  letI : (boundedCoherentToQuasicoherent fan.algebraicRealization).Faithful := inclusion.faithful
  letI (G H : DbCoh fan.algebraicRealization) : FiniteDimensional ℂ (G ⟶ H) :=
    arrangementDbCoh_hom_finite fan regular basis rays complete fullyFaithful G H
  exact SerrePairing.classicalGenerator_of_inverseSerre ℂ iCoh
    (arrangementCoherentInverseSerre fan regular basis rays complete)
    (arrangementCoherentInverseSerreEquiv fan regular basis rays complete fullyFaithful)
    (arrangementCoherentInverseSerreEquiv_source_naturality fan regular basis rays complete fullyFaithful)
    (arrangementCoherentInverseSerreEquiv_target_naturality fan regular basis rays complete fullyFaithful)
    (arrangementCoherentInverseSerre_compact fan regular basis rays complete fullyFaithful)
    G leftDetector

end ToricPower
end
