module

public import ToricPower.ToricClosedSubtorusSupport
public import ToricPower.ClosedSliceComponentCohomology
public import ToricPower.ArrangementCellularAffineSections
public import ToricPower.AffineSectionsDetection
public import ToricPower.ToricDerivedAffineCover

/-! # Actual sheaf cohomology concentration of the closed-subtorus realization

Regularity discharges the integral-component coverage hypothesis. The
scalar chart calculation applies to every parallel component and the
actual affine section comparison detects the homology sheaf globally.
The remaining identification of its top sheaf retains a separate
module-action and chart-compatibility obligation.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
open TauCeti.Toric ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "X" => fan.algebraicRealization

omit nonempty in
include regular in
/-- Every original cell on the chosen integer rows belongs to an
actual integral translate of the zero slice, with no index restriction. -/
theorem fanConeSlice_integralComponents (σ : fan.cones) {q : ℕ}
    (c : Cell (augmentedForms A) q) (selected : fanConeSliceRows fan rays σ ⊆ c.val.2) :
    ∃ a : Fin n → ℤ, cellCenter (augmentedForms A) c-latticeLift a ∈
      arrangementZeroSlice (augmentedForms A) (fanConeSliceRows fan rays σ) := by
  let W := Submodule.span ℝ (σ.val : Set V)
  have integral : ∀ j ∈ fanConeSliceRows fan rays σ,
      ∃ z : ℤ, augmentedForms A j (cellCenter (augmentedForms A) c) = (z : ℝ) := by
    intro j member
    refine ⟨c.val.1 j,?_⟩
    have point := cellCenter_mem (augmentedForms A) c j
    rwa [if_pos (selected member)] at point
  obtain ⟨a,inside⟩ :=
    (toricClosedSubtorusPreimage_iff_rows fan basis rays regular σ W rfl _).mpr integral
  refine ⟨a,?_⟩
  rw [← fanCharacterAnnihilator_eq_zeroSlice fan basis rays σ W rfl]
  exact inside

/-- The original actual quasicoherent cellular realization of the
ordinary constant diagram on the connected closed subtorus. -/
def toricClosedSliceCellularComplex (σ : fan.cones) :
    CochainComplex (QCoh X) ℕ :=
  (arrangementQuasicoherentCellularRealization fan nonempty regular basis rays).obj
    (closedIntegralRowsDiagram A (fanConeSliceRows fan rays σ) ℂ)

/-- All actual homology sheaves away from the intrinsic slice degree
vanish. The top sheaf is not replaced by its scalar dimension. -/
theorem toricClosedSliceCellular_isZero_homology (σ : fan.cones) (q : ℕ)
    (different : q ≠ Module.finrank ℝ
      (arrangementZeroSlice (augmentedForms A) (fanConeSliceRows fan rays σ))) :
    IsZero ((toricClosedSliceCellularComplex fan nonempty regular basis rays σ).homology q) := by
  apply quasicoherent_homology_isZero_of_affineSections ℂ X (toricDerivedChartOpen fan)
    (toricDerivedChartOpen_covers fan)
    (fun τ => isAffineOpen_opensRange (fan.affineToricChartι τ))
  intro τ
  exact (closedSliceCellular_isZero_homology A (fanConeSliceRows fan rays σ)
    (fanConeRaySet fan rays τ) ℂ (fun _ => 0)
    (fun c selected => fanConeSlice_integralComponents fan regular basis rays σ c selected)
    q different).of_iso
      ((HomologicalComplex.homologyFunctor (ModuleCat ℂ) (.up ℕ) q).mapIso
        (arrangementCellularAffineSectionsIso fan nonempty regular basis rays τ
          (closedIntegralRowsDiagram A (fanConeSliceRows fan rays σ) ℂ)))

end ToricPower

end
