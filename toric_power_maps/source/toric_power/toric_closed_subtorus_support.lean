module

public import ToricPower.ToricClosedLinearSlice
public import ToricPower.ArrangementClosedSubtorus

/-! # The closed row support is the actual connected character subtorus

The primitive vectors of a regular cone extend to an integral basis.
Consequently simultaneous integer row values lift to one full integral
character, without a finite-index substitution. The corresponding
coefficient diagram is therefore supported precisely on the image of
the actual annihilator modulo the full character lattice.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays

theorem characterCoordinateEquiv_latticeLift (a : Fin n → ℤ) :
    characterCoordinateEquiv fan.lattice basis (latticeLift a) =
      fan.lattice.realCharacter (basis.equivFun.symm a) := by
  rw [characterCoordinateEquiv_apply,Module.Basis.equivFun_symm_apply,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_zsmul]
  exact Int.cast_smul_eq_zsmul ℝ (a j) (fan.lattice.realCharacter (basis j))

/-- The true preimage of the annihilator subtorus in full real character
coordinates, before choosing a quotient presentation. -/
def toricClosedSubtorusPreimage (W : Submodule ℝ V) : Set (Fin n → ℝ) :=
  {x | ∃ a : Fin n → ℤ, x - latticeLift a ∈ fanCharacterAnnihilator fan basis W}

theorem toricClosedSubtorusPreimage_iff_rows (regular : fan.IsRegular)
    (σ : fan.cones) (W : Submodule ℝ V)
    (spans : Submodule.span ℝ (σ.val : Set V) = W) (x : Fin n → ℝ) :
    x ∈ toricClosedSubtorusPreimage fan basis W ↔
      ∀ j ∈ fanConeSliceRows fan rays σ, ∃ z : ℤ, augmentedForms A j x = (z : ℝ) := by
  constructor
  · rintro ⟨a,shift⟩ j ⟨ρ,rfl⟩
    let v := primitiveGenerator fan.lattice (fan.isToricCone σ.property) ρ
    have inW : i v ∈ W := by
      rw [← spans]
      exact Submodule.subset_span
        (ρ.val.isFaceOf.le (primitiveGenerator_mem fan.lattice (fan.isToricCone σ.property) ρ))
    have shifted : characterCoordinateEquiv fan.lattice basis (x-latticeLift a) ∈
        W.dualAnnihilator := shift
    have zero := ((Submodule.mem_dualAnnihilator
      (characterCoordinateEquiv fan.lattice basis (x-latticeLift a))).mp shifted) (i v) inW
    rw [map_sub,characterCoordinateEquiv_latticeLift fan basis,LinearMap.sub_apply,
      fan.lattice.realCharacter_apply] at zero
    refine ⟨basis.equivFun.symm a v,?_⟩
    rw [← characterCoordinateEquiv_primitive fan basis rays,
      fanRayPrimitiveGenerator_ofToricRay]
    exact sub_eq_zero.mp zero
  · intro integral
    obtain ⟨m,agrees⟩ := regularCone_realCharacter_agrees_on_span fan.lattice
      (regularFanCone fan regular σ) (characterCoordinateEquiv fan.lattice basis x)
      (fun ρ => by
        obtain ⟨z,hz⟩ := integral _ (Set.mem_range_self ρ)
        refine ⟨z,?_⟩
        rw [← characterCoordinateEquiv_primitive fan basis rays,
          fanRayPrimitiveGenerator_ofToricRay] at hz
        exact hz)
    refine ⟨basis.equivFun m,?_⟩
    change characterCoordinateEquiv fan.lattice basis
      (x-latticeLift (basis.equivFun m)) ∈ W.dualAnnihilator
    rw [Submodule.mem_dualAnnihilator]
    intro v hv
    rw [map_sub,characterCoordinateEquiv_latticeLift fan basis,LinearEquiv.symm_apply_apply,
      LinearMap.sub_apply,agrees v (spans.symm ▸ hv),sub_self]

/-- The actual closed constant coefficient diagram has precisely the
subtorus support claimed in the paper; all lattice components are checked. -/
theorem closedIntegralRowsSupport_iff_toricSubtorus (regular : fan.IsRegular)
    (σ : fan.cones) (W : Submodule ℝ V)
    (spans : Submodule.span ℝ (σ.val : Set V) = W) (c : IncidenceObject A) :
    closedIntegralRowsSupport A (fanConeSliceRows fan rays σ) c ↔
      cellCenter (augmentedForms A) c.2.val ∈ toricClosedSubtorusPreimage fan basis W :=
  (closedIntegralRowsSupport_iff_integer A (fanConeSliceRows fan rays σ) c).trans
    (toricClosedSubtorusPreimage_iff_rows fan basis rays regular σ W spans _).symm

end ToricPower

end
