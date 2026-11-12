module

public import ToricPower.FanRayCoordinates
public import TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Separation

/-!
# A strictly positive integral character on any fan cone

The zero face of a genuine toric cone is cut out by an integral character.
The character is therefore strictly positive on every primitive ray of
that cone. This discharges the interior-direction hypothesis in the
boundary case of the cellular costalk calculation. Regularity and
completeness are not needed for this step.
-/

@[expose] public noncomputable section

open TauCeti.Toric

namespace ToricPower

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

/-- The entire actual integral character lattice contains a functional
strictly positive on every ray of a chosen cone. -/
theorem fanCone_exists_strictPositive_character (fan : Fan i) (σ : fan.cones) :
    ∃ m : N →+ ℤ, ∀ ρ : fan.Ray, ρ.toCone ≤ σ →
      0 < m (fanRayPrimitiveGenerator fan ρ) := by
  obtain ⟨m, nonnegative, zeroFace⟩ :=
    (fan.isToricCone σ.property).rational.exists_mem_dualSemigroup_inf_ker_eq
      fan.lattice (fan.isToricCone σ.property).salient.bot_isFaceOf
  refine ⟨m, ?_⟩
  intro ρ contained
  have inCone : fanRayRealVector fan ρ ∈ σ.val := contained (fanRayRealVector_mem fan ρ)
  have nonnegativeValue := (mem_dualSemigroup fan.lattice m).mp nonnegative inCone
  have nonzeroValue : fan.lattice.realCharacter m (fanRayRealVector fan ρ) ≠ 0 := by
    intro zeroValue
    have inZeroFace : fanRayRealVector fan ρ ∈ σ.val ⊓
        PointedCone.ofSubmodule (LinearMap.ker (fan.lattice.realCharacter m)) := by
      exact ⟨inCone, zeroValue⟩
    rw [zeroFace] at inZeroFace
    have vector_zero : fanRayRealVector fan ρ = 0 := by simpa using inZeroFace
    have generator_nonzero : fanRayPrimitiveGenerator fan ρ ≠ 0 :=
      primitiveGenerator_ne_zero fan.lattice (fan.isToricCone ρ.toCone.property)
        (ρ.toToricRay fan ρ.toCone le_rfl)
    apply generator_nonzero
    apply fan.lattice.injective
    simpa only [fanRayRealVector, map_zero] using vector_zero
  have positiveValue := lt_of_le_of_ne nonnegativeValue (Ne.symm nonzeroValue)
  simp only [fanRayRealVector, fan.lattice.realCharacter_apply] at positiveValue
  exact_mod_cast positiveValue

end ToricPower
