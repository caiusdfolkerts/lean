module

public import ToricPower.FanCompletionInterface
public import ToricPower.SubfanRayRetraction

/-!
# Interface for refinement away from a prescribed regular subfan

This records the precise independent output of relative
desingularization: support is unchanged, every refined cone lies in a
coarse cone, and every cone of the prescribed subfan is retained
literally. No existence theorem is asserted here. The final divisorial
condition is separate, because ordinary relative regular refinement
does not by itself prove that the old subfan is full on its old rays.
-/

@[expose] public noncomputable section
open TauCeti.Toric
namespace ToricPower

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

/-- An actual regular refinement which leaves a prescribed subfan's
cones unchanged. All fans remain in the original integral lattice. -/
structure RelativeRegularFanRefinement (original coarse : Fan i) where
  fan : Fan i
  regular : fan.IsRegular
  retains : original.cones ⊆ fan.cones
  refines : ∀ σ ∈ fan.cones, ∃ τ ∈ coarse.cones, σ ≤ τ
  support_eq : fan.support = coarse.support

namespace RelativeRegularFanRefinement

variable {original coarse : Fan i} (refinement : RelativeRegularFanRefinement original coarse)

theorem complete_iff : refinement.fan.IsComplete ↔ coarse.IsComplete := by
  constructor
  · intro complete
    apply (Fan.isComplete_iff coarse).mpr
    intro x
    have member := (Fan.mem_support refinement.fan).mpr
      ((Fan.isComplete_iff refinement.fan).mp complete x)
    rw [refinement.support_eq] at member
    exact (Fan.mem_support coarse).mp member
  · intro complete
    apply (Fan.isComplete_iff refinement.fan).mpr
    intro x
    have member := (Fan.mem_support coarse).mpr ((Fan.isComplete_iff coarse).mp complete x)
    rw [← refinement.support_eq] at member
    exact (Fan.mem_support refinement.fan).mp member

/-- Once the genuine full-on-old-rays subdivision has been proved,
the relative refinement supplies exactly the completion interface
needed by the geometric boundary argument. -/
def toDivisorialCompletion (complete : coarse.IsComplete)
    (full : IsFullOnRays original refinement.fan) : SmoothDivisorialCompletion original where
  fan := refinement.fan
  contains := refinement.retains
  regular := refinement.regular
  complete := refinement.complete_iff.mpr complete
  oldRayClosed := (isFullOnRays_iff_local original refinement.fan).mp full

end RelativeRegularFanRefinement

/-- The dimension-zero base case of the completion induction. -/
theorem fan_isComplete_of_rank_zero (fan : Fan i) (nonempty : fan.cones.Nonempty)
    (rankZero : Module.finrank ℤ N = 0) : fan.IsComplete := by
  letI := fan.lattice.finiteDimensional
  have dimensionZero : Module.finrank ℝ V = 0 := fan.lattice.finrank_eq.symm.trans rankZero
  letI : Subsingleton V := Module.finrank_zero_iff.mp dimensionZero
  rw [Fan.isComplete_iff]
  intro x
  obtain ⟨σ,member⟩ := nonempty
  refine ⟨⊥,fan.bot_mem member,?_⟩
  rw [Subsingleton.elim x 0]
  exact Submodule.zero_mem _

def rankZeroDivisorialCompletion (fan : Fan i) (nonempty : fan.cones.Nonempty)
    (regular : fan.IsRegular) (rankZero : Module.finrank ℤ N = 0) :
    SmoothDivisorialCompletion fan :=
  SmoothDivisorialCompletion.self fan regular (fan_isComplete_of_rank_zero fan nonempty rankZero)

end ToricPower
end

