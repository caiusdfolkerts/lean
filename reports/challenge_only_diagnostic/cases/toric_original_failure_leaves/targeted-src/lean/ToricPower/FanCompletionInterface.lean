module

public import ToricPower.FanRayIndex
public import TauCeti.Geometry.Toric.Algebraic.Regular

/-!
# The geometric data of a relative smooth divisorial completion

All fans in this interface use the original integral lattice and real
ambient vector space. The additional ray condition says that the old
fan is the full subfan on its old rays. Consequently the missing rays,
rather than higher-codimension strata alone, account for the boundary.

This file specifies the actual geometric output and proves elementary
consequences. It makes no existence assertion: existence requires the
relative completion and subdivision construction.
-/

@[expose] public noncomputable section

open TauCeti.Toric
namespace ToricPower

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

/-- A complete regular extension with a divisorial complement. Every
field concerns actual cones of the original and extending fans. -/
structure SmoothDivisorialCompletion (original : Fan i) where
  fan : Fan i
  contains : original.cones ⊆ fan.cones
  regular : fan.IsRegular
  complete : fan.IsComplete
  oldRayClosed : ∀ (σ : PointedCone ℝ V), σ ∈ fan.cones →
    (∀ ρ : ToricRay σ, ρ.toPointedCone ∈ original.cones) → σ ∈ original.cones

namespace SmoothDivisorialCompletion

variable {original : Fan i} (completion : SmoothDivisorialCompletion original)

/-- For an extending cone, membership in the original fan is exactly
the condition that all of its actual rays were present originally. -/
theorem mem_original_iff (σ : completion.fan.cones) :
    σ.val ∈ original.cones ↔
      ∀ ρ : ToricRay σ.val, ρ.toPointedCone ∈ original.cones := by
  constructor
  · intro member ρ
    exact original.mem_of_isFaceOf member ρ.1.isFaceOf
  · exact completion.oldRayClosed σ.val σ.property

/-- The equivalent formulation using globally indexed fan rays. -/
theorem mem_original_of_global_rays (σ : completion.fan.cones)
    (old : ∀ ρ : completion.fan.Ray,
      ρ.toCone.val ≤ σ.val → ρ.toCone.val ∈ original.cones) :
    σ.val ∈ original.cones := by
  apply completion.oldRayClosed σ.val σ.property
  intro ρ
  exact old (Fan.Ray.ofToricRay completion.fan σ ρ) ρ.1.isFaceOf.le

/-- The extending fan is nonempty whenever the original fan is. -/
instance [Nonempty original.cones] : Nonempty completion.fan.cones := by
  obtain ⟨σ⟩ := ‹Nonempty original.cones›
  exact ⟨⟨σ.val, completion.contains σ.property⟩⟩

/-- An already complete regular fan supplies its own completion data. -/
def self (fan : Fan i) (regular : fan.IsRegular) (complete : fan.IsComplete) :
    SmoothDivisorialCompletion fan where
  fan := fan
  contains := fun _ member => member
  regular := regular
  complete := complete
  oldRayClosed := fun _ member _ => member

end SmoothDivisorialCompletion
end ToricPower
end

