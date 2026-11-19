module

public import ToricPower.SubfanRayRetraction

/-!
# The old-ray face has the same intersections with every old cone

This elementary incidence statement is the precise compatibility used
when lifting a completed quotient star. It follows from actual ray
incidence and the fan intersection axiom.
-/

@[expose] public noncomputable section

open TauCeti.Toric
namespace ToricPower

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (fan extension : Fan i) (included : fan.cones ⊆ extension.cones)
  (regular : extension.IsRegular) (full : IsFullOnRays fan extension)

include included in
theorem subfanOldRayFace_inf_old (σ : extension.cones) (τ : fan.cones) :
    σ.val ⊓ τ.val = (subfanOldRayFace fan extension regular full σ).val ⊓ τ.val := by
  apply le_antisymm
  · apply fanCone_le_of_rays extension
      (σ ⊓ subfanConeEmbedding fan extension included τ)
      (subfanConeEmbedding fan extension included
        (subfanOldRayFace fan extension regular full σ ⊓ τ))
    intro ρ below
    change ρ.toCone.val ≤ σ.val ⊓ τ.val at below
    change ρ.toCone.val ≤ (subfanOldRayFace fan extension regular full σ).val ⊓ τ.val
    apply le_inf
    · apply (subfanOldRayFace_rays fan extension regular full σ ρ).mpr
      refine ⟨?_,below.trans inf_le_left⟩
      exact fan.mem_of_isFaceOf τ.property
        (extension.isFaceOf_of_le (included τ.property) ρ.toCone.property
          (below.trans inf_le_right))
    · exact below.trans inf_le_right
  · exact inf_le_inf (subfanOldRayFace_le fan extension regular full σ) le_rfl

end ToricPower
end

