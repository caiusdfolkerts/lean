module

public import ToricPower.SubfanOldFaceIntersections
public import ToricPower.FanLiftedConeProfiles

/-!
# A lifted cone meets old lifted cones along its exact old face

The proof combines the genuine intersection theorem for positive lifts
with the old-ray retraction in the quotient. No additional geometric
intersection assumption is imposed on the chosen integral lifts.
-/

@[expose] public noncomputable section
open TauCeti.Toric
namespace ToricPower.FanSubdivision

variable {P V W : Type*} [AddCommGroup P]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  {j : P →+ W} (fan extension : Fan j) (included : fan.cones ⊆ extension.cones)
  (regular : extension.IsRegular) (full : IsFullOnRays fan extension)
  (a : V) (lifts : extension.Ray → V) (projection : V →ₗ[ℝ] W)
  (kernelVector : projection a = 0)
  (projects : ∀ ρ, projection (lifts ρ) = fanRayRealVector extension ρ)

include kernelVector projects in
theorem liftedCone_inf_oldFace_eq (σ : extension.cones) (τ : fan.cones) :
    liftedCone extension a lifts σ ⊓
        liftedCone extension a lifts (subfanConeEmbedding fan extension included τ) =
      liftedCone extension a lifts
          (subfanConeEmbedding fan extension included
            (subfanOldRayFace fan extension regular full σ)) ⊓
        liftedCone extension a lifts (subfanConeEmbedding fan extension included τ) := by
  rw [liftedCone_inf extension a lifts projection kernelVector projects,
    liftedCone_inf extension a lifts projection kernelVector projects]
  apply congrArg (liftedCone extension a lifts)
  apply Subtype.ext
  exact subfanOldRayFace_inf_old fan extension included regular full σ τ

end ToricPower.FanSubdivision
end

