module

public import ToricPower.FanLiftedConeProfiles

/-!
# Every quotient cone is covered by its actual positive lift

Nonnegative ray coordinates give an explicit preimage in the lifted
cone. No surjectivity on arbitrary ambient points or regularity
assumption is substituted for the required cone-by-cone equality.
-/

@[expose] public noncomputable section
open TauCeti.Toric
namespace ToricPower.FanSubdivision

variable {P V W : Type*} [AddCommGroup P]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  {j : P →+ W} (fan : Fan j) (a : V) (lifts : fan.Ray → V)
  (projection : V →ₗ[ℝ] W) (kernelVector : projection a = 0)
  (projects : ∀ ρ, projection (lifts ρ) = fanRayRealVector fan ρ)

include kernelVector projects in
theorem map_liftedCone_eq (σ : fan.cones) :
    PointedCone.map projection (liftedCone fan a lifts σ) = σ.val := by
  apply le_antisymm
  · intro z member
    obtain ⟨x,hx,rfl⟩ := PointedCone.mem_map.mp member
    exact liftedCone_projects_mem fan a lifts projection kernelVector projects σ hx
  · intro z member
    obtain ⟨coefficients,nonnegative,evaluate⟩ := localRay_nonnegative_representation fan σ member
    let c := extendConeRayProfile fan σ coefficients
    have cNonnegative : ∀ ρ, 0 ≤ c ρ :=
      extendConeRayProfile_nonnegative fan σ coefficients nonnegative
    have supported : rayProfileSupported fan σ c :=
      extendConeRayProfile_supported fan σ coefficients
    have value : fanRayCombination fan c = z :=
      (extendConeRayProfile_evaluate fan σ coefficients).trans evaluate
    refine PointedCone.mem_map.mpr ⟨liftedRayCombination fan lifts c,?_,?_⟩
    · exact (mem_liftedCone_iff fan a lifts σ _).mpr
        ⟨0,c,le_refl _,cNonnegative,supported,by rw [zero_smul,zero_add]⟩
    · rw [liftedRayCombination_projects fan lifts projection projects,value]

end ToricPower.FanSubdivision
end

