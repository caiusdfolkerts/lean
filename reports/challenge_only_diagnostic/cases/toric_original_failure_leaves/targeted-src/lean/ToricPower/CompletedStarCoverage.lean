module

public import ToricPower.CompletedStarPacking
public import ToricPower.FanStarCoverage
public import ToricPower.LiftedConeProjection

/-!
# The constructed packing really completes the selected ray star

The lower-dimensional complete fan supplies a quotient cone for every
direction. The exact image theorem for the lifted cone then produces
the required point in an actual cone of the constructed extension.
-/

@[expose] public noncomputable section

open TauCeti.Toric
namespace ToricPower.FanSubdivision

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (fan : Fan i) (regular : fan.IsRegular) (ray : fan.Ray)

local notation "a" => fanRayPrimitiveGenerator fan ray
local notation "q" => Submodule.mkQ (Submodule.span ℝ {i a})

variable (completion : SmoothDivisorialCompletion (canonicalRayStar fan ray))

theorem completedStarCone_projection (M : ℕ) (σ : completion.fan.cones) :
    PointedCone.map q (completedStarCone fan regular ray completion M σ) = σ.val := by
  apply map_liftedCone_eq completion.fan (i a)
    (fun ρ => i (completedStarRayLift fan regular ray completion M ρ)) q
    (selectedRay_projection_zero fan ray)
  intro ρ
  exact completedStarRayLift_real_projects fan regular ray completion M ρ

theorem completedStarPackedFan_starCovers (M : ℕ)
    (large : completedStarPackingThreshold fan regular ray completion ≤ M) :
    RayStarCovers (completedStarPackedFan fan regular ray completion M large) (i a) := by
  apply rayStarCovers_of_quotient_coverage _ (i a) q (Submodule.ker_mkQ _)
  intro z
  obtain ⟨δ,member,contains⟩ := (Fan.isComplete_iff _).mp completion.complete z
  let σ : completion.fan.cones := ⟨δ,member⟩
  refine ⟨⟨completedStarCone fan regular ray completion M σ,
    completedStarPackedFan_contains_lift fan regular ray completion M large σ⟩,?_,?_⟩
  · exact generator_mem_liftedCone completion.fan (i a)
      (fun ρ => i (completedStarRayLift fan regular ray completion M ρ)) σ
  · rw [completedStarCone_projection]
    exact contains

include regular completion in
/-- The genuine one-ray extension consumed by a finite iteration.
The completion of the smaller quotient star is the induction input. -/
theorem exists_regular_rayStarExtension :
    ∃ extension : Fan i, fan.cones ⊆ extension.cones ∧ extension.IsRegular ∧
      RayStarCovers extension (i a) := by
  let M := completedStarPackingThreshold fan regular ray completion
  refine ⟨completedStarPackedFan fan regular ray completion M le_rfl,
    completedStarPackedFan_contains fan regular ray completion M le_rfl,
    completedStarPackedFan_regular fan regular ray completion M le_rfl,
    completedStarPackedFan_starCovers fan regular ray completion M le_rfl⟩

end ToricPower.FanSubdivision
end

