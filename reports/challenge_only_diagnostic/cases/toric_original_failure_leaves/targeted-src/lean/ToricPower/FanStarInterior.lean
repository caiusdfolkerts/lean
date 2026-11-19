module

public import ToricPower.FanStarCoverage
public import ToricPower.FanRayCoordinates

/-!
# Complete ray stars give actual interior points of the fan support

There are finitely many cones containing the ray. In each of them, the
coordinate of its primitive vector equals one at that vector. The
intersection of their strictly positive coordinate halfspaces is an
open neighbourhood. The quotient-star coverage condition proves that
this neighbourhood is contained in the support.
-/

@[expose] public noncomputable section

open TauCeti.Toric Set
namespace ToricPower.FanSubdivision

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (fan : Fan i) (regular : fan.IsRegular)

include regular in
theorem localFanRayCoordinates_ray (ρ : fan.Ray) (σ : fan.cones)
    (member : fanRayRealVector fan ρ ∈ σ.val) :
    localFanRayCoordinates fan σ (fanRayRealVector fan ρ) = Finsupp.single ρ 1 := by
  classical
  apply fanRayProfile_unique fan regular
    (localFanRayCoordinates_profile fan regular σ member)
  refine ⟨?_,ρ.toCone,?_,?_⟩
  · intro τ
    by_cases same : τ = ρ
    · simp [same]
    · simp [Finsupp.single_apply,same]
  · intro τ supported
    have same : τ = ρ := by
      by_contra different
      have nonzero := Finsupp.mem_support_iff.mp supported
      exact nonzero (by simp [Finsupp.single_apply,different])
    subst τ
    exact le_rfl
  · simp [fanRayCombination]

section Topology

variable [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul ℝ V] [T2Space V]

include regular in
theorem ray_mem_interior_support_of_starCovers (ρ : fan.Ray)
    (covers : RayStarCovers fan (fanRayRealVector fan ρ)) :
    fanRayRealVector fan ρ ∈ interior fan.support := by
  classical
  letI := fan.lattice.finiteDimensional
  let a := fanRayRealVector fan ρ
  let starCones := {σ : fan.cones // a ∈ σ.val}
  let neighbourhood : Set V :=
    ⋂ σ : starCones, {x : V | 0 < localFanRayCoordinates fan σ.val x ρ}
  have openNeighbourhood : IsOpen neighbourhood := by
    apply isOpen_iInter_of_finite
    intro σ
    exact isOpen_lt continuous_const
      (((Finsupp.lapply ρ : (fan.Ray →₀ ℝ) →ₗ[ℝ] ℝ).comp
        (localFanRayCoordinates fan σ.val)).continuous_of_finiteDimensional)
  have containsRay : a ∈ neighbourhood := by
    apply mem_iInter.mpr
    intro σ
    change 0 < localFanRayCoordinates fan σ.val a ρ
    rw [localFanRayCoordinates_ray fan regular ρ σ.val σ.property]
    simp
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (openNeighbourhood.mem_nhds containsRay)
  intro x belongs
  obtain ⟨σ,rayMember,t,translated⟩ := covers x
  have coefficients := (mem_cone_iff_localFanRayCoordinates fan regular σ
    (x+t•a)).mp translated
  have rayCoordinates : localFanRayCoordinates fan σ a = Finsupp.single ρ 1 :=
    localFanRayCoordinates_ray fan regular ρ σ rayMember
  have nonnegative : ∀ τ, 0 ≤ localFanRayCoordinates fan σ x τ := by
    intro τ
    by_cases same : τ = ρ
    · subst τ
      exact (mem_iInter.mp belongs (⟨σ,rayMember⟩ : starCones)).le
    · have value := coefficients.1 τ
      simpa only [map_add,map_smul,rayCoordinates,Finsupp.add_apply,Finsupp.smul_apply,
        Finsupp.single_apply,if_neg same,if_neg (Ne.symm same),smul_zero,add_zero] using value
  have evaluate : fanRayCombination fan (localFanRayCoordinates fan σ x) = x := by
    have value := coefficients.2
    have singleValue : fanRayCombination fan (Finsupp.single ρ 1) = a := by
      simp [fanRayCombination,a]
    rw [map_add,map_smul,rayCoordinates,map_add,map_smul,singleValue] at value
    exact add_right_cancel value
  exact (Fan.mem_support fan).mpr
    ⟨σ.val,σ.property,(mem_cone_iff_localFanRayCoordinates fan regular σ x).mpr
      ⟨nonnegative,evaluate⟩⟩

end Topology
end ToricPower.FanSubdivision
end

