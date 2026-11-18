module

public import ToricPower.FanStarInterior
public import TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Separation

/-!
# The open support around every positive coefficient of a completed star

Completing a ray star makes every point with a positive coefficient at
that ray an interior point of the support, including points on higher
dimensional cones. Cones which do not contain the point are excluded by
actual integral separators vanishing on the selected ray.
-/

@[expose] public noncomputable section
open TauCeti.Toric Set
open scoped Classical

namespace ToricPower.FanSubdivision

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (fan : Fan i) (regular : fan.IsRegular)

include regular in
theorem mem_cone_of_ray_translate (ρ : fan.Ray) (σ : fan.cones)
    (rayMember : fanRayRealVector fan ρ ∈ σ.val) (x : V) (t : ℝ)
    (positive : 0 ≤ localFanRayCoordinates fan σ x ρ)
    (translated : x + t • fanRayRealVector fan ρ ∈ σ.val) : x ∈ σ.val := by
  have coefficients := (mem_cone_iff_localFanRayCoordinates fan regular σ _).mp translated
  have rayCoordinates : localFanRayCoordinates fan σ (fanRayRealVector fan ρ) =
      Finsupp.single ρ 1 := localFanRayCoordinates_ray fan regular ρ σ rayMember
  have nonnegative : ∀ τ, 0 ≤ localFanRayCoordinates fan σ x τ := by
    intro τ
    by_cases same : τ = ρ
    · subst τ
      exact positive
    · have value := coefficients.1 τ
      simpa only [map_add,map_smul,rayCoordinates,Finsupp.add_apply,Finsupp.smul_apply,
        Finsupp.single_apply,if_neg same,if_neg (Ne.symm same),smul_zero,add_zero] using value
  have evaluate : fanRayCombination fan (localFanRayCoordinates fan σ x) = x := by
    have value := coefficients.2
    have singleValue : fanRayCombination fan (Finsupp.single ρ 1) =
        fanRayRealVector fan ρ := by simp [fanRayCombination]
    rw [map_add,map_smul,rayCoordinates,map_add,map_smul,singleValue] at value
    exact add_right_cancel value
  exact (mem_cone_iff_localFanRayCoordinates fan regular σ x).mpr ⟨nonnegative,evaluate⟩

theorem exists_separator_at_star_point (ρ : fan.Ray) (σ τ : fan.cones)
    (raySigma : fanRayRealVector fan ρ ∈ σ.val)
    (rayTau : fanRayRealVector fan ρ ∈ τ.val)
    (x : V) (member : x ∈ σ.val) (outside : x ∉ τ.val) :
    ∃ form : V →ₗ[ℝ] ℝ, form (fanRayRealVector fan ρ) = 0 ∧
      0 < form x ∧ ∀ y ∈ τ.val, form y ≤ 0 := by
  obtain ⟨m,nonnegative,negative,kernel,_⟩ :=
    exists_mem_dualSemigroup_neg_mem_dualSemigroup_inf_ker_eq fan.lattice
      (fan.isToricCone σ.property).rational (fan.isToricCone τ.property).rational
      (fan.inf_isFaceOf_left σ.property τ.property) (fan.inf_isFaceOf_right σ.property τ.property)
  have onSigma : ∀ y ∈ σ.val, 0 ≤ fan.lattice.realCharacter m y :=
    (mem_dualSemigroup fan.lattice m).mp nonnegative
  have onTau : ∀ y ∈ τ.val, fan.lattice.realCharacter m y ≤ 0 := by
    intro y belongs
    have value := (mem_dualSemigroup fan.lattice (-m)).mp negative belongs
    simpa only [map_neg,LinearMap.neg_apply,neg_nonneg] using value
  refine ⟨fan.lattice.realCharacter m,le_antisymm (onTau _ rayTau) (onSigma _ raySigma),?_,onTau⟩
  apply lt_of_le_of_ne (onSigma x member)
  intro zero
  apply outside
  have inKernel : x ∈ σ.val ⊓ PointedCone.ofSubmodule (fan.lattice.realCharacter m).ker :=
    ⟨member,zero.symm⟩
  rw [kernel] at inKernel
  exact inKernel.2

section Topology

variable [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul ℝ V] [T2Space V]

include regular in
theorem positive_ray_coordinate_mem_interior_support (ρ : fan.Ray)
    (covers : RayStarCovers fan (fanRayRealVector fan ρ)) (σ : fan.cones)
    {x : V} (member : x ∈ σ.val)
    (positive : 0 < localFanRayCoordinates fan σ x ρ) :
    x ∈ interior fan.support := by
  letI := fan.lattice.finiteDimensional
  have supported : ρ ∈ (localFanRayCoordinates fan σ x).support :=
    Finsupp.mem_support_iff.mpr positive.ne'
  have rayBelow := localFanRayCoordinates_supported fan σ x ρ supported
  have raySigma : fanRayRealVector fan ρ ∈ σ.val :=
    rayBelow (fanRayRealVector_mem fan ρ)
  let starCones := {τ : fan.cones // fanRayRealVector fan ρ ∈ τ.val}
  have neighbourhoods : ∀ τ : starCones, ∃ U : Set V,
      IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, ∀ t : ℝ,
        y + t • fanRayRealVector fan ρ ∈ τ.val.val → y ∈ τ.val.val := by
    intro τ
    by_cases belongs : x ∈ τ.val.val
    · have same := fanRayProfile_unique fan regular
        (localFanRayCoordinates_profile fan regular σ member)
        (localFanRayCoordinates_profile fan regular τ.val belongs)
      have positiveTau : 0 < localFanRayCoordinates fan τ.val x ρ := by
        rw [← same]
        exact positive
      refine ⟨{y | 0 < localFanRayCoordinates fan τ.val y ρ},?_,positiveTau,?_⟩
      · exact isOpen_lt continuous_const
          (((Finsupp.lapply ρ : (fan.Ray →₀ ℝ) →ₗ[ℝ] ℝ).comp
            (localFanRayCoordinates fan τ.val)).continuous_of_finiteDimensional)
      · intro y hy t translated
        exact mem_cone_of_ray_translate fan regular ρ τ.val τ.property y t hy.le translated
    · obtain ⟨form,rayZero,strict,nonpositive⟩ :=
        exists_separator_at_star_point fan ρ σ τ.val raySigma τ.property x member belongs
      refine ⟨{y | 0 < form y},isOpen_lt continuous_const form.continuous_of_finiteDimensional,
        strict,?_⟩
      intro y hy t translated
      have contradiction := nonpositive _ translated
      rw [map_add,map_smul,rayZero,smul_zero,add_zero] at contradiction
      exact False.elim ((not_lt_of_ge contradiction) hy)
  choose U openU pointU propertyU using neighbourhoods
  have openIntersection : IsOpen (⋂ τ : starCones, U τ) := isOpen_iInter_of_finite openU
  have pointIntersection : x ∈ ⋂ τ : starCones, U τ := mem_iInter.mpr pointU
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (openIntersection.mem_nhds pointIntersection)
  intro y inNeighbourhood
  obtain ⟨τ,rayTau,t,translated⟩ := covers y
  exact (Fan.mem_support fan).mpr ⟨τ.val,τ.property,
    propertyU ⟨τ,rayTau⟩ y (mem_iInter.mp inNeighbourhood ⟨τ,rayTau⟩) t translated⟩

end Topology
end ToricPower.FanSubdivision
end
