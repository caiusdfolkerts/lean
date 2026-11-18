module

public import ToricPower.FanRayQuotientCones
public import TauCeti.Geometry.Toric.Algebraic.Fan.Basic

/-!
# Coverage by the star of an actual vector

The condition below expresses completeness of a ray star without
choosing a quotient presentation. A translate of every ambient point
in the ray direction belongs to a cone containing that direction.
It is stable under literal fan extensions. The quotient criterion is
proved using the actual kernel, rather than a formal fan label.
-/

@[expose] public noncomputable section

open TauCeti.Toric
namespace ToricPower.FanSubdivision

variable {N V W : Type*} [AddCommGroup N]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  {i : N →+ V}

/-- Every quotient direction is covered by a cone containing `a`. -/
def RayStarCovers (fan : Fan i) (a : V) : Prop :=
  ∀ x : V, ∃ σ : fan.cones, a ∈ σ.val ∧ ∃ t : ℝ, x + t • a ∈ σ.val

theorem RayStarCovers.mono {fan extension : Fan i} {a : V}
    (covers : RayStarCovers fan a) (contains : fan.cones ⊆ extension.cones) :
    RayStarCovers extension a := by
  intro x
  obtain ⟨σ,member,t,translated⟩ := covers x
  exact ⟨⟨σ.val,contains σ.property⟩,member,t,translated⟩

theorem rayStarCovers_of_quotient_coverage (fan : Fan i) (a : V)
    (projection : V →ₗ[ℝ] W)
    (kernel : projection.ker = Submodule.span ℝ {a})
    (coverage : ∀ z : W, ∃ σ : fan.cones,
      a ∈ σ.val ∧ z ∈ PointedCone.map projection σ.val) :
    RayStarCovers fan a := by
  intro x
  obtain ⟨σ,member,projected⟩ := coverage (projection x)
  obtain ⟨y,hy,same⟩ := PointedCone.mem_map.mp projected
  obtain ⟨t,value⟩ := eq_add_ray_of_projection_eq projection a kernel same
  exact ⟨σ,member,t,value ▸ hy⟩

theorem RayStarCovers.quotient_coverage (fan : Fan i) (a : V)
    (projection : V →ₗ[ℝ] W) (surjective : Function.Surjective projection)
    (kernelVector : projection a = 0) (covers : RayStarCovers fan a) :
    ∀ z : W, ∃ σ : fan.cones, a ∈ σ.val ∧ z ∈ PointedCone.map projection σ.val := by
  intro z
  obtain ⟨x,rfl⟩ := surjective z
  obtain ⟨σ,member,t,translated⟩ := covers x
  refine ⟨σ,member,PointedCone.mem_map.mpr ⟨x+t•a,translated,?_⟩⟩
  rw [map_add,map_smul,kernelVector,smul_zero,add_zero]

end ToricPower.FanSubdivision
end

