module

public import ToricPower.FanStarOpenSupport
public import ToricPower.FanAdaptedHyperplanes

/-!
# Exterior sign cones meet the packing only on its boundary

A finitely generated cone has a point belonging to no proper face: the
sum of any finite generating family. If an adapted exterior cone met
the interior of the packing support, a small move toward that point
would force the whole cone into one packing cone. This contradiction
is the geometric boundary argument used for gluing the completion.
-/

@[expose] public noncomputable section
open TauCeti.Toric Set
open scoped BigOperators Classical

namespace ToricPower.FanSubdivision

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem finiteCone_exists_face_determining_point (cone : PointedCone ℝ V)
    (finite : cone.FG) :
    ∃ z ∈ cone, ∀ F : PointedCone ℝ V, F.IsFaceOf cone → z ∈ F → cone ≤ F := by
  obtain ⟨generators,spans⟩ := finite
  let z : V := ∑ v : generators, (v : V)
  have generatorMember (v : generators) : (v : V) ∈ cone := by
    rw [← spans]
    exact Submodule.subset_span v.property
  refine ⟨z,cone.sum_mem (fun v _ => generatorMember v),?_⟩
  intro F face member
  rw [← spans]
  apply Submodule.span_le.mpr
  intro v belongs
  exact face.mem_of_sum_mem generatorMember member ⟨v,belongs⟩

variable {N : Type*} [AddCommGroup N] {i : N →+ V} (fan : Fan i)

section Topology

variable [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul ℝ V] [T2Space V]

/-- Every point of a genuinely exterior adapted cone avoids the interior
of the original support. The cone may have any dimension. -/
theorem exteriorCone_disjoint_interior (cone : PointedCone ℝ V) (finite : cone.FG)
    (adapted : ∀ σ : fan.cones, (cone ⊓ σ.val).IsFaceOf cone)
    (outside : ¬ ∃ σ : fan.cones, cone ≤ σ.val) :
    Disjoint (cone : Set V) (interior fan.support) := by
  apply Set.disjoint_left.mpr
  intro x member interiorMember
  obtain ⟨z,zMember,determines⟩ := finiteCone_exists_face_determining_point cone finite
  have continuousLine : Continuous (fun t : ℝ => x + t • z) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have lineOpen : IsOpen {t : ℝ | x + t • z ∈ interior fan.support} :=
    isOpen_interior.preimage continuousLine
  have zeroMember : (0 : ℝ) ∈ {t : ℝ | x + t • z ∈ interior fan.support} := by
    simpa only [Set.mem_setOf_eq,zero_smul,add_zero] using interiorMember
  obtain ⟨epsilon,positive,ball⟩ := Metric.isOpen_iff.mp lineOpen 0 zeroMember
  have halfPositive : 0 < epsilon/2 := half_pos positive
  have small : epsilon/2 ∈ Metric.ball (0 : ℝ) epsilon := by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos halfPositive]
    exact half_lt_self positive
  have moved : x + (epsilon/2) • z ∈ fan.support := interior_subset (ball small)
  obtain ⟨σ,coneMember,movedMember⟩ := (Fan.mem_support fan).mp moved
  have movedInCone : (epsilon/2) • z + x ∈ cone ⊓ σ := by
    constructor
    · exact cone.add_mem (cone.smul_mem halfPositive.le zMember) member
    · rw [add_comm]
      exact movedMember
  have zFace := (adapted ⟨σ,coneMember⟩).mem_of_smul_add_mem
    zMember member halfPositive movedInCone
  apply outside
  exact ⟨⟨σ,coneMember⟩,(determines (cone ⊓ σ) (adapted ⟨σ,coneMember⟩) zFace).trans inf_le_right⟩

theorem exteriorCone_oldRayCoordinate_zero (regular : fan.IsRegular)
    (cone : PointedCone ℝ V) (finite : cone.FG)
    (adapted : ∀ σ : fan.cones, (cone ⊓ σ.val).IsFaceOf cone)
    (outside : ¬ ∃ σ : fan.cones, cone ≤ σ.val)
    (ρ : fan.Ray) (covers : RayStarCovers fan (fanRayRealVector fan ρ))
    (σ : fan.cones) {x : V} (coneMember : x ∈ cone) (fanMember : x ∈ σ.val) :
    localFanRayCoordinates fan σ x ρ = 0 := by
  have nonnegative := (localFanRayCoordinates_profile fan regular σ fanMember).1 ρ
  apply le_antisymm _ nonnegative
  apply le_of_not_gt
  intro positive
  exact Set.disjoint_left.mp (exteriorCone_disjoint_interior fan cone finite adapted outside)
    coneMember (positive_ray_coordinate_mem_interior_support fan regular ρ covers σ fanMember positive)

end Topology
end ToricPower.FanSubdivision
end
