module

public import VolumePolynomials.ShapeTuple
public import VolumePolynomials.FrameCalibration

@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped Pointwise

namespace VolumePolynomials.Holonomy

theorem volume_three_centered_segments (v w z : ThreeSpace) :
    bodyVolume (centeredBody v + centeredBody w + centeredBody z) =
      |determinant3 v w z| := by
  first
  | rw [centeredBody_eq_translate v, centeredBody_eq_translate w, centeredBody_eq_translate z,
      translateBody_add, translateBody_add, bodyVolume_translate, volume_three_origin_segments]

theorem volume_two_centered_segments (v w : ThreeSpace) :
    bodyVolume (centeredBody v + centeredBody w) = 0 := by
  first
  | have h := volume_three_centered_segments v w 0
    simpa [centeredBody_zero, determinant3] using h

theorem coordinate_zero_centeredBody (v : ThreeSpace) (i : Fin 3) (hv : v i = 0) :
    ∀ x ∈ centeredBody v, x i = 0 := by
  first
  | intro x hx
    change x ∈ (centeredBody v : Set ThreeSpace) at hx
    rw [centeredBody_carrier] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    simp [hv]

theorem coordinate_zero_add {K L : Body 3} (i : Fin 3)
    (hK : ∀ x ∈ K, x i = 0) (hL : ∀ x ∈ L, x i = 0) :
    ∀ x ∈ K + L, x i = 0 := by
  first
  | intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_add.mp hx
    change y i + z i = 0
    rw [hK y hy, hL z hz, add_zero]

/-- A body contained in a coordinate plane has literal three-dimensional
Lebesgue volume zero. The origin assumption is supplied in each application. -/
theorem bodyVolume_zero_of_coordinate (K : Body 3) (i : Fin 3)
    (hzero : (0 : ThreeSpace) ∈ K) (hK : ∀ x ∈ K, x i = 0) :
    bodyVolume K = 0 := by
  first
  | apply (bodyVolume_eq_zero_iff_linearHull_ne_top hzero).mpr
    intro htop
    let p : ThreeSpace →ₗ[ℝ] ℝ := (ContinuousLinearMap.proj i).toLinearMap
    have hsub : linearHull K ≤ LinearMap.ker p := by
      apply Submodule.span_le.mpr
      intro x hx
      exact hK x hx
    have hm : axis i ∈ linearHull K := by rw [htop]; trivial
    have hz : p (axis i) = 0 := hsub hm
    simpa [p, axis, Pi.single_apply] using hz

theorem IsCalibratedTuple.volume_planeA {K : Fin 9 → Body 3} (hK : IsCalibratedTuple K) :
    bodyVolume (K ShapeConditions.bodyA + K ShapeConditions.e₁ + K ShapeConditions.e₂) = 0 := by
  first
  | have h₁ : K ShapeConditions.e₁ = centeredBody (axis 0) := hK.segments 0
    have h₂ : K ShapeConditions.e₂ = centeredBody (axis 1) := hK.segments 1
    rw [h₁, h₂]
    apply bodyVolume_zero_of_coordinate _ 2
    · exact zero_mem_body_add (zero_mem_body_add hK.zeroA (zero_mem_centeredBody _))
        (zero_mem_centeredBody _)
    · exact coordinate_zero_add 2
        (coordinate_zero_add 2 hK.planeA
          (coordinate_zero_centeredBody _ 2 (by simp [axis, Pi.single_apply])))
        (coordinate_zero_centeredBody _ 2 (by simp [axis, Pi.single_apply]))

theorem IsCalibratedTuple.volume_planeB {K : Fin 9 → Body 3} (hK : IsCalibratedTuple K) :
    bodyVolume (K ShapeConditions.bodyB + K ShapeConditions.e₁ + K ShapeConditions.e₃) = 0 := by
  first
  | have h₁ : K ShapeConditions.e₁ = centeredBody (axis 0) := hK.segments 0
    have h₃ : K ShapeConditions.e₃ = centeredBody (axis 2) := hK.segments 2
    rw [h₁, h₃]
    apply bodyVolume_zero_of_coordinate _ 1
    · exact zero_mem_body_add (zero_mem_body_add hK.zeroB (zero_mem_centeredBody _))
        (zero_mem_centeredBody _)
    · exact coordinate_zero_add 1
        (coordinate_zero_add 1 hK.planeB
          (coordinate_zero_centeredBody _ 1 (by simp [axis, Pi.single_apply])))
        (coordinate_zero_centeredBody _ 1 (by simp [axis, Pi.single_apply]))

theorem IsCalibratedTuple.volume_planeC {K : Fin 9 → Body 3} (hK : IsCalibratedTuple K) :
    bodyVolume (K ShapeConditions.bodyC + K ShapeConditions.e₂ + K ShapeConditions.e₃) = 0 := by
  first
  | have h₂ : K ShapeConditions.e₂ = centeredBody (axis 1) := hK.segments 1
    have h₃ : K ShapeConditions.e₃ = centeredBody (axis 2) := hK.segments 2
    rw [h₂, h₃]
    apply bodyVolume_zero_of_coordinate _ 0
    · exact zero_mem_body_add (zero_mem_body_add hK.zeroC (zero_mem_centeredBody _))
        (zero_mem_centeredBody _)
    · exact coordinate_zero_add 0
        (coordinate_zero_add 0 hK.planeC
          (coordinate_zero_centeredBody _ 0 (by simp [axis, Pi.single_apply])))
        (coordinate_zero_centeredBody _ 0 (by simp [axis, Pi.single_apply]))

end VolumePolynomials.Holonomy
