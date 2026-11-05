module

public import VolumePolynomials.ShapeProjectionGeometry

@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped Pointwise

namespace VolumePolynomials.Holonomy

open ShapeConditions

variable {K : Fin 9 → Body 3} (hK : IsCalibratedTuple K)

include hK

theorem IsCalibratedTuple.extrusion_axisA :
    extrusionValue (volumeFunction K) (unitWeight bodyA) e₃ = volume.real (planarA K : Set Plane) := by
  first
  | have hs : K e₃ = centeredBody (axis 2) := hK.segments 2
    rw [extrusionValue_volume K _ _ (unitWeight_nonneg bodyA), weightedSum_unitWeight,
      hs, bodyExtrusion_axis]
    rfl

theorem IsCalibratedTuple.extrusion_axisB :
    extrusionValue (volumeFunction K) (unitWeight bodyB) e₂ = volume.real (planarB K : Set Plane) := by
  first
  | have hs : K e₂ = centeredBody (axis 1) := hK.segments 1
    rw [extrusionValue_volume K _ _ (unitWeight_nonneg bodyB), weightedSum_unitWeight,
      hs, bodyExtrusion_axis]
    rfl

theorem IsCalibratedTuple.extrusion_axisC :
    extrusionValue (volumeFunction K) (unitWeight bodyC) e₁ = volume.real (planarC K : Set Plane) := by
  first
  | have hs : K e₁ = centeredBody (axis 0) := hK.segments 0
    rw [extrusionValue_volume K _ _ (unitWeight_nonneg bodyC), weightedSum_unitWeight,
      hs, bodyExtrusion_axis]
    rfl

theorem IsCalibratedTuple.extrusion_VA :
    extrusionValue (volumeFunction K) (unitWeight bodyA) sᵥ = volume.real (planarA K : Set Plane) := by
  first
  | have hs : K sᵥ = centeredBody directionV := hK.segments 3
    rw [extrusionValue_volume K _ _ (unitWeight_nonneg bodyA), weightedSum_unitWeight,
      hs, bodyExtrusion_V, hK.projectionVA]

theorem IsCalibratedTuple.extrusion_VB :
    extrusionValue (volumeFunction K) (unitWeight bodyB) sᵥ =
      volume.real (transport01 '' (planarB K : Set Plane)) := by
  first
  | have hs : K sᵥ = centeredBody directionV := hK.segments 3
    rw [extrusionValue_volume K _ _ (unitWeight_nonneg bodyB), weightedSum_unitWeight,
      hs, bodyExtrusion_V, hK.projectionVB]

theorem IsCalibratedTuple.extrusion_VAB :
    extrusionValue (volumeFunction K) (unitWeight bodyA + unitWeight bodyB) sᵥ =
      volume.real ((planarA K : Set Plane) + transport01 '' (planarB K : Set Plane)) := by
  first
  | have hs : K sᵥ = centeredBody directionV := hK.segments 3
    rw [extrusionValue_volume K (unitWeight bodyA + unitWeight bodyB) sᵥ
      (fun i => add_nonneg (unitWeight_nonneg bodyA i) (unitWeight_nonneg bodyB i)),
      weightedSum_two, hs, bodyExtrusion_V, ConvexBody.coe_add, Set.image_add projectionV,
      hK.projectionVA, hK.projectionVB]

theorem IsCalibratedTuple.extrusion_WB :
    extrusionValue (volumeFunction K) (unitWeight bodyB) s𝓌 = volume.real (planarB K : Set Plane) := by
  first
  | have hs : K s𝓌 = centeredBody directionW := hK.segments 4
    rw [extrusionValue_volume K _ _ (unitWeight_nonneg bodyB), weightedSum_unitWeight,
      hs, bodyExtrusion_W, hK.projectionWB]

theorem IsCalibratedTuple.extrusion_WC :
    extrusionValue (volumeFunction K) (unitWeight bodyC) s𝓌 =
      volume.real (transport12 '' (planarC K : Set Plane)) := by
  first
  | have hs : K s𝓌 = centeredBody directionW := hK.segments 4
    rw [extrusionValue_volume K _ _ (unitWeight_nonneg bodyC), weightedSum_unitWeight,
      hs, bodyExtrusion_W, hK.projectionWC]

theorem IsCalibratedTuple.extrusion_WBC :
    extrusionValue (volumeFunction K) (unitWeight bodyB + unitWeight bodyC) s𝓌 =
      volume.real ((planarB K : Set Plane) + transport12 '' (planarC K : Set Plane)) := by
  first
  | have hs : K s𝓌 = centeredBody directionW := hK.segments 4
    rw [extrusionValue_volume K (unitWeight bodyB + unitWeight bodyC) s𝓌
      (fun i => add_nonneg (unitWeight_nonneg bodyB i) (unitWeight_nonneg bodyC i)),
      weightedSum_two, hs, bodyExtrusion_W, ConvexBody.coe_add, Set.image_add projectionW,
      hK.projectionWB, hK.projectionWC]

theorem IsCalibratedTuple.extrusion_ZA :
    extrusionValue (volumeFunction K) (unitWeight bodyA) s𝓏 = volume.real (planarA K : Set Plane) := by
  first
  | have hs : K s𝓏 = centeredBody directionZ := hK.segments 5
    rw [extrusionValue_volume K _ _ (unitWeight_nonneg bodyA), weightedSum_unitWeight,
      hs, bodyExtrusion_Z, hK.projectionZA]

theorem IsCalibratedTuple.extrusion_ZD (lam : ℝ) (hlam : 0 ≤ lam) :
    extrusionValue (volumeFunction K) (lastNumericalWeight lam) s𝓏 =
      volume.real (lastProjectedSet lam (planarC K)) := by
  first
  | have hs : K s𝓏 = centeredBody directionZ := hK.segments 5
    rw [extrusionValue_volume K _ _ (lastNumericalWeight_nonneg lam hlam),
      weightedSum_last K lam hlam, hs, bodyExtrusion_Z,
      ConvexBody.coe_add, ConvexBody.coe_smul, hK.projectionZ_last]

theorem IsCalibratedTuple.extrusion_ZAD (lam : ℝ) (hlam : 0 ≤ lam) :
    extrusionValue (volumeFunction K) (unitWeight bodyA + lastNumericalWeight lam) s𝓏 =
      volume.real ((planarA K : Set Plane) + lastProjectedSet lam (planarC K)) := by
  first
  | have hs : K s𝓏 = centeredBody directionZ := hK.segments 5
    rw [extrusionValue_volume K (unitWeight bodyA + lastNumericalWeight lam) s𝓏
      (fun i => add_nonneg (unitWeight_nonneg bodyA i)
        (lastNumericalWeight_nonneg lam hlam i)),
      weightedSum_add K (unitWeight bodyA) (lastNumericalWeight lam)
        (unitWeight_nonneg bodyA) (lastNumericalWeight_nonneg lam hlam),
      weightedSum_unitWeight, weightedSum_last K lam hlam, hs, bodyExtrusion_Z,
      ConvexBody.coe_add, Set.image_add projectionZ, hK.projectionZA,
      ConvexBody.coe_add, ConvexBody.coe_smul, hK.projectionZ_last]

end VolumePolynomials.Holonomy
