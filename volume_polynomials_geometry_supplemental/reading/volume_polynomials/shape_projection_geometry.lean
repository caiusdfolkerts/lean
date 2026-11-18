module

public import VolumePolynomials.ShapeTuple
public import VolumePolynomials.ShapeEvaluation
public import VolumePolynomials.ProjectedShapeRigidity

@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped Pointwise

namespace VolumePolynomials.Holonomy

def coordinateProjection (i : Fin 3) : ThreeSpace →L[ℝ] Plane :=
  (ContinuousLinearMap.snd ℝ ℝ Plane).comp (projectionFrame i 0).toContinuousLinearMap

@[simp] theorem fin3_succAbove_two_one :
    (2 : Fin 3).succAbove (1 : Fin 2) = 1 := by decide

@[simp] theorem coordinateProjection_apply (i : Fin 3) (x : ThreeSpace) :
    coordinateProjection i x = (x (i.succAbove 0), x (i.succAbove 1)) := by
  first
  | simp [coordinateProjection]

@[simp] theorem coordinateProjectionXY_apply (x : ThreeSpace) :
    coordinateProjection 2 x = (x 0, x 1) := by
  first
  | simp [show (2 : Fin 3).succAbove (1 : Fin 2) = 1 by decide]

@[simp] theorem coordinateProjectionXZ_apply (x : ThreeSpace) :
    coordinateProjection 1 x = (x 0, x 2) := by simp

@[simp] theorem coordinateProjectionYZ_apply (x : ThreeSpace) :
    coordinateProjection 0 x = (x 1, x 2) := by simp

@[simp] theorem coordinateProjection_embedXY (p : Plane) :
    coordinateProjection 2 (embedXY p) = p := by simp [embedXY]

@[simp] theorem coordinateProjection_embedXZ (p : Plane) :
    coordinateProjection 1 (embedXZ p) = p := by simp [embedXZ]

@[simp] theorem coordinateProjection_embedYZ (p : Plane) :
    coordinateProjection 0 (embedYZ p) = p := by simp [embedYZ]

theorem embedXY_coordinateProjection {x : ThreeSpace} (hx : x 2 = 0) :
    embedXY (coordinateProjection 2 x) = x := by
  first
  | ext i
    fin_cases i <;> simp_all [embedXY]

theorem embedXZ_coordinateProjection {x : ThreeSpace} (hx : x 1 = 0) :
    embedXZ (coordinateProjection 1 x) = x := by
  first
  | ext i
    fin_cases i <;> simp_all [embedXZ]

theorem embedYZ_coordinateProjection {x : ThreeSpace} (hx : x 0 = 0) :
    embedYZ (coordinateProjection 0 x) = x := by
  first
  | ext i
    fin_cases i <;> simp_all [embedYZ]

def planarA (K : Fin 9 → Body 3) : ConvexBody Plane :=
  mapBody (coordinateProjection 2) (K ShapeConditions.bodyA)

def planarB (K : Fin 9 → Body 3) : ConvexBody Plane :=
  mapBody (coordinateProjection 1) (K ShapeConditions.bodyB)

def planarC (K : Fin 9 → Body 3) : ConvexBody Plane :=
  mapBody (coordinateProjection 0) (K ShapeConditions.bodyC)

theorem IsCalibratedTuple.placeA {K : Fin 9 → Body 3} (hK : IsCalibratedTuple K) :
    (K ShapeConditions.bodyA : Set ThreeSpace) = embedXY '' (planarA K : Set Plane) := by
  first
  | change _ = embedXY '' (coordinateProjection 2 '' (K ShapeConditions.bodyA : Set ThreeSpace))
    rw [Set.image_image]
    symm
    calc
      _ = id '' (K ShapeConditions.bodyA : Set ThreeSpace) :=
        Set.image_congr (fun x hx => embedXY_coordinateProjection (hK.planeA x hx))
      _ = _ := Set.image_id' _

theorem IsCalibratedTuple.placeB {K : Fin 9 → Body 3} (hK : IsCalibratedTuple K) :
    (K ShapeConditions.bodyB : Set ThreeSpace) = embedXZ '' (planarB K : Set Plane) := by
  first
  | change _ = embedXZ '' (coordinateProjection 1 '' (K ShapeConditions.bodyB : Set ThreeSpace))
    rw [Set.image_image]
    symm
    calc
      _ = id '' (K ShapeConditions.bodyB : Set ThreeSpace) :=
        Set.image_congr (fun x hx => embedXZ_coordinateProjection (hK.planeB x hx))
      _ = _ := Set.image_id' _

theorem IsCalibratedTuple.placeC {K : Fin 9 → Body 3} (hK : IsCalibratedTuple K) :
    (K ShapeConditions.bodyC : Set ThreeSpace) = embedYZ '' (planarC K : Set Plane) := by
  first
  | change _ = embedYZ '' (coordinateProjection 0 '' (K ShapeConditions.bodyC : Set ThreeSpace))
    rw [Set.image_image]
    symm
    calc
      _ = id '' (K ShapeConditions.bodyC : Set ThreeSpace) :=
        Set.image_congr (fun x hx => embedYZ_coordinateProjection (hK.planeC x hx))
      _ = _ := Set.image_id' _

theorem bodyExtrusion_eq_frame_projection (L : Body 3)
    (T : ThreeSpace ≃L[ℝ] (ℝ × Plane)) (hT : MeasurePreserving T volume volume)
    (v : ThreeSpace) (hv : T v = (1, 0)) :
    bodyVolume (L + centeredBody v) - bodyVolume L =
      volume.real (((ContinuousLinearMap.snd ℝ ℝ Plane).comp
        T.toContinuousLinearMap) '' (L : Set ThreeSpace)) := by
  first
  | have h := ProductExtrusion.realVolume_add_centered_segment T hT L.isCompact L.convex hv
    change volume.real ((L : Set ThreeSpace) + (centeredBody v : Set ThreeSpace)) -
      volume.real (L : Set ThreeSpace) = _
    rw [centeredBody_carrier, h, add_sub_cancel_left]
    congr 1
    rw [PlanarExtrusion.projection, Set.image_image]
    rfl

@[simp] theorem bodyExtrusion_V (L : Body 3) :
    bodyVolume (L + centeredBody directionV) - bodyVolume L =
      volume.real (projectionV '' (L : Set ThreeSpace)) :=
  bodyExtrusion_eq_frame_projection L frameV frameV_measurePreserving directionV frameV_direction

@[simp] theorem bodyExtrusion_W (L : Body 3) :
    bodyVolume (L + centeredBody directionW) - bodyVolume L =
      volume.real (projectionW '' (L : Set ThreeSpace)) :=
  bodyExtrusion_eq_frame_projection L frameW frameW_measurePreserving directionW frameW_direction

@[simp] theorem bodyExtrusion_Z (L : Body 3) :
    bodyVolume (L + centeredBody directionZ) - bodyVolume L =
      volume.real (projectionZ '' (L : Set ThreeSpace)) :=
  bodyExtrusion_eq_frame_projection L frameZ frameZ_measurePreserving directionZ frameZ_direction

@[simp] theorem bodyExtrusion_axis (L : Body 3) (i : Fin 3) :
    bodyVolume (L + centeredBody (axis i)) - bodyVolume L =
      volume.real (coordinateProjection i '' (L : Set ThreeSpace)) := by
  first
  | apply bodyExtrusion_eq_frame_projection L (projectionFrame i 0)
      (projectionFrame_measurePreserving i 0) (axis i)
    simp [projectionFrame_apply, axis, Pi.single_apply, Fin.succAbove_ne, Fin.ne_succAbove]

theorem IsCalibratedTuple.projectionVA {K : Fin 9 → Body 3} (hK : IsCalibratedTuple K) :
    projectionV '' (K ShapeConditions.bodyA : Set ThreeSpace) = (planarA K : Set Plane) := by
  first
  | rw [hK.placeA]
    simp only [Set.image_image, Function.comp_apply, projectionV_embedXY, Set.image_id']

theorem IsCalibratedTuple.projectionVB {K : Fin 9 → Body 3} (hK : IsCalibratedTuple K) :
    projectionV '' (K ShapeConditions.bodyB : Set ThreeSpace) =
      transport01 '' (planarB K : Set Plane) := by
  first
  | rw [hK.placeB]
    simp only [Set.image_image, Function.comp_apply, projectionV_embedXZ]

theorem IsCalibratedTuple.projectionWB {K : Fin 9 → Body 3} (hK : IsCalibratedTuple K) :
    projectionW '' (K ShapeConditions.bodyB : Set ThreeSpace) = (planarB K : Set Plane) := by
  first
  | rw [hK.placeB]
    simp only [Set.image_image, Function.comp_apply, projectionW_embedXZ, Set.image_id']

theorem IsCalibratedTuple.projectionWC {K : Fin 9 → Body 3} (hK : IsCalibratedTuple K) :
    projectionW '' (K ShapeConditions.bodyC : Set ThreeSpace) =
      transport12 '' (planarC K : Set Plane) := by
  first
  | rw [hK.placeC]
    simp only [Set.image_image, Function.comp_apply, projectionW_embedYZ]

theorem IsCalibratedTuple.projectionZA {K : Fin 9 → Body 3} (hK : IsCalibratedTuple K) :
    projectionZ '' (K ShapeConditions.bodyA : Set ThreeSpace) = (planarA K : Set Plane) := by
  first
  | rw [hK.placeA]
    simp only [Set.image_image, Function.comp_apply, projectionZ_embedXY, Set.image_id']

theorem IsCalibratedTuple.projectionZC {K : Fin 9 → Body 3} (hK : IsCalibratedTuple K) :
    projectionZ '' (K ShapeConditions.bodyC : Set ThreeSpace) =
      transport20 '' (planarC K : Set Plane) := by
  first
  | rw [hK.placeC]
    simp only [Set.image_image, Function.comp_apply, projectionZ_embedYZ]

theorem projectionZ_centered_axis0 :
    projectionZ '' (centeredBody (axis 0) : Set ThreeSpace) = centeredSegment (1, 0) := by
  first
  | rw [centeredBody_carrier, centeredSegment_eq_image, Set.image_image]
    congr 1
    funext t
    simp [Function.comp_apply, map_smul, axis, projectionZ_apply, Pi.single_apply]

theorem IsCalibratedTuple.projectionZ_last {K : Fin 9 → Body 3}
    (hK : IsCalibratedTuple K) (lam : ℝ) :
    projectionZ '' (lam • (K ShapeConditions.bodyC : Set ThreeSpace) +
      (K ShapeConditions.e₁ : Set ThreeSpace)) = lastProjectedSet lam (planarC K) := by
  first
  | have haxis := hK.segments 0
    change K ShapeConditions.e₁ = centeredBody (axis 0) at haxis
    rw [haxis, Set.image_add projectionZ,
      Set.image_smul_comm projectionZ lam _ (fun x => projectionZ.map_smul lam x),
      hK.projectionZC, projectionZ_centered_axis0]
    change lam • (transport20 '' (planarC K : Set Plane)) + centeredSegment (1, 0) = _
    rw [add_comm]
    congr 1
    rw [← Set.image_smul, Set.image_image]
    rfl

end VolumePolynomials.Holonomy
