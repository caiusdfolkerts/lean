module

public import VolumePolynomials.PlanarNormalization
public import VolumePolynomials.CoordinateMixedProjection
public import VolumePolynomials.TrivariateMixedVolume
public import VolumePolynomials.ProjectionCoordinates
public import VolumePolynomials.CubicSlice
public import VolumePolynomials.RealizationCone
public import Mathlib.Tactic.LinearCombination

@[expose] public section

set_option autoImplicit false
noncomputable section

/-! The complete seven-term volume polynomial in the coordinate planes,
and the converse direction of Proposition 3.1 with an actual common dilation. -/

open Set MeasureTheory Module
open scoped Pointwise BigOperators

namespace VolumePolynomials.PlanarInteraction

open PlanarExtrusion PlanarMixedForm PlanarCorner PlanarEdges

theorem repeated_XY_XY_YZ (A B : ConvexBody Plane) :
    3 * mixed3 (mapBody embedXY A) (mapBody embedXY A) (mapBody embedYZ B) =
      volume.real (A : Set Plane) * height B := by
  first
  | let A' := mapBody embedXY A
    let B' := mapBody embedYZ B
    have h := cubic_volume_expansion B' A' (by norm_num : (0 : ℝ) ≤ 1)
    have hv := volume_XY_YZ A B
    have hr := repeated_XY_YZ A B
    rw [show volume.real (A' : Set Space) = 0 from volume_embedXY A,
      show volume.real (B' : Set Space) = 0 from volume_embedYZ B] at h
    simp only [ConvexBody.coe_add, ConvexBody.coe_smul, one_smul, one_pow,
      mul_one, mul_zero, add_zero, zero_add] at h
    have hBAA : mixed3 B' A' A' = mixed3 A' A' B' := by
      first
      | rw [mixed3_swap_first B' A' A', mixed3_swap_last A' B' A']
    have hBBA : mixed3 B' B' A' = mixed3 A' B' B' := by
      first
      | rw [mixed3_swap_last B' B' A', mixed3_swap_first B' A' B']
    rw [hBAA, hBBA] at h
    change volume.real (A' + B' : Set Space) = _ at hv
    change 3 * mixed3 A' B' B' = _ at hr
    change 3 * mixed3 A' A' B' = _
    linarith

theorem repeated_XY_XY_XZ (A C : ConvexBody Plane) :
    3 * mixed3 (mapBody embedXY A) (mapBody embedXY A) (mapBody embedXZ C) =
      volume.real (A : Set Plane) * height C := by
  first
  | let A' := mapBody embedXY A
    let C' := mapBody embedXZ C
    have h := cubic_volume_expansion C' A' (by norm_num : (0 : ℝ) ≤ 1)
    have hv := volume_XY_XZ A C
    have hr := repeated_XY_XZ A C
    rw [show volume.real (A' : Set Space) = 0 from volume_embedXY A,
      show volume.real (C' : Set Space) = 0 from volume_embedXZ C] at h
    simp only [ConvexBody.coe_add, ConvexBody.coe_smul, one_smul, one_pow,
      mul_one, mul_zero, add_zero, zero_add] at h
    have hCAA : mixed3 C' A' A' = mixed3 A' A' C' := by
      first
      | rw [mixed3_swap_first C' A' A', mixed3_swap_last A' C' A']
    have hCCA : mixed3 C' C' A' = mixed3 A' C' C' := by
      first
      | rw [mixed3_swap_last C' C' A', mixed3_swap_first C' A' C']
    rw [hCAA, hCCA] at h
    change volume.real (A' + C' : Set Space) = _ at hv
    change 3 * mixed3 A' C' C' = _ at hr
    change 3 * mixed3 A' A' C' = _
    linarith

theorem reframeX_YZ (B : ConvexBody Plane) :
    mapBody reframeX.toContinuousLinearMap (mapBody embedYZ B) = mapBody embedXY B := by
  first
  | apply ConvexBody.ext
    simp only [coe_mapBody, Set.image_image]
    rfl

theorem reframeX_XZ (C : ConvexBody Plane) :
    mapBody reframeX.toContinuousLinearMap (mapBody embedXZ C) = mapBody embedYZ (swapBody C) := by
  first
  | apply ConvexBody.ext
    simp only [swapBody, coe_mapBody, Set.image_image]
    rfl

theorem swapBody_height (C : ConvexBody Plane) : height (swapBody C) = width C := by
  first
  | change volume.real (PlanarExtrusion.projection (swapBody C : Set Plane)) = width C
    rw [swapBody_projection]
    rfl

theorem repeated_YZ_YZ_XZ (B C : ConvexBody Plane) :
    3 * mixed3 (mapBody embedYZ B) (mapBody embedYZ B) (mapBody embedXZ C) =
      volume.real (B : Set Plane) * width C := by
  first
  | have h := mixed3_map_measurePreserving reframeX reframeX_measurePreserving
      (mapBody embedYZ B) (mapBody embedYZ B) (mapBody embedXZ C)
    rw [reframeX_YZ, reframeX_XZ] at h
    rw [← h, repeated_XY_XY_YZ, swapBody_height]

theorem repeated_YZ_XZ_XZ (B C : ConvexBody Plane) :
    3 * mixed3 (mapBody embedYZ B) (mapBody embedXZ C) (mapBody embedXZ C) =
      volume.real (C : Set Plane) * width B := by
  first
  | have h := mixed3_map_measurePreserving reframeX reframeX_measurePreserving
      (mapBody embedYZ B) (mapBody embedXZ C) (mapBody embedXZ C)
    rw [reframeX_YZ, reframeX_XZ] at h
    rw [← h, repeated_XY_YZ, swapBody_area]

def coordinateVolume (A B C : ConvexBody Plane) (t : Fin 3 → ℝ) : ℝ :=
  volume.real (t 0 • mapBody embedXY A + t 1 • mapBody embedYZ B +
    t 2 • mapBody embedXZ C : Set Space)

/-- Every coefficient is expressed in literal area, width, or mixed volume. -/
theorem coordinate_volume_formula (A B C : ConvexBody Plane)
    (t : Fin 3 → ℝ) (ht : ∀ i, 0 ≤ t i) :
    coordinateVolume A B C t =
      t 0 ^ 2 * t 1 * (volume.real (A : Set Plane) * height B) +
      t 0 ^ 2 * t 2 * (volume.real (A : Set Plane) * height C) +
      t 0 * t 1 ^ 2 * (volume.real (B : Set Plane) * width A) +
      t 1 ^ 2 * t 2 * (volume.real (B : Set Plane) * width C) +
      t 0 * t 2 ^ 2 * (volume.real (C : Set Plane) * height A) +
      t 1 * t 2 ^ 2 * (volume.real (C : Set Plane) * width B) +
      t 0 * t 1 * t 2 * (6 * triple A B C) := by
  first
  | have h := trivariate_volume_formula_planar volume space_finrank
      (mapBody embedXY A) (mapBody embedYZ B) (mapBody embedXZ C)
      (volume_embedXY A) (volume_embedYZ B) (volume_embedXZ C) (ht 0) (ht 1) (ht 2)
    have hBAA : mixed3 (mapBody embedYZ B) (mapBody embedYZ B) (mapBody embedXY A) =
        mixed3 (mapBody embedXY A) (mapBody embedYZ B) (mapBody embedYZ B) := by
      first
      | rw [mixed3_swap_last (mapBody embedYZ B) (mapBody embedYZ B) (mapBody embedXY A),
          mixed3_swap_first (mapBody embedYZ B) (mapBody embedXY A)]
    have hCAA : mixed3 (mapBody embedXZ C) (mapBody embedXZ C) (mapBody embedXY A) =
        mixed3 (mapBody embedXY A) (mapBody embedXZ C) (mapBody embedXZ C) := by
      first
      | rw [mixed3_swap_last (mapBody embedXZ C) (mapBody embedXZ C) (mapBody embedXY A),
          mixed3_swap_first (mapBody embedXZ C) (mapBody embedXY A)]
    have hCCB : mixed3 (mapBody embedXZ C) (mapBody embedXZ C) (mapBody embedYZ B) =
        mixed3 (mapBody embedYZ B) (mapBody embedXZ C) (mapBody embedXZ C) := by
      first
      | rw [mixed3_swap_last (mapBody embedXZ C) (mapBody embedXZ C) (mapBody embedYZ B),
          mixed3_swap_first (mapBody embedXZ C) (mapBody embedYZ B)]
    change coordinateVolume A B C t = _ at h
    change mixed3 _ _ _ = _ at hBAA hCAA hCCB
    simp only [show mixedVolume3 (volume : Measure Space) = mixed3 from rfl] at h
    rw [hBAA, hCAA, hCCB] at h
    rw [h]
    have h1 := repeated_XY_XY_YZ A B
    have h2 := repeated_XY_XY_XZ A C
    have h3 := repeated_XY_YZ A B
    have h4 := repeated_YZ_YZ_XZ B C
    have h5 := repeated_XY_XZ A C
    have h6 := repeated_YZ_XZ_XZ B C
    dsimp only [triple]
    linear_combination t 0 ^ 2 * t 1 * h1 + t 0 ^ 2 * t 2 * h2 +
      t 0 * t 1 ^ 2 * h3 + t 1 ^ 2 * t 2 * h4 +
      t 0 * t 2 ^ 2 * h5 + t 1 * t 2 ^ 2 * h6

def coordinateEquiv : VolumePolynomials.Space 3 ≃L[ℝ] Space :=
  (Holonomy.coordinateExtract 0).toContinuousLinearEquiv

theorem coordinateEquiv_measurePreserving : MeasurePreserving coordinateEquiv :=
  Holonomy.coordinateExtract_measurePreserving 0

def cubicTuple (A B C : ConvexBody Plane) : Fin 3 → Body 3 :=
  fun i => mapBody coordinateEquiv.symm.toContinuousLinearMap
    (![mapBody embedXY A, mapBody embedYZ B, mapBody embedXZ C] i)

theorem volumeFunction_cubicTuple (A B C : ConvexBody Plane)
    (t : Fin 3 → ℝ) :
    volumeFunction (cubicTuple A B C) t = coordinateVolume A B C t := by
  first
  | have hsum : weightedSum (cubicTuple A B C) t =
        mapBody coordinateEquiv.symm.toContinuousLinearMap
          (t 0 • mapBody embedXY A + t 1 • mapBody embedYZ B + t 2 • mapBody embedXZ C) := by
      first
      | simp only [weightedSum, cubicTuple, Fin.sum_univ_three, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
          mapBody_add, mapBody_smul]
    rw [volumeFunction, hsum]
    exact measureReal_image_measurePreserving volume volume coordinateEquiv.symm
      (MeasurePreserving.symm coordinateEquiv.toHomeomorph.toMeasurableEquiv
        coordinateEquiv_measurePreserving) _

theorem normalized_coordinate_volume {α s z : ℝ} (D : NormalizedPlanarData α s z)
    (harea : volume.real (D.A : Set Plane) = α * D.T)
    (t : Fin 3 → ℝ) (ht : ∀ i, 0 ≤ t i) :
    coordinateVolume D.A D.B D.C t = D.T / 3 * CubicSlice.value α s z t := by
  first
  | rw [coordinate_volume_formula _ _ _ t ht, harea, D.B_area, D.C_area,
      D.A_width, D.A_height, D.B_width, D.B_height, D.C_width, D.C_height, D.triple_value]
    dsimp only [CubicSlice.value]
    ring

theorem normalized_cubic_realizes {α s z : ℝ} (D : NormalizedPlanarData α s z)
    (harea : volume.real (D.A : Set Plane) = α * D.T) :
    Realizes (cubicTuple D.A D.B D.C) ((D.T / 3) • CubicSlice.coefficients α s z) := by
  first
  | intro t ht
    rw [evaluate_smul, CubicSlice.evaluate_coefficients, volumeFunction_cubicTuple,
      normalized_coordinate_volume D harea t ht]

def cubicDilation {α s z : ℝ} (D : NormalizedPlanarData α s z) : ℝ :=
  (3 / D.T) ^ ((3 : ℝ)⁻¹)

theorem normalized_mem_volumeLocus {α s z : ℝ} (D : NormalizedPlanarData α s z)
    (harea : volume.real (D.A : Set Plane) = α * D.T) :
    CubicSlice.coefficients α s z ∈ VolumeLocus 3 3 := by
  first
  | have hbase : 0 ≤ 3 / D.T := (div_pos (by norm_num) D.T_pos).le
    have hr : 0 ≤ cubicDilation D := Real.rpow_nonneg hbase _
    have hp : cubicDilation D ^ 3 = 3 / D.T :=
      Real.rpow_inv_natCast_pow hbase (by decide)
    have h := (normalized_cubic_realizes D harea).dilate hr
    rw [hp, smul_smul, show 3 / D.T * (D.T / 3) = 1 by field_simp [D.T_pos.ne'], one_smul] at h
    exact ⟨fun i => cubicDilation D • cubicTuple D.A D.B D.C i, h⟩

end VolumePolynomials.PlanarInteraction
