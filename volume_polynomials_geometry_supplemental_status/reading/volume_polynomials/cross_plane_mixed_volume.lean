module

public import VolumePolynomials.ThreeDimensionalMixedVolume

@[expose] public section

set_option autoImplicit false

/-! # Repeated mixed volumes in the coordinate planes

The coefficients are recovered from the literal two-plane Fubini formula at
two positive dilation values. Coordinate permutations preserve the actual
product measures; no proportionality factor is suppressed.
-/

noncomputable section
open Set MeasureTheory Module
open scoped Pointwise BigOperators

namespace VolumePolynomials.PlanarInteraction

open PlanarExtrusion PlanarMixedForm PlanarCorner PlanarEdges OAI.Paper092

def reframeY : Space ≃L[ℝ] Space where
  toFun p := (p.2.2, (p.2.1, p.1))
  invFun p := (p.2.2, (p.2.1, p.1))
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl
  map_add' p q := by ext <;> simp
  map_smul' r p := by ext <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def reframeX : Space ≃L[ℝ] Space where
  toFun p := (p.2.1, (p.2.2, p.1))
  invFun p := (p.2.2, (p.1, p.2.1))
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl
  map_add' p q := by ext <;> simp
  map_smul' r p := by ext <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem reframeX_measurePreserving : MeasurePreserving reframeX := by
  first
  | have hswap : MeasurePreserving (Prod.swap : Space → Plane × ℝ) :=
      Measure.measurePreserving_swap
    have hassoc : MeasurePreserving
        (MeasurableEquiv.prodAssoc : (ℝ × ℝ) × ℝ ≃ᵐ Space) :=
      volume_preserving_prodAssoc
    exact hassoc.comp hswap

theorem reframeY_measurePreserving : MeasurePreserving reframeY := by
  first
  | have hswap : MeasurePreserving (Prod.swap : Plane → Plane) :=
      Measure.measurePreserving_swap
    have hinner : MeasurePreserving (Prod.map id Prod.swap : Space → Space) :=
      (MeasurePreserving.id (volume : Measure ℝ)).prod hswap
    exact reframeX_measurePreserving.comp hinner

theorem realVolume_image_equiv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasureSpace F] [BorelSpace F]
    (T : E ≃L[ℝ] F) (hT : MeasurePreserving T) (S : Set E) :
    volume.real (T '' S) = volume.real S := by
  first
  | have hm := hT.measure_preimage_emb T.toHomeomorph.measurableEmbedding (T '' S)
    rw [Set.preimage_image_eq S T.injective] at hm
    exact congrArg ENNReal.toReal hm.symm

def swapBody (P : ConvexBody Plane) : ConvexBody Plane :=
  mapBody (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).toContinuousLinearMap P

theorem swapBody_area (P : ConvexBody Plane) :
    volume.real (swapBody P : Set Plane) = volume.real (P : Set Plane) :=
  realVolume_image_equiv (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ)
    Measure.measurePreserving_swap _

theorem swapBody_projection (P : ConvexBody Plane) :
    PlanarExtrusion.projection (swapBody P : Set Plane) = Prod.fst '' (P : Set Plane) := by
  first
  | simp only [PlanarExtrusion.projection, swapBody, coe_mapBody, Set.image_image]
    rfl

theorem reframeY_planeSum (A B : ConvexBody Plane) :
    reframeY '' (mapBody embedXY A + mapBody embedYZ B : ConvexBody Space) =
      CrossPlaneVolume.planeSum (swapBody A : Set Plane) (B : Set Plane) := by
  first
  | change reframeY.toLinearEquiv '' (embedXY '' (A : Set Plane) + embedYZ '' (B : Set Plane)) = _
    rw [Set.image_add reframeY.toLinearEquiv]
    simp only [ContinuousLinearEquiv.coe_toLinearEquiv, Set.image_image,
      CrossPlaneVolume.planeSum, swapBody, coe_mapBody]
    congr 1

theorem reframeX_planeSum (A C : ConvexBody Plane) :
    reframeX '' (mapBody embedXY A + mapBody embedXZ C : ConvexBody Space) =
      CrossPlaneVolume.planeSum (A : Set Plane) (C : Set Plane) := by
  first
  | change reframeX.toLinearEquiv '' (embedXY '' (A : Set Plane) + embedXZ '' (C : Set Plane)) = _
    rw [Set.image_add reframeX.toLinearEquiv]
    simp only [ContinuousLinearEquiv.coe_toLinearEquiv, Set.image_image, CrossPlaneVolume.planeSum]
    rfl

theorem volume_XY_YZ (A B : ConvexBody Plane) :
    volume.real ((mapBody embedXY A + mapBody embedYZ B : ConvexBody Space) : Set Space) =
      volume.real (A : Set Plane) * height B + width A * volume.real (B : Set Plane) := by
  first
  | rw [← realVolume_image_equiv reframeY reframeY_measurePreserving,
      reframeY_planeSum, CrossPlaneVolume.realVolume_planeSum
        (swapBody A).isCompact B.isCompact (swapBody A).convex B.convex,
      swapBody_area, swapBody_projection]
    rfl

theorem volume_XY_XZ (A C : ConvexBody Plane) :
    volume.real ((mapBody embedXY A + mapBody embedXZ C : ConvexBody Space) : Set Space) =
      volume.real (A : Set Plane) * height C + height A * volume.real (C : Set Plane) := by
  first
  | rw [← realVolume_image_equiv reframeX reframeX_measurePreserving,
      reframeX_planeSum, CrossPlaneVolume.realVolume_planeSum
        A.isCompact C.isCompact A.convex C.convex]
    rfl

theorem area_zeroBody : volume.real ((0 : ConvexBody Plane) : Set Plane) = 0 := by
  first
  | change (volume ({0} : Set Plane)).toReal = 0
    simp

theorem width_zeroBody : width (0 : ConvexBody Plane) = 0 := by
  first
  | simp [width, measureReal_def]

theorem height_zeroBody : height (0 : ConvexBody Plane) = 0 := by
  first
  | simp [height, measureReal_def]

@[simp] theorem mapBody_zero (f : Plane →L[ℝ] Space) : mapBody f 0 = 0 :=
  (mapBodyHom f).map_zero

theorem volume_embedXY (A : ConvexBody Plane) : volume.real (mapBody embedXY A : Set Space) = 0 := by
  first
  | have h := volume_XY_YZ A 0
    simpa only [mapBody_zero, add_zero, height_zeroBody, area_zeroBody, mul_zero, add_zero] using h

theorem volume_embedYZ (B : ConvexBody Plane) : volume.real (mapBody embedYZ B : Set Space) = 0 := by
  first
  | have h := volume_XY_YZ 0 B
    simpa only [mapBody_zero, zero_add, width_zeroBody, area_zeroBody, zero_mul, zero_add] using h

theorem volume_embedXZ (C : ConvexBody Plane) : volume.real (mapBody embedXZ C : Set Space) = 0 := by
  first
  | have h := volume_XY_XZ 0 C
    simpa only [mapBody_zero, zero_add, height_zeroBody, area_zeroBody, zero_mul, zero_add] using h

theorem repeated_XY_YZ (A B : ConvexBody Plane) :
    3 * mixed3 (mapBody embedXY A) (mapBody embedYZ B) (mapBody embedYZ B) =
      volume.real (B : Set Plane) * width A := by
  first
  | let A' := mapBody embedXY A
    let B' := mapBody embedYZ B
    have h1 := cubic_volume_expansion B' A' (by norm_num : (0 : ℝ) ≤ 1)
    have h2 := cubic_volume_expansion B' A' (by norm_num : (0 : ℝ) ≤ 2)
    have hp1 := volume_XY_YZ A B
    have hp2 := volume_XY_YZ A ((2 : ℝ) • B)
    rw [mapBody_smul] at hp2
    rw [height_smul B (by norm_num : (0 : ℝ) ≤ 2),
      haar_real_smul_body volume B (by norm_num : (0 : ℝ) ≤ 2), plane_finrank] at hp2
    have hA : volume.real (A' : Set Space) = 0 := volume_embedXY A
    have hB : volume.real (B' : Set Space) = 0 := volume_embedYZ B
    rw [hA, hB] at h1 h2
    have hB1 : (1 : ℝ) • B' = B' := one_smul ℝ B'
    rw [hB1] at h1
    simp only [one_pow, mul_zero, add_zero, zero_add] at h1
    have hsym : mixed3 B' B' A' = mixed3 A' B' B' := by
      first
      | rw [mixed3_swap_last B' B' A', mixed3_swap_first B' A' B']
    rw [hsym] at h1 h2
    change volume.real ((A' + B' : ConvexBody Space) : Set Space) = _ at hp1
    change volume.real ((A' + (2 : ℝ) • B' : ConvexBody Space) : Set Space) = _ at hp2
    dsimp only [A', B'] at h1 h2 hp1 hp2
    nlinarith

theorem repeated_XY_XZ (A C : ConvexBody Plane) :
    3 * mixed3 (mapBody embedXY A) (mapBody embedXZ C) (mapBody embedXZ C) =
      volume.real (C : Set Plane) * height A := by
  first
  | let A' := mapBody embedXY A
    let C' := mapBody embedXZ C
    have h1 := cubic_volume_expansion C' A' (by norm_num : (0 : ℝ) ≤ 1)
    have h2 := cubic_volume_expansion C' A' (by norm_num : (0 : ℝ) ≤ 2)
    have hp1 := volume_XY_XZ A C
    have hp2 := volume_XY_XZ A ((2 : ℝ) • C)
    rw [mapBody_smul] at hp2
    rw [height_smul C (by norm_num : (0 : ℝ) ≤ 2),
      haar_real_smul_body volume C (by norm_num : (0 : ℝ) ≤ 2), plane_finrank] at hp2
    have hA : volume.real (A' : Set Space) = 0 := volume_embedXY A
    have hC : volume.real (C' : Set Space) = 0 := volume_embedXZ C
    rw [hA, hC] at h1 h2
    have hC1 : (1 : ℝ) • C' = C' := one_smul ℝ C'
    rw [hC1] at h1
    simp only [one_pow, mul_zero, add_zero, zero_add] at h1
    have hsym : mixed3 C' C' A' = mixed3 A' C' C' := by
      first
      | rw [mixed3_swap_last C' C' A', mixed3_swap_first C' A' C']
    rw [hsym] at h1 h2
    change volume.real ((A' + C' : ConvexBody Space) : Set Space) = _ at hp1
    change volume.real ((A' + (2 : ℝ) • C' : ConvexBody Space) : Set Space) = _ at hp2
    dsimp only [A', C'] at h1 h2 hp1 hp2
    nlinarith

theorem derivative_planeSum (A B C : ConvexBody Plane) :
    HasDerivWithinAt (fun t : ℝ => volume.real
      (((mapBody embedYZ B + mapBody embedXZ C) + t • mapBody embedXY A : ConvexBody Space) : Set Space))
      (6 * triple A B C + volume.real (B : Set Plane) * width A +
        volume.real (C : Set Plane) * height A) (Ioi 0) 0 := by
  first
  | have hd := mixed3_hasDerivWithinAt_volume (mapBody embedXY A)
      (mapBody embedYZ B + mapBody embedXZ C)
    have he : 3 * mixed3 (mapBody embedXY A)
        (mapBody embedYZ B + mapBody embedXZ C) (mapBody embedYZ B + mapBody embedXZ C) =
        6 * triple A B C + volume.real (B : Set Plane) * width A +
          volume.real (C : Set Plane) * height A := by
      first
      | rw [mixed3_add_middle, mixed3_add_last, mixed3_add_last,
          mixed3_swap_last (mapBody embedXY A) (mapBody embedXZ C) (mapBody embedYZ B)]
        have hb := repeated_XY_YZ A B
        have hc := repeated_XY_XZ A C
        dsimp only [triple]
        linarith
    rwa [he] at hd

end VolumePolynomials.PlanarInteraction
