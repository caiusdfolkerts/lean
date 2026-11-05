module

public import VolumePolynomials.PrismFirstVariation
public import VolumePolynomials.MixedVolumeTransport

@[expose] public section

set_option autoImplicit false

/-! # The exact mixed-area formula for a coordinate-segment argument -/

noncomputable section
open Set MeasureTheory Module
open scoped Pointwise BigOperators

namespace VolumePolynomials.PlanarInteraction

open PlanarExtrusion PlanarMixedForm PlanarCorner PlanarEdges OAI.Paper092

def projectBase : Space →L[ℝ] Plane := ContinuousLinearMap.snd ℝ ℝ Plane

def baseBody (S : ConvexBody Space) : ConvexBody Plane := mapBody projectBase S

theorem mixed3_vertical_projection (B C : ConvexBody Space) :
    6 * mixed3 verticalUnit B C = 2 * mixedArea volume (baseBody B) (baseBody C) := by
  first
  | have h := mixed3_verticalUnit (B + C)
    have hB := mixed3_verticalUnit B
    have hC := mixed3_verticalUnit C
    have he (S : ConvexBody Space) : PlanarExtrusion.projection (S : Set Space) =
        (baseBody S : Set Plane) := rfl
    simp only [he] at h hB hC
    have hsum : baseBody (B + C) = baseBody B + baseBody C := mapBody_add projectBase B C
    rw [mixed3_add_middle, mixed3_add_last, mixed3_add_last,
      mixed3_swap_last verticalUnit C B, hsum, area_add volume plane_finrank] at h
    linarith

theorem mixed3_map_measurePreserving (T : Space ≃L[ℝ] Space) (hT : MeasurePreserving T)
    (A B C : ConvexBody Space) :
    mixed3 (mapBody T.toContinuousLinearMap A) (mapBody T.toContinuousLinearMap B)
      (mapBody T.toContinuousLinearMap C) = mixed3 A B C := by
  first
  | have he : (fun i : Fin 3 => mapBody T.toContinuousLinearMap (![A, B, C] i)) =
        ![mapBody T.toContinuousLinearMap A, mapBody T.toContinuousLinearMap B,
          mapBody T.toContinuousLinearMap C] := by funext i; fin_cases i <;> rfl
    simpa only [he, mixed3] using mixedVolume_map_measurePreserving volume volume T hT ![A, B, C]

def verticalProjection (P : ConvexBody Plane) : ConvexBody Plane :=
  mapBody (diagonalLinear 0 1) P

def horizontalProjection (P : ConvexBody Plane) : ConvexBody Plane :=
  mapBody (diagonalLinear 1 0) P

theorem verticalProjection_eq_translate (P : ConvexBody Plane) :
    ∃ v : Plane, verticalProjection P = translateBody v (rightTriangle 0 (height P)) := by
  first
  | let J := Prod.snd '' (P : Set Plane)
    have hJ : IsCompact J := P.isCompact.image continuous_snd
    have hJc : Convex ℝ J := P.convex.linear_image (LinearMap.snd ℝ ℝ ℝ)
    have hJn : J.Nonempty := P.nonempty.image Prod.snd
    have hI : J = Icc (sInf J) (sSup J) :=
      eq_Icc_of_connected_compact ⟨hJn, Real.convex_iff_isPreconnected.mp hJc⟩ hJ
    have hle : sInf J ≤ sSup J := csInf_le_csSup hJn hJ.bddBelow hJ.bddAbove
    have hheight : height P = sSup J - sInf J := by
      first
      | change volume.real J = _
        calc
          volume.real J = volume.real (Icc (sInf J) (sSup J)) := congrArg volume.real hI
          _ = _ := Real.volume_real_Icc_of_le hle
    refine ⟨(0, sInf J), ConvexBody.ext ?_⟩
    rw [coe_translateBody, rightTriangle_vertical (show 0 ≤ height P from measureReal_nonneg)]
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      have hqJ : q.2 ∈ J := ⟨q, hq, rfl⟩
      rw [hI] at hqJ
      refine ⟨(0, q.2 - sInf J), ⟨rfl, ?_⟩, ?_⟩
      · rw [hheight]
        exact ⟨by linarith [hqJ.1], by linarith [hqJ.2]⟩
      · ext <;> simp [diagonalLinear_apply] <;> ring
    · rintro ⟨q, ⟨hq0, hq⟩, rfl⟩
      change q.1 = 0 at hq0
      have hj : sInf J + q.2 ∈ J := by
        first
        | apply (congrArg (fun S : Set ℝ => sInf J + q.2 ∈ S) hI).mpr
          rw [hheight] at hq
          constructor <;> linarith [hq.1, hq.2]
      obtain ⟨r, hr, hre⟩ := hj
      refine ⟨r, hr, ?_⟩
      ext <;> simp [diagonalLinear_apply, hq0, hre]

theorem horizontalProjection_eq_translate (P : ConvexBody Plane) :
    ∃ v : Plane, horizontalProjection P = translateBody v (rightTriangle (width P) 0) := by
  first
  | let J := Prod.fst '' (P : Set Plane)
    have hJ : IsCompact J := P.isCompact.image continuous_fst
    have hJc : Convex ℝ J := P.convex.linear_image (LinearMap.fst ℝ ℝ ℝ)
    have hJn : J.Nonempty := P.nonempty.image Prod.fst
    have hI : J = Icc (sInf J) (sSup J) :=
      eq_Icc_of_connected_compact ⟨hJn, Real.convex_iff_isPreconnected.mp hJc⟩ hJ
    have hle : sInf J ≤ sSup J := csInf_le_csSup hJn hJ.bddBelow hJ.bddAbove
    have hwidth : width P = sSup J - sInf J := by
      first
      | change volume.real J = _
        calc
          volume.real J = volume.real (Icc (sInf J) (sSup J)) := congrArg volume.real hI
          _ = _ := Real.volume_real_Icc_of_le hle
    refine ⟨(sInf J, 0), ConvexBody.ext ?_⟩
    rw [coe_translateBody, rightTriangle_horizontal (show 0 ≤ width P from measureReal_nonneg)]
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      have hqJ : q.1 ∈ J := ⟨q, hq, rfl⟩
      rw [hI] at hqJ
      refine ⟨(q.1 - sInf J, 0), ⟨?_, rfl⟩, ?_⟩
      · rw [hwidth]
        exact ⟨by linarith [hqJ.1], by linarith [hqJ.2]⟩
      · ext <;> simp [diagonalLinear_apply] <;> ring
    · rintro ⟨q, ⟨hq, hq0⟩, rfl⟩
      change q.2 = 0 at hq0
      have hj : sInf J + q.1 ∈ J := by
        first
        | apply (congrArg (fun S : Set ℝ => sInf J + q.1 ∈ S) hI).mpr
          rw [hwidth] at hq
          constructor <;> linarith [hq.1, hq.2]
      obtain ⟨r, hr, hre⟩ := hj
      refine ⟨r, hr, ?_⟩
      ext <;> simp [diagonalLinear_apply, hq0, hre]

theorem mixedArea_verticalProjection (A P : ConvexBody Plane) :
    2 * mixedArea volume A (verticalProjection P) = height P * width A := by
  first
  | obtain ⟨v, hv⟩ := verticalProjection_eq_translate P
    rw [hv, mixedArea_translate_right]
    exact rightTriangle_axisY_mixedArea A measureReal_nonneg

theorem mixedArea_horizontalProjection (A P : ConvexBody Plane) :
    2 * mixedArea volume A (horizontalProjection P) = width P * height A := by
  first
  | obtain ⟨v, hv⟩ := horizontalProjection_eq_translate P
    rw [hv, mixedArea_translate_right]
    exact rightTriangle_axisX_mixedArea A measureReal_nonneg

def liftVertical : Plane →L[ℝ] Space :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).prod (0 : Plane →L[ℝ] Plane)

theorem liftVertical_rightTriangle : mapBody liftVertical (rightTriangle 1 0) = verticalUnit := by
  first
  | apply ConvexBody.ext
    rw [coe_mapBody, rightTriangle_horizontal (by norm_num : (0 : ℝ) ≤ 1)]
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨hq.1, rfl⟩
    · intro hp
      refine ⟨(p.1, 0), ⟨hp.1, rfl⟩, ?_⟩
      apply Prod.ext
      · rfl
      · exact hp.2.symm

theorem liftVertical_unitX :
    mapBody liftVertical unitX = translateBody (-(1 / 2), 0) verticalUnit := by
  first
  | have h := congrArg (mapBody liftVertical) (rightTriangle_zero_right 1)
    rw [liftVertical_rightTriangle, mapBody_translate] at h
    have hc : liftVertical ((1 / 2 : ℝ) • ((1, 0) : Plane)) = (1 / 2, 0) := by ext <;> simp [liftVertical]
    rw [hc] at h
    have h' := congrArg (translateBody (-(1 / 2), 0)) h
    simpa only [translateBody_translate, show ((-(1 / 2), 0) : Space) + (1 / 2, 0) = 0 by ext <;> norm_num,
      translateBody_zero, show PlanarCorner.segmentBody (1, 0) = unitX from rfl] using h'.symm

theorem mixed3_vertical_centered (B C : ConvexBody Space) :
    6 * mixed3 (mapBody liftVertical unitX) B C =
      2 * mixedArea volume (baseBody B) (baseBody C) := by
  first
  | rw [liftVertical_unitX]
    have h := mixed3_translate verticalUnit B C (-(1 / 2), 0) 0 0
    simp only [translateBody_zero] at h
    rw [h]
    exact mixed3_vertical_projection B C

theorem reframeX_unitX : mapBody reframeX.toContinuousLinearMap (mapBody embedXY unitX) =
    mapBody liftVertical unitX := by
  first
  | apply ConvexBody.ext
    simp only [coe_mapBody, Set.image_image]
    ext p
    constructor
    · rintro ⟨q, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨t • (1, 0), ⟨t, ht, rfl⟩, by ext <;> simp [reframeX, embedXY, liftVertical]⟩
    · rintro ⟨q, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨t • (1, 0), ⟨t, ht, rfl⟩, by ext <;> simp [reframeX, embedXY, liftVertical]⟩

theorem reframeY_unitY : mapBody reframeY.toContinuousLinearMap (mapBody embedXY unitY) =
    mapBody liftVertical unitX := by
  first
  | apply ConvexBody.ext
    simp only [coe_mapBody, Set.image_image]
    ext p
    constructor
    · rintro ⟨q, ⟨t, ht, rfl⟩, rfl⟩
      refine ⟨t • ((1, 0) : Plane), ⟨t, ht, rfl⟩, ?_⟩
      ext <;> simp [reframeY, embedXY, liftVertical]
    · rintro ⟨q, ⟨t, ht, rfl⟩, rfl⟩
      refine ⟨t • ((0, 1) : Plane), ⟨t, ht, rfl⟩, ?_⟩
      ext <;> simp [reframeY, embedXY, liftVertical]

theorem base_reframeX_YZ (B : ConvexBody Plane) :
    baseBody (mapBody reframeX.toContinuousLinearMap (mapBody embedYZ B)) = B := by
  first
  | apply ConvexBody.ext
    simp only [baseBody, coe_mapBody, Set.image_image]
    change id '' (B : Set Plane) = (B : Set Plane)
    exact Set.image_id _

theorem base_reframeX_XZ (C : ConvexBody Plane) :
    baseBody (mapBody reframeX.toContinuousLinearMap (mapBody embedXZ C)) = verticalProjection C := by
  first
  | apply ConvexBody.ext
    simp only [baseBody, verticalProjection, coe_mapBody, Set.image_image]
    congr 1
    funext p
    ext <;> simp [projectBase, reframeX, reframeY, embedXZ, embedYZ, diagonalLinear_apply]

theorem base_reframeY_YZ (B : ConvexBody Plane) :
    baseBody (mapBody reframeY.toContinuousLinearMap (mapBody embedYZ B)) = verticalProjection B := by
  first
  | apply ConvexBody.ext
    simp only [baseBody, verticalProjection, coe_mapBody, Set.image_image]
    congr 1
    funext p
    ext <;> simp [projectBase, reframeX, reframeY, embedXZ, embedYZ, diagonalLinear_apply]

theorem base_reframeY_XZ (C : ConvexBody Plane) :
    baseBody (mapBody reframeY.toContinuousLinearMap (mapBody embedXZ C)) = C := by
  first
  | apply ConvexBody.ext
    simp only [baseBody, coe_mapBody, Set.image_image]
    change id '' (C : Set Plane) = (C : Set Plane)
    exact Set.image_id _

theorem triple_unitX (B C : ConvexBody Plane) :
    6 * triple unitX B C = width B * height C := by
  first
  | have h := mixed3_map_measurePreserving reframeX reframeX_measurePreserving
      (mapBody embedXY unitX) (mapBody embedYZ B) (mapBody embedXZ C)
    rw [reframeX_unitX] at h
    change _ = triple unitX B C at h
    rw [← h, mixed3_vertical_centered, base_reframeX_YZ, base_reframeX_XZ,
      mixedArea_verticalProjection]
    ring

theorem triple_unitY (B C : ConvexBody Plane) :
    6 * triple unitY B C = height B * width C := by
  first
  | have h := mixed3_map_measurePreserving reframeY reframeY_measurePreserving
      (mapBody embedXY unitY) (mapBody embedYZ B) (mapBody embedXZ C)
    rw [reframeY_unitY] at h
    change _ = triple unitY B C at h
    rw [← h, mixed3_vertical_centered, base_reframeY_YZ, base_reframeY_XZ,
      mixedArea_symm, mixedArea_verticalProjection]

theorem base_XY (A : ConvexBody Plane) : baseBody (mapBody embedXY A) = A := by
  first
  | apply ConvexBody.ext
    simp only [baseBody, coe_mapBody, Set.image_image]
    change id '' (A : Set Plane) = (A : Set Plane)
    exact Set.image_id _

theorem base_YZ (B : ConvexBody Plane) :
    baseBody (mapBody embedYZ B) = verticalProjection (swapBody B) := by
  first
  | apply ConvexBody.ext
    simp only [baseBody, verticalProjection, swapBody, coe_mapBody, Set.image_image]
    congr 1
    funext p
    ext <;> simp [projectBase, embedYZ, diagonalLinear_apply]

theorem base_XZ (C : ConvexBody Plane) : baseBody (mapBody embedXZ C) = horizontalProjection C := by
  first
  | apply ConvexBody.ext
    simp only [baseBody, horizontalProjection, coe_mapBody, Set.image_image]
    congr 1
    funext p
    ext <;> simp [projectBase, embedXZ, diagonalLinear_apply]

theorem embedYZ_unitY : mapBody embedYZ unitY = mapBody liftVertical unitX := by
  first
  | apply ConvexBody.ext
    ext p
    constructor
    · rintro ⟨q, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨t • (1, 0), ⟨t, ht, rfl⟩, by ext <;> simp [embedYZ, liftVertical]⟩
    · rintro ⟨q, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨t • (0, 1), ⟨t, ht, rfl⟩, by ext <;> simp [embedYZ, liftVertical]⟩

theorem embedXZ_unitY : mapBody embedXZ unitY = mapBody liftVertical unitX := by
  first
  | apply ConvexBody.ext
    ext p
    constructor
    · rintro ⟨q, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨t • (1, 0), ⟨t, ht, rfl⟩, by ext <;> simp [embedXZ, liftVertical]⟩
    · rintro ⟨q, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨t • (0, 1), ⟨t, ht, rfl⟩, by ext <;> simp [embedXZ, liftVertical]⟩

theorem triple_middle_unitY (A C : ConvexBody Plane) :
    6 * triple A unitY C = height A * width C := by
  first
  | rw [triple, embedYZ_unitY, mixed3_swap_first, mixed3_vertical_centered,
      base_XY, base_XZ, mixedArea_horizontalProjection]
    ring

theorem triple_last_unitY (A B : ConvexBody Plane) :
    6 * triple A B unitY = width A * width B := by
  first
  | have hheight : height (swapBody B) = width B := by
      first
      | unfold height width swapBody
        simp only [coe_mapBody, Set.image_image]
        rfl
    rw [triple, embedXZ_unitY, mixed3_swap_last, mixed3_swap_first,
      mixed3_vertical_centered, base_XY, base_YZ, mixedArea_verticalProjection, hheight]
    ring

theorem triple_middle_unitX (A C : ConvexBody Plane) :
    6 * triple A unitX C = width A * height C := by
  first
  | have hB : mapBody embedYZ unitX = mapBody embedXY unitY := by
      first
      | apply ConvexBody.ext
        ext p
        constructor
        · rintro ⟨q, ⟨t, ht, rfl⟩, rfl⟩
          exact ⟨t • (0, 1), ⟨t, ht, rfl⟩, by ext <;> simp [embedYZ, embedXY]⟩
        · rintro ⟨q, ⟨t, ht, rfl⟩, rfl⟩
          exact ⟨t • (1, 0), ⟨t, ht, rfl⟩, by ext <;> simp [embedYZ, embedXY]⟩
    have hbase : baseBody (mapBody reframeY.toContinuousLinearMap (mapBody embedXY A)) =
        horizontalProjection A := by
      first
      | apply ConvexBody.ext
        simp only [baseBody, horizontalProjection, coe_mapBody, Set.image_image]
        congr 1
        funext p
        ext <;> simp [projectBase, reframeY, embedXY, diagonalLinear_apply]
    have ht := mixed3_map_measurePreserving reframeY reframeY_measurePreserving
      (mapBody embedXY unitY) (mapBody embedXY A) (mapBody embedXZ C)
    rw [reframeY_unitY] at ht
    rw [triple, hB, mixed3_swap_first, ← ht, mixed3_vertical_centered, hbase,
      base_reframeY_XZ, mixedArea_symm, mixedArea_horizontalProjection]

theorem triple_last_unitX (A B : ConvexBody Plane) :
    6 * triple A B unitX = height A * height B := by
  first
  | have hC : mapBody embedXZ unitX = mapBody embedXY unitX := by
      first
      | apply ConvexBody.ext
        ext p
        constructor
        · rintro ⟨q, ⟨t, ht, rfl⟩, rfl⟩
          exact ⟨t • (1, 0), ⟨t, ht, rfl⟩, by ext <;> simp [embedXZ, embedXY]⟩
        · rintro ⟨q, ⟨t, ht, rfl⟩, rfl⟩
          exact ⟨t • (1, 0), ⟨t, ht, rfl⟩, by ext <;> simp [embedXZ, embedXY]⟩
    have hbase' : baseBody (mapBody reframeX.toContinuousLinearMap (mapBody embedXY A)) =
        horizontalProjection (swapBody A) := by
      first
      | apply ConvexBody.ext
        simp only [baseBody, horizontalProjection, swapBody, coe_mapBody, Set.image_image]
        congr 1
        funext p
        ext <;> simp [projectBase, reframeX, embedXY, diagonalLinear_apply]
    have hw : width (swapBody A) = height A := by
      first
      | unfold width height swapBody
        simp only [coe_mapBody, Set.image_image]
        rfl
    have ht := mixed3_map_measurePreserving reframeX reframeX_measurePreserving
      (mapBody embedXY unitX) (mapBody embedXY A) (mapBody embedYZ B)
    rw [reframeX_unitX] at ht
    rw [triple, hC, mixed3_swap_last, mixed3_swap_first, ← ht,
      mixed3_vertical_centered, hbase', base_reframeX_YZ, mixedArea_symm,
      mixedArea_horizontalProjection, hw]


end VolumePolynomials.PlanarInteraction
