module

public import VolumePolynomials.CanonicalShapeTuple
public import VolumePolynomials.ShapeCalibrationVolume
public import VolumePolynomials.ShapeProjectionEvaluation
public import VolumePolynomials.HolonomyArea

@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped Pointwise

namespace VolumePolynomials.Holonomy

open ShapeConditions

theorem canonicalTuple_planarA (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1) :
    (planarA (canonicalTuple lam hlam₀ hlam₁) : Set Plane) =
      (forcedBody lam hlam₀ hlam₁ : Set Plane) := by
  first
  | change coordinateProjection 2 ''
      (placedA '' (forcedBody lam hlam₀ hlam₁ : Set Plane)) = _
    simp only [placedA, Set.image_image, Function.comp_apply,
      coordinateProjection_embedXY, Set.image_id']

theorem canonicalTuple_planarB (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1) :
    (planarB (canonicalTuple lam hlam₀ hlam₁) : Set Plane) =
      transport01 '' (forcedBody lam hlam₀ hlam₁ : Set Plane) := by
  first
  | change coordinateProjection 1 ''
      (placedB '' (forcedBody lam hlam₀ hlam₁ : Set Plane)) = _
    simp only [placedB, Set.image_image, Function.comp_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      coordinateProjection_embedXZ]

theorem canonicalTuple_planarC (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1) :
    (planarC (canonicalTuple lam hlam₀ hlam₁) : Set Plane) =
      transport12 '' (transport01 '' (forcedBody lam hlam₀ hlam₁ : Set Plane)) := by
  first
  | change coordinateProjection 0 ''
      (placedC '' (forcedBody lam hlam₀ hlam₁ : Set Plane)) = _
    simp only [placedC, Set.image_image, Function.comp_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      coordinateProjection_embedYZ]

theorem canonicalTuple_projectionAB (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1) :
    transport01 '' (planarB (canonicalTuple lam hlam₀ hlam₁) : Set Plane) =
      (forcedBody lam hlam₀ hlam₁ : Set Plane) := by
  first
  | rw [canonicalTuple_planarB]
    simp [Set.image_image, Function.comp_def, transport01_apply]

theorem canonicalTuple_projectionBC (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1) :
    transport12 '' (planarC (canonicalTuple lam hlam₀ hlam₁) : Set Plane) =
      (planarB (canonicalTuple lam hlam₀ hlam₁) : Set Plane) := by
  first
  | rw [canonicalTuple_planarC, canonicalTuple_planarB]
    have h12 (p : Plane) : transport12 (transport12 p) = p := by
      ext <;> simp only [transport12_apply, neg_neg]
    rw [Set.image_image]
    simp only [h12, Set.image_id']

theorem canonicalTuple_projectionAD (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1) :
    lastProjectedSet lam (planarC (canonicalTuple lam hlam₀ hlam₁)) =
      (forcedBody lam hlam₀ hlam₁ : Set Plane) := by
  first
  | rw [canonicalTuple_planarC, lastProjectedSet, image_transport_cycle,
      ← forcedBody_fixed lam hlam₀ hlam₁]

theorem area_double_convex {A : Set Plane} (hA : Convex ℝ A) :
    volume.real (A + A) = 4 * volume.real A := by
  first
  | have hsum : A + A = (2 : ℝ) • A := by
      simpa only [one_smul, one_add_one_eq_two] using
        (hA.add_smul (show (0 : ℝ) ≤ 1 by norm_num) (show (0 : ℝ) ≤ 1 by norm_num)).symm
    have hdim : Module.finrank ℝ Plane = 2 := by simp [Plane, Module.finrank_prod]
    rw [hsum]
    change (volume ((2 : ℝ) • A)).toReal = 4 * (volume A).toReal
    rw [Measure.addHaar_smul_of_nonneg volume (show (0 : ℝ) ≤ 2 by norm_num),
      hdim, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num)]
    norm_num

/-- The explicit nine-body construction satisfies every equation and every
strict inequality of the finite rational system throughout the full interval. -/
theorem canonicalTuple_ordinaryConditions (lam : ℝ) (hlam₀ : 0 < lam) (hlam₁ : lam < 1) :
    OrdinaryConditions lam (volume.real (forcedBody lam hlam₀.le hlam₁ : Set Plane))
      (volumeFunction (canonicalTuple lam hlam₀.le hlam₁)) := by
  first
  | let K := canonicalTuple lam hlam₀.le hlam₁
    have hK : IsCalibratedTuple K := canonicalTuple_calibrated lam hlam₀.le hlam₁
    have hPA : (planarA K : Set Plane) = (forcedBody lam hlam₀.le hlam₁ : Set Plane) :=
      canonicalTuple_planarA lam hlam₀.le hlam₁
    have hPB : (planarB K : Set Plane) = transport01 '' (forcedBody lam hlam₀.le hlam₁ : Set Plane) :=
      canonicalTuple_planarB lam hlam₀.le hlam₁
    have hPC : (planarC K : Set Plane) =
        transport12 '' (transport01 '' (forcedBody lam hlam₀.le hlam₁ : Set Plane)) :=
      canonicalTuple_planarC lam hlam₀.le hlam₁
    have hAB := canonicalTuple_projectionAB lam hlam₀.le hlam₁
    have hBC := canonicalTuple_projectionBC lam hlam₀.le hlam₁
    have hAD := canonicalTuple_projectionAD lam hlam₀.le hlam₁
    have hpos := forcedBody_area_positive lam hlam₀ hlam₁
    change OrdinaryConditions lam (volume.real (forcedBody lam hlam₀.le hlam₁ : Set Plane))
      (volumeFunction K)
    refine ⟨?_, ?_, ?_⟩
    · intro i j
      have hs : K (segmentIndex i) = centeredBody (calibratedDirection i) := hK.segments i
      have hf : K (frameIndex j) = centeredBody (axis j) := by
        fin_cases j <;> rfl
      rw [volumeFunction, weightedSum_two, hs, hf, volume_two_centered_segments]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · norm_num [volumeFunction, weightedSum_three, K, canonicalTuple, e₁, e₂, e₃,
          volume_three_centered_segments, determinant3, axis, Pi.single_apply]
      · norm_num [volumeFunction, weightedSum_three, K, canonicalTuple, sᵥ, e₂, e₃,
          volume_three_centered_segments, determinant3, directionV, axis, Pi.single_apply]
      · norm_num [volumeFunction, weightedSum_three, K, canonicalTuple, sᵥ, e₁, e₃,
          volume_three_centered_segments, determinant3, directionV, axis, Pi.single_apply]
      · norm_num [volumeFunction, weightedSum_three, K, canonicalTuple, sᵥ, e₁, e₂,
          volume_three_centered_segments, determinant3, directionV, axis, Pi.single_apply]
      · norm_num [volumeFunction, weightedSum_three, K, canonicalTuple, s𝓌, e₂, e₃,
          volume_three_centered_segments, determinant3, directionW, axis, Pi.single_apply]
      · norm_num [volumeFunction, weightedSum_three, K, canonicalTuple, s𝓌, e₁, e₃,
          volume_three_centered_segments, determinant3, directionW, axis, Pi.single_apply]
      · norm_num [volumeFunction, weightedSum_three, K, canonicalTuple, s𝓌, e₁, e₂,
          volume_three_centered_segments, determinant3, directionW, axis, Pi.single_apply]
      · norm_num [volumeFunction, weightedSum_three, K, canonicalTuple, s𝓏, e₂, e₃,
          volume_three_centered_segments, determinant3, directionZ, axis, Pi.single_apply]
      · norm_num [volumeFunction, weightedSum_three, K, canonicalTuple, s𝓏, e₁, e₃,
          volume_three_centered_segments, determinant3, directionZ, axis, Pi.single_apply]
      · norm_num [volumeFunction, weightedSum_three, K, canonicalTuple, s𝓏, e₁, e₂,
          volume_three_centered_segments, determinant3, directionZ, axis, Pi.single_apply]
      · rw [volumeFunction, weightedSum_three]
        change bodyVolume (centeredBody directionV + centeredBody directionW + centeredBody directionZ) = _
        rw [volume_three_centered_segments, calibrated_determinant]
      · simpa only [volumeFunction, weightedSum_three] using hK.volume_planeA
      · simpa only [volumeFunction, weightedSum_three] using hK.volume_planeB
      · simpa only [volumeFunction, weightedSum_three] using hK.volume_planeC
      · rw [hK.extrusion_VA, hK.extrusion_VB, hPA, hAB]
      · rw [hK.extrusion_VAB, hK.extrusion_VA, hPA, hAB]
        exact area_double_convex (forcedBody lam hlam₀.le hlam₁).convex
      · rw [hK.extrusion_WB, hK.extrusion_WC, hBC]
      · rw [hK.extrusion_WBC, hK.extrusion_WB, hBC]
        exact area_double_convex (planarB K).convex
      · rw [hK.extrusion_ZA, hK.extrusion_ZD lam hlam₀.le, hPA, hAD]
      · rw [hK.extrusion_ZAD lam hlam₀.le, hK.extrusion_ZA, hPA, hAD]
        exact area_double_convex (forcedBody lam hlam₀.le hlam₁).convex
      · rw [hK.extrusion_axisA, hPA]
    · refine ⟨hlam₀, hlam₁, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [hK.extrusion_axisA, hPA] using hpos
      · simpa only [hK.extrusion_axisB, hPB, area_transport01] using hpos
      · simpa only [hK.extrusion_axisC, hPC, area_transport12, area_transport01] using hpos
      · simpa only [hK.extrusion_VA, hPA] using hpos
      · simpa only [hK.extrusion_WB, hPB, area_transport01] using hpos
      · simpa only [hK.extrusion_ZA, hPA] using hpos

theorem canonicalTuple_feasible (lam : ℝ) (hlam₀ : 0 < lam) (hlam₁ : lam < 1) :
    Feasible lam (realAreaSeries angle lam) := by
  first
  | obtain ⟨c, hc⟩ := canonicalTuple_realizes lam hlam₀.le hlam₁
    refine ⟨c, ⟨canonicalTuple lam hlam₀.le hlam₁, hc⟩, ?_⟩
    apply (holds_iff_ordinary_volume hlam₀.le hc).mpr
    rw [← forcedBody_area lam hlam₀.le hlam₁]
    exact canonicalTuple_ordinaryConditions lam hlam₀ hlam₁


end VolumePolynomials.Holonomy
