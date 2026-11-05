module

public import Projection.HeightDensity
public import Projection.Rigidity.DilationSandwich
public import TauCeti.Probability.Quantile.Map
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory ProbabilityTheory TauCeti Filter
open scoped Pointwise RealInnerProductSpace Topology

namespace RankThreeProjection.QuantileStability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def heightCDF (K : Set E) (e : E) (s : ℝ) : ℝ :=
  cdf ((volume[|K]).map fun x => ⟪e, x⟫) s

private theorem volumeReal_smul (S : Set E) {scale : ℝ} (hscale : 0 ≤ scale) :
    volume.real (scale • S) = scale ^ Module.finrank ℝ E * volume.real S := by
  simp only [Measure.real]
  rw [Measure.addHaar_smul_of_nonneg volume hscale, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hscale _)]

private theorem volumeReal_height_smul (K : ConvexBody E) (e : E)
    {scale : ℝ} (hscale : 0 < scale) (s : ℝ) :
    volume.real {x ∈ ((scale • K : ConvexBody E) : Set E) | ⟪e, x⟫ ≤ scale * s} =
      scale ^ Module.finrank ℝ E * volume.real {x ∈ (K : Set E) | ⟪e, x⟫ ≤ s} := by
  have hset : {x ∈ ((scale • K : ConvexBody E) : Set E) | ⟪e, x⟫ ≤ scale * s} =
      scale • {x ∈ (K : Set E) | ⟪e, x⟫ ≤ s} := by
    ext x
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hys⟩
      refine ⟨y, ⟨hy, ?_⟩, rfl⟩
      exact (mul_le_mul_iff_of_pos_left hscale).mp
        (by simpa only [real_inner_smul_right] using hys)
    · rintro ⟨y, ⟨hy, hys⟩, rfl⟩
      exact ⟨⟨y, hy, rfl⟩, by
        simpa only [real_inner_smul_right] using mul_le_mul_of_nonneg_left hys hscale.le⟩
  rw [hset, volumeReal_smul _ hscale.le]

/-- CDF comparisons obtained directly from the nested actual bodies
`K ⊆ L ⊆ scale • K`. The factor `scale^dim` accounts for normalization of volume. -/
theorem heightCDF_dilation_bounds (K L : ConvexBody E) (e : E)
    (hK : volume (K : Set E) ≠ 0) {scale : ℝ} (hscale : 0 < scale)
    (hKL : K ≤ L) (hLK : L ≤ scale • K) (s : ℝ) :
    heightCDF (K : Set E) e s / scale ^ Module.finrank ℝ E ≤ heightCDF (L : Set E) e s ∧
      heightCDF (L : Set E) e (scale * s) ≤
        scale ^ Module.finrank ℝ E * heightCDF (K : Set E) e s := by
  have hL : volume (L : Set E) ≠ 0 :=
    ne_of_gt ((pos_iff_ne_zero.mpr hK).trans_le (measure_mono hKL))
  have hV : 0 < volume.real (K : Set E) :=
    ENNReal.toReal_pos hK K.isCompact.measure_lt_top.ne
  have hW : 0 < volume.real (L : Set E) :=
    ENNReal.toReal_pos hL L.isCompact.measure_lt_top.ne
  have hpow : 0 < scale ^ Module.finrank ℝ E := pow_pos hscale _
  have hVW : volume.real (K : Set E) ≤ volume.real (L : Set E) :=
    measureReal_mono hKL L.isCompact.measure_lt_top.ne
  have hWV : volume.real (L : Set E) ≤
      volume.real (K : Set E) * scale ^ Module.finrank ℝ E := by
    have h := measureReal_mono (μ := volume) hLK (scale • K).isCompact.measure_lt_top.ne
    rw [ConvexBody.coe_smul, volumeReal_smul _ hscale.le] at h
    simpa only [mul_comm] using h
  have hsmall : volume.real {x ∈ (K : Set E) | ⟪e, x⟫ ≤ s} ≤
      volume.real {x ∈ (L : Set E) | ⟪e, x⟫ ≤ s} :=
    measureReal_mono (μ := volume) (fun x hx => ⟨hKL hx.1, hx.2⟩)
      (measure_lt_top_of_subset (μ := volume)
        (fun x (hx : x ∈ {x ∈ (L : Set E) | ⟪e, x⟫ ≤ s}) => hx.1)
        L.isCompact.measure_lt_top.ne).ne
  have hlarge : volume.real {x ∈ (L : Set E) | ⟪e, x⟫ ≤ scale * s} ≤
      scale ^ Module.finrank ℝ E * volume.real {x ∈ (K : Set E) | ⟪e, x⟫ ≤ s} := by
    have h := measureReal_mono (μ := volume)
      (fun x (hx : x ∈ {x ∈ (L : Set E) | ⟪e, x⟫ ≤ scale * s}) =>
      (show x ∈ {x ∈ ((scale • K : ConvexBody E) : Set E) | ⟪e, x⟫ ≤ scale * s} from
        ⟨hLK hx.1, hx.2⟩))
      (measure_lt_top_of_subset (μ := volume)
        (fun x (hx : x ∈ {x ∈ ((scale • K : ConvexBody E) : Set E) |
          ⟪e, x⟫ ≤ scale * s}) => hx.1)
        (scale • K).isCompact.measure_lt_top.ne).ne
    rw [volumeReal_height_smul K e hscale s] at h
    exact h
  simp only [heightCDF, cdf_map_inner_cond hK K.isCompact.measure_lt_top.ne,
    cdf_map_inner_cond hL L.isCompact.measure_lt_top.ne]
  constructor
  · rw [div_div]
    apply (div_le_div_iff₀ (mul_pos hV hpow) hW).mpr
    exact (mul_le_mul_of_nonneg_left hWV measureReal_nonneg).trans
      (mul_le_mul_of_nonneg_right hsmall (mul_nonneg hV.le hpow.le))
  · rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hW hV).mpr
    exact (mul_le_mul_of_nonneg_left hVW measureReal_nonneg).trans
      (mul_le_mul_of_nonneg_right hlarge hW.le)

theorem abs_heightQuantile_lt_of_radius (K : ConvexBody E) {e : E} (he : ‖e‖ = 1)
    (hK : volume (K : Set E) ≠ 0) (R : ℝ)
    (hR : ∀ x ∈ (K : Set E), ‖x‖ < R) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    |heightQuantile (K : Set E) e t| < R := by
  obtain ⟨x, hx, heq⟩ := K.convex.quantile_map_inner_cond_mem_image_interior he hK
    K.isCompact.measure_lt_top.ne ht
  unfold heightQuantile
  rw [← heq]
  exact (abs_real_inner_le_norm e x).trans_lt
    (by simpa only [he, one_mul] using hR x (interior_subset hx))

/-- Reflection exchanges the two probability tails exactly. -/
theorem heightQuantile_neg (K : ConvexBody E) {e : E} (he : ‖e‖ = 1)
    (hK : volume (K : Set E) ≠ 0) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    heightQuantile (K : Set E) (-e) t = -heightQuantile (K : Set E) e (1 - t) := by
  let ν := (volume[|(K : Set E)]).map fun x => ⟪e, x⟫
  haveI := cond_isProbabilityMeasure_of_finite hK K.isCompact.measure_lt_top.ne
  have hmap : (volume[|(K : Set E)]).map (fun x => ⟪-e, x⟫) = ν.neg := by
    dsimp only [ν]
    have hmeas : Measurable (fun x : E => ⟪e, x⟫) :=
      (continuous_const.inner continuous_id).measurable
    rw [Measure.neg_def, Measure.map_map measurable_neg hmeas]
    congr 1
    funext x
    simp only [Function.comp_apply, inner_neg_left]
  change ((volume[|(K : Set E)]).map (fun x => ⟪-e, x⟫)).quantile t = -ν.quantile (1 - t)
  rw [hmap, Measure.quantile_neg ht.1 ht.2]
  congr 1
  apply Measure.upperQuantile_eq_of_cdf_eq ν
    (K.convex.strictMonoOn_cdf_map_inner_cond he hK K.isCompact.measure_lt_top.ne)
  · exact Measure.cdf_quantile ν
      (continuous_cdf_map_inner_cond he hK K.isCompact.measure_lt_top.ne)
      (by linarith [ht.2]) (by linarith [ht.1])
  · exact ⟨by linarith [ht.2], by linarith [ht.1]⟩

private theorem heightQuantile_dilation_bound_left (K L : ConvexBody E)
    {e : E} (he : ‖e‖ = 1) (hdim : 2 ≤ Module.finrank ℝ E)
    (hK : volume (K : Set E) ≠ 0) (R : ℝ)
    (hR : ∀ x ∈ (K : Set E), ‖x‖ < R)
    {scale : ℝ} (hscale1 : 1 ≤ scale) (hpow : scale ^ Module.finrank ℝ E ≤ 3 / 2)
    (hKL : K ≤ L) (hLK : L ≤ scale • K)
    {t : ℝ} (ht : 0 < t) (ht2 : t ≤ 1 / 2) :
    |heightQuantile (L : Set E) e t - heightQuantile (K : Set E) e t| ≤
      R * (scale - 1) + 4 * R * (scale ^ Module.finrank ℝ E - 1) := by
  let Λ := scale ^ Module.finrank ℝ E
  let q := heightQuantile (K : Set E) e
  let v := heightQuantileSlope (K : Set E) e
  have hscale : 0 < scale := zero_lt_one.trans_le hscale1
  have hΛ1 : 1 ≤ Λ := one_le_pow₀ hscale1
  have hΛ : 0 < Λ := pow_pos hscale _
  have hΛ2 : Λ ≤ 3 / 2 := hpow
  have hL : volume (L : Set E) ≠ 0 :=
    ne_of_gt ((pos_iff_ne_zero.mpr hK).trans_le (measure_mono hKL))
  have htI : t ∈ Ioo (0 : ℝ) 1 := ⟨ht, by linarith⟩
  have hlowI : t / Λ ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos ht hΛ, (div_lt_iff₀ hΛ).mpr (by linarith)⟩
  have hhighI : Λ * t ∈ Ioo (0 : ℝ) 1 := ⟨mul_pos hΛ ht, by nlinarith⟩
  have hbaseCDF (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) :
      heightCDF (K : Set E) e (q u) = u :=
    Measure.cdf_quantile _ (continuous_cdf_map_inner_cond he hK K.isCompact.measure_lt_top.ne)
      hu.1 hu.2
  have hlow : scale * q (t / Λ) ≤ heightQuantile (L : Set E) e t := by
    have h := (heightCDF_dilation_bounds K L e hK hscale hKL hLK (q (t / Λ))).2
    rw [hbaseCDF _ hlowI] at h
    have heq : Λ * (t / Λ) = t := mul_div_cancel₀ _ hΛ.ne'
    change heightCDF (L : Set E) e (scale * q (t / Λ)) ≤ Λ * (t / Λ) at h
    rw [heq] at h
    by_contra hn
    have hlt := (Measure.quantile_lt_iff
      ((volume[|(L : Set E)]).map fun x => ⟪e, x⟫)
      (continuous_cdf_map_inner_cond he hL L.isCompact.measure_lt_top.ne)
      (L.convex.strictMonoOn_cdf_map_inner_cond he hL L.isCompact.measure_lt_top.ne)
      htI.1 htI.2).mp (lt_of_not_ge hn)
    exact (not_lt_of_ge h) hlt
  have hhigh : heightQuantile (L : Set E) e t ≤ q (Λ * t) := by
    apply (Measure.quantile_le_iff _ htI.1 htI.2).mpr
    have h := (heightCDF_dilation_bounds K L e hK hscale hKL hLK (q (Λ * t))).1
    rw [hbaseCDF _ hhighI] at h
    have heq : (Λ * t) / Λ = t := mul_div_cancel_left₀ _ hΛ.ne'
    change (Λ * t) / Λ ≤ _ at h
    rwa [heq] at h
  obtain ⟨x, hx⟩ := K.nonempty
  have hRpos : 0 < R := (norm_nonneg x).trans_lt (hR x hx)
  have hderiv (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) : HasDerivAt q (v u) u :=
    hasDerivAt_heightQuantile K he hK hu
  have hv (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) : 0 ≤ v u :=
    div_nonneg measureReal_nonneg measureReal_nonneg
  have hweighted (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) : min u (1 - u) * v u ≤ 2 * R :=
    weighted_heightQuantileSlope_le K he hdim hK R hR hu
  have hlh : t / Λ ≤ Λ * t :=
    (show t / Λ ≤ t from (div_le_iff₀ hΛ).mpr (by nlinarith)).trans (by nlinarith)
  have hinc₀ := quantile_multiplicative_increment q v (2 * R) (by linarith)
    hderiv hv hweighted ht ht2 hΛ1 hΛ2 (left_mem_Icc.mpr hlh)
  have hinc₁ := quantile_multiplicative_increment q v (2 * R) (by linarith)
    hderiv hv hweighted ht ht2 hΛ1 hΛ2 (right_mem_Icc.mpr hlh)
  have hqR := abs_heightQuantile_lt_of_radius K he hK R hR hlowI
  have hscaled := mul_le_mul_of_nonneg_left (abs_lt.mp hqR).1.le (sub_nonneg.mpr hscale1)
  rw [abs_le] at hinc₀ hinc₁ ⊢
  constructor
  · nlinarith [hinc₀.1]
  · nlinarith [hinc₁.2, mul_nonneg hRpos.le (sub_nonneg.mpr hscale1)]

/-- Uniform quantile control, including both extreme probability tails.
The displacement bound tends linearly to zero as the dilation tends to one. -/
theorem heightQuantile_dilation_bound (K L : ConvexBody E)
    {e : E} (he : ‖e‖ = 1) (hdim : 2 ≤ Module.finrank ℝ E)
    (hK : volume (K : Set E) ≠ 0) (R : ℝ)
    (hR : ∀ x ∈ (K : Set E), ‖x‖ < R)
    {scale : ℝ} (hscale1 : 1 ≤ scale) (hpow : scale ^ Module.finrank ℝ E ≤ 3 / 2)
    (hKL : K ≤ L) (hLK : L ≤ scale • K)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    |heightQuantile (L : Set E) e t - heightQuantile (K : Set E) e t| ≤
      R * (scale - 1) + 4 * R * (scale ^ Module.finrank ℝ E - 1) := by
  by_cases ht2 : t ≤ 1 / 2
  · exact heightQuantile_dilation_bound_left K L he hdim hK R hR hscale1 hpow hKL hLK ht.1 ht2
  · have hL : volume (L : Set E) ≠ 0 :=
      ne_of_gt ((pos_iff_ne_zero.mpr hK).trans_le (measure_mono hKL))
    have hneg : ‖-e‖ = 1 := by simpa only [norm_neg] using he
    have ht' : 1 - t ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have h := heightQuantile_dilation_bound_left K L hneg hdim hK R hR
      hscale1 hpow hKL hLK ht'.1 (by linarith)
    rw [heightQuantile_neg L he hL ht', heightQuantile_neg K he hK ht'] at h
    simpa only [sub_sub_cancel, neg_sub_neg, abs_sub_comm] using h

end RankThreeProjection.QuantileStability
