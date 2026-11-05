module

public import Projection.KneserSuss
public import Projection.QuantitativeAMGM
public import Mathlib.Analysis.Convex.Body
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Tactic.FieldSimp

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory ProbabilityTheory TauCeti
open scoped Pointwise RealInnerProductSpace

namespace RankThreeProjection.QuantileStability

/-- The exact normalized arithmetic–geometric mean integrand. -/
def midpointRatio (x y : ℝ) : ℝ := (x + y) / (2 * Real.sqrt (x * y))

private theorem one_le_midpointRatio {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    1 ≤ midpointRatio x y := by
  have h := Projection.quantitative_amgm x y (x + y) hx hy
    (by linarith) (by linarith)
  have hz : 0 ≤ (x - y) ^ 2 / (8 * (x + y) ^ 2) :=
    div_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (sq_nonneg _))
  change _ ≤ midpointRatio x y - 1 at h
  linarith

/-- The Kneser–Süss bound controls the squared difference of the two quantile
derivatives on every compact probability interval. The right side is the
actual volume deficit, so a deficit `o(t²)` gives energy `o(t²)`. -/
theorem midpoint_gap_energy_le (x y : ℝ → ℝ) (c V M a b : ℝ)
    (hc : 0 < c) (hV : 0 ≤ V) (hM : 0 < M)
    (hcx : ContinuousOn x (Ioo (0 : ℝ) 1))
    (hcy : ContinuousOn y (Ioo (0 : ℝ) 1))
    (hx : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < x t)
    (hy : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < y t)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1)
    (hxM : ∀ t ∈ Icc a b, x t ≤ M) (hyM : ∀ t ∈ Icc a b, y t ≤ M)
    (hKS : (∫⁻ t in Ioo (0 : ℝ) 1,
      ENNReal.ofReal (c * midpointRatio (x t) (y t))) ≤ ENNReal.ofReal V) :
    c / (8 * M ^ 2) * (∫ t in Icc a b, (x t - y t) ^ 2) ≤ V - c := by
  let U := Ioo (0 : ℝ) 1
  let g : ℝ → ℝ := fun t => c * midpointRatio (x t) (y t)
  letI : IsFiniteMeasure (volume.restrict U) := ⟨by simp [U, Real.volume_Ioo]⟩
  have hsub : Icc a b ⊆ U := fun t ht => ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩
  have hbase (t : ℝ) (ht : t ∈ U) : c ≤ g t := by
    have h := mul_le_mul_of_nonneg_left (one_le_midpointRatio (hx t ht) (hy t ht)) hc.le
    simpa only [mul_one, g] using h
  have hgnonneg : 0 ≤ᵐ[volume.restrict U] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hc.le.trans (hbase t ht)
  have hgcont : ContinuousOn g U := by
    apply continuousOn_const.mul
    apply (hcx.add hcy).div ((hcx.mul hcy).sqrt.const_mul 2)
    intro t ht
    exact mul_ne_zero (by linarith)
      (Real.sqrt_pos.mpr (mul_pos (hx t ht) (hy t ht))).ne'
  have hgi : IntegrableOn g U :=
    ⟨(hgcont.aemeasurable measurableSet_Ioo).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hgnonneg).mpr
        (hKS.trans_lt ENNReal.ofReal_lt_top)⟩
  have hIg : (∫ t in U, g t) ≤ V := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hKS
    rw [← ofReal_integral_eq_lintegral_ofReal hgi hgnonneg,
      ENNReal.toReal_ofReal (integral_nonneg_of_ae hgnonneg),
      ENNReal.toReal_ofReal hV] at h
    exact h
  have hgapint : IntegrableOn (fun t => g t - c) U := hgi.sub (integrable_const c)
  have hgapnonneg : 0 ≤ᵐ[volume.restrict U] (fun t => g t - c) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact sub_nonneg.mpr (hbase t ht)
  have hgap : (∫ t in U, g t - c) ≤ V - c := by
    rw [integral_sub hgi (integrable_const c)]
    have hcI : (∫ _t in U, c) = c := by simp [U, Real.volume_Ioo]
    rw [hcI]
    exact sub_le_sub_right hIg c
  have henergyint : IntegrableOn
      (fun t => (c / (8 * M ^ 2)) * (x t - y t) ^ 2) (Icc a b) :=
    (((hcx.mono hsub).sub (hcy.mono hsub)).pow 2 |>.const_mul _).integrableOn_Icc
  have hpoint (t : ℝ) (ht : t ∈ Icc a b) :
      (c / (8 * M ^ 2)) * (x t - y t) ^ 2 ≤ g t - c := by
    have h := mul_le_mul_of_nonneg_left
      (Projection.quantitative_amgm (x t) (y t) M (hx t (hsub ht))
        (hy t (hsub ht)) (hxM t ht) (hyM t ht)) hc.le
    change _ ≤ c * (midpointRatio (x t) (y t) - 1) at h
    calc
      (c / (8 * M ^ 2)) * (x t - y t) ^ 2 =
          c * ((x t - y t) ^ 2 / (8 * M ^ 2)) := by ring
      _ ≤ c * (midpointRatio (x t) (y t) - 1) := h
      _ = g t - c := by dsimp only [g]; ring
  have hsmall := setIntegral_mono_on henergyint (hgapint.mono_set hsub)
    measurableSet_Icc hpoint
  have hlarge := setIntegral_mono_set hgapint hgapnonneg
    (Filter.Eventually.of_forall (fun t ht => hsub ht))
  rw [integral_const_mul] at hsmall
  exact hsmall.trans (hlarge.trans hgap)

private theorem midpoint_integrand_identity (v w a b : ℝ)
    (hv : 0 < v) (hw : 0 < w) (ha : 0 < a) (hb : 0 < b) :
    ((v / a + w / b) / 2) * (Real.sqrt a * Real.sqrt b) =
      Real.sqrt (v * w) * midpointRatio (v / a) (w / b) := by
  have hs : Real.sqrt ((v / a) * (w / b)) =
      Real.sqrt (v * w) / (Real.sqrt a * Real.sqrt b) := by
    rw [div_mul_div_comm, Real.sqrt_div (mul_nonneg hv.le hw.le), Real.sqrt_mul ha.le]
  unfold midpointRatio
  rw [hs]
  field_simp [(Real.sqrt_pos.mpr (mul_pos hv hw)).ne',
    (Real.sqrt_pos.mpr ha).ne', (Real.sqrt_pos.mpr hb).ne']
  <;> ring

section ConvexBodies

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def heightQuantile (K : Set E) (e : E) : ℝ → ℝ :=
  ((volume[|K]).map fun x => ⟪e, x⟫).quantile

def sectionAtQuantile (K : Set E) (e : E) (t : ℝ) : ℝ :=
  volume.real {y : (ℝ ∙ e)ᗮ | (y : E) + heightQuantile K e t • e ∈ K}

def heightQuantileSlope (K : Set E) (e : E) (t : ℝ) : ℝ :=
  volume.real K / sectionAtQuantile K e t

theorem hasDerivAt_heightQuantile (K : ConvexBody E) {e : E} (he : ‖e‖ = 1)
    (hK : volume (K : Set E) ≠ 0) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (heightQuantile (K : Set E) e)
      (heightQuantileSlope (K : Set E) e t) t :=
  K.convex.hasDerivAt_quantile_map_inner_cond K.isCompact.isBounded
    K.isCompact.measurableSet hK he ht

theorem heightQuantileSlope_pos (K : ConvexBody E) {e : E} (he : ‖e‖ = 1)
    (hK : volume (K : Set E) ≠ 0) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < heightQuantileSlope (K : Set E) e t :=
  div_pos (ENNReal.toReal_pos hK K.isCompact.measure_lt_top.ne)
    (K.convex.volume_real_hyperplaneSection_quantile_pos K.isCompact.isBounded hK he ht)

theorem continuousOn_heightQuantileSlope (K : ConvexBody E) {e : E} (he : ‖e‖ = 1)
    (hK : volume (K : Set E) ≠ 0) :
    ContinuousOn (heightQuantileSlope (K : Set E) e) (Ioo (0 : ℝ) 1) := by
  exact continuousOn_const.div
    (K.convex.continuousOn_volume_real_hyperplaneSection_quantile K.isCompact.isBounded hK he)
    (fun t ht =>
      (K.convex.volume_real_hyperplaneSection_quantile_pos K.isCompact.isBounded hK he ht).ne')

theorem continuousOn_heightQuantile (K : ConvexBody E) {e : E} (he : ‖e‖ = 1)
    (hK : volume (K : Set E) ≠ 0) :
    ContinuousOn (heightQuantile (K : Set E) e) (Ioo (0 : ℝ) 1) :=
  HasDerivAt.continuousOn (fun _ ht => hasDerivAt_heightQuantile K he hK ht)

theorem integrableOn_heightQuantile (K : ConvexBody E) (e : E)
    (hK : volume (K : Set E) ≠ 0) :
    IntegrableOn (heightQuantile (K : Set E) e) (Ioo (0 : ℝ) 1) :=
  integrableOn_quantile_map_inner_cond e K.isCompact.isBounded K.isCompact.measurableSet hK

theorem integral_heightQuantile (K : ConvexBody E) (e : E)
    (hK : volume (K : Set E) ≠ 0) :
    (∫ t in Ioo (0 : ℝ) 1, heightQuantile (K : Set E) e t) =
      ∫ x, ⟪e, x⟫ ∂volume[|(K : Set E)] := by
  haveI := cond_isProbabilityMeasure_of_finite hK K.isCompact.measure_lt_top.ne
  change (∫ t in Ioo (0 : ℝ) 1,
    ((volume[|(K : Set E)]).map fun x => ⟪e, x⟫).quantile t) = _
  rw [Measure.setIntegral_quantile_eq_integral]
  exact integral_map (continuous_const.inner continuous_id).measurable.aemeasurable
    aestronglyMeasurable_id

/-- Quantitative Kneser–Süss for actual compact convex bodies, with no
assumed relation between height quantiles and sections. -/
theorem convexBody_midpoint_quantile_energy (K L : ConvexBody E)
    {e : E} (he : ‖e‖ = 1) (hK : volume (K : Set E) ≠ 0)
    (hL : volume (L : Set E) ≠ 0) (M a b : ℝ) (hM : 0 < M)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1)
    (hxM : ∀ t ∈ Icc a b, heightQuantileSlope (K : Set E) e t ≤ M)
    (hyM : ∀ t ∈ Icc a b, heightQuantileSlope (L : Set E) e t ≤ M) :
    Real.sqrt (volume.real (K : Set E) * volume.real (L : Set E)) / (8 * M ^ 2) *
        (∫ t in Icc a b,
          (heightQuantileSlope (K : Set E) e t - heightQuantileSlope (L : Set E) e t) ^ 2) ≤
      volume.real (((1 / 2 : ℝ) • K + (1 / 2 : ℝ) • L : ConvexBody E) : Set E) -
        Real.sqrt (volume.real (K : Set E) * volume.real (L : Set E)) := by
  let V := volume.real (K : Set E)
  let W := volume.real (L : Set E)
  have hV : 0 < V := ENNReal.toReal_pos hK K.isCompact.measure_lt_top.ne
  have hW : 0 < W := ENNReal.toReal_pos hL L.isCompact.measure_lt_top.ne
  have hsectionK (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      0 < sectionAtQuantile (K : Set E) e t :=
    K.convex.volume_real_hyperplaneSection_quantile_pos K.isCompact.isBounded hK he ht
  have hsectionL (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      0 < sectionAtQuantile (L : Set E) e t :=
    L.convex.volume_real_hyperplaneSection_quantile_pos L.isCompact.isBounded hL he ht
  apply midpoint_gap_energy_le
    (heightQuantileSlope (K : Set E) e) (heightQuantileSlope (L : Set E) e)
    (Real.sqrt (V * W)) _ M a b (Real.sqrt_pos.mpr (mul_pos hV hW))
    measureReal_nonneg hM
  · exact continuousOn_const.div
      (K.convex.continuousOn_volume_real_hyperplaneSection_quantile
        K.isCompact.isBounded hK he) (fun t ht => (hsectionK t ht).ne')
  · exact continuousOn_const.div
      (L.convex.continuousOn_volume_real_hyperplaneSection_quantile
        L.isCompact.isBounded hL he) (fun t ht => (hsectionL t ht).ne')
  · exact fun t ht => div_pos hV (hsectionK t ht)
  · exact fun t ht => div_pos hW (hsectionL t ht)
  · exact ha
  · exact hab
  · exact hb
  · exact hxM
  · exact hyM
  · have hKS := KneserSuss.setLIntegral_ofReal_le_volume_smul_add_smul
      K.convex K.isCompact.isBounded K.isCompact.measurableSet hK
      L.convex L.isCompact.isBounded L.isCompact.measurableSet hL he
      (θ := (1 / 2 : ℝ)) (by linarith) (by linarith)
    have hone : (1 : ℝ) - 1 / 2 = 1 / 2 := by ring
    rw [hone] at hKS
    have hsame :
        (∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal
          (Real.sqrt (V * W) * midpointRatio
            (heightQuantileSlope (K : Set E) e t) (heightQuantileSlope (L : Set E) e t))) =
        ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal
          (((1 / 2 : ℝ) * (V / sectionAtQuantile (K : Set E) e t) +
              (1 / 2 : ℝ) * (W / sectionAtQuantile (L : Set E) e t)) *
            (sectionAtQuantile (K : Set E) e t ^ (1 / 2 : ℝ) *
              sectionAtQuantile (L : Set E) e t ^ (1 / 2 : ℝ))) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      congr 1
      rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
      have hid := midpoint_integrand_identity V W
        (sectionAtQuantile (K : Set E) e t) (sectionAtQuantile (L : Set E) e t)
        hV hW (hsectionK t ht) (hsectionL t ht)
      dsimp only [heightQuantileSlope]
      convert hid.symm using 1 <;> ring
    rw [hsame,
      ofReal_measureReal (((1 / 2 : ℝ) • K + (1 / 2 : ℝ) • L).isCompact.measure_lt_top.ne)]
    simpa only [V, W, sectionAtQuantile, heightQuantile,
      ConvexBody.coe_add, ConvexBody.coe_smul]
      using hKS

end ConvexBodies
end RankThreeProjection.QuantileStability
