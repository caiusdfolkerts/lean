module

public import Projection.QuantileEnergy
public import Projection.QuasiconcaveQuantiles
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Lean.Elab.Tactic.Omega

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory ProbabilityTheory TauCeti
open scoped Pointwise RealInnerProductSpace

namespace RankThreeProjection.QuantileStability

/-- Extending a nonnegative concave-root density by zero preserves
quasiconcavity, including at the ends of its support. -/
theorem quasiconcave_zero_extension_of_concave_rpow
    (f : ℝ → ℝ) (S : Set ℝ) (p : ℝ) (hp : 0 < p)
    (hf : ∀ x, 0 ≤ f x) (hzero : ∀ x ∉ S, f x = 0)
    (hroot : ConcaveOn ℝ S (fun x => f x ^ p)) :
    QuasiconcaveOn ℝ univ f := by
  rw [quasiconcaveOn_iff_min_le]
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  by_cases hmin : min (f x) (f y) ≤ 0
  · exact hmin.trans (hf _)
  have hminpos : 0 < min (f x) (f y) := lt_of_not_ge hmin
  have hx : x ∈ S := by
    by_contra hn
    have h := hminpos.trans_le (min_le_left _ _)
    rw [hzero x hn] at h
    exact (lt_irrefl (0 : ℝ)) h
  have hy : y ∈ S := by
    by_contra hn
    have h := hminpos.trans_le (min_le_right _ _)
    rw [hzero y hn] at h
    exact (lt_irrefl (0 : ℝ)) h
  apply (Real.rpow_le_rpow_iff hminpos.le (hf _) hp).mp
  calc
    min (f x) (f y) ^ p =
        a * min (f x) (f y) ^ p + b * min (f x) (f y) ^ p := by
          rw [← add_mul, hab, one_mul]
    _ ≤ a * f x ^ p + b * f y ^ p :=
      add_le_add
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hminpos.le (min_le_left _ _) hp.le) ha)
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hminpos.le (min_le_right _ _) hp.le) hb)
    _ ≤ _ := hroot.2 hx hy ha hb hab

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def heightDensity (K : Set E) (e : E) (s : ℝ) : ℝ :=
  volume.real {y : (ℝ ∙ e)ᗮ | (y : E) + s • e ∈ K}

theorem heightDensity_zero_off_image (K : ConvexBody E) {e : E} (he : ‖e‖ = 1)
    (s : ℝ) (hs : s ∉ (fun x => ⟪e, x⟫) '' (K : Set E)) :
    heightDensity (K : Set E) e s = 0 := by
  have hempty : {y : (ℝ ∙ e)ᗮ | (y : E) + s • e ∈ (K : Set E)} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro y hy
    exact hs ⟨(y : E) + s • e, hy, inner_add_smul e he y s⟩
  simp only [heightDensity, hempty, measureReal_empty]

theorem heightDensity_quasiconcave (K : ConvexBody E) {e : E} (he : ‖e‖ = 1)
    (hdim : 2 ≤ Module.finrank ℝ E) :
    QuasiconcaveOn ℝ univ (heightDensity (K : Set E) e) := by
  have hp : (0 : ℝ) < (((Module.finrank ℝ E - 1 : ℕ) : ℝ)⁻¹) := by
    apply inv_pos.mpr
    exact Nat.cast_pos.mpr (show 0 < Module.finrank ℝ E - 1 by omega)
  exact quasiconcave_zero_extension_of_concave_rpow
    (heightDensity (K : Set E) e) ((fun x => ⟪e, x⟫) '' (K : Set E)) _ hp
    (fun _ => measureReal_nonneg) (heightDensity_zero_off_image K he)
    (K.convex.concaveOn_volume_real_hyperplaneSection_rpow he
      (fun s => (K.isCompact.isBounded.volume_hyperplaneSection_lt_top e s).ne))

theorem heightDensity_integrable (K : ConvexBody E) {e : E} (he : ‖e‖ = 1) :
    Integrable (heightDensity (K : Set E) e) := by
  apply integrable_toReal_of_lintegral_ne_top
    (measurable_volume_hyperplaneSection e he K.isCompact.measurableSet).aemeasurable
  rw [← volume_eq_lintegral_volume_hyperplaneSection e he K.isCompact.measurableSet.nullMeasurableSet]
  exact K.isCompact.measure_lt_top.ne

/-- Cavalieri's formula expressed with real interval integrals. -/
theorem integral_heightDensity (K : ConvexBody E) {e : E} (he : ‖e‖ = 1)
    {l r : ℝ} (hlr : l ≤ r) :
    (∫ s in l..r, heightDensity (K : Set E) e s) =
      volume.real {x ∈ (K : Set E) | ⟪e, x⟫ ∈ Ioc l r} := by
  rw [intervalIntegral.integral_of_le hlr]
  change (∫ s in Ioc l r,
      (volume {y : (ℝ ∙ e)ᗮ | (y : E) + s • e ∈ (K : Set E)}).toReal) = _
  rw [integral_toReal
    (measurable_volume_hyperplaneSection e he K.isCompact.measurableSet).aemeasurable
    (Filter.Eventually.of_forall
      (fun s => K.isCompact.isBounded.volume_hyperplaneSection_lt_top e s))]
  exact congrArg ENNReal.toReal
    (volume_sep_inner_mem_eq_setLIntegral e he K.isCompact.measurableSet.nullMeasurableSet
      measurableSet_Ioc).symm

/-- Actual convex-body height quantiles obey the uniform weighted derivative
bound. The proof uses Brunn's concavity principle and Cavalieri's formula,
rather than an assumed density or section regularity hypothesis. -/
theorem weighted_heightQuantileSlope_le (K : ConvexBody E) {e : E} (he : ‖e‖ = 1)
    (hdim : 2 ≤ Module.finrank ℝ E) (hK : volume (K : Set E) ≠ 0)
    (R : ℝ) (hR : ∀ x ∈ (K : Set E), ‖x‖ < R)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    min t (1 - t) * heightQuantileSlope (K : Set E) e t ≤ 2 * R := by
  let s := heightQuantile (K : Set E) e t
  let V := volume.real (K : Set E)
  have hV : 0 < V := ENNReal.toReal_pos hK K.isCompact.measure_lt_top.ne
  have hheight (x : E) (hx : x ∈ (K : Set E)) : -R < ⟪e, x⟫ ∧ ⟪e, x⟫ < R := by
    have h := (abs_real_inner_le_norm e x).trans_lt (by simpa only [he, one_mul] using hR x hx)
    exact abs_lt.mp h
  obtain ⟨x, hx, hxs⟩ := K.convex.quantile_map_inner_cond_mem_image_interior he hK
    K.isCompact.measure_lt_top.ne ht
  have hs : s ∈ Ioo (-R) R := by
    dsimp only [s, heightQuantile]
    rw [← hxs]
    exact hheight x (interior_subset hx)
  have hR0 : 0 < R := by linarith [hs.1, hs.2]
  have hleft := (heightDensity_integrable K he).intervalIntegrable (a := -R) (b := s)
  have hright := (heightDensity_integrable K he).intervalIntegrable (a := s) (b := R)
  have hF : (∫ z in -R..s, heightDensity (K : Set E) e z) = t * V := by
    rw [integral_heightDensity K he hs.1.le]
    have hset : {x ∈ (K : Set E) | ⟪e, x⟫ ∈ Ioc (-R) s} =
        {x ∈ (K : Set E) | ⟪e, x⟫ ≤ s} := by
      ext x
      exact and_congr_right (fun hx => ⟨And.right, fun h => ⟨(hheight x hx).1, h⟩⟩)
    rw [hset]
    haveI := cond_isProbabilityMeasure_of_finite hK K.isCompact.measure_lt_top.ne
    have hq := Measure.cdf_quantile
      ((volume[|(K : Set E)]).map fun x => ⟪e, x⟫)
      (continuous_cdf_map_inner_cond he hK K.isCompact.measure_lt_top.ne) ht.1 ht.2
    rw [cdf_map_inner_cond hK K.isCompact.measure_lt_top.ne] at hq
    exact (div_eq_iff hV.ne').mp hq
  have htotal : (∫ z in -R..R, heightDensity (K : Set E) e z) = V := by
    rw [integral_heightDensity K he (by linarith)]
    have hset : {x ∈ (K : Set E) | ⟪e, x⟫ ∈ Ioc (-R) R} = (K : Set E) := by
      ext x
      exact ⟨And.left, fun hx => ⟨hx, (hheight x hx).1, (hheight x hx).2.le⟩⟩
    rw [hset]
  have hG : (∫ z in s..R, heightDensity (K : Set E) e z) = (1 - t) * V := by
    have hsum := intervalIntegral.integral_add_adjacent_intervals hleft hright
    rw [hF, htotal] at hsum
    linarith
  have hfs : 0 < heightDensity (K : Set E) e s :=
    K.convex.volume_real_hyperplaneSection_quantile_pos K.isCompact.isBounded hK he ht
  have hq := quasiconcave_inverse_density_bound (heightDensity (K : Set E) e)
    (Convex.quasiconcaveOn_restrict (heightDensity_quasiconcave K he hdim)
      (subset_univ _) (convex_Icc _ _)) ⟨hs.1.le, hs.2.le⟩ hfs hV.le
    hleft hright hF hG
  change min t (1 - t) * (V / heightDensity (K : Set E) e s) ≤ _
  convert hq using 1 <;> ring

/-- A common outer-radius bound alone gives a common derivative bound on
every compact probability interval, uniformly as the bodies vary. -/
theorem heightQuantileSlope_le_of_radius (K : ConvexBody E) {e : E} (he : ‖e‖ = 1)
    (hdim : 2 ≤ Module.finrank ℝ E) (hK : volume (K : Set E) ≠ 0)
    (R : ℝ) (hR : ∀ x ∈ (K : Set E), ‖x‖ < R)
    {a b t : ℝ} (ha : 0 < a) (hb : b < 1) (ht : t ∈ Icc a b) :
    heightQuantileSlope (K : Set E) e t ≤ 2 * R / min a (1 - b) := by
  have htI : t ∈ Ioo (0 : ℝ) 1 := ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩
  have hp : 0 < min a (1 - b) := lt_min ha (sub_pos.mpr hb)
  have hnonneg : 0 ≤ heightQuantileSlope (K : Set E) e t :=
    div_nonneg measureReal_nonneg measureReal_nonneg
  have hmin : min a (1 - b) ≤ min t (1 - t) :=
    min_le_min ht.1 (sub_le_sub_left ht.2 1)
  have h := (mul_le_mul_of_nonneg_right hmin hnonneg).trans
    (weighted_heightQuantileSlope_le K he hdim hK R hR htI)
  exact (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using h)

end RankThreeProjection.QuantileStability
