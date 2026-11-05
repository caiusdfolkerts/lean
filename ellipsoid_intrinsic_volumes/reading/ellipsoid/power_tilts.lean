module

public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace EllipsoidVerification

abbrev PositiveLine := {t : ℝ // 0 < t}

def positiveMoment (μ : Measure PositiveLine) (r : ℝ) : ℝ :=
  ∫ t, (t.val : ℝ) ^ r ∂μ

def powerTilt (μ : Measure PositiveLine) (r : ℝ) : Measure PositiveLine :=
  (ENNReal.ofReal (positiveMoment μ r))⁻¹ •
    μ.withDensity (fun t => ENNReal.ofReal ((t.val : ℝ) ^ r))

@[fun_prop] theorem measurable_positive_power (r : ℝ) :
    Measurable (fun t : PositiveLine => (t.val : ℝ) ^ r) := by fun_prop

theorem positiveMoment_pos {μ : Measure PositiveLine} (hμ : μ ≠ 0) {r : ℝ}
    (hr : Integrable (fun t : PositiveLine => (t.val : ℝ) ^ r) μ) :
    0 < positiveMoment μ r := by
  rw [positiveMoment, integral_pos_iff_support_of_nonneg
    (fun t => (Real.rpow_pos_of_pos t.property r).le) hr]
  have hs : Function.support (fun t : PositiveLine => (t.val : ℝ) ^ r) = univ := by
    ext t
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (Real.rpow_pos_of_pos t.property r).ne'
  rw [hs]
  exact Measure.measure_univ_pos.mpr hμ

theorem powerTilt_probability {μ : Measure PositiveLine} (hμ : μ ≠ 0) {r : ℝ}
    (hr : Integrable (fun t : PositiveLine => (t.val : ℝ) ^ r) μ) :
    IsProbabilityMeasure (powerTilt μ r) := by
  have hm := positiveMoment_pos hμ hr
  constructor
  simp only [powerTilt, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, smul_eq_mul]
  rw [← ofReal_integral_eq_lintegral_ofReal hr (ae_of_all _ fun t =>
    (Real.rpow_pos_of_pos t.property r).le)]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hm).ne' ENNReal.ofReal_ne_top

theorem integral_powerTilt {μ : Measure PositiveLine} {r : ℝ}
    (hr : Integrable (fun t : PositiveLine => (t.val : ℝ) ^ r) μ)
    (f : PositiveLine → ℝ) :
    (∫ t, f t ∂powerTilt μ r) =
      (∫ t, (t.val : ℝ) ^ r * f t ∂μ) / positiveMoment μ r := by
  have hm : 0 ≤ positiveMoment μ r :=
    integral_nonneg fun t => (Real.rpow_pos_of_pos t.property r).le
  rw [powerTilt, integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul (measurable_positive_power r).ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top), ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hm]
  simp only [ENNReal.toReal_ofReal (Real.rpow_pos_of_pos (Subtype.property _) r).le,
    smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem integrable_powerTilt_power {μ : Measure PositiveLine} (hμ : μ ≠ 0)
    {r a : ℝ} (hr : Integrable (fun t : PositiveLine => (t.val : ℝ) ^ r) μ)
    (hra : Integrable (fun t : PositiveLine => (t.val : ℝ) ^ (r + a)) μ) :
    Integrable (fun t : PositiveLine => (t.val : ℝ) ^ a) (powerTilt μ r) := by
  have hm := positiveMoment_pos hμ hr
  rw [powerTilt, integrable_smul_measure
    (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)
    (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hm).ne')]
  rw [integrable_withDensity_iff_integrable_smul' (measurable_positive_power r).ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  convert hra using 1
  funext t
  rw [ENNReal.toReal_ofReal (Real.rpow_pos_of_pos t.property r).le, smul_eq_mul,
    ← Real.rpow_add t.property]

theorem positiveMoment_powerTilt {μ : Measure PositiveLine} {r a : ℝ}
    (hr : Integrable (fun t : PositiveLine => (t.val : ℝ) ^ r) μ) :
    positiveMoment (powerTilt μ r) a = positiveMoment μ (r + a) / positiveMoment μ r := by
  rw [positiveMoment, integral_powerTilt hr]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun t => (Real.rpow_add t.property r a).symm

def reciprocalTail (μ : Measure PositiveLine) (r s : ℝ) : ℝ :=
  (powerTilt μ r {t | s < (t.val : ℝ)⁻¹}).toReal

theorem reciprocalTail_nonneg (μ : Measure PositiveLine) (r s : ℝ) :
    0 ≤ reciprocalTail μ r s := ENNReal.toReal_nonneg

theorem reciprocalTail_antitone {μ : Measure PositiveLine} {r : ℝ}
    [IsFiniteMeasure (powerTilt μ r)] : Antitone (reciprocalTail μ r) := by
  intro s t hst
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  exact measure_mono fun x hx => lt_of_le_of_lt hst hx

@[fun_prop] theorem measurable_reciprocalTail {μ : Measure PositiveLine} {r : ℝ}
    [IsFiniteMeasure (powerTilt μ r)] : Measurable (reciprocalTail μ r) :=
  reciprocalTail_antitone.measurable

theorem reciprocalTail_le_one {μ : Measure PositiveLine} {r : ℝ}
    [IsProbabilityMeasure (powerTilt μ r)] (s : ℝ) : reciprocalTail μ r s ≤ 1 := by
  have h : powerTilt μ r {t : PositiveLine | s < (t.val : ℝ)⁻¹} ≤
      powerTilt μ r univ :=
    measure_mono (Set.subset_univ {t : PositiveLine | s < (t.val : ℝ)⁻¹})
  rw [measure_univ] at h
  simpa only [reciprocalTail, ENNReal.toReal_one] using
    ENNReal.toReal_mono ENNReal.one_ne_top h

/-- The exact two-by-two determinant behind ordering of power tilts. -/
theorem power_likelihood_cross {x y a b : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (hab : a ≤ b) : x ^ b * y ^ a ≤ x ^ a * y ^ b := by
  have hy : 0 < y := hx.trans_le hxy
  have hpow := Real.rpow_le_rpow hx.le hxy (sub_nonneg.mpr hab)
  have heq : b = a + (b - a) := by ring
  rw [heq, Real.rpow_add hx, Real.rpow_add hy]
  convert mul_le_mul_of_nonneg_left hpow (mul_nonneg
    (Real.rpow_pos_of_pos hx a).le (Real.rpow_pos_of_pos hy a).le) using 1 <;> ring

/-- The unnormalized lower-tail inequality, valid even if the underlying
measure has infinite mass. Only the two displayed moments are needed. -/
theorem restricted_power_moment_cross {μ : Measure PositiveLine} [SFinite μ]
    {a b : ℝ} (hab : a ≤ b)
    (ha : Integrable (fun t : PositiveLine => (t.val : ℝ) ^ a) μ)
    (hb : Integrable (fun t : PositiveLine => (t.val : ℝ) ^ b) μ) (c : ℝ) :
    (∫ t in {t : PositiveLine | t.val < c}, (t.val : ℝ) ^ b ∂μ) * positiveMoment μ a ≤
      (∫ t in {t : PositiveLine | t.val < c}, (t.val : ℝ) ^ a ∂μ) * positiveMoment μ b := by
  let S : Set PositiveLine := {t | t.val < c}
  have hS : MeasurableSet S := measurableSet_lt measurable_subtype_coe measurable_const
  have hcross :
      (∫ x in S, (x.val : ℝ) ^ b ∂μ) * (∫ y in Sᶜ, (y.val : ℝ) ^ a ∂μ) ≤
      (∫ x in S, (x.val : ℝ) ^ a ∂μ) * (∫ y in Sᶜ, (y.val : ℝ) ^ b ∂μ) := by
    rw [← integral_prod_mul, ← integral_prod_mul]
    apply integral_mono_ae ((hb.restrict (s := S)).mul_prod (ha.restrict (s := Sᶜ)))
      ((ha.restrict (s := S)).mul_prod (hb.restrict (s := Sᶜ)))
    change ∀ᵐ z : PositiveLine × PositiveLine ∂(μ.restrict S).prod (μ.restrict Sᶜ),
      (z.1.val : ℝ) ^ b * (z.2.val : ℝ) ^ a ≤
        (z.1.val : ℝ) ^ a * (z.2.val : ℝ) ^ b
    apply (Measure.ae_prod_iff_ae_ae
      (p := fun z : PositiveLine × PositiveLine =>
        (z.1.val : ℝ) ^ b * (z.2.val : ℝ) ^ a ≤
          (z.1.val : ℝ) ^ a * (z.2.val : ℝ) ^ b)
      (measurableSet_le (by fun_prop) (by fun_prop))).2
    filter_upwards [self_mem_ae_restrict hS] with x hx
    filter_upwards [self_mem_ae_restrict hS.compl] with y hy
    have hxy : x.val ≤ y.val := by
      have hx' : x.val < c := hx
      have hy' : c ≤ y.val := le_of_not_gt hy
      exact hx'.le.trans hy'
    exact power_likelihood_cross x.property hxy hab
  have haSum := integral_add_compl hS ha
  have hbSum := integral_add_compl hS hb
  dsimp [positiveMoment]
  rw [← haSum, ← hbSum]
  nlinarith

theorem reciprocalTail_antitone_exponent {μ : Measure PositiveLine} [SFinite μ]
    (hμ : μ ≠ 0) {a b : ℝ} (hab : a ≤ b)
    (ha : Integrable (fun t : PositiveLine => (t.val : ℝ) ^ a) μ)
    (hb : Integrable (fun t : PositiveLine => (t.val : ℝ) ^ b) μ) (s : ℝ) :
    reciprocalTail μ b s ≤ reciprocalTail μ a s := by
  letI := powerTilt_probability hμ ha
  letI := powerTilt_probability hμ hb
  by_cases hs : 0 < s
  · let S : Set PositiveLine := {t | t.val < s⁻¹}
    have hS : MeasurableSet S := measurableSet_lt measurable_subtype_coe measurable_const
    have hset : {t : PositiveLine | s < (t.val : ℝ)⁻¹} = S := by
      ext t
      exact (lt_inv_comm₀ hs t.property)
    have htail (r : ℝ) (hr : Integrable (fun t : PositiveLine => (t.val : ℝ) ^ r) μ) :
        reciprocalTail μ r s = (∫ t in S, (t.val : ℝ) ^ r ∂μ) / positiveMoment μ r := by
      have h := integral_powerTilt hr (S.indicator (fun _ => (1 : ℝ)))
      rw [integral_indicator hS, integral_const] at h
      have hind : (fun t : PositiveLine => (t.val : ℝ) ^ r *
          S.indicator (fun _ => (1 : ℝ)) t) =
          S.indicator (fun t : PositiveLine => (t.val : ℝ) ^ r) := by
        funext t
        by_cases ht : t ∈ S <;> simp [ht]
      rw [hind, integral_indicator hS] at h
      rw [reciprocalTail, hset]
      simpa only [measureReal_def, Measure.restrict_apply_univ, smul_eq_mul, mul_one] using h
    rw [htail a ha, htail b hb]
    apply (div_le_div_iff₀ (positiveMoment_pos hμ hb) (positiveMoment_pos hμ ha)).2
    exact restricted_power_moment_cross hab ha hb s⁻¹
  · have hset : {t : PositiveLine | s < (t.val : ℝ)⁻¹} = univ := by
      ext t
      simp only [mem_setOf_eq, mem_univ, iff_true]
      exact lt_of_le_of_lt (le_of_not_gt hs) (inv_pos.mpr t.property)
    simp [reciprocalTail, hset]

end EllipsoidVerification
