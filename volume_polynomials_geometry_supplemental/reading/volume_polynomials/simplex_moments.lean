module

public import VolumePolynomials.SimplexCoordinates
public import VolumePolynomials.PowerLayerCake
public import VolumePolynomials.BerwaldComparison

@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# The two moments of the cone height

The equalities are integrals over the actual coordinate simplex. They
follow from its homothetic superlevel sets and layer-cake integration.
The construction is valid in every dimension, including dimension zero;
no moment identity is supplied as an assumption.
-/

open Set MeasureTheory Filter

namespace VolumePolynomials.SimplexCoordinates

theorem height_moment (n p : ℕ) :
    (∫ x in simplex n, height x ^ (p + 1)) =
      (p + 1 : ℝ) * volume.real (simplex n) *
        ∫ t in Icc (0 : ℝ) 1, t ^ p * (1 - t) ^ n := by
  first
  | letI : IsFiniteMeasure (volume.restrict (simplex n)) :=
      isFiniteMeasure_restrict.mpr (simplex_compact n).measure_ne_top
    have hnonneg : 0 ≤ᵐ[volume.restrict (simplex n)] (height : Space n → ℝ) := by
      first
      | filter_upwards [ae_restrict_mem (simplex_compact n).measurableSet] with x hx
        exact height_nonnegative hx
    have htail (t : ℝ) :
        (volume.restrict (simplex n)).real {x : Space n | t ≤ height x} =
          volume.real {x : Space n | x ∈ simplex n ∧ t ≤ height x} := by
      first
      | rw [measureReal_restrict_apply' (simplex_compact n).measurableSet]
        congr 1
        ext x
        simp only [mem_inter_iff, mem_setOf_eq, and_comm]
    rw [BerwaldMoments.power_layer_cake
      (continuous_height n).measurable.aemeasurable hnonneg p]
    simp only [htail]
    have hrestrict :
        (∫ t in Ioi (0 : ℝ), t ^ p *
          volume.real {x : Space n | x ∈ simplex n ∧ t ≤ height x}) =
        ∫ t in Ioc (0 : ℝ) 1, t ^ p *
          volume.real {x : Space n | x ∈ simplex n ∧ t ≤ height x} := by
      first
      | apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
          nullMeasurableSet_Ioi Ioc_subset_Ioi_self
        exact Eventually.of_forall fun t ht => by
          have ht1 : 1 < t := by
            have ht0 : 0 < t := ht.1
            by_contra h
            exact ht.2 ⟨ht0, le_of_not_gt h⟩
          rw [superlevel_empty ht1, measureReal_empty, mul_zero]
    rw [hrestrict, ← integral_Icc_eq_integral_Ioc]
    have heq : (∫ t in Icc (0 : ℝ) 1, t ^ p *
          volume.real {x : Space n | x ∈ simplex n ∧ t ≤ height x}) =
        (∫ t in Icc (0 : ℝ) 1, t ^ p * (1 - t) ^ n) *
          volume.real (simplex n) := by
      first
      | rw [← integral_mul_const]
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc,
          ae_restrict_of_ae (Measure.ae_ne volume (1 : ℝ))] with t ht ht1
        rw [superlevel_volume ht.1 (lt_of_le_of_ne ht.2 ht1)]
        ring
    rw [heq]
    ring

theorem integral_height (n : ℕ) :
    (∫ x in simplex n, height x) = volume.real (simplex n) / (n + 1 : ℝ) := by
  first
  | have h := height_moment n 0
    have href : (∫ t in Icc (0 : ℝ) 1, (1 - t) ^ n) = 1 / (n + 1 : ℝ) := by
      first
      | simpa only [div_one] using BerwaldComparison.reference_integral n zero_lt_one
    simpa only [zero_add, pow_one, Nat.cast_zero, zero_add, one_mul, pow_zero,
      href, mul_one_div] using h

theorem integral_height_sq (n : ℕ) :
    (∫ x in simplex n, height x ^ 2) =
      2 * volume.real (simplex n) / ((n + 1 : ℝ) * (n + 2 : ℝ)) := by
  first
  | have h := height_moment n 1
    have href : (∫ t in Icc (0 : ℝ) 1, t * (1 - t) ^ n) =
        1 / ((n + 1 : ℝ) * (n + 2 : ℝ)) := by
      first
      | simpa only [div_one, one_pow] using
          BerwaldComparison.reference_first_moment n zero_lt_one
    simpa only [one_add_one_eq_two, Nat.cast_one, pow_one, href, mul_one_div] using h

def coneHeight {n : ℕ} (x : Space n) : ℝ := (n + 1 : ℝ) * height x

theorem coneHeight_nonnegative {n : ℕ} {x : Space n} (hx : x ∈ simplex n) :
    0 ≤ coneHeight x := mul_nonneg (by positivity) (height_nonnegative hx)

theorem continuous_coneHeight (n : ℕ) : Continuous (coneHeight : Space n → ℝ) :=
  continuous_const.mul (continuous_height n)

theorem coneHeight_affine {n : ℕ} (x y : Space n) {a b : ℝ} (hab : a + b = 1) :
    coneHeight (a • x + b • y) = a * coneHeight x + b * coneHeight y := by
  first
  | simp only [coneHeight, height, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum]
    nlinarith

theorem integral_coneHeight (n : ℕ) :
    (∫ x in simplex n, coneHeight x) = volume.real (simplex n) := by
  first
  | change (∫ x in simplex n, (n + 1 : ℝ) * height x) = _
    rw [integral_const_mul, integral_height]
    have hn : (n + 1 : ℝ) ≠ 0 := by positivity
    field_simp

theorem integral_coneHeight_sq (n : ℕ) :
    (∫ x in simplex n, coneHeight x ^ 2) =
      (2 * (n + 1 : ℝ) / (n + 2 : ℝ)) * volume.real (simplex n) := by
  first
  | simp_rw [coneHeight, mul_pow]
    rw [integral_const_mul, integral_height_sq]
    have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
    have hn2 : (n + 2 : ℝ) ≠ 0 := by positivity
    field_simp <;> ring

/-- These are precisely the two normalized moments used in (6.5). -/
theorem coneHeight_normalized_moments (n : ℕ) :
    (∫ x in simplex n, coneHeight x) / volume.real (simplex n) = 1 ∧
      (∫ x in simplex n, coneHeight x ^ 2) / volume.real (simplex n) =
        2 * (n + 1 : ℝ) / (n + 2 : ℝ) := by
  first
  | have hm := (simplex_volume_pos n).ne'
    rw [integral_coneHeight, integral_coneHeight_sq]
    exact ⟨div_self hm, mul_div_cancel_right₀ _ hm⟩

end VolumePolynomials.SimplexCoordinates
