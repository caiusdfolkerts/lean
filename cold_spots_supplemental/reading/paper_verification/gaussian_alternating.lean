module
public import PaperVerification.GaussianContinuity
public import PaperVerification.GaussianExtrema
public import Mathlib.Topology.Order.IntermediateValue
@[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

theorem alternatingGaussian_zero_pos {α : ℝ} (hα : 0 < α) :
    0 < alternatingGaussian α 0 := by
  have hs := alternatingGaussian_split hα 0
  norm_num at hs
  rw [gaussian_even] at hs
  rw [hs]
  exact sub_pos.mpr (gaussian_half_lt_zero (show 0 < 4 * α by positivity))

lemma alternatingGaussian_sq_pos {α t : ℝ} (hα : 0 < α) (ht : 0 ≤ t)
    (ht2 : t < 1 / 2) : 0 < alternatingGaussian α t ^ 2 := by
  have h2 : 0 < 2 * α := by positivity
  have hu := gaussian_min_on_half_interval_strict h2 ht ht2
  have hw := gaussian_le_zero h2 (t - 1 / 2)
  have hP := gaussian_pos h2 0
  have hQ := gaussian_pos h2 (1 / 2)
  have hmul := mul_pos hP (sub_pos.mpr hu)
  have hmul' := mul_nonneg hQ.le (sub_nonneg.mpr hw)
  rw [alternatingGaussian_duplication hα]
  nlinarith

theorem alternatingGaussian_pos {α t : ℝ} (hα : 0 < α) (ht : 0 ≤ t)
    (ht2 : t < 1 / 2) : 0 < alternatingGaussian α t := by
  by_contra h
  have htB : alternatingGaussian α t ≤ 0 := le_of_not_gt h
  have hzero := alternatingGaussian_zero_pos hα
  obtain ⟨s, hs, hsz⟩ := intermediate_value_Icc' ht
    (continuous_alternatingGaussian hα).continuousOn ⟨htB, hzero.le⟩
  have hsq := alternatingGaussian_sq_pos hα hs.1 (lt_of_le_of_lt hs.2 ht2)
  rw [hsz] at hsq
  norm_num at hsq

theorem alternatingGaussian_nonneg {α t : ℝ} (hα : 0 < α) (ht : 0 ≤ t)
    (ht2 : t ≤ 1 / 2) : 0 ≤ alternatingGaussian α t := by
  rcases eq_or_lt_of_le ht2 with rfl | hlt
  · rw [alternatingGaussian_half]
  · exact (alternatingGaussian_pos hα ht hlt).le

theorem alternatingGaussian_zero_iff_on_half_interval {α t : ℝ} (hα : 0 < α)
    (ht : 0 ≤ t) (ht2 : t ≤ 1 / 2) : alternatingGaussian α t = 0 ↔ t = 1 / 2 := by
  constructor
  · intro hz
    by_contra hne
    have hpos := alternatingGaussian_pos hα ht (lt_of_le_of_ne ht2 hne)
    rw [hz] at hpos
    exact (lt_irrefl _) hpos
  · rintro rfl
    exact alternatingGaussian_half α

lemma alternatingGaussian_int_period (α t : ℝ) (k : ℤ) :
    alternatingGaussian α (t + k) = paritySign k * alternatingGaussian α t := by
  unfold alternatingGaussian
  rw [← (Equiv.addRight k).tsum_eq, ← tsum_mul_left]
  apply tsum_congr
  intro z
  simp only [Equiv.coe_addRight, paritySign_add, Int.cast_add]
  rw [show (z : ℝ) + k - (t + k) = (z : ℝ) - t by ring]
  ring

lemma abs_paritySign (k : ℤ) : |paritySign k| = 1 := by
  simpa only [Real.norm_eq_abs] using norm_paritySign k

lemma alternatingGaussian_abs_period (α t : ℝ) (k : ℤ) :
    |alternatingGaussian α (t + k)| = |alternatingGaussian α t| := by
  rw [alternatingGaussian_int_period, abs_mul, abs_paritySign, one_mul]

lemma alternatingGaussian_abs_argument (α t : ℝ) :
    alternatingGaussian α |t| = alternatingGaussian α t := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg (lt_of_not_ge ht), alternatingGaussian_even]

lemma alternatingGaussian_fold {α : ℝ} (hα : 0 < α) (t : ℝ) :
    |alternatingGaussian α t| = alternatingGaussian α |t - (round t : ℝ)| := by
  have h := alternatingGaussian_abs_period α (t - (round t : ℝ)) (round t)
  rw [sub_add_cancel] at h
  rw [h, ← alternatingGaussian_abs_argument]
  exact abs_of_nonneg (alternatingGaussian_nonneg hα (abs_nonneg _) (abs_sub_round t))

lemma gaussian_halfshift_abs (α t : ℝ) :
    gaussian α (|t| - 1 / 2) = gaussian α (t - 1 / 2) := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg (lt_of_not_ge ht), show -t - 1 / 2 = -(t + 1 / 2) by ring,
      gaussian_even]
    have h := gaussian_one_period α (t - 1 / 2)
    simpa only [show t - 1 / 2 + 1 = t + 1 / 2 by ring] using h

lemma gaussian_halfshift_fold (α t : ℝ) :
    gaussian α (t - 1 / 2) = gaussian α (|t - (round t : ℝ)| - 1 / 2) := by
  rw [gaussian_halfshift_abs]
  have h := gaussian_int_period α (t - (round t : ℝ) - 1 / 2) (round t)
  simpa only [show t - (round t : ℝ) - 1 / 2 + (round t : ℝ) = t - 1 / 2 by ring] using h

lemma alternatingGaussian_abs_halfshift_abs (α t : ℝ) :
    |alternatingGaussian α (|t| - 1 / 2)| = |alternatingGaussian α (t - 1 / 2)| := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg (lt_of_not_ge ht), show -t - 1 / 2 = -(t + 1 / 2) by ring,
      alternatingGaussian_even]
    have h := alternatingGaussian_antiperiod α (t - 1 / 2)
    rw [show t - 1 / 2 + 1 = t + 1 / 2 by ring] at h
    rw [h, abs_neg]

lemma alternatingGaussian_halfshift_fold {α : ℝ} (hα : 0 < α) (t : ℝ) :
    |alternatingGaussian α (t - 1 / 2)| =
      alternatingGaussian α (|t - (round t : ℝ)| - 1 / 2) := by
  have h := alternatingGaussian_abs_period α (t - (round t : ℝ) - 1 / 2) (round t)
  rw [show t - (round t : ℝ) - 1 / 2 + (round t : ℝ) = t - 1 / 2 by ring] at h
  rw [h, ← alternatingGaussian_abs_halfshift_abs]
  apply abs_of_nonneg
  rw [show |t - (round t : ℝ)| - 1 / 2 = -(1 / 2 - |t - (round t : ℝ)|) by ring,
    alternatingGaussian_even]
  apply alternatingGaussian_nonneg hα
  · linarith [abs_sub_round t]
  · linarith [abs_nonneg (t - (round t : ℝ))]

end PaperVerification.ColdSpots
