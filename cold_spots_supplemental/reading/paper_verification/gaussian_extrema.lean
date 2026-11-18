module
public import PaperVerification.GaussianSmallParameter
public import PaperVerification.GaussianLargeParameter
public import Mathlib.Algebra.Order.Round
@[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

theorem gaussian_min_on_half_interval {α t : ℝ} (hα : 0 < α) (ht : 0 ≤ t)
    (ht2 : t ≤ 1 / 2) : gaussian α (1 / 2) ≤ gaussian α t := by
  rcases le_total α 4 with hsmall | hlarge
  · exact gaussian_min_small_parameter hα hsmall t
  · exact gaussian_min_large_parameter hlarge ht ht2

theorem gaussian_min_on_half_interval_strict {α t : ℝ} (hα : 0 < α) (ht : 0 ≤ t)
    (ht2 : t < 1 / 2) : gaussian α (1 / 2) < gaussian α t := by
  rcases le_total α 4 with hsmall | hlarge
  · exact gaussian_min_small_parameter_strict hα hsmall ht ht2
  · exact gaussian_min_large_parameter_strict hlarge ht ht2

lemma gaussian_abs (α t : ℝ) : gaussian α |t| = gaussian α t := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg (lt_of_not_ge ht), gaussian_even]

lemma gaussian_fold (α t : ℝ) :
    gaussian α t = gaussian α |t - (round t : ℝ)| := by
  rw [gaussian_abs]
  have h := gaussian_int_period α (t - (round t : ℝ)) (round t)
  simpa only [sub_add_cancel] using h

/-- Global minimum of the actual integer Gaussian series, for every positive parameter. -/
theorem gaussian_minimum {α : ℝ} (hα : 0 < α) (t : ℝ) :
    gaussian α (1 / 2) ≤ gaussian α t := by
  rw [gaussian_fold α t]
  exact gaussian_min_on_half_interval hα (abs_nonneg _) (abs_sub_round t)

/-- Equality in the Gaussian minimum occurs exactly at nonintegral half integers. -/
theorem gaussian_minimum_iff {α : ℝ} (hα : 0 < α) (t : ℝ) :
    gaussian α t = gaussian α (1 / 2) ↔ ∃ z : ℤ, t = (z : ℝ) + 1 / 2 := by
  constructor
  · intro heq
    have hfold : |t - (round t : ℝ)| = 1 / 2 := by
      apply le_antisymm (abs_sub_round t)
      by_contra h
      have hlt := gaussian_min_on_half_interval_strict hα (abs_nonneg (t - (round t : ℝ)))
        (lt_of_not_ge h)
      rw [← gaussian_fold, heq] at hlt
      exact (lt_irrefl _) hlt
    have hround := sub_half_lt_round t
    by_cases hd : 0 ≤ t - (round t : ℝ)
    · rw [abs_of_nonneg hd] at hfold
      linarith
    · rw [abs_of_neg (lt_of_not_ge hd)] at hfold
      refine ⟨round t - 1, ?_⟩
      push_cast
      linarith
  · rintro ⟨z, rfl⟩
    rw [add_comm, gaussian_int_period]

theorem gaussian_half_lt_zero {α : ℝ} (hα : 0 < α) :
    gaussian α (1 / 2) < gaussian α 0 :=
  gaussian_min_on_half_interval_strict hα le_rfl (by norm_num)

end PaperVerification.ColdSpots
