module
public import PaperVerification.Gaussian
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.FieldSimp
@[expose] public section
noncomputable section

open scoped BigOperators

namespace PaperVerification.ColdSpots

def fourierGaussian (β t : ℝ) : ℝ :=
  ∑' n : ℤ, Real.exp (-β * (n : ℝ) ^ 2) * Real.cos (2 * Real.pi * t * n)

def complexFourierTerm (β t : ℝ) (n : ℤ) : ℂ :=
  Complex.exp (((-β * (n : ℝ) ^ 2 : ℝ) : ℂ) +
    ((2 * Real.pi * t * n : ℝ) : ℂ) * Complex.I)

lemma complexFourierTerm_norm (β t : ℝ) (n : ℤ) :
    ‖complexFourierTerm β t n‖ = Real.exp (-β * (n : ℝ) ^ 2) := by
  rw [complexFourierTerm, Complex.norm_exp]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]

lemma complexFourierTerm_re (β t : ℝ) (n : ℤ) :
    (complexFourierTerm β t n).re =
      Real.exp (-β * (n : ℝ) ^ 2) * Real.cos (2 * Real.pi * t * n) := by
  rw [complexFourierTerm, Complex.exp_re]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
    mul_one, sub_zero, add_zero, zero_add]

lemma summable_complexFourierTerm {β : ℝ} (hβ : 0 < β) (t : ℝ) :
    Summable (complexFourierTerm β t) := by
  apply (summable_gaussian_zero hβ).of_norm_bounded
  intro n
  rw [complexFourierTerm_norm]

lemma summable_fourierGaussian {β : ℝ} (hβ : 0 < β) (t : ℝ) :
    Summable (fun n : ℤ ↦ Real.exp (-β * (n : ℝ) ^ 2) *
      Real.cos (2 * Real.pi * t * n)) := by
  apply (summable_gaussian_zero hβ).of_norm_bounded
  intro n
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)

/-- Poisson summation with its normalization explicitly matched to the manuscript. -/
theorem gaussian_poisson {α : ℝ} (hα : 0 < α) (t : ℝ) :
    gaussian α t = Real.sqrt (Real.pi / α) * fourierGaussian (Real.pi ^ 2 / α) t := by
  have ha : 0 < Real.pi / α := div_pos Real.pi_pos hα
  have hβ : 0 < Real.pi ^ 2 / α := div_pos (sq_pos_of_pos Real.pi_pos) hα
  have hπC : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hαC : (α : ℂ) ≠ 0 := by exact_mod_cast hα.ne'
  have hl (n : ℤ) :
      Complex.exp (-(Real.pi : ℂ) * (Real.pi / α : ℝ) * (n : ℂ) ^ 2 +
        2 * Real.pi * (Complex.I * (t : ℂ)) * n) =
      complexFourierTerm (Real.pi ^ 2 / α) t n := by
    unfold complexFourierTerm
    congr 1
    push_cast
    ring
  have hI : Complex.I * (Complex.I * (t : ℂ)) = -(t : ℂ) := by
    rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
  have hr (n : ℤ) :
      Complex.exp (-(Real.pi : ℂ) / (Real.pi / α : ℝ) *
        ((n : ℂ) + Complex.I * (Complex.I * (t : ℂ))) ^ 2) =
      (Real.exp (-α * ((n : ℝ) - t) ^ 2) : ℂ) := by
    rw [hI, Complex.ofReal_exp]
    congr 1
    push_cast
    field_simp [hπC, hαC]
    ring
  have hc : (1 : ℂ) / ((Real.pi / α : ℝ) : ℂ) ^ (1 / 2 : ℂ) =
      ((1 / Real.sqrt (Real.pi / α) : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow]
    norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    rw [Complex.ofReal_cpow ha.le]
    norm_num
  have ht := Complex.tsum_exp_neg_quadratic
    (show 0 < ((Real.pi / α : ℝ) : ℂ).re by simpa using ha) (Complex.I * (t : ℂ))
  simp only [hl, hr, hc, ← Complex.ofReal_tsum] at ht
  have hre := congrArg Complex.re ht
  rw [Complex.re_tsum (summable_complexFourierTerm hβ t)] at hre
  simp only [complexFourierTerm_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero] at hre
  change fourierGaussian (Real.pi ^ 2 / α) t =
    (1 / Real.sqrt (Real.pi / α)) * gaussian α t at hre
  have hs : Real.sqrt (Real.pi / α) ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  rw [hre]
  field_simp

lemma fourierGaussian_le_zero {β : ℝ} (hβ : 0 < β) (t : ℝ) :
    fourierGaussian β t ≤ fourierGaussian β 0 := by
  unfold fourierGaussian
  apply (summable_fourierGaussian hβ t).tsum_le_tsum _ (summable_fourierGaussian hβ 0)
  intro n
  simp only [mul_zero, zero_mul, Real.cos_zero, mul_one]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.cos_le_one _)

lemma fourierGaussian_lt_zero {β : ℝ} (hβ : 0 < β) (t : ℝ)
    (ht : ¬∃ z : ℤ, t = (z : ℝ)) : fourierGaussian β t < fourierGaussian β 0 := by
  have hcos : Real.cos (2 * Real.pi * t) < 1 := by
    apply lt_of_le_of_ne (Real.cos_le_one _)
    intro heq
    obtain ⟨z, hz⟩ := (Real.cos_eq_one_iff _).mp heq
    apply ht
    refine ⟨z, ?_⟩
    apply (mul_left_cancel₀ (show 2 * Real.pi ≠ 0 by positivity))
    nlinarith [hz]
  unfold fourierGaussian
  apply Summable.tsum_lt_tsum (i := (1 : ℤ)) ?_ ?_
    (summable_fourierGaussian hβ t) (summable_fourierGaussian hβ 0)
  · intro n
    simp only [mul_zero, zero_mul, Real.cos_zero, mul_one]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.cos_le_one _)
  · simp only [Int.cast_one, mul_one, one_pow, mul_zero, zero_mul, Real.cos_zero]
    simpa only [mul_one] using mul_lt_mul_of_pos_left hcos (Real.exp_pos (-β))

theorem gaussian_le_zero {α : ℝ} (hα : 0 < α) (t : ℝ) :
    gaussian α t ≤ gaussian α 0 := by
  rw [gaussian_poisson hα t, gaussian_poisson hα 0]
  exact mul_le_mul_of_nonneg_left
    (fourierGaussian_le_zero (div_pos (sq_pos_of_pos Real.pi_pos) hα) t)
    (Real.sqrt_nonneg _)

theorem gaussian_maximum_iff {α : ℝ} (hα : 0 < α) (t : ℝ) :
    gaussian α t = gaussian α 0 ↔ ∃ z : ℤ, t = (z : ℝ) := by
  constructor
  · intro heq
    by_contra ht
    have hlt := fourierGaussian_lt_zero (div_pos (sq_pos_of_pos Real.pi_pos) hα) t ht
    have h := mul_lt_mul_of_pos_left hlt
      (Real.sqrt_pos.mpr (div_pos Real.pi_pos hα))
    rw [← gaussian_poisson hα t, ← gaussian_poisson hα 0] at h
    exact (ne_of_lt h) heq
  · rintro ⟨z, rfl⟩
    simpa only [zero_add] using gaussian_int_period α 0 z

end PaperVerification.ColdSpots
