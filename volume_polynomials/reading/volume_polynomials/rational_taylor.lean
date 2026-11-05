module

public import VolumePolynomials.HolomorphicSeries
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

@[expose] public section
noncomputable section

namespace VolumePolynomials

open scoped Topology
open Polynomial.Chebyshev Filter Metric

/-- The rational normalized sine coefficient, including the zero constant term. -/
def rationalSineCoefficient : ℕ → ℚ
  | 0 => 0
  | n + 1 => |(U ℚ (n : ℤ)).eval (1 / 3)|

theorem rationalSineCoefficient_eq {θ : ℝ} (hθ : Real.cos θ = 1 / 3)
    (hsin : 0 < Real.sin θ) (n : ℕ) :
    (rationalSineCoefficient n : ℝ) = |Real.sin ((n : ℝ) * θ)| / Real.sin θ := by
  first
  | cases n with
    | zero => simp [rationalSineCoefficient]
    | succ n =>
        have hcast : (((U ℚ (n : ℤ)).eval (1 / 3) : ℚ) : ℝ) =
            (U ℝ (n : ℤ)).eval (1 / 3) := by
          simpa using (algebraMap_eval_U (R := ℚ) (R' := ℝ) (1 / 3) (n : ℤ))
        simp only [rationalSineCoefficient, Rat.cast_abs, hcast]
        apply (eq_div_iff hsin.ne').mpr
        calc
          |(U ℝ (n : ℤ)).eval (1 / 3)| * Real.sin θ =
              |(U ℝ (n : ℤ)).eval (1 / 3) * Real.sin θ| := by
            rw [abs_mul, abs_of_pos hsin]
          _ = |Real.sin (((n + 1 : ℕ) : ℝ) * θ)| := by
            congr 1
            simpa [hθ] using U_real_cos θ (n : ℤ)

theorem rationalSineCoefficient_eq_complex {θ : ℝ} (hθ : Real.cos θ = 1 / 3)
    (hsin : 0 < Real.sin θ) (n : ℕ) :
    (rationalSineCoefficient n : ℂ) = sineCoefficient θ n / (Real.sin θ : ℂ) := by
  first
  | unfold sineCoefficient
    exact_mod_cast rationalSineCoefficient_eq hθ hsin n

/-- Ordinary Cauchy convolution, performed entirely over the rationals. -/
def rationalConvolution (a b : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ p ∈ Finset.antidiagonal n, a p.1 * b p.2

theorem rationalConvolution_term (a b : ℕ → ℚ) (n : ℕ) (z : ℂ) :
    (rationalConvolution a b n : ℂ) * z ^ n =
      ∑ p ∈ Finset.antidiagonal n, ((a p.1 : ℂ) * z ^ p.1) *
        ((b p.2 : ℂ) * z ^ p.2) := by
  first
  | unfold rationalConvolution
    push_cast
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    have hpn := Finset.mem_antidiagonal.mp hp
    rw [← hpn, pow_add]
    ring

/-- The Cauchy product identity together with the absolute convergence needed for iteration. -/
theorem rationalConvolution_hasSum (a b : ℕ → ℚ) (z A B : ℂ)
    (ha : Summable fun n => ‖(a n : ℂ) * z ^ n‖)
    (hb : Summable fun n => ‖(b n : ℂ) * z ^ n‖)
    (hA : HasSum (fun n => (a n : ℂ) * z ^ n) A)
    (hB : HasSum (fun n => (b n : ℂ) * z ^ n) B) :
    (Summable fun n => ‖(rationalConvolution a b n : ℂ) * z ^ n‖) ∧
      HasSum (fun n => (rationalConvolution a b n : ℂ) * z ^ n) (A * B) := by
  first
  | have hn := summable_norm_sum_mul_antidiagonal_of_summable_norm ha hb
    simp only [← rationalConvolution_term] at hn
    refine ⟨hn, ?_⟩
    have heq := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm ha hb
    rw [hA.tsum_eq, hB.tsum_eq] at heq
    simp only [← rationalConvolution_term] at heq
    exact heq.symm ▸ hn.of_norm.hasSum

/-- Rational Taylor coefficients of the complete area generating function. -/
def areaTaylorCoefficient : ℕ → ℚ :=
  rationalConvolution (rationalConvolution rationalSineCoefficient (fun _ => 1))
    (fun n => (-1) ^ n)

/-- The complex extension of formula (7.11). -/
noncomputable def areaGeneratingFunction (θ : ℝ) (z : ℂ) : ℂ :=
  sineGeneratingFunction θ z / ((1 - z ^ 2) * (Real.sin θ : ℂ))

theorem areaGeneratingFunction_hasSum {θ : ℝ} (hθ : Real.cos θ = 1 / 3)
    (hsin : 0 < Real.sin θ) (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum (fun n => (areaTaylorCoefficient n : ℂ) * z ^ n)
      (areaGeneratingFunction θ z) := by
  first
  | have hc : Summable (fun n => ‖(rationalSineCoefficient n : ℂ) * z ^ n‖) := by
      simp_rw [rationalSineCoefficient_eq_complex hθ hsin, div_mul_eq_mul_div, norm_div]
      exact (sine_powerSeries_norm_summable θ z hz).div_const _
    have hC : HasSum (fun n => (rationalSineCoefficient n : ℂ) * z ^ n)
        (sineGeneratingFunction θ z / (Real.sin θ : ℂ)) := by
      simp_rw [rationalSineCoefficient_eq_complex hθ hsin, div_mul_eq_mul_div]
      rw [sineGeneratingFunction_eq_full_series θ z hz]
      exact (sine_powerSeries_summable θ z hz).hasSum.div_const _
    have hplus : Summable (fun n : ℕ => ‖((1 : ℚ) : ℂ) * z ^ n‖) := by
      simpa only [Rat.cast_one, one_mul, norm_pow] using
        summable_geometric_of_lt_one (norm_nonneg z) hz
    have hPlus : HasSum (fun n : ℕ => ((1 : ℚ) : ℂ) * z ^ n) ((1 - z)⁻¹) := by
      simpa using hasSum_geometric_of_norm_lt_one hz
    have hminus : Summable (fun n : ℕ => ‖(((-1 : ℚ) ^ n : ℚ) : ℂ) * z ^ n‖) := by
      simpa only [Rat.cast_pow, Rat.cast_neg, Rat.cast_one, norm_mul, norm_pow,
        norm_neg, norm_one, one_pow, one_mul] using
        summable_geometric_of_lt_one (norm_nonneg z) hz
    have hMinus : HasSum (fun n : ℕ => (((-1 : ℚ) ^ n : ℚ) : ℂ) * z ^ n)
        ((1 + z)⁻¹) := by
      have hzneg : ‖-z‖ < 1 := by simpa using hz
      have hneg : (fun n : ℕ => (((-1 : ℚ) ^ n : ℚ) : ℂ) * z ^ n) =
          (fun n : ℕ => (-z) ^ n) := by
        funext n
        simp only [Rat.cast_pow, Rat.cast_neg, Rat.cast_one, ← mul_pow, neg_one_mul]
      rw [hneg]
      simpa only [sub_neg_eq_add] using hasSum_geometric_of_norm_lt_one hzneg
    obtain ⟨hfirst, hFirst⟩ := rationalConvolution_hasSum rationalSineCoefficient (fun _ => 1)
      z _ _ hc hplus hC hPlus
    have hfinal := (rationalConvolution_hasSum _ (fun n => (-1) ^ n) z _ _
      hfirst hminus hFirst hMinus).2
    convert hfinal using 1
    · rfl
    · unfold areaGeneratingFunction
      rw [show (1 - z ^ 2) = (1 - z) * (1 + z) by ring]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

theorem areaGeneratingFunction_hasFPowerSeriesAt {θ : ℝ}
    (hθ : Real.cos θ = 1 / 3) (hsin : 0 < Real.sin θ) :
    HasFPowerSeriesAt (areaGeneratingFunction θ)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => (areaTaylorCoefficient n : ℂ))) 0 := by
  first
  | rw [hasFPowerSeriesAt_iff]
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with z hz
    simpa only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, zero_add, mul_comm]
      using areaGeneratingFunction_hasSum hθ hsin z (by simpa using hz)

/-- The rational coefficients above are the actual normalized iterated derivatives at zero. -/
theorem areaGeneratingFunction_rational_taylor {θ : ℝ}
    (hθ : Real.cos θ = 1 / 3) (hsin : 0 < Real.sin θ) (n : ℕ) :
    iteratedDeriv n (areaGeneratingFunction θ) 0 / (n.factorial : ℂ) =
      (areaTaylorCoefficient n : ℂ) := by
  first
  | have hp := areaGeneratingFunction_hasFPowerSeriesAt hθ hsin
    have heq := hp.eq_formalMultilinearSeries hp.analyticAt.hasFPowerSeriesAt
    have hc := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) heq
    simpa only [FormalMultilinearSeries.coeff_ofScalars] using hc.symm

end VolumePolynomials
