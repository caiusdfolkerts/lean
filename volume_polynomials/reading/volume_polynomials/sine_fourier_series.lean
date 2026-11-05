module

public import VolumePolynomials.SineFourier
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Normed.Group.InfiniteSum

@[expose] public section
noncomputable section

/-! Absolute convergence and reconstruction of the Fourier series of |sin|. -/

namespace VolumePolynomials

open scoped Topology
open Set Filter

private theorem sineFourier_norm_bound (m : ℤ) (hm : m ≠ 0) :
    ‖sineFourierCoefficient m‖ ≤ (2 / Real.pi) * (1 / (m : ℝ)^2) := by
  first
  | have hmsqInt : (1 : ℤ) ≤ m^2 := by
      have := sq_pos_of_ne_zero hm
      omega
    have hmsq : (1 : ℝ) ≤ (m : ℝ)^2 := by exact_mod_cast hmsqInt
    have hneg : 1 - 4 * (m : ℝ)^2 < 0 := by nlinarith
    have hden : (1 - 4 * (m : ℂ)^2) = ((1 - 4 * (m : ℝ)^2 : ℝ) : ℂ) := by
      push_cast
      rfl
    have hnorm : ‖sineFourierCoefficient m‖ = 2 / (Real.pi * (4 * (m : ℝ)^2 - 1)) := by
      rw [sineFourierCoefficient, norm_div, norm_mul, hden, Complex.norm_real,
        Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos, abs_of_neg hneg]
      norm_num <;> congr 1 <;> ring
    rw [hnorm]
    calc
      2 / (Real.pi * (4 * (m : ℝ)^2 - 1)) ≤ 2 / (Real.pi * (m : ℝ)^2) :=
        div_le_div_of_nonneg_left (by norm_num)
          (mul_pos Real.pi_pos (by linarith))
          (mul_le_mul_of_nonneg_left (by nlinarith) Real.pi_pos.le)
      _ = (2 / Real.pi) * (1 / (m : ℝ)^2) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring

theorem sineFourier_summable_norm : Summable (fun m : ℤ => ‖sineFourierCoefficient m‖) := by
  first
  | have hp : Summable (fun m : ℤ => 1 / (m : ℝ)^2) :=
      Real.summable_one_div_int_pow.mpr (by norm_num)
    apply (hp.mul_left (2 / Real.pi)).of_norm_bounded_eventually
    filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with m hm
    simpa only [norm_norm] using sineFourier_norm_bound m hm

theorem sineFourier_ne_zero (m : ℤ) : sineFourierCoefficient m ≠ 0 := by
  first
  | apply div_ne_zero (by norm_num)
    apply mul_ne_zero
    · exact_mod_cast Real.pi_ne_zero
    · exact_mod_cast (show 1 - 4 * m^2 ≠ 0 by omega)

theorem abs_sine_periodic :
    Function.Periodic (fun x : ℝ => ((|Real.sin x| : ℝ) : ℂ)) Real.pi := by
  first
  | intro x
    simp [Real.sin_add_pi]

/-- The actual continuous function |sin| on the circle of period π. -/
noncomputable def absoluteSineCircle : C(AddCircle Real.pi, ℂ) where
  toFun := Function.Periodic.lift abs_sine_periodic
  continuous_toFun := continuous_coinduced_dom.mpr
    (Complex.continuous_ofReal.comp Real.continuous_sin.abs)

@[simp] theorem absoluteSineCircle_coe (x : ℝ) :
    absoluteSineCircle (x : AddCircle Real.pi) = ((|Real.sin x| : ℝ) : ℂ) := rfl

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

theorem fourierCoeff_absoluteSineCircle (m : ℤ) :
    fourierCoeff absoluteSineCircle m = sineFourierCoefficient m := by
  first
  | rw [fourierCoeff_eq_intervalIntegral _ _ (0 : ℝ)]
    simp only [zero_add, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one]
    convert abs_sine_fourier_integral m using 1
    congr 1
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only
    rw [fourier_coe_apply, absoluteSineCircle_coe, smul_eq_mul]
    congr 2
    push_cast
    field_simp [Real.pi_ne_zero] <;> ring

/-- The Fourier expansion used in equation (7.12), proved through its exact integral coefficients. -/
theorem abs_sine_hasSum_fourier (t : ℝ) :
    HasSum (fun m : ℤ => sineFourierCoefficient m *
      Complex.exp (2 * (m : ℂ) * (t : ℂ) * Complex.I)) ((|Real.sin t| : ℝ) : ℂ) := by
  first
  | have hsum : Summable (fourierCoeff absoluteSineCircle) := by
      have hcoeff : fourierCoeff absoluteSineCircle = sineFourierCoefficient :=
        funext fourierCoeff_absoluteSineCircle
      rw [hcoeff]
      exact sineFourier_summable_norm.of_norm
    have h := has_pointwise_sum_fourier_series_of_summable hsum (t : AddCircle Real.pi)
    convert h using 1
    · ext m
      rw [fourierCoeff_absoluteSineCircle, fourier_coe_apply, smul_eq_mul]
      congr 2
      field_simp [Real.pi_ne_zero] <;> ring
    · rfl

end VolumePolynomials
