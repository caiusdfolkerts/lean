module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FunProp
public import Lean.Elab.Tactic.Omega
public import Lean.Elab.Tactic.NormCast

@[expose] public section
noncomputable section

/-! Exact Fourier-integral computation for the natural-boundary argument. -/

namespace VolumePolynomials

open scoped Interval
open intervalIntegral

noncomputable def sineFourierCoefficient (m : ℤ) : ℂ :=
  2 / ((Real.pi : ℂ) * (1 - 4 * (m : ℂ)^2))

theorem odd_frequency_ne_zero (m : ℤ) : (2 * (m : ℂ) + 1) * Complex.I ≠ 0 := by
  first
  | apply mul_ne_zero _ Complex.I_ne_zero
    exact_mod_cast (show 2 * m + 1 ≠ 0 by omega)

theorem exp_odd_pi (m : ℤ) :
    Complex.exp ((2 * (m : ℂ) + 1) * (Real.pi : ℂ) * Complex.I) = -1 := by
  first
  | have heq : (2 * (m : ℂ) + 1) * (Real.pi : ℂ) * Complex.I =
        (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) + (Real.pi : ℂ) * Complex.I := by ring
    rw [heq, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,
      Complex.exp_pi_mul_I, one_mul]

theorem integral_odd_frequency (m : ℤ) :
    (∫ x in (0 : ℝ)..Real.pi,
      Complex.exp (((2 * (m : ℂ) + 1) * Complex.I) * (x : ℂ))) =
        -2 / ((2 * (m : ℂ) + 1) * Complex.I) := by
  first
  | rw [integral_exp_mul_complex (odd_frequency_ne_zero m)]
    have heq : ((2 * (m : ℂ) + 1) * Complex.I) * (Real.pi : ℂ) =
        (2 * (m : ℂ) + 1) * (Real.pi : ℂ) * Complex.I := by ring
    rw [heq, exp_odd_pi]
    norm_num

theorem sine_exponential_integrand (m : ℤ) (x : ℝ) :
    Complex.exp ((-2 * (m : ℂ) * Complex.I) * (x : ℂ)) * (Real.sin x : ℂ) =
      (Complex.exp (((2 * ((-m - 1 : ℤ) : ℂ) + 1) * Complex.I) * (x : ℂ)) -
       Complex.exp (((2 * ((-m : ℤ) : ℂ) + 1) * Complex.I) * (x : ℂ))) * Complex.I / 2 := by
  first
  | have hm : Complex.exp ((-2 * (m : ℂ) * Complex.I) * (x : ℂ)) *
        Complex.exp (-(x : ℂ) * Complex.I) =
        Complex.exp (((2 * ((-m - 1 : ℤ) : ℂ) + 1) * Complex.I) * (x : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hp : Complex.exp ((-2 * (m : ℂ) * Complex.I) * (x : ℂ)) *
        Complex.exp ((x : ℂ) * Complex.I) =
        Complex.exp (((2 * ((-m : ℤ) : ℂ) + 1) * Complex.I) * (x : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [Complex.ofReal_sin, Complex.sin]
    calc
      _ = (Complex.exp ((-2 * (m : ℂ) * Complex.I) * (x : ℂ)) *
            Complex.exp (-(x : ℂ) * Complex.I) -
          Complex.exp ((-2 * (m : ℂ) * Complex.I) * (x : ℂ)) *
            Complex.exp ((x : ℂ) * Complex.I)) * Complex.I / 2 := by ring
      _ = _ := by rw [hm, hp]

theorem sine_fourier_integral (m : ℤ) :
    (∫ x in (0 : ℝ)..Real.pi,
      Complex.exp ((-2 * (m : ℂ) * Complex.I) * (x : ℂ)) * (Real.sin x : ℂ)) =
        2 / (1 - 4 * (m : ℂ)^2) := by
  first
  | simp_rw [sine_exponential_integrand]
    rw [integral_div, integral_mul_const, integral_sub,
      integral_odd_frequency, integral_odd_frequency]
    · have hm : (2 * (m : ℂ) + 1) ≠ 0 := by
        exact_mod_cast (show 2 * m + 1 ≠ 0 by omega)
      have hp : (2 * (m : ℂ) - 1) ≠ 0 := by
        exact_mod_cast (show 2 * m - 1 ≠ 0 by omega)
      have hq : (1 - 4 * (m : ℂ)^2) ≠ 0 := by
        exact_mod_cast (show 1 - 4 * m^2 ≠ 0 by omega)
      push_cast
      field_simp [Complex.I_ne_zero, hm, hp, hq,
        odd_frequency_ne_zero (-m - 1), odd_frequency_ne_zero (-m)]
      ring_nf
      norm_num [Complex.I_sq]
      have hleft : (-1 - (m : ℂ) * 2) ≠ 0 := by
        convert neg_ne_zero.mpr hm using 1 <;> ring
      have hright : (1 - (m : ℂ) * 2) ≠ 0 := by
        convert neg_ne_zero.mpr hp using 1 <;> ring
      have hquad : (1 - (m : ℂ)^2 * 4) ≠ 0 := by
        simpa only [mul_comm] using hq
      field_simp [hleft, hright, hquad]
      <;> ring
    · exact (by fun_prop : Continuous (fun x : ℝ =>
        Complex.exp (((2 * ((-m - 1 : ℤ) : ℂ) + 1) * Complex.I) * (x : ℂ)))).intervalIntegrable _ _
    · exact (by fun_prop : Continuous (fun x : ℝ =>
        Complex.exp (((2 * ((-m : ℤ) : ℂ) + 1) * Complex.I) * (x : ℂ)))).intervalIntegrable _ _

theorem abs_sine_fourier_integral (m : ℤ) :
    (1 / (Real.pi : ℂ)) * (∫ x in (0 : ℝ)..Real.pi,
      Complex.exp ((-2 * (m : ℂ) * Complex.I) * (x : ℂ)) * ((|Real.sin x| : ℝ) : ℂ)) =
        sineFourierCoefficient m := by
  first
  | have hInt : (∫ x in (0 : ℝ)..Real.pi,
        Complex.exp ((-2 * (m : ℂ) * Complex.I) * (x : ℂ)) * ((|Real.sin x| : ℝ) : ℂ)) =
        ∫ x in (0 : ℝ)..Real.pi,
          Complex.exp ((-2 * (m : ℂ) * Complex.I) * (x : ℂ)) * (Real.sin x : ℂ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x ∈ Set.Icc (0 : ℝ) Real.pi := by
        simpa [Set.uIcc_of_le Real.pi_pos.le] using hx
      dsimp only
      rw [abs_of_nonneg (Real.sin_nonneg_of_mem_Icc hx')]
    rw [hInt, sine_fourier_integral, sineFourierCoefficient]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

end VolumePolynomials
