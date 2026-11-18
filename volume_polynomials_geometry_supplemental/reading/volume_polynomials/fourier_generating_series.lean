module

public import VolumePolynomials.RadialPoles
public import VolumePolynomials.SineFourierSeries
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section
noncomputable section

/-! The Cauchy-kernel representation (7.12) from the proved Fourier expansion. -/

namespace VolumePolynomials

open scoped Topology

/-- The unit frequency e^(2 i m θ). -/
noncomputable def rotationFrequency (θ : ℝ) (m : ℤ) : ℂ :=
  Complex.exp (2 * (m : ℂ) * (θ : ℂ) * Complex.I)

theorem rotationFrequency_norm (θ : ℝ) (m : ℤ) : ‖rotationFrequency θ m‖ = 1 := by
  first
  | have h : 2 * (m : ℂ) * (θ : ℂ) * Complex.I =
        ((2 * (m : ℝ) * θ : ℝ) : ℂ) * Complex.I := by push_cast; rfl
    rw [rotationFrequency, h, Complex.norm_exp_ofReal_mul_I]

noncomputable def sineGeneratingFunction (θ : ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, ((|Real.sin ((n + 1 : ℕ) * θ)| : ℝ) : ℂ) * z^(n + 1)

theorem sine_fourier_at_multiple (θ : ℝ) (n : ℕ) :
    ((|Real.sin ((n : ℝ) * θ)| : ℝ) : ℂ) =
      ∑' m : ℤ, sineFourierCoefficient m * rotationFrequency θ m ^ n := by
  first
  | have h := (abs_sine_hasSum_fourier ((n : ℝ) * θ)).tsum_eq.symm
    rw [h]
    apply tsum_congr
    intro m
    rw [rotationFrequency, ← Complex.exp_nat_mul]
    congr 2
    push_cast
    ring

/-- Absolutely summable Fourier data can be interchanged with a generating series inside the disk. -/
theorem fourier_generating_cauchy {ι : Type*} (β u : ι → ℂ)
    (hβ : Summable fun i => ‖β i‖) (hu : ∀ i, ‖u i‖ = 1)
    (c : ℕ → ℂ) (hc : ∀ n, c n = ∑' i, β i * u i ^ n)
    (z : ℂ) (hz : ‖z‖ < 1) :
    (∑' n : ℕ, c (n + 1) * z^(n + 1)) = weightedCauchySeries β u z := by
  first
  | have hg : Summable (fun n : ℕ => ‖z‖^(n + 1)) :=
      (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg _) hz)
    have hdouble : Summable (fun p : ℕ × ι => β p.2 * (z * u p.2)^(p.1 + 1)) := by
      apply (hg.mul_of_nonneg hβ (fun n => pow_nonneg (norm_nonneg _) _)
        (fun i => norm_nonneg _)).of_norm_bounded
      intro p
      simp only [norm_mul, norm_pow, hu, mul_one]
      exact le_of_eq (mul_comm _ _)
    calc
      (∑' n : ℕ, c (n + 1) * z^(n + 1)) =
          ∑' n : ℕ, ∑' i, β i * (z * u i)^(n + 1) := by
        apply tsum_congr
        intro n
        rw [hc, ← tsum_mul_right]
        apply tsum_congr
        intro i
        rw [mul_pow]
        ring
      _ = ∑' i, ∑' n : ℕ, β i * (z * u i)^(n + 1) := hdouble.tsum_comm.symm
      _ = weightedCauchySeries β u z := by
        apply tsum_congr
        intro i
        have hzi : ‖z * u i‖ < 1 := by simpa [norm_mul, hu] using hz
        simp_rw [pow_succ', ← mul_assoc]
        rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hzi]
        rfl

/-- Equation (7.12), with the actual sine sequence and all Fourier coefficients determined. -/
theorem sineGeneratingFunction_eq_cauchy (θ : ℝ) (z : ℂ) (hz : ‖z‖ < 1) :
    sineGeneratingFunction θ z =
      weightedCauchySeries sineFourierCoefficient (rotationFrequency θ) z := by
  first
  | exact fourier_generating_cauchy sineFourierCoefficient (rotationFrequency θ)
      sineFourier_summable_norm (rotationFrequency_norm θ)
      (fun n => ((|Real.sin ((n : ℝ) * θ)| : ℝ) : ℂ)) (sine_fourier_at_multiple θ) z hz

end VolumePolynomials
