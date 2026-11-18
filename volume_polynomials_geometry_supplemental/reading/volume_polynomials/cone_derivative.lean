module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

@[expose] public section
set_option autoImplicit false

/-! # Dominated right differentiation of radial cone integrals

These are ordinary calculus and integration lemmas. Their hypotheses concern
pointwise radial fibers and an explicit integrable difference-quotient bound;
the geometric input is proved separately for literal Minkowski sums.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace VolumePolynomials.ConeDerivative

theorem radialPower_hasDerivAt (k : ℕ) (c : ℝ) :
    HasDerivAt (fun t : ℝ => (1 + t * c) ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) c 0 := by
  first
  | have hn : (((k + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    convert ((((hasDerivAt_id (0 : ℝ)).mul_const c).const_add 1).pow (k + 1)).div_const
      (((k + 1 : ℕ) : ℝ)) using 1 <;> simp [hn] <;> field_simp <;> ring

theorem tendsto_radialPower_quotient (k : ℕ) (c : ℝ) :
    Tendsto (fun t : ℝ =>
      ((1 + t * c) ^ (k + 1) / ((k + 1 : ℕ) : ℝ) -
        1 / ((k + 1 : ℕ) : ℝ)) / t) (𝓝[>] 0) (𝓝 c) := by
  first
  | have h := (radialPower_hasDerivAt k c).tendsto_slope.mono_left (nhdsGT_le_nhdsNE 0)
    change Tendsto
      (fun t : ℝ => slope
        (fun u : ℝ => (1 + u * c) ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) 0 t)
      (𝓝[>] 0) (𝓝 c) at h
    simpa only [slope_def_field, zero_mul, add_zero, one_pow, sub_zero] using h

theorem radialPower_quotient_bound (k : ℕ) {C t : ℝ}
    (hC : 0 ≤ C) (ht : 0 < t) (ht1 : t ≤ 1) :
    (((1 + t * C) ^ (k + 1) - 1) / (((k + 1 : ℕ) : ℝ) * t)) ≤
      C * (1 + C) ^ k := by
  first
  | have hbase : 1 ≤ 1 + t * C := by linarith [mul_nonneg ht.le hC]
    have hpow : 1 ≤ (1 + t * C) ^ (k + 1) := one_le_pow₀ hbase
    have hdiff := abs_pow_sub_pow_le (a := 1 + t * C) (b := (1 : ℝ)) (n := k + 1)
    rw [one_pow, abs_of_nonneg (sub_nonneg.mpr hpow),
      show 1 + t * C - 1 = t * C by ring,
      abs_of_nonneg (mul_nonneg ht.le hC),
      abs_of_nonneg (zero_le_one.trans hbase), abs_one,
      max_eq_left hbase, Nat.add_sub_cancel] at hdiff
    have hmono : (1 + t * C) ^ k ≤ (1 + C) ^ k := by
      apply pow_le_pow_left₀ (zero_le_one.trans hbase)
      nlinarith
    have hbound := hdiff.trans (mul_le_mul_of_nonneg_left hmono
      (mul_nonneg (mul_nonneg ht.le hC) (Nat.cast_nonneg _)))
    apply (div_le_iff₀ (mul_pos (by positivity) ht)).mpr
    nlinarith

/-- Differentiation of an actual integral along the positive parameter filter.
The finite-measure constant bound is particularly convenient on compact facets. -/
theorem tendsto_integral_difference_quotient
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (F : ℝ → α → ℝ) (g : α → ℝ) (C : ℝ)
    (hF0 : Integrable (F 0) μ)
    (hF : ∀ᶠ t : ℝ in 𝓝[>] 0, Integrable (F t) μ)
    (hbound : ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ᵐ x ∂μ, |(F t x - F 0 x) / t| ≤ C)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun t : ℝ => (F t x - F 0 x) / t)
      (𝓝[>] 0) (𝓝 (g x))) :
    Tendsto (fun t : ℝ => ((∫ x, F t x ∂μ) - ∫ x, F 0 x ∂μ) / t)
      (𝓝[>] 0) (𝓝 (∫ x, g x ∂μ)) := by
  first
  | have hmeas : ∀ᶠ t : ℝ in 𝓝[>] 0,
        AEStronglyMeasurable (fun x => (F t x - F 0 x) / t) μ :=
      hF.mono fun t ht => ((ht.sub hF0).div_const t).aestronglyMeasurable
    have hnorm : ∀ᶠ t : ℝ in 𝓝[>] 0,
        ∀ᵐ x ∂μ, ‖(F t x - F 0 x) / t‖ ≤ C := by
      simpa only [Real.norm_eq_abs] using hbound
    have h := tendsto_integral_filter_of_dominated_convergence (fun _ : α => C)
      hmeas hnorm (integrable_const C) hlim
    apply h.congr'
    filter_upwards [hF] with t ht
    rw [integral_div, integral_sub ht hF0]

end VolumePolynomials.ConeDerivative
