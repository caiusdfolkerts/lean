module

public import VolumePolynomials.GeometricCornerMeasure

@[expose] public section
set_option autoImplicit false

/-! # Every small deficit is attained by an explicit finite cap -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology MeasureTheory

namespace VolumePolynomials.HalfZonotope

open PlanarExtrusion

@[simp] theorem geometricDeficit_one : geometricDeficit 1 = 1 / 2 := by
  first
  | norm_num [geometricDeficit, geometricGenerators, geometricNormalizer,
      rawGeometricGenerators, cornerEnergy]

/-- A first crossing, not an assumption of monotonicity, selects a finite
member for every positive deficit at most one half. -/
theorem exists_geometricDeficit_crossing {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    ∃ n : ℕ, 0 < n ∧ δ ≤ geometricDeficit n ∧ geometricDeficit (n + 1) < δ := by
  first
  | have hevent : ∀ᶠ n : ℕ in atTop, geometricDeficit n < δ :=
      (tendsto_order.mp geometricDeficit_tendsto_zero).2 δ hδ
    have hex : ∃ n : ℕ, 0 < n ∧ geometricDeficit n < δ := by
      first
      | obtain ⟨n, hn, hlt⟩ := ((eventually_ge_atTop (1 : ℕ)).and hevent).exists
        exact ⟨n, hn, hlt⟩
    let N := Nat.find hex
    have hN : 0 < N ∧ geometricDeficit N < δ := Nat.find_spec hex
    have hN1 : N ≠ 1 := by
      first
      | intro heq
        have h := hN.2
        rw [heq, geometricDeficit_one] at h
        linarith
    have hN2 : 2 ≤ N := by omega
    refine ⟨N - 1, by omega, ?_, ?_⟩
    · by_contra h
      have hp : 0 < N - 1 ∧ geometricDeficit (N - 1) < δ :=
        ⟨by omega, lt_of_not_ge h⟩
      exact Nat.find_min hex (by omega : N - 1 < Nat.find hex) hp
    · simpa only [Nat.sub_add_cancel (by omega : 1 ≤ N)] using hN.2

theorem logarithm_le_crossing_index {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (hn : 0 < n)
    (hcross : geometricDeficit (n + 1) < δ) :
    Real.log (1 / δ) ≤ 4 * n := by
  first
  | have hA : (0 : ℝ) < 4 ^ (n + 1) := pow_pos (by norm_num) _
    have hlo : 1 / (4 : ℝ) ^ (n + 1) < δ := by
      first
      | simpa only [one_div] using
          lt_of_le_of_lt (geometricDeficit_bounds (Nat.succ_pos n)).1 hcross
    have hmul : 1 < δ * (4 : ℝ) ^ (n + 1) := (div_lt_iff₀ hA).mp hlo
    have hdiv : 1 / δ ≤ (4 : ℝ) ^ (n + 1) :=
      (div_le_iff₀ hδ).mpr (by nlinarith)
    have hlog := Real.log_le_log (div_pos (by norm_num) hδ) hdiv
    rw [Real.log_pow, Nat.cast_add, Nat.cast_one] at hlog
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hbound := mul_le_mul_of_nonneg_left log_four_le_two
      (by positivity : (0 : ℝ) ≤ n + 1)
    nlinarith

/-- The square-root interpolation parameter is in the entire interval `[0,1]`
and attains the desired deficit exactly. -/
theorem geometric_interpolation_parameter {δ : ℝ} (hδ : 0 < δ)
    {n : ℕ} (hn : 0 < n) (hδn : δ ≤ geometricDeficit n) :
    Real.sqrt (δ / geometricDeficit n) ∈ Icc (0 : ℝ) 1 ∧
      Real.sqrt (δ / geometricDeficit n) ^ 2 * geometricDeficit n = δ := by
  first
  | have hdn : 0 < geometricDeficit n := lt_of_lt_of_le hδ hδn
    have hq : 0 ≤ δ / geometricDeficit n := (div_pos hδ hdn).le
    have hq1 : δ / geometricDeficit n ≤ 1 := (div_le_one hdn).mpr hδn
    have hsquare := Real.sq_sqrt hq
    refine ⟨⟨Real.sqrt_nonneg _, ?_⟩, ?_⟩
    · nlinarith [Real.sqrt_nonneg (δ / geometricDeficit n)]
    · rw [hsquare]
      exact div_mul_cancel₀ δ hdn.ne'

/-- All positive sufficiently small deficits occur in actual finite compact
convex unit-width caps; this is not merely a sequence of finite examples. -/
theorem exists_cap_with_exact_deficit {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    ∃ (n : ℕ) (t : ℝ), 0 < n ∧ t ∈ Icc (0 : ℝ) 1 ∧
      volume.real (cap (interpolatedGenerators t (geometricGenerators n))) = 1 / 2 - δ ∧
      (3 / 50) * δ ^ 2 * Real.log (1 / δ) ≤
        t ^ 4 * geometricConvolutionDeficit n := by
  first
  | obtain ⟨n, hn, hδn, hcross⟩ := exists_geometricDeficit_crossing hδ hδhalf
    let t := Real.sqrt (δ / geometricDeficit n)
    obtain ⟨ht, hscale⟩ := geometric_interpolation_parameter hδ hn hδn
    have harea : volume.real (cap (interpolatedGenerators t (geometricGenerators n))) =
        1 / 2 - δ := by
      first
      | rw [area_interpolated_cap ht (geometricGenerators_signed hn) (geometricGenerators_sum hn),
          area_geometricCap hn]
        nlinarith
    refine ⟨n, t, hn, ht, harea, ?_⟩
    have hη := mul_le_mul_of_nonneg_left (geometricConvolutionDeficit_lower hn)
      (by positivity : 0 ≤ t ^ 4)
    have hsquare : t ^ 4 * geometricDeficit n ^ 2 = δ ^ 2 := by
      first
      | have hs := congrArg (fun x : ℝ => x ^ 2) hscale
        dsimp only [t] at *
        nlinarith
    have hlog := mul_le_mul_of_nonneg_left (logarithm_le_crossing_index hδ hn hcross)
      (sq_nonneg δ)
    nlinarith

end VolumePolynomials.HalfZonotope
