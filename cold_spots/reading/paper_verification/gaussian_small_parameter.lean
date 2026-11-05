module
public import PaperVerification.FourierDominance
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Real.Pi.Bounds
@[expose] public section
noncomputable section

open scoped BigOperators

namespace PaperVerification.ColdSpots

lemma summable_nat_fourierGaussian {β : ℝ} (hβ : 0 < β) (t : ℝ) :
    Summable (fun n : ℕ ↦ Real.exp (-β * ((n : ℝ) + 1) ^ 2) *
      Real.cos (2 * Real.pi * t * ((n : ℝ) + 1))) := by
  have h := (summable_fourierGaussian hβ t).comp_injective
    (i := fun n : ℕ ↦ (n : ℤ) + 1) (by
      intro a b h
      change (a : ℤ) + 1 = (b : ℤ) + 1 at h
      exact_mod_cast (add_right_cancel h))
  simpa only [Function.comp_def, Int.cast_add, Int.cast_natCast, Int.cast_one] using h

lemma fourierGaussian_nat {β : ℝ} (hβ : 0 < β) (t : ℝ) :
    fourierGaussian β t = 1 + 2 * ∑' n : ℕ,
      Real.exp (-β * ((n : ℝ) + 1) ^ 2) *
        Real.cos (2 * Real.pi * t * ((n : ℝ) + 1)) := by
  let f : ℤ → ℝ := fun n ↦ Real.exp (-β * (n : ℝ) ^ 2) *
    Real.cos (2 * Real.pi * t * n)
  have heven (n : ℤ) : f (-n) = f n := by
    simp only [f, Int.cast_neg, neg_sq, mul_neg, Real.cos_neg]
  have hp : Summable (fun n : ℕ ↦ f ((n : ℤ) + 1)) := by
    simpa only [f, Int.cast_add, Int.cast_natCast, Int.cast_one] using
      summable_nat_fourierGaussian hβ t
  have hn : Summable (fun n : ℕ ↦ f (-((n : ℤ) + 1))) :=
    hp.congr (fun n ↦ (heven ((n : ℤ) + 1)).symm)
  have h := tsum_of_add_one_of_neg_add_one hp hn
  simp only [heven] at h
  change fourierGaussian β t = _ at h
  have hzero : f 0 = 1 := by simp [f]
  rw [hzero] at h
  simp only [f, Int.cast_add, Int.cast_natCast, Int.cast_one] at h
  rw [h]
  ring

/-- The first Fourier harmonic dominates the entire remaining series, uniformly in `t`. -/
theorem fourierGaussian_min_gap {β : ℝ} (hβ : 2 ≤ β) (t : ℝ) :
    Real.exp (-β) * (1 + Real.cos (2 * Real.pi * t)) ≤
      fourierGaussian β t - fourierGaussian β (1 / 2) := by
  have hβ0 : 0 < β := by linarith
  let D : ℝ := 1 + Real.cos (2 * Real.pi * t)
  let g : ℝ → ℕ → ℝ := fun u n ↦ Real.exp (-β * ((n : ℝ) + 1) ^ 2) *
    Real.cos (2 * Real.pi * u * ((n : ℝ) + 1))
  let c : ℕ → ℝ := fun n ↦ ((n : ℝ) + 2) ^ 2 *
    Real.exp (-β * ((n : ℝ) + 2) ^ 2)
  have hD : 0 ≤ D := by dsimp [D]; linarith [Real.neg_one_le_cos (2 * Real.pi * t)]
  have hgt : Summable (g t) := summable_nat_fourierGaussian hβ0 t
  have hgh : Summable (g (1 / 2)) := summable_nat_fourierGaussian hβ0 (1 / 2)
  have hdiff : Summable (fun n ↦ g t n - g (1 / 2) n) := hgt.sub hgh
  have htail : Summable (fun n : ℕ ↦ g t (n + 1) - g (1 / 2) (n + 1)) :=
    hdiff.comp_injective (i := fun n : ℕ ↦ n + 1) (by
      intro a b h
      change a + 1 = b + 1 at h
      exact Nat.add_right_cancel h)
  have hc : Summable c := (gaussian_frequency_tail hβ).1
  have hcb : (∑' n, c n) ≤ Real.exp (-β) / 2 := (gaussian_frequency_tail hβ).2
  have hterm (n : ℕ) : -D * c n ≤ g t (n + 1) - g (1 / 2) (n + 1) := by
    have h := mul_le_mul_of_nonneg_left
      (cosine_coefficient_lower (n + 2) (2 * Real.pi * t))
      (Real.exp_pos (-β * ((n : ℝ) + 2) ^ 2)).le
    have ha : ((n : ℝ) + 2) * (2 * Real.pi * t) =
        2 * Real.pi * t * ((n : ℝ) + 2) := by ring
    have hb : ((n : ℝ) + 2) * Real.pi =
        2 * Real.pi * (1 / 2) * ((n : ℝ) + 2) := by ring
    simp only [Nat.cast_add, Nat.cast_ofNat] at h
    rw [ha, hb] at h
    convert h using 1 <;> (try dsimp only [D, c, g]) <;>
      (try simp only [Nat.cast_add_one]) <;> ring
  have hsum := (hc.mul_left (-D)).tsum_le_tsum hterm htail
  rw [tsum_mul_left] at hsum
  have hbound : -D * (Real.exp (-β) / 2) ≤ -D * ∑' n, c n :=
    mul_le_mul_of_nonpos_left hcb (neg_nonpos.mpr hD)
  have hzero : g t 0 - g (1 / 2) 0 = Real.exp (-β) * D := by
    norm_num [g, D]
    rw [show 2 * Real.pi * (1 / 2) = Real.pi by ring, Real.cos_pi]
    ring
  have hsplit := hdiff.tsum_eq_zero_add
  rw [hzero, hgt.tsum_sub hgh] at hsplit
  rw [fourierGaussian_nat hβ0 t, fourierGaussian_nat hβ0 (1 / 2)]
  change Real.exp (-β) * D ≤ (1 + 2 * ∑' n, g t n) -
    (1 + 2 * ∑' n, g (1 / 2) n)
  linarith

theorem fourierGaussian_min {β : ℝ} (hβ : 2 ≤ β) (t : ℝ) :
    fourierGaussian β (1 / 2) ≤ fourierGaussian β t := by
  have hD : 0 ≤ 1 + Real.cos (2 * Real.pi * t) := by
    linarith [Real.neg_one_le_cos (2 * Real.pi * t)]
  have h := fourierGaussian_min_gap hβ t
  nlinarith [Real.exp_pos (-β)]

theorem fourierGaussian_min_strict {β t : ℝ} (hβ : 2 ≤ β) (ht : 0 ≤ t)
    (ht2 : t < 1 / 2) : fourierGaussian β (1 / 2) < fourierGaussian β t := by
  have hx : 2 * Real.pi * t ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨by positivity, by nlinarith [Real.pi_pos]⟩
  have hxlt : 2 * Real.pi * t < Real.pi := by nlinarith [Real.pi_pos]
  have hc := Real.strictAntiOn_cos hx ⟨Real.pi_pos.le, le_rfl⟩ hxlt
  rw [Real.cos_pi] at hc
  have hpos : 0 < Real.exp (-β) * (1 + Real.cos (2 * Real.pi * t)) :=
    mul_pos (Real.exp_pos _) (by linarith)
  have h := fourierGaussian_min_gap hβ t
  linarith

lemma gaussian_reciprocal_parameter_ge_two {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 4) :
    2 ≤ Real.pi ^ 2 / α := by
  apply (le_div_iff₀ hα).mpr
  nlinarith [Real.pi_gt_three]

theorem gaussian_min_small_parameter {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 4)
    (t : ℝ) : gaussian α (1 / 2) ≤ gaussian α t := by
  rw [gaussian_poisson hα (1 / 2), gaussian_poisson hα t]
  exact mul_le_mul_of_nonneg_left
    (fourierGaussian_min (gaussian_reciprocal_parameter_ge_two hα hα4) t)
    (Real.sqrt_nonneg _)

theorem gaussian_min_small_parameter_strict {α t : ℝ} (hα : 0 < α) (hα4 : α ≤ 4)
    (ht : 0 ≤ t) (ht2 : t < 1 / 2) : gaussian α (1 / 2) < gaussian α t := by
  rw [gaussian_poisson hα (1 / 2), gaussian_poisson hα t]
  exact mul_lt_mul_of_pos_left
    (fourierGaussian_min_strict (gaussian_reciprocal_parameter_ge_two hα hα4) ht ht2)
    (Real.sqrt_pos.mpr (div_pos Real.pi_pos hα))

end PaperVerification.ColdSpots
