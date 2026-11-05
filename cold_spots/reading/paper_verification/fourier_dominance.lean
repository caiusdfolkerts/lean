module
public import PaperVerification.GaussianFourier
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Data.Nat.Basic
@[expose] public section
noncomputable section

open scoped BigOperators

namespace PaperVerification.ColdSpots

lemma abs_sin_nat_mul_bound (n : ℕ) (x : ℝ) :
    |Real.sin ((n : ℝ) * x)| ≤ n * |Real.sin x| := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add_one, add_mul, one_mul, Real.sin_add]
    calc
      |Real.sin (n * x) * Real.cos x + Real.cos (n * x) * Real.sin x|
          ≤ |Real.sin (n * x) * Real.cos x| + |Real.cos (n * x) * Real.sin x| := abs_add_le _ _
      _ = |Real.sin (n * x)| * |Real.cos x| + |Real.cos (n * x)| * |Real.sin x| := by
          rw [abs_mul, abs_mul]
      _ ≤ |Real.sin (n * x)| + |Real.sin x| := add_le_add
          (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _))
          (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _))
      _ ≤ n * |Real.sin x| + |Real.sin x| := add_le_add ih le_rfl
      _ = (n + 1) * |Real.sin x| := by ring

lemma one_sub_cos_nat_mul_bound (n : ℕ) (x : ℝ) :
    1 - Real.cos ((n : ℝ) * x) ≤ (n : ℝ) ^ 2 * (1 - Real.cos x) := by
  have hs := abs_sin_nat_mul_bound n (x / 2)
  have hs2 : Real.sin ((n : ℝ) * (x / 2)) ^ 2 ≤
      (n : ℝ) ^ 2 * Real.sin (x / 2) ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))).mpr hs
    simpa only [sq_abs, mul_pow] using h
  rw [Real.sin_sq_eq_half_sub, Real.sin_sq_eq_half_sub] at hs2
  rw [show 2 * ((n : ℝ) * (x / 2)) = n * x by ring,
    show 2 * (x / 2) = x by ring] at hs2
  nlinarith

lemma cosine_coefficient_lower (n : ℕ) (x : ℝ) :
    -(n : ℝ) ^ 2 * (1 + Real.cos x) ≤
      Real.cos ((n : ℝ) * x) - Real.cos ((n : ℝ) * Real.pi) := by
  have h := one_sub_cos_nat_mul_bound n (x - Real.pi)
  rw [Real.cos_sub_pi] at h
  have hshift : Real.cos ((n : ℝ) * x) =
      (-1 : ℝ) ^ n * Real.cos ((n : ℝ) * (x - Real.pi)) := by
    convert Real.cos_add_nat_mul_pi ((n : ℝ) * (x - Real.pi)) n using 1 <;> congr 1 <;> ring
  rw [hshift, Real.cos_nat_mul_pi]
  have hc : (-1 : ℝ) ^ n ≤ 1 := by
    calc (-1 : ℝ) ^ n ≤ |(-1 : ℝ) ^ n| := le_abs_self _
      _ = 1 := by simp
  have hp := mul_nonneg (sub_nonneg.mpr hc)
    (sub_nonneg.mpr (Real.cos_le_one ((n : ℝ) * (x - Real.pi))))
  nlinarith

lemma nat_sq_le_four_pow (n : ℕ) : (n : ℝ) ^ 2 ≤ (4 : ℝ) ^ n := by
  have h := Nat.two_mul_sq_add_one_le_two_pow_two_mul n
  have h' : 2 * n ^ 2 + 1 ≤ 4 ^ n := by
    simpa only [pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num] using h
  exact_mod_cast (show n ^ 2 ≤ 4 ^ n by omega)

lemma gaussian_tail_ratio {β : ℝ} (hβ : 2 ≤ β) :
    0 ≤ 4 * Real.exp (-(3 * β / 2)) ∧ 4 * Real.exp (-(3 * β / 2)) ≤ 1 / 2 := by
  constructor
  · positivity
  have he3 : 8 < Real.exp 3 := by
    have he := Real.exp_one_gt_two
    have hpower : Real.exp 3 = Real.exp 1 ^ 3 := by
      simpa using Real.exp_nat_mul (1 : ℝ) 3
    rw [hpower]
    nlinarith [sq_nonneg (Real.exp 1 - 2)]
  have he : 8 < Real.exp (3 * β / 2) :=
    he3.trans_le (Real.exp_le_exp.mpr (by linarith))
  have hc : Real.exp (3 * β / 2) * Real.exp (-(3 * β / 2)) = 1 := by
    rw [← Real.exp_add]
    simp
  have hp := mul_pos (sub_pos.mpr he) (Real.exp_pos (-(3 * β / 2)))
  nlinarith

lemma gaussian_frequency_tail_term {β : ℝ} (hβ : 2 ≤ β) {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) ^ 2 * Real.exp (-β * (n : ℝ) ^ 2) ≤
      Real.exp (-β) * (1 / 2 : ℝ) ^ n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hβ0 : 0 ≤ β := by linarith
  have hsq : 1 + 3 * (n : ℝ) / 2 ≤ (n : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) - 2 by linarith)
      (show 0 ≤ (n : ℝ) + 1 / 2 by positivity)]
  have hex : -β * (n : ℝ) ^ 2 ≤ -β - (3 * β / 2) * n := by
    nlinarith [mul_nonneg hβ0 (sub_nonneg.mpr hsq)]
  have hfactor : Real.exp (-β - (3 * β / 2) * n) =
      Real.exp (-β) * Real.exp (-(3 * β / 2)) ^ n := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  calc
    (n : ℝ) ^ 2 * Real.exp (-β * (n : ℝ) ^ 2)
        ≤ (4 : ℝ) ^ n * Real.exp (-β - (3 * β / 2) * n) :=
      mul_le_mul (nat_sq_le_four_pow n) (Real.exp_le_exp.mpr hex)
        (Real.exp_pos _).le (by positivity)
    _ = Real.exp (-β) * (4 * Real.exp (-(3 * β / 2))) ^ n := by
      rw [hfactor, mul_pow]
      ring
    _ ≤ Real.exp (-β) * (1 / 2 : ℝ) ^ n :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (gaussian_tail_ratio hβ).1 (gaussian_tail_ratio hβ).2 n)
        (Real.exp_pos _).le

theorem gaussian_frequency_tail {β : ℝ} (hβ : 2 ≤ β) :
    Summable (fun n : ℕ ↦ ((n : ℝ) + 2) ^ 2 * Real.exp (-β * ((n : ℝ) + 2) ^ 2)) ∧
    (∑' n : ℕ, ((n : ℝ) + 2) ^ 2 * Real.exp (-β * ((n : ℝ) + 2) ^ 2)) ≤
      Real.exp (-β) / 2 := by
  let g : ℕ → ℝ := fun n ↦ (Real.exp (-β) / 4) * (1 / 2 : ℝ) ^ n
  have hg : HasSum g (Real.exp (-β) / 2) := by
    change HasSum (fun n : ℕ ↦ (Real.exp (-β) / 4) * (1 / 2 : ℝ) ^ n)
      (Real.exp (-β) / 2)
    convert hasSum_geometric_two.mul_left (Real.exp (-β) / 4) using 1 <;> ring
  have hle (n : ℕ) : ((n : ℝ) + 2) ^ 2 * Real.exp (-β * ((n : ℝ) + 2) ^ 2) ≤ g n := by
    have h := gaussian_frequency_tail_term hβ (n := n + 2) (by omega)
    convert h using 1
    · norm_num
    · dsimp [g]
      rw [pow_add]
      norm_num
      ring
  have hf : Summable (fun n : ℕ ↦ ((n : ℝ) + 2) ^ 2 *
      Real.exp (-β * ((n : ℝ) + 2) ^ 2)) :=
    hg.summable.of_nonneg_of_le (fun n ↦ by positivity) hle
  exact ⟨hf, (hf.tsum_le_tsum hle hg.summable).trans_eq hg.tsum_eq⟩

end PaperVerification.ColdSpots
