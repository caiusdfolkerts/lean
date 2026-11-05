module
public import PaperVerification.TriangularGaussian
public import Mathlib.Algebra.Ring.Int.Parity
@[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

lemma gaussian_pair_sum {α : ℝ} (hα : 0 < α) (t : ℝ) :
    gaussian α t + gaussian α (t - 1 / 2) = gaussian (α / 4) (2 * t) := by
  have h := gaussian_split (show 0 < α / 4 by positivity) (2 * t)
  rw [show 4 * (α / 4) = α by ring,
    show 2 * t / 2 = t by ring, show (2 * t - 1) / 2 = t - 1 / 2 by ring] at h
  exact h.symm

lemma gaussian_pair_sum_le {α : ℝ} (hα : 0 < α) (t : ℝ) :
    gaussian α t + gaussian α (t - 1 / 2) ≤ gaussian α 0 + gaussian α (1 / 2) := by
  have h0 := gaussian_pair_sum hα 0
  simp only [zero_sub, mul_zero, gaussian_even] at h0
  rw [gaussian_pair_sum hα, h0]
  exact gaussian_le_zero (by positivity) _

lemma gaussian_pair_sum_eq_iff {α : ℝ} (hα : 0 < α) (t : ℝ) :
    gaussian α t + gaussian α (t - 1 / 2) = gaussian α 0 + gaussian α (1 / 2) ↔
      ∃ m : ℤ, 2 * t = (m : ℝ) := by
  have h0 := gaussian_pair_sum hα 0
  simp only [zero_sub, mul_zero, gaussian_even] at h0
  rw [gaussian_pair_sum hα, h0]
  exact gaussian_maximum_iff (by positivity) _

lemma gaussian_zero_gt_half {α : ℝ} (hα : 0 < α) :
    gaussian α (1 / 2) < gaussian α 0 := by
  apply lt_of_le_of_ne (gaussian_le_zero hα _)
  intro heq
  obtain ⟨m, hm⟩ := (gaussian_maximum_iff hα (1 / 2)).mp heq
  have hm0 : (0 : ℤ) < m := by exact_mod_cast (show (0 : ℝ) < m by linarith)
  have hm1 : m < (1 : ℤ) := by exact_mod_cast (show (m : ℝ) < 1 by linarith)
  omega

lemma gaussian_pair_difference_abs_le {α : ℝ} (hα : 0 < α) (t : ℝ) :
    |gaussian α t - gaussian α (t - 1 / 2)| ≤ gaussian α 0 - gaussian α (1 / 2) := by
  have hp := gaussian_shift_product_min hα t
  have hs : gaussian α t ^ 2 + gaussian α (t - 1 / 2) ^ 2 ≤
      gaussian α 0 ^ 2 + gaussian α (1 / 2) ^ 2 := by
    have h0 := gaussian_diagonal_sum hα 0
    simp only [zero_sub, mul_zero, gaussian_even] at h0
    rw [gaussian_diagonal_sum hα, h0]
    exact mul_le_mul_of_nonneg_left (gaussian_le_zero (half_pos hα) _)
      (gaussian_pos (half_pos hα) _).le
  have hd := (gaussian_zero_gt_half hα).le
  apply (sq_le_sq₀ (abs_nonneg _) (sub_nonneg.mpr hd)).mp
  rw [sq_abs]
  nlinarith

lemma triangularGaussian_upper_algebra {α : ℝ} (hα : 0 < α) (z : TriPoint) :
    triangularGaussian α z ≤ triangularGaussian α 0 ∧
      (triangularGaussian α z = triangularGaussian α 0 →
        (∃ p : ℤ, 2 * (z.1 - z.2 / 2) = (p : ℝ)) ∧
        (∃ q : ℤ, z.2 = (q : ℝ))) := by
  let s := z.1 - z.2 / 2
  let t := z.2 / 2
  let X := gaussian α s + gaussian α (s - 1 / 2)
  let Y := gaussian (3 * α) t + gaussian (3 * α) (t - 1 / 2)
  let A := gaussian α 0 + gaussian α (1 / 2)
  let B := gaussian (3 * α) 0 + gaussian (3 * α) (1 / 2)
  let d := gaussian α 0 - gaussian α (1 / 2)
  let e := gaussian (3 * α) 0 - gaussian (3 * α) (1 / 2)
  let D := gaussian α s - gaussian α (s - 1 / 2)
  let E := gaussian (3 * α) t - gaussian (3 * α) (t - 1 / 2)
  have h3 : 0 < 3 * α := by positivity
  have hX : 0 < X := add_pos (gaussian_pos hα _) (gaussian_pos hα _)
  have hY : 0 < Y := add_pos (gaussian_pos h3 _) (gaussian_pos h3 _)
  have hA : 0 < A := add_pos (gaussian_pos hα _) (gaussian_pos hα _)
  have hB : 0 < B := add_pos (gaussian_pos h3 _) (gaussian_pos h3 _)
  have hXA : X ≤ A := gaussian_pair_sum_le hα s
  have hYB : Y ≤ B := gaussian_pair_sum_le h3 t
  have hd : 0 < d := sub_pos.mpr (gaussian_zero_gt_half hα)
  have he : 0 < e := sub_pos.mpr (gaussian_zero_gt_half h3)
  have hD : |D| ≤ d := gaussian_pair_difference_abs_le hα s
  have hE : |E| ≤ e := gaussian_pair_difference_abs_le h3 t
  have hDE : D * E ≤ d * e := (le_abs_self _).trans (by
    rw [abs_mul]
    exact mul_le_mul hD hE (abs_nonneg E) hd.le)
  have hXY : X * Y ≤ A * B := mul_le_mul hXA hYB hY.le hA.le
  have hf : 2 * triangularGaussian α z = X * Y + D * E := by
    rw [triangularGaussian_eq_products hα]
    dsimp [X,Y,D,E,s,t]
    ring
  have hf0 : 2 * triangularGaussian α 0 = A * B + d * e := by
    rw [triangularGaussian_eq_products hα]
    norm_num only [Prod.fst_zero, Prod.snd_zero, zero_div, sub_self, zero_sub, gaussian_even]
    dsimp [A,B,d,e]
    ring
  refine ⟨by linarith, ?_⟩
  intro heq
  have hXYeq : X * Y = A * B := by rw [heq] at hf; linarith
  have hXeq : X = A := by
    apply le_antisymm hXA
    by_contra hn
    have hlt := mul_lt_mul_of_pos_right (lt_of_not_ge hn) hB
    have hle := mul_le_mul_of_nonneg_left hYB hX.le
    nlinarith
  have hYeq : Y = B := by
    apply mul_left_cancel₀ hA.ne'
    simpa only [hXeq] using hXYeq
  refine ⟨(gaussian_pair_sum_eq_iff hα s).mp hXeq, ?_⟩
  obtain ⟨q,hq⟩ := (gaussian_pair_sum_eq_iff h3 t).mp hYeq
  exact ⟨q, by dsimp [t] at hq; linarith⟩

theorem triangularGaussian_le_zero {α : ℝ} (hα : 0 < α) (z : TriPoint) :
    triangularGaussian α z ≤ triangularGaussian α 0 :=
  (triangularGaussian_upper_algebra hα z).1

lemma triangularGaussian_half_strict {α : ℝ} (hα : 0 < α) :
    triangularGaussian α ((1 / 2 : ℝ),0) < triangularGaussian α 0 := by
  rw [triangularGaussian_eq_products hα, triangularGaussian_eq_products hα]
  norm_num only [Prod.fst, Prod.snd, Prod.fst_zero, Prod.snd_zero, zero_div,
    sub_zero, sub_self, zero_sub, gaussian_even]
  have h := mul_pos (sub_pos.mpr (gaussian_zero_gt_half hα))
    (sub_pos.mpr (gaussian_zero_gt_half (show 0 < 3 * α by positivity)))
  nlinarith

/-- The maximum of the actual triangular Gaussian occurs precisely at its
integral Eisenstein lattice, with no use of a separate triangular minimum theorem. -/
theorem triangularGaussian_maximum_iff {α : ℝ} (hα : 0 < α) (z : TriPoint) :
    triangularGaussian α z = triangularGaussian α 0 ↔ z ∈ triIntegerLattice := by
  constructor
  · intro hz
    obtain ⟨⟨p,hp⟩,⟨q,hq⟩⟩ := (triangularGaussian_upper_algebra hα z).2 hz
    have hu : z.1 = ((p : ℝ) + q) / 2 := by linarith
    rcases Int.even_or_odd (p + q) with he | ho
    · obtain ⟨k,hk⟩ := he
      refine ⟨(k,q), ?_⟩
      apply Prod.ext
      · change (k : ℝ) = z.1
        have hkr : (p : ℝ) + q = k + k := by exact_mod_cast hk
        linarith
      · exact hq.symm
    · obtain ⟨k,hk⟩ := ho
      have he : z = ((1 / 2 : ℝ),0) + eisEmbed (k,q) := by
        apply Prod.ext
        · change z.1 = 1 / 2 + (k : ℝ)
          have hkr : (p : ℝ) + q = 2 * k + 1 := by exact_mod_cast hk
          linarith
        · simpa [eisEmbed] using hq
      rw [he, triangularGaussian_periodic] at hz
      exact False.elim ((ne_of_lt (triangularGaussian_half_strict hα)) hz)
  · rintro ⟨m,rfl⟩
    simpa only [zero_add] using triangularGaussian_periodic α 0 m

theorem triangularGaussian_c_lt_zero {α : ℝ} (hα : 0 < α) :
    triangularGaussian α triC < triangularGaussian α 0 := by
  apply lt_of_le_of_ne (triangularGaussian_le_zero hα triC)
  intro heq
  obtain ⟨m, hm⟩ := (triangularGaussian_maximum_iff hα triC).mp heq
  have h := congrArg Prod.fst hm
  change (m.1 : ℝ) = 1 / 3 at h
  have h0 : (0 : ℤ) < m.1 := by exact_mod_cast (show (0 : ℝ) < m.1 by linarith)
  have h1 : m.1 < (1 : ℤ) := by exact_mod_cast (show (m.1 : ℝ) < 1 by linarith)
  omega

end PaperVerification.ColdSpots
