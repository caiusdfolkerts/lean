module

public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.NormCast

@[expose] public section
noncomputable section

/-!
The analytic mechanism of the natural-boundary argument in Theorem 7.3:
absolutely summable weights at distinct unit-circle frequencies produce genuine
nonzero radial residues. No Fourier expansion is assumed to be proved by this file.
-/

namespace VolumePolynomials

open scoped Topology
open Filter

noncomputable def radialKernel (r : ℝ) (q : ℂ) : ℂ :=
  (1 - (r : ℂ)) * ((r : ℂ) * q) / (1 - (r : ℂ) * q)

theorem radialKernel_norm_le_one (r : ℝ) (hr₀ : 0 ≤ r) (hr₁ : r < 1)
    (q : ℂ) (hq : ‖q‖ = 1) : ‖radialKernel r q‖ ≤ 1 := by
  first
  | have hrq : ‖(r : ℂ) * q‖ = r := by
      first
      | simp [norm_mul, hq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr₀]
    have hden : 1 - r ≤ ‖1 - (r : ℂ) * q‖ := by
      first
      | simpa only [norm_one, hrq] using norm_sub_norm_le (1 : ℂ) ((r : ℂ) * q)
    have hdenpos : 0 < ‖1 - (r : ℂ) * q‖ := lt_of_lt_of_le (sub_pos.mpr hr₁) hden
    have hone : ‖1 - (r : ℂ)‖ = 1 - r := by
      first
      | rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hr₁)]
    rw [radialKernel, norm_div, norm_mul, hone, hrq, div_le_iff₀ hdenpos, one_mul]
    nlinarith [sq_nonneg (1 - r)]

theorem radialKernel_one (r : ℝ) (hr : r < 1) : radialKernel r 1 = (r : ℂ) := by
  first
  | have hden : (1 : ℂ) - (r : ℂ) ≠ 0 := by
      first
      | exact_mod_cast (ne_of_gt (sub_pos.mpr hr))
    dsimp [radialKernel]
    simp only [mul_one]
    field_simp [hden] <;> ring

theorem radialKernel_tendsto {r : ℕ → ℝ} (hr₁ : ∀ n, r n < 1)
    (hrlim : Tendsto r atTop (𝓝 1)) (q : ℂ) :
    Tendsto (fun n => radialKernel (r n) q) atTop (𝓝 (if q = 1 then 1 else 0)) := by
  first
  | classical
    have hrC : Tendsto (fun n => (r n : ℂ)) atTop (𝓝 1) := by
      first
      | simpa only [Function.comp_def, Complex.ofReal_one] using
          Complex.continuous_ofReal.continuousAt.tendsto.comp hrlim
    have hone : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1) := tendsto_const_nhds
    by_cases hq : q = 1
    · subst q
      simpa [radialKernel_one _ (hr₁ _)] using hrC
    · have hden : (1 : ℂ) - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
      have h := ((hone.sub hrC).mul (hrC.mul_const q)).div
        (hone.sub (hrC.mul_const q)) (by simpa only [one_mul] using hden)
      simpa only [Pi.div_def, one_mul, sub_self, zero_mul, zero_div,
        if_neg hq, radialKernel] using h

/-- A holomorphic-disc candidate obtained from weighted elementary Cauchy kernels. -/
noncomputable def weightedCauchySeries {ι : Type*} (β u : ι → ℂ) (z : ℂ) : ℂ :=
  ∑' i, β i * (z * u i) / (1 - z * u i)

theorem weighted_radial_residue {ι : Type*} (β u : ι → ℂ)
    (hβ : Summable fun i => ‖β i‖) (hu : ∀ i, ‖u i‖ = 1)
    (huinj : Function.Injective u) (r : ℕ → ℝ)
    (hr₀ : ∀ n, 0 ≤ r n) (hr₁ : ∀ n, r n < 1)
    (hrlim : Tendsto r atTop (𝓝 1)) (j : ι) :
    Tendsto (fun n => (1 - (r n : ℂ)) *
      weightedCauchySeries β u ((r n : ℂ) / u j)) atTop (𝓝 (β j)) := by
  first
  | classical
    have huj : u j ≠ 0 := by intro h; simpa [h] using hu j
    have hqnorm (i : ι) : ‖u i / u j‖ = 1 := by simp [norm_div, hu]
    have hlim := tendsto_tsum_of_dominated_convergence hβ
      (f := fun n i => β i * radialKernel (r n) (u i / u j))
      (g := fun i => if i = j then β j else 0) (by
        intro i
        by_cases hij : i = j
        · subst i
          have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => β j) atTop (𝓝 (β j))).mul
            (radialKernel_tendsto hr₁ hrlim (u j / u j))
          simpa [huj] using h
        · have hq : u i / u j ≠ 1 := by
            first
            | intro heq
              exact hij (huinj ((div_eq_one_iff_eq huj).mp heq))
          have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => β i) atTop (𝓝 (β i))).mul
            (radialKernel_tendsto hr₁ hrlim (u i / u j))
          simpa [hq, hij] using h) (by
        apply Eventually.of_forall
        intro n i
        rw [norm_mul]
        exact (mul_le_mul_of_nonneg_left
          (radialKernel_norm_le_one (r n) (hr₀ n) (hr₁ n) _ (hqnorm i))
          (norm_nonneg _)).trans_eq (mul_one _))
    have hsame (n : ℕ) :
        (1 - (r n : ℂ)) * weightedCauchySeries β u ((r n : ℂ) / u j) =
          ∑' i, β i * radialKernel (r n) (u i / u j) := by
      first
      | rw [weightedCauchySeries, ← tsum_mul_left]
        apply tsum_congr
        intro i
        rw [show ((r n : ℂ) / u j) * u i = (r n : ℂ) * (u i / u j) by ring]
        simp only [radialKernel, div_eq_mul_inv]
        ring
    simpa only [← hsame, tsum_ite_eq] using hlim

/-- A nonzero radial residue excludes every finite radial limit at that boundary point. -/
theorem no_finite_radial_limit {ι : Type*} (β u : ι → ℂ)
    (hβ : Summable fun i => ‖β i‖) (hu : ∀ i, ‖u i‖ = 1)
    (huinj : Function.Injective u) (r : ℕ → ℝ)
    (hr₀ : ∀ n, 0 ≤ r n) (hr₁ : ∀ n, r n < 1)
    (hrlim : Tendsto r atTop (𝓝 1)) (j : ι) (hβj : β j ≠ 0) :
    ¬ ∃ w : ℂ, Tendsto (fun n => weightedCauchySeries β u ((r n : ℂ) / u j))
      atTop (𝓝 w) := by
  first
  | rintro ⟨w, hw⟩
    have hrC : Tendsto (fun n => (r n : ℂ)) atTop (𝓝 1) := by
      first
      | simpa only [Function.comp_def, Complex.ofReal_one] using
          Complex.continuous_ofReal.continuousAt.tendsto.comp hrlim
    have hz : Tendsto (fun n => (1 - (r n : ℂ)) *
        weightedCauchySeries β u ((r n : ℂ) / u j)) atTop (𝓝 0) := by
      first
      | simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1)).sub hrC).mul hw
    exact hβj (tendsto_nhds_unique
      (weighted_radial_residue β u hβ hu huinj r hr₀ hr₁ hrlim j) hz)

end VolumePolynomials
