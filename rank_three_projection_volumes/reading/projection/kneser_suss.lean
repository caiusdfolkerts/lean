/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Lebesgue.BrunnMinkowski.Quantile
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Tactic.Linarith.Frontend

@[expose] public section
set_option autoImplicit false
noncomputable section

/-!
# The Kneser–Süss integral bound

This public supplement preserves the proof of the private Kneser–Süss
inequality in the pinned TauCeti source, commit
`06d5bb4e3ebb737dc6538567f5c53bf8800b9362`, file
`MeasureTheory/Measure/Lebesgue/BrunnMinkowski/Equality.lean`.
The theorem body is unchanged; only its visibility and enclosing namespace
are changed. No equality or stability assertion is imported as an assumption.

Original complete source SHA-256: `8cbd41fb3e547a401871d7e0d6ab5da7e43abd5301e6e74adf1b03535d9bfc0b`.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set TauCeti
open scoped ENNReal Pointwise RealInnerProductSpace

namespace RankThreeProjection.KneserSuss

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {e : E} {K L : Set E}

/-- **The Kneser–Süss integral inequality.** Along the weighted height quantile
`z = (1 - θ) z_K + θ z_L`, the derivative `z'` times the weighted geometric mean of the section
volumes of `K` at `z_K τ` and of `L` at `z_L τ`, integrated over `Ioo 0 1`, is at most the volume of
`(1 - θ) • K + θ • L`. -/
theorem setLIntegral_ofReal_le_volume_smul_add_smul (hK : Convex ℝ K)
    (hKb : Bornology.IsBounded K) (hKm : MeasurableSet K) (hK0 : volume K ≠ 0)
    (hL : Convex ℝ L) (hLb : Bornology.IsBounded L) (hLm : MeasurableSet L)
    (hL0 : volume L ≠ 0) (he : ‖e‖ = 1) {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    ∫⁻ τ in Ioo 0 1, ENNReal.ofReal
      (((1 - θ) * (volume.real K / volume.real {y : (ℝ ∙ e)ᗮ |
          (y : E) + ((volume[|K]).map fun x ↦ ⟪e, x⟫).quantile τ • e ∈ K}) +
        θ * (volume.real L / volume.real {y : (ℝ ∙ e)ᗮ |
          (y : E) + ((volume[|L]).map fun x ↦ ⟪e, x⟫).quantile τ • e ∈ L})) *
      (volume.real {y : (ℝ ∙ e)ᗮ |
          (y : E) + ((volume[|K]).map fun x ↦ ⟪e, x⟫).quantile τ • e ∈ K} ^ (1 - θ) *
        volume.real {y : (ℝ ∙ e)ᗮ |
          (y : E) + ((volume[|L]).map fun x ↦ ⟪e, x⟫).quantile τ • e ∈ L} ^ θ)) ≤
      volume ((1 - θ) • K + θ • L) := by
  set zK := ((volume[|K]).map fun x ↦ ⟪e, x⟫).quantile
  set zL := ((volume[|L]).map fun x ↦ ⟪e, x⟫).quantile
  set a : ℝ → ℝ := fun τ ↦ volume.real {y : (ℝ ∙ e)ᗮ | (y : E) + zK τ • e ∈ K}
  set b : ℝ → ℝ := fun τ ↦ volume.real {y : (ℝ ∙ e)ᗮ | (y : E) + zL τ • e ∈ L}
  set M := (1 - θ) • K + θ • L
  have ha (τ : ℝ) (hτ : τ ∈ Ioo 0 1) : 0 < a τ :=
    hK.volume_real_hyperplaneSection_quantile_pos hKb hK0 he hτ
  have hb (τ : ℝ) (hτ : τ ∈ Ioo 0 1) : 0 < b τ :=
    hL.volume_real_hyperplaneSection_quantile_pos hLb hL0 he hτ
  -- The weighted quantile `z` is strictly increasing with positive derivative `z'`.
  set z : ℝ → ℝ := fun τ ↦ (1 - θ) * zK τ + θ * zL τ
  set z' : ℝ → ℝ := fun τ ↦ (1 - θ) * (volume.real K / a τ) + θ * (volume.real L / b τ)
  have hz' (τ : ℝ) (hτ : τ ∈ Ioo 0 1) : HasDerivAt z (z' τ) τ :=
    ((hK.hasDerivAt_quantile_map_inner_cond hKb hKm hK0 he hτ).const_mul (1 - θ)).add
      ((hL.hasDerivAt_quantile_map_inner_cond hLb hLm hL0 he hτ).const_mul θ)
  have hzpos (τ : ℝ) (hτ : τ ∈ Ioo 0 1) : 0 < z' τ := by
    have hKr : 0 < volume.real K := ENNReal.toReal_pos hK0 hKb.measure_lt_top.ne
    have hLr : 0 < volume.real L := ENNReal.toReal_pos hL0 hLb.measure_lt_top.ne
    exact add_pos (mul_pos (by linarith) (div_pos hKr (ha τ hτ)))
      (mul_pos hθ₀ (div_pos hLr (hb τ hτ)))
  have hzmono : StrictMonoOn z (Ioo 0 1) := by
    intro s hs t ht hst
    have hK' := strictMonoOn_quantile _ (continuous_cdf_map_inner_cond he hK0
      hKb.measure_lt_top.ne) hs ht hst
    have hL' := strictMonoOn_quantile _ (continuous_cdf_map_inner_cond he hL0
      hLb.measure_lt_top.ne) hs ht hst
    simp only [z]
    nlinarith
  -- Pointwise, the integrand is bounded by the change-of-variables integrand along `z`, by
  -- Brunn–Minkowski in the hyperplane.
  have hpt (τ : ℝ) (hτ : τ ∈ Ioo 0 1) : ENNReal.ofReal (z' τ * (a τ ^ (1 - θ) * b τ ^ θ)) ≤
      ENNReal.ofReal |z' τ| * volume {y : (ℝ ∙ e)ᗮ | (y : E) + z τ • e ∈ M} := by
    rw [abs_of_pos (hzpos τ hτ), ENNReal.ofReal_mul (hzpos τ hτ).le,
      ENNReal.ofReal_mul (Real.rpow_nonneg (ha τ hτ).le _),
      ← ENNReal.ofReal_rpow_of_nonneg (ha τ hτ).le (by linarith),
      ← ENNReal.ofReal_rpow_of_nonneg (hb τ hτ).le hθ₀.le, ofReal_measureReal
        (hKb.volume_hyperplaneSection_lt_top e _).ne, ofReal_measureReal
        (hLb.volume_hyperplaneSection_lt_top e _).ne]
    exact mul_le_mul_right
      (volume_hyperplaneSection_rpow_mul_volume_hyperplaneSection_rpow_le e hKm hLm hθ₀ hθ₁ _ _) _
  -- Change variables along `z`, then apply Cavalieri's formula to the convex set `M`.
  refine (setLIntegral_mono' measurableSet_Ioo hpt).trans ?_
  rw [← lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
    (fun τ hτ ↦ (hz' τ hτ).hasDerivWithinAt) hzmono.injOn
    (fun ζ ↦ volume {y : (ℝ ∙ e)ᗮ | (y : E) + ζ • e ∈ M})]
  refine (setLIntegral_le_lintegral _ _).trans_eq ?_
  rw [← volume_eq_lintegral_volume_hyperplaneSection e he
    (((hK.smul _).add (hL.smul _)).nullMeasurableSet (μ := volume))]

end RankThreeProjection.KneserSuss
