module

public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

set_option autoImplicit false
noncomputable section

/-! The real power layer-cake identity for arbitrary finite measures. -/

open Set MeasureTheory Filter

namespace VolumePolynomials.BerwaldMoments

section LayerCake

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

/-- A real-valued power version of layer cake on a finite measure space. -/
theorem power_layer_cake {f : α → ℝ} (hf : AEMeasurable f μ)
    (hn : 0 ≤ᵐ[μ] f) (p : ℕ) :
    (∫ x, f x ^ (p + 1) ∂μ) =
      (p + 1 : ℝ) * ∫ t in Ioi 0, t ^ p * μ.real {x | t ≤ f x} := by
  first
  | have hg : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ t ^ p := by
      first
      | filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact pow_nonneg ht.le p
    have h := lintegral_comp_eq_lintegral_meas_le_mul (g := fun t : ℝ => t ^ p) μ hn hf
      (fun t _ => (continuous_id.pow p).intervalIntegrable 0 t) hg
    have hint (x : α) : (∫ t in 0..f x, t ^ p) =
        f x ^ (p + 1) / (p + 1 : ℝ) := by
      first
      | rw [integral_pow]
        simp
    simp only [hint] at h
    have htail : Measurable (fun t : ℝ => μ {x | t ≤ f x}) :=
      Antitone.measurable (fun _ _ hst => measure_mono (fun _ hx => hst.trans hx))
    have hrhs : AEStronglyMeasurable
        (fun t : ℝ => t ^ p * μ.real {x | t ≤ f x}) (volume.restrict (Ioi 0)) :=
      ((measurable_id.pow_const p).mul htail.ennreal_toReal).aestronglyMeasurable
    have hrhsn : 0 ≤ᵐ[volume.restrict (Ioi 0)]
        (fun t : ℝ => t ^ p * μ.real {x | t ≤ f x}) := by
      first
      | filter_upwards [hg] with t ht
        exact mul_nonneg ht measureReal_nonneg
    have hlhsn : 0 ≤ᵐ[μ] (fun x => f x ^ (p + 1) / (p + 1 : ℝ)) := by
      first
      | filter_upwards [hn] with x hx
        exact div_nonneg (pow_nonneg hx _) (by positivity)
    have hlin : (∫ t in Ioi 0, t ^ p * μ.real {x | t ≤ f x}) =
        ENNReal.toReal (∫⁻ t in Ioi 0, μ {x | t ≤ f x} * ENNReal.ofReal (t ^ p)) := by
      first
      | rw [integral_eq_lintegral_of_nonneg_ae hrhsn hrhs]
        congr 1
        apply lintegral_congr_ae
        filter_upwards [hg] with t ht
        rw [ENNReal.ofReal_mul ht, measureReal_def,
          ENNReal.ofReal_toReal (measure_ne_top μ _), mul_comm]
    have hreal : (∫ x, f x ^ (p + 1) / (p + 1 : ℝ) ∂μ) =
        ∫ t in Ioi 0, t ^ p * μ.real {x | t ≤ f x} := by
      first
      | rw [integral_eq_lintegral_of_nonneg_ae hlhsn
          ((hf.pow_const (p + 1)).div_const _).aestronglyMeasurable, h, hlin]
    rw [integral_div] at hreal
    have hp : (p + 1 : ℝ) ≠ 0 := by positivity
    exact (div_eq_iff hp).mp hreal |>.trans (mul_comm _ _)

end LayerCake

end VolumePolynomials.BerwaldMoments
