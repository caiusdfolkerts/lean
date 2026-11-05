module

public import Ellipsoid.SteinerVolume
public import tau_ceti.measure_theory.constructions.haar_to_sphere
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

noncomputable section

open MeasureTheory Set Metric Filter
open scoped BigOperators Topology

namespace EllipsoidVerification

def PositivelyHomogeneous {n : ℕ} (f : Space n → ℝ) (γ : ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → ∀ x, f (r • x) = r ^ γ * f x

theorem integrable_sphere_of_continuousOn_compl_zero {n : ℕ} {f : Space n → ℝ}
    (hf : ContinuousOn f ({0}ᶜ : Set (Space n))) :
    Integrable (fun u : sphere (0 : Space n) 1 => f u) volume.toSphere := by
  have hc : Continuous (fun u : sphere (0 : Space n) 1 => f u) := by
    apply hf.comp_continuous continuous_subtype_val
    intro u
    intro hu
    have hn := u.property
    simpa [show (u : Space n) = 0 from hu] using hn
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem homogeneous_bound {n : ℕ} {f : Space n → ℝ} {γ : ℝ}
    (hf : ContinuousOn f ({0}ᶜ : Set (Space n))) (hh : PositivelyHomogeneous f γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Space n, x ≠ 0 → ‖f x‖ ≤ C * ‖x‖ ^ γ := by
  obtain ⟨B, hB⟩ := (isCompact_sphere (0 : Space n) 1).exists_bound_of_continuousOn
    (hf.mono (by intro x hx hx0; simpa [show x = 0 from hx0] using hx))
  refine ⟨max B 0, le_max_right _ _, fun x hx => ?_⟩
  have hxpos := norm_pos_iff.mpr hx
  have heq : f x = ‖x‖ ^ γ * f (‖x‖⁻¹ • x) := by
    simpa only [smul_smul, mul_inv_cancel₀ hxpos.ne', one_smul] using
      hh ‖x‖ hxpos (‖x‖⁻¹ • x)
  rw [heq, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hxpos γ)]
  exact (mul_le_mul_of_nonneg_left
    ((hB _ (normalized_mem_unitSphere hx)).trans (le_max_left B 0))
    (Real.rpow_nonneg hxpos.le γ)).trans_eq (mul_comm _ _)

theorem integrable_norm_rpow_gaussian {n : ℕ} (hn : 0 < n) {γ : ℝ} (hγ : -(n : ℝ) < γ) :
    Integrable (fun x : Space n => ‖x‖ ^ γ * Real.exp (-‖x‖ ^ 2)) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  apply (integrable_fun_norm_addHaar (volume : Measure (Space n))
    (f := fun r : ℝ => r ^ γ * Real.exp (-r ^ 2))).mpr
  have hi := integrableOn_rpow_mul_exp_neg_mul_sq (b := 1) (by norm_num)
    (s := (n : ℝ) + γ - 1) (by linarith)
  apply hi.congr_fun _ measurableSet_Ioi
  intro r hr
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul, neg_mul, one_mul]
  have hpow : r ^ ((n : ℝ) + γ - 1) = r ^ (n - 1) * r ^ γ := by
    rw [← Real.rpow_natCast r (n - 1), ← Real.rpow_add hr]
    congr 1
    rw [Nat.cast_sub hn, Nat.cast_one]
    ring
  rw [hpow]
  ring

theorem integrable_homogeneous_gaussian {n : ℕ} (hn : 0 < n) {f : Space n → ℝ} {γ : ℝ}
    (hf : ContinuousOn f ({0}ᶜ : Set (Space n))) (hh : PositivelyHomogeneous f γ)
    (hγ : -(n : ℝ) < γ) : Integrable (fun x => f x * Real.exp (-‖x‖ ^ 2)) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨C, hC, hb⟩ := homogeneous_bound hf hh
  apply ((integrable_norm_rpow_gaussian hn hγ).const_mul C).mono'
  · exact ((measurable_of_continuousOn_compl_singleton 0 hf).mul
      (measurable_norm.pow_const 2 |>.neg.exp)).aestronglyMeasurable
  · filter_upwards [volume.ae_ne (0 : Space n)] with x hx
    simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_right (hb x hx) (Real.exp_pos _).le).trans_eq (by ring)

/-- Polar coordinates for a homogeneous integrand times a Gaussian weight,
with the exact radial Gamma factor and the full locally integrable range. -/
theorem integral_homogeneous_gaussian {n : ℕ} (hn : 0 < n) {f : Space n → ℝ} {γ : ℝ}
    (hf : ContinuousOn f ({0}ᶜ : Set (Space n))) (hh : PositivelyHomogeneous f γ)
    (hγ : -(n : ℝ) < γ) :
    (∫ x : Space n, f x * Real.exp (-‖x‖ ^ 2)) =
      (1 / 2 : ℝ) * Real.Gamma (((n : ℝ) + γ) / 2) *
        ∫ u : sphere (0 : Space n) 1, f u ∂volume.toSphere := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [TauCeti.integral_eq_integral_toSphere_integral_Ioi _
    (integrable_homogeneous_gaussian hn hf hh hγ)]
  have hr (u : sphere (0 : Space n) 1) :
      (∫ r in Ioi (0 : ℝ), r ^ (Module.finrank ℝ (Space n) - 1) •
        (f (r • (u : Space n)) * Real.exp (-‖r • (u : Space n)‖ ^ 2))) =
      ((1 / 2 : ℝ) * Real.Gamma (((n : ℝ) + γ) / 2)) * f u := by
    have heq : (∫ r in Ioi (0 : ℝ), r ^ (Module.finrank ℝ (Space n) - 1) •
        (f (r • (u : Space n)) * Real.exp (-‖r • (u : Space n)‖ ^ 2))) =
        ∫ r in Ioi (0 : ℝ), (r ^ ((n : ℝ) + γ - 1) * Real.exp (-r ^ (2 : ℝ))) * f u := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      rw [hh r hr, norm_smul, Real.norm_of_nonneg hr.le, norm_eq_of_mem_sphere u, mul_one]
      simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
      rw [← Real.rpow_natCast r (n - 1), Nat.cast_sub hn, Nat.cast_one, Real.rpow_two]
      have hp : r ^ ((n : ℝ) - 1) * r ^ γ = r ^ ((n : ℝ) + γ - 1) := by
        rw [← Real.rpow_add hr]
        congr 1
        ring
      calc
        _ = (r ^ ((n : ℝ) - 1) * r ^ γ) *
            (f (u : Space n) * Real.exp (-r ^ 2)) := by ring
        _ = _ := by rw [hp]; ring
    rw [heq, integral_mul_const, integral_rpow_mul_exp_neg_rpow (by norm_num) (by linarith)]
    congr 3
    ring
  simp_rw [hr]
  exact integral_const_mul _ _

theorem closedBall_ae_eq_ball_one {n : ℕ} :
    Metric.closedBall (0 : Space n) 1 =ᵐ[volume] Metric.ball 0 1 := by
  have hs := MeasureTheory.Measure.addHaar_sphere_of_ne_zero (volume : Measure (Space n))
    (0 : Space n) (by norm_num : (1 : ℝ) ≠ 0)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hs] with x hx
  have hx' : ‖x‖ ≠ 1 := by simpa only [Metric.mem_sphere, dist_zero_right, Set.mem_compl_iff] using hx
  simp only [Metric.mem_closedBall, Metric.mem_ball, dist_zero_right]
  exact propext (le_iff_lt_or_eq.trans (or_iff_left hx'))

theorem integral_homogeneous_zero_unitBall {n : ℕ} (hn : 0 < n) {f : Space n → ℝ}
    (hf : IntegrableOn f (Metric.closedBall 0 1)) (hh : PositivelyHomogeneous f 0) :
    (∫ x in Metric.closedBall (0 : Space n) 1, f x) =
      (n : ℝ)⁻¹ * ∫ u : sphere (0 : Space n) 1, f u ∂volume.toSphere := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [setIntegral_congr_set closedBall_ae_eq_ball_one,
    TauCeti.setIntegral_ball_zero_eq_integral_Ioo (hf.mono_set ball_subset_closedBall)]
  have heq : (∫ r in Ioo (0 : ℝ) 1, r ^ (Module.finrank ℝ (Space n) - 1) •
      ∫ u : sphere (0 : Space n) 1, f (r • (u : Space n)) ∂volume.toSphere) =
      (∫ r in Ioo (0 : ℝ) 1, r ^ (n - 1)) *
        ∫ u : sphere (0 : Space n) 1, f u ∂volume.toSphere := by
    rw [← integral_mul_const]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r hr
    simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul,
      hh r hr.1, Real.rpow_zero, one_mul]
  rw [heq]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    integral_pow]
  have hcast : ((n - 1 : ℕ) : ℝ) + 1 = n := by
    rw [Nat.cast_sub hn, Nat.cast_one]
    ring
  simp [Nat.sub_add_cancel hn, hcast, hn.ne']

end EllipsoidVerification
