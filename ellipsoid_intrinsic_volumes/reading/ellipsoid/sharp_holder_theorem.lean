module

public import Ellipsoid.SpherePerturbation
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology

namespace EllipsoidVerification

theorem eventually_power_bound_below_linear {n : ℕ} (hn : 0 < n)
    {γ A C d : ℝ} (hγ : 1 / (n : ℝ) < γ) (hA : 0 < A) (hC : 0 < C) (hd : 0 < d) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, C * (A * ε ^ n) ^ γ < d * ε := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : 0 < (n : ℝ) * γ - 1 := by
    have h := (div_lt_iff₀ hnR).mp hγ
    nlinarith
  have ht : Tendsto (fun ε : ℝ => C * A ^ γ * ε ^ ((n : ℝ) * γ - 1))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero, id_eq] using
      (tendsto_nhdsWithin_of_tendsto_nhds (tendsto_id : Tendsto (id : ℝ → ℝ) (𝓝 0) (𝓝 0))
        |>.rpow_const_nhds_zero hp).const_mul (C * A ^ γ)
  filter_upwards [ht.eventually (gt_mem_nhds hd), self_mem_nhdsWithin] with ε hsmall hε
  have h := mul_lt_mul_of_pos_right hsmall hε
  convert h using 1
  rw [Real.mul_rpow hA.le (pow_nonneg hε.le n), ← Real.rpow_natCast_mul hε.le,
    Real.rpow_sub_one hε.ne']
  field_simp [hε.ne']

/-- The non-improvability assertion of Theorem 1.2, with explicit full
ellipsoids in every proposed neighborhood of every interior sphere. -/
theorem sharp_holder_recovery : SharpHolderRecovery := by
  intro n hn a b r ha har hrb γ hγ δ C hδ hC
  have hr : 0 < r := ha.trans har
  have hγpos : 0 < γ := (one_div_pos.mpr (by exact_mod_cast hn)).trans hγ
  obtain ⟨u, v, c, hc, hu, hv, hpoly⟩ := exists_constant_perturbation_real_roots hn
  obtain ⟨A, hA, hvol⟩ := eventually_perturbed_volume_bound hn hr hpoly
  obtain ⟨d, hd, haxis⟩ := eventually_perturbed_axis_lower hn hr hu hv
  have hU := eventually_perturbedAxes_near hr har hrb hδ u
  have hV := eventually_perturbedAxes_near hr har hrb hδ v
  have hpower := eventually_power_bound_below_linear hn hγ hA hC hd
  have hex : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      (perturbedEllipsoid r hr u ε).axesIn a b ∧
      (perturbedEllipsoid r hr v ε).axesIn a b ∧
      (∀ i, |(perturbedEllipsoid r hr u ε).semiaxis i - r| < δ) ∧
      (∀ i, |(perturbedEllipsoid r hr v ε).semiaxis i - r| < δ) ∧
      C * ((perturbedEllipsoid r hr u ε).volumeDistance
        (perturbedEllipsoid r hr v ε)) ^ γ <
        (perturbedEllipsoid r hr u ε).axisDistance (perturbedEllipsoid r hr v ε) := by
    filter_upwards [hvol, haxis, hpower, hU.filter_mono nhdsWithin_le_nhds,
      hV.filter_mono nhdsWithin_le_nhds] with ε hvol haxis hpower hU hV
    refine ⟨hU.1, hV.1, hU.2, hV.2, ?_⟩
    exact (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow ((perturbedEllipsoid r hr u ε).volumeDistance_nonneg hn _)
        hvol hγpos.le) hC.le).trans_lt (hpower.trans_le haxis)
  obtain ⟨ε, hε⟩ := hex.exists
  exact ⟨perturbedEllipsoid r hr u ε, perturbedEllipsoid r hr v ε, hε⟩

end EllipsoidVerification
