module

public import Ellipsoid.NormalizedPerturbationBounds

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology

namespace EllipsoidVerification

/-- The equal-volume sharpness clause. Both constructed ellipsoids have
exactly the volume of the prescribed sphere, while the discrepancy of all
intrinsic volumes still vanishes to order `n`. -/
theorem sharp_holder_recovery_at_fixed_volume : SharpHolderRecoveryAtFixedVolume := by
  intro n hn a b r ha har hrb γ hγ δ C hδ hC
  have hn0 : 0 < n := by omega
  have hr : 0 < r := ha.trans har
  have hγpos : 0 < γ := (one_div_pos.mpr (by exact_mod_cast hn0)).trans hγ
  obtain ⟨u, v, c, hc, hu, hv, hpoly⟩ := exists_constant_perturbation_real_roots hn0
  obtain ⟨A, hA, hvol⟩ := eventually_normalized_volume_bound hn0 hr hpoly
  obtain ⟨d, hd, haxis⟩ := eventually_normalized_axis_lower hn hr hpoly hu hv
  have hU := eventually_normalizedPerturbedAxes_near hn0 hr har hrb hδ u
  have hV := eventually_normalizedPerturbedAxes_near hn0 hr har hrb hδ v
  have hpower := eventually_power_bound_below_linear hn0 hγ hA hC hd
  have hex : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      (normalizedPerturbedEllipsoid r hr u ε).axesIn a b ∧
      (normalizedPerturbedEllipsoid r hr v ε).axesIn a b ∧
      (∀ i, |(normalizedPerturbedEllipsoid r hr u ε).semiaxis i - r| < δ) ∧
      (∀ i, |(normalizedPerturbedEllipsoid r hr v ε).semiaxis i - r| < δ) ∧
      (normalizedPerturbedEllipsoid r hr u ε).volume n =
        (normalizedPerturbedEllipsoid r hr v ε).volume n ∧
      C * ((normalizedPerturbedEllipsoid r hr u ε).volumeDistance
        (normalizedPerturbedEllipsoid r hr v ε)) ^ γ <
        (normalizedPerturbedEllipsoid r hr u ε).axisDistance (normalizedPerturbedEllipsoid r hr v ε) := by
    filter_upwards [hvol, haxis, hpower, hU.filter_mono nhdsWithin_le_nhds,
      hV.filter_mono nhdsWithin_le_nhds] with ε hvol haxis hpower hU hV
    refine ⟨hU.1, hV.1, hU.2, hV.2, ?_, ?_⟩
    · rw [normalizedPerturbedEllipsoid_volume_top hn0 hr u,
        normalizedPerturbedEllipsoid_volume_top hn0 hr v]
    · exact (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow ((normalizedPerturbedEllipsoid r hr u ε).volumeDistance_nonneg hn0 _)
          hvol hγpos.le) hC.le).trans_lt (hpower.trans_le haxis)
  obtain ⟨ε, hε⟩ := hex.exists
  exact ⟨normalizedPerturbedEllipsoid r hr u ε, normalizedPerturbedEllipsoid r hr v ε, hε⟩

end EllipsoidVerification
