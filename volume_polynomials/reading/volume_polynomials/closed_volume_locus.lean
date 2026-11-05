module
public import VolumePolynomials.BodyNormalization
public import VolumePolynomials.RealizationContinuity
public import Mathlib.Topology.Sequences

@[expose] public section

set_option autoImplicit false

/-!
# Closedness of the literal volume-polynomial realization locus

The argument includes zero-volume limits. Compactness is used for tuples with
normalized total volume, and geometric monotonicity controls the zero stratum.
No general mixed-volume or coefficient-positivity theorem is assumed.
-/

noncomputable section
open Set MeasureTheory Finset Metric Filter Topology
open scoped Pointwise BigOperators

namespace VolumePolynomials

theorem continuous_coefficientSum (n d : ℕ) :
    Continuous (fun c : Coefficients n d => ∑ α, c α) := by fun_prop

theorem normalized_mem_boundedLocus {d : ℕ} (hd : 0 < d) {R : ℝ}
    (hR : ∀ (n : ℕ) (K : Fin n → Body d) (c : Coefficients n d),
      Realizes K c → (∑ α, c α) = 1 →
      ∃ L : Fin n → Body d, Realizes L c ∧
        ∀ i, (0 : Space d) ∈ L i ∧ (L i : Set (Space d)) ⊆ closedBall 0 R)
    {n : ℕ} {c : Coefficients n d} (hc : c ∈ VolumeLocus n d)
    (hs : 0 < ∑ α, c α) :
    (∑ α, c α)⁻¹ • c ∈ boundedVolumeLocus n d (closedBall 0 R) := by
  first
  | have hmem := smul_mem_volumeLocus hd hc (inv_nonneg.mpr hs.le)
    obtain ⟨K, hK⟩ := hmem
    have hsum : ∑ α, ((∑ β, c β)⁻¹ • c) α = 1 := by
      simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, inv_mul_cancel₀ hs.ne']
    obtain ⟨L, hL, hbound⟩ := hR n K _ hK hsum
    exact ⟨L, hbound, hL⟩

/-- The realization locus for arbitrary compact convex bodies is closed in the
full finite-dimensional coefficient space, in every positive dimension. -/
theorem isClosed_volumeLocus (n d : ℕ) (hd : 0 < d) : IsClosed (VolumeLocus n d) := by
  first
  | obtain ⟨R, hRpos, hR⟩ := exists_uniform_normalization d hd
    have hcompact := isCompact_boundedVolumeLocus n d (isCompact_closedBall (0 : Space d) R)
    apply IsSeqClosed.isClosed
    intro u c hu huc
    have hsum : Tendsto (fun k => ∑ α, u k α) atTop (𝓝 (∑ α, c α)) :=
      (continuous_coefficientSum n d).continuousAt.tendsto.comp huc
    have hsum_nonneg : 0 ≤ ∑ α, c α := by
      apply le_of_tendsto_of_tendsto' tendsto_const_nhds hsum
      intro k
      obtain ⟨K, hK⟩ := hu k
      exact hK.sum_coefficients_nonneg
    by_cases hs0 : (∑ α, c α) = 0
    · have hc0 : c = 0 := by
        apply coefficients_eq_of_evaluate_nonneg
        intro t ht
        have heval : Tendsto (fun k => evaluate (u k) t) atTop (𝓝 (evaluate c t)) :=
          (continuous_evaluate t).continuousAt.tendsto.comp huc
        have hlow : 0 ≤ evaluate c t := by
          apply le_of_tendsto_of_tendsto' tendsto_const_nhds heval
          intro k
          obtain ⟨K, hK⟩ := hu k
          exact hK.evaluate_nonneg ht
        have hupp : evaluate c t ≤ (1 + ∑ i, t i) ^ d * ∑ α, c α := by
          apply le_of_tendsto_of_tendsto' heval (tendsto_const_nhds.mul hsum)
          intro k
          obtain ⟨K, hK⟩ := hu k
          exact hK.evaluate_le_sum t ht
        rw [hs0, mul_zero] at hupp
        simpa [evaluate] using le_antisymm hupp hlow
      rw [hc0]
      exact zero_mem_volumeLocus hd
    · have hspos : 0 < ∑ α, c α := lt_of_le_of_ne hsum_nonneg (Ne.symm hs0)
      have hevent : ∀ᶠ k in atTop, 0 < ∑ α, u k α := hsum.eventually_const_lt hspos
      have hnorm : Tendsto (fun k => (∑ α, u k α)⁻¹ • u k) atTop
          (𝓝 ((∑ α, c α)⁻¹ • c)) := (hsum.inv₀ hs0).smul huc
      have hnormalized : (∑ α, c α)⁻¹ • c ∈ boundedVolumeLocus n d (closedBall 0 R) := by
        apply hcompact.isClosed.mem_of_tendsto hnorm
        filter_upwards [hevent] with k hk
        exact normalized_mem_boundedLocus hd hR (hu k) hk
      have hmem := smul_mem_volumeLocus hd
        (boundedVolumeLocus_subset n d _ hnormalized) hspos.le
      simpa only [smul_smul, mul_inv_cancel₀ hs0, one_smul] using hmem

end VolumePolynomials
