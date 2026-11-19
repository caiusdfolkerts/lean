module
public import VolumePolynomials.BodyOperations
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# Scaling and zero-volume realizations

The zero-coefficient conclusion below is derived from actual geometric
monotonicity, without assuming coefficient nonnegativity or Minkowski's
polynomial-existence theorem.
-/

noncomputable section
open Set MeasureTheory Finset
open scoped Pointwise BigOperators NNReal

namespace VolumePolynomials

theorem evaluate_smul {n d : ℕ} (r : ℝ) (c : Coefficients n d) (t : Fin n → ℝ) :
    evaluate (r • c) t = r * evaluate c t := by
  simp [evaluate, Finset.mul_sum, mul_assoc]

theorem weightedSum_smul {n d : ℕ} (r : ℝ) (K : Fin n → Body d) (t : Fin n → ℝ) :
    weightedSum (fun i => r • K i) t = r • weightedSum K t := by
  simp [weightedSum, Finset.smul_sum, smul_smul, mul_comm]

theorem Realizes.dilate {n d : ℕ} {K : Fin n → Body d} {c : Coefficients n d}
    (h : Realizes K c) {r : ℝ} (hr : 0 ≤ r) :
    Realizes (fun i => r • K i) (r ^ d • c) := by
  intro t ht
  rw [evaluate_smul, h t ht]
  simp only [volumeFunction, weightedSum_smul, bodyVolume_smul _ hr]

theorem smul_mem_volumeLocus {n d : ℕ} (hd : 0 < d) {c : Coefficients n d}
    (hc : c ∈ VolumeLocus n d) {a : ℝ} (ha : 0 ≤ a) : a • c ∈ VolumeLocus n d := by
  obtain ⟨K, hK⟩ := hc
  have h := hK.dilate (Real.rpow_nonneg ha ((d : ℝ)⁻¹))
  rw [Real.rpow_inv_natCast_pow ha hd.ne'] at h
  exact ⟨_, h⟩

theorem bodyVolume_mono {d : ℕ} {K L : Body d} (h : K ≤ L) :
    bodyVolume K ≤ bodyVolume L :=
  ENNReal.toReal_mono L.isCompact.measure_lt_top.ne (measure_mono h)

theorem weightedSum_le_smul_of_zero_mem {n d : ℕ} (K : Fin n → Body d)
    (h0 : ∀ i, (0 : Space d) ∈ K i) (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i)
    {r : ℝ} (hr : 0 ≤ r) (htr : ∀ i, t i ≤ r) : weightedSum K t ≤ r • ∑ i, K i := by
  rw [Finset.smul_sum]
  apply sum_body_mono
  intro i
  change (⟨t i, ht i⟩ : ℝ≥0) • K i ≤ (⟨r, hr⟩ : ℝ≥0) • K i
  exact (K i).smul_le_of_le (h0 i) (htr i)

theorem volumeFunction_le_of_zero_mem {n d : ℕ} (K : Fin n → Body d)
    (h0 : ∀ i, (0 : Space d) ∈ K i) (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i)
    {r : ℝ} (hr : 0 ≤ r) (htr : ∀ i, t i ≤ r) :
    volumeFunction K t ≤ r ^ d * bodyVolume (∑ i, K i) := by
  calc
    volumeFunction K t ≤ bodyVolume (r • ∑ i, K i) :=
      bodyVolume_mono (weightedSum_le_smul_of_zero_mem K h0 t ht hr htr)
    _ = r ^ d * bodyVolume (∑ i, K i) := bodyVolume_smul _ hr

theorem volumeFunction_le {n d : ℕ} (K : Fin n → Body d)
    (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i) {r : ℝ} (hr : 0 ≤ r)
    (htr : ∀ i, t i ≤ r) :
    volumeFunction K t ≤ r ^ d * bodyVolume (∑ i, K i) := by
  choose p hp using fun i => (K i).nonempty
  let L : Fin n → Body d := fun i => translateBody (-p i) (K i)
  have h0 : ∀ i, (0 : Space d) ∈ L i := by
    intro i
    simpa [L, mem_translateBody] using hp i
  have h := volumeFunction_le_of_zero_mem L h0 t ht hr htr
  have hsum : bodyVolume (∑ i, L i) = bodyVolume (∑ i, K i) := by
    simpa only [volumeFunction, weightedSum_one] using
      volumeFunction_translate K (fun i => -p i) (fun _ => 1)
  rwa [hsum, volumeFunction_translate] at h

theorem Realizes.evaluate_le_sum {n d : ℕ} {K : Fin n → Body d}
    {c : Coefficients n d} (hc : Realizes K c) (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i) :
    evaluate c t ≤ (1 + ∑ i, t i) ^ d * ∑ α, c α := by
  rw [hc t ht, hc.sum_coefficients]
  apply volumeFunction_le K t ht
  · exact add_nonneg zero_le_one (Finset.sum_nonneg fun i _ => ht i)
  · intro i
    exact (Finset.single_le_sum (fun j _ => ht j) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)

/-- A realizing tuple of total volume zero realizes only the zero polynomial.
This includes all configurations whose total Minkowski sum is lower dimensional. -/
theorem Realizes.eq_zero_of_sum_eq_zero {n d : ℕ} {K : Fin n → Body d}
    {c : Coefficients n d} (hc : Realizes K c) (hzero : ∑ α, c α = 0) : c = 0 := by
  apply coefficients_eq_of_evaluate_nonneg
  intro t ht
  have hu := hc.evaluate_le_sum t ht
  rw [hzero, mul_zero] at hu
  have hl := hc.evaluate_nonneg ht
  simpa [evaluate] using le_antisymm hu hl

theorem zero_mem_volumeLocus {n d : ℕ} (hd : 0 < d) :
    (0 : Coefficients n d) ∈ VolumeLocus n d := by
  let : NeZero d := ⟨hd.ne'⟩
  refine ⟨fun _ => 0, fun t _ => ?_⟩
  simp [evaluate, volumeFunction, weightedSum, bodyVolume, Measure.real]
  change 0 = (volume {(0 : Space d)}).toReal
  simp

end VolumePolynomials
