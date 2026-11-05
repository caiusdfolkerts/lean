module

public import Ellipsoid.VolumeNormalization
public import Ellipsoid.SharpHolderTheorem

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology

namespace EllipsoidVerification

theorem eventually_smooth_coefficient_pair_bound {n : ℕ} {r : ℝ} (hr : 0 < r)
    {u v : Fin n → ℝ} {c : ℝ}
    (hpoly : realMonicRootPolynomial v = realMonicRootPolynomial u - Polynomial.C c)
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {H : Coefficients n → Y}
    (hH : ContDiffAt ℝ 1 H (axisCoefficients (fun _ : Fin n => r))) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ‖H (axisCoefficients (perturbedAxes r u ε)) -
        H (axisCoefficients (perturbedAxes r v ε))‖ ≤ A * ε ^ n := by
  obtain ⟨L, U, hU, hLip⟩ := hH.exists_lipschitzOnWith
  refine ⟨(L : ℝ) * |c| + 1, by positivity, ?_⟩
  filter_upwards [((tendsto_perturbedAxisCoefficients hr u).eventually hU).filter_mono
      nhdsWithin_le_nhds,
    ((tendsto_perturbedAxisCoefficients hr v).eventually hU).filter_mono nhdsWithin_le_nhds,
    (eventually_perturbedAxes_sq hr u).filter_mono nhdsWithin_le_nhds,
    (eventually_perturbedAxes_sq hr v).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with ε hEU hFU hsU hsV hε
  have h := hLip.dist_le_mul _ hEU _ hFU
  rw [dist_eq_norm, dist_eq_norm] at h
  calc
    _ ≤ (L : ℝ) * ‖axisCoefficients (perturbedAxes r u ε) -
          axisCoefficients (perturbedAxes r v ε)‖ := h
    _ ≤ (L : ℝ) * (|c| * ε ^ n) := mul_le_mul_of_nonneg_left
      (axisCoefficient_difference_bound_affine hpoly hε hsU hsV) L.2
    _ ≤ ((L : ℝ) * |c| + 1) * ε ^ n := by nlinarith [pow_nonneg hε.le n]

theorem eventually_normalized_volume_bound {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r)
    {u v : Fin n → ℝ} {c : ℝ}
    (hpoly : realMonicRootPolynomial v = realMonicRootPolynomial u - Polynomial.C c) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ ε : ℝ in 𝓝[>] 0,
      (normalizedPerturbedEllipsoid r hr u ε).volumeDistance
        (normalizedPerturbedEllipsoid r hr v ε) ≤ A * ε ^ n := by
  let e := axisCoefficients (fun _ : Fin n => r)
  have he : coefficientAdmissible e := axisCoefficients_admissible _ (fun _ => hr)
  have hH : ContDiffAt ℝ 1
      (fun z => geometricCoefficientMap n (volumeNormalizedCoefficients n r z)) e := by
    have houter : ContDiffAt ℝ 1 (geometricCoefficientMap n)
        (volumeNormalizedCoefficients n r e) := by
      simpa only [e, volumeNormalizedCoefficients_sphere hn hr] using
        contDiffAt_geometricCoefficientMap he
    have hinner : ContDiffAt ℝ 1 (volumeNormalizedCoefficients n r) e :=
      contDiffAt_volumeNormalizedCoefficients (r := r) he.2.2
    simpa only [Function.comp_def] using houter.comp e hinner
  obtain ⟨A, hA, hbound⟩ := eventually_smooth_coefficient_pair_bound hr hpoly hH
  refine ⟨A, hA, hbound.mono fun ε hε => ?_⟩
  rw [← axisCoefficients_normalizedPerturbedAxes, ← axisCoefficients_normalizedPerturbedAxes]
    at hε
  change ‖geometricCoefficientMap n
      (axisCoefficients (normalizedPerturbedEllipsoid r hr u ε).semiaxis) -
    geometricCoefficientMap n
      (axisCoefficients (normalizedPerturbedEllipsoid r hr v ε).semiaxis)‖ ≤ A * ε ^ n at hε
  rw [geometricCoefficientMap_axisCoefficients (normalizedPerturbedEllipsoid r hr u ε),
    geometricCoefficientMap_axisCoefficients (normalizedPerturbedEllipsoid r hr v ε),
    ← FullEllipsoid.volumeDistance_eq_norm hn] at hε
  exact hε

theorem FullEllipsoid.scaled_axisDistance_lower {n : ℕ} (hn : 0 < n)
    (E F E' F' : FullEllipsoid n) {α β B : ℝ} (hα : 0 < α) (hB : 0 ≤ B)
    (hE' : ∀ i, E'.semiaxis i = α * E.semiaxis i)
    (hF' : ∀ i, F'.semiaxis i = β * F.semiaxis i)
    (hF : ∀ i, |F.semiaxis i| ≤ B) :
    α * E.axisDistance F - |α - β| * B ≤ E'.axisDistance F' := by
  apply le_ciInf
  intro σ
  let M := ⨆ i : Fin n, |E'.semiaxis i - F'.semiaxis (σ i)|
  have hM : 0 ≤ M :=
    (abs_nonneg (E'.semiaxis ⟨0, hn⟩ - F'.semiaxis (σ ⟨0, hn⟩))).trans
      (le_ciSup (f := fun i : Fin n => |E'.semiaxis i - F'.semiaxis (σ i)|)
        (Set.finite_range _).bddAbove (⟨0, hn⟩ : Fin n))
  have heach (i : Fin n) : α * |E.semiaxis i - F.semiaxis (σ i)| ≤ M + |α - β| * B := by
    calc
      _ = |(E'.semiaxis i - F'.semiaxis (σ i)) + (β - α) * F.semiaxis (σ i)| := by
        rw [hE', hF']
        have heq : (α * E.semiaxis i - β * F.semiaxis (σ i)) +
            (β - α) * F.semiaxis (σ i) = α * (E.semiaxis i - F.semiaxis (σ i)) := by ring
        rw [heq, abs_mul, abs_of_pos hα]
      _ ≤ |E'.semiaxis i - F'.semiaxis (σ i)| + |(β - α) * F.semiaxis (σ i)| := abs_add_le _ _
      _ ≤ M + |α - β| * B := by
        rw [abs_mul, abs_sub_comm β α]
        exact add_le_add
          (le_ciSup (f := fun j : Fin n => |E'.semiaxis j - F'.semiaxis (σ j)|)
            (Set.finite_range _).bddAbove i)
          (mul_le_mul_of_nonneg_left (hF (σ i)) (abs_nonneg _))
  have haxis : E.axisDistance F ≤ (M + |α - β| * B) / α :=
    E.axisDistance_le_of_perm F σ (by positivity) (fun i =>
      (le_div_iff₀ hα).mpr (by simpa only [mul_comm] using heach i))
  have h := (le_div_iff₀ hα).mp haxis
  change α * E.axisDistance F - |α - β| * B ≤ M
  linarith

theorem eventually_normalized_axis_lower {n : ℕ} (hn : 2 ≤ n) {r : ℝ} (hr : 0 < r)
    {u v : Fin n → ℝ} {c : ℝ}
    (hpoly : realMonicRootPolynomial v = realMonicRootPolynomial u - Polynomial.C c)
    (hu : u ⟨0, by omega⟩ = 0) (hv : ∀ i, v i ≠ 0) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ ε : ℝ in 𝓝[>] 0,
      d * ε ≤ (normalizedPerturbedEllipsoid r hr u ε).axisDistance
        (normalizedPerturbedEllipsoid r hr v ε) := by
  have hn0 : 0 < n := by omega
  obtain ⟨d, hd, haxis⟩ := eventually_perturbed_axis_lower hn0 hr hu hv
  obtain ⟨A, hA, hscale⟩ := eventually_smooth_coefficient_pair_bound hr hpoly
    (contDiffAt_coefficientVolumeScale (r := r)
      (axisCoefficients_admissible (fun _ : Fin n => r) (fun _ => hr)).2.2)
  have hhalf : ∀ᶠ ε : ℝ in 𝓝 0,
      1 / 2 < coefficientVolumeScale n r (axisCoefficients (perturbedAxes r u ε)) :=
    (tendsto_perturbedVolumeScale hn0 hr u).eventually (lt_mem_nhds (by norm_num))
  have hB := eventually_perturbedAxes_near hr hr (by linarith : r < 2 * r)
    (δ := 1) (by norm_num) v
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, 2 * r * A * ε ^ (n - 1) < d / 4 := by
    have hp : 0 < (n - 1 : ℕ) := by omega
    have ht : Tendsto (fun ε : ℝ => 2 * r * A * ε ^ (n - 1)) (𝓝[>] 0) (𝓝 0) := by
      have ht0 : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
        tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
      simpa only [zero_pow hp.ne', mul_zero] using
        (ht0.pow (n - 1)).const_mul (2 * r * A)
    exact ht.eventually (gt_mem_nhds (by positivity))
  refine ⟨d / 4, by positivity, ?_⟩
  filter_upwards [haxis, hscale, hhalf.filter_mono nhdsWithin_le_nhds,
    hB.filter_mono nhdsWithin_le_nhds, hsmall, self_mem_nhdsWithin]
    with ε haxis hscale hhalf hB hsmall hε
  let α := coefficientVolumeScale n r (axisCoefficients (perturbedAxes r u ε))
  let β := coefficientVolumeScale n r (axisCoefficients (perturbedAxes r v ε))
  have hα : 0 < α := by dsimp [α]; linarith
  have hdist := FullEllipsoid.scaled_axisDistance_lower hn0
    (perturbedEllipsoid r hr u ε) (perturbedEllipsoid r hr v ε)
    (normalizedPerturbedEllipsoid r hr u ε) (normalizedPerturbedEllipsoid r hr v ε)
    hα (show 0 ≤ 2 * r by positivity) (fun i => rfl) (fun i => rfl)
    (fun i => by
      change |perturbedAxes r v ε i| ≤ 2 * r
      rw [abs_of_pos (perturbedAxes_pos hr v ε i)]
      exact (hB.1 i).2)
  have hscale' : |α - β| ≤ A * ε ^ n := hscale
  have hnexp : ε ^ n = ε ^ (n - 1) * ε := by
    rw [← pow_succ, Nat.sub_add_cancel hn0]
  have herror : |α - β| * (2 * r) ≤ (d / 4) * ε := by
    have hmul := mul_lt_mul_of_pos_right hsmall hε
    rw [hnexp] at hscale'
    nlinarith [mul_le_mul_of_nonneg_right hscale' (show 0 ≤ 2 * r by positivity)]
  have hmain : (d / 2) * ε ≤ α *
      (perturbedEllipsoid r hr u ε).axisDistance (perturbedEllipsoid r hr v ε) := by
    have hmul := mul_le_mul_of_nonneg_left haxis hα.le
    have hh : (d / 2) * ε ≤ α * (d * ε) := by
      have hde : 0 ≤ d * ε := mul_nonneg hd.le hε.le
      dsimp [α] at hmul ⊢
      nlinarith
    exact hh.trans hmul
  linarith

end EllipsoidVerification
