module

public import Ellipsoid.SpherePerturbation
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

@[expose] public section

noncomputable section

open Set Filter Polynomial
open scoped Topology BigOperators

namespace EllipsoidVerification

def coefficientVolumeScale (n : ℕ) (r : ℝ) (e : Coefficients n) : ℝ :=
  r * (e (Fin.last n)) ^ (-1 / (2 * n : ℝ))

def volumeNormalizedCoefficients (n : ℕ) (r : ℝ) (e : Coefficients n) : Coefficients n :=
  fun j => coefficientVolumeScale n r e ^ (2 * j.val) * e j

theorem contDiffAt_coefficientVolumeScale {n : ℕ} {r : ℝ} {e : Coefficients n}
    (he : 0 < e (Fin.last n)) : ContDiffAt ℝ 1 (coefficientVolumeScale n r) e :=
  contDiffAt_const.mul ((contDiff_apply ℝ (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).contDiffAt.rpow_const_of_ne he.ne')

theorem contDiffAt_volumeNormalizedCoefficients {n : ℕ} {r : ℝ} {e : Coefficients n}
    (he : 0 < e (Fin.last n)) : ContDiffAt ℝ 1 (volumeNormalizedCoefficients n r) e := by
  apply contDiffAt_pi.mpr
  intro j
  exact ((contDiffAt_coefficientVolumeScale he).pow (2 * j.val)).mul (contDiff_apply ℝ (fun _ : Fin (n + 1) => ℝ) j).contDiffAt

theorem coefficientVolumeScale_pos {n : ℕ} {r : ℝ} (hr : 0 < r) {e : Coefficients n}
    (he : 0 < e (Fin.last n)) : 0 < coefficientVolumeScale n r e :=
  mul_pos hr (Real.rpow_pos_of_pos he _)

theorem axisCoefficients_smul {n : ℕ} (s : ℝ) (a : Fin n → ℝ) :
    axisCoefficients (s • a) = fun j => s ^ (2 * j.val) * axisCoefficients a j := by
  funext j
  have h := elementaryOn_scaling Finset.univ (fun i => a i ^ 2) (s ^ 2) j.val
  simpa only [elementaryOn, axisCoefficients, axisCoefficientPolynomial,
    Pi.smul_apply, smul_eq_mul, mul_pow, pow_mul] using h

theorem coefficientVolumeScale_sphere {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) :
    coefficientVolumeScale n r (axisCoefficients (fun _ : Fin n => r)) = 1 := by
  rw [coefficientVolumeScale, axisCoefficients_last]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  rw [← Real.rpow_natCast_mul hr.le]
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hexp : ((n * 2 : ℕ) : ℝ) * (-1 / (2 * n : ℝ)) = -1 := by
    push_cast
    field_simp [hnR]
  rw [hexp, Real.rpow_neg_one, mul_inv_cancel₀ hr.ne']

theorem volumeNormalizedCoefficients_sphere {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) :
    volumeNormalizedCoefficients n r (axisCoefficients (fun _ : Fin n => r)) =
      axisCoefficients (fun _ : Fin n => r) := by
  funext j
  simp only [volumeNormalizedCoefficients, coefficientVolumeScale_sphere hn hr, one_pow, one_mul]

def normalizedPerturbedAxes {n : ℕ} (r : ℝ) (u : Fin n → ℝ) (ε : ℝ) : Fin n → ℝ :=
  coefficientVolumeScale n r (axisCoefficients (perturbedAxes r u ε)) • perturbedAxes r u ε

theorem normalizedPerturbedAxes_pos {n : ℕ} {r : ℝ} (hr : 0 < r)
    (u : Fin n → ℝ) (ε : ℝ) (i : Fin n) : 0 < normalizedPerturbedAxes r u ε i :=
  mul_pos (coefficientVolumeScale_pos hr (axisCoefficients_admissible _
    (perturbedAxes_pos hr u ε)).2.2) (perturbedAxes_pos hr u ε i)

def normalizedPerturbedEllipsoid {n : ℕ} (r : ℝ) (hr : 0 < r) (u : Fin n → ℝ) (ε : ℝ) :
    FullEllipsoid n where
  center := 0
  frame := LinearIsometryEquiv.refl ℝ (Space n)
  semiaxis := normalizedPerturbedAxes r u ε
  semiaxis_pos := normalizedPerturbedAxes_pos hr u ε

theorem axisCoefficients_normalizedPerturbedAxes {n : ℕ} (r : ℝ)
    (u : Fin n → ℝ) (ε : ℝ) :
    axisCoefficients (normalizedPerturbedAxes r u ε) =
      volumeNormalizedCoefficients n r (axisCoefficients (perturbedAxes r u ε)) :=
  axisCoefficients_smul _ _

theorem coefficientVolumeScale_product {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r)
    {a : Fin n → ℝ} (ha : ∀ i, 0 < a i) :
    (coefficientVolumeScale n r (axisCoefficients a)) ^ n * ∏ i, a i = r ^ n := by
  let P := ∏ i, a i
  have hP : 0 < P := Finset.prod_pos fun i _ => ha i
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [coefficientVolumeScale, axisCoefficients_last, mul_pow,
    ← Real.rpow_mul_natCast (sq_nonneg P), ← Real.rpow_natCast_mul hP.le]
  have hexp : (2 : ℝ) * ((-1 / (2 * n : ℝ)) * n) = -1 := by field_simp [hnR]
  norm_num only [Nat.cast_ofNat]
  rw [hexp, Real.rpow_neg_one]
  dsimp [P] at hP ⊢
  field_simp [hP.ne']

theorem normalizedPerturbedEllipsoid_volume_top {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r)
    (u : Fin n → ℝ) (ε : ℝ) :
    (normalizedPerturbedEllipsoid r hr u ε).volume n = unitBallVolume n * r ^ n := by
  rw [FullEllipsoid.volume_top hn]
  change unitBallVolume n * (∏ i, coefficientVolumeScale n r
    (axisCoefficients (perturbedAxes r u ε)) * perturbedAxes r u ε i) = _
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [coefficientVolumeScale_product hn hr (perturbedAxes_pos hr u ε)]

theorem tendsto_perturbedVolumeScale {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r)
    (u : Fin n → ℝ) :
    Tendsto (fun ε => coefficientVolumeScale n r (axisCoefficients (perturbedAxes r u ε)))
      (𝓝 0) (𝓝 1) := by
  have h := ((contDiffAt_coefficientVolumeScale (r := r)
    (axisCoefficients_admissible (fun _ : Fin n => r) (fun _ => hr)).2.2).continuousAt.tendsto).comp
      (tendsto_perturbedAxisCoefficients hr u)
  simpa only [coefficientVolumeScale_sphere hn hr, Function.comp_def] using h

theorem tendsto_normalizedPerturbedAxes {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r)
    (u : Fin n → ℝ) : Tendsto (normalizedPerturbedAxes r u) (𝓝 0) (𝓝 (fun _ => r)) := by
  change Tendsto (fun ε => coefficientVolumeScale n r
    (axisCoefficients (perturbedAxes r u ε)) • perturbedAxes r u ε)
    (𝓝 0) (𝓝 (fun _ : Fin n => r))
  simpa only [one_smul] using
    (tendsto_perturbedVolumeScale hn hr u).smul (tendsto_perturbedAxes hr u)

theorem eventually_normalizedPerturbedAxes_near {n : ℕ} (hn : 0 < n) {r a b δ : ℝ}
    (hr : 0 < r) (har : a < r) (hrb : r < b) (hδ : 0 < δ) (u : Fin n → ℝ) :
    ∀ᶠ ε : ℝ in 𝓝 0,
      (∀ i, a ≤ normalizedPerturbedAxes r u ε i ∧ normalizedPerturbedAxes r u ε i ≤ b) ∧
        (∀ i, |normalizedPerturbedAxes r u ε i - r| < δ) := by
  have h (i : Fin n) := ((continuous_apply i).tendsto (fun _ : Fin n => r)).comp
    (tendsto_normalizedPerturbedAxes hn hr u)
  have h1 : ∀ᶠ ε : ℝ in 𝓝 0, ∀ i, normalizedPerturbedAxes r u ε i ∈ Ioo a b :=
    Filter.eventually_all.mpr fun i => (h i).eventually (Ioo_mem_nhds har hrb)
  have h2 : ∀ᶠ ε : ℝ in 𝓝 0, ∀ i, |normalizedPerturbedAxes r u ε i - r| < δ :=
    Filter.eventually_all.mpr fun i => by
      have hh := (h i).eventually (Metric.ball_mem_nhds r hδ)
      simpa only [Metric.mem_ball, Real.dist_eq, Function.comp_apply] using hh
  exact h1.and h2 |>.mono fun ε hε => ⟨fun i => ⟨(hε.1 i).1.le, (hε.1 i).2.le⟩, hε.2⟩

end EllipsoidVerification
