module

public import Ellipsoid.AffineRootPerturbation
public import Ellipsoid.LocalVolumeForward

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace EllipsoidVerification

/-- The harmless clamp makes the family a full ellipsoid for every real
parameter. It is inactive on a proved neighborhood of zero. -/
def perturbedAxes {n : ℕ} (r : ℝ) (u : Fin n → ℝ) (ε : ℝ) : Fin n → ℝ :=
  fun i => Real.sqrt (max (r ^ 2 / 2) (r ^ 2 + ε * u i))

theorem perturbedAxes_pos {n : ℕ} {r : ℝ} (hr : 0 < r) (u : Fin n → ℝ) (ε : ℝ) (i : Fin n) :
    0 < perturbedAxes r u ε i :=
  Real.sqrt_pos.mpr ((half_pos (sq_pos_of_pos hr)).trans_le (le_max_left _ _))

def perturbedEllipsoid {n : ℕ} (r : ℝ) (hr : 0 < r) (u : Fin n → ℝ) (ε : ℝ) :
    FullEllipsoid n where
  center := 0
  frame := LinearIsometryEquiv.refl ℝ (Space n)
  semiaxis := perturbedAxes r u ε
  semiaxis_pos := perturbedAxes_pos hr u ε

@[fun_prop] theorem continuous_perturbedAxes {n : ℕ} (r : ℝ) (u : Fin n → ℝ) :
    Continuous (perturbedAxes r u) := by
  apply continuous_pi
  intro i
  unfold perturbedAxes
  fun_prop

@[simp] theorem perturbedAxes_zero {n : ℕ} {r : ℝ} (hr : 0 < r) (u : Fin n → ℝ) :
    perturbedAxes r u 0 = fun _ => r := by
  have hhalf : r ^ 2 / 2 ≤ r ^ 2 := by nlinarith [sq_nonneg r]
  funext i
  simp only [perturbedAxes, zero_mul, add_zero, max_eq_right hhalf,
    Real.sqrt_sq_eq_abs, abs_of_pos hr]

theorem tendsto_perturbedAxes {n : ℕ} {r : ℝ} (hr : 0 < r) (u : Fin n → ℝ) :
    Tendsto (perturbedAxes r u) (𝓝 0) (𝓝 (fun _ => r)) := by
  simpa only [perturbedAxes_zero hr] using (continuous_perturbedAxes r u).tendsto 0

theorem eventually_perturbedAxes_sq {n : ℕ} {r : ℝ} (hr : 0 < r) (u : Fin n → ℝ) :
    ∀ᶠ ε : ℝ in 𝓝 0, ∀ i, perturbedAxes r u ε i ^ 2 = r ^ 2 + ε * u i := by
  apply Filter.eventually_all.mpr
  intro i
  have h := (show ContinuousAt (fun ε : ℝ => r ^ 2 + ε * u i) 0 by fun_prop).eventually
    (lt_mem_nhds (show r ^ 2 / 2 < r ^ 2 + 0 * u i by nlinarith [sq_pos_of_pos hr]))
  filter_upwards [h] with ε hε
  rw [perturbedAxes, max_eq_right hε.le, Real.sq_sqrt]
  exact (le_of_lt (half_pos (sq_pos_of_pos hr))).trans hε.le

theorem eventually_perturbedAxes_near {n : ℕ} {r a b δ : ℝ}
    (hr : 0 < r) (har : a < r) (hrb : r < b) (hδ : 0 < δ) (u : Fin n → ℝ) :
    ∀ᶠ ε : ℝ in 𝓝 0,
      (∀ i, a ≤ perturbedAxes r u ε i ∧ perturbedAxes r u ε i ≤ b) ∧
        (∀ i, |perturbedAxes r u ε i - r| < δ) := by
  have h (i : Fin n) := ((continuous_apply i).tendsto (fun _ : Fin n => r)).comp
    (tendsto_perturbedAxes hr u)
  have h1 : ∀ᶠ ε : ℝ in 𝓝 0, ∀ i, perturbedAxes r u ε i ∈ Ioo a b :=
    Filter.eventually_all.mpr fun i => (h i).eventually (Ioo_mem_nhds har hrb)
  have h2 : ∀ᶠ ε : ℝ in 𝓝 0, ∀ i, |perturbedAxes r u ε i - r| < δ :=
    Filter.eventually_all.mpr fun i => by
      have hh := (h i).eventually (Metric.ball_mem_nhds r hδ)
      simpa only [Metric.mem_ball, Real.dist_eq, Function.comp_apply] using hh
  exact h1.and h2 |>.mono fun ε hε => ⟨fun i => ⟨(hε.1 i).1.le, (hε.1 i).2.le⟩, hε.2⟩

theorem tendsto_perturbedAxisCoefficients {n : ℕ} {r : ℝ}
    (hr : 0 < r) (u : Fin n → ℝ) :
    Tendsto (fun ε => axisCoefficients (perturbedAxes r u ε)) (𝓝 0)
      (𝓝 (axisCoefficients (fun _ : Fin n => r))) :=
  (continuous_axisCoefficients n).continuousAt.tendsto.comp (tendsto_perturbedAxes hr u)

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
theorem eventually_perturbed_volume_bound {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r)
    {u v : Fin n → ℝ} {c : ℝ}
    (hpoly : realMonicRootPolynomial v = realMonicRootPolynomial u - Polynomial.C c) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ ε : ℝ in 𝓝[>] 0,
      (perturbedEllipsoid r hr u ε).volumeDistance (perturbedEllipsoid r hr v ε) ≤ A * ε ^ n := by
  obtain ⟨L, hL, U, hU, hLip⟩ := local_volume_forward_lipschitz hn
    (axisCoefficients_admissible (fun _ : Fin n => r) (fun _ => hr))
  refine ⟨L * |c| + 1, by positivity, ?_⟩
  have hEU := (tendsto_perturbedAxisCoefficients hr u).eventually hU
  have hFU := (tendsto_perturbedAxisCoefficients hr v).eventually hU
  filter_upwards [hEU.filter_mono nhdsWithin_le_nhds,
    hFU.filter_mono nhdsWithin_le_nhds,
    (eventually_perturbedAxes_sq hr u).filter_mono nhdsWithin_le_nhds,
    (eventually_perturbedAxes_sq hr v).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with ε hEU hFU hsqU hsqV hε
  have he : ‖axisCoefficients (perturbedAxes r u ε) -
      axisCoefficients (perturbedAxes r v ε)‖ ≤ |c| * ε ^ n :=
    axisCoefficient_difference_bound_affine (a := perturbedAxes r u ε)
      (b := perturbedAxes r v ε) (x := r ^ 2) hpoly hε hsqU hsqV
  have hgeom : (perturbedEllipsoid r hr u ε).volumeDistance
      (perturbedEllipsoid r hr v ε) ≤
        L * ‖axisCoefficients (perturbedAxes r u ε) -
          axisCoefficients (perturbedAxes r v ε)‖ :=
    hLip (perturbedEllipsoid r hr u ε) (perturbedEllipsoid r hr v ε) hEU hFU
  calc
    _ ≤ L * ‖axisCoefficients (perturbedAxes r u ε) - axisCoefficients (perturbedAxes r v ε)‖ :=
      hgeom
    _ ≤ L * (|c| * ε ^ n) := mul_le_mul_of_nonneg_left he hL.le
    _ ≤ (L * |c| + 1) * ε ^ n := by nlinarith [pow_nonneg hε.le n]

theorem finite_abs_uniform_positive {n : ℕ} (hn : 0 < n) {v : Fin n → ℝ}
    (hv : ∀ i, v i ≠ 0) : ∃ d : ℝ, 0 < d ∧ ∀ i, d ≤ |v i| := by
  letI : NeZero n := ⟨hn.ne'⟩
  let d := Finset.univ.inf' Finset.univ_nonempty (fun i : Fin n => |v i|)
  exact ⟨d, (Finset.lt_inf'_iff _).mpr (fun i _ => abs_pos.mpr (hv i)),
    fun i => Finset.inf'_le _ (Finset.mem_univ i)⟩

set_option backward.isDefEq.respectTransparency false in
theorem eventually_perturbed_axis_lower {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r)
    {u v : Fin n → ℝ} (hu : u ⟨0, hn⟩ = 0) (hv : ∀ i, v i ≠ 0) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ ε : ℝ in 𝓝[>] 0,
      d * ε ≤ (perturbedEllipsoid r hr u ε).axisDistance (perturbedEllipsoid r hr v ε) := by
  obtain ⟨d, hd, hdv⟩ := finite_abs_uniform_positive hn hv
  refine ⟨d / (4 * r), by positivity, ?_⟩
  have hU := eventually_perturbedAxes_near hr (a := 0) hr (b := 2 * r)
    (by linarith) (δ := 1) (by norm_num) u
  have hV := eventually_perturbedAxes_near hr (a := 0) hr (b := 2 * r)
    (by linarith) (δ := 1) (by norm_num) v
  filter_upwards [hU.filter_mono nhdsWithin_le_nhds, hV.filter_mono nhdsWithin_le_nhds,
    (eventually_perturbedAxes_sq hr u).filter_mono nhdsWithin_le_nhds,
    (eventually_perturbedAxes_sq hr v).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with ε hU hV hsU hsV hε
  apply le_ciInf
  intro σ
  apply le_trans _ (le_ciSup (Set.finite_range _).bddAbove (⟨0, hn⟩ : Fin n))
  let i : Fin n := ⟨0, hn⟩
  have hsq : |perturbedAxes r u ε i ^ 2 - perturbedAxes r v ε (σ i) ^ 2| = ε * |v (σ i)| := by
    rw [hsU i, hsV (σ i), hu, mul_zero, add_zero]
    ring_nf
    rw [abs_neg, abs_mul, abs_of_pos hε]
  have hfactor : |perturbedAxes r u ε i ^ 2 - perturbedAxes r v ε (σ i) ^ 2| =
      |perturbedAxes r u ε i - perturbedAxes r v ε (σ i)| *
        (perturbedAxes r u ε i + perturbedAxes r v ε (σ i)) := by
    rw [sq_sub_sq, abs_mul,
      abs_of_pos (add_pos (perturbedAxes_pos hr u ε i) (perturbedAxes_pos hr v ε (σ i))),
      mul_comm]
  have hsum : perturbedAxes r u ε i + perturbedAxes r v ε (σ i) ≤ 4 * r := by
    linarith [(hU.1 i).2, (hV.1 (σ i)).2]
  have hbase : d * ε ≤ |perturbedAxes r u ε i - perturbedAxes r v ε (σ i)| * (4 * r) := by
    calc
      _ ≤ ε * |v (σ i)| := by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hdv (σ i)) hε.le
      _ = _ := hsq.symm
      _ = _ := hfactor
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
  have h := (div_le_iff₀ (show 0 < 4 * r by positivity)).mpr hbase
  simpa only [div_mul_eq_mul_div, perturbedEllipsoid, i] using h

end EllipsoidVerification
