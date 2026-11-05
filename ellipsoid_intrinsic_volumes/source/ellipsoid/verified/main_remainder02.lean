module

public import ellipsoid.verified.main_remainder01
public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

/- Generated ordinary proof stage. See audit/staged_ellipsoid_remainder/MainRemainder02/manifest.json. -/

@[expose] public section

section CanonicalSource8
/- Source: Ellipsoid/SharpnessSeeds.lean -/



noncomputable section

open Polynomial Set Filter
open scoped BigOperators Topology

namespace EllipsoidVerification

def realMonicRootPolynomial {n : ℕ} (u : Fin n → ℝ) : ℝ[X] :=
  ∏ i, (X - C (u i))

theorem realMonicRootPolynomial_isMonicOfDegree {n : ℕ} (u : Fin n → ℝ) :
    (realMonicRootPolynomial u).IsMonicOfDegree n := by
  refine ⟨?_, monic_prod_X_sub_C u Finset.univ⟩
  simp [realMonicRootPolynomial, natDegree_prod_of_monic, monic_X_sub_C]

theorem realMonicRootPolynomial_eval_root {n : ℕ} (u : Fin n → ℝ) (i : Fin n) :
    (realMonicRootPolynomial u).eval (u i) = 0 := by
  simp only [realMonicRootPolynomial, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)

theorem integerRootPolynomial_sign_change {n : ℕ} (i : Fin n) :
    (realMonicRootPolynomial (fun j : Fin n => (j.val : ℝ))).eval ((i.val : ℝ) - 1 / 4) *
      (realMonicRootPolynomial (fun j : Fin n => (j.val : ℝ))).eval ((i.val : ℝ) + 1 / 4) < 0 := by
  classical
  simp only [realMonicRootPolynomial, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, ← Finset.prod_mul_distrib]
  rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin n))
    (fun j => ((i.val : ℝ) - 1 / 4 - j.val) * (i.val + 1 / 4 - j.val))
      (Finset.mem_univ i)]
  apply mul_neg_of_neg_of_pos
  · ring_nf
    norm_num
  · apply Finset.prod_pos
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    have hneq : j.val ≠ i.val := fun h => hji (Fin.ext h)
    rcases lt_or_gt_of_ne hneq with hlt | hgt
    · have h : (j.val : ℝ) + 1 ≤ i.val := by exact_mod_cast Nat.succ_le_of_lt hlt
      apply mul_pos <;> linarith
    · have h : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast Nat.succ_le_of_lt hgt
      apply mul_pos_of_neg_of_neg <;> linarith

theorem exists_root_between_of_eval_mul_neg {p : ℝ[X]} {a b : ℝ}
    (hab : a < b) (hp : p.eval a * p.eval b < 0) :
    ∃ x ∈ Ioo a b, p.eval x = 0 := by
  rcases mul_neg_iff.mp hp with h | h
  · exact intermediate_value_Ioo' hab.le p.continuous.continuousOn ⟨h.2, h.1⟩
  · exact intermediate_value_Ioo hab.le p.continuous.continuousOn ⟨h.1, h.2⟩

/-- In every positive degree there are two distinct, completely real-rooted
monic polynomials differing only by a nonzero constant. This establishes the
sharpness seed by explicit disjoint sign-change intervals around integer roots.
It does not assume the openness of the real-rooted locus. -/
theorem exists_constant_perturbation_real_roots {n : ℕ} (hn : 0 < n) :
    ∃ (u v : Fin n → ℝ) (c : ℝ), 0 < c ∧
      u ⟨0, hn⟩ = 0 ∧ (∀ i, v i ≠ 0) ∧
      realMonicRootPolynomial v = realMonicRootPolynomial u - C c := by
  classical
  let u : Fin n → ℝ := fun i => i.val
  let p := realMonicRootPolynomial u
  have heach (i : Fin n) :
      ∀ᶠ c : ℝ in 𝓝 0,
        (p.eval ((i.val : ℝ) - 1 / 4) - c) * (p.eval ((i.val : ℝ) + 1 / 4) - c) < 0 := by
    have hc : ContinuousAt (fun c : ℝ =>
        (p.eval ((i.val : ℝ) - 1 / 4) - c) * (p.eval ((i.val : ℝ) + 1 / 4) - c)) 0 := by fun_prop
    exact hc.eventually (gt_mem_nhds (by
      simpa [p, u] using integerRootPolynomial_sign_change i))
  have hall : ∀ᶠ c : ℝ in 𝓝[>] 0, 0 < c ∧ ∀ i : Fin n,
      (p.eval ((i.val : ℝ) - 1 / 4) - c) * (p.eval ((i.val : ℝ) + 1 / 4) - c) < 0 := by
    have hpos : ∀ᶠ c : ℝ in 𝓝[>] 0, 0 < c := self_mem_nhdsWithin
    exact hpos.and ((Filter.eventually_all.mpr heach).filter_mono nhdsWithin_le_nhds)
  obtain ⟨c, hc, hsign⟩ := hall.exists
  have hex (i : Fin n) : ∃ x ∈ Ioo ((i.val : ℝ) - 1 / 4) (i.val + 1 / 4),
      (p - C c).eval x = 0 := by
    apply exists_root_between_of_eval_mul_neg (by linarith)
    simpa only [Polynomial.eval_sub, Polynomial.eval_C] using hsign i
  choose v hv hroot using hex
  have hv_inj : Function.Injective v := by
    intro i j heq
    apply Fin.ext
    by_contra hneq
    rcases lt_or_gt_of_ne hneq with hij | hji
    · have h : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast Nat.succ_le_of_lt hij
      have hi := (hv i).2
      have hj := (hv j).1
      linarith
    · have h : (j.val : ℝ) + 1 ≤ i.val := by exact_mod_cast Nat.succ_le_of_lt hji
      have hi := (hv i).1
      have hj := (hv j).2
      linarith
  have hq : (p - C c).IsMonicOfDegree n :=
    (realMonicRootPolynomial_isMonicOfDegree u).sub (by simpa using hn)
  have heq : realMonicRootPolynomial v = p - C c := by
    apply sub_eq_zero.mp
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hv_inj
    · intro i
      rw [Polynomial.eval_sub, realMonicRootPolynomial_eval_root, hroot, sub_self]
    · simpa only [Fintype.card_fin] using
        (realMonicRootPolynomial_isMonicOfDegree v).natDegree_sub_lt hn.ne' hq
  refine ⟨u, v, c, hc, by simp [u], ?_, heq⟩
  intro i hi
  have h := hroot i
  rw [hi, Polynomial.eval_sub, Polynomial.eval_C] at h
  have hp0 : p.eval 0 = 0 := by
    simpa only [p, u, Fin.val_mk, Nat.cast_zero] using
      realMonicRootPolynomial_eval_root u ⟨0, hn⟩
  rw [hp0, zero_sub, neg_eq_zero] at h
  exact hc.ne' h

end EllipsoidVerification
end
end CanonicalSource8

section CanonicalSource9
/- Source: Ellipsoid/AffineRootPerturbation.lean -/



noncomputable section

open Polynomial Set
open scoped BigOperators

namespace EllipsoidVerification

theorem realMonicRootPolynomial_affine {n : ℕ} (u : Fin n → ℝ) (x ε : ℝ) (hε : ε ≠ 0) :
    realMonicRootPolynomial (fun i => x + ε * u i) =
      C (ε ^ n) * (realMonicRootPolynomial u).comp (C ε⁻¹ * (X - C x)) := by
  rw [realMonicRootPolynomial, realMonicRootPolynomial, Polynomial.prod_comp,
    show C (ε ^ n) = ∏ _ : Fin n, C ε by simp,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  simp only [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]
  have hC : C ε * C ε⁻¹ = (1 : ℝ[X]) := by rw [← C_mul, mul_inv_cancel₀ hε, map_one]
  rw [mul_sub, ← mul_assoc, hC, one_mul, ← C_mul]
  simp only [C_add]
  ring

theorem realMonicRootPolynomial_affine_sub {n : ℕ} {u v : Fin n → ℝ} {c : ℝ}
    (h : realMonicRootPolynomial v = realMonicRootPolynomial u - C c)
    (x ε : ℝ) (hε : ε ≠ 0) :
    realMonicRootPolynomial (fun i => x + ε * u i) -
      realMonicRootPolynomial (fun i => x + ε * v i) = C (c * ε ^ n) := by
  rw [realMonicRootPolynomial_affine u x ε hε, realMonicRootPolynomial_affine v x ε hε,
    h, Polynomial.sub_comp, Polynomial.C_comp]
  ring_nf
  simp [← Polynomial.C_mul, mul_comm]

theorem realMonicRootPolynomial_coeff {n : ℕ} (d : Fin n → ℝ) {k : ℕ} (hk : k ≤ n) :
    (realMonicRootPolynomial d).coeff (n - k) = (-1 : ℝ) ^ k * elementaryOn Finset.univ d k := by
  have h := coeff_prod_X_add_C (Finset.univ : Finset (Fin n)) (fun i => -d i)
    (k := k) (by simpa using hk)
  simp only [Finset.card_univ, Fintype.card_fin, Polynomial.C_neg, ← sub_eq_add_neg] at h
  rw [realMonicRootPolynomial, h]
  simpa only [neg_one_mul] using elementaryOn_scaling Finset.univ d (-1) k

theorem axisCoefficient_difference_bound_of_rootPolynomial {n : ℕ} {a b : Fin n → ℝ}
    {c : ℝ} (h : realMonicRootPolynomial (fun i => a i ^ 2) -
      realMonicRootPolynomial (fun i => b i ^ 2) = C c) :
    ‖axisCoefficients a - axisCoefficients b‖ ≤ |c| := by
  apply (pi_norm_le_iff_of_nonneg (abs_nonneg c)).mpr
  intro k
  have hk : k.val ≤ n := by omega
  have hcoeff := congrArg (fun p : ℝ[X] => p.coeff (n - k.val)) h
  rw [Polynomial.coeff_sub, realMonicRootPolynomial_coeff _ hk,
    realMonicRootPolynomial_coeff _ hk, ← mul_sub, Polynomial.coeff_C] at hcoeff
  have habs := congrArg abs hcoeff
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] at habs
  change |elementaryOn Finset.univ (fun i => a i ^ 2) k.val -
    elementaryOn Finset.univ (fun i => b i ^ 2) k.val| ≤ |c|
  rw [habs]
  split_ifs <;> simp

theorem axisCoefficient_difference_bound_affine {n : ℕ} {u v a b : Fin n → ℝ} {c : ℝ}
    (h : realMonicRootPolynomial v = realMonicRootPolynomial u - C c)
    {x ε : ℝ} (hε : 0 < ε) (ha : ∀ i, a i ^ 2 = x + ε * u i)
    (hb : ∀ i, b i ^ 2 = x + ε * v i) :
    ‖axisCoefficients a - axisCoefficients b‖ ≤ |c| * ε ^ n := by
  have heq := realMonicRootPolynomial_affine_sub h x ε hε.ne'
  rw [← funext ha, ← funext hb] at heq
  simpa only [abs_mul, abs_pow, abs_of_pos hε] using
    axisCoefficient_difference_bound_of_rootPolynomial heq

end EllipsoidVerification
end
end CanonicalSource9

section CanonicalSource10
/- Source: Ellipsoid/LocalVolumeForward.lean -/



noncomputable section

open Set Filter
open scoped Topology BigOperators ContDiff

namespace EllipsoidVerification

def geometricCoefficientMap (n : ℕ) (e : Coefficients n) : Fin n → ℝ := fun k =>
  if k.val + 1 = n then unitBallVolume n * Real.sqrt (e (Fin.last n))
  else unitBallVolume (k.val + 1) * coefficientTransform e (k.val + 1)

theorem contDiffAt_geometricCoefficientMap {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) : ContDiffAt ℝ 1 (geometricCoefficientMap n) e := by
  apply contDiffAt_pi.mpr
  intro k
  unfold geometricCoefficientMap
  split_ifs with hk
  · exact contDiffAt_const.mul
      ((contDiff_apply ℝ (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).contDiffAt.sqrt he.2.2.ne')
  · have hU := (isOpen_positiveCoefficientDomain n).mem_nhds
      (admissible_mem_positiveCoefficientDomain he)
    have htransform : ContDiffAt ℝ ∞
        (fun e : Coefficients n => coefficientTransform e (k.val + 1)) e :=
      (contDiffOn_coefficientTransform (k := k.val + 1) (by omega) (by omega)).contDiffAt hU
    exact contDiffAt_const.mul (htransform.of_le (by simp))

theorem geometricCoefficientMap_axisCoefficients {n : ℕ} (E : FullEllipsoid n) :
    geometricCoefficientMap n (axisCoefficients E.semiaxis) =
      fun k : Fin n => E.volume (k.val + 1) := by
  funext k
  unfold geometricCoefficientMap
  split_ifs with hk
  · rw [hk, E.volume_top (by omega), axisCoefficients_last,
      Real.sqrt_sq_eq_abs, abs_of_pos (Finset.prod_pos fun i _ => E.semiaxis_pos i)]
  · exact (E.volume_eq_coefficientTransform (by omega) (by omega)).symm

theorem FullEllipsoid.volumeDistance_eq_norm {n : ℕ} (hn : 0 < n)
    (E F : FullEllipsoid n) : E.volumeDistance F =
      ‖(fun k : Fin n => E.volume (k.val + 1)) -
        (fun k : Fin n => F.volume (k.val + 1))‖ := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  apply le_antisymm
  · apply ciSup_le
    intro k
    change |E.volume (k.val + 1) - F.volume (k.val + 1)| ≤
      ‖fun j : Fin n => E.volume (j.val + 1) - F.volume (j.val + 1)‖
    simpa only [Real.norm_eq_abs] using
      (norm_le_pi_norm (fun j : Fin n => E.volume (j.val + 1) - F.volume (j.val + 1)) k)
  · apply (pi_norm_le_iff_of_nonneg (E.volumeDistance_nonneg hn F)).mpr
    exact fun k => E.volume_error_le F k

/-- Smoothness of the literal coefficient integral yields a local upper
Lipschitz bound for the actual geometric measurements. -/
theorem local_volume_forward_lipschitz {n : ℕ} (hn : 0 < n)
    {e : Coefficients n} (he : coefficientAdmissible e) :
    ∃ L : ℝ, 0 < L ∧ ∃ U ∈ 𝓝 e, ∀ E F : FullEllipsoid n,
      axisCoefficients E.semiaxis ∈ U → axisCoefficients F.semiaxis ∈ U →
      E.volumeDistance F ≤ L * ‖axisCoefficients E.semiaxis - axisCoefficients F.semiaxis‖ := by
  obtain ⟨L, U, hU, hLip⟩ := (contDiffAt_geometricCoefficientMap he).exists_lipschitzOnWith
  refine ⟨(L : ℝ) + 1, by positivity, U, hU, ?_⟩
  intro E F hE hF
  have h := hLip.dist_le_mul _ hE _ hF
  rw [dist_eq_norm, dist_eq_norm, geometricCoefficientMap_axisCoefficients,
    geometricCoefficientMap_axisCoefficients, ← E.volumeDistance_eq_norm hn F] at h
  exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))

end EllipsoidVerification
end
end CanonicalSource10

section CanonicalSource11
/- Source: Ellipsoid/SpherePerturbation.lean -/



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
end
end CanonicalSource11

section CanonicalSource12
/- Source: Ellipsoid/SharpHolderTheorem.lean -/



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
end
end CanonicalSource12

section CanonicalSource13
/- Source: Ellipsoid/VolumeNormalization.lean -/



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
end
end CanonicalSource13

section CanonicalSource14
/- Source: Ellipsoid/NormalizedPerturbationBounds.lean -/



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
end
end CanonicalSource14

section CanonicalSource15
/- Source: Ellipsoid/FixedVolumeSharpness.lean -/



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
end
end CanonicalSource15
