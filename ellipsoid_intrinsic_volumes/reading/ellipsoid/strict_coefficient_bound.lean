module

public import Ellipsoid.CoefficientBarrier

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace EllipsoidVerification

def tailHalfLaurent {n : ℕ} (e : Coefficients n) (k : ℕ) (t : ℝ) : ℝ :=
  ∑ j : Fin (n + 1), if k ≤ j.val then e j * t ^ (2 * (j.val : ℝ) - k) else 0

theorem tailHalfLaurent_eq {n : ℕ} (e : Coefficients n) (k : Fin (n + 1))
    {t : ℝ} (ht : 0 < t) :
    tailHalfLaurent e k.val t = t ^ (k.val : ℝ) * (e k + upperLaurent e k.val t) := by
  have hsplit : e k + upperLaurent e k.val t =
      ∑ j : Fin (n + 1), if k.val ≤ j.val then
        e j * t ^ (2 * (j.val : ℝ) - 2 * k.val) else 0 := by
    rw [upperLaurent, ← Fintype.sum_ite_eq' k e,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hjk : j = k
    · subst j
      simp
    · have hval : j.val ≠ k.val := fun h => hjk (Fin.ext h)
      rcases lt_or_gt_of_ne hval with h | h
      · simp [hjk, not_le.mpr h, not_lt.mpr h.le]
      · simp [hjk, h, h.le]
  rw [tailHalfLaurent, hsplit, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs
  · rw [mul_left_comm, ← Real.rpow_add ht]
    congr 2
    ring
  · simp

theorem tailHalfLaurent_tendsto_zero {n k : ℕ} (e : Coefficients n) (hk : 0 < k) :
    Tendsto (tailHalfLaurent e k) (𝓝[>] 0) (𝓝 0) := by
  have ht0 : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have h (j : Fin (n + 1)) : Tendsto
      (fun t : ℝ => if k ≤ j.val then e j * t ^ (2 * (j.val : ℝ) - k) else 0)
      (𝓝[>] 0) (𝓝 0) := by
    by_cases hj : k ≤ j.val
    · have hjR : (k : ℝ) ≤ j.val := by exact_mod_cast hj
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      have hp := (ht0.rpow_const_nhds_zero
        (show 0 < 2 * (j.val : ℝ) - k by linarith)).const_mul (e j)
      simpa only [hj, if_true, mul_zero] using hp
    · simp only [hj, if_false]
      exact tendsto_const_nhds
  change Tendsto (fun t : ℝ => ∑ j : Fin (n + 1),
    if k ≤ j.val then e j * t ^ (2 * (j.val : ℝ) - k) else 0)
      (𝓝[>] 0) (𝓝 0)
  simpa only [Finset.sum_const_zero] using
    tendsto_finsetSum Finset.univ (fun j _ => h j)

theorem coefficientBarrier_first_term {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) (k : Fin (n + 1))
    (hk : 0 < k.val) (hkn : k.val < n) {t : ℝ} (ht : 0 < t) :
    (e k + upperLaurent e k.val t) /
        Real.sqrt (lowerLaurent e k.val t + e k + upperLaurent e k.val t) =
      tailHalfLaurent e k.val t / Real.sqrt (coefficientPolynomial e t) := by
  have hS : 0 < lowerLaurent e k.val t + e k + upperLaurent e k.val t := by
    have hh := lowerLaurent_pos he hk ht
    have hu := upperLaurent_pos he hkn ht
    have hc := he.1 k
    linarith
  have hsqrt : Real.sqrt (coefficientPolynomial e t) = t ^ (k.val : ℝ) *
      Real.sqrt (lowerLaurent e k.val t + e k + upperLaurent e k.val t) := by
    rw [coefficientPolynomial_eq_scaled_laurent e k ht,
      Real.sqrt_mul (Real.rpow_nonneg ht.le _), Real.sqrt_eq_rpow,
      ← Real.rpow_mul ht.le]
    congr 2
    ring
  rw [hsqrt, tailHalfLaurent_eq e k ht]
  field_simp [(Real.rpow_pos_of_pos ht (k.val : ℝ)).ne', (Real.sqrt_pos.mpr hS).ne']

@[simp] theorem coefficientPolynomial_zero {n : ℕ} (e : Coefficients n) :
    coefficientPolynomial e 0 = e 0 := by
  classical
  unfold coefficientPolynomial
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j hj hj0
    have hpos : 0 < 2 * j.val := by
      have hjv : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
      omega
    simp [hpos.ne']
  · simp

theorem coefficientBarrier_tendsto_zero {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) (k : Fin (n + 1))
    (hk : 0 < k.val) (hkn : k.val < n) :
    Tendsto (barrierPrimitive (lowerLaurent e k.val) (upperLaurent e k.val) (e k))
      (𝓝[>] 0) (𝓝 (-Real.sqrt (e k))) := by
  have hQ : Tendsto (fun t => Real.sqrt (coefficientPolynomial e t)) (𝓝[>] 0)
      (𝓝 (Real.sqrt (e 0))) := by
    have hQ0 : Tendsto (coefficientPolynomial e) (𝓝[>] (0 : ℝ))
        (𝓝 (coefficientPolynomial e 0)) :=
      tendsto_nhdsWithin_of_tendsto_nhds (continuous_coefficientPolynomial e).continuousAt
    simpa only [coefficientPolynomial_zero] using
      hQ0.sqrt
  have hB := (tailHalfLaurent_tendsto_zero e hk).div hQ (Real.sqrt_pos.mpr he.2.1).ne'
  have hU := (upperLaurent_tendsto_zero e k.val).const_add (e k) |>.sqrt
  have hlim := hB.sub hU
  simp only [zero_div, add_zero, zero_sub] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [barrierPrimitive, coefficientBarrier_first_term he k hk hkn ht]
  simp only [Pi.div_apply]

theorem coefficientBarrier_tendsto_atTop {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) (k : Fin (n + 1))
    (hk : 0 < k.val) (hkn : k.val < n) :
    Tendsto (barrierPrimitive (lowerLaurent e k.val) (upperLaurent e k.val) (e k))
      atTop (𝓝 0) := by
  apply squeeze_zero_norm'
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    simpa only [Real.norm_eq_abs] using
      abs_barrierPrimitive_le_sqrt (lowerLaurent_pos he hk ht).le
        (add_pos_of_nonneg_of_pos (he.1 k) (upperLaurent_pos he hkn ht))
  · simpa only [Real.sqrt_zero] using (lowerLaurent_tendsto_atTop e k.val).sqrt

theorem continuousOn_coefficientRemainder {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) (k : Fin (n + 1))
    (hk : 0 < k.val) (hkn : k.val < n) :
    ContinuousOn (barrierRemainder (lowerLaurent e k.val) (upperLaurent e k.val)
      (upperLaurentDerivative e k.val) (e k)) (Ioi 0) := by
  intro t ht
  apply ContinuousAt.continuousWithinAt
  have hh := (hasDerivAt_lowerLaurent e k.val ht).continuousAt
  have hu := (hasDerivAt_upperLaurent e k.val ht).continuousAt
  have hup := continuousAt_upperLaurentDerivative e k.val ht
  have hb := add_pos_of_nonneg_of_pos (he.1 k) (upperLaurent_pos he hkn ht)
  have hS : 0 < lowerLaurent e k.val t + e k + upperLaurent e k.val t := by
    have h := lowerLaurent_pos he hk ht
    linarith
  have hcont := (hup.div_const 2).mul
    (((hu.const_add (e k)).sqrt.inv₀ (Real.sqrt_pos.mpr hb).ne').sub
      ((((hh.add_const (e k)).add hu).sqrt).inv₀ (Real.sqrt_pos.mpr hS).ne'))
  apply hcont.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun _ => by
    simp only [barrierRemainder, Pi.mul_apply, Pi.sub_apply, Pi.inv_apply, Pi.add_apply]

/-- The strict coefficient estimate of Theorem 2.1, including `e_k = 0`.
All endpoint limits and the positive improper remainder are proved above. -/
theorem coefficientTransform_gt_sqrt {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) (k : Fin (n + 1))
    (hk : 0 < k.val) (hkn : k.val < n) :
    Real.sqrt (e k) < coefficientTransform e k.val := by
  exact integral_gt_of_positive_remainder
    (integrable_coefficientIntegrand he hk hkn)
    (fun t ht => coefficientIntegrand_nonneg he ht)
    (continuousOn_coefficientRemainder he k hk hkn)
    (fun t ht => barrierRemainder_pos (lowerLaurent_pos he hk ht)
      (add_pos_of_nonneg_of_pos (he.1 k) (upperLaurent_pos he hkn ht))
      (upperLaurentDerivative_pos he hkn ht))
    (fun t ht => hasDerivAt_coefficientBarrier he k hk hkn ht)
    (coefficientBarrier_tendsto_zero he k hk hkn)
    (coefficientBarrier_tendsto_atTop he k hk hkn)

theorem coefficientTransform_coefficient_lt_sq {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) (k : Fin (n + 1))
    (hk : 0 < k.val) (hkn : k.val < n) :
    e k < (coefficientTransform e k.val) ^ 2 := by
  have h := coefficientTransform_gt_sqrt he k hk hkn
  have hs := Real.sq_sqrt (he.1 k)
  have hp : 0 < coefficientTransform e k.val := (Real.sqrt_nonneg _).trans_lt h
  nlinarith [Real.sqrt_nonneg (e k)]

end EllipsoidVerification
