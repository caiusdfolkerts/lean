module

public import Ellipsoid.CoefficientLaurent

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace EllipsoidVerification

def coefficientIntegrand {n : ℕ} (e : Coefficients n) (k : ℕ) (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * t ^ (-(k : ℝ)) *
    (coefficientHead e k t * coefficientDerivative e t -
      coefficientHeadDerivative e k t * coefficientPolynomial e t) *
    coefficientPolynomial e t ^ (-(3 / 2 : ℝ))

theorem integrable_coefficientIntegrand {n k : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) (hk : 0 < k) (hkn : k < n) :
    IntegrableOn (coefficientIntegrand e k) (Ioi 0) := by
  have hU := admissible_mem_positiveCoefficientDomain he
  have hi (l j : Fin (n + 1)) : IntegrableOn (fun t : ℝ =>
      if l.val < k ∧ k ≤ j.val then ((j.val : ℝ) - l.val) * e l * e j *
        (t ^ (2 * (l.val : ℝ) + 2 * j.val - k - 1) *
          coefficientPolynomial e t ^ (-(3 / 2 : ℝ))) else 0) (Ioi 0) := by
    by_cases hc : l.val < k ∧ k ≤ j.val
    · simp only [hc, if_true]
      exact (integrable_coefficientMellinPower hU
        (cut_moment_range hk hkn hc.1 hc.2).1
        (by nlinarith [(cut_moment_range hk hkn hc.1 hc.2).2])).const_mul _
    · simp [hc]
  apply (integrable_finsetSum _ (fun l _ => integrable_finsetSum _ (fun j _ => hi l j))).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simpa only [coefficientIntegrand] using
    (coefficientTransform_integrand_expansion e k ht).symm

theorem coefficientIntegrand_nonneg {n k : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) {t : ℝ} (ht : 0 < t) :
    0 ≤ coefficientIntegrand e k t := by
  rw [coefficientIntegrand, coefficientTransform_integrand_expansion e k ht]
  apply Finset.sum_nonneg
  intro l hl
  apply Finset.sum_nonneg
  intro j hj
  split_ifs with h
  · have hlj : (l.val : ℝ) ≤ j.val := by exact_mod_cast h.1.le.trans h.2
    exact mul_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.mpr hlj) (he.1 l)) (he.1 j))
      (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.rpow_nonneg (coefficientPolynomial_pos he t).le _))
  · exact le_rfl

theorem coefficientHeadDerivative_eq_laurent {n : ℕ} (e : Coefficients n) (k : ℕ)
    {t : ℝ} (ht : 0 < t) :
    coefficientHeadDerivative e k t =
      (2 * (k : ℝ) * t ^ (2 * (k : ℝ) - 1)) * lowerLaurent e k t +
        t ^ (2 * (k : ℝ)) * lowerLaurentDerivative e k t := by
  have h := (Real.hasDerivAt_rpow_const (Or.inl ht.ne') :
    HasDerivAt (fun s : ℝ => s ^ (2 * (k : ℝ))) (2 * k * t ^ (2 * (k : ℝ) - 1)) t).mul
      (hasDerivAt_lowerLaurent e k ht)
  have h' : HasDerivAt (coefficientHead e k) _ t := h.congr_of_eventuallyEq (by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact coefficientHead_eq_scaled_lowerLaurent e k hs)
  exact (hasDerivAt_coefficientHead e k t).unique h'

theorem coefficientDerivative_eq_laurent {n : ℕ} (e : Coefficients n) (k : Fin (n + 1))
    {t : ℝ} (ht : 0 < t) :
    coefficientDerivative e t =
      (2 * (k.val : ℝ) * t ^ (2 * (k.val : ℝ) - 1)) *
        (lowerLaurent e k.val t + e k + upperLaurent e k.val t) +
      t ^ (2 * (k.val : ℝ)) *
        (lowerLaurentDerivative e k.val t + upperLaurentDerivative e k.val t) := by
  have h := (Real.hasDerivAt_rpow_const (Or.inl ht.ne') :
    HasDerivAt (fun s : ℝ => s ^ (2 * (k.val : ℝ)))
      (2 * k.val * t ^ (2 * (k.val : ℝ) - 1)) t).mul
      (((hasDerivAt_lowerLaurent e k.val ht).add_const (e k)).add
        (hasDerivAt_upperLaurent e k.val ht))
  have h' : HasDerivAt (coefficientPolynomial e) _ t := h.congr_of_eventuallyEq (by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact coefficientPolynomial_eq_scaled_laurent e k hs)
  exact (hasDerivAt_coefficientPolynomial e t).unique h'

theorem rpow_negative_three_halves {s : ℝ} (hs : 0 < s) :
    s ^ (-(3 / 2 : ℝ)) = (s * Real.sqrt s)⁻¹ := by
  have h : s * Real.sqrt s = s ^ (3 / 2 : ℝ) := by
    calc
      _ = s ^ (1 : ℝ) * s ^ (1 / 2 : ℝ) := by rw [Real.rpow_one, Real.sqrt_eq_rpow]
      _ = _ := by rw [← Real.rpow_add hs]; norm_num
  rw [h]
  exact Real.rpow_neg hs.le (3 / 2)

theorem coefficientIntegrand_eq_laurent {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) (k : Fin (n + 1))
    (hk : 0 < k.val) (hkn : k.val < n) {t : ℝ} (ht : 0 < t) :
    coefficientIntegrand e k.val t =
      (lowerLaurent e k.val t * upperLaurentDerivative e k.val t -
        (e k + upperLaurent e k.val t) * lowerLaurentDerivative e k.val t) /
      (2 * (lowerLaurent e k.val t + e k + upperLaurent e k.val t) *
        Real.sqrt (lowerLaurent e k.val t + e k + upperLaurent e k.val t)) := by
  let H := lowerLaurent e k.val t
  let U := upperLaurent e k.val t
  let HP := lowerLaurentDerivative e k.val t
  let UP := upperLaurentDerivative e k.val t
  let S := H + e k + U
  let T := t ^ (2 * (k.val : ℝ))
  let TP := 2 * (k.val : ℝ) * t ^ (2 * (k.val : ℝ) - 1)
  have hS : 0 < S := by
    have hh := lowerLaurent_pos he hk ht
    have hu := upperLaurent_pos he hkn ht
    have hc := he.1 k
    dsimp [S, H, U]
    linarith
  have hT : 0 < T := Real.rpow_pos_of_pos ht _
  have hw : (T * H) * (TP * S + T * (HP + UP)) -
      (TP * H + T * HP) * (T * S) = T ^ 2 * (H * UP - (e k + U) * HP) := by
    dsimp [S]
    ring
  have hp : t ^ (-(k.val : ℝ)) * T ^ 2 * T ^ (-(3 / 2 : ℝ)) = 1 := by
    dsimp [T]
    rw [← Real.rpow_mul_natCast ht.le, ← Real.rpow_mul ht.le,
      ← Real.rpow_add ht, ← Real.rpow_add ht]
    convert Real.rpow_zero t using 1 <;> ring
  rw [coefficientIntegrand, coefficientHead_eq_scaled_lowerLaurent e k.val ht,
    coefficientPolynomial_eq_scaled_laurent e k ht, coefficientDerivative_eq_laurent e k ht,
    coefficientHeadDerivative_eq_laurent e k.val ht]
  change (1 / 2 : ℝ) * t ^ (-(k.val : ℝ)) *
    ((T * H) * (TP * S + T * (HP + UP)) - (TP * H + T * HP) * (T * S)) *
      (T * S) ^ (-(3 / 2 : ℝ)) = _
  rw [hw, Real.mul_rpow hT.le hS.le]
  calc
    _ = (1 / 2 : ℝ) * (t ^ (-(k.val : ℝ)) * T ^ 2 * T ^ (-(3 / 2 : ℝ))) *
        (H * UP - (e k + U) * HP) * S ^ (-(3 / 2 : ℝ)) := by ring
    _ = _ := by
      rw [hp, rpow_negative_three_halves hS]
      dsimp [S, H, U, HP, UP]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

theorem hasDerivAt_coefficientBarrier {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) (k : Fin (n + 1))
    (hk : 0 < k.val) (hkn : k.val < n) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (barrierPrimitive (lowerLaurent e k.val) (upperLaurent e k.val) (e k))
      (coefficientIntegrand e k.val t -
        barrierRemainder (lowerLaurent e k.val) (upperLaurent e k.val)
          (upperLaurentDerivative e k.val) (e k) t) t := by
  rw [coefficientIntegrand_eq_laurent he k hk hkn ht]
  exact hasDerivAt_barrierPrimitive (hasDerivAt_lowerLaurent e k.val ht)
    (hasDerivAt_upperLaurent e k.val ht) (lowerLaurent_pos he hk ht)
    (add_pos_of_nonneg_of_pos (he.1 k) (upperLaurent_pos he hkn ht))

end EllipsoidVerification
