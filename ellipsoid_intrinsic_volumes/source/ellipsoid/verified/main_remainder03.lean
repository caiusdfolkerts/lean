module

public import ellipsoid.verified.main_remainder02

/- Generated ordinary proof stage. See audit/staged_ellipsoid_remainder/MainRemainder03/manifest.json. -/

@[expose] public section

section CanonicalSource16
/- Source: Ellipsoid/PositiveRemainder.lean -/



noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace EllipsoidVerification

/-- A positive remainder in an improper integration-by-parts formula gives
a strict lower bound. Only finite-interval integrability of the remainder is
required; its improper integrability is a consequence, not an assumption. -/
theorem integral_gt_of_positive_remainder {f G R : ℝ → ℝ} {b : ℝ}
    (hf : IntegrableOn f (Ioi 0)) (hf0 : ∀ t > 0, 0 ≤ f t)
    (hR : ContinuousOn R (Ioi 0)) (hRpos : ∀ t > 0, 0 < R t)
    (hG : ∀ t > 0, HasDerivAt G (f t - R t) t)
    (hG0 : Tendsto G (𝓝[>] 0) (𝓝 (-b)))
    (hGtop : Tendsto G atTop (𝓝 0)) : b < ∫ t in Ioi (0 : ℝ), f t := by
  let δ := ∫ t in (1 : ℝ)..2, R t
  have hδ : 0 < δ := intervalIntegral.integral_pos (by norm_num)
    (hR.mono (by intro t ht; exact lt_of_lt_of_le zero_lt_one ht.1))
    (fun t ht => (hRpos t (zero_lt_one.trans ht.1)).le)
    ⟨1, by norm_num, hRpos 1 zero_lt_one⟩
  have hbound {s t : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (ht2 : 2 ≤ t) :
      G t - G s + δ ≤ ∫ u in Ioi (0 : ℝ), f u := by
    have hst : s ≤ t := by linarith
    have hsub : Icc s t ⊆ Ioi (0 : ℝ) := fun u hu => hs.trans_le hu.1
    have hfi : IntervalIntegrable f volume s t :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hst).mpr (hf.mono_set hsub)
    have hRi : IntervalIntegrable R volume s t :=
      (show ContinuousOn R (uIcc s t) by
        simpa only [uIcc_of_le hst] using hR.mono hsub).intervalIntegrable
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u hu => hG u (hsub (by simpa only [uIcc_of_le hst] using hu))) (hfi.sub hRi)
    rw [intervalIntegral.integral_sub hfi hRi] at hFTC
    have hRle : δ ≤ ∫ u in s..t, R u :=
      intervalIntegral.integral_mono_interval hs1 (by norm_num) ht2
        ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun u hu =>
          (hRpos u (hs.trans hu.1)).le)) hRi
    have hfle : (∫ u in s..t, f u) ≤ ∫ u in Ioi (0 : ℝ), f u := by
      rw [intervalIntegral.integral_of_le hst]
      exact setIntegral_mono_set hf
        ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ hf0))
        (show Ioc s t ⊆ Ioi (0 : ℝ) from fun u hu => hs.trans hu.1).eventuallySubset
    linarith
  have ht : Tendsto (fun s : ℝ => G s⁻¹ - G s + δ) (𝓝[>] 0) (𝓝 (b + δ)) := by
    have hlimit := ((hGtop.comp tendsto_inv_nhdsGT_zero).sub hG0).add_const δ
    change Tendsto (fun s : ℝ => G s⁻¹ - G s + δ) (𝓝[>] 0)
      (𝓝 (0 - (-b) + δ)) at hlimit
    simpa only [zero_sub, neg_neg] using hlimit
  have hevent : ∀ᶠ s : ℝ in 𝓝[>] 0,
      G s⁻¹ - G s + δ ≤ ∫ u in Ioi (0 : ℝ), f u := by
    filter_upwards [(self_mem_nhdsWithin : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s),
      (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)).filter_mono
        nhdsWithin_le_nhds] with s hs hs2
    apply hbound hs (by linarith)
    simpa only [one_div] using
      (le_div_iff₀ hs).mpr (show (2 : ℝ) * s ≤ 1 by linarith)
  exact (lt_add_of_pos_right b hδ).trans_le (le_of_tendsto ht hevent)

def barrierPrimitive (h u : ℝ → ℝ) (c t : ℝ) : ℝ :=
  (c + u t) / Real.sqrt (h t + c + u t) - Real.sqrt (c + u t)

def barrierRemainder (h u up : ℝ → ℝ) (c t : ℝ) : ℝ :=
  (up t / 2) * ((Real.sqrt (c + u t))⁻¹ - (Real.sqrt (h t + c + u t))⁻¹)

theorem barrierRemainder_pos {h u up : ℝ → ℝ} {c t : ℝ}
    (hh : 0 < h t) (hb : 0 < c + u t) (hup : 0 < up t) :
    0 < barrierRemainder h u up c t := by
  apply mul_pos (half_pos hup)
  apply sub_pos.mpr
  exact (inv_lt_inv₀ (Real.sqrt_pos.mpr (by linarith)) (Real.sqrt_pos.mpr hb)).mpr
    (Real.sqrt_lt_sqrt hb.le (by linarith))

theorem hasDerivAt_barrierPrimitive {h u : ℝ → ℝ} {c t hp up : ℝ}
    (hh : HasDerivAt h hp t) (hu : HasDerivAt u up t)
    (hh0 : 0 < h t) (hb : 0 < c + u t) :
    HasDerivAt (barrierPrimitive h u c)
      ((h t * up - (c + u t) * hp) /
          (2 * (h t + c + u t) * Real.sqrt (h t + c + u t)) -
        (up / 2) * ((Real.sqrt (c + u t))⁻¹ - (Real.sqrt (h t + c + u t))⁻¹)) t := by
  have hS : 0 < h t + c + u t := by linarith
  have hsum := (hh.add_const c).add hu
  have hbase := (hu.const_add c).div (hsum.sqrt hS.ne') (Real.sqrt_pos.mpr hS).ne'
  have hder := hbase.sub ((hu.const_add c).sqrt hb.ne')
  convert hder using 1
  · rfl
  · let a := Real.sqrt (h t + c + u t)
    let b := Real.sqrt (c + u t)
    have ha : a ≠ 0 := (Real.sqrt_pos.mpr hS).ne'
    have hb' : b ≠ 0 := (Real.sqrt_pos.mpr hb).ne'
    have hs : a ^ 2 = h t + c + u t := Real.sq_sqrt hS.le
    change (h t * up - (c + u t) * hp) /
        (2 * (h t + c + u t) * a) - (up / 2) * (b⁻¹ - a⁻¹) =
      (up * a - (c + u t) * ((hp + up) / (2 * a))) / a ^ 2 - up / (2 * b)
    rw [← hs]
    have hh' : h t = a ^ 2 - (c + u t) := by linarith
    rw [hh']
    field_simp [ha, hb']
    ring

/-- This elementary estimate controls the upper boundary without subtracting
two uncontrolled divergent quantities. -/
theorem abs_barrierPrimitive_le_sqrt {h u : ℝ → ℝ} {c t : ℝ}
    (hh : 0 ≤ h t) (hb : 0 < c + u t) :
    |barrierPrimitive h u c t| ≤ Real.sqrt (h t) := by
  let a := Real.sqrt (h t + c + u t)
  let b := Real.sqrt (c + u t)
  have ha : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have hb0 : 0 < b := Real.sqrt_pos.mpr hb
  have hba : b ≤ a := Real.sqrt_le_sqrt (by linarith)
  have hb2 : b ^ 2 = c + u t := Real.sq_sqrt hb.le
  have hdiff : a - b ≤ Real.sqrt (h t) := by
    have ha2 : a ^ 2 = h t + c + u t := Real.sq_sqrt (by linarith)
    have hh2 := Real.sq_sqrt hh
    have hh0 := Real.sqrt_nonneg (h t)
    nlinarith [mul_nonneg hb0.le hh0]
  have heq : barrierPrimitive h u c t = -(b / a * (a - b)) := by
    dsimp [barrierPrimitive]
    change (c + u t) / a - b = _
    rw [← hb2]
    field_simp [ha.ne']
    ring
  rw [heq, abs_neg, abs_of_nonneg (mul_nonneg (div_nonneg hb0.le ha.le) (sub_nonneg.mpr hba))]
  calc
    _ ≤ 1 * (a - b) := mul_le_mul_of_nonneg_right ((div_le_one ha).mpr hba) (sub_nonneg.mpr hba)
    _ ≤ Real.sqrt (h t) := by simpa only [one_mul] using hdiff

end EllipsoidVerification
end
end CanonicalSource16

section CanonicalSource17
/- Source: Ellipsoid/CoefficientLaurent.lean -/



noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace EllipsoidVerification

def lowerLaurent {n : ℕ} (e : Coefficients n) (k : ℕ) (t : ℝ) : ℝ :=
  ∑ j : Fin (n + 1), if j.val < k then e j * t ^ (2 * (j.val : ℝ) - 2 * k) else 0

def upperLaurent {n : ℕ} (e : Coefficients n) (k : ℕ) (t : ℝ) : ℝ :=
  ∑ j : Fin (n + 1), if k < j.val then e j * t ^ (2 * (j.val : ℝ) - 2 * k) else 0

def lowerLaurentDerivative {n : ℕ} (e : Coefficients n) (k : ℕ) (t : ℝ) : ℝ :=
  ∑ j : Fin (n + 1), if j.val < k then
    e j * (2 * (j.val : ℝ) - 2 * k) * t ^ (2 * (j.val : ℝ) - 2 * k - 1) else 0

def upperLaurentDerivative {n : ℕ} (e : Coefficients n) (k : ℕ) (t : ℝ) : ℝ :=
  ∑ j : Fin (n + 1), if k < j.val then
    e j * (2 * (j.val : ℝ) - 2 * k) * t ^ (2 * (j.val : ℝ) - 2 * k - 1) else 0

theorem hasDerivAt_lowerLaurent {n : ℕ} (e : Coefficients n) (k : ℕ)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (lowerLaurent e k) (lowerLaurentDerivative e k t) t := by
  unfold lowerLaurent lowerLaurentDerivative
  apply HasDerivAt.fun_sum
  intro j hj
  by_cases h : j.val < k
  · simp only [h, if_true]
    convert (Real.hasDerivAt_rpow_const (Or.inl ht.ne')).const_mul (e j) using 1 <;> ring
  · simpa only [h, if_false] using hasDerivAt_const t (0 : ℝ)

theorem hasDerivAt_upperLaurent {n : ℕ} (e : Coefficients n) (k : ℕ)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (upperLaurent e k) (upperLaurentDerivative e k t) t := by
  unfold upperLaurent upperLaurentDerivative
  apply HasDerivAt.fun_sum
  intro j hj
  by_cases h : k < j.val
  · simp only [h, if_true]
    convert (Real.hasDerivAt_rpow_const (Or.inl ht.ne')).const_mul (e j) using 1 <;> ring
  · simpa only [h, if_false] using hasDerivAt_const t (0 : ℝ)

theorem continuousAt_upperLaurentDerivative {n : ℕ} (e : Coefficients n) (k : ℕ)
    {t : ℝ} (ht : 0 < t) : ContinuousAt (upperLaurentDerivative e k) t := by
  apply tendsto_finsetSum
  intro j hj
  by_cases h : k < j.val
  · simp only [h, if_true]
    exact continuousAt_const.mul (continuousAt_id.rpow_const (Or.inl ht.ne'))
  · simp only [h, if_false]
    exact continuousAt_const

theorem lowerLaurent_pos {n k : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) (hk : 0 < k) {t : ℝ} (ht : 0 < t) :
    0 < lowerLaurent e k t := by
  have hnon (j : Fin (n + 1)) :
      0 ≤ if j.val < k then e j * t ^ (2 * (j.val : ℝ) - 2 * k) else 0 := by
    split_ifs
    · exact mul_nonneg (he.1 j) (Real.rpow_nonneg ht.le _)
    · exact le_rfl
  have h := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin (n + 1)))) =>
    hnon j) (Finset.mem_univ 0)
  apply lt_of_lt_of_le _ h
  simpa only [Fin.val_zero, hk, if_true, Nat.cast_zero, mul_zero, zero_sub] using
    mul_pos he.2.1 (Real.rpow_pos_of_pos ht (-(2 * k : ℝ)))

theorem upperLaurent_pos {n k : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) (hkn : k < n) {t : ℝ} (ht : 0 < t) :
    0 < upperLaurent e k t := by
  have hnon (j : Fin (n + 1)) :
      0 ≤ if k < j.val then e j * t ^ (2 * (j.val : ℝ) - 2 * k) else 0 := by
    split_ifs
    · exact mul_nonneg (he.1 j) (Real.rpow_nonneg ht.le _)
    · exact le_rfl
  have h := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin (n + 1)))) =>
    hnon j) (Finset.mem_univ (Fin.last n))
  apply lt_of_lt_of_le _ h
  simpa only [Fin.val_last, hkn, if_true] using
    mul_pos he.2.2 (Real.rpow_pos_of_pos ht (2 * (n : ℝ) - 2 * k))

theorem upperLaurentDerivative_pos {n k : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) (hkn : k < n) {t : ℝ} (ht : 0 < t) :
    0 < upperLaurentDerivative e k t := by
  have hnon (j : Fin (n + 1)) : 0 ≤ if k < j.val then
      e j * (2 * (j.val : ℝ) - 2 * k) * t ^ (2 * (j.val : ℝ) - 2 * k - 1) else 0 := by
    split_ifs with h
    · have hh : (k : ℝ) < j.val := by exact_mod_cast h
      exact mul_nonneg (mul_nonneg (he.1 j) (by linarith)) (Real.rpow_nonneg ht.le _)
    · exact le_rfl
  have h := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin (n + 1)))) =>
    hnon j) (Finset.mem_univ (Fin.last n))
  apply lt_of_lt_of_le _ h
  have hh : (k : ℝ) < n := by exact_mod_cast hkn
  simpa only [Fin.val_last, hkn, if_true] using
    mul_pos (mul_pos he.2.2 (show 0 < 2 * (n : ℝ) - 2 * k by linarith))
      (Real.rpow_pos_of_pos ht _)

theorem coefficientHead_eq_scaled_lowerLaurent {n : ℕ} (e : Coefficients n) (k : ℕ)
    {t : ℝ} (ht : 0 < t) :
    coefficientHead e k t = t ^ (2 * (k : ℝ)) * lowerLaurent e k t := by
  rw [coefficientHead_rpow, lowerLaurent, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs
  · rw [mul_left_comm, ← Real.rpow_add ht]
    congr 2
    ring
  · simp

theorem coefficientPolynomial_eq_scaled_laurent {n : ℕ} (e : Coefficients n)
    (k : Fin (n + 1)) {t : ℝ} (ht : 0 < t) :
    coefficientPolynomial e t = t ^ (2 * (k.val : ℝ)) *
      (lowerLaurent e k.val t + e k + upperLaurent e k.val t) := by
  have hsplit : lowerLaurent e k.val t + e k + upperLaurent e k.val t =
      ∑ j : Fin (n + 1), e j * t ^ (2 * (j.val : ℝ) - 2 * k.val) := by
    rw [lowerLaurent, upperLaurent,
      ← Fintype.sum_ite_eq' k e,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hjk : j = k
    · subst j
      simp
    · have hval : j.val ≠ k.val := fun h => hjk (Fin.ext h)
      rcases lt_or_gt_of_ne hval with h | h <;>
        simp [hjk, h, not_lt.mpr h.le]
  rw [hsplit, coefficientPolynomial_rpow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_left_comm, ← Real.rpow_add ht]
  congr 2
  ring

theorem lowerLaurent_tendsto_atTop {n : ℕ} (e : Coefficients n) (k : ℕ) :
    Tendsto (lowerLaurent e k) atTop (𝓝 0) := by
  have h (j : Fin (n + 1)) : Tendsto
      (fun t : ℝ => if j.val < k then e j * t ^ (2 * (j.val : ℝ) - 2 * k) else 0)
      atTop (𝓝 0) := by
    by_cases hj : j.val < k
    · have hjR : (j.val : ℝ) < k := by exact_mod_cast hj
      have hp := (tendsto_rpow_neg_atTop (show 0 < 2 * (k : ℝ) - 2 * j.val by linarith)).const_mul (e j)
      simpa only [hj, if_true, mul_zero, neg_sub] using hp
    · simp only [hj, if_false]
      exact tendsto_const_nhds
  have hfun : lowerLaurent e k = (fun t : ℝ =>
      ∑ j : Fin (n + 1), if j.val < k then
        e j * t ^ (2 * (j.val : ℝ) - 2 * k) else 0) := by
    funext t
    rfl
  rw [hfun]
  simpa only [Finset.sum_const_zero] using
    tendsto_finsetSum Finset.univ (fun j _ => h j)

theorem upperLaurent_tendsto_zero {n : ℕ} (e : Coefficients n) (k : ℕ) :
    Tendsto (upperLaurent e k) (𝓝[>] 0) (𝓝 0) := by
  have hid : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have h (j : Fin (n + 1)) : Tendsto
      (fun t : ℝ => if k < j.val then e j * t ^ (2 * (j.val : ℝ) - 2 * k) else 0)
      (𝓝[>] 0) (𝓝 0) := by
    by_cases hj : k < j.val
    · have hjR : (k : ℝ) < j.val := by exact_mod_cast hj
      have hp := (hid.rpow_const_nhds_zero
        (show 0 < 2 * (j.val : ℝ) - 2 * k by linarith)).const_mul (e j)
      simpa only [hj, if_true, mul_zero] using hp
    · simp only [hj, if_false]
      exact tendsto_const_nhds
  have hfun : upperLaurent e k = (fun t : ℝ =>
      ∑ j : Fin (n + 1), if k < j.val then
        e j * t ^ (2 * (j.val : ℝ) - 2 * k) else 0) := by
    funext t
    rfl
  rw [hfun]
  simpa only [Finset.sum_const_zero] using
    tendsto_finsetSum Finset.univ (fun j _ => h j)

end EllipsoidVerification
end
end CanonicalSource17

section CanonicalSource18
/- Source: Ellipsoid/CoefficientBarrier.lean -/



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
end
end CanonicalSource18

section CanonicalSource19
/- Source: Ellipsoid/StrictCoefficientBound.lean -/



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
end
end CanonicalSource19

section CanonicalSource20
/- Source: Ellipsoid/CoefficientProperness.lean -/



noncomputable section

open scoped ContDiff

open Set Filter Matrix
open scoped Topology BigOperators

namespace EllipsoidVerification

def closedCoefficientOrthant (m : ℕ) : Set (Fin m → ℝ) := {x | 0 ≤ x}

def restrictedCoefficientMap (m : ℕ) (e0 en : ℝ) : closedCoefficientOrthant m → (Fin m → ℝ) :=
  fun x => coefficientMap m e0 en x

theorem isClosed_closedCoefficientOrthant (m : ℕ) : IsClosed (closedCoefficientOrthant m) :=
  isClosed_le continuous_const continuous_id

theorem coefficientMap_smooth_neighborhood {m : ℕ} {e0 en : ℝ}
    (h0 : 0 < e0) (hn : 0 < en) :
    ∃ U : Set (Fin m → ℝ), IsOpen U ∧ closedCoefficientOrthant m ⊆ U ∧
      ContDiffOn ℝ ∞ (coefficientMap m e0 en) U := by
  let U := fixedEndpoints m e0 en ⁻¹' positiveCoefficientDomain (m + 1)
  have hPhi : ContDiff ℝ ∞ (fixedEndpoints m e0 en) := by
    apply contDiff_pi.mpr
    intro j
    unfold fixedEndpoints
    split_ifs <;> fun_prop
  refine ⟨U, (isOpen_positiveCoefficientDomain (m + 1)).preimage hPhi.continuous, ?_, ?_⟩
  · exact fun x hx => admissible_mem_positiveCoefficientDomain (fixedEndpoints_admissible h0 hn hx)
  · apply contDiffOn_pi.mpr
    intro k
    exact (contDiffOn_coefficientTransform (k := k.val + 1) (by omega) (by omega)).comp
      hPhi.contDiffOn (fun x hx => hx)

theorem coefficientMap_contDiffAt {m : ℕ} {e0 en : ℝ} {x : Fin m → ℝ}
    (h0 : 0 < e0) (hn : 0 < en) (hx : 0 ≤ x) :
    ContDiffAt ℝ ∞ (coefficientMap m e0 en) x := by
  obtain ⟨U, hU, hO, hF⟩ := coefficientMap_smooth_neighborhood h0 hn
  exact hF.contDiffAt (hU.mem_nhds (hO hx))

theorem continuousOn_coefficientMap_orthant {m : ℕ} {e0 en : ℝ}
    (h0 : 0 < e0) (hn : 0 < en) :
    ContinuousOn (coefficientMap m e0 en) (closedCoefficientOrthant m) :=
  fun x hx => (coefficientMap_contDiffAt h0 hn hx).continuousAt.continuousWithinAt

theorem continuous_restrictedCoefficientMap {m : ℕ} {e0 en : ℝ}
    (h0 : 0 < e0) (hn : 0 < en) : Continuous (restrictedCoefficientMap m e0 en) :=
  (continuousOn_coefficientMap_orthant h0 hn).restrict

theorem coefficientMap_coordinate_lt_sq {m : ℕ} {e0 en : ℝ} {x : Fin m → ℝ}
    (h0 : 0 < e0) (hn : 0 < en) (hx : 0 ≤ x) (i : Fin m) :
    x i < (coefficientMap m e0 en x i) ^ 2 := by
  have hi := i.isLt
  have h := coefficientTransform_coefficient_lt_sq (fixedEndpoints_admissible h0 hn hx)
    (⟨i.val + 1, by omega⟩ : Fin (m + 2))
    (by change 0 < i.val + 1; omega) (by change i.val + 1 < m + 1; omega)
  rw [fixedEndpoints_internal m e0 en x i] at h
  simpa only [coefficientMap, Fin.val_mk] using h

theorem isCompact_coefficientMap_preimage {m : ℕ} {e0 en : ℝ}
    (h0 : 0 < e0) (hn : 0 < en) {K : Set (Fin m → ℝ)} (hK : IsCompact K) :
    IsCompact (closedCoefficientOrthant m ∩ coefficientMap m e0 en ⁻¹' K) := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (continuous_id : Continuous (id : (Fin m → ℝ) → _)).continuousOn
  let M := max B 0
  have hM : 0 ≤ M := le_max_right _ _
  have hclosed := (continuousOn_coefficientMap_orthant h0 hn).preimage_isClosed_of_isClosed
    (isClosed_closedCoefficientOrthant m) hK.isClosed
  apply (isCompact_Icc : IsCompact (Icc (0 : Fin m → ℝ) (fun _ => M ^ 2))).of_isClosed_subset hclosed
  intro x hx
  refine ⟨hx.1, fun i => ?_⟩
  have hbound : ‖coefficientMap m e0 en x‖ ≤ M := (hB _ hx.2).trans (le_max_left _ _)
  have hi : |coefficientMap m e0 en x i| ≤ M := by
    simpa only [Real.norm_eq_abs] using
      (norm_le_pi_norm (coefficientMap m e0 en x) i).trans hbound
  have hsq : (coefficientMap m e0 en x i) ^ 2 ≤ M ^ 2 := by
    have h := abs_le.mp hi
    nlinarith
  exact (coefficientMap_coordinate_lt_sq h0 hn hx.1 i).le.trans hsq

theorem restrictedCoefficientMap_isProperMap {m : ℕ} {e0 en : ℝ}
    (h0 : 0 < e0) (hn : 0 < en) : IsProperMap (restrictedCoefficientMap m e0 en) := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨continuous_restrictedCoefficientMap h0 hn, ?_⟩
  intro K hK
  rw [Subtype.isCompact_iff]
  convert isCompact_coefficientMap_preimage h0 hn hK using 1
  ext x
  simp only [Set.mem_image, Set.mem_preimage, Set.mem_inter_iff, Subtype.exists,
    restrictedCoefficientMap, exists_prop]
  aesop

theorem restrictedCoefficientMap_isClosedEmbedding {m : ℕ} {e0 en : ℝ}
    (h0 : 0 < e0) (hn : 0 < en) :
    Topology.IsClosedEmbedding (restrictedCoefficientMap m e0 en) := by
  apply Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_restrictedCoefficientMap h0 hn)
  · intro x y hxy
    exact Subtype.ext (coefficientMap_injOn_nonnegative h0 hn x.property y.property hxy)
  · exact (restrictedCoefficientMap_isProperMap h0 hn).isClosedMap

theorem coefficientMap_has_smooth_localInverse {m : ℕ} {e0 en : ℝ} {x : Fin m → ℝ}
    (h0 : 0 < e0) (hn : 0 < en) (hx : 0 ≤ x) :
    ∃ G : (Fin m → ℝ) → (Fin m → ℝ),
      ContDiffAt ℝ ∞ G (coefficientMap m e0 en x) ∧
      (∀ᶠ y in 𝓝 x, G (coefficientMap m e0 en y) = y) ∧
      (∀ᶠ z in 𝓝 (coefficientMap m e0 en x), coefficientMap m e0 en (G z) = z) := by
  let J := fixedCoefficientJacobian m e0 en x
  have hJ := fixedCoefficientJacobian_diagonallyStable h0 hn hx
  have hinj : Function.Injective (matrixDerivative J) := by
    apply (injective_iff_map_eq_zero (matrixDerivative J)).mpr
    intro v hv
    by_contra hne
    obtain ⟨i, hi⟩ := hJ.exists_positive_coordinate hne
    have hvi := congrFun hv i
    change (J *ᵥ v) i = 0 at hvi
    rw [hvi, mul_zero] at hi
    exact (lt_irrefl 0) hi
  let A := (LinearEquiv.ofInjectiveEndo (matrixDerivative J).toLinearMap hinj).toContinuousLinearEquiv
  have hA : HasFDerivAt (coefficientMap m e0 en) (A : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ)) x :=
    hasFDerivAt_coefficientMap h0 hn hx
  have hs := coefficientMap_contDiffAt h0 hn hx
  have hstrict := hs.hasStrictFDerivAt' hA (by simp)
  refine ⟨hstrict.localInverse _ A x, ?_, hstrict.eventually_left_inverse,
    hstrict.eventually_right_inverse⟩
  exact hs.to_localInverse hA (by simp)

/-- All assertions of the coefficient-transform theorem are kept explicit,
including its boundary, actual derivative, properness, and local smooth inverse. -/
structure CoefficientTransformConclusion (m : ℕ) (e0 en : ℝ) : Prop where
  injective : Set.InjOn (coefficientMap m e0 en) (closedCoefficientOrthant m)
  smoothNeighborhood : ∃ U : Set (Fin m → ℝ), IsOpen U ∧ closedCoefficientOrthant m ⊆ U ∧
    ContDiffOn ℝ ∞ (coefficientMap m e0 en) U
  principalMinors : ∀ x, 0 ≤ x → principalJacobianPositive (fixedCoefficientJacobian m e0 en x)
  exactDerivative : ∀ x, 0 ≤ x → HasFDerivAt (coefficientMap m e0 en)
    (matrixDerivative (fixedCoefficientJacobian m e0 en x)) x
  strictBound : ∀ x, 0 ≤ x → ∀ i, Real.sqrt (x i) < coefficientMap m e0 en x i
  proper : IsProperMap (restrictedCoefficientMap m e0 en)
  embedding : Topology.IsClosedEmbedding (restrictedCoefficientMap m e0 en)
  closedImage : IsClosed (Set.range (restrictedCoefficientMap m e0 en))
  smoothLocalInverse : ∀ x, 0 ≤ x → ∃ G : (Fin m → ℝ) → (Fin m → ℝ),
    ContDiffAt ℝ ∞ G (coefficientMap m e0 en x) ∧
    (∀ᶠ y in 𝓝 x, G (coefficientMap m e0 en y) = y) ∧
    (∀ᶠ z in 𝓝 (coefficientMap m e0 en x), coefficientMap m e0 en (G z) = z)

theorem coefficient_transform_theorem {m : ℕ} {e0 en : ℝ}
    (h0 : 0 < e0) (hn : 0 < en) : CoefficientTransformConclusion m e0 en where
  injective := coefficientMap_injOn_nonnegative h0 hn
  smoothNeighborhood := coefficientMap_smooth_neighborhood h0 hn
  principalMinors := fun x hx => coefficientMap_principalJacobianPositive h0 hn hx
  exactDerivative := fun x hx => hasFDerivAt_coefficientMap h0 hn hx
  strictBound := by
    intro x hx i
    have hi := i.isLt
    have h := coefficientTransform_gt_sqrt (fixedEndpoints_admissible h0 hn hx)
      (⟨i.val + 1, by omega⟩ : Fin (m + 2))
      (by change 0 < i.val + 1; omega) (by change i.val + 1 < m + 1; omega)
    rw [fixedEndpoints_internal m e0 en x i] at h
    simpa only [coefficientMap, Fin.val_mk] using h
  proper := restrictedCoefficientMap_isProperMap h0 hn
  embedding := restrictedCoefficientMap_isClosedEmbedding h0 hn
  closedImage := (restrictedCoefficientMap_isProperMap h0 hn).isClosed_range
  smoothLocalInverse := fun x hx => coefficientMap_has_smooth_localInverse h0 hn hx

end EllipsoidVerification
end
end CanonicalSource20

section CanonicalSource21
/- Source: Ellipsoid/MeasuredCoefficientBox.lean -/



noncomputable section

open Set Filter Polynomial Finset
open scoped BigOperators

namespace EllipsoidVerification

theorem finset_product_rpow {ι : Type*} [DecidableEq ι] (s : Finset ι) (d : ι → ℝ)
    (hd : ∀ i ∈ s, 0 ≤ d i) (r : ℝ) : (∏ i ∈ s, d i) ^ r = ∏ i ∈ s, (d i) ^ r := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi,
        Real.mul_rpow (hd i (Finset.mem_insert_self _ _))
          (Finset.prod_nonneg fun j hj => hd j (Finset.mem_insert_of_mem hj)),
        ih (fun j hj => hd j (Finset.mem_insert_of_mem hj))]

theorem elementaryOn_eq_sum_products {n k : ℕ} (d : Fin n → ℝ) (hk : k ≤ n) :
    elementaryOn Finset.univ d k =
      ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ∏ i ∈ s, d i := by
  rw [← coeff_prod_X_add_C Finset.univ d (by simpa using hk), Finset.prod_X_add_C_coeff]
  · simp only [Finset.card_univ, Fintype.card_fin, Nat.sub_sub_self hk]
  · simp

theorem product_powersetCard_products {n k : ℕ} (d : Fin n → ℝ) (hk : 0 < k) :
    (∏ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ∏ i ∈ s, d i) =
      (∏ i, d i) ^ ((n - 1).choose (k - 1)) := by
  classical
  let S := (Finset.univ : Finset (Fin n)).powersetCard k
  calc
    _ = ∏ s ∈ S, ∏ i : Fin n, if i ∈ s then d i else 1 := by
      apply Finset.prod_congr rfl
      intro s hs
      exact (Finset.prod_ite_mem_eq s d).symm
    _ = ∏ i : Fin n, ∏ s ∈ S, if i ∈ s then d i else 1 := Finset.prod_comm
    _ = ∏ i : Fin n, d i ^ ((n - 1).choose (k - 1)) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [← Finset.prod_filter, Finset.prod_const]
      congr 1
      have h := Finset.card_filter_powersetCard_subset ({i} : Finset (Fin n))
        Finset.univ k (Finset.subset_univ _)
        (by simpa only [Finset.card_singleton] using (Nat.succ_le_iff.mpr hk))
      simpa only [S, Finset.singleton_subset_iff, Finset.card_univ, Fintype.card_fin,
        Finset.card_singleton] using h
    _ = _ := Finset.prod_pow _ _ _

theorem elementary_ge_geometric_mean {n k : ℕ} (hn : 0 < n)
    (hk : k ≤ n) (d : Fin n → ℝ) (hd : ∀ i, 0 < d i) :
    (n.choose k : ℝ) * (∏ i, d i) ^ ((k : ℝ) / n) ≤ elementaryOn Finset.univ d k := by
  classical
  by_cases hk0 : k = 0
  · subst k
    simp [elementaryOn, Polynomial.coeff_zero_prod]
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
  let S := (Finset.univ : Finset (Fin n)).powersetCard k
  let N : ℝ := n.choose k
  have hN : 0 < N := by
    change (0 : ℝ) < (n.choose k : ℝ)
    exact_mod_cast Nat.choose_pos hk
  have hprod : 0 < ∏ i, d i := Finset.prod_pos fun i _ => hd i
  have hw : (∑ _s ∈ S, N⁻¹) = 1 := by
    simp only [Finset.sum_const, S, Finset.card_powersetCard, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    exact mul_inv_cancel₀ hN.ne'
  have h := Real.geom_mean_le_arith_mean_weighted S (fun _ => N⁻¹)
    (fun s => ∏ i ∈ s, d i) (fun s hs => inv_nonneg.mpr hN.le) hw
    (fun s hs => Finset.prod_nonneg fun i hi => (hd i).le)
  have hcount : (((n - 1).choose (k - 1) : ℕ) : ℝ) * N⁻¹ = (k : ℝ) / n := by
    have hnat := Nat.add_one_mul_choose_eq (n - 1) (k - 1)
    rw [Nat.sub_add_cancel hn, Nat.sub_add_cancel hkpos] at hnat
    have hr : (n : ℝ) * ((n - 1).choose (k - 1) : ℝ) = N * k := by
      change (n : ℝ) * ((n - 1).choose (k - 1) : ℝ) = (n.choose k : ℝ) * (k : ℝ)
      exact_mod_cast hnat
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    field_simp [hN.ne', hnR]
    nlinarith
  rw [← finset_product_rpow S (fun s => ∏ i ∈ s, d i)
      (fun s hs => Finset.prod_nonneg fun i hi => (hd i).le),
    product_powersetCard_products d hkpos, ← Real.rpow_natCast_mul hprod.le,
    hcount, ← Finset.mul_sum, ← elementaryOn_eq_sum_products d hk] at h
  have hmul := mul_le_mul_of_nonneg_left h hN.le
  simpa only [mul_inv_cancel_left₀ hN.ne'] using hmul

/-- The coefficient box determined by measured intrinsic volumes, as stated
in Section 5.1. Both constants and the exponent `2k/n` are retained exactly. -/
theorem measured_coefficient_box {n : ℕ} (hn : 0 < n) (E : FullEllipsoid n)
    (k : Fin (n + 1)) (hk : 0 < k.val) (hkn : k.val < n) :
    (n.choose k.val : ℝ) * (E.volume n / unitBallVolume n) ^ (2 * (k.val : ℝ) / n) ≤
      axisCoefficients E.semiaxis k ∧
    axisCoefficients E.semiaxis k < (E.volume k.val / unitBallVolume k.val) ^ 2 ∧
    axisCoefficients E.semiaxis (Fin.last n) = (E.volume n / unitBallVolume n) ^ 2 := by
  have hp : 0 < ∏ i, E.semiaxis i := Finset.prod_pos fun i _ => E.semiaxis_pos i
  have htop : E.volume n / unitBallVolume n = ∏ i, E.semiaxis i := by
    rw [E.volume_top hn]
    field_simp [(unitBallVolume_pos n).ne']
  have hmid : E.volume k.val / unitBallVolume k.val =
      coefficientTransform (axisCoefficients E.semiaxis) k.val := by
    rw [E.volume_eq_coefficientTransform hk hkn]
    field_simp [(unitBallVolume_pos k.val).ne']
  refine ⟨?_, ?_, ?_⟩
  · have h := elementary_ge_geometric_mean hn hkn.le (fun i => E.semiaxis i ^ 2)
      (fun i => sq_pos_of_pos (E.semiaxis_pos i))
    rw [Finset.prod_pow, ← Real.rpow_natCast_mul hp.le] at h
    simpa only [Nat.cast_ofNat, htop, axisCoefficients, axisCoefficientPolynomial, elementaryOn,
      show (2 : ℝ) * ((k.val : ℝ) / n) = 2 * (k.val : ℝ) / n by ring] using h
  · rw [hmid]
    exact coefficientTransform_coefficient_lt_sq
      (axisCoefficients_admissible E.semiaxis E.semiaxis_pos) k hk hkn
  · rw [axisCoefficients_last, htop]

end EllipsoidVerification
end
end CanonicalSource21

section CanonicalSource22
/- Source: Ellipsoid/Main.lean -/



/-!
# Complete Ellipsoid theorem entry point

This source entry point includes every principal theorem, the exact geometric
Steiner/GSZ correspondence in their dependency closure, the measured coefficient
bounds, and both directions of the customary affine-ball parameterization.
It is separate from generated compiled stages and does not certify compilation.
-/

namespace EllipsoidVerification

theorem principal_reconstruction_and_stability :
    IntrinsicReconstruction ∧ UniformHolderRecovery ∧ SharpHolderRecovery ∧
      SharpHolderRecoveryAtFixedVolume :=
  ⟨intrinsic_reconstruction, uniform_holder_recovery, sharp_holder_recovery,
    sharp_holder_recovery_at_fixed_volume⟩

end EllipsoidVerification
end CanonicalSource22
