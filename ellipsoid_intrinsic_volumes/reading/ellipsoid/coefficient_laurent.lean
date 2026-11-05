module

public import Ellipsoid.CoefficientExpansion
public import Ellipsoid.AxisRationalIdentity
public import Ellipsoid.PositiveRemainder

@[expose] public section

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
