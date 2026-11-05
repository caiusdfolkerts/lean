module

public import Ellipsoid.MellinIntegrationByParts

@[expose] public section

noncomputable section

open scoped ContDiff

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace EllipsoidVerification

def coefficientExpansion {n : ℕ} (e : Coefficients n) (k : ℕ) : ℝ :=
  ∑ l : Fin (n + 1), ∑ j : Fin (n + 1), if l.val < k ∧ k ≤ j.val then
    ((j.val : ℝ) - l.val) * e l * e j *
      mellinMoment e (2 * (l.val : ℝ) + 2 * j.val - k) else 0

theorem coefficientPolynomial_rpow {n : ℕ} (e : Coefficients n) (t : ℝ) :
    coefficientPolynomial e t = ∑ j : Fin (n + 1), e j * t ^ (2 * (j.val : ℝ)) := by
  simp [coefficientPolynomial, ← Real.rpow_natCast]

theorem coefficientHead_rpow {n : ℕ} (e : Coefficients n) (k : ℕ) (t : ℝ) :
    coefficientHead e k t = ∑ j : Fin (n + 1), if j.val < k then
      e j * t ^ (2 * (j.val : ℝ)) else 0 := by
  simp [coefficientHead, ← Real.rpow_natCast]

theorem coefficientDerivative_rpow {n : ℕ} (e : Coefficients n) {t : ℝ} (ht : 0 < t) :
    coefficientDerivative e t = ∑ j : Fin (n + 1),
      (2 * j.val : ℝ) * e j * t ^ (2 * (j.val : ℝ) - 1) := by
  unfold coefficientDerivative
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : j.val = 0
  · simp [h]
  · rw [← Real.rpow_natCast, Nat.cast_sub (show 1 ≤ 2 * j.val by omega)]
    push_cast
    rfl

theorem coefficientHeadDerivative_rpow {n : ℕ} (e : Coefficients n) (k : ℕ)
    {t : ℝ} (ht : 0 < t) :
    coefficientHeadDerivative e k t = ∑ j : Fin (n + 1), if j.val < k then
      (2 * j.val : ℝ) * e j * t ^ (2 * (j.val : ℝ) - 1) else 0 := by
  unfold coefficientHeadDerivative
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hcut : j.val < k
  · rw [if_pos hcut, if_pos hcut]
    by_cases h : j.val = 0
    · simp [h]
    · rw [← Real.rpow_natCast, Nat.cast_sub (show 1 ≤ 2 * j.val by omega)]
      push_cast
      rfl
  · simp [hcut]

/-- Antisymmetric terms on the same side of a finite cut cancel exactly. -/
theorem head_pair_cancellation {n : ℕ} (e : Coefficients n) (k : ℕ)
    (g : Fin (n + 1) → Fin (n + 1) → ℝ) (hg : ∀ i j, g i j = g j i) :
    (∑ l : Fin (n + 1), ∑ j : Fin (n + 1), if l.val < k then
      ((j.val : ℝ) - l.val) * e l * e j * g l j else 0) =
    ∑ l : Fin (n + 1), ∑ j : Fin (n + 1), if l.val < k ∧ k ≤ j.val then
      ((j.val : ℝ) - l.val) * e l * e j * g l j else 0 := by
  let S : ℝ := ∑ l : Fin (n + 1), ∑ j : Fin (n + 1), if l.val < k ∧ j.val < k then
    ((j.val : ℝ) - l.val) * e l * e j * g l j else 0
  have hneg : S = -S := by
    calc
      S = ∑ l : Fin (n + 1), ∑ j : Fin (n + 1),
          -(if j.val < k ∧ l.val < k then
            ((l.val : ℝ) - j.val) * e j * e l * g j l else 0) := by
        unfold S
        apply Finset.sum_congr rfl
        intro l hl
        apply Finset.sum_congr rfl
        intro j hj
        rw [hg j l]
        by_cases hlk : l.val < k <;> by_cases hjk : j.val < k <;>
          simp only [hlk, hjk, and_self, if_true, if_false, and_false, false_and,
            neg_zero] <;> ring
      _ = -(∑ l : Fin (n + 1), ∑ j : Fin (n + 1),
          if j.val < k ∧ l.val < k then
            ((l.val : ℝ) - j.val) * e j * e l * g j l else 0) := by
        simp only [Finset.sum_neg_distrib]
      _ = -S := congrArg Neg.neg (Finset.sum_comm)
  have hS : S = 0 := by linarith
  have hsplit : (∑ l : Fin (n + 1), ∑ j : Fin (n + 1), if l.val < k then
      ((j.val : ℝ) - l.val) * e l * e j * g l j else 0) =
      (∑ l : Fin (n + 1), ∑ j : Fin (n + 1), if l.val < k ∧ k ≤ j.val then
        ((j.val : ℝ) - l.val) * e l * e j * g l j else 0) + S := by
    unfold S
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hlk : l.val < k
    · by_cases hjk : j.val < k
      · have hjnot : ¬ k ≤ j.val := Nat.not_le.mpr hjk
        simp [hlk, hjk, hjnot]
      · have hjle : k ≤ j.val := Nat.le_of_not_gt hjk
        simp [hlk, hjk, hjle]
    · simp [hlk]
  simpa [hS] using hsplit

theorem coefficientTransform_integrand_expansion {n : ℕ} (e : Coefficients n) (k : ℕ)
    {t : ℝ} (ht : 0 < t) :
    (1 / 2 : ℝ) * t ^ (-(k : ℝ)) *
      (coefficientHead e k t * coefficientDerivative e t -
        coefficientHeadDerivative e k t * coefficientPolynomial e t) *
        coefficientPolynomial e t ^ (-(3 / 2 : ℝ)) =
      ∑ l : Fin (n + 1), ∑ j : Fin (n + 1), if l.val < k ∧ k ≤ j.val then
        ((j.val : ℝ) - l.val) * e l * e j *
          (t ^ (2 * (l.val : ℝ) + 2 * j.val - k - 1) *
            coefficientPolynomial e t ^ (-(3 / 2 : ℝ))) else 0 := by
  rw [← head_pair_cancellation e k
    (fun l j => t ^ (2 * (l.val : ℝ) + 2 * j.val - k - 1) *
      coefficientPolynomial e t ^ (-(3 / 2 : ℝ)))
    (by intro i j; congr 2; ring)]
  have hexpand :
      coefficientHead e k t * coefficientDerivative e t -
          coefficientHeadDerivative e k t * coefficientPolynomial e t =
        ∑ l : Fin (n + 1), ∑ j : Fin (n + 1), if l.val < k then
          e l * t ^ (2 * (l.val : ℝ)) *
              ((2 * j.val : ℝ) * e j * t ^ (2 * (j.val : ℝ) - 1)) -
            ((2 * l.val : ℝ) * e l * t ^ (2 * (l.val : ℝ) - 1)) *
              (e j * t ^ (2 * (j.val : ℝ))) else 0 := by
    rw [coefficientHead_rpow, coefficientDerivative_rpow e ht,
      coefficientHeadDerivative_rpow e k ht, coefficientPolynomial_rpow e t]
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hcut : l.val < k <;> simp only [hcut, if_true, if_false, zero_mul, sub_self]
  rw [hexpand]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_ite, ite_mul, mul_zero, zero_mul]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hlk : l.val < k
  · simp only [hlk, if_true]
    have hpow1 : t ^ (-(k : ℝ)) * (t ^ (2 * (l.val : ℝ)) *
        t ^ (2 * (j.val : ℝ) - 1)) = t ^ (2 * (l.val : ℝ) + 2 * j.val - k - 1) := by
      rw [← Real.rpow_add ht, ← Real.rpow_add ht]
      congr 1
      ring
    have hpow2 : t ^ (-(k : ℝ)) * (t ^ (2 * (l.val : ℝ) - 1) *
        t ^ (2 * (j.val : ℝ))) = t ^ (2 * (l.val : ℝ) + 2 * j.val - k - 1) := by
      rw [← Real.rpow_add ht, ← Real.rpow_add ht]
      congr 1
      ring
    linear_combination
      (((j.val : ℝ) * e l * e j) * coefficientPolynomial e t ^
        (-(3 / 2 : ℝ))) * hpow1 -
      (((l.val : ℝ) * e l * e j) * coefficientPolynomial e t ^
        (-(3 / 2 : ℝ))) * hpow2
  · simp [hlk]

theorem cut_moment_range {n k : ℕ} (hk : 0 < k) (hkn : k < n)
    {l j : Fin (n + 1)} (hl : l.val < k) (hj : k ≤ j.val) :
    0 < 2 * (l.val : ℝ) + 2 * j.val - k ∧
      2 * (l.val : ℝ) + 2 * j.val - k < 3 * n := by
  have hl0 : (0 : ℝ) ≤ l.val := Nat.cast_nonneg _
  have hln : (l.val : ℝ) < k := by exact_mod_cast hl
  have hj0 : (k : ℝ) ≤ j.val := by exact_mod_cast hj
  have hjn : (j.val : ℝ) ≤ n := by exact_mod_cast Nat.le_of_lt_succ j.isLt
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hkn' : (k : ℝ) < n := by exact_mod_cast hkn
  constructor <;> linarith

theorem coefficientTransform_eq_expansion {n : ℕ} {e : Coefficients n}
    (he : e ∈ positiveCoefficientDomain n) {k : ℕ} (hk : 0 < k) (hkn : k < n) :
    coefficientTransform e k = coefficientExpansion e k := by
  have hi (l j : Fin (n + 1)) : IntegrableOn (fun t : ℝ =>
      if l.val < k ∧ k ≤ j.val then ((j.val : ℝ) - l.val) * e l * e j *
        (t ^ (2 * (l.val : ℝ) + 2 * j.val - k - 1) *
          coefficientPolynomial e t ^ (-(3 / 2 : ℝ))) else 0) (Ioi 0) := by
    by_cases hc : l.val < k ∧ k ≤ j.val
    · simp only [hc, if_true]
      apply Integrable.const_mul
      exact integrable_coefficientMellinPower he (cut_moment_range hk hkn hc.1 hc.2).1
        (by nlinarith [(cut_moment_range hk hkn hc.1 hc.2).2])
    · simp [hc]
  rw [coefficientTransform]
  calc
    _ = ∫ t in Ioi (0 : ℝ), ∑ l : Fin (n + 1), ∑ j : Fin (n + 1),
        if l.val < k ∧ k ≤ j.val then ((j.val : ℝ) - l.val) * e l * e j *
          (t ^ (2 * (l.val : ℝ) + 2 * j.val - k - 1) *
            coefficientPolynomial e t ^ (-(3 / 2 : ℝ))) else 0 :=
      setIntegral_congr_fun measurableSet_Ioi fun t ht =>
        coefficientTransform_integrand_expansion e k ht
    _ = coefficientExpansion e k := by
      rw [integral_finsetSum _ (fun l _ => integrable_finsetSum _ (fun j _ => hi l j))]
      unfold coefficientExpansion
      apply Finset.sum_congr rfl
      intro l hl
      rw [integral_finsetSum _ (fun j _ => hi l j)]
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hc : l.val < k ∧ k ≤ j.val
      · simp [hc, mellinMoment, integral_const_mul]
      · simp [hc]

theorem contDiffOn_coefficientExpansion {n k : ℕ} (hk : 0 < k) (hkn : k < n) :
    ContDiffOn ℝ ∞ (fun e : Coefficients n => coefficientExpansion e k)
      (positiveCoefficientDomain n) := by
  unfold coefficientExpansion
  apply ContDiffOn.sum
  intro l hl
  apply ContDiffOn.sum
  intro j hj
  by_cases hc : l.val < k ∧ k ≤ j.val
  · simp only [hc, if_true]
    exact (contDiffOn_const.mul (contDiff_apply ℝ (fun _ : Fin (n + 1) => ℝ) l).contDiffOn |>.mul
      (contDiff_apply ℝ (fun _ : Fin (n + 1) => ℝ) j).contDiffOn).mul
      (contDiffOn_mellinMoment (cut_moment_range hk hkn hc.1 hc.2).1
        (cut_moment_range hk hkn hc.1 hc.2).2)
  · simp only [hc, if_false]
    exact contDiffOn_const

theorem contDiffOn_coefficientTransform {n k : ℕ} (hk : 0 < k) (hkn : k < n) :
    ContDiffOn ℝ ∞ (fun e : Coefficients n => coefficientTransform e k)
      (positiveCoefficientDomain n) :=
  (contDiffOn_coefficientExpansion hk hkn).congr
    (fun e he => coefficientTransform_eq_expansion he hk hkn)

end EllipsoidVerification
