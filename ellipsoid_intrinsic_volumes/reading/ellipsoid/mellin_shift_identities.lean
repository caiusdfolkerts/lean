module

public import Ellipsoid.CoefficientExpansion

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace EllipsoidVerification

theorem coefficientMellinPower_multiply {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) {s r : ℝ} (hr : 0 < r) (hrn : r < 2 * n * s) :
    coefficientMellinPower e s r = ∑ j : Fin (n + 1),
      e j * coefficientMellinPower e (s + 1) (r + 2 * j.val) := by
  have hi (j : Fin (n + 1)) : IntegrableOn
      (fun t : ℝ => t ^ (r + 2 * j.val - 1) * coefficientPolynomial e t ^ (-(s + 1)))
      (Ioi 0) := by
    apply integrable_coefficientMellinPower (admissible_mem_positiveCoefficientDomain he)
    · positivity
    · have hj : (j.val : ℝ) ≤ n := by exact_mod_cast Nat.le_of_lt_succ j.isLt
      nlinarith
  unfold coefficientMellinPower
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ (fun j _ => (hi j).const_mul _)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have hq := coefficientPolynomial_pos he t
  have hp : coefficientPolynomial e t ^ (-s) =
      coefficientPolynomial e t * coefficientPolynomial e t ^ (-(s + 1)) := by
    calc
      _ = coefficientPolynomial e t ^ (1 : ℝ) *
          coefficientPolynomial e t ^ (-(s + 1)) := by
        rw [← Real.rpow_add hq]
        congr 1
        ring
      _ = _ := by rw [Real.rpow_one]
  dsimp only
  rw [hp, ← mul_assoc, coefficientPolynomial_mul_rpow e (r - 1) ht, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [show r - 1 + 2 * (j.val : ℝ) = r + 2 * j.val - 1 by ring]
  ring

theorem weighted_mellin_shift {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) {r : ℝ} (hr : 0 < r) (hrn : r < 3 * n) :
    ∑ j : Fin (n + 1), (j.val : ℝ) * e j *
      coefficientMellinPower e (5 / 2) (r + 2 * j.val) = (r / 3) * mellinMoment e r := by
  have hm := coefficientMellinPower_multiply he (s := (3 / 2 : ℝ)) hr (by nlinarith)
  have hb := coefficientMellinPower_recurrence he (s := (3 / 2 : ℝ)) hr (by nlinarith)
  norm_num only at hm hb
  change mellinMoment e r = _ at hm
  have hbal : r * (∑ j : Fin (n + 1), e j * coefficientMellinPower e (5 / 2) (r + 2 * j.val)) -
      3 * (∑ j : Fin (n + 1), (j.val : ℝ) * e j *
        coefficientMellinPower e (5 / 2) (r + 2 * j.val)) = 0 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    convert hb using 1
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [← hm] at hbal
  linarith

theorem centered_mellin_shift {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) {r : ℝ} (hr : 0 < r) (hrn : r < 3 * n) (l : ℝ) :
    ∑ j : Fin (n + 1), ((j.val : ℝ) - l) * e j *
      coefficientMellinPower e (5 / 2) (r + 2 * j.val) =
        (r / 3 - l) * mellinMoment e r := by
  have hm := coefficientMellinPower_multiply he (s := (3 / 2 : ℝ)) hr (by nlinarith)
  norm_num only at hm
  change mellinMoment e r = _ at hm
  calc
    _ = (∑ j : Fin (n + 1), (j.val : ℝ) * e j *
        coefficientMellinPower e (5 / 2) (r + 2 * j.val)) -
      l * ∑ j : Fin (n + 1), e j * coefficientMellinPower e (5 / 2) (r + 2 * j.val) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
    _ = _ := by rw [weighted_mellin_shift he hr hrn, ← hm]; ring

theorem head_cross_mellin_reduction {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) (k : ℕ) (r : ℝ)
    (hr : ∀ l : Fin (n + 1), l.val < k → 0 < r + 2 * l.val)
    (hrn : ∀ l : Fin (n + 1), l.val < k → r + 2 * l.val < 3 * n) :
    (∑ l : Fin (n + 1), ∑ j : Fin (n + 1), if l.val < k ∧ k ≤ j.val then
      ((j.val : ℝ) - l.val) * e l * e j *
        coefficientMellinPower e (5 / 2) (r + 2 * l.val + 2 * j.val) else 0) =
    ∑ l : Fin (n + 1), if l.val < k then
      e l * ((r + 2 * l.val) / 3 - l.val) * mellinMoment e (r + 2 * l.val) else 0 := by
  rw [← head_pair_cancellation e k
    (fun l j => coefficientMellinPower e (5 / 2) (r + 2 * l.val + 2 * j.val))
    (by intro i j; congr 1; ring)]
  apply Finset.sum_congr rfl
  intro l hl
  by_cases hlk : l.val < k
  · simp only [hlk, if_true]
    rw [show (∑ j : Fin (n + 1), ((j.val : ℝ) - l.val) * e l * e j *
        coefficientMellinPower e (5 / 2) (r + 2 * l.val + 2 * j.val)) =
        e l * ∑ j : Fin (n + 1), ((j.val : ℝ) - l.val) * e j *
          coefficientMellinPower e (5 / 2) ((r + 2 * l.val) + 2 * j.val) by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring]
    rw [centered_mellin_shift he (hr l hlk) (hrn l hlk) l.val]
    ring
  · simp [hlk]

theorem tail_pair_cancellation {n : ℕ} (e : Coefficients n) (k : ℕ)
    (g : Fin (n + 1) → Fin (n + 1) → ℝ) (hg : ∀ i j, g i j = g j i) :
    (∑ j : Fin (n + 1), ∑ l : Fin (n + 1), if k ≤ j.val then
      ((j.val : ℝ) - l.val) * e l * e j * g l j else 0) =
    ∑ l : Fin (n + 1), ∑ j : Fin (n + 1), if l.val < k ∧ k ≤ j.val then
      ((j.val : ℝ) - l.val) * e l * e j * g l j else 0 := by
  let S : ℝ := ∑ j : Fin (n + 1), ∑ l : Fin (n + 1), if k ≤ l.val ∧ k ≤ j.val then
    ((j.val : ℝ) - l.val) * e l * e j * g l j else 0
  have hneg : S = -S := by
    calc
      S = ∑ j : Fin (n + 1), ∑ l : Fin (n + 1), if k ≤ j.val ∧ k ≤ l.val then
          ((l.val : ℝ) - j.val) * e j * e l * g j l else 0 := Finset.sum_comm
      _ = -S := by
        change _ = -(∑ j : Fin (n + 1), ∑ l : Fin (n + 1),
          if k ≤ l.val ∧ k ≤ j.val then
            ((j.val : ℝ) - l.val) * e l * e j * g l j else 0)
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro l hl
        rw [hg j l]
        by_cases hlk : k ≤ l.val <;> by_cases hjk : k ≤ j.val <;>
          simp [hlk, hjk] <;> ring
  have hS : S = 0 := by linarith
  have hsplit : (∑ j : Fin (n + 1), ∑ l : Fin (n + 1), if k ≤ j.val then
      ((j.val : ℝ) - l.val) * e l * e j * g l j else 0) =
      (∑ j : Fin (n + 1), ∑ l : Fin (n + 1), if l.val < k ∧ k ≤ j.val then
        ((j.val : ℝ) - l.val) * e l * e j * g l j else 0) + S := by
    unfold S
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    by_cases hlk : k ≤ l.val <;> by_cases hjk : k ≤ j.val <;> simp [hlk, hjk]
  rw [hS, add_zero] at hsplit
  exact hsplit.trans (Finset.sum_comm)

theorem tail_cross_mellin_reduction {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) (k : ℕ) (r : ℝ)
    (hr : ∀ j : Fin (n + 1), k ≤ j.val → 0 < r + 2 * j.val)
    (hrn : ∀ j : Fin (n + 1), k ≤ j.val → r + 2 * j.val < 3 * n) :
    (∑ l : Fin (n + 1), ∑ j : Fin (n + 1), if l.val < k ∧ k ≤ j.val then
      ((j.val : ℝ) - l.val) * e l * e j *
        coefficientMellinPower e (5 / 2) (r + 2 * l.val + 2 * j.val) else 0) =
    ∑ j : Fin (n + 1), if k ≤ j.val then
      e j * (j.val - (r + 2 * j.val) / 3) * mellinMoment e (r + 2 * j.val) else 0 := by
  rw [← tail_pair_cancellation e k
    (fun l j => coefficientMellinPower e (5 / 2) (r + 2 * l.val + 2 * j.val))
    (by intro i j; congr 1; ring)]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hjk : k ≤ j.val
  · simp only [hjk, if_true]
    have h := centered_mellin_shift he (hr j hjk) (hrn j hjk) j.val
    rw [show (∑ l : Fin (n + 1), ((j.val : ℝ) - l.val) * e l * e j *
        coefficientMellinPower e (5 / 2) (r + 2 * l.val + 2 * j.val)) =
        -e j * ∑ l : Fin (n + 1), ((l.val : ℝ) - j.val) * e l *
          coefficientMellinPower e (5 / 2) ((r + 2 * j.val) + 2 * l.val) by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      rw [show r + 2 * (l.val : ℝ) + 2 * j.val = (r + 2 * j.val) + 2 * l.val by ring]
      ring]
    rw [h]
    ring
  · simp [hjk]

end EllipsoidVerification
