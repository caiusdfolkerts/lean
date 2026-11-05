module

public import Ellipsoid.JacobianPositivity
public import Ellipsoid.MellinIntegrationByParts

@[expose] public section

noncomputable section

open MeasureTheory Matrix Finset
open scoped BigOperators

namespace EllipsoidVerification

/-- The equality of the head and tail diagonal formulas in Lemma 4.1 is
the Mellin recurrence with parameter `s = 1/2` and exponent `r = k`. -/
theorem jacobianHeadMoment_eq_tail_diagonal {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) (k : Fin (n - 1)) :
    jacobianHeadMoment e k k = jacobianTailMoment e k k := by
  have h := coefficientMellinPower_recurrence he
    (s := (1 / 2 : ℝ)) (r := internalDegree k) (internalDegree_pos k)
    (by nlinarith [internalDegree_lt k])
  have hdiff : jacobianHeadMoment e k k - jacobianTailMoment e k k =
      ∑ l : Fin (n + 1), (internalDegree k - l.val) * e l *
        mellinMoment e (internalDegree k + 2 * l.val) := by
    unfold jacobianHeadMoment jacobianTailMoment
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    rw [show 2 * internalDegree k - internalDegree k + 2 * (l.val : ℝ) =
        internalDegree k + 2 * l.val by ring]
    rcases lt_trichotomy (l.val : ℝ) (internalDegree k) with hlt | heq | hgt
    · simp only [hlt, not_lt.mpr hlt.le, if_true, if_false, sub_zero]
    · simp [heq]
    · simp only [hgt, not_lt.mpr hgt.le, if_true, if_false, zero_sub]
      ring
  apply sub_eq_zero.mp
  rw [hdiff]
  convert h using 1
  apply Finset.sum_congr rfl
  intro l hl
  norm_num [coefficientMellinPower, mellinMoment]

theorem coefficientJacobian_eq_balancedJacobian {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) : coefficientJacobian e = balancedJacobian e := by
  funext k j
  have hh : (∑ l : Fin (n + 1), if l.val < k.val + 1 then
      (((k.val + 1 : ℕ) : ℝ) - l.val) * e l * mellinMoment e
          (2 * ((j.val + 1 : ℕ) : ℝ) - ((k.val + 1 : ℕ) : ℝ) + 2 * l.val)
      else 0) = jacobianHeadMoment e k j := by
    unfold jacobianHeadMoment
    apply Finset.sum_congr rfl
    intro l hl
    have htest : (l.val : ℝ) < internalDegree k ↔ l.val < k.val + 1 := by
      simpa only [internalDegree, Nat.cast_add, Nat.cast_one] using
        (Nat.cast_lt (α := ℝ) (m := l.val) (n := k.val + 1))
    simp only [htest]
    simp only [internalDegree, Nat.cast_add, Nat.cast_one]
  have ht : (∑ l : Fin (n + 1), if k.val + 1 < l.val then
      ((l.val : ℝ) - (k.val + 1 : ℕ)) * e l * mellinMoment e
          (2 * ((j.val + 1 : ℕ) : ℝ) - ((k.val + 1 : ℕ) : ℝ) + 2 * l.val)
      else 0) = jacobianTailMoment e k j := by
    unfold jacobianTailMoment
    apply Finset.sum_congr rfl
    intro l hl
    have htest : internalDegree k < (l.val : ℝ) ↔ k.val + 1 < l.val := by
      simpa only [internalDegree, Nat.cast_add, Nat.cast_one] using
        (Nat.cast_lt (α := ℝ) (m := k.val + 1) (n := l.val))
    simp only [htest]
    simp only [internalDegree, Nat.cast_add, Nat.cast_one]
  simp only [coefficientJacobian, hh, ht, balancedJacobian]
  rcases lt_trichotomy k j with hlt | rfl | hgt
  · simp [hlt, hlt.le]
  · rw [jacobianHeadMoment_eq_tail_diagonal he]
    simp
    ring
  · simp [hgt, not_le.mpr hgt, not_lt.mpr hgt.le]

theorem coefficientJacobian_principal_minors_pos {n : ℕ} (hn : 0 < n)
    {e : Coefficients n} (he : coefficientAdmissible e) :
    principalJacobianPositive (coefficientJacobian e) := by
  rw [coefficientJacobian_eq_balancedJacobian he]
  exact balancedJacobian_principal_minors_pos hn he

end EllipsoidVerification
