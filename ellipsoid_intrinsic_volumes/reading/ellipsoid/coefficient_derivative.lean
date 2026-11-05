module

public import Ellipsoid.MellinShiftIdentities
public import Ellipsoid.MellinDifferentiation
public import Ellipsoid.JacobianBalance
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace EllipsoidVerification

theorem fderiv_mellin_product_single {n : ℕ} {e : Coefficients n}
    (he : e ∈ positiveCoefficientDomain n) (l j q : Fin (n + 1)) (c : ℝ)
    {r : ℝ} (hr : 0 < r) (hrn : r < 3 * n) :
    fderiv ℝ (fun e : Coefficients n => c * e l * e j * mellinMoment e r) e
      ((Pi.single q (1 : ℝ) : Coefficients n)) =
        c * ((Pi.single q (1 : ℝ) : Coefficients n) l * e j + e l * (Pi.single q (1 : ℝ) : Coefficients n) j) * mellinMoment e r -
        (3 / 2 : ℝ) * c * e l * e j *
          coefficientMellinPower e (5 / 2) (r + 2 * q.val) := by
  have hm : DifferentiableAt ℝ (fun z : Coefficients n => mellinMoment z r) e :=
    (hasFDerivAt_coefficientMellinPower he hr (by nlinarith : r < 2 * n * (3 / 2 : ℝ))).differentiableAt
  have hl := hasFDerivAt_apply (𝕜 := ℝ) l e
  have hj := hasFDerivAt_apply (𝕜 := ℝ) j e
  have h := ((hl.const_mul c).fun_mul hj).fun_mul hm.hasFDerivAt
  rw [h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  have hm' := fderiv_coefficientMellinPower_single he (s := (3 / 2 : ℝ)) hr
    (by nlinarith : r < 2 * n * (3 / 2 : ℝ)) q
  norm_num only at hm'
  change fderiv ℝ (fun z : Coefficients n => mellinMoment z r) e ((Pi.single q (1 : ℝ) : Coefficients n)) = _ at hm'
  rw [hm']
  ring

def coefficientRawDerivative {n : ℕ} (e : Coefficients n) (k : ℕ)
    (q : Fin (n + 1)) : ℝ :=
  ∑ l : Fin (n + 1), ∑ j : Fin (n + 1), if l.val < k ∧ k ≤ j.val then
    ((j.val : ℝ) - l.val) * ((Pi.single q (1 : ℝ) : Coefficients n) l * e j + e l * (Pi.single q (1 : ℝ) : Coefficients n) j) *
        mellinMoment e (2 * (l.val : ℝ) + 2 * j.val - k) -
      (3 / 2 : ℝ) * ((j.val : ℝ) - l.val) * e l * e j *
        coefficientMellinPower e (5 / 2) (2 * (l.val : ℝ) + 2 * j.val - k + 2 * q.val)
    else 0

theorem fderiv_coefficientTransform_single_raw {n : ℕ} {e : Coefficients n}
    (he : e ∈ positiveCoefficientDomain n) {k : ℕ} (hk : 0 < k) (hkn : k < n)
    (q : Fin (n + 1)) :
    fderiv ℝ (fun e : Coefficients n => coefficientTransform e k) e ((Pi.single q (1 : ℝ) : Coefficients n)) =
      coefficientRawDerivative e k q := by
  have hEq : (fun z : Coefficients n => coefficientTransform z k) =ᶠ[𝓝 e]
      (fun z => coefficientExpansion z k) := by
    filter_upwards [(isOpen_positiveCoefficientDomain n).mem_nhds he] with z hz
    exact coefficientTransform_eq_expansion hz hk hkn
  rw [hEq.fderiv_eq]
  have hd (l j : Fin (n + 1)) : DifferentiableAt ℝ (fun z : Coefficients n =>
      if l.val < k ∧ k ≤ j.val then ((j.val : ℝ) - l.val) * z l * z j *
        mellinMoment z (2 * (l.val : ℝ) + 2 * j.val - k) else 0) e := by
    by_cases hc : l.val < k ∧ k ≤ j.val
    · simp only [hc, true_and, and_true, if_true]
      have hm := (hasFDerivAt_coefficientMellinPower he
        (cut_moment_range hk hkn hc.1 hc.2).1
        (by nlinarith [(cut_moment_range hk hkn hc.1 hc.2).2] :
          2 * (l.val : ℝ) + 2 * j.val - k < 2 * n * (3 / 2 : ℝ))).differentiableAt
      exact (((hasFDerivAt_apply (𝕜 := ℝ) l e).differentiableAt.const_mul _).fun_mul
        (hasFDerivAt_apply (𝕜 := ℝ) j e).differentiableAt).fun_mul hm
    · simp only [hc, if_false]
      exact differentiableAt_const _
  unfold coefficientExpansion coefficientRawDerivative
  rw [fderiv_fun_sum (fun l _ => DifferentiableAt.fun_sum (fun j _ => hd l j))]
  simp only [ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro l hl
  rw [fderiv_fun_sum (fun j _ => hd l j)]
  simp only [ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hc : l.val < k ∧ k ≤ j.val
  · simp only [hc, true_and, and_true, if_true]
    exact fderiv_mellin_product_single he l j q _
      (cut_moment_range hk hkn hc.1 hc.2).1 (cut_moment_range hk hkn hc.1 hc.2).2
  · simp [hc]

theorem coefficientRawDerivative_split {n : ℕ} (e : Coefficients n) (k : ℕ)
    (q : Fin (n + 1)) :
    coefficientRawDerivative e k q =
      (∑ l : Fin (n + 1), ∑ j : Fin (n + 1), if l.val < k ∧ k ≤ j.val then
        ((j.val : ℝ) - l.val) * ((Pi.single q (1 : ℝ) : Coefficients n) l * e j + e l * (Pi.single q (1 : ℝ) : Coefficients n) j) *
          mellinMoment e (2 * (l.val : ℝ) + 2 * j.val - k) else 0) -
      (3 / 2 : ℝ) * ∑ l : Fin (n + 1), ∑ j : Fin (n + 1),
        if l.val < k ∧ k ≤ j.val then ((j.val : ℝ) - l.val) * e l * e j *
          coefficientMellinPower e (5 / 2) (2 * q.val - k + 2 * l.val + 2 * j.val) else 0 := by
  unfold coefficientRawDerivative
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hc : l.val < k ∧ k ≤ j.val
  · simp only [hc, true_and, and_true, if_true]
    rw [show 2 * (l.val : ℝ) + 2 * j.val - k + 2 * q.val =
      2 * (q.val : ℝ) - k + 2 * l.val + 2 * j.val by ring]
    ring
  · simp [hc]

theorem coefficientRawDerivative_head {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) {k : ℕ} (hk : 0 < k) (hkn : k < n)
    (q : Fin (n + 1)) (hq : k ≤ q.val) (hqn : q.val < n) :
    coefficientRawDerivative e k q =
      (1 / 2 : ℝ) * ∑ l : Fin (n + 1), if l.val < k then
        ((k : ℝ) - l.val) * e l * mellinMoment e (2 * q.val - k + 2 * l.val) else 0 := by
  have hr (l : Fin (n + 1)) (hl : l.val < k) :
      0 < 2 * (q.val : ℝ) - k + 2 * l.val ∧
        2 * (q.val : ℝ) - k + 2 * l.val < 3 * n := by
    have hl0 := Nat.cast_nonneg (α := ℝ) l.val
    have hkl : (l.val : ℝ) < k := by exact_mod_cast hl
    have hkq : (k : ℝ) ≤ q.val := by exact_mod_cast hq
    have hqnr : (q.val : ℝ) < n := by exact_mod_cast hqn
    have hkr : (0 : ℝ) < k := by exact_mod_cast hk
    have hknr : (k : ℝ) < n := by exact_mod_cast hkn
    constructor <;> linarith
  rw [coefficientRawDerivative_split, head_cross_mellin_reduction he k
    (2 * (q.val : ℝ) - k) (fun l hl => (hr l hl).1) (fun l hl => (hr l hl).2)]
  have hd : (∑ l : Fin (n + 1), ∑ j : Fin (n + 1), if l.val < k ∧ k ≤ j.val then
      ((j.val : ℝ) - l.val) * ((Pi.single q (1 : ℝ) : Coefficients n) l * e j + e l * (Pi.single q (1 : ℝ) : Coefficients n) j) *
        mellinMoment e (2 * (l.val : ℝ) + 2 * j.val - k) else 0) =
      ∑ l : Fin (n + 1), if l.val < k then ((q.val : ℝ) - l.val) * e l *
        mellinMoment e (2 * q.val - k + 2 * l.val) else 0 := by
    apply Finset.sum_congr rfl
    intro l hl
    by_cases hlk : l.val < k
    · have hlq : l ≠ q := by intro h; subst h; omega
      simp only [hlk, true_and, Pi.single_eq_of_ne hlq, zero_mul, zero_add]
      rw [Finset.sum_eq_single q]
      · simp [hq, show 2 * (l.val : ℝ) + 2 * q.val - k =
          2 * (q.val : ℝ) - k + 2 * l.val by ring]
      · intro j hj hjq
        simp [Pi.single_eq_of_ne hjq]
      · simp
    · simp [hlk]
  rw [hd, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  by_cases hlk : l.val < k <;> simp only [hlk, if_true, if_false, mul_zero, sub_zero] <;> ring

theorem coefficientRawDerivative_tail {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) {k : ℕ} (hk : 0 < k) (hkn : k < n)
    (q : Fin (n + 1)) (hq0 : 0 < q.val) (hq : q.val < k) :
    coefficientRawDerivative e k q =
      (1 / 2 : ℝ) * ∑ j : Fin (n + 1), if k < j.val then
        ((j.val : ℝ) - k) * e j * mellinMoment e (2 * q.val - k + 2 * j.val) else 0 := by
  have hr (j : Fin (n + 1)) (hj : k ≤ j.val) :
      0 < 2 * (q.val : ℝ) - k + 2 * j.val ∧
        2 * (q.val : ℝ) - k + 2 * j.val < 3 * n := by
    have hq0r : (0 : ℝ) < q.val := by exact_mod_cast hq0
    have hqk : (q.val : ℝ) < k := by exact_mod_cast hq
    have hkj : (k : ℝ) ≤ j.val := by exact_mod_cast hj
    have hjn : (j.val : ℝ) ≤ n := by exact_mod_cast Nat.le_of_lt_succ j.isLt
    have hknr : (k : ℝ) < n := by exact_mod_cast hkn
    constructor <;> linarith
  rw [coefficientRawDerivative_split, tail_cross_mellin_reduction he k
    (2 * (q.val : ℝ) - k) (fun j hj => (hr j hj).1) (fun j hj => (hr j hj).2)]
  have hd : (∑ l : Fin (n + 1), ∑ j : Fin (n + 1), if l.val < k ∧ k ≤ j.val then
      ((j.val : ℝ) - l.val) * ((Pi.single q (1 : ℝ) : Coefficients n) l * e j + e l * (Pi.single q (1 : ℝ) : Coefficients n) j) *
        mellinMoment e (2 * (l.val : ℝ) + 2 * j.val - k) else 0) =
      ∑ j : Fin (n + 1), if k ≤ j.val then ((j.val : ℝ) - q.val) * e j *
        mellinMoment e (2 * q.val - k + 2 * j.val) else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hjk : k ≤ j.val
    · have hjq : j ≠ q := by intro h; subst h; omega
      simp only [hjk, and_true, Pi.single_eq_of_ne hjq, mul_zero, add_zero]
      rw [Finset.sum_eq_single q]
      · simp [hq, show 2 * (q.val : ℝ) + 2 * j.val - k =
          2 * (q.val : ℝ) - k + 2 * j.val by ring]
      · intro l hl hlq
        simp [Pi.single_eq_of_ne hlq]
      · simp
    · simp [hjk]
  rw [hd, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rcases lt_trichotomy k j.val with hlt | heq | hgt
  · simp only [hlt, hlt.le, if_true]
    ring
  · simp [← heq]
    ring
  · simp [not_le.mpr hgt, not_lt.mpr hgt.le]

/-- The Jacobian formula is now identified with the derivative of the literal
improper integral. It is not an independently stipulated matrix. -/
theorem fderiv_coefficientTransform_single {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) (k q : Fin (n - 1)) :
    fderiv ℝ (fun e : Coefficients n => coefficientTransform e (k.val + 1)) e
      (Pi.single (⟨q.val + 1, by omega⟩ : Fin (n + 1)) 1) = coefficientJacobian e k q := by
  rw [fderiv_coefficientTransform_single_raw (admissible_mem_positiveCoefficientDomain he)
    (by omega) (by omega)]
  unfold coefficientJacobian
  dsimp only
  have hkbound := k.isLt
  have hqbound := q.isLt
  by_cases hkq : k ≤ q
  · rw [if_pos hkq, coefficientRawDerivative_head (k := k.val + 1) he
      (by omega) (by omega) (⟨q.val + 1, by omega⟩ : Fin (n + 1))
      (by change k.val + 1 ≤ q.val + 1; exact Nat.add_le_add_right hkq 1)
      (by change q.val + 1 < n; omega)]
  · rw [if_neg hkq, coefficientRawDerivative_tail (k := k.val + 1) he
      (by omega) (by omega) (⟨q.val + 1, by omega⟩ : Fin (n + 1))
      (by change 0 < q.val + 1; omega)
      (by change q.val + 1 < k.val + 1; exact Nat.add_lt_add_right (lt_of_not_ge hkq) 1)]

end EllipsoidVerification
