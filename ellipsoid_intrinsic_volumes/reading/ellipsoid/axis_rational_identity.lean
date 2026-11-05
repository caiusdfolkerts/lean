module

public import Ellipsoid.AngularMellin
public import Ellipsoid.MellinIntegrationByParts
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

@[expose] public section

noncomputable section

open MeasureTheory Set Polynomial
open scoped BigOperators

namespace EllipsoidVerification

def axisRational {n : ℕ} (a : Fin n → ℝ) (k : ℕ) (u : ℝ) : ℝ :=
  ∑ i, a i ^ 2 * elementaryOn (Finset.univ.erase i) (fun j => a j ^ 2) (k - 1) /
    (1 + a i ^ 2 * u)

def axisHeadPolynomial {n : ℕ} (a : Fin n → ℝ) (k : ℕ) : ℝ[X] :=
  ∑ l ∈ Finset.range k, C ((axisCoefficientPolynomial a).coeff l) * X ^ l

theorem elementaryOn_zero {ι : Type*} (s : Finset ι) (d : ι → ℝ) :
    elementaryOn s d 0 = 1 := by
  simp [elementaryOn, Polynomial.coeff_zero_prod]

theorem axisRational_one {n : ℕ} (a : Fin n → ℝ) (u : ℝ) :
    axisRational a 1 u = ∑ i, a i ^ 2 / (1 + a i ^ 2 * u) := by
  simp [axisRational, elementaryOn_zero]

theorem axisRational_recurrence {n k : ℕ} (a : Fin n → ℝ) (hk : 0 < k)
    {u : ℝ} (hu : 0 ≤ u) :
    u * axisRational a (k + 1) u - axisRational a k u =
      (axisCoefficientPolynomial a).coeff k * (u * axisRational a 1 u - k) := by
  let e := elementaryOn Finset.univ (fun i => a i ^ 2) k
  have hden (i : Fin n) : 1 + a i ^ 2 * u ≠ 0 := by positivity
  have heach (i : Fin n) :
      u * (a i ^ 2 * elementaryOn (Finset.univ.erase i) (fun j => a j ^ 2) k /
        (1 + a i ^ 2 * u)) -
      a i ^ 2 * elementaryOn (Finset.univ.erase i) (fun j => a j ^ 2) (k - 1) /
        (1 + a i ^ 2 * u) =
      e * u * (a i ^ 2 / (1 + a i ^ 2 * u)) -
        a i ^ 2 * elementaryOn (Finset.univ.erase i) (fun j => a j ^ 2) (k - 1) := by
    dsimp [e]
    rw [elementaryOn_erase Finset.univ (fun j => a j ^ 2) (Finset.mem_univ i) hk]
    field_simp [hden i]
    ring
  rw [axisRational, axisRational, Nat.add_sub_cancel, Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp_rw [heach]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, elementaryOn_euler _ _ hk, axisRational_one]
  change e * u * _ - (k : ℝ) * e = e * (u * _ - k)
  ring

theorem axisHeadPolynomial_succ {n : ℕ} (a : Fin n → ℝ) (k : ℕ) :
    axisHeadPolynomial a (k + 1) = axisHeadPolynomial a k +
      C ((axisCoefficientPolynomial a).coeff k) * X ^ k := by
  exact Finset.sum_range_succ _ _

theorem axisHeadPolynomial_wronskian {n k : ℕ} (a : Fin n → ℝ) {u : ℝ} (hu : 0 ≤ u) :
    u ^ k * axisRational a (k + 1) u =
      (axisHeadPolynomial a (k + 1)).eval u * axisRational a 1 u -
        (axisHeadPolynomial a (k + 1)).derivative.eval u := by
  induction k with
  | zero =>
      simp [axisHeadPolynomial, axisCoefficientPolynomial, Polynomial.coeff_zero_prod]
  | succ k ih =>
      have hr := axisRational_recurrence a (k := k + 1) (by omega) hu
      rw [axisHeadPolynomial_succ a (k + 1)]
      simp only [Polynomial.eval_add,
        Polynomial.derivative_add, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.derivative_C_mul, Polynomial.derivative_X_pow,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ] at hr ⊢
      linear_combination u ^ k * hr + ih

theorem axisCoefficientPolynomial_derivative_eval {n : ℕ} (a : Fin n → ℝ)
    {u : ℝ} (hu : 0 ≤ u) :
    (axisCoefficientPolynomial a).derivative.eval u =
      (axisCoefficientPolynomial a).eval u * axisRational a 1 u := by
  have hden (i : Fin n) : 1 + a i ^ 2 * u ≠ 0 := by positivity
  rw [axisCoefficientPolynomial, Polynomial.derivative_prod_finset,
    Polynomial.eval_finsetSum, Polynomial.eval_prod, axisRational_one, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.derivative_add,
    Polynomial.derivative_one, Polynomial.derivative_C_mul, Polynomial.derivative_X,
    mul_one, zero_add, Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_one,
    Polynomial.eval_X]
  rw [← Finset.mul_prod_erase Finset.univ (fun j => 1 + a j ^ 2 * u) (Finset.mem_univ i)]
  field_simp [hden i]
  simp_rw [mul_comm u]
  ring

theorem coefficientHead_axisCoefficients {n k : ℕ} (a : Fin n → ℝ) (hk : k ≤ n + 1) (t : ℝ) :
    coefficientHead (axisCoefficients a) k t = (axisHeadPolynomial a k).eval (t ^ 2) := by
  simp only [coefficientHead, axisCoefficients, axisHeadPolynomial,
    Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, ← pow_mul]
  rw [Fin.sum_univ_eq_sum_range (fun l : ℕ =>
    if l < k then (axisCoefficientPolynomial a).coeff l * t ^ (2 * l) else 0) (n + 1)]
  have hsub : Finset.range k ⊆ Finset.range (n + 1) := Finset.range_mono hk
  rw [← Finset.sum_subset hsub]
  · apply Finset.sum_congr rfl
    intro l hl
    simp [Finset.mem_range.mp hl]
  · intro l hl hlk
    simp [show ¬ l < k from fun h => hlk (Finset.mem_range.mpr h)]

theorem hasDerivAt_coefficientHead {n : ℕ} (e : Coefficients n) (k : ℕ) (t : ℝ) :
    HasDerivAt (coefficientHead e k) (coefficientHeadDerivative e k t) t := by
  unfold coefficientHead coefficientHeadDerivative
  apply HasDerivAt.fun_sum
  intro l hl
  by_cases h : l.val < k
  · simp only [h, if_true]
    simpa only [Pi.pow_apply, id_eq, mul_one, one_mul, Nat.cast_mul, Nat.cast_ofNat,
      mul_assoc, mul_left_comm, mul_comm] using
      ((hasDerivAt_id t).pow (2 * l.val)).const_mul (e l)
  · simp only [h, if_false]
    exact hasDerivAt_const t 0

theorem coefficientDerivative_axisCoefficients {n : ℕ} (a : Fin n → ℝ) (t : ℝ) :
    coefficientDerivative (axisCoefficients a) t =
      2 * t * (axisCoefficientPolynomial a).derivative.eval (t ^ 2) := by
  have hp : coefficientPolynomial (axisCoefficients a) =
      fun z => (axisCoefficientPolynomial a).eval (z ^ 2) := by
    funext z
    rw [coefficientPolynomial_axisCoefficients]
    simp only [axisCoefficientPolynomial, Polynomial.eval_prod, Polynomial.eval_add,
      Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  have h := ((axisCoefficientPolynomial a).hasDerivAt (t ^ 2)).comp t
    ((hasDerivAt_id t).pow 2)
  have h₀ : HasDerivAt (fun z : ℝ => (axisCoefficientPolynomial a).eval (z ^ 2))
      ((axisCoefficientPolynomial a).derivative.eval (t ^ 2) * (2 * t)) t := by
    simpa only [Function.comp_def, Pi.pow_apply, id_eq, Nat.cast_ofNat,
      show (2 : ℕ) - 1 = 1 from rfl, pow_one, mul_one] using h
  have h' := hasDerivAt_coefficientPolynomial (axisCoefficients a) t
  rw [hp] at h'
  calc
    _ = (axisCoefficientPolynomial a).derivative.eval (t ^ 2) * (2 * t) := h'.unique h₀
    _ = _ := by ring

theorem coefficientHeadDerivative_axisCoefficients {n k : ℕ} (a : Fin n → ℝ)
    (hk : k ≤ n + 1) (t : ℝ) :
    coefficientHeadDerivative (axisCoefficients a) k t =
      2 * t * (axisHeadPolynomial a k).derivative.eval (t ^ 2) := by
  have h := ((axisHeadPolynomial a k).hasDerivAt (t ^ 2)).comp t
    ((hasDerivAt_id t).pow 2)
  have h₀ : HasDerivAt (fun z : ℝ => (axisHeadPolynomial a k).eval (z ^ 2))
      ((axisHeadPolynomial a k).derivative.eval (t ^ 2) * (2 * t)) t := by
    simpa only [Function.comp_def, Pi.pow_apply, id_eq, Nat.cast_ofNat,
      show (2 : ℕ) - 1 = 1 from rfl, pow_one, mul_one] using h
  have hp : coefficientHead (axisCoefficients a) k =
      fun z => (axisHeadPolynomial a k).eval (z ^ 2) := by
    funext z
    exact coefficientHead_axisCoefficients a hk z
  have h' := hasDerivAt_coefficientHead (axisCoefficients a) k t
  rw [hp] at h'
  calc
    _ = (axisHeadPolynomial a k).derivative.eval (t ^ 2) * (2 * t) := h'.unique h₀
    _ = _ := by ring

theorem coefficientTransform_integrand_axis {n k : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) (hk : 0 < k) (hkn : k ≤ n) {t : ℝ} (ht : 0 < t) :
    (1 / 2 : ℝ) * t ^ (-(k : ℝ)) *
      (coefficientHead (axisCoefficients a) k t * coefficientDerivative (axisCoefficients a) t -
        coefficientHeadDerivative (axisCoefficients a) k t * coefficientPolynomial (axisCoefficients a) t) *
      coefficientPolynomial (axisCoefficients a) t ^ (-(3 / 2 : ℝ)) =
      t ^ ((k : ℝ) - 1) * axisRational a k (t ^ 2) *
        coefficientPolynomial (axisCoefficients a) t ^ (-(1 / 2 : ℝ)) := by
  have hq := coefficientPolynomial_pos (axisCoefficients_admissible a ha) t
  have hQ : (axisCoefficientPolynomial a).eval (t ^ 2) =
      coefficientPolynomial (axisCoefficients a) t := by
    simp only [coefficientPolynomial_axisCoefficients, axisCoefficientPolynomial,
      Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]
  have hW := axisHeadPolynomial_wronskian (k := k - 1) a (sq_nonneg t)
  rw [Nat.sub_add_cancel hk] at hW
  rw [coefficientHead_axisCoefficients a (by omega), coefficientDerivative_axisCoefficients,
    coefficientHeadDerivative_axisCoefficients a (by omega),
    axisCoefficientPolynomial_derivative_eval a (sq_nonneg t), hQ]
  have hwronskian :
      (axisHeadPolynomial a k).eval (t ^ 2) *
          (2 * t * (coefficientPolynomial (axisCoefficients a) t * axisRational a 1 (t ^ 2))) -
        (2 * t * (axisHeadPolynomial a k).derivative.eval (t ^ 2)) *
          coefficientPolynomial (axisCoefficients a) t =
      2 * t * coefficientPolynomial (axisCoefficients a) t *
        ((t ^ 2) ^ (k - 1) * axisRational a k (t ^ 2)) := by
    rw [hW]
    ring
  rw [hwronskian]
  have htPow : t ^ (-(k : ℝ)) * t * (t ^ 2) ^ (k - 1) = t ^ ((k : ℝ) - 1) := by
    have hnat : (t ^ 2) ^ (k - 1) = t ^ ((2 : ℝ) * ((k - 1 : ℕ) : ℝ)) := by
      calc
        _ = (t ^ (2 : ℕ)) ^ ((k - 1 : ℕ) : ℝ) :=
          (Real.rpow_natCast (t ^ (2 : ℕ)) (k - 1)).symm
        _ = _ := (Real.rpow_natCast_mul ht.le 2 ((k - 1 : ℕ) : ℝ)).symm
    calc
      _ = (t ^ (-(k : ℝ)) * t ^ (1 : ℝ)) *
          t ^ ((2 : ℝ) * ((k - 1 : ℕ) : ℝ)) := by rw [hnat, Real.rpow_one]
      _ = t ^ (-(k : ℝ) + 1 + 2 * ((k - 1 : ℕ) : ℝ)) := by
        rw [← Real.rpow_add ht, ← Real.rpow_add ht]
      _ = _ := by
        congr 1
        rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
        ring
  have hqPow : coefficientPolynomial (axisCoefficients a) t *
      coefficientPolynomial (axisCoefficients a) t ^ (-(3 / 2 : ℝ)) =
      coefficientPolynomial (axisCoefficients a) t ^ (-(1 / 2 : ℝ)) := by
    calc
      _ = coefficientPolynomial (axisCoefficients a) t ^ (1 : ℝ) *
          coefficientPolynomial (axisCoefficients a) t ^ (-(3 / 2 : ℝ)) := by
        rw [Real.rpow_one]
      _ = coefficientPolynomial (axisCoefficients a) t ^ ((1 : ℝ) + -(3 / 2 : ℝ)) :=
        (Real.rpow_add hq 1 (-(3 / 2 : ℝ))).symm
      _ = _ := by norm_num
  calc
    _ = (t ^ (-(k : ℝ)) * t * (t ^ 2) ^ (k - 1)) * axisRational a k (t ^ 2) *
      (coefficientPolynomial (axisCoefficients a) t *
        coefficientPolynomial (axisCoefficients a) t ^ (-(3 / 2 : ℝ))) := by ring
    _ = _ := by rw [htPow, hqPow]

end EllipsoidVerification
