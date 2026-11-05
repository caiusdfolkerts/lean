module

public import Ellipsoid.AxisRationalIdentity
public import Ellipsoid.GeometricInvariance

@[expose] public section

noncomputable section

open MeasureTheory Set Polynomial Metric
open scoped BigOperators

namespace EllipsoidVerification

def axisHeadMellinIntegrand {n : ℕ} (a : Fin n → ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  ∑ i, (a i ^ 2 * elementaryOn (Finset.univ.erase i) (fun j => a j ^ 2) (k - 1)) *
    axisMellinIntegrand a k i t

def axisTailMellinIntegrand {n : ℕ} (a : Fin n → ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  ∑ i, (a i ^ 2 * elementaryOn (Finset.univ.erase i) (fun j => a j ^ 2) k) *
    axisMellinIntegrand a ((k : ℝ) + 2) i t

theorem axisHeadMellinIntegrand_eq {n : ℕ} (a : Fin n → ℝ) (k : ℕ) (t : ℝ) :
    axisHeadMellinIntegrand a k t =
      t ^ ((k : ℝ) - 1) * axisRational a k (t ^ 2) *
        coefficientPolynomial (axisCoefficients a) t ^ (-(1 / 2 : ℝ)) := by
  rw [axisHeadMellinIntegrand, axisRational, coefficientPolynomial_axisCoefficients,
    Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp [axisMellinIntegrand]
  ring

theorem axisTailMellinIntegrand_eq {n : ℕ} (a : Fin n → ℝ) (k : ℕ) (t : ℝ) :
    axisTailMellinIntegrand a k t =
      t ^ ((k : ℝ) + 1) * axisRational a (k + 1) (t ^ 2) *
        coefficientPolynomial (axisCoefficients a) t ^ (-(1 / 2 : ℝ)) := by
  rw [axisTailMellinIntegrand, axisRational, Nat.add_sub_cancel,
    coefficientPolynomial_axisCoefficients, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp [axisMellinIntegrand]
  rw [show (k : ℝ) + 2 - 1 = (k : ℝ) + 1 by ring]
  ring

theorem integrableOn_axisHeadMellinIntegrand {n k : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) (hk : 0 < k) (hkn : k < n) :
    IntegrableOn (axisHeadMellinIntegrand a k) (Ioi 0) := by
  exact integrable_finsetSum _ fun i _ => (integrableOn_axisMellinIntegrand ha
    (by exact_mod_cast hk) (by exact_mod_cast (show k < n + 2 by omega)) i).const_mul _

theorem integrableOn_axisTailMellinIntegrand {n k : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) (hk : 0 < k) (hkn : k < n) :
    IntegrableOn (axisTailMellinIntegrand a k) (Ioi 0) := by
  exact integrable_finsetSum _ fun i _ => (integrableOn_axisMellinIntegrand ha
    (by positivity) (by exact_mod_cast Nat.add_lt_add_right hkn 2) i).const_mul _

theorem coefficientTransform_eq_axisHeadIntegral {n k : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) (hk : 0 < k) (hkn : k ≤ n) :
    coefficientTransform (axisCoefficients a) k = ∫ t in Ioi (0 : ℝ), axisHeadMellinIntegrand a k t := by
  unfold coefficientTransform
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  rw [axisHeadMellinIntegrand_eq]
  exact coefficientTransform_integrand_axis ha hk hkn ht

theorem mellinBoundary_axis_rational {n k : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => t ^ (k : ℝ) *
      coefficientPolynomial (axisCoefficients a) t ^ (-(1 / 2 : ℝ)))
      (t ^ ((k : ℝ) - 1) * ((k : ℝ) - t ^ 2 * axisRational a 1 (t ^ 2)) *
        coefficientPolynomial (axisCoefficients a) t ^ (-(1 / 2 : ℝ))) t := by
  have hq := coefficientPolynomial_pos (axisCoefficients_admissible a ha) t
  have hD : coefficientDerivative (axisCoefficients a) t =
      2 * t * (coefficientPolynomial (axisCoefficients a) t * axisRational a 1 (t ^ 2)) := by
    rw [coefficientDerivative_axisCoefficients,
      axisCoefficientPolynomial_derivative_eval a (sq_nonneg t)]
    congr 2
    simp only [axisCoefficientPolynomial, coefficientPolynomial_axisCoefficients,
      Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_one,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  have hd := (Real.hasDerivAt_rpow_const (p := (k : ℝ)) (Or.inl ht.ne')).mul
    ((hasDerivAt_coefficientPolynomial (axisCoefficients a) t).rpow_const
      (p := -(1 / 2 : ℝ)) (Or.inl hq.ne'))
  convert hd using 1
  symm
  rw [hD]
  have htP : t ^ (k : ℝ) = t ^ ((k : ℝ) - 1) * t := by
    calc
      _ = t ^ ((k : ℝ) - 1) * t ^ (1 : ℝ) := by
        rw [← Real.rpow_add ht]
        congr 1
        ring
      _ = _ := by rw [Real.rpow_one]
  have hqP : coefficientPolynomial (axisCoefficients a) t ^ (-(1 / 2 : ℝ) - 1) *
      coefficientPolynomial (axisCoefficients a) t =
        coefficientPolynomial (axisCoefficients a) t ^ (-(1 / 2 : ℝ)) := by
    calc
      _ = coefficientPolynomial (axisCoefficients a) t ^ (-(1 / 2 : ℝ) - 1) *
          coefficientPolynomial (axisCoefficients a) t ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = _ := by
        rw [← Real.rpow_add hq]
        congr 1
        ring
  rw [htP]
  calc
    _ = (k : ℝ) * t ^ ((k : ℝ) - 1) * coefficientPolynomial (axisCoefficients a) t ^ (-(1 / 2 : ℝ)) -
      t ^ ((k : ℝ) - 1) * t ^ 2 * axisRational a 1 (t ^ 2) *
        (coefficientPolynomial (axisCoefficients a) t ^ (-(1 / 2 : ℝ) - 1) *
          coefficientPolynomial (axisCoefficients a) t) := by ring
    _ = _ := by rw [hqP]; ring

theorem axisHeadTail_integral_eq {n k : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) (hk : 0 < k) (hkn : k < n) :
    (∫ t in Ioi (0 : ℝ), axisHeadMellinIntegrand a k t) =
      ∫ t in Ioi (0 : ℝ), axisTailMellinIntegrand a k t := by
  let e := axisCoefficients a
  have he := axisCoefficients_admissible a ha
  have hi (j : Fin (n + 1)) : IntegrableOn (fun t : ℝ =>
      t ^ ((k : ℝ) + 2 * j.val - 1) * coefficientPolynomial e t ^ (-(3 / 2 : ℝ))) (Ioi 0) := by
    apply integrable_mellinMoment he
    · positivity
    · have hj : (j.val : ℝ) ≤ n := by exact_mod_cast Nat.le_of_lt_succ j.isLt
      have hkr : (k : ℝ) < n := by exact_mod_cast hkn
      linarith
  have hsum : (∫ t in Ioi (0 : ℝ), ∑ j : Fin (n + 1), ((k : ℝ) - j.val) * e j *
      (t ^ ((k : ℝ) + 2 * j.val - 1) * coefficientPolynomial e t ^ (-(3 / 2 : ℝ)))) = 0 := by
    rw [integral_finsetSum _ (fun j _ => (hi j).const_mul _)]
    simp only [integral_const_mul]
    have hrec := coefficientMellinPower_recurrence he
      (s := (1 / 2 : ℝ)) (r := (k : ℝ)) (by exact_mod_cast hk)
      (by
        have hkr : (k : ℝ) < n := by exact_mod_cast hkn
        push_cast
        nlinarith)
    norm_num [coefficientMellinPower] at hrec
    exact hrec
  have hpoint (t : ℝ) (ht : 0 < t) :
      axisHeadMellinIntegrand a k t - axisTailMellinIntegrand a k t =
      (axisCoefficientPolynomial a).coeff k *
        ∑ j : Fin (n + 1), ((k : ℝ) - j.val) * e j *
          (t ^ ((k : ℝ) + 2 * j.val - 1) * coefficientPolynomial e t ^ (-(3 / 2 : ℝ))) := by
    have hd := (mellinBoundary_axis_rational (k := k) ha ht).unique
      (mellinBoundary_derivative he (1 / 2) k ht)
    norm_num only [one_mul] at hd
    rw [axisHeadMellinIntegrand_eq, axisTailMellinIntegrand_eq, ← hd]
    have hpow : t ^ ((k : ℝ) + 1) = t ^ ((k : ℝ) - 1) * t ^ 2 := by
      rw [← Real.rpow_two, ← Real.rpow_add ht]
      congr 1
      ring
    rw [hpow]
    have hr := axisRational_recurrence a hk (sq_nonneg t)
    linear_combination -(t ^ ((k : ℝ) - 1) * coefficientPolynomial e t ^ (-(1 / 2 : ℝ))) * hr
  apply sub_eq_zero.mp
  rw [← integral_sub (integrableOn_axisHeadMellinIntegrand ha hk hkn)
    (integrableOn_axisTailMellinIntegrand ha hk hkn)]
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint, integral_const_mul, hsum, mul_zero]

def angularMellinConstant (n : ℕ) (β : ℝ) : ℝ :=
  2 * (Real.sqrt Real.pi) ^ n /
    (Real.Gamma (β / 2) * Real.Gamma (((n : ℝ) + 2 - β) / 2))

theorem sphere_axisA_eq_headMellin {n k : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) (hk : 0 < k) (hkn : k < n) :
    (∫ u : sphere (0 : Space n) 1, axisA a k u / axisSupport a u ^ k ∂volume.toSphere) =
      angularMellinConstant n k * ∫ t in Ioi (0 : ℝ), axisHeadMellinIntegrand a k t := by
  have hs (i : Fin n) := integrable_sphere_of_continuousOn_compl_zero
    (continuousOn_axisAngularFunction ha (k : ℝ) i)
  have hi (i : Fin n) := integrableOn_axisMellinIntegrand (β := (k : ℝ)) ha (by exact_mod_cast hk)
    (by exact_mod_cast (show k < n + 2 by omega)) i
  have hp (u : sphere (0 : Space n) 1) :
      axisA a k u / axisSupport a u ^ k =
        ∑ i, (a i ^ 2 * elementaryOn (Finset.univ.erase i) (fun j => a j ^ 2) (k - 1)) *
          axisAngularFunction a k i u := by
    have hu : 0 ≤ axisSupport a u := norm_nonneg _
    simp only [axisA, Finset.sum_div, axisAngularFunction, Real.rpow_neg hu,
      Real.rpow_natCast, div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  simp_rw [hp]
  rw [integral_finsetSum _ (fun i _ => (hs i).const_mul _)]
  simp only [integral_const_mul]
  simp_rw [sphere_axisAngularFunction_eq_mellin (β := (k : ℝ)) ha (by exact_mod_cast hk)
    (by exact_mod_cast (show k < n + 2 by omega))]
  simp only [axisHeadMellinIntegrand]
  rw [integral_finsetSum _ (fun i _ => (hi i).const_mul _)]
  simp only [integral_const_mul, angularMellinConstant, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem sphere_axisC_eq_tailMellin {n k : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) (hk : 0 < k) (hkn : k < n) :
    (∫ u : sphere (0 : Space n) 1, axisC a k u / axisSupport a u ^ (k + 2) ∂volume.toSphere) =
      angularMellinConstant n ((k : ℝ) + 2) * ∫ t in Ioi (0 : ℝ), axisTailMellinIntegrand a k t := by
  have hs (i : Fin n) := integrable_sphere_of_continuousOn_compl_zero
    (continuousOn_axisAngularFunction ha ((k : ℝ) + 2) i)
  have hi (i : Fin n) := integrableOn_axisMellinIntegrand (β := (k : ℝ) + 2) ha (by positivity)
    (by exact_mod_cast Nat.add_lt_add_right hkn 2) i
  have hp (u : sphere (0 : Space n) 1) :
      axisC a k u / axisSupport a u ^ (k + 2) =
        ∑ i, (a i ^ 2 * elementaryOn (Finset.univ.erase i) (fun j => a j ^ 2) k) *
          axisAngularFunction a ((k : ℝ) + 2) i u := by
    have hu : 0 ≤ axisSupport a u := norm_nonneg _
    have hpow : axisSupport a u ^ ((k : ℝ) + 2) = axisSupport a u ^ (k + 2) := by
      rw [show (k : ℝ) + 2 = ((k + 2 : ℕ) : ℝ) by simp only [Nat.cast_add, Nat.cast_ofNat],
        Real.rpow_natCast]
    simp only [axisC, Finset.sum_div, axisAngularFunction, Real.rpow_neg hu,
      hpow, div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  simp_rw [hp]
  rw [integral_finsetSum _ (fun i _ => (hs i).const_mul _)]
  simp only [integral_const_mul]
  simp_rw [sphere_axisAngularFunction_eq_mellin (β := (k : ℝ) + 2) ha (by positivity)
    (by exact_mod_cast Nat.add_lt_add_right hkn 2)]
  simp only [axisTailMellinIntegrand]
  rw [integral_finsetSum _ (fun i _ => (hi i).const_mul _)]
  simp only [integral_const_mul, angularMellinConstant, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end EllipsoidVerification
