module

public import ellipsoid.verified.main02
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/- Generated ordinary proof stage. See audit/staged_ellipsoid_main/Main03/manifest.json. -/

@[expose] public section

section CanonicalSource20
/- Source: Ellipsoid/GSZFormula.lean -/



noncomputable section

open MeasureTheory Set Polynomial Metric
open scoped BigOperators

namespace EllipsoidVerification

theorem angularMellinConstants_sum {n k : ℕ} (hk : 0 < k) (hkn : k < n) :
    angularMellinConstant n k + angularMellinConstant n ((k : ℝ) + 2) =
      (n : ℝ) * unitBallVolume (n - k) * unitBallVolume k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hknR : (k : ℝ) < n := by exact_mod_cast hkn
  have hnkR : 0 < (n : ℝ) - k := sub_pos.mpr hknR
  have hgk := (Real.Gamma_pos_of_pos (half_pos hkR)).ne'
  have hgnk := (Real.Gamma_pos_of_pos (half_pos hnkR)).ne'
  rw [angularMellinConstant, angularMellinConstant, unitBallVolume_eq, unitBallVolume_eq,
    Nat.cast_sub hkn.le]
  rw [show ((n : ℝ) + 2 - k) / 2 = ((n : ℝ) - k) / 2 + 1 by ring,
    show ((k : ℝ) + 2) / 2 = (k : ℝ) / 2 + 1 by ring,
    show ((n : ℝ) + 2 - ((k : ℝ) + 2)) / 2 = ((n : ℝ) - k) / 2 by ring,
    Real.Gamma_add_one (half_pos hkR).ne', Real.Gamma_add_one (half_pos hnkR).ne']
  field_simp [hgk, hgnk, hkR.ne', hnkR.ne']
  rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hkn.le]
  ring

theorem integrable_sphere_axisA {n k : ℕ} {a : Fin n → ℝ} (ha : ∀ i, 0 < a i) :
    Integrable (fun u : sphere (0 : Space n) 1 => axisA a k u / axisSupport a u ^ k)
      volume.toSphere := by
  have hc : Continuous (fun u : sphere (0 : Space n) 1 => axisA a k u / axisSupport a u ^ k) := by
    apply Continuous.div
    · unfold axisA
      fun_prop
    · exact ((continuous_axisSupport a).comp continuous_subtype_val).pow k
    · intro u
      exact pow_ne_zero _ (axisSupport_pos ha (by
        intro h; simpa [h] using u.property)).ne'
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem integrable_sphere_axisC {n k : ℕ} {a : Fin n → ℝ} (ha : ∀ i, 0 < a i) :
    Integrable (fun u : sphere (0 : Space n) 1 => axisC a k u / axisSupport a u ^ (k + 2))
      volume.toSphere := by
  have hc : Continuous (fun u : sphere (0 : Space n) 1 => axisC a k u / axisSupport a u ^ (k + 2)) := by
    apply Continuous.div
    · unfold axisC
      fun_prop
    · exact ((continuous_axisSupport a).comp continuous_subtype_val).pow (k + 2)
    · intro u
      exact pow_ne_zero _ (axisSupport_pos ha (by
        intro h; simpa [h] using u.property)).ne'
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The GSZ geometric integral formula, derived here from the actual Steiner
polynomial, its normal-map Jacobian, Gaussian integrals, and Mellin integration
by parts. The right side is the literal coefficient integral from the paper. -/
theorem intrinsicVolume_axisBody_eq_coefficientTransform {n k : ℕ}
    {a : Fin n → ℝ} (ha : ∀ i, 0 < a i) (hk : 0 < k) (hkn : k < n) :
    intrinsicVolume (axisBody a) k =
      unitBallVolume k * coefficientTransform (axisCoefficients a) k := by
  rw [intrinsicVolume_axisBody_eq_sphere (by omega) ha hk hkn.le,
    integral_add (integrable_sphere_axisA ha) (integrable_sphere_axisC ha),
    sphere_axisA_eq_headMellin ha hk hkn, sphere_axisC_eq_tailMellin ha hk hkn,
    ← axisHeadTail_integral_eq ha hk hkn, ← add_mul, angularMellinConstants_sum hk hkn,
    coefficientTransform_eq_axisHeadIntegral ha hk hkn.le]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp [hnR, (unitBallVolume_pos (n - k)).ne']

theorem FullEllipsoid.volume_eq_coefficientTransform {n k : ℕ} (E : FullEllipsoid n)
    (hk : 0 < k) (hkn : k < n) :
    E.volume k = unitBallVolume k * coefficientTransform (axisCoefficients E.semiaxis) k := by
  rw [E.volume_eq_axes]
  exact intrinsicVolume_axisBody_eq_coefficientTransform E.semiaxis_pos hk hkn

end EllipsoidVerification
end
end CanonicalSource20

section CanonicalSource21
/- Source: Ellipsoid/CoefficientExpansion.lean -/



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
end
end CanonicalSource21

section CanonicalSource22
/- Source: Ellipsoid/MellinShiftIdentities.lean -/



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
end
end CanonicalSource22

section CanonicalSource23
/- Source: Ellipsoid/PowerTilts.lean -/



noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace EllipsoidVerification

abbrev PositiveLine := {t : ℝ // 0 < t}

def positiveMoment (μ : Measure PositiveLine) (r : ℝ) : ℝ :=
  ∫ t, (t.val : ℝ) ^ r ∂μ

def powerTilt (μ : Measure PositiveLine) (r : ℝ) : Measure PositiveLine :=
  (ENNReal.ofReal (positiveMoment μ r))⁻¹ •
    μ.withDensity (fun t => ENNReal.ofReal ((t.val : ℝ) ^ r))

@[fun_prop] theorem measurable_positive_power (r : ℝ) :
    Measurable (fun t : PositiveLine => (t.val : ℝ) ^ r) := by fun_prop

theorem positiveMoment_pos {μ : Measure PositiveLine} (hμ : μ ≠ 0) {r : ℝ}
    (hr : Integrable (fun t : PositiveLine => (t.val : ℝ) ^ r) μ) :
    0 < positiveMoment μ r := by
  rw [positiveMoment, integral_pos_iff_support_of_nonneg
    (fun t => (Real.rpow_pos_of_pos t.property r).le) hr]
  have hs : Function.support (fun t : PositiveLine => (t.val : ℝ) ^ r) = univ := by
    ext t
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (Real.rpow_pos_of_pos t.property r).ne'
  rw [hs]
  exact Measure.measure_univ_pos.mpr hμ

theorem powerTilt_probability {μ : Measure PositiveLine} (hμ : μ ≠ 0) {r : ℝ}
    (hr : Integrable (fun t : PositiveLine => (t.val : ℝ) ^ r) μ) :
    IsProbabilityMeasure (powerTilt μ r) := by
  have hm := positiveMoment_pos hμ hr
  constructor
  simp only [powerTilt, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, smul_eq_mul]
  rw [← ofReal_integral_eq_lintegral_ofReal hr (ae_of_all _ fun t =>
    (Real.rpow_pos_of_pos t.property r).le)]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hm).ne' ENNReal.ofReal_ne_top

theorem integral_powerTilt {μ : Measure PositiveLine} {r : ℝ}
    (hr : Integrable (fun t : PositiveLine => (t.val : ℝ) ^ r) μ)
    (f : PositiveLine → ℝ) :
    (∫ t, f t ∂powerTilt μ r) =
      (∫ t, (t.val : ℝ) ^ r * f t ∂μ) / positiveMoment μ r := by
  have hm : 0 ≤ positiveMoment μ r :=
    integral_nonneg fun t => (Real.rpow_pos_of_pos t.property r).le
  rw [powerTilt, integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul (measurable_positive_power r).ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top), ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hm]
  simp only [ENNReal.toReal_ofReal (Real.rpow_pos_of_pos (Subtype.property _) r).le,
    smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem integrable_powerTilt_power {μ : Measure PositiveLine} (hμ : μ ≠ 0)
    {r a : ℝ} (hr : Integrable (fun t : PositiveLine => (t.val : ℝ) ^ r) μ)
    (hra : Integrable (fun t : PositiveLine => (t.val : ℝ) ^ (r + a)) μ) :
    Integrable (fun t : PositiveLine => (t.val : ℝ) ^ a) (powerTilt μ r) := by
  have hm := positiveMoment_pos hμ hr
  rw [powerTilt, integrable_smul_measure
    (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)
    (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hm).ne')]
  rw [integrable_withDensity_iff_integrable_smul' (measurable_positive_power r).ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  convert hra using 1
  funext t
  rw [ENNReal.toReal_ofReal (Real.rpow_pos_of_pos t.property r).le, smul_eq_mul,
    ← Real.rpow_add t.property]

theorem positiveMoment_powerTilt {μ : Measure PositiveLine} {r a : ℝ}
    (hr : Integrable (fun t : PositiveLine => (t.val : ℝ) ^ r) μ) :
    positiveMoment (powerTilt μ r) a = positiveMoment μ (r + a) / positiveMoment μ r := by
  rw [positiveMoment, integral_powerTilt hr]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun t => (Real.rpow_add t.property r a).symm

def reciprocalTail (μ : Measure PositiveLine) (r s : ℝ) : ℝ :=
  (powerTilt μ r {t | s < (t.val : ℝ)⁻¹}).toReal

theorem reciprocalTail_nonneg (μ : Measure PositiveLine) (r s : ℝ) :
    0 ≤ reciprocalTail μ r s := ENNReal.toReal_nonneg

theorem reciprocalTail_antitone {μ : Measure PositiveLine} {r : ℝ}
    [IsFiniteMeasure (powerTilt μ r)] : Antitone (reciprocalTail μ r) := by
  intro s t hst
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  exact measure_mono fun x hx => lt_of_le_of_lt hst hx

@[fun_prop] theorem measurable_reciprocalTail {μ : Measure PositiveLine} {r : ℝ}
    [IsFiniteMeasure (powerTilt μ r)] : Measurable (reciprocalTail μ r) :=
  reciprocalTail_antitone.measurable

theorem reciprocalTail_le_one {μ : Measure PositiveLine} {r : ℝ}
    [IsProbabilityMeasure (powerTilt μ r)] (s : ℝ) : reciprocalTail μ r s ≤ 1 := by
  have h : powerTilt μ r {t : PositiveLine | s < (t.val : ℝ)⁻¹} ≤
      powerTilt μ r univ :=
    measure_mono (Set.subset_univ {t : PositiveLine | s < (t.val : ℝ)⁻¹})
  rw [measure_univ] at h
  simpa only [reciprocalTail, ENNReal.toReal_one] using
    ENNReal.toReal_mono ENNReal.one_ne_top h

/-- The exact two-by-two determinant behind ordering of power tilts. -/
theorem power_likelihood_cross {x y a b : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (hab : a ≤ b) : x ^ b * y ^ a ≤ x ^ a * y ^ b := by
  have hy : 0 < y := hx.trans_le hxy
  have hpow := Real.rpow_le_rpow hx.le hxy (sub_nonneg.mpr hab)
  have heq : b = a + (b - a) := by ring
  rw [heq, Real.rpow_add hx, Real.rpow_add hy]
  convert mul_le_mul_of_nonneg_left hpow (mul_nonneg
    (Real.rpow_pos_of_pos hx a).le (Real.rpow_pos_of_pos hy a).le) using 1 <;> ring

/-- The unnormalized lower-tail inequality, valid even if the underlying
measure has infinite mass. Only the two displayed moments are needed. -/
theorem restricted_power_moment_cross {μ : Measure PositiveLine} [SFinite μ]
    {a b : ℝ} (hab : a ≤ b)
    (ha : Integrable (fun t : PositiveLine => (t.val : ℝ) ^ a) μ)
    (hb : Integrable (fun t : PositiveLine => (t.val : ℝ) ^ b) μ) (c : ℝ) :
    (∫ t in {t : PositiveLine | t.val < c}, (t.val : ℝ) ^ b ∂μ) * positiveMoment μ a ≤
      (∫ t in {t : PositiveLine | t.val < c}, (t.val : ℝ) ^ a ∂μ) * positiveMoment μ b := by
  let S : Set PositiveLine := {t | t.val < c}
  have hS : MeasurableSet S := measurableSet_lt measurable_subtype_coe measurable_const
  have hcross :
      (∫ x in S, (x.val : ℝ) ^ b ∂μ) * (∫ y in Sᶜ, (y.val : ℝ) ^ a ∂μ) ≤
      (∫ x in S, (x.val : ℝ) ^ a ∂μ) * (∫ y in Sᶜ, (y.val : ℝ) ^ b ∂μ) := by
    rw [← integral_prod_mul, ← integral_prod_mul]
    apply integral_mono_ae ((hb.restrict (s := S)).mul_prod (ha.restrict (s := Sᶜ)))
      ((ha.restrict (s := S)).mul_prod (hb.restrict (s := Sᶜ)))
    change ∀ᵐ z : PositiveLine × PositiveLine ∂(μ.restrict S).prod (μ.restrict Sᶜ),
      (z.1.val : ℝ) ^ b * (z.2.val : ℝ) ^ a ≤
        (z.1.val : ℝ) ^ a * (z.2.val : ℝ) ^ b
    apply (Measure.ae_prod_iff_ae_ae
      (p := fun z : PositiveLine × PositiveLine =>
        (z.1.val : ℝ) ^ b * (z.2.val : ℝ) ^ a ≤
          (z.1.val : ℝ) ^ a * (z.2.val : ℝ) ^ b)
      (measurableSet_le (by fun_prop) (by fun_prop))).2
    filter_upwards [self_mem_ae_restrict hS] with x hx
    filter_upwards [self_mem_ae_restrict hS.compl] with y hy
    have hxy : x.val ≤ y.val := by
      have hx' : x.val < c := hx
      have hy' : c ≤ y.val := le_of_not_gt hy
      exact hx'.le.trans hy'
    exact power_likelihood_cross x.property hxy hab
  have haSum := integral_add_compl hS ha
  have hbSum := integral_add_compl hS hb
  dsimp [positiveMoment]
  rw [← haSum, ← hbSum]
  nlinarith

theorem reciprocalTail_antitone_exponent {μ : Measure PositiveLine} [SFinite μ]
    (hμ : μ ≠ 0) {a b : ℝ} (hab : a ≤ b)
    (ha : Integrable (fun t : PositiveLine => (t.val : ℝ) ^ a) μ)
    (hb : Integrable (fun t : PositiveLine => (t.val : ℝ) ^ b) μ) (s : ℝ) :
    reciprocalTail μ b s ≤ reciprocalTail μ a s := by
  letI := powerTilt_probability hμ ha
  letI := powerTilt_probability hμ hb
  by_cases hs : 0 < s
  · let S : Set PositiveLine := {t | t.val < s⁻¹}
    have hS : MeasurableSet S := measurableSet_lt measurable_subtype_coe measurable_const
    have hset : {t : PositiveLine | s < (t.val : ℝ)⁻¹} = S := by
      ext t
      exact (lt_inv_comm₀ hs t.property)
    have htail (r : ℝ) (hr : Integrable (fun t : PositiveLine => (t.val : ℝ) ^ r) μ) :
        reciprocalTail μ r s = (∫ t in S, (t.val : ℝ) ^ r ∂μ) / positiveMoment μ r := by
      have h := integral_powerTilt hr (S.indicator (fun _ => (1 : ℝ)))
      rw [integral_indicator hS, integral_const] at h
      have hind : (fun t : PositiveLine => (t.val : ℝ) ^ r *
          S.indicator (fun _ => (1 : ℝ)) t) =
          S.indicator (fun t : PositiveLine => (t.val : ℝ) ^ r) := by
        funext t
        by_cases ht : t ∈ S <;> simp [ht]
      rw [hind, integral_indicator hS] at h
      rw [reciprocalTail, hset]
      simpa only [measureReal_def, Measure.restrict_apply_univ, smul_eq_mul, mul_one] using h
    rw [htail a ha, htail b hb]
    apply (div_le_div_iff₀ (positiveMoment_pos hμ hb) (positiveMoment_pos hμ ha)).2
    exact restricted_power_moment_cross hab ha hb s⁻¹
  · have hset : {t : PositiveLine | s < (t.val : ℝ)⁻¹} = univ := by
      ext t
      simp only [mem_setOf_eq, mem_univ, iff_true]
      exact lt_of_le_of_lt (le_of_not_gt hs) (inv_pos.mpr t.property)
    simp [reciprocalTail, hset]

end EllipsoidVerification
end
end CanonicalSource23

section CanonicalSource24
/- Source: Ellipsoid/PositiveJacobians.lean -/



/-!
# The finite-dimensional positivity bridge

The coefficient Jacobian is generally not symmetric. The determinant argument
below uses its strictly positive quadratic form and a nonsingular homotopy to
the identity. It does not incorrectly apply a symmetric-matrix determinant
theorem directly to the Jacobian.
-/

noncomputable section

open Matrix Set
open scoped BigOperators MatrixOrder

namespace EllipsoidVerification

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def symmetricPart (A : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  (1 / 2 : ℝ) • (A + Aᵀ)

theorem symmetricPart_isHermitian (A : Matrix ι ι ℝ) :
    (symmetricPart A).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  ext i j
  simp [symmetricPart, Matrix.transpose_apply, add_comm] <;> ring

theorem quadratic_symmetricPart (A : Matrix ι ι ℝ) (x : ι → ℝ) :
    x ⬝ᵥ (symmetricPart A *ᵥ x) = x ⬝ᵥ (A *ᵥ x) := by
  have htranspose : x ⬝ᵥ (Aᵀ *ᵥ x) = x ⬝ᵥ (A *ᵥ x) := by
    simp only [dotProduct, mulVec, Matrix.transpose_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp only [symmetricPart, Matrix.smul_mulVec, Matrix.add_mulVec, dotProduct_smul,
    dotProduct_add, smul_eq_mul]
  rw [htranspose]
  ring

theorem quadratic_pos_of_symmetricPart_posDef {A : Matrix ι ι ℝ}
    (hA : (symmetricPart A).PosDef) {x : ι → ℝ} (hx : x ≠ 0) :
    0 < x ⬝ᵥ (A *ᵥ x) := by
  simpa only [star_trivial, quadratic_symmetricPart] using hA.dotProduct_mulVec_pos hx

theorem det_ne_zero_of_quadratic_pos {A : Matrix ι ι ℝ}
    (hA : ∀ x : ι → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (A *ᵥ x)) : A.det ≠ 0 := by
  have hinj : Function.Injective A.mulVec := by
    intro x y hxy
    by_contra hne
    have h := hA (x - y) (sub_ne_zero.mpr hne)
    exact (lt_irrefl (0 : ℝ)) (by
      simpa only [Matrix.mulVec_sub, hxy, sub_self, dotProduct_zero] using h)
  have hu : IsUnit A := Matrix.mulVec_injective_iff_isUnit.mp hinj
  exact isUnit_iff_ne_zero.mp (A.isUnit_iff_isUnit_det.mp hu)

theorem det_pos_of_quadratic_pos {A : Matrix ι ι ℝ}
    (hA : ∀ x : ι → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (A *ᵥ x)) : 0 < A.det := by
  let H : ℝ → Matrix ι ι ℝ := fun t => (1 - t) • 1 + t • A
  have hH (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (H t).det ≠ 0 := by
    apply det_ne_zero_of_quadratic_pos
    intro x hx
    have hxpos : 0 < x ⬝ᵥ x := by
      simpa only [star_trivial, Matrix.one_mulVec] using
        (Matrix.PosDef.one : (1 : Matrix ι ι ℝ).PosDef).dotProduct_mulVec_pos hx
    have hAx := hA x hx
    change 0 < x ⬝ᵥ (((1 - t) • 1 + t • A) *ᵥ x)
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_add, dotProduct_smul, smul_eq_mul]
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) hxpos.le,
      mul_nonneg ht.1 hAx.le]
  have hcont : Continuous (fun t => (H t).det) := by
    dsimp [H]
    fun_prop
  by_contra h
  have hA0 : A.det ≤ 0 := le_of_not_gt h
  have hzeroRange : (0 : ℝ) ∈ Icc (H 1).det (H 0).det := by
    constructor
    · simpa [H] using hA0
    · simp [H]
  obtain ⟨t, ht, hzero⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1)
    hcont.continuousOn hzeroRange
  exact hH t ht hzero

theorem det_pos_of_symmetricPart_posDef {A : Matrix ι ι ℝ}
    (hA : (symmetricPart A).PosDef) : 0 < A.det :=
  det_pos_of_quadratic_pos fun _ hx => quadratic_pos_of_symmetricPart_posDef hA hx

theorem symmetricPart_diagonal_mul_submatrix (A : Matrix ι ι ℝ) (d : ι → ℝ)
    (s : Finset ι) :
    symmetricPart ((Matrix.diagonal d * A).submatrix
      (fun i : s => i.val) (fun i : s => i.val)) =
    (symmetricPart (Matrix.diagonal d * A)).submatrix
      (fun i : s => i.val) (fun i : s => i.val) := by
  ext i j
  rfl

theorem principal_minor_pos_of_diagonal_stability
    {A : Matrix ι ι ℝ} {d : ι → ℝ} (hd : ∀ i, 0 < d i)
    (hA : (symmetricPart (Matrix.diagonal d * A)).PosDef) (s : Finset ι) :
    0 < (A.submatrix (fun i : s => i.val) (fun i : s => i.val)).det := by
  have hs : ((symmetricPart (Matrix.diagonal d * A)).submatrix
      (fun i : s => i.val) (fun i : s => i.val)).PosDef :=
    hA.submatrix (e := fun i : s => i.val) (fun a b h => Subtype.ext h)
  have heq : (Matrix.diagonal d * A).submatrix (fun i : s => i.val) (fun i : s => i.val) =
      Matrix.diagonal (fun i : s => d i.val) *
        A.submatrix (fun i : s => i.val) (fun i : s => i.val) := by
    ext i j
    simp [Matrix.diagonal_mul]
  have hsmall : (symmetricPart ((Matrix.diagonal d * A).submatrix
      (fun i : s => i.val) (fun i : s => i.val))).PosDef := by
    rw [symmetricPart_diagonal_mul_submatrix]
    exact hs
  have hdet := det_pos_of_symmetricPart_posDef hsmall
  rw [heq, Matrix.det_mul, Matrix.det_diagonal] at hdet
  exact (mul_pos_iff_of_pos_left (Finset.prod_pos fun i _ => hd i.val)).mp hdet

/-- The strict Schur product lemma used in Lemma 3.1. Only the first
matrix's diagonal is required to be positive. -/
theorem posDef_hadamard_of_posSemidef_positive_diagonal
    {G R : Matrix ι ι ℝ} (hG : G.PosSemidef) (hdiag : ∀ i, 0 < G i i)
    (hR : R.PosDef) : (G ⊙ R).PosDef := by
  cases isEmpty_or_nonempty ι with
  | inl h =>
      letI := h
      have heq : G ⊙ R = (1 : Matrix ι ι ℝ) := Subsingleton.elim _ _
      rw [heq]
      exact Matrix.PosDef.one
  | inr h =>
      letI := h
      obtain ⟨c, hc, hcR⟩ := (CFC.exists_pos_algebraMap_le_iff R hR.isHermitian).2 (by
        intro t ht
        rw [hR.isHermitian.spectrum_real_eq_range_eigenvalues] at ht
        obtain ⟨i, rfl⟩ := ht
        exact hR.eigenvalues_pos i)
      have hrem : (R - c • (1 : Matrix ι ι ℝ)).PosSemidef := by
        simpa only [Algebra.algebraMap_eq_smul_one] using (Matrix.le_iff.mp hcR)
      have hdiagPD : (Matrix.diagonal (fun i => c * G i i)).PosDef :=
        Matrix.PosDef.diagonal fun i => mul_pos hc (hdiag i)
      have heq : G ⊙ R = Matrix.diagonal (fun i => c * G i i) +
          G ⊙ (R - c • (1 : Matrix ι ι ℝ)) := by
        ext i j
        by_cases hij : i = j
        · subst j
          simp [Matrix.hadamard_apply, Matrix.sub_apply, Matrix.smul_apply]
          ring
        · simp [Matrix.hadamard_apply, Matrix.sub_apply, Matrix.smul_apply, hij]
      rw [heq]
      exact hdiagPD.add_posSemidef (hG.hadamard hrem)

end EllipsoidVerification
end
end CanonicalSource24

section CanonicalSource25
/- Source: Ellipsoid/IntegralGram.lean -/



noncomputable section

open MeasureTheory Matrix Set
open scoped BigOperators

namespace EllipsoidVerification

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]

theorem integral_gram_posSemidef (μ : Measure Ω) (f : ι → Ω → ℝ)
    (hf : ∀ i j, Integrable (fun x => f i x * f j x) μ) :
    Matrix.PosSemidef ((fun i j => ∫ x, f i x * f j x ∂μ) : Matrix ι ι ℝ) := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    simp only [star_trivial, mul_comm]
  · intro c
    have hnonneg : 0 ≤ ∫ x, (∑ i, c i * f i x) ^ 2 ∂μ :=
      integral_nonneg fun _ => sq_nonneg _
    have heq : (∫ x, (∑ i, c i * f i x) ^ 2 ∂μ) =
        c ⬝ᵥ (((fun i j => ∫ x, f i x * f j x ∂μ) : Matrix ι ι ℝ) *ᵥ c) := by
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
        (fun j _ => ((hf i j).const_mul (c i * c j)).congr (ae_of_all _ fun x => by ring)))]
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_finsetSum _ (fun j _ => ((hf i j).const_mul (c i * c j)).congr
        (ae_of_all _ fun x => by ring))]
      apply Finset.sum_congr rfl
      intro j hj
      calc
        (∫ x, c j * f j x * (c i * f i x) ∂μ) =
            ∫ x, (c i * c j) * (f i x * f j x) ∂μ :=
          integral_congr_ae (ae_of_all _ fun x => by ring)
        _ = _ := by rw [integral_const_mul]; ring
    simpa only [star_trivial, heq] using hnonneg

theorem integral_matrix_posSemidef (μ : Measure Ω) (A : Ω → Matrix ι ι ℝ)
    (hA : ∀ᵐ x ∂μ, (A x).PosSemidef)
    (hAi : ∀ i j, Integrable (fun x => A x i j) μ) :
    Matrix.PosSemidef ((fun i j => ∫ x, A x i j ∂μ) : Matrix ι ι ℝ) := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    simp only [star_trivial]
    apply integral_congr_ae
    filter_upwards [hA] with x hx
    exact hx.isHermitian.isSymm.apply i j
  · intro c
    have h : 0 ≤ ∫ x, c ⬝ᵥ (A x *ᵥ c) ∂μ :=
      integral_nonneg_of_ae (hA.mono fun x hx => by
        simpa only [star_trivial, Pi.zero_apply] using hx.dotProduct_mulVec_nonneg c)
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum] at h ⊢
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
      (fun j _ => ((hAi i j).mul_const (c j)).const_mul (c i)))] at h
    simp only [integral_finsetSum _ (fun j _ =>
      ((hAi _ j).mul_const (c j)).const_mul _), integral_const_mul, integral_mul_const] at h
    simpa only [star_trivial] using h

/-- The covariance kernel `min(a_i,a_j)` is positive semidefinite for
arbitrary nonnegative times, including coincidences and zero times. -/
theorem minKernel_posSemidef (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    Matrix.PosSemidef ((fun i j => min (a i) (a j)) : Matrix ι ι ℝ) := by
  let f : ι → ℝ → ℝ := fun i => (Ioo 0 (a i)).indicator (fun _ => 1)
  have hprod (i j : ι) : (fun t => f i t * f j t) =
      (Ioo 0 (min (a i) (a j))).indicator (fun _ => (1 : ℝ)) := by
    funext t
    by_cases hi : t ∈ Ioo 0 (a i) <;> by_cases hj : t ∈ Ioo 0 (a j)
    · simp only [f, Set.indicator_of_mem hi, Set.indicator_of_mem hj, mul_one]
      rw [Set.indicator_of_mem
        (show t ∈ Ioo 0 (min (a i) (a j)) from ⟨hi.1, lt_min hi.2 hj.2⟩)]
    · simp only [f, Set.indicator_of_mem hi, Set.indicator_of_notMem hj, mul_zero]
      rw [Set.indicator_of_notMem (by simpa [Set.mem_Ioo, lt_min_iff, hi.1, hi.2] using hj)]
    · simp only [f, Set.indicator_of_notMem hi, zero_mul]
      rw [Set.indicator_of_notMem (by
        intro ht
        exact hi ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩)]
    · simp only [f, Set.indicator_of_notMem hi, zero_mul]
      rw [Set.indicator_of_notMem (by
        intro ht
        exact hi ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩)]
  have hfi (i j : ι) : Integrable (fun t => f i t * f j t) volume := by
    rw [hprod]
    exact (integrableOn_const (by simp [Real.volume_Ioo]) :
      IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo 0 (min (a i) (a j))) ).integrable_indicator
      measurableSet_Ioo
  have h := integral_gram_posSemidef volume f hfi
  have heq (i j : ι) : (∫ t, f i t * f j t) = min (a i) (a j) := by
    rw [hprod, integral_indicator measurableSet_Ioo, integral_const]
    simp only [Real.volume_Ioo, measureReal_def, Measure.restrict_apply_univ,
      sub_zero, smul_eq_mul, mul_one, ENNReal.toReal_ofReal (le_min (ha i) (ha j))]
  simpa only [heq] using h

theorem weighted_minKernel_posSemidef (a v : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    Matrix.PosSemidef ((fun i j => v i * v j * min (a i) (a j)) : Matrix ι ι ℝ) := by
  have h := (minKernel_posSemidef a ha).mul_mul_conjTranspose_same (Matrix.diagonal v)
  have heq : Matrix.diagonal v * Matrix.of (fun i j => min (a i) (a j)) *
      (Matrix.diagonal v)ᴴ = Matrix.of (fun i j => v i * v j * min (a i) (a j)) := by
    ext i j
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.diagonal_conjTranspose,
      star_trivial]
    ring
  change (Matrix.diagonal v * Matrix.of (fun i j => min (a i) (a j)) *
    (Matrix.diagonal v)ᴴ).PosSemidef at h
  rw [heq] at h
  exact h

end EllipsoidVerification
end
end CanonicalSource25

section CanonicalSource26
/- Source: Ellipsoid/OrderedMinKernel.lean -/



noncomputable section

open Matrix Finset
open scoped BigOperators

namespace EllipsoidVerification

def minRatioKernel {m : ℕ} (p : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => min (p i) (p j) / max (p i) (p j)

def squaredNodesWithZero {m : ℕ} (p : Fin m → ℝ) : Fin (m + 1) → ℝ :=
  Fin.cases 0 (fun i => p i ^ 2)

def squaredNodeIncrement {m : ℕ} (p : Fin m → ℝ) (i : Fin m) : ℝ :=
  squaredNodesWithZero p i.succ - squaredNodesWithZero p i.castSucc

theorem squaredNodeIncrement_pos {m : ℕ} {p : Fin m → ℝ}
    (hp : StrictMono p) (hpos : ∀ i, 0 < p i) (i : Fin m) :
    0 < squaredNodeIncrement p i := by
  cases m with
  | zero => exact Fin.elim0 i
  | succ m =>
      refine Fin.cases ?_ (fun j => ?_) i
      · change 0 < p 0 ^ 2 - 0
        simpa only [sub_zero] using sq_pos_of_pos (hpos 0)
      · have hlt := hp j.castSucc_lt_succ
        have h0 := hpos j.castSucc
        simp only [squaredNodeIncrement, squaredNodesWithZero, Fin.castSucc_succ,
          Fin.cases_succ]
        nlinarith

theorem sum_squaredNodeIncrement {m : ℕ} (p : Fin m → ℝ) (i : Fin m) :
    ∑ j ∈ Finset.Iic i, squaredNodeIncrement p j = p i ^ 2 := by
  simpa [squaredNodeIncrement, squaredNodesWithZero] using
    Fin.sum_Iic_sub i (squaredNodesWithZero p)

def minRatioCholesky {m : ℕ} (p : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => if j ≤ i then Real.sqrt (squaredNodeIncrement p j) / p i else 0

theorem minRatioCholesky_isLowerTriangular {m : ℕ} (p : Fin m → ℝ) :
    (minRatioCholesky p).IsLowerTriangular := by
  intro i j hij
  have hij' : i < j := hij
  simp [minRatioCholesky, not_le.mpr hij']

theorem det_minRatioCholesky_pos {m : ℕ} {p : Fin m → ℝ}
    (hp : StrictMono p) (hpos : ∀ i, 0 < p i) :
    0 < (minRatioCholesky p).det := by
  rw [Matrix.det_of_isLowerTriangular _ (minRatioCholesky_isLowerTriangular p)]
  apply Finset.prod_pos
  intro i hi
  simp only [minRatioCholesky, le_refl, if_true]
  exact div_pos (Real.sqrt_pos.2 (squaredNodeIncrement_pos hp hpos i)) (hpos i)

theorem minRatioCholesky_mul_transpose {m : ℕ} {p : Fin m → ℝ}
    (hp : StrictMono p) (hpos : ∀ i, 0 < p i) :
    minRatioCholesky p * (minRatioCholesky p)ᵀ = minRatioKernel p := by
  ext i j
  have hentry (k : Fin m) :
      minRatioCholesky p i k * minRatioCholesky p j k =
        if k ≤ min i j then squaredNodeIncrement p k / (p i * p j) else 0 := by
    by_cases hki : k ≤ i <;> by_cases hkj : k ≤ j
    · simp only [minRatioCholesky, hki, hkj, if_true,
        le_min_iff.mpr ⟨hki, hkj⟩]
      rw [div_mul_div_comm, Real.mul_self_sqrt (squaredNodeIncrement_pos hp hpos k).le]
    · simp [minRatioCholesky, hki, hkj, le_min_iff]
    · simp [minRatioCholesky, hki, hkj, le_min_iff]
    · simp [minRatioCholesky, hki, hkj, le_min_iff]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, hentry]
  rw [← Finset.sum_filter]
  have hset : Finset.univ.filter (fun k : Fin m => k ≤ min i j) = Finset.Iic (min i j) := by
    ext k
    simp
  rw [hset, ← Finset.sum_div, sum_squaredNodeIncrement]
  rcases le_total i j with hij | hji
  · simp only [min_eq_left hij, minRatioKernel, min_eq_left (hp.monotone hij),
      max_eq_right (hp.monotone hij)]
    field_simp [(hpos i).ne', (hpos j).ne']
  · simp only [min_eq_right hji, minRatioKernel, min_eq_right (hp.monotone hji),
      max_eq_left (hp.monotone hji)]
    field_simp [(hpos i).ne', (hpos j).ne']

/-- The strict auxiliary kernel in Lemma 3.1, with no probabilistic
assumption and with all positive, pairwise ordered real parameters. -/
theorem minRatioKernel_posDef {m : ℕ} {p : Fin m → ℝ}
    (hp : StrictMono p) (hpos : ∀ i, 0 < p i) : (minRatioKernel p).PosDef := by
  rw [← minRatioCholesky_mul_transpose hp hpos]
  have hu : IsUnit (minRatioCholesky p) :=
    (minRatioCholesky p).isUnit_iff_isUnit_det.mpr
      (isUnit_iff_ne_zero.mpr (det_minRatioCholesky_pos hp hpos).ne')
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.PosDef.mul_conjTranspose_self (minRatioCholesky p)
      (Matrix.vecMul_injective_iff_isUnit.mpr hu)

end EllipsoidVerification
end
end CanonicalSource26

section CanonicalSource27
/- Source: Ellipsoid/TailMoments.lean -/



noncomputable section

open MeasureTheory Set Matrix
open scoped BigOperators ENNReal

namespace EllipsoidVerification

theorem integrable_tail_mellin_and_integral
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsFiniteMeasure ν]
    (X : Ω → ℝ) (hXm : Measurable X) (hX0 : ∀ x, 0 ≤ X x)
    {r : ℝ} (hr : 0 < r) (hXi : Integrable (fun x => X x ^ r) ν) :
    IntegrableOn (fun s : ℝ => s ^ (r - 1) * (ν {x | s < X x}).toReal) (Ioi 0) ∧
      (∫ s in Ioi (0 : ℝ), s ^ (r - 1) * (ν {x | s < X x}).toReal) =
        (∫ x, X x ^ r ∂ν) / r := by
  let q : ℝ → ℝ := fun s => (ν {x | s < X x}).toReal
  have hq : Antitone q := by
    intro s t hst
    exact ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono fun x hx => lt_of_le_of_lt hst hx)
  have hqm : Measurable q := hq.measurable
  let H : ℝ → ℝ := fun s => s ^ (r - 1) * q s
  have hHm : Measurable H := (measurable_id.pow_const _).mul hqm
  have hH0 : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] H := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    exact mul_nonneg (Real.rpow_nonneg hs.le _) ENNReal.toReal_nonneg
  have heq : (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (H s)) =
      ∫⁻ s in Ioi (0 : ℝ), ν {x | s < X x} * ENNReal.ofReal (s ^ (r - 1)) := by
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    dsimp only [H, q]
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _),
      ENNReal.ofReal_toReal (measure_ne_top _ _), mul_comm]
  have hLayer := lintegral_rpow_eq_lintegral_meas_lt_mul ν (ae_of_all _ hX0)
    hXm.aemeasurable hr
  rw [← heq] at hLayer
  have hfinite : (∫⁻ x, ENNReal.ofReal (X x ^ r) ∂ν) ≠ ∞ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hXi (ae_of_all _ fun x =>
      Real.rpow_nonneg (hX0 x) r)]
    exact ENNReal.ofReal_ne_top
  have hHfinite : (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (H s)) ≠ ∞ := by
    intro htop
    rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hr).ne'] at hLayer
    exact hfinite hLayer
  have hHi : Integrable H (volume.restrict (Ioi (0 : ℝ))) :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hHm.aestronglyMeasurable hH0).mp hHfinite
  refine ⟨hHi, ?_⟩
  have hReal := congrArg ENNReal.toReal hLayer
  rw [← integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x =>
    Real.rpow_nonneg (hX0 x) r) hXi.aestronglyMeasurable,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hr.le,
    ← integral_eq_lintegral_of_nonneg_ae hH0 hHm.aestronglyMeasurable] at hReal
  exact (eq_div_iff hr.ne').mpr (by simpa only [mul_comm] using hReal.symm)

theorem reciprocalTail_mellin {μ : Measure PositiveLine} (hμ : μ ≠ 0)
    {a r : ℝ} (hr : 0 < r)
    (ha : Integrable (fun t : PositiveLine => (t.val : ℝ) ^ a) μ)
    (har : Integrable (fun t : PositiveLine => (t.val : ℝ) ^ (a - r)) μ) :
    IntegrableOn (fun s : ℝ => s ^ (r - 1) * reciprocalTail μ a s) (Ioi 0) ∧
      (∫ s in Ioi (0 : ℝ), s ^ (r - 1) * reciprocalTail μ a s) =
        positiveMoment μ (a - r) / (r * positiveMoment μ a) := by
  letI := powerTilt_probability hμ ha
  have hpow : Integrable (fun t : PositiveLine => (t.val : ℝ) ^ (-r)) (powerTilt μ a) := by
    apply integrable_powerTilt_power hμ ha
    simpa only [sub_eq_add_neg] using har
  have hi : Integrable (fun t : PositiveLine => ((t.val : ℝ)⁻¹) ^ r) (powerTilt μ a) := by
    convert hpow using 1
    funext t
    rw [Real.inv_rpow t.property.le, Real.rpow_neg t.property.le]
  obtain ⟨hInt, hval⟩ := integrable_tail_mellin_and_integral (powerTilt μ a)
    (fun t : PositiveLine => (t.val : ℝ)⁻¹) (by fun_prop)
    (fun t => inv_nonneg.mpr t.property.le) hr hi
  refine ⟨hInt, ?_⟩
  change (∫ s in Ioi (0 : ℝ), s ^ (r - 1) *
    ((powerTilt μ a) {t | s < (t.val : ℝ)⁻¹}).toReal) = _
  rw [hval, integral_powerTilt ha]
  have heq : (fun t : PositiveLine => (t.val : ℝ) ^ a * ((t.val : ℝ)⁻¹) ^ r) =
      (fun t : PositiveLine => (t.val : ℝ) ^ (a - r)) := by
    funext t
    rw [Real.inv_rpow t.property.le, ← Real.rpow_neg t.property.le,
      ← Real.rpow_add t.property, sub_eq_add_neg]
  rw [heq]
  dsimp [positiveMoment]
  ring

def orderedMomentGram (μ : Measure PositiveLine) {ι : Type*} (p : ι → ℝ) :
    Matrix ι ι ℝ :=
  fun i j => positiveMoment μ (2 * max (p i) (p j) - min (p i) (p j)) /
    ((p i + p j) * positiveMoment μ (3 * max (p i) (p j)))

def orderedMomentKernel (μ : Measure PositiveLine) {ι : Type*} (p : ι → ℝ) :
    Matrix ι ι ℝ := fun i j =>
      min (p i) (p j) * positiveMoment μ (3 * min (p i) (p j)) *
        positiveMoment μ (2 * max (p i) (p j) - min (p i) (p j))

theorem orderedMomentGram_posSemidef {μ : Measure PositiveLine} [SFinite μ]
    (hμ : μ ≠ 0) {m : ℕ} {p : Fin m → ℝ}
    (hp : StrictMono p) (hp0 : ∀ i, 0 < p i)
    (h3 : ∀ i, Integrable (fun t : PositiveLine => (t.val : ℝ) ^ (3 * p i)) μ)
    (hm : ∀ i j, i ≤ j → Integrable
      (fun t : PositiveLine => (t.val : ℝ) ^ (2 * p j - p i)) μ) :
    (orderedMomentGram μ p).PosSemidef := by
  let A : ℝ → Matrix (Fin m) (Fin m) ℝ := fun s i j =>
    s ^ (p i - 1 / 2) * s ^ (p j - 1 / 2) *
      min (reciprocalTail μ (3 * p i) s) (reciprocalTail μ (3 * p j) s)
  have hA : ∀ s : ℝ, (A s).PosSemidef := by
    intro s
    exact weighted_minKernel_posSemidef (fun i => reciprocalTail μ (3 * p i) s)
      (fun i => s ^ (p i - 1 / 2)) (fun i => reciprocalTail_nonneg _ _ _)
  have hentry (i j : Fin m) :
      (fun s => A s i j) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun s => s ^ (p i + p j - 1) * reciprocalTail μ (3 * max (p i) (p j)) s) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    dsimp [A]
    rw [← Real.rpow_add hs]
    have hexp : p i - 1 / 2 + (p j - 1 / 2) = p i + p j - 1 := by ring
    rw [hexp]
    rcases le_total i j with hij | hji
    · rw [max_eq_right (hp.monotone hij), min_eq_right
        (reciprocalTail_antitone_exponent hμ (by linarith [hp.monotone hij]) (h3 i) (h3 j) s)]
    · rw [max_eq_left (hp.monotone hji), min_eq_left
        (reciprocalTail_antitone_exponent hμ (by linarith [hp.monotone hji]) (h3 j) (h3 i) s)]
  have htail (i j : Fin m) :
      IntegrableOn (fun s : ℝ => s ^ (p i + p j - 1) *
        reciprocalTail μ (3 * max (p i) (p j)) s) (Ioi 0) ∧
      (∫ s in Ioi (0 : ℝ), s ^ (p i + p j - 1) *
        reciprocalTail μ (3 * max (p i) (p j)) s) = orderedMomentGram μ p i j := by
    rcases le_total i j with hij | hji
    · have he : 3 * p j - (p i + p j) = 2 * p j - p i := by ring
      simpa only [max_eq_right (hp.monotone hij), min_eq_left (hp.monotone hij),
        he, orderedMomentGram] using reciprocalTail_mellin hμ (add_pos (hp0 i) (hp0 j))
          (h3 j) (by simpa only [he] using hm i j hij)
    · have he : 3 * p i - (p i + p j) = 2 * p i - p j := by ring
      simpa only [max_eq_left (hp.monotone hji), min_eq_right (hp.monotone hji),
        he, orderedMomentGram] using reciprocalTail_mellin hμ (add_pos (hp0 i) (hp0 j))
          (h3 i) (by simpa only [he] using hm j i hji)
  have hi (i j : Fin m) : Integrable (fun s => A s i j) (volume.restrict (Ioi (0 : ℝ))) :=
    (htail i j).1.congr (hentry i j).symm
  have h := integral_matrix_posSemidef (volume.restrict (Ioi (0 : ℝ))) A
    (ae_of_all _ hA) hi
  have hmat : ((fun i j => ∫ s in Ioi (0 : ℝ), A s i j) :
      Matrix (Fin m) (Fin m) ℝ) = orderedMomentGram μ p := by
    ext i j
    rw [integral_congr_ae (hentry i j), (htail i j).2]
  rw [hmat] at h
  exact h

theorem orderedMomentGram_diagonal_pos {μ : Measure PositiveLine} (hμ : μ ≠ 0)
    {m : ℕ} {p : Fin m → ℝ} (hp0 : ∀ i, 0 < p i)
    (h3 : ∀ i, Integrable (fun t : PositiveLine => (t.val : ℝ) ^ (3 * p i)) μ)
    (hm : ∀ i, Integrable (fun t : PositiveLine => (t.val : ℝ) ^ p i) μ) (i : Fin m) :
    0 < orderedMomentGram μ p i i := by
  simp only [orderedMomentGram, min_self, max_self, show 2 * p i - p i = p i by ring]
  exact div_pos (positiveMoment_pos hμ (hm i))
    (mul_pos (add_pos (hp0 i) (hp0 i)) (positiveMoment_pos hμ (h3 i)))

end EllipsoidVerification
end
end CanonicalSource27

section CanonicalSource28
/- Source: Ellipsoid/OrderedMomentKernel.lean -/



noncomputable section

open Matrix MeasureTheory
open scoped BigOperators

namespace EllipsoidVerification

theorem orderedMomentKernel_gram_identity
    {μ : Measure PositiveLine} (hμ : μ ≠ 0) {m : ℕ} {p : Fin m → ℝ}
    (hp : StrictMono p) (hp0 : ∀ i, 0 < p i)
    (h3 : ∀ i, Integrable (fun t : PositiveLine => (t.val : ℝ) ^ (3 * p i)) μ) :
    orderedMomentKernel μ p =
      Matrix.diagonal (fun i => p i * positiveMoment μ (3 * p i)) *
        (orderedMomentGram μ p + orderedMomentGram μ p ⊙ minRatioKernel p) *
      Matrix.diagonal (fun i => p i * positiveMoment μ (3 * p i)) := by
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.add_apply,
    Matrix.hadamard_apply, orderedMomentKernel, orderedMomentGram, minRatioKernel]
  have hi := positiveMoment_pos hμ (h3 i)
  have hj := positiveMoment_pos hμ (h3 j)
  have hsum := add_pos (hp0 i) (hp0 j)
  rcases le_total i j with hij | hji
  · rw [min_eq_left (hp.monotone hij), max_eq_right (hp.monotone hij)]
    field_simp [(hp0 j).ne', hj.ne', hsum.ne'] <;> ring
  · rw [min_eq_right (hp.monotone hji), max_eq_left (hp.monotone hji)]
    field_simp [(hp0 i).ne', hi.ne', hsum.ne'] <;> ring

/-- Lemma 3.1 in its full measure-theoretic generality. The measure need not
have finite mass; the assumed moments are precisely those in the paper.
The subtype is the positive real half-line with its inherited Borel space. -/
theorem orderedMomentKernel_posDef
    {μ : Measure PositiveLine} [SigmaFinite μ] (hμ : μ ≠ 0)
    {m : ℕ} {p : Fin m → ℝ} (hp : StrictMono p) (hp0 : ∀ i, 0 < p i)
    (h3 : ∀ i, Integrable (fun t : PositiveLine => (t.val : ℝ) ^ (3 * p i)) μ)
    (hm : ∀ i j, i ≤ j → Integrable
      (fun t : PositiveLine => (t.val : ℝ) ^ (2 * p j - p i)) μ) :
    (orderedMomentKernel μ p).PosDef := by
  have hG := orderedMomentGram_posSemidef hμ hp hp0 h3 hm
  have hdiag : ∀ i, 0 < orderedMomentGram μ p i i :=
    orderedMomentGram_diagonal_pos hμ hp0 h3 (fun i => by
      simpa only [show 2 * p i - p i = p i by ring] using hm i i le_rfl)
  have hR := minRatioKernel_posDef hp hp0
  have hstrict := posDef_hadamard_of_posSemidef_positive_diagonal hG hdiag hR
  have hsum : (orderedMomentGram μ p + orderedMomentGram μ p ⊙ minRatioKernel p).PosDef :=
    Matrix.PosDef.posSemidef_add hG hstrict
  let D : Matrix (Fin m) (Fin m) ℝ :=
    Matrix.diagonal (fun i => p i * positiveMoment μ (3 * p i))
  have hD : D.PosDef := Matrix.PosDef.diagonal
    (fun i => mul_pos (hp0 i) (positiveMoment_pos hμ (h3 i)))
  have hconj := hsum.mul_mul_conjTranspose_same (B := D)
    (Matrix.vecMul_injective_iff_isUnit.mpr hD.isUnit)
  rw [orderedMomentKernel_gram_identity hμ hp hp0 h3]
  simpa only [D, Matrix.diagonal_conjTranspose, star_trivial] using hconj

theorem orderedMomentKernel_posDef_of_injective
    {μ : Measure PositiveLine} [SigmaFinite μ] (hμ : μ ≠ 0)
    {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ι → ℝ}
    (hp : Function.Injective p) (hp0 : ∀ i, 0 < p i)
    (h3 : ∀ i, Integrable (fun t : PositiveLine => (t.val : ℝ) ^ (3 * p i)) μ)
    (hm : ∀ i j, p i ≤ p j → Integrable
      (fun t : PositiveLine => (t.val : ℝ) ^ (2 * p j - p i)) μ) :
    (orderedMomentKernel μ p).PosDef := by
  letI : LinearOrder ι := LinearOrder.lift' p hp
  let e := Fintype.orderIsoFinOfCardEq ι rfl
  have hmono : StrictMono (fun i => p (e i)) := by
    intro i j hij
    exact e.strictMono hij
  have h := orderedMomentKernel_posDef hμ hmono (fun i => hp0 (e i))
    (fun i => h3 (e i)) (fun i j hij => hm (e i) (e j) (hmono.monotone hij))
  have hsub := h.submatrix e.symm.injective
  have hmat : (orderedMomentKernel μ (fun i => p (e i))).submatrix e.symm e.symm =
      orderedMomentKernel μ p := by
    ext i j
    simp only [Matrix.submatrix_apply, orderedMomentKernel, OrderIso.apply_symm_apply]
  rw [hmat] at hsub
  exact hsub

end EllipsoidVerification
end
end CanonicalSource28

section CanonicalSource29
/- Source: Ellipsoid/MellinMeasures.lean -/



noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace EllipsoidVerification

def positiveLineLebesgue : Measure PositiveLine :=
  (volume : Measure ℝ).comap Subtype.val

instance positiveLineLebesgue_finiteOnCompacts : IsFiniteMeasureOnCompacts positiveLineLebesgue :=
  IsFiniteMeasureOnCompacts.comap' volume continuous_subtype_val
    (MeasurableEmbedding.subtype_coe measurableSet_Ioi)

instance sigmaFinite_positiveLineLebesgue : SigmaFinite positiveLineLebesgue := by
  apply SigmaFinite.of_map positiveLineLebesgue
    (measurable_subtype_coe : Measurable (Subtype.val : PositiveLine → ℝ)).aemeasurable
  have hmap : positiveLineLebesgue.map (Subtype.val : PositiveLine → ℝ) =
      (volume : Measure ℝ).restrict {t : ℝ | 0 < t} :=
    map_comap_subtype_coe (s := {t : ℝ | 0 < t}) measurableSet_Ioi (volume : Measure ℝ)
  rw [hmap]
  infer_instance

def mellinMeasure {n : ℕ} (e : Coefficients n) (a : ℝ) : Measure PositiveLine :=
  positiveLineLebesgue.withDensity (fun t : PositiveLine => ENNReal.ofReal
    ((t.val : ℝ) ^ (a - 1) * coefficientPolynomial e t.val ^ (-(3 / 2 : ℝ))))

instance sigmaFinite_mellinMeasure {n : ℕ} (e : Coefficients n) (a : ℝ) :
    SigmaFinite (mellinMeasure e a) := by unfold mellinMeasure; infer_instance

@[fun_prop] theorem measurable_mellinDensity {n : ℕ} (e : Coefficients n) (a : ℝ) :
    Measurable (fun t : PositiveLine =>
      (t.val : ℝ) ^ (a - 1) * coefficientPolynomial e t.val ^ (-(3 / 2 : ℝ))) := by
  unfold coefficientPolynomial
  fun_prop

theorem positiveMoment_mellinMeasure {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) (a r : ℝ) :
    positiveMoment (mellinMeasure e a) r = mellinMoment e (a + r) := by
  rw [positiveMoment, mellinMeasure,
    integral_withDensity_eq_integral_toReal_smul (measurable_mellinDensity e a).ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have hfun : (fun t : PositiveLine =>
      (ENNReal.ofReal ((t.val : ℝ) ^ (a - 1) *
        coefficientPolynomial e t.val ^ (-(3 / 2 : ℝ)))).toReal • (t.val : ℝ) ^ r) =
      (fun t : PositiveLine => (t.val : ℝ) ^ (a + r - 1) *
        coefficientPolynomial e t.val ^ (-(3 / 2 : ℝ))) := by
    funext t
    rw [ENNReal.toReal_ofReal (mul_nonneg (Real.rpow_nonneg t.property.le _)
      (Real.rpow_nonneg (coefficientPolynomial_pos he t.val).le _)), smul_eq_mul]
    calc
      t.val ^ (a - 1) * coefficientPolynomial e t.val ^ (-(3 / 2 : ℝ)) * t.val ^ r =
          (t.val ^ (a - 1) * t.val ^ r) * coefficientPolynomial e t.val ^ (-(3 / 2 : ℝ)) := by ring
      _ = _ := by rw [← Real.rpow_add t.property]; congr 2 <;> ring
  rw [hfun]
  exact integral_subtype_comap (s := {t : ℝ | 0 < t}) measurableSet_Ioi
    (fun t : ℝ => t ^ (a + r - 1) * coefficientPolynomial e t ^ (-(3 / 2 : ℝ)))

theorem integrable_mellinMeasure_power {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) {a r : ℝ}
    (har0 : 0 < a + r) (harn : a + r < 3 * n) :
    Integrable (fun t : PositiveLine => (t.val : ℝ) ^ r) (mellinMeasure e a) := by
  rw [mellinMeasure, integrable_withDensity_iff_integrable_smul'
    (measurable_mellinDensity e a).ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have hi : Integrable (fun t : PositiveLine =>
      (t.val : ℝ) ^ (a + r - 1) * coefficientPolynomial e t.val ^ (-(3 / 2 : ℝ)))
      positiveLineLebesgue :=
    (integrableOn_iff_comap_subtypeVal (s := {t : ℝ | 0 < t}) measurableSet_Ioi).1
      (integrable_mellinMoment he har0 harn)
  apply hi.congr
  exact ae_of_all _ fun t => by
    dsimp only
    symm
    rw [ENNReal.toReal_ofReal (mul_nonneg (Real.rpow_nonneg t.property.le _)
      (Real.rpow_nonneg (coefficientPolynomial_pos he t.val).le _)), smul_eq_mul]
    calc
      t.val ^ (a - 1) * coefficientPolynomial e t.val ^ (-(3 / 2 : ℝ)) * t.val ^ r =
          (t.val ^ (a - 1) * t.val ^ r) * coefficientPolynomial e t.val ^ (-(3 / 2 : ℝ)) := by ring
      _ = _ := by rw [← Real.rpow_add t.property]; congr 2 <;> ring

theorem mellinMoment_pos {n : ℕ} {e : Coefficients n} (he : coefficientAdmissible e)
    {r : ℝ} (hr0 : 0 < r) (hrn : r < 3 * n) : 0 < mellinMoment e r := by
  have hpos : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      0 < t ^ (r - 1) * coefficientPolynomial e t ^ (-(3 / 2 : ℝ)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact mul_pos (Real.rpow_pos_of_pos ht _) (Real.rpow_pos_of_pos (coefficientPolynomial_pos he t) _)
  change 0 < ∫ t : ℝ in Ioi 0,
    t ^ (r - 1) * coefficientPolynomial e t ^ (-(3 / 2 : ℝ))
  apply (integral_pos_iff_support_of_nonneg_ae (hpos.mono fun _ hx => hx.le)
    (integrable_mellinMoment he hr0 hrn)).2
  have hs : Function.support (fun t : ℝ => t ^ (r - 1) *
      coefficientPolynomial e t ^ (-(3 / 2 : ℝ))) =ᵐ[volume.restrict (Ioi (0 : ℝ))] univ :=
    hpos.mono fun t ht => by
      apply propext
      constructor
      · intro _
        exact Set.mem_univ t
      · intro _
        exact ht.ne'
  rw [measure_congr hs, Measure.restrict_apply_univ]
  simp

theorem mellinMeasure_ne_zero {n : ℕ} (hn : 0 < n) {e : Coefficients n}
    (he : coefficientAdmissible e) (a : ℝ) : mellinMeasure e a ≠ 0 := by
  intro hzero
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnupper : (n : ℝ) < 3 * n := by linarith
  have hpos := mellinMoment_pos he hnR hnupper
  have hmoment := positiveMoment_mellinMeasure he a ((n : ℝ) - a)
  rw [hzero] at hmoment
  simp only [positiveMoment, integral_zero_measure, add_sub_cancel] at hmoment
  exact hpos.ne' hmoment.symm

def positiveReciprocal : PositiveLine ≃ᵐ PositiveLine where
  toFun t := ⟨t.val⁻¹, inv_pos.mpr t.property⟩
  invFun t := ⟨t.val⁻¹, inv_pos.mpr t.property⟩
  left_inv t := by ext; simp
  right_inv t := by ext; simp
  measurable_toFun := by
    change Measurable (fun t : PositiveLine => (⟨t.val⁻¹, inv_pos.mpr t.property⟩ : PositiveLine))
    exact measurable_subtype_coe.inv.subtype_mk
  measurable_invFun := by
    change Measurable (fun t : PositiveLine => (⟨t.val⁻¹, inv_pos.mpr t.property⟩ : PositiveLine))
    exact measurable_subtype_coe.inv.subtype_mk

@[simp] theorem positiveReciprocal_val (t : PositiveLine) :
    (positiveReciprocal t).val = t.val⁻¹ := rfl

@[simp] theorem positiveReciprocal_involutive (t : PositiveLine) :
    positiveReciprocal (positiveReciprocal t) = t := by
  apply Subtype.ext
  simp only [positiveReciprocal_val, inv_inv]

def reciprocalMellinMeasure {n : ℕ} (e : Coefficients n) (a : ℝ) : Measure PositiveLine :=
  (mellinMeasure e a).map positiveReciprocal

instance sigmaFinite_reciprocalMellinMeasure {n : ℕ} (e : Coefficients n) (a : ℝ) :
    SigmaFinite (reciprocalMellinMeasure e a) := positiveReciprocal.sigmaFinite_map

theorem reciprocalMellinMeasure_ne_zero {n : ℕ} (hn : 0 < n) {e : Coefficients n}
    (he : coefficientAdmissible e) (a : ℝ) : reciprocalMellinMeasure e a ≠ 0 := by
  intro h
  apply mellinMeasure_ne_zero hn he a
  have hmap := congrArg (Measure.map positiveReciprocal) h
  simpa only [reciprocalMellinMeasure, Measure.map_map positiveReciprocal.measurable
    positiveReciprocal.measurable, Function.comp_def,
    show (fun x => positiveReciprocal (positiveReciprocal x)) = id by
      funext t; exact positiveReciprocal_involutive t,
    Measure.map_id, Measure.map_zero] using hmap

theorem positiveMoment_reciprocalMellinMeasure {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) (a r : ℝ) :
    positiveMoment (reciprocalMellinMeasure e a) r = mellinMoment e (a - r) := by
  rw [positiveMoment, reciprocalMellinMeasure, integral_map_equiv positiveReciprocal]
  have hfun : (fun t : PositiveLine => ((positiveReciprocal t).val : ℝ) ^ r) =
      (fun t : PositiveLine => (t.val : ℝ) ^ (-r)) := by
    funext t
    simp only [positiveReciprocal_val, Real.inv_rpow t.property.le, Real.rpow_neg t.property.le]
  rw [hfun]
  exact positiveMoment_mellinMeasure he a (-r)

theorem integrable_reciprocalMellinMeasure_power {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) {a r : ℝ} (har0 : 0 < a - r) (harn : a - r < 3 * n) :
    Integrable (fun t : PositiveLine => (t.val : ℝ) ^ r) (reciprocalMellinMeasure e a) := by
  rw [reciprocalMellinMeasure, integrable_map_equiv positiveReciprocal]
  have hi := integrable_mellinMeasure_power he (a := a) (r := -r) har0 harn
  convert hi using 1
  funext t
  simp only [Function.comp_apply, positiveReciprocal_val,
    Real.inv_rpow t.property.le, Real.rpow_neg t.property.le]

end EllipsoidVerification
end
end CanonicalSource29
