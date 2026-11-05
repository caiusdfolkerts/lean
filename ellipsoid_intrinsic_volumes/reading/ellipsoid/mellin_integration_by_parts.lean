module

public import Ellipsoid.MellinDifferentiation
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace EllipsoidVerification

theorem hasDerivAt_coefficientPolynomial {n : ℕ} (e : Coefficients n) (t : ℝ) :
    HasDerivAt (coefficientPolynomial e) (coefficientDerivative e t) t := by
  unfold coefficientPolynomial coefficientDerivative
  apply HasDerivAt.fun_sum
  intro j hj
  simpa only [id_eq, mul_one, one_mul, Nat.cast_mul, Nat.cast_ofNat,
    mul_comm, mul_left_comm, mul_assoc] using
    (((hasDerivAt_id t).fun_pow (2 * j.val)).const_mul (e j))

theorem coefficientPolynomial_mul_rpow {n : ℕ} (e : Coefficients n) (r : ℝ)
    {t : ℝ} (ht : 0 < t) :
    t ^ r * coefficientPolynomial e t =
      ∑ j : Fin (n + 1), e j * t ^ (r + 2 * j.val) := by
  unfold coefficientPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Real.rpow_natCast, mul_left_comm, ← Real.rpow_add ht]
  congr 2
  push_cast
  ring

theorem coefficientDerivative_mul_rpow {n : ℕ} (e : Coefficients n) (r : ℝ)
    {t : ℝ} (ht : 0 < t) :
    t ^ r * coefficientDerivative e t =
      ∑ j : Fin (n + 1), (2 * j.val : ℝ) * e j * t ^ (r + 2 * j.val - 1) := by
  unfold coefficientDerivative
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hj0 : j.val = 0
  · simp [hj0]
  · rw [← Real.rpow_natCast]
    have hj1 : 1 ≤ 2 * j.val := by omega
    rw [Nat.cast_sub hj1]
    push_cast
    rw [show t ^ r * ((2 * (j.val : ℝ)) * e j * t ^ (2 * (j.val : ℝ) - 1)) =
        (2 * (j.val : ℝ)) * e j * (t ^ r * t ^ (2 * (j.val : ℝ) - 1)) by ring,
      ← Real.rpow_add ht]
    congr 2
    ring

theorem mellinBoundary_derivative {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) (s r : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => t ^ r * coefficientPolynomial e t ^ (-s))
      (∑ j : Fin (n + 1), (r - 2 * s * j.val) * e j *
        (t ^ (r + 2 * j.val - 1) * coefficientPolynomial e t ^ (-(s + 1)))) t := by
  have hq := coefficientPolynomial_pos he t
  have hd := (Real.hasDerivAt_rpow_const (Or.inl ht.ne') :
      HasDerivAt (fun t : ℝ => t ^ r) (r * t ^ (r - 1)) t).mul
    ((hasDerivAt_coefficientPolynomial e t).rpow_const (p := -s) (Or.inl hq.ne'))
  convert hd using 1
  symm
  have hpow : coefficientPolynomial e t ^ (-s) =
      coefficientPolynomial e t * coefficientPolynomial e t ^ (-(s + 1)) := by
    calc
      _ = coefficientPolynomial e t ^ (1 : ℝ) *
          coefficientPolynomial e t ^ (-(s + 1)) := by
        rw [← Real.rpow_add hq]
        congr 1
        ring
      _ = _ := by rw [Real.rpow_one]
  rw [hpow]
  have h1 := coefficientPolynomial_mul_rpow e (r - 1) ht
  have h2 := coefficientDerivative_mul_rpow e r ht
  have hrewrite :
      r * t ^ (r - 1) *
          (coefficientPolynomial e t * coefficientPolynomial e t ^ (-(s + 1))) +
        t ^ r * (coefficientDerivative e t * -s * coefficientPolynomial e t ^ (-s - 1)) =
      (r * (t ^ (r - 1) * coefficientPolynomial e t) -
        s * (t ^ r * coefficientDerivative e t)) * coefficientPolynomial e t ^ (-(s + 1)) := by
    rw [show -s - 1 = -(s + 1) by ring]
    ring
  rw [hrewrite, h1, h2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [show r - 1 + 2 * (j.val : ℝ) = r + 2 * j.val - 1 by ring]
  ring

theorem mellinBoundary_tendsto_atTop {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) {s r : ℝ} (hs : 0 < s) (hr : r < 2 * n * s) :
    Tendsto (fun t : ℝ => t ^ r * coefficientPolynomial e t ^ (-s)) atTop (𝓝 0) := by
  have hbound : ∀ᶠ t : ℝ in atTop,
      0 ≤ t ^ r * coefficientPolynomial e t ^ (-s) ∧
        t ^ r * coefficientPolynomial e t ^ (-s) ≤
          e (Fin.last n) ^ (-s) * t ^ (-(2 * n * s - r)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    refine ⟨mul_nonneg (Real.rpow_nonneg ht.le _) (Real.rpow_nonneg
      (coefficientPolynomial_pos he t).le _), ?_⟩
    have hp := Real.rpow_le_rpow_of_nonpos
      (mul_pos he.2.2 (pow_pos ht (2 * n)))
      (coefficientPolynomial_ge_leading he.1 t) (neg_nonpos.mpr hs.le)
    have hp' := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg ht.le r)
    convert hp' using 1
    rw [Real.mul_rpow he.2.2.le (pow_nonneg ht.le _), ← Real.rpow_natCast,
      ← Real.rpow_mul ht.le]
    rw [show t ^ r * (e (Fin.last n) ^ (-s) * t ^ (((2 * n : ℕ) : ℝ) * -s)) =
        e (Fin.last n) ^ (-s) * (t ^ r * t ^ (((2 * n : ℕ) : ℝ) * -s)) by ring,
      ← Real.rpow_add ht]
    congr 2
    push_cast
    ring
  have hlim := (tendsto_rpow_neg_atTop (sub_pos.mpr hr)).const_mul
    (e (Fin.last n) ^ (-s))
  simpa using squeeze_zero' (hbound.mono fun _ h => h.1)
    (hbound.mono fun _ h => h.2) (by simpa only [mul_zero] using hlim)

/-- The complete integration-by-parts recurrence for positive Mellin
parameters. Every term is integrable, and both boundary values vanish. -/
theorem coefficientMellinPower_recurrence {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) {s r : ℝ}
    (hr : 0 < r) (hrn : r < 2 * n * s) :
    ∑ j : Fin (n + 1), (r - 2 * s * j.val) * e j *
      coefficientMellinPower e (s + 1) (r + 2 * j.val) = 0 := by
  have hs : 0 < s := by
    by_contra hs
    have hn := Nat.cast_nonneg (α := ℝ) n
    have := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ (2 : ℝ) * n)
      (le_of_not_gt hs)
    linarith
  have hi (j : Fin (n + 1)) :
      IntegrableOn (fun t : ℝ => t ^ (r + 2 * j.val - 1) *
        coefficientPolynomial e t ^ (-(s + 1))) (Ioi 0) := by
    apply integrable_coefficientMellinPower (admissible_mem_positiveCoefficientDomain he)
    · positivity
    · have hj : (j.val : ℝ) ≤ n := by exact_mod_cast Nat.le_of_lt_succ j.isLt
      nlinarith
  have hsum : IntegrableOn (fun t : ℝ => ∑ j : Fin (n + 1),
      (r - 2 * s * j.val) * e j *
        (t ^ (r + 2 * j.val - 1) * coefficientPolynomial e t ^ (-(s + 1)))) (Ioi 0) :=
    integrable_finsetSum _ fun j _ => (hi j).const_mul _
  have hcont : ContinuousWithinAt
      (fun t : ℝ => t ^ r * coefficientPolynomial e t ^ (-s)) (Ici 0) 0 := by
    apply ContinuousAt.continuousWithinAt
    apply (Real.continuousAt_rpow_const 0 r (Or.inr hr.le)).mul
    exact (continuous_coefficientPolynomial e).continuousAt.rpow_const
      (Or.inl (coefficientPolynomial_pos he 0).ne')
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hcont
    (fun t ht => mellinBoundary_derivative he s r ht) hsum
    (mellinBoundary_tendsto_atTop he hs hrn)
  simp only [Real.zero_rpow hr.ne', zero_mul, sub_zero] at h
  rw [integral_finsetSum _ (fun j _ => (hi j).const_mul _)] at h
  simpa only [integral_const_mul, coefficientMellinPower] using h

end EllipsoidVerification
