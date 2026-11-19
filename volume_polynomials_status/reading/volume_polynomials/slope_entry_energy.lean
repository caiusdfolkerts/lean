module

public import VolumePolynomials.SlopeMeasureMoments

@[expose] public section

/-!
# The entrywise energy and mass inequality

For every finite positive measure with both reciprocal exponential moments at
most one, the genuine corner energy I satisfies m⁴ ≤ I(2-I). No restriction to
atomic measures is made. This supplies the uniform determinant gap in Lemma 5.2.
-/

open MeasureTheory Set
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace VolumePolynomials

theorem slope_mass_le_one (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hp : slopeExponentialMoment μ (-1 / 2) ≤ 1)
    (hq : slopeExponentialMoment μ (1 / 2) ≤ 1) : μ.real univ ≤ 1 := by
  have hCS := slope_mass_sq_le_moments μ
    (hp.trans_lt (by norm_num)) (hq.trans_lt (by norm_num))
  have hp0 : 0 ≤ ∫ x : ℝ, Real.exp ((-1 / 2) * x) ∂μ :=
    integral_nonneg fun x => (Real.exp_pos _).le
  have hq0 : 0 ≤ ∫ x : ℝ, Real.exp ((1 / 2) * x) ∂μ :=
    integral_nonneg fun x => (Real.exp_pos _).le
  have hprod := mul_le_mul (integral_exponential_le_one hp)
    (integral_exponential_le_one hq) hq0 (by norm_num : (0 : ℝ) ≤ 1)
  nlinarith [measureReal_nonneg (μ := μ) (s := univ)]

theorem slope_entry_mass_fourth_le_energy (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hp : slopeExponentialMoment μ (-1 / 2) ≤ 1)
    (hq : slopeExponentialMoment μ (1 / 2) ≤ 1) :
    (μ.real univ) ^ 4 ≤ ‖cornerMean μ‖ ^ 2 * (2 - ‖cornerMean μ‖ ^ 2) := by
  let p : ℝ → ℝ := fun x => Real.exp ((-1 / 2) * x)
  let q : ℝ → ℝ := fun x => Real.exp ((1 / 2) * x)
  let K : ℝ × ℝ → ℝ := fun z => cornerKernel z.1 z.2
  let J : ℝ × ℝ → ℝ := fun z => Real.exp (|z.1 - z.2| / 2)
  have hpint : Integrable p μ := slopeExponentialMoment_integrable (hp.trans_lt (by norm_num))
  have hqint : Integrable q μ := slopeExponentialMoment_integrable (hq.trans_lt (by norm_num))
  have hKint : Integrable K (μ.prod μ) := by
    apply (integrable_const (1 : ℝ)).mono' (by dsimp [K]; unfold cornerKernel; fun_prop)
    exact Filter.Eventually.of_forall fun z => by
      simpa only [K, Real.norm_eq_abs, abs_of_pos (cornerKernel_pos _ _)] using
        cornerKernel_le_one z.1 z.2
  have hsum (z : ℝ × ℝ) : K z + J z = p z.1 * q z.2 + q z.1 * p z.2 := by
    dsimp [K, J, p, q, cornerKernel]
    rw [← Real.exp_add, ← Real.exp_add]
    by_cases hz : 0 ≤ z.1 - z.2
    · rw [abs_of_nonneg hz]
      congr 1 <;> congr 1 <;> ring
    · rw [abs_of_neg (lt_of_not_ge hz), add_comm]
      congr 1 <;> congr 1 <;> ring
  have hJint : Integrable J (μ.prod μ) := by
    apply ((hpint.mul_prod hqint).add (hqint.mul_prod hpint)).mono' (by dsimp [J]; fun_prop)
    apply Filter.Eventually.of_forall
    intro z
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    change J z ≤ p z.1 * q z.2 + q z.1 * p z.2
    have hKpos : 0 ≤ K z := (cornerKernel_pos _ _).le
    linarith [hsum z]
  have hIeq : ∫ z : ℝ × ℝ, K z ∂μ.prod μ = ‖cornerMean μ‖ ^ 2 := by
    rw [norm_cornerMean_sq, integral_prod _ hKint]
  have hIJ : ‖cornerMean μ‖ ^ 2 + (∫ z : ℝ × ℝ, J z ∂μ.prod μ) ≤ 2 := by
    rw [← hIeq, ← integral_add hKint hJint]
    simp_rw [hsum]
    rw [integral_add (hpint.mul_prod hqint) (hqint.mul_prod hpint),
      integral_prod_mul, integral_prod_mul]
    have hp0 : 0 ≤ ∫ x, p x ∂μ := integral_nonneg fun x => (Real.exp_pos _).le
    have hq0 : 0 ≤ ∫ x, q x ∂μ := integral_nonneg fun x => (Real.exp_pos _).le
    have hprod := mul_le_mul (integral_exponential_le_one hp)
      (integral_exponential_le_one hq) hq0 (by norm_num : (0 : ℝ) ≤ 1)
    have hprod' : (∫ x, p x ∂μ) * (∫ x, q x ∂μ) ≤ 1 := by
      simpa only [p, q, mul_one] using hprod
    nlinarith
  let f : ℝ × ℝ → ℝ := fun z => Real.exp (-|z.1 - z.2| / 4)
  let g : ℝ × ℝ → ℝ := fun z => Real.exp (|z.1 - z.2| / 4)
  have hfsq (z : ℝ × ℝ) : f z ^ 2 = K z := by
    dsimp [f, K, cornerKernel]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hgsq (z : ℝ × ℝ) : g z ^ 2 = J z := by
    dsimp [g, J]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hfg (z : ℝ × ℝ) : f z * g z = 1 := by
    dsimp [f, g]
    have he : -|z.1 - z.2| / 4 + |z.1 - z.2| / 4 = 0 := by ring
    rw [← Real.exp_add, he, Real.exp_zero]
  have hf : MemLp f 2 (μ.prod μ) :=
    (memLp_two_iff_integrable_sq (by dsimp [f]; fun_prop)).mpr (by simpa only [hfsq] using hKint)
  have hg : MemLp g 2 (μ.prod μ) :=
    (memLp_two_iff_integrable_sq (by dsimp [g]; fun_prop)).mpr (by simpa only [hgsq] using hJint)
  have hmass : (∫ z : ℝ × ℝ, (1 : ℝ) ∂μ.prod μ) = (μ.real univ) ^ 2 := by
    simpa only [one_mul, integral_const, smul_eq_mul, mul_one, pow_two] using
      (integral_prod_mul (μ := μ) (ν := μ) (fun _ : ℝ => (1 : ℝ)) (fun _ : ℝ => (1 : ℝ)))
  have hCS := integral_mul_sq_le hf hg
  simp only [hfg, hfsq, hgsq, hmass, hIeq] at hCS
  have hbound := mul_le_mul_of_nonneg_left hIJ (sq_nonneg ‖cornerMean μ‖)
  nlinarith

end VolumePolynomials
