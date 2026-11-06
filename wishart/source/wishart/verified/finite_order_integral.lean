module

public import wishart.verified.finite_order_growth

@[expose] public section

/-!
# Differentiating finite-order polynomial expectations

The value and first derivative are bounded only on an almost-sure support
set.  Uniform domination on a compact parameter interval follows from those
two polynomial bounds and the actual moments of the input measure.  Higher
derivatives and bounds outside the support set are not assumed.
-/

noncomputable section

open MeasureTheory Filter Set WishartVerification
open scoped Topology ENNReal

namespace Wishart.FiniteOrder

variable {E G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup G]

theorem PolynomialBoundOn.uniform_parameter {S : Set E} {F : ℝ × E → G}
    (hF : PolynomialBoundOn (univ ×ˢ S) F) (t : ℝ) :
    ∃ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ s ∈ Icc (t - 1) (t + 1), ∀ x ∈ S,
        ‖F (s, x)‖ ≤ C * (1 + ‖x‖) ^ k := by
  obtain ⟨k, M, hM, hb⟩ := hF
  refine ⟨k, M * (|t| + 2) ^ k, by positivity, ?_⟩
  intro s hs x hx
  have hst : |s - t| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hsabs : |s| ≤ |t| + 1 := by
    calc
      |s| = |(s - t) + t| := by congr 1; ring
      _ ≤ |s - t| + |t| := by
        simpa only [Real.norm_eq_abs] using norm_add_le (s - t) t
      _ ≤ |t| + 1 := by linarith
  have hnorm : 1 + ‖(s, x)‖ ≤ (|t| + 2) * (1 + ‖x‖) := by
    rw [Prod.norm_def, Real.norm_eq_abs]
    have hmax : max |s| ‖x‖ ≤ |t| + 1 + ‖x‖ :=
      max_le (hsabs.trans (le_add_of_nonneg_right (norm_nonneg x)))
        (by linarith [abs_nonneg t])
    nlinarith [mul_nonneg (abs_nonneg t) (norm_nonneg x), norm_nonneg x]
  calc
    ‖F (s, x)‖ ≤ M * (1 + ‖(s, x)‖) ^ k := hb _ ⟨mem_univ _, hx⟩
    _ ≤ M * ((|t| + 2) * (1 + ‖x‖)) ^ k :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hnorm k) hM
    _ = (M * (|t| + 2) ^ k) * (1 + ‖x‖) ^ k := by rw [mul_pow]; ring

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsFiniteMeasure μ]

theorem integrable_polynomial_envelope
    (hμ : HasAllFiniteMoments (fun x : E => ‖x‖) μ) (C : ℝ) (k : ℕ) :
    Integrable (fun x : E => C * (1 + ‖x‖) ^ k) μ := by
  have h := ((HasAllFiniteMoments.const (μ := μ) 1).add hμ).rpow
    (show 0 ≤ (k : ℝ) by positivity)
  simpa only [Real.rpow_natCast] using (h.const_mul C).integrable

theorem integrable_parameter_polynomialOn
    (hμ : HasAllFiniteMoments (fun x : E => ‖x‖) μ)
    {S : Set E} (hS : ∀ᵐ x ∂μ, x ∈ S) {F : ℝ × E → ℝ}
    (hF : PolynomialBoundOn (univ ×ˢ S) F) (t : ℝ)
    (hmeas : AEStronglyMeasurable (fun x => F (t, x)) μ) :
    Integrable (fun x => F (t, x)) μ := by
  obtain ⟨k, C, _hC, hb⟩ := hF.uniform_parameter t
  apply (integrable_polynomial_envelope hμ C k).mono' hmeas
  filter_upwards [hS] with x hx
  exact hb t ⟨by linarith, by linarith⟩ x hx

theorem continuous_integral_polynomialOn
    (hμ : HasAllFiniteMoments (fun x : E => ‖x‖) μ)
    {S : Set E} (hS : ∀ᵐ x ∂μ, x ∈ S) {F : ℝ × E → ℝ}
    (hF : Continuous F) (hbound : PolynomialBoundOn (univ ×ˢ S) F) :
    Continuous (fun t : ℝ => ∫ x, F (t, x) ∂μ) := by
  rw [continuous_iff_continuousAt]
  intro t
  obtain ⟨k, C, _hC, hb⟩ := hbound.uniform_parameter t
  apply continuousAt_of_dominated
    (bound := fun x : E => C * (1 + ‖x‖) ^ k)
  · exact Eventually.of_forall fun s =>
      (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [Icc_mem_nhds (show t - 1 < t by linarith)
      (show t < t + 1 by linarith)] with s hs
    filter_upwards [hS] with x hx
    exact hb s hs x hx
  · exact integrable_polynomial_envelope hμ C k
  · exact Eventually.of_forall fun x =>
      (hF.comp (continuous_id.prodMk continuous_const)).continuousAt

theorem continuous_parameterDerivative_of_c1 {F : ℝ × E → ℝ}
    (hF : ContDiff ℝ 1 F) : Continuous (parameterDerivative F) := by
  exact (hF.continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem hasDerivAt_parameter_slice_of_c1 {F : ℝ × E → ℝ}
    (hF : ContDiff ℝ 1 F) (x : E) (t : ℝ) :
    HasDerivAt (fun s => F (s, x)) (parameterDerivative F (t, x)) t := by
  have hpair : HasDerivAt (fun s : ℝ => (s, x)) (1, 0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  exact (hF.differentiable (by norm_num) (t, x)).hasFDerivAt.comp_hasDerivAt t hpair

theorem hasDerivAt_integral_c1PolynomialOn
    (hμ : HasAllFiniteMoments (fun x : E => ‖x‖) μ)
    {S : Set E} (hS : ∀ᵐ x ∂μ, x ∈ S) {F : ℝ × E → ℝ}
    (hF : C1PolynomialOn (univ ×ˢ S) F) (t : ℝ) :
    HasDerivAt (fun s => ∫ x, F (s, x) ∂μ)
      (∫ x, parameterDerivative F (t, x) ∂μ) t := by
  have hD : PolynomialBoundOn (univ ×ˢ S) (parameterDerivative F) :=
    hF.derivative.clm_apply (PolynomialBoundOn.const _ (1, (0 : E)))
  have hDc := continuous_parameterDerivative_of_c1 hF.regular
  obtain ⟨k, C, _hC, hb⟩ := hD.uniform_parameter t
  let data : IntegralDerivativeData μ (fun s x => F (s, x))
      (fun s x => parameterDerivative F (s, x)) t := {
    neighborhood := Icc (t - 1) (t + 1)
    neighborhood_mem := Icc_mem_nhds (by linarith) (by linarith)
    bound := fun x => C * (1 + ‖x‖) ^ k
    measurable_near := Eventually.of_forall fun s =>
      (hF.regular.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    integrable_at := integrable_parameter_polynomialOn hμ hS hF.value t
      ((hF.regular.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    derivative_measurable :=
      (hDc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    derivative_bound := hS.mono fun x hx s hs => hb s hs x hx
    integrable_bound := integrable_polynomial_envelope hμ C k
    has_derivative := Eventually.of_forall fun x s _ =>
      hasDerivAt_parameter_slice_of_c1 hF.regular x s }
  exact data.hasDerivAt

end Wishart.FiniteOrder

end
