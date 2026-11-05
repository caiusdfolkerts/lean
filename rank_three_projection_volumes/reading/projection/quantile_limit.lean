module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.Ring.Basic

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace RankThreeProjection.QuantileStability

/-- The elementary integral Cauchy–Schwarz inequality, obtained by integrating
a square. The hypotheses explicitly include both required integrabilities. -/
theorem integral_sq_le_mass_mul_integral_sq
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → ℝ) (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ)
    (hm : 0 < μ.real univ) :
    (∫ x, f x ∂μ) ^ 2 ≤ μ.real univ * ∫ x, f x ^ 2 ∂μ := by
  let I := ∫ x, f x ∂μ
  let J := ∫ x, f x ^ 2 ∂μ
  let m := μ.real univ
  let c := I / m
  have hc : c * m = I := div_mul_cancel₀ _ hm.ne'
  have hnonneg : 0 ≤ ∫ x, (f x - c) ^ 2 ∂μ :=
    integral_nonneg (fun _ => sq_nonneg _)
  have he : (∫ x, (f x - c) ^ 2 ∂μ) = J - 2 * c * I + c ^ 2 * m := by
    calc
      _ = ∫ x, (f x ^ 2 - (2 * c) * f x) + c ^ 2 ∂μ := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun _ => by ring)
      _ = _ := by
        have hAdd := integral_add (hf2.sub (hf.const_mul (2 * c)))
          (integrable_const (c ^ 2))
        simp only [Pi.sub_apply] at hAdd
        rw [hAdd, integral_sub hf2 (hf.const_mul (2 * c)),
          integral_const_mul, integral_const]
        change J - (2 * c) * I + m * c ^ 2 = _
        ring
  rw [he] at hnonneg
  have hp := mul_nonneg hnonneg hm.le
  have he' : (J - 2 * c * I + c ^ 2 * m) * m = m * J - I ^ 2 := by
    rw [← hc]
    ring
  rw [he'] at hp
  exact sub_nonneg.mp hp

/-- A one-dimensional energy bound controls oscillation. No Sobolev
completion or boundary regularity theorem is used. -/
theorem oscillation_sq_le_interval_energy (f v : ℝ → ℝ) {a b : ℝ}
    (hab : a ≤ b)
    (hderiv : ∀ x ∈ Icc a b, HasDerivAt f (v x) x)
    (hcont : ContinuousOn v (Icc a b)) :
    (f b - f a) ^ 2 ≤ (b - a) * ∫ x in Icc a b, v x ^ 2 := by
  rcases hab.lt_or_eq with hab | rfl
  · let μ : Measure ℝ := volume.restrict (Icc a b)
    letI : IsFiniteMeasure μ := ⟨by simp [μ, Real.volume_Icc]⟩
    have hm : μ.real univ = b - a := by
      simp [μ, Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (sub_pos.mpr hab).le]
    have hCS := integral_sq_le_mass_mul_integral_sq μ v hcont.integrableOn_Icc
      (hcont.pow 2).integrableOn_Icc (by rw [hm]; exact sub_pos.mpr hab)
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (by simpa only [uIcc_of_le hab.le] using hderiv) (hcont.intervalIntegrable_of_Icc hab.le)
    have hI : (∫ x in Icc a b, v x) = f b - f a := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le]
      exact hFTC
    change (∫ x in Icc a b, v x) ^ 2 ≤ μ.real univ *
      ∫ x in Icc a b, v x ^ 2 at hCS
    rw [hI, hm] at hCS
    exact hCS
  · simp

/-- An energy `o(t²)` makes the corresponding oscillation `o(t)`. -/
theorem tendsto_scaled_oscillation_of_energy
    (f v : ℝ → ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hderiv : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ∀ x ∈ Icc a b, HasDerivAt (f t) (v t x) x)
    (hcont : ∀ᶠ t in 𝓝[>] (0 : ℝ), ContinuousOn (v t) (Icc a b))
    (henergy : Tendsto
      (fun t : ℝ => (∫ x in Icc a b, v t x ^ 2) / t ^ 2) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun t : ℝ => (f t b - f t a) / t) (𝓝[>] 0) (𝓝 0) := by
  have hbound : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ((f t b - f t a) / t) ^ 2 ≤
        (b - a) * ((∫ x in Icc a b, v t x ^ 2) / t ^ 2) := by
    filter_upwards [hderiv, hcont] with t hd hc
    have h := div_le_div_of_nonneg_right
      (oscillation_sq_le_interval_energy (f t) (v t) hab hd hc) (sq_nonneg t)
    simpa only [div_pow, mul_div_assoc] using h
  have hsquare : Tendsto (fun t : ℝ => ((f t b - f t a) / t) ^ 2)
      (𝓝[>] 0) (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun _ => sq_nonneg _)) hbound
      (by simpa only [mul_zero] using tendsto_const_nhds.mul henergy)
  have habs := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero,
    Real.norm_eq_abs] using habs

/-- A bounded family whose pairwise oscillations vanish has a unique limit
once its mean is prescribed. The conclusion includes convergence in `L¹`,
which is what is needed for the ridge-test argument. -/
theorem mean_determines_flat_limit
    {ι X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {l : Filter ι} [l.IsCountablyGenerated]
    (F : ι → X → ℝ) (x₀ : X) (C c : ℝ)
    (hmeas : ∀ᶠ i in l, AEStronglyMeasurable (F i) μ)
    (hbound : ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖F i x‖ ≤ C)
    (hbound₀ : ∀ᶠ i in l, ‖F i x₀‖ ≤ C)
    (hosc : ∀ᵐ x ∂μ, Tendsto (fun i => F i x - F i x₀) l (𝓝 0))
    (hmean : Tendsto (fun i => ∫ x, F i x ∂μ) l (𝓝 c)) :
    Tendsto (fun i => F i x₀) l (𝓝 c) ∧
      (∀ᵐ x ∂μ, Tendsto (fun i => F i x) l (𝓝 c)) ∧
      Tendsto (fun i => ∫ x, ‖F i x - c‖ ∂μ) l (𝓝 0) := by
  have hint : ∀ᶠ i in l, Integrable (F i) μ := by
    filter_upwards [hmeas, hbound] with i hi hb
    exact (integrable_const C).mono' hi hb
  have hGmeas : ∀ᶠ i in l, AEStronglyMeasurable (fun x => F i x - F i x₀) μ :=
    hmeas.mono (fun i hi => hi.sub aestronglyMeasurable_const)
  have hGbound : ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖F i x - F i x₀‖ ≤ 2 * C := by
    filter_upwards [hbound, hbound₀] with i hi hi₀
    filter_upwards [hi] with x hx
    have h := (norm_sub_le (F i x) (F i x₀)).trans (add_le_add hx hi₀)
    linarith
  have hGlim : Tendsto (fun i => ∫ x, F i x - F i x₀ ∂μ) l (𝓝 0) := by
    simpa only [integral_zero] using
      tendsto_integral_filter_of_dominated_convergence (fun _ : X => 2 * C)
        hGmeas hGbound (integrable_const (2 * C)) hosc
  have hsplit : (fun i => ∫ x, F i x - F i x₀ ∂μ) =ᶠ[l]
      (fun i => (∫ x, F i x ∂μ) - F i x₀) := by
    filter_upwards [hint] with i hi
    rw [integral_sub hi (integrable_const (F i x₀))]
    simp
  have hdiff := Filter.Tendsto.congr' hsplit hGlim
  have h₀ : Tendsto (fun i => F i x₀) l (𝓝 c) := by
    simpa only [sub_sub_cancel, sub_zero] using hmean.sub hdiff
  have hpoint : ∀ᵐ x ∂μ, Tendsto (fun i => F i x) l (𝓝 c) := by
    filter_upwards [hosc] with x hx
    simpa only [sub_add_cancel, zero_add] using hx.add h₀
  refine ⟨h₀, hpoint, ?_⟩
  have hNmeas : ∀ᶠ i in l, AEStronglyMeasurable (fun x => ‖F i x - c‖) μ :=
    hmeas.mono (fun i hi => (hi.sub aestronglyMeasurable_const).norm)
  have hNbound : ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖‖F i x - c‖‖ ≤ C + ‖c‖ := by
    filter_upwards [hbound] with i hi
    filter_upwards [hi] with x hx
    rw [norm_norm]
    exact (norm_sub_le _ _).trans (add_le_add hx le_rfl)
  have hNlim : ∀ᵐ x ∂μ, Tendsto (fun i => ‖F i x - c‖) l (𝓝 (0 : ℝ)) := by
    filter_upwards [hpoint] with x hx
    simpa only [sub_self, norm_zero] using
      (hx.sub (tendsto_const_nhds : Tendsto (fun _ : ι => c) l (𝓝 c))).norm
  simpa only [integral_zero] using
    tendsto_integral_filter_of_dominated_convergence (fun _ : X => C + ‖c‖)
      hNmeas hNbound (integrable_const (C + ‖c‖)) hNlim

/-- Integration preserves a unit Lipschitz estimate for the difference
quotient. This turns the centered quantile `L¹` limit into cosine and sine
first-variation identities without differentiating the test functions. -/
theorem integral_lipschitz_difference_quotient_le
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f g : X → ℝ) (ψ : ℝ → ℝ) (t : ℝ)
    (hψ : ∀ x y : ℝ, |ψ x - ψ y| ≤ |x - y|)
    (hfi : Integrable (fun x => ψ (f x)) μ)
    (hgi : Integrable (fun x => ψ (g x)) μ)
    (hdi : Integrable (fun x => (g x - f x) / t) μ) :
    |((∫ x, ψ (g x) ∂μ) - ∫ x, ψ (f x) ∂μ) / t| ≤
      ∫ x, |(g x - f x) / t| ∂μ := by
  rw [← integral_sub hgi hfi, ← integral_div]
  calc
    _ ≤ ∫ x, |(ψ (g x) - ψ (f x)) / t| ∂μ := by
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (fun x => (ψ (g x) - ψ (f x)) / t)
    _ ≤ _ := by
      apply integral_mono ((hgi.sub hfi).div_const t).norm hdi.norm
      intro x
      simp only [Real.norm_eq_abs, abs_div]
      exact div_le_div_of_nonneg_right (hψ (g x) (f x)) (abs_nonneg t)

/-- The right derivative at zero, in the convenient quotient form used by
the quantile and volume-polynomial arguments. -/
theorem hasDerivWithinAt_Ici_zero_iff_div {f : ℝ → ℝ} {c : ℝ}
    (hf0 : f 0 = 0) :
    HasDerivWithinAt f c (Ici 0) 0 ↔
      Tendsto (fun t : ℝ => f t / t) (𝓝[>] 0) (𝓝 c) := by
  have hset : Ici (0 : ℝ) \ {0} = Ioi 0 := by
    ext t
    simp only [Set.mem_sdiff, mem_Ici, mem_singleton_iff, mem_Ioi]
    exact ⟨fun h => lt_of_le_of_ne h.1 (Ne.symm h.2), fun h => ⟨h.le, h.ne'⟩⟩
  have hslope : slope f 0 = (fun t : ℝ => f t / t) := by
    funext t
    simp only [slope_def_field, hf0, sub_zero]
  rw [hasDerivWithinAt_iff_tendsto_slope, hset, hslope]

end RankThreeProjection.QuantileStability
