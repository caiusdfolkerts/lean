module
public import PaperVerification.GeometricMeanLog
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
@[expose] public section
noncomputable section

namespace PaperVerification.Hyperbolic

open MeasureTheory Set Filter Topology

variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [CompactSpace X] [OpensMeasurableSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [CompactSpace Y] [OpensMeasurableSpace Y]

theorem geometricMoment_congr_ae (k : ℝ) {f g : C(X, ℝ)} (μ : ProbabilityMeasure X)
    (h : ∀ᵐ x ∂(μ : Measure X), f x = g x) :
    geometricMoment k f μ = geometricMoment k g μ := by
  unfold geometricMoment
  congr 1
  funext n
  unfold truncatedGeometricMoment
  congr 2
  apply integral_congr_ae
  filter_upwards [h] with x hx
  simp only [truncatedLog, ContinuousMap.coe_mk, hx]

theorem geometricMoment_map [BorelSpace Y] (k : ℝ) (f : C(Y, ℝ)) (T : C(X, Y))
    (μ : ProbabilityMeasure X) :
    geometricMoment k f (μ.map T) = geometricMoment k (f.comp T) μ := by
  unfold geometricMoment
  congr 1
  funext n
  unfold truncatedGeometricMoment
  congr 2
  change (∫ y, truncatedLog f n y ∂Measure.map T (μ : Measure X)) = _
  rw [integral_map_of_stronglyMeasurable T.continuous.measurable
    (truncatedLog f n).continuous.stronglyMeasurable]
  rfl

theorem geometricMoment_const (k : ℝ) (hk : 0 ≤ k) {c : ℝ} (hc : 0 < c)
    (μ : ProbabilityMeasure X) :
    geometricMoment k (ContinuousMap.const X c) μ = c ^ k := by
  rw [geometricMoment_eq_exp_integral_of_lower_bound k hk _ μ hc (fun _ ↦ le_rfl)]
  simp only [ContinuousMap.const_apply, integral_const, measureReal_def, measure_univ,
    ENNReal.toReal_one, one_smul]
  rw [Real.rpow_def_of_pos hc]
  congr 1
  ring

theorem geometricMean_const {c : ℝ} (hc : 0 < c) (μ : ProbabilityMeasure X) :
    geometricMean (ContinuousMap.const X c) μ = c := by
  rw [geometricMean, geometricMoment_const 1 zero_le_one hc, Real.rpow_one]

/-- Multiplication by a positive continuous factor, including zero and divergent means. -/
theorem geometricMoment_mul_pos_right (k : ℝ) (hk : 0 < k) (f g : C(X, ℝ))
    (μ : ProbabilityMeasure X) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 < g x) :
    geometricMoment k (f * g) μ = geometricMoment k f μ * geometricMoment k g μ := by
  let logg : C(X, ℝ) := ⟨fun x ↦ Real.log (g x), g.continuous.log (fun x ↦ (hg x).ne')⟩
  have hglog : Integrable (fun x ↦ Real.log (g x)) (μ : Measure X) :=
    integrable_continuousMap logg μ
  have hgae : ∀ᵐ x ∂(μ : Measure X), 0 < g x := Eventually.of_forall hg
  have hfg : ∀ x, 0 ≤ (f * g) x := fun x ↦ mul_nonneg (hf x) (hg x).le
  by_cases hfzero : geometricMoment k f μ = 0
  · have hzero : geometricMoment k (f * g) μ = 0 := by
      by_contra hne
      have hp : 0 < geometricMoment k (f * g) μ :=
        lt_of_le_of_ne (geometricMoment_nonneg k (f * g) μ) (Ne.symm hne)
      obtain ⟨hpae, hplog⟩ :=
        ae_pos_and_integrable_log_of_geometricMoment_pos k hk (f * g) μ hfg hp
      have hfae : ∀ᵐ x ∂(μ : Measure X), 0 < f x := by
        filter_upwards [hpae] with x hx
        change 0 < f x * g x at hx
        exact pos_of_mul_pos_right (by simpa only [mul_comm] using hx) (hg x).le
      have hlogf : Integrable (fun x ↦ Real.log (f x)) (μ : Measure X) := by
        apply (hplog.sub hglog).congr
        filter_upwards [hfae] with x hx
        change Real.log (f x * g x) - Real.log (g x) = Real.log (f x)
        rw [Real.log_mul hx.ne' (hg x).ne']
        ring
      have hp' := (geometricMoment_pos_iff k hk f μ hf).mpr ⟨hfae, hlogf⟩
      rw [hfzero] at hp'
      exact (lt_irrefl _) hp'
    rw [hzero, hfzero, zero_mul]
  · have hp : 0 < geometricMoment k f μ :=
      lt_of_le_of_ne (geometricMoment_nonneg k f μ) (Ne.symm hfzero)
    obtain ⟨hfae, hflog⟩ := ae_pos_and_integrable_log_of_geometricMoment_pos k hk f μ hf hp
    have hpae : ∀ᵐ x ∂(μ : Measure X), 0 < (f * g) x := by
      filter_upwards [hfae] with x hx
      exact mul_pos hx (hg x)
    have hlogeq : (fun x ↦ Real.log ((f * g) x)) =ᵐ[(μ : Measure X)]
        (fun x ↦ Real.log (f x) + Real.log (g x)) := by
      filter_upwards [hfae] with x hx
      exact Real.log_mul hx.ne' (hg x).ne'
    have hplog : Integrable (fun x ↦ Real.log ((f * g) x)) (μ : Measure X) :=
      (hflog.add hglog).congr hlogeq.symm
    rw [geometricMoment_eq_exp_integral_of_integrable_log k hk.le (f * g) μ hpae hplog,
      geometricMoment_eq_exp_integral_of_integrable_log k hk.le f μ hfae hflog,
      geometricMoment_eq_exp_integral_of_integrable_log k hk.le g μ hgae hglog,
      integral_congr_ae hlogeq, integral_add hflog hglog, mul_add, Real.exp_add]

theorem geometricMean_mul_pos_right (f g : C(X, ℝ)) (μ : ProbabilityMeasure X)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 < g x) :
    geometricMean (f * g) μ = geometricMean f μ * geometricMean g μ :=
  geometricMoment_mul_pos_right 1 zero_lt_one f g μ hf hg

theorem geometricMean_ge_const (f : C(X, ℝ)) (μ : ProbabilityMeasure X)
    {c : ℝ} (hc : 0 < c) (hf : ∀ x, c ≤ f x) : c ≤ geometricMean f μ := by
  rw [← geometricMean_const hc μ]
  exact geometricMoment_mono 1 zero_le_one hf μ

/-- Equality in a positive uniform lower bound is exactly almost-everywhere equality. -/
theorem geometricMean_eq_const_iff (f : C(X, ℝ)) (μ : ProbabilityMeasure X)
    {c : ℝ} (hc : 0 < c) (hf : ∀ x, c ≤ f x) :
    geometricMean f μ = c ↔ ∀ᵐ x ∂(μ : Measure X), f x = c := by
  let logf : C(X, ℝ) := ⟨fun x ↦ Real.log (f x),
    f.continuous.log (fun x ↦ (hc.trans_le (hf x)).ne')⟩
  have hi : Integrable (fun x ↦ Real.log (f x)) (μ : Measure X) :=
    integrable_continuousMap logf μ
  have hcint : (∫ _ : X, Real.log c ∂μ) = Real.log c := by simp
  have heq : geometricMean f μ = Real.exp (∫ x, Real.log (f x) ∂μ) := by
    simpa only [geometricMean, one_mul] using geometricMoment_eq_exp_integral_of_lower_bound
      1 zero_le_one f μ hc hf
  constructor
  · intro h
    rw [heq, ← Real.exp_log hc] at h
    have hint : (∫ _ : X, Real.log c ∂μ) = ∫ x, Real.log (f x) ∂μ := by
      rw [hcint]
      exact (Real.exp_injective h).symm
    have hae := (integral_eq_iff_of_ae_le (integrable_const (Real.log c)) hi
      (Eventually.of_forall (fun x ↦ Real.log_le_log hc (hf x)))).mp hint
    filter_upwards [hae] with x hx
    exact (Real.log_injOn_pos (hc.trans_le (hf x)) hc hx.symm)
  · intro h
    change geometricMoment 1 f μ = c
    rw [geometricMoment_congr_ae 1 (g := ContinuousMap.const X c) μ h]
    exact geometricMean_const hc μ

theorem geometricMoment_pos_of_pos (k : ℝ) (hk : 0 < k) (f : C(X, ℝ))
    (μ : ProbabilityMeasure X) (hf : ∀ x, 0 < f x) : 0 < geometricMoment k f μ := by
  let logf : C(X, ℝ) := ⟨fun x ↦ Real.log (f x), f.continuous.log (fun x ↦ (hf x).ne')⟩
  exact (geometricMoment_pos_iff k hk f μ (fun x ↦ (hf x).le)).mpr
    ⟨Eventually.of_forall hf, integrable_continuousMap logf μ⟩

/-- All positive real moments have the expected power law, including zero means. -/
theorem geometricMoment_eq_rpow (k : ℝ) (hk : 0 < k) (f : C(X, ℝ))
    (μ : ProbabilityMeasure X) (hf : ∀ x, 0 ≤ f x) :
    geometricMoment k f μ = geometricMean f μ ^ k := by
  by_cases hz : geometricMean f μ = 0
  · have hm : geometricMoment k f μ = 0 := by
      apply (geometricMoment_eq_zero_iff k hk f μ hf).mpr
      exact (geometricMoment_eq_zero_iff 1 zero_lt_one f μ hf).mp hz
    rw [hm, hz, Real.zero_rpow hk.ne']
  · have hp : 0 < geometricMean f μ :=
      lt_of_le_of_ne (geometricMean_nonneg f μ) (Ne.symm hz)
    obtain ⟨hfae, hflog⟩ :=
      ae_pos_and_integrable_log_of_geometricMoment_pos 1 zero_lt_one f μ hf hp
    have heq : geometricMean f μ = Real.exp (∫ x, Real.log (f x) ∂μ) := by
      simpa only [geometricMean, one_mul] using
        geometricMoment_eq_exp_integral_of_integrable_log 1 zero_le_one f μ hfae hflog
    rw [geometricMoment_eq_exp_integral_of_integrable_log k hk.le f μ hfae hflog,
      heq, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    ring

theorem geometricMean_pow (n : ℕ) (f : C(X, ℝ)) (μ : ProbabilityMeasure X)
    (hf : ∀ x, 0 ≤ f x) : geometricMean (f ^ n) μ = geometricMean f μ ^ n := by
  rcases eq_or_lt_of_le (Nat.zero_le n) with rfl | hn
  · simp only [pow_zero]
    exact geometricMean_const zero_lt_one μ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpower : ∀ x, 0 ≤ (f ^ n) x := fun x ↦ pow_nonneg (hf x) n
  by_cases hz : geometricMean f μ = 0
  · have hpzero : geometricMean (f ^ n) μ = 0 := by
      apply (geometricMoment_eq_zero_iff 1 zero_lt_one (f ^ n) μ hpower).mpr
      rintro ⟨hpae, hplog⟩
      have hfae : ∀ᵐ x ∂(μ : Measure X), 0 < f x := by
        filter_upwards [hpae] with x hx
        apply lt_of_le_of_ne (hf x)
        intro heq
        have hfx : f x = 0 := heq.symm
        simp only [ContinuousMap.coe_pow, Pi.pow_apply, hfx, zero_pow hn.ne'] at hx
        exact (lt_irrefl (0 : ℝ)) hx
      have hflog : Integrable (fun x ↦ Real.log (f x)) (μ : Measure X) := by
        apply (hplog.const_mul (n : ℝ)⁻¹).congr
        exact Eventually.of_forall (fun x ↦ by
          simp only [ContinuousMap.coe_pow, Pi.pow_apply, Real.log_pow]
          field_simp [hnR.ne'])
      have hp := (geometricMoment_pos_iff 1 zero_lt_one f μ hf).mpr ⟨hfae, hflog⟩
      rw [show geometricMoment 1 f μ = geometricMean f μ from rfl, hz] at hp
      exact (lt_irrefl _) hp
    rw [hpzero, hz, zero_pow hn.ne']
  · have hp : 0 < geometricMean f μ :=
      lt_of_le_of_ne (geometricMean_nonneg f μ) (Ne.symm hz)
    obtain ⟨hfae, hflog⟩ :=
      ae_pos_and_integrable_log_of_geometricMoment_pos 1 zero_lt_one f μ hf hp
    have hpae : ∀ᵐ x ∂(μ : Measure X), 0 < (f ^ n) x := by
      filter_upwards [hfae] with x hx
      exact pow_pos hx n
    have hplog : Integrable (fun x ↦ Real.log ((f ^ n) x)) (μ : Measure X) := by
      simpa only [ContinuousMap.coe_pow, Pi.pow_apply, Real.log_pow] using hflog.const_mul (n : ℝ)
    rw [geometricMean,
      geometricMoment_eq_exp_integral_of_integrable_log 1 zero_le_one (f ^ n) μ hpae hplog,
      ← geometricMoment_nat n f μ,
      geometricMoment_eq_exp_integral_of_integrable_log (n : ℝ) hnR.le f μ hfae hflog]
    simp only [one_mul, ContinuousMap.coe_pow, Pi.pow_apply, Real.log_pow, integral_const_mul]

theorem geometricMoment_nat_pow (k n : ℕ) (f : C(X, ℝ)) (μ : ProbabilityMeasure X)
    (hf : ∀ x, 0 ≤ f x) :
    geometricMoment (k : ℝ) (f ^ n) μ = geometricMoment ((n * k : ℕ) : ℝ) f μ := by
  rw [geometricMoment_nat, geometricMean_pow n f μ hf, ← pow_mul, ← geometricMoment_nat]


end PaperVerification.Hyperbolic
