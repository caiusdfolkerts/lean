module

public import wishart.verified.field_common_base
public import tau_ceti.analysis.inner_product_space.harmonic.subharmonic
public import tau_ceti.analysis.inner_product_space.harmonic.mean_value.basic
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Analysis.CStarAlgebra.Unitary.Maps
public import Mathlib.Data.Real.Star

/- Generated ordinary proof stage. See audit/staged_field_analytic/FieldAnalytic01/manifest.json. -/

@[expose] public section

section CanonicalSource0
/- Source: Wishart/ScalarFieldSubharmonic.lean -/



/-!
# The scalar submean argument for the complex and quaternion cases

The regularized factors used in Section 7 are continuous and finite. We use
the submean inequality on every ball, which is preserved by sums, maxima,
convex increasing composition, and integrable averaging. Its implication for
the usual continuous subharmonicity notion gives the maximum principle. A
radial subharmonic average is therefore increasing in the squared radius.
-/

noncomputable section
open MeasureTheory InnerProductSpace Laplacian Metric Set Filter Topology TauCeti
open scoped Classical BigOperators

namespace WishartVerification

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The ordinary submean inequality on all balls of an entire continuous
function. This is an analytic property, not a definition of the desired
Wishart expectation comparison. -/
structure BallSubmean (f : E → ℝ) : Prop where
  continuous : Continuous f
  le_average : ∀ (x : E) (r : ℝ), 0 < r → f x ≤ ⨍ y in ball x r, f y

theorem continuous_integrableOn_ball {f : E → ℝ} (hf : Continuous f)
    (x : E) (r : ℝ) : IntegrableOn f (ball x r) :=
  (hf.continuousOn.integrableOn_compact (isCompact_closedBall x r)).mono_set
    ball_subset_closedBall

theorem setAverage_mono_continuous {f g : E → ℝ} (hf : Continuous f)
    (hg : Continuous g) (hle : ∀ x, f x ≤ g x) (x : E) (r : ℝ) :
    (⨍ y in ball x r, f y) ≤ ⨍ y in ball x r, g y := by
  rw [setAverage_eq, setAverage_eq]
  exact smul_le_smul_of_nonneg_left
    (integral_mono (continuous_integrableOn_ball hf x r)
      (continuous_integrableOn_ball hg x r) hle) (inv_nonneg.mpr measureReal_nonneg)

theorem BallSubmean.of_contDiff_laplacian_nonneg {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hΔ : ∀ x, 0 ≤ Δ f x) : BallSubmean f := by
  refine ⟨hf.continuous, ?_⟩
  intro x r hr
  exact le_setAverage_ball_of_laplacian_nonneg hf.contDiffOn hf.continuous.continuousOn
    (fun y _ => hΔ y) hr

theorem BallSubmean.subharmonicOn {f : E → ℝ} (hf : BallSubmean f) (U : Set E) :
    SubharmonicOn f U := by
  refine ⟨hf.continuous.continuousOn, ?_⟩
  intro x hx
  have h : ∀ᶠ r in 𝓝[>] (0 : ℝ), f x ≤ ⨍ y in ball x r, f y := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact hf.le_average x r hr
  exact h.frequently

theorem BallSubmean.const (c : ℝ) : BallSubmean (fun _ : E => c) := by
  refine ⟨continuous_const, ?_⟩
  intro x r hr
  haveI : IsFiniteMeasure (volume.restrict (ball x r) : Measure E) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  haveI : NeZero (volume.restrict (ball x r) : Measure E) :=
    ⟨mt Measure.restrict_eq_zero.mp (measure_ball_pos volume x hr).ne'⟩
  exact (average_const _ c).ge

theorem BallSubmean.add {f g : E → ℝ} (hf : BallSubmean f) (hg : BallSubmean g) :
    BallSubmean (fun x => f x + g x) := by
  refine ⟨hf.continuous.add hg.continuous, ?_⟩
  intro x r hr
  rw [setAverage_fun_add (continuous_integrableOn_ball hf.continuous x r)
    (continuous_integrableOn_ball hg.continuous x r)]
  exact add_le_add (hf.le_average x r hr) (hg.le_average x r hr)

theorem BallSubmean.const_mul {f : E → ℝ} (hf : BallSubmean f) {c : ℝ} (hc : 0 ≤ c) :
    BallSubmean (fun x => c * f x) := by
  refine ⟨continuous_const.mul hf.continuous, ?_⟩
  intro x r hr
  rw [average_const_mul]
  exact mul_le_mul_of_nonneg_left (hf.le_average x r hr) hc

theorem BallSubmean.finset_sum {ι : Type*} (s : Finset ι) (f : ι → E → ℝ)
    (hf : ∀ i ∈ s, BallSubmean (f i)) : BallSubmean (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using BallSubmean.const (E := E) 0
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using (hf i (Finset.mem_insert_self i s)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- A continuous upper envelope inherits the submean inequality when every
point has an attaining submean minorant. The indexing set need not be finite. -/
theorem BallSubmean.of_attaining_minorants {f : E → ℝ} (hf : Continuous f)
    (hminorant : ∀ x, ∃ g : E → ℝ,
      BallSubmean g ∧ (∀ y, g y ≤ f y) ∧ g x = f x) : BallSubmean f := by
  refine ⟨hf, ?_⟩
  intro x r hr
  obtain ⟨g, hg, hgf, htouch⟩ := hminorant x
  rw [← htouch]
  exact (hg.le_average x r hr).trans
    (setAverage_mono_continuous hg.continuous hf hgf x r)

theorem BallSubmean.max {f g : E → ℝ} (hf : BallSubmean f) (hg : BallSubmean g) :
    BallSubmean (fun x => max (f x) (g x)) := by
  apply BallSubmean.of_attaining_minorants (hf.continuous.max hg.continuous)
  intro x
  rcases le_total (f x) (g x) with h | h
  · exact ⟨g, hg, fun y => le_max_right _ _, (max_eq_right h).symm⟩
  · exact ⟨f, hf, fun y => le_max_left _ _, (max_eq_left h).symm⟩

theorem BallSubmean.exp {f : E → ℝ} (hf : BallSubmean f) :
    BallSubmean (fun x => Real.exp (f x)) := by
  refine ⟨Real.continuous_exp.comp hf.continuous, ?_⟩
  intro x r hr
  haveI : IsFiniteMeasure (volume.restrict (ball x r) : Measure E) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  haveI : NeZero (volume.restrict (ball x r) : Measure E) :=
    ⟨mt Measure.restrict_eq_zero.mp (measure_ball_pos volume x hr).ne'⟩
  exact (Real.exp_le_exp.mpr (hf.le_average x r hr)).trans
    (convexOn_exp.map_average_le Real.continuous_exp.continuousOn isClosed_univ
      (Filter.Eventually.of_forall fun _ => Set.mem_univ _)
      (continuous_integrableOn_ball hf.continuous x r)
      (continuous_integrableOn_ball (Real.continuous_exp.comp hf.continuous) x r))

/-- Fubini passes the actual submean inequality through an integrable average.
The application supplies the integrability and continuity from polynomial
growth and the Gaussian moments. -/
theorem BallSubmean.integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (F : Ω → E → ℝ)
    (hF : ∀ᵐ z ∂μ, BallSubmean (F z))
    (hpoint : ∀ x, Integrable (fun z => F z x) μ)
    (hjoint : ∀ x r, 0 < r → Integrable (fun z : Ω × E => F z.1 z.2)
      (μ.prod (volume.restrict (ball x r))))
    (hcont : Continuous (fun x => ∫ z, F z x ∂μ)) :
    BallSubmean (fun x => ∫ z, F z x ∂μ) := by
  refine ⟨hcont, ?_⟩
  intro x r hr
  have hint := hjoint x r hr
  have hav : Integrable (fun z => ⨍ y in ball x r, F z y) μ := by
    simpa only [setAverage_eq, smul_eq_mul] using
      hint.integral_prod_left.const_mul ((volume.real (ball x r))⁻¹)
  calc
    (∫ z, F z x ∂μ) ≤ ∫ z, (⨍ y in ball x r, F z y) ∂μ :=
      integral_mono_ae (hpoint x) hav (hF.mono fun z hz => hz.le_average x r hr)
    _ = ⨍ y in ball x r, ∫ z, F z y ∂μ := by
      simp only [setAverage_eq, smul_eq_mul]
      rw [integral_const_mul, integral_integral_swap hint]

/-- The maximum principle is the precise reason that a radial submean
function increases with the squared radius. -/
theorem BallSubmean.monotoneOn_sqrt_smul [Nontrivial E] {F : E → ℝ}
    (hF : BallSubmean F)
    (hradial : ∀ x y : E, ‖x‖ = ‖y‖ → F x = F y) (v : E) :
    MonotoneOn (fun t : ℝ => F (Real.sqrt t • v)) (Ici 0) := by
  intro s hs t ht hst
  let y := Real.sqrt t • v
  have hball : Real.sqrt s • v ∈ closedBall (0 : E) ‖y‖ := by
    rw [mem_closedBall, dist_zero_right]
    simp only [y, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hst) (norm_nonneg v)
  apply (hF.subharmonicOn (ball (0 : E) ‖y‖)).le_of_le_sphere
    hF.continuous.continuousOn (harmonicOnNhd_const (F y)) continuous_const.continuousOn _ _ hball
  intro x hx
  apply le_of_eq
  apply hradial
  simpa only [mem_sphere, dist_zero_right] using hx

end WishartVerification
end
end CanonicalSource0

section CanonicalSource1
/- Source: Wishart/ShiftedNormLog.lean -/



/-!
# The dimension-dependent logarithmic Laplacian

For `q(u) = d ‖u-a‖² + e`, the calculation gives
`Δ log q = 2 (dim E - 2) d / q + 4 d e / q²`.
Thus dimensions two and four admit the single-row comparison used in
Section 7, even when a mean direction lies outside the Gaussian covariance
range. The positive constant `e` is supplied by the determinant lemma.
-/

noncomputable section
open MeasureTheory InnerProductSpace Laplacian Gradient TauCeti
open scoped RealInnerProductSpace

namespace WishartVerification

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def positiveRadialQuadratic (d e : ℝ) (u : E) : ℝ := d * ‖u‖ ^ 2 + e

theorem positiveRadialQuadratic_pos {d e : ℝ} (hd : 0 ≤ d) (he : 0 < e) (u : E) :
    0 < positiveRadialQuadratic d e u :=
  add_pos_of_nonneg_of_pos (mul_nonneg hd (sq_nonneg _)) he

theorem contDiff_positiveRadialQuadratic (d e : ℝ) :
    ContDiff ℝ 2 (positiveRadialQuadratic (E := E) d e) := by
  have h : ContDiff ℝ 2 (fun u : E => ‖u‖ ^ 2) := contDiff_norm_sq ℝ
  exact (contDiff_const.mul h).add contDiff_const

theorem fderiv_positiveRadialQuadratic (d e : ℝ) (u : E) :
    fderiv ℝ (positiveRadialQuadratic d e) u = (2 * d : ℝ) • innerSL ℝ u := by
  change fderiv ℝ (fun y : E => d * ‖y‖ ^ 2 + e) u = _
  rw [fderiv_add_const,
    fderiv_const_mul (hasStrictFDerivAt_norm_sq u).hasFDerivAt.differentiableAt,
    fderiv_norm_sq_apply]
  ext v
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem norm_gradient_positiveRadialQuadratic_sq {d e : ℝ} (hd : 0 ≤ d) (u : E) :
    ‖∇ (positiveRadialQuadratic d e) u‖ ^ 2 = 4 * d ^ 2 * ‖u‖ ^ 2 := by
  have hnorm : ‖∇ (positiveRadialQuadratic d e) u‖ =
      ‖fderiv ℝ (positiveRadialQuadratic d e) u‖ :=
    (toDual ℝ E).symm.norm_map _
  rw [hnorm, fderiv_positiveRadialQuadratic,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) hd),
    innerSL_apply_norm]
  ring

theorem laplacian_positiveRadialQuadratic (d e : ℝ) (u : E) :
    Δ (positiveRadialQuadratic (E := E) d e) u =
      2 * (Module.finrank ℝ E : ℝ) * d := by
  have h : ContDiff ℝ 2 (fun y : E => ‖y‖ ^ 2) := contDiff_norm_sq ℝ
  have heq : positiveRadialQuadratic (E := E) d e =
      (d • (fun y : E => ‖y‖ ^ 2)) + (fun _ => e) := rfl
  have hd : ContDiffAt ℝ 2 (d • (fun y : E => ‖y‖ ^ 2)) u :=
    (h.const_smul d).contDiffAt
  rw [heq, hd.laplacian_add
      (contDiffAt_const : ContDiffAt ℝ 2 (fun _ : E => e) u),
    laplacian_smul d h.contDiffAt,
    laplacian_norm_sq, laplacian_const, Pi.zero_apply, add_zero, smul_eq_mul]
  ring

theorem contDiff_log_positiveRadialQuadratic {d e : ℝ} (hd : 0 ≤ d) (he : 0 < e) :
    ContDiff ℝ 2 (fun u : E => Real.log (positiveRadialQuadratic d e u)) := by
  apply (contDiff_positiveRadialQuadratic d e).log
  exact fun u => (positiveRadialQuadratic_pos hd he u).ne'

theorem laplacian_log_positiveRadialQuadratic {d e : ℝ} (hd : 0 ≤ d) (he : 0 < e)
    (u : E) :
    Δ (fun y : E => Real.log (positiveRadialQuadratic d e y)) u =
      2 * ((Module.finrank ℝ E : ℝ) - 2) * d / positiveRadialQuadratic d e u +
        4 * d * e / positiveRadialQuadratic d e u ^ 2 := by
  have hq := positiveRadialQuadratic_pos hd he u
  have hcomp : (fun y : E => Real.log (positiveRadialQuadratic d e y)) =
      Real.log ∘ positiveRadialQuadratic d e := rfl
  rw [hcomp, (Real.contDiffAt_log.mpr hq.ne').laplacian_comp
      (contDiff_positiveRadialQuadratic d e).contDiffAt,
    norm_gradient_positiveRadialQuadratic_sq hd, laplacian_positiveRadialQuadratic]
  simp only [Real.deriv_log', deriv_inv]
  have hqne := hq.ne'
  dsimp only [positiveRadialQuadratic] at hqne ⊢
  field_simp [hqne]
  ring

theorem laplacian_log_shiftedQuadratic {d e : ℝ} (hd : 0 ≤ d) (he : 0 < e)
    (a u : E) :
    Δ (fun y : E => Real.log (d * ‖y - a‖ ^ 2 + e)) u =
      2 * ((Module.finrank ℝ E : ℝ) - 2) * d / (d * ‖u - a‖ ^ 2 + e) +
        4 * d * e / (d * ‖u - a‖ ^ 2 + e) ^ 2 := by
  have h := congrFun (laplacian_comp_add_right
    (fun y : E => Real.log (positiveRadialQuadratic d e y)) (-a)) u
  have h' := h.trans (laplacian_log_positiveRadialQuadratic hd he (u + -a))
  simpa only [sub_eq_add_neg, positiveRadialQuadratic] using h'

theorem ballSubmean_log_shiftedQuadratic [MeasurableSpace E] [BorelSpace E]
    (hdim : 2 ≤ Module.finrank ℝ E) {d e : ℝ} (hd : 0 ≤ d) (he : 0 < e) (a : E) :
    BallSubmean (fun u : E => Real.log (d * ‖u - a‖ ^ 2 + e)) := by
  apply BallSubmean.of_contDiff_laplacian_nonneg
  · exact (contDiff_log_positiveRadialQuadratic hd he).comp
      (contDiff_id.sub contDiff_const)
  · intro u
    rw [laplacian_log_shiftedQuadratic hd he]
    have hdim' : 0 ≤ (Module.finrank ℝ E : ℝ) - 2 := by
      have h : (2 : ℝ) ≤ Module.finrank ℝ E := by exact_mod_cast hdim
      linarith
    have hq := positiveRadialQuadratic_pos hd he (u - a)
    exact add_nonneg
      (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hdim') hd) hq.le)
      (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hd) he.le) (sq_nonneg _))

/-- Completing the square with the quantitative Cauchy--Schwarz bound from
the positive definite compression. The remaining constant is at least one. -/
theorem affineQuadratic_complete_square {c d : ℝ} (hd : 0 < d) (η : E)
    (hη : ‖η‖ ^ 2 ≤ d * (c - 1)) :
    ∃ (a : E) (e : ℝ), 1 ≤ e ∧ ∀ u : E,
      c + 2 * ⟪η, u⟫_ℝ + d * ‖u‖ ^ 2 = d * ‖u - a‖ ^ 2 + e := by
  let a : E := -(d⁻¹ • η)
  let e : ℝ := c - ‖η‖ ^ 2 / d
  have he : 1 ≤ e := by
    have hdiv : ‖η‖ ^ 2 / d ≤ c - 1 := (div_le_iff₀ hd).mpr (by
      simpa only [mul_comm] using hη)
    dsimp only [e]
    linarith
  refine ⟨a, e, he, ?_⟩
  intro u
  have hnorm : ‖u - a‖ ^ 2 = ‖u‖ ^ 2 +
      2 * d⁻¹ * ⟪η, u⟫_ℝ + (d⁻¹) ^ 2 * ‖η‖ ^ 2 := by
    simp only [a, sub_neg_eq_add, norm_add_sq_real, inner_smul_right,
      norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_comm]
    ring
  rw [hnorm]
  dsimp only [e]
  field_simp [hd.ne']
  ring

/-- The precise row-update logarithm of equation (21), including the constant
case `d = 0`. The result is valid in every real dimension at least two. -/
theorem ballSubmean_log_affineQuadratic [MeasurableSpace E] [BorelSpace E]
    (hdim : 2 ≤ Module.finrank ℝ E) {c d : ℝ}
    (hc : 0 < c) (hd : 0 ≤ d) (η : E) (hη : ‖η‖ ^ 2 ≤ d * (c - 1)) :
    BallSubmean (fun u : E => Real.log (c + 2 * ⟪η, u⟫_ℝ + d * ‖u‖ ^ 2)) := by
  rcases hd.eq_or_lt with hd0 | hdpos
  · have hηzero : η = 0 := by
      have hsq : ‖η‖ ^ 2 = 0 := le_antisymm (by simpa only [← hd0, zero_mul] using hη)
        (sq_nonneg _)
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)
    simpa only [← hd0, hηzero, inner_zero_left, mul_zero, zero_mul, add_zero] using
      BallSubmean.const (E := E) (Real.log c)
  · obtain ⟨a, e, he, heq⟩ := affineQuadratic_complete_square hdpos η hη
    have hepos : 0 < e := lt_of_lt_of_le (by norm_num) he
    simpa only [heq] using ballSubmean_log_shiftedQuadratic hdim hdpos.le hepos a

/-- The quantitative cross-term estimate can be read directly from the
global lower bound of the quadratic, including its degenerate constant case.
This avoids a separate matrix Cauchy--Schwarz theorem in the row application. -/
theorem affineQuadratic_cross_bound_of_one_le {c d : ℝ} (hd : 0 ≤ d) (η : E)
    (hlower : ∀ u : E, 1 ≤ c + 2 * ⟪η, u⟫_ℝ + d * ‖u‖ ^ 2) :
    ‖η‖ ^ 2 ≤ d * (c - 1) := by
  rcases hd.eq_or_lt with hd0 | hdpos
  · have hη : η = 0 := by
      by_contra hη
      have hn : ‖η‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hη)
      have ht := hlower ((-(c / (2 * ‖η‖ ^ 2))) • η)
      rw [← hd0, zero_mul, add_zero, inner_smul_right,
        real_inner_self_eq_norm_sq] at ht
      have heq : c + 2 * (-(c / (2 * ‖η‖ ^ 2)) * ‖η‖ ^ 2) = 0 := by
        field_simp [hn]
        ring
      rw [heq] at ht
      norm_num at ht
    simp only [hη, norm_zero, zero_pow (by norm_num : 2 ≠ 0), ← hd0, zero_mul, le_refl]
  · have ht := hlower ((-d⁻¹) • η)
    have heq : c + 2 * ⟪η, (-d⁻¹) • η⟫_ℝ + d * ‖(-d⁻¹) • η‖ ^ 2 =
        c - ‖η‖ ^ 2 / d := by
      rw [inner_smul_right, real_inner_self_eq_norm_sq, norm_smul,
        Real.norm_eq_abs, mul_pow, sq_abs]
      field_simp [hdpos.ne']
      ring
    rw [heq] at ht
    have hdiv : ‖η‖ ^ 2 / d ≤ c - 1 := by linarith
    have h := (div_le_iff₀ hdpos).mp hdiv
    simpa only [mul_comm] using h

theorem ballSubmean_log_affineQuadratic_of_one_le [MeasurableSpace E] [BorelSpace E]
    (hdim : 2 ≤ Module.finrank ℝ E) {c d : ℝ} (hd : 0 ≤ d) (η : E)
    (hlower : ∀ u : E, 1 ≤ c + 2 * ⟪η, u⟫_ℝ + d * ‖u‖ ^ 2) :
    BallSubmean (fun u : E => Real.log (c + 2 * ⟪η, u⟫_ℝ + d * ‖u‖ ^ 2)) := by
  have hc : 0 < c := by
    have h := hlower 0
    simp only [inner_zero_right, mul_zero, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
      add_zero] at h
    linarith
  exact ballSubmean_log_affineQuadratic hdim hc hd η
    (affineQuadratic_cross_bound_of_one_le hd η hlower)

end WishartVerification
end
end CanonicalSource1

section CanonicalSource2
/- Source: Wishart/LogSubmeanClosure.lean -/



/-!
# Products, maxima, and singular limits in the row argument

Positive logarithmically submean functions are closed under the exact finite
operations used by spectral supporting planes. An attaining compression is
sufficient for an upper envelope, even when the family of compressions is
infinite. A separate dominated-limit lemma handles singular offsets; its
continuity and domination conditions are stated explicitly and proved at
the concrete applications.
-/

noncomputable section
open MeasureTheory Metric Set Filter Topology
open scoped Classical BigOperators
namespace WishartVerification

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

structure PositiveLogSubmean (f : E → ℝ) : Prop where
  positive : ∀ x, 0 < f x
  continuous : Continuous f
  logarithm : BallSubmean (fun x => Real.log (f x))

theorem PositiveLogSubmean.toBallSubmean {f : E → ℝ} (hf : PositiveLogSubmean f) :
    BallSubmean f := by
  have h := hf.logarithm.exp
  have heq : (fun x => Real.exp (Real.log (f x))) = f :=
    funext fun x => Real.exp_log (hf.positive x)
  rwa [heq] at h

theorem PositiveLogSubmean.const {c : ℝ} (hc : 0 < c) :
    PositiveLogSubmean (fun _ : E => c) :=
  ⟨fun _ => hc, continuous_const, BallSubmean.const (Real.log c)⟩

theorem PositiveLogSubmean.mul {f g : E → ℝ}
    (hf : PositiveLogSubmean f) (hg : PositiveLogSubmean g) :
    PositiveLogSubmean (fun x => f x * g x) := by
  refine ⟨fun x => mul_pos (hf.positive x) (hg.positive x),
    hf.continuous.mul hg.continuous, ?_⟩
  have heq : (fun x => Real.log (f x * g x)) =
      fun x => Real.log (f x) + Real.log (g x) := by
    funext x
    exact Real.log_mul (hf.positive x).ne' (hg.positive x).ne'
  rw [heq]
  exact hf.logarithm.add hg.logarithm

theorem PositiveLogSubmean.rpow {f : E → ℝ} (hf : PositiveLogSubmean f)
    {a : ℝ} (ha : 0 ≤ a) : PositiveLogSubmean (fun x => f x ^ a) := by
  refine ⟨fun x => Real.rpow_pos_of_pos (hf.positive x) a,
    (Real.continuous_rpow_const ha).comp hf.continuous, ?_⟩
  have heq : (fun x => Real.log (f x ^ a)) = fun x => a * Real.log (f x) :=
    funext fun x => Real.log_rpow (hf.positive x) a
  rw [heq]
  exact hf.logarithm.const_mul ha

theorem PositiveLogSubmean.finset_prod {ι : Type*} (s : Finset ι)
    (f : ι → E → ℝ) (hf : ∀ i ∈ s, PositiveLogSubmean (f i)) :
    PositiveLogSubmean (fun x => ∏ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using PositiveLogSubmean.const (E := E) zero_lt_one
  | @insert i s hi ih =>
    simpa only [Finset.prod_insert hi] using (hf i (Finset.mem_insert_self i s)).mul
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem PositiveLogSubmean.of_attaining_family {ι : Type*}
    (f : ι → E → ℝ) (hf : ∀ i, PositiveLogSubmean (f i))
    {F : E → ℝ} (hF : Continuous F) (hpos : ∀ x, 0 < F x)
    (hle : ∀ i x, f i x ≤ F x) (hattain : ∀ x, ∃ i, f i x = F x) :
    PositiveLogSubmean F := by
  refine ⟨hpos, hF, ?_⟩
  apply BallSubmean.of_attaining_minorants (hF.log (fun x => (hpos x).ne'))
  intro x
  obtain ⟨i, hi⟩ := hattain x
  refine ⟨fun y => Real.log (f i y), (hf i).logarithm, ?_, ?_⟩
  · intro y
    exact Real.log_le_log ((hf i).positive y) (hle i y)
  · exact congrArg Real.log hi

theorem PositiveLogSubmean.finiteMaximum {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → E → ℝ) (hf : ∀ i, PositiveLogSubmean (f i)) :
    PositiveLogSubmean (fun x => finiteMaximum (fun i => f i x)) := by
  apply PositiveLogSubmean.of_attaining_family f hf
    (continuous_finiteMaximum fun i => (hf i).continuous)
    (fun x => finiteMaximum_pos fun i => (hf i).positive x)
    (fun i x => le_finiteMaximum (fun j => f j x) i)
  intro x
  obtain ⟨i, hi, hmax⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => f i x)
  exact ⟨i, hmax.symm⟩

theorem BallSubmean.of_dominated_limit {F : ℕ → E → ℝ} {f : E → ℝ}
    (hF : ∀ n, BallSubmean (F n)) (hf : Continuous f)
    (hlim : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (hbound : ∀ x r, 0 < r → ∃ B : E → ℝ,
      IntegrableOn B (ball x r) ∧ ∀ n y, y ∈ ball x r → ‖F n y‖ ≤ B y) :
    BallSubmean f := by
  refine ⟨hf, ?_⟩
  intro x r hr
  obtain ⟨B, hB, hdom⟩ := hbound x r hr
  have hint : Tendsto (fun n => ∫ y in ball x r, F n y) atTop
      (𝓝 (∫ y in ball x r, f y)) := by
    apply tendsto_integral_of_dominated_convergence B
      (fun n => (hF n).continuous.aestronglyMeasurable) hB
    · intro n
      filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
      exact hdom n y hy
    · exact Filter.Eventually.of_forall hlim
  have hav : Tendsto (fun n => ⨍ y in ball x r, F n y) atTop
      (𝓝 (⨍ y in ball x r, f y)) := by
    simpa only [setAverage_eq, smul_eq_mul] using
      hint.const_mul ((volume.real (ball x r))⁻¹)
  exact le_of_tendsto_of_tendsto (hlim x) hav
    (Filter.Eventually.of_forall fun n => (hF n).le_average x r hr)

/-- A positive regularization may decrease to a function with zeros. The
submean inequality survives because its first term is a continuous bound
on every compact ball. -/
theorem BallSubmean.of_nonnegative_antitone_limit {F : ℕ → E → ℝ} {f : E → ℝ}
    (hF : ∀ n, BallSubmean (F n)) (hf : Continuous f)
    (hnonneg : ∀ n x, 0 ≤ F n x) (hmono : ∀ x, Antitone (fun n => F n x))
    (hlim : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    BallSubmean f := by
  apply BallSubmean.of_dominated_limit hF hf hlim
  intro x r hr
  refine ⟨F 0, continuous_integrableOn_ball (hF 0).continuous x r, ?_⟩
  intro n y hy
  rw [Real.norm_of_nonneg (hnonneg n y)]
  exact hmono y (Nat.zero_le n)

end WishartVerification
end
end CanonicalSource2

section CanonicalSource3
/- Source: Wishart/ComplexRowSubmean.lean -/



/-!
# The complex rank-one row logarithm

The ordinary complex determinant lemma yields a positive real quadratic
factor. Its two-dimensional logarithmic Laplacian has the required sign.
All matrix expressions are actual complex matrices and conjugate transposes;
the determinant is identified explicitly with the product of real Hermitian
eigenvalues.
-/

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexOrder InnerProductSpace RealInnerProductSpace BigOperators Classical
namespace Wishart.ComplexMatrix
open WishartVerification

variable {n : Type*} [Fintype n] [DecidableEq n]

def realDeterminant (A : Matrix n n ℂ) : ℝ := A.det.re

theorem realDeterminant_eq_prod_eigenvalues {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    realDeterminant A = ∏ i, hA.eigenvalues i := by
  rw [realDeterminant, hA.det_eq_prod_eigenvalues]
  simpa only [RCLike.ofReal_eq_complex_ofReal, Complex.ofRealHom_eq_coe,
    Complex.ofReal_re] using
    (congrArg Complex.re
      (map_prod Complex.ofRealHom (fun i => hA.eigenvalues i) Finset.univ)).symm

theorem realDeterminant_pos {A : Matrix n n ℂ} (hA : A.PosDef) :
    0 < realDeterminant A := (RCLike.pos_iff.mp hA.det_pos).1

def scalarRow (u : ℂ) (w : Matrix Unit n ℂ) : Matrix Unit n ℂ :=
  Matrix.of fun i j => u * w i j

@[simp] theorem scalarRow_apply (u : ℂ) (w : Matrix Unit n ℂ) (i : Unit) (j : n) :
    scalarRow u w i j = u * w i j := rfl

def rowPair (Q : Matrix n n ℂ) (a b : Matrix Unit n ℂ) : ℂ :=
  (a * Q⁻¹ * bᴴ) () ()

def rowQuadratic (Q : Matrix n n ℂ) (a : Matrix Unit n ℂ) : ℝ := (rowPair Q a a).re

theorem rowQuadratic_nonneg {Q : Matrix n n ℂ} (hQ : Q.PosDef) (a : Matrix Unit n ℂ) :
    0 ≤ rowQuadratic Q a := by
  have h := hQ.inv.posSemidef.conjTranspose_mul_mul_same aᴴ
  simp only [Matrix.conjTranspose_conjTranspose] at h
  exact (RCLike.nonneg_iff.mp (h.diag_nonneg (i := ()))).1

theorem rowQuadratic_matrix {Q : Matrix n n ℂ} (hQ : Q.PosDef) (a : Matrix Unit n ℂ) :
    a * Q⁻¹ * aᴴ = Matrix.diagonal (fun _ : Unit => (rowQuadratic Q a : ℂ)) := by
  have h := hQ.inv.posSemidef.conjTranspose_mul_mul_same aᴴ
  simp only [Matrix.conjTranspose_conjTranspose] at h
  ext i j
  cases i
  cases j
  apply Complex.ext
  · rfl
  · simpa only [Matrix.diagonal_apply_eq, RCLike.im_eq_complex_im,
      Complex.ofReal_im] using
      (RCLike.nonneg_iff.mp (h.diag_nonneg (i := ()))).2

theorem realDeterminant_rankOne {Q : Matrix n n ℂ} (hQ : Q.PosDef)
    (a : Matrix Unit n ℂ) :
    realDeterminant (Q + aᴴ * a) = realDeterminant Q * (1 + rowQuadratic Q a) := by
  have hd := Matrix.det_add_mul aᴴ a
    ((Matrix.isUnit_iff_isUnit_det Q).mp hQ.isUnit)
  rw [rowQuadratic_matrix hQ,
    Matrix.det_unique (1 + Matrix.diagonal (fun _ : Unit => (rowQuadratic Q a : ℂ)))] at hd
  have h := congrArg Complex.re hd
  simpa only [realDeterminant, Matrix.add_apply, Matrix.one_apply_eq,
    Matrix.diagonal_apply_eq, Complex.mul_re, Complex.add_re, Complex.one_re,
    Complex.ofReal_re, Complex.add_im, Complex.one_im, Complex.ofReal_im,
    zero_add, mul_zero, sub_zero] using h

theorem rowPair_add_left (Q : Matrix n n ℂ) (a b c : Matrix Unit n ℂ) :
    rowPair Q (a + b) c = rowPair Q a c + rowPair Q b c := by
  simp only [rowPair, Matrix.add_mul, Matrix.add_apply]

theorem rowPair_add_right (Q : Matrix n n ℂ) (a b c : Matrix Unit n ℂ) :
    rowPair Q a (b + c) = rowPair Q a b + rowPair Q a c := by
  simp only [rowPair, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_apply]

theorem rowPair_scalar_left (Q : Matrix n n ℂ) (a b : Matrix Unit n ℂ) (u : ℂ) :
    rowPair Q (scalarRow u a) b = u * rowPair Q a b := by
  change (((u • a) * Q⁻¹) * bᴴ) () () = u * ((a * Q⁻¹) * bᴴ) () ()
  rw [Matrix.smul_mul, Matrix.smul_mul]
  rfl

theorem rowPair_scalar_right (Q : Matrix n n ℂ) (a b : Matrix Unit n ℂ) (u : ℂ) :
    rowPair Q a (scalarRow u b) = rowPair Q a b * star u := by
  simp only [rowPair, Matrix.mul_apply, scalarRow_apply, Matrix.conjTranspose_apply,
    star_mul, Finset.sum_mul, mul_assoc]

theorem rowPair_star {Q : Matrix n n ℂ} (hQ : Q.PosDef)
    (a b : Matrix Unit n ℂ) : star (rowPair Q a b) = rowPair Q b a := by
  have h : (a * Q⁻¹ * bᴴ)ᴴ = b * Q⁻¹ * aᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hQ.inv.isHermitian.eq, Matrix.mul_assoc]
  simpa only [rowPair, Matrix.conjTranspose_apply] using congrArg (fun M => M () ()) h

theorem rowPair_self_real {Q : Matrix n n ℂ} (hQ : Q.PosDef)
    (a : Matrix Unit n ℂ) : rowPair Q a a = (rowQuadratic Q a : ℂ) := by
  simpa only [rowPair, Matrix.diagonal_apply_eq] using
    congrArg (fun M => M () ()) (rowQuadratic_matrix hQ a)

theorem complex_scalar_quadratic (u : ℂ) (d : ℝ) :
    (u * ((d : ℂ) * star u)).re = d * ‖u‖ ^ 2 := by
  have heq : u * ((d : ℂ) * star u) = (d : ℂ) * (u * star u) := by ring
  rw [heq, Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow,
    ← Complex.ofReal_mul, Complex.ofReal_re]

theorem complex_re_mul_eq_inner (β u : ℂ) : (u * β).re = ⟪star β, u⟫_ℝ := by
  change (u * β).re = (u * star (star β)).re
  rw [star_star]

theorem rowQuadratic_scalar_shift {Q : Matrix n n ℂ} (hQ : Q.PosDef)
    (a v : Matrix Unit n ℂ) (u : ℂ) :
    rowQuadratic Q (a + scalarRow u v) =
      rowQuadratic Q a + 2 * ⟪star (rowPair Q v a), u⟫_ℝ +
        rowQuadratic Q v * ‖u‖ ^ 2 := by
  change (rowPair Q (a + scalarRow u v) (a + scalarRow u v)).re = _
  rw [rowPair_add_left, rowPair_add_right, rowPair_add_right,
    rowPair_scalar_right, rowPair_scalar_left, rowPair_scalar_left,
    rowPair_scalar_right]
  rw [← rowPair_star hQ v a, rowPair_self_real hQ v]
  simp only [Complex.add_re]
  have hcross : (star (u * rowPair Q v a)).re = (u * rowPair Q v a).re := by
    rw [Complex.star_def, Complex.conj_re]
  rw [← star_mul, complex_scalar_quadratic, hcross, complex_re_mul_eq_inner]
  change rowQuadratic Q a + _ + _ = _
  ring

theorem ballSubmean_log_one_add_rowQuadratic {Q : Matrix n n ℂ} (hQ : Q.PosDef)
    (a v : Matrix Unit n ℂ) :
    BallSubmean (fun u : ℂ => Real.log (1 + rowQuadratic Q (a + scalarRow u v))) := by
  have heq (u : ℂ) : 1 + rowQuadratic Q (a + scalarRow u v) =
      (1 + rowQuadratic Q a) + 2 * ⟪star (rowPair Q v a), u⟫_ℝ +
        rowQuadratic Q v * ‖u‖ ^ 2 := by
    rw [rowQuadratic_scalar_shift hQ]
    ring
  have h := ballSubmean_log_affineQuadratic_of_one_le
    (E := ℂ) (by simpa only [Complex.finrank_real_complex] using (le_refl (2 : ℕ)))
    (rowQuadratic_nonneg hQ v) (star (rowPair Q v a)) (fun u => by
      rw [← heq u]
      exact le_add_of_nonneg_right (rowQuadratic_nonneg hQ _))
  simpa only [heq] using h

theorem continuous_realDeterminant : Continuous (realDeterminant : Matrix n n ℂ → ℝ) := by
  unfold realDeterminant
  fun_prop

theorem positiveLogSubmean_rowDeterminant {Q : Matrix n n ℂ} (hQ : Q.PosDef)
    (a v : Matrix Unit n ℂ) :
    PositiveLogSubmean (fun u : ℂ =>
      realDeterminant (Q + (a + scalarRow u v)ᴴ * (a + scalarRow u v))) := by
  have hpos (u : ℂ) : 0 <
      realDeterminant (Q + (a + scalarRow u v)ᴴ * (a + scalarRow u v)) := by
    rw [realDeterminant_rankOne hQ]
    exact mul_pos (realDeterminant_pos hQ)
      (add_pos_of_pos_of_nonneg zero_lt_one (rowQuadratic_nonneg hQ _))
  refine ⟨hpos, continuous_realDeterminant.comp (by unfold scalarRow; fun_prop), ?_⟩
  have hlog : (fun u : ℂ => Real.log
      (realDeterminant (Q + (a + scalarRow u v)ᴴ * (a + scalarRow u v)))) =
      fun u => Real.log (realDeterminant Q) +
        Real.log (1 + rowQuadratic Q (a + scalarRow u v)) := by
    funext u
    rw [realDeterminant_rankOne hQ,
      Real.log_mul (realDeterminant_pos hQ).ne'
        (by have h := rowQuadratic_nonneg hQ (a + scalarRow u v); positivity)]
  rw [hlog]
  exact (BallSubmean.const _).add (ballSubmean_log_one_add_rowQuadratic hQ a v)

end Wishart.ComplexMatrix
end
end CanonicalSource3

section CanonicalSource4
/- Source: Wishart/FieldGaussianRows.lean -/



/-!
# Actual complex and quaternion Gaussian rows

The row law is the rectangular real-linear image of the ordinary standard
Gaussian on the underlying real inner-product space.  Its scalar normalization
is `1 / sqrt(dim ℝ F)`, exactly the variance convention in Section 7.  A singular
rectangular factor is permitted.  Left multiplication by a unit field scalar
is an actual linear isometry and preserves this law.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical Matrix BigOperators Quaternion ENNReal

namespace Wishart.FieldGaussian

variable (F : Type*) [NormedRing F] [StarRing F] [CStarRing F]
  [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [SMulCommClass ℝ F F] [IsScalarTower ℝ F F]
  [MeasurableSpace F] [BorelSpace F]

abbrev Row (m : ℕ) := PiLp 2 (fun _ : Fin m => F)

def rowPhase {m : ℕ} (u : unitary F) : Row F m ≃ₗᵢ[ℝ] Row F m :=
  LinearIsometryEquiv.piLpCongrRight 2 fun _ => Unitary.mulLeft ℝ F u

@[simp] theorem rowPhase_apply {m : ℕ} (u : unitary F) (z : Row F m) (i : Fin m) :
    rowPhase F u z i = (u : F) * z i := by
  simp only [rowPhase, LinearIsometryEquiv.piLpCongrRight_apply,
    PiLp.toLp_apply, Unitary.mulLeft_apply]

/-- Right multiplication by a genuinely arbitrary rectangular field matrix,
viewed as a real continuous linear map. -/
def rowFactorLinearMap {r m : ℕ} (R : Matrix (Fin r) (Fin m) F) :
    Row F r →ₗ[ℝ] Row F m where
  toFun z := WithLp.toLp 2 fun j => ∑ i, z i * R i j
  map_add' x y := by
    ext j
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c z := by
    ext j
    simp [smul_mul_assoc, Finset.smul_sum]

def rowFactorCLM {r m : ℕ} (R : Matrix (Fin r) (Fin m) F) :
    Row F r →L[ℝ] Row F m := (rowFactorLinearMap F R).toContinuousLinearMap

@[simp] theorem rowFactorCLM_apply {r m : ℕ} (R : Matrix (Fin r) (Fin m) F)
    (z : Row F r) (j : Fin m) :
    rowFactorCLM F R z j = ∑ i, z i * R i j := rfl

def standardDeviation : ℝ := (Real.sqrt (Module.finrank ℝ F))⁻¹

def normalizedRowFactorCLM {r m : ℕ} (R : Matrix (Fin r) (Fin m) F) :
    Row F r →L[ℝ] Row F m := standardDeviation F • rowFactorCLM F R

/-- The actual centered field Gaussian row with rectangular covariance factor
`R`; for an identity factor each real component has variance `1 / dim ℝ F`. -/
def gaussianRowWithFactor {r m : ℕ} (R : Matrix (Fin r) (Fin m) F) :
    Measure (Row F m) :=
  (stdGaussian (Row F r)).map (normalizedRowFactorCLM F R)

instance gaussianRowWithFactor_isProbability {r m : ℕ}
    (R : Matrix (Fin r) (Fin m) F) : IsProbabilityMeasure (gaussianRowWithFactor F R) := by
  unfold gaussianRowWithFactor
  infer_instance

instance gaussianRowWithFactor_isGaussian {r m : ℕ}
    (R : Matrix (Fin r) (Fin m) F) : IsGaussian (gaussianRowWithFactor F R) := by
  unfold gaussianRowWithFactor
  infer_instance

theorem rowFactor_phase {r m : ℕ} (R : Matrix (Fin r) (Fin m) F)
    (u : unitary F) (z : Row F r) :
    rowFactorCLM F R (rowPhase F u z) = rowPhase F u (rowFactorCLM F R z) := by
  ext j
  simp only [rowFactorCLM_apply, rowPhase_apply, Finset.mul_sum, mul_assoc]

theorem normalizedRowFactor_phase {r m : ℕ} (R : Matrix (Fin r) (Fin m) F)
    (u : unitary F) (z : Row F r) :
    normalizedRowFactorCLM F R (rowPhase F u z) =
      rowPhase F u (normalizedRowFactorCLM F R z) := by
  simp only [normalizedRowFactorCLM, ContinuousLinearMap.smul_apply,
    rowFactor_phase, map_smul]

theorem gaussianRowWithFactor_map_phase {r m : ℕ}
    (R : Matrix (Fin r) (Fin m) F) (u : unitary F) :
    (gaussianRowWithFactor F R).map (rowPhase F u) = gaussianRowWithFactor F R := by
  unfold gaussianRowWithFactor
  rw [Measure.map_map (rowPhase F u).continuous.measurable
    (normalizedRowFactorCLM F R).continuous.measurable]
  have heq : (rowPhase F u) ∘ (normalizedRowFactorCLM F R) =
      (normalizedRowFactorCLM F R) ∘ (rowPhase F u) := by
    funext z
    exact (normalizedRowFactor_phase F R u z).symm
  rw [heq, ← Measure.map_map (normalizedRowFactorCLM F R).continuous.measurable
    (rowPhase F u).continuous.measurable, stdGaussian_map]

theorem measurePreserving_rowPhase {r m : ℕ} (R : Matrix (Fin r) (Fin m) F)
    (u : unitary F) :
    MeasurePreserving (rowPhase F u) (gaussianRowWithFactor F R)
      (gaussianRowWithFactor F R) :=
  ⟨(rowPhase F u).continuous.measurable, gaussianRowWithFactor_map_phase F R u⟩

theorem norm_allFiniteMoments {r m : ℕ} (R : Matrix (Fin r) (Fin m) F) :
    WishartVerification.HasAllFiniteMoments (fun z : Row F m => ‖z‖)
      (gaussianRowWithFactor F R) := by
  intro p hp
  exact (IsGaussian.memLp_id (gaussianRowWithFactor F R) p hp).norm

/-- The Hermitian row Gram matrix in its original field. -/
def rowGram {m : ℕ} (z : Row F m) : Matrix (Fin m) (Fin m) F :=
  Matrix.of fun i j => star (z i) * z j

theorem rowGram_phase {m : ℕ} (u : unitary F) (z : Row F m) :
    rowGram F (rowPhase F u z) = rowGram F z := by
  ext i j
  simp only [rowGram, Matrix.of_apply, rowPhase_apply, star_mul]
  calc
    star (z i) * star (u : F) * ((u : F) * z j) =
        star (z i) * (star (u : F) * (u : F)) * z j := by simp only [mul_assoc]
    _ = star (z i) * z j := by rw [Unitary.coe_star_mul_self, mul_one]

/-- Rotating both the Gaussian sample and its scalar displacement gives the
same Gram matrix pointwise.  This is the exact invariance used for radiality. -/
theorem rowGram_phase_shift {m : ℕ} (u : unitary F) (z v : Row F m) (a : F) :
    rowGram F (WithLp.toLp 2 fun i => (rowPhase F u z) i + ((u : F) * a) * v i) =
      rowGram F (WithLp.toLp 2 fun i => z i + a * v i) := by
  have heq : (WithLp.toLp 2 fun i => (rowPhase F u z) i + ((u : F) * a) * v i) =
      rowPhase F u (WithLp.toLp 2 fun i => z i + a * v i) := by
    ext i
    simp only [rowPhase_apply, mul_add, mul_assoc]
  rw [heq, rowGram_phase]

end Wishart.FieldGaussian
end
end CanonicalSource4

section CanonicalSource5
/- Source: Wishart/FieldWishartDefinitions.lean -/



/-!
# The literal complex and quaternion laws of Section 7

The reference measure is ordinary real Lebesgue measure on the Hermitian
vector space, specified by a real basis.  The arbitrary basis normalization
is absorbed into the probability normalizer.  The density is exactly (19),
with b = 2 and b = 4 respectively.  The integer law is independently defined
as the image of n independent normalized field Gaussian rows.

No density identity or probability assertion for the real-shape density is
assumed by these definitions.  Those require the subsequent integration and
regression proofs.  The integer Gaussian image is already an actual probability
measure by construction.
-/

noncomputable section
open Matrix MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped Classical Quaternion Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator Ring ENNReal

namespace Wishart.FieldGaussian

variable (F : Type*) [NormedRing F] [StarRing F] [CStarRing F]
  [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [SMulCommClass ℝ F F] [IsScalarTower ℝ F F] [StarModule ℝ F]
  [MeasurableSpace F] [BorelSpace F]

abbrev Hermitian (p : ℕ) := selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) F)

def rowsMatrix {n p : ℕ} (z : Fin n → Row F p) : Matrix (Fin n) (Fin p) F :=
  Matrix.of fun i j => z i j

def rowsGram {n p : ℕ} (z : Fin n → Row F p) : Hermitian F p :=
  ⟨(rowsMatrix F z)ᴴ * rowsMatrix F z,
    (Matrix.isHermitian_conjTranspose_mul_self (rowsMatrix F z)).isSelfAdjoint⟩

theorem continuous_rowsMatrix (n p : ℕ) :
    Continuous (rowsMatrix F : (Fin n → Row F p) → Matrix (Fin n) (Fin p) F) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (PiLp.continuous_apply 2 (fun _ : Fin p => F) j).comp (continuous_apply i)

theorem continuous_rowsGram (n p : ℕ) :
    Continuous (rowsGram F : (Fin n → Row F p) → Hermitian F p) := by
  apply Continuous.subtype_mk
  exact (continuous_rowsMatrix F n p).matrix_conjTranspose.matrix_mul
    (continuous_rowsMatrix F n p)

def gramWithFactor {r p : ℕ} (n : ℕ) (R : Matrix (Fin r) (Fin p) F) :
    Measure (Hermitian F p) :=
  (Measure.pi (fun _ : Fin n => gaussianRowWithFactor F R)).map (rowsGram F)

instance gramWithFactor_isProbability {r p : ℕ} (n : ℕ)
    (R : Matrix (Fin r) (Fin p) F) : IsProbabilityMeasure (gramWithFactor F n R) := by
  unfold gramWithFactor
  infer_instance

end Wishart.FieldGaussian

namespace Wishart.ComplexMatrix

abbrev Hermitian (p : ℕ) := selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)

def hermitianLebesgue (p : ℕ) : Measure (Hermitian p) :=
  (Module.finBasis ℝ (Hermitian p)).addHaar

instance hermitianLebesgue_isAddHaar (p : ℕ) : IsAddHaarMeasure (hermitianLebesgue p) := by
  unfold hermitianLebesgue
  infer_instance

instance hermitianLebesgue_sigmaFinite (p : ℕ) : SigmaFinite (hermitianLebesgue p) := by
  unfold hermitianLebesgue
  infer_instance

/-- The unnormalized literal complex density (b = 2). -/
def wishartWeight {p : ℕ} (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℂ)
    (X : Hermitian p) : ℝ≥0∞ :=
  if (X : Matrix (Fin p) (Fin p) ℂ).PosDef then
    ENNReal.ofReal (realDeterminant (X : Matrix (Fin p) (Fin p) ℂ) ^ (α - p) *
      Real.exp (-((Sigma⁻¹ * (X : Matrix (Fin p) (Fin p) ℂ)).trace).re))
  else 0

def wishartNormalizer {p : ℕ} (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℂ) : ℝ≥0∞ :=
  ∫⁻ X, wishartWeight α Sigma X ∂hermitianLebesgue p

def wishartMeasure {p : ℕ} (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℂ) :
    Measure (Hermitian p) :=
  (wishartNormalizer α Sigma)⁻¹ • (hermitianLebesgue p).withDensity (wishartWeight α Sigma)

/-- The genuine n-row field Gaussian Gram law, including singular sample sizes. -/
def gramMeasure {p : ℕ} (n : ℕ) (Sigma : Matrix (Fin p) (Fin p) ℂ) : Measure (Hermitian p) :=
  Wishart.FieldGaussian.gramWithFactor ℂ n (CFC.sqrt Sigma)

instance gramMeasure_isProbability {p : ℕ} (n : ℕ) (Sigma : Matrix (Fin p) (Fin p) ℂ) :
    IsProbabilityMeasure (gramMeasure n Sigma) := by unfold gramMeasure; infer_instance

def compressionCovariance {p k : ℕ} (B : Matrix (Fin p) (Fin k) ℂ)
    (Sigma : Matrix (Fin p) (Fin p) ℂ) : Matrix (Fin k) (Fin k) ℂ := Bᴴ * Sigma * B

/-- The exact standardized compression.  The congruence form makes the total
function Hermitian even outside its intended positive-definite parameters. -/
def normalizedCompression {p k : ℕ} (B : Matrix (Fin p) (Fin k) ℂ)
    (Sigma : Matrix (Fin p) (Fin p) ℂ) (X : Hermitian p) : Hermitian k :=
  let R := B * (CFC.sqrt (compressionCovariance B Sigma))⁻¹
  ⟨Rᴴ * (X : Matrix (Fin p) (Fin p) ℂ) * R,
    (Matrix.isHermitian_conjTranspose_mul_mul R
      (show IsSelfAdjoint (X : Matrix (Fin p) (Fin p) ℂ) from X.property).isHermitian).isSelfAdjoint⟩

theorem wishartWeight_eq_formula {p : ℕ} (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℂ)
    (X : Hermitian p) (hX : (X : Matrix (Fin p) (Fin p) ℂ).PosDef) :
    wishartWeight α Sigma X = ENNReal.ofReal
      (realDeterminant (X : Matrix (Fin p) (Fin p) ℂ) ^ ((2 : ℝ) / 2 * (α - p + 1) - 1) *
        Real.exp (-(2 : ℝ) / 2 * ((Sigma⁻¹ * (X : Matrix (Fin p) (Fin p) ℂ)).trace).re)) := by
  rw [wishartWeight, if_pos hX]
  congr 2 <;> ring

end Wishart.ComplexMatrix

namespace Wishart.QuaternionMatrix

open scoped Matrix.Norms.Frobenius

set_option backward.isDefEq.respectTransparency false in
local instance matrixBorelSpace (p q : ℕ) :
    BorelSpace (Matrix (Fin p) (Fin q) ℍ[ℝ]) :=
  inferInstanceAs (BorelSpace (Fin p → Fin q → ℍ[ℝ]))

set_option backward.isDefEq.respectTransparency false in
local instance hermitianBorelSpace (p : ℕ) : BorelSpace (Hermitian p) :=
  inferInstanceAs
    (BorelSpace {X : Matrix (Fin p) (Fin p) ℍ[ℝ] // X ∈ selfAdjoint.submodule ℝ _})

set_option backward.isDefEq.respectTransparency false in
def hermitianLebesgue (p : ℕ) : Measure (Hermitian p) :=
  (Module.finBasis ℝ (Hermitian p)).addHaar

set_option backward.isDefEq.respectTransparency false in
instance hermitianLebesgue_isAddHaar (p : ℕ) : IsAddHaarMeasure (hermitianLebesgue p) := by
  unfold hermitianLebesgue
  exact isAddHaarMeasure_basis_addHaar (Module.finBasis ℝ (Hermitian p))

set_option backward.isDefEq.respectTransparency false in
instance hermitianLebesgue_sigmaFinite (p : ℕ) : SigmaFinite (hermitianLebesgue p) := by
  unfold hermitianLebesgue
  infer_instance

/-- The unnormalized literal quaternion density (b = 4). -/
def wishartWeight {p : ℕ} (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ])
    (X : Hermitian p) : ℝ≥0∞ :=
  if PosDef (X : Matrix (Fin p) (Fin p) ℍ[ℝ]) then
    ENNReal.ofReal (positiveDeterminant (X : Matrix (Fin p) (Fin p) ℍ[ℝ]) ^ (2 * (α - p + 1) - 1) *
      Real.exp (-2 * ((Sigma⁻¹ʳ * (X : Matrix (Fin p) (Fin p) ℍ[ℝ])).trace).re))
  else 0

def wishartNormalizer {p : ℕ} (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) : ℝ≥0∞ :=
  ∫⁻ X, wishartWeight α Sigma X ∂hermitianLebesgue p

def wishartMeasure {p : ℕ} (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) :
    Measure (Hermitian p) :=
  (wishartNormalizer α Sigma)⁻¹ • (hermitianLebesgue p).withDensity (wishartWeight α Sigma)

def gramMeasure {p : ℕ} (n : ℕ) (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) : Measure (Hermitian p) :=
  Wishart.FieldGaussian.gramWithFactor ℍ[ℝ] n (sqrt Sigma)

instance gramMeasure_isProbability {p : ℕ} (n : ℕ) (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) :
    IsProbabilityMeasure (gramMeasure n Sigma) := by unfold gramMeasure; infer_instance

def compressionCovariance {p k : ℕ} (B : Matrix (Fin p) (Fin k) ℍ[ℝ])
    (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) : Matrix (Fin k) (Fin k) ℍ[ℝ] := Bᴴ * Sigma * B

def normalizedCompression {p k : ℕ} (B : Matrix (Fin p) (Fin k) ℍ[ℝ])
    (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) (X : Hermitian p) : Hermitian k :=
  let R := B * (sqrt (compressionCovariance B Sigma))⁻¹ʳ
  ⟨Rᴴ * (X : Matrix (Fin p) (Fin p) ℍ[ℝ]) * R,
    (Matrix.isHermitian_conjTranspose_mul_mul R
      (show IsSelfAdjoint (X : Matrix (Fin p) (Fin p) ℍ[ℝ]) from X.property).isHermitian).isSelfAdjoint⟩

theorem wishartWeight_eq_formula {p : ℕ} (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ])
    (X : Hermitian p) (hX : PosDef (X : Matrix (Fin p) (Fin p) ℍ[ℝ])) :
    wishartWeight α Sigma X = ENNReal.ofReal
      (positiveDeterminant (X : Matrix (Fin p) (Fin p) ℍ[ℝ]) ^ ((4 : ℝ) / 2 * (α - p + 1) - 1) *
        Real.exp (-(4 : ℝ) / 2 * ((Sigma⁻¹ʳ * (X : Matrix (Fin p) (Fin p) ℍ[ℝ])).trace).re)) := by
  rw [wishartWeight, if_pos hX]
  congr 2 <;> ring

end Wishart.QuaternionMatrix
end
end CanonicalSource5

section CanonicalSource6
/- Source: Wishart/FieldHermitianCoercions.lean -/



/-!
# Hermitian matrices over a real star module

This elementary coercion lemma applies to complex and quaternion matrices as
well as real ones.  It reads the actual membership proof in the self-adjoint
submodule; no spectral or positivity assertion is introduced.
-/

namespace WishartVerification

theorem hermitian_matrix_coe {F ι : Type*} [AddCommGroup F] [Module ℝ F]
    [StarAddMonoid F] [StarModule ℝ F]
    (X : selfAdjoint.submodule ℝ (Matrix ι ι F)) :
    (X : Matrix ι ι F).IsHermitian := X.property

end WishartVerification
end CanonicalSource6

section CanonicalSource7
/- Source: Wishart/FieldHermitianCoordinates.lean -/



/-!
# Ordinary real block coordinates on complex and quaternion Hermitian matrices

The off-diagonal block is a full rectangular field matrix; its opposite block
is its conjugate transpose.  This is a real linear equivalence, so it transports
Lebesgue measure to a fixed positive finite multiple of the product reference.
No probability law or Schur-complement Jacobian is assumed here.
-/

noncomputable section
open Matrix MeasureTheory MeasureTheory.Measure
open scoped Classical Matrix ComplexOrder Quaternion NNReal ENNReal Matrix.Norms.Frobenius

namespace Wishart.FieldHermitian

variable (F : Type*) [NormedRing F] [NormedAlgebra ℝ F]
  [StarRing F] [CStarRing F] [StarModule ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

abbrev Hermitian (p : ℕ) := selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) F)
abbrev BlockSpace (p q : ℕ) := Hermitian F p × Matrix (Fin p) (Fin q) F × Hermitian F q

set_option backward.isDefEq.respectTransparency false in
/-- The finite matrix Borel structure is the ordinary product Borel structure. -/
local instance matrixBorelSpace (p q : ℕ) :
    BorelSpace (Matrix (Fin p) (Fin q) F) :=
  inferInstanceAs (BorelSpace (Fin p → Fin q → F))

set_option backward.isDefEq.respectTransparency false in
local instance hermitianBorelSpace (p : ℕ) : BorelSpace (Hermitian F p) :=
  inferInstanceAs (BorelSpace {X : Matrix (Fin p) (Fin p) F // X ∈ Hermitian F p})

def leadingBlock {p q : ℕ} (X : Hermitian F (p + q)) : Hermitian F p :=
  ⟨(X : Matrix (Fin (p + q)) (Fin (p + q)) F).submatrix
      (Fin.castAdd q) (Fin.castAdd q),
    ((WishartVerification.hermitian_matrix_coe X).submatrix _).isSelfAdjoint⟩

def trailingBlock {p q : ℕ} (X : Hermitian F (p + q)) : Hermitian F q :=
  ⟨(X : Matrix (Fin (p + q)) (Fin (p + q)) F).submatrix
      (Fin.natAdd p) (Fin.natAdd p),
    ((WishartVerification.hermitian_matrix_coe X).submatrix _).isSelfAdjoint⟩

def offDiagonalBlock {p q : ℕ} (X : Hermitian F (p + q)) : Matrix (Fin p) (Fin q) F :=
  (X : Matrix (Fin (p + q)) (Fin (p + q)) F).submatrix (Fin.castAdd q) (Fin.natAdd p)

def fromBlocks {p q : ℕ} (z : BlockSpace F p q) : Hermitian F (p + q) :=
  ⟨(Matrix.fromBlocks (z.1 : Matrix (Fin p) (Fin p) F) z.2.1 z.2.1ᴴ
      (z.2.2 : Matrix (Fin q) (Fin q) F)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm, by
    apply Matrix.IsHermitian.isSelfAdjoint
    apply Matrix.IsHermitian.submatrix
    rw [Matrix.IsHermitian, Matrix.fromBlocks_conjTranspose]
    simp only [Matrix.conjTranspose_conjTranspose,
      (WishartVerification.hermitian_matrix_coe z.1).eq,
      (WishartVerification.hermitian_matrix_coe z.2.2).eq]⟩

def blockCoordinates (p q : ℕ) : Hermitian F (p + q) ≃ₗ[ℝ] BlockSpace F p q where
  toFun X := (leadingBlock F X, offDiagonalBlock F X, trailingBlock F X)
  invFun := fromBlocks F
  left_inv X := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    rcases i with i | i <;> rcases j with j | j
    · simp [fromBlocks, leadingBlock, offDiagonalBlock, trailingBlock]
    · simp [fromBlocks, leadingBlock, offDiagonalBlock, trailingBlock]
    · simp only [fromBlocks, Matrix.submatrix_apply, Equiv.symm_apply_apply,
        Matrix.fromBlocks_apply₂₁, Matrix.conjTranspose_apply, offDiagonalBlock,
        Matrix.submatrix_apply, finSumFinEquiv_apply_right, finSumFinEquiv_apply_left,
        finSumFinEquiv_symm_apply_natAdd, finSumFinEquiv_symm_apply_castAdd]
      change star (X.val (Fin.castAdd q j) (Fin.natAdd p i)) =
        X.val (Fin.natAdd p i) (Fin.castAdd q j)
      exact (WishartVerification.hermitian_matrix_coe X).apply _ _
    · simp [fromBlocks, leadingBlock, offDiagonalBlock, trailingBlock]
  right_inv z := by
    rcases z with ⟨A, B, D⟩
    apply Prod.ext
    · apply Subtype.ext
      ext i j
      simp [leadingBlock, fromBlocks]
    · apply Prod.ext
      · ext i j
        simp [offDiagonalBlock, fromBlocks]
      · apply Subtype.ext
        ext i j
        simp [trailingBlock, fromBlocks]
  map_add' X Y := by
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Prod.ext
      · rfl
      · apply Subtype.ext
        rfl
  map_smul' r X := by
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Prod.ext
      · rfl
      · apply Subtype.ext
        rfl

@[simp] theorem blockCoordinates_apply {p q : ℕ} (X : Hermitian F (p + q)) :
    blockCoordinates F p q X = (leadingBlock F X, offDiagonalBlock F X, trailingBlock F X) := rfl

@[simp] theorem blockCoordinates_symm_apply {p q : ℕ} (z : BlockSpace F p q) :
    (blockCoordinates F p q).symm z = fromBlocks F z := rfl

def blockCoordinatesCL (p q : ℕ) : Hermitian F (p + q) ≃L[ℝ] BlockSpace F p q :=
  (blockCoordinates F p q).toContinuousLinearEquiv

set_option backward.isDefEq.respectTransparency false in
def hermitianLebesgue (p : ℕ) : Measure (Hermitian F p) :=
  (Module.finBasis ℝ (Hermitian F p)).addHaar

set_option backward.isDefEq.respectTransparency false in
def rectangularLebesgue (p q : ℕ) : Measure (Matrix (Fin p) (Fin q) F) :=
  (Module.finBasis ℝ (Matrix (Fin p) (Fin q) F)).addHaar

set_option backward.isDefEq.respectTransparency false in
instance hermitianLebesgue_isAddHaar (p : ℕ) : IsAddHaarMeasure (hermitianLebesgue F p) := by
  unfold hermitianLebesgue
  exact isAddHaarMeasure_basis_addHaar (Module.finBasis ℝ (Hermitian F p))

set_option backward.isDefEq.respectTransparency false in
instance rectangularLebesgue_isAddHaar (p q : ℕ) :
    IsAddHaarMeasure (rectangularLebesgue F p q) := by
  unfold rectangularLebesgue
  exact isAddHaarMeasure_basis_addHaar (Module.finBasis ℝ (Matrix (Fin p) (Fin q) F))

set_option backward.isDefEq.respectTransparency false in
instance hermitianLebesgue_sigmaFinite (p : ℕ) : SigmaFinite (hermitianLebesgue F p) := by
  unfold hermitianLebesgue
  infer_instance

set_option backward.isDefEq.respectTransparency false in
instance rectangularLebesgue_sigmaFinite (p q : ℕ) :
    SigmaFinite (rectangularLebesgue F p q) := by
  unfold rectangularLebesgue
  infer_instance

def blockLebesgue (p q : ℕ) : Measure (BlockSpace F p q) :=
  (hermitianLebesgue F p).prod
    ((rectangularLebesgue F p q).prod (hermitianLebesgue F q))

set_option backward.isDefEq.respectTransparency false in
instance blockLebesgue_isAddHaar (p q : ℕ) : IsAddHaarMeasure (blockLebesgue F p q) := by
  unfold blockLebesgue
  infer_instance

instance blockLebesgue_sigmaFinite (p q : ℕ) : SigmaFinite (blockLebesgue F p q) := by
  unfold blockLebesgue
  infer_instance

set_option backward.isDefEq.respectTransparency false in
def blockCoordinateFactor (p q : ℕ) : ℝ≥0 :=
  Measure.addHaarScalarFactor
    ((hermitianLebesgue F (p + q)).map (blockCoordinatesCL F p q)) (blockLebesgue F p q)

set_option backward.isDefEq.respectTransparency false in
theorem blockCoordinateFactor_pos (p q : ℕ) : 0 < blockCoordinateFactor F p q := by
  letI : IsAddHaarMeasure ((hermitianLebesgue F (p + q)).map (blockCoordinatesCL F p q)) :=
    (blockCoordinatesCL F p q).isAddHaarMeasure_map _
  exact Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _

set_option backward.isDefEq.respectTransparency false in
/-- Exact ordinary Lebesgue reference transport; the factor is positive and
finite and will cancel in the normalized probability density. -/
theorem map_blockCoordinates_hermitianLebesgue (p q : ℕ) :
    (hermitianLebesgue F (p + q)).map (blockCoordinatesCL F p q) =
      blockCoordinateFactor F p q • blockLebesgue F p q := by
  letI : IsAddHaarMeasure ((hermitianLebesgue F (p + q)).map (blockCoordinatesCL F p q)) :=
    (blockCoordinatesCL F p q).isAddHaarMeasure_map _
  exact Measure.isAddLeftInvariant_eq_smul _ _

set_option backward.isDefEq.respectTransparency false in
theorem lintegral_blockCoordinates (p q : ℕ)
    (f : BlockSpace F p q → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ X, f (blockCoordinates F p q X) ∂hermitianLebesgue F (p + q)) =
      (blockCoordinateFactor F p q : ℝ≥0∞) *
        ∫⁻ A, ∫⁻ B, ∫⁻ D, f (A, B, D)
          ∂hermitianLebesgue F q ∂rectangularLebesgue F p q ∂hermitianLebesgue F p := by
  change (∫⁻ X, f (blockCoordinatesCL F p q X) ∂hermitianLebesgue F (p + q)) = _
  rw [← lintegral_map hf (blockCoordinatesCL F p q).continuous.measurable,
    map_blockCoordinates_hermitianLebesgue,
    lintegral_smul_measure]
  congr 1
  rw [blockLebesgue, lintegral_prod _ hf.aemeasurable]
  apply lintegral_congr
  intro A
  exact lintegral_prod _ (hf.comp (measurable_const.prodMk measurable_id)).aemeasurable

end Wishart.FieldHermitian
end
end CanonicalSource7

section CanonicalSource8
/- Source: Wishart/FieldJacobian.lean -/



/-!
# The real Jacobian of field-matrix multiplication

Quaternion matrices act on right-coefficient columns.  That action is real
linear.  Unitary diagonalization computes its real determinant as the fourth
power of the Moore determinant; the complex exponent is two.  Acting on m
columns raises the same determinant to the mth power.
-/

noncomputable section
open Matrix MeasureTheory
open scoped Classical Quaternion Matrix ComplexOrder Ring
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace Wishart.FieldJacobian

variable {F : Type*} [Ring F] [Algebra ℝ F]
  [FiniteDimensional ℝ F]
variable {n : Type*} [Fintype n] [DecidableEq n]

def columnAction (A : Matrix n n F) : (n → F) →ₗ[ℝ] (n → F) where
  toFun := A.mulVec
  map_add' := A.mulVec_add
  map_smul' r x := A.mulVec_smul r x

@[simp] theorem columnAction_apply (A : Matrix n n F) (x : n → F) :
    columnAction A x = A *ᵥ x := rfl

theorem columnAction_mul (A B : Matrix n n F) :
    columnAction (A * B) = (columnAction A).comp (columnAction B) := by
  apply LinearMap.ext
  intro x
  exact (Matrix.mulVec_mulVec x A B).symm

@[simp] theorem columnAction_one : columnAction (1 : Matrix n n F) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  exact Matrix.one_mulVec x

theorem det_columnAction_diagonal_real (lam : n → ℝ) :
    LinearMap.det (columnAction (Matrix.diagonal (fun i => (algebraMap ℝ F) (lam i)))) =
      (∏ i, lam i) ^ Module.finrank ℝ F := by
  have heq : columnAction (Matrix.diagonal (fun i => (algebraMap ℝ F) (lam i))) =
      LinearMap.pi (fun i => ((lam i) • (LinearMap.id : F →ₗ[ℝ] F)).comp (LinearMap.proj i)) := by
    apply LinearMap.ext
    intro x
    funext i
    simp [columnAction, Matrix.mulVec_diagonal, Algebra.smul_def]
  rw [heq, LinearMap.det_pi]
  simp only [LinearMap.det_smul, LinearMap.det_id, mul_one]
  exact Finset.prod_pow _ _ _

theorem det_columnAction_of_diagonalization [StarRing F]
    (A : Matrix n n F) (U : unitary (Matrix n n F)) (lam : n → ℝ)
    (hdiag : (star U : Matrix n n F) * A * U =
      Matrix.diagonal (fun i => (algebraMap ℝ F) (lam i))) :
    LinearMap.det (columnAction A) = (∏ i, lam i) ^ Module.finrank ℝ F := by
  have hunit : LinearMap.det (columnAction (star U : Matrix n n F)) *
      LinearMap.det (columnAction (U : Matrix n n F)) = 1 := by
    rw [← LinearMap.det_comp, ← columnAction_mul, Unitary.coe_star_mul_self,
      columnAction_one, LinearMap.det_id]
  have hd := congrArg (fun M : Matrix n n F => LinearMap.det (columnAction M)) hdiag
  rw [columnAction_mul, columnAction_mul, LinearMap.det_comp, LinearMap.det_comp,
    det_columnAction_diagonal_real] at hd
  calc
    LinearMap.det (columnAction A) = LinearMap.det (columnAction A) * 1 := by ring
    _ = LinearMap.det (columnAction A) *
        (LinearMap.det (columnAction (star U : Matrix n n F)) *
          LinearMap.det (columnAction (U : Matrix n n F))) := by rw [hunit]
    _ = _ := by rw [← hd]; ring

variable {m : Type*} [Fintype m] [DecidableEq m]

def leftAction (A : Matrix n n F) : Matrix n m F →ₗ[ℝ] Matrix n m F where
  toFun B := A * B
  map_add' B C := Matrix.mul_add A B C
  map_smul' r B := Matrix.mul_smul A r B

def columnsEquiv : Matrix n m F ≃ₗ[ℝ] (m → n → F) where
  toFun := Matrix.transpose
  invFun := Matrix.transpose
  left_inv := Matrix.transpose_transpose
  right_inv := Matrix.transpose_transpose
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem det_leftAction (A : Matrix n n F) :
    LinearMap.det (leftAction (m := m) A) =
      LinearMap.det (columnAction A) ^ Fintype.card m := by
  let e := columnsEquiv (F := F) (n := n) (m := m)
  have heq : (e : Matrix n m F →ₗ[ℝ] (m → n → F)).comp
      ((leftAction A).comp (e.symm : (m → n → F) →ₗ[ℝ] Matrix n m F)) =
      LinearMap.pi (fun j : m => (columnAction A).comp (LinearMap.proj j)) := by
    apply LinearMap.ext
    intro X
    funext j i
    rfl
  have h := LinearMap.det_conj (leftAction (m := m) A) e
  rw [heq, LinearMap.det_pi, Finset.prod_const, Finset.card_univ] at h
  exact h.symm

end Wishart.FieldJacobian

namespace Wishart.QuaternionMatrix
open Wishart.FieldJacobian

theorem det_real_columnAction {p : ℕ} {A : Matrix (Fin p) (Fin p) ℍ[ℝ]}
    (hA : PosSemidef A) :
    LinearMap.det (columnAction A) = positiveDeterminant A ^ 4 := by
  let D := eigenDecomposition A hA.isHermitian
  rw [det_columnAction_of_diagonalization A D.frame D.values D.diagonalization,
    Quaternion.finrank_eq_four, D.positiveDeterminant_eq_prod hA]

theorem det_real_leftAction {p m : ℕ} {A : Matrix (Fin p) (Fin p) ℍ[ℝ]}
    (hA : PosSemidef A) :
    LinearMap.det (leftAction (m := Fin m) A) = positiveDeterminant A ^ (4 * m) := by
  rw [det_leftAction, det_real_columnAction hA, Fintype.card_fin, ← pow_mul]

/-- The Schur substitution multiplies each quaternion off-diagonal column by
sqrt(S), with Jacobian det_H(S)^(2m). -/
theorem det_real_leftAction_sqrt {p m : ℕ} {S : Matrix (Fin p) (Fin p) ℍ[ℝ]}
    (hS : PosSemidef S) :
    LinearMap.det (leftAction (m := Fin m) (sqrt S)) = positiveDeterminant S ^ (2 * m) := by
  have hsq : positiveDeterminant (sqrt S) ^ 2 = positiveDeterminant S := by
    have hdetmul : positiveDeterminant (sqrt S * sqrt S) = positiveDeterminant (sqrt S) ^ 2 := by
      unfold positiveDeterminant
      rw [complexRepresentation_mul, Matrix.det_mul]
      have him := (RCLike.nonneg_iff.mp (Matrix.PosSemidef.det_nonneg hS.sqrt)).2
      change (complexRepresentation (sqrt S)).det.im = 0 at him
      rw [Complex.mul_re, him, mul_zero, sub_zero, ← pow_two,
        Real.sqrt_sq hS.sqrt.det_re_nonneg]
      exact hS.sqrt.positiveDeterminant_sq.symm
    simpa only [sqrt_mul_self hS] using hdetmul.symm
  rw [det_real_leftAction hS.sqrt]
  calc
    positiveDeterminant (sqrt S) ^ (4 * m) =
        (positiveDeterminant (sqrt S) ^ 2) ^ (2 * m) := by rw [← pow_mul]; congr 1; omega
    _ = _ := by rw [hsq]

end Wishart.QuaternionMatrix

namespace Wishart.ComplexMatrix
open Wishart.FieldJacobian

theorem det_real_columnAction {p : ℕ} {A : Matrix (Fin p) (Fin p) ℂ}
    (hA : A.IsHermitian) :
    LinearMap.det (columnAction A) = realDeterminant A ^ 2 := by
  have hdiag : (star hA.eigenvectorUnitary : Matrix (Fin p) (Fin p) ℂ) * A *
      hA.eigenvectorUnitary = Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) :=
    by simpa only [Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star,
      RCLike.ofReal_eq_complex_ofReal, Function.comp_def] using
      hA.conjStarAlgAut_star_eigenvectorUnitary
  rw [det_columnAction_of_diagonalization A hA.eigenvectorUnitary hA.eigenvalues hdiag,
    Complex.finrank_real_complex, realDeterminant_eq_prod_eigenvalues hA]

theorem det_real_leftAction {p m : ℕ} {A : Matrix (Fin p) (Fin p) ℂ}
    (hA : A.IsHermitian) :
    LinearMap.det (leftAction (m := Fin m) A) = realDeterminant A ^ (2 * m) := by
  rw [det_leftAction, det_real_columnAction hA, Fintype.card_fin, ← pow_mul]

theorem det_real_leftAction_sqrt {p m : ℕ} {S : Matrix (Fin p) (Fin p) ℂ}
    (hS : S.PosSemidef) :
    LinearMap.det (leftAction (m := Fin m) (CFC.sqrt S)) = realDeterminant S ^ m := by
  have hR : (CFC.sqrt S).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg S)
  have him : (CFC.sqrt S).det.im = 0 := (RCLike.nonneg_iff.mp hR.det_nonneg).2
  have hsq : realDeterminant (CFC.sqrt S) ^ 2 = realDeterminant S := by
    have h := congrArg (fun A : Matrix (Fin p) (Fin p) ℂ => A.det.re)
      (CFC.sqrt_mul_sqrt_self S hS.nonneg)
    simpa only [Matrix.det_mul, Complex.mul_re, him, zero_mul, sub_zero,
      realDeterminant, pow_two] using h
  rw [det_real_leftAction hR.isHermitian, pow_mul, hsq]

end Wishart.ComplexMatrix
end
end CanonicalSource8

section CanonicalSource9
/- Source: Wishart/SchurMeasure.lean -/



/-!
# The measure change behind a field Schur complement

The nonlinear Schur substitution needs only two ordinary Haar substitutions:
an invertible real linear map on the rectangular block and translation on the
trailing Hermitian block.  In particular, no differentiability of the matrix
square root is required for the measure identity.
-/

noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped ENNReal

namespace WishartVerification

variable {Ω : Type*} [MeasurableSpace Ω]

/-- An actual proportional density of a probability measure determines its
normalizer.  In particular the conclusion explicitly rules out a zero or
infinite raw mass; normalized-density totalization cannot hide either case. -/
theorem normalized_ennreal_density_of_probability
    (κ μ : Measure Ω) [IsProbabilityMeasure κ] (w : Ω → ℝ≥0∞) (c : ℝ≥0∞)
    (hlaw : κ = c • μ.withDensity w) :
    (∫⁻ x, w x ∂μ) ≠ 0 ∧ (∫⁻ x, w x ∂μ) ≠ ∞ ∧
      κ = (∫⁻ x, w x ∂μ)⁻¹ • μ.withDensity w := by
  let Z := ∫⁻ x, w x ∂μ
  have hmass : c * Z = 1 := by
    have h := congrArg (fun ρ : Measure Ω => ρ Set.univ) hlaw
    simpa only [measure_univ, Measure.smul_apply, smul_eq_mul,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, Z] using h.symm
  have hc0 : c ≠ 0 := by intro hc; simpa [hc] using hmass
  have hZ0 : Z ≠ 0 := by intro hZ; simpa [hZ] using hmass
  have hZtop : Z ≠ ∞ := by
    intro hZ
    rw [hZ, ENNReal.mul_top hc0] at hmass
    simpa using hmass
  have hc : c = Z⁻¹ := by
    calc
      c = (c * Z) * Z⁻¹ := (ENNReal.mul_inv_cancel_right hZ0 hZtop).symm
      _ = Z⁻¹ := by rw [hmass, one_mul]
  exact ⟨hZ0, hZtop, by simpa only [hc, Z] using hlaw⟩

variable {E H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]

/-- Ordinary linear change of variables, written with the forward Jacobian
so it can be inserted directly into the Schur-density factorization. -/
theorem lintegral_forward_jacobian (μ : Measure E) [IsAddHaarMeasure μ]
    (L : E ≃L[ℝ] E) (f : E → ℝ≥0∞) (hf : Measurable f) :
    ENNReal.ofReal |LinearMap.det (L : E →ₗ[ℝ] E)| *
        (∫⁻ x, f (L x) ∂μ) = ∫⁻ x, f x ∂μ := by
  let j := ENNReal.ofReal |LinearMap.det (L : E →ₗ[ℝ] E)|
  have hd : LinearMap.det (L : E →ₗ[ℝ] E) ≠ 0 := L.toLinearEquiv.isUnit_det'.ne_zero
  have hj0 : j ≠ 0 := (ENNReal.ofReal_pos.mpr (abs_pos.mpr hd)).ne'
  have hjtop : j ≠ ∞ := ENNReal.ofReal_ne_top
  have hmap : μ.map L = j⁻¹ • μ := by
    have hcoe : ((L : E →ₗ[ℝ] E) : E → E) = (L : E → E) := by
      funext x
      rfl
    simpa only [hcoe, j, abs_inv, ENNReal.ofReal_inv_of_pos (abs_pos.mpr hd)] using
      Measure.map_linearMap_addHaar_eq_smul_addHaar μ (f := (L : E →ₗ[ℝ] E)) hd
  change j * (∫⁻ x, f (L x) ∂μ) = _
  rw [← lintegral_map hf L.continuous.measurable, hmap,
    lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel hj0 hjtop, one_mul]

/-- The exact triangular fiber substitution.  The translation is allowed to
depend arbitrarily on the rectangular coordinate; its Jacobian remains one. -/
theorem lintegral_schur_fiber (μ : Measure E) (ν : Measure H)
    [IsAddHaarMeasure μ] [IsAddHaarMeasure ν] [SigmaFinite ν]
    (L : E ≃L[ℝ] E) (Q : E → H) (f : E × H → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, ∫⁻ w,
      ENNReal.ofReal |LinearMap.det (L : E →ₗ[ℝ] E)| * f (L z, w + Q z) ∂ν ∂μ) =
      ∫⁻ b, ∫⁻ d, f (b, d) ∂ν ∂μ := by
  have hinner (z : E) :
      (∫⁻ w, ENNReal.ofReal |LinearMap.det (L : E →ₗ[ℝ] E)| *
          f (L z, w + Q z) ∂ν) =
        ENNReal.ofReal |LinearMap.det (L : E →ₗ[ℝ] E)| *
          ∫⁻ d, f (L z, d) ∂ν := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact congrArg
      (fun t : ℝ≥0∞ => ENNReal.ofReal |LinearMap.det (L : E →ₗ[ℝ] E)| * t)
      (lintegral_add_right_eq_self (μ := ν) (fun d : H => f (L z, d)) (Q z))
  simp_rw [hinner]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact lintegral_forward_jacobian μ L
    (fun b => ∫⁻ d, f (b, d) ∂ν) hf.lintegral_prod_right'

variable {A : Type*} [MeasurableSpace A]

/-- Fiberwise Schur change of variables over an arbitrary leading-block
reference.  Only almost-everywhere invertible fibers are represented by `L`;
the intended application takes the leading-block reference restricted to its
positive-definite cone. -/
theorem lintegral_schur_product (κ : Measure A) (μ : Measure E) (ν : Measure H)
    [IsAddHaarMeasure μ] [IsAddHaarMeasure ν] [SigmaFinite ν]
    (L : A → E ≃L[ℝ] E) (Q : A → E → H)
    (f : A × E × H → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ a, ∫⁻ z, ∫⁻ w,
      ENNReal.ofReal |LinearMap.det (L a : E →ₗ[ℝ] E)| *
        f (a, L a z, w + Q a z) ∂ν ∂μ ∂κ) =
      ∫⁻ a, ∫⁻ b, ∫⁻ d, f (a, b, d) ∂ν ∂μ ∂κ := by
  apply lintegral_congr
  intro a
  exact lintegral_schur_fiber μ ν (L a) (Q a) (fun x => f (a, x))
    (hf.comp (measurable_const.prodMk measurable_id))

end WishartVerification
end
end CanonicalSource9

section CanonicalSource10
/- Source: Wishart/FieldDensityEngine.lean -/



/-!
# Normalization and probability transport from an actual density factorization

The weights and reference measures remain explicit. A change-of-variables
identity for every nonnegative measurable test determines the raw measure.
Positive finite lower-dimensional masses then determine the full normalizer
and the exact pushforward of the three independent normalized source laws.
Neither probability nor a conditional Wishart law is assumed for the output.
-/

noncomputable section
open MeasureTheory Set
open scoped Classical ENNReal
namespace WishartVerification.FieldDensity

variable {X A B C : Type*}
  [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]

def normalizer (μ : Measure X) (w : X → ℝ≥0∞) : ℝ≥0∞ := ∫⁻ x, w x ∂μ

def normalized (μ : Measure X) (w : X → ℝ≥0∞) : Measure X :=
  (normalizer μ w)⁻¹ • μ.withDensity w

structure FiniteDensity (μ : Measure X) (w : X → ℝ≥0∞) : Prop where
  positive : 0 < normalizer μ w
  finite : normalizer μ w < ⊤

theorem raw_mass (μ : Measure X) (w : X → ℝ≥0∞) :
    (μ.withDensity w) univ = normalizer μ w := by
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rfl

theorem isProbability_normalized {μ : Measure X} {w : X → ℝ≥0∞}
    (hw : FiniteDensity μ w) : IsProbabilityMeasure (normalized μ w) := by
  constructor
  rw [normalized, Measure.smul_apply, smul_eq_mul, raw_mass,
    ENNReal.inv_mul_cancel hw.positive.ne' hw.finite.ne]

theorem raw_eq_smul_normalized {μ : Measure X} {w : X → ℝ≥0∞}
    (hw : FiniteDensity μ w) : μ.withDensity w = normalizer μ w • normalized μ w := by
  rw [normalized, smul_smul, ENNReal.mul_inv_cancel hw.positive.ne' hw.finite.ne, one_smul]

theorem normalized_of_raw_eq_smul_probability (μ : Measure X) (w : X → ℝ≥0∞)
    (κ : Measure X) [IsProbabilityMeasure κ] {c : ℝ≥0∞}
    (hc0 : 0 < c) (hctop : c < ⊤) (hraw : μ.withDensity w = c • κ) :
    normalizer μ w = c ∧ FiniteDensity μ w ∧ normalized μ w = κ := by
  have hmass : normalizer μ w = c := by
    rw [← raw_mass, hraw, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  refine ⟨hmass, ⟨hmass.symm ▸ hc0, hmass.symm ▸ hctop⟩, ?_⟩
  rw [normalized, hmass, hraw, smul_smul,
    ENNReal.inv_mul_cancel hc0.ne' hctop.ne, one_smul]

/-- Multiplying an actual integrable density by a positive finite constant
changes its mass but not its normalized law. -/
theorem constant_mul {μ : Measure X} {w : X → ℝ≥0∞}
    (hw : FiniteDensity μ w) {a : ℝ≥0∞} (ha0 : 0 < a) (hatop : a < ⊤) :
    normalizer μ (fun x => a * w x) = a * normalizer μ w ∧
    FiniteDensity μ (fun x => a * w x) ∧
    normalized μ (fun x => a * w x) = normalized μ w := by
  letI := isProbability_normalized hw
  apply normalized_of_raw_eq_smul_probability μ (fun x => a * w x) (normalized μ w)
    (CanonicallyOrderedAdd.mul_pos.mpr ⟨ha0, hw.positive⟩)
    (ENNReal.mul_lt_top hatop hw.finite)
  change μ.withDensity (a • w) = (a * normalizer μ w) • normalized μ w
  rw [withDensity_smul' a w hatop.ne, raw_eq_smul_normalized hw, smul_smul]

theorem ae_normalized_of_weight_ne_zero {μ : Measure X} {w : X → ℝ≥0∞}
    (hw : Measurable w) {P : X → Prop} (hP : ∀ x, w x ≠ 0 → P x) :
    ∀ᵐ x ∂normalized μ w, P x := by
  exact Measure.ae_smul_measure ((ae_withDensity_iff hw).mpr (ae_of_all μ hP)) _

theorem triple_withDensity (μA : Measure A) (μB : Measure B) (μC : Measure C)
    [SFinite μA] [SFinite μB] [SFinite μC]
    (wA : A → ℝ≥0∞) (wB : B → ℝ≥0∞) (wC : C → ℝ≥0∞)
    (hwA : Measurable wA) (hwB : Measurable wB) (hwC : Measurable wC) :
    (μA.withDensity wA).prod ((μB.withDensity wB).prod (μC.withDensity wC)) =
      (μA.prod (μB.prod μC)).withDensity (fun z => wA z.1 * (wB z.2.1 * wC z.2.2)) := by
  have hBC : Measurable (fun z : B × C => wB z.1 * wC z.2) :=
    (hwB.comp measurable_fst).mul (hwC.comp measurable_snd)
  rw [prod_withDensity hwB hwC, prod_withDensity hwA hBC]

/-- The reference substitution is an equality of real mathematical integrals,
tested against every nonnegative measurable function. This converts that
equality to the corresponding equality of raw measures. -/
theorem raw_measure_of_product_factorization
    (μX : Measure X) (μA : Measure A) (μB : Measure B) (μC : Measure C)
    [SFinite μA] [SFinite μB] [SFinite μC]
    (wX : X → ℝ≥0∞) (wA : A → ℝ≥0∞) (wB : B → ℝ≥0∞) (wC : C → ℝ≥0∞)
    (hwX : Measurable wX) (hwA : Measurable wA)
    (hwB : Measurable wB) (hwC : Measurable wC)
    (T : A × B × C → X) (hT : Measurable T) (c : ℝ≥0∞)
    (hchange : ∀ f : X → ℝ≥0∞, Measurable f →
      (∫⁻ x, wX x * f x ∂μX) = c *
        ∫⁻ z, (wA z.1 * (wB z.2.1 * wC z.2.2)) * f (T z) ∂μA.prod (μB.prod μC)) :
    μX.withDensity wX = c •
      ((μA.withDensity wA).prod ((μB.withDensity wB).prod (μC.withDensity wC))).map T := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hweight : Measurable (fun z : A × B × C =>
      wA z.1 * (wB z.2.1 * wC z.2.2)) := by fun_prop
  have htest : Measurable (fun z : A × B × C => f (T z)) := hf.comp hT
  rw [lintegral_withDensity_eq_lintegral_mul μX hwX hf,
    lintegral_smul_measure, lintegral_map hf hT,
    triple_withDensity μA μB μC wA wB wC hwA hwB hwC,
    lintegral_withDensity_eq_lintegral_mul _ hweight htest]
  exact hchange f hf

theorem triple_raw_eq_smul_normalized
    (μA : Measure A) (μB : Measure B) (μC : Measure C)
    [SFinite μA] [SFinite μB] [SFinite μC]
    (wA : A → ℝ≥0∞) (wB : B → ℝ≥0∞) (wC : C → ℝ≥0∞)
    (hA : FiniteDensity μA wA) (hB : FiniteDensity μB wB) (hC : FiniteDensity μC wC) :
    (μA.withDensity wA).prod ((μB.withDensity wB).prod (μC.withDensity wC)) =
      (normalizer μA wA * (normalizer μB wB * normalizer μC wC)) •
        ((normalized μA wA).prod ((normalized μB wB).prod (normalized μC wC))) := by
  letI := isProbability_normalized hA
  letI := isProbability_normalized hB
  letI := isProbability_normalized hC
  have hBC : (μB.withDensity wB).prod (μC.withDensity wC) =
      (normalizer μB wB * normalizer μC wC) •
        ((normalized μB wB).prod (normalized μC wC)) := by
    rw [raw_eq_smul_normalized hB, raw_eq_smul_normalized hC,
      Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  rw [raw_eq_smul_normalized hA, hBC,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]

/-- Exact normalized Schur-law engine. Positive finite raw mass and the full
probability law are conclusions, and all three independent source laws remain
the normalized literal densities. -/
theorem normalize_product_factorization
    (μX : Measure X) (μA : Measure A) (μB : Measure B) (μC : Measure C)
    [SFinite μA] [SFinite μB] [SFinite μC]
    (wX : X → ℝ≥0∞) (wA : A → ℝ≥0∞) (wB : B → ℝ≥0∞) (wC : C → ℝ≥0∞)
    (hwX : Measurable wX) (hwA : Measurable wA)
    (hwB : Measurable wB) (hwC : Measurable wC)
    (hA : FiniteDensity μA wA) (hB : FiniteDensity μB wB) (hC : FiniteDensity μC wC)
    (T : A × B × C → X) (hT : Measurable T) {c : ℝ≥0∞}
    (hc0 : 0 < c) (hctop : c < ⊤)
    (hchange : ∀ f : X → ℝ≥0∞, Measurable f →
      (∫⁻ x, wX x * f x ∂μX) = c *
        ∫⁻ z, (wA z.1 * (wB z.2.1 * wC z.2.2)) * f (T z) ∂μA.prod (μB.prod μC)) :
    normalizer μX wX = c * (normalizer μA wA * (normalizer μB wB * normalizer μC wC)) ∧
    FiniteDensity μX wX ∧
    normalized μX wX =
      ((normalized μA wA).prod ((normalized μB wB).prod (normalized μC wC))).map T := by
  letI := isProbability_normalized hA
  letI := isProbability_normalized hB
  letI := isProbability_normalized hC
  let κ := ((normalized μA wA).prod ((normalized μB wB).prod (normalized μC wC))).map T
  haveI : IsProbabilityMeasure κ := by dsimp [κ]; infer_instance
  have hraw := raw_measure_of_product_factorization μX μA μB μC wX wA wB wC
    hwX hwA hwB hwC T hT c hchange
  rw [triple_raw_eq_smul_normalized μA μB μC wA wB wC hA hB hC,
    Measure.map_smul _ hT.aemeasurable, smul_smul] at hraw
  exact normalized_of_raw_eq_smul_probability μX wX κ
    (CanonicallyOrderedAdd.mul_pos.mpr ⟨hc0,
      CanonicallyOrderedAdd.mul_pos.mpr ⟨hA.positive,
        CanonicallyOrderedAdd.mul_pos.mpr ⟨hB.positive, hC.positive⟩⟩⟩)
    (ENNReal.mul_lt_top hctop (ENNReal.mul_lt_top hA.finite
      (ENNReal.mul_lt_top hB.finite hC.finite))) hraw

/-- A nested-integral variant matches the concrete Schur substitution. -/
theorem product_factorization_of_nested
    (μX : Measure X) (μA : Measure A) (μB : Measure B) (μC : Measure C)
    [SFinite μA] [SFinite μB] [SFinite μC]
    (wX : X → ℝ≥0∞) (wA : A → ℝ≥0∞) (wB : B → ℝ≥0∞) (wC : C → ℝ≥0∞)
    (hwA : Measurable wA) (hwB : Measurable wB) (hwC : Measurable wC)
    (T : A × B × C → X) (hT : Measurable T) (c : ℝ≥0∞)
    (hchange : ∀ f : X → ℝ≥0∞, Measurable f →
      (∫⁻ x, wX x * f x ∂μX) = c *
        ∫⁻ a, ∫⁻ b, ∫⁻ d, (wA a * (wB b * wC d)) * f (T (a,b,d)) ∂μC ∂μB ∂μA) :
    ∀ f : X → ℝ≥0∞, Measurable f →
      (∫⁻ x, wX x * f x ∂μX) = c *
        ∫⁻ z, (wA z.1 * (wB z.2.1 * wC z.2.2)) * f (T z) ∂μA.prod (μB.prod μC) := by
  intro f hf
  rw [hchange f hf]
  congr 1
  have hm : Measurable (fun z : A × B × C =>
      (wA z.1 * (wB z.2.1 * wC z.2.2)) * f (T z)) := by fun_prop
  rw [lintegral_prod _ hm.aemeasurable]
  apply lintegral_congr
  intro a
  exact (lintegral_prod _ (hm.comp (measurable_const.prodMk measurable_id)).aemeasurable).symm

end WishartVerification.FieldDensity
end
end CanonicalSource10
