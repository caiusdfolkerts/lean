module

public import VolumePolynomials.RadialAlgebraicObstruction
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Topology.Order.LeftRightNhds

@[expose] public section
noncomputable section

namespace VolumePolynomials

open scoped Topology
open Set Filter Metric Polynomial

/-- The real area function displayed in (7.11), with the sum indexed from one. -/
def realAreaSeries (θ lam : ℝ) : ℝ :=
  (∑' n : ℕ, |Real.sin (((n + 1 : ℕ) : ℝ) * θ)| * lam ^ (n + 1)) /
    ((1 - lam ^ 2) * Real.sin θ)

theorem ofReal_realAreaSeries (θ lam : ℝ) :
    (realAreaSeries θ lam : ℂ) = areaGeneratingFunction θ (lam : ℂ) := by
  first
  | simp only [realAreaSeries, areaGeneratingFunction, sineGeneratingFunction,
      Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one,
      Complex.ofReal_pow, Complex.ofReal_tsum]

/-- The complex identity theorem applied to zeros accumulating from the positive
real axis. An eventual identity near zero is enough. -/
theorem analytic_zero_on_disk_of_right_germ (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (ball 0 1))
    (hz : ∀ᶠ x : ℝ in 𝓝[>] 0, f (x : ℂ) = 0) :
    Set.EqOn f 0 (ball 0 1) := by
  first
  | let r : ℕ → ℝ := fun n => (1 / 2) * (1 / 2) ^ n
    have hrpos (n : ℕ) : 0 < r n := by dsimp [r]; positivity
    have hr : Tendsto r atTop (𝓝 0) := by
      simpa [r] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (1 / 2 : ℝ)
    have hrC : Tendsto (fun n => (r n : ℂ)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, Complex.ofReal_zero] using
        Complex.continuous_ofReal.continuousAt.tendsto.comp hr
    have hrRight : Tendsto r atTop (𝓝[>] (0 : ℝ)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hr, Filter.Eventually.of_forall hrpos⟩
    have hzeros : ∀ᶠ n in atTop, f (r n : ℂ) = 0 := hrRight.eventually hz
    have hclosure : (0 : ℂ) ∈ closure ({z : ℂ | f z = 0} \ {0}) := by
      apply mem_closure_of_tendsto hrC
      filter_upwards [hzeros] with n hn
      refine ⟨hn, ?_⟩
      simpa using (show (r n : ℂ) ≠ 0 by exact_mod_cast (hrpos n).ne')
    exact hf.eqOn_zero_of_preconnected_of_mem_closure (convex_ball (0 : ℂ) (1 : ℝ)).isPreconnected
      (mem_ball_self (by norm_num)) hclosure

/-- The complex identity theorem applied to an actual real interval inside the disk. -/
theorem analytic_zero_on_disk_of_real_interval (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (ball 0 1))
    (hz : ∀ x : ℝ, x ∈ Ioo 0 1 → f (x : ℂ) = 0) :
    Set.EqOn f 0 (ball 0 1) := by
  first
  | apply analytic_zero_on_disk_of_right_germ f hf
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
    exact hz x hx

theorem analytic_bivariate_relation (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F (ball 0 1))
    (P : Polynomial (Polynomial ℂ)) :
    AnalyticOnNhd ℂ (fun z => P.eval₂ (Polynomial.evalRingHom z) (F z)) (ball 0 1) := by
  first
  | simp_rw [Polynomial.eval₂_eq_sum_range, Polynomial.coe_evalRingHom]
    apply Finset.analyticOnNhd_fun_sum
    intro n hn
    exact ((AnalyticOnNhd.eval_polynomial (P.coeff n)).mono (Set.subset_univ _)).mul (hF.pow n)

/-- A real polynomial in two variables, lifted coefficientwise to the complex numbers. -/
def complexifyBivariate (P : Polynomial (Polynomial ℝ)) : Polynomial (Polynomial ℂ) :=
  P.map (Polynomial.mapRingHom Complex.ofRealHom)

theorem complexifyBivariate_ne_zero {P : Polynomial (Polynomial ℝ)} (hP : P ≠ 0) :
    complexifyBivariate P ≠ 0 := by
  first
  | apply (Polynomial.map_ne_zero_iff (Polynomial.map_injective Complex.ofRealHom
      Complex.ofReal_injective)).mpr hP

theorem complexifyBivariate_eval (P : Polynomial (Polynomial ℝ)) (x y : ℝ) :
    (complexifyBivariate P).eval₂ (Polynomial.evalRingHom (x : ℂ)) (y : ℂ) =
      ((P.eval₂ (Polynomial.evalRingHom x) y : ℝ) : ℂ) := by
  first
  | have hcomp : (Polynomial.evalRingHom (x : ℂ)).comp
        (Polynomial.mapRingHom Complex.ofRealHom) =
          Complex.ofRealHom.comp (Polynomial.evalRingHom x) := by
      apply RingHom.ext
      intro p
      change (p.map Complex.ofRealHom).eval (Complex.ofRealHom x) =
        Complex.ofRealHom (p.eval x)
      exact Polynomial.eval_map_apply (p := p) Complex.ofRealHom x
    rw [complexifyBivariate, Polynomial.eval₂_map, hcomp]
    exact (Polynomial.hom_eval₂ (p := P) (f := Polynomial.evalRingHom x)
      (g := Complex.ofRealHom) (x := y)).symm

/-- No nonzero polynomial with arbitrary real coefficients can vanish on the graph of the
area function over the full parameter interval `(0,1)`. This is the polynomial-relation form
of transcendence over `ℝ(lam)`. -/
theorem realAreaSeries_no_polynomial_relation {θ : ℝ}
    (hθ : Real.cos θ = 1 / 3) (hsin : Real.sin θ ≠ 0)
    (P : Polynomial (Polynomial ℝ)) (hP : P ≠ 0) :
    ¬ ∀ lam : ℝ, lam ∈ Ioo 0 1 →
      P.eval₂ (Polynomial.evalRingHom lam) (realAreaSeries θ lam) = 0 := by
  first
  | intro hrel
    have hreal : ∀ lam : ℝ, lam ∈ Ioo 0 1 →
        (complexifyBivariate P).eval₂ (Polynomial.evalRingHom (lam : ℂ))
          (areaGeneratingFunction θ (lam : ℂ)) = 0 := by
      intro lam hlam
      rw [← ofReal_realAreaSeries, complexifyBivariate_eval, hrel lam hlam]
      simp
    have hall := analytic_zero_on_disk_of_real_interval _
      (analytic_bivariate_relation _ (areaGeneratingFunction_analyticOnNhd θ hsin)
        (complexifyBivariate P)) hreal
    apply areaGeneratingFunction_no_polynomial_relation hθ hsin (complexifyBivariate P)
      (complexifyBivariate_ne_zero hP)
    intro z hz
    exact hall (by simpa using hz)

end VolumePolynomials
