module

public import VolumePolynomials.AreaTranscendence
public import VolumePolynomials.AlgebraicGerms
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.RingTheory.Localization.Integral

@[expose] public section
noncomputable section

open Filter Polynomial Set Metric
open scoped Topology Polynomial.Bivariate

namespace VolumePolynomials

/-- Germs of real functions on a right-hand neighborhood of zero. -/
abbrev PositiveRealGerm := Germ (𝓝[>] (0 : ℝ)) ℝ

theorem positive_nhds_le_cofinite : (𝓝[>] (0 : ℝ)) ≤ Filter.cofinite := by
  first
  | apply le_trans _ (nhdsNE_le_cofinite (0 : ℝ))
    exact nhdsWithin_mono 0 (fun x hx => ne_of_gt hx)

/-- A nonzero real polynomial is invertible as a punctured right-hand germ,
even when it vanishes at zero itself. -/
theorem polynomial_evaluation_germ_isUnit (p : Polynomial ℝ) (hp : p ≠ 0) :
    IsUnit (germPolynomialEvaluation (𝓝[>] (0 : ℝ)) id p) := by
  first
  | have hne : ∀ᶠ x : ℝ in 𝓝[>] 0, p.eval x ≠ 0 :=
      (Polynomial.eventually_eval_ne_zero_cofinite hp).filter_mono positive_nhds_le_cofinite
    apply isUnit_iff_exists_inv.mpr
    refine ⟨Germ.ofFun (fun x : ℝ => (p.eval x)⁻¹), ?_⟩
    change Germ.ofFun (fun x : ℝ => p.eval x * (p.eval x)⁻¹) =
      (Germ.ofFun (fun _ : ℝ => (1 : ℝ)) : PositiveRealGerm)
    apply Germ.coe_eq.mpr
    filter_upwards [hne] with x hx
    exact mul_inv_cancel₀ hx

/-- The standard rational function field is evaluated into actual right-hand
germs by the universal property of localization. -/
def rationalFunctionGermEvaluation : RatFunc ℝ →+* PositiveRealGerm :=
  IsLocalization.lift (S := RatFunc ℝ) (M := nonZeroDivisors (Polynomial ℝ))
    (g := germPolynomialEvaluation (𝓝[>] (0 : ℝ)) id)
    (fun p => polynomial_evaluation_germ_isUnit p (nonZeroDivisors.ne_zero p.property))

@[simp] theorem rationalFunctionGermEvaluation_polynomial (p : Polynomial ℝ) :
    rationalFunctionGermEvaluation (algebraMap (Polynomial ℝ) (RatFunc ℝ) p) =
      Germ.ofFun (fun x : ℝ => p.eval x) :=
  IsLocalization.lift_eq _ p

theorem rationalFunctionGermEvaluation_injective :
    Function.Injective rationalFunctionGermEvaluation := rationalFunctionGermEvaluation.injective

def rationalFunctionGermAlgebra : Algebra (RatFunc ℝ) PositiveRealGerm :=
  rationalFunctionGermEvaluation.toAlgebra

theorem realAreaSeries_no_right_polynomial_relation {θ : ℝ}
    (hθ : Real.cos θ = 1 / 3) (hsin : Real.sin θ ≠ 0) :
    ¬ HasPolynomialRelation (𝓝[>] (0 : ℝ)) id (realAreaSeries θ) := by
  first
  | rintro ⟨P, hP, hrel⟩
    have hreal : ∀ᶠ x : ℝ in 𝓝[>] 0,
        (complexifyBivariate P).eval₂ (Polynomial.evalRingHom (x : ℂ))
          (areaGeneratingFunction θ (x : ℂ)) = 0 := by
      filter_upwards [hrel] with x hx
      rw [← ofReal_realAreaSeries, complexifyBivariate_eval, Polynomial.eval₂_evalRingHom]
      simpa only [id_eq, hx, Complex.ofReal_zero] using congrArg Complex.ofReal hx
    have hall := analytic_zero_on_disk_of_right_germ _
      (analytic_bivariate_relation _ (areaGeneratingFunction_analyticOnNhd θ hsin)
        (complexifyBivariate P)) hreal
    apply areaGeneratingFunction_no_polynomial_relation hθ hsin (complexifyBivariate P)
      (complexifyBivariate_ne_zero hP)
    intro z hz
    exact hall (by simpa using hz)

/-- Literal transcendence over Mathlib's rational function field `RatFunc ℝ`.
The algebra structure evaluates the independent variable at the identity germ;
its injectivity is proved above. Polynomial-ring and fraction-field algebraicity
are equivalent by the kernel-checked denominator-clearing theorem. -/
theorem realAreaSeries_transcendental_ratFunc {θ : ℝ}
    (hθ : Real.cos θ = 1 / 3) (hsin : Real.sin θ ≠ 0) :
    letI : Algebra (RatFunc ℝ) PositiveRealGerm := rationalFunctionGermAlgebra
    Transcendental (RatFunc ℝ) (Germ.ofFun (realAreaSeries θ) : PositiveRealGerm) := by
  first
  | letI : Algebra (RatFunc ℝ) PositiveRealGerm := rationalFunctionGermAlgebra
    letI : Algebra (Polynomial ℝ) PositiveRealGerm :=
      (germPolynomialEvaluation (𝓝[>] (0 : ℝ)) id).toAlgebra
    letI : IsScalarTower (Polynomial ℝ) (RatFunc ℝ) PositiveRealGerm := by
      apply IsScalarTower.of_algebraMap_eq
      intro p
      exact (rationalFunctionGermEvaluation_polynomial p).symm
    intro h
    have hp : IsAlgebraic (Polynomial ℝ)
        (Germ.ofFun (realAreaSeries θ) : PositiveRealGerm) :=
      (IsFractionRing.isAlgebraic_iff (Polynomial ℝ) (RatFunc ℝ) PositiveRealGerm).mpr h
    exact realAreaSeries_no_right_polynomial_relation hθ hsin
      ((hasPolynomialRelation_iff_isAlgebraic (𝓝[>] (0 : ℝ)) id (realAreaSeries θ)).mpr hp)


end VolumePolynomials
