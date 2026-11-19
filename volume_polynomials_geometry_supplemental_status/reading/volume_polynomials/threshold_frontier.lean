module

public import VolumePolynomials.AlgebraicGerms
public import VolumePolynomials.SemialgebraicBoundary
public import VolumePolynomials.ThresholdScalar
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Logarithmic boundary gaps exclude semialgebraicity

This proves the final implication in Corollary 5.6 directly from the finite-sign
definition of a semialgebraic set. An attained fiber minimum lies on the frontier;
a frontier satisfies a nonzero polynomial relation. The explicit comparison root
is algebraic. Algebraic closure in the ring of function germs eliminates the root,
and the logarithmic growth theorem gives a contradiction.

The actual geometric fiber minima and the two-sided gap estimate remain explicit
hypotheses. They must be supplied by the volume-polynomial normalization and
Theorem 5.5 before this can imply the paper's main Theorem 1.1.
-/

open Filter Polynomial Asymptotics Set
open scoped Topology Polynomial.Bivariate

namespace VolumePolynomials

theorem hasPolynomialRelation_comparisonRoot {α : Type*} (l : Filter α) (s : α → ℝ) :
    HasPolynomialRelation l s (fun x => comparisonRoot (s x)) := by
  refine ⟨Y ^ 2 - C (1 + X) * Y + C (C (1 / 2) * X), ?_, ?_⟩
  · intro hzero
    have hcoeff := congrArg (fun p : ℝ[X][Y] => p.coeff 2) hzero
    norm_num [Polynomial.coeff_one] at hcoeff
  · apply Filter.Eventually.of_forall
    intro x
    have hquad := comparisonRoot_quadratic (s x)
    simp only [evalEval_add, evalEval_sub, evalEval_pow, evalEval_mul, evalEval_X,
      evalEval_C, eval_add, eval_one, eval_X, eval_mul, eval_C]
    nlinarith [hquad]

/-- A semialgebraic set's attained lower fiber endpoints satisfy an actual
nonzero polynomial equation on every sufficiently small positive interval. -/
theorem polynomialRelation_of_semialgebraic_minima
    {S : Set (Fin 2 → ℝ)} {b : ℝ → ℝ} {a : ℝ}
    (ha : 0 < a) (hS : TauCeti.IsSemialgebraic S)
    (hattain : ∀ x ∈ Ioo 0 a, ![x, b x] ∈ S)
    (hminimum : ∀ x ∈ Ioo 0 a, ∀ y : ℝ, ![x, y] ∈ S → b x ≤ y) :
    HasPolynomialRelation atTop (fun x : ℝ => x⁻¹) (fun x => b x⁻¹) := by
  obtain ⟨p, hp, hfront⟩ := frontier_polynomial_relation hS
  let q : ℝ[X][Y] := Polynomial.Bivariate.swap (twoVariableEquiv p)
  have hq : q ≠ 0 := by
    intro hqzero
    apply hp
    apply twoVariableEquiv.injective
    apply Polynomial.Bivariate.swap.injective
    simpa only [map_zero] using hqzero
  refine ⟨q, hq, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    tendsto_inv_atTop_zero.eventually (Iio_mem_nhds ha)] with x hx hxsmall
  have hxin : x⁻¹ ∈ Ioo 0 a := ⟨inv_pos.mpr hx, hxsmall⟩
  change (Polynomial.Bivariate.swap (twoVariableEquiv p)).evalEval x⁻¹ (b x⁻¹) = 0
  rw [bivariate_eval_swap, twoVariableEquiv_eval]
  exact hfront _ (fiber_minimum_mem_frontier (hattain _ hxin) (hminimum _ hxin))

/-- The exact logarithmic minimum-gap implication, with no quantifier-elimination
assumption and no semialgebraicity hypothesis about the minimum function itself. -/
theorem not_semialgebraic_of_logarithmic_minimum_gap_frontier
    {S : Set (Fin 2 → ℝ)} {b : ℝ → ℝ} {a c C : ℝ}
    (ha : 0 < a) (hc : 0 < c)
    (hattain : ∀ x ∈ Ioo 0 a, ![x, b x] ∈ S)
    (hminimum : ∀ x ∈ Ioo 0 a, ∀ y : ℝ, ![x, y] ∈ S → b x ≤ y)
    (hgap : ∀ᶠ x in 𝓝[>] (0 : ℝ),
      c * x ^ 3 * Real.log x⁻¹ ≤ comparisonRoot x - b x ∧
      comparisonRoot x - b x ≤ C * x ^ 3 * Real.log x⁻¹) :
    ¬ TauCeti.IsSemialgebraic S := by
  intro hS
  have hb := polynomialRelation_of_semialgebraic_minima ha hS hattain hminimum
  have hr := hasPolynomialRelation_comparisonRoot atTop (fun x : ℝ => x⁻¹)
  have hnz : ∀ᶠ x in atTop, (x : ℝ)⁻¹ ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact inv_ne_zero hx.ne'
  have hrelation := hasPolynomialRelation_scaled_gap hr hb hnz 3
  have hbound : ∀ᶠ x in atTop,
      c * Real.log x ≤ (comparisonRoot x⁻¹ - b x⁻¹) / (x⁻¹) ^ 3 ∧
      (comparisonRoot x⁻¹ - b x⁻¹) / (x⁻¹) ^ 3 ≤ C * Real.log x := by
    filter_upwards [tendsto_inv_atTop_nhdsGT_zero.eventually hgap,
      eventually_gt_atTop (0 : ℝ)] with x hx hxpos
    have hpow : 0 < (x⁻¹) ^ 3 := pow_pos (inv_pos.mpr hxpos) 3
    simp only [inv_inv] at hx
    constructor
    · apply (le_div_iff₀ hpow).mpr
      nlinarith [hx.1]
    · apply (div_le_iff₀ hpow).mpr
      nlinarith [hx.2]
  obtain ⟨hinf, hlog⟩ := growth_of_two_sided_log_bounds hc hbound
  exact no_polynomialRelation_of_logBound hinf hlog hrelation

end VolumePolynomials
