module

public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The analytic obstruction behind the logarithmic boundary gap

This file proves the nonalgebraicity mechanism used in Corollary 5.6 of
*Volume polynomials and the Heine–Shephard problem*. The results are about
ordinary real polynomials and their actual evaluations. No assertion about
mixed volumes or semialgebraic sets is assumed in their definitions.
-/

open Filter Polynomial Asymptotics
open scoped Topology Polynomial.Bivariate

namespace VolumePolynomials

/-- The elementary two-sided logarithmic estimates imply the two asymptotic
properties needed below. The upper constant need not be optimal. -/
theorem growth_of_two_sided_log_bounds {g : ℝ → ℝ} {c C : ℝ}
    (hc : 0 < c)
    (hbound : ∀ᶠ x in atTop, c * Real.log x ≤ g x ∧ g x ≤ C * Real.log x) :
    Tendsto g atTop atTop ∧ g =O[atTop] Real.log := by
  constructor
  · exact tendsto_atTop_mono' atTop (hbound.mono fun _ h => h.1)
      (Tendsto.const_mul_atTop hc Real.tendsto_log_atTop)
  · apply IsBigO.of_bound C
    filter_upwards [hbound, eventually_ge_atTop (1 : ℝ)] with x hx hxone
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hxone
    have hg : 0 ≤ g x := (mul_nonneg hc.le hlog).trans hx.1
    simpa only [Real.norm_eq_abs, abs_of_nonneg hg, abs_of_nonneg hlog] using hx.2

/-- Every polynomial of a logarithmically bounded function is negligible
compared with the independent variable. -/
theorem polynomial_comp_logBound_div_tendsto_zero
    {g : ℝ → ℝ} (hg : Tendsto g atTop atTop)
    (hlog : g =O[atTop] Real.log) (p : ℝ[X]) :
    Tendsto (fun x => p.eval (g x) / x) atTop (𝓝 0) := by
  have hp : p.eval =O[atTop] fun y => y ^ p.natDegree := by
    simpa using p.isBigO_atTop_of_degree_le (X ^ p.natDegree)
      (by simp)
  have hpow : (fun x => g x ^ p.natDegree) =O[atTop]
      fun x => Real.log x ^ p.natDegree := hlog.pow _
  exact (((hp.comp_tendsto hg).trans hpow).trans_isLittleO
    Real.isLittleO_pow_log_id_atTop).tendsto_div_nhds_zero

/-- Allowing polynomial dependence on `1 / x` preserves the preceding bound. -/
theorem bivariate_comp_logBound_div_tendsto_zero
    {g : ℝ → ℝ} (hg : Tendsto g atTop atTop)
    (hlog : g =O[atTop] Real.log) (p : ℝ[X][Y]) :
    Tendsto (fun x => p.evalEval (g x) x⁻¹ / x) atTop (𝓝 0) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [evalEval_add, add_div, zero_add] using hp.add hq
  | monomial n a =>
      have h := (polynomial_comp_logBound_div_tendsto_zero hg hlog a).mul
        (tendsto_inv_atTop_zero.pow n)
      simpa only [evalEval, eval_monomial, eval_mul, eval_pow, eval_C,
        zero_mul, mul_div_right_comm] using h

/-- A nonzero polynomial evaluated along a function tending to infinity cannot
tend to zero. This also covers constant nonzero polynomials. -/
theorem polynomial_comp_not_tendsto_zero
    {g : ℝ → ℝ} (hg : Tendsto g atTop atTop)
    {p : ℝ[X]} (hp : p ≠ 0) :
    ¬ Tendsto (fun x => p.eval (g x)) atTop (𝓝 0) := by
  intro h
  by_cases hn : p.natDegree = 0
  · have hpc : p = C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hn
    have hval : p.coeff 0 = 0 := by
      rw [hpc] at h
      simpa only [eval_C, tendsto_const_nhds_iff] using h
    exact hp (by rw [hpc, hval, C_0])
  · have habs : Tendsto (fun x => |p.eval (g x)|) atTop atTop :=
      (p.abs_tendsto_atTop (Polynomial.natDegree_pos_iff_degree_pos.mp
        (Nat.pos_of_ne_zero hn))).comp hg
    have hzero : Tendsto (fun x => |p.eval (g x)|) atTop (𝓝 0) := by
      simpa using h.abs
    exact (not_tendsto_nhds_of_tendsto_atTop habs 0) hzero

/-- A function tending to infinity with logarithmic growth satisfies no
nonzero polynomial relation with the reciprocal independent variable.
This is the contradiction used after the lowest power of `s` is divided out
in Corollary 5.6, with `x = 1 / s`. -/
theorem no_bivariate_relation_of_logBound
    {g : ℝ → ℝ} (hg : Tendsto g atTop atTop)
    (hlog : g =O[atTop] Real.log) {p : ℝ[X][Y]} (hp : p ≠ 0) :
    ¬ (∀ᶠ x in atTop, p.evalEval (g x) x⁻¹ = 0) := by
  intro hrel
  obtain ⟨q, hpq, hq⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp 0
  simp only [map_zero, sub_zero] at hpq hq
  have hq0 : q.coeff 0 ≠ 0 := by
    simpa only [X_dvd_iff] using hq
  have hqrel : ∀ᶠ x in atTop, q.evalEval (g x) x⁻¹ = 0 := by
    filter_upwards [hrel, eventually_gt_atTop (0 : ℝ)] with x hx hxpos
    rw [hpq, evalEval_mul, evalEval_pow, evalEval_X] at hx
    exact (mul_eq_zero.mp hx).resolve_left (pow_ne_zero _ (inv_ne_zero hxpos.ne'))
  have ht := bivariate_comp_logBound_div_tendsto_zero hg hlog q.divX
  have heq : (fun x => (q.coeff 0).eval (g x)) =ᶠ[atTop]
      (fun x => -(q.divX.evalEval (g x) x⁻¹ / x)) := by
    filter_upwards [hqrel] with x hx
    have hsplit := congrArg (fun p : ℝ[X][Y] => p.evalEval (g x) x⁻¹)
      q.X_mul_divX_add
    simp only [evalEval_add, evalEval_mul, evalEval_X, evalEval_C, hx] at hsplit
    rw [div_eq_mul_inv]
    nlinarith [hsplit]
  have hneg : Tendsto (fun x => -(q.divX.evalEval (g x) x⁻¹ / x)) atTop (𝓝 0) := by
    simpa using ht.neg
  exact polynomial_comp_not_tendsto_zero hg hq0 (hneg.congr' heq.symm)

end VolumePolynomials
