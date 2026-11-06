module

public import wishart.verified.field_residual08
public import wishart.verified.field_frontier03
public import wishart.verified.core01
public import Mathlib.Topology.Algebra.MvPolynomial

/- Source: Wishart/SpectralExampleMoments.lean -/

@[expose] public section

/-!
# Finite moments of the uncomposed spectral examples

Polynomial evaluation is a literal finite sum of monomials.  A symmetric
absolute norm of the square-root vector is bounded by its value at the all-one
vector times the square root of the coordinate sum.  Thus the asserted growth
bounds are derived from the examples themselves, rather than assumed.
-/

noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators ENNReal

namespace WishartVerification
variable {Ω σ : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

theorem HasAllFiniteMoments.polynomial_eval
    (P : MvPolynomial σ ℝ) (x : Ω → σ → ℝ)
    (hx : ∀ i, HasAllFiniteMoments (fun ω => x ω i) μ) :
    HasAllFiniteMoments (fun ω => MvPolynomial.eval (x ω) P) μ := by
  simp only [MvPolynomial.eval_eq]
  apply HasAllFiniteMoments.finset_sum P.support
  intro d hd
  apply HasAllFiniteMoments.const_mul
  apply HasAllFiniteMoments.finset_prod d.support
  intro i hi
  simpa only [Real.rpow_natCast] using
    (hx i).rpow (show (0 : ℝ) ≤ (d i : ℝ) by positivity)

theorem HasAllFiniteMoments.finite_lintegral_product
    {ι : Type*} [Fintype ι] (f : ι → Ω → ℝ)
    (hf : ∀ i, HasAllFiniteMoments (f i) μ) :
    (∫⁻ ω, ENNReal.ofReal (∏ i, f i ω) ∂μ) < ⊤ := by
  have hi := (HasAllFiniteMoments.finset_prod Finset.univ f (fun i _ => hf i)).integrable
  exact lt_of_le_of_lt (lintegral_mono fun ω => Real.ofReal_le_enorm (∏ i, f i ω))
    hi.hasFiniteIntegral

end WishartVerification

namespace Wishart.Spectral.SymmetricAbsoluteNorm
open WishartVerification
variable {k : ℕ} (q : SymmetricAbsoluteNorm k)

theorem sqrt_value_le_sum_sqrt {x : Fin k → ℝ} (hx : ∀ i, 0 ≤ x i) :
    q (fun i => Real.sqrt (x i)) ≤ q (fun _ => 1) * Real.sqrt (∑ i, x i) := by
  have hs : 0 ≤ ∑ i, x i := Finset.sum_nonneg fun i _ => hx i
  calc
    _ ≤ q (fun _ => Real.sqrt (∑ i, x i)) :=
      q.monotoneOn_nonnegative (fun i => Real.sqrt_nonneg _)
        (fun i => Real.sqrt_nonneg _) (fun i => Real.sqrt_le_sqrt
          (Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ i)))
    _ = q (Real.sqrt (∑ i, x i) • (fun _ : Fin k => (1 : ℝ))) := by
      congr 1
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, mul_one]
    _ = _ := by rw [q.smul_nonneg (Real.sqrt_nonneg _)]; exact mul_comm _ _

theorem sqrt_value_allFiniteMoments {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (x : Ω → Fin k → ℝ)
    (hxm : Measurable x) (hx0 : ∀ᵐ ω ∂μ, ∀ i, 0 ≤ x ω i)
    (hx : ∀ i, HasAllFiniteMoments (fun ω => x ω i) μ) :
    HasAllFiniteMoments (fun ω => q (fun i => Real.sqrt (x ω i))) μ := by
  have hroot : Measurable (fun ω => fun i => Real.sqrt (x ω i)) := by
    apply measurable_pi_iff.mpr
    intro i
    exact Real.continuous_sqrt.measurable.comp ((measurable_pi_apply i).comp hxm)
  have hsum := HasAllFiniteMoments.finset_sum Finset.univ
    (fun i ω => x ω i) (fun i _ => hx i)
  have henv : HasAllFiniteMoments
      (fun ω => q (fun _ => 1) * Real.sqrt (∑ i, x ω i)) μ := by
    simpa only [Real.sqrt_eq_rpow] using
      (hsum.rpow (show (0 : ℝ) ≤ 1 / 2 by norm_num)).const_mul (q (fun _ => 1))
  exact allFiniteMoments_of_nonnegative_bound (q.continuous.measurable.comp hroot)
    (Filter.Eventually.of_forall fun ω => q.nonneg _)
    (hx0.mono fun ω hω => q.sqrt_value_le_sum_sqrt hω) henv

end Wishart.Spectral.SymmetricAbsoluteNorm
