module

public import wishart.verified.radial_expectation_c2

/-!
# The literal analytic conclusions of the radial mean lemma

This interface records ordinary derivatives, the finite right derivative at
zero, the displayed ODE, and monotonicity under nonnegativity of the expected
operator. The signed-radius derivative formulas discharge every analytic
hypothesis; no pointwise sign condition on the test is needed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open WishartVerification
open scoped Topology

namespace Wishart.FiniteOrder

/-- The analytic conclusions of Lemma 3.1, stated using ordinary derivatives. -/
structure RadialMeanConclusion (N : ℝ) (F G : ℝ → ℝ) : Prop where
  differentiable : ∀ t, 0 < t → DifferentiableAt ℝ F t
  twice_differentiable : ∀ t, 0 < t → DifferentiableAt ℝ (deriv F) t
  origin : ∃ d : ℝ, HasDerivWithinAt F d (Ici 0) 0 ∧
    Tendsto (deriv F) (𝓝[>] (0 : ℝ)) (𝓝 d)
  ode : ∀ t, 0 < t → 4 * t * deriv (deriv F) t + 2 * N * deriv F t = G t
  monotone : (∀ t, 0 < t → 0 ≤ G t) → MonotoneOn F (Ici 0)

theorem RadialMeanConclusion.congr {N : ℝ} {F F' G G' : ℝ → ℝ}
    (h : RadialMeanConclusion N F G) (hF : F = F') (hG : G = G') :
    RadialMeanConclusion N F' G' := by
  subst F'
  subst G'
  exact h

/-- An even twice differentiable signed-radius expectation yields precisely
the square-root profile and boundary conditions in the paper. -/
theorem radialMeanConclusion_of_signedRadius {N : ℝ} (hN : 0 < N)
    {J J₁ J₂ G : ℝ → ℝ}
    (hJ : ∀ r, HasDerivAt J (J₁ r) r)
    (hJ₁ : ∀ r, HasDerivAt J₁ (J₂ r) r)
    (heven : ∀ r, J (-r) = J r)
    (hODE : ∀ t, 0 < t →
      4 * t * ((J₂ (Real.sqrt t) - J₁ (Real.sqrt t) / Real.sqrt t) / (4 * t)) +
        2 * N * (J₁ (Real.sqrt t) / (2 * Real.sqrt t)) = G t) :
    RadialMeanConclusion N (fun t => J (Real.sqrt t)) G := by
  let F : ℝ → ℝ := fun t => J (Real.sqrt t)
  let D : ℝ → ℝ := fun t => J₁ (Real.sqrt t) / (2 * Real.sqrt t)
  let D₂ : ℝ → ℝ := fun t =>
    (J₂ (Real.sqrt t) - J₁ (Real.sqrt t) / Real.sqrt t) / (4 * t)
  have hFD (t : ℝ) (ht : 0 < t) : HasDerivAt F (D t) t :=
    Wishart.hasDerivAt_sqrt_profile ht (hJ (Real.sqrt t))
  have hDD₂ (t : ℝ) (ht : 0 < t) : HasDerivAt D (D₂ t) t :=
    hasDerivAt_sqrt_profile_derivative ht (hJ₁ (Real.sqrt t))
  have hderiv (t : ℝ) (ht : 0 < t) :
      HasDerivAt (deriv F) (D₂ t) t := by
    apply (hDD₂ t ht).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact (hFD s hs).deriv
  refine ⟨fun t ht => (hFD t ht).differentiableAt,
    fun t ht => (hderiv t ht).differentiableAt, ?_, ?_, ?_⟩
  · refine ⟨J₂ 0 / 2, ?_, ?_⟩
    · exact Wishart.hasDerivWithinAt_sqrt_profile_zero_of_even heven (hJ 0)
        (fun r _ => hJ r) (hJ₁ 0)
    · exact Wishart.tendsto_deriv_sqrt_profile_of_even heven (hJ 0)
        (fun r _ => hJ r) (hJ₁ 0)
  · intro t ht
    change 4 * t * deriv (deriv F) t + 2 * N * deriv F t = G t
    rw [(hderiv t ht).deriv, (hFD t ht).deriv]
    exact hODE t ht
  · intro hG
    apply Wishart.monotoneOn_of_radial_operator_nonneg_of_derivative_limit
      (N := N) (D := D) (D₂ := D₂) (L := J₂ 0 / 2) hN
    · exact ((continuous_iff_continuousAt.mpr fun r => (hJ r).continuousAt).comp
        Real.continuous_sqrt).continuousOn
    · exact hFD
    · exact hDD₂
    · exact Wishart.tendsto_sqrt_derivative_quotient
        (Wishart.hasDerivAt_even_zero heven (hJ 0)) (hJ₁ 0)
    · intro t ht
      change 0 ≤ 4 * t * ((J₂ (Real.sqrt t) - J₁ (Real.sqrt t) / Real.sqrt t) / (4 * t)) +
        2 * N * (J₁ (Real.sqrt t) / (2 * Real.sqrt t))
      rw [hODE t ht]
      exact hG t ht

/-- The signed-radius integrated identity has exactly the displayed ODE after
the square-root substitution. -/
theorem sqrt_radial_ode_of_signed_identity {N r t A B G : ℝ}
    (ht : 0 < t) (hr : r = Real.sqrt t)
    (h : r * G = r * A + (N - 1) * B) :
    4 * t * ((A - B / Real.sqrt t) / (4 * t)) +
      2 * N * (B / (2 * Real.sqrt t)) = G := by
  subst r
  have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  have heq : 4 * t * ((A - B / Real.sqrt t) / (4 * t)) +
      2 * N * (B / (2 * Real.sqrt t)) =
      (Real.sqrt t * A + (N - 1) * B) / Real.sqrt t := by
    field_simp
    <;> ring
  rw [heq, ← h, mul_div_cancel_left₀ G hs]

end Wishart.FiniteOrder
