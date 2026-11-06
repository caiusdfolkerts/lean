module

public import wishart.verified.lemma_3_1_real

/-!
# Independent literal statements for Lemma 3.1

These gates spell out the open-neighborhood C² hypothesis and the three
polynomial bounds separately. Their conclusions use ordinary derivatives and
actual independent product measures. No theorem-type alias, assumed moment
identity, assumed radial ODE, or pointwise generator sign condition occurs.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti.Probability Matrix Filter Set
open WishartVerification Wishart.FiniteOrder
open scoped Topology RealInnerProductSpace

namespace WishartAudit

/-- The usual polynomial operator-norm bound on a Hessian is equivalent to
bounding its bilinear evaluation by the product of the direction norms. This
direction is the one used by the literal gates below. -/
private theorem hessianPolynomialBound_of_bilinearBound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E} {g : E → ℝ}
    (h : ∃ k : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ X ∈ S, ∀ H K : E,
      ‖fderiv ℝ (fderiv ℝ g) X H K‖ ≤ M * (1 + ‖X‖) ^ k * ‖H‖ * ‖K‖) :
    PolynomialBoundOn S (fderiv ℝ (fderiv ℝ g)) := by
  obtain ⟨k, M, hM, hb⟩ := h
  refine ⟨k, M, hM, ?_⟩
  intro X hX
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hM (by positivity))
  intro H
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (mul_nonneg hM (by positivity)) (norm_nonneg H))
  intro K
  exact hb X hX H K


/-- The explicit Hessian bound in the gates is exactly polynomial growth in
operator norm; the two formulations impose the same hypothesis. -/
theorem hessian_polynomial_bound_iff_bilinear_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E} {g : E → ℝ} :
    PolynomialBoundOn S (fderiv ℝ (fderiv ℝ g)) ↔
      ∃ k : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ X ∈ S, ∀ H K : E,
        ‖fderiv ℝ (fderiv ℝ g) X H K‖ ≤ M * (1 + ‖X‖) ^ k * ‖H‖ * ‖K‖ := by
  constructor
  · rintro ⟨k, M, hM, hb⟩
    refine ⟨k, M, hM, ?_⟩
    intro X hX H K
    calc
      ‖fderiv ℝ (fderiv ℝ g) X H K‖ ≤
          ‖fderiv ℝ (fderiv ℝ g) X H‖ * ‖K‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖fderiv ℝ (fderiv ℝ g) X‖ * ‖H‖) * ‖K‖ :=
        mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg K)
      _ ≤ M * (1 + ‖X‖) ^ k * ‖H‖ * ‖K‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hb X hX) (norm_nonneg H)) (norm_nonneg K)
  · exact hessianPolynomialBound_of_bilinearBound

/-- The integer assertion of Lemma 3.1, including singular covariance and
all positive integer shapes, under the printed local C² assumptions. -/
theorem lemma_3_1_integer_literal {p : ℕ} (N : ℕ) (hN : 1 ≤ N)
    {C : Matrix (Fin p) (Fin p) ℝ} (hC : C.PosSemidef)
    (g : SymmetricMatrix p → ℝ) (U : Set (SymmetricMatrix p))
    (hU : IsOpen U)
    (hcone : ∀ X : SymmetricMatrix p, (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef → X ∈ U)
    (hC2 : ContDiffOn ℝ 2 g U)
    (h0 : ∃ k : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ X : SymmetricMatrix p,
      (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef → ‖g X‖ ≤ M * (1 + ‖X‖) ^ k)
    (h1 : ∃ k : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ X : SymmetricMatrix p,
      (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef → ‖fderiv ℝ g X‖ ≤ M * (1 + ‖X‖) ^ k)
    (h2 : ∃ k : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ X : SymmetricMatrix p,
      (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef → ∀ H K : SymmetricMatrix p,
        ‖fderiv ℝ (fderiv ℝ g) X H K‖ ≤ M * (1 + ‖X‖) ^ k * ‖H‖ * ‖K‖)
    (v : EuclideanSpace ℝ (Fin p)) :
    let μ := (wishartGramMeasure (N - 1) C).prod
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) C)
    let F := fun t : ℝ => ∫ Y : RadialInputSpace p, g (radialInput v (Real.sqrt t) Y) ∂μ
    let G := fun t : ℝ => ∫ Y : RadialInputSpace p,
      symmetricRadialGenerator (N : ℝ) v g (radialInput v (Real.sqrt t) Y) ∂μ
    IsProbabilityMeasure μ ∧
    (∀ s : ℝ, Integrable (fun Y : RadialInputSpace p => g (radialInput v s Y)) μ ∧
      Integrable (fun Y : RadialInputSpace p =>
        symmetricRadialGenerator (N : ℝ) v g (radialInput v s Y)) μ) ∧
    (∃ d : ℝ, HasDerivWithinAt F d (Ici 0) 0 ∧
      Tendsto (deriv F) (𝓝[>] (0 : ℝ)) (𝓝 d)) ∧
    (∀ t : ℝ, 0 < t → DifferentiableAt ℝ F t ∧ DifferentiableAt ℝ (deriv F) t ∧
      4 * t * deriv (deriv F) t + 2 * (N : ℝ) * deriv F t = G t) ∧
    ((∀ t : ℝ, 0 < t → 0 ≤ G t) → MonotoneOn F (Ici 0)) := by
  have hg : C2PolynomialNear (psdCone p) g :=
    ⟨⟨U, hU, hcone, hC2⟩, h0, h1, hessianPolynomialBound_of_bilinearBound h2⟩
  obtain ⟨h, hint⟩ := lemma_3_1_integer N hN hC hg v
  refine ⟨inferInstance, hint, h.origin, ?_, h.monotone⟩
  intro t ht
  exact ⟨h.differentiable t ht, h.twice_differentiable t ht, h.ode t ht⟩

/-- The real-shape assertion of Lemma 3.1 with the stated rank condition.
The range law is displayed as a pushforward from its exact rank dimension;
the factor's covariance and full column rank are also checked conclusions. -/
theorem lemma_3_1_real_literal {p : ℕ}
    {C : Matrix (Fin p) (Fin p) ℝ} (hC : C.PosSemidef)
    (_hrank : 1 ≤ C.rank) {N : ℝ} (hN : (C.rank : ℝ) < N)
    (g : SymmetricMatrix p → ℝ) (U : Set (SymmetricMatrix p))
    (hU : IsOpen U)
    (hcone : ∀ X : SymmetricMatrix p, (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef → X ∈ U)
    (hC2 : ContDiffOn ℝ 2 g U)
    (h0 : ∃ k : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ X : SymmetricMatrix p,
      (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef → ‖g X‖ ≤ M * (1 + ‖X‖) ^ k)
    (h1 : ∃ k : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ X : SymmetricMatrix p,
      (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef → ‖fderiv ℝ g X‖ ≤ M * (1 + ‖X‖) ^ k)
    (h2 : ∃ k : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ X : SymmetricMatrix p,
      (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef → ∀ H K : SymmetricMatrix p,
        ‖fderiv ℝ (fderiv ℝ g) X H K‖ ≤ M * (1 + ‖X‖) ^ k * ‖H‖ * ‖K‖)
    (v : EuclideanSpace ℝ (Fin p)) :
    let L : Matrix (Fin p) (Fin C.rank) ℝ := reducedCovarianceFactor hC
    let μ := ((nonsingularWishartMeasure (N - 1)
      (1 : Matrix (Fin C.rank) (Fin C.rank) ℝ)).map
        (Matrix.symmetricCongruenceLinearMap L)).prod
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) C)
    let F := fun t : ℝ => ∫ Y : RadialInputSpace p, g (radialInput v (Real.sqrt t) Y) ∂μ
    let G := fun t : ℝ => ∫ Y : RadialInputSpace p,
      symmetricRadialGenerator N v g (radialInput v (Real.sqrt t) Y) ∂μ
    L * Lᵀ = C ∧ Function.Injective L.mulVec ∧ IsProbabilityMeasure μ ∧
    (∀ s : ℝ, Integrable (fun Y : RadialInputSpace p => g (radialInput v s Y)) μ ∧
      Integrable (fun Y : RadialInputSpace p =>
        symmetricRadialGenerator N v g (radialInput v s Y)) μ) ∧
    (∃ d : ℝ, HasDerivWithinAt F d (Ici 0) 0 ∧
      Tendsto (deriv F) (𝓝[>] (0 : ℝ)) (𝓝 d)) ∧
    (∀ t : ℝ, 0 < t → DifferentiableAt ℝ F t ∧ DifferentiableAt ℝ (deriv F) t ∧
      4 * t * deriv (deriv F) t + 2 * N * deriv F t = G t) ∧
    ((∀ t : ℝ, 0 < t → 0 ≤ G t) → MonotoneOn F (Ici 0)) := by
  have hg : C2PolynomialNear (psdCone p) g :=
    ⟨⟨U, hU, hcone, hC2⟩, h0, h1, hessianPolynomialBound_of_bilinearBound h2⟩
  obtain ⟨h, hint⟩ := lemma_3_1_real hC hN hg v
  letI := isProbabilityMeasure_covarianceRangeWishartMeasure hC
    (ν := N - 1) (by linarith)
  have hprob : IsProbabilityMeasure
      ((covarianceRangeWishartMeasure (N - 1) hC).prod
        (multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) C)) := inferInstance
  refine ⟨reducedCovarianceFactor_covariance hC, reducedCovarianceFactor_injective hC,
    hprob, hint, h.origin, ?_, h.monotone⟩
  intro t ht
  exact ⟨h.differentiable t ht, h.twice_differentiable t ht, h.ode t ht⟩

end WishartAudit
