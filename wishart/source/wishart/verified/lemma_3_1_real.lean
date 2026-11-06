module

public import wishart.verified.lemma_3_1_integer
public import wishart.verified.real_radial_c2
public import wishart.verified.finite_order_covariance

/-!
# Lemma 3.1 at every admissible real shape

The range-Wishart law is the literal pushforward of a standard Wishart
matrix by a rectangular covariance factor. A reduced factor uses exactly
`rank C` columns, so the admissible shape condition is exactly `N > rank C`.
The independent ambient Gaussian has covariance `C`; the mean direction is
unrestricted. The test is C² only near the positive semidefinite cone.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti.Probability Matrix Filter Set
open WishartVerification
open scoped Topology RealInnerProductSpace Matrix.Norms.L2Operator

namespace Wishart.FiniteOrder

/-- The actual independent range-Wishart/Gaussian law satisfies the radial
mean conclusions for a globally C² representative. -/
theorem radialRange_conclusion_c2 {p r : ℕ} {N : ℝ} (hN : (r : ℝ) < N)
    (L : Matrix (Fin p) (Fin r) ℝ) {f : SymmetricMatrix p → ℝ}
    (hf : C2PolynomialOn (psdCone p) f) (v : EuclideanSpace ℝ (Fin p)) :
    RadialMeanConclusion N
      (fun t => ∫ Y : RadialInputSpace p, f (radialInput v (Real.sqrt t) Y)
        ∂(rangeWishartMeasure (N - 1) L).prod (multivariateGaussian 0 (L * Lᵀ)))
      (fun t => ∫ Y : RadialInputSpace p,
        symmetricRadialGenerator N v f (radialInput v (Real.sqrt t) Y)
        ∂(rangeWishartMeasure (N - 1) L).prod (multivariateGaussian 0 (L * Lᵀ))) := by
  have h := radialMeanConclusion_of_signedRadius ((Nat.cast_nonneg r).trans_lt hN)
    (hasDerivAt_linearRadiusExpectation_c2 hN L v hf)
    (hasDerivAt_linearRadiusFirstExpectation_c2 hN L v hf)
    (linearRadiusExpectation_even_c2 hN L v hf)
    (fun t ht => linearRadialProfile_ode_c2 hN L v hf ht)
  apply h.congr
  · exact funext fun t => linearRadiusExpectation_eq_actual N L v hf.regular.continuous (Real.sqrt t)
  · exact funext fun t => linearRadiusExpectation_eq_actual N L v
      (continuous_symmetricRadialGenerator_c2 hf.regular N v) (Real.sqrt t)

/-- Absolute integrability of the test and its generator under the actual
range-Wishart/Gaussian product law. -/
theorem integrable_radialRange_test_and_generator_c2 {p r : ℕ}
    {N : ℝ} (hN : (r : ℝ) < N) (L : Matrix (Fin p) (Fin r) ℝ)
    {f : SymmetricMatrix p → ℝ} (hf : C2PolynomialOn (psdCone p) f)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) :
    Integrable (fun Y : RadialInputSpace p => f (radialInput v s Y))
        ((rangeWishartMeasure (N - 1) L).prod (multivariateGaussian 0 (L * Lᵀ))) ∧
      Integrable (fun Y : RadialInputSpace p =>
        symmetricRadialGenerator N v f (radialInput v s Y))
        ((rangeWishartMeasure (N - 1) L).prod (multivariateGaussian 0 (L * Lᵀ))) := by
  letI := isProbabilityMeasure_rangeWishartMeasure (ν := N - 1) (by linarith) L
  have hμ := allFiniteNormMoments_prod (allFiniteMoments_rangeWishart_norm (N - 1) L)
    (allFiniteMoments_gaussian_norm
      (μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) (L * Lᵀ)))
  have hS : ∀ᵐ Y ∂(rangeWishartMeasure (N - 1) L).prod (multivariateGaussian
      (0 : EuclideanSpace ℝ (Fin p)) (L * Lᵀ)), Y ∈ radialSupport p :=
    Measure.quasiMeasurePreserving_fst.ae (ae_rangeWishart_psd (N - 1) L)
  have hV := hasTemperateGrowth_radialInput_slice v s
  refine ⟨?_, ?_⟩
  · exact (hf.value.comp (PolynomialBoundOn.of_temperate hV) (radialInput_mapsTo v s)).integrable
      hμ (hf.regular.continuous.comp hV.1.continuous).aestronglyMeasurable hS
  · exact ((polynomial_symmetricRadialGenerator_c2 hf N v).comp
      (PolynomialBoundOn.of_temperate hV) (radialInput_mapsTo v s)).integrable hμ
      ((continuous_symmetricRadialGenerator_c2 hf.regular N v).comp
        hV.1.continuous).aestronglyMeasurable hS

/-- The exact local hypotheses apply for every rectangular range realization,
without requiring the shift to belong to the covariance range. -/
theorem radialRange_conclusion_near_c2 {p r : ℕ} {N : ℝ} (hN : (r : ℝ) < N)
    (L : Matrix (Fin p) (Fin r) ℝ) {f : SymmetricMatrix p → ℝ}
    (hf : C2PolynomialNear (psdCone p) f) (v : EuclideanSpace ℝ (Fin p)) :
    RadialMeanConclusion N
      (fun t => ∫ Y : RadialInputSpace p, f (radialInput v (Real.sqrt t) Y)
        ∂(rangeWishartMeasure (N - 1) L).prod (multivariateGaussian 0 (L * Lᵀ)))
      (fun t => ∫ Y : RadialInputSpace p,
        symmetricRadialGenerator N v f (radialInput v (Real.sqrt t) Y)
        ∂(rangeWishartMeasure (N - 1) L).prod (multivariateGaussian 0 (L * Lᵀ))) ∧
    ∀ s : ℝ,
      Integrable (fun Y : RadialInputSpace p => f (radialInput v s Y))
        ((rangeWishartMeasure (N - 1) L).prod (multivariateGaussian 0 (L * Lᵀ))) ∧
      Integrable (fun Y : RadialInputSpace p =>
        symmetricRadialGenerator N v f (radialInput v s Y))
        ((rangeWishartMeasure (N - 1) L).prod (multivariateGaussian 0 (L * Lᵀ))) := by
  obtain ⟨g, hg, heq⟩ := exists_c2PolynomialOn_extension_psd hf
  have hS : ∀ᵐ Y ∂(rangeWishartMeasure (N - 1) L).prod (multivariateGaussian
      (0 : EuclideanSpace ℝ (Fin p)) (L * Lᵀ)), Y ∈ radialSupport p :=
    Measure.quasiMeasurePreserving_fst.ae (ae_rangeWishart_psd (N - 1) L)
  have hval (s : ℝ) : (fun Y : RadialInputSpace p => g (radialInput v s Y)) =ᵐ[
      (rangeWishartMeasure (N - 1) L).prod (multivariateGaussian 0 (L * Lᵀ))]
      (fun Y => f (radialInput v s Y)) := by
    filter_upwards [hS] with Y hY
    exact (heq _ (radialInput_mapsTo v s hY)).1
  have hgen (s : ℝ) : (fun Y : RadialInputSpace p =>
      symmetricRadialGenerator N v g (radialInput v s Y)) =ᵐ[
      (rangeWishartMeasure (N - 1) L).prod (multivariateGaussian 0 (L * Lᵀ))]
      (fun Y => symmetricRadialGenerator N v f (radialInput v s Y)) := by
    filter_upwards [hS] with Y hY
    exact symmetricRadialGenerator_congr_jet
      (heq _ (radialInput_mapsTo v s hY)).2.1 (heq _ (radialInput_mapsTo v s hY)).2.2 _ _
  refine ⟨(radialRange_conclusion_c2 hN L hg v).congr
    (funext fun t => integral_congr_ae (hval (Real.sqrt t)))
    (funext fun t => integral_congr_ae (hgen (Real.sqrt t))), ?_⟩
  intro s
  have hi := integrable_radialRange_test_and_generator_c2 hN L hg v s
  exact ⟨hi.1.congr (hval s), hi.2.congr (hgen s)⟩

/-- A fixed full-column-rank factor with exactly the covariance rank many
columns. The choice is used only to specify the literal range law. -/
def reducedCovarianceFactor {p : ℕ} {C : Matrix (Fin p) (Fin p) ℝ}
    (hC : C.PosSemidef) : Matrix (Fin p) (Fin C.rank) ℝ :=
  Classical.choose (exists_reduced_covariance_factor hC)

theorem reducedCovarianceFactor_covariance {p : ℕ} {C : Matrix (Fin p) (Fin p) ℝ}
    (hC : C.PosSemidef) : reducedCovarianceFactor hC * (reducedCovarianceFactor hC)ᵀ = C :=
  (Classical.choose_spec (exists_reduced_covariance_factor hC)).1

theorem reducedCovarianceFactor_injective {p : ℕ} {C : Matrix (Fin p) (Fin p) ℝ}
    (hC : C.PosSemidef) : Function.Injective (reducedCovarianceFactor hC).mulVec :=
  (Classical.choose_spec (exists_reduced_covariance_factor hC)).2

/-- Shape-ν Wishart measure with covariance C on its range: push forward the
standard rank(C)-dimensional Wishart matrix by a reduced covariance factor. -/
def covarianceRangeWishartMeasure {p : ℕ} (ν : ℝ)
    {C : Matrix (Fin p) (Fin p) ℝ} (hC : C.PosSemidef) : Measure (SymmetricMatrix p) :=
  rangeWishartMeasure ν (reducedCovarianceFactor hC)

theorem isProbabilityMeasure_covarianceRangeWishartMeasure {p : ℕ}
    {C : Matrix (Fin p) (Fin p) ℝ} (hC : C.PosSemidef) {ν : ℝ}
    (hν : (C.rank : ℝ) - 1 < ν) :
    IsProbabilityMeasure (covarianceRangeWishartMeasure ν hC) :=
  isProbabilityMeasure_rangeWishartMeasure hν (reducedCovarianceFactor hC)

/-- **Lemma 3.1, real shape.** The covariance is any positive semidefinite
matrix, the admissible shape is exactly N > rank(C), and the mean direction
is arbitrary. The rank-zero case is valid as well as the printed rank ≥ 1
case. The actual independent range-Wishart and Gaussian laws are explicit. -/
theorem lemma_3_1_real {p : ℕ} {C : Matrix (Fin p) (Fin p) ℝ}
    (hC : C.PosSemidef) {N : ℝ} (hN : (C.rank : ℝ) < N)
    {g : SymmetricMatrix p → ℝ} (hg : C2PolynomialNear (psdCone p) g)
    (v : EuclideanSpace ℝ (Fin p)) :
    RadialMeanConclusion N
      (fun t => ∫ Y : RadialInputSpace p, g (radialInput v (Real.sqrt t) Y)
        ∂(covarianceRangeWishartMeasure (N - 1) hC).prod (multivariateGaussian 0 C))
      (fun t => ∫ Y : RadialInputSpace p,
        symmetricRadialGenerator N v g (radialInput v (Real.sqrt t) Y)
        ∂(covarianceRangeWishartMeasure (N - 1) hC).prod (multivariateGaussian 0 C)) ∧
    ∀ s : ℝ,
      Integrable (fun Y : RadialInputSpace p => g (radialInput v s Y))
        ((covarianceRangeWishartMeasure (N - 1) hC).prod (multivariateGaussian 0 C)) ∧
      Integrable (fun Y : RadialInputSpace p =>
        symmetricRadialGenerator N v g (radialInput v s Y))
        ((covarianceRangeWishartMeasure (N - 1) hC).prod (multivariateGaussian 0 C)) := by
  simpa only [reducedCovarianceFactor_covariance, covarianceRangeWishartMeasure] using
    radialRange_conclusion_near_c2 hN (reducedCovarianceFactor hC) hg v

end Wishart.FiniteOrder
