module

public import wishart.verified.radial_conclusion
public import wishart.verified.integer_radial_c2

/-!
# Lemma 3.1 at every positive integer shape

The covariance may be any positive semidefinite matrix, including zero, and
the shift may lie outside its range. The test is assumed C² only on an open
neighborhood of the cone; only its value and first two derivatives have
polynomial bounds there. The measure is the actual independent Gaussian
Gram/Gaussian product law.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti.Probability Matrix Filter Set
open WishartVerification
open scoped Topology RealInnerProductSpace Matrix.Norms.L2Operator

namespace Wishart.FiniteOrder

theorem symmetricRadialGenerator_congr_jet {p : ℕ} {f g : SymmetricMatrix p → ℝ}
    {X : SymmetricMatrix p}
    (hD : fderiv ℝ f X = fderiv ℝ g X)
    (hD₂ : fderiv ℝ (fderiv ℝ f) X = fderiv ℝ (fderiv ℝ g) X)
    (N : ℝ) (v : EuclideanSpace ℝ (Fin p)) :
    symmetricRadialGenerator N v f X = symmetricRadialGenerator N v g X := by
  simp only [symmetricRadialGenerator, radialCovarianceContraction,
    symmetricSecondDerivative, hD, hD₂]

/-- First prove the conclusion for a global C² representative, retaining
polynomial bounds only on the positive semidefinite support. -/
theorem radialGram_conclusion_c2 {p : ℕ} {C : Matrix (Fin p) (Fin p) ℝ}
    (hC : C.PosSemidef) (n : ℕ) {f : SymmetricMatrix p → ℝ}
    (hf : C2PolynomialOn (psdCone p) f) (v : EuclideanSpace ℝ (Fin p)) :
    RadialMeanConclusion ((n : ℝ) + 1)
      (fun t => ∫ Y : RadialInputSpace p, f (radialInput v (Real.sqrt t) Y)
        ∂(wishartGramMeasure n C).prod (multivariateGaussian 0 C))
      (fun t => ∫ Y : RadialInputSpace p,
        symmetricRadialGenerator ((n : ℝ) + 1) v f (radialInput v (Real.sqrt t) Y)
        ∂(wishartGramMeasure n C).prod (multivariateGaussian 0 C)) := by
  have hμ := allFiniteNormMoments_prod (allFiniteMoments_gram_norm n C)
    (allFiniteMoments_gaussian_norm (μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) C))
  have hS : ∀ᵐ Y ∂(wishartGramMeasure n C).prod (multivariateGaussian
      (0 : EuclideanSpace ℝ (Fin p)) C), Y ∈ radialSupport p :=
    Measure.quasiMeasurePreserving_fst.ae (ae_posSemidef_wishartGramMeasure n C)
  apply radialMeanConclusion_of_signedRadius (by positivity : 0 < (n : ℝ) + 1)
    (hasDerivAt_radialExpectation_c2 hμ hS hf v)
    (hasDerivAt_radialFirstExpectation_c2 hμ hS hf v)
    (radialExpectation_even_c2 hC (allFiniteMoments_gram_norm n C)
      (ae_posSemidef_wishartGramMeasure n C) hf v)
  intro t ht
  apply sqrt_radial_ode_of_signed_identity ht rfl
  simpa only [add_sub_cancel_right] using
    radial_gram_generator_identity_c2_posSemidef hC n hf v (Real.sqrt t)

/-- Every function and operator expectation in the integer radial lemma is
absolutely integrable; the value of the Bochner integral is never supplied
by its default value on nonintegrable functions. -/
theorem integrable_radialGram_test_and_generator_c2 {p : ℕ}
    (n : ℕ) (C : Matrix (Fin p) (Fin p) ℝ)
    {f : SymmetricMatrix p → ℝ} (hf : C2PolynomialOn (psdCone p) f)
    (N : ℝ) (v : EuclideanSpace ℝ (Fin p)) (r : ℝ) :
    Integrable (fun Y : RadialInputSpace p => f (radialInput v r Y))
        ((wishartGramMeasure n C).prod (multivariateGaussian 0 C)) ∧
      Integrable (fun Y : RadialInputSpace p =>
        symmetricRadialGenerator N v f (radialInput v r Y))
        ((wishartGramMeasure n C).prod (multivariateGaussian 0 C)) := by
  have hV := hasTemperateGrowth_radialInput_slice v r
  refine ⟨?_, ?_⟩
  · exact integrable_radialGram_polynomialOn n C (hf.regular.continuous.comp hV.1.continuous)
      (hf.value.comp (PolynomialBoundOn.of_temperate hV) (radialInput_mapsTo v r))
  · exact integrable_radialGram_polynomialOn n C
      ((continuous_symmetricRadialGenerator_c2 hf.regular N v).comp hV.1.continuous)
      ((polynomial_symmetricRadialGenerator_c2 hf N v).comp
        (PolynomialBoundOn.of_temperate hV) (radialInput_mapsTo v r))

/-- The exact near-cone hypothesis in Lemma 3.1, for a background Gram
matrix with `n` Gaussian rows and a further independent shifted row. -/
theorem radialGram_conclusion_near_c2 {p : ℕ} {C : Matrix (Fin p) (Fin p) ℝ}
    (hC : C.PosSemidef) (n : ℕ) {f : SymmetricMatrix p → ℝ}
    (hf : C2PolynomialNear (psdCone p) f) (v : EuclideanSpace ℝ (Fin p)) :
    RadialMeanConclusion ((n : ℝ) + 1)
      (fun t => ∫ Y : RadialInputSpace p, f (radialInput v (Real.sqrt t) Y)
        ∂(wishartGramMeasure n C).prod (multivariateGaussian 0 C))
      (fun t => ∫ Y : RadialInputSpace p,
        symmetricRadialGenerator ((n : ℝ) + 1) v f (radialInput v (Real.sqrt t) Y)
        ∂(wishartGramMeasure n C).prod (multivariateGaussian 0 C)) ∧
    ∀ r : ℝ,
      Integrable (fun Y : RadialInputSpace p => f (radialInput v r Y))
        ((wishartGramMeasure n C).prod (multivariateGaussian 0 C)) ∧
      Integrable (fun Y : RadialInputSpace p =>
        symmetricRadialGenerator ((n : ℝ) + 1) v f (radialInput v r Y))
        ((wishartGramMeasure n C).prod (multivariateGaussian 0 C)) := by
  obtain ⟨g, hg, heq⟩ := exists_c2PolynomialOn_extension_psd hf
  have hS : ∀ᵐ Y ∂(wishartGramMeasure n C).prod (multivariateGaussian
      (0 : EuclideanSpace ℝ (Fin p)) C), Y ∈ radialSupport p :=
    Measure.quasiMeasurePreserving_fst.ae (ae_posSemidef_wishartGramMeasure n C)
  have hval (r : ℝ) : (fun Y : RadialInputSpace p => g (radialInput v r Y)) =ᵐ[
      (wishartGramMeasure n C).prod (multivariateGaussian 0 C)]
      (fun Y => f (radialInput v r Y)) := by
    filter_upwards [hS] with Y hY
    exact (heq _ (radialInput_mapsTo v r hY)).1
  have hgen (r : ℝ) : (fun Y : RadialInputSpace p =>
      symmetricRadialGenerator ((n : ℝ) + 1) v g (radialInput v r Y)) =ᵐ[
      (wishartGramMeasure n C).prod (multivariateGaussian 0 C)]
      (fun Y => symmetricRadialGenerator ((n : ℝ) + 1) v f (radialInput v r Y)) := by
    filter_upwards [hS] with Y hY
    exact symmetricRadialGenerator_congr_jet
      (heq _ (radialInput_mapsTo v r hY)).2.1 (heq _ (radialInput_mapsTo v r hY)).2.2 _ _
  refine ⟨(radialGram_conclusion_c2 hC n hg v).congr
    (funext fun t => integral_congr_ae (hval (Real.sqrt t)))
    (funext fun t => integral_congr_ae (hgen (Real.sqrt t))), ?_⟩
  intro r
  have hi := integrable_radialGram_test_and_generator_c2 n C hg ((n : ℝ) + 1) v r
  exact ⟨hi.1.congr (hval r), hi.2.congr (hgen r)⟩

/-- **Lemma 3.1, integer shape.** Every positive integer shape is allowed,
with arbitrary positive semidefinite covariance and arbitrary mean direction.
`C2PolynomialNear` is exactly C² near the cone and polynomial growth of
only the value, first derivative, and second derivative on the cone. -/
theorem lemma_3_1_integer {p : ℕ} (N : ℕ) (hN : 1 ≤ N)
    {C : Matrix (Fin p) (Fin p) ℝ} (hC : C.PosSemidef)
    {g : SymmetricMatrix p → ℝ} (hg : C2PolynomialNear (psdCone p) g)
    (v : EuclideanSpace ℝ (Fin p)) :
    RadialMeanConclusion (N : ℝ)
      (fun t => ∫ Y : RadialInputSpace p, g (radialInput v (Real.sqrt t) Y)
        ∂(wishartGramMeasure (N - 1) C).prod (multivariateGaussian 0 C))
      (fun t => ∫ Y : RadialInputSpace p,
        symmetricRadialGenerator (N : ℝ) v g (radialInput v (Real.sqrt t) Y)
        ∂(wishartGramMeasure (N - 1) C).prod (multivariateGaussian 0 C)) ∧
    ∀ r : ℝ,
      Integrable (fun Y : RadialInputSpace p => g (radialInput v r Y))
        ((wishartGramMeasure (N - 1) C).prod (multivariateGaussian 0 C)) ∧
      Integrable (fun Y : RadialInputSpace p =>
        symmetricRadialGenerator (N : ℝ) v g (radialInput v r Y))
        ((wishartGramMeasure (N - 1) C).prod (multivariateGaussian 0 C)) := by
  have hcast : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hN
  simpa only [hcast] using radialGram_conclusion_near_c2 hC (N - 1) hg v

end Wishart.FiniteOrder
