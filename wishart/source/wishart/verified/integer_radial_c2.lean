module

public import wishart.verified.radial_mean_c2
public import wishart.verified.finite_order_congruence

/-!
# The C² radial identity at every positive semidefinite covariance

A fixed standard Gaussian source in twice the ambient dimension realizes all
covariances `C + δ² I`. Its transport preserves positive semidefinite support
and is polynomial in the parameter. Continuous test integrands with polynomial
bounds on that support therefore have continuous expectations, even at zero.
Passing the already proved identity to this limit covers singular covariance
and noncentral directions outside its range, without higher derivatives.
-/

@[expose] public section

noncomputable section

open Matrix MeasureTheory ProbabilityTheory TauCeti.Probability Filter Set
open WishartVerification
open scoped Topology RealInnerProductSpace Matrix.Norms.Operator

namespace Wishart.FiniteOrder

variable {p : ℕ}

/-- Polynomial bounds on the actual positive semidefinite support imply
integrability under every Gaussian Gram/Gaussian product law. -/
theorem integrable_radialGram_polynomialOn (n : ℕ) (C : Matrix (Fin p) (Fin p) ℝ)
    {H : RadialInputSpace p → ℝ} (hH : Continuous H)
    (hp : PolynomialBoundOn (radialSupport p) H) :
    Integrable H ((wishartGramMeasure n C).prod (multivariateGaussian 0 C)) := by
  exact hp.integrable
    (allFiniteNormMoments_prod (allFiniteMoments_gram_norm n C) allFiniteMoments_gaussian_norm)
    hH.aestronglyMeasurable
    (Measure.quasiMeasurePreserving_fst.ae (ae_posSemidef_wishartGramMeasure n C))

/-- Covariance regularization is continuous for every continuous integrand
with a polynomial bound on the supported matrix/vector pairs. -/
theorem continuous_radialGram_covarianceRegularization_polynomialOn
    {C : Matrix (Fin p) (Fin p) ℝ} (hC : C.PosSemidef) (n : ℕ)
    {H : RadialInputSpace p → ℝ} (hH : Continuous H)
    (hp : PolynomialBoundOn (radialSupport p) H) :
    Continuous (fun δ : ℝ => ∫ Y : RadialInputSpace p, H Y
      ∂(wishartGramMeasure n (C + δ ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ))).prod
        (multivariateGaussian 0 (C + δ ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ)))) := by
  let A := covarianceRegularizationBase C
  let B := covarianceRegularizationNoise p
  let μ := (wishartGramMeasure n (1 : Matrix (Fin (p + p)) (Fin (p + p)) ℝ)).prod
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin (p + p))) 1)
  let F : ℝ × RadialInputSpace (p + p) → ℝ := fun z =>
    H (rectangularRadialNoiseTransport A B z.1 z.2)
  have hμ : HasAllFiniteMoments (fun Y : RadialInputSpace (p + p) => ‖Y‖) μ :=
    allFiniteNormMoments_prod (allFiniteMoments_gram_norm n 1) allFiniteMoments_gaussian_norm
  have hsupport : ∀ᵐ Y ∂μ, Y ∈ radialSupport (p + p) :=
    Measure.quasiMeasurePreserving_fst.ae (ae_posSemidef_wishartGramMeasure n 1)
  have hT := hasTemperateGrowth_rectangularRadialNoiseTransport A B
  have hTs : MapsTo (fun z : ℝ × RadialInputSpace (p + p) =>
      rectangularRadialNoiseTransport A B z.1 z.2)
      (univ ×ˢ radialSupport (p + p)) (radialSupport p) := by
    intro z hz
    exact symmetricCongruence_mapsTo_psdCone (A + z.1 • B) hz.2
  have hF : Continuous F := hH.comp hT.1.continuous
  have hFp : PolynomialBoundOn (univ ×ˢ radialSupport (p + p)) F :=
    hp.comp (PolynomialBoundOn.of_temperate hT) hTs
  have heq (δ : ℝ) : (∫ Y, F (δ, Y) ∂μ) =
      ∫ Y : RadialInputSpace p, H Y
        ∂(wishartGramMeasure n (C + δ ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ))).prod
          (multivariateGaussian 0 (C + δ ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ))) := by
    have hmap := map_rectangularRadialNoiseTransport n A B δ
    rw [covarianceRegularization_covariance hC] at hmap
    have hm : Measurable (rectangularRadialNoiseTransport A B δ) :=
      (hT.1.continuous.comp
        (continuous_const.prodMk continuous_id :
          Continuous (fun Y : RadialInputSpace (p + p) => (δ, Y)))).measurable
    have hi := integral_map (μ := μ) hm.aemeasurable hH.aestronglyMeasurable
    rw [hmap] at hi
    exact hi.symm
  exact (continuous_integral_polynomialOn hμ hsupport hF hFp).congr heq

/-- The exact integrated radial generator identity for every natural Gram
degree and every positive semidefinite covariance. The shift is unrestricted. -/
theorem radial_gram_generator_identity_c2_posSemidef
    {C : Matrix (Fin p) (Fin p) ℝ} (hC : C.PosSemidef) (n : ℕ)
    {f : SymmetricMatrix p → ℝ} (hf : C2PolynomialOn (psdCone p) f)
    (v : EuclideanSpace ℝ (Fin p)) (r : ℝ) :
    r * (∫ Y : RadialInputSpace p,
      symmetricRadialGenerator ((n : ℝ) + 1) v f (radialInput v r Y)
      ∂(wishartGramMeasure n C).prod (multivariateGaussian 0 C)) =
    r * (∫ Y : RadialInputSpace p, radialSecondIntegrand f v r Y
      ∂(wishartGramMeasure n C).prod (multivariateGaussian 0 C)) +
    (n : ℝ) * (∫ Y : RadialInputSpace p, radialFirstIntegrand f v r Y
      ∂(wishartGramMeasure n C).prod (multivariateGaussian 0 C)) := by
  have hpair : PolynomialBoundOn (radialSupport p)
      (fun Y : RadialInputSpace p => (r, Y)) :=
    PolynomialBoundOn.of_temperate
      (hasTemperateGrowth_prodMk (Function.HasTemperateGrowth.const r) Function.HasTemperateGrowth.id)
  have hpairs : MapsTo (fun Y : RadialInputSpace p => (r, Y))
      (radialSupport p) (univ ×ˢ radialSupport p) := fun _ hY => ⟨mem_univ _, hY⟩
  have hV := hasTemperateGrowth_radialInput_slice v r
  have hgen := continuous_radialGram_covarianceRegularization_polynomialOn hC n
    ((continuous_symmetricRadialGenerator_c2 hf.regular ((n : ℝ) + 1) v).comp hV.1.continuous)
    ((polynomial_symmetricRadialGenerator_c2 hf ((n : ℝ) + 1) v).comp
      (PolynomialBoundOn.of_temperate hV) (radialInput_mapsTo v r))
  have hsecond := continuous_radialGram_covarianceRegularization_polynomialOn hC n
    ((continuous_radialSecondIntegrand_c2 hf.regular v).comp
      (continuous_const.prodMk continuous_id))
    ((polynomial_radialSecondIntegrand_c2 hf v).comp hpair hpairs)
  have hfirst := continuous_radialGram_covarianceRegularization_polynomialOn hC n
    ((c1_radialFirstIntegrand hf v).regular.continuous.comp
      (continuous_const.prodMk continuous_id))
    ((c1_radialFirstIntegrand hf v).value.comp hpair hpairs)
  let δ (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)
  have hδ : ∀ k, 0 < δ k := fun k => by dsimp [δ]; positivity
  have hlim : Tendsto δ atTop (𝓝 (0 : ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hgenlim := hgen.continuousAt.tendsto.comp hlim
  have hsecondlim := hsecond.continuousAt.tendsto.comp hlim
  have hfirstlim := hfirst.continuousAt.tendsto.comp hlim
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_smul, add_zero] at hgenlim hsecondlim hfirstlim
  have heq (k : ℕ) :
      r * (∫ Y : RadialInputSpace p,
        symmetricRadialGenerator ((n : ℝ) + 1) v f (radialInput v r Y)
        ∂(wishartGramMeasure n (C + δ k ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ))).prod
          (multivariateGaussian 0 (C + δ k ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ)))) =
      r * (∫ Y : RadialInputSpace p, radialSecondIntegrand f v r Y
        ∂(wishartGramMeasure n (C + δ k ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ))).prod
          (multivariateGaussian 0 (C + δ k ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ)))) +
      (n : ℝ) * (∫ Y : RadialInputSpace p, radialFirstIntegrand f v r Y
        ∂(wishartGramMeasure n (C + δ k ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ))).prod
          (multivariateGaussian 0 (C + δ k ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ)))) := by
    have hpos := covarianceRegularization_posDef hC (hδ k)
    exact radial_generator_identity_of_stein_c2 hpos (allFiniteMoments_gram_norm n _)
      (ae_posSemidef_wishartGramMeasure n _) (coneSteinIdentity_gram hpos n) hf v r
  exact tendsto_nhds_unique (hgenlim.const_mul r)
    (((hsecondlim.const_mul r).add (hfirstlim.const_mul (n : ℝ))).congr'
      (Eventually.of_forall fun k => (heq k).symm))

end Wishart.FiniteOrder

end
