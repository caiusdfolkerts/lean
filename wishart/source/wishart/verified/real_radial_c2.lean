module

public import wishart.verified.scalar_radial_c2
public import wishart.verified.finite_order_congruence
public import wishart.verified.radial_expectation_c2

@[expose] public section

/-!
# Real-shape C² radial identities under rectangular covariance transport

A rectangular lift has first column the arbitrary mean direction and remaining
columns a covariance factor.  Its congruence sends the transverse scalar
regression source to the actual ambient matrix.  No condition that the mean
belong to the covariance range is needed.
-/

noncomputable section

open Matrix MeasureTheory ProbabilityTheory TauCeti.Probability Filter Set
open WishartVerification
open scoped Topology RealInnerProductSpace BigOperators Matrix.Norms.Operator

namespace Wishart.FiniteOrder

variable {p r : ℕ}

def linearRadiusExpectation (N : ℝ) (L : Matrix (Fin p) (Fin r) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (f : SymmetricMatrix p → ℝ) (s : ℝ) : ℝ :=
  ∫ x, f (linearRadialInput L v s x) ∂scalarRegressionNoiseMeasure N r

def linearRadiusFirstExpectation (N : ℝ) (L : Matrix (Fin p) (Fin r) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (f : SymmetricMatrix p → ℝ) (s : ℝ) : ℝ :=
  scalarRadiusFirstExpectation N
    (fun X => f (Matrix.symmetricCongruenceLinearMap (radialLiftMatrix v L) X)) s

def linearRadiusSecondExpectation (N : ℝ) (L : Matrix (Fin p) (Fin r) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (f : SymmetricMatrix p → ℝ) (s : ℝ) : ℝ :=
  scalarRadiusSecondExpectation N
    (fun X => f (Matrix.symmetricCongruenceLinearMap (radialLiftMatrix v L) X)) s

def linearRadialGeneratorExpectation (N : ℝ) (L : Matrix (Fin p) (Fin r) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (f : SymmetricMatrix p → ℝ) (t : ℝ) : ℝ :=
  ∫ x, symmetricRadialGenerator N v f (linearRadialInput L v (Real.sqrt t) x)
    ∂scalarRegressionNoiseMeasure N r

theorem linearRadiusExpectation_eq_scalar (N : ℝ) (L : Matrix (Fin p) (Fin r) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (f : SymmetricMatrix p → ℝ) :
    linearRadiusExpectation N L v f = scalarRadiusExpectation N
      (fun X => f (Matrix.symmetricCongruenceLinearMap (radialLiftMatrix v L) X)) := by
  funext s
  apply integral_congr_ae
  exact Eventually.of_forall fun x => congrArg f (radialLiftMatrix_scalarRadialMatrix L v s x).symm

theorem hasDerivAt_linearRadiusExpectation_c2 {N : ℝ} (hN : (r : ℝ) < N)
    (L : Matrix (Fin p) (Fin r) ℝ) (v : EuclideanSpace ℝ (Fin p))
    {f : SymmetricMatrix p → ℝ} (hf : C2PolynomialOn (psdCone p) f) (s : ℝ) :
    HasDerivAt (linearRadiusExpectation N L v f) (linearRadiusFirstExpectation N L v f s) s := by
  rw [linearRadiusExpectation_eq_scalar]
  exact hasDerivAt_scalarRadiusExpectation_c2 hN (hf.symmetricCongruence (radialLiftMatrix v L)) s

theorem hasDerivAt_linearRadiusFirstExpectation_c2 {N : ℝ} (hN : (r : ℝ) < N)
    (L : Matrix (Fin p) (Fin r) ℝ) (v : EuclideanSpace ℝ (Fin p))
    {f : SymmetricMatrix p → ℝ} (hf : C2PolynomialOn (psdCone p) f) (s : ℝ) :
    HasDerivAt (linearRadiusFirstExpectation N L v f)
      (linearRadiusSecondExpectation N L v f s) s :=
  hasDerivAt_scalarRadiusFirstExpectation_c2 hN (hf.symmetricCongruence (radialLiftMatrix v L)) s

theorem continuous_linearRadiusSecondExpectation_c2 {N : ℝ} (hN : (r : ℝ) < N)
    (L : Matrix (Fin p) (Fin r) ℝ) (v : EuclideanSpace ℝ (Fin p))
    {f : SymmetricMatrix p → ℝ} (hf : C2PolynomialOn (psdCone p) f) :
    Continuous (linearRadiusSecondExpectation N L v f) :=
  continuous_scalarRadiusSecondExpectation_c2 hN (hf.symmetricCongruence (radialLiftMatrix v L))

theorem linearRadiusExpectation_even_c2 {N : ℝ} (hN : (r : ℝ) < N)
    (L : Matrix (Fin p) (Fin r) ℝ) (v : EuclideanSpace ℝ (Fin p))
    {f : SymmetricMatrix p → ℝ} (hf : C2PolynomialOn (psdCone p) f) (s : ℝ) :
    linearRadiusExpectation N L v f (-s) = linearRadiusExpectation N L v f s := by
  rw [linearRadiusExpectation_eq_scalar]
  exact scalarRadiusExpectation_even_c2 hN
    (hf.symmetricCongruence (radialLiftMatrix v L)).regular s

theorem linearRadialGeneratorExpectation_eq_scalar (N : ℝ)
    (L : Matrix (Fin p) (Fin r) ℝ) (v : EuclideanSpace ℝ (Fin p))
    {f : SymmetricMatrix p → ℝ} (hf : ContDiff ℝ 2 f) (t : ℝ) :
    linearRadialGeneratorExpectation N L v f t = scalarRadialGeneratorExpectation N
      (fun X => f (Matrix.symmetricCongruenceLinearMap (radialLiftMatrix v L) X)) t := by
  symm
  apply integral_congr_ae
  filter_upwards [ae_scalarRadialMatrix_posSemidef N (Real.sqrt t)] with x hx
  rw [symmetricRadialGenerator_congruence_c2 _ _ _ hf _ hx,
    radialLiftMatrix_axis, radialLiftMatrix_scalarRadialMatrix]

theorem continuous_linearRadialGeneratorExpectation_c2 {N : ℝ} (hN : (r : ℝ) < N)
    (L : Matrix (Fin p) (Fin r) ℝ) (v : EuclideanSpace ℝ (Fin p))
    {f : SymmetricMatrix p → ℝ} (hf : C2PolynomialOn (psdCone p) f) :
    Continuous (linearRadialGeneratorExpectation N L v f) := by
  have heq := funext (linearRadialGeneratorExpectation_eq_scalar N L v hf.regular)
  rw [heq]
  exact continuous_scalarRadialGeneratorExpectation_c2 hN
    (hf.symmetricCongruence (radialLiftMatrix v L))

/-- The real-shape radial equation for every rectangular covariance image. -/
theorem linearRadialProfile_ode_c2 {N : ℝ} (hN : (r : ℝ) < N)
    (L : Matrix (Fin p) (Fin r) ℝ) (v : EuclideanSpace ℝ (Fin p))
    {f : SymmetricMatrix p → ℝ} (hf : C2PolynomialOn (psdCone p) f)
    {t : ℝ} (ht : 0 < t) :
    4 * t * ((linearRadiusSecondExpectation N L v f (Real.sqrt t) -
        linearRadiusFirstExpectation N L v f (Real.sqrt t) / Real.sqrt t) / (4 * t)) +
      2 * N * (linearRadiusFirstExpectation N L v f (Real.sqrt t) / (2 * Real.sqrt t)) =
        linearRadialGeneratorExpectation N L v f t := by
  rw [linearRadialGeneratorExpectation_eq_scalar N L v hf.regular]
  exact scalarRadialProfile_ode_c2 hN (hf.symmetricCongruence (radialLiftMatrix v L)) ht

/-- The Wishart law on the image of a covariance factor, represented by its
literal pushforward. A reduced factor has precisely the covariance rank. -/
def rangeWishartMeasure (ν : ℝ) (L : Matrix (Fin p) (Fin r) ℝ) :
    Measure (SymmetricMatrix p) :=
  (nonsingularWishartMeasure ν (1 : Matrix (Fin r) (Fin r) ℝ)).map
    (Matrix.symmetricCongruenceLinearMap L)

instance rangeWishartMeasure_isFinite (ν : ℝ) (L : Matrix (Fin p) (Fin r) ℝ) :
    IsFiniteMeasure (rangeWishartMeasure ν L) := by
  unfold rangeWishartMeasure
  infer_instance

theorem isProbabilityMeasure_rangeWishartMeasure {ν : ℝ} (hν : (r : ℝ) - 1 < ν)
    (L : Matrix (Fin p) (Fin r) ℝ) : IsProbabilityMeasure (rangeWishartMeasure ν L) := by
  letI := isProbabilityMeasure_nonsingularWishartMeasure Matrix.PosDef.one hν
  unfold rangeWishartMeasure
  infer_instance

def linearRadialNoise (L : Matrix (Fin p) (Fin r) ℝ) (x : ScalarRegressionNoise r) :
    RadialInputSpace p :=
  (Matrix.symmetricCongruenceLinearMap L x.2, L.toEuclideanLin x.1)

theorem measurable_linearRadialNoise (L : Matrix (Fin p) (Fin r) ℝ) :
    Measurable (linearRadialNoise L) :=
  (((Matrix.symmetricCongruenceLinearMap L).toContinuousLinearMap.continuous.comp
    continuous_snd).prodMk (L.toEuclideanLin.toContinuousLinearMap.continuous.comp
      continuous_fst)).measurable

theorem map_linearRadialNoise (N : ℝ) (L : Matrix (Fin p) (Fin r) ℝ) :
    (scalarRegressionNoiseMeasure N r).map (linearRadialNoise L) =
      (rangeWishartMeasure (N - 1) L).prod
        (multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) (L * Lᵀ)) := by
  have hG : (multivariateGaussian (0 : EuclideanSpace ℝ (Fin r)) 1).map L.toEuclideanLin =
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) (L * Lᵀ) := by
    simpa only [map_zero, add_zero, Matrix.mul_one] using
      map_affine_multivariateGaussian (0 : EuclideanSpace ℝ (Fin r)) Matrix.PosSemidef.one L 0
  let μG := multivariateGaussian (0 : EuclideanSpace ℝ (Fin r)) (1 : Matrix (Fin r) (Fin r) ℝ)
  let μW := nonsingularWishartMeasure (N - 1) (1 : Matrix (Fin r) (Fin r) ℝ)
  have hL : Measurable (L.toEuclideanLin : EuclideanSpace ℝ (Fin r) → EuclideanSpace ℝ (Fin p)) :=
    L.toEuclideanLin.toContinuousLinearMap.continuous.measurable
  have hΦ : Measurable (Matrix.symmetricCongruenceLinearMap L : SymmetricMatrix r → SymmetricMatrix p) :=
    (Matrix.symmetricCongruenceLinearMap L).toContinuousLinearMap.continuous.measurable
  calc
    _ = ((μG.map L.toEuclideanLin).prod
        (μW.map (Matrix.symmetricCongruenceLinearMap L))).map Prod.swap := by
      rw [Measure.map_prod_map _ _ hL hΦ, Measure.map_map measurable_swap (hL.prodMap hΦ)]
      rfl
    _ = _ := by rw [Measure.prod_swap, hG]; rfl

theorem radialInput_linearRadialNoise (L : Matrix (Fin p) (Fin r) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (s : ℝ) (x : ScalarRegressionNoise r) :
    radialInput v s (linearRadialNoise L x) = linearRadialInput L v s x := rfl

theorem allFiniteMoments_rangeWishart_norm (ν : ℝ) (L : Matrix (Fin p) (Fin r) ℝ) :
    HasAllFiniteMoments (fun W : SymmetricMatrix p => ‖W‖) (rangeWishartMeasure ν L) := by
  let Φ := (Matrix.symmetricCongruenceLinearMap L).toContinuousLinearMap
  have hT : MeasurePreserving Φ (nonsingularWishartMeasure ν (1 : Matrix (Fin r) (Fin r) ℝ))
      (rangeWishartMeasure ν L) := ⟨Φ.continuous.measurable, rfl⟩
  exact HasAllFiniteMoments.of_comp_measurePreserving hT measurable_norm
    (allFiniteMoments_temperate_norm (allFiniteMoments_wishart_norm ν 1) Φ.hasTemperateGrowth)

theorem ae_rangeWishart_psd (ν : ℝ) (L : Matrix (Fin p) (Fin r) ℝ) :
    ∀ᵐ W ∂rangeWishartMeasure ν L, W ∈ psdCone p := by
  have hΦ : Measurable (Matrix.symmetricCongruenceLinearMap L : SymmetricMatrix r → SymmetricMatrix p) :=
    (Matrix.symmetricCongruenceLinearMap L).toContinuousLinearMap.continuous.measurable
  unfold rangeWishartMeasure
  change ∀ᵐ (W : SymmetricMatrix p) ∂(nonsingularWishartMeasure ν (1 : Matrix (Fin r) (Fin r) ℝ)).map
    (Matrix.symmetricCongruenceLinearMap L), (W : Matrix (Fin p) (Fin p) ℝ).PosSemidef
  rw [ae_map_iff hΦ.aemeasurable (isClosed_psdCone p).measurableSet]
  filter_upwards [ae_posDef_nonsingularWishartMeasure ν (1 : Matrix (Fin r) (Fin r) ℝ)] with W hW
  exact symmetricCongruence_mapsTo_psdCone L hW.posSemidef

/-- The linear source is exactly an independent range-Wishart matrix and
an ambient Gaussian with covariance `L * Lᵀ`. -/
theorem linearRadiusExpectation_eq_actual (N : ℝ) (L : Matrix (Fin p) (Fin r) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) {f : SymmetricMatrix p → ℝ} (hf : Continuous f) (s : ℝ) :
    linearRadiusExpectation N L v f s =
      ∫ Y : RadialInputSpace p, f (radialInput v s Y)
        ∂(rangeWishartMeasure (N - 1) L).prod (multivariateGaussian 0 (L * Lᵀ)) := by
  have htest : Continuous (fun Y : RadialInputSpace p => f (radialInput v s Y)) :=
    hf.comp ((hasTemperateGrowth_radialInput v).1.continuous.comp
      (continuous_const.prodMk continuous_id))
  have h := integral_map (μ := scalarRegressionNoiseMeasure N r)
    (measurable_linearRadialNoise L).aemeasurable htest.aestronglyMeasurable
  rw [map_linearRadialNoise] at h
  exact h.symm

end Wishart.FiniteOrder

end
