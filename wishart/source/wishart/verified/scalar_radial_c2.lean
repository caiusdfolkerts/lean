module

public import wishart.verified.finite_order_stein
public import wishart.verified.finite_order_radial_calculus
public import wishart.verified.finite_order_integral

@[expose] public section

/-!
# The transverse radial equation under the printed C² hypotheses

The expectation uses the actual independent Gaussian and Wishart regression
noise. Only the value and the first two derivatives of the test are assumed
polynomially bounded on the positive semidefinite cone.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti.Probability Matrix Filter Set
open WishartVerification
open scoped RealInnerProductSpace BigOperators Topology

namespace Wishart.FiniteOrder

set_option backward.isDefEq.respectTransparency false in
theorem wishart_radial_generator_stationarity_c2 {p : ℕ} {N : ℝ}
    (hN : (p : ℝ) - 1 < N) {f : SymmetricMatrix p → ℝ}
    (hf : C2PolynomialOn (psdCone p) f) (v : EuclideanSpace ℝ (Fin p)) :
    (∫ X, symmetricRadialGenerator N v f X
      ∂nonsingularWishartMeasure N (1 : Matrix (Fin p) (Fin p) ℝ)) =
      ∫ X, fderiv ℝ f X (congruenceVelocity (outerMatrix v v) X)
        ∂nonsingularWishartMeasure N (1 : Matrix (Fin p) (Fin p) ℝ) := by
  letI := isProbabilityMeasure_nonsingularWishartMeasure Matrix.PosDef.one hN
  let μ := nonsingularWishartMeasure N (1 : Matrix (Fin p) (Fin p) ℝ)
  let gi := radialDerivativeTest f v
  let L (i : Fin p) (X : SymmetricMatrix p) :=
    fderiv ℝ (gi i) X (congruenceVelocity (outerMatrix v (coordinateVector i)) X)
  let R (i : Fin p) (X : SymmetricMatrix p) :=
    (symmetricMatrixAction X v) i * gi i X
  let B (X : SymmetricMatrix p) := fderiv ℝ f X (rankOneSymmetric v)
  let V (X : SymmetricMatrix p) := fderiv ℝ f X (congruenceVelocity (outerMatrix v v) X)
  have hμ := allFiniteMoments_wishart_norm N (1 : Matrix (Fin p) (Fin p) ℝ)
  have hsupport : ∀ᵐ X ∂μ, X ∈ psdCone p := by
    filter_upwards [ae_posDef_nonsingularWishartMeasure N (1 : Matrix (Fin p) (Fin p) ℝ)] with X hX
    exact hX.posSemidef
  have hgi (i : Fin p) := c1_radialDerivativeTest hf v i
  have hgiint (i : Fin p) : Integrable (gi i) μ :=
    (hgi i).value.integrable hμ (hgi i).regular.continuous.aestronglyMeasurable hsupport
  have hLint (i : Fin p) : Integrable (L i) μ :=
    ((hgi i).derivative.clm_apply (PolynomialBoundOn.of_temperate
      (congruenceVelocity (outerMatrix v (coordinateVector i))).hasTemperateGrowth)).integrable hμ
        (((hgi i).regular.continuous_fderiv (by norm_num)).clm_apply
          (congruenceVelocity (outerMatrix v (coordinateVector i))).continuous).aestronglyMeasurable
        hsupport
  have hRint (i : Fin p) : Integrable (R i) μ := by
    have h := (C1PolynomialOn.of_temperate (s := psdCone p)
      ((innerSL ℝ (coordinateVector i)).hasTemperateGrowth.comp
        (symmetricMatrixAction.bilinear_hasTemperateGrowth Function.HasTemperateGrowth.id
          (Function.HasTemperateGrowth.const v)))).mul (hgi i)
    simpa only [Function.comp_def, Pi.mul_def, id_eq, innerSL_apply_apply,
      coordinate_inner, R, gi, μ] using
        h.value.integrable hμ h.regular.continuous.aestronglyMeasurable hsupport
  have hBint : Integrable B μ :=
    (hf.derivative.clm_apply (PolynomialBoundOn.const _ (rankOneSymmetric v))).integrable hμ
      ((hf.regular.continuous_fderiv (by norm_num)).clm_apply continuous_const).aestronglyMeasurable
      hsupport
  have hVint : Integrable V μ :=
    (hf.derivative.clm_apply (PolynomialBoundOn.of_temperate
      (congruenceVelocity (outerMatrix v v)).hasTemperateGrowth)).integrable hμ
        ((hf.regular.continuous_fderiv (by norm_num)).clm_apply
          (congruenceVelocity (outerMatrix v v)).continuous).aestronglyMeasurable hsupport
  have hLi (i : Fin p) : (∫ X, L i X ∂μ) =
      (∫ X, R i X ∂μ) - N * v i * (∫ X, gi i X ∂μ) := by
    have h := wishart_stein_c1 Matrix.PosDef.one hN (hgi i)
      (outerMatrix v (coordinateVector i))
    simp only [inv_one, trace_mul_outerMatrix_mul,
      Matrix.toLpLin_one, LinearMap.id_apply, trace_outerMatrix, coordinate_inner,
      sub_mul] at h
    rw [integral_sub (hRint i) ((hgiint i).const_mul (N * v i)), integral_const_mul] at h
    exact h
  have hLpoint (X : SymmetricMatrix p) : (∑ i, L i X) =
      radialCovarianceContraction f X v (X : Matrix (Fin p) (Fin p) ℝ) := by
    rw [radialCovarianceContraction_eq_directional_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [symmetricSecondDerivative_eq_c2 hf.regular]
    simp only [L, gi, congruenceVelocity_outerMatrix]
    rfl
  have hRpoint (X : SymmetricMatrix p) : (∑ i, R i X) = V X := by
    dsimp [R, gi, radialDerivativeTest, V]
    rw [congruenceVelocity_outerMatrix,
      ← map_sum_coordinateVector (symmetricRankDirection v) (symmetricMatrixAction X v)]
    simp only [map_sum, map_smul, smul_eq_mul, symmetricMatrixAction_apply,
      Matrix.toLpLin_apply]
  have hBpoint (X : SymmetricMatrix p) : (∑ i, v i * gi i X) = 2 * B X :=
    sum_radialDerivativeTest f v X
  have hsum := congrArg (fun a : Fin p → ℝ => ∑ i, a i) (funext hLi)
  have hLsum : (∑ i, ∫ X, L i X ∂μ) =
      ∫ X, radialCovarianceContraction f X v (X : Matrix (Fin p) (Fin p) ℝ) ∂μ := by
    rw [← integral_finsetSum _ (fun i _ => hLint i)]
    exact integral_congr_ae (Filter.Eventually.of_forall hLpoint)
  have hRsum : (∑ i, ∫ X, R i X ∂μ) = ∫ X, V X ∂μ := by
    rw [← integral_finsetSum _ (fun i _ => hRint i)]
    exact integral_congr_ae (Filter.Eventually.of_forall hRpoint)
  have hBsum : (∑ i, v i * ∫ X, gi i X ∂μ) = 2 * ∫ X, B X ∂μ := by
    simp_rw [← integral_const_mul]
    rw [← integral_finsetSum _ (fun i _ => (hgiint i).const_mul (v i)),
      integral_congr_ae (Filter.Eventually.of_forall hBpoint), integral_const_mul]
  have hcovint : Integrable (fun X =>
      radialCovarianceContraction f X v (X : Matrix (Fin p) (Fin p) ℝ)) μ :=
    (integrable_finsetSum _ (fun i _ => hLint i)).congr
      (Filter.Eventually.of_forall hLpoint)
  change (∫ X, symmetricRadialGenerator N v f X ∂μ) = ∫ X, V X ∂μ
  simp only [symmetricRadialGenerator]
  rw [integral_add (hBint.const_mul (2 * N)) hcovint, integral_const_mul]
  simp only [Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum] at hsum
  rw [hLsum, hRsum, hBsum] at hsum
  linarith


set_option backward.isDefEq.respectTransparency false in
theorem wishart_diagonal_test_weak_identity_c2 {p : ℕ} {N : ℝ}
    (hN : (p : ℝ) - 1 < N) (a : Fin p)
    {f : SymmetricMatrix p → ℝ} (hf : C2PolynomialOn (psdCone p) f)
    {φ : ℝ → ℝ} (hφ : φ.HasTemperateGrowth) :
    Integrable (diagonalTestWeakIntegrand N a f φ)
      (nonsingularWishartMeasure N (1 : Matrix (Fin p) (Fin p) ℝ)) ∧
    (∫ X, diagonalTestWeakIntegrand N a f φ X
      ∂nonsingularWishartMeasure N (1 : Matrix (Fin p) (Fin p) ℝ)) = 0 := by
  letI := isProbabilityMeasure_nonsingularWishartMeasure Matrix.PosDef.one hN
  let μ := nonsingularWishartMeasure N (1 : Matrix (Fin p) (Fin p) ℝ)
  let g : SymmetricMatrix p → ℝ := fun X => φ (diagonalEntryCLM a X) * f X
  have htest : (fun X => φ (diagonalEntryCLM a X)).HasTemperateGrowth := by
    simpa only [Function.comp_def] using hφ.comp (diagonalEntryCLM a).hasTemperateGrowth
  have hg : C2PolynomialOn (psdCone p) g := (C2PolynomialOn.of_temperate htest).mul hf
  have hμ := allFiniteMoments_wishart_norm N (1 : Matrix (Fin p) (Fin p) ℝ)
  have hsupport : ∀ᵐ X ∂μ, X ∈ psdCone p := by
    filter_upwards [ae_posDef_nonsingularWishartMeasure N (1 : Matrix (Fin p) (Fin p) ℝ)] with X hX
    exact hX.posSemidef
  have hL : Integrable (symmetricRadialGenerator N (coordinateVector a) g) μ :=
    (polynomial_symmetricRadialGenerator_c2 hg N (coordinateVector a)).integrable hμ
      (continuous_symmetricRadialGenerator_c2 hg.regular N (coordinateVector a)).aestronglyMeasurable
      hsupport
  have hV : Integrable (fun X => fderiv ℝ g X
      (congruenceVelocity (outerMatrix (coordinateVector a) (coordinateVector a)) X)) μ :=
    (hg.derivative.clm_apply (PolynomialBoundOn.of_temperate
      (congruenceVelocity (outerMatrix (coordinateVector a) (coordinateVector a))).hasTemperateGrowth)).integrable hμ
        ((hg.regular.continuous_fderiv (by norm_num)).clm_apply
          (congruenceVelocity (outerMatrix (coordinateVector a) (coordinateVector a))).continuous).aestronglyMeasurable
        hsupport
  have heq : diagonalTestWeakIntegrand N a f φ = fun X =>
      symmetricRadialGenerator N (coordinateVector a) g X - fderiv ℝ g X
        (congruenceVelocity (outerMatrix (coordinateVector a) (coordinateVector a)) X) := by
    funext X
    rw [show g = fun X => φ (diagonalEntryCLM a X) * f X from rfl,
      symmetricRadialGenerator_diagonal_test_c2 hφ hf.regular,
      fderiv_product_apply_c1 (htest.1.of_le (by simp)) hf.toC1.regular,
      fderiv_scalar_linear_apply hφ, diagonalEntry_congruence_coordinate]
    dsimp [diagonalTestWeakIntegrand]
    ring
  rw [heq]
  refine ⟨hL.sub hV, ?_⟩
  rw [integral_sub hL hV, wishart_radial_generator_stationarity_c2 hN hg, sub_self]


def scalarNoiseSupport (r : ℕ) : Set (ScalarRegressionNoise r) :=
  {x | x.2 ∈ psdCone r}

theorem ae_scalarNoiseSupport (N : ℝ) (r : ℕ) :
    ∀ᵐ x ∂scalarRegressionNoiseMeasure N r, x ∈ scalarNoiseSupport r := by
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae
    (ae_posDef_nonsingularWishartMeasure (N - 1) (1 : Matrix (Fin r) (Fin r) ℝ))] with x hx
  exact hx.posSemidef

theorem scalarRadialData_mapsTo (r : ℕ) :
    MapsTo (scalarRadialDataCLM r) (scalarNoiseSupport r) (radialSupport (1 + r)) := by
  intro x hx
  change ((scalarRadialDataCLM r x).1 : Matrix (Fin (1 + r)) (Fin (1 + r)) ℝ).PosSemidef
  change (x.2 : Matrix (Fin r) (Fin r) ℝ).PosSemidef at hx
  rw [scalarRadialDataCLM_apply, Matrix.coe_symmetricCongruenceLinearMap_apply]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hx.mul_mul_conjTranspose_same (scalarNoiseMatrix r)

theorem scalarRadialData_parameter_mapsTo (r : ℕ) :
    MapsTo (fun y : ℝ × ScalarRegressionNoise r => (y.1, scalarRadialDataCLM r y.2))
      (univ ×ˢ scalarNoiseSupport r) (univ ×ˢ radialSupport (1 + r)) := by
  intro y hy
  exact ⟨mem_univ _, scalarRadialData_mapsTo r hy.2⟩

theorem scalarRadialMatrix_parameter_mapsTo (r : ℕ) :
    MapsTo (fun y : ℝ × ScalarRegressionNoise r => scalarRadialMatrix y.1 y.2)
      (univ ×ˢ scalarNoiseSupport r) (psdCone (1 + r)) :=
  (radialInput_parameter_mapsTo (scalarTransverseAxis r)).comp
    (scalarRadialData_parameter_mapsTo r)

theorem c1_scalarRadialIntegrand {r : ℕ} {f : SymmetricMatrix (1 + r) → ℝ}
    (hf : C2PolynomialOn (psdCone (1 + r)) f) :
    C1PolynomialOn (univ ×ˢ scalarNoiseSupport r)
      (fun y : ℝ × ScalarRegressionNoise r => f (scalarRadialMatrix y.1 y.2)) :=
  (c1_radialIntegrand hf (scalarTransverseAxis r)).comp
    (C1PolynomialOn.of_temperate (hasTemperateGrowth_scalarRadialDataParameter r))
    (scalarRadialData_parameter_mapsTo r)

theorem c1_scalarRadialFirst {r : ℕ} {f : SymmetricMatrix (1 + r) → ℝ}
    (hf : C2PolynomialOn (psdCone (1 + r)) f) :
    C1PolynomialOn (univ ×ˢ scalarNoiseSupport r)
      (fun y : ℝ × ScalarRegressionNoise r => scalarRadialFirst f y.1 y.2) :=
  (c1_radialFirstIntegrand hf (scalarTransverseAxis r)).comp
    (C1PolynomialOn.of_temperate (hasTemperateGrowth_scalarRadialDataParameter r))
    (scalarRadialData_parameter_mapsTo r)

theorem continuous_scalarRadialSecond_c2 {r : ℕ} {f : SymmetricMatrix (1 + r) → ℝ}
    (hf : ContDiff ℝ 2 f) :
    Continuous (fun y : ℝ × ScalarRegressionNoise r => scalarRadialSecond f y.1 y.2) :=
  (continuous_radialSecondIntegrand_c2 hf (scalarTransverseAxis r)).comp
    (hasTemperateGrowth_scalarRadialDataParameter r).1.continuous

theorem polynomial_scalarRadialSecond_c2 {r : ℕ} {f : SymmetricMatrix (1 + r) → ℝ}
    (hf : C2PolynomialOn (psdCone (1 + r)) f) :
    PolynomialBoundOn (univ ×ˢ scalarNoiseSupport r)
      (fun y : ℝ × ScalarRegressionNoise r => scalarRadialSecond f y.1 y.2) := by
  have h := PolynomialBoundOn.comp
    (f := fun z : ℝ × RadialInputSpace (1 + r) =>
      radialSecondIntegrand f (scalarTransverseAxis r) z.1 z.2)
    (g := fun y : ℝ × ScalarRegressionNoise r => (y.1, scalarRadialDataCLM r y.2))
    (polynomial_radialSecondIntegrand_c2 hf (scalarTransverseAxis r))
    (PolynomialBoundOn.of_temperate (hasTemperateGrowth_scalarRadialDataParameter r))
    (scalarRadialData_parameter_mapsTo r)
  simpa only [scalarRadialSecond] using h

theorem integrable_scalarRadiusSlice_polynomial {r : ℕ} {N : ℝ} (hN : (r : ℝ) < N)
    {f : SymmetricMatrix (1 + r) → ℝ} (hf : Continuous f)
    (hb : PolynomialBoundOn (psdCone (1 + r)) f) (s : ℝ) :
    Integrable (fun x => f (scalarRadialMatrix s x)) (scalarRegressionNoiseMeasure N r) := by
  letI := isProbabilityMeasure_scalarRegressionNoiseMeasure hN
  apply integrable_parameter_polynomialOn (allFiniteNormMoments_scalarRegressionNoise hN)
    (ae_scalarNoiseSupport N r)
    (hb.comp (PolynomialBoundOn.of_temperate (hasTemperateGrowth_scalarRadialMatrix r))
      (scalarRadialMatrix_parameter_mapsTo r)) s
  exact (hf.comp ((hasTemperateGrowth_scalarRadialMatrix r).1.continuous.comp
    (continuous_const.prodMk continuous_id))).aestronglyMeasurable

theorem integrable_scalarRadiusSlice_c2 {r : ℕ} {N : ℝ} (hN : (r : ℝ) < N)
    {f : SymmetricMatrix (1 + r) → ℝ} (hf : C2PolynomialOn (psdCone (1 + r)) f) (s : ℝ) :
    Integrable (fun x => f (scalarRadialMatrix s x)) (scalarRegressionNoiseMeasure N r) :=
  integrable_scalarRadiusSlice_polynomial hN hf.regular.continuous hf.value s

theorem integrable_scalarRadiusFirstSlice_c2 {r : ℕ} {N : ℝ} (hN : (r : ℝ) < N)
    {f : SymmetricMatrix (1 + r) → ℝ} (hf : C2PolynomialOn (psdCone (1 + r)) f) (s : ℝ) :
    Integrable (scalarRadialFirst f s) (scalarRegressionNoiseMeasure N r) := by
  letI := isProbabilityMeasure_scalarRegressionNoiseMeasure hN
  exact integrable_parameter_polynomialOn (allFiniteNormMoments_scalarRegressionNoise hN)
    (ae_scalarNoiseSupport N r) (c1_scalarRadialFirst hf).value s
    (((c1_scalarRadialFirst hf).regular.continuous.comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable)

theorem continuous_scalarRadiusExpectation_polynomial {r : ℕ} {N : ℝ}
    (hN : (r : ℝ) < N) {f : SymmetricMatrix (1 + r) → ℝ} (hf : Continuous f)
    (hb : PolynomialBoundOn (psdCone (1 + r)) f) : Continuous (scalarRadiusExpectation N f) := by
  letI := isProbabilityMeasure_scalarRegressionNoiseMeasure hN
  exact continuous_integral_polynomialOn (allFiniteNormMoments_scalarRegressionNoise hN)
    (ae_scalarNoiseSupport N r)
    (hf.comp (hasTemperateGrowth_scalarRadialMatrix r).1.continuous)
    (hb.comp (PolynomialBoundOn.of_temperate (hasTemperateGrowth_scalarRadialMatrix r))
      (scalarRadialMatrix_parameter_mapsTo r))

theorem hasDerivAt_scalarRadiusExpectation_c2 {r : ℕ} {N : ℝ}
    (hN : (r : ℝ) < N) {f : SymmetricMatrix (1 + r) → ℝ}
    (hf : C2PolynomialOn (psdCone (1 + r)) f) (s : ℝ) :
    HasDerivAt (scalarRadiusExpectation N f) (scalarRadiusFirstExpectation N f s) s := by
  letI := isProbabilityMeasure_scalarRegressionNoiseMeasure hN
  have hparam := c1_scalarRadialIntegrand hf
  have hd := hasDerivAt_integral_c1PolynomialOn (allFiniteNormMoments_scalarRegressionNoise hN)
    (ae_scalarNoiseSupport N r) hparam s
  convert hd using 1
  · rfl
  apply integral_congr_ae
  filter_upwards with x
  exact (hasDerivAt_radialIntegrand_c2 hf.regular (scalarTransverseAxis r)
    (scalarRadialDataCLM r x) s).unique (hasDerivAt_parameter_slice_of_c1 hparam.regular x s)

theorem hasDerivAt_scalarRadiusFirstExpectation_c2 {r : ℕ} {N : ℝ}
    (hN : (r : ℝ) < N) {f : SymmetricMatrix (1 + r) → ℝ}
    (hf : C2PolynomialOn (psdCone (1 + r)) f) (s : ℝ) :
    HasDerivAt (scalarRadiusFirstExpectation N f) (scalarRadiusSecondExpectation N f s) s := by
  letI := isProbabilityMeasure_scalarRegressionNoiseMeasure hN
  have hparam := c1_scalarRadialFirst hf
  have hd := hasDerivAt_integral_c1PolynomialOn (allFiniteNormMoments_scalarRegressionNoise hN)
    (ae_scalarNoiseSupport N r) hparam s
  convert hd using 1
  · rfl
  apply integral_congr_ae
  filter_upwards with x
  exact (hasDerivAt_radialFirstIntegrand_c2 hf.regular (scalarTransverseAxis r)
    (scalarRadialDataCLM r x) s).unique (hasDerivAt_parameter_slice_of_c1 hparam.regular x s)

theorem continuous_scalarRadiusSecondExpectation_c2 {r : ℕ} {N : ℝ}
    (hN : (r : ℝ) < N) {f : SymmetricMatrix (1 + r) → ℝ}
    (hf : C2PolynomialOn (psdCone (1 + r)) f) : Continuous (scalarRadiusSecondExpectation N f) := by
  letI := isProbabilityMeasure_scalarRegressionNoiseMeasure hN
  exact continuous_integral_polynomialOn (allFiniteNormMoments_scalarRegressionNoise hN)
    (ae_scalarNoiseSupport N r) (continuous_scalarRadialSecond_c2 hf.regular)
    (polynomial_scalarRadialSecond_c2 hf)

theorem scalarRadiusExpectation_even_c2 {r : ℕ} {N : ℝ}
    (hN : (r : ℝ) < N) {f : SymmetricMatrix (1 + r) → ℝ}
    (hf : ContDiff ℝ 2 f) (s : ℝ) :
    scalarRadiusExpectation N f (-s) = scalarRadiusExpectation N f s := by
  let γ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin r)) (1 : Matrix (Fin r) (Fin r) ℝ)
  have hneg : MeasurePreserving (fun z : EuclideanSpace ℝ (Fin r) => -z) γ γ :=
    ⟨by fun_prop, map_neg_centered_multivariateGaussian Matrix.PosSemidef.one⟩
  have hp : MeasurePreserving (Prod.map (fun z : EuclideanSpace ℝ (Fin r) => -z) id)
      (scalarRegressionNoiseMeasure N r) (scalarRegressionNoiseMeasure N r) :=
    hneg.prod (MeasurePreserving.id
      (nonsingularWishartMeasure (N - 1) (1 : Matrix (Fin r) (Fin r) ℝ)))
  have htest : Measurable (fun x : ScalarRegressionNoise r => f (scalarRadialMatrix s x)) :=
    (hf.continuous.comp ((hasTemperateGrowth_scalarRadialMatrix r).1.continuous.comp
      (continuous_const.prodMk continuous_id))).measurable
  have hid := integral_map hp.measurable.aemeasurable
    (show AEStronglyMeasurable (fun x : ScalarRegressionNoise r => f (scalarRadialMatrix s x))
      ((scalarRegressionNoiseMeasure N r).map (Prod.map (fun z => -z) id)) from by
        rw [hp.map_eq]
        exact htest.aestronglyMeasurable)
  rw [hp.map_eq] at hid
  symm
  apply hid.trans
  apply integral_congr_ae
  filter_upwards with x
  congr 1
  dsimp [scalarRadialMatrix, radialInput, scalarRadialDataCLM_apply, Prod.map]
  rw [map_neg]
  have he : -(scalarNoiseMatrix r).toEuclideanLin x.1 + s • scalarTransverseAxis r =
      -((scalarNoiseMatrix r).toEuclideanLin x.1 + (-s) • scalarTransverseAxis r) := by module
  rw [he, rankOneSymmetric_neg]

theorem scalarRegression_diagonal_test_integral_c2 {r : ℕ} {N : ℝ}
    (hN : (r : ℝ) < N) {f : SymmetricMatrix (1 + r) → ℝ}
    (hf : C2PolynomialOn (psdCone (1 + r)) f) (φ : ℝ → ℝ) {t : ℝ} (ht : 0 < t) :
    (∫ x, diagonalTestWeakIntegrand N (Fin.castAdd r (0 : Fin 1)) f φ
      (scalarRegressionMatrix t x) ∂scalarRegressionNoiseMeasure N r) =
      radialWeakIntegrand N (scalarRadialProfile N f) (scalarRadialProfileDerivative N f)
        (scalarRadialGeneratorExpectation N f) φ t := by
  let μ := scalarRegressionNoiseMeasure N r
  let F (x : ScalarRegressionNoise r) := f (scalarRadialMatrix (Real.sqrt t) x)
  let G (x : ScalarRegressionNoise r) :=
    symmetricRadialGenerator N (scalarTransverseAxis r) f (scalarRadialMatrix (Real.sqrt t) x)
  let D (x : ScalarRegressionNoise r) := scalarRadialFirst f (Real.sqrt t) x
  have hiF : Integrable F μ := integrable_scalarRadiusSlice_c2 hN hf _
  have hiG : Integrable G μ := integrable_scalarRadiusSlice_polynomial hN
    (continuous_symmetricRadialGenerator_c2 hf.regular N (scalarTransverseAxis r))
    (polynomial_symmetricRadialGenerator_c2 hf N (scalarTransverseAxis r)) _
  have hiD : Integrable D μ := integrable_scalarRadiusFirstSlice_c2 hN hf _
  have heq (x : ScalarRegressionNoise r) :
      diagonalTestWeakIntegrand N (Fin.castAdd r (0 : Fin 1)) f φ
          (scalarRegressionMatrix t x) =
        φ t * G x + (4 * t * deriv (deriv φ) t + 2 * N * deriv φ t) * F x +
          (4 * deriv φ t - φ t) * (Real.sqrt t * D x) - 2 * t * deriv φ t * F x := by
    simp only [diagonalTestWeakIntegrand, diagonalEntryCLM_apply,
      scalarRegressionMatrix_selected ht.le]
    rw [← scalarRadialMatrix_eq_regression ht.le x,
      ← scalarTransverseAxis_eq_coordinate r, scalarRadialMatrix_first_drift]
  simp_rw [heq]
  have hiAB : Integrable (fun x => φ t * G x +
      (4 * t * deriv (deriv φ) t + 2 * N * deriv φ t) * F x) μ :=
    (hiG.const_mul (φ t)).add (hiF.const_mul (4 * t * deriv (deriv φ) t + 2 * N * deriv φ t))
  have hiABC : Integrable (fun x => φ t * G x +
      (4 * t * deriv (deriv φ) t + 2 * N * deriv φ t) * F x +
        (4 * deriv φ t - φ t) * (Real.sqrt t * D x)) μ :=
    hiAB.add ((hiD.const_mul (Real.sqrt t)).const_mul (4 * deriv φ t - φ t))
  rw [integral_sub hiABC (hiF.const_mul (2 * t * deriv φ t)),
    integral_add hiAB ((hiD.const_mul (Real.sqrt t)).const_mul (4 * deriv φ t - φ t)),
    integral_add (hiG.const_mul (φ t))
      (hiF.const_mul (4 * t * deriv (deriv φ) t + 2 * N * deriv φ t))]
  simp only [integral_const_mul]
  change φ t * scalarRadialGeneratorExpectation N f t +
      (4 * t * deriv (deriv φ) t + 2 * N * deriv φ t) * scalarRadialProfile N f t +
      (4 * deriv φ t - φ t) *
        (Real.sqrt t * scalarRadiusFirstExpectation N f (Real.sqrt t)) -
      2 * t * deriv φ t * scalarRadialProfile N f t = _
  rw [scalarRadiusFirstExpectation_scale N f ht]
  unfold radialWeakIntegrand
  ring

/-- The weak radial premise is a theorem of the genuine Wishart law. -/
theorem scalarRadialProfile_weak_identity_c2 {r : ℕ} {N : ℝ}
    (hN : (r : ℝ) < N) {f : SymmetricMatrix (1 + r) → ℝ}
    (hf : C2PolynomialOn (psdCone (1 + r)) f) {φ : ℝ → ℝ} (hφ : φ.HasTemperateGrowth) :
    (∫ t, radialWeakIntegrand N (scalarRadialProfile N f) (scalarRadialProfileDerivative N f)
      (scalarRadialGeneratorExpectation N f) φ t ∂chiSquaredMeasure N) = 0 := by
  have hN0 : 0 < N := (Nat.cast_nonneg r).trans_lt hN
  have hdegree : (((1 + r : ℕ) : ℝ) - 1) < N := by
    push_cast
    linarith
  letI := isProbabilityMeasure_chiSquaredMeasure hN0.le
  letI := isProbabilityMeasure_scalarRegressionNoiseMeasure hN
  let h := diagonalTestWeakIntegrand N (Fin.castAdd r (0 : Fin 1)) f φ
  have htest := wishart_diagonal_test_weak_identity_c2 hdegree (Fin.castAdd r (0 : Fin 1)) hf hφ
  have hmap : MeasurePreserving (Function.uncurry (scalarRegressionMatrix (r := r)))
      ((chiSquaredMeasure N).prod (scalarRegressionNoiseMeasure N r))
      (nonsingularWishartMeasure N (1 : Matrix (Fin (1 + r)) (Fin (1 + r)) ℝ)) :=
    ⟨measurable_scalarRegressionMatrix, map_scalarRegressionMatrix hN⟩
  have hsource : Integrable (fun x : ℝ × ScalarRegressionNoise r =>
      h (scalarRegressionMatrix x.1 x.2))
      ((chiSquaredMeasure N).prod (scalarRegressionNoiseMeasure N r)) :=
    hmap.integrable_comp_of_integrable htest.1
  have hid := integral_map hmap.measurable.aemeasurable
    (show AEStronglyMeasurable h
      (((chiSquaredMeasure N).prod (scalarRegressionNoiseMeasure N r)).map
        (Function.uncurry scalarRegressionMatrix)) from by
      rw [hmap.map_eq]
      exact htest.1.aestronglyMeasurable)
  rw [hmap.map_eq] at hid
  have hzero : (∫ x : ℝ × ScalarRegressionNoise r, h (scalarRegressionMatrix x.1 x.2)
      ∂(chiSquaredMeasure N).prod (scalarRegressionNoiseMeasure N r)) = 0 :=
    hid.symm.trans htest.2
  rw [integral_prod _ hsource] at hzero
  have heq : (fun t => ∫ x, h (scalarRegressionMatrix t x) ∂scalarRegressionNoiseMeasure N r) =ᵐ[
      chiSquaredMeasure N]
      (fun t => radialWeakIntegrand N (scalarRadialProfile N f)
        (scalarRadialProfileDerivative N f) (scalarRadialGeneratorExpectation N f) φ t) := by
    filter_upwards [ae_pos_chiSquaredMeasure hN0] with t ht
    exact scalarRegression_diagonal_test_integral_c2 hN hf φ ht
  rwa [integral_congr_ae heq] at hzero

theorem hasDerivAt_scalarRadialProfile_c2 {r : ℕ} {N : ℝ}
    (hN : (r : ℝ) < N) {f : SymmetricMatrix (1 + r) → ℝ}
    (hf : C2PolynomialOn (psdCone (1 + r)) f) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (scalarRadialProfile N f) (scalarRadialProfileDerivative N f t) t :=
  hasDerivAt_sqrt_profile ht (hasDerivAt_scalarRadiusExpectation_c2 hN hf (Real.sqrt t))

theorem hasDerivAt_scalarRadialProfileDerivative_c2 {r : ℕ} {N : ℝ}
    (hN : (r : ℝ) < N) {f : SymmetricMatrix (1 + r) → ℝ}
    (hf : C2PolynomialOn (psdCone (1 + r)) f) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (scalarRadialProfileDerivative N f) (scalarRadialProfileSecondDerivative N f t) t :=
  hasDerivAt_sqrt_profile_derivative ht (hasDerivAt_scalarRadiusFirstExpectation_c2 hN hf (Real.sqrt t))

theorem continuousOn_scalarRadialProfileSecondDerivative_c2 {r : ℕ} {N : ℝ}
    (hN : (r : ℝ) < N) {f : SymmetricMatrix (1 + r) → ℝ}
    (hf : C2PolynomialOn (psdCone (1 + r)) f) :
    ContinuousOn (scalarRadialProfileSecondDerivative N f) (Ioi 0) := by
  have hJ₁ : Continuous (scalarRadiusFirstExpectation N f) :=
    continuous_iff_continuousAt.mpr fun s => (hasDerivAt_scalarRadiusFirstExpectation_c2 hN hf s).continuousAt
  have hJ₂ := continuous_scalarRadiusSecondExpectation_c2 hN hf
  exact ((hJ₂.comp Real.continuous_sqrt).continuousOn.sub
    ((hJ₁.comp Real.continuous_sqrt).continuousOn.div Real.continuous_sqrt.continuousOn
      (fun t ht => (Real.sqrt_pos.mpr ht).ne'))).div
    (continuousOn_const.mul continuousOn_id) (fun t ht => mul_ne_zero (by norm_num) ht.ne')

theorem continuous_scalarRadialGeneratorExpectation_c2 {r : ℕ} {N : ℝ}
    (hN : (r : ℝ) < N) {f : SymmetricMatrix (1 + r) → ℝ}
    (hf : C2PolynomialOn (psdCone (1 + r)) f) : Continuous (scalarRadialGeneratorExpectation N f) := by
  exact (continuous_scalarRadiusExpectation_polynomial hN
    (continuous_symmetricRadialGenerator_c2 hf.regular N (scalarTransverseAxis r))
    (polynomial_symmetricRadialGenerator_c2 hf N (scalarTransverseAxis r))).comp Real.continuous_sqrt

/-- The pointwise transverse radial ODE, for every real N>r. -/
theorem scalarRadialProfile_ode_c2 {r : ℕ} {N : ℝ}
    (hN : (r : ℝ) < N) {f : SymmetricMatrix (1 + r) → ℝ}
    (hf : C2PolynomialOn (psdCone (1 + r)) f) {t : ℝ} (ht : 0 < t) :
    4 * t * scalarRadialProfileSecondDerivative N f t +
      2 * N * scalarRadialProfileDerivative N f t = scalarRadialGeneratorExpectation N f t := by
  apply radial_ode_of_chiSquared_tests ((Nat.cast_nonneg r).trans_lt hN)
    (fun t ht => hasDerivAt_scalarRadialProfile_c2 hN hf ht)
    (fun t ht => hasDerivAt_scalarRadialProfileDerivative_c2 hN hf ht)
    (continuousOn_scalarRadialProfileSecondDerivative_c2 hN hf)
    (continuous_scalarRadialGeneratorExpectation_c2 hN hf).continuousOn _ t ht
  intro φ hφ hcφ hsφ
  exact scalarRadialProfile_weak_identity_c2 hN hf (hcφ.hasTemperateGrowth hφ)


theorem monotoneOn_scalarRadialProfile_of_generator_nonneg_c2 {r : ℕ} {N : ℝ}
    (hN : (r : ℝ) < N) {f : SymmetricMatrix (1 + r) → ℝ}
    (hf : C2PolynomialOn (psdCone (1 + r)) f)
    (hgen : ∀ X : SymmetricMatrix (1 + r),
      (X : Matrix (Fin (1 + r)) (Fin (1 + r)) ℝ).PosSemidef →
      0 ≤ symmetricRadialGenerator N (scalarTransverseAxis r) f X) :
    MonotoneOn (scalarRadialProfile N f) (Ici 0) := by
  have hN0 : 0 < N := (Nat.cast_nonneg r).trans_lt hN
  have heven := scalarRadiusExpectation_even_c2 hN hf.regular
  apply monotoneOn_of_radial_operator_nonneg_of_derivative_limit
    (N := N) (D := scalarRadialProfileDerivative N f)
    (D₂ := scalarRadialProfileSecondDerivative N f)
    (L := scalarRadiusSecondExpectation N f 0 / 2) hN0
  · exact ((continuous_iff_continuousAt.mpr fun s =>
      (hasDerivAt_scalarRadiusExpectation_c2 hN hf s).continuousAt).comp Real.continuous_sqrt).continuousOn
  · intro t ht
    exact hasDerivAt_scalarRadialProfile_c2 hN hf ht
  · intro t ht
    exact hasDerivAt_scalarRadialProfileDerivative_c2 hN hf ht
  · exact tendsto_sqrt_derivative_quotient
      (hasDerivAt_even_zero heven (hasDerivAt_scalarRadiusExpectation_c2 hN hf 0))
      (hasDerivAt_scalarRadiusFirstExpectation_c2 hN hf 0)
  · intro t ht
    rw [scalarRadialProfile_ode_c2 hN hf ht]
    apply integral_nonneg_of_ae
    filter_upwards [ae_scalarRadialMatrix_posSemidef N (Real.sqrt t)] with x hx
    exact hgen _ hx


end Wishart.FiniteOrder

end
