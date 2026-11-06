module

public import wishart.verified.finite_order_extension
public import wishart.verified.finite_order_integral
public import wishart.verified.finite_order_radial_calculus

/-!
# Two derivatives and the origin of the actual radial expectation

All moment estimates are restricted to the positive semidefinite support.
The signed-radius profile has two derivatives; its evenness gives the finite
right derivative of the square-root profile at zero.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti.Probability Matrix Filter Set
open WishartVerification
open scoped Topology RealInnerProductSpace Matrix.Norms.L2Operator

namespace Wishart.FiniteOrder

/-- The exact local regularity and growth hypothesis in the paper: two
continuous derivatives on an open neighborhood of the support, with polynomial
bounds for the value, differential, and Hessian only on the support. -/
structure C2PolynomialNear {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (f : E → ℝ) : Prop where
  local_regular : ∃ U : Set E, IsOpen U ∧ S ⊆ U ∧ ContDiffOn ℝ 2 f U
  value : PolynomialBoundOn S f
  derivative : PolynomialBoundOn S (fderiv ℝ f)
  second : PolynomialBoundOn S (fderiv ℝ (fderiv ℝ f))

/-- The cutoff extension preserves precisely the three bounded quantities. -/
theorem C2PolynomialNear.extension {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {S : Set E} {f : E → ℝ}
    (hf : C2PolynomialNear S f) (hS : IsClosed S) :
    ∃ g : E → ℝ, C2PolynomialOn S g ∧ ∀ X ∈ S,
      g X = f X ∧ fderiv ℝ g X = fderiv ℝ f X ∧
        fderiv ℝ (fderiv ℝ g) X = fderiv ℝ (fderiv ℝ f) X := by
  obtain ⟨U, hU, hSU, hreg⟩ := hf.local_regular
  obtain ⟨g, hg, heq⟩ := exists_c2_extension_near_closed hS hU hSU hreg
  refine ⟨g, ⟨hg, ?_, ?_, ?_⟩, heq⟩
  · exact hf.value.congr fun X hX => (heq X hX).1.symm
  · exact hf.derivative.congr fun X hX => (heq X hX).2.1.symm
  · exact hf.second.congr fun X hX => (heq X hX).2.2.symm

theorem isClosed_psdCone (p : ℕ) : IsClosed (psdCone p) :=
  Matrix.posSemidef_is_closed.preimage continuous_subtype_val

/-- A C² test near the cone has a global representative with the same
value, differential, and Hessian at every positive semidefinite matrix. -/
theorem exists_c2PolynomialOn_extension_psd {p : ℕ} {f : SymmetricMatrix p → ℝ}
    (hf : C2PolynomialNear (psdCone p) f) :
    ∃ g : SymmetricMatrix p → ℝ, C2PolynomialOn (psdCone p) g ∧
      ∀ X ∈ psdCone p, g X = f X ∧ fderiv ℝ g X = fderiv ℝ f X ∧
        fderiv ℝ (fderiv ℝ g) X = fderiv ℝ (fderiv ℝ f) X :=
  hf.extension (isClosed_psdCone p)

section Differentiation

variable {p : ℕ} {μ : Measure (RadialInputSpace p)} [IsFiniteMeasure μ]
  (hμ : HasAllFiniteMoments (fun Y : RadialInputSpace p => ‖Y‖) μ)
  (hS : ∀ᵐ Y ∂μ, Y ∈ radialSupport p)

include hμ hS in
theorem hasDerivAt_radialExpectation_c2 {f : SymmetricMatrix p → ℝ}
    (hf : C2PolynomialOn (psdCone p) f)
    (v : EuclideanSpace ℝ (Fin p)) (r : ℝ) :
    HasDerivAt (fun s => ∫ Y, f (radialInput v s Y) ∂μ)
      (∫ Y, radialFirstIntegrand f v r Y ∂μ) r := by
  have hF := c1_radialIntegrand hf v
  have hd := hasDerivAt_integral_c1PolynomialOn hμ hS hF r
  have heq : (∫ Y, parameterDerivative
      (fun q : ℝ × RadialInputSpace p => f (radialInput v q.1 q.2)) (r, Y) ∂μ) =
      ∫ Y, radialFirstIntegrand f v r Y ∂μ := by
    apply integral_congr_ae
    filter_upwards with Y
    exact (hasDerivAt_parameter_slice_of_c1 hF.regular Y r).unique
      (hasDerivAt_radialIntegrand_c2 hf.regular v Y r)
  rwa [heq] at hd

include hμ hS in
theorem hasDerivAt_radialFirstExpectation_c2 {f : SymmetricMatrix p → ℝ}
    (hf : C2PolynomialOn (psdCone p) f)
    (v : EuclideanSpace ℝ (Fin p)) (r : ℝ) :
    HasDerivAt (fun s => ∫ Y, radialFirstIntegrand f v s Y ∂μ)
      (∫ Y, radialSecondIntegrand f v r Y ∂μ) r := by
  have hF := c1_radialFirstIntegrand hf v
  have hd := hasDerivAt_integral_c1PolynomialOn hμ hS hF r
  have heq : (∫ Y, parameterDerivative
      (fun q : ℝ × RadialInputSpace p => radialFirstIntegrand f v q.1 q.2) (r, Y) ∂μ) =
      ∫ Y, radialSecondIntegrand f v r Y ∂μ := by
    apply integral_congr_ae
    filter_upwards with Y
    exact (hasDerivAt_parameter_slice_of_c1 hF.regular Y r).unique
      (hasDerivAt_radialFirstIntegrand_c2 hf.regular v Y r)
  rwa [heq] at hd

include hμ hS in
theorem continuous_radialSecondExpectation_c2 {f : SymmetricMatrix p → ℝ}
    (hf : C2PolynomialOn (psdCone p) f) (v : EuclideanSpace ℝ (Fin p)) :
    Continuous (fun r : ℝ => ∫ Y, radialSecondIntegrand f v r Y ∂μ) :=
  continuous_integral_polynomialOn hμ hS (continuous_radialSecondIntegrand_c2 hf.regular v)
    (polynomial_radialSecondIntegrand_c2 hf v)

include hμ hS in
theorem integrable_radialIntegrand_c2 {f : SymmetricMatrix p → ℝ}
    (hf : C2PolynomialOn (psdCone p) f) (v : EuclideanSpace ℝ (Fin p)) (r : ℝ) :
    Integrable (fun Y => f (radialInput v r Y)) μ :=
  integrable_parameter_polynomialOn hμ hS (c1_radialIntegrand hf v).value r
    (((c1_radialIntegrand hf v).regular.continuous).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable

end Differentiation

theorem radialExpectation_even_c2 {p : ℕ} {C : Matrix (Fin p) (Fin p) ℝ}
    (hC : C.PosSemidef) {μW : Measure (SymmetricMatrix p)} [IsProbabilityMeasure μW]
    (hμW : HasAllFiniteMoments (fun W : SymmetricMatrix p => ‖W‖) μW)
    (hWpsd : ∀ᵐ W ∂μW, W ∈ psdCone p)
    {f : SymmetricMatrix p → ℝ} (hf : C2PolynomialOn (psdCone p) f)
    (v : EuclideanSpace ℝ (Fin p)) (r : ℝ) :
    (∫ Y : RadialInputSpace p, f (radialInput v (-r) Y)
      ∂μW.prod (multivariateGaussian 0 C)) =
    ∫ Y : RadialInputSpace p, f (radialInput v r Y)
      ∂μW.prod (multivariateGaussian 0 C) := by
  let μZ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) C
  let μ := μW.prod μZ
  have hμ : HasAllFiniteMoments (fun Y : RadialInputSpace p => ‖Y‖) μ :=
    allFiniteNormMoments_prod hμW allFiniteMoments_gaussian_norm
  have hS : ∀ᵐ Y ∂μ, Y ∈ radialSupport p := Measure.quasiMeasurePreserving_fst.ae hWpsd
  have hint (s : ℝ) : Integrable (fun Y => f (radialInput v s Y)) μ :=
    integrable_radialIntegrand_c2 hμ hS hf v s
  rw [integral_prod _ (hint (-r)), integral_prod _ (hint r)]
  apply integral_congr_ae
  filter_upwards with W
  have hneg : MeasurePreserving (fun z : EuclideanSpace ℝ (Fin p) => -z) μZ μZ :=
    ⟨by fun_prop, map_neg_centered_multivariateGaussian hC⟩
  have h := hneg.integral_comp (MeasurableEquiv.neg _).measurableEmbedding
    (fun z => f (W + rankOneSymmetric (z + r • v)))
  change (∫ z, f (W + rankOneSymmetric (z + (-r) • v)) ∂μZ) =
    ∫ z, f (W + rankOneSymmetric (z + r • v)) ∂μZ
  calc
    (∫ z, f (W + rankOneSymmetric (z + (-r) • v)) ∂μZ) =
        ∫ z, f (W + rankOneSymmetric (-z + r • v)) ∂μZ := by
      apply integral_congr_ae
      filter_upwards with z
      have he : -z + r • v = -(z + (-r) • v) := by module
      rw [he, rankOneSymmetric_neg]
    _ = _ := h

theorem hasDerivWithinAt_radialProfile_zero_c2 {p : ℕ}
    {C : Matrix (Fin p) (Fin p) ℝ} (hC : C.PosSemidef)
    {μW : Measure (SymmetricMatrix p)} [IsProbabilityMeasure μW]
    (hμW : HasAllFiniteMoments (fun W : SymmetricMatrix p => ‖W‖) μW)
    (hWpsd : ∀ᵐ W ∂μW, W ∈ psdCone p)
    {f : SymmetricMatrix p → ℝ} (hf : C2PolynomialOn (psdCone p) f)
    (v : EuclideanSpace ℝ (Fin p)) :
    HasDerivWithinAt (fun t : ℝ => ∫ Y : RadialInputSpace p,
      f (radialInput v (Real.sqrt t) Y) ∂μW.prod (multivariateGaussian 0 C))
      ((∫ Y : RadialInputSpace p, radialSecondIntegrand f v 0 Y
        ∂μW.prod (multivariateGaussian 0 C)) / 2) (Ici 0) 0 := by
  have hμ := allFiniteNormMoments_prod hμW
    (allFiniteMoments_gaussian_norm (μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) C))
  have hS : ∀ᵐ Y ∂μW.prod (multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) C),
      Y ∈ radialSupport p := Measure.quasiMeasurePreserving_fst.ae hWpsd
  exact Wishart.hasDerivWithinAt_sqrt_profile_zero_of_even
    (radialExpectation_even_c2 hC hμW hWpsd hf v)
    (hasDerivAt_radialExpectation_c2 hμ hS hf v 0)
    (fun s _ => hasDerivAt_radialExpectation_c2 hμ hS hf v s)
    (hasDerivAt_radialFirstExpectation_c2 hμ hS hf v 0)

end Wishart.FiniteOrder
