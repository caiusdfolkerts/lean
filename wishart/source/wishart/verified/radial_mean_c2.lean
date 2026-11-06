module

public import wishart.verified.finite_order_stein
public import wishart.verified.finite_order_integral
public import wishart.verified.finite_order_radial_calculus
public import wishart.verified.finite_order_gram

/-!
# The radial mean identity with the paper's C² hypotheses

The internal Stein assembly below uses only a value and one derivative of its
test.  Its application to a derivative of the observable therefore requires
exactly C² regularity.  Public applications instantiate this identity with
the actual real-shape Wishart and integer Gaussian Gram laws.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti.Probability Matrix Filter Set
open WishartVerification
open scoped Topology RealInnerProductSpace BigOperators Matrix.Norms.Operator

namespace Wishart.FiniteOrder

/-- The first-order integration by parts formula needed of the background
law.  It will be discharged by the genuine Wishart or Gram identity. -/
def ConeSteinIdentity {p : ℕ} (μ : Measure (SymmetricMatrix p))
    (C : Matrix (Fin p) (Fin p) ℝ) (ν : ℝ) : Prop :=
  ∀ (g : SymmetricMatrix p → ℝ), C1PolynomialOn (psdCone p) g →
    ∀ (T : SymmetricMatrix p), T ∈ psdCone p →
    ∀ (u v : EuclideanSpace ℝ (Fin p)),
      (∫ W, fderiv ℝ g (W + T)
        (symmetricRankDirection v (symmetricMatrixAction W u)) ∂μ) =
        ∫ W, (⟪u, symmetricMatrixAction W (C⁻¹.toEuclideanLin v)⟫ -
          ν * ⟪u, v⟫) * g (W + T) ∂μ

theorem coneSteinIdentity_wishart {p : ℕ} {C : Matrix (Fin p) (Fin p) ℝ}
    (hC : C.PosDef) {ν : ℝ} (hν : (p : ℝ) - 1 < ν) :
    ConeSteinIdentity (nonsingularWishartMeasure ν C) C ν := by
  intro g hg T hT u v
  simpa only [congruenceVelocity_outerMatrix, trace_mul_outerMatrix_mul,
    trace_outerMatrix] using wishart_stein_translate_c1 hC hν hg (outerMatrix v u) T hT

theorem coneSteinIdentity_gram {p : ℕ} {C : Matrix (Fin p) (Fin p) ℝ}
    (hC : C.PosDef) (n : ℕ) :
    ConeSteinIdentity (wishartGramMeasure n C) C (n : ℝ) := by
  intro g hg T hT u v
  exact gram_stein_translate_c1 n hC hg T hT u v

section Background

variable {p : ℕ} {C : Matrix (Fin p) (Fin p) ℝ} (hC : C.PosDef)
  {ν : ℝ} {μW : Measure (SymmetricMatrix p)} [IsProbabilityMeasure μW]
  (hμW : HasAllFiniteMoments (fun W : SymmetricMatrix p => ‖W‖) μW)
  (hWpsd : ∀ᵐ W ∂μW, W ∈ psdCone p)
  (hstein : ConeSteinIdentity μW C ν)

include hWpsd in
theorem radial_noise_support :
    ∀ᵐ Y ∂μW.prod (multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) C),
      Y ∈ radialSupport p :=
  Measure.quasiMeasurePreserving_fst.ae hWpsd

set_option backward.isDefEq.respectTransparency false in
include hC hμW hWpsd hstein in
theorem weighted_radial_stein_c1 {g : SymmetricMatrix p → ℝ}
    (hg : C1PolynomialOn (psdCone p) g)
    (u v : EuclideanSpace ℝ (Fin p)) (r : ℝ) :
    r * (∫ Y : RadialInputSpace p,
      ⟪u, symmetricMatrixAction Y.1 (C⁻¹.toEuclideanLin v)⟫ *
        g (radialInput v r Y)
      ∂μW.prod (multivariateGaussian 0 C)) =
    ν * (∫ Y : RadialInputSpace p, ⟪u, Y.2 + r • v⟫ * g (radialInput v r Y)
      ∂μW.prod (multivariateGaussian 0 C)) := by
  let μZ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) C
  let μ := μW.prod μZ
  let w : RadialInputSpace p → EuclideanSpace ℝ (Fin p) := fun Y => Y.2 + r • v
  let V : RadialInputSpace p → SymmetricMatrix p := radialInput v r
  let L : RadialInputSpace p → ℝ := fun Y =>
    fderiv ℝ g (V Y) (symmetricRankDirection (w Y) (symmetricMatrixAction Y.1 u))
  let G : RadialInputSpace p → ℝ := fun Y =>
    ⟪u, symmetricMatrixAction Y.1 (C⁻¹.toEuclideanLin Y.2)⟫ * g (V Y)
  let Q : RadialInputSpace p → ℝ := fun Y =>
    ⟪u, symmetricMatrixAction Y.1 (C⁻¹.toEuclideanLin v)⟫ * g (V Y)
  let R : RadialInputSpace p → ℝ := fun Y => ⟪u, w Y⟫ * g (V Y)
  let S : RadialInputSpace p → ℝ := fun Y =>
    (⟪u, symmetricMatrixAction Y.1 (C⁻¹.toEuclideanLin (w Y))⟫ - ν * ⟪u, w Y⟫) * g (V Y)
  have hμ : HasAllFiniteMoments (fun Y : RadialInputSpace p => ‖Y‖) μ :=
    allFiniteNormMoments_prod hμW allFiniteMoments_gaussian_norm
  have hsupport : ∀ᵐ Y ∂μ, Y ∈ radialSupport p := radial_noise_support hWpsd
  have hW := (ContinuousLinearMap.fst ℝ (SymmetricMatrix p) (EuclideanSpace ℝ (Fin p))).hasTemperateGrowth
  have hZ := (ContinuousLinearMap.snd ℝ (SymmetricMatrix p) (EuclideanSpace ℝ (Fin p))).hasTemperateGrowth
  have hw : w.HasTemperateGrowth := hZ.add (Function.HasTemperateGrowth.const (r • v))
  have hV : V.HasTemperateGrowth := hW.add (hasTemperateGrowth_rankOneSymmetric.comp hw)
  have hgV := hg.value.comp (PolynomialBoundOn.of_temperate hV) (radialInput_mapsTo v r)
  have hgVc : Continuous (fun Y => g (V Y)) := hg.regular.continuous.comp hV.1.continuous
  have hCi := (LinearMap.toContinuousLinearMap C⁻¹.toEuclideanLin).hasTemperateGrowth
  have hinner := (innerSL ℝ u).hasTemperateGrowth
  have hWu := symmetricMatrixAction.bilinear_hasTemperateGrowth hW (Function.HasTemperateGrowth.const u)
  have hH : (fun Y : RadialInputSpace p =>
      symmetricRankDirection (w Y) (symmetricMatrixAction Y.1 u)).HasTemperateGrowth := by
    simpa only [symmetricRankDirection, ContinuousLinearMap.smul_apply,
      Pi.smul_def, Pi.smul_apply, ContinuousLinearMap.coe_fst', two_smul,
      ContinuousLinearMap.add_apply] using
      (Function.HasTemperateGrowth.const (2 : ℝ)).fun_smul
        (symmetricOuterCLM.bilinear_hasTemperateGrowth hw hWu)
  have hLt : PolynomialBoundOn (radialSupport p) L :=
    (hg.derivative.comp (PolynomialBoundOn.of_temperate hV) (radialInput_mapsTo v r)).clm_apply
      (PolynomialBoundOn.of_temperate hH)
  have hGc := hinner.comp (symmetricMatrixAction.bilinear_hasTemperateGrowth hW (hCi.comp hZ))
  have hQc := hinner.comp (symmetricMatrixAction.bilinear_hasTemperateGrowth hW
    (Function.HasTemperateGrowth.const (C⁻¹.toEuclideanLin v)))
  have hRc := hinner.comp hw
  have hSc := (hinner.comp (symmetricMatrixAction.bilinear_hasTemperateGrowth hW (hCi.comp hw))).sub
    ((Function.HasTemperateGrowth.const ν).mul (hinner.comp hw))
  have hLint : Integrable L μ := hLt.integrable hμ
    (((hg.regular.continuous_fderiv (by norm_num)).comp hV.1.continuous).clm_apply
      hH.1.continuous).aestronglyMeasurable hsupport
  have hGint : Integrable G μ :=
    ((PolynomialBoundOn.of_temperate hGc).mul hgV).integrable hμ
      (hGc.1.continuous.mul hgVc).aestronglyMeasurable hsupport
  have hQint : Integrable Q μ :=
    ((PolynomialBoundOn.of_temperate hQc).mul hgV).integrable hμ
      (hQc.1.continuous.mul hgVc).aestronglyMeasurable hsupport
  have hRint : Integrable R μ :=
    ((PolynomialBoundOn.of_temperate hRc).mul hgV).integrable hμ
      (hRc.1.continuous.mul hgVc).aestronglyMeasurable hsupport
  have hSint : Integrable S μ :=
    ((PolynomialBoundOn.of_temperate hSc).mul hgV).integrable hμ
      (hSc.1.continuous.mul hgVc).aestronglyMeasurable hsupport
  have hWishart (z : EuclideanSpace ℝ (Fin p)) :
      (∫ W, L (W, z) ∂μW) = ∫ W, S (W, z) ∂μW := by
    simpa only [L, S, w, V, radialInput] using
      hstein g hg (rankOneSymmetric (z + r • v))
        (rankOneSymmetric_posSemidef _) u (z + r • v)
  have hGaussian (W : SymmetricMatrix p) (hW : W ∈ psdCone p) :
      (∫ z, G (W, z) ∂μZ) = ∫ z, L (W, z) ∂μZ := by
    have hshift : (fun z : EuclideanSpace ℝ (Fin p) => z + r • v).HasTemperateGrowth :=
      Function.HasTemperateGrowth.id.add (Function.HasTemperateGrowth.const _)
    have hmap : (fun z : EuclideanSpace ℝ (Fin p) =>
        W + rankOneSymmetric (z + r • v)).HasTemperateGrowth :=
      (Function.HasTemperateGrowth.const W).add (hasTemperateGrowth_rankOneSymmetric.comp hshift)
    have htest : C1PolynomialOn univ (fun z : EuclideanSpace ℝ (Fin p) =>
        g (W + rankOneSymmetric (z + r • v))) :=
      hg.comp (C1PolynomialOn.of_temperate hmap)
        (fun z _ => hW.add (rankOneSymmetric_posSemidef _))
    have hid := gaussian_stein_c1 hC htest (symmetricMatrixAction W u)
    have hd (z h : EuclideanSpace ℝ (Fin p)) :
        fderiv ℝ (fun z : EuclideanSpace ℝ (Fin p) => g (W + rankOneSymmetric (z + r • v))) z h =
          fderiv ℝ g (W + rankOneSymmetric (z + r • v))
            (symmetricRankDirection (z + r • v) h) := by
      have hin := (hasFDerivAt_rankOneSymmetric (z + r • v)).comp z
        ((hasFDerivAt_id z).add_const (r • v))
      have hderiv := ((hg.regular.differentiable (by norm_num) _).hasFDerivAt.comp z (hin.const_add W)).fderiv
      simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply] using congrArg (fun J => J h) hderiv
    simpa only [hd, inner_symmetricMatrixAction, L, G, w, V, radialInput] using hid
  have hSG : (∫ Y, S Y ∂μ) = ∫ Y, G Y ∂μ := by
    rw [integral_prod_symm S hSint, integral_prod G hGint]
    calc
      (∫ z, ∫ W, S (W, z) ∂μW ∂μZ) = ∫ z, ∫ W, L (W, z) ∂μW ∂μZ :=
        integral_congr_ae (Eventually.of_forall fun z => (hWishart z).symm)
      _ = ∫ Y, L Y ∂μ := (integral_prod_symm L hLint).symm
      _ = ∫ W, ∫ z, L (W, z) ∂μZ ∂μW := integral_prod L hLint
      _ = ∫ W, ∫ z, G (W, z) ∂μZ ∂μW := by
        apply integral_congr_ae
        filter_upwards [hWpsd] with W hW
        exact (hGaussian W hW).symm
  have hsplit : S = fun Y => G Y + r * Q Y - ν * R Y := by
    funext Y
    simp only [S, G, Q, R, w, map_add, map_smul, inner_add_right, real_inner_smul_right]
    ring
  rw [hsplit] at hSG
  have hsumInt : Integrable (fun Y => G Y + r * Q Y) μ := by
    simpa only [Pi.add_def] using hGint.add (hQint.const_mul r)
  rw [integral_sub hsumInt (hRint.const_mul ν),
    integral_add hGint (hQint.const_mul r), integral_const_mul, integral_const_mul] at hSG
  change r * (∫ Y, Q Y ∂μ) = ν * (∫ Y, R Y ∂μ)
  linarith

set_option backward.isDefEq.respectTransparency false in
include hμW hWpsd hstein in
theorem radial_background_stein_c1 {g : SymmetricMatrix p → ℝ}
    (hg : C1PolynomialOn (psdCone p) g)
    (u v : EuclideanSpace ℝ (Fin p)) (r : ℝ) :
    (∫ Y : RadialInputSpace p,
      fderiv ℝ g (radialInput v r Y)
        (symmetricRankDirection v (symmetricMatrixAction Y.1 u))
      ∂μW.prod (multivariateGaussian 0 C)) =
    ∫ Y : RadialInputSpace p,
      (⟪u, symmetricMatrixAction Y.1 (C⁻¹.toEuclideanLin v)⟫ - ν * ⟪u, v⟫) *
        g (radialInput v r Y)
      ∂μW.prod (multivariateGaussian 0 C) := by
  let μ := μW.prod (multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) C)
  have hμ : HasAllFiniteMoments (fun Y : RadialInputSpace p => ‖Y‖) μ :=
    allFiniteNormMoments_prod hμW allFiniteMoments_gaussian_norm
  have hsupport : ∀ᵐ Y ∂μ, Y ∈ radialSupport p := radial_noise_support hWpsd
  have hW := (ContinuousLinearMap.fst ℝ (SymmetricMatrix p) (EuclideanSpace ℝ (Fin p))).hasTemperateGrowth
  have hV := hasTemperateGrowth_radialInput_slice v r
  have hWu := symmetricMatrixAction.bilinear_hasTemperateGrowth hW
    (Function.HasTemperateGrowth.const u)
  have hH := (symmetricRankDirection v).hasTemperateGrowth.comp hWu
  have hL : Integrable (fun Y : RadialInputSpace p =>
      fderiv ℝ g (radialInput v r Y)
        (symmetricRankDirection v (symmetricMatrixAction Y.1 u))) μ :=
    ((hg.derivative.comp (PolynomialBoundOn.of_temperate hV) (radialInput_mapsTo v r)).clm_apply
      (PolynomialBoundOn.of_temperate hH)).integrable hμ
      (((hg.regular.continuous_fderiv (by norm_num)).comp hV.1.continuous).clm_apply
        hH.1.continuous).aestronglyMeasurable hsupport
  have hscore := ((innerSL ℝ u).hasTemperateGrowth.comp
    (symmetricMatrixAction.bilinear_hasTemperateGrowth hW
      (Function.HasTemperateGrowth.const (C⁻¹.toEuclideanLin v)))).sub
        (Function.HasTemperateGrowth.const (ν * ⟪u, v⟫))
  have hR : Integrable (fun Y : RadialInputSpace p =>
      (⟪u, symmetricMatrixAction Y.1 (C⁻¹.toEuclideanLin v)⟫ - ν * ⟪u, v⟫) *
        g (radialInput v r Y)) μ :=
    ((PolynomialBoundOn.of_temperate hscore).mul
      (hg.value.comp (PolynomialBoundOn.of_temperate hV) (radialInput_mapsTo v r))).integrable hμ
      (hscore.1.continuous.mul (hg.regular.continuous.comp hV.1.continuous)).aestronglyMeasurable hsupport
  rw [integral_prod_symm _ hL, integral_prod_symm _ hR]
  apply integral_congr_ae
  filter_upwards with z
  simpa only [radialInput] using
    hstein g hg (rankOneSymmetric (z + r • v)) (rankOneSymmetric_posSemidef _) u v

set_option backward.isDefEq.respectTransparency false in
include hC hμW hWpsd hstein in
/-- The integrated radial identity obtained from the two genuine first-order
Stein formulas.  The observable has only two derivatives. -/
theorem radial_generator_identity_of_stein_c2 {f : SymmetricMatrix p → ℝ}
    (hf : C2PolynomialOn (psdCone p) f)
    (v : EuclideanSpace ℝ (Fin p)) (r : ℝ) :
    r * (∫ Y : RadialInputSpace p, symmetricRadialGenerator (ν + 1) v f (radialInput v r Y)
      ∂μW.prod (multivariateGaussian 0 C)) =
    r * (∫ Y : RadialInputSpace p, radialSecondIntegrand f v r Y
      ∂μW.prod (multivariateGaussian 0 C)) +
    ν * (∫ Y : RadialInputSpace p, radialFirstIntegrand f v r Y
      ∂μW.prod (multivariateGaussian 0 C)) := by
  let μ := μW.prod (multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) C)
  let V := radialInput v r
  let gi := radialDerivativeTest f v
  let L : Fin p → RadialInputSpace p → ℝ := fun i Y =>
    fderiv ℝ (gi i) (V Y)
      (symmetricRankDirection v (symmetricMatrixAction Y.1 (coordinateVector i)))
  let Q : Fin p → RadialInputSpace p → ℝ := fun i Y =>
    ⟪coordinateVector i, symmetricMatrixAction Y.1 (C⁻¹.toEuclideanLin v)⟫ * gi i (V Y)
  let R : Fin p → RadialInputSpace p → ℝ := fun i Y =>
    (Y.2 + r • v) i * gi i (V Y)
  let B : RadialInputSpace p → ℝ := fun Y => fderiv ℝ f (V Y) (rankOneSymmetric v)
  have hμ : HasAllFiniteMoments (fun Y : RadialInputSpace p => ‖Y‖) μ :=
    allFiniteNormMoments_prod hμW allFiniteMoments_gaussian_norm
  have hsupport : ∀ᵐ Y ∂μ, Y ∈ radialSupport p := radial_noise_support hWpsd
  have hV := hasTemperateGrowth_radialInput_slice v r
  have hW := (ContinuousLinearMap.fst ℝ (SymmetricMatrix p) (EuclideanSpace ℝ (Fin p))).hasTemperateGrowth
  have hZ := (ContinuousLinearMap.snd ℝ (SymmetricMatrix p) (EuclideanSpace ℝ (Fin p))).hasTemperateGrowth
  have hgi (i : Fin p) : C1PolynomialOn (psdCone p) (gi i) := c1_radialDerivativeTest hf v i
  have hgiV (i : Fin p) := (hgi i).comp (C1PolynomialOn.of_temperate hV) (radialInput_mapsTo v r)
  have hgint (i : Fin p) : Integrable (fun Y => gi i (V Y)) μ :=
    (hgiV i).value.integrable hμ (hgiV i).regular.continuous.aestronglyMeasurable hsupport
  have hLint (i : Fin p) : Integrable (L i) μ := by
    have hH := (symmetricRankDirection v).hasTemperateGrowth.comp
      (symmetricMatrixAction.bilinear_hasTemperateGrowth hW
        (Function.HasTemperateGrowth.const (coordinateVector i)))
    exact (((hgi i).derivative.comp (PolynomialBoundOn.of_temperate hV)
      (radialInput_mapsTo v r)).clm_apply (PolynomialBoundOn.of_temperate hH)).integrable hμ
      ((((hgi i).regular.continuous_fderiv (by norm_num)).comp hV.1.continuous).clm_apply
        hH.1.continuous).aestronglyMeasurable hsupport
  have hQint (i : Fin p) : Integrable (Q i) μ := by
    have hcoeff := (innerSL ℝ (coordinateVector i)).hasTemperateGrowth.comp
      (symmetricMatrixAction.bilinear_hasTemperateGrowth hW
        (Function.HasTemperateGrowth.const (C⁻¹.toEuclideanLin v)))
    have ht := (C1PolynomialOn.of_temperate hcoeff).mul (hgiV i)
    exact ht.value.integrable hμ ht.regular.continuous.aestronglyMeasurable hsupport
  have hRint (i : Fin p) : Integrable (R i) μ := by
    have hcoeff := (innerSL ℝ (coordinateVector i)).hasTemperateGrowth.comp
      (hZ.add (Function.HasTemperateGrowth.const (r • v)))
    have ht := (C1PolynomialOn.of_temperate hcoeff).mul (hgiV i)
    simpa only [Function.comp_def, Pi.add_def, Pi.mul_def,
      ContinuousLinearMap.coe_snd', innerSL_apply_apply, coordinate_inner, R, gi, V] using
      ht.value.integrable hμ ht.regular.continuous.aestronglyMeasurable hsupport
  have hBint : Integrable B μ :=
    ((hf.derivative.comp (PolynomialBoundOn.of_temperate hV) (radialInput_mapsTo v r)).clm_apply
      (PolynomialBoundOn.const _ (rankOneSymmetric v))).integrable hμ
      (((hf.regular.continuous_fderiv (by norm_num)).comp hV.1.continuous).clm_apply
        continuous_const).aestronglyMeasurable hsupport
  have hsecond : Integrable (radialSecondIntegrand f v r) μ :=
    integrable_parameter_polynomialOn hμ hsupport (polynomial_radialSecondIntegrand_c2 hf v) r
      ((continuous_radialSecondIntegrand_c2 hf.regular v).comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hWi (i : Fin p) :
      (∫ Y, L i Y ∂μ) = (∫ Y, Q i Y ∂μ) - ν * v i * (∫ Y, gi i (V Y) ∂μ) := by
    have h := radial_background_stein_c1 hμW hWpsd hstein (hgi i) (coordinateVector i) v r
    simp only [sub_mul, coordinate_inner] at h
    have hQint' : Integrable (fun Y : RadialInputSpace p =>
        (symmetricMatrixAction Y.1 (C⁻¹.toEuclideanLin v)) i * gi i (V Y)) μ := by
      simpa only [Q, coordinate_inner] using hQint i
    change (∫ Y, L i Y ∂μ) = ∫ Y,
      (symmetricMatrixAction Y.1 (C⁻¹.toEuclideanLin v)) i * gi i (V Y) -
        ν * v i * gi i (V Y) ∂μ at h
    rw [integral_sub hQint' ((hgint i).const_mul (ν * v i)), integral_const_mul] at h
    simpa only [Q, coordinate_inner] using h
  have hRi (i : Fin p) : r * (∫ Y, Q i Y ∂μ) = ν * (∫ Y, R i Y ∂μ) := by
    simpa only [Q, R, gi, V, μ, coordinate_inner] using
      weighted_radial_stein_c1 hC hμW hWpsd hstein (hgi i) (coordinateVector i) v r
  have hLi (i : Fin p) :
      r * (∫ Y, L i Y ∂μ) + r * ν * v i * (∫ Y, gi i (V Y) ∂μ) =
        ν * (∫ Y, R i Y ∂μ) := by
    rw [hWi]
    nlinarith [hRi i]
  have hsum := congrArg (fun a : Fin p → ℝ => ∑ i, a i) (funext hLi)
  have hLpoint (Y : RadialInputSpace p) :
      (∑ i, L i Y) = radialCovarianceContraction f (V Y) v
        (Y.1 : Matrix (Fin p) (Fin p) ℝ) := by
    rw [radialCovarianceContraction_eq_directional_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact (symmetricSecondDerivative_eq_c2 hf.regular _ _ _).symm
  have hRpoint (Y : RadialInputSpace p) :
      (∑ i, R i Y) = radialFirstIntegrand f v r Y :=
    (radialFirstIntegrand_eq_coordinate_sum f v r Y).symm
  have hBpoint (Y : RadialInputSpace p) :
      (∑ i, v i * gi i (V Y)) = 2 * B Y := sum_radialDerivativeTest f v (V Y)
  have hLsum : (∑ i, ∫ Y, L i Y ∂μ) =
      ∫ Y, radialCovarianceContraction f (V Y) v (Y.1 : Matrix (Fin p) (Fin p) ℝ) ∂μ := by
    rw [← integral_finsetSum _ (fun i _ => hLint i)]
    exact integral_congr_ae (Eventually.of_forall hLpoint)
  have hRsum : (∑ i, ∫ Y, R i Y ∂μ) = ∫ Y, radialFirstIntegrand f v r Y ∂μ := by
    rw [← integral_finsetSum _ (fun i _ => hRint i)]
    exact integral_congr_ae (Eventually.of_forall hRpoint)
  have hBsum : (∑ i, v i * (∫ Y, gi i (V Y) ∂μ)) = 2 * (∫ Y, B Y ∂μ) := by
    simp_rw [← integral_const_mul]
    rw [← integral_finsetSum _ (fun i _ => (hgint i).const_mul (v i))]
    rw [integral_congr_ae (Eventually.of_forall hBpoint), integral_const_mul]
  have hcovint : Integrable (fun Y =>
      radialCovarianceContraction f (V Y) v (Y.1 : Matrix (Fin p) (Fin p) ℝ)) μ :=
    (integrable_finsetSum _ (fun i _ => hLint i)).congr (Eventually.of_forall hLpoint)
  have hgen :
      (∫ Y, symmetricRadialGenerator (ν + 1) v f (V Y) ∂μ) =
        (∫ Y, radialSecondIntegrand f v r Y ∂μ) +
        (∫ Y, radialCovarianceContraction f (V Y) v
          (Y.1 : Matrix (Fin p) (Fin p) ℝ) ∂μ) +
        2 * ν * (∫ Y, B Y ∂μ) := by
    simp_rw [V, symmetricRadialGenerator_decomposition]
    have hsumInt : Integrable (fun Y => radialSecondIntegrand f v r Y +
        radialCovarianceContraction f (V Y) v (Y.1 : Matrix (Fin p) (Fin p) ℝ)) μ := by
      simpa only [Pi.add_def] using hsecond.add hcovint
    change (∫ Y, (radialSecondIntegrand f v r Y +
        radialCovarianceContraction f (V Y) v (Y.1 : Matrix (Fin p) (Fin p) ℝ)) +
        2 * (ν + 1 - 1) * B Y ∂μ) = _
    rw [integral_add hsumInt (hBint.const_mul (2 * (ν + 1 - 1))),
      integral_add hsecond hcovint, integral_const_mul]
    ring
  change r * (∫ Y, symmetricRadialGenerator (ν + 1) v f (V Y) ∂μ) = _
  rw [hgen]
  simp only [Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum] at hsum
  rw [hLsum, hRsum] at hsum
  have hBsum' : (∑ i, v i * ∫ Y, gi i (V Y) ∂μ) = 2 * ∫ Y, B Y ∂μ := hBsum
  rw [hBsum'] at hsum
  nlinarith

end Background

end Wishart.FiniteOrder
