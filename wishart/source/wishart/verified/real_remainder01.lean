module

public import wishart.verified.real_core_extensions
public import tau_ceti.probability.distributions.wishart.low_dimension
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/- Generated ordinary proof stage. See audit/staged_real_remainder/RealRemainder01/manifest.json. -/

@[expose] public section

section CanonicalSource0
/- Source: Wishart/DeterminantTilts.lean -/



/-!
# Exact real-degree determinant tilts of the Wishart law

Multiplication by `det(X)^r` changes the degree from `α` to `α+2r`.
Both parameters are kept inside their genuine probability ranges.  The law
identity supplies integrability and the exact multivariate-gamma moment;
neither is introduced as an unproved special-function evaluation.
-/

open Matrix MeasureTheory TauCeti TauCeti.Probability WishartVerification
open scoped Classical ENNReal MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace Wishart

def wishartDenominator {p : ℕ} (α : ℝ) (S : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  (2 : ℝ) ^ (α * (p : ℝ) / 2) * S.det ^ (α / 2) * multivariateGamma p (α / 2)

theorem wishartDenominator_pos {p : ℕ} {α : ℝ} {S : Matrix (Fin p) (Fin p) ℝ}
    (hS : S.PosDef) (hα : (p : ℝ) - 1 < α) : 0 < wishartDenominator α S :=
  mul_pos (mul_pos (Real.rpow_pos_of_pos two_pos _) (Real.rpow_pos_of_pos hS.det_pos _))
    (multivariateGamma_pos (by linarith))

def wishartDetTiltConstant {p : ℕ} (α : ℝ) (S : Matrix (Fin p) (Fin p) ℝ) (r : ℝ) : ℝ :=
  wishartDenominator (α + 2 * r) S / wishartDenominator α S

theorem wishartDetTiltConstant_pos {p : ℕ} {α r : ℝ}
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef)
    (hα : (p : ℝ) - 1 < α) (hr : (p : ℝ) - 1 < α + 2 * r) :
    0 < wishartDetTiltConstant α S r :=
  div_pos (wishartDenominator_pos hS hr) (wishartDenominator_pos hS hα)

theorem wishartPDFReal_mul_det_rpow {p : ℕ} {α r : ℝ}
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef)
    (hα : (p : ℝ) - 1 < α) (hr : (p : ℝ) - 1 < α + 2 * r)
    (X : SymmetricMatrix p) :
    nonsingularWishartPDFReal α S X * (X : Matrix (Fin p) (Fin p) ℝ).det ^ r =
      wishartDetTiltConstant α S r * nonsingularWishartPDFReal (α + 2 * r) S X := by
  by_cases hX : (X : Matrix (Fin p) (Fin p) ℝ).PosDef
  · rw [nonsingularWishartPDFReal_of_posDef α S hX,
      nonsingularWishartPDFReal_of_posDef (α + 2 * r) S hX]
    have hexp : (α + 2 * r - (p : ℝ) - 1) / 2 = (α - (p : ℝ) - 1) / 2 + r := by ring
    rw [hexp, Real.rpow_add hX.det_pos]
    change (_ / wishartDenominator α S) * _ =
      (wishartDenominator (α + 2 * r) S / wishartDenominator α S) *
        (_ / wishartDenominator (α + 2 * r) S)
    field_simp [(wishartDenominator_pos hS hα).ne', (wishartDenominator_pos hS hr).ne']
  · rw [nonsingularWishartPDFReal_of_not_posDef α S hX,
      nonsingularWishartPDFReal_of_not_posDef (α + 2 * r) S hX, zero_mul, mul_zero]

/-- Equality of the entire tilted measures, with their actual finite positive
normalization constant. -/
theorem withDensity_wishart_det_rpow {p : ℕ} {α r : ℝ}
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef)
    (hα : (p : ℝ) - 1 < α) (hr : (p : ℝ) - 1 < α + 2 * r) :
    (nonsingularWishartMeasure α S).withDensity
        (fun X : SymmetricMatrix p => ENNReal.ofReal ((X : Matrix (Fin p) (Fin p) ℝ).det ^ r)) =
      ENNReal.ofReal (wishartDetTiltConstant α S r) • nonsingularWishartMeasure (α + 2 * r) S := by
  rw [nonsingularWishartMeasure_of_posDef hS hα,
    nonsingularWishartMeasure_of_posDef hS hr,
    ← withDensity_mul _ (measurable_nonsingularWishartPDF α S) (by fun_prop)]
  have hd : (nonsingularWishartPDF α S *
      (fun X : SymmetricMatrix p => ENNReal.ofReal ((X : Matrix (Fin p) (Fin p) ℝ).det ^ r))) =
      (fun X => ENNReal.ofReal (wishartDetTiltConstant α S r) *
        nonsingularWishartPDF (α + 2 * r) S X) := by
    funext X
    rw [Pi.mul_apply, nonsingularWishartPDF_def,
      ← ENNReal.ofReal_mul (nonsingularWishartPDFReal_nonneg hS hα X),
      wishartPDFReal_mul_det_rpow hS hα hr X,
      ENNReal.ofReal_mul (wishartDetTiltConstant_pos hS hα hr).le,
      nonsingularWishartPDF_def]
  rw [hd]
  simpa only [Pi.smul_def, smul_eq_mul] using
    (withDensity_smul (μ := symmetricLebesgue p)
      (ENNReal.ofReal (wishartDetTiltConstant α S r))
      (measurable_nonsingularWishartPDF (α + 2 * r) S))

theorem integrable_wishart_det_rpow_mul {p : ℕ} {α r : ℝ}
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef)
    (hα : (p : ℝ) - 1 < α) (hr : (p : ℝ) - 1 < α + 2 * r)
    {f : SymmetricMatrix p → ℝ} (hf : Integrable f (nonsingularWishartMeasure (α + 2 * r) S)) :
    Integrable (fun X : SymmetricMatrix p => (X : Matrix (Fin p) (Fin p) ℝ).det ^ r * f X)
      (nonsingularWishartMeasure α S) := by
  have htilt : Integrable f ((nonsingularWishartMeasure α S).withDensity
      (fun X : SymmetricMatrix p => ENNReal.ofReal ((X : Matrix (Fin p) (Fin p) ℝ).det ^ r))) := by
    rw [withDensity_wishart_det_rpow hS hα hr]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  have hweighted := (integrable_withDensity_iff_integrable_smul'
    (by fun_prop) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)).mp htilt
  apply hweighted.congr
  filter_upwards [ae_posDef_nonsingularWishartMeasure α S] with X hX
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hX.det_pos.le _), smul_eq_mul]

theorem integral_wishart_det_rpow_mul {p : ℕ} {α r : ℝ}
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef)
    (hα : (p : ℝ) - 1 < α) (hr : (p : ℝ) - 1 < α + 2 * r)
    (f : SymmetricMatrix p → ℝ) :
    (∫ X, (X : Matrix (Fin p) (Fin p) ℝ).det ^ r * f X
      ∂nonsingularWishartMeasure α S) =
      wishartDetTiltConstant α S r * ∫ X, f X ∂nonsingularWishartMeasure (α + 2 * r) S := by
  have hae : (fun X : SymmetricMatrix p =>
      (ENNReal.ofReal ((X : Matrix (Fin p) (Fin p) ℝ).det ^ r)).toReal • f X) =ᵐ[
        nonsingularWishartMeasure α S]
      (fun X => (X : Matrix (Fin p) (Fin p) ℝ).det ^ r * f X) := by
    filter_upwards [ae_posDef_nonsingularWishartMeasure α S] with X hX
    rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hX.det_pos.le _), smul_eq_mul]
  rw [← integral_congr_ae hae,
    ← integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
    withDensity_wishart_det_rpow hS hα hr, integral_smul_measure,
    ENNReal.toReal_ofReal (wishartDetTiltConstant_pos hS hα hr).le, smul_eq_mul]

theorem wishartDetTiltConstant_eq_gamma_ratio {p : ℕ} {α r : ℝ}
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef) (hα : (p : ℝ) - 1 < α) :
    wishartDetTiltConstant α S r =
      (2 : ℝ) ^ ((p : ℝ) * r) * S.det ^ r *
        (multivariateGamma p (α / 2 + r) / multivariateGamma p (α / 2)) := by
  have he : (α + 2 * r) / 2 = α / 2 + r := by ring
  have hep : (α + 2 * r) * (p : ℝ) / 2 = α * (p : ℝ) / 2 + (p : ℝ) * r := by ring
  rw [wishartDetTiltConstant, wishartDenominator, wishartDenominator,
    he, hep, Real.rpow_add two_pos, Real.rpow_add hS.det_pos]
  field_simp [(Real.rpow_pos_of_pos two_pos (α * (p : ℝ) / 2)).ne',
    (Real.rpow_pos_of_pos hS.det_pos (α / 2)).ne',
    (multivariateGamma_pos (p := p) (by linarith : ((p : ℝ) - 1) / 2 < α / 2)).ne']

theorem integrable_det_rpow_wishart {p : ℕ} {α r : ℝ}
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef)
    (hα : (p : ℝ) - 1 < α) (hr : (p : ℝ) - 1 < α + 2 * r) :
    Integrable (fun X : SymmetricMatrix p => (X : Matrix (Fin p) (Fin p) ℝ).det ^ r)
      (nonsingularWishartMeasure α S) := by
  letI := isProbabilityMeasure_nonsingularWishartMeasure hS hr
  simpa only [mul_one] using integrable_wishart_det_rpow_mul hS hα hr (integrable_const (1 : ℝ))

theorem integral_det_rpow_wishart {p : ℕ} {α r : ℝ}
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef)
    (hα : (p : ℝ) - 1 < α) (hr : (p : ℝ) - 1 < α + 2 * r) :
    (∫ X : SymmetricMatrix p, (X : Matrix (Fin p) (Fin p) ℝ).det ^ r
      ∂nonsingularWishartMeasure α S) =
      (2 : ℝ) ^ ((p : ℝ) * r) * S.det ^ r *
        (multivariateGamma p (α / 2 + r) / multivariateGamma p (α / 2)) := by
  letI := isProbabilityMeasure_nonsingularWishartMeasure hS hr
  simpa only [mul_one, integral_const, probReal_univ, one_smul,
    wishartDetTiltConstant_eq_gamma_ratio hS hα] using
    integral_wishart_det_rpow_mul hS hα hr (fun _ => (1 : ℝ))

end Wishart
end
end CanonicalSource0

section CanonicalSource1
/- Source: Wishart/InverseCompressionMarginal.lean -/



/-!
# The full matrix law of every inverse-Wishart compression

The degree shift `β-p+k` is derived from affine regression, after the exact
normalization of an arbitrary full-column-rank matrix.  The conclusion is an
equality of full matrix measures, not just a diagonal or determinant marginal.
-/

open Matrix MeasureTheory TauCeti TauCeti.Probability
open scoped Classical MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace Wishart

theorem map_compression_inverseWishartMeasure {p k : ℕ} {β : ℝ}
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (hβ : (p : ℝ) - 1 < β) (B : Matrix (Fin p) (Fin k) ℝ) (hB : B.rank = k) :
    (inverseWishartMeasure β Omega).map (Matrix.symmetricCongruenceLinearMap Bᵀ) =
      inverseWishartMeasure (β - p + k) (compressionScale Omega B) := by
  have hkp : k ≤ p := by rw [← hB]; exact B.rank_le_height
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkp
  let N := compressionNormalization hOmega B hB
  let T := CFC.sqrt (compressionScale Omega B)
  have hG := compressionScale_posDef hOmega B hB
  have hT : T.det ≠ 0 := sqrt_det_ne_zero_of_posDef hG
  have hTT : T * Tᵀ = compressionScale Omega B := by
    rw [matrix_sqrt_transpose]
    exact CFC.sqrt_mul_sqrt_self _ hG.posSemidef.nonneg
  have hE : Fin.castLE N.q_le = Fin.castAdd m := by
    funext i
    apply Fin.ext
    rfl
  have hfun : (Matrix.symmetricCongruenceLinearMap Bᵀ :
        SymmetricMatrix (k + m) → SymmetricMatrix k) ∘
      Matrix.symmetricCongruenceLinearMap N.ambient =
        Matrix.symmetricCongruenceLinearMap T ∘ principalSymmetricBlock (Fin.castAdd m) := by
    rw [principalSymmetricBlock_eq_congruence]
    funext Y
    simp only [Function.comp_apply, ← LinearMap.comp_apply,
      ← Matrix.symmetricCongruenceLinearMap_mul]
    rw [N.selected, hE]
  have hAmeas : Measurable (Matrix.symmetricCongruenceLinearMap N.ambient) :=
    (LinearMap.continuous_of_finiteDimensional _).measurable
  have hBmeas : Measurable (Matrix.symmetricCongruenceLinearMap Bᵀ) :=
    (LinearMap.continuous_of_finiteDimensional _).measurable
  have hTmeas : Measurable (Matrix.symmetricCongruenceLinearMap T) :=
    (LinearMap.continuous_of_finiteDimensional _).measurable
  rw [← map_inverseCompressionNormalization β N, Measure.map_map hBmeas hAmeas,
    hfun, ← Measure.map_map hTmeas (measurable_principalSymmetricBlock _),
    map_selectedBlock_identityInverseWishart hβ,
    map_symmetricCongruenceLinearMap_inverseWishartMeasure_of_det_ne_zero (β - m) 1 T hT,
    Matrix.mul_one, hTT]
  congr 1
  push_cast
  ring

theorem map_normalizedCompression_inverseWishartMeasure {p k : ℕ} {β : ℝ}
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (hβ : (p : ℝ) - 1 < β) (B : Matrix (Fin p) (Fin k) ℝ) (hB : B.rank = k) :
    (inverseWishartMeasure β Omega).map (normalizedCompression Omega B) =
      inverseWishartMeasure (β - p + k) (1 : Matrix (Fin k) (Fin k) ℝ) := by
  have hG := compressionScale_posDef hOmega B hB
  let R := (CFC.sqrt (compressionScale Omega B))⁻¹
  have hR : R.det ≠ 0 := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    exact inv_ne_zero (sqrt_det_ne_zero_of_posDef hG)
  have hfun : normalizedCompression Omega B =
      (Matrix.symmetricCongruenceLinearMap R : SymmetricMatrix k → SymmetricMatrix k) ∘
        Matrix.symmetricCongruenceLinearMap Bᵀ := by
    funext X
    unfold normalizedCompression normalizedCompressionRows
    rw [Matrix.symmetricCongruenceLinearMap_mul]
    rfl
  rw [hfun, ← Measure.map_map
    (LinearMap.continuous_of_finiteDimensional _).measurable
    (LinearMap.continuous_of_finiteDimensional _).measurable,
    map_compression_inverseWishartMeasure hOmega hβ B hB,
    map_symmetricCongruenceLinearMap_inverseWishartMeasure_of_det_ne_zero _ _ R hR]
  rw [(inverseSqrt_properties hG).2.1]

end Wishart
end
end CanonicalSource1

section CanonicalSource2
/- Source: Wishart/ScalarRegression.lean -/



/-!
# The scalar selected-block regression law

For N > r, a chi-squared variable t of degree N, an independent standard
r-dimensional Gaussian z, and an independent W_r(N-1,I) matrix W give the full
W_(1+r)(N,I) law through [[t,sqrt(t)zᵀ],[sqrt(t)z,W+zzᵀ]]. This realizes the
transverse mean-shift model in the radial identity as an actual conditional
Wishart representation, throughout the admissible real-shape range.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace Wishart

abbrev ScalarRegressionNoise (r : ℕ) := EuclideanSpace ℝ (Fin r) × SymmetricMatrix r

def scalarRegressionNoiseMeasure (N : ℝ) (r : ℕ) : Measure (ScalarRegressionNoise r) :=
  (multivariateGaussian (0 : EuclideanSpace ℝ (Fin r)) 1).prod
    (nonsingularWishartMeasure (N - 1) (1 : Matrix (Fin r) (Fin r) ℝ))

instance isFiniteMeasure_scalarRegressionNoiseMeasure (N : ℝ) (r : ℕ) :
    IsFiniteMeasure (scalarRegressionNoiseMeasure N r) := by
  unfold scalarRegressionNoiseMeasure
  infer_instance

def scalarRegressionData {r : ℕ} (x : ℝ × ScalarRegressionNoise r) :
    RegressionData 1 r :=
  (symmetricFinOneEquiv.symm x.1, ((fun _ => x.2.1), x.2.2))

def scalarRegressionMatrix {r : ℕ} (t : ℝ) (x : ScalarRegressionNoise r) :
    SymmetricMatrix (1 + r) :=
  regressionReconstruction (0 : Matrix (Fin 1) (Fin r) ℝ)
    (scalarRegressionData (t, x))

@[fun_prop] theorem measurable_scalarRegressionData {r : ℕ} :
    Measurable (scalarRegressionData (r := r)) := by
  unfold scalarRegressionData
  fun_prop

@[fun_prop] theorem measurable_scalarRegressionMatrix {r : ℕ} :
    Measurable (Function.uncurry (scalarRegressionMatrix (r := r))) :=
  (measurable_regressionReconstruction 0).comp measurable_scalarRegressionData

theorem map_chiSquared_symmetricFinOneEquiv_symm {N : ℝ} (hN : 0 < N) :
    (chiSquaredMeasure N).map symmetricFinOneEquiv.symm =
      nonsingularWishartMeasure N (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  have hforward : (nonsingularWishartMeasure N (1 : Matrix (Fin 1) (Fin 1) ℝ)).map
      symmetricFinOneEquiv = chiSquaredMeasure N := by
    simpa only [Matrix.one_apply_eq, one_mul, Measure.map_id'] using
      map_symmetricFinOneEquiv_nonsingularWishartMeasure hN
        (S := (1 : Matrix (Fin 1) (Fin 1) ℝ)) (by simp)
  rw [← hforward, Measure.map_map symmetricFinOneEquiv.symm.continuous.measurable
    symmetricFinOneEquiv.continuous.measurable]
  have hfun : (symmetricFinOneEquiv.symm : ℝ → SymmetricMatrix 1) ∘
      symmetricFinOneEquiv = id :=
    funext fun X => symmetricFinOneEquiv.symm_apply_apply X
  rw [hfun, Measure.map_id]

theorem measurePreserving_scalarRegressionData {N : ℝ} {r : ℕ} (hNr : (r : ℝ) < N) :
    MeasurePreserving (scalarRegressionData (r := r))
      ((chiSquaredMeasure N).prod (scalarRegressionNoiseMeasure N r))
      (regressionDataMeasure N 1 r 1) := by
  have hN : 0 < N := (Nat.cast_nonneg r).trans_lt hNr
  letI := isProbabilityMeasure_chiSquaredMeasure hN.le
  letI := isProbabilityMeasure_nonsingularWishartMeasure
    (S := (1 : Matrix (Fin r) (Fin r) ℝ)) Matrix.PosDef.one
    (show (r : ℝ) - 1 < N - 1 by linarith)
  have hS : MeasurePreserving symmetricFinOneEquiv.symm (chiSquaredMeasure N)
      (nonsingularWishartMeasure N (1 : Matrix (Fin 1) (Fin 1) ℝ)) :=
    ⟨symmetricFinOneEquiv.symm.continuous.measurable,
      map_chiSquared_symmetricFinOneEquiv_symm hN⟩
  have hz : MeasurePreserving
      (fun z : EuclideanSpace ℝ (Fin r) => fun _ : Fin 1 => z)
      (multivariateGaussian 0 (1 : Matrix (Fin r) (Fin r) ℝ))
      (Measure.pi (fun _ : Fin 1 =>
        multivariateGaussian (0 : EuclideanSpace ℝ (Fin r)) 1)) := by
    have h := MeasurePreserving.symm
      (MeasurableEquiv.funUnique (Fin 1) (EuclideanSpace ℝ (Fin r)))
      (measurePreserving_funUnique (multivariateGaussian 0
        (1 : Matrix (Fin r) (Fin r) ℝ)) (Fin 1))
    have heq :
        ((MeasurableEquiv.funUnique (Fin 1) (EuclideanSpace ℝ (Fin r))).symm :
            EuclideanSpace ℝ (Fin r) → Fin 1 → EuclideanSpace ℝ (Fin r)) =
          fun z _ => z := by
      funext z i
      exact @uniqueElim_const (Fin 1) (EuclideanSpace ℝ (Fin r)) inferInstance z i
    rw [heq] at h
    exact h
  have hdata := hS.prod (hz.prod (MeasurePreserving.id
    (nonsingularWishartMeasure (N - 1) (1 : Matrix (Fin r) (Fin r) ℝ))))
  have hfun :
      (Prod.map (symmetricFinOneEquiv.symm : ℝ → SymmetricMatrix 1)
        (Prod.map (fun z : EuclideanSpace ℝ (Fin r) => fun _ : Fin 1 => z) id)) =
      (scalarRegressionData : ℝ × ScalarRegressionNoise r → RegressionData 1 r) := by
    funext x
    rfl
  rw [hfun] at hdata
  simpa only [scalarRegressionNoiseMeasure, regressionDataMeasure, Nat.cast_one] using hdata

@[simp] theorem regressionScale_zero_one (q r : ℕ) :
    regressionScale (0 : Matrix (Fin q) (Fin r) ℝ) 1 = 1 := by
  simp [regressionScale, Matrix.fromBlocks_one]

/-- The full matrix law in the scalar regression model. -/
theorem map_scalarRegressionMatrix {N : ℝ} {r : ℕ} (hN : (r : ℝ) < N) :
    ((chiSquaredMeasure N).prod (scalarRegressionNoiseMeasure N r)).map
        (Function.uncurry scalarRegressionMatrix) =
      nonsingularWishartMeasure N (1 : Matrix (Fin (1 + r)) (Fin (1 + r)) ℝ) := by
  have hNpos : 0 < N := (Nat.cast_nonneg r).trans_lt hN
  have hdegree : (((1 + r : ℕ) : ℝ) - 1) < N := by
    push_cast
    linarith
  have hdata := (measurePreserving_scalarRegressionData hN).map_eq
  have hfun : Function.uncurry (scalarRegressionMatrix (r := r)) =
      regressionReconstruction (0 : Matrix (Fin 1) (Fin r) ℝ) ∘
        scalarRegressionData := rfl
  rw [hfun, ← Measure.map_map (measurable_regressionReconstruction 0)
    measurable_scalarRegressionData, hdata,
    map_regressionReconstruction hdegree 0 Matrix.PosDef.one,
    regressionScale_zero_one]

theorem sqrt_symmetricFinOneEquiv_symm {t : ℝ} (ht : 0 ≤ t) :
    CFC.sqrt ((symmetricFinOneEquiv.symm t : SymmetricMatrix 1) :
        Matrix (Fin 1) (Fin 1) ℝ) =
      ((symmetricFinOneEquiv.symm (Real.sqrt t) : SymmetricMatrix 1) :
        Matrix (Fin 1) (Fin 1) ℝ) := by
  apply CFC.sqrt_unique
  · ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.mul_apply, Real.mul_self_sqrt ht]
  · have hdiag : ((symmetricFinOneEquiv.symm (Real.sqrt t) : SymmetricMatrix 1) :
        Matrix (Fin 1) (Fin 1) ℝ) = Matrix.diagonal (fun _ => Real.sqrt t) := by
      ext i j
      fin_cases i
      fin_cases j
      simp
    rw [hdiag]
    exact (Matrix.PosSemidef.diagonal (fun _ => Real.sqrt_nonneg t)).nonneg

/-- A version of the conditional matrix with every entry displayed. -/
theorem scalarRegressionMatrix_submatrix {r : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (x : ScalarRegressionNoise r) :
    ((scalarRegressionMatrix t x : SymmetricMatrix (1 + r)) :
        Matrix (Fin (1 + r)) (Fin (1 + r)) ℝ).submatrix
          finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks
        (Matrix.of (fun _ _ : Fin 1 => t))
        (Matrix.of (fun (_ : Fin 1) j => Real.sqrt t * x.1 j))
        (Matrix.of (fun i (_ : Fin 1) => x.1 i * Real.sqrt t))
        (Matrix.of (fun i j => x.1 i * x.1 j +
          (x.2 : Matrix (Fin r) (Fin r) ℝ) i j)) := by
  rw [scalarRegressionMatrix, regressionReconstruction_submatrix]
  simp only [scalarRegressionData, Matrix.transpose_zero, Matrix.zero_mul,
    zero_add, sqrt_symmetricFinOneEquiv_symm ht, regressionBlockMatrix]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.mul_apply, Matrix.transpose_apply, Real.mul_self_sqrt ht]

/-- The distinguished matrix entry is literally the radial parameter. -/
theorem scalarRegressionMatrix_selected {r : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (x : ScalarRegressionNoise r) :
    ((scalarRegressionMatrix t x : SymmetricMatrix (1 + r)) :
      Matrix (Fin (1 + r)) (Fin (1 + r)) ℝ)
        (Fin.castAdd r 0) (Fin.castAdd r 0) = t := by
  have h := congrArg
    (fun A : Matrix (Fin 1 ⊕ Fin r) (Fin 1 ⊕ Fin r) ℝ => A (.inl 0) (.inl 0))
    (scalarRegressionMatrix_submatrix ht x)
  simpa only [Matrix.submatrix_apply, finSumFinEquiv_apply_left,
    Matrix.fromBlocks_apply₁₁, Matrix.of_apply] using h

end Wishart
end
end CanonicalSource2

section CanonicalSource3
/- Source: Wishart/ScalarRegressionGeometry.lean -/



/-!
# The transverse radial model inside scalar Wishart regression

The covariance is the actual matrix diag(0,I_r), of exact rank r. The Gaussian
noise is its rectangular linear image, and the scalar conditional matrix is
the embedded residual plus the rank-one shifted Gaussian outer product.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace Wishart

def scalarNoiseMatrix (r : ℕ) : Matrix (Fin (1 + r)) (Fin r) ℝ :=
  (Matrix.fromRows (0 : Matrix (Fin 1) (Fin r) ℝ) 1).submatrix
    finSumFinEquiv.symm (Equiv.refl (Fin r))

def scalarTransverseCovariance (r : ℕ) : Matrix (Fin (1 + r)) (Fin (1 + r)) ℝ :=
  scalarNoiseMatrix r * (scalarNoiseMatrix r)ᵀ

def scalarTransverseAxis (r : ℕ) : EuclideanSpace ℝ (Fin (1 + r)) :=
  WithLp.toLp 2 (Sum.elim (fun _ : Fin 1 => (1 : ℝ))
    (fun _ : Fin r => (0 : ℝ)) ∘ finSumFinEquiv.symm)

@[simp] theorem scalarNoiseMatrix_castAdd (r : ℕ) (i : Fin 1) (j : Fin r) :
    scalarNoiseMatrix r (Fin.castAdd r i) j = 0 := by
  simp [scalarNoiseMatrix]

@[simp] theorem scalarNoiseMatrix_natAdd (r : ℕ) (i j : Fin r) :
    scalarNoiseMatrix r (Fin.natAdd 1 i) j = (1 : Matrix (Fin r) (Fin r) ℝ) i j := by
  simp [scalarNoiseMatrix]

@[simp] theorem scalarTransverseAxis_castAdd (r : ℕ) (i : Fin 1) :
    scalarTransverseAxis r (Fin.castAdd r i) = 1 := by
  simp [scalarTransverseAxis]

@[simp] theorem scalarTransverseAxis_natAdd (r : ℕ) (i : Fin r) :
    scalarTransverseAxis r (Fin.natAdd 1 i) = 0 := by
  simp [scalarTransverseAxis]

theorem scalarTransverseAxis_ne_zero (r : ℕ) : scalarTransverseAxis r ≠ 0 := by
  intro h
  have hzero := congrArg (fun v : EuclideanSpace ℝ (Fin (1 + r)) => v (Fin.castAdd r 0)) h
  exact one_ne_zero (by simpa only [scalarTransverseAxis_castAdd, PiLp.zero_apply] using hzero)

@[simp] theorem scalarNoiseMatrix_gram (r : ℕ) :
    (scalarNoiseMatrix r)ᵀ * scalarNoiseMatrix r = 1 := by
  simpa only [scalarNoiseMatrix, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv,
    Matrix.transpose_fromRows, Matrix.transpose_zero, Matrix.transpose_one,
    Matrix.fromCols_mul_fromRows, Matrix.zero_mul, Matrix.one_mul, zero_add,
    Equiv.coe_refl, Matrix.submatrix_id_id]

theorem scalarTransverseCovariance_blocks (r : ℕ) :
    scalarTransverseCovariance r =
      (Matrix.fromBlocks (0 : Matrix (Fin 1) (Fin 1) ℝ) 0 0
        (1 : Matrix (Fin r) (Fin r) ℝ)).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm := by
  simp only [scalarTransverseCovariance, scalarNoiseMatrix, Matrix.transpose_submatrix,
    Matrix.submatrix_mul_equiv, Matrix.transpose_fromRows, Matrix.transpose_zero,
    Matrix.transpose_one, Matrix.fromRows_mul_fromCols, Matrix.zero_mul,
    Matrix.mul_zero, Matrix.one_mul]

theorem scalarTransverseCovariance_posSemidef (r : ℕ) :
    (scalarTransverseCovariance r).PosSemidef := by
  simpa only [scalarTransverseCovariance, Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_self_mul_conjTranspose (scalarNoiseMatrix r)

theorem scalarTransverseCovariance_rank (r : ℕ) :
    (scalarTransverseCovariance r).rank = r := by
  rw [scalarTransverseCovariance, Matrix.rank_self_mul_transpose,
    ← Matrix.rank_transpose_mul_self, scalarNoiseMatrix_gram,
    Matrix.rank_one, Fintype.card_fin]

@[simp] theorem scalarNoiseMatrix_apply_castAdd (r : ℕ)
    (z : EuclideanSpace ℝ (Fin r)) (i : Fin 1) :
    (scalarNoiseMatrix r).toEuclideanLin z (Fin.castAdd r i) = 0 := by
  simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]

@[simp] theorem scalarNoiseMatrix_apply_natAdd (r : ℕ)
    (z : EuclideanSpace ℝ (Fin r)) (i : Fin r) :
    (scalarNoiseMatrix r).toEuclideanLin z (Fin.natAdd 1 i) = z i := by
  simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Matrix.one_apply]

/-- The embedded noise has precisely the singular Gaussian covariance used in
the transverse radial argument. -/
theorem map_scalarNoiseMatrix_gaussian (r : ℕ) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin r)) 1).map
        (scalarNoiseMatrix r).toEuclideanLin =
      multivariateGaussian 0 (scalarTransverseCovariance r) := by
  simpa only [map_zero, add_zero, Matrix.mul_one, scalarTransverseCovariance] using
    map_affine_multivariateGaussian (0 : EuclideanSpace ℝ (Fin r))
      Matrix.PosSemidef.one (scalarNoiseMatrix r) 0

theorem scalarResidualMatrix_blocks {r : ℕ} (W : SymmetricMatrix r) :
    ((Matrix.symmetricCongruenceLinearMap (scalarNoiseMatrix r) W :
        SymmetricMatrix (1 + r)) : Matrix (Fin (1 + r)) (Fin (1 + r)) ℝ) =
      (Matrix.fromBlocks (0 : Matrix (Fin 1) (Fin 1) ℝ) 0 0
        (W : Matrix (Fin r) (Fin r) ℝ)).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm := by
  rw [Matrix.coe_symmetricCongruenceLinearMap_apply]
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [scalarNoiseMatrix, Matrix.mul_apply, Matrix.submatrix_apply,
      Matrix.transpose_apply, Matrix.one_apply]

/-- The conditional matrix is exactly a residual plus a Gaussian outer
product with transverse mean sqrt(t)e₀. This equality is on actual symmetric
matrices, not merely on their selected blocks or their eigenvalues. -/
theorem scalarRegressionMatrix_eq_rankOne {r : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (x : ScalarRegressionNoise r) :
    scalarRegressionMatrix t x =
      Matrix.symmetricCongruenceLinearMap (scalarNoiseMatrix r) x.2 +
        WishartVerification.rankOneSymmetric
          ((scalarNoiseMatrix r).toEuclideanLin x.1 +
            Real.sqrt t • scalarTransverseAxis r) := by
  apply Subtype.ext
  apply Matrix.submatrix_injective finSumFinEquiv.surjective finSumFinEquiv.surjective
  change (scalarRegressionMatrix t x : Matrix (Fin (1 + r)) (Fin (1 + r)) ℝ).submatrix
    finSumFinEquiv finSumFinEquiv = _
  rw [scalarRegressionMatrix_submatrix ht x]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [scalarResidualMatrix_blocks, WishartVerification.coe_rankOneSymmetric,
      scalarNoiseMatrix, scalarTransverseAxis, Matrix.vecMulVec,
      Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.one_apply,
      Matrix.submatrix_apply, Real.mul_self_sqrt ht, add_comm]

end Wishart
end
end CanonicalSource3

section CanonicalSource4
/- Source: Wishart/WishartStationarity.lean -/



/-!
# The stationary radial generator under the actual Wishart law

Summing the proved congruence Stein identity over coordinate derivative tests
gives the second-order identity. This is valid for every admissible real shape.
It is used with a compact scalar test of the first diagonal entry to obtain
the transverse, singular-covariance radial equation by scalar regression.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti.Probability Matrix
open WishartVerification
open scoped RealInnerProductSpace BigOperators

namespace Wishart

set_option backward.isDefEq.respectTransparency false in
theorem hasTemperateGrowth_symmetricRadialGenerator {p : ℕ}
    {f : SymmetricMatrix p → ℝ} (hf : f.HasTemperateGrowth)
    (N : ℝ) (v : EuclideanSpace ℝ (Fin p)) :
    (symmetricRadialGenerator N v f).HasTemperateGrowth := by
  have hb : (fun X : SymmetricMatrix p => fderiv ℝ f X (rankOneSymmetric v)).HasTemperateGrowth := by
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply] using
      (ContinuousLinearMap.apply ℝ ℝ
        (rankOneSymmetric v)).hasTemperateGrowth.comp (hasTemperateGrowth_fderiv hf)
  have hsum : (fun X : SymmetricMatrix p => ∑ i : Fin p,
      fderiv ℝ (radialDerivativeTest f v i) X
        (congruenceVelocity (outerMatrix v (coordinateVector i)) X)).HasTemperateGrowth := by
    apply Function.HasTemperateGrowth.sum
    intro i hi
    exact (ContinuousLinearMap.apply ℝ ℝ).bilinear_hasTemperateGrowth
      (congruenceVelocity (outerMatrix v (coordinateVector i))).hasTemperateGrowth
      (hasTemperateGrowth_fderiv (hasTemperateGrowth_radialDerivativeTest hf v i))
  have heq : symmetricRadialGenerator N v f = fun X : SymmetricMatrix p =>
      2 * N * fderiv ℝ f X (rankOneSymmetric v) +
        ∑ i : Fin p, fderiv ℝ (radialDerivativeTest f v i) X
          (congruenceVelocity (outerMatrix v (coordinateVector i)) X) := by
    funext X
    rw [symmetricRadialGenerator, radialCovarianceContraction_eq_directional_sum]
    simp only [symmetricSecondDerivative_eq hf, congruenceVelocity_outerMatrix]
    rfl
  rw [heq]
  exact ((Function.HasTemperateGrowth.const (2 * N)).mul hb).add hsum

set_option backward.isDefEq.respectTransparency false in
/-- The radial generator is stationary against the matching first-order
congruence drift. Every term is an actual integrable derivative of the test. -/
theorem wishart_radial_generator_stationarity {p : ℕ} {N : ℝ}
    (hN : (p : ℝ) - 1 < N) {f : SymmetricMatrix p → ℝ}
    (hf : f.HasTemperateGrowth) (v : EuclideanSpace ℝ (Fin p)) :
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
  have hgi (i : Fin p) := hasTemperateGrowth_radialDerivativeTest hf v i
  have hgiint (i : Fin p) : Integrable (gi i) μ :=
    integrable_temperate_of_allNormMoments hμ (hgi i)
  have hLint (i : Fin p) : Integrable (L i) μ :=
    integrable_fderiv_apply_temperate hμ (hgi i)
      (congruenceVelocity (outerMatrix v (coordinateVector i))).hasTemperateGrowth
  have hRint (i : Fin p) : Integrable (R i) μ := by
    have h := ((innerSL ℝ (coordinateVector i)).hasTemperateGrowth.comp
      (symmetricMatrixAction.bilinear_hasTemperateGrowth Function.HasTemperateGrowth.id
        (Function.HasTemperateGrowth.const v))).mul (hgi i)
    simpa only [Function.comp_def, Pi.mul_def, id_eq, innerSL_apply_apply,
      coordinate_inner, R, gi, μ] using integrable_temperate_of_allNormMoments hμ h
  have hBint : Integrable B μ := by
    simpa only [B, Function.comp_def, ContinuousLinearMap.apply_apply, μ] using
      integrable_temperate_of_allNormMoments hμ
        ((ContinuousLinearMap.apply ℝ ℝ
          (rankOneSymmetric v)).hasTemperateGrowth.comp (hasTemperateGrowth_fderiv hf))
  have hVint : Integrable V μ := integrable_fderiv_apply_temperate hμ hf
    (congruenceVelocity (outerMatrix v v)).hasTemperateGrowth
  have hLi (i : Fin p) : (∫ X, L i X ∂μ) =
      (∫ X, R i X ∂μ) - N * v i * (∫ X, gi i X ∂μ) := by
    have h := wishart_stein_temperate Matrix.PosDef.one hN (hgi i)
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
    rw [symmetricSecondDerivative_eq hf]
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

end Wishart
end
end CanonicalSource4

section CanonicalSource5
/- Source: Wishart/RadialTestCalculus.lean -/



/-!
# Multiplication by a test of one Wishart diagonal entry

These are actual first and second derivative formulas. They identify precisely
the compact-test integrand that scalar regression sends to the chi-squared
weak radial equation.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti.Probability Matrix
open WishartVerification
open scoped BigOperators Matrix.Norms.Operator

namespace Wishart

section Derivatives

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_product_apply {f g : E → ℝ}
    (hf : f.HasTemperateGrowth) (hg : g.HasTemperateGrowth) (X H : E) :
    fderiv ℝ (fun Y => f Y * g Y) X H =
      f X * fderiv ℝ g X H + g X * fderiv ℝ f X H := by
  rw [fderiv_fun_mul (hf.1.differentiable (by simp) X) (hg.1.differentiable (by simp) X)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

set_option backward.isDefEq.respectTransparency false in
theorem second_fderiv_product_apply {f g : E → ℝ}
    (hf : f.HasTemperateGrowth) (hg : g.HasTemperateGrowth) (X H K : E) :
    fderiv ℝ (fun Y => fderiv ℝ (fun Z => f Z * g Z) Y H) X K =
      f X * fderiv ℝ (fun Y => fderiv ℝ g Y H) X K +
      g X * fderiv ℝ (fun Y => fderiv ℝ f Y H) X K +
      fderiv ℝ f X K * fderiv ℝ g X H + fderiv ℝ g X K * fderiv ℝ f X H := by
  have hdf : (fun Y => fderiv ℝ f Y H).HasTemperateGrowth := by
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply] using
      (ContinuousLinearMap.apply ℝ ℝ H).hasTemperateGrowth.comp (hasTemperateGrowth_fderiv hf)
  have hdg : (fun Y => fderiv ℝ g Y H).HasTemperateGrowth := by
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply] using
      (ContinuousLinearMap.apply ℝ ℝ H).hasTemperateGrowth.comp (hasTemperateGrowth_fderiv hg)
  have heq : (fun Y => fderiv ℝ (fun Z => f Z * g Z) Y H) =
      fun Y => f Y * fderiv ℝ g Y H + g Y * fderiv ℝ f Y H :=
    funext fun Y => fderiv_product_apply hf hg Y H
  have hleft : DifferentiableAt ℝ (fun Y => f Y * fderiv ℝ g Y H) X :=
    (hf.1.differentiable (by simp) X).mul (hdg.1.differentiable (by simp) X)
  have hright : DifferentiableAt ℝ (fun Y => g Y * fderiv ℝ f Y H) X :=
    (hg.1.differentiable (by simp) X).mul (hdf.1.differentiable (by simp) X)
  rw [heq, fderiv_fun_add hleft hright]
  simp only [ContinuousLinearMap.add_apply, fderiv_product_apply hf hdg,
    fderiv_product_apply hg hdf]
  ring

theorem fderiv_scalar_linear_apply {φ : ℝ → ℝ} (hφ : φ.HasTemperateGrowth)
    (L : E →L[ℝ] ℝ) (X H : E) :
    fderiv ℝ (fun Y => φ (L Y)) X H = deriv φ (L X) * L H := by
  have h := ((hφ.1.differentiable (by simp) (L X)).hasDerivAt.comp_hasFDerivAt X
    L.hasFDerivAt).fderiv
  simpa only [Function.comp_def, ContinuousLinearMap.smul_apply, smul_eq_mul] using
    congrArg (fun T : E →L[ℝ] ℝ => T H) h

theorem hasTemperateGrowth_deriv {φ : ℝ → ℝ} (hφ : φ.HasTemperateGrowth) :
    (deriv φ).HasTemperateGrowth := by
  have h := (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).hasTemperateGrowth.comp
    (hasTemperateGrowth_fderiv hφ)
  exact h

theorem second_fderiv_scalar_linear_apply {φ : ℝ → ℝ}
    (hφ : φ.HasTemperateGrowth) (L : E →L[ℝ] ℝ) (X H K : E) :
    fderiv ℝ (fun Y => fderiv ℝ (fun Z => φ (L Z)) Y H) X K =
      deriv (deriv φ) (L X) * L K * L H := by
  have heq : (fun Y => fderiv ℝ (fun Z => φ (L Z)) Y H) =
      fun Y => deriv φ (L Y) * L H := funext fun Y => fderiv_scalar_linear_apply hφ L Y H
  rw [heq]
  have h := (((hasTemperateGrowth_deriv hφ).1.differentiable (by simp) (L X)).hasDerivAt.comp_hasFDerivAt X
    L.hasFDerivAt).mul_const (L H)
  simpa only [Function.comp_def, ContinuousLinearMap.smul_apply, smul_eq_mul,
    mul_comm, mul_left_comm, mul_assoc] using
    congrArg (fun T : E →L[ℝ] ℝ => T K) h.fderiv

end Derivatives

def diagonalEntryCLM {p : ℕ} (a : Fin p) : SymmetricMatrix p →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((Matrix.entryLinearMap ℝ ℝ a a).comp
      (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)).subtype)

@[simp] theorem diagonalEntryCLM_apply {p : ℕ} (a : Fin p) (X : SymmetricMatrix p) :
    diagonalEntryCLM a X = (X : Matrix (Fin p) (Fin p) ℝ) a a := rfl

@[simp] theorem diagonalEntry_rankOne_coordinate {p : ℕ} (a : Fin p) :
    diagonalEntryCLM a (rankOneSymmetric (coordinateVector a)) = 1 := by
  simp [coe_rankOneSymmetric, coordinateVector_apply, Matrix.vecMulVec_apply]

@[simp] theorem diagonalEntry_direction_coordinate {p : ℕ} (a i : Fin p) :
    diagonalEntryCLM a (symmetricRankDirection (coordinateVector a) (coordinateVector i)) =
      2 * (if i = a then 1 else 0) := by
  by_cases hai : a = i <;>
    simp [coe_symmetricRankDirection, coordinateVector_apply, Matrix.vecMulVec_apply,
      hai, eq_comm] <;> norm_num

@[simp] theorem diagonalEntry_congruence_coordinate {p : ℕ}
    (a : Fin p) (X : SymmetricMatrix p) :
    diagonalEntryCLM a (congruenceVelocity (outerMatrix (coordinateVector a) (coordinateVector a)) X) =
      2 * diagonalEntryCLM a X := by
  simp [coe_congruenceVelocity, outerMatrix, coordinateVector_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.vecMulVec_apply]
  ring

theorem coordinate_drift_sum {p : ℕ} (a : Fin p)
    (f : SymmetricMatrix p → ℝ) (X : SymmetricMatrix p) :
    (∑ i : Fin p, (X : Matrix (Fin p) (Fin p) ℝ) a i *
      fderiv ℝ f X (symmetricRankDirection (coordinateVector a) (coordinateVector i))) =
      fderiv ℝ f X
        (congruenceVelocity (outerMatrix (coordinateVector a) (coordinateVector a)) X) := by
  rw [congruenceVelocity_outerMatrix,
    ← map_sum_coordinateVector (symmetricRankDirection (coordinateVector a))
      (symmetricMatrixAction X (coordinateVector a))]
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  have hX := (selfAdjoint.isHermitian_coe X).isSymm
  simp [symmetricMatrixAction_apply, Matrix.toLpLin_apply, coordinateVector,
    Matrix.mulVec_single_one, Matrix.col_apply, hX.apply]

set_option backward.isDefEq.respectTransparency false in
theorem symmetricRadialGenerator_diagonal_test {p : ℕ}
    {φ : ℝ → ℝ} (hφ : φ.HasTemperateGrowth)
    {f : SymmetricMatrix p → ℝ} (hf : f.HasTemperateGrowth)
    (N : ℝ) (a : Fin p) (X : SymmetricMatrix p) :
    symmetricRadialGenerator N (coordinateVector a)
        (fun Y => φ (diagonalEntryCLM a Y) * f Y) X =
      φ (diagonalEntryCLM a X) * symmetricRadialGenerator N (coordinateVector a) f X +
        (4 * diagonalEntryCLM a X * deriv (deriv φ) (diagonalEntryCLM a X) +
          2 * N * deriv φ (diagonalEntryCLM a X)) * f X +
        4 * deriv φ (diagonalEntryCLM a X) *
          fderiv ℝ f X
            (congruenceVelocity (outerMatrix (coordinateVector a) (coordinateVector a)) X) := by
  have htest : (fun Y => φ (diagonalEntryCLM a Y)).HasTemperateGrowth := by
    simpa only [Function.comp_def] using hφ.comp (diagonalEntryCLM a).hasTemperateGrowth
  have hproduct : (fun Y => φ (diagonalEntryCLM a Y) * f Y).HasTemperateGrowth := by
    simpa only [Pi.mul_def] using htest.mul hf
  rw [symmetricRadialGenerator_eq_directional hproduct,
    symmetricRadialGenerator_eq_directional hf]
  unfold symmetricDirectionalGenerator
  simp_rw [second_fderiv_product_apply htest hf]
  simp_rw [second_fderiv_scalar_linear_apply hφ]
  simp only [fderiv_product_apply htest hf, fderiv_scalar_linear_apply hφ,
    diagonalEntry_rankOne_coordinate, diagonalEntry_direction_coordinate,
    mul_one, mul_add, Finset.sum_add_distrib]
  have hX := (selfAdjoint.isHermitian_coe X).isSymm
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_const_zero, Finset.sum_ite_irrel,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_one]
  simp_rw [show ∀ i, (X : Matrix (Fin p) (Fin p) ℝ) i a =
      (X : Matrix (Fin p) (Fin p) ℝ) a i from fun i => (hX.apply i a).symm]
  have hdouble (c : ℝ) (H : Fin p → Fin p → ℝ) :
      (∑ i, ∑ j, (X : Matrix (Fin p) (Fin p) ℝ) i j * (c * H i j)) =
        c * ∑ i, ∑ j, (X : Matrix (Fin p) (Fin p) ℝ) i j * H i j := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hleft (c : ℝ) (D : Fin p → ℝ) :
      (∑ i, (X : Matrix (Fin p) (Fin p) ℝ) a i * (c * D i)) =
        c * ∑ i, (X : Matrix (Fin p) (Fin p) ℝ) a i * D i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hright (c : ℝ) (D : Fin p → ℝ) :
      (∑ i, (X : Matrix (Fin p) (Fin p) ℝ) a i * D i * c) =
        c * ∑ i, (X : Matrix (Fin p) (Fin p) ℝ) a i * D i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  simp only [hdouble, hleft, hright, coordinate_drift_sum, diagonalEntryCLM_apply]
  have hscaled (c : ℝ) (D : Fin p → ℝ) :
      (∑ i, c * (X : Matrix (Fin p) (Fin p) ℝ) a i * D i * 2) =
        2 * c * ∑ i, (X : Matrix (Fin p) (Fin p) ℝ) a i * D i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  ring_nf
  rw [hscaled, coordinate_drift_sum]
  ring

def diagonalTestWeakIntegrand {p : ℕ} (N : ℝ) (a : Fin p)
    (f : SymmetricMatrix p → ℝ) (φ : ℝ → ℝ) (X : SymmetricMatrix p) : ℝ :=
  let t := diagonalEntryCLM a X
  let V := fderiv ℝ f X
    (congruenceVelocity (outerMatrix (coordinateVector a) (coordinateVector a)) X)
  φ t * symmetricRadialGenerator N (coordinateVector a) f X +
    (4 * t * deriv (deriv φ) t + 2 * N * deriv φ t) * f X +
      (4 * deriv φ t - φ t) * V - 2 * t * deriv φ t * f X

set_option backward.isDefEq.respectTransparency false in
/-- The exact weak test identity before disintegration into a chi-squared
diagonal entry and the independent scalar-regression noise. -/
theorem wishart_diagonal_test_weak_identity {p : ℕ} {N : ℝ}
    (hN : (p : ℝ) - 1 < N) (a : Fin p)
    {f : SymmetricMatrix p → ℝ} (hf : f.HasTemperateGrowth)
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
  have hg : g.HasTemperateGrowth := by simpa only [g, Pi.mul_def] using htest.mul hf
  have hμ := allFiniteMoments_wishart_norm N (1 : Matrix (Fin p) (Fin p) ℝ)
  have hL : Integrable (symmetricRadialGenerator N (coordinateVector a) g) μ :=
    integrable_temperate_of_allNormMoments hμ
      (hasTemperateGrowth_symmetricRadialGenerator hg N (coordinateVector a))
  have hV : Integrable (fun X => fderiv ℝ g X
      (congruenceVelocity (outerMatrix (coordinateVector a) (coordinateVector a)) X)) μ :=
    integrable_fderiv_apply_temperate hμ hg
      (congruenceVelocity (outerMatrix (coordinateVector a) (coordinateVector a))).hasTemperateGrowth
  have heq : diagonalTestWeakIntegrand N a f φ = fun X =>
      symmetricRadialGenerator N (coordinateVector a) g X - fderiv ℝ g X
        (congruenceVelocity (outerMatrix (coordinateVector a) (coordinateVector a)) X) := by
    funext X
    rw [show g = fun X => φ (diagonalEntryCLM a X) * f X from rfl,
      symmetricRadialGenerator_diagonal_test hφ hf,
      fderiv_product_apply htest hf,
      fderiv_scalar_linear_apply hφ, diagonalEntry_congruence_coordinate]
    dsimp [diagonalTestWeakIntegrand]
    ring
  rw [heq]
  refine ⟨hL.sub hV, ?_⟩
  rw [integral_sub hL hV, wishart_radial_generator_stationarity hN hg, sub_self]

end Wishart
end
end CanonicalSource5

section CanonicalSource6
/- Source: Wishart/ScalarRadialProfile.lean -/



/-!
# Analytic profiles for the transverse scalar-regression source

The noise lives in dimension r, while the mean points along the missing first
coordinate in dimension r+1. The source is the actual independent Gaussian
and W_r(N−1,I) pair. Polynomial derivative growth justifies both derivatives
of its signed-radius expectation, and symmetry makes that expectation even.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability Filter Set Topology
open WishartVerification
open scoped Matrix MatrixOrder Matrix.Norms.Operator

namespace Wishart

def scalarRadialDataCLM (r : ℕ) : ScalarRegressionNoise r →L[ℝ] RadialInputSpace (1 + r) :=
  ((LinearMap.toContinuousLinearMap
      (Matrix.symmetricCongruenceLinearMap (scalarNoiseMatrix r))).comp
    (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin r)) (SymmetricMatrix r))).prod
  (((scalarNoiseMatrix r).toEuclideanLin.toContinuousLinearMap).comp
    (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin r)) (SymmetricMatrix r)))

@[simp] theorem scalarRadialDataCLM_apply {r : ℕ} (x : ScalarRegressionNoise r) :
    scalarRadialDataCLM r x =
      (Matrix.symmetricCongruenceLinearMap (scalarNoiseMatrix r) x.2,
        (scalarNoiseMatrix r).toEuclideanLin x.1) := rfl

def scalarRadialMatrix {r : ℕ} (s : ℝ) (x : ScalarRegressionNoise r) :
    SymmetricMatrix (1 + r) :=
  radialInput (scalarTransverseAxis r) s (scalarRadialDataCLM r x)

def scalarRadialFirst {r : ℕ} (f : SymmetricMatrix (1 + r) → ℝ)
    (s : ℝ) (x : ScalarRegressionNoise r) : ℝ :=
  radialFirstIntegrand f (scalarTransverseAxis r) s (scalarRadialDataCLM r x)

def scalarRadialSecond {r : ℕ} (f : SymmetricMatrix (1 + r) → ℝ)
    (s : ℝ) (x : ScalarRegressionNoise r) : ℝ :=
  radialSecondIntegrand f (scalarTransverseAxis r) s (scalarRadialDataCLM r x)

theorem hasTemperateGrowth_scalarRadialDataParameter (r : ℕ) :
    (fun y : ℝ × ScalarRegressionNoise r => (y.1, scalarRadialDataCLM r y.2)).HasTemperateGrowth :=
  hasTemperateGrowth_prodMk (ContinuousLinearMap.fst ℝ ℝ (ScalarRegressionNoise r)).hasTemperateGrowth
    ((scalarRadialDataCLM r).hasTemperateGrowth.comp
      (ContinuousLinearMap.snd ℝ ℝ (ScalarRegressionNoise r)).hasTemperateGrowth)

theorem hasTemperateGrowth_scalarRadialMatrix (r : ℕ) :
    (fun y : ℝ × ScalarRegressionNoise r => scalarRadialMatrix y.1 y.2).HasTemperateGrowth :=
  (hasTemperateGrowth_radialInput (scalarTransverseAxis r)).comp
    (hasTemperateGrowth_scalarRadialDataParameter r)

theorem hasTemperateGrowth_scalarRadialFirst {r : ℕ}
    {f : SymmetricMatrix (1 + r) → ℝ} (hf : f.HasTemperateGrowth) :
    (fun y : ℝ × ScalarRegressionNoise r => scalarRadialFirst f y.1 y.2).HasTemperateGrowth :=
  (hasTemperateGrowth_radialFirstIntegrand hf (scalarTransverseAxis r)).comp
    (hasTemperateGrowth_scalarRadialDataParameter r)

set_option maxHeartbeats 800000 in
theorem hasTemperateGrowth_scalarRadialSecond {r : ℕ}
    {f : SymmetricMatrix (1 + r) → ℝ} (hf : f.HasTemperateGrowth) :
    (fun y : ℝ × ScalarRegressionNoise r => scalarRadialSecond f y.1 y.2).HasTemperateGrowth :=
  (hasTemperateGrowth_radialSecondIntegrand hf (scalarTransverseAxis r)).comp
    (hasTemperateGrowth_scalarRadialDataParameter r)

theorem isProbabilityMeasure_scalarRegressionNoiseMeasure {r : ℕ} {N : ℝ}
    (hN : (r : ℝ) < N) : IsProbabilityMeasure (scalarRegressionNoiseMeasure N r) := by
  letI := isProbabilityMeasure_nonsingularWishartMeasure
    (S := (1 : Matrix (Fin r) (Fin r) ℝ)) Matrix.PosDef.one
    (show (r : ℝ) - 1 < N - 1 by linarith)
  unfold scalarRegressionNoiseMeasure
  infer_instance

theorem allFiniteNormMoments_scalarRegressionNoise {r : ℕ} {N : ℝ}
    (hN : (r : ℝ) < N) :
    HasAllFiniteMoments (fun x : ScalarRegressionNoise r => ‖x‖)
      (scalarRegressionNoiseMeasure N r) := by
  letI := isProbabilityMeasure_nonsingularWishartMeasure
    (S := (1 : Matrix (Fin r) (Fin r) ℝ)) Matrix.PosDef.one
    (show (r : ℝ) - 1 < N - 1 by linarith)
  exact allFiniteNormMoments_prod allFiniteMoments_gaussian_norm
    (allFiniteMoments_wishart_norm (N - 1) 1)

theorem scalarTransverseAxis_eq_coordinate (r : ℕ) :
    scalarTransverseAxis r = coordinateVector (Fin.castAdd r (0 : Fin 1)) := by
  apply PiLp.ext
  intro i
  obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin 1 ⊕ Fin r ≃ Fin (1 + r)).surjective i
  rcases i with i | i
  · have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [coordinateVector_apply]
  · have hne : Fin.natAdd 1 i ≠ Fin.castAdd r (0 : Fin 1) := by
      intro h
      have hv := congrArg (fun j : Fin (1 + r) => j.val) h
      change 1 + i.val = 0 at hv
      omega
    simp [coordinateVector_apply, hne]

theorem scalarRadialMatrix_eq_regression {r : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (x : ScalarRegressionNoise r) :
    scalarRadialMatrix (Real.sqrt t) x = scalarRegressionMatrix t x :=
  (scalarRegressionMatrix_eq_rankOne ht x).symm

theorem scalarRadialMatrix_axis_action {r : ℕ} (s : ℝ) (x : ScalarRegressionNoise r) :
    symmetricMatrixAction (scalarRadialMatrix s x) (scalarTransverseAxis r) =
      s • ((scalarNoiseMatrix r).toEuclideanLin x.1 + s • scalarTransverseAxis r) := by
  have he := scalarTransverseAxis_eq_coordinate r
  apply PiLp.ext
  intro i
  rw [symmetricMatrixAction_apply, he]
  simp only [Matrix.toLpLin_apply, coordinateVector, Matrix.mulVec_single_one, Matrix.col_apply]
  obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin 1 ⊕ Fin r ≃ Fin (1 + r)).surjective i
  rcases i with i | i
  · have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [scalarRadialMatrix, radialInput, scalarRadialDataCLM_apply,
      Matrix.coe_symmetricCongruenceLinearMap_apply, coe_rankOneSymmetric,
      Matrix.vecMulVec_apply, scalarNoiseMatrix, Matrix.mul_apply, Matrix.mulVec,
      dotProduct, Matrix.transpose_apply, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul,
      scalarTransverseAxis_castAdd, pow_two]
  · have hne : Fin.natAdd 1 i ≠ Fin.castAdd r (0 : Fin 1) := by
      intro h
      have hv := congrArg (fun j : Fin (1 + r) => j.val) h
      change 1 + i.val = 0 at hv
      omega
    simp [scalarRadialMatrix, radialInput, scalarRadialDataCLM_apply,
      Matrix.coe_symmetricCongruenceLinearMap_apply, coe_rankOneSymmetric,
      Matrix.vecMulVec_apply, scalarNoiseMatrix, Matrix.mul_apply, Matrix.mulVec,
      dotProduct, Matrix.transpose_apply, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul,
      scalarTransverseAxis_castAdd, scalarTransverseAxis_natAdd, hne, Matrix.one_apply] <;> ring

theorem scalarRadialMatrix_congruence_direction {r : ℕ}
    (s : ℝ) (x : ScalarRegressionNoise r) :
    congruenceVelocity (outerMatrix (scalarTransverseAxis r) (scalarTransverseAxis r))
      (scalarRadialMatrix s x) =
        s • radialDirection (scalarTransverseAxis r) s (scalarRadialDataCLM r x) := by
  rw [congruenceVelocity_outerMatrix, scalarRadialMatrix_axis_action, map_smul]
  rfl

theorem scalarRadialMatrix_first_drift {r : ℕ} (f : SymmetricMatrix (1 + r) → ℝ)
    (s : ℝ) (x : ScalarRegressionNoise r) :
    fderiv ℝ f (scalarRadialMatrix s x)
      (congruenceVelocity (outerMatrix (scalarTransverseAxis r) (scalarTransverseAxis r))
        (scalarRadialMatrix s x)) = s * scalarRadialFirst f s x := by
  rw [scalarRadialMatrix_congruence_direction, map_smul]
  rfl

def scalarRadiusExpectation {r : ℕ} (N : ℝ) (f : SymmetricMatrix (1 + r) → ℝ)
    (s : ℝ) : ℝ :=
  ∫ x, f (scalarRadialMatrix s x) ∂scalarRegressionNoiseMeasure N r

def scalarRadiusFirstExpectation {r : ℕ} (N : ℝ) (f : SymmetricMatrix (1 + r) → ℝ)
    (s : ℝ) : ℝ :=
  ∫ x, scalarRadialFirst f s x ∂scalarRegressionNoiseMeasure N r

def scalarRadiusSecondExpectation {r : ℕ} (N : ℝ) (f : SymmetricMatrix (1 + r) → ℝ)
    (s : ℝ) : ℝ :=
  ∫ x, scalarRadialSecond f s x ∂scalarRegressionNoiseMeasure N r

theorem hasDerivAt_scalarRadiusExpectation {r : ℕ} {N : ℝ}
    (hN : (r : ℝ) < N) {f : SymmetricMatrix (1 + r) → ℝ}
    (hf : f.HasTemperateGrowth) (s : ℝ) :
    HasDerivAt (scalarRadiusExpectation N f) (scalarRadiusFirstExpectation N f s) s := by
  letI := isProbabilityMeasure_scalarRegressionNoiseMeasure hN
  have hparam := hf.comp (hasTemperateGrowth_scalarRadialMatrix r)
  have hd := hasDerivAt_integral_temperate (allFiniteNormMoments_scalarRegressionNoise hN) hparam s
  convert hd using 1
  · rfl
  apply integral_congr_ae
  filter_upwards with x
  exact (hasDerivAt_radialIntegrand hf (scalarTransverseAxis r) (scalarRadialDataCLM r x) s).unique
    (hasDerivAt_parameter_slice hparam x s)

theorem hasDerivAt_scalarRadiusFirstExpectation {r : ℕ} {N : ℝ}
    (hN : (r : ℝ) < N) {f : SymmetricMatrix (1 + r) → ℝ}
    (hf : f.HasTemperateGrowth) (s : ℝ) :
    HasDerivAt (scalarRadiusFirstExpectation N f) (scalarRadiusSecondExpectation N f s) s := by
  letI := isProbabilityMeasure_scalarRegressionNoiseMeasure hN
  have hparam := hasTemperateGrowth_scalarRadialFirst hf
  have hd := hasDerivAt_integral_temperate (allFiniteNormMoments_scalarRegressionNoise hN) hparam s
  convert hd using 1
  · rfl
  apply integral_congr_ae
  filter_upwards with x
  exact (hasDerivAt_radialFirstIntegrand hf (scalarTransverseAxis r)
    (scalarRadialDataCLM r x) s).unique (hasDerivAt_parameter_slice hparam x s)

theorem continuous_scalarRadiusSecondExpectation {r : ℕ} {N : ℝ}
    (hN : (r : ℝ) < N) {f : SymmetricMatrix (1 + r) → ℝ}
    (hf : f.HasTemperateGrowth) : Continuous (scalarRadiusSecondExpectation N f) := by
  letI := isProbabilityMeasure_scalarRegressionNoiseMeasure hN
  apply continuous_iff_continuousAt.mpr
  intro s
  exact (hasDerivAt_integral_temperate (allFiniteNormMoments_scalarRegressionNoise hN)
    (hasTemperateGrowth_scalarRadialSecond hf) s).continuousAt

theorem scalarRadiusExpectation_even {r : ℕ} {N : ℝ}
    (hN : (r : ℝ) < N) {f : SymmetricMatrix (1 + r) → ℝ}
    (hf : f.HasTemperateGrowth) (s : ℝ) :
    scalarRadiusExpectation N f (-s) = scalarRadiusExpectation N f s := by
  let γ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin r)) (1 : Matrix (Fin r) (Fin r) ℝ)
  have hneg : MeasurePreserving (fun z : EuclideanSpace ℝ (Fin r) => -z) γ γ :=
    ⟨by fun_prop, map_neg_centered_multivariateGaussian Matrix.PosSemidef.one⟩
  have hp : MeasurePreserving (Prod.map (fun z : EuclideanSpace ℝ (Fin r) => -z) id)
      (scalarRegressionNoiseMeasure N r) (scalarRegressionNoiseMeasure N r) :=
    hneg.prod (MeasurePreserving.id
      (nonsingularWishartMeasure (N - 1) (1 : Matrix (Fin r) (Fin r) ℝ)))
  have htest : Measurable (fun x : ScalarRegressionNoise r => f (scalarRadialMatrix s x)) :=
    (hf.comp ((hasTemperateGrowth_scalarRadialMatrix r).comp
      (hasTemperateGrowth_prodMk (Function.HasTemperateGrowth.const s)
        Function.HasTemperateGrowth.id))).1.continuous.measurable
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

end Wishart
end
end CanonicalSource6

section CanonicalSource7
/- Source: Wishart/ChiSquaredStein.lean -/



/-!
# The scalar chi-squared integration-by-parts identity

This is proved from the actual chi-squared density. Compact support inside the
positive ray removes both boundary terms for every real degree N > 0, including
the range in which the density is singular at zero.
-/

noncomputable section

open MeasureTheory Filter Set TauCeti.Probability
open scoped Topology

namespace Wishart

theorem continuous_mul_of_tsupport_subset {f g : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hf : ContinuousOn f U) (hg : Continuous g)
    (hsupp : tsupport g ⊆ U) : Continuous (fun x => f x * g x) := by
  apply continuous_of_tsupport
  intro x hx
  have hxg : x ∈ tsupport g := tsupport_mul_subset_right hx
  exact (hf.continuousAt (hU.mem_nhds (hsupp hxg))).mul hg.continuousAt

theorem integrable_mul_of_tsupport_subset {f g : ℝ → ℝ} {U : Set ℝ}
    {μ : Measure ℝ} [IsLocallyFiniteMeasure μ]
    (hU : IsOpen U) (hf : ContinuousOn f U) (hg : Continuous g)
    (hcompact : HasCompactSupport g) (hsupp : tsupport g ⊆ U) :
    Integrable (fun x => f x * g x) μ :=
  (continuous_mul_of_tsupport_subset hU hf hg hsupp).integrable_of_hasCompactSupport
    hcompact.mul_left

theorem integral_chiSquared_eq_density {N : ℝ} (hN : 0 < N) (f : ℝ → ℝ) :
    (∫ t, f t ∂chiSquaredMeasure N) = ∫ t, chiSquaredPDFReal N t * f t := by
  rw [chiSquaredMeasure_eq_withDensity hN,
    show chiSquaredPDF N = fun t => ENNReal.ofReal (chiSquaredPDFReal N t) by
      funext t; exact chiSquaredPDF_eq_ofReal N t,
    integral_withDensity_ofReal (measurable_chiSquaredPDFReal N).aemeasurable
      (Eventually.of_forall (chiSquaredPDFReal_nonneg hN.le))]
  rfl

theorem chiSquaredPDFReal_pos_of_pos {N t : ℝ} (hN : 0 < N) (ht : 0 < t) :
    0 < chiSquaredPDFReal N t := by
  rw [chiSquaredPDFReal_of_nonneg ht.le]
  exact div_pos
    (mul_pos (Real.rpow_pos_of_pos ht _) (Real.exp_pos _))
    (mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
      (Real.Gamma_pos_of_pos (by positivity)))

theorem continuousOn_chiSquaredPDFReal (N : ℝ) :
    ContinuousOn (chiSquaredPDFReal N) (Ioi 0) := by
  intro t ht
  have hp := Real.hasDerivAt_rpow_const (p := N / 2 - 1) (Or.inl ht.ne')
  have he := (((hasDerivAt_id t).neg).div_const 2).exp
  have hc := ((hp.mul he).div_const ((2 : ℝ) ^ (N / 2) * Real.Gamma (N / 2))).continuousAt
  apply (hc.congr_of_eventuallyEq ?_).continuousWithinAt
  filter_upwards [eventually_gt_nhds ht] with s hs
  exact chiSquaredPDFReal_of_nonneg hs.le

/-- The divergence form of the chi-squared weight on the positive ray. -/
theorem hasDerivAt_twice_mul_chiSquaredPDFReal (N : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => 2 * s * chiSquaredPDFReal N s)
      ((N - t) * chiSquaredPDFReal N t) t := by
  let Z : ℝ := (2 : ℝ) ^ (N / 2) * Real.Gamma (N / 2)
  have hp := Real.hasDerivAt_rpow_const (p := N / 2) (Or.inl ht.ne')
  have he := (((hasDerivAt_id t).neg).div_const 2).exp
  have hd := ((hp.mul he).const_mul 2).div_const Z
  have hpower : t ^ (N / 2) = t ^ (N / 2 - 1) * t := by
    simpa only [sub_add_cancel] using Real.rpow_add_one ht.ne' (N / 2 - 1)
  have hformula : HasDerivAt
      (fun s : ℝ => 2 * (s ^ (N / 2) * Real.exp (-s / 2)) / Z)
      ((N - t) * chiSquaredPDFReal N t) t := by
    convert hd using 1
    · rfl
    · rw [chiSquaredPDFReal_of_nonneg ht.le, hpower]
      dsimp [Z]
      ring
  apply hformula.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with s hs
  have hpower' : s ^ (N / 2) = s ^ (N / 2 - 1) * s := by
    simpa only [sub_add_cancel] using Real.rpow_add_one hs.ne' (N / 2 - 1)
  rw [chiSquaredPDFReal_of_nonneg hs.le, hpower']
  dsimp [Z]
  ring

/-- Scalar Stein identity for a C¹ test with compact support in (0,∞).
The derivative is an explicit function, so this lemma can also be applied to
localized products of functions which are only differentiable on (0,∞). -/
theorem chiSquared_stein_compact {N : ℝ} (hN : 0 < N)
    {f f' : ℝ → ℝ} (hderiv : ∀ t, HasDerivAt f (f' t) t)
    (hf' : Continuous f') (hcompact : HasCompactSupport f)
    (hsupp : tsupport f ⊆ Ioi 0) :
    (∫ t, 2 * t * f' t ∂chiSquaredMeasure N) =
      ∫ t, (t - N) * f t ∂chiSquaredMeasure N := by
  have hf : Continuous f := continuous_iff_continuousAt.mpr fun t =>
    (hderiv t).continuousAt
  have hderiv_eq : f' = deriv f := funext fun t => (hderiv t).deriv.symm
  have hcompact' : HasCompactSupport f' := hderiv_eq.symm ▸ hcompact.deriv
  have hsupp' : tsupport f' ⊆ Ioi 0 := by
    rw [hderiv_eq]
    exact tsupport_deriv_subset.trans hsupp
  let u : ℝ → ℝ := fun t => 2 * t * chiSquaredPDFReal N t
  let u' : ℝ → ℝ := fun t => (N - t) * chiSquaredPDFReal N t
  have hucont : ContinuousOn u (Ioi 0) :=
    (continuousOn_const.mul continuousOn_id).mul (continuousOn_chiSquaredPDFReal N)
  have hu'cont : ContinuousOn u' (Ioi 0) :=
    (continuousOn_const.sub continuousOn_id).mul (continuousOn_chiSquaredPDFReal N)
  have hi₁ : Integrable (u * f') :=
    integrable_mul_of_tsupport_subset isOpen_Ioi hucont hf' hcompact' hsupp'
  have hi₂ : Integrable (u' * f) :=
    integrable_mul_of_tsupport_subset isOpen_Ioi hu'cont hf hcompact hsupp
  have hi₀ : Integrable (u * f) :=
    integrable_mul_of_tsupport_subset isOpen_Ioi hucont hf hcompact hsupp
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := u) (u' := u') (v := f) (v' := f')
    (fun t ht => hasDerivAt_twice_mul_chiSquaredPDFReal N (hsupp ht))
    (fun t _ => hderiv t) hi₁ hi₂ hi₀
  rw [integral_chiSquared_eq_density hN, integral_chiSquared_eq_density hN]
  have hleft : (fun t => chiSquaredPDFReal N t * (2 * t * f' t)) =
      fun t => u t * f' t := by
    funext t
    dsimp [u]
    ring
  have hright : (fun t => chiSquaredPDFReal N t * ((t - N) * f t)) =
      fun t => -(u' t * f t) := by
    funext t
    dsimp [u']
    ring
  rw [hleft, hright, integral_neg]
  exact hibp

end Wishart
end
end CanonicalSource7

section CanonicalSource8
/- Source: Wishart/RadialWeakODE.lean -/



/-!
# From the conditional Wishart test identity to the radial ODE

The weak identity in this file is the one obtained by applying the Wishart
congruence Stein formula to phi(X00) g(X), then using scalar block regression.
Two applications of the proved scalar chi-squared integration-by-parts formula
turn it into the pointwise ODE.  No distributional or pointwise differential
equation is introduced as an axiom.
-/

noncomputable section

open MeasureTheory Filter Set TauCeti.Probability
open scoped Topology ContDiff

namespace Wishart

def chiSquaredFirstOrder (N : ℝ) (f f' : ℝ → ℝ) (t : ℝ) : ℝ :=
  2 * t * f' t + (N - t) * f t

theorem chiSquaredFirstOrder_integral {N : ℝ} (hN : 0 < N)
    {f f' : ℝ → ℝ} (hderiv : ∀ t, HasDerivAt f (f' t) t)
    (hf' : Continuous f') (hcompact : HasCompactSupport f)
    (hsupp : tsupport f ⊆ Ioi 0) :
    Integrable (chiSquaredFirstOrder N f f') (chiSquaredMeasure N) ∧
      (∫ t, chiSquaredFirstOrder N f f' t ∂chiSquaredMeasure N) = 0 := by
  letI := isProbabilityMeasure_chiSquaredMeasure hN.le
  have hf : Continuous f := continuous_iff_continuousAt.mpr fun t =>
    (hderiv t).continuousAt
  have hderiv_eq : f' = deriv f := funext fun t => (hderiv t).deriv.symm
  have hcompact' : HasCompactSupport f' := hderiv_eq.symm ▸ hcompact.deriv
  have hi₁ : Integrable (fun t => 2 * t * f' t) (chiSquaredMeasure N) :=
    ((continuous_const.mul continuous_id).mul hf').integrable_of_hasCompactSupport
      hcompact'.mul_left
  have hi₂ : Integrable (fun t => (N - t) * f t) (chiSquaredMeasure N) :=
    ((continuous_const.sub continuous_id).mul hf).integrable_of_hasCompactSupport
      hcompact.mul_left
  refine ⟨hi₁.add hi₂, ?_⟩
  change (∫ t, 2 * t * f' t + (N - t) * f t ∂chiSquaredMeasure N) = 0
  rw [integral_add hi₁ hi₂,
    chiSquared_stein_compact hN hderiv hf' hcompact hsupp]
  have hneg : (fun t => (N - t) * f t) = fun t => -((t - N) * f t) := by
    funext t
    ring
  rw [hneg, integral_neg, add_neg_cancel]

/-- The exact scalar expression obtained from the full Wishart Stein identity
after conditioning on the first diagonal entry and differentiating its scaling
in the regression representation. -/
def radialWeakIntegrand (N : ℝ) (F D G φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  φ t * G t + (4 * t * deriv (deriv φ) t + 2 * N * deriv φ t) * F t +
    8 * t * deriv φ t * D t - 2 * t * φ t * D t - 2 * t * deriv φ t * F t

set_option backward.isDefEq.respectTransparency false in
/-- The chi-squared weak identity forces the pointwise radial ODE throughout
the positive ray. The only analytic hypotheses are the displayed ordinary
derivatives and continuity of the operator expectation. -/
theorem radial_ode_of_chiSquared_tests {N : ℝ} (hN : 0 < N)
    {F D D₂ G : ℝ → ℝ}
    (hFD : ∀ t, 0 < t → HasDerivAt F (D t) t)
    (hDD₂ : ∀ t, 0 < t → HasDerivAt D (D₂ t) t)
    (hD₂ : ContinuousOn D₂ (Ioi 0)) (hG : ContinuousOn G (Ioi 0))
    (hweak : ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioi 0 →
        (∫ t, radialWeakIntegrand N F D G φ t ∂chiSquaredMeasure N) = 0) :
    ∀ t, 0 < t → 4 * t * D₂ t + 2 * N * D t = G t := by
  letI := isProbabilityMeasure_chiSquaredMeasure hN.le
  have hF : ContinuousOn F (Ioi 0) := fun t ht =>
    (hFD t ht).continuousAt.continuousWithinAt
  have hD : ContinuousOn D (Ioi 0) := fun t ht =>
    (hDD₂ t ht).continuousAt.continuousWithinAt
  let R : ℝ → ℝ := fun t => G t - (4 * t * D₂ t + 2 * N * D t)
  have hR : ContinuousOn R (Ioi 0) :=
    hG.sub (((continuousOn_const.mul continuousOn_id).mul hD₂).add
      (continuousOn_const.mul hD))
  have htests : ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioi 0 → (∫ t, φ t * R t ∂chiSquaredMeasure N) = 0 := by
    intro φ hφ hcφ hsφ
    have hφ' : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
    have hφ'' : ContDiff ℝ ∞ (deriv (deriv φ)) :=
      (contDiff_infty_iff_deriv.mp hφ').2
    have hsφ' : tsupport (deriv φ) ⊆ Ioi 0 := tsupport_deriv_subset.trans hsφ
    have hsφ'' : tsupport (deriv (deriv φ)) ⊆ Ioi 0 :=
      tsupport_deriv_subset.trans hsφ'
    let H₁ : ℝ → ℝ := fun t => D t * φ t
    let H₁' : ℝ → ℝ := fun t => D t * deriv φ t + D₂ t * φ t
    let H₂ : ℝ → ℝ := fun t => F t * deriv φ t
    let H₂' : ℝ → ℝ := fun t => F t * deriv (deriv φ) t + D t * deriv φ t
    have hdH₁ : ∀ t, HasDerivAt H₁ (H₁' t) t := by
      intro t
      simpa only [H₁, H₁', ContinuousLinearMap.mul_apply'] using
        (ContinuousLinearMap.mul ℝ ℝ).hasDerivAt_of_bilinear
          (fun ht => hDD₂ t (hsφ ht))
          (fun _ => (hφ.differentiable (by simp) t).hasDerivAt)
    have hdH₂ : ∀ t, HasDerivAt H₂ (H₂' t) t := by
      intro t
      simpa only [H₂, H₂', ContinuousLinearMap.mul_apply'] using
        (ContinuousLinearMap.mul ℝ ℝ).hasDerivAt_of_bilinear
          (fun ht => hFD t (hsφ' ht))
          (fun _ => (hφ'.differentiable (by simp) t).hasDerivAt)
    have hcH₁' : Continuous H₁' :=
      (continuous_mul_of_tsupport_subset isOpen_Ioi hD hφ'.continuous hsφ').add
        (continuous_mul_of_tsupport_subset isOpen_Ioi hD₂ hφ.continuous hsφ)
    have hcH₂' : Continuous H₂' :=
      (continuous_mul_of_tsupport_subset isOpen_Ioi hF hφ''.continuous hsφ'').add
        (continuous_mul_of_tsupport_subset isOpen_Ioi hD hφ'.continuous hsφ')
    have hH₁ := chiSquaredFirstOrder_integral hN hdH₁ hcH₁' hcφ.mul_left
      (tsupport_mul_subset_right.trans hsφ)
    have hH₂ := chiSquaredFirstOrder_integral hN hdH₂ hcH₂' hcφ.deriv.mul_left
      (tsupport_mul_subset_right.trans hsφ')
    have hiR : Integrable (fun t => φ t * R t) (chiSquaredMeasure N) := by
      simpa only [mul_comm] using integrable_mul_of_tsupport_subset
        (μ := chiSquaredMeasure N) isOpen_Ioi hR hφ.continuous hcφ hsφ
    have hi₁ := hH₁.1.const_mul (2 : ℝ)
    have hi₂ := hH₂.1.const_mul (2 : ℝ)
    have hidentity : radialWeakIntegrand N F D G φ = fun t =>
        φ t * R t + 2 * chiSquaredFirstOrder N H₁ H₁' t +
          2 * chiSquaredFirstOrder N H₂ H₂' t := by
      funext t
      dsimp [radialWeakIntegrand, chiSquaredFirstOrder, H₁, H₁', H₂, H₂', R]
      ring
    have hw := hweak φ hφ hcφ hsφ
    have hadd₁ :
        (∫ t, φ t * R t + 2 * chiSquaredFirstOrder N H₁ H₁' t ∂chiSquaredMeasure N) =
          (∫ t, φ t * R t ∂chiSquaredMeasure N) +
            ∫ t, 2 * chiSquaredFirstOrder N H₁ H₁' t ∂chiSquaredMeasure N := by
      simpa only [Pi.add_apply] using integral_add hiR hi₁
    have hadd₂ :
        (∫ t, (φ t * R t + 2 * chiSquaredFirstOrder N H₁ H₁' t) +
          2 * chiSquaredFirstOrder N H₂ H₂' t ∂chiSquaredMeasure N) =
          (∫ t, φ t * R t + 2 * chiSquaredFirstOrder N H₁ H₁' t ∂chiSquaredMeasure N) +
            ∫ t, 2 * chiSquaredFirstOrder N H₂ H₂' t ∂chiSquaredMeasure N := by
      simpa only [Pi.add_apply] using integral_add (hiR.add hi₁) hi₂
    rw [hidentity, hadd₂, hadd₁, integral_const_mul, integral_const_mul,
      hH₁.2, hH₂.2] at hw
    simpa only [mul_zero, add_zero] using hw
  have hae : ∀ᵐ t ∂chiSquaredMeasure N, t ∈ Ioi 0 → R t = 0 :=
    isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hR.locallyIntegrableOn measurableSet_Ioi)
      (fun φ hφ hcφ hsφ => by simpa only [smul_eq_mul] using htests φ hφ hcφ hsφ)
  rw [chiSquaredMeasure_eq_withDensity hN,
    ae_withDensity_iff (measurable_chiSquaredPDF N)] at hae
  have haeVolume : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioi 0 → R t = 0 := by
    filter_upwards [hae] with t ht hpos
    apply ht _ hpos
    rw [chiSquaredPDF_eq_ofReal]
    exact (ENNReal.ofReal_pos.mpr (chiSquaredPDFReal_pos_of_pos hN hpos)).ne'
  have hpoint : EqOn R (fun _ => 0) (Ioi 0) :=
    Measure.eqOn_open_of_ae_eq (μ := (volume : Measure ℝ))
      ((ae_restrict_iff' measurableSet_Ioi).mpr haeVolume)
      isOpen_Ioi hR continuousOn_const
  intro t ht
  exact (sub_eq_zero.mp (hpoint ht)).symm

end Wishart
end
end CanonicalSource8

section CanonicalSource9
/- Source: Wishart/ScalarRadialIdentity.lean -/



/-!
# The real-shape transverse radial identity

The weak identity is obtained by transporting the actual Wishart generator
identity through the proved scalar regression law. It is then converted to
the pointwise ODE by chi-squared integration by parts. No weak equation,
integer-shape representation, or conditional-law premise remains.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability Filter Set Topology
open WishartVerification
open scoped Matrix MatrixOrder Matrix.Norms.Operator

namespace Wishart

def scalarRadialProfile {r : ℕ} (N : ℝ) (f : SymmetricMatrix (1 + r) → ℝ) (t : ℝ) : ℝ :=
  scalarRadiusExpectation N f (Real.sqrt t)

def scalarRadialProfileDerivative {r : ℕ} (N : ℝ) (f : SymmetricMatrix (1 + r) → ℝ)
    (t : ℝ) : ℝ :=
  scalarRadiusFirstExpectation N f (Real.sqrt t) / (2 * Real.sqrt t)

def scalarRadialProfileSecondDerivative {r : ℕ} (N : ℝ)
    (f : SymmetricMatrix (1 + r) → ℝ) (t : ℝ) : ℝ :=
  (scalarRadiusSecondExpectation N f (Real.sqrt t) -
    scalarRadiusFirstExpectation N f (Real.sqrt t) / Real.sqrt t) / (4 * t)

def scalarRadialGeneratorExpectation {r : ℕ} (N : ℝ)
    (f : SymmetricMatrix (1 + r) → ℝ) (t : ℝ) : ℝ :=
  scalarRadiusExpectation N (symmetricRadialGenerator N (scalarTransverseAxis r) f) (Real.sqrt t)

theorem integrable_scalarRadiusSlice {r : ℕ} {N : ℝ} (hN : (r : ℝ) < N)
    {f : SymmetricMatrix (1 + r) → ℝ} (hf : f.HasTemperateGrowth) (s : ℝ) :
    Integrable (fun x => f (scalarRadialMatrix s x)) (scalarRegressionNoiseMeasure N r) := by
  letI := isProbabilityMeasure_scalarRegressionNoiseMeasure hN
  exact integrable_temperate_of_allNormMoments (allFiniteNormMoments_scalarRegressionNoise hN)
    ((hf.comp (hasTemperateGrowth_scalarRadialMatrix r)).comp
      (hasTemperateGrowth_prodMk (Function.HasTemperateGrowth.const s)
        Function.HasTemperateGrowth.id))

theorem integrable_scalarRadiusFirstSlice {r : ℕ} {N : ℝ} (hN : (r : ℝ) < N)
    {f : SymmetricMatrix (1 + r) → ℝ} (hf : f.HasTemperateGrowth) (s : ℝ) :
    Integrable (scalarRadialFirst f s) (scalarRegressionNoiseMeasure N r) := by
  letI := isProbabilityMeasure_scalarRegressionNoiseMeasure hN
  exact integrable_temperate_of_allNormMoments (allFiniteNormMoments_scalarRegressionNoise hN)
    ((hasTemperateGrowth_scalarRadialFirst hf).comp
      (hasTemperateGrowth_prodMk (Function.HasTemperateGrowth.const s)
        Function.HasTemperateGrowth.id))

theorem scalarRadiusFirstExpectation_scale {r : ℕ} (N : ℝ)
    (f : SymmetricMatrix (1 + r) → ℝ) {t : ℝ} (ht : 0 < t) :
    Real.sqrt t * scalarRadiusFirstExpectation N f (Real.sqrt t) =
      2 * t * scalarRadialProfileDerivative N f t := by
  have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  dsimp [scalarRadialProfileDerivative]
  field_simp [hs]
  rw [Real.sq_sqrt ht.le]
  ring

theorem scalarRegression_diagonal_test_integral {r : ℕ} {N : ℝ}
    (hN : (r : ℝ) < N) {f : SymmetricMatrix (1 + r) → ℝ}
    (hf : f.HasTemperateGrowth) (φ : ℝ → ℝ) {t : ℝ} (ht : 0 < t) :
    (∫ x, diagonalTestWeakIntegrand N (Fin.castAdd r (0 : Fin 1)) f φ
      (scalarRegressionMatrix t x) ∂scalarRegressionNoiseMeasure N r) =
      radialWeakIntegrand N (scalarRadialProfile N f) (scalarRadialProfileDerivative N f)
        (scalarRadialGeneratorExpectation N f) φ t := by
  let μ := scalarRegressionNoiseMeasure N r
  let F (x : ScalarRegressionNoise r) := f (scalarRadialMatrix (Real.sqrt t) x)
  let G (x : ScalarRegressionNoise r) :=
    symmetricRadialGenerator N (scalarTransverseAxis r) f (scalarRadialMatrix (Real.sqrt t) x)
  let D (x : ScalarRegressionNoise r) := scalarRadialFirst f (Real.sqrt t) x
  have hiF : Integrable F μ := integrable_scalarRadiusSlice hN hf _
  have hiG : Integrable G μ := integrable_scalarRadiusSlice hN
    (hasTemperateGrowth_symmetricRadialGenerator hf N (scalarTransverseAxis r)) _
  have hiD : Integrable D μ := integrable_scalarRadiusFirstSlice hN hf _
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
theorem scalarRadialProfile_weak_identity {r : ℕ} {N : ℝ}
    (hN : (r : ℝ) < N) {f : SymmetricMatrix (1 + r) → ℝ}
    (hf : f.HasTemperateGrowth) {φ : ℝ → ℝ} (hφ : φ.HasTemperateGrowth) :
    (∫ t, radialWeakIntegrand N (scalarRadialProfile N f) (scalarRadialProfileDerivative N f)
      (scalarRadialGeneratorExpectation N f) φ t ∂chiSquaredMeasure N) = 0 := by
  have hN0 : 0 < N := (Nat.cast_nonneg r).trans_lt hN
  have hdegree : (((1 + r : ℕ) : ℝ) - 1) < N := by
    push_cast
    linarith
  letI := isProbabilityMeasure_chiSquaredMeasure hN0.le
  letI := isProbabilityMeasure_scalarRegressionNoiseMeasure hN
  let h := diagonalTestWeakIntegrand N (Fin.castAdd r (0 : Fin 1)) f φ
  have htest := wishart_diagonal_test_weak_identity hdegree (Fin.castAdd r (0 : Fin 1)) hf hφ
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
    exact scalarRegression_diagonal_test_integral hN hf φ ht
  rwa [integral_congr_ae heq] at hzero

theorem hasDerivAt_scalarRadialProfile {r : ℕ} {N : ℝ}
    (hN : (r : ℝ) < N) {f : SymmetricMatrix (1 + r) → ℝ}
    (hf : f.HasTemperateGrowth) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (scalarRadialProfile N f) (scalarRadialProfileDerivative N f t) t :=
  hasDerivAt_sqrt_profile ht (hasDerivAt_scalarRadiusExpectation hN hf (Real.sqrt t))

theorem hasDerivAt_scalarRadialProfileDerivative {r : ℕ} {N : ℝ}
    (hN : (r : ℝ) < N) {f : SymmetricMatrix (1 + r) → ℝ}
    (hf : f.HasTemperateGrowth) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (scalarRadialProfileDerivative N f) (scalarRadialProfileSecondDerivative N f t) t :=
  hasDerivAt_sqrt_profile_derivative ht (hasDerivAt_scalarRadiusFirstExpectation hN hf (Real.sqrt t))

theorem continuousOn_scalarRadialProfileSecondDerivative {r : ℕ} {N : ℝ}
    (hN : (r : ℝ) < N) {f : SymmetricMatrix (1 + r) → ℝ}
    (hf : f.HasTemperateGrowth) :
    ContinuousOn (scalarRadialProfileSecondDerivative N f) (Ioi 0) := by
  have hJ₁ : Continuous (scalarRadiusFirstExpectation N f) :=
    continuous_iff_continuousAt.mpr fun s => (hasDerivAt_scalarRadiusFirstExpectation hN hf s).continuousAt
  have hJ₂ := continuous_scalarRadiusSecondExpectation hN hf
  exact ((hJ₂.comp Real.continuous_sqrt).continuousOn.sub
    ((hJ₁.comp Real.continuous_sqrt).continuousOn.div Real.continuous_sqrt.continuousOn
      (fun t ht => (Real.sqrt_pos.mpr ht).ne'))).div
    (continuousOn_const.mul continuousOn_id) (fun t ht => mul_ne_zero (by norm_num) ht.ne')

theorem continuous_scalarRadialGeneratorExpectation {r : ℕ} {N : ℝ}
    (hN : (r : ℝ) < N) {f : SymmetricMatrix (1 + r) → ℝ}
    (hf : f.HasTemperateGrowth) : Continuous (scalarRadialGeneratorExpectation N f) := by
  have hgen := hasTemperateGrowth_symmetricRadialGenerator hf N (scalarTransverseAxis r)
  exact (continuous_iff_continuousAt.mpr fun s =>
    (hasDerivAt_scalarRadiusExpectation hN hgen s).continuousAt).comp Real.continuous_sqrt

/-- The pointwise transverse radial ODE, for every real N>r. -/
theorem scalarRadialProfile_ode {r : ℕ} {N : ℝ}
    (hN : (r : ℝ) < N) {f : SymmetricMatrix (1 + r) → ℝ}
    (hf : f.HasTemperateGrowth) {t : ℝ} (ht : 0 < t) :
    4 * t * scalarRadialProfileSecondDerivative N f t +
      2 * N * scalarRadialProfileDerivative N f t = scalarRadialGeneratorExpectation N f t := by
  apply radial_ode_of_chiSquared_tests ((Nat.cast_nonneg r).trans_lt hN)
    (fun t ht => hasDerivAt_scalarRadialProfile hN hf ht)
    (fun t ht => hasDerivAt_scalarRadialProfileDerivative hN hf ht)
    (continuousOn_scalarRadialProfileSecondDerivative hN hf)
    (continuous_scalarRadialGeneratorExpectation hN hf).continuousOn _ t ht
  intro φ hφ hcφ hsφ
  exact scalarRadialProfile_weak_identity hN hf (hcφ.hasTemperateGrowth hφ)

theorem ae_scalarRadialMatrix_posSemidef {r : ℕ} (N s : ℝ) :
    ∀ᵐ x ∂scalarRegressionNoiseMeasure N r,
      (scalarRadialMatrix s x : Matrix (Fin (1 + r)) (Fin (1 + r)) ℝ).PosSemidef := by
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae
    (ae_posDef_nonsingularWishartMeasure (N - 1) (1 : Matrix (Fin r) (Fin r) ℝ))] with x hx
  have hres : ((scalarRadialDataCLM r x).1 : Matrix (Fin (1 + r)) (Fin (1 + r)) ℝ).PosSemidef := by
    rw [scalarRadialDataCLM_apply, Matrix.coe_symmetricCongruenceLinearMap_apply]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hx.posSemidef.mul_mul_conjTranspose_same (scalarNoiseMatrix r)
  exact hres.add (rankOneSymmetric_posSemidef _)

/-- Genuine radial monotonicity when the mean lies outside the Gaussian
covariance support. The source is the exact scalar-regression realization. -/
theorem monotoneOn_scalarRadialProfile_of_generator_nonneg {r : ℕ} {N : ℝ}
    (hN : (r : ℝ) < N) {f : SymmetricMatrix (1 + r) → ℝ}
    (hf : f.HasTemperateGrowth)
    (hgen : ∀ X : SymmetricMatrix (1 + r),
      (X : Matrix (Fin (1 + r)) (Fin (1 + r)) ℝ).PosSemidef →
      0 ≤ symmetricRadialGenerator N (scalarTransverseAxis r) f X) :
    MonotoneOn (scalarRadialProfile N f) (Ici 0) := by
  have hN0 : 0 < N := (Nat.cast_nonneg r).trans_lt hN
  have heven := scalarRadiusExpectation_even hN hf
  apply monotoneOn_of_radial_operator_nonneg_of_derivative_limit
    (N := N) (D := scalarRadialProfileDerivative N f)
    (D₂ := scalarRadialProfileSecondDerivative N f)
    (L := scalarRadiusSecondExpectation N f 0 / 2) hN0
  · exact ((continuous_iff_continuousAt.mpr fun s =>
      (hasDerivAt_scalarRadiusExpectation hN hf s).continuousAt).comp Real.continuous_sqrt).continuousOn
  · intro t ht
    exact hasDerivAt_scalarRadialProfile hN hf ht
  · intro t ht
    exact hasDerivAt_scalarRadialProfileDerivative hN hf ht
  · exact tendsto_sqrt_derivative_quotient
      (hasDerivAt_even_zero heven (hasDerivAt_scalarRadiusExpectation hN hf 0))
      (hasDerivAt_scalarRadiusFirstExpectation hN hf 0)
  · intro t ht
    rw [scalarRadialProfile_ode hN hf ht]
    apply integral_nonneg_of_ae
    filter_upwards [ae_scalarRadialMatrix_posSemidef N (Real.sqrt t)] with x hx
    exact hgen _ hx

end Wishart
end
end CanonicalSource9
