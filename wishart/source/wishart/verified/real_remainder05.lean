module

public import wishart.verified.real_remainder04
public import Mathlib.Analysis.Convex.Approximation
public import Mathlib.Analysis.Convex.Continuous

/- Generated ordinary proof stage. See audit/staged_real_remainder/RealRemainder05/manifest.json. -/

@[expose] public section

section CanonicalSource40
/- Source: Wishart/OuterSpectralMoments.lean -/



/-! # Haar averages of the finite geometric outer approximations -/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open WishartVerification
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.Operator

namespace Wishart

variable {q m : ℕ} {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]

theorem fullSpectralConditionalMoment_finiteOuter_nonneg
    (n : ℝ) (C : Matrix (Fin m) (Fin m) ℝ) (K : Matrix (Fin q) (Fin m) ℝ)
    (O : Matrix (Fin q) (Fin q) ℝ)
    (k : κ → ℕ) (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin (q + m)) (Fin (k i)) ℝ) (a b : κ → ι → ℝ)
    (hB : ∀ i, (B i).PosSemidef) (lam : Fin q → ℝ) :
    0 ≤ fullSpectralConditionalMoment n C K (affineMaximumProduct 0 k B M a b) lam O := by
  apply integral_nonneg_of_ae
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae
    (ae_posDef_nonsingularWishartMeasure (n - q) C)] with x hx
  apply affineMaximumProduct_zero_nonneg k B M a b hB
  apply regressionGramWithMean_posSemidef
  simpa only [regressionNoiseLinearMap, Matrix.coe_symmetricCongruenceLinearMap_apply,
    Matrix.conjTranspose_eq_transpose_of_trivial] using
    hx.posSemidef.mul_mul_conjTranspose_same (regressionNoiseInjection q m)

theorem fullRegressionSpectralAverage_finiteOuter_nonneg
    (n : ℝ) (C : Matrix (Fin m) (Fin m) ℝ) (K : Matrix (Fin q) (Fin m) ℝ)
    (k : κ → ℕ) (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin (q + m)) (Fin (k i)) ℝ) (a b : κ → ι → ℝ)
    (hB : ∀ i, (B i).PosSemidef) (lam : Fin q → ℝ) :
    0 ≤ fullRegressionSpectralAverage n C K (affineMaximumProduct 0 k B M a b) lam := by
  unfold fullRegressionSpectralAverage
  apply parameterAverageOn_nonneg
  intro lam' _ O
  exact fullSpectralConditionalMoment_finiteOuter_nonneg n C K ↑O k B M a b hB lam'

theorem integrable_haar_fullSpectralConditionalMoment_finiteOuter
    {n : ℝ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (K : Matrix (Fin q) (Fin m) ℝ)
    (k : κ → ℕ) (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin (q + m)) (Fin (k i)) ℝ) (a b : κ → ι → ℝ)
    (ha : ∀ i j, 0 ≤ a i j) (lam : Fin q → ℝ) :
    Integrable (fun O : Spectral.Orth q =>
      fullSpectralConditionalMoment n C K (affineMaximumProduct 0 k B M a b) lam ↑O)
      (haarProb (Spectral.Orth q)) := by
  letI := isProbabilityMeasure_regressionNoiseMeasure hn hC
  exact (allFiniteMoments_affineMaximumProduct_of_entries 0 k B M a b ha _
    (allFiniteMoments_haarFullRegressionModel_entry hn hC K lam)).integrable.integral_prod_left

theorem monotoneOn_fullRegressionSpectralAverage_finiteOuter
    {n : ℝ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (K : Matrix (Fin q) (Fin m) ℝ)
    (k : κ → ℕ) (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin (q + m)) (Fin (k i)) ℝ) (a b : κ → ι → ℝ)
    (hB : ∀ i, (B i).PosSemidef) (ha : ∀ i j, 0 ≤ a i j)
    (hsize : ∀ i, min (k i : ℝ) (((1 + m : ℕ) : ℝ)) + 1 ≤ n - q + 1) :
    MonotoneOn (fullRegressionSpectralAverage n C K (affineMaximumProduct 0 k B M a b))
      (Spectral.positiveChamber q) := by
  apply parameterAverageOn_monotoneOn
  · intro lam hlam
    exact integrable_haar_fullSpectralConditionalMoment_finiteOuter hn hC K k B M a b ha lam
  · intro lam hlam lam' hlam' hle
    exact Filter.Eventually.of_forall fun O =>
      monotoneOn_fullSpectralConditionalMoment_finiteOuter hn hC K ↑O k B M a b hB ha hsize
        (fun i => (hlam.2 i).le) (fun i => (hlam'.2 i).le) hle

end Wishart
end
end CanonicalSource40

section CanonicalSource41
/- Source: Wishart/LaguerreAssociation.lean -/



noncomputable section

open MeasureTheory

namespace Wishart

/-- Association for the actual normalized real-Wishart eigenvalue law.
Its positive finite normalizer and complete density are proved, not assumed. -/
theorem integral_laguerre_mul_ge {p : ℕ} {n : ℝ} (hn : (p : ℝ) - 1 < n)
    {f g : (Fin p → ℝ) → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfmono : MonotoneOn f (Spectral.positiveChamber p))
    (hgmono : MonotoneOn g (Spectral.positiveChamber p))
    (hfi : Integrable f (regressionEigenLaw p n))
    (hgi : Integrable g (regressionEigenLaw p n))
    (hfgi : Integrable (fun x => f x * g x) (regressionEigenLaw p n)) :
    (∫ x, f x ∂regressionEigenLaw p n) * (∫ x, g x ∂regressionEigenLaw p n) ≤
      ∫ x, f x * g x ∂regressionEigenLaw p n := by
  obtain ⟨hZ0, hZtop, _⟩ := Spectral.identityEigenLaw_normalized_density hn
  have h := WishartVerification.lemma_2_1_association
    (Set.Ioi 0) measurableSet_Ioi (fun _ : Fin p => Spectral.laguerreWeight p n) 1
    (by norm_num) (fun _ => Spectral.measurable_laguerreWeight p n)
    (fun _ => Spectral.laguerreWeight_nonneg p n) hZ0 hZtop
    f g hfm hgm hf0 hg0 hfmono hgmono
  exact WishartVerification.integral_mul_le_of_lintegral_mul_le _ _ _
    hf0 hg0 hfi hgi hfgi h

end Wishart
end
end CanonicalSource41

section CanonicalSource42
/- Source: Wishart/FullRankCompressionSplit.lean -/



/-!
# Unrestricted splitting of a full-rank determinant factor

A full-rank normalized compression is the entire whitened matrix. Its selected
factor is a symmetric function of the whole spectrum. The other compression
determinants are Loewner-increasing, so their Haar average is coordinatewise
increasing. Association of the actual Laguerre law gives the split for every
real degree above p−1, with no additional rank threshold.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open WishartVerification
open scoped Matrix MatrixOrder Matrix.Norms.Operator

namespace Wishart

def wholeMatrixSpectralAverage {p : ℕ} (g : SymmetricMatrix p → ℝ) : (Fin p → ℝ) → ℝ :=
  parameterAverageOn (haarProb (Spectral.Orth p)) (Spectral.positiveChamber p)
    (fun x => g (regressionSpectralMatrix x))

@[fun_prop] theorem measurable_wholeMatrixSpectralAverage {p : ℕ}
    {g : SymmetricMatrix p → ℝ} (hg : Measurable g) :
    Measurable (wholeMatrixSpectralAverage g) :=
  parameterAverageOn_measurable _ _ (orderedChamber_measurable _ measurableSet_Ioi) _
    (hg.comp (measurable_regressionSpectralMatrix p))

theorem integral_wholeMatrixSpectralAverage {p : ℕ} {n : ℝ}
    (hn : (p : ℝ) - 1 < n) {g : SymmetricMatrix p → ℝ}
    (hgi : Integrable g (nonsingularWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ))) :
    (∫ X, g X ∂nonsingularWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ)) =
      ∫ lam, wholeMatrixSpectralAverage g lam ∂regressionEigenLaw p n := by
  letI := Spectral.laguerreLaw_isProbability hn
  rw [integral_regressionSpectralMatrix hn hgi.aestronglyMeasurable]
  exact (integral_parameterAverageOn _ _ _ (Spectral.ae_laguerreLaw_mem_chamber hn) _
    ((measurePreserving_regressionSpectralMatrix hn).integrable_comp_of_integrable hgi)).symm

theorem integrable_wholeMatrixSpectralAverage {p : ℕ} {n : ℝ}
    (hn : (p : ℝ) - 1 < n) {g : SymmetricMatrix p → ℝ}
    (hgi : Integrable g (nonsingularWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ))) :
    Integrable (wholeMatrixSpectralAverage g) (regressionEigenLaw p n) :=
  parameterAverageOn_integrable _ _ _ (Spectral.ae_laguerreLaw_mem_chamber hn) _
    ((measurePreserving_regressionSpectralMatrix hn).integrable_comp_of_integrable hgi)

theorem wholeMatrixSpectralAverage_compressionProduct_nonneg {p : ℕ}
    {ι : Type*} [Fintype ι] (D : ι → CompressionData p)
    (hB : ∀ i, (D i).offset.PosSemidef) (lam : Fin p → ℝ) :
    0 ≤ wholeMatrixSpectralAverage (compressionProduct D) lam :=
  parameterAverageOn_nonneg _ _ _ (fun lam hlam O =>
    compressionProduct_nonneg D hB (spectralMatrix_posSemidef O lam (fun i => (hlam.2 i).le))) lam

theorem integrable_haar_compressionProduct_spectral {p : ℕ}
    {ι : Type*} [Fintype ι] (D : ι → CompressionData p)
    (hη : ∀ i, 0 ≤ (D i).exponent) (lam : Fin p → ℝ) :
    Integrable (fun O : Spectral.Orth p => compressionProduct D (regressionSpectralMatrix (lam, O)))
      (haarProb (Spectral.Orth p)) := by
  apply HasAllFiniteMoments.integrable
  apply allFiniteMoments_compressionProduct_of_entries D hη
  intro i j
  apply allFiniteMoments_continuous_compact
  change Continuous (fun O : Spectral.Orth p =>
    (Spectral.conjugate O (Spectral.diagonalSym lam) : Matrix (Fin p) (Fin p) ℝ) i j)
  have hconj : Continuous (fun O : Spectral.Orth p =>
      Spectral.conjugate O (Spectral.diagonalSym lam)) :=
    (Spectral.continuous_conjugate p).comp (continuous_id.prodMk continuous_const)
  exact (continuous_apply j).comp ((continuous_apply i).comp hconj.subtype_val)

theorem monotoneOn_wholeMatrixSpectralAverage_compressionProduct {p : ℕ}
    {ι : Type*} [Fintype ι] (D : ι → CompressionData p)
    (hB : ∀ i, (D i).offset.PosSemidef) (hη : ∀ i, 0 ≤ (D i).exponent) :
    MonotoneOn (wholeMatrixSpectralAverage (compressionProduct D)) (Spectral.positiveChamber p) := by
  apply parameterAverageOn_monotoneOn
  · intro lam hlam
    exact integrable_haar_compressionProduct_spectral D hη lam
  · intro lam hlam lam' hlam' hle
    exact Filter.Eventually.of_forall fun O =>
      compressionProduct_loewner_mono D hB hη _ _
        (spectralMatrix_posSemidef O lam (fun i => (hlam.2 i).le))
        (spectralMatrix_difference_posSemidef O lam lam' hle)

theorem integral_shiftedMatrixDetPower_spectral {p : ℕ} {n c : ℝ}
    (hn : (p : ℝ) - 1 < n) (hc : 0 ≤ c) (η : ℝ) :
    (∫ X, shiftedMatrixDetPower c η X
      ∂nonsingularWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ)) =
      ∫ lam, shiftedSpectralDetPower c η lam ∂regressionEigenLaw p n := by
  letI := Spectral.laguerreLaw_isProbability hn
  rw [integral_regressionSpectralMatrix hn (shiftedMatrixDetPower_measurable c η).aestronglyMeasurable,
    integral_congr_ae (ae_shiftedMatrixDetPower_spectral hn hc η), integral_fun_fst]
  simp only [probReal_univ, one_smul]

theorem integrable_shifted_mul_wholeMatrix_source {p : ℕ} {n c : ℝ}
    (hn : (p : ℝ) - 1 < n) (hc : 0 ≤ c) (η : ℝ)
    {g : SymmetricMatrix p → ℝ}
    (hjoint : Integrable (fun X => shiftedMatrixDetPower c η X * g X)
      (nonsingularWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ))) :
    Integrable (fun x => shiftedSpectralDetPower c η x.1 * g (regressionSpectralMatrix x))
      ((regressionEigenLaw p n).prod (haarProb (Spectral.Orth p))) := by
  apply ((measurePreserving_regressionSpectralMatrix hn).integrable_comp_of_integrable hjoint).congr
  filter_upwards [ae_shiftedMatrixDetPower_spectral hn hc η] with x hx
  exact congrArg (fun r => r * g (regressionSpectralMatrix x)) hx

theorem integral_shifted_mul_wholeMatrixSpectralAverage {p : ℕ} {n c : ℝ}
    (hn : (p : ℝ) - 1 < n) (hc : 0 ≤ c) (η : ℝ)
    {g : SymmetricMatrix p → ℝ}
    (hjoint : Integrable (fun X => shiftedMatrixDetPower c η X * g X)
      (nonsingularWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ))) :
    (∫ X, shiftedMatrixDetPower c η X * g X
      ∂nonsingularWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ)) =
      ∫ lam, shiftedSpectralDetPower c η lam * wholeMatrixSpectralAverage g lam
        ∂regressionEigenLaw p n := by
  letI := Spectral.laguerreLaw_isProbability hn
  rw [integral_regressionSpectralMatrix hn hjoint.aestronglyMeasurable]
  have heq : (fun x => shiftedMatrixDetPower c η (regressionSpectralMatrix x) *
      g (regressionSpectralMatrix x)) =ᵐ[
      (regressionEigenLaw p n).prod (haarProb (Spectral.Orth p))]
      (fun x => shiftedSpectralDetPower c η x.1 * g (regressionSpectralMatrix x)) := by
    filter_upwards [ae_shiftedMatrixDetPower_spectral hn hc η] with x hx
    exact congrArg (fun r => r * g (regressionSpectralMatrix x)) hx
  rw [integral_congr_ae heq]
  exact (integral_mul_parameterAverageOn _ _ _ (Spectral.ae_laguerreLaw_mem_chamber hn) _ _
    (integrable_shifted_mul_wholeMatrix_source hn hc η hjoint)).symm

/-- The normalized full-rank determinant split, for every finite family of
overlapping compressions and every real shape in the nonsingular range. -/
theorem fullRank_shifted_power_split_identity {p : ℕ} {n c η : ℝ}
    (hn : (p : ℝ) - 1 < n) (hc : 0 ≤ c) (hη : 0 ≤ η)
    {ι : Type*} [Fintype ι] (D : ι → CompressionData p)
    (hB : ∀ i, (D i).offset.PosSemidef) (hDη : ∀ i, 0 ≤ (D i).exponent) :
    (∫ X, shiftedMatrixDetPower c η X
      ∂nonsingularWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ)) *
      (∫ X, compressionProduct D X
        ∂nonsingularWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ)) ≤
      ∫ X, shiftedMatrixDetPower c η X * compressionProduct D X
        ∂nonsingularWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ) := by
  letI := Spectral.laguerreLaw_isProbability hn
  have hgi := (allFiniteMoments_wishart_compressionProduct Matrix.PosDef.one hn D hDη).integrable
  have hji := ((allFiniteMoments_shiftedMatrixDetPower hn c hη).mul
    (allFiniteMoments_wishart_compressionProduct Matrix.PosDef.one hn D hDη)).integrable
  rw [integral_shiftedMatrixDetPower_spectral hn hc η,
    integral_wholeMatrixSpectralAverage hn hgi,
    integral_shifted_mul_wholeMatrixSpectralAverage hn hc η hji]
  apply integral_laguerre_mul_ge hn
    (shiftedSpectralDetPower_measurable c η)
    (measurable_wholeMatrixSpectralAverage (measurable_compressionProduct D))
    (shiftedSpectralDetPower_nonneg c η)
    (wholeMatrixSpectralAverage_compressionProduct_nonneg D hB)
    ((shiftedSpectralDetPower_monotone c η hη).monotoneOn _)
    (monotoneOn_wholeMatrixSpectralAverage_compressionProduct D hB hDη)
    (allFiniteMoments_shiftedSpectralDetPower hn hc hη).integrable
    (integrable_wholeMatrixSpectralAverage hn hgi)
  exact mul_parameterAverageOn_integrable _ _ _ (Spectral.ae_laguerreLaw_mem_chamber hn) _ _
    (integrable_shifted_mul_wholeMatrix_source hn hc η hji)

theorem compressionNormalization_shifted_rpow_full {p : ℕ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef)
    (B : Matrix (Fin p) (Fin p) ℝ) (hB : B.rank = p)
    (N : CompressionNormalization Sigma B) {c : ℝ} (hc : 0 ≤ c) (η : ℝ)
    (Y : SymmetricMatrix p) (hY : (Y : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    (Bᵀ * (Matrix.symmetricCongruenceLinearMap N.ambient Y : Matrix (Fin p) (Fin p) ℝ) * B +
      c • compressionScale Sigma B).det ^ η =
      (compressionScale Sigma B).det ^ η * shiftedMatrixDetPower c η Y := by
  have hsel : (Y : Matrix (Fin p) (Fin p) ℝ).submatrix (Fin.castLE N.q_le)
      (Fin.castLE N.q_le) = (Y : Matrix (Fin p) (Fin p) ℝ) := by ext i j; rfl
  rw [compressionNormalization_shifted_det hSigma B hB N c Y, hsel,
    Real.mul_rpow (compressionScale_posDef hSigma B hB).det_pos.le
      (hY.add (Matrix.PosSemidef.one.smul hc)).det_nonneg]
  rfl

/-- The full-rank part of manuscript Theorem 5.1 for determinant powers.
No overlap, compression-rank, or extra shape condition is imposed. -/
theorem fullRank_shifted_power_split {p : ℕ} {n : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (B : Matrix (Fin p) (Fin p) ℝ) (hB : B.rank = p)
    {c η : ℝ} (hc : 0 ≤ c) (hη : 0 ≤ η)
    {ι : Type*} [Fintype ι] (D : ι → CompressionData p)
    (hD : ∀ i, (D i).offset.PosSemidef) (hDη : ∀ i, 0 ≤ (D i).exponent) :
    (∫ X, (Bᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * B + c • compressionScale Sigma B).det ^ η
      ∂nonsingularWishartMeasure n Sigma) *
      (∫ X, compressionProduct D X ∂nonsingularWishartMeasure n Sigma) ≤
      ∫ X, (Bᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * B + c • compressionScale Sigma B).det ^ η *
        compressionProduct D X ∂nonsingularWishartMeasure n Sigma := by
  let N := compressionNormalization hSigma B hB
  let D' := pullbackCompressionData D N.ambient
  let a := (compressionScale Sigma B).det ^ η
  have ha : 0 ≤ a := Real.rpow_nonneg (compressionScale_posDef hSigma B hB).det_pos.le _
  have hpush := map_compressionNormalization n N
  have htransform (f : SymmetricMatrix p → ℝ) (hf : Measurable f) :
      (∫ X, f X ∂nonsingularWishartMeasure n Sigma) =
        ∫ Y, f (Matrix.symmetricCongruenceLinearMap N.ambient Y)
          ∂nonsingularWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ) := by
    rw [← hpush, integral_map (LinearMap.continuous_of_finiteDimensional _).measurable.aemeasurable
      hf.aestronglyMeasurable]
  let selected (X : SymmetricMatrix p) :=
    (Bᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * B + c • compressionScale Sigma B).det ^ η
  have hsmeas : Measurable selected := by dsimp [selected]; fun_prop
  have hselected : (∫ X, selected X ∂nonsingularWishartMeasure n Sigma) =
      a * ∫ Y, shiftedMatrixDetPower c η Y
        ∂nonsingularWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ) := by
    rw [htransform selected hsmeas, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_posDef_nonsingularWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ)] with Y hY
    exact compressionNormalization_shifted_rpow_full hSigma B hB N hc η Y hY.posSemidef
  have hremaining : (∫ X, compressionProduct D X ∂nonsingularWishartMeasure n Sigma) =
      ∫ Y, compressionProduct D' Y ∂nonsingularWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ) := by
    rw [htransform _ (measurable_compressionProduct D)]
    simp only [compressionProduct_congruence, D']
  have hjoint : (∫ X, selected X * compressionProduct D X ∂nonsingularWishartMeasure n Sigma) =
      a * ∫ Y, shiftedMatrixDetPower c η Y * compressionProduct D' Y
        ∂nonsingularWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ) := by
    rw [htransform (fun X => selected X * compressionProduct D X)
      (hsmeas.mul (measurable_compressionProduct D)), ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_posDef_nonsingularWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ)] with Y hY
    rw [show selected (Matrix.symmetricCongruenceLinearMap N.ambient Y) =
      a * shiftedMatrixDetPower c η Y from
        compressionNormalization_shifted_rpow_full hSigma B hB N hc η Y hY.posSemidef,
      compressionProduct_congruence, mul_assoc]
  change (∫ X, selected X ∂nonsingularWishartMeasure n Sigma) * _ ≤
    ∫ X, selected X * compressionProduct D X ∂nonsingularWishartMeasure n Sigma
  rw [hselected, hremaining, hjoint, mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (fullRank_shifted_power_split_identity hn hc hη D' hD hDη) ha

end Wishart
end
end CanonicalSource42

section CanonicalSource43
/- Source: Wishart/OverlapPowerSplit.lean -/



/-!+# The determinant-power splits for arbitrary overlapping compressions

The selected compression is normalized by an explicitly constructed invertible
ambient congruence. The entire remaining matrix, including its cross blocks,
is retained in the regression law. Its conditional spectral average is increasing
under exactly the manuscript's minimum-rank condition. The one-factor comparison
removes that condition for a pair. All moments below are actual Wishart moments;
their integrability and the Haar/Laguerre representation are derived internally.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open WishartVerification
open scoped Matrix MatrixOrder Matrix.Norms.Operator

namespace Wishart

def shiftedCompressionDetPower {p q : ℕ}
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (B : Matrix (Fin p) (Fin q) ℝ)
    (c η : ℝ) (X : SymmetricMatrix p) : ℝ :=
  (Bᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * B + c • compressionScale Sigma B).det ^ η

@[fun_prop] theorem measurable_shiftedCompressionDetPower {p q : ℕ}
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (B : Matrix (Fin p) (Fin q) ℝ)
    (c η : ℝ) : Measurable (shiftedCompressionDetPower Sigma B c η) := by
  unfold shiftedCompressionDetPower
  fun_prop

/-- A reusable assembly lemma with only the explicit conditional-average
monotonicity left as an auxiliary premise. The subsequent theorems instantiate
that premise with the proved radial comparison or the one-determinant comparison. -/
theorem regression_shifted_power_split_of_spectral_monotone
    {q m : ℕ} {n c η : ℝ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (hc : 0 ≤ c) (hη : 0 ≤ η)
    {ι : Type*} [Fintype ι] (D : ι → CompressionData (q + m))
    (hD : ∀ i, (D i).offset.PosSemidef) (hDη : ∀ i, 0 ≤ (D i).exponent)
    (hmono : MonotoneOn (fullRegressionSpectralAverage n C K (compressionProduct D))
      (Spectral.positiveChamber q)) :
    (∫ X, shiftedMatrixDetPower c η (principalSymmetricBlock (Fin.castAdd m) X)
      ∂nonsingularWishartMeasure n (regressionScale K C)) *
      (∫ X, compressionProduct D X ∂nonsingularWishartMeasure n (regressionScale K C)) ≤
      ∫ X, shiftedMatrixDetPower c η (principalSymmetricBlock (Fin.castAdd m) X) *
        compressionProduct D X ∂nonsingularWishartMeasure n (regressionScale K C) := by
  have hnq : (q : ℝ) - 1 < n := by
    push_cast at hn
    linarith [Nat.cast_nonneg (α := ℝ) m]
  letI := isProbabilityMeasure_nonsingularWishartMeasure (regressionScale_posDef K hC) hn
  letI := Spectral.laguerreLaw_isProbability hnq
  have hselected : HasAllFiniteMoments
      (fun X => shiftedMatrixDetPower c η (principalSymmetricBlock (Fin.castAdd m) X))
      (nonsingularWishartMeasure n (regressionScale K C)) :=
    (allFiniteMoments_shiftedMatrixDetPower hnq c hη).comp_measurePreserving
      ⟨measurable_principalSymmetricBlock _, map_regressionSelectedBlock hn K hC⟩
  have hremaining := allFiniteMoments_wishart_compressionProduct
    (regressionScale_posDef K hC) hn D hDη
  have hjoint := (hselected.mul hremaining).integrable
  have hspectral : ∀ lam ∈ Spectral.positiveChamber q, ∀ O : Spectral.Orth q,
      shiftedMatrixDetPower c η (regressionSpectralMatrix (lam, O)) =
        shiftedSpectralDetPower c η lam := by
    intro lam hlam O
    exact shiftedMatrixDetPower_conjugate_diagonal O hc η lam hlam.2
  rw [integral_fullRegression_selected_spectral hn K hC
      (shiftedMatrixDetPower_measurable c η) hspectral,
    integral_fullRegression_remaining_spectral hn K hC
      (measurable_compressionProduct D) hremaining.integrable,
    integral_fullRegression_joint_spectral hn K hC hspectral
      (measurable_compressionProduct D) hjoint]
  exact integral_laguerre_mul_ge hnq
    (shiftedSpectralDetPower_measurable c η)
    (measurable_fullRegressionSpectralAverage n C K (measurable_compressionProduct D))
    (shiftedSpectralDetPower_nonneg c η)
    (fullRegressionSpectralAverage_compressionProduct_nonneg n C K D hD)
    ((shiftedSpectralDetPower_monotone c η hη).monotoneOn _) hmono
    (allFiniteMoments_shiftedSpectralDetPower hnq hc hη).integrable
    (integrable_fullRegressionSpectralAverage hn K hC
      (measurable_compressionProduct D) hremaining.integrable)
    (integrable_selected_mul_fullRegressionSpectralAverage hn K hC hspectral
      (measurable_compressionProduct D) hjoint)

theorem identity_leading_shifted_power_split
    {q m : ℕ} {n c η : ℝ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (hc : 0 ≤ c) (hη : 0 ≤ η)
    {ι : Type*} [Fintype ι] (D : ι → CompressionData (q + m))
    (hD : ∀ i, (D i).offset.PosSemidef) (hDη : ∀ i, 0 ≤ (D i).exponent)
    (hsize : ∀ i, min ((D i).size : ℝ) (((1 + m : ℕ) : ℝ)) + 1 ≤ n - q + 1) :
    (∫ X, shiftedMatrixDetPower c η (principalSymmetricBlock (Fin.castAdd m) X)
      ∂nonsingularWishartMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)) *
      (∫ X, compressionProduct D X
        ∂nonsingularWishartMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)) ≤
      ∫ X, shiftedMatrixDetPower c η (principalSymmetricBlock (Fin.castAdd m) X) *
        compressionProduct D X
        ∂nonsingularWishartMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) := by
  have h := regression_shifted_power_split_of_spectral_monotone hn
    (0 : Matrix (Fin q) (Fin m) ℝ) Matrix.PosDef.one hc hη D hD hDη
    (monotoneOn_fullRegressionSpectralAverage_compressionProduct hn Matrix.PosDef.one
      0 D hD hDη hsize)
  simpa only [regressionScale_zero_one] using h

/-- The pair case has no condition beyond the full nonsingular real-shape range. -/
theorem identity_leading_shifted_power_pair
    {q m k : ℕ} {n c η θ : ℝ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (hc : 0 ≤ c) (hη : 0 ≤ η) (hθ : 0 ≤ θ)
    {E : Matrix (Fin k) (Fin k) ℝ} (hE : E.PosSemidef)
    (M : Matrix (Fin (q + m)) (Fin k) ℝ) :
    (∫ X, shiftedMatrixDetPower c η (principalSymmetricBlock (Fin.castAdd m) X)
      ∂nonsingularWishartMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)) *
      (∫ X, compressedDeterminant E M X ^ θ
        ∂nonsingularWishartMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)) ≤
      ∫ X, shiftedMatrixDetPower c η (principalSymmetricBlock (Fin.castAdd m) X) *
        compressedDeterminant E M X ^ θ
        ∂nonsingularWishartMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) := by
  have hmono : MonotoneOn
      (fullRegressionSpectralAverage n (1 : Matrix (Fin m) (Fin m) ℝ)
        (0 : Matrix (Fin q) (Fin m) ℝ) (compressionProduct (singleDetCompressionData E M θ)))
      (Spectral.positiveChamber q) := by
    have hf : compressionProduct (singleDetCompressionData E M θ) =
        fun X => compressedDeterminant E M X ^ θ :=
      funext (compressionProduct_singleDet E M θ)
    rw [hf]
    exact monotoneOn_fullRegressionSpectralAverage_singleDet_rpow
      hn Matrix.PosDef.one 0 hE M hθ
  simpa only [compressionProduct_singleDet, regressionScale_zero_one] using
    regression_shifted_power_split_of_spectral_monotone hn
      (0 : Matrix (Fin q) (Fin m) ℝ) Matrix.PosDef.one hc hη
      (singleDetCompressionData E M θ) (fun _ => hE) (fun _ => hθ) hmono

theorem compressionNormalization_shifted_rpow_sum {q m : ℕ}
    {Sigma : Matrix (Fin (q + m)) (Fin (q + m)) ℝ} (hSigma : Sigma.PosDef)
    (B : Matrix (Fin (q + m)) (Fin q) ℝ) (hB : B.rank = q)
    (N : CompressionNormalization Sigma B) {c : ℝ} (hc : 0 ≤ c) (η : ℝ)
    (Y : SymmetricMatrix (q + m))
    (hY : (Y : Matrix (Fin (q + m)) (Fin (q + m)) ℝ).PosSemidef) :
    shiftedCompressionDetPower Sigma B c η (Matrix.symmetricCongruenceLinearMap N.ambient Y) =
      (compressionScale Sigma B).det ^ η *
        shiftedMatrixDetPower c η (principalSymmetricBlock (Fin.castAdd m) Y) := by
  have heq : (Fin.castLE N.q_le : Fin q → Fin (q + m)) = Fin.castAdd m := by
    funext i
    apply Fin.ext
    rfl
  unfold shiftedCompressionDetPower
  rw [compressionNormalization_shifted_det hSigma B hB N c Y, heq,
    Real.mul_rpow (compressionScale_posDef hSigma B hB).det_pos.le
      ((hY.submatrix (Fin.castAdd m)).add (Matrix.PosSemidef.one.smul hc)).det_nonneg]
  rfl

/-- Transport of a concrete whitened split through the proved normalization law. -/
theorem compression_power_split_of_whitened_split {q m : ℕ} {n c η : ℝ}
    {Sigma : Matrix (Fin (q + m)) (Fin (q + m)) ℝ} (hSigma : Sigma.PosDef)
    (B : Matrix (Fin (q + m)) (Fin q) ℝ) (hB : B.rank = q)
    (hc : 0 ≤ c) {ι : Type*} [Fintype ι] (D : ι → CompressionData (q + m))
    (hidentity :
      (∫ X, shiftedMatrixDetPower c η (principalSymmetricBlock (Fin.castAdd m) X)
        ∂nonsingularWishartMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)) *
        (∫ X, compressionProduct
          (pullbackCompressionData D (compressionNormalization hSigma B hB).ambient) X
          ∂nonsingularWishartMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)) ≤
        ∫ X, shiftedMatrixDetPower c η (principalSymmetricBlock (Fin.castAdd m) X) *
          compressionProduct
            (pullbackCompressionData D (compressionNormalization hSigma B hB).ambient) X
          ∂nonsingularWishartMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)) :
    (∫ X, shiftedCompressionDetPower Sigma B c η X ∂nonsingularWishartMeasure n Sigma) *
      (∫ X, compressionProduct D X ∂nonsingularWishartMeasure n Sigma) ≤
      ∫ X, shiftedCompressionDetPower Sigma B c η X * compressionProduct D X
        ∂nonsingularWishartMeasure n Sigma := by
  let N := compressionNormalization hSigma B hB
  let D' := pullbackCompressionData D N.ambient
  let a := (compressionScale Sigma B).det ^ η
  have ha : 0 ≤ a := Real.rpow_nonneg (compressionScale_posDef hSigma B hB).det_pos.le _
  have hpush := map_compressionNormalization n N
  have htransform (f : SymmetricMatrix (q + m) → ℝ) (hf : Measurable f) :
      (∫ X, f X ∂nonsingularWishartMeasure n Sigma) =
        ∫ Y, f (Matrix.symmetricCongruenceLinearMap N.ambient Y)
          ∂nonsingularWishartMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) := by
    rw [← hpush, integral_map (LinearMap.continuous_of_finiteDimensional _).measurable.aemeasurable
      hf.aestronglyMeasurable]
  have hselected :
      (∫ X, shiftedCompressionDetPower Sigma B c η X ∂nonsingularWishartMeasure n Sigma) =
        a * ∫ Y, shiftedMatrixDetPower c η (principalSymmetricBlock (Fin.castAdd m) Y)
          ∂nonsingularWishartMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) := by
    rw [htransform _ (measurable_shiftedCompressionDetPower Sigma B c η), ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_posDef_nonsingularWishartMeasure n
      (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)] with Y hY
    exact compressionNormalization_shifted_rpow_sum hSigma B hB N hc η Y hY.posSemidef
  have hremaining : (∫ X, compressionProduct D X ∂nonsingularWishartMeasure n Sigma) =
      ∫ Y, compressionProduct D' Y
        ∂nonsingularWishartMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) := by
    rw [htransform _ (measurable_compressionProduct D)]
    simp only [compressionProduct_congruence, D']
  have hjoint :
      (∫ X, shiftedCompressionDetPower Sigma B c η X * compressionProduct D X
        ∂nonsingularWishartMeasure n Sigma) =
      a * ∫ Y, shiftedMatrixDetPower c η (principalSymmetricBlock (Fin.castAdd m) Y) *
        compressionProduct D' Y
        ∂nonsingularWishartMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) := by
    rw [htransform (fun X => shiftedCompressionDetPower Sigma B c η X * compressionProduct D X)
      ((measurable_shiftedCompressionDetPower Sigma B c η).mul
      (measurable_compressionProduct D)), ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_posDef_nonsingularWishartMeasure n
      (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)] with Y hY
    rw [compressionNormalization_shifted_rpow_sum hSigma B hB N hc η Y hY.posSemidef,
      compressionProduct_congruence, mul_assoc]
  rw [hselected, hremaining, hjoint, mul_assoc]
  exact mul_le_mul_of_nonneg_left hidentity ha

/-- The selected-factor assertion of Theorem 5.1 for all nonnegative determinant
powers. The threshold is exactly `min(q + kᵢ, p + 1) ≤ n` for every remaining
factor; the equivalent maximum formulation is recorded below. -/
theorem compression_power_selected_split {p q : ℕ} {n c η : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (B : Matrix (Fin p) (Fin q) ℝ) (hB : B.rank = q) (hc : 0 ≤ c) (hη : 0 ≤ η)
    {ι : Type*} [Fintype ι] (D : ι → CompressionData p)
    (hD : ∀ i, (D i).offset.PosSemidef) (hDη : ∀ i, 0 ≤ (D i).exponent)
    (hsize : ∀ i, min ((q : ℝ) + (D i).size) ((p : ℝ) + 1) ≤ n) :
    (∫ X, shiftedCompressionDetPower Sigma B c η X ∂nonsingularWishartMeasure n Sigma) *
      (∫ X, compressionProduct D X ∂nonsingularWishartMeasure n Sigma) ≤
      ∫ X, shiftedCompressionDetPower Sigma B c η X * compressionProduct D X
        ∂nonsingularWishartMeasure n Sigma := by
  have hqp : q ≤ p := (compressionNormalization hSigma B hB).q_le
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hqp
  apply compression_power_split_of_whitened_split hSigma B hB hc D
  apply identity_leading_shifted_power_split hn hc hη
    (pullbackCompressionData D (compressionNormalization hSigma B hB).ambient)
    (fun i => hD i) (fun i => hDη i)
  intro i
  change min ((D i).size : ℝ) (((1 + m : ℕ) : ℝ)) + 1 ≤ n - q + 1
  have hmin : min ((q : ℝ) + (D i).size) ((((q + m : ℕ) : ℝ)) + 1) =
      (q : ℝ) + min ((D i).size : ℝ) (((1 + m : ℕ) : ℝ)) := by
    have harith : (((q + m : ℕ) : ℝ)) + 1 = (q : ℝ) + (((1 + m : ℕ) : ℝ)) := by
      push_cast
      ring
    rw [harith, min_add_add_left]
  have hi := hsize i
  rw [hmin] at hi
  linarith

/-- The unrestricted pair assertion for determinant powers and arbitrary
overlapping full-column-rank selections, including singular fixed offsets. -/
theorem compression_power_pair {p q k : ℕ} {n c η θ : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (B : Matrix (Fin p) (Fin q) ℝ) (hB : B.rank = q)
    (hc : 0 ≤ c) (hη : 0 ≤ η) (hθ : 0 ≤ θ)
    {E : Matrix (Fin k) (Fin k) ℝ} (hE : E.PosSemidef)
    (M : Matrix (Fin p) (Fin k) ℝ) :
    (∫ X, shiftedCompressionDetPower Sigma B c η X ∂nonsingularWishartMeasure n Sigma) *
      (∫ X, compressedDeterminant E M X ^ θ ∂nonsingularWishartMeasure n Sigma) ≤
      ∫ X, shiftedCompressionDetPower Sigma B c η X * compressedDeterminant E M X ^ θ
        ∂nonsingularWishartMeasure n Sigma := by
  have hqp : q ≤ p := (compressionNormalization hSigma B hB).q_le
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hqp
  have hidentity := identity_leading_shifted_power_pair hn hc hη hθ hE
    ((compressionNormalization hSigma B hB).ambientᵀ * M)
  have hproduct : compressionProduct
      (pullbackCompressionData (singleDetCompressionData E M θ)
        (compressionNormalization hSigma B hB).ambient) =
      fun X => compressedDeterminant E
        ((compressionNormalization hSigma B hB).ambientᵀ * M) X ^ θ := by
    funext X
    exact compressionProduct_singleDet E
      ((compressionNormalization hSigma B hB).ambientᵀ * M) θ X
  have hsplit := compression_power_split_of_whitened_split (n := n) (c := c) (η := η)
    hSigma B hB hc (singleDetCompressionData E M θ)
    (by rw [hproduct]; exact hidentity)
  simpa only [compressionProduct_singleDet] using hsplit

/-- The finite maximum in manuscript condition (10) is exactly the family of
individual minimum-rank conditions used by the generator proof. -/
theorem compression_rank_threshold_iff {p q : ℕ} {n : ℝ}
    {ι : Type*} [Fintype ι] [Nonempty ι] (k : ι → ℕ) :
    min ((q : ℝ) + (Finset.univ.sup k : ℕ)) ((p : ℝ) + 1) ≤ n ↔
      ∀ i, min ((q : ℝ) + k i) ((p : ℝ) + 1) ≤ n := by
  classical
  constructor
  · intro h i
    have hk : (k i : ℝ) ≤ (Finset.univ.sup k : ℕ) :=
      Nat.cast_le.mpr (Finset.le_sup (Finset.mem_univ i))
    have hsum : (q : ℝ) + k i ≤ (q : ℝ) + (Finset.univ.sup k : ℕ) := by linarith
    have hmin : min ((q : ℝ) + k i) ((p : ℝ) + 1) ≤
        min ((q : ℝ) + (Finset.univ.sup k : ℕ)) ((p : ℝ) + 1) :=
      min_le_min hsum le_rfl
    exact hmin.trans h
  · intro h
    obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup
      (Finset.univ : Finset ι) Finset.univ_nonempty k
    simpa only [heq] using h i

theorem compression_power_selected_split_max {p q : ℕ} {n c η : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (B : Matrix (Fin p) (Fin q) ℝ) (hB : B.rank = q) (hc : 0 ≤ c) (hη : 0 ≤ η)
    {ι : Type*} [Fintype ι] [Nonempty ι] (D : ι → CompressionData p)
    (hD : ∀ i, (D i).offset.PosSemidef) (hDη : ∀ i, 0 ≤ (D i).exponent)
    (hsize : min ((q : ℝ) + (Finset.univ.sup (fun i => (D i).size) : ℕ))
      ((p : ℝ) + 1) ≤ n) :
    (∫ X, shiftedCompressionDetPower Sigma B c η X ∂nonsingularWishartMeasure n Sigma) *
      (∫ X, compressionProduct D X ∂nonsingularWishartMeasure n Sigma) ≤
      ∫ X, shiftedCompressionDetPower Sigma B c η X * compressionProduct D X
        ∂nonsingularWishartMeasure n Sigma :=
  compression_power_selected_split hSigma hn B hB hc hη D hD hDη
    ((compression_rank_threshold_iff (fun i => (D i).size)).mp hsize)

theorem shifted_compression_power_pair {p q k : ℕ} {n c d η θ : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (B : Matrix (Fin p) (Fin q) ℝ) (hB : B.rank = q)
    (M : Matrix (Fin p) (Fin k) ℝ) (hM : M.rank = k)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hη : 0 ≤ η) (hθ : 0 ≤ θ) :
    (∫ X, shiftedCompressionDetPower Sigma B c η X ∂nonsingularWishartMeasure n Sigma) *
      (∫ X, shiftedCompressionDetPower Sigma M d θ X ∂nonsingularWishartMeasure n Sigma) ≤
      ∫ X, shiftedCompressionDetPower Sigma B c η X * shiftedCompressionDetPower Sigma M d θ X
        ∂nonsingularWishartMeasure n Sigma := by
  simpa only [shiftedCompressionDetPower, compressedDeterminant, add_comm] using
    compression_power_pair hSigma hn B hB hc hη hθ
      ((compressionScale_posDef hSigma M hM).posSemidef.smul hd) M

theorem compression_power_selected_split_full {p q : ℕ} {n c η : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (B : Matrix (Fin p) (Fin q) ℝ) (hB : B.rank = q) (hqp : q = p)
    (hc : 0 ≤ c) (hη : 0 ≤ η)
    {ι : Type*} [Fintype ι] (D : ι → CompressionData p)
    (hD : ∀ i, (D i).offset.PosSemidef) (hDη : ∀ i, 0 ≤ (D i).exponent) :
    (∫ X, shiftedCompressionDetPower Sigma B c η X ∂nonsingularWishartMeasure n Sigma) *
      (∫ X, compressionProduct D X ∂nonsingularWishartMeasure n Sigma) ≤
      ∫ X, shiftedCompressionDetPower Sigma B c η X * compressionProduct D X
        ∂nonsingularWishartMeasure n Sigma := by
  subst q
  exact fullRank_shifted_power_split hSigma hn B hB hc hη D hD hDη

theorem shiftedCompressionDetPower_eq_one_of_size_zero {p q : ℕ}
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (B : Matrix (Fin p) (Fin q) ℝ)
    (c η : ℝ) (hq : q = 0) (X : SymmetricMatrix p) :
    shiftedCompressionDetPower Sigma B c η X = 1 := by
  subst q
  simp only [shiftedCompressionDetPower, Matrix.det_isEmpty, Real.one_rpow]

end Wishart
end
end CanonicalSource43

section CanonicalSource44
/- Source: Wishart/OuterSelectedTests.lean -/



/-! # Finite supporting-line tests on a selected shifted determinant -/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open WishartVerification
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.Operator

namespace WishartVerification

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem measurable_finiteMaximum {Ω : Type*} [MeasurableSpace Ω]
    (x : ι → Ω → ℝ) (hx : ∀ i, Measurable (x i)) :
    Measurable (fun z => finiteMaximum (fun i => x i z)) :=
  (continuous_finiteMaximum (fun i : ι => continuous_apply i)).measurable.comp
    (measurable_pi_iff.mpr hx)

def finiteShiftedDetTest {q : ℕ} (c : ℝ) (a b : ι → ℝ) (S : SymmetricMatrix q) : ℝ :=
  finiteMaximum (fun j => Real.exp (b j) * shiftedMatrixDetPower c (a j) S)

def finiteShiftedSpectralTest {q : ℕ} (c : ℝ) (a b : ι → ℝ) (lam : Fin q → ℝ) : ℝ :=
  finiteMaximum (fun j => Real.exp (b j) * shiftedSpectralDetPower c (a j) lam)

theorem measurable_finiteShiftedDetTest (q : ℕ) (c : ℝ) (a b : ι → ℝ) :
    Measurable (finiteShiftedDetTest (q := q) c a b) :=
  measurable_finiteMaximum _ fun j => measurable_const.mul (shiftedMatrixDetPower_measurable c (a j))

theorem measurable_finiteShiftedSpectralTest (q : ℕ) (c : ℝ) (a b : ι → ℝ) :
    Measurable (finiteShiftedSpectralTest (q := q) c a b) :=
  measurable_finiteMaximum _ fun j => measurable_const.mul (shiftedSpectralDetPower_measurable c (a j))

theorem finiteShiftedSpectralTest_nonneg (q : ℕ) (c : ℝ) (a b : ι → ℝ)
    (lam : Fin q → ℝ) : 0 ≤ finiteShiftedSpectralTest c a b lam :=
  finiteMaximum_nonneg fun j => mul_nonneg (Real.exp_pos _).le (shiftedSpectralDetPower_nonneg c (a j) lam)

theorem finiteShiftedSpectralTest_monotone (q : ℕ) (c : ℝ) (a b : ι → ℝ)
    (ha : ∀ j, 0 ≤ a j) : Monotone (finiteShiftedSpectralTest (q := q) c a b) := by
  intro lam lam' hle
  exact finiteMaximum_mono fun j => mul_le_mul_of_nonneg_left
    (shiftedSpectralDetPower_monotone c (a j) (ha j) hle) (Real.exp_pos _).le

theorem finiteShiftedDetTest_spectral {q : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (a b : ι → ℝ) (lam : Fin q → ℝ)
    (hlam : lam ∈ Wishart.Spectral.positiveChamber q) (O : Wishart.Spectral.Orth q) :
    finiteShiftedDetTest c a b (Wishart.regressionSpectralMatrix (lam, O)) =
      finiteShiftedSpectralTest c a b lam := by
  unfold finiteShiftedDetTest finiteShiftedSpectralTest
  congr 1
  funext j
  unfold Wishart.regressionSpectralMatrix
  rw [shiftedMatrixDetPower_conjugate_diagonal O hc (a j) lam hlam.2]

theorem allFiniteMoments_finiteShiftedDetTest {q : ℕ} {n c : ℝ}
    (hn : (q : ℝ) - 1 < n) (a b : ι → ℝ) (ha : ∀ j, 0 ≤ a j) :
    HasAllFiniteMoments (finiteShiftedDetTest (q := q) c a b)
      (nonsingularWishartMeasure n (1 : Matrix (Fin q) (Fin q) ℝ)) := by
  letI := isProbabilityMeasure_nonsingularWishartMeasure Matrix.PosDef.one hn
  exact hasAllFiniteMoments_finiteMaximum _ fun j =>
    (allFiniteMoments_shiftedMatrixDetPower hn c (ha j)).const_mul (Real.exp (b j))

theorem allFiniteMoments_finiteShiftedSpectralTest {q : ℕ} {n c : ℝ}
    (hn : (q : ℝ) - 1 < n) (hc : 0 ≤ c) (a b : ι → ℝ) (ha : ∀ j, 0 ≤ a j) :
    HasAllFiniteMoments (finiteShiftedSpectralTest (q := q) c a b)
      (Wishart.regressionEigenLaw q n) := by
  letI := Wishart.Spectral.laguerreLaw_isProbability hn
  exact hasAllFiniteMoments_finiteMaximum _ fun j =>
    (allFiniteMoments_shiftedSpectralDetPower hn hc (ha j)).const_mul (Real.exp (b j))

end WishartVerification

namespace Wishart

variable {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]

theorem identity_leading_finiteOuter_split_of_spectral_monotone
    {q m : ℕ} {n c : ℝ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (hc : 0 ≤ c) (a₀ b₀ : ι → ℝ) (ha₀ : ∀ j, 0 ≤ a₀ j)
    (k : κ → ℕ) (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin (q + m)) (Fin (k i)) ℝ) (a b : κ → ι → ℝ)
    (hB : ∀ i, (B i).PosSemidef) (ha : ∀ i j, 0 ≤ a i j)
    (hmono : MonotoneOn
      (fullRegressionSpectralAverage n (1 : Matrix (Fin m) (Fin m) ℝ)
        (0 : Matrix (Fin q) (Fin m) ℝ) (affineMaximumProduct 0 k B M a b))
      (Spectral.positiveChamber q)) :
    (∫ X, finiteShiftedDetTest c a₀ b₀ (principalSymmetricBlock (Fin.castAdd m) X)
      ∂nonsingularWishartMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)) *
      (∫ X, affineMaximumProduct 0 k B M a b X
        ∂nonsingularWishartMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)) ≤
      ∫ X, finiteShiftedDetTest c a₀ b₀ (principalSymmetricBlock (Fin.castAdd m) X) *
        affineMaximumProduct 0 k B M a b X
        ∂nonsingularWishartMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) := by
  have hnq : (q : ℝ) - 1 < n := by
    push_cast at hn
    linarith [Nat.cast_nonneg (α := ℝ) m]
  let K : Matrix (Fin q) (Fin m) ℝ := 0
  let C : Matrix (Fin m) (Fin m) ℝ := 1
  have hC : C.PosDef := Matrix.PosDef.one
  have hScale : regressionScale K C = 1 := regressionScale_zero_one q m
  letI := isProbabilityMeasure_nonsingularWishartMeasure (regressionScale_posDef K hC) hn
  letI := Spectral.laguerreLaw_isProbability hnq
  have hselected : HasAllFiniteMoments
      (fun X => finiteShiftedDetTest c a₀ b₀ (principalSymmetricBlock (Fin.castAdd m) X))
      (nonsingularWishartMeasure n (regressionScale K C)) :=
    (allFiniteMoments_finiteShiftedDetTest hnq a₀ b₀ ha₀).comp_measurePreserving
      ⟨measurable_principalSymmetricBlock _, map_regressionSelectedBlock hn K hC⟩
  have hremaining := allFiniteMoments_affineMaximumProduct_of_entries 0 k B M a b ha
    (fun X : SymmetricMatrix (q + m) => X)
    (fun i j => allFiniteMoments_wishart_entry (α := n) (Sigma := regressionScale K C) i j)
  have hjoint := (hselected.mul hremaining).integrable
  have hspectral := finiteShiftedDetTest_spectral (q := q) hc a₀ b₀
  have hgm := (continuous_affineMaximumProduct 0 k B M a b ha).measurable
  rw [← hScale]
  rw [integral_fullRegression_selected_spectral hn K hC
      (measurable_finiteShiftedDetTest q c a₀ b₀) hspectral,
    integral_fullRegression_remaining_spectral hn K hC hgm hremaining.integrable,
    integral_fullRegression_joint_spectral hn K hC hspectral hgm hjoint]
  exact integral_laguerre_mul_ge hnq
    (measurable_finiteShiftedSpectralTest q c a₀ b₀)
    (measurable_fullRegressionSpectralAverage n C K hgm)
    (finiteShiftedSpectralTest_nonneg q c a₀ b₀)
    (fullRegressionSpectralAverage_finiteOuter_nonneg n C K k B M a b hB)
    ((finiteShiftedSpectralTest_monotone q c a₀ b₀ ha₀).monotoneOn _)
    hmono
    (allFiniteMoments_finiteShiftedSpectralTest hnq hc a₀ b₀ ha₀).integrable
    (integrable_fullRegressionSpectralAverage hn K hC hgm hremaining.integrable)
    (integrable_selected_mul_fullRegressionSpectralAverage hn K hC hspectral hgm hjoint)

theorem identity_leading_finiteOuter_split
    {q m : ℕ} {n c : ℝ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (hc : 0 ≤ c) (a₀ b₀ : ι → ℝ) (ha₀ : ∀ j, 0 ≤ a₀ j)
    (k : κ → ℕ) (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin (q + m)) (Fin (k i)) ℝ) (a b : κ → ι → ℝ)
    (hB : ∀ i, (B i).PosSemidef) (ha : ∀ i j, 0 ≤ a i j)
    (hsize : ∀ i, min (k i : ℝ) (((1 + m : ℕ) : ℝ)) + 1 ≤ n - q + 1) :
    (∫ X, finiteShiftedDetTest c a₀ b₀ (principalSymmetricBlock (Fin.castAdd m) X)
      ∂nonsingularWishartMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)) *
      (∫ X, affineMaximumProduct 0 k B M a b X
        ∂nonsingularWishartMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)) ≤
      ∫ X, finiteShiftedDetTest c a₀ b₀ (principalSymmetricBlock (Fin.castAdd m) X) *
        affineMaximumProduct 0 k B M a b X
        ∂nonsingularWishartMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) := by
  apply identity_leading_finiteOuter_split_of_spectral_monotone hn hc a₀ b₀ ha₀ k B M a b hB ha
  exact monotoneOn_fullRegressionSpectralAverage_finiteOuter hn Matrix.PosDef.one
    (0 : Matrix (Fin q) (Fin m) ℝ) k B M a b hB ha hsize

end Wishart
end
end CanonicalSource44

section CanonicalSource45
/- Source: Wishart/OuterWholeMatrix.lean -/



/-! # Full-rank finite outer splits with no additional shape restriction -/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open WishartVerification
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.Operator

namespace Wishart

theorem integral_wholeMatrix_spectral_test {p : ℕ} {n : ℝ}
    (hn : (p : ℝ) - 1 < n) {h : SymmetricMatrix p → ℝ}
    {f : (Fin p → ℝ) → ℝ} (hm : Measurable h)
    (hspec : ∀ lam ∈ Spectral.positiveChamber p, ∀ O : Spectral.Orth p,
      h (regressionSpectralMatrix (lam, O)) = f lam) :
    (∫ X, h X ∂nonsingularWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ)) =
      ∫ lam, f lam ∂regressionEigenLaw p n := by
  letI := Spectral.laguerreLaw_isProbability hn
  rw [integral_regressionSpectralMatrix hn hm.aestronglyMeasurable]
  have heq : (fun x => h (regressionSpectralMatrix x)) =ᵐ[
      (regressionEigenLaw p n).prod (haarProb (Spectral.Orth p))] (fun x => f x.1) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae
      (Spectral.ae_laguerreLaw_mem_chamber hn)] with x hx
    exact hspec x.1 hx x.2
  rw [integral_congr_ae heq, integral_fun_fst]
  simp only [probReal_univ, one_smul]

theorem integrable_wholeMatrix_spectral_product_source {p : ℕ} {n : ℝ}
    (hn : (p : ℝ) - 1 < n) {h g : SymmetricMatrix p → ℝ}
    {f : (Fin p → ℝ) → ℝ}
    (hspec : ∀ lam ∈ Spectral.positiveChamber p, ∀ O : Spectral.Orth p,
      h (regressionSpectralMatrix (lam, O)) = f lam)
    (hjoint : Integrable (fun X => h X * g X)
      (nonsingularWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ))) :
    Integrable (fun x => f x.1 * g (regressionSpectralMatrix x))
      ((regressionEigenLaw p n).prod (haarProb (Spectral.Orth p))) := by
  apply ((measurePreserving_regressionSpectralMatrix hn).integrable_comp_of_integrable hjoint).congr
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae
    (Spectral.ae_laguerreLaw_mem_chamber hn)] with x hx
  change h (regressionSpectralMatrix (x.1, x.2)) * g (regressionSpectralMatrix x) =
    f x.1 * g (regressionSpectralMatrix x)
  rw [hspec x.1 hx x.2]

theorem integral_wholeMatrix_spectral_product {p : ℕ} {n : ℝ}
    (hn : (p : ℝ) - 1 < n) {h g : SymmetricMatrix p → ℝ}
    {f : (Fin p → ℝ) → ℝ}
    (hspec : ∀ lam ∈ Spectral.positiveChamber p, ∀ O : Spectral.Orth p,
      h (regressionSpectralMatrix (lam, O)) = f lam)
    (hjoint : Integrable (fun X => h X * g X)
      (nonsingularWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ))) :
    (∫ X, h X * g X ∂nonsingularWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ)) =
      ∫ lam, f lam * wholeMatrixSpectralAverage g lam ∂regressionEigenLaw p n := by
  letI := Spectral.laguerreLaw_isProbability hn
  rw [integral_regressionSpectralMatrix hn hjoint.aestronglyMeasurable]
  have heq : (fun x => h (regressionSpectralMatrix x) * g (regressionSpectralMatrix x)) =ᵐ[
      (regressionEigenLaw p n).prod (haarProb (Spectral.Orth p))]
      (fun x => f x.1 * g (regressionSpectralMatrix x)) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae
      (Spectral.ae_laguerreLaw_mem_chamber hn)] with x hx
    rw [hspec x.1 hx x.2]
  rw [integral_congr_ae heq]
  exact (integral_mul_parameterAverageOn _ _ _ (Spectral.ae_laguerreLaw_mem_chamber hn) _ _
    (integrable_wholeMatrix_spectral_product_source hn hspec hjoint)).symm

variable {p : ℕ} {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]

theorem affineMaximumProduct_loewner_mono
    (k : κ → ℕ) (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (a b : κ → ι → ℝ)
    (hB : ∀ i, (B i).PosSemidef) (ha : ∀ i j, 0 ≤ a i j)
    (X Y : SymmetricMatrix p)
    (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    (hXY : ((Y : Matrix (Fin p) (Fin p) ℝ) - X).PosSemidef) :
    affineMaximumProduct 0 k B M a b X ≤ affineMaximumProduct 0 k B M a b Y := by
  have heq (i : κ) (Z : SymmetricMatrix p) :
      (regularizedCompression 0 (B i) (M i) Z).det = compressedDeterminant (B i) (M i) Z := by
    simp only [regularizedCompression, compressionCLM_apply, compressedDeterminant,
      zero_smul, add_zero]
  simp only [affineMaximumProduct, heq]
  apply Finset.prod_le_prod₀
  · intro i hi
    exact finiteMaximum_nonneg fun j => mul_nonneg (Real.exp_pos _).le
      (Real.rpow_nonneg (compressedDeterminant_nonneg (hB i) (M i) hX) _)
  · intro i hi
    exact finiteMaximum_mono fun j => mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (compressedDeterminant_nonneg (hB i) (M i) hX)
        (compressedDeterminant_mono (hB i) (M i) X Y hX hXY) (ha i j)) (Real.exp_pos _).le

theorem integrable_haar_finiteOuter_spectral
    (k : κ → ℕ) (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (a b : κ → ι → ℝ)
    (ha : ∀ i j, 0 ≤ a i j) (lam : Fin p → ℝ) :
    Integrable (fun O : Spectral.Orth p =>
      affineMaximumProduct 0 k B M a b (regressionSpectralMatrix (lam, O)))
      (haarProb (Spectral.Orth p)) := by
  apply HasAllFiniteMoments.integrable
  apply allFiniteMoments_continuous_compact
  apply (continuous_affineMaximumProduct 0 k B M a b ha).comp
  change Continuous (fun O : Spectral.Orth p => Spectral.conjugate O (Spectral.diagonalSym lam))
  simpa only [Function.comp_def, Function.uncurry, id_eq] using
    (Spectral.continuous_conjugate p).comp
      (continuous_id.prodMk
        (continuous_const : Continuous (fun _ : Spectral.Orth p => Spectral.diagonalSym lam)))

theorem monotoneOn_wholeMatrixSpectralAverage_finiteOuter
    (k : κ → ℕ) (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (a b : κ → ι → ℝ)
    (hB : ∀ i, (B i).PosSemidef) (ha : ∀ i j, 0 ≤ a i j) :
    MonotoneOn (wholeMatrixSpectralAverage (affineMaximumProduct 0 k B M a b))
      (Spectral.positiveChamber p) := by
  apply parameterAverageOn_monotoneOn
  · intro lam hlam
    exact integrable_haar_finiteOuter_spectral k B M a b ha lam
  · intro lam hlam lam' hlam' hle
    exact Filter.Eventually.of_forall fun O => affineMaximumProduct_loewner_mono k B M a b hB ha _ _
      (spectralMatrix_posSemidef O lam (fun i => (hlam.2 i).le))
      (spectralMatrix_difference_posSemidef O lam lam' hle)

theorem fullRank_finiteOuter_split_identity {n c : ℝ}
    (hn : (p : ℝ) - 1 < n) (hc : 0 ≤ c)
    (a₀ b₀ : ι → ℝ) (ha₀ : ∀ j, 0 ≤ a₀ j)
    (k : κ → ℕ) (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (a b : κ → ι → ℝ)
    (hB : ∀ i, (B i).PosSemidef) (ha : ∀ i j, 0 ≤ a i j) :
    (∫ X, finiteShiftedDetTest c a₀ b₀ X
      ∂nonsingularWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ)) *
      (∫ X, affineMaximumProduct 0 k B M a b X
        ∂nonsingularWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ)) ≤
      ∫ X, finiteShiftedDetTest c a₀ b₀ X * affineMaximumProduct 0 k B M a b X
        ∂nonsingularWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ) := by
  letI := isProbabilityMeasure_nonsingularWishartMeasure Matrix.PosDef.one hn
  letI := Spectral.laguerreLaw_isProbability hn
  have hgm := (continuous_affineMaximumProduct 0 k B M a b ha).measurable
  have hgi := allFiniteMoments_affineMaximumProduct_of_entries 0 k B M a b ha
    (fun X : SymmetricMatrix p => X)
    (fun i j => allFiniteMoments_wishart_entry (α := n)
      (Sigma := (1 : Matrix (Fin p) (Fin p) ℝ)) i j)
  have hji := ((allFiniteMoments_finiteShiftedDetTest (c := c) hn a₀ b₀ ha₀).mul hgi).integrable
  have hspectral := finiteShiftedDetTest_spectral (q := p) hc a₀ b₀
  rw [integral_wholeMatrix_spectral_test hn (measurable_finiteShiftedDetTest p c a₀ b₀) hspectral,
    integral_wholeMatrixSpectralAverage hn hgi.integrable,
    integral_wholeMatrix_spectral_product hn hspectral hji]
  apply integral_laguerre_mul_ge hn
    (measurable_finiteShiftedSpectralTest p c a₀ b₀)
    (measurable_wholeMatrixSpectralAverage hgm)
    (finiteShiftedSpectralTest_nonneg p c a₀ b₀)
    (parameterAverageOn_nonneg _ _ _ (fun lam hlam O =>
      affineMaximumProduct_zero_nonneg k B M a b hB
        (spectralMatrix_posSemidef O lam (fun i => (hlam.2 i).le))))
    ((finiteShiftedSpectralTest_monotone p c a₀ b₀ ha₀).monotoneOn _)
    (monotoneOn_wholeMatrixSpectralAverage_finiteOuter k B M a b hB ha)
    (allFiniteMoments_finiteShiftedSpectralTest hn hc a₀ b₀ ha₀).integrable
    (integrable_wholeMatrixSpectralAverage hn hgi.integrable)
  exact mul_parameterAverageOn_integrable _ _ _ (Spectral.ae_laguerreLaw_mem_chamber hn) _ _
    (integrable_wholeMatrix_spectral_product_source hn hspectral hji)

end Wishart
end
end CanonicalSource45

section CanonicalSource46
/- Source: Wishart/ConvexLogApproximation.lean -/



/-!
# Finite supporting-line approximation of the logarithmic outer function

Finite convex increasing functions are approximated from below by increasing
finite maxima of affine functions with nonnegative slopes. No differentiability
or growth assumption is imposed on the limiting function.
-/

noncomputable section

open Set Filter Topology

namespace WishartVerification

/-- The paper's condition on a positive outer function, on its actual domain
`(0,∞)`. Values at nonpositive arguments do not enter this definition. -/
structure GeometricallyLogConvex (f : ℝ → ℝ) : Prop where
  positive : ∀ x, 0 < x → 0 < f x
  convex_log : ConvexOn ℝ Set.univ (fun s => Real.log (f (Real.exp s)))
  monotone_log : Monotone (fun s => Real.log (f (Real.exp s)))

theorem exp_log_profile_eq {f : ℝ → ℝ} (hf : GeometricallyLogConvex f)
    {x : ℝ} (hx : 0 < x) :
    Real.exp ((fun s => Real.log (f (Real.exp s))) (Real.log x)) = f x := by
  dsimp only
  rw [Real.exp_log hx, Real.exp_log (hf.positive x hx)]

theorem nonnegative_slope_of_affine_minorant {h : ℝ → ℝ} (hm : Monotone h)
    {a b : ℝ} (hab : ∀ x : ℝ, a * x + b ≤ h x) : 0 ≤ a := by
  by_contra ha
  have ha' : a < 0 := lt_of_not_ge ha
  have hb : b ≤ h 0 := by simpa using hab 0
  let t : ℝ := (h 0 - b + 1) / (-a)
  have ht : 0 < t := div_pos (by linarith) (neg_pos.mpr ha')
  have hbound := (hab (-t)).trans (hm (neg_nonpos.mpr ht.le))
  have heq : a * (-t) + b = h 0 + 1 := by
    dsimp [t]
    field_simp [ha'.ne]
    ring
  rw [heq] at hbound
  linarith

/-- The supporting lines are supplied by Mathlib's proved convex approximation
theorem. Their slopes are nonnegative because the target is increasing on all
of the real line. -/
theorem exists_nonnegative_affine_minorants {h : ℝ → ℝ}
    (hc : ConvexOn ℝ Set.univ h) (hm : Monotone h) :
    ∃ a b : ℕ → ℝ,
      (∀ i, 0 ≤ a i) ∧
      (∀ i x, a i * x + b i ≤ h x) ∧
      (∀ x, (⨆ i, a i * x + b i) = h x) := by
  have hcont : Continuous h := by
    simpa only [interior_univ, continuousOn_univ] using hc.continuousOn_interior
  obtain ⟨l, b, hle, hsup⟩ := hc.real_univ_sSup_of_nat_affine_eq hcont.lowerSemicontinuous
  have hl (i : ℕ) (x : ℝ) : l i x = l i 1 * x := by
    calc
      l i x = l i (x • (1 : ℝ)) := by simp
      _ = x • l i 1 := map_smul _ _ _
      _ = _ := by simp [mul_comm]
  have hminor (i : ℕ) (x : ℝ) : l i 1 * x + b i ≤ h x := by
    have hi := hle i x
    change l i x + b i ≤ h x at hi
    rw [hl i x] at hi
    exact hi
  refine ⟨fun i => l i 1, b,
    fun i => nonnegative_slope_of_affine_minorant hm (hminor i), hminor, ?_⟩
  intro x
  have hs := congrFun hsup x
  simp only [iSup_apply, Pi.add_apply, Function.const_apply] at hs
  calc
    (⨆ i, l i 1 * x + b i) = ⨆ i, l i x + b i := by
      apply congrArg iSup
      funext i
      rw [hl i x]
    _ = h x := hs

def affinePartialMaximum (a b : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (Finset.range (n + 1)).sup'
    (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero n)) (fun i => a i * x + b i)

theorem affinePartialMaximum_le {a b : ℕ → ℝ} {h : ℝ → ℝ}
    (hle : ∀ i x, a i * x + b i ≤ h x) (n : ℕ) (x : ℝ) :
    affinePartialMaximum a b n x ≤ h x :=
  Finset.sup'_le _ _ (fun i _ => hle i x)

theorem affine_le_partialMaximum (a b : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    a n * x + b n ≤ affinePartialMaximum a b n x := by
  unfold affinePartialMaximum
  exact Finset.le_sup' (fun i => a i * x + b i) (Finset.mem_range.mpr (Nat.lt_succ_self n))

theorem affinePartialMaximum_mono_index (a b : ℕ → ℝ) (x : ℝ) :
    Monotone (fun n => affinePartialMaximum a b n x) := by
  intro m n hmn
  unfold affinePartialMaximum
  exact Finset.sup'_mono _ (Finset.range_mono (Nat.add_le_add_right hmn 1)) _

theorem affinePartialMaximum_monotone {a b : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (n : ℕ) :
    Monotone (affinePartialMaximum a b n) := by
  intro x y hxy
  exact Finset.sup'_mono_fun (fun i _ => add_le_add
    (mul_le_mul_of_nonneg_left hxy (ha i)) le_rfl)

theorem affinePartialMaximum_tendsto {a b : ℕ → ℝ} {h : ℝ → ℝ}
    (hle : ∀ i x, a i * x + b i ≤ h x)
    (hsup : ∀ x, (⨆ i, a i * x + b i) = h x) (x : ℝ) :
    Tendsto (fun n => affinePartialMaximum a b n x) atTop (𝓝 (h x)) := by
  have hb : BddAbove (Set.range (fun n => affinePartialMaximum a b n x)) :=
    ⟨h x, by rintro _ ⟨n, rfl⟩; exact affinePartialMaximum_le hle n x⟩
  have heq : (⨆ n, affinePartialMaximum a b n x) = h x := by
    apply le_antisymm
    · exact ciSup_le (fun n => affinePartialMaximum_le hle n x)
    · rw [← hsup x]
      apply ciSup_le
      intro n
      exact (affine_le_partialMaximum a b n x).trans (le_ciSup hb n)
  simpa only [heq] using tendsto_atTop_ciSup (affinePartialMaximum_mono_index a b x) hb

/-- The finite approximants to the original positive outer function are
positive, bounded above by that function, and converge at every positive
argument. Thus the later expectation limit needs no new growth hypothesis. -/
theorem geometricallyLogConvex_approximants {f : ℝ → ℝ} (hf : GeometricallyLogConvex f) :
    ∃ a b : ℕ → ℝ, (∀ i, 0 ≤ a i) ∧
      ∀ x : ℝ, 0 < x →
        (∀ n, 0 < Real.exp (affinePartialMaximum a b n (Real.log x)) ∧
          Real.exp (affinePartialMaximum a b n (Real.log x)) ≤ f x) ∧
        Monotone (fun n => Real.exp (affinePartialMaximum a b n (Real.log x))) ∧
        Tendsto (fun n => Real.exp (affinePartialMaximum a b n (Real.log x)))
          atTop (𝓝 (f x)) := by
  obtain ⟨a, b, ha, hle, hsup⟩ := exists_nonnegative_affine_minorants
    hf.convex_log hf.monotone_log
  refine ⟨a, b, ha, fun x hx => ?_⟩
  refine ⟨fun n => ⟨Real.exp_pos _, ?_⟩, ?_, ?_⟩
  · rw [← exp_log_profile_eq hf hx]
    exact Real.exp_le_exp.mpr (affinePartialMaximum_le hle n (Real.log x))
  · exact Real.exp_monotone.comp (affinePartialMaximum_mono_index a b (Real.log x))
  · simpa only [Function.comp_def, exp_log_profile_eq hf hx] using Real.continuous_exp.continuousAt.tendsto.comp
      (affinePartialMaximum_tendsto hle hsup (Real.log x))

end WishartVerification
end
end CanonicalSource46

section CanonicalSource47
/- Source: Wishart/OuterFunctionLimit.lean -/



/-!
# The limit to general geometrically log-convex functions

This passage takes place in nonnegative extended integrals, so it imposes no
moment or polynomial-growth hypothesis on the limiting outer functions. The
arguments must be positive almost everywhere; applications prove that fact
from their actual matrix law.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal

namespace WishartVerification

theorem finiteMonomialMaximum_eq_exp_affineMaximum
    (a b : ℕ → ℝ) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    finiteMaximum (fun j : Fin (n + 1) => Real.exp (b j) * x ^ (a j)) =
      Real.exp (affinePartialMaximum a b n (Real.log x)) := by
  have heq (j : ℕ) : Real.exp (b j) * x ^ (a j) =
      Real.exp (a j * Real.log x + b j) := by
    rw [Real.rpow_def_of_pos hx, ← Real.exp_add]
    congr 1
    ring
  apply le_antisymm
  · apply finiteMaximum_le
    intro j
    rw [heq]
    apply Real.exp_le_exp.mpr
    unfold affinePartialMaximum
    exact Finset.le_sup' (fun k : ℕ => a k * Real.log x + b k)
      (Finset.mem_range.mpr j.isLt)
  · obtain ⟨j, hj, hmax⟩ := Finset.exists_mem_eq_sup'
      (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero n)) (fun j => a j * Real.log x + b j)
    let jf : Fin (n + 1) := ⟨j, Finset.mem_range.mp hj⟩
    change Real.exp ((Finset.range (n + 1)).sup' _ _) ≤ _
    rw [hmax]
    calc
      Real.exp (a j * Real.log x + b j) = Real.exp (b jf) * x ^ (a jf) := (heq j).symm
      _ ≤ _ := le_finiteMaximum
        (fun j : Fin (n + 1) => Real.exp (b j) * x ^ (a j)) jf

variable {κ : Type*} [Fintype κ]

def finiteOuterTest {ι : Type*} [Fintype ι] [Nonempty ι]
    (a b : κ → ι → ℝ) (d : κ → ℝ) : ℝ :=
  ∏ i, finiteMaximum (fun j => Real.exp (b i j) * (d i) ^ (a i j))

theorem continuous_finiteOuterTest {ι : Type*} [Fintype ι] [Nonempty ι]
    (a b : κ → ι → ℝ) (ha : ∀ i j, 0 ≤ a i j) : Continuous (finiteOuterTest a b) := by
  apply continuous_finsetProd
  intro i hi
  apply continuous_finiteMaximum
  intro j
  exact continuous_const.mul ((Real.continuous_rpow_const (ha i j)).comp (continuous_apply i))

def supportingOuterProduct (a b : κ → ℕ → ℝ) (n : ℕ) (d : κ → ℝ) : ℝ :=
  finiteOuterTest (fun i (j : Fin (n + 1)) => a i j)
    (fun i (j : Fin (n + 1)) => b i j) d

theorem supportingOuterProduct_eq (a b : κ → ℕ → ℝ) (n : ℕ)
    {d : κ → ℝ} (hd : ∀ i, 0 < d i) :
    supportingOuterProduct a b n d =
      ∏ i, Real.exp (affinePartialMaximum (a i) (b i) n (Real.log (d i))) := by
  unfold supportingOuterProduct finiteOuterTest
  apply Finset.prod_congr rfl
  intro i hi
  exact finiteMonomialMaximum_eq_exp_affineMaximum (a i) (b i) n (hd i)

theorem supportingOuterProduct_nonneg (a b : κ → ℕ → ℝ) (n : ℕ)
    {d : κ → ℝ} (hd : ∀ i, 0 < d i) :
    0 ≤ supportingOuterProduct a b n d := by
  rw [supportingOuterProduct_eq a b n hd]
  exact Finset.prod_nonneg (fun i _ => (Real.exp_pos _).le)

theorem supportingOuterProduct_mono_index (a b : κ → ℕ → ℝ)
    {d : κ → ℝ} (hd : ∀ i, 0 < d i) :
    Monotone (fun n => supportingOuterProduct a b n d) := by
  intro n m hnm
  change supportingOuterProduct a b n d ≤ supportingOuterProduct a b m d
  rw [supportingOuterProduct_eq a b n hd, supportingOuterProduct_eq a b m hd]
  apply Finset.prod_le_prod₀
  · intro i hi
    exact (Real.exp_pos _).le
  · intro i hi
    exact Real.exp_le_exp.mpr (affinePartialMaximum_mono_index (a i) (b i) _ hnm)

theorem supportingOuterProduct_tendsto (a b : κ → ℕ → ℝ) (f : κ → ℝ → ℝ)
    (hlimit : ∀ i x, 0 < x →
      Tendsto (fun n => Real.exp (affinePartialMaximum (a i) (b i) n (Real.log x)))
        atTop (𝓝 (f i x)))
    {d : κ → ℝ} (hd : ∀ i, 0 < d i) :
    Tendsto (fun n => supportingOuterProduct a b n d) atTop (𝓝 (∏ i, f i (d i))) := by
  simp only [supportingOuterProduct_eq a b _ hd]
  exact tendsto_finsetProd _ (fun i _ => hlimit i (d i) (hd i))

theorem supportingOuterProduct_lintegral_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (a b : κ → ℕ → ℝ) (ha : ∀ i n, 0 ≤ a i n) (f : κ → ℝ → ℝ)
    (hlimit : ∀ i x, 0 < x →
      Tendsto (fun n => Real.exp (affinePartialMaximum (a i) (b i) n (Real.log x)))
        atTop (𝓝 (f i x)))
    (d : Ω → κ → ℝ) (hdm : Measurable d)
    (hdpos : ∀ᵐ z ∂μ, ∀ i, 0 < d z i) :
    Tendsto (fun n => ∫⁻ z, ENNReal.ofReal (supportingOuterProduct a b n (d z)) ∂μ) atTop
      (𝓝 (∫⁻ z, ENNReal.ofReal (∏ i, f i (d z i)) ∂μ)) := by
  apply lintegral_tendsto_of_tendsto_of_monotone
  · intro n
    exact ((continuous_finiteOuterTest
      (fun i (j : Fin (n + 1)) => a i j)
      (fun i (j : Fin (n + 1)) => b i j)
      (fun i j => ha i j)).measurable.comp hdm).ennreal_ofReal.aemeasurable
  · filter_upwards [hdpos] with z hz
    intro n m hnm
    exact ENNReal.ofReal_le_ofReal (supportingOuterProduct_mono_index a b hz hnm)
  · filter_upwards [hdpos] with z hz
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (supportingOuterProduct_tendsto a b f hlimit hz)

/-- Every comparison for the finite nonnegative-slope approximants passes to
the paper's full outer-function class, including infinite expectations.
The finite comparisons in an application are supplied by the proved radial
generator and its two analytic limits. -/
theorem geometric_outer_comparison_of_finite_comparisons
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ)
    (d : Ω → κ → ℝ) (e : Ξ → κ → ℝ)
    (hdm : Measurable d) (hem : Measurable e)
    (hdpos : ∀ᵐ z ∂μ, ∀ i, 0 < d z i)
    (hepos : ∀ᵐ z ∂ν, ∀ i, 0 < e z i)
    (hfinite : ∀ n : ℕ, ∀ a b : κ → Fin (n + 1) → ℝ,
      (∀ i j, 0 ≤ a i j) →
      (∫⁻ z, ENNReal.ofReal (finiteOuterTest a b (d z)) ∂μ) ≤
        ∫⁻ z, ENNReal.ofReal (finiteOuterTest a b (e z)) ∂ν)
    (f : κ → ℝ → ℝ) (hf : ∀ i, GeometricallyLogConvex (f i)) :
    (∫⁻ z, ENNReal.ofReal (∏ i, f i (d z i)) ∂μ) ≤
      ∫⁻ z, ENNReal.ofReal (∏ i, f i (e z i)) ∂ν := by
  classical
  choose a b ha happrox using fun i => geometricallyLogConvex_approximants (hf i)
  have hlimit (i : κ) (x : ℝ) (hx : 0 < x) := (happrox i x hx).2.2
  exact le_of_tendsto_of_tendsto
    (supportingOuterProduct_lintegral_tendsto μ a b ha f hlimit d hdm hdpos)
    (supportingOuterProduct_lintegral_tendsto ν a b ha f hlimit e hem hepos)
    (Filter.Eventually.of_forall fun n =>
      hfinite n (fun i j => a i j) (fun i j => b i j) (fun i j => ha i j))

end WishartVerification
end
end CanonicalSource47

section CanonicalSource48
/- Source: Wishart/OuterNormalization.lean -/



/-!
# Covariance normalization of finite outer tests

The actual determinant of the selected compression's covariance is absorbed
in the intercept of each supporting line. The remaining compressions use the
same invertible ambient congruence. No scalar covariance or disjointness
hypothesis is introduced.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open WishartVerification
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.Operator

namespace Wishart

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def finiteCompressionDetTest {p q : ℕ}
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (Q : Matrix (Fin p) (Fin q) ℝ)
    (c : ℝ) (a b : ι → ℝ) (X : SymmetricMatrix p) : ℝ :=
  finiteMaximum (fun j => Real.exp (b j) * shiftedCompressionDetPower Sigma Q c (a j) X)

theorem measurable_finiteCompressionDetTest {p q : ℕ}
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (Q : Matrix (Fin p) (Fin q) ℝ)
    (c : ℝ) (a b : ι → ℝ) : Measurable (finiteCompressionDetTest Sigma Q c a b) :=
  measurable_finiteMaximum _ fun j =>
    measurable_const.mul (measurable_shiftedCompressionDetPower Sigma Q c (a j))

theorem compressionNormalization_finiteOuter {q m : ℕ}
    {Sigma : Matrix (Fin (q + m)) (Fin (q + m)) ℝ} (hSigma : Sigma.PosDef)
    (Q : Matrix (Fin (q + m)) (Fin q) ℝ) (hQ : Q.rank = q)
    (N : CompressionNormalization Sigma Q) {c : ℝ} (hc : 0 ≤ c)
    (a b : ι → ℝ) (Y : SymmetricMatrix (q + m))
    (hY : (Y : Matrix (Fin (q + m)) (Fin (q + m)) ℝ).PosSemidef) :
    finiteCompressionDetTest Sigma Q c a b (Matrix.symmetricCongruenceLinearMap N.ambient Y) =
      finiteShiftedDetTest c a
        (fun j => b j + Real.log (compressionScale Sigma Q).det * a j)
        (principalSymmetricBlock (Fin.castAdd m) Y) := by
  unfold finiteCompressionDetTest finiteShiftedDetTest
  congr 1
  funext j
  rw [compressionNormalization_shifted_rpow_sum hSigma Q hQ N hc (a j) Y hY,
    Real.rpow_def_of_pos (compressionScale_posDef hSigma Q hQ).det_pos, Real.exp_add]
  ring

theorem compression_finiteOuter_split_of_whitened_split {q m : ℕ} {n c : ℝ}
    {Sigma : Matrix (Fin (q + m)) (Fin (q + m)) ℝ} (hSigma : Sigma.PosDef) (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (Q : Matrix (Fin (q + m)) (Fin q) ℝ) (hQ : Q.rank = q) (hc : 0 ≤ c)
    (a₀ b₀ : ι → ℝ) (ha₀ : ∀ j, 0 ≤ a₀ j)
    {κ : Type*} [Fintype κ]
    (k : κ → ℕ) (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin (q + m)) (Fin (k i)) ℝ) (a b : κ → ι → ℝ)
    (hB : ∀ i, (B i).PosSemidef) (ha : ∀ i j, 0 ≤ a i j)
    (hidentity :
      let N := compressionNormalization hSigma Q hQ
      let b₀' := fun j => b₀ j + Real.log (compressionScale Sigma Q).det * a₀ j
      let M' := fun i => N.ambientᵀ * M i
      (∫ X, finiteShiftedDetTest c a₀ b₀' (principalSymmetricBlock (Fin.castAdd m) X)
        ∂nonsingularWishartMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)) *
        (∫ X, affineMaximumProduct 0 k B M' a b X
          ∂nonsingularWishartMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)) ≤
        ∫ X, finiteShiftedDetTest c a₀ b₀' (principalSymmetricBlock (Fin.castAdd m) X) *
          affineMaximumProduct 0 k B M' a b X
          ∂nonsingularWishartMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)) :
    (∫ X, finiteCompressionDetTest Sigma Q c a₀ b₀ X ∂nonsingularWishartMeasure n Sigma) *
      (∫ X, affineMaximumProduct 0 k B M a b X ∂nonsingularWishartMeasure n Sigma) ≤
      ∫ X, finiteCompressionDetTest Sigma Q c a₀ b₀ X * affineMaximumProduct 0 k B M a b X
        ∂nonsingularWishartMeasure n Sigma := by
  let N := compressionNormalization hSigma Q hQ
  let b₀' : ι → ℝ := fun j => b₀ j + Real.log (compressionScale Sigma Q).det * a₀ j
  let M' := fun i => N.ambientᵀ * M i
  have htransform (f : SymmetricMatrix (q + m) → ℝ) (hf : Measurable f) :
      (∫ X, f X ∂nonsingularWishartMeasure n Sigma) =
        ∫ Y, f (Matrix.symmetricCongruenceLinearMap N.ambient Y)
          ∂nonsingularWishartMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) := by
    rw [← map_compressionNormalization n N,
      integral_map (LinearMap.continuous_of_finiteDimensional _).measurable.aemeasurable
        hf.aestronglyMeasurable]
  have hs (Y : SymmetricMatrix (q + m))
      (hY : (Y : Matrix (Fin (q + m)) (Fin (q + m)) ℝ).PosDef) :
      finiteCompressionDetTest Sigma Q c a₀ b₀ (Matrix.symmetricCongruenceLinearMap N.ambient Y) =
        finiteShiftedDetTest c a₀ b₀' (principalSymmetricBlock (Fin.castAdd m) Y) :=
    compressionNormalization_finiteOuter hSigma Q hQ N hc a₀ b₀ Y hY.posSemidef
  have hselected :
      (∫ X, finiteCompressionDetTest Sigma Q c a₀ b₀ X ∂nonsingularWishartMeasure n Sigma) =
        ∫ Y, finiteShiftedDetTest c a₀ b₀' (principalSymmetricBlock (Fin.castAdd m) Y)
          ∂nonsingularWishartMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) := by
    rw [htransform _ (measurable_finiteCompressionDetTest Sigma Q c a₀ b₀)]
    apply integral_congr_ae
    exact (ae_posDef_nonsingularWishartMeasure n 1).mono hs
  have hremaining :
      (∫ X, affineMaximumProduct 0 k B M a b X ∂nonsingularWishartMeasure n Sigma) =
        ∫ Y, affineMaximumProduct 0 k B M' a b Y
          ∂nonsingularWishartMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) := by
    rw [htransform _ (continuous_affineMaximumProduct 0 k B M a b ha).measurable]
    simp only [affineMaximumProduct_congruence, M']
  have hjoint :
      (∫ X, finiteCompressionDetTest Sigma Q c a₀ b₀ X * affineMaximumProduct 0 k B M a b X
        ∂nonsingularWishartMeasure n Sigma) =
        ∫ Y, finiteShiftedDetTest c a₀ b₀' (principalSymmetricBlock (Fin.castAdd m) Y) *
          affineMaximumProduct 0 k B M' a b Y
          ∂nonsingularWishartMeasure n (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) := by
    rw [htransform _ ((measurable_finiteCompressionDetTest Sigma Q c a₀ b₀).fun_mul
      (continuous_affineMaximumProduct 0 k B M a b ha).measurable)]
    apply integral_congr_ae
    filter_upwards [ae_posDef_nonsingularWishartMeasure n
      (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)] with Y hY
    rw [hs Y hY, affineMaximumProduct_congruence]
  rw [hselected, hremaining, hjoint]
  exact hidentity

theorem compression_finiteOuter_selected_split {p q : ℕ} {n c : ℝ}
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (hn : (p : ℝ) - 1 < n)
    (Q : Matrix (Fin p) (Fin q) ℝ) (hQ : Q.rank = q) (hc : 0 ≤ c)
    (a₀ b₀ : ι → ℝ) (ha₀ : ∀ j, 0 ≤ a₀ j)
    {κ : Type*} [Fintype κ]
    (k : κ → ℕ) (B : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (M : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (a b : κ → ι → ℝ)
    (hB : ∀ i, (B i).PosSemidef) (ha : ∀ i j, 0 ≤ a i j)
    (hsize : ∀ i, min ((q : ℝ) + k i) ((p : ℝ) + 1) ≤ n) :
    (∫ X, finiteCompressionDetTest Sigma Q c a₀ b₀ X ∂nonsingularWishartMeasure n Sigma) *
      (∫ X, affineMaximumProduct 0 k B M a b X ∂nonsingularWishartMeasure n Sigma) ≤
      ∫ X, finiteCompressionDetTest Sigma Q c a₀ b₀ X * affineMaximumProduct 0 k B M a b X
        ∂nonsingularWishartMeasure n Sigma := by
  have hqp : q ≤ p := (compressionNormalization hSigma Q hQ).q_le
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hqp
  let N := compressionNormalization hSigma Q hQ
  let b₀' : ι → ℝ := fun j => b₀ j + Real.log (compressionScale Sigma Q).det * a₀ j
  let M' := fun i => N.ambientᵀ * M i
  apply compression_finiteOuter_split_of_whitened_split hSigma hn Q hQ hc a₀ b₀ ha₀ k B M a b hB ha
  apply identity_leading_finiteOuter_split hn hc a₀ b₀' ha₀ k B M' a b hB ha
  intro i
  have hmin : min ((q : ℝ) + k i) (((q + m : ℕ) : ℝ) + 1) =
      (q : ℝ) + min (k i : ℝ) (((1 + m : ℕ) : ℝ)) := by
    have harith : (((q + m : ℕ) : ℝ)) + 1 = (q : ℝ) + (((1 + m : ℕ) : ℝ)) := by
      push_cast
      ring
    rw [harith, min_add_add_left]
  have hi := hsize i
  rw [hmin] at hi
  linarith

end Wishart
end
end CanonicalSource48

section CanonicalSource49
/- Source: Wishart/IndependentProductIntegral.lean -/



/-! # Independent nonnegative real products

The identity is an actual Tonelli calculation, including infinite integrals.
This generic measure lemma is shared by the real and field limit arguments.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace WishartVerification

theorem lintegral_independent_real_product
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} [SFinite μ] [SFinite ν]
    {f : Ω → ℝ} {g : Ξ → ℝ} (hfm : AEMeasurable f μ) (hgm : AEMeasurable g ν)
    (hfpos : ∀ᵐ z ∂μ, 0 ≤ f z) :
    (∫⁻ z : Ω × Ξ, ENNReal.ofReal (f z.1 * g z.2) ∂μ.prod ν) =
      (∫⁻ z, ENNReal.ofReal (f z) ∂μ) * ∫⁻ z, ENNReal.ofReal (g z) ∂ν := by
  have heq : (fun z : Ω × Ξ => ENNReal.ofReal (f z.1 * g z.2)) =ᵐ[μ.prod ν]
      (fun z => ENNReal.ofReal (f z.1) * ENNReal.ofReal (g z.2)) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hfpos] with z hz
    exact ENNReal.ofReal_mul hz
  rw [lintegral_congr_ae heq]
  exact lintegral_prod_mul hfm.ennreal_ofReal hgm.ennreal_ofReal

end WishartVerification
end
end CanonicalSource49
