module

public import wishart.verified.field_analytic01
public import wishart.verified.field_spectral_moments
public import wishart.verified.field_residual09

/- Source: Wishart/FieldExampleFiniteMoments.lean -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The printed finite moments of the uncomposed field examples

Every assertion is for the actual density or Gaussian Gram law.  The norm
and polynomial envelopes are proved in SpectralExampleMoments, and all
compression eigenvalue moments are supplied by FieldSpectralMoments.  No
integrability, growth, or profile hypothesis is added to these conclusions.
-/

noncomputable section
open Matrix MeasureTheory Set
open WishartVerification
open scoped Classical Quaternion ComplexOrder MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace Wishart

theorem complex_polynomialPower_allFiniteMoments {p k : ℕ}
    (Sigma : Matrix (Fin p) (Fin p) ℂ) (hSigma : Sigma.PosDef)
    (B : Matrix (Fin p) (Fin k) ℂ) {c : ℝ} (hc : 0 ≤ c)
    (μ : Measure (ComplexMatrix.Hermitian p)) (hμ : IsSectionSevenComplexLaw Sigma μ)
    (P : MvPolynomial (Fin k) ℝ) {a : ℝ} (ha : 0 ≤ a) :
    HasAllFiniteMoments (fun X => (MvPolynomial.eval (FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe (ComplexMatrix.normalizedCompression B Sigma X + c •
        (⟨1, Matrix.isHermitian_one⟩ : ComplexMatrix.Hermitian k)))) P) ^ a) μ := by
  letI := hμ.isProbability hSigma
  exact (HasAllFiniteMoments.polynomial_eval P _
    (fun j => complex_shifted_eigenvalue_allFiniteMoments Sigma hSigma B hc μ hμ j)).rpow ha

theorem complex_tracePower_allFiniteMoments {p k : ℕ}
    (Sigma : Matrix (Fin p) (Fin p) ℂ) (hSigma : Sigma.PosDef)
    (B : Matrix (Fin p) (Fin k) ℂ) {c : ℝ} (hc : 0 ≤ c)
    (μ : Measure (ComplexMatrix.Hermitian p)) (hμ : IsSectionSevenComplexLaw Sigma μ)
    {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) :
    HasAllFiniteMoments (fun X => (CFC.rpow ((ComplexMatrix.normalizedCompression B Sigma X + c •
        (⟨1, Matrix.isHermitian_one⟩ : ComplexMatrix.Hermitian k)) : Matrix (Fin k) (Fin k) ℂ) r).trace.re ^ (a / r)) μ := by
  letI := hμ.isProbability hSigma
  let lam : ComplexMatrix.Hermitian p → Fin k → ℝ := fun X => FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe (ComplexMatrix.normalizedCompression B Sigma X + c •
        (⟨1, Matrix.isHermitian_one⟩ : ComplexMatrix.Hermitian k)))
  have h := (HasAllFiniteMoments.finset_sum Finset.univ
    (fun j X => lam X j ^ r) (fun j _ =>
      (complex_shifted_eigenvalue_allFiniteMoments Sigma hSigma B hc μ hμ j).rpow hr.le)).rpow
        (div_nonneg ha hr.le)
  apply h.congr_ae
  filter_upwards [hμ.ae_posSemidef] with X hX
  let S : ComplexMatrix.Hermitian k := ComplexMatrix.normalizedCompression B Sigma X + c • ⟨1, Matrix.isHermitian_one⟩
  have hS : (S : Matrix (Fin k) (Fin k) ℂ).PosSemidef :=
    (ComplexMatrix.normalizedCompression_posSemidef B Sigma X hX).add (Matrix.PosDef.one.posSemidef.smul hc)
  change (∑ j, (FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe S)) j ^ r) ^ (a / r) = (CFC.rpow (S : Matrix (Fin k) (Fin k) ℂ) r).trace.re ^ (a / r)
  rw [FieldSpectral.real_trace_rpow hS]

theorem complex_unitarilyInvariantNorm_power_allFiniteMoments {p k : ℕ}
    (Sigma : Matrix (Fin p) (Fin p) ℂ) (hSigma : Sigma.PosDef)
    (B : Matrix (Fin p) (Fin k) ℂ) {c : ℝ} (hc : 0 ≤ c)
    (μ : Measure (ComplexMatrix.Hermitian p)) (hμ : IsSectionSevenComplexLaw Sigma μ)
    (N : Spectral.UnitarilyInvariantNorm ℂ k) {a : ℝ} (ha : 0 ≤ a) :
    HasAllFiniteMoments (fun X => N (CFC.sqrt ((ComplexMatrix.normalizedCompression B Sigma X + c •
        (⟨1, Matrix.isHermitian_one⟩ : ComplexMatrix.Hermitian k)) : Matrix (Fin k) (Fin k) ℂ)) ^ a) μ := by
  letI := hμ.isProbability hSigma
  let S : ComplexMatrix.Hermitian p → ComplexMatrix.Hermitian k := fun X =>
    ComplexMatrix.normalizedCompression B Sigma X + c • ⟨1, Matrix.isHermitian_one⟩
  let lam : ComplexMatrix.Hermitian p → Fin k → ℝ := fun X => FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe (S X))
  have hm : Measurable S := (ComplexMatrix.measurable_normalizedCompression B Sigma).add measurable_const
  have hlam : Measurable lam := (FieldSpectral.continuous_orderedValues (𝕜 := ℂ) k).measurable.comp hm
  have hS (X : ComplexMatrix.Hermitian p) (hX : (X : Matrix (Fin p) (Fin p) ℂ).PosSemidef) :
      (S X : Matrix (Fin k) (Fin k) ℂ).PosSemidef :=
    (ComplexMatrix.normalizedCompression_posSemidef B Sigma X hX).add (Matrix.PosDef.one.posSemidef.smul hc)
  have h0 : ∀ᵐ X ∂μ, ∀ j, 0 ≤ lam X j := hμ.ae_posSemidef.mono fun X hX j =>
    FieldSpectral.orderedValues_nonneg (hS X hX) j
  have h := (N.diagonalNorm.sqrt_value_allFiniteMoments lam hlam h0
    (fun j => complex_shifted_eigenvalue_allFiniteMoments Sigma hSigma B hc μ hμ j)).rpow ha
  apply h.congr_ae
  filter_upwards [hμ.ae_posSemidef] with X hX
  change (N.diagonalNorm (fun j => Real.sqrt ((FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe (S X))) j))) ^ a =
    N (CFC.sqrt ((S X) : Matrix (Fin k) (Fin k) ℂ)) ^ a
  rw [Spectral.ComplexNorm.norm_sqrt_eq_diagonal N (S X) (hS X hX)]

open scoped Matrix.Norms.Frobenius in
theorem quaternion_polynomialPower_allFiniteMoments {p k : ℕ}
    (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) (hSigma : QuaternionMatrix.PosDef Sigma)
    (B : Matrix (Fin p) (Fin k) ℍ[ℝ]) {c : ℝ} (hc : 0 ≤ c)
    (μ : Measure (QuaternionMatrix.Hermitian p)) (hμ : IsSectionSevenQuaternionLaw Sigma μ)
    (P : MvPolynomial (Fin k) ℝ) {a : ℝ} (ha : 0 ≤ a) :
    HasAllFiniteMoments (fun X => (MvPolynomial.eval (QuaternionMatrix.orderedValues (QuaternionMatrix.normalizedCompression B Sigma X + c •
        (⟨1, Matrix.isHermitian_one⟩ : QuaternionMatrix.Hermitian k))) P) ^ a) μ := by
  letI := hμ.isProbability hSigma
  exact (HasAllFiniteMoments.polynomial_eval P _
    (fun j => quaternion_shifted_eigenvalue_allFiniteMoments Sigma hSigma B hc μ hμ j)).rpow ha

open scoped Matrix.Norms.Frobenius in
theorem quaternion_tracePower_allFiniteMoments {p k : ℕ}
    (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) (hSigma : QuaternionMatrix.PosDef Sigma)
    (B : Matrix (Fin p) (Fin k) ℍ[ℝ]) {c : ℝ} (hc : 0 ≤ c)
    (μ : Measure (QuaternionMatrix.Hermitian p)) (hμ : IsSectionSevenQuaternionLaw Sigma μ)
    {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) :
    HasAllFiniteMoments (fun X => (QuaternionMatrix.matrixRpow ((QuaternionMatrix.normalizedCompression B Sigma X + c •
        (⟨1, Matrix.isHermitian_one⟩ : QuaternionMatrix.Hermitian k)) : Matrix (Fin k) (Fin k) ℍ[ℝ]) r).trace.re ^ (a / r)) μ := by
  letI := hμ.isProbability hSigma
  let lam : QuaternionMatrix.Hermitian p → Fin k → ℝ := fun X => QuaternionMatrix.orderedValues (QuaternionMatrix.normalizedCompression B Sigma X + c •
        (⟨1, Matrix.isHermitian_one⟩ : QuaternionMatrix.Hermitian k))
  have h := (HasAllFiniteMoments.finset_sum Finset.univ
    (fun j X => lam X j ^ r) (fun j _ =>
      (quaternion_shifted_eigenvalue_allFiniteMoments Sigma hSigma B hc μ hμ j).rpow hr.le)).rpow
        (div_nonneg ha hr.le)
  apply h.congr_ae
  filter_upwards [hμ.ae_posSemidef] with X hX
  let S : QuaternionMatrix.Hermitian k := QuaternionMatrix.normalizedCompression B Sigma X + c • ⟨1, Matrix.isHermitian_one⟩
  have hS : QuaternionMatrix.PosSemidef (S : Matrix (Fin k) (Fin k) ℍ[ℝ]) :=
    (QuaternionMatrix.normalizedCompression_posSemidef B Sigma X hX).add (QuaternionMatrix.posDef_one.posSemidef.smul hc)
  change (∑ j, (QuaternionMatrix.orderedValues S) j ^ r) ^ (a / r) = (QuaternionMatrix.matrixRpow (S : Matrix (Fin k) (Fin k) ℍ[ℝ]) r).trace.re ^ (a / r)
  rw [QuaternionMatrix.real_trace_matrixRpow S hS]

open scoped Matrix.Norms.Frobenius in
theorem quaternion_unitarilyInvariantNorm_power_allFiniteMoments {p k : ℕ}
    (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) (hSigma : QuaternionMatrix.PosDef Sigma)
    (B : Matrix (Fin p) (Fin k) ℍ[ℝ]) {c : ℝ} (hc : 0 ≤ c)
    (μ : Measure (QuaternionMatrix.Hermitian p)) (hμ : IsSectionSevenQuaternionLaw Sigma μ)
    (N : Spectral.UnitarilyInvariantNorm ℍ[ℝ] k) {a : ℝ} (ha : 0 ≤ a) :
    HasAllFiniteMoments (fun X => N (QuaternionMatrix.sqrt (QuaternionMatrix.normalizedCompression B Sigma X + c •
        (⟨1, Matrix.isHermitian_one⟩ : QuaternionMatrix.Hermitian k))) ^ a) μ := by
  letI := hμ.isProbability hSigma
  let S : QuaternionMatrix.Hermitian p → QuaternionMatrix.Hermitian k := fun X =>
    QuaternionMatrix.normalizedCompression B Sigma X + c • ⟨1, Matrix.isHermitian_one⟩
  let lam : QuaternionMatrix.Hermitian p → Fin k → ℝ := fun X => QuaternionMatrix.orderedValues (S X)
  have hm : Measurable S := (QuaternionMatrix.measurable_normalizedCompression B Sigma).add measurable_const
  have hlam : Measurable lam := (QuaternionMatrix.continuous_orderedValues k).measurable.comp hm
  have hS (X : QuaternionMatrix.Hermitian p) (hX : QuaternionMatrix.PosSemidef (X : Matrix (Fin p) (Fin p) ℍ[ℝ])) :
      QuaternionMatrix.PosSemidef (S X : Matrix (Fin k) (Fin k) ℍ[ℝ]) :=
    (QuaternionMatrix.normalizedCompression_posSemidef B Sigma X hX).add (QuaternionMatrix.posDef_one.posSemidef.smul hc)
  have h0 : ∀ᵐ X ∂μ, ∀ j, 0 ≤ lam X j := hμ.ae_posSemidef.mono fun X hX j =>
    QuaternionMatrix.orderedValues_nonneg (S X) (hS X hX) j
  have h := (N.diagonalNorm.sqrt_value_allFiniteMoments lam hlam h0
    (fun j => quaternion_shifted_eigenvalue_allFiniteMoments Sigma hSigma B hc μ hμ j)).rpow ha
  apply h.congr_ae
  filter_upwards [hμ.ae_posSemidef] with X hX
  change (N.diagonalNorm (fun j => Real.sqrt ((QuaternionMatrix.orderedValues (S X)) j))) ^ a =
    N (QuaternionMatrix.sqrt (S X)) ^ a
  rw [Spectral.QuaternionNorm.norm_sqrt_eq_diagonal N (S X) (hS X hX)]

variable {p : ℕ} {ι : Type*} [Fintype ι]

theorem complex_polynomialPowers_finite_joint_moment
    (Sigma : Matrix (Fin p) (Fin p) ℂ) (hSigma : Sigma.PosDef)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℂ)
    (c a : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (ha : ∀ i, 0 ≤ a i)
    (P : ∀ i, MvPolynomial (Fin (k i)) ℝ)
    (μ : Measure (ComplexMatrix.Hermitian p)) (hμ : IsSectionSevenComplexLaw Sigma μ) :
    (∫⁻ X, ENNReal.ofReal (∏ i, (MvPolynomial.eval (FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe (ComplexMatrix.normalizedCompression (B i) Sigma X + c i •
        (⟨1, Matrix.isHermitian_one⟩ : ComplexMatrix.Hermitian (k i))))) (P i)) ^ a i) ∂μ) < ⊤ := by
  letI := hμ.isProbability hSigma
  exact HasAllFiniteMoments.finite_lintegral_product _ (fun i =>
    complex_polynomialPower_allFiniteMoments Sigma hSigma (B i) (hc i) μ hμ (P i) (ha i))

theorem complex_tracePowers_finite_joint_moment
    (Sigma : Matrix (Fin p) (Fin p) ℂ) (hSigma : Sigma.PosDef)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℂ)
    (c a : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (ha : ∀ i, 0 ≤ a i)
    (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (μ : Measure (ComplexMatrix.Hermitian p)) (hμ : IsSectionSevenComplexLaw Sigma μ) :
    (∫⁻ X, ENNReal.ofReal (∏ i, (CFC.rpow ((ComplexMatrix.normalizedCompression (B i) Sigma X + c i •
        (⟨1, Matrix.isHermitian_one⟩ : ComplexMatrix.Hermitian (k i))) : Matrix (Fin (k i)) (Fin (k i)) ℂ) (r i)).trace.re ^ (a i / r i)) ∂μ) < ⊤ := by
  letI := hμ.isProbability hSigma
  exact HasAllFiniteMoments.finite_lintegral_product _ (fun i =>
    complex_tracePower_allFiniteMoments Sigma hSigma (B i) (hc i) μ hμ (hr i) (ha i))

theorem complex_unitarilyInvariantNormPowers_finite_joint_moment
    (Sigma : Matrix (Fin p) (Fin p) ℂ) (hSigma : Sigma.PosDef)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℂ)
    (c a : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (ha : ∀ i, 0 ≤ a i)
    (N : ∀ i, Spectral.UnitarilyInvariantNorm ℂ (k i))
    (μ : Measure (ComplexMatrix.Hermitian p)) (hμ : IsSectionSevenComplexLaw Sigma μ) :
    (∫⁻ X, ENNReal.ofReal (∏ i, N i (CFC.sqrt ((ComplexMatrix.normalizedCompression (B i) Sigma X + c i •
        (⟨1, Matrix.isHermitian_one⟩ : ComplexMatrix.Hermitian (k i))) : Matrix (Fin (k i)) (Fin (k i)) ℂ)) ^ a i) ∂μ) < ⊤ := by
  letI := hμ.isProbability hSigma
  exact HasAllFiniteMoments.finite_lintegral_product _ (fun i =>
    complex_unitarilyInvariantNorm_power_allFiniteMoments Sigma hSigma (B i) (hc i) μ hμ (N i) (ha i))

open scoped Matrix.Norms.Frobenius in
theorem quaternion_polynomialPowers_finite_joint_moment
    (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) (hSigma : QuaternionMatrix.PosDef Sigma)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℍ[ℝ])
    (c a : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (ha : ∀ i, 0 ≤ a i)
    (P : ∀ i, MvPolynomial (Fin (k i)) ℝ)
    (μ : Measure (QuaternionMatrix.Hermitian p)) (hμ : IsSectionSevenQuaternionLaw Sigma μ) :
    (∫⁻ X, ENNReal.ofReal (∏ i, (MvPolynomial.eval (QuaternionMatrix.orderedValues (QuaternionMatrix.normalizedCompression (B i) Sigma X + c i •
        (⟨1, Matrix.isHermitian_one⟩ : QuaternionMatrix.Hermitian (k i)))) (P i)) ^ a i) ∂μ) < ⊤ := by
  letI := hμ.isProbability hSigma
  exact HasAllFiniteMoments.finite_lintegral_product _ (fun i =>
    quaternion_polynomialPower_allFiniteMoments Sigma hSigma (B i) (hc i) μ hμ (P i) (ha i))

open scoped Matrix.Norms.Frobenius in
theorem quaternion_tracePowers_finite_joint_moment
    (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) (hSigma : QuaternionMatrix.PosDef Sigma)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℍ[ℝ])
    (c a : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (ha : ∀ i, 0 ≤ a i)
    (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (μ : Measure (QuaternionMatrix.Hermitian p)) (hμ : IsSectionSevenQuaternionLaw Sigma μ) :
    (∫⁻ X, ENNReal.ofReal (∏ i, (QuaternionMatrix.matrixRpow ((QuaternionMatrix.normalizedCompression (B i) Sigma X + c i •
        (⟨1, Matrix.isHermitian_one⟩ : QuaternionMatrix.Hermitian (k i))) : Matrix (Fin (k i)) (Fin (k i)) ℍ[ℝ]) (r i)).trace.re ^ (a i / r i)) ∂μ) < ⊤ := by
  letI := hμ.isProbability hSigma
  exact HasAllFiniteMoments.finite_lintegral_product _ (fun i =>
    quaternion_tracePower_allFiniteMoments Sigma hSigma (B i) (hc i) μ hμ (hr i) (ha i))

open scoped Matrix.Norms.Frobenius in
theorem quaternion_unitarilyInvariantNormPowers_finite_joint_moment
    (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) (hSigma : QuaternionMatrix.PosDef Sigma)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℍ[ℝ])
    (c a : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (ha : ∀ i, 0 ≤ a i)
    (N : ∀ i, Spectral.UnitarilyInvariantNorm ℍ[ℝ] (k i))
    (μ : Measure (QuaternionMatrix.Hermitian p)) (hμ : IsSectionSevenQuaternionLaw Sigma μ) :
    (∫⁻ X, ENNReal.ofReal (∏ i, N i (QuaternionMatrix.sqrt (QuaternionMatrix.normalizedCompression (B i) Sigma X + c i •
        (⟨1, Matrix.isHermitian_one⟩ : QuaternionMatrix.Hermitian (k i)))) ^ a i) ∂μ) < ⊤ := by
  letI := hμ.isProbability hSigma
  exact HasAllFiniteMoments.finite_lintegral_product _ (fun i =>
    quaternion_unitarilyInvariantNorm_power_allFiniteMoments Sigma hSigma (B i) (hc i) μ hμ (N i) (ha i))

end Wishart

