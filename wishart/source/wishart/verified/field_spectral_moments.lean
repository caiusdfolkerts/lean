module

public import wishart.verified.field_analytic01
public import wishart.verified.field_residual07
public import wishart.verified.field_residual09
public import wishart.verified.spectral_example_moments

/- Source: Wishart/FieldSpectralMoments.lean -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Actual moments of every shifted compression eigenvalue

Each nonnegative eigenvalue is bounded by the actual compression trace, and
that trace has a proved affine bound in the ambient trace.  The final law
wrappers discharge all trace and support premises from the literal density
or Gaussian Gram distribution.
-/

noncomputable section
open Matrix MeasureTheory Set
open WishartVerification
open scoped Classical Quaternion ComplexOrder MatrixOrder Matrix.Norms.L2Operator Ring

namespace Wishart.ComplexMatrix
variable {p k : ℕ}

theorem shiftedCompression_eigenvalue_allFiniteMoments_of_trace
    (Sigma : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin k) ℂ)
    {c : ℝ} (hc : 0 ≤ c) (μ : Measure (Hermitian p)) [IsFiniteMeasure μ]
    (hPSD : ∀ᵐ (X : Hermitian p) ∂μ, (X : Matrix (Fin p) (Fin p) ℂ).PosSemidef)
    (htrace : HasAllFiniteMoments (fun X : Hermitian p =>
      (X : Matrix (Fin p) (Fin p) ℂ).trace.re) μ) (j : Fin k) :
    HasAllFiniteMoments (fun X => FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe
      (normalizedCompression B Sigma X + c • (⟨1, Matrix.isHermitian_one⟩ : Hermitian k))) j) μ := by
  let R := B * (CFC.sqrt (compressionCovariance B Sigma))⁻¹
  let D : Matrix (Fin k) (Fin k) ℂ := c • 1
  let S : Hermitian p → Hermitian k := fun X =>
    normalizedCompression B Sigma X + c • ⟨1, Matrix.isHermitian_one⟩
  have hm : Measurable S := (measurable_normalizedCompression B Sigma).add measurable_const
  have hSm : Measurable (fun X => FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe (S X))) :=
    (FieldSpectral.continuous_orderedValues (𝕜 := ℂ) k).measurable.comp hm
  have hS (X : Hermitian p) (hX : (X : Matrix (Fin p) (Fin p) ℂ).PosSemidef) :
      (S X : Matrix (Fin k) (Fin k) ℂ).PosSemidef :=
    (normalizedCompression_posSemidef B Sigma X hX).add (Matrix.PosDef.one.posSemidef.smul hc)
  apply allFiniteMoments_of_nonnegative_bound ((measurable_pi_apply j).comp hSm)
    (hPSD.mono fun X hX => FieldSpectral.orderedValues_nonneg (hS X hX) j)
  · filter_upwards [hPSD] with X hX
    exact (FieldSpectral.orderedValues_le_trace (hS X hX) j).trans
      (FieldSpectral.realTrace_compression_add_le hX R D)
  · exact (htrace.const_mul (FieldSpectral.compressionTraceConstant R)).add
      (HasAllFiniteMoments.const D.trace.re)

end Wishart.ComplexMatrix

namespace Wishart.QuaternionMatrix
open scoped Matrix.Norms.Frobenius
variable {p k : ℕ}

theorem orderedValues_le_realTrace (A : Hermitian k) (hA : PosSemidef (A : Matrix (Fin k) (Fin k) ℍ[ℝ])) (j : Fin k) :
    orderedValues A j ≤ (A : Matrix (Fin k) (Fin k) ℍ[ℝ]).trace.re := by
  rw [orderedValues_eq_decomposition,
    (orderedEigenDecomposition (A : Matrix (Fin k) (Fin k) ℍ[ℝ]) (WishartVerification.hermitian_matrix_coe A)).trace_eq_sum]
  exact Finset.single_le_sum
    (fun i _ => (orderedEigenDecomposition (A : Matrix (Fin k) (Fin k) ℍ[ℝ]) (WishartVerification.hermitian_matrix_coe A)).values_nonneg hA i)
    (Finset.mem_univ j)

theorem shiftedCompression_eigenvalue_allFiniteMoments_of_trace
    (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) (B : Matrix (Fin p) (Fin k) ℍ[ℝ])
    {c : ℝ} (hc : 0 ≤ c) (μ : Measure (Hermitian p)) [IsFiniteMeasure μ]
    (hPSD : ∀ᵐ (X : Hermitian p) ∂μ, PosSemidef (X : Matrix (Fin p) (Fin p) ℍ[ℝ]))
    (htrace : HasAllFiniteMoments (fun X : Hermitian p =>
      (X : Matrix (Fin p) (Fin p) ℍ[ℝ]).trace.re) μ) (j : Fin k) :
    HasAllFiniteMoments (fun X => orderedValues
      (normalizedCompression B Sigma X + c • (⟨1, Matrix.isHermitian_one⟩ : Hermitian k)) j) μ := by
  let R := B * (sqrt (compressionCovariance B Sigma))⁻¹ʳ
  let D : Matrix (Fin k) (Fin k) ℍ[ℝ] := c • 1
  let S : Hermitian p → Hermitian k := fun X =>
    normalizedCompression B Sigma X + c • ⟨1, Matrix.isHermitian_one⟩
  have hm : Measurable S := (measurable_normalizedCompression B Sigma).add measurable_const
  have hSm : Measurable (fun X => orderedValues (S X)) :=
    (continuous_orderedValues k).measurable.comp hm
  have hS (X : Hermitian p) (hX : PosSemidef (X : Matrix (Fin p) (Fin p) ℍ[ℝ])) : PosSemidef (S X : Matrix (Fin k) (Fin k) ℍ[ℝ]) :=
    (normalizedCompression_posSemidef B Sigma X hX).add (posDef_one.posSemidef.smul hc)
  apply allFiniteMoments_of_nonnegative_bound ((measurable_pi_apply j).comp hSm)
    (hPSD.mono fun X hX => orderedValues_nonneg (S X) (hS X hX) j)
  · filter_upwards [hPSD] with X hX
    exact (orderedValues_le_realTrace (S X) (hS X hX) j).trans
      (realTrace_compression_add_le hX R D)
  · exact (htrace.const_mul (compressionTraceConstant R)).add
      (HasAllFiniteMoments.const D.trace.re)

end Wishart.QuaternionMatrix

namespace Wishart

theorem IsSectionSevenComplexLaw.isProbability {p : ℕ}
    {Sigma : Matrix (Fin p) (Fin p) ℂ} (hSigma : Sigma.PosDef)
    {μ : Measure (ComplexMatrix.Hermitian p)} (hμ : IsSectionSevenComplexLaw Sigma μ) :
    IsProbabilityMeasure μ := by
  rcases hμ with ⟨α, hα, rfl⟩ | ⟨n, hn, rfl⟩
  · exact ComplexMatrix.wishart_probability hα hSigma
  · infer_instance

theorem IsSectionSevenQuaternionLaw.isProbability {p : ℕ}
    {Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]} (hSigma : QuaternionMatrix.PosDef Sigma)
    {μ : Measure (QuaternionMatrix.Hermitian p)} (hμ : IsSectionSevenQuaternionLaw Sigma μ) :
    IsProbabilityMeasure μ := by
  rcases hμ with ⟨α, hα, rfl⟩ | ⟨n, hn, rfl⟩
  · exact QuaternionMatrix.wishart_probability hα hSigma
  · infer_instance

theorem IsSectionSevenComplexLaw.trace_allFiniteMoments {p : ℕ}
    {Sigma : Matrix (Fin p) (Fin p) ℂ} (hSigma : Sigma.PosDef)
    {μ : Measure (ComplexMatrix.Hermitian p)} (hμ : IsSectionSevenComplexLaw Sigma μ) :
    HasAllFiniteMoments (fun X : ComplexMatrix.Hermitian p =>
      (X : Matrix (Fin p) (Fin p) ℂ).trace.re) μ := by
  rcases hμ with ⟨α, hα, rfl⟩ | ⟨n, hn, rfl⟩
  · exact ComplexMatrix.trace_allFiniteMoments hα hSigma
  · exact ComplexMatrix.trace_gram_allFiniteMoments n Sigma

theorem IsSectionSevenQuaternionLaw.trace_allFiniteMoments {p : ℕ}
    {Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]} (hSigma : QuaternionMatrix.PosDef Sigma)
    {μ : Measure (QuaternionMatrix.Hermitian p)} (hμ : IsSectionSevenQuaternionLaw Sigma μ) :
    HasAllFiniteMoments (fun X : QuaternionMatrix.Hermitian p =>
      (X : Matrix (Fin p) (Fin p) ℍ[ℝ]).trace.re) μ := by
  rcases hμ with ⟨α, hα, rfl⟩ | ⟨n, hn, rfl⟩
  · exact QuaternionMatrix.trace_allFiniteMoments hα hSigma
  · exact QuaternionMatrix.trace_gram_allFiniteMoments n Sigma

theorem complex_shifted_eigenvalue_allFiniteMoments {p k : ℕ}
    (Sigma : Matrix (Fin p) (Fin p) ℂ) (hSigma : Sigma.PosDef)
    (B : Matrix (Fin p) (Fin k) ℂ) {c : ℝ} (hc : 0 ≤ c)
    (μ : Measure (ComplexMatrix.Hermitian p)) (hμ : IsSectionSevenComplexLaw Sigma μ) (j : Fin k) :
    HasAllFiniteMoments (fun X => FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe
      (ComplexMatrix.normalizedCompression B Sigma X + c •
        (⟨1, Matrix.isHermitian_one⟩ : ComplexMatrix.Hermitian k))) j) μ := by
  letI := hμ.isProbability hSigma
  exact ComplexMatrix.shiftedCompression_eigenvalue_allFiniteMoments_of_trace Sigma B hc μ
    hμ.ae_posSemidef (hμ.trace_allFiniteMoments hSigma) j

theorem quaternion_shifted_eigenvalue_allFiniteMoments {p k : ℕ}
    (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) (hSigma : QuaternionMatrix.PosDef Sigma)
    (B : Matrix (Fin p) (Fin k) ℍ[ℝ]) {c : ℝ} (hc : 0 ≤ c)
    (μ : Measure (QuaternionMatrix.Hermitian p)) (hμ : IsSectionSevenQuaternionLaw Sigma μ) (j : Fin k) :
    HasAllFiniteMoments (fun X => QuaternionMatrix.orderedValues
      (QuaternionMatrix.normalizedCompression B Sigma X + c •
        (⟨1, Matrix.isHermitian_one⟩ : QuaternionMatrix.Hermitian k)) j) μ := by
  letI := hμ.isProbability hSigma
  exact QuaternionMatrix.shiftedCompression_eigenvalue_allFiniteMoments_of_trace Sigma B hc μ
    hμ.ae_posSemidef (hμ.trace_allFiniteMoments hSigma) j

end Wishart
