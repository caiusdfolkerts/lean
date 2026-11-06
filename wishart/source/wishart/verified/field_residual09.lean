module

public import wishart.verified.field_residual08
public import Mathlib.Topology.Order.MonotoneConvergence
public import tau_ceti.analysis.matrix.functional_calculus
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/- Recovered canonical proof stage; see verification/recovery-patches.json. -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

section CanonicalSource80
/- Source: Wishart/FieldWhiteningDeterminants.lean -/



/-!
# The literal determinant under standardized compression

The scalar covariance factor is proved by undoing the actual square-root
whitening.  The identities include zero sample eigenvalues, arbitrary
nonnegative proportional shifts, and zero-column compressions.
-/

noncomputable section
open Matrix
open scoped Classical Quaternion ComplexOrder MatrixOrder Matrix.Norms.L2Operator Ring

namespace Wishart.FieldHermitian

theorem undo_shifted_congruence {F : Type*} [Ring F] [Algebra ℝ F]
    [StarRing F] [StarModule ℝ F] {p k : ℕ}
    (B R : Matrix (Fin p) (Fin k) F) (K C : Matrix (Fin k) (Fin k) F)
    (X : Matrix (Fin p) (Fin p) F) (c : ℝ)
    (hRK : R * K = B) (hgram : Kᴴ * K = C) :
    Kᴴ * (Rᴴ * X * R + c • (1 : Matrix (Fin k) (Fin k) F)) * K =
      Bᴴ * X * B + c • C := by
  calc
    _ = (R * K)ᴴ * X * (R * K) + c • (Kᴴ * K) := by
      simp only [Matrix.conjTranspose_mul, mul_add, add_mul, Matrix.mul_smul,
        Matrix.smul_mul, Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by rw [hRK, hgram]

end Wishart.FieldHermitian

namespace Wishart.ComplexMatrix
variable {p k : ℕ}

theorem unnormalize_shiftedCompression {Sigma : Matrix (Fin p) (Fin p) ℂ}
    (hSigma : Sigma.PosDef) (B : Matrix (Fin p) (Fin k) ℂ)
    (hB : Function.Injective B.mulVec) (X : Hermitian p) (c : ℝ) :
    (CFC.sqrt (compressionCovariance B Sigma))ᴴ *
        ((normalizedCompression B Sigma X : Matrix (Fin k) (Fin k) ℂ) + c • 1) *
          CFC.sqrt (compressionCovariance B Sigma) =
      Bᴴ * (X : Matrix (Fin p) (Fin p) ℂ) * B + c • compressionCovariance B Sigma := by
  let C := compressionCovariance B Sigma
  let K := CFC.sqrt C
  let R := B * K⁻¹
  have hC : C.PosDef := compressionCovariance_posDef hSigma hB
  have hK : K.PosDef := Matrix.isStrictlyPositive_iff_posDef.mp
    (Matrix.isStrictlyPositive_iff_posDef.mpr hC).sqrt
  have hunit : IsUnit K.det := (Matrix.isUnit_iff_isUnit_det K).mp hK.isUnit
  have hRK : R * K = B := by
    dsimp only [R]
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul K hunit, Matrix.mul_one]
  have hgram : Kᴴ * K = C := by
    rw [hK.isHermitian.eq]
    exact CFC.sqrt_mul_sqrt_self C hC.posSemidef.nonneg
  change Kᴴ * (Rᴴ * (X : Matrix (Fin p) (Fin p) ℂ) * R + c • 1) * K = _
  exact FieldHermitian.undo_shifted_congruence B R K C X c hRK hgram

theorem realDeterminant_eq_prod_orderedValues (A : Hermitian k) :
    realDeterminant (A : Matrix (Fin k) (Fin k) ℂ) =
      ∏ j, FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe A) j := by
  rw [realDeterminant_eq_prod_eigenvalues (WishartVerification.hermitian_matrix_coe A)]
  simp only [FieldSpectral.orderedValues_eq, Function.comp_apply]
  exact (Equiv.prod_comp (FieldSpectral.orderedIndex k)
    (WishartVerification.hermitian_matrix_coe A).eigenvalues).symm

theorem shiftedCompressionDeterminant_eq_covariance_mul
    {Sigma : Matrix (Fin p) (Fin p) ℂ} (hSigma : Sigma.PosDef)
    (B : Matrix (Fin p) (Fin k) ℂ) (hB : Function.Injective B.mulVec)
    (X : Hermitian p) (hX : (X : Matrix (Fin p) (Fin p) ℂ).PosSemidef)
    {c : ℝ} (hc : 0 ≤ c) :
    realDeterminant (Bᴴ * (X : Matrix (Fin p) (Fin p) ℂ) * B +
      c • compressionCovariance B Sigma) =
      realDeterminant (compressionCovariance B Sigma) *
        realDeterminant ((normalizedCompression B Sigma X + c •
          (⟨1, Matrix.isHermitian_one⟩ : Hermitian k)) : Matrix (Fin k) (Fin k) ℂ) := by
  let C := compressionCovariance B Sigma
  let K := CFC.sqrt C
  let S : Hermitian k := normalizedCompression B Sigma X + c • ⟨1, Matrix.isHermitian_one⟩
  have hC : C.PosDef := compressionCovariance_posDef hSigma hB
  have hK : K.PosDef := Matrix.isStrictlyPositive_iff_posDef.mp
    (Matrix.isStrictlyPositive_iff_posDef.mpr hC).sqrt
  have hgram : Kᴴ * K = C := by
    rw [hK.isHermitian.eq]
    exact CFC.sqrt_mul_sqrt_self C hC.posSemidef.nonneg
  have hS : (S : Matrix (Fin k) (Fin k) ℂ).PosSemidef :=
    (normalizedCompression_posSemidef B Sigma X hX).add
      (Matrix.PosDef.one.posSemidef.smul hc)
  have h := realDeterminant_congruence hS K
  rw [hgram] at h
  have hu := unnormalize_shiftedCompression hSigma B hB X c
  change Kᴴ * (S : Matrix (Fin k) (Fin k) _) * K =
    Bᴴ * (X : Matrix (Fin p) (Fin p) _) * B + c • C at hu
  rw [hu] at h
  exact h

theorem shiftedCompressionDeterminant_eq_covariance_eigenproduct
    {Sigma : Matrix (Fin p) (Fin p) ℂ} (hSigma : Sigma.PosDef)
    (B : Matrix (Fin p) (Fin k) ℂ) (hB : Function.Injective B.mulVec)
    (X : Hermitian p) (hX : (X : Matrix (Fin p) (Fin p) ℂ).PosSemidef)
    {c : ℝ} (hc : 0 ≤ c) :
    realDeterminant (Bᴴ * (X : Matrix (Fin p) (Fin p) ℂ) * B +
      c • compressionCovariance B Sigma) =
      realDeterminant (compressionCovariance B Sigma) *
        ∏ j, FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe
          (normalizedCompression B Sigma X + c •
            (⟨1, Matrix.isHermitian_one⟩ : Hermitian k))) j := by
  rw [shiftedCompressionDeterminant_eq_covariance_mul hSigma B hB X hX hc]
  exact congrArg (fun q => realDeterminant (compressionCovariance B Sigma) * q)
    (realDeterminant_eq_prod_orderedValues (normalizedCompression B Sigma X + c •
      (⟨1, Matrix.isHermitian_one⟩ : Hermitian k)))

end Wishart.ComplexMatrix

namespace Wishart.QuaternionMatrix
open scoped Matrix.Norms.Frobenius
variable {p k : ℕ}

theorem unnormalize_shiftedCompression {Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]}
    (hSigma : PosDef Sigma) (B : Matrix (Fin p) (Fin k) ℍ[ℝ])
    (hB : FullColumnRank B) (X : Hermitian p) (c : ℝ) :
    (sqrt (compressionCovariance B Sigma))ᴴ *
        ((normalizedCompression B Sigma X : Matrix (Fin k) (Fin k) ℍ[ℝ]) + c • 1) *
          sqrt (compressionCovariance B Sigma) =
      Bᴴ * (X : Matrix (Fin p) (Fin p) ℍ[ℝ]) * B + c • compressionCovariance B Sigma := by
  let C := compressionCovariance B Sigma
  let K := sqrt C
  let R := B * K⁻¹ʳ
  have hC : PosDef C := compressionCovariance_posDef hSigma hB
  have hK : PosDef K := hC.sqrt
  have hRK : R * K = B := by
    dsimp only [R]
    rw [Matrix.mul_assoc, Ring.inverse_mul_cancel K hK.isUnit, Matrix.mul_one]
  have hgram : Kᴴ * K = C := by
    rw [hK.isHermitian.eq]
    exact sqrt_mul_self hC.posSemidef
  change Kᴴ * (Rᴴ * (X : Matrix (Fin p) (Fin p) ℍ[ℝ]) * R + c • 1) * K = _
  exact FieldHermitian.undo_shifted_congruence B R K C X c hRK hgram

theorem shiftedCompressionDeterminant_eq_covariance_mul
    {Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]} (hSigma : PosDef Sigma)
    (B : Matrix (Fin p) (Fin k) ℍ[ℝ]) (hB : FullColumnRank B)
    (X : Hermitian p) (hX : PosSemidef (X : Matrix (Fin p) (Fin p) ℍ[ℝ])) {c : ℝ} (hc : 0 ≤ c) :
    positiveDeterminant (Bᴴ * (X : Matrix (Fin p) (Fin p) ℍ[ℝ]) * B +
      c • compressionCovariance B Sigma) =
      positiveDeterminant (compressionCovariance B Sigma) *
        positiveDeterminant ((normalizedCompression B Sigma X + c •
          (⟨1, Matrix.isHermitian_one⟩ : Hermitian k)) : Matrix (Fin k) (Fin k) ℍ[ℝ]) := by
  let C := compressionCovariance B Sigma
  let K := sqrt C
  let S : Hermitian k := normalizedCompression B Sigma X + c • ⟨1, Matrix.isHermitian_one⟩
  have hC : PosDef C := compressionCovariance_posDef hSigma hB
  have hK : PosDef K := hC.sqrt
  have hgram : Kᴴ * K = C := by
    rw [hK.isHermitian.eq]
    exact sqrt_mul_self hC.posSemidef
  have hS : PosSemidef (S : Matrix (Fin k) (Fin k) ℍ[ℝ]) := (normalizedCompression_posSemidef B Sigma X hX).add
    (posDef_one.posSemidef.smul hc)
  have h := positiveDeterminant_congruence hS K
  rw [hgram] at h
  have hu := unnormalize_shiftedCompression hSigma B hB X c
  change Kᴴ * (S : Matrix (Fin k) (Fin k) _) * K =
    Bᴴ * (X : Matrix (Fin p) (Fin p) _) * B + c • C at hu
  rw [hu] at h
  exact h

theorem shiftedCompressionDeterminant_eq_covariance_eigenproduct
    {Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]} (hSigma : PosDef Sigma)
    (B : Matrix (Fin p) (Fin k) ℍ[ℝ]) (hB : FullColumnRank B)
    (X : Hermitian p) (hX : PosSemidef (X : Matrix (Fin p) (Fin p) ℍ[ℝ])) {c : ℝ} (hc : 0 ≤ c) :
    positiveDeterminant (Bᴴ * (X : Matrix (Fin p) (Fin p) ℍ[ℝ]) * B +
      c • compressionCovariance B Sigma) =
      positiveDeterminant (compressionCovariance B Sigma) *
        ∏ j, orderedValues (normalizedCompression B Sigma X + c •
          (⟨1, Matrix.isHermitian_one⟩ : Hermitian k)) j := by
  rw [shiftedCompressionDeterminant_eq_covariance_mul hSigma B hB X hX hc]
  exact congrArg (fun q => positiveDeterminant (compressionCovariance B Sigma) * q)
    (positiveDeterminant_eq_mooreDeterminant
      (normalizedCompression B Sigma X + c • (⟨1, Matrix.isHermitian_one⟩ : Hermitian k))
      ((normalizedCompression_posSemidef B Sigma X hX).add (posDef_one.posSemidef.smul hc)))

end Wishart.QuaternionMatrix
end
end CanonicalSource80

section CanonicalSource81
/- Source: Wishart/CanonicalGeometricBoundary.lean -/



/-!
# The canonical value at zero of a positive geometric outer function

The printed positive-domain hypotheses already imply a finite nonnegative
right limit.  This file constructs that limit from the actual function and
proves continuity of its extension.  No value at zero is assumed.
-/

noncomputable section
open Set Filter Topology

namespace WishartVerification

def geometricRightLimit (f : ℝ → ℝ) : ℝ := ⨅ t : ℝ, f (Real.exp t)

def canonicalGeometricExtension (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if 0 < x then f x else geometricRightLimit f

@[simp] theorem canonicalGeometricExtension_zero (f : ℝ → ℝ) :
    canonicalGeometricExtension f 0 = geometricRightLimit f := by
  simp only [canonicalGeometricExtension, lt_self_iff_false, if_false]

theorem canonicalGeometricExtension_pos (f : ℝ → ℝ) {x : ℝ} (hx : 0 < x) :
    canonicalGeometricExtension f x = f x := if_pos hx

theorem GeometricallyLogConvex.geometricRightLimit_nonneg {f : ℝ → ℝ}
    (hf : GeometricallyLogConvex f) : 0 ≤ geometricRightLimit f :=
  le_ciInf fun t => (hf.positive _ (Real.exp_pos t)).le

theorem GeometricallyLogConvex.tendsto_right_limit {f : ℝ → ℝ}
    (hf : GeometricallyLogConvex f) :
    Tendsto f (𝓝[>] 0) (𝓝 (geometricRightLimit f)) := by
  have hm : Monotone (fun t : ℝ => f (Real.exp t)) := by
    intro t u htu
    exact hf.monotoneOn (Real.exp_pos t) (Real.exp_pos u) (Real.exp_le_exp.mpr htu)
  have hb : BddBelow (range (fun t : ℝ => f (Real.exp t))) := by
    refine ⟨0, ?_⟩
    rintro y ⟨t, rfl⟩
    exact (hf.positive _ (Real.exp_pos t)).le
  have h := (tendsto_atBot_ciInf hm hb).comp Real.tendsto_log_nhdsGT_zero
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp only [Function.comp_apply, Real.exp_log hx]

theorem GeometricallyLogConvex.canonicalExtension {f : ℝ → ℝ}
    (hf : GeometricallyLogConvex f) :
    GeometricallyLogConvex (canonicalGeometricExtension f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [canonicalGeometricExtension_pos f hx]
    exact hf.positive x hx
  · simpa only [canonicalGeometricExtension_pos f (Real.exp_pos _)] using hf.convex_log
  · simpa only [canonicalGeometricExtension_pos f (Real.exp_pos _)] using hf.monotone_log

theorem GeometricallyLogConvex.canonicalExtension_continuous_zero {f : ℝ → ℝ}
    (hf : GeometricallyLogConvex f) :
    ContinuousWithinAt (canonicalGeometricExtension f) (Ici 0) 0 := by
  have hright : ContinuousWithinAt (canonicalGeometricExtension f) (Ioi 0) 0 := by
    rw [ContinuousWithinAt, canonicalGeometricExtension_zero]
    apply hf.tendsto_right_limit.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (canonicalGeometricExtension_pos f hx).symm
  have hset : Ioi (0 : ℝ) ∪ {0} = Ici 0 := by
    ext x
    simp only [mem_union, mem_Ioi, mem_singleton_iff, mem_Ici]
    constructor
    · rintro (hx | rfl)
      · exact hx.le
      · exact le_rfl
    · intro hx
      rcases hx.eq_or_lt with heq | hlt
      · exact Or.inr heq.symm
      · exact Or.inl hlt
  rw [← hset]
  exact hright.union continuousWithinAt_singleton

theorem GeometricallyLogConvex.canonicalExtension_on_nonnegative {f : ℝ → ℝ}
    (hf : GeometricallyLogConvex f) :
    GeometricOuterOnNonnegative (canonicalGeometricExtension f) :=
  ⟨hf.canonicalExtension, by simpa only [canonicalGeometricExtension_zero] using
      hf.geometricRightLimit_nonneg, hf.canonicalExtension_continuous_zero⟩

/-- The canonical extension agrees with every continuous right extension of
the same positive function, including the boundary convention in the paper. -/
theorem canonicalGeometricExtension_unique {f g : ℝ → ℝ}
    (hf : GeometricallyLogConvex f) (hg : ContinuousWithinAt g (Ici 0) 0)
    (heq : ∀ x, 0 < x → g x = f x) :
    EqOn g (canonicalGeometricExtension f) (Ici 0) := by
  have hzero : g 0 = geometricRightLimit f := by
    apply tendsto_nhds_unique (hg.mono Ioi_subset_Ici_self)
    apply hf.tendsto_right_limit.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (heq x hx).symm
  intro x hx
  rcases hx.eq_or_lt with heq0 | hpos
  · subst x
    simpa only [canonicalGeometricExtension_zero] using hzero
  · rw [canonicalGeometricExtension_pos f hpos]
    exact heq x hpos

theorem geometricallyLogConvex_rpow {a : ℝ} (ha : 0 ≤ a) :
    GeometricallyLogConvex (fun x : ℝ => x ^ a) := by
  have hlog (t : ℝ) : Real.log ((Real.exp t) ^ a) = a * t := by
    rw [Real.log_rpow (Real.exp_pos t), Real.log_exp]
  refine ⟨fun x hx => Real.rpow_pos_of_pos hx a, ?_, ?_⟩
  · refine ⟨convex_univ, ?_⟩
    intro x hx y hy u v hu hv huv
    simp only [hlog, smul_eq_mul]
    exact le_of_eq (by ring)
  · intro x y hxy
    simpa only [hlog] using mul_le_mul_of_nonneg_left hxy ha

theorem canonicalGeometricExtension_rpow {a x : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) :
    canonicalGeometricExtension (fun t : ℝ => t ^ a) x = x ^ a :=
  (canonicalGeometricExtension_unique (geometricallyLogConvex_rpow ha)
    (Real.continuous_rpow_const ha).continuousWithinAt (fun _ _ => rfl) hx).symm

end WishartVerification
end
end CanonicalSource81

section CanonicalSource82
/- Source: Wishart/FieldDeterminantExamples.lean -/



/-!
# Geometric outer functions of literal unnormalized determinants

The positive-domain outer functions have their actual canonical right limit
at zero.  The covariance determinant is absorbed into the profile only after
the matrix whitening identity has been proved.  The displayed factors are
therefore the literal shifted compression determinants from the manuscript.
-/

noncomputable section
open Matrix MeasureTheory Set
open WishartVerification
open scoped Classical Quaternion ComplexOrder MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace Wishart
variable {p : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem IsSectionSevenComplexLaw.ae_posSemidef
    {Sigma : Matrix (Fin p) (Fin p) ℂ} {μ : Measure (ComplexMatrix.Hermitian p)}
    (hμ : IsSectionSevenComplexLaw Sigma μ) :
    ∀ᵐ (X : ComplexMatrix.Hermitian p) ∂μ, (X : Matrix (Fin p) (Fin p) ℂ).PosSemidef := by
  rcases hμ with ⟨α, hα, rfl⟩ | ⟨n, hn, rfl⟩
  · exact (ComplexMatrix.wishart_ae_posDef α Sigma).mono fun X hX => hX.posSemidef
  · exact ComplexMatrix.gramMeasure_ae_posSemidef n Sigma

theorem IsSectionSevenQuaternionLaw.ae_posSemidef
    {Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]} {μ : Measure (QuaternionMatrix.Hermitian p)}
    (hμ : IsSectionSevenQuaternionLaw Sigma μ) :
    ∀ᵐ (X : QuaternionMatrix.Hermitian p) ∂μ, QuaternionMatrix.PosSemidef (X : Matrix (Fin p) (Fin p) ℍ[ℝ]) := by
  rcases hμ with ⟨α, hα, rfl⟩ | ⟨n, hn, rfl⟩
  · exact (QuaternionMatrix.wishart_ae_posDef α Sigma).mono fun X hX => hX.posSemidef
  · exact QuaternionMatrix.gramMeasure_ae_posSemidef n Sigma

theorem complex_geometricDeterminant_comparison
    (Sigma : Matrix (Fin p) (Fin p) ℂ) (hSigma : Sigma.PosDef)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℂ)
    (hB : ∀ i, Function.Injective (B i).mulVec)
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (f : ι → ℝ → ℝ) (hf : ∀ i, GeometricallyLogConvex (f i))
    (μ : Measure (ComplexMatrix.Hermitian p)) (hμ : IsSectionSevenComplexLaw Sigma μ) :
    ExtendedSelectedProductComparison μ (fun i X => canonicalGeometricExtension (f i)
      (ComplexMatrix.realDeterminant ((B i)ᴴ * (X : Matrix (Fin p) (Fin p) ℂ) * B i +
        c i • ComplexMatrix.compressionCovariance (B i) Sigma))) := by
  let d : ι → ℝ := fun i =>
    ComplexMatrix.realDeterminant (ComplexMatrix.compressionCovariance (B i) Sigma)
  have hd (i : ι) : 0 < d i := ComplexMatrix.realDeterminant_pos
    (ComplexMatrix.compressionCovariance_posDef hSigma (hB i))
  let g : ∀ i, (Fin (k i) → ℝ) → ℝ := fun i x =>
    canonicalGeometricExtension (f i) (d i * ∏ j, x j)
  have hg (i : ι) : (∀ x, g i x = 0) ∨ ∃ h : (Fin (k i) → ℝ) → ℝ,
      ConvexOn ℝ univ h ∧ Monotone h ∧ Spectral.SymmetricProfile h ∧
      ∀ x, (∀ j, 0 ≤ x j) → Spectral.spectralBoundaryValue h x = g i x := by
    let h : (Fin (k i) → ℝ) → ℝ := Spectral.geometricDeterminantProfile (canonicalGeometricExtension (f i)) (d i)
    have hh := Spectral.geometricDeterminantProfile_properties (k := k i) (hf i).canonicalExtension (hd i)
    exact Or.inr ⟨h, hh.1, hh.2.1, hh.2.2, fun x hx =>
      Spectral.spectralBoundaryValue_geometricDeterminantProfile
        (hf i).canonicalExtension_on_nonnegative (hd i) hx⟩
  have h := complex_spectral_zero_or_profile_comparison Sigma hSigma k B hB c hc g hg μ hμ
  apply h.of_zero_or_aeEq
  intro i
  apply Or.inr
  filter_upwards [hμ.ae_posSemidef] with X hX
  rw [ComplexMatrix.shiftedCompressionDeterminant_eq_covariance_eigenproduct
    hSigma (B i) (hB i) X hX (hc i)]

theorem quaternion_geometricDeterminant_comparison
    (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) (hSigma : QuaternionMatrix.PosDef Sigma)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℍ[ℝ])
    (hB : ∀ i, QuaternionMatrix.FullColumnRank (B i))
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (f : ι → ℝ → ℝ) (hf : ∀ i, GeometricallyLogConvex (f i))
    (μ : Measure (QuaternionMatrix.Hermitian p)) (hμ : IsSectionSevenQuaternionLaw Sigma μ) :
    ExtendedSelectedProductComparison μ (fun i X => canonicalGeometricExtension (f i)
      (QuaternionMatrix.positiveDeterminant ((B i)ᴴ * (X : Matrix (Fin p) (Fin p) ℍ[ℝ]) * B i +
        c i • QuaternionMatrix.compressionCovariance (B i) Sigma))) := by
  let d : ι → ℝ := fun i =>
    QuaternionMatrix.positiveDeterminant (QuaternionMatrix.compressionCovariance (B i) Sigma)
  have hd (i : ι) : 0 < d i :=
    (QuaternionMatrix.compressionCovariance_posDef hSigma (hB i)).positiveDeterminant_pos
  let g : ∀ i, (Fin (k i) → ℝ) → ℝ := fun i x =>
    canonicalGeometricExtension (f i) (d i * ∏ j, x j)
  have hg (i : ι) : (∀ x, g i x = 0) ∨ ∃ h : (Fin (k i) → ℝ) → ℝ,
      ConvexOn ℝ univ h ∧ Monotone h ∧ Spectral.SymmetricProfile h ∧
      ∀ x, (∀ j, 0 ≤ x j) → Spectral.spectralBoundaryValue h x = g i x := by
    let h : (Fin (k i) → ℝ) → ℝ := Spectral.geometricDeterminantProfile (canonicalGeometricExtension (f i)) (d i)
    have hh := Spectral.geometricDeterminantProfile_properties (k := k i) (hf i).canonicalExtension (hd i)
    exact Or.inr ⟨h, hh.1, hh.2.1, hh.2.2, fun x hx =>
      Spectral.spectralBoundaryValue_geometricDeterminantProfile
        (hf i).canonicalExtension_on_nonnegative (hd i) hx⟩
  have h := quaternion_spectral_zero_or_profile_comparison Sigma hSigma k B hB c hc g hg μ hμ
  apply h.of_zero_or_aeEq
  intro i
  apply Or.inr
  filter_upwards [hμ.ae_posSemidef] with X hX
  rw [QuaternionMatrix.shiftedCompressionDeterminant_eq_covariance_eigenproduct
    hSigma (B i) (hB i) X hX (hc i)]

theorem complex_unnormalizedDeterminantPower_comparison
    (Sigma : Matrix (Fin p) (Fin p) ℂ) (hSigma : Sigma.PosDef)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℂ)
    (hB : ∀ i, Function.Injective (B i).mulVec)
    (c a : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (ha : ∀ i, 0 ≤ a i)
    (μ : Measure (ComplexMatrix.Hermitian p)) (hμ : IsSectionSevenComplexLaw Sigma μ) :
    ExtendedSelectedProductComparison μ (fun i X =>
      (ComplexMatrix.realDeterminant ((B i)ᴴ * (X : Matrix (Fin p) (Fin p) ℂ) * B i +
        c i • ComplexMatrix.compressionCovariance (B i) Sigma)) ^ a i) := by
  have h := complex_geometricDeterminant_comparison Sigma hSigma k B hB c hc
    (fun i x => x ^ a i) (fun i => geometricallyLogConvex_rpow (ha i)) μ hμ
  apply h.of_zero_or_aeEq
  intro i
  apply Or.inr
  filter_upwards [hμ.ae_posSemidef] with X hX
  apply (canonicalGeometricExtension_rpow (ha i) _).symm
  rw [ComplexMatrix.shiftedCompressionDeterminant_eq_covariance_eigenproduct
    hSigma (B i) (hB i) X hX (hc i)]
  apply mul_nonneg (ComplexMatrix.realDeterminant_pos
    (ComplexMatrix.compressionCovariance_posDef hSigma (hB i))).le
  apply Finset.prod_nonneg
  intro j hj
  exact FieldSpectral.orderedValues_nonneg
    ((ComplexMatrix.normalizedCompression_posSemidef (B i) Sigma X hX).add
      (Matrix.PosDef.one.posSemidef.smul (hc i))) j

theorem quaternion_unnormalizedDeterminantPower_comparison
    (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) (hSigma : QuaternionMatrix.PosDef Sigma)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℍ[ℝ])
    (hB : ∀ i, QuaternionMatrix.FullColumnRank (B i))
    (c a : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (ha : ∀ i, 0 ≤ a i)
    (μ : Measure (QuaternionMatrix.Hermitian p)) (hμ : IsSectionSevenQuaternionLaw Sigma μ) :
    ExtendedSelectedProductComparison μ (fun i X =>
      (QuaternionMatrix.positiveDeterminant ((B i)ᴴ * (X : Matrix (Fin p) (Fin p) ℍ[ℝ]) * B i +
        c i • QuaternionMatrix.compressionCovariance (B i) Sigma)) ^ a i) := by
  have h := quaternion_geometricDeterminant_comparison Sigma hSigma k B hB c hc
    (fun i x => x ^ a i) (fun i => geometricallyLogConvex_rpow (ha i)) μ hμ
  apply h.of_zero_or_aeEq
  intro i
  exact Or.inr (Filter.Eventually.of_forall fun X =>
    (canonicalGeometricExtension_rpow (ha i) (QuaternionMatrix.positiveDeterminant_nonneg _)).symm)

end Wishart
end
end CanonicalSource82

section CanonicalSource83
/- Source: Wishart/FieldRealPowers.lean -/



/-!
# Real matrix powers and their actual traces

The quaternion power is constructed from the continuous functional calculus
of the faithful complex representation.  Its value lies in the representation
image because every function on the finite Hermitian spectrum agrees with a
real polynomial.  The construction therefore does not define the trace by
the desired eigenvalue formula.  The trace formula is proved afterwards,
using the actual doubled complex spectrum.
-/

noncomputable section
open Matrix Polynomial Set
open scoped Classical Quaternion ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Wishart.FieldSpectral

def complexReindexStarAlgEquiv {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (e : m ≃ n) :
    Matrix m m ℂ ≃⋆ₐ[ℝ] Matrix n n ℂ where
  __ := Matrix.reindexAlgEquiv ℝ ℂ e
  map_star' A := by
    ext i j
    rfl
  map_smul' r A := by
    ext i j
    rfl

theorem cfc_complex_submatrix_equiv {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (e : m ≃ n)
    {A : Matrix m m ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).submatrix e.symm e.symm = cfc f (A.submatrix e.symm e.symm) := by
  let φ := complexReindexStarAlgEquiv e
  have hφ : Continuous φ := φ.toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  exact StarAlgHomClass.map_cfc φ f A (A.finite_real_spectrum.continuousOn f)
    hφ hA.isSelfAdjoint (hA.submatrix e.symm).isSelfAdjoint

theorem rpow_complex_submatrix_equiv {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (e : m ≃ n)
    {A : Matrix m m ℂ} (hA : A.PosSemidef) (r : ℝ) :
    (CFC.rpow A r).submatrix e.symm e.symm = CFC.rpow (A.submatrix e.symm e.symm) r := by
  have hleft : CFC.rpow A r = cfc (fun x : ℝ => x ^ r) A :=
    CFC.rpow_eq_cfc_real (y := r) hA.nonneg
  have hright : CFC.rpow (A.submatrix e.symm e.symm) r =
      cfc (fun x : ℝ => x ^ r) (A.submatrix e.symm e.symm) :=
    CFC.rpow_eq_cfc_real (y := r) (hA.submatrix e.symm).nonneg
  rw [hleft, hright]
  exact cfc_complex_submatrix_equiv e hA.isHermitian _

theorem trace_submatrix_equiv {R m n : Type*} [AddCommMonoid R]
    [Fintype m] [Fintype n] (e : m ≃ n) (A : Matrix m m R) :
    (A.submatrix e.symm e.symm).trace = A.trace := by
  exact Equiv.sum_comp e.symm (fun i => A i i)

theorem real_trace_rpow {p : ℕ} {A : Matrix (Fin p) (Fin p) ℂ}
    (hA : A.PosSemidef) (r : ℝ) :
    (CFC.rpow A r).trace.re = ∑ i, (orderedValues hA.isHermitian i) ^ r := by
  have hreal : CFC.rpow A r = cfc (fun x : ℝ => x ^ r) A :=
    CFC.rpow_eq_cfc_real (y := r) hA.nonneg
  rw [hreal, hA.isHermitian.trace_cfc]
  simp only [Complex.re_sum, Complex.ofReal_re, orderedValues_eq, Function.comp_apply]
  exact (Equiv.sum_comp (orderedIndex p) (fun i => hA.isHermitian.eigenvalues i ^ r)).symm

end Wishart.FieldSpectral

namespace Wishart.QuaternionMatrix
open scoped Matrix.Norms.Frobenius

variable {n : Type*} [Fintype n] [DecidableEq n]

def realFunctionalCalculus (f : ℝ → ℝ) (A : Matrix n n ℍ[ℝ]) : Matrix n n ℍ[ℝ] :=
  representationLeftInverse (cfc f (complexRepresentation A))

theorem complexRepresentation_realFunctionalCalculus {A : Matrix n n ℍ[ℝ]}
    (hA : A.IsHermitian) (f : ℝ → ℝ) :
    complexRepresentation (realFunctionalCalculus f A) = cfc f (complexRepresentation A) := by
  let Y := complexRepresentation A
  have hY : Y.IsHermitian := (isHermitian_complexRepresentation_iff A).mpr hA
  let s := Y.finite_real_spectrum.toFinset
  let q : ℝ[X] := Lagrange.interpolate s id f
  have hq (t : ℝ) (ht : t ∈ spectrum ℝ Y) : q.eval t = f t := by
    exact Lagrange.eval_interpolate_at_node f (Set.injOn_id _)
      (by simpa only [s, Set.Finite.mem_toFinset] using ht)
  have hpoly : cfc f Y = aeval Y q := by
    rw [← cfc_polynomial q Y hY.isSelfAdjoint]
    exact cfc_congr fun t ht => (hq t ht).symm
  have hmap : complexRepresentation (aeval A q) = aeval Y q :=
    (Polynomial.aeval_algHom_apply complexRepresentationStarAlgHom A q).symm
  have hrange : ∃ R : Matrix n n ℍ[ℝ], complexRepresentation R = cfc f Y :=
    ⟨aeval A q, hmap.trans hpoly.symm⟩
  obtain ⟨R, hR⟩ := hrange
  change complexRepresentation (representationLeftInverse (cfc f Y)) = cfc f Y
  rw [← hR, representationLeftInverse_representation]

theorem realFunctionalCalculus_polynomial {A : Matrix n n ℍ[ℝ]}
    (hA : A.IsHermitian) (q : ℝ[X]) : realFunctionalCalculus q.eval A = aeval A q := by
  apply complexRepresentation_injective
  rw [complexRepresentation_realFunctionalCalculus hA,
    cfc_polynomial q (complexRepresentation A)
      ((isHermitian_complexRepresentation_iff A).mpr hA).isSelfAdjoint]
  exact Polynomial.aeval_algHom_apply complexRepresentationStarAlgHom A q

def matrixRpow (A : Matrix n n ℍ[ℝ]) (r : ℝ) : Matrix n n ℍ[ℝ] :=
  representationLeftInverse (CFC.rpow (complexRepresentation A) r)

theorem complexRepresentation_matrixRpow {A : Matrix n n ℍ[ℝ]}
    (hA : PosSemidef A) (r : ℝ) :
    complexRepresentation (matrixRpow A r) = CFC.rpow (complexRepresentation A) r := by
  have hreal : CFC.rpow (complexRepresentation A) r =
      cfc (fun x : ℝ => x ^ r) (complexRepresentation A) :=
    CFC.rpow_eq_cfc_real (y := r) (Matrix.PosSemidef.nonneg hA)
  rw [matrixRpow, hreal]
  exact complexRepresentation_realFunctionalCalculus hA.isHermitian _

theorem matrixRpow_posSemidef {A : Matrix n n ℍ[ℝ]}
    (hA : PosSemidef A) (r : ℝ) : PosSemidef (matrixRpow A r) := by
  unfold PosSemidef
  rw [complexRepresentation_matrixRpow hA]
  exact Matrix.nonneg_iff_posSemidef.mp CFC.rpow_nonneg

theorem flatRepresentation_matrixRpow {p : ℕ} {A : Matrix (Fin p) (Fin p) ℍ[ℝ]}
    (hA : PosSemidef A) (r : ℝ) :
    flatRepresentation (matrixRpow A r) = CFC.rpow (flatRepresentation A) r := by
  rw [flatRepresentation, complexRepresentation_matrixRpow hA]
  exact Wishart.FieldSpectral.rpow_complex_submatrix_equiv finProdFinEquiv hA r

theorem real_trace_flatRepresentation {p : ℕ} (A : Matrix (Fin p) (Fin p) ℍ[ℝ]) :
    (flatRepresentation A).trace.re = 2 * A.trace.re := by
  rw [flatRepresentation, Wishart.FieldSpectral.trace_submatrix_equiv,
    trace_complexRepresentation, Complex.ofReal_re]

theorem sum_rpow_doubleValues {p : ℕ} (x : Fin p → ℝ) (r : ℝ) :
    (∑ i : Fin (p * 2), doubleValues x i ^ r) = 2 * ∑ i, x i ^ r := by
  have h := Equiv.sum_comp (finProdFinEquiv : Fin p × Fin 2 ≃ Fin (p * 2))
    (fun i => doubleValues x i ^ r)
  simpa only [doubleValues, Equiv.symm_apply_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, Finset.sum_add_distrib, two_mul] using h.symm

theorem real_trace_matrixRpow {p : ℕ} (S : Hermitian p) (hS : PosSemidef (S : Matrix (Fin p) (Fin p) ℍ[ℝ])) (r : ℝ) :
    (matrixRpow (S : Matrix (Fin p) (Fin p) ℍ[ℝ]) r).trace.re = ∑ i, (orderedValues S i) ^ r := by
  have h := Wishart.FieldSpectral.real_trace_rpow (flatRepresentation_posSemidef hS) r
  rw [← flatRepresentation_matrixRpow hS r, real_trace_flatRepresentation] at h
  change 2 * (matrixRpow (S : Matrix (Fin p) (Fin p) ℍ[ℝ]) r).trace.re =
    ∑ i, (Wishart.FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe (flatHermitian S)) i) ^ r at h
  rw [flat_orderedValues_eq_double, sum_rpow_doubleValues, ← orderedValues_eq_decomposition] at h
  linarith

end Wishart.QuaternionMatrix
end
end CanonicalSource83

section CanonicalSource84
/- Source: Wishart/FieldTracePowerExamples.lean -/



/-!
# Literal trace-power examples of Theorem 7.1

These comparisons use actual matrix powers and their traces.  All dimensions,
including the empty compression, are included.  There is no assumed profile
membership or trace/eigenvalue identity in either final comparison theorem.
-/

noncomputable section
open Matrix MeasureTheory Set
open scoped Classical Quaternion ComplexOrder MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace Wishart

theorem complex_tracePower_zero_or_profile {k : ℕ} {r a : ℝ}
    (hr : 0 < r) (ha : 0 ≤ a) :
    (∀ S : ComplexMatrix.Hermitian k, (S : Matrix (Fin k) (Fin k) ℂ).PosSemidef →
      (CFC.rpow (S : Matrix (Fin k) (Fin k) ℂ) r).trace.re ^ (a / r) = 0) ∨
      ∃ h : (Fin k → ℝ) → ℝ,
        ConvexOn ℝ univ h ∧ Monotone h ∧ Spectral.SymmetricProfile h ∧
        ∀ S : ComplexMatrix.Hermitian k, (S : Matrix (Fin k) (Fin k) ℂ).PosSemidef →
          Spectral.spectralBoundaryValue h
            (FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe S)) =
              (CFC.rpow (S : Matrix (Fin k) (Fin k) ℂ) r).trace.re ^ (a / r) := by
  rcases Spectral.tracePower_zero_or_profile (k := k) hr ha with hz | ⟨h, hc, hm, hs, hv⟩
  · refine Or.inl fun S hS => ?_
    rw [FieldSpectral.real_trace_rpow hS]
    exact hz _
  · refine Or.inr ⟨h, hc, hm, hs, fun S hS => ?_⟩
    rw [FieldSpectral.real_trace_rpow hS]
    exact hv _ (FieldSpectral.orderedValues_nonneg hS)

theorem quaternion_tracePower_zero_or_profile {k : ℕ} {r a : ℝ}
    (hr : 0 < r) (ha : 0 ≤ a) :
    (∀ S : QuaternionMatrix.Hermitian k, QuaternionMatrix.PosSemidef (S : Matrix (Fin k) (Fin k) ℍ[ℝ]) →
      (QuaternionMatrix.matrixRpow (S : Matrix (Fin k) (Fin k) ℍ[ℝ]) r).trace.re ^ (a / r) = 0) ∨
      ∃ h : (Fin k → ℝ) → ℝ,
        ConvexOn ℝ univ h ∧ Monotone h ∧ Spectral.SymmetricProfile h ∧
        ∀ S : QuaternionMatrix.Hermitian k, QuaternionMatrix.PosSemidef (S : Matrix (Fin k) (Fin k) ℍ[ℝ]) →
          Spectral.spectralBoundaryValue h (QuaternionMatrix.orderedValues S) =
            (QuaternionMatrix.matrixRpow (S : Matrix (Fin k) (Fin k) ℍ[ℝ]) r).trace.re ^ (a / r) := by
  rcases Spectral.tracePower_zero_or_profile (k := k) hr ha with hz | ⟨h, hc, hm, hs, hv⟩
  · refine Or.inl fun S hS => ?_
    rw [QuaternionMatrix.real_trace_matrixRpow S hS]
    exact hz _
  · refine Or.inr ⟨h, hc, hm, hs, fun S hS => ?_⟩
    rw [QuaternionMatrix.real_trace_matrixRpow S hS]
    exact hv _ (QuaternionMatrix.orderedValues_nonneg S hS)

theorem complex_tracePower_comparison {p : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Sigma : Matrix (Fin p) (Fin p) ℂ) (hSigma : Sigma.PosDef)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℂ)
    (hB : ∀ i, Function.Injective (B i).mulVec)
    (c r a : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (hr : ∀ i, 0 < r i) (ha : ∀ i, 0 ≤ a i)
    (μ : Measure (ComplexMatrix.Hermitian p)) (hμ : IsSectionSevenComplexLaw Sigma μ) :
    ExtendedSelectedProductComparison μ (fun i X =>
      (CFC.rpow ((ComplexMatrix.normalizedCompression (B i) Sigma X + c i •
        (⟨1, Matrix.isHermitian_one⟩ : ComplexMatrix.Hermitian (k i))) :
          Matrix (Fin (k i)) (Fin (k i)) ℂ) (r i)).trace.re ^ (a i / r i)) :=
  complex_zero_or_profile_comparison Sigma hSigma k B hB c hc
    (fun i S => (CFC.rpow (S : Matrix (Fin (k i)) (Fin (k i)) ℂ) (r i)).trace.re ^ (a i / r i))
    (fun i => complex_tracePower_zero_or_profile (hr i) (ha i)) μ hμ

theorem quaternion_tracePower_comparison {p : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) (hSigma : QuaternionMatrix.PosDef Sigma)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℍ[ℝ])
    (hB : ∀ i, QuaternionMatrix.FullColumnRank (B i))
    (c r a : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (hr : ∀ i, 0 < r i) (ha : ∀ i, 0 ≤ a i)
    (μ : Measure (QuaternionMatrix.Hermitian p)) (hμ : IsSectionSevenQuaternionLaw Sigma μ) :
    ExtendedSelectedProductComparison μ (fun i X =>
      (QuaternionMatrix.matrixRpow ((QuaternionMatrix.normalizedCompression (B i) Sigma X + c i •
        (⟨1, Matrix.isHermitian_one⟩ : QuaternionMatrix.Hermitian (k i))) :
          Matrix (Fin (k i)) (Fin (k i)) ℍ[ℝ]) (r i)).trace.re ^
          (a i / r i)) :=
  quaternion_zero_or_profile_comparison Sigma hSigma k B hB c hc
    (fun i S => (QuaternionMatrix.matrixRpow (S : Matrix (Fin (k i)) (Fin (k i)) ℍ[ℝ]) (r i)).trace.re ^ (a i / r i))
    (fun i => quaternion_tracePower_zero_or_profile (hr i) (ha i)) μ hμ

end Wishart
end
end CanonicalSource84

section CanonicalSource85
/- Source: Wishart/FieldPolynomialExamples.lean -/



/-!
# Actual polynomial, elementary and Schur-positive examples

These are comparisons for the literal eigenvalue polynomials.  The zero
polynomial and all elementary degrees are included.  In the Schur case,
symmetry and coefficient nonnegativity are derived from the actual Schur
polynomials rather than supplied as additional hypotheses.
-/

noncomputable section
open Matrix MeasureTheory Set
open scoped Classical Quaternion ComplexOrder MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace Wishart

variable {p : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem complex_polynomialPower_comparison
    (Sigma : Matrix (Fin p) (Fin p) ℂ) (hSigma : Sigma.PosDef)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℂ)
    (hB : ∀ i, Function.Injective (B i).mulVec)
    (c a : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (ha : ∀ i, 0 ≤ a i)
    (P : ∀ i, MvPolynomial (Fin (k i)) ℝ)
    (hP : ∀ i d, 0 ≤ (P i).coeff d) (hPsym : ∀ i, (P i).IsSymmetric)
    (μ : Measure (ComplexMatrix.Hermitian p)) (hμ : IsSectionSevenComplexLaw Sigma μ) :
    ExtendedSelectedProductComparison μ (fun i X =>
      (MvPolynomial.eval (FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe
        (ComplexMatrix.normalizedCompression (B i) Sigma X + c i •
          (⟨1, Matrix.isHermitian_one⟩ : ComplexMatrix.Hermitian (k i))))) (P i)) ^ a i) :=
  complex_spectral_zero_or_profile_comparison Sigma hSigma k B hB c hc
    (fun i x => (MvPolynomial.eval x (P i)) ^ a i)
    (fun i => Spectral.polynomialPower_zero_or_profile (P i) (hP i) (hPsym i) (ha i)) μ hμ

theorem quaternion_polynomialPower_comparison
    (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) (hSigma : QuaternionMatrix.PosDef Sigma)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℍ[ℝ])
    (hB : ∀ i, QuaternionMatrix.FullColumnRank (B i))
    (c a : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (ha : ∀ i, 0 ≤ a i)
    (P : ∀ i, MvPolynomial (Fin (k i)) ℝ)
    (hP : ∀ i d, 0 ≤ (P i).coeff d) (hPsym : ∀ i, (P i).IsSymmetric)
    (μ : Measure (QuaternionMatrix.Hermitian p)) (hμ : IsSectionSevenQuaternionLaw Sigma μ) :
    ExtendedSelectedProductComparison μ (fun i X =>
      (MvPolynomial.eval (QuaternionMatrix.orderedValues
        (QuaternionMatrix.normalizedCompression (B i) Sigma X + c i •
          (⟨1, Matrix.isHermitian_one⟩ : QuaternionMatrix.Hermitian (k i)))) (P i)) ^ a i) :=
  quaternion_spectral_zero_or_profile_comparison Sigma hSigma k B hB c hc
    (fun i x => (MvPolynomial.eval x (P i)) ^ a i)
    (fun i => Spectral.polynomialPower_zero_or_profile (P i) (hP i) (hPsym i) (ha i)) μ hμ

theorem complex_elementaryPower_comparison
    (Sigma : Matrix (Fin p) (Fin p) ℂ) (hSigma : Sigma.PosDef)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℂ)
    (hB : ∀ i, Function.Injective (B i).mulVec)
    (c a : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (ha : ∀ i, 0 ≤ a i) (degree : ι → ℕ)
    (μ : Measure (ComplexMatrix.Hermitian p)) (hμ : IsSectionSevenComplexLaw Sigma μ) :
    ExtendedSelectedProductComparison μ (fun i X =>
      (MvPolynomial.eval (FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe
        (ComplexMatrix.normalizedCompression (B i) Sigma X + c i •
          (⟨1, Matrix.isHermitian_one⟩ : ComplexMatrix.Hermitian (k i)))))
            (MvPolynomial.esymm (Fin (k i)) ℝ (degree i))) ^ a i) :=
  complex_polynomialPower_comparison Sigma hSigma k B hB c a hc ha
    (fun i => MvPolynomial.esymm (Fin (k i)) ℝ (degree i))
    (fun i => Spectral.elementaryPolynomial_coeff_nonneg (degree i))
    (fun i => MvPolynomial.esymm_isSymmetric _ _ (degree i)) μ hμ

theorem quaternion_elementaryPower_comparison
    (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) (hSigma : QuaternionMatrix.PosDef Sigma)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℍ[ℝ])
    (hB : ∀ i, QuaternionMatrix.FullColumnRank (B i))
    (c a : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (ha : ∀ i, 0 ≤ a i) (degree : ι → ℕ)
    (μ : Measure (QuaternionMatrix.Hermitian p)) (hμ : IsSectionSevenQuaternionLaw Sigma μ) :
    ExtendedSelectedProductComparison μ (fun i X =>
      (MvPolynomial.eval (QuaternionMatrix.orderedValues
        (QuaternionMatrix.normalizedCompression (B i) Sigma X + c i •
          (⟨1, Matrix.isHermitian_one⟩ : QuaternionMatrix.Hermitian (k i))))
            (MvPolynomial.esymm (Fin (k i)) ℝ (degree i))) ^ a i) :=
  quaternion_polynomialPower_comparison Sigma hSigma k B hB c a hc ha
    (fun i => MvPolynomial.esymm (Fin (k i)) ℝ (degree i))
    (fun i => Spectral.elementaryPolynomial_coeff_nonneg (degree i))
    (fun i => MvPolynomial.esymm_isSymmetric _ _ (degree i)) μ hμ

theorem complex_schurPositivePower_comparison {β : ι → Type*} [∀ i, Fintype (β i)]
    (Sigma : Matrix (Fin p) (Fin p) ℂ) (hSigma : Sigma.PosDef)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℂ)
    (hB : ∀ i, Function.Injective (B i).mulVec)
    (c a : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (ha : ∀ i, 0 ≤ a i)
    (coefficient : ∀ i, β i → ℝ) (shape : ∀ i, β i → YoungDiagram)
    (hcoefficient : ∀ i j, 0 ≤ coefficient i j)
    (μ : Measure (ComplexMatrix.Hermitian p)) (hμ : IsSectionSevenComplexLaw Sigma μ) :
    ExtendedSelectedProductComparison μ (fun i X =>
      (MvPolynomial.eval (FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe
        (ComplexMatrix.normalizedCompression (B i) Sigma X + c i •
          (⟨1, Matrix.isHermitian_one⟩ : ComplexMatrix.Hermitian (k i)))))
            (Spectral.schurPositivePolynomial (coefficient i) (shape i))) ^ a i) :=
  complex_polynomialPower_comparison Sigma hSigma k B hB c a hc ha
    (fun i => Spectral.schurPositivePolynomial (coefficient i) (shape i))
    (fun i => Spectral.schurPositivePolynomial_coeff_nonneg (coefficient i) (shape i) (hcoefficient i))
    (fun i => Spectral.schurPositivePolynomial_symmetric (coefficient i) (shape i)) μ hμ

theorem quaternion_schurPositivePower_comparison {β : ι → Type*} [∀ i, Fintype (β i)]
    (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) (hSigma : QuaternionMatrix.PosDef Sigma)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℍ[ℝ])
    (hB : ∀ i, QuaternionMatrix.FullColumnRank (B i))
    (c a : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (ha : ∀ i, 0 ≤ a i)
    (coefficient : ∀ i, β i → ℝ) (shape : ∀ i, β i → YoungDiagram)
    (hcoefficient : ∀ i j, 0 ≤ coefficient i j)
    (μ : Measure (QuaternionMatrix.Hermitian p)) (hμ : IsSectionSevenQuaternionLaw Sigma μ) :
    ExtendedSelectedProductComparison μ (fun i X =>
      (MvPolynomial.eval (QuaternionMatrix.orderedValues
        (QuaternionMatrix.normalizedCompression (B i) Sigma X + c i •
          (⟨1, Matrix.isHermitian_one⟩ : QuaternionMatrix.Hermitian (k i))))
            (Spectral.schurPositivePolynomial (coefficient i) (shape i))) ^ a i) :=
  quaternion_polynomialPower_comparison Sigma hSigma k B hB c a hc ha
    (fun i => Spectral.schurPositivePolynomial (coefficient i) (shape i))
    (fun i => Spectral.schurPositivePolynomial_coeff_nonneg (coefficient i) (shape i) (hcoefficient i))
    (fun i => Spectral.schurPositivePolynomial_symmetric (coefficient i) (shape i)) μ hμ

end Wishart
end
end CanonicalSource85
