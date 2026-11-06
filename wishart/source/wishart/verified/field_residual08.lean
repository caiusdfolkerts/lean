module

public import wishart.verified.field_residual07
public import Mathlib.Probability.HasLaw
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.Topology.Algebra.MvPolynomial
public import tau_ceti.ring_theory.mv_polynomial.symmetric.schur.symmetric
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic

/- Recovered canonical proof stage; see verification/recovery-patches.json. -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

section CanonicalSource70
/- Source: Wishart/FieldPrincipalTheorem.lean -/



/-!
# The full complex and quaternionic Wishart theorem

The comparison is proved separately for the literal normalized density at
all admissible real shapes and for the actual Gaussian Gram image at every
positive integer sample size. Both routes include arbitrary overlapping
full-column-rank compressions, shifts, full finite convex increasing symmetric
logarithmic profiles, and their positive-semidefinite boundary values.

The final conjunction also proves density nonvacuity and finite nonnegative
determinant-power moments. These conclusions are not assumptions of the
comparison statements.
-/

noncomputable section
open Matrix MeasureTheory
open scoped Classical Quaternion ENNReal
namespace Wishart

theorem theorem_7_1_complex : TheoremSevenOneComplex := by
  intro p ι _ _ Sigma hSigma F μ hμ
  rcases hμ with ⟨α, hα, rfl⟩ | ⟨n, hn, rfl⟩
  · exact F.density_selected_product_comparison hα Sigma hSigma
  · exact F.gram_selected_product_comparison n Sigma hSigma

theorem theorem_7_1_quaternion : TheoremSevenOneQuaternion := by
  intro p ι _ _ Sigma hSigma F μ hμ
  rcases hμ with ⟨α, hα, rfl⟩ | ⟨n, hn, rfl⟩
  · exact F.density_selected_product_comparison hα Sigma hSigma
  · exact F.gram_selected_product_comparison n Sigma hSigma

/-- The full Section 7 target, with both literal laws, both fields,
nonvacuous normalization, the selected-factor chains, and finite powers. -/
theorem theorem_7_1 : TheoremSevenOne :=
  ⟨theorem_7_1_complex_normalization, theorem_7_1_quaternion_normalization,
    theorem_7_1_complex, theorem_7_1_quaternion,
    theorem_7_1_complex_finite_powers, theorem_7_1_quaternion_finite_powers⟩

end Wishart
end
end CanonicalSource70

section CanonicalSource71
/- Source: Wishart/FieldRandomMatrixCorrespondence.lean -/



/-!
# The field theorem on an arbitrary probability space

The canonical-law formulation transports to every actual random matrix with
that law. Measurability of the singular spectral factors is derived from the
proved continuous approximants and their almost-everywhere PSD limits. It is
not inserted as an extra hypothesis of either final field theorem.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical Quaternion ComplexOrder ENNReal Matrix.Norms.Frobenius

namespace Wishart

theorem ExtendedSelectedProductComparison.of_hasLaw
    {Ω E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [DecidableEq ι]
    {P : Measure Ω} {μ : Measure E} {X : Ω → E} {f : ι → E → ℝ}
    (h : ExtendedSelectedProductComparison μ f)
    (hf : ∀ i, AEMeasurable (f i) μ) (hX : HasLaw X μ P) :
    ExtendedSelectedProductComparison P (fun i ω => f i (X ω)) := by
  have hs (i : ι) :
      (∫⁻ ω, ENNReal.ofReal (f i (X ω)) ∂P) = ∫⁻ x, ENNReal.ofReal (f i x) ∂μ :=
    hX.lintegral_comp (hf i).ennreal_ofReal
  have hp (J : Finset ι) :
      (∫⁻ ω, ENNReal.ofReal (∏ i ∈ J, f i (X ω)) ∂P) =
        ∫⁻ x, ENNReal.ofReal (∏ i ∈ J, f i x) ∂μ :=
    hX.lintegral_comp (Finset.aemeasurable_fun_prod J (fun i _ => hf i)).ennreal_ofReal
  intro J j hj
  simpa only [hs, hp] using h J j hj

namespace ComplexSpectralFamily

theorem aemeasurable_factor_of_ae_posSemidef {p : ℕ} {ι : Type*}
    (F : ComplexSpectralFamily p ι) (Sigma : Matrix (Fin p) (Fin p) ℂ)
    (μ : Measure (ComplexMatrix.Hermitian p))
    (hPSD : ∀ᵐ (X : ComplexMatrix.Hermitian p) ∂μ, (X : Matrix (Fin p) (Fin p) ℂ).PosSemidef) (i : ι) :
    AEMeasurable (F.factor Sigma i) μ := by
  have hA : Measurable (F.shiftedCompression Sigma i) :=
    ((ComplexMatrix.continuous_normalizedCompression (F.matrix i) Sigma).add continuous_const).measurable
  apply aemeasurable_of_tendsto_metrizable_ae atTop
    (fun n => ((FieldGaussian.continuous_complexFaceApprox (F.convex i) (F.increasing i) n).measurable.comp hA).aemeasurable)
  filter_upwards [hPSD] with X hX
  exact FieldGaussian.complexFaceApprox_tendsto (F.convex i) (F.increasing i) (F.symmetric i)
    (F.shiftedCompression Sigma i X)
    (FieldSpectral.identityShift_posSemidef _
      (ComplexMatrix.normalizedCompression_posSemidef (F.matrix i) Sigma X hX)
      (F.shift_nonneg i))

theorem aemeasurable_factor_of_sectionSevenLaw {p : ℕ} {ι : Type*}
    (F : ComplexSpectralFamily p ι) (Sigma : Matrix (Fin p) (Fin p) ℂ)
    {μ : Measure (ComplexMatrix.Hermitian p)} (hμ : IsSectionSevenComplexLaw Sigma μ)
    (i : ι) : AEMeasurable (F.factor Sigma i) μ := by
  apply F.aemeasurable_factor_of_ae_posSemidef Sigma μ _ i
  rcases hμ with ⟨α, hα, rfl⟩ | ⟨n, hn, rfl⟩
  · exact (ComplexMatrix.wishart_ae_posDef α Sigma).mono fun X hX => hX.posSemidef
  · exact ComplexMatrix.gramMeasure_ae_posSemidef n Sigma

end ComplexSpectralFamily

namespace QuaternionSpectralFamily

theorem aemeasurable_factor_of_ae_posSemidef {p : ℕ} {ι : Type*}
    (F : QuaternionSpectralFamily p ι) (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ])
    (μ : Measure (QuaternionMatrix.Hermitian p))
    (hPSD : ∀ᵐ (X : QuaternionMatrix.Hermitian p) ∂μ, QuaternionMatrix.PosSemidef (X : Matrix (Fin p) (Fin p) ℍ[ℝ])) (i : ι) :
    AEMeasurable (F.factor Sigma i) μ := by
  have hA : Measurable (F.shiftedCompression Sigma i) :=
    ((QuaternionMatrix.continuous_normalizedCompression (F.matrix i) Sigma).add continuous_const).measurable
  apply aemeasurable_of_tendsto_metrizable_ae atTop
    (fun n => ((FieldGaussian.continuous_quaternionFaceApprox (F.convex i) (F.increasing i) n).measurable.comp hA).aemeasurable)
  filter_upwards [hPSD] with X hX
  exact FieldGaussian.quaternionFaceApprox_tendsto (F.convex i) (F.increasing i) (F.symmetric i)
    (F.shiftedCompression Sigma i X)
    (QuaternionMatrix.identityShift_posSemidef _
      (QuaternionMatrix.normalizedCompression_posSemidef (F.matrix i) Sigma X hX)
      (F.shift_nonneg i))

theorem aemeasurable_factor_of_sectionSevenLaw {p : ℕ} {ι : Type*}
    (F : QuaternionSpectralFamily p ι) (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ])
    {μ : Measure (QuaternionMatrix.Hermitian p)} (hμ : IsSectionSevenQuaternionLaw Sigma μ)
    (i : ι) : AEMeasurable (F.factor Sigma i) μ := by
  apply F.aemeasurable_factor_of_ae_posSemidef Sigma μ _ i
  rcases hμ with ⟨α, hα, rfl⟩ | ⟨n, hn, rfl⟩
  · exact (QuaternionMatrix.wishart_ae_posDef α Sigma).mono fun X hX => hX.posSemidef
  · exact QuaternionMatrix.gramMeasure_ae_posSemidef n Sigma

end QuaternionSpectralFamily

theorem theorem_7_1_complex_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {p : ℕ}
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (Sigma : Matrix (Fin p) (Fin p) ℂ) (hSigma : Sigma.PosDef)
    (F : ComplexSpectralFamily p ι) {μ : Measure (ComplexMatrix.Hermitian p)}
    (hμ : IsSectionSevenComplexLaw Sigma μ) {X : Ω → ComplexMatrix.Hermitian p}
    (hX : HasLaw X μ P) :
    ExtendedSelectedProductComparison P (fun i ω => F.factor Sigma i (X ω)) :=
  (theorem_7_1_complex p ι Sigma hSigma F μ hμ).of_hasLaw
    (F.aemeasurable_factor_of_sectionSevenLaw Sigma hμ) hX

theorem theorem_7_1_quaternion_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {p : ℕ}
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) (hSigma : QuaternionMatrix.PosDef Sigma)
    (F : QuaternionSpectralFamily p ι) {μ : Measure (QuaternionMatrix.Hermitian p)}
    (hμ : IsSectionSevenQuaternionLaw Sigma μ) {X : Ω → QuaternionMatrix.Hermitian p}
    (hX : HasLaw X μ P) :
    ExtendedSelectedProductComparison P (fun i ω => F.factor Sigma i (X ω)) :=
  (theorem_7_1_quaternion p ι Sigma hSigma F μ hμ).of_hasLaw
    (F.aemeasurable_factor_of_sectionSevenLaw Sigma hμ) hX

theorem theorem_7_1_complex_finite_powers_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {p : ℕ}
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (Sigma : Matrix (Fin p) (Fin p) ℂ) (hSigma : Sigma.PosDef)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℂ)
    (hB : ∀ i, Function.Injective (B i).mulVec)
    (c ν : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (hν : ∀ i, 0 ≤ ν i)
    {μ : Measure (ComplexMatrix.Hermitian p)} (hμ : IsSectionSevenComplexLaw Sigma μ)
    {X : Ω → ComplexMatrix.Hermitian p} (hX : HasLaw X μ P) :
    (∫⁻ ω, ENNReal.ofReal (∏ i, ComplexMatrix.realDeterminant
      ((B i)ᴴ * (X ω : Matrix (Fin p) (Fin p) ℂ) * B i +
        c i • ComplexMatrix.compressionCovariance (B i) Sigma) ^ ν i) ∂P) < ⊤ := by
  have hm : Measurable (fun Y : ComplexMatrix.Hermitian p => ENNReal.ofReal
      (∏ i, ComplexMatrix.realDeterminant
        ((B i)ᴴ * (Y : Matrix (Fin p) (Fin p) ℂ) * B i +
          c i • ComplexMatrix.compressionCovariance (B i) Sigma) ^ ν i)) := by
    apply Measurable.ennreal_ofReal
    apply Finset.measurable_prod
    intro i hi
    apply (Real.continuous_rpow_const (hν i)).measurable.comp
    apply ComplexMatrix.continuous_realDeterminant.measurable.comp
    fun_prop
  rw [hX.lintegral_comp hm.aemeasurable]
  exact theorem_7_1_complex_finite_powers p ι Sigma hSigma k B hB c ν hc hν μ hμ

theorem theorem_7_1_quaternion_finite_powers_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {p : ℕ}
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) (hSigma : QuaternionMatrix.PosDef Sigma)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℍ[ℝ])
    (hB : ∀ i, QuaternionMatrix.FullColumnRank (B i))
    (c ν : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (hν : ∀ i, 0 ≤ ν i)
    {μ : Measure (QuaternionMatrix.Hermitian p)} (hμ : IsSectionSevenQuaternionLaw Sigma μ)
    {X : Ω → QuaternionMatrix.Hermitian p} (hX : HasLaw X μ P) :
    (∫⁻ ω, ENNReal.ofReal (∏ i, QuaternionMatrix.positiveDeterminant
      ((B i)ᴴ * (X ω : Matrix (Fin p) (Fin p) ℍ[ℝ]) * B i +
        c i • QuaternionMatrix.compressionCovariance (B i) Sigma) ^ ν i) ∂P) < ⊤ := by
  have hm : Measurable (fun Y : QuaternionMatrix.Hermitian p => ENNReal.ofReal
      (∏ i, QuaternionMatrix.positiveDeterminant
        ((B i)ᴴ * (Y : Matrix (Fin p) (Fin p) ℍ[ℝ]) * B i +
          c i • QuaternionMatrix.compressionCovariance (B i) Sigma) ^ ν i)) := by
    apply Measurable.ennreal_ofReal
    apply Finset.measurable_prod
    intro i hi
    apply (Real.continuous_rpow_const (hν i)).measurable.comp
    apply QuaternionMatrix.continuous_positiveDeterminant.measurable.comp
    fun_prop
  rw [hX.lintegral_comp hm.aemeasurable]
  exact theorem_7_1_quaternion_finite_powers p ι Sigma hSigma k B hB c ν hc hν μ hμ

end Wishart
end
end CanonicalSource71

section CanonicalSource72
/- Source: Wishart/FieldGaussianComponentLaw.lean -/



/-!
# The real component convention for the field Gaussian rows

This is an equality of the actual joint coordinate laws, not a choice of
notation for a variance parameter.  In every real orthonormal basis the
identity-covariance field row has independent `N(0, 1 / dim_R F)` coordinates.
The existing rectangular-factor transport then gives the Gaussian rows used
in the Gram alternative of Theorem 7.1.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical Quaternion NNReal

namespace Wishart.FieldGaussian
open scoped Matrix.Norms.Frobenius

variable (F : Type*) [NormedRing F] [StarRing F] [CStarRing F]
  [InnerProductSpace ℝ F] [StarModule ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  [SMulCommClass ℝ F F] [IsScalarTower ℝ F F]

@[reducible] local instance compatibleScalarAlgebraStage8_1 : NormedAlgebra ℝ F where
  toAlgebra := Algebra.ofModule (fun r x y => smul_mul_assoc r x y)
    (fun r x y => mul_smul_comm r x y)
  norm_smul_le r x := (norm_smul r x).le


/-- All real orthonormal coordinates are independent and have variance exactly
the reciprocal of the real dimension of the scalar field. -/
theorem gaussianRowWithFactor_one_coordinate_law {p : ℕ} {ι : Type*} [Fintype ι]
    (hF : 0 < Module.finrank ℝ F) (b : OrthonormalBasis ι ℝ (Row F p)) :
    (gaussianRowWithFactor F (1 : Matrix (Fin p) (Fin p) F)).map
        (fun z i => b.repr z i) =
      Measure.pi (fun _ : ι => gaussianReal 0 (Module.finrank ℝ F : ℝ≥0)⁻¹) := by
  rw [gaussianRowWithFactor,
    Measure.map_map (by fun_prop) (normalizedRowFactorCLM F 1).continuous.measurable,
    stdGaussian_eq_map_pi_orthonormalBasis b,
    Measure.map_map (by fun_prop) (by fun_prop)]
  have heq :
      (fun x : ι → ℝ => fun i => b.repr
        (normalizedRowFactorCLM F (1 : Matrix (Fin p) (Fin p) F)
          (∑ j, x j • b j)) i) =
      (fun x : ι → ℝ => fun i => standardDeviation F * x i) := by
    funext x i
    rw [normalizedRowFactorCLM_one,
      b.sum_repr_symm (WithLp.toLp 2 x)]
    simp only [map_smul, LinearIsometryEquiv.apply_symm_apply,
      PiLp.smul_apply, PiLp.toLp_apply, smul_eq_mul]
  change (Measure.pi fun _ : ι => gaussianReal 0 1).map
    (fun x i => b.repr (normalizedRowFactorCLM F 1 (∑ j, x j • b j)) i) = _
  haveI : ∀ _ : ι, SigmaFinite
      ((gaussianReal (0 : ℝ) 1).map (fun x : ℝ => standardDeviation F * x)) := fun _ => by
    rw [gaussianReal_map_const_mul]
    infer_instance
  rw [heq, Measure.pi_map_pi (fun _ => by fun_prop)]
  simp only [gaussianReal_map_const_mul, mul_zero, mul_one]
  apply congrArg Measure.pi
  funext i
  apply congrArg (gaussianReal 0)
  apply NNReal.coe_injective
  change standardDeviation F ^ 2 = (Module.finrank ℝ F : ℝ)⁻¹
  exact standardDeviation_sq F hF

theorem complex_standard_row_coordinate_law {p : ℕ} {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (Row ℂ p)) :
    (gaussianRowWithFactor ℂ (1 : Matrix (Fin p) (Fin p) ℂ)).map
        (fun z i => b.repr z i) =
      Measure.pi (fun _ : ι => gaussianReal 0 (1 / 2)) := by
  simpa only [Complex.finrank_real_complex, Nat.cast_ofNat, one_div] using
    gaussianRowWithFactor_one_coordinate_law ℂ
      (by simp only [Complex.finrank_real_complex]; decide) b

theorem quaternion_standard_row_coordinate_law {p : ℕ} {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (Row ℍ[ℝ] p)) :
    (gaussianRowWithFactor ℍ[ℝ] (1 : Matrix (Fin p) (Fin p) ℍ[ℝ])).map
        (fun z i => b.repr z i) =
      Measure.pi (fun _ : ι => gaussianReal 0 (1 / 4)) := by
  simpa only [Quaternion.finrank_eq_four, Nat.cast_ofNat, one_div] using
    gaussianRowWithFactor_one_coordinate_law ℍ[ℝ]
      (by simp only [Quaternion.finrank_eq_four]; decide) b

end Wishart.FieldGaussian
end
end CanonicalSource72

section CanonicalSource73
/- Source: Wishart/SpectralProfileExamples.lean -/



/-!
# Explicit members of the logarithmic spectral class

Convexity of a finite positive exponential sum is proved from the convexity of
the exponential, after normalizing the two endpoint sums. Thus no convexity or
positivity of a polynomial profile is supplied as an extra premise. The final
polynomial theorem assumes exactly that the polynomial is nonzero, symmetric,
and has nonnegative coefficients. Elementary symmetric polynomials are then
instantiated using their actual Mathlib definition. Boundary identities include
zero eigenvalues and exponent zero.
-/

noncomputable section
open Set Filter Topology
open scoped Classical BigOperators

namespace Wishart.Spectral

variable {k : ℕ} {ι : Type*} [Fintype ι]

def weightedExponentialSum (c : ι → ℝ) (g : ι → (Fin k → ℝ) → ℝ)
    (x : Fin k → ℝ) : ℝ := ∑ i, c i * Real.exp (g i x)

theorem weightedExponentialSum_pos (c : ι → ℝ) (g : ι → (Fin k → ℝ) → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hpos : ∃ i, 0 < c i) (x : Fin k → ℝ) :
    0 < weightedExponentialSum c g x := by
  obtain ⟨i, hi⟩ := hpos
  exact (mul_pos hi (Real.exp_pos _)).trans_le
    (Finset.single_le_sum (fun j _ => mul_nonneg (hc j) (Real.exp_pos _).le)
      (Finset.mem_univ i))

theorem weightedExponentialSum_normalized (c : ι → ℝ)
    (g : ι → (Fin k → ℝ) → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hpos : ∃ i, 0 < c i) (x : Fin k → ℝ) :
    (∑ i, c i * Real.exp (g i x - Real.log (weightedExponentialSum c g x))) = 1 := by
  simp_rw [Real.exp_sub, Real.exp_log (weightedExponentialSum_pos c g hc hpos x),
    ← mul_div_assoc]
  rw [← Finset.sum_div]
  exact div_self (weightedExponentialSum_pos c g hc hpos x).ne'

/-- Log-sum-exp convexity, including zero coefficients in the original sum. -/
theorem convexOn_log_weightedExponentialSum (c : ι → ℝ)
    (g : ι → (Fin k → ℝ) → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hpos : ∃ i, 0 < c i) (hg : ∀ i, ConvexOn ℝ univ (g i)) :
    ConvexOn ℝ univ (fun x => Real.log (weightedExponentialSum c g x)) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  let A := Real.log (weightedExponentialSum c g x)
  let B := Real.log (weightedExponentialSum c g y)
  let C := a * A + b * B
  have hterm (i : ι) :
      Real.exp (g i (a • x + b • y) - C) ≤
        a * Real.exp (g i x - A) + b * Real.exp (g i y - B) := by
    apply le_trans _ (convexOn_exp.2 (mem_univ _) (mem_univ _) ha hb hab)
    apply Real.exp_le_exp.mpr
    have h := (hg i).2 hx hy ha hb hab
    dsimp only [C]
    simp only [smul_eq_mul] at h ⊢
    linarith
  have hsum : (∑ i, c i * Real.exp (g i (a • x + b • y) - C)) ≤ 1 := by
    calc
      _ ≤ ∑ i, c i * (a * Real.exp (g i x - A) +
          b * Real.exp (g i y - B)) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hterm i) (hc i))
      _ = a * (∑ i, c i * Real.exp (g i x - A)) +
          b * (∑ i, c i * Real.exp (g i y - B)) := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 1 := by
        rw [weightedExponentialSum_normalized c g hc hpos x,
          weightedExponentialSum_normalized c g hc hpos y]
        simpa only [mul_one] using hab
  have hdiv : weightedExponentialSum c g (a • x + b • y) / Real.exp C ≤ 1 := by
    simpa only [Real.exp_sub, ← mul_div_assoc, ← Finset.sum_div,
      weightedExponentialSum] using hsum
  have hlog := (Real.log_le_iff_le_exp
    (weightedExponentialSum_pos c g hc hpos (a • x + b • y))).mpr
      ((div_le_one (Real.exp_pos C)).mp hdiv)
  exact hlog

theorem monotone_log_weightedExponentialSum (c : ι → ℝ)
    (g : ι → (Fin k → ℝ) → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hpos : ∃ i, 0 < c i) (hg : ∀ i, Monotone (g i)) :
    Monotone (fun x => Real.log (weightedExponentialSum c g x)) := by
  intro x y hxy
  apply Real.log_le_log (weightedExponentialSum_pos c g hc hpos x)
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (hg i hxy)) (hc i)

theorem convexOn_coordinatePlane (a : Fin k → ℝ) (b : ℝ) :
    ConvexOn ℝ univ (coordinatePlane a b) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy s t hs ht hst
  apply le_of_eq
  simp only [coordinatePlane, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  have hsum : (∑ i, a i * (s * x i)) + (∑ i, a i * (t * y i)) =
      (∑ i, s * (a i * x i)) + (∑ i, t * (a i * y i)) := by
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring
  rw [hsum]
  have hb : s * b + t * b = b := by rw [← add_mul, hst, one_mul]
  linarith

theorem monotone_coordinatePlane {a : Fin k → ℝ} (ha : ∀ i, 0 ≤ a i) (b : ℝ) :
    Monotone (coordinatePlane a b) := by
  intro x y hxy
  unfold coordinatePlane
  have hsum : (∑ i, a i * x i) ≤ ∑ i, a i * y i :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hxy i) (ha i)
  linarith

def determinantPowerProfile (ν : ℝ) (x : Fin k → ℝ) : ℝ := ν * ∑ i, x i

theorem determinantPowerProfile_properties {ν : ℝ} (hν : 0 ≤ ν) :
    ConvexOn ℝ univ (determinantPowerProfile (k := k) ν) ∧
    Monotone (determinantPowerProfile (k := k) ν) ∧
    SymmetricProfile (determinantPowerProfile (k := k) ν) := by
  have heq : determinantPowerProfile (k := k) ν = coordinatePlane (fun _ => ν) 0 := by
    funext x
    simp [determinantPowerProfile, coordinatePlane, Finset.mul_sum]
  refine ⟨?_, ?_, ?_⟩
  · rw [heq]
    exact convexOn_coordinatePlane _ _
  · rw [heq]
    exact monotone_coordinatePlane (fun _ => hν) _
  · intro σ x
    simp only [determinantPowerProfile, Function.comp_apply, Equiv.sum_comp]

def polynomialPowerProfile (p : MvPolynomial (Fin k) ℝ) (ν : ℝ)
    (x : Fin k → ℝ) : ℝ :=
  ν * Real.log (MvPolynomial.eval (fun i => Real.exp (x i)) p)

theorem polynomial_eval_exp_eq_weighted (p : MvPolynomial (Fin k) ℝ)
    (x : Fin k → ℝ) :
    MvPolynomial.eval (fun i => Real.exp (x i)) p =
      weightedExponentialSum (fun d : p.support => p.coeff d)
        (fun d => coordinatePlane (fun i => (d.val i : ℝ)) 0) x := by
  rw [MvPolynomial.eval_eq', weightedExponentialSum,
    Finset.sum_coe_sort p.support (fun d => p.coeff d *
      Real.exp (coordinatePlane (fun i => (d i : ℝ)) 0 x))]
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  simp only [coordinatePlane, add_zero, Real.exp_sum, Real.exp_nat_mul]

theorem polynomial_eval_pos (p : MvPolynomial (Fin k) ℝ) (hp : p ≠ 0)
    (hc : ∀ d, 0 ≤ p.coeff d) {x : Fin k → ℝ} (hx : ∀ i, 0 < x i) :
    0 < MvPolynomial.eval x p := by
  rw [MvPolynomial.eval_eq']
  obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hp
  have hcoeff : 0 < p.coeff d := lt_of_le_of_ne (hc d)
    (Ne.symm (MvPolynomial.mem_support_iff.mp hd))
  have hterm : 0 < p.coeff d * ∏ i, x i ^ d i :=
    mul_pos hcoeff (Finset.prod_pos (fun i _ => pow_pos (hx i) _))
  exact hterm.trans_le (Finset.single_le_sum
    (fun e he => mul_nonneg (hc e) (Finset.prod_nonneg fun i _ => pow_nonneg (hx i).le _)) hd)

theorem polynomialPowerProfile_properties (p : MvPolynomial (Fin k) ℝ)
    (hp : p ≠ 0) (hc : ∀ d, 0 ≤ p.coeff d) (hsym : p.IsSymmetric)
    {ν : ℝ} (hν : 0 ≤ ν) :
    ConvexOn ℝ univ (polynomialPowerProfile p ν) ∧
    Monotone (polynomialPowerProfile p ν) ∧ SymmetricProfile (polynomialPowerProfile p ν) := by
  let c : p.support → ℝ := fun d => p.coeff d
  let g : p.support → (Fin k → ℝ) → ℝ := fun d =>
    coordinatePlane (fun i => (d.val i : ℝ)) 0
  have hc' (d : p.support) : 0 ≤ c d := hc d
  have hpos : ∃ d : p.support, 0 < c d := by
    obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hp
    exact ⟨⟨d, hd⟩, lt_of_le_of_ne (hc d)
      (Ne.symm (MvPolynomial.mem_support_iff.mp hd))⟩
  have heq : polynomialPowerProfile p ν = fun x =>
      ν * Real.log (weightedExponentialSum c g x) := by
    funext x
    rw [polynomialPowerProfile, polynomial_eval_exp_eq_weighted]
  refine ⟨?_, ?_, ?_⟩
  · rw [heq]
    exact (convexOn_log_weightedExponentialSum c g hc' hpos
      (fun d => convexOn_coordinatePlane _ _)).smul hν
  · rw [heq]
    intro x y hxy
    exact mul_le_mul_of_nonneg_left
      (monotone_log_weightedExponentialSum c g hc' hpos
        (fun d => monotone_coordinatePlane (fun i => Nat.cast_nonneg _) 0) hxy) hν
  · intro σ x
    unfold polynomialPowerProfile
    congr 2
    have h := congrArg (MvPolynomial.eval (fun i => Real.exp (x i))) (hsym σ)
    simpa only [MvPolynomial.eval_rename, Function.comp_def] using h

/-- The profile evaluates to the actual polynomial power even on singular faces. -/
theorem spectralBoundaryValue_polynomialPowerProfile
    (p : MvPolynomial (Fin k) ℝ) (hp : p ≠ 0) (hc : ∀ d, 0 ≤ p.coeff d)
    (hsym : p.IsSymmetric) {ν : ℝ} (hν : 0 ≤ ν)
    {x : Fin k → ℝ} (hx : ∀ i, 0 ≤ x i) :
    spectralBoundaryValue (polynomialPowerProfile p ν) x = (MvPolynomial.eval x p) ^ ν := by
  have hm := (polynomialPowerProfile_properties p hp hc hsym hν).2.1
  have harg : Tendsto (fun ε : ℝ => fun i => x i + ε) (𝓝[>] 0) (𝓝 x) := by
    apply tendsto_pi_nhds.mpr
    intro i
    simpa only [add_zero] using tendsto_const_nhds.add
      (show Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) from nhdsWithin_le_nhds)
  have hlimit : Tendsto (fun ε : ℝ => (MvPolynomial.eval (fun i => x i + ε) p) ^ ν)
      (𝓝[>] 0) (𝓝 ((MvPolynomial.eval x p) ^ ν)) :=
    ((Real.continuous_rpow_const hν).tendsto _).comp
      ((MvPolynomial.continuous_eval p).tendsto _ |>.comp harg)
  apply tendsto_nhds_unique (spectralBoundaryValue_tendsto_epsilon hm hx)
  apply hlimit.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hxp (i : Fin k) : 0 < x i + ε := add_pos_of_nonneg_of_pos (hx i) hε
  simp only [polynomialPowerProfile, Real.exp_log (hxp _)]
  rw [Real.rpow_def_of_pos (polynomial_eval_pos p hp hc hxp)]
  congr 1
  ring

theorem elementaryPolynomial_coeff_nonneg (r : ℕ) (d : Fin k →₀ ℕ) :
    0 ≤ (MvPolynomial.esymm (Fin k) ℝ r).coeff d := by
  rw [MvPolynomial.esymm_eq_sum_monomial, MvPolynomial.coeff_sum]
  apply Finset.sum_nonneg
  intro S hS
  simp only [MvPolynomial.coeff_monomial]
  split_ifs <;> norm_num

theorem elementaryPolynomial_ne_zero {r : ℕ} (hr : r ≤ k) :
    MvPolynomial.esymm (Fin k) ℝ r ≠ 0 := by
  apply MvPolynomial.support_nonempty.mp
  rw [MvPolynomial.support_esymm]
  exact (Finset.powersetCard_nonempty.mpr (by simpa using hr)).image _

theorem elementaryPowerProfile_properties {r : ℕ} (hr : r ≤ k)
    {ν : ℝ} (hν : 0 ≤ ν) :
    ConvexOn ℝ univ (polynomialPowerProfile (MvPolynomial.esymm (Fin k) ℝ r) ν) ∧
    Monotone (polynomialPowerProfile (MvPolynomial.esymm (Fin k) ℝ r) ν) ∧
    SymmetricProfile (polynomialPowerProfile (MvPolynomial.esymm (Fin k) ℝ r) ν) :=
  polynomialPowerProfile_properties _ (elementaryPolynomial_ne_zero hr)
    (elementaryPolynomial_coeff_nonneg r) (MvPolynomial.esymm_isSymmetric _ _ r) hν

theorem spectralBoundaryValue_elementaryPowerProfile {r : ℕ} (hr : r ≤ k)
    {ν : ℝ} (hν : 0 ≤ ν) {x : Fin k → ℝ} (hx : ∀ i, 0 ≤ x i) :
    spectralBoundaryValue (polynomialPowerProfile (MvPolynomial.esymm (Fin k) ℝ r) ν) x =
      (∑ S ∈ (Finset.univ : Finset (Fin k)).powersetCard r, ∏ i ∈ S, x i) ^ ν := by
  rw [spectralBoundaryValue_polynomialPowerProfile _ (elementaryPolynomial_ne_zero hr)
    (elementaryPolynomial_coeff_nonneg r) (MvPolynomial.esymm_isSymmetric _ _ r) hν hx]
  simp only [MvPolynomial.esymm, map_sum, map_prod, MvPolynomial.eval_X]

end Wishart.Spectral
end
end CanonicalSource73

section CanonicalSource74
/- Source: Wishart/SpectralSchurProfiles.lean -/



/-!
# Actual Schur-positive polynomials in the field spectral class

The polynomial is the finite nonnegative linear combination of the actual
tableau-defined Schur polynomials.  Its ordinary monomial coefficients are
proved nonnegative from the Kostka-number formula, and its symmetry is the
proved Bender--Knuth symmetry.  Neither property is an extra hypothesis.

An identically zero polynomial is handled explicitly.  It is not represented
as the exponential of a finite logarithmic profile: its positive powers are
the genuine zero factor in the extended product convention.
-/

noncomputable section
open Set MvPolynomial
open scoped Classical BigOperators

namespace Wishart.Spectral
variable {k : ℕ} {ι : Type*} [Fintype ι]

def schurPositivePolynomial (c : ι → ℝ) (mu : ι → YoungDiagram) :
    MvPolynomial (Fin k) ℝ :=
  ∑ j, MvPolynomial.C (c j) * TauCeti.diagramSchurPoly k ℝ (mu j)

theorem schurPositivePolynomial_coeff_nonneg (c : ι → ℝ) (mu : ι → YoungDiagram)
    (hc : ∀ j, 0 ≤ c j) (d : Fin k →₀ ℕ) :
    0 ≤ (schurPositivePolynomial (k := k) c mu).coeff d := by
  rw [schurPositivePolynomial, MvPolynomial.coeff_sum]
  apply Finset.sum_nonneg
  intro j hj
  rw [MvPolynomial.coeff_C_mul, TauCeti.coeff_diagramSchurPoly]
  exact mul_nonneg (hc j) (Nat.cast_nonneg _)

theorem schurPositivePolynomial_symmetric (c : ι → ℝ) (mu : ι → YoungDiagram) :
    (schurPositivePolynomial (k := k) c mu).IsSymmetric := by
  intro σ
  simp only [schurPositivePolynomial, map_sum, map_mul, MvPolynomial.rename_C,
    TauCeti.isSymmetric_diagramSchurPoly k ℝ (mu _) σ]

theorem schurPositiveProfile_properties (c : ι → ℝ) (mu : ι → YoungDiagram)
    (hc : ∀ j, 0 ≤ c j) (hp : schurPositivePolynomial (k := k) c mu ≠ 0)
    {a : ℝ} (ha : 0 ≤ a) :
    ConvexOn ℝ univ (polynomialPowerProfile (schurPositivePolynomial (k := k) c mu) a) ∧
      Monotone (polynomialPowerProfile (schurPositivePolynomial (k := k) c mu) a) ∧
      SymmetricProfile (polynomialPowerProfile (schurPositivePolynomial (k := k) c mu) a) :=
  polynomialPowerProfile_properties _ hp
    (schurPositivePolynomial_coeff_nonneg c mu hc)
    (schurPositivePolynomial_symmetric c mu) ha

theorem spectralBoundaryValue_schurPositiveProfile (c : ι → ℝ) (mu : ι → YoungDiagram)
    (hc : ∀ j, 0 ≤ c j) (hp : schurPositivePolynomial (k := k) c mu ≠ 0)
    {a : ℝ} (ha : 0 ≤ a) {x : Fin k → ℝ} (hx : ∀ i, 0 ≤ x i) :
    spectralBoundaryValue (polynomialPowerProfile (schurPositivePolynomial (k := k) c mu) a) x =
      (∑ j, c j * MvPolynomial.eval x (TauCeti.diagramSchurPoly k ℝ (mu j))) ^ a := by
  rw [spectralBoundaryValue_polynomialPowerProfile _ hp
    (schurPositivePolynomial_coeff_nonneg c mu hc)
    (schurPositivePolynomial_symmetric c mu) ha hx]
  simp only [schurPositivePolynomial, map_sum, map_mul, MvPolynomial.eval_C]

/-- Every printed Schur-positive power is either identically zero, or is the
boundary value of an actual admissible finite profile.  No nonzero hypothesis
is imposed on the polynomial in this exhaustive statement. -/
theorem schurPositivePower_zero_or_profile (c : ι → ℝ) (mu : ι → YoungDiagram)
    (hc : ∀ j, 0 ≤ c j) {a : ℝ} (ha : 0 ≤ a) :
    (∀ x : Fin k → ℝ, (MvPolynomial.eval x (schurPositivePolynomial (k := k) c mu)) ^ a = 0) ∨
      ∃ h : (Fin k → ℝ) → ℝ,
        ConvexOn ℝ univ h ∧ Monotone h ∧ SymmetricProfile h ∧
        ∀ x : Fin k → ℝ, (∀ i, 0 ≤ x i) →
          spectralBoundaryValue h x =
            (MvPolynomial.eval x (schurPositivePolynomial (k := k) c mu)) ^ a := by
  by_cases hp : schurPositivePolynomial (k := k) c mu = 0
  · by_cases ha0 : a = 0
    · subst a
      refine Or.inr ⟨fun _ => 0, convexOn_const 0 convex_univ,
        monotone_const, ?_, ?_⟩
      · intro σ x
        rfl
      · intro x hx
        simp only [spectralBoundaryValue, spectralRegularization, Real.exp_zero,
          ciInf_const, Real.rpow_zero]
    · exact Or.inl fun x => by simp only [hp, map_zero, Real.zero_rpow ha0]
  · refine Or.inr ⟨polynomialPowerProfile (schurPositivePolynomial (k := k) c mu) a,
      (schurPositiveProfile_properties c mu hc hp ha).1,
      (schurPositiveProfile_properties c mu hc hp ha).2.1,
      (schurPositiveProfile_properties c mu hc hp ha).2.2, ?_⟩
    intro x hx
    exact spectralBoundaryValue_polynomialPowerProfile _ hp
      (schurPositivePolynomial_coeff_nonneg c mu hc)
      (schurPositivePolynomial_symmetric c mu) ha hx

end Wishart.Spectral
end
end CanonicalSource74

section CanonicalSource75
/- Source: Wishart/SpectralTraceAndOuterProfiles.lean -/



/-!
# The determinant-outer and trace-power examples in Theorem 7.1

The profile hypotheses are proved from the printed hypotheses on the outer
function or the two real exponents.  Boundary identities use the actual
right-hand matrix-eigenvalue regularization, through the existing scalar
boundary theorem.  No logarithmic convexity premise is added to trace powers.
-/

noncomputable section
open Set Filter Topology
open scoped Classical BigOperators

namespace Wishart.Spectral
open WishartVerification
variable {k : ℕ}

theorem spectralBoundaryValue_eq_of_continuousOn
    {h : (Fin k → ℝ) → ℝ} (hm : Monotone h)
    {g : (Fin k → ℝ) → ℝ}
    (hg : ContinuousOn g {x | ∀ i, 0 ≤ x i})
    (hvalue : ∀ x : Fin k → ℝ, (∀ i, 0 < x i) →
      Real.exp (h (fun i => Real.log (x i))) = g x)
    {x : Fin k → ℝ} (hx : ∀ i, 0 ≤ x i) :
    spectralBoundaryValue h x = g x := by
  have harg : Tendsto (fun ε : ℝ => fun i => x i + ε) (𝓝[>] 0) (𝓝 x) := by
    apply tendsto_pi_nhds.mpr
    intro i
    simpa only [add_zero] using tendsto_const_nhds.add
      (show Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) from nhdsWithin_le_nhds)
  have harg' : Tendsto (fun ε : ℝ => fun i => x i + ε) (𝓝[>] 0)
      (𝓝[{z : Fin k → ℝ | ∀ i, 0 ≤ z i}] x) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨harg, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with ε hε i
    exact (add_pos_of_nonneg_of_pos (hx i) hε).le
  apply tendsto_nhds_unique (spectralBoundaryValue_tendsto_epsilon hm hx)
  apply ((hg x hx).tendsto.comp harg').congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (hvalue (fun i => x i + ε)
    (fun i => add_pos_of_nonneg_of_pos (hx i) hε)).symm

def geometricDeterminantProfile (f : ℝ → ℝ) (c : ℝ) (x : Fin k → ℝ) : ℝ :=
  Real.log (f (c * Real.exp (∑ i, x i)))

theorem geometricDeterminantProfile_properties {f : ℝ → ℝ}
    (hf : GeometricallyLogConvex f) {c : ℝ} (hc : 0 < c) :
    ConvexOn ℝ univ (geometricDeterminantProfile (k := k) f c) ∧
      Monotone (geometricDeterminantProfile (k := k) f c) ∧
      SymmetricProfile (geometricDeterminantProfile (k := k) f c) := by
  have hscaled := hf.scale_argument hc
  refine ⟨⟨convex_univ, ?_⟩, ?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    have h := hscaled.convex_log.2 (mem_univ (∑ i, x i))
      (mem_univ (∑ i, y i)) ha hb hab
    simpa only [geometricDeterminantProfile, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum] using h
  · intro x y hxy
    exact hscaled.monotone_log (Finset.sum_le_sum fun i _ => hxy i)
  · intro σ x
    simp only [geometricDeterminantProfile, Function.comp_apply, Equiv.sum_comp]

theorem geometricDeterminantProfile_positive_value {f : ℝ → ℝ}
    (hf : GeometricallyLogConvex f) {c : ℝ} (hc : 0 < c)
    {x : Fin k → ℝ} (hx : ∀ i, 0 < x i) :
    Real.exp (geometricDeterminantProfile f c (fun i => Real.log (x i))) =
      f (c * ∏ i, x i) := by
  simp only [geometricDeterminantProfile, Real.exp_sum, Real.exp_log (hx _)]
  exact Real.exp_log (hf.positive _ (mul_pos hc (Finset.prod_pos fun i _ => hx i)))

/-- If the outer function is presented with its stipulated continuous value
at zero, the scalar boundary is precisely that actual value at the determinant. -/
theorem spectralBoundaryValue_geometricDeterminantProfile {f : ℝ → ℝ}
    (hf : GeometricOuterOnNonnegative f) {c : ℝ} (hc : 0 < c)
    {x : Fin k → ℝ} (hx : ∀ i, 0 ≤ x i) :
    spectralBoundaryValue (geometricDeterminantProfile f c) x = f (c * ∏ i, x i) := by
  apply spectralBoundaryValue_eq_of_continuousOn
    (geometricDeterminantProfile_properties hf.geometric hc).2.1 _
    (fun y hy => geometricDeterminantProfile_positive_value hf.geometric hc hy) hx
  apply hf.continuousOn.comp (by fun_prop)
  intro y hy
  exact mul_nonneg hc.le (Finset.prod_nonneg fun i _ => hy i)

def tracePowerProfile (r a : ℝ) (x : Fin k → ℝ) : ℝ :=
  (a / r) * Real.log (∑ i, Real.exp (r * x i))

theorem tracePowerProfile_properties (hk : 0 < k) {r a : ℝ}
    (hr : 0 < r) (ha : 0 ≤ a) :
    ConvexOn ℝ univ (tracePowerProfile (k := k) r a) ∧
      Monotone (tracePowerProfile (k := k) r a) ∧
      SymmetricProfile (tracePowerProfile (k := k) r a) := by
  let c : Fin k → ℝ := fun _ => 1
  let g : Fin k → (Fin k → ℝ) → ℝ := fun i x => r * x i
  have hpos : ∃ i : Fin k, 0 < c i := ⟨⟨0, hk⟩, zero_lt_one⟩
  have hg (i : Fin k) : ConvexOn ℝ univ (g i) := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy u v hu hv huv
    dsimp [g]
    exact le_of_eq (by ring)
  have hm (i : Fin k) : Monotone (g i) := fun x y hxy =>
    mul_le_mul_of_nonneg_left (hxy i) hr.le
  have heq : tracePowerProfile (k := k) r a =
      fun x => (a / r) * Real.log (weightedExponentialSum c g x) := by
    funext x
    simp only [tracePowerProfile, weightedExponentialSum, c, g, one_mul]
  refine ⟨?_, ?_, ?_⟩
  · rw [heq]
    exact (convexOn_log_weightedExponentialSum c g (fun _ => zero_le_one) hpos hg).smul
      (div_nonneg ha hr.le)
  · rw [heq]
    intro x y hxy
    exact mul_le_mul_of_nonneg_left
      (monotone_log_weightedExponentialSum c g (fun _ => zero_le_one) hpos hm hxy)
      (div_nonneg ha hr.le)
  · intro σ x
    unfold tracePowerProfile
    congr 2
    exact Equiv.sum_comp σ (fun i => Real.exp (r * x i))

theorem tracePowerProfile_positive_value (hk : 0 < k) {r a : ℝ}
    {x : Fin k → ℝ} (hx : ∀ i, 0 < x i) :
    Real.exp (tracePowerProfile r a (fun i => Real.log (x i))) =
      (∑ i, x i ^ r) ^ (a / r) := by
  have hsum : 0 < ∑ i, x i ^ r :=
    Finset.sum_pos (fun i _ => Real.rpow_pos_of_pos (hx i) r)
      ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  have hterm (i : Fin k) : Real.exp (r * Real.log (x i)) = x i ^ r := by
    rw [Real.rpow_def_of_pos (hx i), mul_comm r]
  rw [tracePowerProfile, Real.rpow_def_of_pos hsum]
  simp only [hterm]
  congr 1
  ring

theorem spectralBoundaryValue_tracePowerProfile (hk : 0 < k) {r a : ℝ}
    (hr : 0 < r) (ha : 0 ≤ a) {x : Fin k → ℝ} (hx : ∀ i, 0 ≤ x i) :
    spectralBoundaryValue (tracePowerProfile r a) x = (∑ i, x i ^ r) ^ (a / r) := by
  apply spectralBoundaryValue_eq_of_continuousOn
    (tracePowerProfile_properties hk hr ha).2.1 _
    (fun y hy => tracePowerProfile_positive_value hk hy) hx
  exact ((Real.continuous_rpow_const (div_nonneg ha hr.le)).comp
    (continuous_finsetSum _ fun i _ =>
      (Real.continuous_rpow_const hr.le).comp (continuous_apply i))).continuousOn

end Wishart.Spectral
end
end CanonicalSource75

section CanonicalSource76
/- Source: Wishart/SpectralNormProfiles.lean -/



/-!
# Logarithmic convexity derived from a symmetric absolute norm

Coordinate monotonicity follows by averaging a vector with its sign flip.
Logarithmic convexity follows by normalizing two positive vectors, applying
the scalar weighted arithmetic--geometric inequality, then using norm
convexity and homogeneity.  It is not included among the norm's assumptions.
-/

noncomputable section
open Set Filter Topology
open scoped Classical BigOperators

namespace Wishart.Spectral

structure SymmetricAbsoluteNorm (k : ℕ) where
  toSeminorm : Seminorm ℝ (Fin k → ℝ)
  separates : ∀ x, toSeminorm x = 0 → x = 0
  permutation : ∀ (σ : Equiv.Perm (Fin k)) x, toSeminorm (x ∘ σ) = toSeminorm x
  signFlip : ∀ (i : Fin k) x, toSeminorm (Function.update x i (-x i)) = toSeminorm x

instance {k : ℕ} : CoeFun (SymmetricAbsoluteNorm k) (fun _ => (Fin k → ℝ) → ℝ) :=
  ⟨fun q => q.toSeminorm⟩

namespace SymmetricAbsoluteNorm
variable {k : ℕ} (q : SymmetricAbsoluteNorm k)

theorem nonneg (x : Fin k → ℝ) : 0 ≤ q x := apply_nonneg q.toSeminorm x

theorem smul_nonneg {a : ℝ} (ha : 0 ≤ a) (x : Fin k → ℝ) :
    q (a • x) = a * q x := by
  change q.toSeminorm (a • x) = _
  rw [map_smul_eq_mul, Real.norm_of_nonneg ha]

theorem continuous : Continuous q := by
  simpa only [interior_univ, continuousOn_univ] using
    q.toSeminorm.convexOn.continuousOn_interior

theorem positive (hk : 0 < k) {x : Fin k → ℝ} (hx : ∀ i, 0 < x i) : 0 < q x := by
  apply lt_of_le_of_ne (q.nonneg x)
  intro hzero
  have h := q.separates x hzero.symm
  have hx0 := hx ⟨0, hk⟩
  exact (lt_irrefl (0 : ℝ)) (by simpa only [h, Pi.zero_apply] using hx0)

theorem monotoneOn_nonnegative : MonotoneOn q {x | ∀ i, 0 ≤ x i} := by
  apply WishartVerification.monotoneOn_of_monotone_updates (fun _ => Ici (0 : ℝ)) q
  intro x hx i t ht hxt
  by_cases ht0 : t = 0
  · have hx0 : x i = 0 := le_antisymm (by simpa only [ht0] using hxt) (hx i)
    simp only [ht0, ← hx0, Function.update_eq_self, le_refl]
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    let y := Function.update x i t
    let z := Function.update y i (-t)
    let a := (t + x i) / (2 * t)
    let b := (t - x i) / (2 * t)
    have ha : 0 ≤ a := div_nonneg (add_nonneg ht (hx i)) (by positivity)
    have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr hxt) (by positivity)
    have hab : a + b = 1 := by dsimp [a, b]; field_simp [ht0]; ring
    have heq : a • y + b • z = x := by
      funext j
      by_cases hji : j = i
      · subst j
        simp only [Pi.add_apply, Pi.smul_apply, y, z, Function.update_self, smul_eq_mul]
        dsimp [a, b]
        field_simp [ht0]
        ring
      · simp only [Pi.add_apply, Pi.smul_apply, y, z, Function.update_of_ne hji,
          smul_eq_mul, ← add_mul, hab, one_mul]
    have hz : q z = q y := by simpa only [z, y, Function.update_self] using q.signFlip i y
    calc
      q x = q (a • y + b • z) := congrArg q heq.symm
      _ ≤ a * q y + b * q z :=
        q.toSeminorm.convexOn.2 (mem_univ y) (mem_univ z) ha hb hab
      _ = q y := by rw [hz, ← add_mul, hab, one_mul]

def logarithmicProfile (x : Fin k → ℝ) : ℝ := Real.log (q (fun i => Real.exp (x i)))

theorem normalized_exponential_norm (hk : 0 < k) (x : Fin k → ℝ) :
    q (fun i => Real.exp (x i - q.logarithmicProfile x)) = 1 := by
  have hq : 0 < q (fun i => Real.exp (x i)) := q.positive hk (fun i => Real.exp_pos _)
  have heq : (fun i => Real.exp (x i - q.logarithmicProfile x)) =
      (q (fun i => Real.exp (x i)))⁻¹ • (fun i => Real.exp (x i)) := by
    funext i
    simp only [logarithmicProfile, Real.exp_sub, Real.exp_log hq, Pi.smul_apply,
      smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [heq, q.smul_nonneg (inv_nonneg.mpr hq.le), inv_mul_cancel₀ hq.ne']

theorem logarithmicProfile_convex (hk : 0 < k) : ConvexOn ℝ univ q.logarithmicProfile := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  let z := a • x + b • y
  let C := a * q.logarithmicProfile x + b * q.logarithmicProfile y
  have hcoordinate (i : Fin k) :
      Real.exp (z i - C) ≤ a * Real.exp (x i - q.logarithmicProfile x) +
        b * Real.exp (y i - q.logarithmicProfile y) := by
    have h := convexOn_exp.2 (mem_univ (x i - q.logarithmicProfile x))
      (mem_univ (y i - q.logarithmicProfile y)) ha hb hab
    simp only [smul_eq_mul] at h
    have heq : z i - C = a * (x i - q.logarithmicProfile x) +
        b * (y i - q.logarithmicProfile y) := by
      dsimp [z, C]
      ring
    rw [heq]
    exact h
  have hnorm : q (fun i => Real.exp (z i - C)) ≤ 1 := by
    calc
      _ ≤ q (a • (fun i => Real.exp (x i - q.logarithmicProfile x)) +
          b • (fun i => Real.exp (y i - q.logarithmicProfile y))) :=
        q.monotoneOn_nonnegative (fun i => (Real.exp_pos _).le)
          (fun i => add_nonneg (mul_nonneg ha (Real.exp_pos _).le)
            (mul_nonneg hb (Real.exp_pos _).le)) hcoordinate
      _ ≤ a * q (fun i => Real.exp (x i - q.logarithmicProfile x)) +
          b * q (fun i => Real.exp (y i - q.logarithmicProfile y)) :=
        q.toSeminorm.convexOn.2 (mem_univ _) (mem_univ _) ha hb hab
      _ = 1 := by rw [q.normalized_exponential_norm hk x,
          q.normalized_exponential_norm hk y, mul_one, mul_one, hab]
  have heq : (fun i => Real.exp (z i)) =
      Real.exp C • (fun i => Real.exp (z i - C)) := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, ← Real.exp_add]
    congr 1
    ring
  have hbound : q (fun i => Real.exp (z i)) ≤ Real.exp C := by
    rw [heq, q.smul_nonneg (Real.exp_pos C).le]
    exact (mul_le_mul_of_nonneg_left hnorm (Real.exp_pos C).le).trans_eq (mul_one _)
  exact (Real.log_le_iff_le_exp (q.positive hk (fun i => Real.exp_pos _))).mpr hbound

theorem logarithmicProfile_monotone (hk : 0 < k) : Monotone q.logarithmicProfile := by
  intro x y hxy
  apply Real.log_le_log (q.positive hk (fun i => Real.exp_pos _))
  exact q.monotoneOn_nonnegative (fun i => (Real.exp_pos _).le)
    (fun i => (Real.exp_pos _).le) (fun i => Real.exp_le_exp.mpr (hxy i))

def sqrtPowerProfile (a : ℝ) (x : Fin k → ℝ) : ℝ :=
  a * q.logarithmicProfile (fun i => x i / 2)

theorem sqrtPowerProfile_properties (hk : 0 < k) {a : ℝ} (ha : 0 ≤ a) :
    ConvexOn ℝ univ (q.sqrtPowerProfile a) ∧ Monotone (q.sqrtPowerProfile a) ∧
      SymmetricProfile (q.sqrtPowerProfile a) := by
  have hc := (q.logarithmicProfile_convex hk).comp_linearMap
    ((1 / 2 : ℝ) • (LinearMap.id : (Fin k → ℝ) →ₗ[ℝ] (Fin k → ℝ)))
  refine ⟨?_, ?_, ?_⟩
  · have harg (x : Fin k → ℝ) : (1 / 2 : ℝ) • x = fun i => x i / 2 := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, one_mul, mul_comm]
    change ConvexOn ℝ univ (fun x : Fin k → ℝ => a * q.logarithmicProfile (fun i => x i / 2))
    simpa only [Set.preimage_univ, Function.comp_def, LinearMap.smul_apply,
      LinearMap.id_apply, harg, smul_eq_mul] using hc.smul ha
  · intro x y hxy
    exact mul_le_mul_of_nonneg_left
      (q.logarithmicProfile_monotone hk (fun i => div_le_div_of_nonneg_right (hxy i) (by norm_num))) ha
  · intro σ x
    unfold sqrtPowerProfile logarithmicProfile
    congr 2
    exact q.permutation σ (fun i => Real.exp (x i / 2))

theorem sqrtPowerProfile_positive_value (hk : 0 < k) {a : ℝ}
    {x : Fin k → ℝ} (hx : ∀ i, 0 < x i) :
    Real.exp (q.sqrtPowerProfile a (fun i => Real.log (x i))) =
      q (fun i => Real.sqrt (x i)) ^ a := by
  have heq (i : Fin k) : Real.exp (Real.log (x i) / 2) = Real.sqrt (x i) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (hx i)]
    congr 1
    ring
  have hq : 0 < q (fun i => Real.sqrt (x i)) :=
    q.positive hk (fun i => Real.sqrt_pos.mpr (hx i))
  simp only [sqrtPowerProfile, logarithmicProfile, heq]
  rw [Real.rpow_def_of_pos hq, mul_comm a]

theorem spectralBoundaryValue_sqrtPowerProfile (hk : 0 < k) {a : ℝ}
    (ha : 0 ≤ a) {x : Fin k → ℝ} (hx : ∀ i, 0 ≤ x i) :
    spectralBoundaryValue (q.sqrtPowerProfile a) x = q (fun i => Real.sqrt (x i)) ^ a := by
  apply spectralBoundaryValue_eq_of_continuousOn (q.sqrtPowerProfile_properties hk ha).2.1 _
    (fun y hy => q.sqrtPowerProfile_positive_value hk hy) hx
  exact ((Real.continuous_rpow_const ha).comp
    (q.continuous.comp (continuous_pi fun i => Real.continuous_sqrt.comp (continuous_apply i)))).continuousOn

end SymmetricAbsoluteNorm
end Wishart.Spectral
end
end CanonicalSource76

section CanonicalSource77
/- Source: Wishart/FieldUnitaryNormProfiles.lean -/



/-!
# Actual unitarily invariant norms give the advertised spectral profiles

The matrix norm is a separating real seminorm, invariant under actual left
and right unitary multiplication.  Its restriction to real diagonal matrices
is proved to be a symmetric absolute norm.  The convexity required by Theorem
7.1 is then derived from the norm axioms, rather than assumed.  The boundary
identity is with the norm of the genuine positive square root, including
singular matrices.
-/

noncomputable section
open Matrix Set
open scoped Classical Quaternion ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Wishart.Spectral

structure UnitarilyInvariantNorm (F : Type*) [Ring F] [Algebra ℝ F] [StarRing F]
    (k : ℕ) where
  toSeminorm : Seminorm ℝ (Matrix (Fin k) (Fin k) F)
  separates : ∀ M, toSeminorm M = 0 → M = 0
  invariant : ∀ (U V : unitary (Matrix (Fin k) (Fin k) F)) M,
    toSeminorm (U.val * M * V.val) = toSeminorm M

instance {F : Type*} [Ring F] [Algebra ℝ F] [StarRing F] {k : ℕ} :
    CoeFun (UnitarilyInvariantNorm F k)
      (fun _ => Matrix (Fin k) (Fin k) F → ℝ) := ⟨fun N => N.toSeminorm⟩

namespace UnitarilyInvariantNorm

variable {F : Type*} [Ring F] [Algebra ℝ F] [StarRing F]

def realDiagonalMap (k : ℕ) :
    (Fin k → ℝ) →ₗ[ℝ] Matrix (Fin k) (Fin k) F where
  toFun x := Matrix.diagonal (fun i => algebraMap ℝ F (x i))
  map_add' x y := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal_apply, hij]
  map_smul' a x := by
    ext i j
    simp [Matrix.diagonal_apply, Algebra.smul_def]

def signUnitary {k : ℕ} (i : Fin k) : unitary (Matrix (Fin k) (Fin k) F) := by
  let D : Matrix (Fin k) (Fin k) F := Matrix.diagonal (fun j => if j = i then -1 else 1)
  have hs : Dᴴ = D := by
    ext j l
    by_cases hjl : j = l
    · subst l
      by_cases hji : j = i <;> simp [D, Matrix.conjTranspose_apply, Matrix.diagonal_apply, hji]
    · simp [D, Matrix.conjTranspose_apply, Matrix.diagonal_apply, hjl, Ne.symm hjl]
  have hsq : D * D = 1 := by
    dsimp [D]
    rw [Matrix.diagonal_mul_diagonal]
    ext j l
    by_cases hjl : j = l
    · subst l
      by_cases hji : j = i <;> simp [hji]
    · simp [Matrix.diagonal_apply, hjl]
  refine ⟨D, ?_⟩
  change Dᴴ * D = 1 ∧ D * Dᴴ = 1
  exact ⟨by rw [hs, hsq], by rw [hs, hsq]⟩

theorem signUnitary_mul_diagonal {k : ℕ} (i : Fin k) (x : Fin k → ℝ) :
    (signUnitary (F := F) i).val * realDiagonalMap k x =
      realDiagonalMap k (Function.update x i (-x i)) := by
  change Matrix.diagonal (fun j => if j = i then (-1 : F) else 1) *
    Matrix.diagonal (fun j => algebraMap ℝ F (x j)) = _
  rw [Matrix.diagonal_mul_diagonal]
  ext j l
  by_cases hjl : j = l
  · subst l
    by_cases hji : j = i
    · subst j
      simp [realDiagonalMap]
    · simp [realDiagonalMap, hji]
  · simp [realDiagonalMap, Matrix.diagonal_apply, hjl]

def permutationUnitary {k : ℕ} (e : Equiv.Perm (Fin k)) :
    unitary (Matrix (Fin k) (Fin k) F) := by
  refine ⟨e.permMatrix F, ?_⟩
  change (e.permMatrix F)ᴴ * e.permMatrix F = 1 ∧
    e.permMatrix F * (e.permMatrix F)ᴴ = 1
  constructor <;> simp only [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul,
    inv_mul_cancel, mul_inv_cancel, Matrix.permMatrix_one]

theorem permutationUnitary_diagonal {k : ℕ} (e : Equiv.Perm (Fin k)) (x : Fin k → ℝ) :
    (permutationUnitary (F := F) e).val *
        realDiagonalMap k x * (star (permutationUnitary (F := F) e)).val = realDiagonalMap k (x ∘ e) := by
  change e.permMatrix F * _ * (e.permMatrix F)ᴴ = _
  rw [Matrix.conjTranspose_permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  simp [realDiagonalMap, Matrix.submatrix_apply, Matrix.diagonal_apply, Equiv.Perm.inv_def, e.injective.eq_iff]

variable [FaithfulSMul ℝ F]

def diagonalNorm {k : ℕ} (N : UnitarilyInvariantNorm F k) : SymmetricAbsoluteNorm k where
  toSeminorm := N.toSeminorm.comp (realDiagonalMap k)
  separates x hx := by
    have hM := N.separates (realDiagonalMap k x) hx
    funext i
    apply FaithfulSMul.algebraMap_injective ℝ F
    have hi := congrArg (fun M : Matrix (Fin k) (Fin k) F => M i i) hM
    simpa [realDiagonalMap] using hi
  permutation e x := by
    change N (realDiagonalMap k (x ∘ e)) = N (realDiagonalMap k x)
    rw [← permutationUnitary_diagonal e x]
    exact N.invariant (permutationUnitary e) (star (permutationUnitary e)) _
  signFlip i x := by
    change N (realDiagonalMap k (Function.update x i (-x i))) = N (realDiagonalMap k x)
    rw [← signUnitary_mul_diagonal i x]
    simpa only [OneMemClass.coe_one, Matrix.mul_one] using
      N.invariant (signUnitary i) 1 (realDiagonalMap k x)

@[simp] theorem diagonalNorm_apply {k : ℕ} (N : UnitarilyInvariantNorm F k) (x : Fin k → ℝ) :
    N.diagonalNorm x = N (Matrix.diagonal (fun i => algebraMap ℝ F (x i))) := rfl

def sqrtPowerProfile {k : ℕ} (N : UnitarilyInvariantNorm F k) (a : ℝ) :
    (Fin k → ℝ) → ℝ := N.diagonalNorm.sqrtPowerProfile a

theorem sqrtPowerProfile_properties {k : ℕ} (N : UnitarilyInvariantNorm F k)
    (hk : 0 < k) {a : ℝ} (ha : 0 ≤ a) :
    ConvexOn ℝ univ (N.sqrtPowerProfile a) ∧ Monotone (N.sqrtPowerProfile a) ∧
      SymmetricProfile (N.sqrtPowerProfile a) :=
  N.diagonalNorm.sqrtPowerProfile_properties hk ha

theorem spectralBoundaryValue_sqrtPowerProfile_diagonal {k : ℕ}
    (N : UnitarilyInvariantNorm F k) (hk : 0 < k) {a : ℝ} (ha : 0 ≤ a)
    {x : Fin k → ℝ} (hx : ∀ i, 0 ≤ x i) :
    spectralBoundaryValue (N.sqrtPowerProfile a) x =
      N (Matrix.diagonal (fun i => algebraMap ℝ F (Real.sqrt (x i)))) ^ a :=
  N.diagonalNorm.spectralBoundaryValue_sqrtPowerProfile hk ha hx

theorem empty_apply (N : UnitarilyInvariantNorm F 0)
    (M : Matrix (Fin 0) (Fin 0) F) : N M = 0 := by
  calc
    N M = N 0 := congrArg N (Subsingleton.elim M 0)
    _ = 0 := map_zero N.toSeminorm

theorem empty_power (N : UnitarilyInvariantNorm F 0) (a : ℝ)
    (M : Matrix (Fin 0) (Fin 0) F) :
    N M ^ a = if a = 0 then 1 else 0 := by
  rw [N.empty_apply M]
  by_cases ha : a = 0 <;> simp [ha]

end UnitarilyInvariantNorm

namespace ComplexNorm

theorem norm_sqrt_eq_diagonal {k : ℕ} (N : UnitarilyInvariantNorm ℂ k)
    (S : Wishart.ComplexMatrix.Hermitian k)
    (hS : (S : Matrix (Fin k) (Fin k) ℂ).PosSemidef) :
    N (CFC.sqrt (S : Matrix (Fin k) (Fin k) ℂ)) =
      N.diagonalNorm (fun i => Real.sqrt (Wishart.FieldSpectral.orderedValues
        (WishartVerification.hermitian_matrix_coe S) i)) := by
  let lam := Wishart.FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe S)
  obtain ⟨U, hU⟩ := Wishart.FieldSpectral.exists_sorted_diagonalization
    (WishartVerification.hermitian_matrix_coe S)
  have hlam : ∀ i, 0 ≤ lam i := Wishart.FieldSpectral.orderedValues_nonneg hS
  change star U.val * S.val * U.val = Matrix.diagonal (fun i => (lam i : ℂ)) at hU
  have hrec : (Wishart.FieldCharts.unitaryConjugate ℂ U
      (Wishart.FieldCharts.diagonalHermitian ℂ lam) : Matrix (Fin k) (Fin k) ℂ) = S := by
    change (U : Matrix (Fin k) (Fin k) ℂ) * Matrix.diagonal (fun i => (lam i : ℂ)) * star U = S
    rw [← hU]
    calc
      _ = ((U : Matrix (Fin k) (Fin k) ℂ) * star U) * S *
          ((U : Matrix (Fin k) (Fin k) ℂ) * star U) := by
            simp only [Matrix.mul_assoc, Unitary.coe_star]
      _ = _ := by rw [Unitary.coe_mul_star_self, Matrix.one_mul, Matrix.mul_one]
  conv_lhs => rw [← hrec, Wishart.ComplexMatrix.sqrt_unitary_diagonal U lam hlam]
  change N ((U : Matrix (Fin k) (Fin k) ℂ) *
    Matrix.diagonal (fun i => (Real.sqrt (lam i) : ℂ)) * star U) =
      N (Matrix.diagonal (fun i => (Real.sqrt (lam i) : ℂ)))
  simpa only [Unitary.coe_star] using N.invariant U (star U) _

theorem spectralBoundaryValue_norm_sqrt_power {k : ℕ}
    (N : UnitarilyInvariantNorm ℂ k) (hk : 0 < k) {a : ℝ} (ha : 0 ≤ a)
    (S : Wishart.ComplexMatrix.Hermitian k)
    (hS : (S : Matrix (Fin k) (Fin k) ℂ).PosSemidef) :
    spectralBoundaryValue (N.sqrtPowerProfile a)
      (Wishart.FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe S)) =
        N (CFC.sqrt (S : Matrix (Fin k) (Fin k) ℂ)) ^ a := by
  rw [norm_sqrt_eq_diagonal N S hS]
  exact N.diagonalNorm.spectralBoundaryValue_sqrtPowerProfile hk ha
    (Wishart.FieldSpectral.orderedValues_nonneg hS)

end ComplexNorm

namespace QuaternionNorm

theorem norm_sqrt_eq_diagonal {k : ℕ} (N : UnitarilyInvariantNorm ℍ[ℝ] k)
    (S : Wishart.QuaternionMatrix.Hermitian k) (hS : Wishart.QuaternionMatrix.PosSemidef (S : Matrix (Fin k) (Fin k) ℍ[ℝ])) :
    N (Wishart.QuaternionMatrix.sqrt S) =
      N.diagonalNorm (fun i => Real.sqrt (Wishart.QuaternionMatrix.orderedValues S i)) := by
  let lam := Wishart.QuaternionMatrix.orderedValues S
  obtain ⟨U, hU⟩ := Wishart.QuaternionMatrix.exists_conjugate_diagonal S
  have hlam : ∀ i, 0 ≤ lam i := Wishart.QuaternionMatrix.orderedValues_nonneg S hS
  have hrec : Wishart.FieldCharts.unitaryConjugate ℍ[ℝ] U
      (Wishart.FieldCharts.diagonalHermitian ℍ[ℝ] lam) = S := hU
  conv_lhs => rw [← hrec, Wishart.QuaternionMatrix.sqrt_unitary_diagonal U lam hlam]
  change N (U.val *
    Matrix.diagonal (fun i => (Real.sqrt (lam i) : ℍ[ℝ])) * star U.val) =
      N (Matrix.diagonal (fun i => (Real.sqrt (lam i) : ℍ[ℝ])))
  simpa only [Unitary.coe_star] using N.invariant U (star U) _

theorem spectralBoundaryValue_norm_sqrt_power {k : ℕ}
    (N : UnitarilyInvariantNorm ℍ[ℝ] k) (hk : 0 < k) {a : ℝ} (ha : 0 ≤ a)
    (S : Wishart.QuaternionMatrix.Hermitian k) (hS : Wishart.QuaternionMatrix.PosSemidef (S : Matrix (Fin k) (Fin k) ℍ[ℝ])) :
    spectralBoundaryValue (N.sqrtPowerProfile a) (Wishart.QuaternionMatrix.orderedValues S) =
      N (Wishart.QuaternionMatrix.sqrt S) ^ a := by
  rw [norm_sqrt_eq_diagonal N S hS]
  exact N.diagonalNorm.spectralBoundaryValue_sqrtPowerProfile hk ha
    (Wishart.QuaternionMatrix.orderedValues_nonneg S hS)

end QuaternionNorm
end Wishart.Spectral
end
end CanonicalSource77

section CanonicalSource78
/- Source: Wishart/SpectralDegenerateExamples.lean -/



/-!
# Exhaustive example statements, including identically zero factors

A finite real logarithmic profile is positive on the positive cone.  Thus an
identically zero polynomial or a norm in dimension zero must be retained as
an explicit zero-factor case, not disguised as such a profile.  The results
below have no nonzero-polynomial or positive-dimension premise.
-/

noncomputable section
open Matrix Set
open scoped Classical Quaternion ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Wishart.Spectral

variable {k : ℕ}

theorem spectralBoundaryValue_determinantPowerProfile {a : ℝ} (ha : 0 ≤ a)
    {x : Fin k → ℝ} (hx : ∀ i, 0 ≤ x i) :
    spectralBoundaryValue (determinantPowerProfile a) x = (∏ i, x i) ^ a := by
  apply spectralBoundaryValue_eq_of_continuousOn
    (determinantPowerProfile_properties ha).2.1 _ ?_ hx
  · exact ((Real.continuous_rpow_const ha).comp
      (continuous_finsetProd _ fun i _ => continuous_apply i)).continuousOn
  · intro y hy
    rw [Real.rpow_def_of_pos (Finset.prod_pos fun i _ => hy i),
      Real.log_prod (fun i _ => (hy i).ne')]
    simp only [determinantPowerProfile]
    congr 1
    ring

theorem polynomialPower_zero_or_profile (p : MvPolynomial (Fin k) ℝ)
    (hp : ∀ d, 0 ≤ p.coeff d) (hs : p.IsSymmetric) {a : ℝ} (ha : 0 ≤ a) :
    (∀ x : Fin k → ℝ, (MvPolynomial.eval x p) ^ a = 0) ∨
      ∃ h : (Fin k → ℝ) → ℝ,
        ConvexOn ℝ univ h ∧ Monotone h ∧ SymmetricProfile h ∧
        ∀ x : Fin k → ℝ, (∀ i, 0 ≤ x i) →
          spectralBoundaryValue h x = (MvPolynomial.eval x p) ^ a := by
  by_cases hp0 : p = 0
  · by_cases ha0 : a = 0
    · subst a
      refine Or.inr ⟨fun _ => 0, convexOn_const 0 convex_univ,
        monotone_const, ?_, ?_⟩
      · intro σ x
        rfl
      · intro x hx
        simp only [spectralBoundaryValue, spectralRegularization, Real.exp_zero,
          ciInf_const, Real.rpow_zero]
    · exact Or.inl fun x => by simp only [hp0, map_zero, Real.zero_rpow ha0]
  · exact Or.inr ⟨polynomialPowerProfile p a,
      (polynomialPowerProfile_properties p hp0 hp hs ha).1,
      (polynomialPowerProfile_properties p hp0 hp hs ha).2.1,
      (polynomialPowerProfile_properties p hp0 hp hs ha).2.2,
      fun x hx => spectralBoundaryValue_polynomialPowerProfile p hp0 hp hs ha hx⟩

theorem elementaryPower_zero_or_profile (r : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    (∀ x : Fin k → ℝ,
      (∑ S ∈ (Finset.univ : Finset (Fin k)).powersetCard r, ∏ i ∈ S, x i) ^ a = 0) ∨
      ∃ h : (Fin k → ℝ) → ℝ,
        ConvexOn ℝ univ h ∧ Monotone h ∧ SymmetricProfile h ∧
        ∀ x : Fin k → ℝ, (∀ i, 0 ≤ x i) →
          spectralBoundaryValue h x =
            (∑ S ∈ (Finset.univ : Finset (Fin k)).powersetCard r, ∏ i ∈ S, x i) ^ a := by
  simpa only [MvPolynomial.esymm, map_sum, map_prod, MvPolynomial.eval_X] using
    polynomialPower_zero_or_profile (MvPolynomial.esymm (Fin k) ℝ r)
      (elementaryPolynomial_coeff_nonneg r) (MvPolynomial.esymm_isSymmetric _ _ r) ha

theorem tracePower_zero_or_profile {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) :
    (∀ x : Fin k → ℝ, (∑ i, x i ^ r) ^ (a / r) = 0) ∨
      ∃ h : (Fin k → ℝ) → ℝ,
        ConvexOn ℝ univ h ∧ Monotone h ∧ SymmetricProfile h ∧
        ∀ x : Fin k → ℝ, (∀ i, 0 ≤ x i) →
          spectralBoundaryValue h x = (∑ i, x i ^ r) ^ (a / r) := by
  by_cases hk : k = 0
  · subst k
    by_cases ha0 : a = 0
    · subst a
      refine Or.inr ⟨fun _ => 0, convexOn_const 0 convex_univ,
        monotone_const, ?_, ?_⟩
      · intro σ x
        rfl
      · intro x hx
        simp only [spectralBoundaryValue, spectralRegularization, Real.exp_zero,
          ciInf_const, zero_div, Real.rpow_zero]
    · exact Or.inl fun x => by
        simp only [Finset.univ_eq_empty, Finset.sum_empty,
          Real.zero_rpow (div_ne_zero ha0 hr.ne')]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    exact Or.inr ⟨tracePowerProfile r a,
      (tracePowerProfile_properties hkpos hr ha).1,
      (tracePowerProfile_properties hkpos hr ha).2.1,
      (tracePowerProfile_properties hkpos hr ha).2.2,
      fun x hx => spectralBoundaryValue_tracePowerProfile hkpos hr ha hx⟩

theorem complexNormPower_zero_or_profile (N : UnitarilyInvariantNorm ℂ k)
    {a : ℝ} (ha : 0 ≤ a) :
    (∀ S : Wishart.ComplexMatrix.Hermitian k,
      N (CFC.sqrt (S : Matrix (Fin k) (Fin k) ℂ)) ^ a = 0) ∨
      ∃ h : (Fin k → ℝ) → ℝ,
        ConvexOn ℝ univ h ∧ Monotone h ∧ SymmetricProfile h ∧
        ∀ S : Wishart.ComplexMatrix.Hermitian k,
          (S : Matrix (Fin k) (Fin k) ℂ).PosSemidef →
          spectralBoundaryValue h (Wishart.FieldSpectral.orderedValues
            (WishartVerification.hermitian_matrix_coe S)) =
              N (CFC.sqrt (S : Matrix (Fin k) (Fin k) ℂ)) ^ a := by
  by_cases hk : k = 0
  · subst k
    by_cases ha0 : a = 0
    · subst a
      refine Or.inr ⟨fun _ => 0, convexOn_const 0 convex_univ,
        monotone_const, ?_, ?_⟩
      · intro σ x
        rfl
      · intro S hS
        simp only [spectralBoundaryValue, spectralRegularization, Real.exp_zero,
          ciInf_const, Real.rpow_zero]
    · exact Or.inl fun S => by rw [N.empty_power]; simp only [ha0, ite_false]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    exact Or.inr ⟨N.sqrtPowerProfile a, (N.sqrtPowerProfile_properties hkpos ha).1,
      (N.sqrtPowerProfile_properties hkpos ha).2.1,
      (N.sqrtPowerProfile_properties hkpos ha).2.2,
      fun S hS => ComplexNorm.spectralBoundaryValue_norm_sqrt_power N hkpos ha S hS⟩

theorem quaternionNormPower_zero_or_profile (N : UnitarilyInvariantNorm ℍ[ℝ] k)
    {a : ℝ} (ha : 0 ≤ a) :
    (∀ S : Wishart.QuaternionMatrix.Hermitian k,
      N (Wishart.QuaternionMatrix.sqrt S) ^ a = 0) ∨
      ∃ h : (Fin k → ℝ) → ℝ,
        ConvexOn ℝ univ h ∧ Monotone h ∧ SymmetricProfile h ∧
        ∀ S : Wishart.QuaternionMatrix.Hermitian k, Wishart.QuaternionMatrix.PosSemidef (S : Matrix (Fin k) (Fin k) ℍ[ℝ]) →
          spectralBoundaryValue h (Wishart.QuaternionMatrix.orderedValues S) =
            N (Wishart.QuaternionMatrix.sqrt S) ^ a := by
  by_cases hk : k = 0
  · subst k
    by_cases ha0 : a = 0
    · subst a
      refine Or.inr ⟨fun _ => 0, convexOn_const 0 convex_univ,
        monotone_const, ?_, ?_⟩
      · intro σ x
        rfl
      · intro S hS
        simp only [spectralBoundaryValue, spectralRegularization, Real.exp_zero,
          ciInf_const, Real.rpow_zero]
    · exact Or.inl fun S => by rw [N.empty_power]; simp only [ha0, ite_false]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    exact Or.inr ⟨N.sqrtPowerProfile a, (N.sqrtPowerProfile_properties hkpos ha).1,
      (N.sqrtPowerProfile_properties hkpos ha).2.1,
      (N.sqrtPowerProfile_properties hkpos ha).2.2,
      fun S hS => QuaternionNorm.spectralBoundaryValue_norm_sqrt_power N hkpos ha S hS⟩

end Wishart.Spectral
end
end CanonicalSource78

section CanonicalSource79
/- Source: Wishart/FieldZeroFactorComparison.lean -/



/-!
# The printed zero-factor convention and automatic norm comparisons

The selected chain is unchanged when some factors are almost everywhere
zero.  The proof uses the actual nonnegative extended integrals, including
their `0 * infinity = 0` convention.  This transports the exhaustive
zero-or-profile examples to the actual laws of Theorem 7.1.
-/

noncomputable section
open Matrix MeasureTheory Set
open scoped Classical Quaternion ComplexOrder MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace Wishart

variable {E ι : Type*} [MeasurableSpace E] [DecidableEq ι]

theorem ae_eq_finset_product {μ : Measure E} {f g : ι → E → ℝ}
    (J : Finset ι) (h : ∀ i ∈ J, f i =ᵐ[μ] g i) :
    (fun X => ∏ i ∈ J, f i X) =ᵐ[μ] fun X => ∏ i ∈ J, g i X := by
  induction J using Finset.induction_on with
  | empty => exact Filter.Eventually.of_forall fun X => rfl
  | @insert i J hi ih =>
      simp only [Finset.prod_insert hi]
      exact (h i (Finset.mem_insert_self i J)).mul
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem lintegral_ofReal_eq_zero_of_ae_zero {μ : Measure E} {f : E → ℝ}
    (hf : f =ᵐ[μ] 0) : (∫⁻ X, ENNReal.ofReal (f X) ∂μ) = 0 := by
  calc
    _ = ∫⁻ _X, (0 : ℝ≥0∞) ∂μ := lintegral_congr_ae (hf.mono fun X hX => by simp [hX])
    _ = 0 := lintegral_zero

theorem ExtendedSelectedProductComparison.of_zero_or_aeEq {μ : Measure E}
    {f g : ι → E → ℝ} (hf : ExtendedSelectedProductComparison μ f)
    (hg : ∀ i, g i =ᵐ[μ] 0 ∨ g i =ᵐ[μ] f i) :
    ExtendedSelectedProductComparison μ g := by
  intro J j hj
  by_cases hz : ∃ i ∈ J, g i =ᵐ[μ] 0
  · obtain ⟨i, hi, hzero⟩ := hz
    have hi0 := lintegral_ofReal_eq_zero_of_ae_zero hzero
    have hJ0 : (∫⁻ X, ENNReal.ofReal (∏ l ∈ J, g l X) ∂μ) = 0 := by
      apply lintegral_ofReal_eq_zero_of_ae_zero
      filter_upwards [hzero] with X hX
      exact Finset.prod_eq_zero hi hX
    have hprod0 : (∏ l ∈ J, ∫⁻ X, ENNReal.ofReal (g l X) ∂μ) = 0 :=
      Finset.prod_eq_zero hi hi0
    have hsplit0 : (∫⁻ X, ENNReal.ofReal (g j X) ∂μ) *
        (∫⁻ X, ENNReal.ofReal (∏ l ∈ J.erase j, g l X) ∂μ) = 0 := by
      by_cases hij : i = j
      · subst i
        rw [hi0, zero_mul]
      · have herase0 : (∫⁻ X, ENNReal.ofReal (∏ l ∈ J.erase j, g l X) ∂μ) = 0 := by
          apply lintegral_ofReal_eq_zero_of_ae_zero
          filter_upwards [hzero] with X hX
          exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hij, hi⟩) hX
        rw [herase0, mul_zero]
    rw [hJ0, hprod0, hsplit0]
    exact ⟨le_rfl, le_rfl⟩
  · have heq (i : ι) (hi : i ∈ J) : g i =ᵐ[μ] f i :=
      (hg i).resolve_left (fun h => hz ⟨i, hi, h⟩)
    have hsingle (i : ι) (hi : i ∈ J) :
        (∫⁻ X, ENNReal.ofReal (g i X) ∂μ) = ∫⁻ X, ENNReal.ofReal (f i X) ∂μ :=
      lintegral_congr_ae ((heq i hi).mono fun X hX => congrArg ENNReal.ofReal hX)
    have hprod (K : Finset ι) (hK : K ⊆ J) :
        (∫⁻ X, ENNReal.ofReal (∏ i ∈ K, g i X) ∂μ) =
          ∫⁻ X, ENNReal.ofReal (∏ i ∈ K, f i X) ∂μ :=
      lintegral_congr_ae ((ae_eq_finset_product K (fun i hi => heq i (hK hi))).mono
        fun X hX => congrArg ENNReal.ofReal hX)
    have hmom : (∏ i ∈ J, ∫⁻ X, ENNReal.ofReal (g i X) ∂μ) =
        ∏ i ∈ J, ∫⁻ X, ENNReal.ofReal (f i X) ∂μ :=
      Finset.prod_congr rfl hsingle
    rw [hsingle j hj, hprod J (fun _ h => h), hprod (J.erase j) (Finset.erase_subset _ _), hmom]
    exact hf J j hj

theorem complex_zero_or_profile_comparison {p : ℕ} [Fintype ι]
    (Sigma : Matrix (Fin p) (Fin p) ℂ) (hSigma : Sigma.PosDef)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℂ)
    (hB : ∀ i, Function.Injective (B i).mulVec)
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (ψ : ∀ i, ComplexMatrix.Hermitian (k i) → ℝ)
    (hψ : ∀ i, (∀ S : ComplexMatrix.Hermitian (k i), (S : Matrix (Fin (k i)) (Fin (k i)) ℂ).PosSemidef → ψ i S = 0) ∨
      ∃ h : (Fin (k i) → ℝ) → ℝ,
        ConvexOn ℝ univ h ∧ Monotone h ∧ Spectral.SymmetricProfile h ∧
        ∀ S : ComplexMatrix.Hermitian (k i), (S : Matrix (Fin (k i)) (Fin (k i)) ℂ).PosSemidef →
          Spectral.spectralBoundaryValue h
            (FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe S)) = ψ i S)
    (μ : Measure (ComplexMatrix.Hermitian p)) (hμ : IsSectionSevenComplexLaw Sigma μ) :
    ExtendedSelectedProductComparison μ (fun i X => ψ i
      (ComplexMatrix.normalizedCompression (B i) Sigma X + c i •
        (⟨1, Matrix.isHermitian_one⟩ : ComplexMatrix.Hermitian (k i)))) := by
  have hex (i : ι) : ∃ h : (Fin (k i) → ℝ) → ℝ,
      ConvexOn ℝ univ h ∧ Monotone h ∧ Spectral.SymmetricProfile h ∧
      ((∀ S : ComplexMatrix.Hermitian (k i), (S : Matrix (Fin (k i)) (Fin (k i)) ℂ).PosSemidef → ψ i S = 0) ∨
        ∀ S : ComplexMatrix.Hermitian (k i), (S : Matrix (Fin (k i)) (Fin (k i)) ℂ).PosSemidef →
          Spectral.spectralBoundaryValue h
            (FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe S)) = ψ i S) := by
    rcases hψ i with hz | ⟨h, hconv, hmono, hsym, heq⟩
    · exact ⟨fun _ => 0, convexOn_const 0 convex_univ, monotone_const, fun _ _ => rfl, Or.inl hz⟩
    · exact ⟨h, hconv, hmono, hsym, Or.inr heq⟩
  choose h hconv hmono hsym heq using hex
  let F : ComplexSpectralFamily p ι := ⟨k, B, hB, c, hc, h, hconv, hmono, hsym⟩
  have hsupport : ∀ᵐ X : ComplexMatrix.Hermitian p ∂μ, (X : Matrix (Fin p) (Fin p) ℂ).PosSemidef := by
    rcases hμ with ⟨α, hα, rfl⟩ | ⟨n, hn, rfl⟩
    · exact (ComplexMatrix.wishart_ae_posDef α Sigma).mono fun X hX => hX.posSemidef
    · exact ComplexMatrix.gramMeasure_ae_posSemidef n Sigma
  have hcompare : ExtendedSelectedProductComparison μ (F.factor Sigma) := by
    rcases hμ with ⟨α, hα, rfl⟩ | ⟨n, hn, rfl⟩
    · exact F.density_selected_product_comparison hα Sigma hSigma
    · exact F.gram_selected_product_comparison n Sigma hSigma
  apply hcompare.of_zero_or_aeEq
  intro i
  have hpos (X : ComplexMatrix.Hermitian p)
      (hX : (X : Matrix (Fin p) (Fin p) ℂ).PosSemidef) :
      (F.shiftedCompression Sigma i X : Matrix (Fin (k i)) (Fin (k i)) ℂ).PosSemidef :=
    (ComplexMatrix.normalizedCompression_posSemidef (B i) Sigma X hX).add
      (Matrix.PosDef.one.posSemidef.smul (hc i))
  rcases heq i with hz | hval
  · exact Or.inl (hsupport.mono fun X hX => hz _ (hpos X hX))
  · exact Or.inr (hsupport.mono fun X hX => (hval _ (hpos X hX)).symm)

theorem quaternion_zero_or_profile_comparison {p : ℕ} [Fintype ι]
    (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) (hSigma : QuaternionMatrix.PosDef Sigma)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℍ[ℝ])
    (hB : ∀ i, QuaternionMatrix.FullColumnRank (B i))
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (ψ : ∀ i, QuaternionMatrix.Hermitian (k i) → ℝ)
    (hψ : ∀ i, (∀ S : QuaternionMatrix.Hermitian (k i), QuaternionMatrix.PosSemidef (S : Matrix (Fin (k i)) (Fin (k i)) ℍ[ℝ]) → ψ i S = 0) ∨
      ∃ h : (Fin (k i) → ℝ) → ℝ,
        ConvexOn ℝ univ h ∧ Monotone h ∧ Spectral.SymmetricProfile h ∧
        ∀ S : QuaternionMatrix.Hermitian (k i), QuaternionMatrix.PosSemidef (S : Matrix (Fin (k i)) (Fin (k i)) ℍ[ℝ]) →
          Spectral.spectralBoundaryValue h (QuaternionMatrix.orderedValues S) = ψ i S)
    (μ : Measure (QuaternionMatrix.Hermitian p)) (hμ : IsSectionSevenQuaternionLaw Sigma μ) :
    ExtendedSelectedProductComparison μ (fun i X => ψ i
      (QuaternionMatrix.normalizedCompression (B i) Sigma X + c i •
        (⟨1, Matrix.isHermitian_one⟩ : QuaternionMatrix.Hermitian (k i)))) := by
  have hex (i : ι) : ∃ h : (Fin (k i) → ℝ) → ℝ,
      ConvexOn ℝ univ h ∧ Monotone h ∧ Spectral.SymmetricProfile h ∧
      ((∀ S : QuaternionMatrix.Hermitian (k i), QuaternionMatrix.PosSemidef (S : Matrix (Fin (k i)) (Fin (k i)) ℍ[ℝ]) → ψ i S = 0) ∨
        ∀ S : QuaternionMatrix.Hermitian (k i), QuaternionMatrix.PosSemidef (S : Matrix (Fin (k i)) (Fin (k i)) ℍ[ℝ]) →
          Spectral.spectralBoundaryValue h (QuaternionMatrix.orderedValues S) = ψ i S) := by
    rcases hψ i with hz | ⟨h, hconv, hmono, hsym, heq⟩
    · exact ⟨fun _ => 0, convexOn_const 0 convex_univ, monotone_const, fun _ _ => rfl, Or.inl hz⟩
    · exact ⟨h, hconv, hmono, hsym, Or.inr heq⟩
  choose h hconv hmono hsym heq using hex
  let F : QuaternionSpectralFamily p ι := ⟨k, B, hB, c, hc, h, hconv, hmono, hsym⟩
  have hsupport : ∀ᵐ X : QuaternionMatrix.Hermitian p ∂μ, QuaternionMatrix.PosSemidef (X : Matrix (Fin p) (Fin p) ℍ[ℝ]) := by
    rcases hμ with ⟨α, hα, rfl⟩ | ⟨n, hn, rfl⟩
    · exact (QuaternionMatrix.wishart_ae_posDef α Sigma).mono fun X hX => hX.posSemidef
    · exact QuaternionMatrix.gramMeasure_ae_posSemidef n Sigma
  have hcompare : ExtendedSelectedProductComparison μ (F.factor Sigma) := by
    rcases hμ with ⟨α, hα, rfl⟩ | ⟨n, hn, rfl⟩
    · exact F.density_selected_product_comparison hα Sigma hSigma
    · exact F.gram_selected_product_comparison n Sigma hSigma
  apply hcompare.of_zero_or_aeEq
  intro i
  have hpos (X : QuaternionMatrix.Hermitian p) (hX : QuaternionMatrix.PosSemidef (X : Matrix (Fin p) (Fin p) ℍ[ℝ])) :
      QuaternionMatrix.PosSemidef (F.shiftedCompression Sigma i X : Matrix (Fin (k i)) (Fin (k i)) ℍ[ℝ]) :=
    (QuaternionMatrix.normalizedCompression_posSemidef (B i) Sigma X hX).add
      (QuaternionMatrix.posDef_one.posSemidef.smul (hc i))
  rcases heq i with hz | hval
  · exact Or.inl (hsupport.mono fun X hX => hz _ (hpos X hX))
  · exact Or.inr (hsupport.mono fun X hX => (hval _ (hpos X hX)).symm)

theorem complex_spectral_zero_or_profile_comparison {p : ℕ} [Fintype ι]
    (Sigma : Matrix (Fin p) (Fin p) ℂ) (hSigma : Sigma.PosDef)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℂ)
    (hB : ∀ i, Function.Injective (B i).mulVec)
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (ψ : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hψ : ∀ i, (∀ x, ψ i x = 0) ∨ ∃ h : (Fin (k i) → ℝ) → ℝ,
      ConvexOn ℝ univ h ∧ Monotone h ∧ Spectral.SymmetricProfile h ∧
      ∀ x, (∀ l, 0 ≤ x l) → Spectral.spectralBoundaryValue h x = ψ i x)
    (μ : Measure (ComplexMatrix.Hermitian p)) (hμ : IsSectionSevenComplexLaw Sigma μ) :
    ExtendedSelectedProductComparison μ (fun i X => ψ i (FieldSpectral.orderedValues
      (WishartVerification.hermitian_matrix_coe (ComplexMatrix.normalizedCompression (B i) Sigma X + c i •
        (⟨1, Matrix.isHermitian_one⟩ : ComplexMatrix.Hermitian (k i)))))) := by
  apply complex_zero_or_profile_comparison Sigma hSigma k B hB c hc
    (fun i S => ψ i (FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe S))) _ μ hμ
  intro i
  rcases hψ i with hz | ⟨h, hconv, hmono, hsym, heq⟩
  · exact Or.inl fun S _ => hz _
  · exact Or.inr ⟨h, hconv, hmono, hsym,
      fun S hS => heq _ (FieldSpectral.orderedValues_nonneg hS)⟩

theorem quaternion_spectral_zero_or_profile_comparison {p : ℕ} [Fintype ι]
    (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) (hSigma : QuaternionMatrix.PosDef Sigma)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℍ[ℝ])
    (hB : ∀ i, QuaternionMatrix.FullColumnRank (B i))
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (ψ : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hψ : ∀ i, (∀ x, ψ i x = 0) ∨ ∃ h : (Fin (k i) → ℝ) → ℝ,
      ConvexOn ℝ univ h ∧ Monotone h ∧ Spectral.SymmetricProfile h ∧
      ∀ x, (∀ l, 0 ≤ x l) → Spectral.spectralBoundaryValue h x = ψ i x)
    (μ : Measure (QuaternionMatrix.Hermitian p)) (hμ : IsSectionSevenQuaternionLaw Sigma μ) :
    ExtendedSelectedProductComparison μ (fun i X => ψ i (QuaternionMatrix.orderedValues
      (QuaternionMatrix.normalizedCompression (B i) Sigma X + c i •
        (⟨1, Matrix.isHermitian_one⟩ : QuaternionMatrix.Hermitian (k i))))) := by
  apply quaternion_zero_or_profile_comparison Sigma hSigma k B hB c hc
    (fun i S => ψ i (QuaternionMatrix.orderedValues S)) _ μ hμ
  intro i
  rcases hψ i with hz | ⟨h, hconv, hmono, hsym, heq⟩
  · exact Or.inl fun S _ => hz _
  · exact Or.inr ⟨h, hconv, hmono, hsym,
      fun S hS => heq _ (QuaternionMatrix.orderedValues_nonneg S hS)⟩

theorem complex_unitarilyInvariantNorm_power_comparison {p : ℕ} [Fintype ι]
    (Sigma : Matrix (Fin p) (Fin p) ℂ) (hSigma : Sigma.PosDef)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℂ)
    (hB : ∀ i, Function.Injective (B i).mulVec)
    (c a : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (ha : ∀ i, 0 ≤ a i)
    (N : ∀ i, Spectral.UnitarilyInvariantNorm ℂ (k i))
    (μ : Measure (ComplexMatrix.Hermitian p)) (hμ : IsSectionSevenComplexLaw Sigma μ) :
    ExtendedSelectedProductComparison μ (fun i X =>
      N i (CFC.sqrt ((ComplexMatrix.normalizedCompression (B i) Sigma X + c i •
        (⟨1, Matrix.isHermitian_one⟩ : ComplexMatrix.Hermitian (k i))) :
          Matrix (Fin (k i)) (Fin (k i)) ℂ)) ^ a i) := by
  apply complex_zero_or_profile_comparison Sigma hSigma k B hB c hc
    (fun i S => N i (CFC.sqrt (S : Matrix (Fin (k i)) (Fin (k i)) ℂ)) ^ a i) _ μ hμ
  intro i
  rcases Spectral.complexNormPower_zero_or_profile (N i) (ha i) with hz | hp
  · exact Or.inl fun S _ => hz S
  · exact Or.inr hp

theorem quaternion_unitarilyInvariantNorm_power_comparison {p : ℕ} [Fintype ι]
    (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) (hSigma : QuaternionMatrix.PosDef Sigma)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℍ[ℝ])
    (hB : ∀ i, QuaternionMatrix.FullColumnRank (B i))
    (c a : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (ha : ∀ i, 0 ≤ a i)
    (N : ∀ i, Spectral.UnitarilyInvariantNorm ℍ[ℝ] (k i))
    (μ : Measure (QuaternionMatrix.Hermitian p)) (hμ : IsSectionSevenQuaternionLaw Sigma μ) :
    ExtendedSelectedProductComparison μ (fun i X =>
      N i (QuaternionMatrix.sqrt ((QuaternionMatrix.normalizedCompression (B i) Sigma X + c i •
        (⟨1, Matrix.isHermitian_one⟩ : QuaternionMatrix.Hermitian (k i))) :
          Matrix (Fin (k i)) (Fin (k i)) ℍ[ℝ])) ^ a i) := by
  apply quaternion_zero_or_profile_comparison Sigma hSigma k B hB c hc
    (fun i S => N i (QuaternionMatrix.sqrt (S : Matrix (Fin (k i)) (Fin (k i)) ℍ[ℝ])) ^ a i) _ μ hμ
  intro i
  rcases Spectral.quaternionNormPower_zero_or_profile (N i) (ha i) with hz | hp
  · exact Or.inl fun S _ => hz S
  · exact Or.inr hp

end Wishart
end
end CanonicalSource79

