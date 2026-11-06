module

public import wishart.verified.field_residual01
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.Topology.Compactness.Compact
public import wishart.verified.shared_extended_limits01

/- Recovered canonical proof stage; see verification/recovery-patches.json. -/

@[expose] public section
set_option maxErrors 1000
set_option maxHeartbeats 1600000

set_option backward.isDefEq.respectTransparency false

section CanonicalSource10
/- Source: Wishart/SpectralBoundaryValues.lean -/



/-!
# The literal spectral boundary value

The definition below is proved to be the limit obtained by adding `ε` to all
eigenvalues and sending `ε` down to zero. On the face with positive-coordinate
set `J`, it equals the exponential face profile. The proof uses upper and
lower bounds with a fixed omitted-coordinate level; it therefore also covers
the faces whose logarithmic profile tends to minus infinity.
-/

noncomputable section
open Set Filter Topology
open scoped Classical BigOperators

namespace Wishart.Spectral

variable {k : ℕ}

def positiveCoordinateSet (x : Fin k → ℝ) : Finset (Fin k) :=
  Finset.univ.filter (fun i => 0 < x i)

theorem mem_positiveCoordinateSet (x : Fin k → ℝ) (i : Fin k) :
    i ∈ positiveCoordinateSet x ↔ 0 < x i := by simp only [positiveCoordinateSet,
      Finset.mem_filter, Finset.mem_univ, true_and]

theorem eq_zero_of_not_mem_positiveCoordinateSet {x : Fin k → ℝ}
    (hx : ∀ i, 0 ≤ x i) {i : Fin k} (hi : i ∉ positiveCoordinateSet x) : x i = 0 :=
  le_antisymm (le_of_not_gt (fun h => hi ((mem_positiveCoordinateSet x i).mpr h))) (hx i)

def spectralRegularization (h : (Fin k → ℝ) → ℝ) (x : Fin k → ℝ) (t : ℝ) : ℝ :=
  Real.exp (h (fun i => Real.log (x i + Real.exp t)))

def spectralBoundaryValue (h : (Fin k → ℝ) → ℝ) (x : Fin k → ℝ) : ℝ :=
  ⨅ t : ℝ, spectralRegularization h x t

theorem spectralBoundaryValue_nonneg (h : (Fin k → ℝ) → ℝ) (x : Fin k → ℝ) :
    0 ≤ spectralBoundaryValue h x := le_ciInf (fun t => (Real.exp_pos _).le)

theorem monotone_spectralRegularization {h : (Fin k → ℝ) → ℝ}
    (hm : Monotone h) {x : Fin k → ℝ} (hx : ∀ i, 0 ≤ x i) :
    Monotone (spectralRegularization h x) := by
  intro s t hst
  apply Real.exp_le_exp.mpr
  apply hm
  intro i
  apply Real.log_le_log (add_pos_of_nonneg_of_pos (hx i) (Real.exp_pos s))
  linarith [Real.exp_le_exp.mpr hst]

theorem spectralBoundaryValue_tendsto {h : (Fin k → ℝ) → ℝ}
    (hm : Monotone h) {x : Fin k → ℝ} (hx : ∀ i, 0 ≤ x i) :
    Tendsto (spectralRegularization h x) atBot (𝓝 (spectralBoundaryValue h x)) :=
  tendsto_atBot_ciInf (monotone_spectralRegularization hm hx)
    ⟨0, by rintro _ ⟨t, rfl⟩; exact (Real.exp_pos _).le⟩

/-- Equivalence to the regularized limit stated in the paper. -/
theorem spectralBoundaryValue_tendsto_epsilon {h : (Fin k → ℝ) → ℝ}
    (hm : Monotone h) {x : Fin k → ℝ} (hx : ∀ i, 0 ≤ x i) :
    Tendsto (fun ε : ℝ => Real.exp (h (fun i => Real.log (x i + ε))))
      (𝓝[>] 0) (𝓝 (spectralBoundaryValue h x)) := by
  have ht := (spectralBoundaryValue_tendsto hm hx).comp Real.tendsto_log_nhdsGT_zero
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  simp only [Function.comp_apply, spectralRegularization, Real.exp_log hε]

theorem spectralBoundaryValue_eq_on_positive {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ univ h) (hm : Monotone h) {x : Fin k → ℝ}
    (hx : ∀ i, 0 < x i) :
    spectralBoundaryValue h x = Real.exp (h (fun i => Real.log (x i))) := by
  have hcont : Continuous h := by
    simpa only [interior_univ, continuousOn_univ] using hc.continuousOn_interior
  have harg : Tendsto (fun ε : ℝ => fun i => Real.log (x i + ε)) (𝓝[>] 0)
      (𝓝 (fun i => Real.log (x i))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply (Real.continuousAt_log (hx i).ne').tendsto.comp
    simpa only [add_zero] using
      (tendsto_const_nhds.add (show Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) from
        nhdsWithin_le_nhds))
  exact tendsto_nhds_unique (spectralBoundaryValue_tendsto_epsilon hm (fun i => (hx i).le))
    (Real.continuous_exp.continuousAt.tendsto.comp (hcont.continuousAt.tendsto.comp harg))

theorem spectralBoundaryValue_eq_faceExponential {h : (Fin k → ℝ) → ℝ}
    (hc : ConvexOn ℝ univ h) (hm : Monotone h) {x : Fin k → ℝ}
    (hx : ∀ i, 0 ≤ x i) :
    spectralBoundaryValue h x = faceExponential h (positiveCoordinateSet x)
      (fun i => Real.log (x i)) := by
  let J := positiveCoordinateSet x
  let lx : J → ℝ := fun i => Real.log (x i)
  have hcont : Continuous h := by
    simpa only [interior_univ, continuousOn_univ] using hc.continuousOn_interior
  have hxb (i : J) : 0 < x i := (mem_positiveCoordinateSet x i).mp i.property
  apply le_antisymm
  · apply le_ciInf
    intro s
    let upper (t : ℝ) : ℝ := Real.exp (h (faceFill J
      (fun i => Real.log (x i + Real.exp t)) s))
    have hu : Tendsto upper atBot (𝓝 (Real.exp (h (faceFill J lx s)))) := by
      apply Real.continuous_exp.continuousAt.tendsto.comp
      apply hcont.continuousAt.tendsto.comp
      apply tendsto_pi_nhds.mpr
      intro i
      by_cases hi : i ∈ J
      · simp only [faceFill, dif_pos hi, lx]
        apply (Real.continuousAt_log (hxb ⟨i, hi⟩).ne').tendsto.comp
        simpa only [add_zero] using tendsto_const_nhds.add Real.tendsto_exp_atBot
      · simp only [faceFill, dif_neg hi]
        exact tendsto_const_nhds
    apply le_of_tendsto_of_tendsto (spectralBoundaryValue_tendsto hm hx) hu
    filter_upwards [eventually_le_atBot s] with t ht
    apply Real.exp_le_exp.mpr
    apply hm
    intro i
    by_cases hi : i ∈ J
    · simp only [faceFill, dif_pos hi, le_refl]
    · have hzero := eq_zero_of_not_mem_positiveCoordinateSet hx hi
      simpa only [faceFill, dif_neg hi, hzero, zero_add, Real.log_exp] using ht
  · apply le_ciInf
    intro t
    have hlow : faceExponential h J lx ≤ Real.exp (h (faceFill J lx t)) :=
      ciInf_le ⟨0, by rintro _ ⟨s, rfl⟩; exact (Real.exp_pos _).le⟩ t
    apply hlow.trans
    apply Real.exp_le_exp.mpr
    apply hm
    intro i
    by_cases hi : i ∈ J
    · simp only [faceFill, dif_pos hi, lx]
      exact Real.log_le_log (hxb ⟨i, hi⟩) (le_add_of_nonneg_right (Real.exp_pos t).le)
    · have hzero := eq_zero_of_not_mem_positiveCoordinateSet hx hi
      simp only [faceFill, dif_neg hi, hzero, zero_add, Real.log_exp, le_refl]

theorem spectralBoundaryValue_monotone {h : (Fin k → ℝ) → ℝ}
    (hm : Monotone h) {x y : Fin k → ℝ}
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) (hxy : x ≤ y) :
    spectralBoundaryValue h x ≤ spectralBoundaryValue h y := by
  apply le_of_tendsto_of_tendsto (spectralBoundaryValue_tendsto hm hx)
    (spectralBoundaryValue_tendsto hm hy)
  apply Filter.Eventually.of_forall
  intro t
  apply Real.exp_le_exp.mpr
  apply hm
  intro i
  exact Real.log_le_log (add_pos_of_nonneg_of_pos (hx i) (Real.exp_pos t))
    (by linarith [hxy i])

theorem spectralBoundaryValue_symmetric {h : (Fin k → ℝ) → ℝ}
    (hsym : SymmetricProfile h) (σ : Equiv.Perm (Fin k)) (x : Fin k → ℝ) :
    spectralBoundaryValue h (x ∘ σ) = spectralBoundaryValue h x := by
  apply congrArg iInf
  funext t
  unfold spectralRegularization
  congr 1
  exact hsym σ (fun i => Real.log (x i + Real.exp t))

end Wishart.Spectral
end
end CanonicalSource10

section CanonicalSource11
/- Source: Wishart/FieldTheoremStatement.lean -/




/-!
# Exact targets for Theorem 7.1

These definitions specify the outstanding theorem, not an assumed interface.
The law is either the literal real-shape density or an actual integer Gaussian
Gram image. The matrix factors use the actual ordered eigenvalues and the
regularized boundary value. No stochastic-order, regression, integrability,
subharmonicity, rank-threshold, or comparison premise is inserted.
-/

noncomputable section
open Matrix MeasureTheory Set
open scoped Classical Quaternion ComplexOrder BigOperators ENNReal
namespace Wishart

/-- Both inequalities in the selected-factor chain, with extended expectations.
Using nonnegative extended multiplication also fixes the paper's zero-factor
convention: `0 * ∞ = 0`. -/
def ExtendedSelectedProductComparison {E ι : Type*} [MeasurableSpace E]
    [DecidableEq ι] (μ : Measure E) (f : ι → E → ℝ) : Prop :=
  ∀ (J : Finset ι) (j : ι), j ∈ J →
    (∫⁻ X, ENNReal.ofReal (f j X) ∂μ) *
      (∫⁻ X, ENNReal.ofReal (∏ i ∈ J.erase j, f i X) ∂μ) ≤
        ∫⁻ X, ENNReal.ofReal (∏ i ∈ J, f i X) ∂μ ∧
    (∏ i ∈ J, ∫⁻ X, ENNReal.ofReal (f i X) ∂μ) ≤
      (∫⁻ X, ENNReal.ofReal (f j X) ∂μ) *
        (∫⁻ X, ENNReal.ofReal (∏ i ∈ J.erase j, f i X) ∂μ)

structure ComplexSpectralFamily (p : ℕ) (ι : Type*) where
  size : ι → ℕ
  matrix : ∀ i, Matrix (Fin p) (Fin (size i)) ℂ
  full_rank : ∀ i, Function.Injective (matrix i).mulVec
  shift : ι → ℝ
  shift_nonneg : ∀ i, 0 ≤ shift i
  profile : ∀ i, (Fin (size i) → ℝ) → ℝ
  convex : ∀ i, ConvexOn ℝ univ (profile i)
  increasing : ∀ i, Monotone (profile i)
  symmetric : ∀ i, Spectral.SymmetricProfile (profile i)

structure QuaternionSpectralFamily (p : ℕ) (ι : Type*) where
  size : ι → ℕ
  matrix : ∀ i, Matrix (Fin p) (Fin (size i)) ℍ[ℝ]
  full_rank : ∀ i, QuaternionMatrix.FullColumnRank (matrix i)
  shift : ι → ℝ
  shift_nonneg : ∀ i, 0 ≤ shift i
  profile : ∀ i, (Fin (size i) → ℝ) → ℝ
  convex : ∀ i, ConvexOn ℝ univ (profile i)
  increasing : ∀ i, Monotone (profile i)
  symmetric : ∀ i, Spectral.SymmetricProfile (profile i)

namespace ComplexSpectralFamily
variable {p : ℕ} {ι : Type*} (F : ComplexSpectralFamily p ι)

def shiftedCompression (Sigma : Matrix (Fin p) (Fin p) ℂ) (i : ι)
    (X : ComplexMatrix.Hermitian p) : ComplexMatrix.Hermitian (F.size i) :=
  ComplexMatrix.normalizedCompression (F.matrix i) Sigma X + F.shift i •
    (⟨1, Matrix.isHermitian_one⟩ : ComplexMatrix.Hermitian (F.size i))

def factor (Sigma : Matrix (Fin p) (Fin p) ℂ) (i : ι)
    (X : ComplexMatrix.Hermitian p) : ℝ :=
  Spectral.spectralBoundaryValue (F.profile i)
    (FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe (F.shiftedCompression Sigma i X)))

theorem factor_nonneg (Sigma : Matrix (Fin p) (Fin p) ℂ) (i : ι)
    (X : ComplexMatrix.Hermitian p) : 0 ≤ F.factor Sigma i X :=
  Spectral.spectralBoundaryValue_nonneg _ _

/-- The boundary value is exactly the right-hand regularization of the
actual eigenvalue list; its equivalence to matrix regularization additionally
uses translation of Hermitian eigenvalues by a scalar identity. -/
theorem factor_eigenvalue_boundary (Sigma : Matrix (Fin p) (Fin p) ℂ) (i : ι)
    (X : ComplexMatrix.Hermitian p)
    (hS : (F.shiftedCompression Sigma i X : Matrix (Fin (F.size i)) (Fin (F.size i)) ℂ).PosSemidef) :
    Filter.Tendsto (fun ε : ℝ => Real.exp (F.profile i (fun a =>
      Real.log (FieldSpectral.orderedValues
        (WishartVerification.hermitian_matrix_coe (F.shiftedCompression Sigma i X)) a + ε))))
      (nhdsWithin 0 (Ioi 0)) (nhds (F.factor Sigma i X)) :=
  Spectral.spectralBoundaryValue_tendsto_epsilon (F.increasing i)
    (fun a => by
      rw [FieldSpectral.orderedValues_eq]
      exact hS.eigenvalues_nonneg _)

end ComplexSpectralFamily

namespace QuaternionSpectralFamily
variable {p : ℕ} {ι : Type*} (F : QuaternionSpectralFamily p ι)

def shiftedCompression (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) (i : ι)
    (X : QuaternionMatrix.Hermitian p) : QuaternionMatrix.Hermitian (F.size i) :=
  QuaternionMatrix.normalizedCompression (F.matrix i) Sigma X + F.shift i •
    (⟨1, Matrix.isHermitian_one⟩ : QuaternionMatrix.Hermitian (F.size i))

def factor (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) (i : ι)
    (X : QuaternionMatrix.Hermitian p) : ℝ :=
  Spectral.spectralBoundaryValue (F.profile i)
    (QuaternionMatrix.orderedValues (F.shiftedCompression Sigma i X))

theorem factor_nonneg (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) (i : ι)
    (X : QuaternionMatrix.Hermitian p) : 0 ≤ F.factor Sigma i X :=
  Spectral.spectralBoundaryValue_nonneg _ _

theorem factor_eigenvalue_boundary (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) (i : ι)
    (X : QuaternionMatrix.Hermitian p)
    (hS : QuaternionMatrix.PosSemidef (F.shiftedCompression Sigma i X).val) :
    Filter.Tendsto (fun ε : ℝ => Real.exp (F.profile i (fun a =>
      Real.log (QuaternionMatrix.orderedValues (F.shiftedCompression Sigma i X) a + ε))))
      (nhdsWithin 0 (Ioi 0)) (nhds (F.factor Sigma i X)) :=
  Spectral.spectralBoundaryValue_tendsto_epsilon (F.increasing i)
    (QuaternionMatrix.orderedValues_nonneg _ hS)

end QuaternionSpectralFamily

/-- The two allowed actual complex laws; the real-shape normalization must
still be established, rather than built into this predicate as an assumption. -/
def IsSectionSevenComplexLaw {p : ℕ} (Sigma : Matrix (Fin p) (Fin p) ℂ)
    (μ : Measure (ComplexMatrix.Hermitian p)) : Prop :=
  (∃ α : ℝ, (p : ℝ) - 1 < α ∧ μ = ComplexMatrix.wishartMeasure α Sigma) ∨
  (∃ n : ℕ, 1 ≤ n ∧ μ = ComplexMatrix.gramMeasure n Sigma)

def IsSectionSevenQuaternionLaw {p : ℕ} (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ])
    (μ : Measure (QuaternionMatrix.Hermitian p)) : Prop :=
  (∃ α : ℝ, (p : ℝ) - 1 < α ∧ μ = QuaternionMatrix.wishartMeasure α Sigma) ∨
  (∃ n : ℕ, 1 ≤ n ∧ μ = QuaternionMatrix.gramMeasure n Sigma)

/-- This is a required conclusion in the final Section 7 package. It prevents
the normalization convention `∞⁻¹ = 0` from making a malformed density law
produce a vacuous zero-measure comparison. -/
def SectionSevenComplexNormalization : Prop :=
  ∀ (p : ℕ) (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℂ),
    (p : ℝ) - 1 < α → Sigma.PosDef →
    0 < ComplexMatrix.wishartNormalizer α Sigma ∧
      ComplexMatrix.wishartNormalizer α Sigma < ⊤ ∧
      IsProbabilityMeasure (ComplexMatrix.wishartMeasure α Sigma)

def SectionSevenQuaternionNormalization : Prop :=
  ∀ (p : ℕ) (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]),
    (p : ℝ) - 1 < α → QuaternionMatrix.PosDef Sigma →
    0 < QuaternionMatrix.wishartNormalizer α Sigma ∧
      QuaternionMatrix.wishartNormalizer α Sigma < ⊤ ∧
      IsProbabilityMeasure (QuaternionMatrix.wishartMeasure α Sigma)

/-- Full complex principal target: all admissible real shapes and all positive
integer sample sizes, all finite families and all full-column-rank overlaps. -/
def TheoremSevenOneComplex : Prop :=
  ∀ (p : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (Sigma : Matrix (Fin p) (Fin p) ℂ), Sigma.PosDef →
    ∀ (F : ComplexSpectralFamily p ι) (μ : Measure (ComplexMatrix.Hermitian p)),
      IsSectionSevenComplexLaw Sigma μ → ExtendedSelectedProductComparison μ (F.factor Sigma)

def TheoremSevenOneQuaternion : Prop :=
  ∀ (p : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]), QuaternionMatrix.PosDef Sigma →
    ∀ (F : QuaternionSpectralFamily p ι) (μ : Measure (QuaternionMatrix.Hermitian p)),
      IsSectionSevenQuaternionLaw Sigma μ → ExtendedSelectedProductComparison μ (F.factor Sigma)

/-- The finite determinant-power assertion is a separate part of 7.1; it is
not silently inferred from the extended comparison. -/
def TheoremSevenOneComplexFinitePowers : Prop :=
  ∀ (p : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (Sigma : Matrix (Fin p) (Fin p) ℂ), Sigma.PosDef →
    ∀ (k : ι → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℂ),
      (∀ i, Function.Injective (B i).mulVec) →
      ∀ (c ν : ι → ℝ), (∀ i, 0 ≤ c i) → (∀ i, 0 ≤ ν i) →
      ∀ μ : Measure (ComplexMatrix.Hermitian p), IsSectionSevenComplexLaw Sigma μ →
      (∫⁻ X, ENNReal.ofReal (∏ i, ComplexMatrix.realDeterminant
        ((B i)ᴴ * (X : Matrix (Fin p) (Fin p) ℂ) * B i +
          c i • ComplexMatrix.compressionCovariance (B i) Sigma) ^ ν i) ∂μ) < ⊤

def TheoremSevenOneQuaternionFinitePowers : Prop :=
  ∀ (p : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]), QuaternionMatrix.PosDef Sigma →
    ∀ (k : ι → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℍ[ℝ]),
      (∀ i, QuaternionMatrix.FullColumnRank (B i)) →
      ∀ (c ν : ι → ℝ), (∀ i, 0 ≤ c i) → (∀ i, 0 ≤ ν i) →
      ∀ μ : Measure (QuaternionMatrix.Hermitian p), IsSectionSevenQuaternionLaw Sigma μ →
      (∫⁻ X, ENNReal.ofReal (∏ i, QuaternionMatrix.positiveDeterminant
        ((B i)ᴴ * (X : Matrix (Fin p) (Fin p) ℍ[ℝ]) * B i +
          c i • QuaternionMatrix.compressionCovariance (B i) Sigma) ^ ν i) ∂μ) < ⊤

/-- The required combined Section 7 target, including law nonvacuity and
finite moments. Defining this proposition does not assert it. -/
def TheoremSevenOne : Prop :=
  SectionSevenComplexNormalization ∧ SectionSevenQuaternionNormalization ∧
  TheoremSevenOneComplex ∧ TheoremSevenOneQuaternion ∧
  TheoremSevenOneComplexFinitePowers ∧ TheoremSevenOneQuaternionFinitePowers

end Wishart
end
end CanonicalSource11

section CanonicalSource12
/- Source: Wishart/FieldNormalizationTheorems.lean -/



/-!
# The nonvacuity part of the Section 7 target

These conclusions use the literal Lebesgue densities at every admissible real
shape and positive covariance. They establish probability and positive-cone
support. The selected-product comparisons remain separate principal goals.
-/

noncomputable section
open MeasureTheory
open scoped Classical Quaternion ComplexOrder ENNReal
namespace Wishart
open WishartVerification.FieldDensity

theorem theorem_7_1_complex_normalization : SectionSevenComplexNormalization := by
  intro p α Sigma hα hSigma
  have h := (ComplexMatrix.finiteDensity_wishart_and_covariance_law hα hSigma).1
  exact ⟨h.positive, h.finite, ComplexMatrix.wishart_probability hα hSigma⟩

theorem theorem_7_1_quaternion_normalization : SectionSevenQuaternionNormalization := by
  intro p α Sigma hα hSigma
  have h := (QuaternionMatrix.finiteDensity_wishart_and_covariance_law hα hSigma).1
  exact ⟨h.positive, h.finite, QuaternionMatrix.wishart_probability hα hSigma⟩

theorem ComplexMatrix.wishart_ae_posDef {p : ℕ} (α : ℝ)
    (Sigma : Matrix (Fin p) (Fin p) ℂ) :
    ∀ᵐ (X : ComplexMatrix.Hermitian p) ∂ComplexMatrix.wishartMeasure α Sigma,
      (X : Matrix (Fin p) (Fin p) ℂ).PosDef := by
  apply ae_normalized_of_weight_ne_zero (ComplexMatrix.measurable_wishartWeight α Sigma)
  intro X hX
  by_contra h
  exact hX (by rw [ComplexMatrix.wishartWeight, if_neg h])

theorem QuaternionMatrix.wishart_ae_posDef {p : ℕ} (α : ℝ)
    (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) :
    ∀ᵐ (X : QuaternionMatrix.Hermitian p) ∂QuaternionMatrix.wishartMeasure α Sigma,
      QuaternionMatrix.PosDef (X : Matrix (Fin p) (Fin p) ℍ[ℝ]) := by
  apply ae_normalized_of_weight_ne_zero (QuaternionMatrix.measurable_wishartWeight α Sigma)
  intro X hX
  by_contra h
  exact hX (by rw [QuaternionMatrix.wishartWeight, if_neg h])

end Wishart
end
end CanonicalSource12

section CanonicalSource13
/- Source: Wishart/FieldOrderedSpectra.lean -/




/-!
# Actual ascending complex and quaternion spectral selectors

The probability chart uses increasing eigenvalues. The manuscript's leading
eigenvalue products use decreasing eigenvalues. Both are connected by the
literal fixed reversal permutation, including multiplicities.
-/

noncomputable section
open Matrix MeasureTheory
open scoped Classical Quaternion ComplexOrder Matrix.Norms.L2Operator ENNReal

namespace Wishart.FieldCharts

variable (F : Type*) [Ring F] [Algebra ℝ F] [StarRing F] [StarModule ℝ F]

def permutationUnitary {p : ℕ} (e : Equiv.Perm (Fin p)) : unitary (Matrix (Fin p) (Fin p) F) :=
  ⟨e.permMatrix F, by
    change (e.permMatrix F)ᴴ * e.permMatrix F = 1 ∧
      e.permMatrix F * (e.permMatrix F)ᴴ = 1
    constructor <;> simp only [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul,
      inv_mul_cancel, mul_inv_cancel, Matrix.permMatrix_one]⟩

theorem permutation_conjugate_diagonal {p : ℕ} (e : Equiv.Perm (Fin p))
    (lam : Fin p → ℝ) :
    unitaryConjugate F (permutationUnitary F e) (diagonalHermitian F lam) =
      diagonalHermitian F (lam ∘ e) := by
  apply Subtype.ext
  change e.permMatrix F * Matrix.diagonal (fun i => algebraMap ℝ F (lam i)) *
    (e.permMatrix F)ᴴ = _
  rw [Matrix.conjTranspose_permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  simp [diagonalHermitian, realDiagonal, Matrix.submatrix_apply,
    Matrix.diagonal_apply, Equiv.Perm.inv_def, e.injective.eq_iff]

end Wishart.FieldCharts

namespace Wishart.ComplexMatrix
open Wishart.FieldCharts

def ascendingValues {p : ℕ} (X : Hermitian p) : Fin p → ℝ :=
  Wishart.FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe X) ∘ Fin.rev

theorem ascendingValues_reversal {p : ℕ} (X : Hermitian p) :
    ascendingValues X ∘ Fin.rev = Wishart.FieldSpectral.orderedValues
      (WishartVerification.hermitian_matrix_coe X) := by
  funext i
  simp only [ascendingValues, Function.comp_apply, Fin.rev_rev]

theorem ascendingValues_monotone {p : ℕ} (X : Hermitian p) : Monotone (ascendingValues X) :=
  fun _ _ h => Wishart.FieldSpectral.antitone_orderedValues (WishartVerification.hermitian_matrix_coe X) (Fin.rev_anti h)

theorem continuous_ascendingValues (p : ℕ) : Continuous (@ascendingValues p) := by
  apply continuous_pi
  intro i
  exact (continuous_apply (Fin.rev i)).comp (Wishart.FieldSpectral.continuous_orderedValues p)

theorem ascendingValues_conjugate {p : ℕ} (U : unitary (Matrix (Fin p) (Fin p) ℂ))
    (X : Hermitian p) : ascendingValues (unitaryConjugate ℂ U X) = ascendingValues X := by
  have hc : (unitaryConjugate ℂ U X : Matrix (Fin p) (Fin p) ℂ).charpoly =
      (X : Matrix (Fin p) (Fin p) ℂ).charpoly := by
    change ((U : Matrix (Fin p) (Fin p) ℂ) * X * star U).charpoly = _
    rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
      Unitary.coe_star, Unitary.coe_star_mul_self, Matrix.one_mul]
  have hs := ((WishartVerification.hermitian_matrix_coe (unitaryConjugate ℂ U X)).eigenvalues_eq_eigenvalues_iff
    (WishartVerification.hermitian_matrix_coe X)).mpr hc
  funext i
  simp only [ascendingValues, Function.comp_apply, Wishart.FieldSpectral.orderedValues_eq, hs]

theorem ascendingValues_diagonal {p : ℕ} (lam : Fin p → ℝ) (hlam : Monotone lam) :
    ascendingValues (diagonalHermitian ℂ lam) = lam := by
  let P := permutationUnitary ℂ (Fin.revPerm : Equiv.Perm (Fin p))
  have hrev : Antitone (lam ∘ Fin.rev) := fun _ _ h => hlam (Fin.rev_anti h)
  have hs : Wishart.FieldSpectral.orderedValues
      (WishartVerification.hermitian_matrix_coe (diagonalHermitian ℂ (lam ∘ Fin.rev))) = lam ∘ Fin.rev :=
    Wishart.FieldSpectral.orderedValues_diagonal _ hrev
  have hperm := ascendingValues_conjugate P (diagonalHermitian ℂ lam)
  rw [permutation_conjugate_diagonal] at hperm
  rw [← hperm]
  funext i
  simp only [ascendingValues, hs, Function.comp_apply, Fin.revPerm_apply, Fin.rev_rev]

theorem exists_conjugate_ascending {p : ℕ} (X : Hermitian p) :
    ∃ U : unitary (Matrix (Fin p) (Fin p) ℂ),
      unitaryConjugate ℂ U (diagonalHermitian ℂ (ascendingValues X)) = X := by
  obtain ⟨O,hO⟩ := Wishart.FieldSpectral.exists_sorted_diagonalization
    (WishartVerification.hermitian_matrix_coe X)
  let P := permutationUnitary ℂ (Fin.revPerm : Equiv.Perm (Fin p))
  refine ⟨O * star P, ?_⟩
  have hrec : unitaryConjugate ℂ O (diagonalHermitian ℂ
      (Wishart.FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe X))) = X := by
    apply Subtype.ext
    change (O : Matrix (Fin p) (Fin p) ℂ) * _ * star O = _
    change (O : Matrix (Fin p) (Fin p) ℂ) * Matrix.diagonal (fun i => (Wishart.FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe X) i : ℂ)) * star (O : Matrix (Fin p) (Fin p) ℂ) = X.val
    have hO2 : star O.val * X.val * O.val = Matrix.diagonal (fun i => (Wishart.FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe X) i : ℂ)) := by
      convert hO using 1 <;> rfl
    rw [← hO2]
    simp only [← Matrix.mul_assoc, O.property.2, Matrix.one_mul]
    rw [Matrix.mul_assoc, O.property.2, Matrix.mul_one]
  change unitaryConjugate ℂ (O * star P) (diagonalHermitian ℂ (Wishart.FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe X) ∘ (Fin.revPerm : Equiv.Perm (Fin p)))) = X
  rw [← permutation_conjugate_diagonal ℂ Fin.revPerm,
    ← unitaryConjugate_mul]
  simpa only [P, mul_assoc, Unitary.star_mul_self, mul_one] using hrec

theorem wishartWeight_unitary {p : ℕ} (α : ℝ)
    (U : unitary (Matrix (Fin p) (Fin p) ℂ)) (X : Hermitian p) :
    wishartWeight α 1 (unitaryConjugate ℂ U X) = wishartWeight α 1 X := by
  have h := wishartWeight_congruence_standard α
    ((star U).val : Matrix (Fin p) (Fin p) ℂ) (Unitary.isUnit_coe (U := star U)) X
  have hu : U.val * U.valᴴ = 1 := U.property.2
  simpa only [Wishart.FieldHermitian.congruence, unitaryConjugate,
    Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose, hu,
    Unitary.coe_mul_star_self, realDeterminant, Matrix.det_one,
    Complex.one_re, Real.one_rpow, ENNReal.ofReal_one, one_mul] using h

theorem map_unitaryConjugate_wishart {p : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α) (U : unitary (Matrix (Fin p) (Fin p) ℂ)) :
    (wishartMeasure α (1 : Matrix (Fin p) (Fin p) ℂ)).map (unitaryConjugate ℂ U) =
      wishartMeasure α (1 : Matrix (Fin p) (Fin p) ℂ) := by
  have h := WishartVerification.FieldDensity.normalized_transport_haar
    (conjugationLinearEquiv ℂ U).toContinuousLinearEquiv (hermitianLebesgue p)
    (hermitianLebesgue p) (wishartWeight α 1) (wishartWeight α 1)
    (finiteDensity_wishart_standard p hα) (wishartWeight_unitary α U)
  exact h.2.symm

end Wishart.ComplexMatrix

namespace Wishart.QuaternionMatrix
open scoped Matrix.Norms.Frobenius
open Wishart.FieldCharts

theorem ascendingValues_reversal {p : ℕ} (X : Hermitian p) :
    ascendingValues X ∘ Fin.rev = orderedValues X := by
  funext i
  simp only [ascendingValues, Function.comp_apply, Fin.rev_rev]

theorem orderedValues_diagonal {p : ℕ} (lam : Fin p → ℝ) (hlam : Antitone lam) :
    orderedValues (Wishart.FieldCharts.diagonalHermitian ℍ[ℝ] lam) = lam := by
  have hflat : flatHermitian (Wishart.FieldCharts.diagonalHermitian ℍ[ℝ] lam) =
      Wishart.FieldCharts.diagonalHermitian ℂ (doubleValues lam) := by
    apply Subtype.ext
    exact flatRepresentation_diagonal lam
  have he := congrArg (fun A : Wishart.FieldSpectral.Hermitian ℂ (p*2) =>
    Wishart.FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe A)) hflat
  have hd := Wishart.FieldSpectral.orderedValues_diagonal (𝕜 := ℂ) (doubleValues lam) (doubleValues_antitone hlam)
  funext i
  change Wishart.FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe
    (flatHermitian (Wishart.FieldCharts.diagonalHermitian ℍ[ℝ] lam))) (doubledIndex i) = lam i
  rw [he]
  convert congrFun hd (doubledIndex i) using 1 <;>
    simp [doubleValues, doubledIndex]

theorem ascendingValues_conjugate {p : ℕ}
    (U : unitary (Matrix (Fin p) (Fin p) ℍ[ℝ])) (X : Hermitian p) :
    ascendingValues (unitaryConjugate ℍ[ℝ] U X) = ascendingValues X := by
  change orderedValues (conjugate U X) ∘ Fin.rev = orderedValues X ∘ Fin.rev
  rw [orderedValues_conjugate]

theorem ascendingValues_diagonal {p : ℕ} (lam : Fin p → ℝ) (hlam : Monotone lam) :
    ascendingValues (Wishart.FieldCharts.diagonalHermitian ℍ[ℝ] lam) = lam := by
  let P := Wishart.FieldCharts.permutationUnitary ℍ[ℝ] (Fin.revPerm : Equiv.Perm (Fin p))
  have hrev : Antitone (lam ∘ Fin.rev) := fun _ _ h => hlam (Fin.rev_anti h)
  have hs := orderedValues_diagonal (lam ∘ Fin.rev) hrev
  have hperm := ascendingValues_conjugate P
    (Wishart.FieldCharts.diagonalHermitian ℍ[ℝ] lam)
  rw [permutation_conjugate_diagonal] at hperm
  rw [← hperm]
  funext i
  change orderedValues (Wishart.FieldCharts.diagonalHermitian ℍ[ℝ] (lam ∘ Fin.rev)) (Fin.rev i) = lam i
  rw [hs]
  simp

theorem exists_conjugate_ascending {p : ℕ} (X : Hermitian p) :
    ∃ U : unitary (Matrix (Fin p) (Fin p) ℍ[ℝ]),
      unitaryConjugate ℍ[ℝ] U
        (Wishart.FieldCharts.diagonalHermitian ℍ[ℝ] (ascendingValues X)) = X := by
  obtain ⟨O,hO⟩ := exists_conjugate_diagonal X
  let P := Wishart.FieldCharts.permutationUnitary ℍ[ℝ] (Fin.revPerm : Equiv.Perm (Fin p))
  refine ⟨O * star P, ?_⟩
  change unitaryConjugate ℍ[ℝ] (O * star P) (Wishart.FieldCharts.diagonalHermitian ℍ[ℝ] (orderedValues X ∘ (Fin.revPerm : Equiv.Perm (Fin p)))) = X
  rw [← permutation_conjugate_diagonal ℍ[ℝ] Fin.revPerm,
    ← unitaryConjugate_mul]
  have hO' : unitaryConjugate ℍ[ℝ] O
      (Wishart.FieldCharts.diagonalHermitian ℍ[ℝ] (orderedValues X)) = X := by
    convert hO using 1 <;> apply Subtype.ext <;> rfl
  simpa only [P, mul_assoc, Unitary.star_mul_self, mul_one] using hO' 

theorem wishartWeight_unitary {p : ℕ} (α : ℝ)
    (U : unitary (Matrix (Fin p) (Fin p) ℍ[ℝ])) (X : Hermitian p) :
    wishartWeight α 1 (unitaryConjugate ℍ[ℝ] U X) = wishartWeight α 1 X := by
  have h := wishartWeight_congruence_standard α
    ((star U).val : Matrix (Fin p) (Fin p) ℍ[ℝ]) (Unitary.isUnit_coe (U := star U)) X
  have hu : U.val * U.valᴴ = 1 := U.property.2
  simpa only [Wishart.FieldHermitian.congruence, unitaryConjugate,
    Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose, hu,
    Unitary.coe_mul_star_self, positiveDeterminant, complexRepresentation_one,
    Matrix.det_one, Complex.one_re, Real.sqrt_one, Real.one_rpow,
    ENNReal.ofReal_one, one_mul] using h

theorem map_unitaryConjugate_wishart {p : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α) (U : unitary (Matrix (Fin p) (Fin p) ℍ[ℝ])) :
    (wishartMeasure α (1 : Matrix (Fin p) (Fin p) ℍ[ℝ])).map (unitaryConjugate ℍ[ℝ] U) =
      wishartMeasure α (1 : Matrix (Fin p) (Fin p) ℍ[ℝ]) := by
  have h := WishartVerification.FieldDensity.normalized_transport_haar
    (Wishart.FieldCharts.conjugationLinearEquiv ℍ[ℝ] U).toContinuousLinearEquiv
    (hermitianLebesgue p) (hermitianLebesgue p) (wishartWeight α 1) (wishartWeight α 1)
    (finiteDensity_wishart_standard p hα) (wishartWeight_unitary α U)
  exact h.2.symm

end Wishart.QuaternionMatrix
end
end CanonicalSource13

section CanonicalSource14
/- Source: Wishart/FieldSimpleSpectrum.lean -/



/-!
# Repeated spectra are null in the actual field Hermitian space

A finite translate cover of the unitary group supplies finitely many local
Cayley windows. Their repeated-spectrum parameter sets have zero real
Jacobian, so the equal-dimensional critical-image theorem proves nullity.
No discriminant or quaternion characteristic polynomial is assumed.
-/

noncomputable section
open MeasureTheory.Measure
open Matrix MeasureTheory Set
open scoped Classical Topology Matrix.Norms.Operator ENNReal

namespace Wishart.FieldCharts

variable (F : Type*) [NormedRing F] [NormedAlgebra ℝ F] [StarRing F]
  [StarModule ℝ F] [FiniteDimensional ℝ F] [ContinuousStar F] [MeasurableSpace F] [BorelSpace F] [Nontrivial F]

theorem gapProduct_eq_zero_of_not_injective {p : ℕ} {lam : Fin p → ℝ}
    (hlam : ¬ Function.Injective lam) :
    (∏ ij : PairIndex p, (lam ij.1.2 - lam ij.1.1)) = 0 := by
  obtain ⟨i,j,hij,hne⟩ := Function.not_injective_iff.mp hlam
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact Finset.prod_eq_zero (Finset.mem_univ ⟨(i,j),hlt⟩) (sub_eq_zero.mpr hij.symm)
  · exact Finset.prod_eq_zero (Finset.mem_univ ⟨(j,i),hgt⟩) (sub_eq_zero.mpr hij)

theorem chartDerivative_det_zero_of_repeated (R : RealPartData F) {p : ℕ}
    [CompactSpace (unitary (Matrix (Fin p) (Fin p) F))] (x : Coordinates F p)
    (hx : x.2 ∈ cayleyDomain F p) (hrepeated : ¬Function.Injective x.1) :
    (chartDerivative F R x.2 hx x.1).det = 0 := by
  apply abs_eq_zero.mp
  rw [abs_det_chartDerivative, gapProduct_eq_zero_of_not_injective hrepeated,
    abs_zero, zero_pow (Module.finrank_pos (R := ℝ) (M := F)).ne', mul_zero]

theorem ProductWindow.exists_finite_frame_cover (R : RealPartData F) {p : ℕ}
    [CompactSpace (unitary (Matrix (Fin p) (Fin p) F))] (W : ProductWindow F R p) :
    ∃ t : Finset (unitary (Matrix (Fin p) (Fin p) F)), ∀ U,
      ∃ V ∈ t, V⁻¹ * U ∈ W.frameWindow F R := by
  let S := fun V : unitary (Matrix (Fin p) (Fin p) F) =>
    (fun U => V⁻¹ * U) ⁻¹' W.frameWindow F R
  have hopen (V) : IsOpen (S V) :=
    (W.frameWindow_open F R).preimage (continuous_const.mul continuous_id)
  have hcover : (univ : Set (unitary (Matrix (Fin p) (Fin p) F))) ⊆ ⋃ V, S V := by
    intro U _
    apply mem_iUnion.mpr
    refine ⟨U,?_⟩
    simpa only [S, mem_preimage, inv_mul_cancel] using W.one_mem_frameWindow F R
  obtain ⟨t,ht⟩ := isCompact_univ.elim_finite_subcover S hopen hcover
  refine ⟨t, fun U => ?_⟩
  obtain ⟨V,hV,hVU⟩ := mem_iUnion₂.mp (ht (mem_univ U))
  exact ⟨V,hV,hVU⟩

theorem ProductWindow.orbit_in_translated_image (R : RealPartData F) {p : ℕ}
    (W : ProductWindow F R p) (lam : Fin p → ℝ)
    (U V : unitary (Matrix (Fin p) (Fin p) F)) (hVU : V⁻¹ * U ∈ W.frameWindow F R) :
    ∃ a ∈ W.angularWindow,
      orbitCoordinates F R lam U = coordinateConjugation F R V (chartCoordinates F R (lam,a)) := by
  obtain ⟨a,ha,heq⟩ := (W.mem_frameWindow_iff F R (V⁻¹*U)).mp hVU
  let C := cayleyUnitary F a (W.angular_subset ha)
  have hm : unitaryConjugate F (V⁻¹*U) (diagonalHermitian F (referenceSpectrum p)) =
      unitaryConjugate F C (diagonalHermitian F (referenceSpectrum p)) :=
    (hermitianCoordinates F R p).injective heq
  have hfull := conjugate_diagonal_eq_forall_of_eq_simple F (referenceSpectrum p)
    (referenceSpectrum_mem_chamber p).1.injective (V⁻¹*U) C hm lam
  have hconj := congrArg (unitaryConjugate F V) hfull
  rw [← unitaryConjugate_mul, mul_inv_cancel_left] at hconj
  refine ⟨a,ha,?_⟩
  simpa [orbitCoordinates, coordinateConjugation, chartCoordinates, C, conjugationLinearEquiv, spectralMap, unitaryConjugate, cayleyUnitary, diagonalHermitian, LinearEquiv.trans_apply] using congrArg (hermitianCoordinates F R p) hconj

theorem repeated_selector_null_of_orbits (R : RealPartData F) {p : ℕ}
    [CompactSpace (unitary (Matrix (Fin p) (Fin p) F))]
    [MeasurableSpace (Coordinates F p)] [BorelSpace (Coordinates F p)]
    (μ : Measure (Coordinates F p)) [IsAddHaarMeasure μ]
    (selector : Hermitian F p → Fin p → ℝ)
    (horbit : ∀ X : Hermitian F p, ∃ U : unitary (Matrix (Fin p) (Fin p) F),
      unitaryConjugate F U (diagonalHermitian F (selector X)) = X) :
    μ {x : Coordinates F p | ¬ Function.Injective
      (selector ((hermitianCoordinates F R p).symm x))} = 0 := by
  let W := chosenWindow F R p
  let bad : Set (Coordinates F p) :=
    {x | ¬Function.Injective x.1 ∧ x.2 ∈ W.angularWindow}
  let chart (U : unitary (Matrix (Fin p) (Fin p) F)) (x : Coordinates F p) :=
    coordinateConjugation F R U (chartCoordinates F R x)
  have hnull (U : unitary (Matrix (Fin p) (Fin p) F)) : μ (chart U '' bad) = 0 := by
    let L := (coordinateConjugation F R U).toContinuousLinearEquiv.toContinuousLinearMap
    have hd (x : Coordinates F p) (hx : x ∈ bad) :
        HasFDerivAt (chart U)
          (L.comp (chartDerivative F R x.2 (W.angular_subset hx.2) x.1)) x := by
      exact L.hasFDerivAt.comp x
        ((hasStrictFDerivAt_chartCoordinates F R x (W.angular_subset hx.2)).hasFDerivAt)
    apply addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
      (f' := fderiv ℝ (chart U))
    · intro x hx
      rw [(hd x hx).fderiv]
      exact (hd x hx).hasFDerivWithinAt
    · intro x hx
      rw [(hd x hx).fderiv]
      change LinearMap.det (L.toLinearMap.comp (chartDerivative F R x.2 (W.angular_subset hx.2) x.1).toLinearMap) = 0
      rw [LinearMap.det_comp]
      have hz := chartDerivative_det_zero_of_repeated F R x (W.angular_subset hx.2) hx.1
      change LinearMap.det (chartDerivative F R x.2 (W.angular_subset hx.2) x.1).toLinearMap = 0 at hz
      rw [hz, mul_zero]
  obtain ⟨t,ht⟩ := W.exists_finite_frame_cover F R
  apply measure_mono_null (t := ⋃ U ∈ t, chart U '' bad)
  · intro x hx
    let X := (hermitianCoordinates F R p).symm x
    obtain ⟨U,hU⟩ := horbit X
    obtain ⟨V,hV,hVU⟩ := ht U
    obtain ⟨a,ha,heq⟩ := W.orbit_in_translated_image F R (selector X) U V hVU
    apply mem_iUnion₂.mpr
    refine ⟨V,hV,(selector X,a),⟨hx,ha⟩,?_⟩
    change coordinateConjugation F R V (chartCoordinates F R (selector X,a)) = x
    rw [← heq]
    change hermitianCoordinates F R p (unitaryConjugate F U (diagonalHermitian F (selector X))) = x
    rw [hU,LinearEquiv.apply_symm_apply]
  · exact (measure_biUnion_null_iff t.countable_toSet).mpr fun U _ => hnull U

end Wishart.FieldCharts
end
end CanonicalSource14

section CanonicalSource15
/- Source: Wishart/FieldHaarReconstruction.lean -/




/-!
# Independent Haar reconstruction of the actual field Wishart law

The spectral selector is continuous and its orbit witness is purely pointwise.
No measurable eigenframe is selected.  The actual density transfers the proved
Lebesgue nullity of repeated eigenvalues to every admissible real shape.
-/

noncomputable section
open MeasureTheory.Measure
open Matrix MeasureTheory Set
open scoped Classical Quaternion ComplexOrder Matrix.Norms.L2Operator ENNReal

namespace Wishart.FieldCharts
open scoped Matrix.Norms.Frobenius

variable (F : Type*) [NormedRing F] [NormedAlgebra ℝ F] [StarRing F]
  [StarModule ℝ F] [FiniteDimensional ℝ F] [ContinuousStar F] [MeasurableSpace F] [BorelSpace F] [Nontrivial F]

theorem continuous_unitaryConjugate (p : ℕ) :
    Continuous (Function.uncurry (unitaryConjugate F (p := p))) := by
  apply Continuous.subtype_mk
  change Continuous (fun z : unitary (Matrix (Fin p) (Fin p) F) × Hermitian F p =>
    z.1.val * z.2.val * star z.1.val)
  fun_prop

theorem continuous_diagonalHermitian (p : ℕ) :
    Continuous (diagonalHermitian F (p := p)) := by
  apply Continuous.subtype_mk
  change Continuous (fun lam : Fin p → ℝ => Matrix.diagonal
    (fun i => algebraMap ℝ F (lam i)))
  fun_prop

theorem measurable_unitary_diagonal (p : ℕ) : Measurable
    (fun z : unitary (Matrix (Fin p) (Fin p) F) × (Fin p → ℝ) =>
      unitaryConjugate F z.1 (diagonalHermitian F z.2)) := by
  have hc : Continuous (fun z : unitary (Matrix (Fin p) (Fin p) F) × (Fin p → ℝ) =>
      unitaryConjugate F z.1 (diagonalHermitian F z.2)) :=
    (continuous_unitaryConjugate F p).comp
      (continuous_fst.prodMk ((continuous_diagonalHermitian F p).comp continuous_snd))
  exact hc.measurable

theorem hermitianLebesgue_repeated_selector (R : RealPartData F) {p : ℕ}
    [CompactSpace (unitary (Matrix (Fin p) (Fin p) F))]
    [MeasurableSpace (Hermitian F p)] [BorelSpace (Hermitian F p)]
    (μ : Measure (Hermitian F p)) [IsAddHaarMeasure μ]
    (selector : Hermitian F p → Fin p → ℝ)
    (horbit : ∀ X : Hermitian F p, ∃ U : unitary (Matrix (Fin p) (Fin p) F),
      unitaryConjugate F U (diagonalHermitian F (selector X)) = X) :
    μ {X | ¬Function.Injective (selector X)} = 0 := by
  let e := (hermitianCoordinates F R p).toContinuousLinearEquiv
  letI : IsAddHaarMeasure (μ.map e) := e.isAddHaarMeasure_map μ
  have h := repeated_selector_null_of_orbits F R (μ.map e) selector horbit
  change (μ.map e.toHomeomorph) {x | ¬Function.Injective (selector ((hermitianCoordinates F R p).symm x))} = 0 at h
  rw [e.toHomeomorph.measurableEmbedding.map_apply] at h
  have hset : e.toHomeomorph ⁻¹' {x | ¬Function.Injective (selector ((hermitianCoordinates F R p).symm x))} =
      {X | ¬Function.Injective (selector X)} := by
    ext X
    change (¬Function.Injective (selector ((hermitianCoordinates F R p).symm (hermitianCoordinates F R p X)))) ↔ _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  rw [hset] at h
  exact h

end Wishart.FieldCharts

namespace Wishart.ComplexMatrix
open Wishart.FieldCharts

def identityEigenLaw (p : ℕ) (α : ℝ) : Measure (Fin p → ℝ) :=
  (wishartMeasure α (1 : Matrix (Fin p) (Fin p) ℂ)).map ascendingValues

theorem identityEigenLaw_isProbability {p : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α) : IsProbabilityMeasure (identityEigenLaw p α) := by
  letI := wishart_standard_probability p hα
  unfold identityEigenLaw
  infer_instance

theorem ae_simple_spectrum_wishart {p : ℕ} (α : ℝ)
    (Sigma : Matrix (Fin p) (Fin p) ℂ) :
    ∀ᵐ X ∂wishartMeasure α Sigma, Function.Injective (ascendingValues X) := by
  rw [ae_iff]
  exact ((withDensity_absolutelyContinuous (hermitianLebesgue p)
    (wishartWeight α Sigma)).smul_left (wishartNormalizer α Sigma)⁻¹)
    (hermitianLebesgue_repeated_selector ℂ realPartData
      (hermitianLebesgue p) ascendingValues exists_conjugate_ascending)

theorem ascendingValues_pos {p : ℕ} (X : Hermitian p)
    (hX : (X : Matrix (Fin p) (Fin p) ℂ).PosDef) (i : Fin p) :
    0 < ascendingValues X i := by
  change 0 < Wishart.FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe X) (Fin.rev i)
  rw [Wishart.FieldSpectral.orderedValues_eq]
  exact hX.eigenvalues_pos _

theorem ae_identityEigenLaw_mem_chamber {p : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α) :
    ∀ᵐ lam ∂identityEigenLaw p α, lam ∈ chamber p := by
  apply (ae_map_iff (continuous_ascendingValues p).measurable.aemeasurable
    (Wishart.Spectral.isOpen_positiveChamber p).measurableSet).mpr
  filter_upwards [ae_simple_spectrum_wishart α 1, wishart_ae_posDef α 1] with X hX hp
  refine ⟨(ascendingValues_monotone X).strictMono_of_injective hX,
    fun i => ascendingValues_pos X hp i⟩

theorem haar_ascending_spectral_reconstruction {p : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α) :
    ((TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) ℂ))).prod
      (identityEigenLaw p α)).map
      (fun z => unitaryConjugate ℂ z.1 (diagonalHermitian ℂ z.2)) =
        wishartMeasure α (1 : Matrix (Fin p) (Fin p) ℂ) := by
  letI := wishart_standard_probability p hα
  exact Wishart.map_prod_orbit_representative _ _ (unitaryConjugate ℂ)
    ascendingValues (diagonalHermitian ℂ)
    (continuous_unitaryConjugate ℂ p).measurable
    (continuous_ascendingValues p).measurable
    (continuous_diagonalHermitian ℂ p).measurable
    (unitaryConjugate_mul ℂ) (map_unitaryConjugate_wishart hα)
    exists_conjugate_ascending

end Wishart.ComplexMatrix

namespace Wishart.QuaternionMatrix
open scoped Matrix.Norms.Frobenius
open Wishart.FieldCharts

def identityEigenLaw (p : ℕ) (α : ℝ) : Measure (Fin p → ℝ) :=
  (wishartMeasure α (1 : Matrix (Fin p) (Fin p) ℍ[ℝ])).map ascendingValues

theorem identityEigenLaw_isProbability {p : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α) : IsProbabilityMeasure (identityEigenLaw p α) := by
  letI := wishart_standard_probability p hα
  unfold identityEigenLaw
  infer_instance

theorem ae_simple_spectrum_wishart {p : ℕ} (α : ℝ)
    (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) :
    ∀ᵐ X ∂wishartMeasure α Sigma, Function.Injective (ascendingValues X) := by
  rw [ae_iff]
  exact ((withDensity_absolutelyContinuous (hermitianLebesgue p)
    (wishartWeight α Sigma)).smul_left (wishartNormalizer α Sigma)⁻¹)
    (hermitianLebesgue_repeated_selector ℍ[ℝ] realPartData
      (hermitianLebesgue p) ascendingValues exists_conjugate_ascending)

theorem orderedValues_pos {p : ℕ} (X : Hermitian p)
    (hX : PosDef (X : Matrix (Fin p) (Fin p) ℍ[ℝ])) (i : Fin p) :
    0 < orderedValues X i := by
  have hf : (flatRepresentation (X : Matrix (Fin p) (Fin p) ℍ[ℝ])).PosDef :=
    hX.submatrix finProdFinEquiv.symm.injective
  change 0 < Wishart.FieldSpectral.orderedValues
    (WishartVerification.hermitian_matrix_coe (flatHermitian X)) (doubledIndex i)
  rw [Wishart.FieldSpectral.orderedValues_eq]
  exact hf.eigenvalues_pos _

theorem ascendingValues_pos {p : ℕ} (X : Hermitian p)
    (hX : PosDef (X : Matrix (Fin p) (Fin p) ℍ[ℝ])) (i : Fin p) :
    0 < ascendingValues X i := orderedValues_pos X hX (Fin.rev i)

theorem ae_identityEigenLaw_mem_chamber {p : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α) :
    ∀ᵐ lam ∂identityEigenLaw p α, lam ∈ chamber p := by
  apply (ae_map_iff (continuous_ascendingValues p).measurable.aemeasurable
    (Wishart.Spectral.isOpen_positiveChamber p).measurableSet).mpr
  filter_upwards [ae_simple_spectrum_wishart α 1, wishart_ae_posDef α 1] with X hX hp
  refine ⟨(ascendingValues_monotone X).strictMono_of_injective hX,
    fun i => ascendingValues_pos X hp i⟩

theorem haar_ascending_spectral_reconstruction {p : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α) :
    ((TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) ℍ[ℝ]))).prod
      (identityEigenLaw p α)).map
      (fun z => unitaryConjugate ℍ[ℝ] z.1
        (Wishart.FieldCharts.diagonalHermitian ℍ[ℝ] z.2)) =
        wishartMeasure α (1 : Matrix (Fin p) (Fin p) ℍ[ℝ]) := by
  letI := wishart_standard_probability p hα
  exact Wishart.map_prod_orbit_representative _ _ (unitaryConjugate ℍ[ℝ])
    ascendingValues (Wishart.FieldCharts.diagonalHermitian ℍ[ℝ])
    (continuous_unitaryConjugate ℍ[ℝ] p).measurable
    (continuous_ascendingValues p).measurable
    (continuous_diagonalHermitian ℍ[ℝ] p).measurable
    (unitaryConjugate_mul ℍ[ℝ]) (map_unitaryConjugate_wishart hα)
    exists_conjugate_ascending

end Wishart.QuaternionMatrix
end
end CanonicalSource15

section CanonicalSource16
/- Source: Wishart/FieldSpectralIntegration.lean -/



/-!
# Deriving the full spectral density from the actual chart

The two evaluations of a single chart restriction identify complete measures.
The hypotheses of the reusable calculation are pointwise density algebra,
the already proved Haar reconstruction, and the actual full-mass chamber.
The complex and quaternion files instantiate every one of these hypotheses.
-/

noncomputable section
open Matrix MeasureTheory Set WishartVerification.FieldDensity
open scoped Classical ENNReal Matrix.Norms.Operator

namespace Wishart.FieldCharts
open scoped Matrix.Norms.Frobenius

variable (F : Type*) [NormedRing F] [NormedAlgebra ℝ F] [StarRing F]
  [StarModule ℝ F] [FiniteDimensional ℝ F] [ContinuousStar F] [Nontrivial F]
  [MeasurableSpace F] [BorelSpace F]

theorem setLIntegral_imageWindow_normalized_density (R : RealPartData F) {p : ℕ}
    [CompactSpace (unitary (Matrix (Fin p) (Fin p) F))] (W : ProductWindow F R p)
    (w : Coordinates F p → ℝ≥0∞) (hw : Measurable w)
    (selector : Coordinates F p → Fin p → ℝ) (hselector : Measurable selector)
    (q : (Fin p → ℝ) → ℝ) (hq : Measurable q)
    (hqoff : ∀ lam ∉ chamber p, q lam = 0)
    (hselect : ∀ x ∈ chamber p ×ˢ W.angularWindow,
      selector (chartCoordinates F R x) = x.1)
    (hfactor : ∀ x ∈ chamber p ×ˢ W.angularWindow,
      ENNReal.ofReal (|∏ ij : PairIndex p, (x.1 ij.1.2 - x.1 ij.1.1)| ^ Module.finrank ℝ F) *
        w (chartCoordinates F R x) = ENNReal.ofReal (q x.1))
    (f : (Fin p → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x in W.imageWindow F R, f (selector x)
      ∂normalized (coordinateLebesgue F p) w) =
        (W.angularMass F R * (normalizer (coordinateLebesgue F p) w)⁻¹) *
          ∫⁻ lam, ENNReal.ofReal (q lam) * f lam := by
  let Q : (Fin p → ℝ) → ℝ≥0∞ := fun lam => ENNReal.ofReal (q lam) * f lam
  let A : OffDiagonal F p → ℝ≥0∞ := W.angularWeight F R
  have hQ : Measurable Q := hq.ennreal_ofReal.mul hf
  have hA : Measurable A := W.measurable_angularWeight F R
  have hsupport : Function.support Q ⊆ chamber p := by
    intro lam hlam
    by_contra hn
    apply hlam
    simp only [Q,hqoff lam hn,ENNReal.ofReal_zero,zero_mul]
  have hAI : (∫⁻ z in W.angularWindow, A z ∂angularLebesgue F p) =
      W.angularMass F R := by
    apply setLIntegral_eq_of_support_subset
    exact Set.support_indicator_subset
  have hQI : (∫⁻ lam in chamber p, Q lam) = ∫⁻ lam, Q lam :=
    setLIntegral_eq_of_support_subset hsupport
  have hsep :
      (∫⁻ x in chamber p ×ˢ W.angularWindow, A x.2 * Q x.1
        ∂coordinateLebesgue F p) = W.angularMass F R * ∫⁻ lam, Q lam := by
    rw [coordinateLebesgue, setLIntegral_prod (fun x : Coordinates F p => A x.2 * Q x.1)
      (show Measurable (fun x : Coordinates F p => A x.2 * Q x.1) from
        (hA.comp measurable_snd).mul (hQ.comp measurable_fst)).aemeasurable]
    simp_rw [lintegral_mul_const _ hA, hAI]
    rw [lintegral_const_mul _ hQ,hQI]
  have hdom := (Wishart.Spectral.isOpen_positiveChamber p).measurableSet.prod
    W.angular_open.measurableSet
  have hder (x : Coordinates F p) (hx : x ∈ chamber p ×ˢ W.angularWindow) :
      HasFDerivWithinAt (chartCoordinates F R) (fderiv ℝ (chartCoordinates F R) x)
        (chamber p ×ˢ W.angularWindow) x :=
    (hasStrictFDerivAt_chartCoordinates F R x (W.angular_subset hx.2)).differentiableAt.hasFDerivAt.hasFDerivWithinAt
  calc
    (∫⁻ x in W.imageWindow F R, f (selector x)
        ∂normalized (coordinateLebesgue F p) w) =
        (normalizer (coordinateLebesgue F p) w)⁻¹ *
          ∫⁻ x in W.imageWindow F R, w x * f (selector x) ∂coordinateLebesgue F p := by
      rw [normalized,Measure.restrict_smul,lintegral_smul_measure]
      congr 1
      exact setLIntegral_withDensity_eq_setLIntegral_mul _ hw
        (hf.comp hselector) (W.measurableSet_imageWindow F R)
    _ = (normalizer (coordinateLebesgue F p) w)⁻¹ *
        ∫⁻ x in chamber p ×ˢ W.angularWindow,
          ENNReal.ofReal |(fderiv ℝ (chartCoordinates F R) x).det| *
            (w (chartCoordinates F R x) * f (selector (chartCoordinates F R x)))
          ∂coordinateLebesgue F p := by
      congr 1
      exact lintegral_image_eq_lintegral_abs_det_fderiv_mul
        (coordinateLebesgue F p) hdom hder (W.injOn_chamber F R) _
    _ = (normalizer (coordinateLebesgue F p) w)⁻¹ *
        ∫⁻ x in chamber p ×ˢ W.angularWindow, A x.2 * Q x.1
          ∂coordinateLebesgue F p := by
      congr 1
      apply setLIntegral_congr_fun hdom
      intro x hx
      dsimp only
      rw [abs_det_fderiv_chartCoordinates F R x (W.angular_subset hx.2),
        ENNReal.ofReal_mul (abs_nonneg _), hselect x hx]
      change ENNReal.ofReal (angularJacobian F x.2) *
        ENNReal.ofReal _ * (w (chartCoordinates F R x) * f x.1) = _
      rw [mul_assoc,← mul_assoc (ENNReal.ofReal _) (w _),hfactor x hx]
      simp only [A,Q,W.angularWeight_of_mem F R hx.2]
    _ = _ := by rw [hsep]; simp only [Q,mul_assoc,mul_left_comm]

theorem setLIntegral_imageWindow_haar (R : RealPartData F) {p : ℕ}
    [CompactSpace (unitary (Matrix (Fin p) (Fin p) F))] (W : ProductWindow F R p)
    (μ : Measure (Coordinates F p))
    (κ : Measure (Fin p → ℝ)) [IsProbabilityMeasure κ]
    (selector : Coordinates F p → Fin p → ℝ) (hselector : Measurable selector)
    (hselect : ∀ lam ∈ chamber p, ∀ U : unitary (Matrix (Fin p) (Fin p) F),
      selector (orbitCoordinates F R lam U) = lam)
    (hae : ∀ᵐ lam ∂κ, lam ∈ chamber p)
    (hrec : ((TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) F))).prod κ).map
      (fun z => orbitCoordinates F R z.2 z.1) = μ)
    (f : (Fin p → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x in W.imageWindow F R, f (selector x) ∂μ) =
      TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) F)) (W.frameWindow F R) *
        ∫⁻ lam, f lam ∂κ := by
  let T : unitary (Matrix (Fin p) (Fin p) F) × (Fin p → ℝ) → Coordinates F p :=
    fun z => orbitCoordinates F R z.2 z.1
  let H : Coordinates F p → ℝ≥0∞ :=
    (W.imageWindow F R).indicator (fun x => f (selector x))
  have hT : Measurable T := by
    have hc : Measurable (fun X : Hermitian F p => hermitianCoordinates F R p X) :=
      (hermitianCoordinates F R p).toLinearMap.continuous_of_finiteDimensional.measurable
    exact hc.comp (measurable_unitary_diagonal F p)
  have hH : Measurable H := (hf.comp hselector).indicator (W.measurableSet_imageWindow F R)
  have hinner (lam : Fin p → ℝ) (hlam : lam ∈ chamber p) :
      (∫⁻ U, H (T (U,lam)) ∂TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) F))) =
        TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) F)) (W.frameWindow F R) * f lam := by
    have heq (U : unitary (Matrix (Fin p) (Fin p) F)) : H (T (U,lam)) =
        (W.frameWindow F R).indicator (fun _ => f lam) U := by
      by_cases hU : U ∈ W.frameWindow F R
      · have hx : orbitCoordinates F R lam U ∈ W.imageWindow F R :=
          (W.orbit_mem_image_iff F R lam hlam U).mpr hU
        simp only [H,T,Set.indicator_of_mem hx,Set.indicator_of_mem hU,hselect lam hlam U]
      · have hx : orbitCoordinates F R lam U ∉ W.imageWindow F R :=
          fun hx => hU ((W.orbit_mem_image_iff F R lam hlam U).mp hx)
        simp only [H,T,Set.indicator_of_notMem hx,Set.indicator_of_notMem hU]
    rw [lintegral_congr heq,
      lintegral_indicator_const (W.frameWindow_open F R).measurableSet]
    exact mul_comm _ _
  calc
    (∫⁻ x in W.imageWindow F R, f (selector x) ∂μ) = ∫⁻ x, H x ∂μ :=
      (lintegral_indicator (W.measurableSet_imageWindow F R) _).symm
    _ = ∫⁻ lam, ∫⁻ U, H (T (U,lam))
        ∂TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) F)) ∂κ := by
      rw [← hrec,lintegral_map hH hT]
      exact lintegral_prod_symm _ (hH.comp hT).aemeasurable
    _ = ∫⁻ lam, TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) F))
        (W.frameWindow F R) * f lam ∂κ := lintegral_congr_ae (hae.mono hinner)
    _ = _ := lintegral_const_mul _ hf

theorem spectralLaw_normalized_density (R : RealPartData F) {p : ℕ}
    [CompactSpace (unitary (Matrix (Fin p) (Fin p) F))]
    (w : Coordinates F p → ℝ≥0∞) (hw : Measurable w)
    (κ : Measure (Fin p → ℝ)) [IsProbabilityMeasure κ]
    (selector : Coordinates F p → Fin p → ℝ) (hselector : Measurable selector)
    (q : (Fin p → ℝ) → ℝ) (hq : Measurable q)
    (hqoff : ∀ lam ∉ chamber p, q lam = 0)
    (hselect : ∀ lam ∈ chamber p, ∀ U : unitary (Matrix (Fin p) (Fin p) F),
      selector (orbitCoordinates F R lam U) = lam)
    (hfactor : ∀ lam ∈ chamber p, ∀ U : unitary (Matrix (Fin p) (Fin p) F),
      ENNReal.ofReal (|∏ ij : PairIndex p, (lam ij.1.2 - lam ij.1.1)| ^ Module.finrank ℝ F) *
        w (orbitCoordinates F R lam U) = ENNReal.ofReal (q lam))
    (hae : ∀ᵐ lam ∂κ, lam ∈ chamber p)
    (hrec : ((TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) F))).prod κ).map
      (fun z => orbitCoordinates F R z.2 z.1) = normalized (coordinateLebesgue F p) w) :
    (∫⁻ lam, ENNReal.ofReal (q lam)) ≠ 0 ∧
    (∫⁻ lam, ENNReal.ofReal (q lam)) ≠ ∞ ∧
    κ = WishartVerification.normalizedWeight volume q := by
  let W := chosenWindow F R p
  let c := TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) F)) (W.frameWindow F R)
  let A := W.angularMass F R * (normalizer (coordinateLebesgue F p) w)⁻¹
  have hlaw : c • κ = A • (volume : Measure (Fin p → ℝ)).withDensity
      (fun lam => ENNReal.ofReal (q lam)) := by
    apply Measure.ext_of_lintegral
    intro f hf
    rw [lintegral_smul_measure,lintegral_smul_measure]
    change c * (∫⁻ lam, f lam ∂κ) = A * _
    rw [← setLIntegral_imageWindow_haar F R W _ κ selector hselector hselect hae hrec f hf]
    rw [setLIntegral_imageWindow_normalized_density F R W w hw selector hselector q hq hqoff
      (fun x hx => hselect x.1 hx.1 (cayleyUnitary F x.2 (W.angular_subset hx.2)))
      (fun x hx => hfactor x.1 hx.1 (cayleyUnitary F x.2 (W.angular_subset hx.2))) f hf]
    rw [lintegral_withDensity_eq_lintegral_mul _ hq.ennreal_ofReal hf]
    rfl
  obtain ⟨_,_,h0,ht,heq⟩ :=
    WishartVerification.normalizedWeight_eq_of_scaled_probability_density κ volume q c A
      (W.haar_frameWindow_pos F R).ne' (W.haar_frameWindow_ne_top F R) hlaw
  exact ⟨h0,ht,heq⟩

end Wishart.FieldCharts
end
end CanonicalSource16

section CanonicalSource17
/- Source: Wishart/FieldSpectralWeights.lean -/



/-!
# The literal beta-two and beta-four Laguerre weights

The field dimension is the natural number beta. The exponent and rate agree
with the manuscript, and the density vanishes off the strictly increasing
positive chamber. Its matrix-density factorization is proved separately for
the actual complex determinant and actual quaternion Moore determinant.
-/

noncomputable section
open Matrix MeasureTheory
open scoped Classical Quaternion ComplexOrder ENNReal Matrix.Norms.L2Operator

namespace Wishart.FieldSpectral

def laguerreWeight (β p : ℕ) (α t : ℝ) : ℝ :=
  (max t 0) ^ ((β : ℝ) / 2 * (α - p + 1) - 1) * Real.exp (-((β : ℝ) / 2 * t))

def fieldEigenDensity (β p : ℕ) (α : ℝ) : (Fin p → ℝ) → ℝ :=
  WishartVerification.chamberWeight (Set.Ioi 0) (fun _ => laguerreWeight β p α) β

theorem laguerreWeight_nonneg (β p : ℕ) (α t : ℝ) : 0 ≤ laguerreWeight β p α t :=
  mul_nonneg (Real.rpow_nonneg (le_max_right _ _) _) (Real.exp_pos _).le

theorem measurable_laguerreWeight (β p : ℕ) (α : ℝ) :
    Measurable (laguerreWeight β p α) := by
  exact ((measurable_id.max measurable_const).pow_const _).mul
    ((measurable_const.mul measurable_id).neg.exp)

theorem laguerreWeight_pos (β p : ℕ) (α : ℝ) {t : ℝ} (ht : 0 < t) :
    0 < laguerreWeight β p α t := by
  unfold laguerreWeight
  exact mul_pos (Real.rpow_pos_of_pos (ht.trans_le (le_max_left _ _)) _) (Real.exp_pos _)

theorem fieldEigenDensity_nonneg (β p : ℕ) (α : ℝ) (lam : Fin p → ℝ) :
    0 ≤ fieldEigenDensity β p α lam :=
  WishartVerification.chamberWeight_nonneg _ _ _ (fun _ => laguerreWeight_nonneg β p α) lam

theorem measurable_fieldEigenDensity (β p : ℕ) (α : ℝ) :
    Measurable (fieldEigenDensity β p α) :=
  WishartVerification.chamberWeight_measurable _ measurableSet_Ioi _ _
    (fun _ => measurable_laguerreWeight β p α)

theorem fieldEigenDensity_off_chamber {β p : ℕ} (hβ : 0 < β) (α : ℝ)
    (lam : Fin p → ℝ) (hlam : lam ∉ Wishart.FieldCharts.chamber p) :
    fieldEigenDensity β p α lam = 0 :=
  WishartVerification.chamberWeight_eq_zero_off _ _ β (by exact_mod_cast hβ) lam hlam

theorem fieldEigenDensity_on_chamber {β p : ℕ} (hβ : 0 < β) (α : ℝ)
    (lam : Fin p → ℝ) (hlam : lam ∈ Wishart.FieldCharts.chamber p) :
    fieldEigenDensity β p α lam = (∏ i, laguerreWeight β p α (lam i)) *
      (∏ ij : Wishart.FieldCharts.PairIndex p, (lam ij.1.2 - lam ij.1.1)) ^ β := by
  rw [fieldEigenDensity, WishartVerification.chamberWeight_eq_density _ _ β
    (by exact_mod_cast hβ),if_pos hlam]
  congr 1
  simp_rw [Real.rpow_natCast]
  change _ = Wishart.Spectral.gapProduct lam ^ β
  rw [Wishart.Spectral.gapProduct_eq_double_product]
  simp only [← Finset.prod_pow,ite_pow,one_pow]

theorem prod_laguerreWeight {p : ℕ} (β : ℕ) (α : ℝ)
    (lam : Fin p → ℝ) (hlam : ∀ i, 0 < lam i) :
    (∏ i, laguerreWeight β p α (lam i)) =
      (∏ i, lam i) ^ ((β : ℝ) / 2 * (α - p + 1) - 1) *
        Real.exp (-((β : ℝ) / 2 * ∑ i, lam i)) := by
  have hm (i : Fin p) : max (lam i) 0 = lam i := max_eq_left (hlam i).le
  simp only [laguerreWeight,hm,Finset.prod_mul_distrib]
  rw [Real.finsetProd_rpow _ _ (fun i _ => (hlam i).le),← Real.exp_sum]
  simp only [Finset.sum_neg_distrib,← Finset.mul_sum]

end Wishart.FieldSpectral

namespace Wishart.ComplexMatrix
open Wishart.FieldCharts

theorem wishartWeight_conjugate_diagonal {p : ℕ} (α : ℝ)
    (U : unitary (Matrix (Fin p) (Fin p) ℂ)) (lam : Fin p → ℝ) (hlam : ∀ i, 0 < lam i) :
    wishartWeight α 1 (unitaryConjugate ℂ U (diagonalHermitian ℂ lam)) =
      ENNReal.ofReal (∏ i, Wishart.FieldSpectral.laguerreWeight 2 p α (lam i)) := by
  rw [wishartWeight_unitary,Wishart.FieldSpectral.prod_laguerreWeight 2 α lam hlam]
  have hp : (diagonalHermitian ℂ lam : Matrix (Fin p) (Fin p) ℂ).PosDef :=
    Matrix.PosDef.diagonal fun i => RCLike.pos_iff.mpr ⟨hlam i,by simp⟩
  rw [wishartWeight,if_pos hp]
  simp only [realDeterminant,diagonalHermitian,realDiagonal,
    Matrix.det_diagonal,map_prod,Complex.ofReal_re,inv_one,Matrix.one_mul,
    Matrix.trace_diagonal,map_sum,Nat.cast_ofNat,div_self (by norm_num : (2:ℝ) ≠ 0),
    one_mul]
  simp only [Complex.coe_algebraMap, ← Complex.ofReal_prod, ← Complex.ofReal_sum,
    Complex.ofReal_re] <;> congr 2 <;> ring

end Wishart.ComplexMatrix

namespace Wishart.QuaternionMatrix
open scoped Matrix.Norms.Frobenius
open Wishart.FieldCharts

theorem wishartWeight_conjugate_diagonal {p : ℕ} (α : ℝ)
    (U : unitary (Matrix (Fin p) (Fin p) ℍ[ℝ])) (lam : Fin p → ℝ) (hlam : ∀ i, 0 < lam i) :
    wishartWeight α 1 (unitaryConjugate ℍ[ℝ] U (Wishart.FieldCharts.diagonalHermitian ℍ[ℝ] lam)) =
      ENNReal.ofReal (∏ i, Wishart.FieldSpectral.laguerreWeight 4 p α (lam i)) := by
  rw [wishartWeight_unitary,Wishart.FieldSpectral.prod_laguerreWeight 4 α lam hlam]
  have hp : PosDef (Wishart.FieldCharts.diagonalHermitian ℍ[ℝ] lam :
      Matrix (Fin p) (Fin p) ℍ[ℝ]) := by
    unfold PosDef
    rw [show (Wishart.FieldCharts.diagonalHermitian ℍ[ℝ] lam : Matrix (Fin p) (Fin p) ℍ[ℝ]) =
      Matrix.diagonal (fun i => (lam i : ℍ[ℝ])) from rfl,complexRepresentation_diagonal]
    exact Matrix.PosDef.diagonal fun i => RCLike.pos_iff.mpr ⟨hlam i.1,by simp⟩
  rw [wishartWeight,if_pos hp]
  change ENNReal.ofReal ((positiveDeterminant (Matrix.diagonal (fun i => (lam i : ℍ[ℝ])))) ^ _ * _) = _
  rw [positiveDeterminant_diagonal lam (fun i => (hlam i).le)]
  simp only [Ring.inverse_one,Matrix.one_mul,Wishart.FieldCharts.diagonalHermitian,
    realDiagonal,Matrix.trace_diagonal,map_sum,QuaternionAlgebra.re_coe,Nat.cast_ofNat]
  have htrace : (∑ i, (lam i : ℍ[ℝ])).re = ∑ i, lam i := by
    change (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)) (∑ i, (lam i : ℍ[ℝ])) = _
    rw [map_sum]
    rfl
  norm_num [htrace]

end Wishart.QuaternionMatrix
end
end CanonicalSource17

section CanonicalSource18
/- Source: Wishart/ChamberExtendedAssociation.lean -/



/-!
# Ordered-spectrum association for extended-valued conditional expectations

The actual chamber density is unchanged. Two independent finite truncation
levels extend the real-valued theorem to nonnegative extended-valued tests.
The proof uses order-continuity of multiplication through suprema, including
the convention `0 * ∞ = 0`; it does not assume ordinary continuity there.
-/

noncomputable section
open MeasureTheory Set
open scoped Classical ENNReal
namespace WishartVerification

theorem lemma_2_1_ennreal_association
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (s : Set ℝ) (hs : MeasurableSet s) (w : ι → ℝ → ℝ)
    (β : ℝ) (hβ : 0 < β) (hwm : ∀ i, Measurable (w i))
    (hw0 : ∀ i t, 0 ≤ w i t)
    (hZ0 : (∫⁻ x : ι → ℝ, ENNReal.ofReal (chamberWeight s w β x)) ≠ 0)
    (hZtop : (∫⁻ x : ι → ℝ, ENNReal.ofReal (chamberWeight s w β x)) ≠ ∞)
    (f g : (ι → ℝ) → ℝ≥0∞) (hfm : Measurable f) (hgm : Measurable g)
    (hfi : MonotoneOn f (orderedChamber s)) (hgi : MonotoneOn g (orderedChamber s)) :
    (∫⁻ x, f x ∂normalizedWeight volume (chamberWeight s w β)) *
        (∫⁻ x, g x ∂normalizedWeight volume (chamberWeight s w β)) ≤
      ∫⁻ x, f x * g x ∂normalizedWeight volume (chamberWeight s w β) := by
  let μ := normalizedWeight volume (chamberWeight s w β)
  change (∫⁻ x, f x ∂μ) * (∫⁻ x, g x ∂μ) ≤ ∫⁻ x, f x * g x ∂μ
  rw [lintegral_eq_iSup_ennrealTruncation μ hfm,
    lintegral_eq_iSup_ennrealTruncation μ hgm, ENNReal.iSup_mul]
  simp_rw [ENNReal.mul_iSup]
  apply iSup_le
  intro n
  apply iSup_le
  intro m
  have h := lemma_2_1_association s hs w β hβ hwm hw0 hZ0 hZtop
    (ennrealTruncation n f) (ennrealTruncation m g)
    (measurable_ennrealTruncation n hfm) (measurable_ennrealTruncation m hgm)
    (ennrealTruncation_nonneg n f) (ennrealTruncation_nonneg m g)
    (monotoneOn_ennrealTruncation n hfi) (monotoneOn_ennrealTruncation m hgi)
  apply h.trans
  apply lintegral_mono
  intro x
  dsimp only
  rw [ENNReal.ofReal_mul (ennrealTruncation_nonneg n f x),
    ofReal_ennrealTruncation, ofReal_ennrealTruncation]
  exact mul_le_mul' (min_le_left _ _) (min_le_left _ _)

end WishartVerification
end
end CanonicalSource18

section CanonicalSource19
/- Source: Wishart/FieldSpectralDensity.lean -/



/-!
# Complete beta-two and beta-four spectral laws

All shapes are real and satisfy only alpha > p-1. The measures below are the
literal normalized matrix densities. Their spectral laws and independent Haar
representations follow from the actual Cayley Jacobian and normalization; no
classical integration formula or spectral-law hypothesis is imported.
-/

noncomputable section
open MeasureTheory.Measure
open Matrix MeasureTheory Set WishartVerification.FieldDensity
open scoped Classical Quaternion ComplexOrder Matrix.Norms.L2Operator ENNReal

namespace Wishart.FieldCharts
open scoped Matrix.Norms.Frobenius

variable (F : Type*) [NormedRing F] [NormedAlgebra ℝ F] [StarRing F]
  [StarModule ℝ F] [FiniteDimensional ℝ F] [ContinuousStar F] [Nontrivial F]
  [MeasurableSpace F] [BorelSpace F]

theorem spectral_density_from_hermitian (R : RealPartData F) {p : ℕ}
    [CompactSpace (unitary (Matrix (Fin p) (Fin p) F))]
    (μ : Measure (Hermitian F p)) [IsAddHaarMeasure μ]
    (w : Hermitian F p → ℝ≥0∞) (hw : Measurable w) (hfinite : FiniteDensity μ w)
    (selector : Hermitian F p → Fin p → ℝ) (hselector : Measurable selector)
    (q : (Fin p → ℝ) → ℝ) (hq : Measurable q)
    (hqoff : ∀ lam ∉ chamber p, q lam = 0)
    (hselect : ∀ lam ∈ chamber p, ∀ U : unitary (Matrix (Fin p) (Fin p) F),
      selector (unitaryConjugate F U (diagonalHermitian F lam)) = lam)
    (hfactor : ∀ lam ∈ chamber p, ∀ U : unitary (Matrix (Fin p) (Fin p) F),
      ENNReal.ofReal (|∏ ij : PairIndex p, (lam ij.1.2 - lam ij.1.1)| ^ Module.finrank ℝ F) *
        w (unitaryConjugate F U (diagonalHermitian F lam)) = ENNReal.ofReal (q lam))
    (hae : ∀ᵐ lam ∂(normalized μ w).map selector, lam ∈ chamber p)
    (hrec : ((TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) F))).prod
      ((normalized μ w).map selector)).map
        (fun z => unitaryConjugate F z.1 (diagonalHermitian F z.2)) = normalized μ w) :
    (∫⁻ lam, ENNReal.ofReal (q lam)) ≠ 0 ∧
    (∫⁻ lam, ENNReal.ofReal (q lam)) ≠ ∞ ∧
    (normalized μ w).map selector = WishartVerification.normalizedWeight volume q := by
  let e := (hermitianCoordinates F R p).toContinuousLinearEquiv
  let wc : Coordinates F p → ℝ≥0∞ := w ∘ e.symm
  let sc : Coordinates F p → Fin p → ℝ := selector ∘ e.symm
  let κ := (normalized μ w).map selector
  letI := isProbability_normalized hfinite
  haveI : IsProbabilityMeasure κ := by dsimp [κ]; infer_instance
  have hcoord : normalized (coordinateLebesgue F p) wc = (normalized μ w).map e :=
    (normalized_transport_haar e μ (coordinateLebesgue F p) w wc hfinite
      (fun X => by simp only [wc,Function.comp_apply,e.symm_apply_apply])).2
  have hbuild : Measurable (fun z : unitary (Matrix (Fin p) (Fin p) F) × (Fin p → ℝ) =>
      unitaryConjugate F z.1 (diagonalHermitian F z.2)) :=
    measurable_unitary_diagonal F p
  have hrec' : ((TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) F))).prod κ).map
      (fun z => orbitCoordinates F R z.2 z.1) = normalized (coordinateLebesgue F p) wc := by
    rw [hcoord]
    have h := congrArg (fun ν : Measure (Hermitian F p) => ν.map e) hrec
    rw [Measure.map_map e.continuous.measurable hbuild] at h
    exact h
  apply spectralLaw_normalized_density F R wc (hw.comp e.symm.continuous.measurable)
    κ sc (hselector.comp e.symm.continuous.measurable) q hq hqoff _ _ hae hrec'
  · intro lam hlam U
    simpa only [sc,Function.comp_apply,orbitCoordinates,e,
      LinearEquiv.coe_toContinuousLinearEquiv_symm', LinearEquiv.symm_apply_apply] using hselect lam hlam U
  · intro lam hlam U
    simpa only [wc,Function.comp_apply,orbitCoordinates,e,
      LinearEquiv.coe_toContinuousLinearEquiv_symm', LinearEquiv.symm_apply_apply] using hfactor lam hlam U

end Wishart.FieldCharts

namespace Wishart.ComplexMatrix
open Wishart.FieldCharts Wishart.FieldSpectral

theorem identityEigenLaw_normalized_density {p : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α) :
    (∫⁻ lam : Fin p → ℝ, ENNReal.ofReal (fieldEigenDensity 2 p α lam)) ≠ 0 ∧
    (∫⁻ lam : Fin p → ℝ, ENNReal.ofReal (fieldEigenDensity 2 p α lam)) ≠ ∞ ∧
    identityEigenLaw p α = WishartVerification.normalizedWeight volume (fieldEigenDensity 2 p α) := by
  apply spectral_density_from_hermitian ℂ realPartData
    (hermitianLebesgue p) (wishartWeight α 1) (measurable_wishartWeight α 1)
    (finiteDensity_wishart_standard p hα) ascendingValues (continuous_ascendingValues p).measurable
    (fieldEigenDensity 2 p α) (measurable_fieldEigenDensity 2 p α)
    (fieldEigenDensity_off_chamber (by decide) α) _ _
    (ae_identityEigenLaw_mem_chamber hα) (haar_ascending_spectral_reconstruction hα)
  · intro lam hlam U
    rw [ascendingValues_conjugate,ascendingValues_diagonal lam hlam.1.monotone]
  · intro lam hlam U
    rw [wishartWeight_conjugate_diagonal α U lam hlam.2,
      fieldEigenDensity_on_chamber (by decide) α lam hlam,Complex.finrank_real_complex]
    rw [← ENNReal.ofReal_mul (pow_nonneg (abs_nonneg _) 2)]
    congr 1
    rw [abs_of_pos (Finset.prod_pos fun ij _ => sub_pos.mpr (hlam.1 ij.2))]
    exact mul_comm _ _

theorem laguerreLaw_isProbability {p : ℕ} {α : ℝ} (hα : (p : ℝ) - 1 < α) :
    IsProbabilityMeasure (WishartVerification.normalizedWeight volume (fieldEigenDensity 2 p α)) := by
  rw [← (identityEigenLaw_normalized_density hα).2.2]
  exact identityEigenLaw_isProbability hα

theorem ae_laguerreLaw_mem_chamber {p : ℕ} {α : ℝ} (hα : (p : ℝ) - 1 < α) :
    ∀ᵐ lam ∂WishartVerification.normalizedWeight volume (fieldEigenDensity 2 p α),
      lam ∈ chamber p := by
  rw [← (identityEigenLaw_normalized_density hα).2.2]
  exact ae_identityEigenLaw_mem_chamber hα

theorem wishart_haar_laguerre_representation {p : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α) :
    ((TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) ℂ))).prod
      (WishartVerification.normalizedWeight volume (fieldEigenDensity 2 p α))).map
        (fun z => unitaryConjugate ℂ z.1 (diagonalHermitian ℂ z.2)) =
      wishartMeasure α (1 : Matrix (Fin p) (Fin p) ℂ) := by
  rw [← (identityEigenLaw_normalized_density hα).2.2]
  exact haar_ascending_spectral_reconstruction hα

theorem wishart_laguerre_haar_representation {p : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α) :
    ((WishartVerification.normalizedWeight volume (fieldEigenDensity 2 p α)).prod
      (TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) ℂ)))).map
        (fun z => unitaryConjugate ℂ z.2 (diagonalHermitian ℂ z.1)) =
      wishartMeasure α (1 : Matrix (Fin p) (Fin p) ℂ) := by
  letI := laguerreLaw_isProbability hα
  have hb : Measurable (fun z : unitary (Matrix (Fin p) (Fin p) ℂ) × (Fin p → ℝ) =>
      unitaryConjugate ℂ z.1 (diagonalHermitian ℂ z.2)) :=
    measurable_unitary_diagonal ℂ p
  have h := wishart_haar_laguerre_representation hα
  rw [← Measure.prod_swap (μ := WishartVerification.normalizedWeight volume (fieldEigenDensity 2 p α))
    (ν := TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) ℂ))),Measure.map_map hb measurable_swap] at h
  exact h

theorem identityEigenLaw_association {p : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α) (f g : (Fin p → ℝ) → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g)
    (hfm : MonotoneOn f (chamber p)) (hgm : MonotoneOn g (chamber p)) :
    (∫⁻ lam, f lam ∂identityEigenLaw p α) * (∫⁻ lam, g lam ∂identityEigenLaw p α) ≤
      ∫⁻ lam, f lam * g lam ∂identityEigenLaw p α := by
  obtain ⟨h0,ht,hlaw⟩ := identityEigenLaw_normalized_density hα
  rw [hlaw]
  exact WishartVerification.lemma_2_1_ennreal_association
    (Set.Ioi 0) measurableSet_Ioi (fun _ : Fin p => laguerreWeight 2 p α) 2
    (by norm_num) (fun _ => measurable_laguerreWeight 2 p α)
    (fun _ => laguerreWeight_nonneg 2 p α) h0 ht f g hf hg hfm hgm

end Wishart.ComplexMatrix

namespace Wishart.QuaternionMatrix
open scoped Matrix.Norms.Frobenius
open Wishart.FieldCharts Wishart.FieldSpectral

theorem identityEigenLaw_normalized_density {p : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α) :
    (∫⁻ lam : Fin p → ℝ, ENNReal.ofReal (fieldEigenDensity 4 p α lam)) ≠ 0 ∧
    (∫⁻ lam : Fin p → ℝ, ENNReal.ofReal (fieldEigenDensity 4 p α lam)) ≠ ∞ ∧
    identityEigenLaw p α = WishartVerification.normalizedWeight volume (fieldEigenDensity 4 p α) := by
  apply spectral_density_from_hermitian ℍ[ℝ] realPartData
    (hermitianLebesgue p) (wishartWeight α 1) (measurable_wishartWeight α 1)
    (finiteDensity_wishart_standard p hα) ascendingValues (continuous_ascendingValues p).measurable
    (fieldEigenDensity 4 p α) (measurable_fieldEigenDensity 4 p α)
    (fieldEigenDensity_off_chamber (by decide) α) _ _
    (ae_identityEigenLaw_mem_chamber hα) (haar_ascending_spectral_reconstruction hα)
  · intro lam hlam U
    rw [ascendingValues_conjugate,ascendingValues_diagonal lam hlam.1.monotone]
  · intro lam hlam U
    rw [wishartWeight_conjugate_diagonal α U lam hlam.2,
      fieldEigenDensity_on_chamber (by decide) α lam hlam,Quaternion.finrank_eq_four]
    rw [← ENNReal.ofReal_mul (pow_nonneg (abs_nonneg _) 4)]
    congr 1
    rw [abs_of_pos (Finset.prod_pos fun ij _ => sub_pos.mpr (hlam.1 ij.2))]
    exact mul_comm _ _

theorem laguerreLaw_isProbability {p : ℕ} {α : ℝ} (hα : (p : ℝ) - 1 < α) :
    IsProbabilityMeasure (WishartVerification.normalizedWeight volume (fieldEigenDensity 4 p α)) := by
  rw [← (identityEigenLaw_normalized_density hα).2.2]
  exact identityEigenLaw_isProbability hα

theorem ae_laguerreLaw_mem_chamber {p : ℕ} {α : ℝ} (hα : (p : ℝ) - 1 < α) :
    ∀ᵐ lam ∂WishartVerification.normalizedWeight volume (fieldEigenDensity 4 p α),
      lam ∈ chamber p := by
  rw [← (identityEigenLaw_normalized_density hα).2.2]
  exact ae_identityEigenLaw_mem_chamber hα

theorem wishart_haar_laguerre_representation {p : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α) :
    ((TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) ℍ[ℝ]))).prod
      (WishartVerification.normalizedWeight volume (fieldEigenDensity 4 p α))).map
        (fun z => unitaryConjugate ℍ[ℝ] z.1 (Wishart.FieldCharts.diagonalHermitian ℍ[ℝ] z.2)) =
      wishartMeasure α (1 : Matrix (Fin p) (Fin p) ℍ[ℝ]) := by
  rw [← (identityEigenLaw_normalized_density hα).2.2]
  exact haar_ascending_spectral_reconstruction hα

theorem wishart_laguerre_haar_representation {p : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α) :
    ((WishartVerification.normalizedWeight volume (fieldEigenDensity 4 p α)).prod
      (TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) ℍ[ℝ])))).map
        (fun z => unitaryConjugate ℍ[ℝ] z.2 (Wishart.FieldCharts.diagonalHermitian ℍ[ℝ] z.1)) =
      wishartMeasure α (1 : Matrix (Fin p) (Fin p) ℍ[ℝ]) := by
  letI := laguerreLaw_isProbability hα
  have hb : Measurable (fun z : unitary (Matrix (Fin p) (Fin p) ℍ[ℝ]) × (Fin p → ℝ) =>
      unitaryConjugate ℍ[ℝ] z.1 (Wishart.FieldCharts.diagonalHermitian ℍ[ℝ] z.2)) :=
    measurable_unitary_diagonal ℍ[ℝ] p
  have h := wishart_haar_laguerre_representation hα
  rw [← Measure.prod_swap (μ := WishartVerification.normalizedWeight volume (fieldEigenDensity 4 p α))
    (ν := TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) ℍ[ℝ]))),Measure.map_map hb measurable_swap] at h
  exact h

theorem identityEigenLaw_association {p : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α) (f g : (Fin p → ℝ) → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g)
    (hfm : MonotoneOn f (chamber p)) (hgm : MonotoneOn g (chamber p)) :
    (∫⁻ lam, f lam ∂identityEigenLaw p α) * (∫⁻ lam, g lam ∂identityEigenLaw p α) ≤
      ∫⁻ lam, f lam * g lam ∂identityEigenLaw p α := by
  obtain ⟨h0,ht,hlaw⟩ := identityEigenLaw_normalized_density hα
  rw [hlaw]
  exact WishartVerification.lemma_2_1_ennreal_association
    (Set.Ioi 0) measurableSet_Ioi (fun _ : Fin p => laguerreWeight 4 p α) 4
    (by norm_num) (fun _ => measurable_laguerreWeight 4 p α)
    (fun _ => laguerreWeight_nonneg 4 p α) h0 ht f g hf hg hfm hgm

end Wishart.QuaternionMatrix
end
end CanonicalSource19
