module

public import wishart.verified.field_residual09

@[expose] public section

/-!
# Literal mathematical audit targets for Theorem 7.1

The comparison and moment targets below quantify over the raw matrices,
shifts and profiles.  The permitted laws are written out, and probability
normalization is a conclusion of a separate density target.  In particular,
neither a normalized-law premise nor a conditional comparison premise is
inserted into the theorem.

The matrix boundary convention, real Gaussian component variance, exact
whitening formula and quaternion determinant interpretation are separate
theorem roots.  Their presence in the source files is not enough: the final
declaration and dependency audit includes these roots even when the proof
of the packaged comparison does not depend on them. Compilation checks the
proof bodies; the audit inspects the checked environment and records its
external-library boundary. The build receipt records successful execution.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical BigOperators Quaternion ENNReal ComplexOrder Ring Matrix MatrixOrder
  Matrix.Norms.L2Operator

namespace FieldSevenOneAudit

def complexPhi {k : ℕ} (h : (Fin k → ℝ) → ℝ)
    (S : Wishart.ComplexMatrix.Hermitian k) : ℝ :=
  Wishart.Spectral.spectralBoundaryValue h
    (Wishart.FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe S))

def quaternionPhi {k : ℕ} (h : (Fin k → ℝ) → ℝ)
    (S : Wishart.QuaternionMatrix.Hermitian k) : ℝ :=
  Wishart.Spectral.spectralBoundaryValue h
    (Wishart.QuaternionMatrix.orderedValues S)

theorem complex_positive_value {k : ℕ} (h : (Fin k → ℝ) → ℝ)
    (hc : ConvexOn ℝ univ h) (hm : Monotone h)
    (S : Wishart.ComplexMatrix.Hermitian k)
    (hS : (S : Matrix (Fin k) (Fin k) ℂ).PosDef) :
    complexPhi h S = Real.exp (h (fun i => Real.log
      (Wishart.FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe S) i))) :=
  Wishart.Spectral.spectralBoundaryValue_eq_on_positive hc hm
    (Wishart.FieldSpectral.orderedValues_pos hS)

theorem quaternion_positive_value {k : ℕ} (h : (Fin k → ℝ) → ℝ)
    (hc : ConvexOn ℝ univ h) (hm : Monotone h)
    (S : Wishart.QuaternionMatrix.Hermitian k)
    (hS : Wishart.QuaternionMatrix.PosDef S.val) :
    quaternionPhi h S = Real.exp (h (fun i => Real.log
      (Wishart.QuaternionMatrix.orderedValues S i))) :=
  Wishart.Spectral.spectralBoundaryValue_eq_on_positive hc hm
    (Wishart.QuaternionMatrix.orderedValues_pos S hS)

/-- This is the limit of the actual shifted matrix spectrum, including every
singular positive-semidefinite matrix, not just a coordinatewise convention. -/
theorem complex_matrix_boundary {k : ℕ} (h : (Fin k → ℝ) → ℝ)
    (hm : Monotone h) (S : Wishart.ComplexMatrix.Hermitian k)
    (hS : (S : Matrix (Fin k) (Fin k) ℂ).PosSemidef) :
    Tendsto (fun ε : ℝ => Real.exp (h (fun i => Real.log
      (Wishart.FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe
        (S + ε • (⟨1, Matrix.isHermitian_one⟩ : Wishart.ComplexMatrix.Hermitian k))) i))))
      (𝓝[>] 0) (𝓝 (complexPhi h S)) :=
  Wishart.FieldSpectral.boundary_eq_matrix_regularization hm S hS

theorem quaternion_matrix_boundary {k : ℕ} (h : (Fin k → ℝ) → ℝ)
    (hm : Monotone h) (S : Wishart.QuaternionMatrix.Hermitian k)
    (hS : Wishart.QuaternionMatrix.PosSemidef S.val) :
    Tendsto (fun ε : ℝ => Real.exp (h (fun i => Real.log
      (Wishart.QuaternionMatrix.orderedValues
        (S + ε • (⟨1, Matrix.isHermitian_one⟩ : Wishart.QuaternionMatrix.Hermitian k)) i))))
      (𝓝[>] 0) (𝓝 (quaternionPhi h S)) :=
  Wishart.QuaternionMatrix.boundary_eq_matrix_regularization hm S hS

theorem complex_whitening_formula {p k : ℕ}
    (Sigma : Matrix (Fin p) (Fin p) ℂ) (hSigma : Sigma.PosDef)
    (B : Matrix (Fin p) (Fin k) ℂ) (hB : Function.Injective B.mulVec)
    (X : Wishart.ComplexMatrix.Hermitian p) :
    (Wishart.ComplexMatrix.normalizedCompression B Sigma X :
      Matrix (Fin k) (Fin k) ℂ) =
      (CFC.sqrt (Bᴴ * Sigma * B))⁻¹ * (Bᴴ * X.val * B) *
        (CFC.sqrt (Bᴴ * Sigma * B))⁻¹ :=
  Wishart.ComplexMatrix.normalizedCompression_eq_formula hSigma hB X

theorem quaternion_whitening_formula {p k : ℕ}
    (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ])
    (hSigma : Wishart.QuaternionMatrix.PosDef Sigma)
    (B : Matrix (Fin p) (Fin k) ℍ[ℝ]) (hB : Function.Injective B.mulVec)
    (X : Wishart.QuaternionMatrix.Hermitian p) :
    (Wishart.QuaternionMatrix.normalizedCompression B Sigma X :
      Matrix (Fin k) (Fin k) ℍ[ℝ]) =
      (Wishart.QuaternionMatrix.sqrt (Bᴴ * Sigma * B))⁻¹ʳ * (Bᴴ * X.val * B) *
        (Wishart.QuaternionMatrix.sqrt (Bᴴ * Sigma * B))⁻¹ʳ :=
  Wishart.QuaternionMatrix.normalizedCompression_eq_formula hSigma hB X

theorem complex_determinant_eigenvalues {k : ℕ}
    (S : Wishart.ComplexMatrix.Hermitian k) :
    Wishart.ComplexMatrix.realDeterminant S.val =
      ∏ i, Wishart.FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe S) i :=
  Wishart.ComplexMatrix.realDeterminant_eq_prod_orderedValues S

/-- The determinant used in the quaternion density and moments is the
product of the `k` genuine quaternion Hermitian eigenvalues, with zero
eigenvalues retained.  The proof is through actual quaternion diagonalization. -/
theorem quaternion_determinant_eigenvalues {k : ℕ}
    (S : Wishart.QuaternionMatrix.Hermitian k)
    (hS : Wishart.QuaternionMatrix.PosSemidef S.val) :
    Wishart.QuaternionMatrix.positiveDeterminant S.val =
      ∏ i, Wishart.QuaternionMatrix.orderedValues S i :=
  Wishart.QuaternionMatrix.positiveDeterminant_eq_mooreDeterminant S hS

/-- The representation-defined quaternion cone is the ordinary cone of
nonnegative Hermitian quadratic forms on right column vectors. -/
theorem quaternion_positive_cone {k : ℕ} (A : Matrix (Fin k) (Fin k) ℍ[ℝ]) :
    Wishart.QuaternionMatrix.PosSemidef A ↔ A.IsHermitian ∧
      ∀ v : Fin k → ℍ[ℝ], 0 ≤ (star v ⬝ᵥ (A *ᵥ v)).re :=
  Wishart.QuaternionMatrix.posSemidef_iff_quadratic A

theorem quaternion_strict_positive_cone {k : ℕ} (A : Matrix (Fin k) (Fin k) ℍ[ℝ]) :
    Wishart.QuaternionMatrix.PosDef A ↔ A.IsHermitian ∧
      ∀ v : Fin k → ℍ[ℝ], v ≠ 0 → 0 < (star v ⬝ᵥ (A *ᵥ v)).re :=
  Wishart.QuaternionMatrix.posDef_iff_quadratic A

/-- Full column rank uses right coefficients: no nonzero quaternion column
vector is killed by the actual matrix-vector multiplication. -/
theorem quaternion_full_column_rank {p k : ℕ} (B : Matrix (Fin p) (Fin k) ℍ[ℝ]) :
    Wishart.QuaternionMatrix.FullColumnRank B ↔ Function.Injective B.mulVec :=
  Iff.rfl

theorem quaternion_rank_complex_representation {p k : ℕ}
    (B : Matrix (Fin p) (Fin k) ℍ[ℝ]) :
    Wishart.QuaternionMatrix.FullColumnRank B ↔
      Function.Injective (Wishart.QuaternionMatrix.complexRepresentation B).mulVec :=
  Wishart.QuaternionMatrix.fullColumnRank_iff_complexRepresentation B

/-- Equality of the entire real coordinate law also asserts independence.
Every orthonormal basis is allowed, including the usual component basis. -/
theorem complex_component_law {p : ℕ} {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (Wishart.FieldGaussian.Row ℂ p)) :
    (Wishart.FieldGaussian.gaussianRowWithFactor ℂ
      (1 : Matrix (Fin p) (Fin p) ℂ)).map (fun z i => b.repr z i) =
      Measure.pi (fun _ : ι => gaussianReal 0 (1 / 2)) :=
  Wishart.FieldGaussian.complex_standard_row_coordinate_law b

theorem quaternion_component_law {p : ℕ} {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (Wishart.FieldGaussian.Row ℍ[ℝ] p)) :
    (Wishart.FieldGaussian.gaussianRowWithFactor ℍ[ℝ]
      (1 : Matrix (Fin p) (Fin p) ℍ[ℝ])).map (fun z i => b.repr z i) =
      Measure.pi (fun _ : ι => gaussianReal 0 (1 / 4)) :=
  Wishart.FieldGaussian.quaternion_standard_row_coordinate_law b

theorem complex_covariance_factor {p : ℕ} (Sigma : Matrix (Fin p) (Fin p) ℂ)
    (hSigma : Sigma.PosDef) : (CFC.sqrt Sigma)ᴴ * CFC.sqrt Sigma = Sigma := by
  rw [(Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg Sigma)).isHermitian.eq,
    CFC.sqrt_mul_sqrt_self Sigma hSigma.posSemidef.nonneg]

theorem quaternion_covariance_factor {p : ℕ}
    (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ])
    (hSigma : Wishart.QuaternionMatrix.PosDef Sigma) :
    (Wishart.QuaternionMatrix.sqrt Sigma)ᴴ * Wishart.QuaternionMatrix.sqrt Sigma = Sigma := by
  rw [hSigma.sqrt.isHermitian.eq, Wishart.QuaternionMatrix.sqrt_mul_self hSigma.posSemidef]

/-- The integer alternative is literally `Zᴴ Z` with independent Gaussian
rows, including sample sizes smaller than the ambient dimension. -/
theorem complex_gram_image {p : ℕ} (n : ℕ) (Sigma : Matrix (Fin p) (Fin p) ℂ) :
    Wishart.ComplexMatrix.gramMeasure n Sigma =
      (Measure.pi (fun _ : Fin n => Wishart.FieldGaussian.gaussianRowWithFactor ℂ
        (CFC.sqrt Sigma))).map
          (fun Z : Fin n → Wishart.FieldGaussian.Row ℂ p =>
            (⟨(Matrix.of (fun i j => Z i j))ᴴ * Matrix.of (fun i j => Z i j),
              (Matrix.isHermitian_conjTranspose_mul_self _).isSelfAdjoint⟩ :
                Wishart.ComplexMatrix.Hermitian p)) := rfl

theorem quaternion_gram_image {p : ℕ} (n : ℕ)
    (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) :
    Wishart.QuaternionMatrix.gramMeasure n Sigma =
      (Measure.pi (fun _ : Fin n => Wishart.FieldGaussian.gaussianRowWithFactor ℍ[ℝ]
        (Wishart.QuaternionMatrix.sqrt Sigma))).map
          (fun Z : Fin n → Wishart.FieldGaussian.Row ℍ[ℝ] p =>
            (⟨(Matrix.of (fun i j => Z i j))ᴴ * Matrix.of (fun i j => Z i j),
              (Matrix.isHermitian_conjTranspose_mul_self _).isSelfAdjoint⟩ :
                Wishart.QuaternionMatrix.Hermitian p)) := rfl

/-- Legacy checkpoint identifier. The field density is equation (20) of the
attached manuscript; correctly numbered aliases are supplied below. -/
def complexDensity19 {p : ℕ} (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℂ)
    (X : Wishart.ComplexMatrix.Hermitian p) : ℝ≥0∞ :=
  if (X : Matrix (Fin p) (Fin p) ℂ).PosDef then
    ENNReal.ofReal (Wishart.ComplexMatrix.realDeterminant X.val ^
      ((2 : ℝ) / 2 * (α - p + 1) - 1) *
      Real.exp (-(2 : ℝ) / 2 * ((Sigma⁻¹ * X.val).trace).re)) else 0

def quaternionDensity19 {p : ℕ} (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ])
    (X : Wishart.QuaternionMatrix.Hermitian p) : ℝ≥0∞ :=
  if Wishart.QuaternionMatrix.PosDef X.val then
    ENNReal.ofReal ((∏ i, Wishart.QuaternionMatrix.orderedValues X i) ^
      ((4 : ℝ) / 2 * (α - p + 1) - 1) *
      Real.exp (-(4 : ℝ) / 2 * ((Sigma⁻¹ʳ * X.val).trace).re)) else 0

theorem complexDensity19_eq_weight {p : ℕ} (α : ℝ)
    (Sigma : Matrix (Fin p) (Fin p) ℂ) :
    complexDensity19 α Sigma = Wishart.ComplexMatrix.wishartWeight α Sigma := by
  funext X
  by_cases hX : (X : Matrix (Fin p) (Fin p) ℂ).PosDef
  · rw [complexDensity19, if_pos hX]
    exact (Wishart.ComplexMatrix.wishartWeight_eq_formula α Sigma X hX).symm
  · simp only [complexDensity19, Wishart.ComplexMatrix.wishartWeight, if_neg hX]

theorem quaternionDensity19_eq_weight {p : ℕ} (α : ℝ)
    (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) :
    quaternionDensity19 α Sigma = Wishart.QuaternionMatrix.wishartWeight α Sigma := by
  funext X
  by_cases hX : Wishart.QuaternionMatrix.PosDef (X : Matrix (Fin p) (Fin p) ℍ[ℝ])
  · rw [quaternionDensity19, if_pos hX,
      ← quaternion_determinant_eigenvalues X hX.posSemidef]
    exact (Wishart.QuaternionMatrix.wishartWeight_eq_formula α Sigma X hX).symm
  · simp only [quaternionDensity19, Wishart.QuaternionMatrix.wishartWeight, if_neg hX]

theorem complex_density_19 {p : ℕ} (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℂ)
    (hα : (p : ℝ) - 1 < α) (hSigma : Sigma.PosDef) :
    let Z := ∫⁻ X, complexDensity19 α Sigma X ∂Wishart.ComplexMatrix.hermitianLebesgue p
    0 < Z ∧ Z < ⊤ ∧ IsProbabilityMeasure (Wishart.ComplexMatrix.wishartMeasure α Sigma) ∧
      Wishart.ComplexMatrix.wishartMeasure α Sigma =
        Z⁻¹ • (Wishart.ComplexMatrix.hermitianLebesgue p).withDensity (complexDensity19 α Sigma) := by
  rw [complexDensity19_eq_weight]
  have h := Wishart.theorem_7_1_complex_normalization p α Sigma hα hSigma
  exact ⟨h.1, h.2.1, h.2.2, rfl⟩

theorem quaternion_density_19 {p : ℕ} (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ])
    (hα : (p : ℝ) - 1 < α) (hSigma : Wishart.QuaternionMatrix.PosDef Sigma) :
    let Z := ∫⁻ X, quaternionDensity19 α Sigma X ∂Wishart.QuaternionMatrix.hermitianLebesgue p
    0 < Z ∧ Z < ⊤ ∧ IsProbabilityMeasure (Wishart.QuaternionMatrix.wishartMeasure α Sigma) ∧
      Wishart.QuaternionMatrix.wishartMeasure α Sigma =
        Z⁻¹ • (Wishart.QuaternionMatrix.hermitianLebesgue p).withDensity
          (quaternionDensity19 α Sigma) := by
  rw [quaternionDensity19_eq_weight]
  have h := Wishart.theorem_7_1_quaternion_normalization p α Sigma hα hSigma
  exact ⟨h.1, h.2.1, h.2.2, rfl⟩

/-- The literal complex density in equation (20), with the older checkpoint
name retained solely for source compatibility. -/
abbrev complexDensity20 {p : ℕ} (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℂ) :
    Wishart.ComplexMatrix.Hermitian p → ℝ≥0∞ := complexDensity19 α Sigma

/-- The literal quaternion density in equation (20), expressed through its
genuine quaternion eigenvalue product rather than the doubled complex list. -/
abbrev quaternionDensity20 {p : ℕ} (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) :
    Wishart.QuaternionMatrix.Hermitian p → ℝ≥0∞ := quaternionDensity19 α Sigma

theorem complexDensity20_eq_weight {p : ℕ} (α : ℝ)
    (Sigma : Matrix (Fin p) (Fin p) ℂ) :
    complexDensity20 α Sigma = Wishart.ComplexMatrix.wishartWeight α Sigma :=
  complexDensity19_eq_weight α Sigma

theorem quaternionDensity20_eq_weight {p : ℕ} (α : ℝ)
    (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) :
    quaternionDensity20 α Sigma = Wishart.QuaternionMatrix.wishartWeight α Sigma :=
  quaternionDensity19_eq_weight α Sigma

theorem complex_density_20 {p : ℕ} (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℂ)
    (hα : (p : ℝ) - 1 < α) (hSigma : Sigma.PosDef) :
    let Z := ∫⁻ X, complexDensity20 α Sigma X ∂Wishart.ComplexMatrix.hermitianLebesgue p
    0 < Z ∧ Z < ⊤ ∧ IsProbabilityMeasure (Wishart.ComplexMatrix.wishartMeasure α Sigma) ∧
      Wishart.ComplexMatrix.wishartMeasure α Sigma =
        Z⁻¹ • (Wishart.ComplexMatrix.hermitianLebesgue p).withDensity (complexDensity20 α Sigma) :=
  complex_density_19 α Sigma hα hSigma

theorem quaternion_density_20 {p : ℕ} (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ])
    (hα : (p : ℝ) - 1 < α) (hSigma : Wishart.QuaternionMatrix.PosDef Sigma) :
    let Z := ∫⁻ X, quaternionDensity20 α Sigma X ∂Wishart.QuaternionMatrix.hermitianLebesgue p
    0 < Z ∧ Z < ⊤ ∧ IsProbabilityMeasure (Wishart.QuaternionMatrix.wishartMeasure α Sigma) ∧
      Wishart.QuaternionMatrix.wishartMeasure α Sigma =
        Z⁻¹ • (Wishart.QuaternionMatrix.hermitianLebesgue p).withDensity
          (quaternionDensity20 α Sigma) :=
  quaternion_density_19 α Sigma hα hSigma

def complexFactor {p k : ℕ} (B : Matrix (Fin p) (Fin k) ℂ)
    (Sigma : Matrix (Fin p) (Fin p) ℂ) (c : ℝ) (h : (Fin k → ℝ) → ℝ)
    (X : Wishart.ComplexMatrix.Hermitian p) : ℝ :=
  complexPhi h (Wishart.ComplexMatrix.normalizedCompression B Sigma X + c •
    (⟨1, Matrix.isHermitian_one⟩ : Wishart.ComplexMatrix.Hermitian k))

def quaternionFactor {p k : ℕ} (B : Matrix (Fin p) (Fin k) ℍ[ℝ])
    (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) (c : ℝ) (h : (Fin k → ℝ) → ℝ)
    (X : Wishart.QuaternionMatrix.Hermitian p) : ℝ :=
  quaternionPhi h (Wishart.QuaternionMatrix.normalizedCompression B Sigma X + c •
    (⟨1, Matrix.isHermitian_one⟩ : Wishart.QuaternionMatrix.Hermitian k))

def ComplexSelectedChainStatement : Prop :=
  ∀ (p : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (Sigma : Matrix (Fin p) (Fin p) ℂ), Sigma.PosDef →
    ∀ (k : ι → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℂ),
      (∀ i, Function.Injective (B i).mulVec) →
      ∀ (c : ι → ℝ), (∀ i, 0 ≤ c i) →
      ∀ (h : ∀ i, (Fin (k i) → ℝ) → ℝ),
        (∀ i, ConvexOn ℝ univ (h i)) → (∀ i, Monotone (h i)) →
        (∀ i, Wishart.Spectral.SymmetricProfile (h i)) →
        ∀ μ : Measure (Wishart.ComplexMatrix.Hermitian p),
          ((∃ α : ℝ, (p : ℝ) - 1 < α ∧ μ = Wishart.ComplexMatrix.wishartMeasure α Sigma) ∨
            (∃ n : ℕ, 1 ≤ n ∧ μ = Wishart.ComplexMatrix.gramMeasure n Sigma)) →
          ∀ (J : Finset ι) (j : ι), j ∈ J →
            (∏ i ∈ J, ∫⁻ X, ENNReal.ofReal (complexFactor (B i) Sigma (c i) (h i) X) ∂μ) ≤
              (∫⁻ X, ENNReal.ofReal (complexFactor (B j) Sigma (c j) (h j) X) ∂μ) *
                (∫⁻ X, ENNReal.ofReal (∏ i ∈ J.erase j,
                  complexFactor (B i) Sigma (c i) (h i) X) ∂μ) ∧
            (∫⁻ X, ENNReal.ofReal (complexFactor (B j) Sigma (c j) (h j) X) ∂μ) *
              (∫⁻ X, ENNReal.ofReal (∏ i ∈ J.erase j,
                complexFactor (B i) Sigma (c i) (h i) X) ∂μ) ≤
              ∫⁻ X, ENNReal.ofReal (∏ i ∈ J,
                complexFactor (B i) Sigma (c i) (h i) X) ∂μ

theorem complex_selected_chain : ComplexSelectedChainStatement := by
  intro p ι _ _ Sigma hSigma k B hB c hc h hconv hm hsymm μ hμ J j hj
  let F : Wishart.ComplexSpectralFamily p ι :=
    ⟨k, B, hB, c, hc, h, hconv, hm, hsymm⟩
  have hchain := Wishart.theorem_7_1_complex p ι Sigma hSigma F μ hμ J j hj
  exact ⟨hchain.2, hchain.1⟩

def QuaternionSelectedChainStatement : Prop :=
  ∀ (p : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]), Wishart.QuaternionMatrix.PosDef Sigma →
    ∀ (k : ι → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℍ[ℝ]),
      (∀ i, Function.Injective (B i).mulVec) →
      ∀ (c : ι → ℝ), (∀ i, 0 ≤ c i) →
      ∀ (h : ∀ i, (Fin (k i) → ℝ) → ℝ),
        (∀ i, ConvexOn ℝ univ (h i)) → (∀ i, Monotone (h i)) →
        (∀ i, Wishart.Spectral.SymmetricProfile (h i)) →
        ∀ μ : Measure (Wishart.QuaternionMatrix.Hermitian p),
          ((∃ α : ℝ, (p : ℝ) - 1 < α ∧ μ = Wishart.QuaternionMatrix.wishartMeasure α Sigma) ∨
            (∃ n : ℕ, 1 ≤ n ∧ μ = Wishart.QuaternionMatrix.gramMeasure n Sigma)) →
          ∀ (J : Finset ι) (j : ι), j ∈ J →
            (∏ i ∈ J, ∫⁻ X, ENNReal.ofReal (quaternionFactor (B i) Sigma (c i) (h i) X) ∂μ) ≤
              (∫⁻ X, ENNReal.ofReal (quaternionFactor (B j) Sigma (c j) (h j) X) ∂μ) *
                (∫⁻ X, ENNReal.ofReal (∏ i ∈ J.erase j,
                  quaternionFactor (B i) Sigma (c i) (h i) X) ∂μ) ∧
            (∫⁻ X, ENNReal.ofReal (quaternionFactor (B j) Sigma (c j) (h j) X) ∂μ) *
              (∫⁻ X, ENNReal.ofReal (∏ i ∈ J.erase j,
                quaternionFactor (B i) Sigma (c i) (h i) X) ∂μ) ≤
              ∫⁻ X, ENNReal.ofReal (∏ i ∈ J,
                quaternionFactor (B i) Sigma (c i) (h i) X) ∂μ

theorem quaternion_selected_chain : QuaternionSelectedChainStatement := by
  intro p ι _ _ Sigma hSigma k B hB c hc h hconv hm hsymm μ hμ J j hj
  let F : Wishart.QuaternionSpectralFamily p ι :=
    ⟨k, B, hB, c, hc, h, hconv, hm, hsymm⟩
  have hchain := Wishart.theorem_7_1_quaternion p ι Sigma hSigma F μ hμ J j hj
  exact ⟨hchain.2, hchain.1⟩

def ComplexFinitePowersStatement : Prop :=
  ∀ (p : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (Sigma : Matrix (Fin p) (Fin p) ℂ), Sigma.PosDef →
    ∀ (k : ι → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℂ),
      (∀ i, Function.Injective (B i).mulVec) →
      ∀ (c ν : ι → ℝ), (∀ i, 0 ≤ c i) → (∀ i, 0 ≤ ν i) →
      ∀ μ : Measure (Wishart.ComplexMatrix.Hermitian p),
        ((∃ α : ℝ, (p : ℝ) - 1 < α ∧ μ = Wishart.ComplexMatrix.wishartMeasure α Sigma) ∨
          (∃ n : ℕ, 1 ≤ n ∧ μ = Wishart.ComplexMatrix.gramMeasure n Sigma)) →
        (∫⁻ X : Wishart.ComplexMatrix.Hermitian p, ENNReal.ofReal (∏ i, Wishart.ComplexMatrix.realDeterminant
          ((B i)ᴴ * X.val * B i + c i • ((B i)ᴴ * Sigma * B i)) ^ ν i) ∂μ) < ⊤

theorem complex_finite_powers : ComplexFinitePowersStatement :=
  Wishart.theorem_7_1_complex_finite_powers

def QuaternionFinitePowersStatement : Prop :=
  ∀ (p : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]), Wishart.QuaternionMatrix.PosDef Sigma →
    ∀ (k : ι → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℍ[ℝ]),
      (∀ i, Function.Injective (B i).mulVec) →
      ∀ (c ν : ι → ℝ), (∀ i, 0 ≤ c i) → (∀ i, 0 ≤ ν i) →
      ∀ μ : Measure (Wishart.QuaternionMatrix.Hermitian p),
        ((∃ α : ℝ, (p : ℝ) - 1 < α ∧ μ = Wishart.QuaternionMatrix.wishartMeasure α Sigma) ∨
          (∃ n : ℕ, 1 ≤ n ∧ μ = Wishart.QuaternionMatrix.gramMeasure n Sigma)) →
        (∫⁻ X : Wishart.QuaternionMatrix.Hermitian p, ENNReal.ofReal (∏ i, Wishart.QuaternionMatrix.positiveDeterminant
          ((B i)ᴴ * X.val * B i + c i • ((B i)ᴴ * Sigma * B i)) ^ ν i) ∂μ) < ⊤

theorem quaternion_finite_powers : QuaternionFinitePowersStatement :=
  Wishart.theorem_7_1_quaternion_finite_powers

#check Wishart.QuaternionMatrix.flat_orderedValues_eq_double
#check Wishart.QuaternionMatrix.exists_conjugate_diagonal
#check Wishart.FieldGaussian.gaussianRowWithFactor_one_map_factor
#check Wishart.ComplexMatrix.gramMeasure_covariance_law
#check Wishart.QuaternionMatrix.gramMeasure_covariance_law



end FieldSevenOneAudit
