module

public import wishart.verified.field_residual03
public import wishart.verified.field_frontier03
public import Mathlib.Analysis.InnerProductSpace.PiL2

/- Recovered canonical proof stage; see verification/recovery-patches.json. -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxErrors 1000

section CanonicalSource30
/- Source: Wishart/FieldSingleRowExtended.lean -/



/-!
# Nonnegative-integral form of the actual single-row comparison

Each finite spectral approximation has a polynomial envelope, so its Gaussian
row integral is finite. The Bochner comparison can therefore be converted to
the extended nonnegative integral exactly. This is the form used by Tonelli
when mixing arbitrarily distributed positive-semidefinite background matrices.
-/

noncomputable section
open Matrix MeasureTheory Set
open scoped Classical Quaternion ComplexOrder ENNReal
namespace Wishart.FieldGaussian
open scoped Matrix.Norms.Frobenius
open WishartVerification Wishart.Spectral

theorem complex_single_row_spectral_lintegral_comparison {r m : ℕ} {ι : Type*} [Fintype ι]
    (R : Matrix (Fin r) (Fin m) ℂ) (v : Row ℂ m)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin m) (Fin (k i)) ℂ)
    (Q : ∀ i, FieldSpectral.Hermitian ℂ (k i))
    (hQ : ∀ i, (Q i : Matrix (Fin (k i)) (Fin (k i)) ℂ).PosSemidef)
    (h : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hc : ∀ i, ConvexOn ℝ univ (h i)) (hm : ∀ i, Monotone (h i)) (L : ι → ℕ) :
    MonotoneOn (fun t : ℝ => ∫⁻ z,
      ENNReal.ofReal (∏ i, complexFaceApprox (hc i) (hm i) (L i)
        (compressedRowGram ℂ (Q i) (B i) (z + Real.sqrt t • v)))
      ∂gaussianRowWithFactor ℂ R) (Ici 0) := by
  let G : Row ℂ m × ℂ → ℝ := fun w => ∏ i,
    complexFaceApprox (hc i) (hm i) (L i)
      (compressedHermitianRowUpdate ℂ (Q i) (B i) v w)
  have hcont : Continuous G := continuous_finsetProd _ fun i _ =>
    (continuous_complexFaceApprox (hc i) (hm i) (L i)).comp
      (continuous_compressedHermitianRowUpdate ℂ (Q i) (B i) v)
  have hpoly : JointPolynomialBound G := JointPolynomialBound.finset_prod
    Finset.univ _ (fun i _ => polynomial_complexFaceApprox_row
      (hc i) (hm i) (L i) (Q i) (hQ i) (B i) v)
  have hint (t : ℝ) : Integrable (fun z => ∏ i,
      complexFaceApprox (hc i) (hm i) (L i)
        (compressedRowGram ℂ (Q i) (B i) (z + Real.sqrt t • v)))
        (gaussianRowWithFactor ℂ R) := by
    simpa only [G, compressedHermitianRowUpdate_real] using
      integrable_polynomial_section (norm_allFiniteMoments ℂ R) hcont hpoly
        (Real.sqrt t • (1 : ℂ))
  have hnonneg (t : ℝ) (z : Row ℂ m) : 0 ≤ ∏ i,
      complexFaceApprox (hc i) (hm i) (L i)
        (compressedRowGram ℂ (Q i) (B i) (z + Real.sqrt t • v)) := by
    apply Finset.prod_nonneg
    intro i hi
    apply complexFaceApprox_nonneg
    change ((Q i : Matrix (Fin (k i)) (Fin (k i)) ℂ) +
      rowGram ℂ (rowFactorCLM ℂ (B i) (z + Real.sqrt t • v))).PosSemidef
    rw [rowGram_eq_matrix]
    exact (hQ i).add (Matrix.posSemidef_conjTranspose_mul_self _)
  intro s hs t ht hst
  dsimp only
  rw [← ofReal_integral_eq_lintegral_ofReal (hint s) (ae_of_all _ (hnonneg s)),
    ← ofReal_integral_eq_lintegral_ofReal (hint t) (ae_of_all _ (hnonneg t))]
  exact ENNReal.ofReal_le_ofReal
    (complex_single_row_spectral_comparison R v k B Q hQ h hc hm L hs ht hst)

theorem quaternion_single_row_spectral_lintegral_comparison {r m : ℕ} {ι : Type*} [Fintype ι]
    (R : Matrix (Fin r) (Fin m) ℍ[ℝ]) (v : Row ℍ[ℝ] m)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin m) (Fin (k i)) ℍ[ℝ])
    (Q : ∀ i, QuaternionMatrix.Hermitian (k i))
    (hQ : ∀ i, QuaternionMatrix.PosSemidef (Q i).val)
    (h : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hc : ∀ i, ConvexOn ℝ univ (h i)) (hm : ∀ i, Monotone (h i)) (L : ι → ℕ) :
    MonotoneOn (fun t : ℝ => ∫⁻ z,
      ENNReal.ofReal (∏ i, quaternionFaceApprox (hc i) (hm i) (L i)
        (compressedRowGram ℍ[ℝ] (Q i) (B i) (z + Real.sqrt t • v)))
      ∂gaussianRowWithFactor ℍ[ℝ] R) (Ici 0) := by
  let G : Row ℍ[ℝ] m × ℍ[ℝ] → ℝ := fun w => ∏ i,
    quaternionFaceApprox (hc i) (hm i) (L i)
      (compressedHermitianRowUpdate ℍ[ℝ] (Q i) (B i) v w)
  have hcont : Continuous G := continuous_finsetProd _ fun i _ =>
    (continuous_quaternionFaceApprox (hc i) (hm i) (L i)).comp
      (continuous_compressedHermitianRowUpdate ℍ[ℝ] (Q i) (B i) v)
  have hpoly : JointPolynomialBound G := JointPolynomialBound.finset_prod
    Finset.univ _ (fun i _ => polynomial_quaternionFaceApprox_row
      (hc i) (hm i) (L i) (Q i) (hQ i) (B i) v)
  have hint (t : ℝ) : Integrable (fun z => ∏ i,
      quaternionFaceApprox (hc i) (hm i) (L i)
        (compressedRowGram ℍ[ℝ] (Q i) (B i) (z + Real.sqrt t • v)))
        (gaussianRowWithFactor ℍ[ℝ] R) := by
    simpa only [G, compressedHermitianRowUpdate_real] using
      integrable_polynomial_section (norm_allFiniteMoments ℍ[ℝ] R) hcont hpoly
        (Real.sqrt t • (1 : ℍ[ℝ]))
  have hnonneg (t : ℝ) (z : Row ℍ[ℝ] m) : 0 ≤ ∏ i,
      quaternionFaceApprox (hc i) (hm i) (L i)
        (compressedRowGram ℍ[ℝ] (Q i) (B i) (z + Real.sqrt t • v)) := by
    apply Finset.prod_nonneg
    intro i hi
    apply quaternionFaceApprox_nonneg
    change QuaternionMatrix.PosSemidef ((Q i : Matrix (Fin (k i)) (Fin (k i)) ℍ[ℝ]) +
      rowGram ℍ[ℝ] (rowFactorCLM ℍ[ℝ] (B i) (z + Real.sqrt t • v)))
    rw [rowGram_eq_matrix]
    exact (hQ i).add (QuaternionMatrix.posSemidef_gram _)
  intro s hs t ht hst
  dsimp only
  rw [← ofReal_integral_eq_lintegral_ofReal (hint s) (ae_of_all _ (hnonneg s)),
    ← ofReal_integral_eq_lintegral_ofReal (hint t) (ae_of_all _ (hnonneg t))]
  exact ENNReal.ofReal_le_ofReal
    (quaternion_single_row_spectral_comparison R v k B Q hQ h hc hm L hs ht hst)

end Wishart.FieldGaussian
end
end CanonicalSource30

section CanonicalSource31
/- Source: Wishart/FieldMultipleRows.lean -/



/-!
# Coordinate monotonicity of the actual field Gaussian row mixtures

All factors may use different, overlapping compression matrices. A fixed PSD
offset is permitted in each factor. Successively conditioning on the other
Gaussian rows supplies PSD offsets to the proved scalar-field comparison.
The conclusion is an extended expectation and includes zero eigenvalues.
-/

noncomputable section
open Matrix MeasureTheory Set
open scoped Classical Quaternion ComplexOrder ENNReal
namespace Wishart.FieldGaussian
open scoped Matrix.Norms.Frobenius
open WishartVerification Wishart.Spectral

section Contribution
variable (F : Type*) [NormedDivisionRing F]
  [StarRing F] [CStarRing F]
  [InnerProductSpace ℝ F] [StarModule ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] {m k : ℕ}
  [SMulCommClass ℝ F F] [IsScalarTower ℝ F F]

@[reducible] local instance compatibleScalarAlgebraStage4_1 : NormedAlgebra ℝ F where
  toAlgebra := Algebra.ofModule (fun r x y => smul_mul_assoc r x y)
    (fun r x y => mul_smul_comm r x y)
  norm_smul_le r x := (norm_smul r x).le


def compressedRowContribution (B : Matrix (Fin m) (Fin k) F) (z : Row F m) :
    selfAdjoint.submodule ℝ (Matrix (Fin k) (Fin k) F) :=
  ⟨rowGram F (rowFactorCLM F B z), by
    rw [rowGram_eq_matrix]
    exact Matrix.isHermitian_conjTranspose_mul_self _⟩

theorem continuous_compressedRowContribution (B : Matrix (Fin m) (Fin k) F) :
    Continuous (compressedRowContribution F B) := by
  apply Continuous.subtype_mk
  unfold rowGram
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (((PiLp.continuous_apply 2 (fun _ : Fin k => F) i).comp
    (rowFactorCLM F B).continuous).star).mul
      ((PiLp.continuous_apply 2 (fun _ : Fin k => F) j).comp
        (rowFactorCLM F B).continuous)

theorem compressedRowGram_eq_add
    (Q : selfAdjoint.submodule ℝ (Matrix (Fin k) (Fin k) F))
    (B : Matrix (Fin m) (Fin k) F) (z : Row F m) :
    compressedRowGram F Q B z = Q + compressedRowContribution F B z := by
  apply Subtype.ext
  rfl

end Contribution

theorem complex_multiple_rows_spectral_comparison {r m n : ℕ} {ι : Type*} [Fintype ι]
    (R : Matrix (Fin r) (Fin m) ℂ) (v : Fin n → Row ℂ m)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin m) (Fin (k i)) ℂ)
    (Q : ∀ i, FieldSpectral.Hermitian ℂ (k i))
    (hQ : ∀ i, (Q i : Matrix (Fin (k i)) (Fin (k i)) ℂ).PosSemidef)
    (h : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hc : ∀ i, ConvexOn ℝ univ (h i)) (hm : ∀ i, Monotone (h i)) (L : ι → ℕ) :
    MonotoneOn (fun lam : Fin n → ℝ => ∫⁻ z,
      ENNReal.ofReal (∏ i, complexFaceApprox (hc i) (hm i) (L i)
        (Q i + ∑ a, compressedRowContribution ℂ (B i) (z a + Real.sqrt (lam a) • v a)))
      ∂Measure.pi (fun _ : Fin n => gaussianRowWithFactor ℂ R)) (Ici 0) := by
  let E := ∀ i, FieldSpectral.Hermitian ℂ (k i)
  let P : E → Prop := fun A => ∀ i, (A i : Matrix (Fin (k i)) (Fin (k i)) ℂ).PosSemidef
  let G : Row ℂ m → E := fun z i => compressedRowContribution ℂ (B i) z
  let H : E → ℝ≥0∞ := fun A => ENNReal.ofReal
    (∏ i, complexFaceApprox (hc i) (hm i) (L i) (A i))
  have hzero : P 0 := fun i => Matrix.PosSemidef.zero
  have hadd : ∀ A C, P A → P C → P (A + C) := fun A C hA hC i => (hA i).add (hC i)
  have hG : Measurable G := measurable_pi_iff.mpr fun i =>
    (continuous_compressedRowContribution ℂ (B i)).measurable
  have hrow : ∀ z, P (G z) := by
    intro z i
    change (rowGram ℂ (rowFactorCLM ℂ (B i) z)).PosSemidef
    rw [rowGram_eq_matrix]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  have hH : Measurable H := by
    apply Measurable.ennreal_ofReal
    apply Finset.measurable_prod
    intro i hi
    exact (continuous_complexFaceApprox (hc i) (hm i) (L i)).measurable.comp (measurable_pi_apply i)
  have hsingle : ∀ A, P A → ∀ w : Row ℂ m,
      MonotoneOn (fun t : ℝ => ∫⁻ z, H (A + G (z + Real.sqrt t • w))
        ∂gaussianRowWithFactor ℂ R) (Ici 0) := by
    intro A hA w
    simpa only [E, H, G, Pi.add_apply, compressedRowGram_eq_add] using
      complex_single_row_spectral_lintegral_comparison R w k B A hA h hc hm L
  have hmono := monotone_lintegral_shiftedRowSum (gaussianRowWithFactor ℂ R)
    hzero hadd G hG hrow H hH hsingle Q hQ v
  simpa only [E, H, G, shiftedRowSum, Pi.add_apply, Finset.sum_apply] using hmono

theorem quaternion_multiple_rows_spectral_comparison {r m n : ℕ} {ι : Type*} [Fintype ι]
    (R : Matrix (Fin r) (Fin m) ℍ[ℝ]) (v : Fin n → Row ℍ[ℝ] m)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin m) (Fin (k i)) ℍ[ℝ])
    (Q : ∀ i, QuaternionMatrix.Hermitian (k i))
    (hQ : ∀ i, QuaternionMatrix.PosSemidef (Q i).val)
    (h : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hc : ∀ i, ConvexOn ℝ univ (h i)) (hm : ∀ i, Monotone (h i)) (L : ι → ℕ) :
    MonotoneOn (fun lam : Fin n → ℝ => ∫⁻ z,
      ENNReal.ofReal (∏ i, quaternionFaceApprox (hc i) (hm i) (L i)
        (Q i + ∑ a, compressedRowContribution ℍ[ℝ] (B i) (z a + Real.sqrt (lam a) • v a)))
      ∂Measure.pi (fun _ : Fin n => gaussianRowWithFactor ℍ[ℝ] R)) (Ici 0) := by
  let E := ∀ i, QuaternionMatrix.Hermitian (k i)
  let P : E → Prop := fun A => ∀ i, QuaternionMatrix.PosSemidef (A i).val
  let G : Row ℍ[ℝ] m → E := fun z i => compressedRowContribution ℍ[ℝ] (B i) z
  let H : E → ℝ≥0∞ := fun A => ENNReal.ofReal
    (∏ i, quaternionFaceApprox (hc i) (hm i) (L i) (A i))
  have hzero : P 0 := by
    intro i
    change QuaternionMatrix.PosSemidef (0 : Matrix (Fin (k i)) (Fin (k i)) ℍ[ℝ])
    rw [QuaternionMatrix.PosSemidef, QuaternionMatrix.complexRepresentation_zero]
    exact Matrix.PosSemidef.zero
  have hadd : ∀ A C, P A → P C → P (A + C) := fun A C hA hC i => (hA i).add (hC i)
  have hG : Measurable G := measurable_pi_iff.mpr fun i =>
    (continuous_compressedRowContribution ℍ[ℝ] (B i)).measurable
  have hrow : ∀ z, P (G z) := by
    intro z i
    change QuaternionMatrix.PosSemidef (rowGram ℍ[ℝ] (rowFactorCLM ℍ[ℝ] (B i) z))
    rw [rowGram_eq_matrix]
    exact QuaternionMatrix.posSemidef_gram _
  have hH : Measurable H := by
    apply Measurable.ennreal_ofReal
    apply Finset.measurable_prod
    intro i hi
    exact (continuous_quaternionFaceApprox (hc i) (hm i) (L i)).measurable.comp (measurable_pi_apply i)
  have hsingle : ∀ A, P A → ∀ w : Row ℍ[ℝ] m,
      MonotoneOn (fun t : ℝ => ∫⁻ z, H (A + G (z + Real.sqrt t • w))
        ∂gaussianRowWithFactor ℍ[ℝ] R) (Ici 0) := by
    intro A hA w
    simpa only [E, H, G, Pi.add_apply, compressedRowGram_eq_add] using
      quaternion_single_row_spectral_lintegral_comparison R w k B A hA h hc hm L
  have hmono := monotone_lintegral_shiftedRowSum (gaussianRowWithFactor ℍ[ℝ] R)
    hzero hadd G hG hrow H hH hsingle Q hQ v
  simpa only [E, H, G, shiftedRowSum, Pi.add_apply, Finset.sum_apply] using hmono

end Wishart.FieldGaussian
end
end CanonicalSource31

section CanonicalSource32
/- Source: Wishart/FieldSpectralSchur.lean -/




/-!
# Spectral Schur matrices as sums of shifted rows

The leading block is the actual unitary reconstruction of its real spectrum.
The square-root identity is proved from positivity and uniqueness. After the
Gaussian block is rotated by the same frame, the Schur matrix is a fixed
trailing background plus the Gram matrix of `[diag(sqrt λ) Uᴴ, Z]`.
This is the algebraic link to the unrestricted field row comparison.
-/

noncomputable section
open Matrix MeasureTheory
open scoped Classical Quaternion ComplexOrder MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace Wishart.FieldCharts

variable (F : Type*) [NormedRing F] [NormedAlgebra ℝ F]
  [StarRing F] [CStarRing F] [StarModule ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

theorem realDiagonal_sqrt_mul_self {p : ℕ} (lam : Fin p → ℝ) (hlam : ∀ i, 0 ≤ lam i) :
    realDiagonal F (fun i => Real.sqrt (lam i)) *
      realDiagonal F (fun i => Real.sqrt (lam i)) = realDiagonal F lam := by
  rw [realDiagonal, realDiagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [← map_mul, ← pow_two, Real.sq_sqrt (hlam i)]

theorem unitaryConjugate_square {p : ℕ} (U : unitary (Matrix (Fin p) (Fin p) F))
    (lam : Fin p → ℝ) (hlam : ∀ i, 0 ≤ lam i) :
    (unitaryConjugate F U (diagonalHermitian F (fun i => Real.sqrt (lam i))) :
      Matrix (Fin p) (Fin p) F) *
      (unitaryConjugate F U (diagonalHermitian F (fun i => Real.sqrt (lam i))) :
        Matrix (Fin p) (Fin p) F) = unitaryConjugate F U (diagonalHermitian F lam) := by
  change (U.val * realDiagonal F (fun i => Real.sqrt (lam i)) * star U.val) *
    (U.val * realDiagonal F (fun i => Real.sqrt (lam i)) * star U.val) = _
  calc
    _ = U.val *
        (realDiagonal F (fun i => Real.sqrt (lam i)) *
          realDiagonal F (fun i => Real.sqrt (lam i))) * star U.val := by
      simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (star U.val) U.val,
        U.property.1, Matrix.one_mul]
    _ = _ := by rw [realDiagonal_sqrt_mul_self F lam hlam]; rfl

def horizontalJoin {r p q : ℕ} (A : Matrix (Fin r) (Fin p) F)
    (B : Matrix (Fin r) (Fin q) F) : Matrix (Fin r) (Fin (p + q)) F :=
  Matrix.of fun i j => Sum.elim (A i) (B i) (finSumFinEquiv.symm j)

theorem horizontalJoin_gram {r p q : ℕ} (A : Matrix (Fin r) (Fin p) F)
    (B : Matrix (Fin r) (Fin q) F) :
    (horizontalJoin F A B)ᴴ * horizontalJoin F A B =
      (Matrix.fromBlocks (Aᴴ * A) (Aᴴ * B) (Bᴴ * A) (Bᴴ * B)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm := by
  ext i j
  generalize hi : (finSumFinEquiv.symm i : Fin p ⊕ Fin q) = a
  generalize hj : (finSumFinEquiv.symm j : Fin p ⊕ Fin q) = b
  cases a <;> cases b <;>
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, horizontalJoin,
      Matrix.of_apply, Matrix.submatrix_apply, hi, hj, Sum.elim_inl, Sum.elim_inr,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

def trailingBackground {p q : ℕ} (W : Hermitian F q) : Hermitian F (p + q) :=
  Wishart.FieldHermitian.fromBlocks F (0, 0, W)

def spectralSchurGram {p q : ℕ} (U : unitary (Matrix (Fin p) (Fin p) F))
    (lam : Fin p → ℝ) (Z : Matrix (Fin p) (Fin q) F) : Hermitian F (p + q) :=
  let A := horizontalJoin F (realDiagonal F (fun i => Real.sqrt (lam i)) * star U.val) Z
  ⟨Aᴴ * A, Matrix.isHermitian_conjTranspose_mul_self A⟩

end Wishart.FieldCharts

namespace Wishart.ComplexMatrix
open scoped Matrix.Norms.L2Operator
open Wishart.FieldCharts
variable {p q : ℕ}

theorem posSemidef_unitary_diagonal (U : unitary (Matrix (Fin p) (Fin p) ℂ))
    (lam : Fin p → ℝ) (hlam : ∀ i, 0 ≤ lam i) :
    (unitaryConjugate ℂ U (diagonalHermitian ℂ lam) : Matrix (Fin p) (Fin p) ℂ).PosSemidef := by
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  exact Matrix.PosSemidef.diagonal fun i => RCLike.nonneg_iff.mpr ⟨hlam i, by simp⟩

theorem sqrt_unitary_diagonal (U : unitary (Matrix (Fin p) (Fin p) ℂ))
    (lam : Fin p → ℝ) (hlam : ∀ i, 0 ≤ lam i) :
    CFC.sqrt (unitaryConjugate ℂ U (diagonalHermitian ℂ lam) : Matrix (Fin p) (Fin p) ℂ) =
      unitaryConjugate ℂ U (diagonalHermitian ℂ (fun i => Real.sqrt (lam i))) :=
  CFC.sqrt_unique (unitaryConjugate_square ℂ U lam hlam)
    (posSemidef_unitary_diagonal U _ (fun i => Real.sqrt_nonneg _)).nonneg

theorem schurInput_unitary_diagonal (U : unitary (Matrix (Fin p) (Fin p) ℂ))
    (lam : Fin p → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (W : Hermitian q) (Z : Matrix (Fin p) (Fin q) ℂ) :
    schurInput (unitaryConjugate ℂ U (diagonalHermitian ℂ lam)) W
      (U.val * Z) =
      trailingBackground ℂ W + spectralSchurGram ℂ U lam Z := by
  apply Subtype.ext
  simp only [Submodule.coe_add]
  rw [show (spectralSchurGram ℂ U lam Z : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) =
    (horizontalJoin ℂ (realDiagonal ℂ (fun i => Real.sqrt (lam i)) * star U.val) Z)ᴴ *
      horizontalJoin ℂ (realDiagonal ℂ (fun i => Real.sqrt (lam i)) * star U.val) Z from rfl,
    horizontalJoin_gram]
  have hD : (realDiagonal ℂ (fun i => Real.sqrt (lam i)))ᴴ =
      realDiagonal ℂ (fun i => Real.sqrt (lam i)) :=
    (WishartVerification.hermitian_matrix_coe (diagonalHermitian ℂ _)).eq
  have htop : (realDiagonal ℂ (fun i => Real.sqrt (lam i)) * star U.val)ᴴ *
      (realDiagonal ℂ (fun i => Real.sqrt (lam i)) * star U.val) =
        (unitaryConjugate ℂ U (diagonalHermitian ℂ lam) : Matrix (Fin p) (Fin p) ℂ) := by
    rw [Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose, hD]
    calc
      _ = U.val *
          (realDiagonal ℂ (fun i => Real.sqrt (lam i)) *
            realDiagonal ℂ (fun i => Real.sqrt (lam i))) * star U.val := by simp only [Matrix.mul_assoc, Matrix.star_eq_conjTranspose]
      _ = _ := by rw [realDiagonal_sqrt_mul_self ℂ lam hlam]; rfl
  simp only [schurInput]
  rw [sqrt_unitary_diagonal U lam hlam]
  simp only [trailingBackground, Wishart.FieldHermitian.fromBlocks,
    Submodule.coe_zero, ← Matrix.submatrix_add, ← Matrix.fromBlocks_add,
    zero_add, add_zero, Matrix.conjTranspose_zero]
  congr 1
  simp only [unitaryConjugate, Wishart.FieldCharts.diagonalHermitian,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hD, Matrix.mul_assoc]
  have hu : U.valᴴ * U.val = 1 := U.property.1
  have hd := realDiagonal_sqrt_mul_self ℂ lam hlam
  simp only [← Matrix.mul_assoc U.valᴴ U.val, hu, Matrix.one_mul,
    ← Matrix.mul_assoc (realDiagonal ℂ (fun i => Real.sqrt (lam i)))
      (realDiagonal ℂ (fun i => Real.sqrt (lam i))), hd]
  apply Matrix.ext
  intro i j
  generalize hi : (finSumFinEquiv.symm i : Fin p ⊕ Fin q) = ai
  generalize hj : (finSumFinEquiv.symm j : Fin p ⊕ Fin q) = aj
  cases ai <;> cases aj <;> simp [Matrix.submatrix_apply, Matrix.add_apply, hi, hj]


end Wishart.ComplexMatrix

namespace Wishart.QuaternionMatrix
open scoped Matrix.Norms.Frobenius
open Wishart.FieldCharts
variable {p q : ℕ}

theorem posSemidef_unitary_diagonal (U : unitary (Matrix (Fin p) (Fin p) ℍ[ℝ]))
    (lam : Fin p → ℝ) (hlam : ∀ i, 0 ≤ lam i) :
    PosSemidef (unitaryConjugate ℍ[ℝ] U (Wishart.FieldCharts.diagonalHermitian ℍ[ℝ] lam)).val := by
  have hD : PosSemidef (realDiagonal ℍ[ℝ] lam) := by
    unfold PosSemidef realDiagonal
    change (complexRepresentation (Matrix.diagonal (fun i => (lam i : ℍ[ℝ])))).PosSemidef
    rw [complexRepresentation_diagonal]
    exact Matrix.PosSemidef.diagonal fun i => RCLike.nonneg_iff.mpr ⟨hlam i.1, by simp⟩
  simpa only [unitaryConjugate, Wishart.FieldCharts.diagonalHermitian, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] using
    hD.congruence (star U.val)

theorem sqrt_unitary_diagonal (U : unitary (Matrix (Fin p) (Fin p) ℍ[ℝ]))
    (lam : Fin p → ℝ) (hlam : ∀ i, 0 ≤ lam i) :
    sqrt (unitaryConjugate ℍ[ℝ] U (Wishart.FieldCharts.diagonalHermitian ℍ[ℝ] lam)) =
      (unitaryConjugate ℍ[ℝ] U (Wishart.FieldCharts.diagonalHermitian ℍ[ℝ] (fun i => Real.sqrt (lam i)))).val := by
  apply complexRepresentation_injective
  rw [complexRepresentation_sqrt (posSemidef_unitary_diagonal U lam hlam)]
  apply CFC.sqrt_unique
  · rw [← complexRepresentation_mul, unitaryConjugate_square ℍ[ℝ] U lam hlam]
  · exact Matrix.PosSemidef.nonneg (posSemidef_unitary_diagonal U _ (fun i => Real.sqrt_nonneg _))

theorem schurInput_unitary_diagonal (U : unitary (Matrix (Fin p) (Fin p) ℍ[ℝ]))
    (lam : Fin p → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (W : Hermitian q) (Z : Matrix (Fin p) (Fin q) ℍ[ℝ]) :
    schurInput (unitaryConjugate ℍ[ℝ] U (Wishart.FieldCharts.diagonalHermitian ℍ[ℝ] lam)) W
      (U.val * Z) =
      trailingBackground ℍ[ℝ] W + spectralSchurGram ℍ[ℝ] U lam Z := by
  apply Subtype.ext
  simp only [Submodule.coe_add]
  rw [show (spectralSchurGram ℍ[ℝ] U lam Z : Matrix (Fin (p + q)) (Fin (p + q)) ℍ[ℝ]) =
    (horizontalJoin ℍ[ℝ] (realDiagonal ℍ[ℝ] (fun i => Real.sqrt (lam i)) * star U.val) Z)ᴴ *
      horizontalJoin ℍ[ℝ] (realDiagonal ℍ[ℝ] (fun i => Real.sqrt (lam i)) * star U.val) Z from rfl,
    horizontalJoin_gram]
  have hD : (realDiagonal ℍ[ℝ] (fun i => Real.sqrt (lam i)))ᴴ =
      realDiagonal ℍ[ℝ] (fun i => Real.sqrt (lam i)) :=
    (WishartVerification.hermitian_matrix_coe (Wishart.FieldCharts.diagonalHermitian ℍ[ℝ] _)).eq
  have htop : (realDiagonal ℍ[ℝ] (fun i => Real.sqrt (lam i)) * star U.val)ᴴ *
      (realDiagonal ℍ[ℝ] (fun i => Real.sqrt (lam i)) * star U.val) =
        (unitaryConjugate ℍ[ℝ] U (Wishart.FieldCharts.diagonalHermitian ℍ[ℝ] lam) : Matrix (Fin p) (Fin p) ℍ[ℝ]) := by
    rw [Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose, hD]
    calc
      _ = U.val *
          (realDiagonal ℍ[ℝ] (fun i => Real.sqrt (lam i)) *
            realDiagonal ℍ[ℝ] (fun i => Real.sqrt (lam i))) * star U.val := by simp only [Matrix.mul_assoc, Matrix.star_eq_conjTranspose]
      _ = _ := by rw [realDiagonal_sqrt_mul_self ℍ[ℝ] lam hlam]; rfl
  simp only [schurInput]
  rw [sqrt_unitary_diagonal U lam hlam]
  simp only [trailingBackground, Wishart.FieldHermitian.fromBlocks,
    Submodule.coe_zero, ← Matrix.submatrix_add, ← Matrix.fromBlocks_add,
    zero_add, add_zero, Matrix.conjTranspose_zero]
  congr 1
  simp only [unitaryConjugate, Wishart.FieldCharts.diagonalHermitian,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hD, Matrix.mul_assoc]
  have hu : U.valᴴ * U.val = 1 := U.property.1
  have hd := realDiagonal_sqrt_mul_self ℍ[ℝ] lam hlam
  simp only [← Matrix.mul_assoc U.valᴴ U.val, hu, Matrix.one_mul,
    ← Matrix.mul_assoc (realDiagonal ℍ[ℝ] (fun i => Real.sqrt (lam i)))
      (realDiagonal ℍ[ℝ] (fun i => Real.sqrt (lam i))), hd]
  apply Matrix.ext
  intro i j
  generalize hi : (finSumFinEquiv.symm i : Fin p ⊕ Fin q) = ai
  generalize hj : (finSumFinEquiv.symm j : Fin p ⊕ Fin q) = aj
  cases ai <;> cases aj <;> simp [Matrix.submatrix_apply, Matrix.add_apply, hi, hj]


end Wishart.QuaternionMatrix
end
end CanonicalSource32

section CanonicalSource33
set_option maxHeartbeats 400000
/- Source: Wishart/FieldSchurRows.lean -/




/-!
# Padded rows and arbitrary compressions of a Schur matrix

The singular row covariance used below is the explicit trailing-coordinate
selector. The row-law change is a pushforward of the actual Gaussian source.
Thus no full-rank assumption on the noise is introduced when conditioning on
the leading block.
-/

noncomputable section
open Matrix MeasureTheory Set
open scoped Classical Quaternion ComplexOrder ENNReal

namespace Wishart.FieldGaussian
open scoped Matrix.Norms.Frobenius
open Wishart.FieldCharts Wishart.Spectral

variable (F : Type*) [NormedDivisionRing F]
  [StarRing F] [CStarRing F]
  [InnerProductSpace ℝ F] [StarModule ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  [SMulCommClass ℝ F F] [IsScalarTower ℝ F F]

@[reducible] local instance compatibleScalarAlgebraStage4_2 : NormedAlgebra ℝ F where
  toAlgebra := Algebra.ofModule (fun r x y => smul_mul_assoc r x y)
    (fun r x y => mul_smul_comm r x y)
  norm_smul_le r x := (norm_smul r x).le


def compress {m k : ℕ} (B : Matrix (Fin m) (Fin k) F)
    (X : Hermitian F m) : Hermitian F k :=
  ⟨Bᴴ * (X : Matrix (Fin m) (Fin m) F) * B,
    Matrix.isHermitian_conjTranspose_mul_mul B (WishartVerification.hermitian_matrix_coe X)⟩

theorem continuous_compress {m k : ℕ} (B : Matrix (Fin m) (Fin k) F) :
    Continuous (compress F B) := by
  apply Continuous.subtype_mk
  fun_prop

@[simp] theorem compress_add {m k : ℕ} (B : Matrix (Fin m) (Fin k) F)
    (X Y : Hermitian F m) : compress F B (X + Y) = compress F B X + compress F B Y := by
  apply Subtype.ext
  simp only [compress, Submodule.coe_add, Matrix.mul_add, Matrix.add_mul]

def trailingSelector (p q : ℕ) : Matrix (Fin q) (Fin (p + q)) F :=
  horizontalJoin F 0 1

def leadingRows {p q : ℕ} (U : unitary (Matrix (Fin p) (Fin p) F)) :
    Fin p → Row F (p + q) := fun a =>
  WithLp.toLp 2 (horizontalJoin F (star U.val) (0 : Matrix (Fin p) (Fin q) F) a)

theorem shiftedRows_horizontalJoin {p q : ℕ}
    (U : unitary (Matrix (Fin p) (Fin p) F)) (lam : Fin p → ℝ)
    (z : Fin p → Row F q) :
    rowsMatrix F (fun a => rowFactorCLM F (trailingSelector F p q) (z a) +
      Real.sqrt (lam a) • leadingRows F U a) =
        horizontalJoin F (realDiagonal F (fun a => Real.sqrt (lam a)) * star U.val)
          (rowsMatrix F z) := by
  ext a j
  change (rowFactorCLM F (trailingSelector F p q) (z a)) j +
    Real.sqrt (lam a) • (leadingRows F U a) j = _
  generalize hj : (finSumFinEquiv.symm j : Fin p ⊕ Fin q) = b
  cases b with
  | inl i =>
    simp [rowFactorCLM_apply, trailingSelector, leadingRows, horizontalJoin,
      hj, rowsMatrix, realDiagonal, Matrix.diagonal_mul, Algebra.smul_def]
  | inr i =>
    simp [rowFactorCLM_apply, trailingSelector, leadingRows, horizontalJoin,
      hj, rowsMatrix, Matrix.one_apply]

theorem compress_rowsGram {n m k : ℕ} (B : Matrix (Fin m) (Fin k) F)
    (z : Fin n → Row F m) :
    compress F B (rowsGram F z) = ∑ a, compressedRowContribution F B (z a) := by
  apply Subtype.ext
  rw [show (compress F B (rowsGram F z) : Matrix (Fin k) (Fin k) F) =
    (rowsGram F (fun a => rowFactorCLM F B (z a)) : Matrix (Fin k) (Fin k) F) from
      (rowsGram_factor F B z).symm]
  ext i j
  simp only [rowsGram, rowsMatrix, Matrix.of_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Submodule.coe_sum, Matrix.sum_apply,
    compressedRowContribution, rowGram]

theorem compress_spectralSchurGram {p q k : ℕ}
    (B : Matrix (Fin (p + q)) (Fin k) F)
    (U : unitary (Matrix (Fin p) (Fin p) F)) (lam : Fin p → ℝ)
    (z : Fin p → Row F q) :
    compress F B (spectralSchurGram F U lam (rowsMatrix F z)) =
      ∑ a, compressedRowContribution F B
        (rowFactorCLM F (trailingSelector F p q) (z a) +
          Real.sqrt (lam a) • leadingRows F U a) := by
  rw [← compress_rowsGram]
  apply congrArg (compress F B)
  apply Subtype.ext
  change _ = (rowsMatrix F (fun a => rowFactorCLM F (trailingSelector F p q) (z a) + Real.sqrt (lam a) • leadingRows F U a))ᴴ * (rowsMatrix F (fun a => rowFactorCLM F (trailingSelector F p q) (z a) + Real.sqrt (lam a) • leadingRows F U a))
  rw [shiftedRows_horizontalJoin]
  rfl

theorem trailingBackground_eq_compress {p q : ℕ} (W : Hermitian F q) :
    trailingBackground F (p := p) W = compress F (trailingSelector F p q) W := by
  apply Subtype.ext
  ext i j
  generalize hi : (finSumFinEquiv.symm i : Fin p ⊕ Fin q) = a
  generalize hj : (finSumFinEquiv.symm j : Fin p ⊕ Fin q) = b
  cases a <;> cases b <;>
    simp [trailingBackground, Wishart.FieldHermitian.fromBlocks, compress,
      trailingSelector, horizontalJoin, Matrix.mul_apply, Matrix.conjTranspose_apply,
      hi, hj, Matrix.one_apply, star_zero, star_one]
  simp_rw [apply_ite star]
  simp

theorem lintegral_matrixGaussian_eq_padded_rows {p q : ℕ}
    (f : Matrix (Fin p) (Fin q) F → ℝ≥0∞) (g : (Fin p → Row F (p + q)) → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g)
    (heq : ∀ z : Fin p → Row F q, f (rowsMatrix F z) =
      g (fun a => rowFactorCLM F (trailingSelector F p q) (z a))) :
    (∫⁻ Z, f Z ∂matrixGaussian F p q) =
      ∫⁻ z, g z ∂Measure.pi (fun _ : Fin p => gaussianRowWithFactor F (trailingSelector F p q)) := by
  rw [matrixGaussian, lintegral_map hf (continuous_rowsMatrix F p q).measurable,
    ← gaussianRowsWithFactor_one_map_factor F (trailingSelector F p q)]
  have hmap : Measurable (fun z : Fin p → Row F q =>
      fun a => rowFactorCLM F (trailingSelector F p q) (z a)) :=
    measurable_pi_iff.mpr fun a =>
      (rowFactorCLM F (trailingSelector F p q)).continuous.measurable.comp (measurable_pi_apply a)
  rw [lintegral_map hg hmap]
  exact lintegral_congr heq

end Wishart.FieldGaussian

namespace Wishart.ComplexMatrix
open scoped Matrix.Norms.L2Operator
open Wishart.FieldGaussian Wishart.FieldCharts Wishart.Spectral

set_option backward.isDefEq.respectTransparency true in
theorem monotone_spectralSchur_average {p q : ℕ} {ι : Type*} [Fintype ι]
    (U : unitary (Matrix (Fin p) (Fin p) ℂ))
    (W : Hermitian q) (hW : (W : Matrix (Fin q) (Fin q) ℂ).PosSemidef)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin (p + q)) (Fin (k i)) ℂ)
    (Q : ∀ i, Hermitian (k i))
    (hQ : ∀ i, (Q i : Matrix (Fin (k i)) (Fin (k i)) ℂ).PosSemidef)
    (h : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hc : ∀ i, ConvexOn ℝ univ (h i)) (hm : ∀ i, Monotone (h i)) (L : ι → ℕ) :
    MonotoneOn (fun lam : Fin p → ℝ => ∫⁻ Z,
      ENNReal.ofReal (∏ i, complexFaceApprox (hc i) (hm i) (L i)
        (Q i + compress ℂ (B i) (trailingBackground ℂ W + spectralSchurGram ℂ U lam Z)))
      ∂matrixGaussian ℂ p q) (Ici 0) := by
  let Q' := fun i => Q i + compress ℂ (B i) (trailingBackground ℂ (p := p) W)
  have hback : (trailingBackground ℂ (p := p) W : Matrix (Fin (p + q)) (Fin (p + q)) ℂ).PosSemidef := by
    rw [show trailingBackground ℂ (p := p) W = compress ℂ (trailingSelector ℂ p q) W from trailingBackground_eq_compress ℂ W]
    exact hW.conjTranspose_mul_mul_same _
  have hQ' : ∀ i, (Q' i : Matrix (Fin (k i)) (Fin (k i)) ℂ).PosSemidef :=
    fun i => (hQ i).add (hback.conjTranspose_mul_mul_same (B i))
  have hmono := complex_multiple_rows_spectral_comparison
    (trailingSelector ℂ p q) (leadingRows ℂ U) k B Q' hQ' h hc hm L
  have heq (lam : Fin p → ℝ) :
      (∫⁻ Z, ENNReal.ofReal (∏ i, complexFaceApprox (hc i) (hm i) (L i)
        (Q i + compress ℂ (B i) (trailingBackground ℂ W + spectralSchurGram ℂ U lam Z)))
        ∂matrixGaussian ℂ p q) =
      ∫⁻ z, ENNReal.ofReal (∏ i, complexFaceApprox (hc i) (hm i) (L i)
        (Q' i + ∑ a, compressedRowContribution ℂ (B i)
          (z a + Real.sqrt (lam a) • leadingRows ℂ U a)))
        ∂Measure.pi (fun _ : Fin p => gaussianRowWithFactor ℂ (trailingSelector ℂ p q)) := by
    apply lintegral_matrixGaussian_eq_padded_rows ℂ
    · apply Measurable.ennreal_ofReal
      apply Finset.measurable_prod
      intro i hi
      apply (continuous_complexFaceApprox (hc i) (hm i) (L i)).measurable.comp
      apply Measurable.add measurable_const
      apply (continuous_compress ℂ (B i)).measurable.comp
      apply Measurable.add measurable_const
      apply Measurable.subtype_mk
      have hj : Continuous (fun Z : Matrix (Fin p) (Fin q) ℂ =>
          horizontalJoin ℂ (realDiagonal ℂ (fun i => Real.sqrt (lam i)) * star U.val) Z) := by
        apply continuous_pi
        intro a
        apply continuous_pi
        intro j
        simp only [horizontalJoin, Matrix.of_apply]
        cases finSumFinEquiv.symm j <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> fun_prop
      exact (show Continuous (fun Z : Matrix (Fin p) (Fin q) ℂ =>
        (horizontalJoin ℂ (realDiagonal ℂ (fun i => Real.sqrt (lam i)) * star U.val) Z)ᴴ *
          horizontalJoin ℂ (realDiagonal ℂ (fun i => Real.sqrt (lam i)) * star U.val) Z) by fun_prop).measurable
    · apply Measurable.ennreal_ofReal
      apply Finset.measurable_prod
      intro i hi
      apply (continuous_complexFaceApprox (hc i) (hm i) (L i)).measurable.comp
      apply Measurable.add measurable_const
      apply Finset.measurable_sum
      intro a ha
      exact (continuous_compressedRowContribution ℂ (B i)).measurable.comp
        ((measurable_pi_apply a).add measurable_const)
    · intro z
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      congr 1
      have hg : compress ℂ (B i) (spectralSchurGram ℂ U lam (rowsMatrix ℂ z)) =
          ∑ a, compressedRowContribution ℂ (B i)
            (rowFactorCLM ℂ (trailingSelector ℂ p q) (z a) +
              Real.sqrt (lam a) • leadingRows ℂ U a) := by
        have hgram := compress_spectralSchurGram ℂ (B i) U lam z
        simpa only [spectralSchurGram, realDiagonal,
          Algebra.algebraMap_eq_smul_one] using hgram
      rw [compress_add]
      calc
        _ = Q i + (compress ℂ (B i) (trailingBackground ℂ W) +
            ∑ a, compressedRowContribution ℂ (B i)
              (rowFactorCLM ℂ (trailingSelector ℂ p q) (z a) +
                Real.sqrt (lam a) • leadingRows ℂ U a)) := by
          rw [hg]
        _ = _ := (add_assoc _ _ _).symm
  simpa only [heq] using hmono

end Wishart.ComplexMatrix

namespace Wishart.QuaternionMatrix
open scoped Matrix.Norms.Frobenius
open Wishart.FieldGaussian Wishart.FieldCharts Wishart.Spectral

set_option backward.isDefEq.respectTransparency true in
theorem monotone_spectralSchur_average {p q : ℕ} {ι : Type*} [Fintype ι]
    (U : unitary (Matrix (Fin p) (Fin p) ℍ[ℝ]))
    (W : Hermitian q) (hW : PosSemidef W.val)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin (p + q)) (Fin (k i)) ℍ[ℝ])
    (Q : ∀ i, Hermitian (k i)) (hQ : ∀ i, PosSemidef (Q i).val)
    (h : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hc : ∀ i, ConvexOn ℝ univ (h i)) (hm : ∀ i, Monotone (h i)) (L : ι → ℕ) :
    MonotoneOn (fun lam : Fin p → ℝ => ∫⁻ Z,
      ENNReal.ofReal (∏ i, quaternionFaceApprox (hc i) (hm i) (L i)
        (Q i + compress ℍ[ℝ] (B i) (trailingBackground ℍ[ℝ] W + spectralSchurGram ℍ[ℝ] U lam Z)))
      ∂matrixGaussian ℍ[ℝ] p q) (Ici 0) := by
  let Q' := fun i => Q i + compress ℍ[ℝ] (B i) (trailingBackground ℍ[ℝ] (p := p) W)
  have hback : PosSemidef (trailingBackground ℍ[ℝ] (p := p) W).val := by
    rw [show trailingBackground ℍ[ℝ] (p := p) W = compress ℍ[ℝ] (trailingSelector ℍ[ℝ] p q) W from trailingBackground_eq_compress ℍ[ℝ] W]
    exact hW.congruence _
  have hQ' : ∀ i, PosSemidef (Q' i).val :=
    fun i => (hQ i).add (hback.congruence (B i))
  have hmono := quaternion_multiple_rows_spectral_comparison
    (trailingSelector ℍ[ℝ] p q) (leadingRows ℍ[ℝ] U) k B Q' hQ' h hc hm L
  have heq (lam : Fin p → ℝ) :
      (∫⁻ Z, ENNReal.ofReal (∏ i, quaternionFaceApprox (hc i) (hm i) (L i)
        (Q i + compress ℍ[ℝ] (B i) (trailingBackground ℍ[ℝ] W + spectralSchurGram ℍ[ℝ] U lam Z)))
        ∂matrixGaussian ℍ[ℝ] p q) =
      ∫⁻ z, ENNReal.ofReal (∏ i, quaternionFaceApprox (hc i) (hm i) (L i)
        (Q' i + ∑ a, compressedRowContribution ℍ[ℝ] (B i)
          (z a + Real.sqrt (lam a) • leadingRows ℍ[ℝ] U a)))
        ∂Measure.pi (fun _ : Fin p => gaussianRowWithFactor ℍ[ℝ] (trailingSelector ℍ[ℝ] p q)) := by
    apply lintegral_matrixGaussian_eq_padded_rows ℍ[ℝ]
    · apply Measurable.ennreal_ofReal
      apply Finset.measurable_prod
      intro i hi
      apply (continuous_quaternionFaceApprox (hc i) (hm i) (L i)).measurable.comp
      apply Continuous.measurable
      apply Continuous.add continuous_const
      apply (continuous_compress ℍ[ℝ] (B i)).comp
      apply Continuous.add continuous_const
      apply Continuous.subtype_mk
      have hj : Continuous (fun Z : Matrix (Fin p) (Fin q) ℍ[ℝ] =>
          horizontalJoin ℍ[ℝ] (realDiagonal ℍ[ℝ] (fun i => Real.sqrt (lam i)) * star U.val) Z) := by
        apply continuous_pi
        intro a
        apply continuous_pi
        intro j
        simp only [horizontalJoin, Matrix.of_apply]
        cases finSumFinEquiv.symm j <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> fun_prop
      exact (show Continuous (fun Z : Matrix (Fin p) (Fin q) ℍ[ℝ] =>
        (horizontalJoin ℍ[ℝ] (realDiagonal ℍ[ℝ] (fun i => Real.sqrt (lam i)) * star U.val) Z)ᴴ *
          horizontalJoin ℍ[ℝ] (realDiagonal ℍ[ℝ] (fun i => Real.sqrt (lam i)) * star U.val) Z) by fun_prop)
    · apply Measurable.ennreal_ofReal
      apply Finset.measurable_prod
      intro i hi
      apply (continuous_quaternionFaceApprox (hc i) (hm i) (L i)).measurable.comp
      apply Continuous.measurable
      apply Continuous.add continuous_const
      apply continuous_finsetSum
      intro a ha
      exact (continuous_compressedRowContribution ℍ[ℝ] (B i)).comp
        ((continuous_apply a).add continuous_const)
    · intro z
      apply congrArg ENNReal.ofReal
      apply Finset.prod_congr rfl
      intro i hi
      apply congrArg (quaternionFaceApprox (hc i) (hm i) (L i))
      have hg : compress ℍ[ℝ] (B i) (spectralSchurGram ℍ[ℝ] U lam (rowsMatrix ℍ[ℝ] z)) =
          ∑ a, compressedRowContribution ℍ[ℝ] (B i)
            (rowFactorCLM ℍ[ℝ] (trailingSelector ℍ[ℝ] p q) (z a) +
              Real.sqrt (lam a) • leadingRows ℍ[ℝ] U a) := by
        have hgram := compress_spectralSchurGram ℍ[ℝ] (B i) U lam z
        simpa only [spectralSchurGram, realDiagonal,
          Algebra.algebraMap_eq_smul_one] using hgram
      rw [compress_add]
      calc
        _ = Q i + (compress ℍ[ℝ] (B i) (trailingBackground ℍ[ℝ] W) +
            ∑ a, compressedRowContribution ℍ[ℝ] (B i)
              (rowFactorCLM ℍ[ℝ] (trailingSelector ℍ[ℝ] p q) (z a) +
                Real.sqrt (lam a) • leadingRows ℍ[ℝ] U a)) := by
          rw [hg]
        _ = _ := (add_assoc _ _ _).symm
  simpa only [heq] using hmono

end Wishart.QuaternionMatrix
end
end CanonicalSource33

section CanonicalSource34
/- Source: Wishart/FieldSpectralSchurLaw.lean -/



/-!
# The actual conditional spectral Schur representation

The source law is the ascending eigenvalue law, independent Haar frame,
independent normalized Gaussian block, and independent residual Wishart
matrix. Both shapes remain arbitrary real admissible shapes. This file proves
the full map identity from the density-derived Schur and spectral laws.
-/

noncomputable section
open Matrix MeasureTheory Set
open scoped Classical Quaternion ComplexOrder ENNReal

namespace Wishart.ComplexMatrix
open scoped Matrix.Norms.L2Operator
open Wishart.FieldCharts Wishart.FieldGaussian WishartVerification
variable {p q : ℕ}

abbrev SchurNoise (p q : ℕ) := unitary (Matrix (Fin p) (Fin p) ℂ) ×
  Matrix (Fin p) (Fin q) ℂ × Hermitian q

def schurNoiseLaw (p q : ℕ) (α : ℝ) : Measure (SchurNoise p q) :=
  (TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) ℂ))).prod
    ((matrixGaussian ℂ p q).prod (wishartMeasure (α - p) (1 : Matrix (Fin q) (Fin q) ℂ)))

def spectralSchurBuild (z : (Fin p → ℝ) × SchurNoise p q) : Hermitian (p + q) :=
  schurInput (unitaryConjugate ℂ z.2.1 (diagonalHermitian ℂ z.1)) z.2.2.2 z.2.2.1

theorem measurable_spectralSchurBuild : Measurable (@spectralSchurBuild p q) := by
  exact measurable_schurInput.comp
    (((measurable_unitary_diagonal ℂ p).comp
      ((measurable_fst.comp measurable_snd).prodMk measurable_fst)).prodMk
        (measurable_snd.comp measurable_snd))

theorem schurNoiseLaw_probability {α : ℝ} (hα : ((p + q : ℕ) : ℝ) - 1 < α) :
    IsProbabilityMeasure (schurNoiseLaw p q α) := by
  have hW : (q : ℝ) - 1 < α - p := by push_cast at hα; linarith
  letI := wishart_standard_probability q hW
  unfold schurNoiseLaw
  infer_instance

set_option backward.isDefEq.respectTransparency true in
theorem spectralSchurBuild_law {α : ℝ} (hα : ((p + q : ℕ) : ℝ) - 1 < α) :
    ((identityEigenLaw p α).prod (schurNoiseLaw p q α)).map spectralSchurBuild =
      wishartMeasure α (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) := by
  have hpα : (p : ℝ) - 1 < α := by
    have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    push_cast at hα
    linarith
  have hqα : (q : ℝ) - 1 < α - p := by push_cast at hα; linarith
  letI := wishart_standard_probability q hqα
  let A := fun z : (Fin p → ℝ) × unitary (Matrix (Fin p) (Fin p) ℂ) =>
    unitaryConjugate ℂ z.2 (diagonalHermitian ℂ z.1)
  have hA : Measurable A := (measurable_unitary_diagonal ℂ p).comp
    (measurable_snd.prodMk measurable_fst)
  have hspectral : ((identityEigenLaw p α).prod
      (TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) ℂ)))).map A =
      wishartMeasure α (1 : Matrix (Fin p) (Fin p) ℂ) := by
    rw [(identityEigenLaw_normalized_density hpα).2.2]
    exact wishart_laguerre_haar_representation hpα
  rw [(finiteDensity_and_schur_law α (finiteDensity_wishart_standard p hpα)
    (finiteDensity_wishart_standard q hqα)).2]
  rw [← hspectral]
  exact (map_nested_prod (identityEigenLaw p α)
    (TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) ℂ)))
    ((matrixGaussian ℂ p q).prod (wishartMeasure (α - p) (1 : Matrix (Fin q) (Fin q) ℂ)))
    A hA (fun z => schurInput z.1 z.2.2 z.2.1) measurable_schurInput).symm

theorem leadingBlock_spectralSchurBuild (z : (Fin p → ℝ) × SchurNoise p q) :
    Wishart.FieldHermitian.leadingBlock ℂ (spectralSchurBuild z) =
      unitaryConjugate ℂ z.2.1 (diagonalHermitian ℂ z.1) := by
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  simp [Wishart.FieldHermitian.leadingBlock, spectralSchurBuild, schurInput,
    Wishart.FieldHermitian.fromBlocks, Matrix.submatrix_apply]

end Wishart.ComplexMatrix

namespace Wishart.QuaternionMatrix
open scoped Matrix.Norms.Frobenius
open Wishart.FieldCharts Wishart.FieldGaussian WishartVerification
variable {p q : ℕ}

abbrev SchurNoise (p q : ℕ) := unitary (Matrix (Fin p) (Fin p) ℍ[ℝ]) ×
  Matrix (Fin p) (Fin q) ℍ[ℝ] × Hermitian q

def schurNoiseLaw (p q : ℕ) (α : ℝ) : Measure (SchurNoise p q) :=
  (TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) ℍ[ℝ]))).prod
    ((matrixGaussian ℍ[ℝ] p q).prod (wishartMeasure (α - p) (1 : Matrix (Fin q) (Fin q) ℍ[ℝ])))

def spectralSchurBuild (z : (Fin p → ℝ) × SchurNoise p q) : Hermitian (p + q) :=
  schurInput (unitaryConjugate ℍ[ℝ] z.2.1 (Wishart.FieldCharts.diagonalHermitian ℍ[ℝ] z.1)) z.2.2.2 z.2.2.1

theorem measurable_spectralSchurBuild : Measurable (@spectralSchurBuild p q) := by
  exact measurable_schurInput.comp
    (((measurable_unitary_diagonal ℍ[ℝ] p).comp
      ((measurable_fst.comp measurable_snd).prodMk measurable_fst)).prodMk
        (measurable_snd.comp measurable_snd))

theorem schurNoiseLaw_probability {α : ℝ} (hα : ((p + q : ℕ) : ℝ) - 1 < α) :
    IsProbabilityMeasure (schurNoiseLaw p q α) := by
  have hW : (q : ℝ) - 1 < α - p := by push_cast at hα; linarith
  letI := wishart_standard_probability q hW
  unfold schurNoiseLaw
  infer_instance

set_option backward.isDefEq.respectTransparency true in
theorem spectralSchurBuild_law {α : ℝ} (hα : ((p + q : ℕ) : ℝ) - 1 < α) :
    ((identityEigenLaw p α).prod (schurNoiseLaw p q α)).map spectralSchurBuild =
      wishartMeasure α (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℍ[ℝ]) := by
  have hpα : (p : ℝ) - 1 < α := by
    have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    push_cast at hα
    linarith
  have hqα : (q : ℝ) - 1 < α - p := by push_cast at hα; linarith
  letI := wishart_standard_probability q hqα
  let A := fun z : (Fin p → ℝ) × unitary (Matrix (Fin p) (Fin p) ℍ[ℝ]) =>
    unitaryConjugate ℍ[ℝ] z.2 (Wishart.FieldCharts.diagonalHermitian ℍ[ℝ] z.1)
  have hswap : Measurable (Prod.swap :
      ((Fin p → ℝ) × unitary (Matrix (Fin p) (Fin p) ℍ[ℝ])) →
        unitary (Matrix (Fin p) (Fin p) ℍ[ℝ]) × (Fin p → ℝ)) := measurable_swap
  have hA : Measurable A := by
    have hA0 := (measurable_unitary_diagonal ℍ[ℝ] p).comp hswap
    simpa only [Function.comp_def, Prod.fst_swap, Prod.snd_swap, A] using hA0
  have hspectral : ((identityEigenLaw p α).prod
      (TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) ℍ[ℝ])))).map A =
      wishartMeasure α (1 : Matrix (Fin p) (Fin p) ℍ[ℝ]) := by
    rw [(identityEigenLaw_normalized_density hpα).2.2]
    exact wishart_laguerre_haar_representation hpα
  let ν := (matrixGaussian ℍ[ℝ] p q).prod
    (wishartMeasure (α - p) (1 : Matrix (Fin q) (Fin q) ℍ[ℝ]))
  let T := fun z : Hermitian p × (Matrix (Fin p) (Fin q) ℍ[ℝ] × Hermitian q) =>
    schurInput z.1 z.2.2 z.2.1
  have hsplit := map_nested_prod (identityEigenLaw p α)
    (TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) ℍ[ℝ])))
    ν A hA T measurable_schurInput
  have hprod := congrArg (fun μ : Measure (Hermitian p) => (μ.prod ν).map T) hspectral
  calc
    _ = ((((identityEigenLaw p α).prod
        (TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) ℍ[ℝ])))).map A).prod ν).map T := hsplit.symm
    _ = ((wishartMeasure α (1 : Matrix (Fin p) (Fin p) ℍ[ℝ])).prod ν).map T := hprod
    _ = _ := (finiteDensity_and_schur_law α (finiteDensity_wishart_standard p hpα)
      (finiteDensity_wishart_standard q hqα)).2.symm

theorem leadingBlock_spectralSchurBuild (z : (Fin p → ℝ) × SchurNoise p q) :
    Wishart.FieldHermitian.leadingBlock ℍ[ℝ] (spectralSchurBuild z) =
      unitaryConjugate ℍ[ℝ] z.2.1 (Wishart.FieldCharts.diagonalHermitian ℍ[ℝ] z.1) := by
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  simp [Wishart.FieldHermitian.leadingBlock, spectralSchurBuild, schurInput,
    Wishart.FieldHermitian.fromBlocks, Matrix.submatrix_apply]

end Wishart.QuaternionMatrix
end
end CanonicalSource34

section CanonicalSource35
/- Source: Wishart/FieldConditionalMonotonicity.lean -/



/-!
# Monotonicity of the actual conditional field expectations

The Gaussian rotation is justified by its exact invariant law. Tonelli moves
the residual positive matrix outside the Gaussian integral; its positivity is
an almost-everywhere consequence of the literal density. The field row theorem
then supplies coordinatewise monotonicity with no rank threshold.
-/

noncomputable section
open Matrix MeasureTheory Set
open scoped Classical Quaternion ComplexOrder ENNReal

namespace Wishart.ComplexMatrix
open scoped Matrix.Norms.Frobenius
open Wishart.FieldCharts Wishart.FieldGaussian Wishart.Spectral
variable {p q : ℕ}

theorem spectralSchur_conditional_integral {α : ℝ}
    (hα : ((p + q : ℕ) : ℝ) - 1 < α)
    (f : Hermitian (p + q) → ℝ≥0∞) (hf : Measurable f)
    (lam : Fin p → ℝ) (hlam : ∀ a, 0 ≤ lam a) :
    (∫⁻ z, f (spectralSchurBuild (lam,z)) ∂schurNoiseLaw p q α) =
      ∫⁻ U, ∫⁻ W, ∫⁻ Z,
        f (trailingBackground ℂ W + spectralSchurGram ℂ U lam Z)
        ∂matrixGaussian ℂ p q
        ∂wishartMeasure (α - p) (1 : Matrix (Fin q) (Fin q) ℂ)
        ∂TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) ℂ)) := by
  have hW : (q : ℝ) - 1 < α - p := by push_cast at hα; linarith
  letI := wishart_standard_probability q hW
  have hmeas : Measurable (fun z : SchurNoise p q => f (spectralSchurBuild (lam,z))) :=
    hf.comp (measurable_spectralSchurBuild.comp (measurable_const.prodMk measurable_id))
  rw [schurNoiseLaw, lintegral_prod _ hmeas.aemeasurable]
  apply lintegral_congr
  intro U
  have hUW : Measurable (fun z : Matrix (Fin p) (Fin q) ℂ × Hermitian q =>
      f (schurInput (unitaryConjugate ℂ U (diagonalHermitian ℂ lam)) z.2 z.1)) :=
    hf.comp (measurable_schurInput.comp (measurable_const.prodMk measurable_id))
  dsimp only [spectralSchurBuild]
  rw [lintegral_prod_symm _ hUW.aemeasurable]
  apply lintegral_congr
  intro W
  have hZ : Measurable (fun Z : Matrix (Fin p) (Fin q) ℂ =>
      f (schurInput (unitaryConjugate ℂ U (diagonalHermitian ℂ lam)) W Z)) :=
    hf.comp (measurable_schurInput.comp
      (measurable_const.prodMk (measurable_id.prodMk measurable_const)))
  have hrot := matrixGaussian_map_unitary_left (p := p) (q := q) ℂ
    (by simp [Complex.finrank_real_complex]) Complex.reLm complex_re_star_mul U
  conv_lhs => rw [← hrot, lintegral_map hZ (by fun_prop)]
  apply lintegral_congr
  intro Z
  exact congrArg f (schurInput_unitary_diagonal U lam hlam W Z)

theorem monotone_spectralSchur_conditional_product {α : ℝ}
    (hα : ((p + q : ℕ) : ℝ) - 1 < α) {ι : Type*} [Fintype ι]
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin (p + q)) (Fin (k i)) ℂ)
    (Q : ∀ i, Hermitian (k i)) (hQ : ∀ i, (Q i : Matrix (Fin (k i)) (Fin (k i)) ℂ).PosSemidef)
    (h : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hc : ∀ i, ConvexOn ℝ univ (h i)) (hm : ∀ i, Monotone (h i)) (L : ι → ℕ) :
    MonotoneOn (fun lam : Fin p → ℝ => ∫⁻ z,
      ENNReal.ofReal (∏ i, complexFaceApprox (hc i) (hm i) (L i)
        (Q i + compress ℂ (B i) (spectralSchurBuild (lam,z))))
      ∂schurNoiseLaw p q α) (Ici 0) := by
  let f : Hermitian (p + q) → ℝ≥0∞ := fun X =>
    ENNReal.ofReal (∏ i, complexFaceApprox (hc i) (hm i) (L i) (Q i + compress ℂ (B i) X))
  have hf : Measurable f := by
    apply Measurable.ennreal_ofReal
    apply Finset.measurable_prod
    intro i hi
    exact (continuous_complexFaceApprox (hc i) (hm i) (L i)).measurable.comp
      (continuous_const.add (continuous_compress ℂ (B i))).measurable
  intro x hx y hy hxy
  change (∫⁻ z, f (spectralSchurBuild (x,z)) ∂schurNoiseLaw p q α) ≤
    ∫⁻ z, f (spectralSchurBuild (y,z)) ∂schurNoiseLaw p q α
  rw [spectralSchur_conditional_integral hα f hf x hx,
    spectralSchur_conditional_integral hα f hf y hy]
  apply lintegral_mono
  intro U
  apply lintegral_mono_ae
  filter_upwards [wishart_ae_posDef (α - p) (1 : Matrix (Fin q) (Fin q) ℂ)] with W hW
  exact monotone_spectralSchur_average U W hW.posSemidef k B Q hQ h hc hm L hx hy hxy

end Wishart.ComplexMatrix

namespace Wishart.QuaternionMatrix
open scoped Matrix.Norms.Frobenius
open Wishart.FieldCharts Wishart.FieldGaussian Wishart.Spectral
variable {p q : ℕ}

theorem spectralSchur_conditional_integral {α : ℝ}
    (hα : ((p + q : ℕ) : ℝ) - 1 < α)
    (f : Hermitian (p + q) → ℝ≥0∞) (hf : Measurable f)
    (lam : Fin p → ℝ) (hlam : ∀ a, 0 ≤ lam a) :
    (∫⁻ z, f (spectralSchurBuild (lam,z)) ∂schurNoiseLaw p q α) =
      ∫⁻ U, ∫⁻ W, ∫⁻ Z,
        f (trailingBackground ℍ[ℝ] W + spectralSchurGram ℍ[ℝ] U lam Z)
        ∂matrixGaussian ℍ[ℝ] p q
        ∂wishartMeasure (α - p) (1 : Matrix (Fin q) (Fin q) ℍ[ℝ])
        ∂TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) ℍ[ℝ])) := by
  have hW : (q : ℝ) - 1 < α - p := by push_cast at hα; linarith
  letI := wishart_standard_probability q hW
  have hmeas : Measurable (fun z : SchurNoise p q => f (spectralSchurBuild (lam,z))) :=
    hf.comp (measurable_spectralSchurBuild.comp (measurable_const.prodMk measurable_id))
  rw [schurNoiseLaw, lintegral_prod _ hmeas.aemeasurable]
  apply lintegral_congr
  intro U
  have hUW : Measurable (fun z : Matrix (Fin p) (Fin q) ℍ[ℝ] × Hermitian q =>
      f (schurInput (unitaryConjugate ℍ[ℝ] U (Wishart.FieldCharts.diagonalHermitian ℍ[ℝ] lam)) z.2 z.1)) :=
    hf.comp (measurable_schurInput.comp (measurable_const.prodMk measurable_id))
  dsimp only [spectralSchurBuild]
  rw [lintegral_prod_symm _ hUW.aemeasurable]
  apply lintegral_congr
  intro W
  have hZ : Measurable (fun Z : Matrix (Fin p) (Fin q) ℍ[ℝ] =>
      f (schurInput (unitaryConjugate ℍ[ℝ] U (Wishart.FieldCharts.diagonalHermitian ℍ[ℝ] lam)) W Z)) :=
    hf.comp (measurable_schurInput.comp
      (measurable_const.prodMk (measurable_id.prodMk measurable_const)))
  have hrot := matrixGaussian_map_unitary_left (p := p) (q := q) ℍ[ℝ]
    (by simp [Quaternion.finrank_eq_four]) (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)) quaternion_re_star_mul U
  conv_lhs => rw [← hrot, lintegral_map hZ (by fun_prop)]
  apply lintegral_congr
  intro Z
  exact congrArg f (schurInput_unitary_diagonal U lam hlam W Z)

theorem monotone_spectralSchur_conditional_product {α : ℝ}
    (hα : ((p + q : ℕ) : ℝ) - 1 < α) {ι : Type*} [Fintype ι]
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin (p + q)) (Fin (k i)) ℍ[ℝ])
    (Q : ∀ i, Hermitian (k i)) (hQ : ∀ i, PosSemidef (Q i).val)
    (h : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hc : ∀ i, ConvexOn ℝ univ (h i)) (hm : ∀ i, Monotone (h i)) (L : ι → ℕ) :
    MonotoneOn (fun lam : Fin p → ℝ => ∫⁻ z,
      ENNReal.ofReal (∏ i, quaternionFaceApprox (hc i) (hm i) (L i)
        (Q i + compress ℍ[ℝ] (B i) (spectralSchurBuild (lam,z))))
      ∂schurNoiseLaw p q α) (Ici 0) := by
  let f : Hermitian (p + q) → ℝ≥0∞ := fun X =>
    ENNReal.ofReal (∏ i, quaternionFaceApprox (hc i) (hm i) (L i) (Q i + compress ℍ[ℝ] (B i) X))
  have hf : Measurable f := by
    apply Measurable.ennreal_ofReal
    apply Finset.measurable_prod
    intro i hi
    exact (continuous_quaternionFaceApprox (hc i) (hm i) (L i)).measurable.comp
      (measurable_const.add (continuous_compress ℍ[ℝ] (B i)).measurable)
  intro x hx y hy hxy
  change (∫⁻ z, f (spectralSchurBuild (x,z)) ∂schurNoiseLaw p q α) ≤
    ∫⁻ z, f (spectralSchurBuild (y,z)) ∂schurNoiseLaw p q α
  rw [spectralSchur_conditional_integral hα f hf x hx,
    spectralSchur_conditional_integral hα f hf y hy]
  apply lintegral_mono
  intro U
  apply lintegral_mono_ae
  filter_upwards [wishart_ae_posDef (α - p) (1 : Matrix (Fin q) (Fin q) ℍ[ℝ])] with W hW
  exact monotone_spectralSchur_average U W hW.posSemidef k B Q hQ h hc hm L hx hy hxy

end Wishart.QuaternionMatrix
end
end CanonicalSource35

section CanonicalSource36
/- Source: Wishart/FieldExpectationLimits.lean -/




/-!
# Passing the field comparisons to the full spectral boundary class

The approximants converge on every PSD rank stratum. The selected split is
passed through independent-copy monotone convergence, so infinite expectations
and identically zero boundary factors are retained. The finite-comparison
premise of these internal assembly lemmas must be supplied by the actual law.
-/

noncomputable section
open Matrix MeasureTheory Set Filter Topology
open scoped Classical Quaternion ComplexOrder BigOperators ENNReal
namespace Wishart.FieldGaussian
open scoped Matrix.Norms.Frobenius
open WishartVerification Wishart.Spectral

theorem complex_spectral_boundary_selected_split {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (μ : Measure Ω) [SFinite μ]
    (k₀ : ℕ) (k : ι → ℕ)
    (A₀ : Ω → FieldSpectral.Hermitian ℂ k₀)
    (A : ∀ i, Ω → FieldSpectral.Hermitian ℂ (k i))
    (hAm₀ : Measurable A₀) (hAm : ∀ i, Measurable (A i))
    (hA₀ : ∀ᵐ x ∂μ, (A₀ x : Matrix (Fin k₀) (Fin k₀) ℂ).PosSemidef)
    (hA : ∀ᵐ x ∂μ, ∀ i, (A i x : Matrix (Fin (k i)) (Fin (k i)) ℂ).PosSemidef)
    (h₀ : (Fin k₀ → ℝ) → ℝ) (h : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hc₀ : ConvexOn ℝ univ h₀) (hc : ∀ i, ConvexOn ℝ univ (h i))
    (hm₀ : Monotone h₀) (hm : ∀ i, Monotone (h i))
    (hs₀ : SymmetricProfile h₀) (hs : ∀ i, SymmetricProfile (h i))
    (hfinite : ∀ n,
      (∫⁻ x, ENNReal.ofReal (complexFaceApprox hc₀ hm₀ n (A₀ x)) ∂μ) *
        (∫⁻ x, ENNReal.ofReal (∏ i, complexFaceApprox (hc i) (hm i) n (A i x)) ∂μ) ≤
        ∫⁻ x, ENNReal.ofReal (complexFaceApprox hc₀ hm₀ n (A₀ x) *
          ∏ i, complexFaceApprox (hc i) (hm i) n (A i x)) ∂μ) :
    (∫⁻ x, ENNReal.ofReal (spectralBoundaryValue h₀
      (FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe (A₀ x)))) ∂μ) *
    (∫⁻ x, ENNReal.ofReal (∏ i, spectralBoundaryValue (h i)
      (FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe (A i x)))) ∂μ) ≤
    ∫⁻ x, ENNReal.ofReal (spectralBoundaryValue h₀
      (FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe (A₀ x))) *
      ∏ i, spectralBoundaryValue (h i)
        (FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe (A i x)))) ∂μ := by
  apply selected_split_of_nonnegative_approximations μ
    (fun n x => complexFaceApprox hc₀ hm₀ n (A₀ x))
    (fun n i x => complexFaceApprox (hc i) (hm i) n (A i x))
  · intro n
    exact (continuous_complexFaceApprox hc₀ hm₀ n).measurable.comp hAm₀
  · intro n i
    exact (continuous_complexFaceApprox (hc i) (hm i) n).measurable.comp (hAm i)
  · filter_upwards [hA₀] with x hx n
    exact complexFaceApprox_nonneg hc₀ hm₀ n (A₀ x) hx
  · filter_upwards [hA] with x hx n i
    exact complexFaceApprox_nonneg (hc i) (hm i) n (A i x) (hx i)
  · exact Filter.Eventually.of_forall fun x => complexFaceApprox_monotone_index hc₀ hm₀ (A₀ x)
  · exact Filter.Eventually.of_forall fun x i => complexFaceApprox_monotone_index (hc i) (hm i) (A i x)
  · filter_upwards [hA₀] with x hx
    exact complexFaceApprox_tendsto hc₀ hm₀ hs₀ (A₀ x) hx
  · filter_upwards [hA] with x hx i
    exact complexFaceApprox_tendsto (hc i) (hm i) (hs i) (A i x) (hx i)
  · exact hfinite

theorem quaternion_spectral_boundary_selected_split {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (μ : Measure Ω) [SFinite μ]
    (k₀ : ℕ) (k : ι → ℕ)
    (A₀ : Ω → QuaternionMatrix.Hermitian k₀)
    (A : ∀ i, Ω → QuaternionMatrix.Hermitian (k i))
    (hAm₀ : Measurable A₀) (hAm : ∀ i, Measurable (A i))
    (hA₀ : ∀ᵐ x ∂μ, QuaternionMatrix.PosSemidef (A₀ x).val)
    (hA : ∀ᵐ x ∂μ, ∀ i, QuaternionMatrix.PosSemidef (A i x).val)
    (h₀ : (Fin k₀ → ℝ) → ℝ) (h : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hc₀ : ConvexOn ℝ univ h₀) (hc : ∀ i, ConvexOn ℝ univ (h i))
    (hm₀ : Monotone h₀) (hm : ∀ i, Monotone (h i))
    (hs₀ : SymmetricProfile h₀) (hs : ∀ i, SymmetricProfile (h i))
    (hfinite : ∀ n,
      (∫⁻ x, ENNReal.ofReal (quaternionFaceApprox hc₀ hm₀ n (A₀ x)) ∂μ) *
        (∫⁻ x, ENNReal.ofReal (∏ i, quaternionFaceApprox (hc i) (hm i) n (A i x)) ∂μ) ≤
        ∫⁻ x, ENNReal.ofReal (quaternionFaceApprox hc₀ hm₀ n (A₀ x) *
          ∏ i, quaternionFaceApprox (hc i) (hm i) n (A i x)) ∂μ) :
    (∫⁻ x, ENNReal.ofReal (spectralBoundaryValue h₀ (QuaternionMatrix.orderedValues (A₀ x))) ∂μ) *
    (∫⁻ x, ENNReal.ofReal (∏ i, spectralBoundaryValue (h i)
      (QuaternionMatrix.orderedValues (A i x))) ∂μ) ≤
    ∫⁻ x, ENNReal.ofReal (spectralBoundaryValue h₀ (QuaternionMatrix.orderedValues (A₀ x)) *
      ∏ i, spectralBoundaryValue (h i) (QuaternionMatrix.orderedValues (A i x))) ∂μ := by
  apply selected_split_of_nonnegative_approximations μ
    (fun n x => quaternionFaceApprox hc₀ hm₀ n (A₀ x))
    (fun n i x => quaternionFaceApprox (hc i) (hm i) n (A i x))
  · intro n
    exact (continuous_quaternionFaceApprox hc₀ hm₀ n).measurable.comp hAm₀
  · intro n i
    exact (continuous_quaternionFaceApprox (hc i) (hm i) n).measurable.comp (hAm i)
  · filter_upwards [hA₀] with x hx n
    exact quaternionFaceApprox_nonneg hc₀ hm₀ n (A₀ x) hx
  · filter_upwards [hA] with x hx n i
    exact quaternionFaceApprox_nonneg (hc i) (hm i) n (A i x) (hx i)
  · exact Filter.Eventually.of_forall fun x => quaternionFaceApprox_monotone_index hc₀ hm₀ (A₀ x)
  · exact Filter.Eventually.of_forall fun x i => quaternionFaceApprox_monotone_index (hc i) (hm i) (A i x)
  · filter_upwards [hA₀] with x hx
    exact quaternionFaceApprox_tendsto hc₀ hm₀ hs₀ (A₀ x) hx
  · filter_upwards [hA] with x hx i
    exact quaternionFaceApprox_tendsto (hc i) (hm i) (hs i) (A i x) (hx i)
  · exact hfinite

end Wishart.FieldGaussian
end
end CanonicalSource36

section CanonicalSource37
/- Source: Wishart/FieldLeadingComparison.lean -/




/-!
# The unrestricted field selected-factor comparison for a leading block

This is the actual real-shape density law, not an abstract regression premise.
The selected finite spectral approximant depends only on the ascending leading
spectrum (read in reverse order); the conditional product of every other,
possibly overlapping compression is increasing by the field row argument.
Association of the actual beta-two or beta-four spectrum closes the proof.
-/

noncomputable section
open Matrix MeasureTheory Set
open scoped Classical Quaternion ComplexOrder ENNReal

namespace Wishart.ComplexMatrix
open scoped Matrix.Norms.Frobenius
open Wishart.FieldCharts Wishart.FieldGaussian Wishart.Spectral WishartVerification
variable {p q : ℕ}

theorem orderedValues_unitary_diagonal (U : unitary (Matrix (Fin p) (Fin p) ℂ))
    (lam : Fin p → ℝ) (hlam : Monotone lam) :
    Wishart.FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe (unitaryConjugate ℂ U (diagonalHermitian ℂ lam))) = lam ∘ Fin.rev := by
  rw [← ascendingValues_reversal, ascendingValues_conjugate, ascendingValues_diagonal lam hlam]

theorem leading_selected_finite_comparison {α : ℝ}
    (hα : ((p + q : ℕ) : ℝ) - 1 < α) {ι : Type*} [Fintype ι]
    (c : ℝ) (hc0 : 0 ≤ c)
    (h₀ : (Fin p → ℝ) → ℝ) (hc₀ : ConvexOn ℝ univ h₀) (hm₀ : Monotone h₀) (L₀ : ℕ)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin (p + q)) (Fin (k i)) ℂ)
    (Q : ∀ i, Hermitian (k i)) (hQ : ∀ i, (Q i : Matrix (Fin (k i)) (Fin (k i)) ℂ).PosSemidef)
    (h : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hc : ∀ i, ConvexOn ℝ univ (h i)) (hm : ∀ i, Monotone (h i)) (L : ι → ℕ) :
    (∫⁻ X, ENNReal.ofReal (complexFaceApprox hc₀ hm₀ L₀
      (Wishart.FieldSpectral.identityShift (Wishart.FieldHermitian.leadingBlock ℂ X) c))
      ∂wishartMeasure α (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ)) *
    (∫⁻ X, ENNReal.ofReal (∏ i, complexFaceApprox (hc i) (hm i) (L i)
      (Q i + compress ℂ (B i) X))
      ∂wishartMeasure α (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ)) ≤
    ∫⁻ X, ENNReal.ofReal (complexFaceApprox hc₀ hm₀ L₀
      (Wishart.FieldSpectral.identityShift (Wishart.FieldHermitian.leadingBlock ℂ X) c)) *
      ENNReal.ofReal (∏ i, complexFaceApprox (hc i) (hm i) (L i)
        (Q i + compress ℂ (B i) X))
      ∂wishartMeasure α (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) := by
  have hpα : (p : ℝ) - 1 < α := by
    have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    push_cast at hα
    linarith
  letI := identityEigenLaw_isProbability hpα
  letI := schurNoiseLaw_probability hα
  let f : Hermitian (p + q) → ℝ≥0∞ := fun X => ENNReal.ofReal
    (complexFaceApprox hc₀ hm₀ L₀ (Wishart.FieldSpectral.identityShift (Wishart.FieldHermitian.leadingBlock ℂ X) c))
  let g : Hermitian (p + q) → ℝ≥0∞ := fun X => ENNReal.ofReal
    (∏ i, complexFaceApprox (hc i) (hm i) (L i) (Q i + compress ℂ (B i) X))
  let φ : (Fin p → ℝ) → ℝ≥0∞ := fun lam => ENNReal.ofReal
    (sortedFaceMonomialApprox hc₀ hm₀ L₀ (fun a => lam (Fin.rev a) + c))
  have hf : Measurable f := by
    apply (continuous_complexFaceApprox hc₀ hm₀ L₀).measurable.ennreal_ofReal.comp
    apply Measurable.subtype_mk
    change Measurable (fun X : Hermitian (p+q) =>
      (Wishart.FieldHermitian.leadingBlock ℂ X).val + c • (1 : Matrix (Fin p) (Fin p) ℂ))
    unfold Wishart.FieldHermitian.leadingBlock
    fun_prop
  have hg : Measurable g := by
    apply Measurable.ennreal_ofReal
    apply Finset.measurable_prod
    intro i hi
    exact (continuous_complexFaceApprox (hc i) (hm i) (L i)).measurable.comp
      (continuous_const.add (continuous_compress ℂ (B i))).measurable
  have hφ : Measurable φ := by
    apply (continuous_sortedFaceMonomialApprox hc₀ hm₀ L₀).measurable.ennreal_ofReal.comp
    fun_prop
  apply selected_split_of_conditional_association
    (wishartMeasure α (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ))
    (identityEigenLaw p α) (schurNoiseLaw p q α) (chamber p)
    (ae_identityEigenLaw_mem_chamber hpα) spectralSchurBuild measurable_spectralSchurBuild
    (spectralSchurBuild_law hα) f g hf hg φ hφ
  · intro lam hlam z
    dsimp only [f, φ]
    rw [leadingBlock_spectralSchurBuild]
    have hpos := Wishart.FieldSpectral.identityShift_posSemidef
      (unitaryConjugate ℂ z.1 (diagonalHermitian ℂ lam))
      (posSemidef_unitary_diagonal z.1 lam (fun a => (hlam.2 a).le)) hc0
    rw [complexFaceApprox_eq_sorted hc₀ hm₀ L₀ _ hpos,
      Wishart.FieldSpectral.orderedValues_identityShift, orderedValues_unitary_diagonal z.1 lam hlam.1.monotone]
    rfl
  · exact identityEigenLaw_association hpα
  · intro x hx y hy hxy
    apply ENNReal.ofReal_le_ofReal
    apply sortedFaceMonomialApprox_mono hc₀ hm₀ L₀
    · intro a
      exact add_nonneg (hx.2 (Fin.rev a)).le hc0
    · intro a
      linarith [hxy (Fin.rev a)]
  · intro x hx y hy hxy
    exact monotone_spectralSchur_conditional_product hα k B Q hQ h hc hm L
      (fun a => (hx.2 a).le) (fun a => (hy.2 a).le) hxy

end Wishart.ComplexMatrix

namespace Wishart.QuaternionMatrix
open scoped Matrix.Norms.Frobenius
open Wishart.FieldCharts Wishart.FieldGaussian Wishart.Spectral WishartVerification
variable {p q : ℕ}

theorem orderedValues_unitary_diagonal (U : unitary (Matrix (Fin p) (Fin p) ℍ[ℝ]))
    (lam : Fin p → ℝ) (hlam : Monotone lam) :
    orderedValues (unitaryConjugate ℍ[ℝ] U (Wishart.FieldCharts.diagonalHermitian ℍ[ℝ] lam)) = lam ∘ Fin.rev := by
  rw [← ascendingValues_reversal, ascendingValues_conjugate, ascendingValues_diagonal lam hlam]

theorem leading_selected_finite_comparison {α : ℝ}
    (hα : ((p + q : ℕ) : ℝ) - 1 < α) {ι : Type*} [Fintype ι]
    (c : ℝ) (hc0 : 0 ≤ c)
    (h₀ : (Fin p → ℝ) → ℝ) (hc₀ : ConvexOn ℝ univ h₀) (hm₀ : Monotone h₀) (L₀ : ℕ)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin (p + q)) (Fin (k i)) ℍ[ℝ])
    (Q : ∀ i, Hermitian (k i)) (hQ : ∀ i, PosSemidef (Q i).val)
    (h : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hc : ∀ i, ConvexOn ℝ univ (h i)) (hm : ∀ i, Monotone (h i)) (L : ι → ℕ) :
    (∫⁻ X, ENNReal.ofReal (quaternionFaceApprox hc₀ hm₀ L₀
      (identityShift (Wishart.FieldHermitian.leadingBlock ℍ[ℝ] X) c))
      ∂wishartMeasure α (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℍ[ℝ])) *
    (∫⁻ X, ENNReal.ofReal (∏ i, quaternionFaceApprox (hc i) (hm i) (L i)
      (Q i + compress ℍ[ℝ] (B i) X))
      ∂wishartMeasure α (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℍ[ℝ])) ≤
    ∫⁻ X, ENNReal.ofReal (quaternionFaceApprox hc₀ hm₀ L₀
      (identityShift (Wishart.FieldHermitian.leadingBlock ℍ[ℝ] X) c)) *
      ENNReal.ofReal (∏ i, quaternionFaceApprox (hc i) (hm i) (L i)
        (Q i + compress ℍ[ℝ] (B i) X))
      ∂wishartMeasure α (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℍ[ℝ]) := by
  have hpα : (p : ℝ) - 1 < α := by
    have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    push_cast at hα
    linarith
  letI := identityEigenLaw_isProbability hpα
  letI := schurNoiseLaw_probability hα
  let f : Hermitian (p + q) → ℝ≥0∞ := fun X => ENNReal.ofReal
    (quaternionFaceApprox hc₀ hm₀ L₀ (identityShift (Wishart.FieldHermitian.leadingBlock ℍ[ℝ] X) c))
  let g : Hermitian (p + q) → ℝ≥0∞ := fun X => ENNReal.ofReal
    (∏ i, quaternionFaceApprox (hc i) (hm i) (L i) (Q i + compress ℍ[ℝ] (B i) X))
  let φ : (Fin p → ℝ) → ℝ≥0∞ := fun lam => ENNReal.ofReal
    (sortedFaceMonomialApprox hc₀ hm₀ L₀ (fun a => lam (Fin.rev a) + c))
  have hf : Measurable f := by
    apply (continuous_quaternionFaceApprox hc₀ hm₀ L₀).measurable.ennreal_ofReal.comp
    apply Measurable.subtype_mk
    change Measurable (fun X : Hermitian (p+q) =>
      (Wishart.FieldHermitian.leadingBlock ℍ[ℝ] X).val + c • (1 : Matrix (Fin p) (Fin p) ℍ[ℝ]))
    unfold Wishart.FieldHermitian.leadingBlock
    fun_prop
  have hg : Measurable g := by
    apply Measurable.ennreal_ofReal
    apply Finset.measurable_prod
    intro i hi
    exact (continuous_quaternionFaceApprox (hc i) (hm i) (L i)).measurable.comp
      (measurable_const.add (continuous_compress ℍ[ℝ] (B i)).measurable)
  have hφ : Measurable φ := by
    apply (continuous_sortedFaceMonomialApprox hc₀ hm₀ L₀).measurable.ennreal_ofReal.comp
    fun_prop
  apply selected_split_of_conditional_association
    (wishartMeasure α (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℍ[ℝ]))
    (identityEigenLaw p α) (schurNoiseLaw p q α) (chamber p)
    (ae_identityEigenLaw_mem_chamber hpα) spectralSchurBuild measurable_spectralSchurBuild
    (spectralSchurBuild_law hα) f g hf hg φ hφ
  · intro lam hlam z
    dsimp only [f, φ]
    rw [leadingBlock_spectralSchurBuild]
    have hpos := identityShift_posSemidef
      (unitaryConjugate ℍ[ℝ] z.1 (Wishart.FieldCharts.diagonalHermitian ℍ[ℝ] lam))
      (posSemidef_unitary_diagonal z.1 lam (fun a => (hlam.2 a).le)) hc0
    rw [quaternionFaceApprox_eq_sorted hc₀ hm₀ L₀ _ hpos,
      orderedValues_identityShift, orderedValues_unitary_diagonal z.1 lam hlam.1.monotone]
    rfl
  · exact identityEigenLaw_association hpα
  · intro x hx y hy hxy
    apply ENNReal.ofReal_le_ofReal
    apply sortedFaceMonomialApprox_mono hc₀ hm₀ L₀
    · intro a
      exact add_nonneg (hx.2 (Fin.rev a)).le hc0
    · intro a
      linarith [hxy (Fin.rev a)]
  · intro x hx y hy hxy
    exact monotone_spectralSchur_conditional_product hα k B Q hQ h hc hm L
      (fun a => (hx.2 a).le) (fun a => (hy.2 a).le) hxy

end Wishart.QuaternionMatrix
end
end CanonicalSource37

section CanonicalSource38
/- Source: Wishart/FieldFrameCompletion.lean -/



/-!
# Completing actual orthonormal column frames

The real/complex proof extends an orthonormal family to an orthonormal basis.
For quaternions the proof is a column induction using the already proved
quaternion Householder construction.  It never treats quaternion columns as
a left-linear complex basis, and it does not assume a completion theorem.

The resulting square unitary agrees with every prescribed column, with the
literal `Fin.castLE` inclusion into the first coordinates.
-/

noncomputable section

open Matrix Set
open scoped Classical Quaternion BigOperators

namespace Wishart.FieldSpectral

variable {𝕜 : Type*} [RCLike 𝕜]

theorem exists_unitary_extension {p q : ℕ} (hqp : q ≤ p)
    (B : Matrix (Fin p) (Fin q) 𝕜) (hB : Bᴴ * B = 1) :
    ∃ U : Matrix.unitaryGroup (Fin p) 𝕜,
      (U : Matrix (Fin p) (Fin p) 𝕜).submatrix id (Fin.castLE hqp) = B := by
  let v : Fin p → EuclideanSpace 𝕜 (Fin p) := fun j =>
    WithLp.toLp 2 (fun i => if h : j.val < q then B i ⟨j.val, h⟩ else 0)
  let s : Set (Fin p) := {j | j.val < q}
  have hv (j : Fin p) (hj : j.val < q) (i : Fin p) :
      v j i = B i ⟨j.val, hj⟩ := by simp [v, hj]
  have horth : Orthonormal 𝕜 (s.domRestrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    have hiq : i.val < q := hi
    have hjq : j.val < q := hj
    have h := congrArg (fun A : Matrix (Fin q) (Fin q) 𝕜 =>
      A ⟨i.val, hiq⟩ ⟨j.val, hjq⟩) hB
    simpa only [Set.domRestrict_apply, PiLp.inner_apply, RCLike.inner_apply',
      hv i hiq, hv j hjq, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, Subtype.ext_iff, Fin.ext_iff, RCLike.star_def] using h
  have hcard : Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin p)) = Fintype.card (Fin p) := by simp
  obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq hcard
  let U : Matrix (Fin p) (Fin p) 𝕜 := fun i j => b j i
  have hU : Uᴴ * U = 1 := by
    apply Matrix.ext
    intro i j
    have h := orthonormal_iff_ite.mp b.orthonormal i j
    change (∑ a, star (b i a) * b j a) = if i = j then 1 else 0
    simpa only [PiLp.inner_apply, RCLike.inner_apply', RCLike.star_def] using h
  refine ⟨⟨U, Matrix.mem_unitaryGroup_iff'.mpr hU⟩, ?_⟩
  apply Matrix.ext
  intro i j
  change b (Fin.castLE hqp j) i = B i j
  rw [hb _ (show Fin.castLE hqp j ∈ s from j.isLt)]
  simpa using hv (Fin.castLE hqp j) j.isLt i

theorem OrthonormalFrame.exists_unitary {p q : ℕ} (hqp : q ≤ p)
    (B : OrthonormalFrame 𝕜 p q) :
    ∃ U : Matrix.unitaryGroup (Fin p) 𝕜,
      (U : Matrix (Fin p) (Fin p) 𝕜).submatrix id (Fin.castLE hqp) = B.val :=
  exists_unitary_extension hqp B.val B.property

end Wishart.FieldSpectral

namespace Wishart.QuaternionMatrix
open scoped Matrix.Norms.Frobenius

/-- An orthonormal quaternion frame extends to a square quaternion unitary.
The two-sided unitary identities are retained explicitly by the `unitary`
subtype; no commutativity of quaternion multiplication is used. -/
theorem exists_unitary_extension : ∀ (p q : ℕ) (hqp : q ≤ p)
    (B : Matrix (Fin p) (Fin q) ℍ[ℝ]), Bᴴ * B = 1 →
    ∃ U : unitary (Matrix (Fin p) (Fin p) ℍ[ℝ]),
      (U.val : Matrix (Fin p) (Fin p) ℍ[ℝ]).submatrix id (Fin.castLE hqp) = B := by
  intro p
  induction p with
  | zero =>
      intro q hqp B hB
      have hq : q = 0 := Nat.eq_zero_of_le_zero hqp
      subst q
      exact ⟨1, Subsingleton.elim _ _⟩
  | succ p ih =>
      intro q hqp B hB
      cases q with
      | zero => exact ⟨1, by apply Matrix.ext; intro i j; exact Fin.elim0 j⟩
      | succ q =>
          have hqp' : q ≤ p := Nat.le_of_succ_le_succ hqp
          let x : Fin (p + 1) → ℍ[ℝ] := fun i => B i 0
          have hx : star x ⬝ᵥ x = 1 := by
            have h := congrArg (fun A : Matrix (Fin (q + 1)) (Fin (q + 1)) ℍ[ℝ] =>
              A 0 0) hB
            simpa only [x, dotProduct, Pi.star_apply, Matrix.mul_apply,
              Matrix.conjTranspose_apply, Matrix.one_apply, if_true] using h
          obtain ⟨U, hUcol⟩ := exists_unitary_firstColumn x hx
          let C : Matrix (Fin (p + 1)) (Fin (q + 1)) ℍ[ℝ] :=
            (U.val : Matrix (Fin (p + 1)) (Fin (p + 1)) ℍ[ℝ])ᴴ * B
          have hC : Cᴴ * C = 1 := by
            dsimp only [C]
            rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
            calc
              _ = Bᴴ * ((U.val : Matrix (Fin (p + 1)) (Fin (p + 1)) ℍ[ℝ]) *
                (U.val : Matrix (Fin (p + 1)) (Fin (p + 1)) ℍ[ℝ])ᴴ) * B := by
                  simp only [Matrix.mul_assoc]
              _ = 1 := by rw [show (U.val : Matrix (Fin (p + 1)) (Fin (p + 1)) ℍ[ℝ]) *
                (U.val : Matrix (Fin (p + 1)) (Fin (p + 1)) ℍ[ℝ])ᴴ = 1 from U.property.2,
                Matrix.mul_one, hB]
          have hCrow (j : Fin (q + 1)) :
              C 0 j = (1 : Matrix (Fin (q + 1)) (Fin (q + 1)) ℍ[ℝ]) 0 j := by
            calc
              C 0 j = (Bᴴ * B) 0 j := by
                simp only [C, Matrix.mul_apply, Matrix.conjTranspose_apply, hUcol, x]
              _ = _ := congrArg (fun A => A 0 j) hB
          have hCcol (i : Fin (p + 1)) :
              C i 0 = (1 : Matrix (Fin (p + 1)) (Fin (p + 1)) ℍ[ℝ]) i 0 := by
            calc
              C i 0 = ((U.val : Matrix (Fin (p + 1)) (Fin (p + 1)) ℍ[ℝ])ᴴ *
                  (U.val : Matrix (Fin (p + 1)) (Fin (p + 1)) ℍ[ℝ])) i 0 := by
                    simp only [C, Matrix.mul_apply, Matrix.conjTranspose_apply, hUcol, x]
              _ = _ := congrArg (fun A => A i 0) U.property.1
          let D : Matrix (Fin p) (Fin q) ℍ[ℝ] := C.submatrix Fin.succ Fin.succ
          have hD : Dᴴ * D = 1 := by
            apply Matrix.ext
            intro i j
            have h := congrArg (fun A : Matrix (Fin (q + 1)) (Fin (q + 1)) ℍ[ℝ] =>
              A i.succ j.succ) hC
            simpa only [D, Matrix.mul_apply, Matrix.conjTranspose_apply,
              Matrix.submatrix_apply, Fin.sum_univ_succ, hCrow, Matrix.one_apply,
              Ne.symm (Fin.succ_ne_zero _), if_false, star_zero, zero_mul, zero_add,
              Fin.succ_inj] using h
          obtain ⟨V, hV⟩ := ih q hqp' D hD
          let W := blockSuccUnitary V
          have hcast0 : Fin.castLE hqp (0 : Fin (q + 1)) = (0 : Fin (p + 1)) := rfl
          have hcasts (j : Fin q) : Fin.castLE hqp j.succ = (Fin.castLE hqp' j).succ := rfl
          have hWC : (W.val : Matrix (Fin (p + 1)) (Fin (p + 1)) ℍ[ℝ]).submatrix id
              (Fin.castLE hqp) = C := by
            apply Matrix.ext
            intro i j
            refine Fin.cases ?_ (fun i => ?_) i <;>
              refine Fin.cases ?_ (fun j => ?_) j
            · simpa only [W, blockSuccUnitary, Matrix.submatrix_apply, id_eq,
                hcast0, blockSucc_zero_zero, hCcol, Matrix.one_apply, if_true]
            · simpa only [W, blockSuccUnitary, Matrix.submatrix_apply, id_eq,
                hcasts, blockSucc_zero_succ, hCrow, Matrix.one_apply,
                Ne.symm (Fin.succ_ne_zero _), if_false]
            · simpa only [W, blockSuccUnitary, Matrix.submatrix_apply, id_eq,
                hcast0, blockSucc_succ_zero, hCcol, Matrix.one_apply,
                Fin.succ_ne_zero, if_false]
            · simpa only [W, blockSuccUnitary, Matrix.submatrix_apply, id_eq,
                hcasts, blockSucc_succ_succ, D] using congrArg (fun A => A i j) hV
          have hUC : (U.val : Matrix (Fin (p + 1)) (Fin (p + 1)) ℍ[ℝ]) * C = B := by
            dsimp only [C]
            rw [← Matrix.mul_assoc, show
              (U.val : Matrix (Fin (p + 1)) (Fin (p + 1)) ℍ[ℝ]) *
                (U.val : Matrix (Fin (p + 1)) (Fin (p + 1)) ℍ[ℝ])ᴴ = 1 from U.property.2,
              Matrix.one_mul]
          refine ⟨U * W, ?_⟩
          apply Matrix.ext
          intro i j
          change (∑ k, (U.val : Matrix (Fin (p + 1)) (Fin (p + 1)) ℍ[ℝ]) i k *
            (W.val : Matrix (Fin (p + 1)) (Fin (p + 1)) ℍ[ℝ]) k (Fin.castLE hqp j)) = B i j
          calc
            _ = ((U.val : Matrix (Fin (p + 1)) (Fin (p + 1)) ℍ[ℝ]) * C) i j := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [show (W.val : Matrix (Fin (p + 1)) (Fin (p + 1)) ℍ[ℝ]) k
                (Fin.castLE hqp j) = C k j from congrArg (fun A => A k j) hWC]
            _ = _ := congrArg (fun A => A i j) hUC

theorem OrthonormalFrame.exists_unitary {p q : ℕ} (hqp : q ≤ p)
    (B : OrthonormalFrame p q) :
    ∃ U : unitary (Matrix (Fin p) (Fin p) ℍ[ℝ]),
      (U.val : Matrix (Fin p) (Fin p) ℍ[ℝ]).submatrix id (Fin.castLE hqp) = B.val :=
  exists_unitary_extension p q hqp B.val B.property

theorem OrthonormalFrame.exists_unitary_with_dimension {p q : ℕ}
    (B : OrthonormalFrame p q) :
    ∃ (hqp : q ≤ p) (U : unitary (Matrix (Fin p) (Fin p) ℍ[ℝ])),
      (U.val : Matrix (Fin p) (Fin p) ℍ[ℝ]).submatrix id (Fin.castLE hqp) = B.val := by
  have hqp : q ≤ p := by
    simpa using (fullColumnRank_of_orthonormal B.val B.property).card_le
  obtain ⟨U, hU⟩ := B.exists_unitary hqp
  exact ⟨hqp, U, hU⟩

end Wishart.QuaternionMatrix
end
end CanonicalSource38

section CanonicalSource39
/- Source: Wishart/FieldCompressionWhitening.lean -/




/-!
# Whitening arbitrary full-column-rank field compressions

The normalized columns are explicitly `sqrt(Sigma) B (sqrt(Bᴴ Sigma B))⁻¹`.
Their Gram matrix is the identity, and their compression of the standard
matrix is exactly the manuscript's normalized compression of the original
matrix. This is valid for both nonsingular density laws and singular Gram
laws; the algebra does not require the random matrix to be invertible.
-/

noncomputable section
open Matrix MeasureTheory
open scoped Classical Quaternion ComplexOrder MatrixOrder Matrix.Norms.L2Operator Ring

namespace Wishart.FieldGaussian
open scoped Matrix.Norms.Frobenius

variable (F : Type*) [NormedRing F] [StarRing F] [CStarRing F]
  [InnerProductSpace ℝ F] [StarModule ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  [SMulCommClass ℝ F F] [IsScalarTower ℝ F F]

@[reducible] local instance compatibleScalarAlgebraStage4_3 : NormedAlgebra ℝ F where
  toAlgebra := Algebra.ofModule (fun r x y => smul_mul_assoc r x y)
    (fun r x y => mul_smul_comm r x y)
  norm_smul_le r x := (norm_smul r x).le


theorem gramWithFactor_map_congruence {r p : ℕ} (n : ℕ)
    (R : Matrix (Fin r) (Fin p) F) (B : Matrix (Fin p) (Fin p) F) :
    (gramWithFactor F n R).map (Wishart.FieldHermitian.congruence F B) =
      gramWithFactor F n (R * B) := by
  have hB : Measurable (Wishart.FieldHermitian.congruence F B) := by
    apply Measurable.subtype_mk
    fun_prop
  have hrows : Measurable (fun z : Fin n → Row F p => fun i => rowFactorCLM F B (z i)) := by
    apply measurable_pi_iff.mpr
    intro i
    exact (rowFactorCLM F B).continuous.measurable.comp (measurable_pi_apply i)
  unfold gramWithFactor
  rw [Measure.map_map hB (continuous_rowsGram F n p).measurable,
    ← (measurePreserving_gaussianRowsFactor (n := n) F R B).map_eq,
    Measure.map_map (continuous_rowsGram F n p).measurable hrows]
  apply congrArg ((Measure.pi (fun _ : Fin n => gaussianRowWithFactor F R)).map)
  funext z
  apply Subtype.ext
  exact (rowsGram_factor F B z).symm

end Wishart.FieldGaussian

namespace Wishart.ComplexMatrix
variable {p k : ℕ}

def whitenedColumns (Sigma : Matrix (Fin p) (Fin p) ℂ)
    (B : Matrix (Fin p) (Fin k) ℂ) : Matrix (Fin p) (Fin k) ℂ :=
  CFC.sqrt Sigma * B * (CFC.sqrt (compressionCovariance B Sigma))⁻¹

theorem compressionCovariance_posDef {Sigma : Matrix (Fin p) (Fin p) ℂ}
    (hSigma : Sigma.PosDef) {B : Matrix (Fin p) (Fin k) ℂ}
    (hB : Function.Injective B.mulVec) : (compressionCovariance B Sigma).PosDef :=
  hSigma.conjTranspose_mul_mul_same hB

/-- The normalized compression is exactly the inverse-square-root formula
in the manuscript; no invertibility of the sample matrix is required. -/
theorem normalizedCompression_eq_formula {Sigma : Matrix (Fin p) (Fin p) ℂ}
    (hSigma : Sigma.PosDef) {B : Matrix (Fin p) (Fin k) ℂ}
    (hB : Function.Injective B.mulVec) (X : Hermitian p) :
    (normalizedCompression B Sigma X : Matrix (Fin k) (Fin k) ℂ) =
      (CFC.sqrt (Bᴴ * Sigma * B))⁻¹ * (Bᴴ * (X : Matrix (Fin p) (Fin p) ℂ) * B) *
        (CFC.sqrt (Bᴴ * Sigma * B))⁻¹ := by
  have hC := compressionCovariance_posDef hSigma hB
  have hK : (CFC.sqrt (Bᴴ * Sigma * B)).PosDef :=
    Matrix.isStrictlyPositive_iff_posDef.mp
      (Matrix.isStrictlyPositive_iff_posDef.mpr hC).sqrt
  simp only [normalizedCompression, compressionCovariance, Matrix.conjTranspose_mul]
  rw [hK.inv.isHermitian.eq]
  simp only [Matrix.mul_assoc]

theorem whitenedColumns_gram {Sigma : Matrix (Fin p) (Fin p) ℂ}
    (hSigma : Sigma.PosDef) {B : Matrix (Fin p) (Fin k) ℂ}
    (hB : Function.Injective B.mulVec) :
    (whitenedColumns Sigma B)ᴴ * whitenedColumns Sigma B = 1 := by
  let C := compressionCovariance B Sigma
  let K := CFC.sqrt C
  have hC : C.PosDef := compressionCovariance_posDef hSigma hB
  have hK : K.PosDef := Matrix.isStrictlyPositive_iff_posDef.mp
    (Matrix.isStrictlyPositive_iff_posDef.mpr hC).sqrt
  have hS : (CFC.sqrt Sigma).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg Sigma)).isHermitian
  have hKi : (K⁻¹)ᴴ = K⁻¹ := hK.inv.isHermitian.eq
  have hKunit : IsUnit K.det := (Matrix.isUnit_iff_isUnit_det K).mp hK.isUnit
  have hmiddle : Bᴴ * (CFC.sqrt Sigma * CFC.sqrt Sigma) * B = C := by
    rw [CFC.sqrt_mul_sqrt_self Sigma hSigma.posSemidef.nonneg]
    rfl
  change (CFC.sqrt Sigma * B * K⁻¹)ᴴ * (CFC.sqrt Sigma * B * K⁻¹) = 1
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hS.eq, hKi]
  calc
    _ = K⁻¹ * (Bᴴ * (CFC.sqrt Sigma * CFC.sqrt Sigma) * B) * K⁻¹ := by
      simp only [Matrix.mul_assoc]
    _ = K⁻¹ * C * K⁻¹ := by rw [hmiddle]
    _ = K⁻¹ * (K * K) * K⁻¹ := by rw [CFC.sqrt_mul_sqrt_self C hC.posSemidef.nonneg]
    _ = 1 := by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul K hKunit, Matrix.one_mul,
        Matrix.mul_nonsing_inv K hKunit]

theorem normalizedCompression_whiten {Sigma : Matrix (Fin p) (Fin p) ℂ}
    (hSigma : Sigma.PosDef) (B : Matrix (Fin p) (Fin k) ℂ) (Y : Hermitian p) :
    normalizedCompression B Sigma (Wishart.FieldHermitian.congruence ℂ (CFC.sqrt Sigma) Y) =
      ⟨(whitenedColumns Sigma B)ᴴ * (Y : Matrix (Fin p) (Fin p) ℂ) * whitenedColumns Sigma B,
        Matrix.isHermitian_conjTranspose_mul_mul _ (WishartVerification.hermitian_matrix_coe Y)⟩ := by
  apply Subtype.ext
  have hS : (CFC.sqrt Sigma).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg Sigma)).isHermitian
  simp only [normalizedCompression, whitenedColumns, Wishart.FieldHermitian.congruence,
    Matrix.conjTranspose_mul, hS.eq, Matrix.mul_assoc]

theorem gramMeasure_covariance_law (n : ℕ) (Sigma : Matrix (Fin p) (Fin p) ℂ) :
    gramMeasure n Sigma = (gramMeasure n (1 : Matrix (Fin p) (Fin p) ℂ)).map
      (Wishart.FieldHermitian.congruence ℂ (CFC.sqrt Sigma)) := by
  simp only [gramMeasure, CFC.sqrt_one]
  convert (Wishart.FieldGaussian.gramWithFactor_map_congruence ℂ n (1 : Matrix (Fin p) (Fin p) ℂ) (CFC.sqrt Sigma)).symm using 1 <;> (first | rfl | simp only [Matrix.one_mul])

theorem normalizedCompression_eq_compress_of_gram_one
    (B : Matrix (Fin p) (Fin k) ℂ) (hB : Bᴴ * B = 1) (X : Hermitian p) :
    normalizedCompression B (1 : Matrix (Fin p) (Fin p) ℂ) X =
      ⟨Bᴴ * (X : Matrix (Fin p) (Fin p) ℂ) * B,
        Matrix.isHermitian_conjTranspose_mul_mul B (WishartVerification.hermitian_matrix_coe X)⟩ := by
  simp only [normalizedCompression, compressionCovariance, Matrix.mul_one, hB,
    CFC.sqrt_one, inv_one]

end Wishart.ComplexMatrix

namespace Wishart.QuaternionMatrix
open scoped Matrix.Norms.Frobenius
variable {p k : ℕ}

def whitenedColumns (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ])
    (B : Matrix (Fin p) (Fin k) ℍ[ℝ]) : Matrix (Fin p) (Fin k) ℍ[ℝ] :=
  sqrt Sigma * B * (sqrt (compressionCovariance B Sigma))⁻¹ʳ

theorem compressionCovariance_posDef {Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]}
    (hSigma : PosDef Sigma) {B : Matrix (Fin p) (Fin k) ℍ[ℝ]}
    (hB : FullColumnRank B) : PosDef (compressionCovariance B Sigma) :=
  FullColumnRank.congruence_posDef hSigma hB

/-- The actual quaternion congruence equals the manuscript's ordered
inverse-square-root formula, with multiplication order retained. -/
theorem normalizedCompression_eq_formula {Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]}
    (hSigma : PosDef Sigma) {B : Matrix (Fin p) (Fin k) ℍ[ℝ]}
    (hB : FullColumnRank B) (X : Hermitian p) :
    (normalizedCompression B Sigma X : Matrix (Fin k) (Fin k) ℍ[ℝ]) =
      (sqrt (Bᴴ * Sigma * B))⁻¹ʳ * (Bᴴ * (X : Matrix (Fin p) (Fin p) ℍ[ℝ]) * B) *
        (sqrt (Bᴴ * Sigma * B))⁻¹ʳ := by
  have hK : PosDef (sqrt (Bᴴ * Sigma * B)) :=
    (compressionCovariance_posDef hSigma hB).sqrt
  simp only [normalizedCompression, compressionCovariance, Matrix.conjTranspose_mul]
  rw [hK.ringInverse.isHermitian.eq]
  simp only [Matrix.mul_assoc]

theorem whitenedColumns_gram {Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]}
    (hSigma : PosDef Sigma) {B : Matrix (Fin p) (Fin k) ℍ[ℝ]}
    (hB : FullColumnRank B) :
    (whitenedColumns Sigma B)ᴴ * whitenedColumns Sigma B = 1 := by
  let C := compressionCovariance B Sigma
  let K := sqrt C
  have hC : PosDef C := compressionCovariance_posDef hSigma hB
  have hK : PosDef K := hC.sqrt
  have hKi : (K⁻¹ʳ)ᴴ = K⁻¹ʳ := hK.ringInverse.isHermitian.eq
  have hmiddle : Bᴴ * (sqrt Sigma * sqrt Sigma) * B = C := by
    rw [sqrt_mul_self hSigma.posSemidef]
    rfl
  change (sqrt Sigma * B * K⁻¹ʳ)ᴴ * (sqrt Sigma * B * K⁻¹ʳ) = 1
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hSigma.sqrt.isHermitian.eq, hKi]
  calc
    _ = K⁻¹ʳ * (Bᴴ * (sqrt Sigma * sqrt Sigma) * B) * K⁻¹ʳ := by
      simp only [Matrix.mul_assoc]
    _ = K⁻¹ʳ * C * K⁻¹ʳ := by rw [hmiddle]
    _ = K⁻¹ʳ * (K * K) * K⁻¹ʳ := by rw [sqrt_mul_self hC.posSemidef]
    _ = 1 := by
      rw [← Matrix.mul_assoc, Ring.inverse_mul_cancel K hK.isUnit, Matrix.one_mul,
        Ring.mul_inverse_cancel K hK.isUnit]

theorem normalizedCompression_whiten {Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]}
    (hSigma : PosDef Sigma) (B : Matrix (Fin p) (Fin k) ℍ[ℝ]) (Y : Hermitian p) :
    normalizedCompression B Sigma (Wishart.FieldHermitian.congruence ℍ[ℝ] (sqrt Sigma) Y) =
      ⟨(whitenedColumns Sigma B)ᴴ * (Y : Matrix (Fin p) (Fin p) ℍ[ℝ]) * whitenedColumns Sigma B,
        Matrix.isHermitian_conjTranspose_mul_mul _ (WishartVerification.hermitian_matrix_coe Y)⟩ := by
  apply Subtype.ext
  simp only [normalizedCompression, whitenedColumns, Wishart.FieldHermitian.congruence,
    Matrix.conjTranspose_mul, hSigma.sqrt.isHermitian.eq, Matrix.mul_assoc]

theorem sqrt_one_matrix : sqrt (1 : Matrix (Fin p) (Fin p) ℍ[ℝ]) = 1 := by
  apply complexRepresentation_injective
  rw [complexRepresentation_sqrt posDef_one.posSemidef, complexRepresentation_one, CFC.sqrt_one]

theorem gramMeasure_covariance_law (n : ℕ) (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) :
    gramMeasure n Sigma = (gramMeasure n (1 : Matrix (Fin p) (Fin p) ℍ[ℝ])).map
      (Wishart.FieldHermitian.congruence ℍ[ℝ] (sqrt Sigma)) := by
  simp only [gramMeasure, sqrt_one_matrix]
  convert (Wishart.FieldGaussian.gramWithFactor_map_congruence ℍ[ℝ] n (1 : Matrix (Fin p) (Fin p) ℍ[ℝ]) (sqrt Sigma)).symm using 1 <;> (first | rfl | simp only [Matrix.one_mul])

theorem normalizedCompression_eq_compress_of_gram_one
    (B : Matrix (Fin p) (Fin k) ℍ[ℝ]) (hB : Bᴴ * B = 1) (X : Hermitian p) :
    normalizedCompression B (1 : Matrix (Fin p) (Fin p) ℍ[ℝ]) X =
      ⟨Bᴴ * (X : Matrix (Fin p) (Fin p) ℍ[ℝ]) * B,
        Matrix.isHermitian_conjTranspose_mul_mul B (WishartVerification.hermitian_matrix_coe X)⟩ := by
  simp only [normalizedCompression, compressionCovariance, Matrix.mul_one, hB,
    sqrt_one_matrix, Ring.inverse_one]

end Wishart.QuaternionMatrix
end
end CanonicalSource39
