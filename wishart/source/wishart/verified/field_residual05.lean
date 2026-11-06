module

public import wishart.verified.field_residual04
public import wishart.verified.real_remainder11

/- Recovered canonical proof stage; see verification/recovery-patches.json. -/

@[expose] public section

open scoped Matrix.Norms.Frobenius

section CanonicalSource40
/- Source: Wishart/FieldCompressionRotation.lean -/



/-!
# Exact reduction of an arbitrary orthonormal compression to a leading block

A completed unitary frame rotates all the other compression matrices at the
same time. The formulas are pointwise matrix identities, so they apply to
singular as well as positive-definite random matrices.
-/

noncomputable section
open Matrix MeasureTheory
open scoped Classical Quaternion ComplexOrder Ring
namespace Wishart.FieldGaussian
open Wishart.FieldCharts

variable (F : Type*) [NormedDivisionRing F]
  [StarRing F] [CStarRing F]
  [InnerProductSpace ℝ F] [StarModule ℝ F] [FiniteDimensional ℝ F]
  [SMulCommClass ℝ F F] [IsScalarTower ℝ F F]
  [MeasurableSpace F] [BorelSpace F]

@[reducible] local instance compatibleScalarAlgebraStage5_1 : NormedAlgebra ℝ F where
  toAlgebra := Algebra.ofModule (fun r x y => smul_mul_assoc r x y)
    (fun r x y => mul_smul_comm r x y)
  norm_smul_le r x := (norm_smul r x).le

def leadingSelector (p q : ℕ) : Matrix (Fin (p + q)) (Fin p) F :=
  (1 : Matrix (Fin (p + q)) (Fin (p + q)) F).submatrix id (Fin.castAdd q)

theorem compress_leadingSelector {p q : ℕ} (X : Hermitian F (p + q)) :
    compress F (leadingSelector F p q) X = Wishart.FieldHermitian.leadingBlock F X := by
  apply Subtype.ext
  change ((1 : Matrix (Fin (p + q)) (Fin (p + q)) F).submatrix id (Fin.castAdd q))ᴴ *
    (X : Matrix (Fin (p + q)) (Fin (p + q)) F) *
      (1 : Matrix (Fin (p + q)) (Fin (p + q)) F).submatrix id (Fin.castAdd q) = _
  rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one]
  have hl := Matrix.one_submatrix_mul (Fin.castAdd q) (Equiv.refl (Fin (p + q)))
    (X : Matrix (Fin (p + q)) (Fin (p + q)) F)
  have hr := Matrix.mul_submatrix_one (Equiv.refl (Fin (p + q))) (Fin.castAdd q)
    ((X : Matrix (Fin (p + q)) (Fin (p + q)) F).submatrix (Fin.castAdd q) id)
  simp only [Equiv.coe_refl, Equiv.refl_symm, Function.id_comp] at hl hr
  rw [hl, hr]
  rfl

theorem compress_unitaryConjugate {p k : ℕ}
    (U : unitary (Matrix (Fin p) (Fin p) F)) (B : Matrix (Fin p) (Fin k) F)
    (X : Hermitian F p) :
    compress F B (unitaryConjugate F U X) =
      compress F ((star U : Matrix (Fin p) (Fin p) F) * B) X := by
  apply Subtype.ext
  simp only [compress, unitaryConjugate, Matrix.conjTranspose_mul,
    Unitary.coe_star, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

theorem frame_mul_leadingSelector {p q : ℕ}
    (U : unitary (Matrix (Fin (p + q)) (Fin (p + q)) F))
    (B : Matrix (Fin (p + q)) (Fin p) F)
    (hB : (U : Matrix (Fin (p + q)) (Fin (p + q)) F).submatrix id (Fin.castAdd q) = B) :
    (U : Matrix (Fin (p + q)) (Fin (p + q)) F) * leadingSelector F p q = B := by
  have h := Matrix.mul_submatrix_one (Equiv.refl (Fin (p + q))) (Fin.castAdd q)
    (U : Matrix (Fin (p + q)) (Fin (p + q)) F)
  simpa only [Equiv.coe_refl, Equiv.refl_symm, Function.id_comp, leadingSelector, hB] using h

theorem star_frame_mul_columns {p q : ℕ}
    (U : unitary (Matrix (Fin (p + q)) (Fin (p + q)) F))
    (B : Matrix (Fin (p + q)) (Fin p) F)
    (hB : (U : Matrix (Fin (p + q)) (Fin (p + q)) F).submatrix id (Fin.castAdd q) = B) :
    (star U : Matrix (Fin (p + q)) (Fin (p + q)) F) * B = leadingSelector F p q := by
  rw [← frame_mul_leadingSelector F U B hB, ← Matrix.mul_assoc,
    Unitary.coe_star_mul_self, Matrix.one_mul]

theorem compress_completed_frame {p q : ℕ}
    (U : unitary (Matrix (Fin (p + q)) (Fin (p + q)) F))
    (B : Matrix (Fin (p + q)) (Fin p) F)
    (hB : (U : Matrix (Fin (p + q)) (Fin (p + q)) F).submatrix id (Fin.castAdd q) = B)
    (X : Hermitian F (p + q)) :
    compress F B (unitaryConjugate F U X) = Wishart.FieldHermitian.leadingBlock F X := by
  rw [compress_unitaryConjugate, star_frame_mul_columns F U B hB, compress_leadingSelector]

theorem injective_mulVec_of_gram_eq_one {m k : ℕ}
    (B : Matrix (Fin m) (Fin k) F) (hB : Bᴴ * B = 1) :
    Function.Injective B.mulVec := by
  have hleft : Function.LeftInverse Bᴴ.mulVec B.mulVec := by
    intro x
    rw [Matrix.mulVec_mulVec, hB, Matrix.one_mulVec]
  exact hleft.injective

end Wishart.FieldGaussian

namespace Wishart.QuaternionMatrix
open Wishart.FieldGaussian

theorem leadingBlock_posSemidef {p q : ℕ} (X : Hermitian (p + q)) (hX : PosSemidef X.val) :
    PosSemidef (Wishart.FieldHermitian.leadingBlock ℍ[ℝ] X).val := by
  have h := hX.congruence (leadingSelector ℍ[ℝ] p q)
  have he := congrArg (fun Y : Wishart.FieldCharts.Hermitian ℍ[ℝ] p => Y.val)
    (compress_leadingSelector ℍ[ℝ] X)
  change (leadingSelector ℍ[ℝ] p q)ᴴ * X.val * leadingSelector ℍ[ℝ] p q =
    (Wishart.FieldHermitian.leadingBlock ℍ[ℝ] X).val at he
  exact he ▸ h

end Wishart.QuaternionMatrix
end
end CanonicalSource40

section CanonicalSource41
/- Source: Wishart/FieldArbitraryComparison.lean -/



/-!
# Arbitrary selected orthonormal compressions

A genuine completed unitary rotates the selected frame to the first columns.
The entire law is invariant under that rotation, while every other arbitrary
compression is rotated by the same matrix. This proves the finite comparisons
needed for monotone passage to the full boundary profiles.
-/

noncomputable section
open Matrix MeasureTheory Set
open scoped Classical Quaternion ComplexOrder ENNReal

namespace Wishart.ComplexMatrix
open Wishart.FieldCharts Wishart.FieldGaussian Wishart.Spectral

theorem orthonormal_selected_finite_comparison {p q : ℕ} {α : ℝ}
    (hα : ((p + q : ℕ) : ℝ) - 1 < α) {ι : Type*} [Fintype ι]
    (B₀ : Matrix (Fin (p + q)) (Fin p) ℂ) (hB₀ : B₀ᴴ * B₀ = 1)
    (c : ℝ) (hc0 : 0 ≤ c)
    (h₀ : (Fin p → ℝ) → ℝ) (hc₀ : ConvexOn ℝ univ h₀) (hm₀ : Monotone h₀) (L₀ : ℕ)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin (p + q)) (Fin (k i)) ℂ)
    (Q : ∀ i, Hermitian (k i)) (hQ : ∀ i, (Q i : Matrix (Fin (k i)) (Fin (k i)) ℂ).PosSemidef)
    (h : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hc : ∀ i, ConvexOn ℝ univ (h i)) (hm : ∀ i, Monotone (h i)) (L : ι → ℕ) :
    (∫⁻ X, ENNReal.ofReal (complexFaceApprox hc₀ hm₀ L₀ (Wishart.FieldSpectral.identityShift (compress ℂ B₀ X) c))
      ∂wishartMeasure α (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ)) *
    (∫⁻ X, ENNReal.ofReal (∏ i, complexFaceApprox (hc i) (hm i) (L i) (Q i + compress ℂ (B i) X))
      ∂wishartMeasure α (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ)) ≤
    ∫⁻ X, ENNReal.ofReal (complexFaceApprox hc₀ hm₀ L₀ (Wishart.FieldSpectral.identityShift (compress ℂ B₀ X) c)) *
      ENNReal.ofReal (∏ i, complexFaceApprox (hc i) (hm i) (L i) (Q i + compress ℂ (B i) X))
      ∂wishartMeasure α (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) := by
  obtain ⟨U, hU⟩ := Wishart.FieldSpectral.exists_unitary_extension (Nat.le_add_right p q) B₀ hB₀
  have hcast : (Fin.castLE (Nat.le_add_right p q) : Fin p → Fin (p + q)) =
      Fin.castAdd q := by funext i; rfl
  rw [hcast] at hU
  let f : Hermitian (p + q) → ℝ≥0∞ := fun X => ENNReal.ofReal
    (complexFaceApprox hc₀ hm₀ L₀ (Wishart.FieldSpectral.identityShift (compress ℂ B₀ X) c))
  let g : Hermitian (p + q) → ℝ≥0∞ := fun X => ENNReal.ofReal
    (∏ i, complexFaceApprox (hc i) (hm i) (L i) (Q i + compress ℂ (B i) X))
  have hf : Measurable f :=
    (continuous_complexFaceApprox hc₀ hm₀ L₀).measurable.ennreal_ofReal.comp
      (((continuous_compress ℂ B₀).add continuous_const).measurable)
  have hg : Measurable g := by
    apply Measurable.ennreal_ofReal
    apply Finset.measurable_prod
    intro i hi
    exact (continuous_complexFaceApprox (hc i) (hm i) (L i)).measurable.comp
      ((continuous_const.add (continuous_compress ℂ (B i))).measurable)
  have hmap := map_unitaryConjugate_wishart hα U
  have hUm : Measurable (unitaryConjugate ℂ U) := by
    apply Measurable.subtype_mk
    fun_prop
  have hint (t : Hermitian (p + q) → ℝ≥0∞) (ht : Measurable t) :
      (∫⁻ X, t X ∂wishartMeasure α (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ)) =
      ∫⁻ X, t (unitaryConjugate ℂ U X)
        ∂wishartMeasure α (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) := by
    conv_lhs => rw [← hmap, lintegral_map ht hUm]
  change (∫⁻ X, f X ∂_) * (∫⁻ X, g X ∂_) ≤ ∫⁻ X, f X * g X ∂_
  rw [hint f hf, hint g hg, hint (fun X => f X * g X) (hf.mul hg)]
  have hselected (X : Hermitian (p + q)) :
      compress ℂ B₀ (unitaryConjugate ℂ U X) =
        Wishart.FieldHermitian.leadingBlock ℂ X := by
    simpa only [compress, unitaryConjugate, Wishart.FieldHermitian.leadingBlock] using
      (compress_completed_frame ℂ U B₀ hU X)
  have hother (i : ι) (X : Hermitian (p + q)) :
      compress ℂ (B i) (unitaryConjugate ℂ U X) =
        compress ℂ ((star U : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) * B i) X := by
    apply Subtype.ext
    simp only [compress, unitaryConjugate, Unitary.coe_star, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  simp only [f, g, hselected, hother]
  exact leading_selected_finite_comparison hα c hc0 h₀ hc₀ hm₀ L₀
    k (fun i => (star U : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) * B i) Q hQ h hc hm L

end Wishart.ComplexMatrix

namespace Wishart.QuaternionMatrix
open Wishart.FieldCharts Wishart.FieldGaussian Wishart.Spectral

theorem orthonormal_selected_finite_comparison {p q : ℕ} {α : ℝ}
    (hα : ((p + q : ℕ) : ℝ) - 1 < α) {ι : Type*} [Fintype ι]
    (B₀ : Matrix (Fin (p + q)) (Fin p) ℍ[ℝ]) (hB₀ : B₀ᴴ * B₀ = 1)
    (c : ℝ) (hc0 : 0 ≤ c)
    (h₀ : (Fin p → ℝ) → ℝ) (hc₀ : ConvexOn ℝ univ h₀) (hm₀ : Monotone h₀) (L₀ : ℕ)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin (p + q)) (Fin (k i)) ℍ[ℝ])
    (Q : ∀ i, Hermitian (k i)) (hQ : ∀ i, PosSemidef (Q i).val)
    (h : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hc : ∀ i, ConvexOn ℝ univ (h i)) (hm : ∀ i, Monotone (h i)) (L : ι → ℕ) :
    (∫⁻ X, ENNReal.ofReal (quaternionFaceApprox hc₀ hm₀ L₀ (identityShift (compress ℍ[ℝ] B₀ X) c))
      ∂wishartMeasure α (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℍ[ℝ])) *
    (∫⁻ X, ENNReal.ofReal (∏ i, quaternionFaceApprox (hc i) (hm i) (L i) (Q i + compress ℍ[ℝ] (B i) X))
      ∂wishartMeasure α (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℍ[ℝ])) ≤
    ∫⁻ X, ENNReal.ofReal (quaternionFaceApprox hc₀ hm₀ L₀ (identityShift (compress ℍ[ℝ] B₀ X) c)) *
      ENNReal.ofReal (∏ i, quaternionFaceApprox (hc i) (hm i) (L i) (Q i + compress ℍ[ℝ] (B i) X))
      ∂wishartMeasure α (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℍ[ℝ]) := by
  obtain ⟨U, hU⟩ := exists_unitary_extension (p + q) p (Nat.le_add_right p q) B₀ hB₀
  have hcast : (Fin.castLE (Nat.le_add_right p q) : Fin p → Fin (p + q)) =
      Fin.castAdd q := by funext i; rfl
  rw [hcast] at hU
  let f : Hermitian (p + q) → ℝ≥0∞ := fun X => ENNReal.ofReal
    (quaternionFaceApprox hc₀ hm₀ L₀ (identityShift (compress ℍ[ℝ] B₀ X) c))
  let g : Hermitian (p + q) → ℝ≥0∞ := fun X => ENNReal.ofReal
    (∏ i, quaternionFaceApprox (hc i) (hm i) (L i) (Q i + compress ℍ[ℝ] (B i) X))
  have hf : Measurable f :=
    (continuous_quaternionFaceApprox hc₀ hm₀ L₀).measurable.ennreal_ofReal.comp
      (((continuous_compress ℍ[ℝ] B₀).add continuous_const).measurable)
  have hg : Measurable g := by
    apply Measurable.ennreal_ofReal
    apply Finset.measurable_prod
    intro i hi
    exact (continuous_quaternionFaceApprox (hc i) (hm i) (L i)).measurable.comp
      ((continuous_const.add (continuous_compress ℍ[ℝ] (B i))).measurable)
  have hmap := map_unitaryConjugate_wishart hα U
  have hUm : Measurable (unitaryConjugate ℍ[ℝ] U) := by
    apply Measurable.subtype_mk
    fun_prop
  have hint (t : Hermitian (p + q) → ℝ≥0∞) (ht : Measurable t) :
      (∫⁻ X, t X ∂wishartMeasure α (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℍ[ℝ])) =
      ∫⁻ X, t (unitaryConjugate ℍ[ℝ] U X)
        ∂wishartMeasure α (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℍ[ℝ]) := by
    conv_lhs => rw [← hmap, lintegral_map ht hUm]
  change (∫⁻ X, f X ∂_) * (∫⁻ X, g X ∂_) ≤ ∫⁻ X, f X * g X ∂_
  rw [hint f hf, hint g hg, hint (fun X => f X * g X) (hf.mul hg)]
  have hselected (X : Hermitian (p + q)) :
      compress ℍ[ℝ] B₀ (unitaryConjugate ℍ[ℝ] U X) =
        Wishart.FieldHermitian.leadingBlock ℍ[ℝ] X := by
    simpa only [compress, unitaryConjugate, Wishart.FieldHermitian.leadingBlock] using
      (compress_completed_frame ℍ[ℝ] U B₀ hU X)
  have hother (i : ι) (X : Hermitian (p + q)) :
      compress ℍ[ℝ] (B i) (unitaryConjugate ℍ[ℝ] U X) =
        compress ℍ[ℝ] (star U.val * B i) X := by
    apply Subtype.ext
    simp only [compress, unitaryConjugate, Unitary.coe_star, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  simp only [f, g, hselected, hother]
  exact leading_selected_finite_comparison hα c hc0 h₀ hc₀ hm₀ L₀
    k (fun i => star U.val * B i) Q hQ h hc hm L

end Wishart.QuaternionMatrix
end
end CanonicalSource41

section CanonicalSource42
/- Source: Wishart/FieldDensityComparison.lean -/



/-!
# Real-shape comparisons at arbitrary covariance

Whitening gives an exact pushforward of the literal matrix density. The
selected normalized columns are orthonormal; their dimension bound follows
from their genuine injectivity. Every other compression is transported by the
same pointwise congruence. No restriction on overlaps is introduced.
-/

noncomputable section
open Matrix MeasureTheory Set
open scoped Classical Quaternion ComplexOrder ENNReal
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace Wishart.ComplexMatrix
open Wishart.FieldGaussian Wishart.Spectral

theorem density_selected_finite_comparison {m k₀ : ℕ} {α : ℝ}
    (hα : (m : ℝ) - 1 < α) (Sigma : Matrix (Fin m) (Fin m) ℂ) (hSigma : Sigma.PosDef)
    {ι : Type*} [Fintype ι]
    (B₀ : Matrix (Fin m) (Fin k₀) ℂ) (hB₀ : Function.Injective B₀.mulVec)
    (c : ℝ) (hc0 : 0 ≤ c)
    (h₀ : (Fin k₀ → ℝ) → ℝ) (hc₀ : ConvexOn ℝ univ h₀) (hm₀ : Monotone h₀) (L₀ : ℕ)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin m) (Fin (k i)) ℂ)
    (Q : ∀ i, Hermitian (k i)) (hQ : ∀ i, (Q i : Matrix (Fin (k i)) (Fin (k i)) ℂ).PosSemidef)
    (h : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hc : ∀ i, ConvexOn ℝ univ (h i)) (hm : ∀ i, Monotone (h i)) (L : ι → ℕ) :
    (∫⁻ X, ENNReal.ofReal (complexFaceApprox hc₀ hm₀ L₀
      (Wishart.FieldSpectral.identityShift (normalizedCompression B₀ Sigma X) c)) ∂wishartMeasure α Sigma) *
    (∫⁻ X, ENNReal.ofReal (∏ i, complexFaceApprox (hc i) (hm i) (L i)
      (Q i + normalizedCompression (B i) Sigma X)) ∂wishartMeasure α Sigma) ≤
    ∫⁻ X, ENNReal.ofReal (complexFaceApprox hc₀ hm₀ L₀
      (Wishart.FieldSpectral.identityShift (normalizedCompression B₀ Sigma X) c)) *
      ENNReal.ofReal (∏ i, complexFaceApprox (hc i) (hm i) (L i)
        (Q i + normalizedCompression (B i) Sigma X)) ∂wishartMeasure α Sigma := by
  have hdim := LinearMap.finrank_le_finrank_of_injective (f := B₀.mulVecLin) hB₀
  have hk : k₀ ≤ m := by simpa using hdim
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hk
  let f : Hermitian (k₀ + q) → ℝ≥0∞ := fun X => ENNReal.ofReal
    (complexFaceApprox hc₀ hm₀ L₀ (Wishart.FieldSpectral.identityShift (normalizedCompression B₀ Sigma X) c))
  let g : Hermitian (k₀ + q) → ℝ≥0∞ := fun X => ENNReal.ofReal
    (∏ i, complexFaceApprox (hc i) (hm i) (L i) (Q i + normalizedCompression (B i) Sigma X))
  have hcomp {k : ℕ} (D : Matrix (Fin (k₀ + q)) (Fin k) ℂ) :
      Continuous (normalizedCompression D Sigma) := by
    apply Continuous.subtype_mk
    fun_prop
  have hf : Measurable f :=
    (continuous_complexFaceApprox hc₀ hm₀ L₀).measurable.ennreal_ofReal.comp
      ((hcomp B₀).add continuous_const).measurable
  have hg : Measurable g := by
    apply Measurable.ennreal_ofReal
    apply Finset.measurable_prod
    intro i hi
    exact (continuous_complexFaceApprox (hc i) (hm i) (L i)).measurable.comp
      (continuous_const.add (hcomp (B i))).measurable
  have hT : Measurable (Wishart.FieldHermitian.congruence ℂ (CFC.sqrt Sigma)) := by
    apply Measurable.subtype_mk
    fun_prop
  have hlaw := (finiteDensity_wishart_and_covariance_law hα hSigma).2
  change (∫⁻ X, f X ∂wishartMeasure α Sigma) * (∫⁻ X, g X ∂wishartMeasure α Sigma) ≤
    ∫⁻ X, f X * g X ∂wishartMeasure α Sigma
  rw [hlaw, lintegral_map hf hT, lintegral_map hg hT, lintegral_map (f := fun X => f X * g X) (hf.mul hg) hT]
  have hfinite := orthonormal_selected_finite_comparison hα
    (whitenedColumns Sigma B₀) (whitenedColumns_gram hSigma hB₀)
    c hc0 h₀ hc₀ hm₀ L₀ k (fun i => whitenedColumns Sigma (B i)) Q hQ h hc hm L
  simpa only [f, g, normalizedCompression_whiten hSigma, compress] using hfinite

end Wishart.ComplexMatrix

namespace Wishart.QuaternionMatrix
open Wishart.FieldGaussian Wishart.Spectral

theorem density_selected_finite_comparison {m k₀ : ℕ} {α : ℝ}
    (hα : (m : ℝ) - 1 < α) (Sigma : Matrix (Fin m) (Fin m) ℍ[ℝ]) (hSigma : PosDef Sigma)
    {ι : Type*} [Fintype ι]
    (B₀ : Matrix (Fin m) (Fin k₀) ℍ[ℝ]) (hB₀ : FullColumnRank B₀)
    (c : ℝ) (hc0 : 0 ≤ c)
    (h₀ : (Fin k₀ → ℝ) → ℝ) (hc₀ : ConvexOn ℝ univ h₀) (hm₀ : Monotone h₀) (L₀ : ℕ)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin m) (Fin (k i)) ℍ[ℝ])
    (Q : ∀ i, Hermitian (k i)) (hQ : ∀ i, PosSemidef (Q i).val)
    (h : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hc : ∀ i, ConvexOn ℝ univ (h i)) (hm : ∀ i, Monotone (h i)) (L : ι → ℕ) :
    (∫⁻ X, ENNReal.ofReal (quaternionFaceApprox hc₀ hm₀ L₀
      (identityShift (normalizedCompression B₀ Sigma X) c)) ∂wishartMeasure α Sigma) *
    (∫⁻ X, ENNReal.ofReal (∏ i, quaternionFaceApprox (hc i) (hm i) (L i)
      (Q i + normalizedCompression (B i) Sigma X)) ∂wishartMeasure α Sigma) ≤
    ∫⁻ X, ENNReal.ofReal (quaternionFaceApprox hc₀ hm₀ L₀
      (identityShift (normalizedCompression B₀ Sigma X) c)) *
      ENNReal.ofReal (∏ i, quaternionFaceApprox (hc i) (hm i) (L i)
        (Q i + normalizedCompression (B i) Sigma X)) ∂wishartMeasure α Sigma := by
  have hk : k₀ ≤ m := by simpa using hB₀.card_le
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hk
  let f : Hermitian (k₀ + q) → ℝ≥0∞ := fun X => ENNReal.ofReal
    (quaternionFaceApprox hc₀ hm₀ L₀ (identityShift (normalizedCompression B₀ Sigma X) c))
  let g : Hermitian (k₀ + q) → ℝ≥0∞ := fun X => ENNReal.ofReal
    (∏ i, quaternionFaceApprox (hc i) (hm i) (L i) (Q i + normalizedCompression (B i) Sigma X))
  have hcomp {k : ℕ} (D : Matrix (Fin (k₀ + q)) (Fin k) ℍ[ℝ]) :
      Continuous (normalizedCompression D Sigma) := by
    apply Continuous.subtype_mk
    fun_prop
  have hf : Measurable f :=
    (continuous_quaternionFaceApprox hc₀ hm₀ L₀).measurable.ennreal_ofReal.comp
      ((hcomp B₀).add continuous_const).measurable
  have hg : Measurable g := by
    apply Measurable.ennreal_ofReal
    apply Finset.measurable_prod
    intro i hi
    exact (continuous_quaternionFaceApprox (hc i) (hm i) (L i)).measurable.comp
      (continuous_const.add (hcomp (B i))).measurable
  have hT : Measurable (Wishart.FieldHermitian.congruence ℍ[ℝ] (sqrt Sigma)) := by
    apply Measurable.subtype_mk
    fun_prop
  have hlaw := (finiteDensity_wishart_and_covariance_law hα hSigma).2
  change (∫⁻ X, f X ∂wishartMeasure α Sigma) * (∫⁻ X, g X ∂wishartMeasure α Sigma) ≤
    ∫⁻ X, f X * g X ∂wishartMeasure α Sigma
  rw [hlaw, lintegral_map hf hT, lintegral_map hg hT, lintegral_map (f := fun X => f X * g X) (hf.mul hg) hT]
  have hfinite := orthonormal_selected_finite_comparison hα
    (whitenedColumns Sigma B₀) (whitenedColumns_gram hSigma hB₀)
    c hc0 h₀ hc₀ hm₀ L₀ k (fun i => whitenedColumns Sigma (B i)) Q hQ h hc hm L
  simpa only [f, g, normalizedCompression_whiten hSigma, compress] using hfinite

end Wishart.QuaternionMatrix
end
end CanonicalSource42

section CanonicalSource43
/- Source: Wishart/FieldCompressionSupport.lean -/



/-!
# Measurability and positive-cone support of the actual field objects

Normalized compression is a congruence even when evaluated outside the
intended full-rank parameters. Positivity of both density and integer laws is
therefore transported without an invertibility assumption on the sample.
-/

noncomputable section
open Matrix MeasureTheory Set
open scoped Classical Quaternion ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Wishart.ComplexMatrix
variable {p k : ℕ}

theorem continuous_normalizedCompression (B : Matrix (Fin p) (Fin k) ℂ)
    (Sigma : Matrix (Fin p) (Fin p) ℂ) : Continuous (normalizedCompression B Sigma) := by
  apply Continuous.subtype_mk
  fun_prop

theorem measurable_normalizedCompression (B : Matrix (Fin p) (Fin k) ℂ)
    (Sigma : Matrix (Fin p) (Fin p) ℂ) : Measurable (normalizedCompression B Sigma) :=
  (continuous_normalizedCompression B Sigma).measurable

theorem normalizedCompression_posSemidef (B : Matrix (Fin p) (Fin k) ℂ)
    (Sigma : Matrix (Fin p) (Fin p) ℂ) (X : Hermitian p)
    (hX : (X : Matrix (Fin p) (Fin p) ℂ).PosSemidef) :
    (normalizedCompression B Sigma X : Matrix (Fin k) (Fin k) ℂ).PosSemidef :=
  hX.conjTranspose_mul_mul_same _

theorem measurableSet_posSemidef :
    MeasurableSet {X : Hermitian p | (X : Matrix (Fin p) (Fin p) ℂ).PosSemidef} := by
  simp_rw [← Matrix.nonneg_iff_posSemidef]
  exact (isClosed_le continuous_const continuous_subtype_val).measurableSet

theorem gramMeasure_ae_posSemidef (n : ℕ) (Sigma : Matrix (Fin p) (Fin p) ℂ) :
    ∀ᵐ (X : Hermitian p) ∂gramMeasure n Sigma, (X : Matrix (Fin p) (Fin p) ℂ).PosSemidef := by
  unfold gramMeasure Wishart.FieldGaussian.gramWithFactor
  rw [ae_map_iff (Wishart.FieldGaussian.continuous_rowsGram ℂ n p).measurable.aemeasurable
    measurableSet_posSemidef]
  exact Filter.Eventually.of_forall fun z => Matrix.posSemidef_conjTranspose_mul_self _

end Wishart.ComplexMatrix

namespace Wishart.QuaternionMatrix
variable {p k : ℕ}

theorem continuous_normalizedCompression (B : Matrix (Fin p) (Fin k) ℍ[ℝ])
    (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) : Continuous (normalizedCompression B Sigma) := by
  apply Continuous.subtype_mk
  fun_prop

theorem measurable_normalizedCompression (B : Matrix (Fin p) (Fin k) ℍ[ℝ])
    (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) : Measurable (normalizedCompression B Sigma) :=
  (continuous_normalizedCompression B Sigma).measurable

theorem normalizedCompression_posSemidef (B : Matrix (Fin p) (Fin k) ℍ[ℝ])
    (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) (X : Hermitian p) (hX : PosSemidef X.val) :
    PosSemidef (normalizedCompression B Sigma X).val := hX.congruence _

theorem measurableSet_posSemidef : MeasurableSet {X : Hermitian p | PosSemidef X.val} := by
  unfold PosSemidef
  simp_rw [← Matrix.nonneg_iff_posSemidef]
  apply (isClosed_le continuous_const _).measurableSet
  apply Continuous.comp continuous_complexRepresentation continuous_subtype_val

theorem gramMeasure_ae_posSemidef (n : ℕ) (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) :
    ∀ᵐ (X : Hermitian p) ∂gramMeasure n Sigma, PosSemidef X.val := by
  unfold gramMeasure Wishart.FieldGaussian.gramWithFactor
  rw [ae_map_iff (Wishart.FieldGaussian.continuous_rowsGram ℍ[ℝ] n p).measurable.aemeasurable
    measurableSet_posSemidef]
  exact Filter.Eventually.of_forall fun z => posSemidef_gram _

end Wishart.QuaternionMatrix
end
end CanonicalSource43

section CanonicalSource44
/- Source: Wishart/FieldDensityBoundary.lean -/




/-!
# Full real-shape field comparison, including spectral boundary values

All finite approximant comparisons are supplied by the actual density theorem
in the preceding file. Positive-cone support is proved from that density. The
result has the full finite convex increasing symmetric logarithmic profile
class, arbitrary full-column-rank selected compression, arbitrary other
compressions, and positive semidefinite offsets.
-/

noncomputable section
open Matrix MeasureTheory Set
open scoped Classical Quaternion ComplexOrder ENNReal

namespace Wishart.ComplexMatrix
open Wishart.FieldGaussian Wishart.Spectral

theorem density_selected_boundary_comparison {m k₀ : ℕ} {α : ℝ}
    (hα : (m : ℝ) - 1 < α) (Sigma : Matrix (Fin m) (Fin m) ℂ) (hSigma : Sigma.PosDef)
    {ι : Type*} [Fintype ι]
    (B₀ : Matrix (Fin m) (Fin k₀) ℂ) (hB₀ : Function.Injective B₀.mulVec)
    (c : ℝ) (hc0 : 0 ≤ c)
    (h₀ : (Fin k₀ → ℝ) → ℝ) (hc₀ : ConvexOn ℝ univ h₀)
    (hm₀ : Monotone h₀) (hs₀ : SymmetricProfile h₀)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin m) (Fin (k i)) ℂ)
    (Q : ∀ i, Hermitian (k i)) (hQ : ∀ i, (Q i : Matrix (Fin (k i)) (Fin (k i)) ℂ).PosSemidef)
    (h : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hc : ∀ i, ConvexOn ℝ univ (h i)) (hm : ∀ i, Monotone (h i))
    (hs : ∀ i, SymmetricProfile (h i)) :
    (∫⁻ X, ENNReal.ofReal (spectralBoundaryValue h₀ (Wishart.FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe (Wishart.FieldSpectral.identityShift (normalizedCompression B₀ Sigma X) c))))
      ∂wishartMeasure α Sigma) *
    (∫⁻ X, ENNReal.ofReal (∏ i, spectralBoundaryValue (h i) (Wishart.FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe (Q i + normalizedCompression (B i) Sigma X))))
      ∂wishartMeasure α Sigma) ≤
    ∫⁻ X, ENNReal.ofReal (spectralBoundaryValue h₀ (Wishart.FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe (Wishart.FieldSpectral.identityShift (normalizedCompression B₀ Sigma X) c))) *
      ∏ i, spectralBoundaryValue (h i) (Wishart.FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe (Q i + normalizedCompression (B i) Sigma X)))) ∂wishartMeasure α Sigma := by
  letI := wishart_probability hα hSigma
  let μ := wishartMeasure α Sigma
  let A₀ : Hermitian m → Hermitian k₀ := fun X => Wishart.FieldSpectral.identityShift (normalizedCompression B₀ Sigma X) c
  let A : ∀ i, Hermitian m → Hermitian (k i) := fun i X => Q i + normalizedCompression (B i) Sigma X
  have hAm₀ : Measurable A₀ := ((continuous_normalizedCompression B₀ Sigma).add continuous_const).measurable
  have hAm (i : ι) : Measurable (A i) :=
    (continuous_const.add (continuous_normalizedCompression (B i) Sigma)).measurable
  have hA₀ : ∀ᵐ X ∂μ, (A₀ X : Matrix (Fin k₀) (Fin k₀) ℂ).PosSemidef := by
    filter_upwards [wishart_ae_posDef α Sigma] with X hX
    exact Wishart.FieldSpectral.identityShift_posSemidef _ (normalizedCompression_posSemidef B₀ Sigma X hX.posSemidef) hc0
  have hA : ∀ᵐ X ∂μ, ∀ i, (A i X : Matrix (Fin (k i)) (Fin (k i)) ℂ).PosSemidef := by
    filter_upwards [wishart_ae_posDef α Sigma] with X hX i
    exact (hQ i).add (normalizedCompression_posSemidef (B i) Sigma X hX.posSemidef)
  apply complex_spectral_boundary_selected_split μ k₀ k A₀ A hAm₀ hAm hA₀ hA h₀ h hc₀ hc hm₀ hm hs₀ hs
  intro n
  have hh := density_selected_finite_comparison hα Sigma hSigma B₀ hB₀ c hc0
    h₀ hc₀ hm₀ n k B Q hQ h hc hm (fun _ => n)
  calc
    _ ≤ ∫⁻ X, ENNReal.ofReal (complexFaceApprox hc₀ hm₀ n (A₀ X)) *
      ENNReal.ofReal (∏ i, complexFaceApprox (hc i) (hm i) n (A i X)) ∂μ := hh
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [hA₀] with X hX
      exact (ENNReal.ofReal_mul (complexFaceApprox_nonneg hc₀ hm₀ n (A₀ X) hX)).symm

end Wishart.ComplexMatrix

namespace Wishart.QuaternionMatrix
open Wishart.FieldGaussian Wishart.Spectral

theorem density_selected_boundary_comparison {m k₀ : ℕ} {α : ℝ}
    (hα : (m : ℝ) - 1 < α) (Sigma : Matrix (Fin m) (Fin m) ℍ[ℝ]) (hSigma : PosDef Sigma)
    {ι : Type*} [Fintype ι]
    (B₀ : Matrix (Fin m) (Fin k₀) ℍ[ℝ]) (hB₀ : FullColumnRank B₀)
    (c : ℝ) (hc0 : 0 ≤ c)
    (h₀ : (Fin k₀ → ℝ) → ℝ) (hc₀ : ConvexOn ℝ univ h₀)
    (hm₀ : Monotone h₀) (hs₀ : SymmetricProfile h₀)
    (k : ι → ℕ) (B : ∀ i, Matrix (Fin m) (Fin (k i)) ℍ[ℝ])
    (Q : ∀ i, Hermitian (k i)) (hQ : ∀ i, PosSemidef (Q i).val)
    (h : ∀ i, (Fin (k i) → ℝ) → ℝ)
    (hc : ∀ i, ConvexOn ℝ univ (h i)) (hm : ∀ i, Monotone (h i))
    (hs : ∀ i, SymmetricProfile (h i)) :
    (∫⁻ X, ENNReal.ofReal (spectralBoundaryValue h₀ (orderedValues (identityShift (normalizedCompression B₀ Sigma X) c)))
      ∂wishartMeasure α Sigma) *
    (∫⁻ X, ENNReal.ofReal (∏ i, spectralBoundaryValue (h i) (orderedValues (Q i + normalizedCompression (B i) Sigma X)))
      ∂wishartMeasure α Sigma) ≤
    ∫⁻ X, ENNReal.ofReal (spectralBoundaryValue h₀ (orderedValues (identityShift (normalizedCompression B₀ Sigma X) c)) *
      ∏ i, spectralBoundaryValue (h i) (orderedValues (Q i + normalizedCompression (B i) Sigma X))) ∂wishartMeasure α Sigma := by
  letI := wishart_probability hα hSigma
  let μ := wishartMeasure α Sigma
  let A₀ : Hermitian m → Hermitian k₀ := fun X => identityShift (normalizedCompression B₀ Sigma X) c
  let A : ∀ i, Hermitian m → Hermitian (k i) := fun i X => Q i + normalizedCompression (B i) Sigma X
  have hAm₀ : Measurable A₀ := ((continuous_normalizedCompression B₀ Sigma).add continuous_const).measurable
  have hAm (i : ι) : Measurable (A i) :=
    (continuous_const.add (continuous_normalizedCompression (B i) Sigma)).measurable
  have hA₀ : ∀ᵐ X ∂μ, PosSemidef (A₀ X).val := by
    filter_upwards [wishart_ae_posDef α Sigma] with X hX
    exact identityShift_posSemidef _ (normalizedCompression_posSemidef B₀ Sigma X hX.posSemidef) hc0
  have hA : ∀ᵐ X ∂μ, ∀ i, PosSemidef (A i X).val := by
    filter_upwards [wishart_ae_posDef α Sigma] with X hX i
    exact (hQ i).add (normalizedCompression_posSemidef (B i) Sigma X hX.posSemidef)
  apply quaternion_spectral_boundary_selected_split μ k₀ k A₀ A hAm₀ hAm hA₀ hA h₀ h hc₀ hc hm₀ hm hs₀ hs
  intro n
  have hh := density_selected_finite_comparison hα Sigma hSigma B₀ hB₀ c hc0
    h₀ hc₀ hm₀ n k B Q hQ h hc hm (fun _ => n)
  calc
    _ ≤ ∫⁻ X, ENNReal.ofReal (quaternionFaceApprox hc₀ hm₀ n (A₀ X)) *
      ENNReal.ofReal (∏ i, quaternionFaceApprox (hc i) (hm i) n (A i X)) ∂μ := hh
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [hA₀] with X hX
      exact (ENNReal.ofReal_mul (quaternionFaceApprox_nonneg hc₀ hm₀ n (A₀ X) hX)).symm

end Wishart.QuaternionMatrix
end
end CanonicalSource44

section CanonicalSource45
/- Source: Wishart/ExtendedProductAssembly.lean -/



/-!
# The full extended product chain from every selected split

Only multiplication and finite induction are used. In particular the argument
never divides by a moment, cancels infinity, or assumes strict positivity.
-/

noncomputable section
open MeasureTheory
open scoped Classical ENNReal
namespace Wishart

theorem extendedSelectedProductComparison_of_splits {E ι : Type*}
    [MeasurableSpace E] [DecidableEq ι] (μ : Measure E) [IsProbabilityMeasure μ]
    (f : ι → E → ℝ)
    (hsplit : ∀ (J : Finset ι) (j : ι), j ∈ J →
      (∫⁻ X, ENNReal.ofReal (f j X) ∂μ) *
        (∫⁻ X, ENNReal.ofReal (∏ i ∈ J.erase j, f i X) ∂μ) ≤
          ∫⁻ X, ENNReal.ofReal (∏ i ∈ J, f i X) ∂μ) :
    ExtendedSelectedProductComparison μ f := by
  let m : Finset ι → ℝ≥0∞ := fun J => ∫⁻ X, ENNReal.ofReal (∏ i ∈ J, f i X) ∂μ
  have hempty : m ∅ = 1 := by simp [m]
  have hsingle (i : ι) : m {i} = ∫⁻ X, ENNReal.ofReal (f i X) ∂μ := by simp [m]
  have hall (J : Finset ι) : (∏ i ∈ J, m {i}) ≤ m J := by
    apply WishartVerification.MomentAssembly.extended_product_singletons_le_of_exists_split
      m hempty (fun _ => bot_le) _ J
    intro S hS
    obtain ⟨j, hj⟩ := hS
    exact ⟨j, hj, by simpa only [hsingle, m] using hsplit S j hj⟩
  intro J j hj
  refine ⟨hsplit J j hj, ?_⟩
  have hlower := mul_le_mul_of_nonneg_left (hall (J.erase j)) (bot_le : 0 ≤ m {j})
  rw [Finset.mul_prod_erase J (fun i => m {i}) hj] at hlower
  simpa only [hsingle, m] using hlower

end Wishart
end
end CanonicalSource45

section CanonicalSource46
/- Source: Wishart/FieldDensityProducts.lean -/



/-!
# Theorem 7.1: the full real-shape selected-product assertions

These theorems supply the complete non-integer-shape branch of each field
comparison target. They are not the entire Theorem 7.1 package: the separate
integer Gram laws and finite determinant moments are assembled separately.
-/

noncomputable section
open Matrix MeasureTheory Set
open scoped Classical Quaternion ComplexOrder ENNReal
namespace Wishart

namespace ComplexSpectralFamily
variable {p : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem density_selected_product_comparison {α : ℝ} (hα : (p : ℝ) - 1 < α)
    (Sigma : Matrix (Fin p) (Fin p) ℂ) (hSigma : Sigma.PosDef)
    (F : ComplexSpectralFamily p ι) :
    ExtendedSelectedProductComparison (ComplexMatrix.wishartMeasure α Sigma) (F.factor Sigma) := by
  letI := ComplexMatrix.wishart_probability hα hSigma
  apply extendedSelectedProductComparison_of_splits
  intro J j hj
  have h := ComplexMatrix.density_selected_boundary_comparison hα Sigma hSigma
    (F.matrix j) (F.full_rank j) (F.shift j) (F.shift_nonneg j)
    (F.profile j) (F.convex j) (F.increasing j) (F.symmetric j)
    (fun i : J.erase j => F.size i)
    (fun i : J.erase j => F.matrix i)
    (fun i : J.erase j => F.shift i •
      (⟨1, Matrix.isHermitian_one⟩ : ComplexMatrix.Hermitian (F.size i)))
    (fun i => (Matrix.PosDef.one.posSemidef.smul (F.shift_nonneg i)))
    (fun i : J.erase j => F.profile i)
    (fun i => F.convex i) (fun i => F.increasing i) (fun i => F.symmetric i)
  have hselected (i : ι) (X : ComplexMatrix.Hermitian p) :
      Spectral.spectralBoundaryValue (F.profile i) (FieldSpectral.orderedValues
        (WishartVerification.hermitian_matrix_coe
          (FieldSpectral.identityShift (ComplexMatrix.normalizedCompression (F.matrix i) Sigma X)
            (F.shift i)))) = F.factor Sigma i X := rfl
  have hother (i : ι) (X : ComplexMatrix.Hermitian p) :
      Spectral.spectralBoundaryValue (F.profile i) (FieldSpectral.orderedValues
        (WishartVerification.hermitian_matrix_coe
          (F.shift i • (⟨1, Matrix.isHermitian_one⟩ : ComplexMatrix.Hermitian (F.size i)) +
            ComplexMatrix.normalizedCompression (F.matrix i) Sigma X))) = F.factor Sigma i X := by
    exact congrArg (fun Y : ComplexMatrix.Hermitian (F.size i) =>
      Spectral.spectralBoundaryValue (F.profile i)
        (FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe Y)))
      (add_comm _ _)
  have hp (X : ComplexMatrix.Hermitian p) :
      (∏ i : J.erase j, F.factor Sigma i X) = ∏ i ∈ J.erase j, F.factor Sigma i X :=
    Finset.prod_coe_sort (J.erase j) (fun i => F.factor Sigma i X)
  have hs :
      (∫⁻ X, ENNReal.ofReal (F.factor Sigma j X) ∂ComplexMatrix.wishartMeasure α Sigma) *
        (∫⁻ X, ENNReal.ofReal (∏ i ∈ J.erase j, F.factor Sigma i X)
          ∂ComplexMatrix.wishartMeasure α Sigma) ≤
      ∫⁻ X, ENNReal.ofReal (F.factor Sigma j X * ∏ i ∈ J.erase j, F.factor Sigma i X)
        ∂ComplexMatrix.wishartMeasure α Sigma := by
    simp_rw [← hp]
    simpa only [hselected, hother] using h
  convert hs using 1
  apply congrArg (fun t : ComplexMatrix.Hermitian p → ℝ≥0∞ => ∫⁻ X, t X ∂ComplexMatrix.wishartMeasure α Sigma)
  funext X
  rw [Finset.mul_prod_erase J (fun i => F.factor Sigma i X) hj]

end ComplexSpectralFamily

namespace QuaternionSpectralFamily
variable {p : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem density_selected_product_comparison {α : ℝ} (hα : (p : ℝ) - 1 < α)
    (Sigma : Matrix (Fin p) (Fin p) ℍ[ℝ]) (hSigma : QuaternionMatrix.PosDef Sigma)
    (F : QuaternionSpectralFamily p ι) :
    ExtendedSelectedProductComparison (QuaternionMatrix.wishartMeasure α Sigma) (F.factor Sigma) := by
  letI := QuaternionMatrix.wishart_probability hα hSigma
  apply extendedSelectedProductComparison_of_splits
  intro J j hj
  have h := QuaternionMatrix.density_selected_boundary_comparison hα Sigma hSigma
    (F.matrix j) (F.full_rank j) (F.shift j) (F.shift_nonneg j)
    (F.profile j) (F.convex j) (F.increasing j) (F.symmetric j)
    (fun i : J.erase j => F.size i)
    (fun i : J.erase j => F.matrix i)
    (fun i : J.erase j => F.shift i •
      (⟨1, Matrix.isHermitian_one⟩ : QuaternionMatrix.Hermitian (F.size i)))
    (fun i => (QuaternionMatrix.posDef_one.posSemidef.smul (F.shift_nonneg i)))
    (fun i : J.erase j => F.profile i)
    (fun i => F.convex i) (fun i => F.increasing i) (fun i => F.symmetric i)
  have hp (X : QuaternionMatrix.Hermitian p) :
      (∏ i : J.erase j, F.factor Sigma i X) = ∏ i ∈ J.erase j, F.factor Sigma i X :=
    Finset.prod_coe_sort (J.erase j) (fun i => F.factor Sigma i X)
  have hs :
      (∫⁻ X, ENNReal.ofReal (F.factor Sigma j X) ∂QuaternionMatrix.wishartMeasure α Sigma) *
        (∫⁻ X, ENNReal.ofReal (∏ i ∈ J.erase j, F.factor Sigma i X)
          ∂QuaternionMatrix.wishartMeasure α Sigma) ≤
      ∫⁻ X, ENNReal.ofReal (F.factor Sigma j X * ∏ i ∈ J.erase j, F.factor Sigma i X)
        ∂QuaternionMatrix.wishartMeasure α Sigma := by
    simp_rw [← hp]
    simpa only [factor, shiftedCompression, QuaternionMatrix.identityShift, add_comm] using h
  convert hs using 1
  apply congrArg (fun t : QuaternionMatrix.Hermitian p → ℝ≥0∞ => ∫⁻ X, t X ∂QuaternionMatrix.wishartMeasure α Sigma)
  funext X
  rw [Finset.mul_prod_erase J (fun i => F.factor Sigma i X) hj]

end QuaternionSpectralFamily

end Wishart
end
end CanonicalSource46

section CanonicalSource47
/- Source: Wishart/FieldGaussianSplitting.lean -/



/-!
# Exact independent row and column splits of field Gaussian matrices

These are complete measure identities derived from the literal Gaussian
density. No conditional distribution or independence assertion is assumed.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
open scoped Classical Quaternion ENNReal Matrix.Norms.Frobenius

namespace WishartVerification.FieldDensity

theorem finiteDensity_product {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν]
    (f : A → ℝ≥0∞) (g : B → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (hF : FiniteDensity μ f) (hG : FiniteDensity ν g) :
    FiniteDensity (μ.prod ν) (fun z => f z.1 * g z.2) ∧
      normalized (μ.prod ν) (fun z => f z.1 * g z.2) =
        (normalized μ f).prod (normalized ν g) := by
  letI := isProbability_normalized hF
  letI := isProbability_normalized hG
  have hraw : (μ.prod ν).withDensity (fun z => f z.1 * g z.2) =
      (normalizer μ f * normalizer ν g) • ((normalized μ f).prod (normalized ν g)) := by
    rw [← prod_withDensity hf hg,raw_eq_smul_normalized hF,raw_eq_smul_normalized hG,
      Measure.prod_smul_left,Measure.prod_smul_right,smul_smul]
  exact (normalized_of_raw_eq_smul_probability _ _ _
    (CanonicallyOrderedAdd.mul_pos.mpr ⟨hF.positive, hG.positive⟩) (ENNReal.mul_lt_top hF.finite hG.finite) hraw).2

end WishartVerification.FieldDensity

namespace Wishart.FieldGaussian
open WishartVerification.FieldDensity Wishart.FieldDensity

variable (F : Type*) [NormedRing F] [StarRing F] [CStarRing F]
  [InnerProductSpace ℝ F] [StarModule ℝ F] [FiniteDimensional ℝ F]
  [SMulCommClass ℝ F F] [IsScalarTower ℝ F F]
  [MeasurableSpace F] [BorelSpace F]

@[reducible] local instance compatibleScalarAlgebraStage5_2 : NormedAlgebra ℝ F where
  toAlgebra := Algebra.ofModule (fun r x y => smul_mul_assoc r x y)
    (fun r x y => mul_smul_comm r x y)
  norm_smul_le r x := (norm_smul r x).le

theorem finiteDensity_rowKernel_and_law (q : ℕ) (hF : 0 < Module.finrank ℝ F) :
    FiniteDensity (volume : Measure (Row F q)) (rowKernel F q) ∧
      normalized volume (rowKernel F q) = gaussianRowWithFactor F (1 : Matrix (Fin q) (Fin q) F) := by
  obtain ⟨c,hctop,hc⟩ := gaussianRowWithFactor_one_density F q hF
  have hraw : gaussianRowWithFactor F (1 : Matrix (Fin q) (Fin q) F) =
      c • (volume : Measure (Row F q)).withDensity (rowKernel F q) := by
    rw [hc]
    exact withDensity_smul' c _ hctop
  obtain ⟨h0,ht,heq⟩ := WishartVerification.normalized_ennreal_density_of_probability
    (gaussianRowWithFactor F (1 : Matrix (Fin q) (Fin q) F)) volume (rowKernel F q) c hraw
  exact ⟨⟨pos_iff_ne_zero.mpr h0,lt_top_iff_ne_top.mpr ht⟩,heq.symm⟩

def appendColumn {n q : ℕ} (v : Row F n) (G : Matrix (Fin n) (Fin q) F) :
    Matrix (Fin n) (Fin (q+1)) F := Matrix.of fun i j => Fin.cases (v i) (G i) j

def splitColumnLinearEquiv (n q : ℕ) :
    (Row F n × Matrix (Fin n) (Fin q) F) ≃ₗ[ℝ] Matrix (Fin n) (Fin (q+1)) F where
  toFun z := appendColumn F z.1 z.2
  invFun G := (WithLp.toLp 2 (fun i => G i 0),G.submatrix id Fin.succ)
  left_inv z := by apply Prod.ext <;> ext i <;> rfl
  right_inv G := by ext i j; exact Fin.cases rfl (fun _ => rfl) j
  map_add' a b := by ext i j; exact Fin.cases rfl (fun _ => rfl) j
  map_smul' r a := by ext i j; exact Fin.cases rfl (fun _ => rfl) j

theorem matrixKernel_appendColumn {n q : ℕ} (v : Row F n)
    (G : Matrix (Fin n) (Fin q) F) :
    matrixKernel F (appendColumn F v G) = rowKernel F n v * matrixKernel F G := by
  have hnorm : rectangularNormSquare (appendColumn F v G) = ‖v‖ ^ 2 + rectangularNormSquare G := by
    simp only [rectangularNormSquare,appendColumn,Matrix.of_apply,Fin.sum_univ_succ,
      Fin.cases_zero,Fin.cases_succ,Finset.sum_add_distrib,PiLp.norm_sq_eq_of_L2]
  rw [matrixKernel,hnorm,mul_add,Real.exp_add,ENNReal.ofReal_mul (Real.exp_pos _).le]
  rfl

theorem matrixGaussian_split_column (n q : ℕ) (hF : 0 < Module.finrank ℝ F) :
    ((gaussianRowWithFactor F (1 : Matrix (Fin n) (Fin n) F)).prod
      (matrixGaussian F n q)).map (fun z => appendColumn F z.1 z.2) =
        matrixGaussian F n (q+1) := by
  have hrow := finiteDensity_rowKernel_and_law F n hF
  have hmat := finiteDensity_matrixKernel_and_law F n q hF
  have hp := finiteDensity_product (volume : Measure (Row F n))
    (Wishart.FieldHermitian.rectangularLebesgue F n q) (rowKernel F n) (matrixKernel F)
    (measurable_rowKernel F n) (measurable_matrixKernel F n q) hrow.1 hmat.1
  have h := @normalized_transport_haar
    (Row F n × Matrix (Fin n) (Fin q) F) (Matrix (Fin n) (Fin (q+1)) F)
    _ _ _ _ (by exact inferInstanceAs (BorelSpace (Row F n × Matrix (Fin n) (Fin q) F)))
    _ _ _ _ (by exact inferInstanceAs (BorelSpace (Matrix (Fin n) (Fin (q+1)) F)))
    ((splitColumnLinearEquiv F n q).toContinuousLinearEquiv)
    ((volume : Measure (Row F n)).prod (Wishart.FieldHermitian.rectangularLebesgue F n q)) (Wishart.FieldHermitian.rectangularLebesgue F n (q+1))
    (by exact inferInstanceAs (Measure.IsAddHaarMeasure ((volume : Measure (Row F n)).prod (Wishart.FieldHermitian.rectangularLebesgue F n q))))
    (by exact inferInstanceAs (Measure.IsAddHaarMeasure (Wishart.FieldHermitian.rectangularLebesgue F n (q+1))))
    (fun z => rowKernel F n z.1 * matrixKernel F z.2) (matrixKernel F) hp.1
    (fun z => matrixKernel_appendColumn F z.1 z.2)
  rw [hp.2,hrow.2,hmat.2,(finiteDensity_matrixKernel_and_law F n (q+1) hF).2] at h
  exact h.2.symm

def appendRow {n q : ℕ} (v : Row F q) (G : Matrix (Fin n) (Fin q) F) :
    Matrix (Fin (n+1)) (Fin q) F := Matrix.of fun i j => Fin.cases (v j) (fun k => G k j) i

def splitRowLinearEquiv (n q : ℕ) :
    (Row F q × Matrix (Fin n) (Fin q) F) ≃ₗ[ℝ] Matrix (Fin (n+1)) (Fin q) F where
  toFun z := appendRow F z.1 z.2
  invFun G := (WithLp.toLp 2 (G 0),G.submatrix Fin.succ id)
  left_inv z := by apply Prod.ext <;> ext i <;> rfl
  right_inv G := by ext i j; exact Fin.cases rfl (fun _ => rfl) i
  map_add' a b := by ext i j; exact Fin.cases rfl (fun _ => rfl) i
  map_smul' r a := by ext i j; exact Fin.cases rfl (fun _ => rfl) i

theorem matrixKernel_appendRow {n q : ℕ} (v : Row F q)
    (G : Matrix (Fin n) (Fin q) F) :
    matrixKernel F (appendRow F v G) = rowKernel F q v * matrixKernel F G := by
  have hnorm : rectangularNormSquare (appendRow F v G) = ‖v‖ ^ 2 + rectangularNormSquare G := by
    simp only [rectangularNormSquare,appendRow,Matrix.of_apply,Fin.sum_univ_succ,
      Fin.cases_zero,Fin.cases_succ,PiLp.norm_sq_eq_of_L2]
  rw [matrixKernel,hnorm,mul_add,Real.exp_add,ENNReal.ofReal_mul (Real.exp_pos _).le]
  rfl

theorem matrixGaussian_split_row (n q : ℕ) (hF : 0 < Module.finrank ℝ F) :
    ((gaussianRowWithFactor F (1 : Matrix (Fin q) (Fin q) F)).prod
      (matrixGaussian F n q)).map (fun z => appendRow F z.1 z.2) =
        matrixGaussian F (n+1) q := by
  have hrow := finiteDensity_rowKernel_and_law F q hF
  have hmat := finiteDensity_matrixKernel_and_law F n q hF
  have hp := finiteDensity_product (volume : Measure (Row F q))
    (Wishart.FieldHermitian.rectangularLebesgue F n q) (rowKernel F q) (matrixKernel F)
    (measurable_rowKernel F q) (measurable_matrixKernel F n q) hrow.1 hmat.1
  have h := @normalized_transport_haar
    (Row F q × Matrix (Fin n) (Fin q) F) (Matrix (Fin (n+1)) (Fin q) F)
    _ _ _ _ (by exact inferInstanceAs (BorelSpace (Row F q × Matrix (Fin n) (Fin q) F)))
    _ _ _ _ (by exact inferInstanceAs (BorelSpace (Matrix (Fin (n+1)) (Fin q) F)))
    ((splitRowLinearEquiv F n q).toContinuousLinearEquiv)
    ((volume : Measure (Row F q)).prod (Wishart.FieldHermitian.rectangularLebesgue F n q)) (Wishart.FieldHermitian.rectangularLebesgue F (n+1) q)
    (by exact inferInstanceAs (Measure.IsAddHaarMeasure ((volume : Measure (Row F q)).prod (Wishart.FieldHermitian.rectangularLebesgue F n q))))
    (by exact inferInstanceAs (Measure.IsAddHaarMeasure (Wishart.FieldHermitian.rectangularLebesgue F (n+1) q)))
    (fun z => rowKernel F q z.1 * matrixKernel F z.2) (matrixKernel F) hp.1
    (fun z => matrixKernel_appendRow F z.1 z.2)
  rw [hp.2,hrow.2,hmat.2,(finiteDensity_matrixKernel_and_law F (n+1) q hF).2] at h
  exact h.2.symm

def transposeMatrixLinearEquiv (n p : ℕ) :
    Matrix (Fin n) (Fin p) F ≃ₗ[ℝ] Matrix (Fin p) (Fin n) F where
  toFun Z := Zᵀ
  invFun Z := Zᵀ
  left_inv Z := Matrix.transpose_transpose Z
  right_inv Z := Matrix.transpose_transpose Z
  map_add' A B := Matrix.transpose_add A B
  map_smul' r A := Matrix.transpose_smul r A

theorem matrixGaussian_map_transpose (n p : ℕ) (hF : 0 < Module.finrank ℝ F) :
    (matrixGaussian F n p).map Matrix.transpose = matrixGaussian F p n := by
  have h := @normalized_transport_haar
    (Matrix (Fin n) (Fin p) F) (Matrix (Fin p) (Fin n) F)
    _ _ _ _ (by exact inferInstanceAs (BorelSpace (Matrix (Fin n) (Fin p) F)))
    _ _ _ _ (by exact inferInstanceAs (BorelSpace (Matrix (Fin p) (Fin n) F)))
    ((transposeMatrixLinearEquiv F n p).toContinuousLinearEquiv)
    (Wishart.FieldHermitian.rectangularLebesgue F n p) (Wishart.FieldHermitian.rectangularLebesgue F p n)
    (by exact inferInstanceAs (Measure.IsAddHaarMeasure (Wishart.FieldHermitian.rectangularLebesgue F n p)))
    (by exact inferInstanceAs (Measure.IsAddHaarMeasure (Wishart.FieldHermitian.rectangularLebesgue F p n))) (matrixKernel F) (matrixKernel F)
    (finiteDensity_matrixKernel_and_law F n p hF).1 (fun Z => by
      unfold matrixKernel rectangularNormSquare
      congr 3
      exact Finset.sum_comm)
  rw [(finiteDensity_matrixKernel_and_law F n p hF).2,
    (finiteDensity_matrixKernel_and_law F p n hF).2] at h
  exact h.2.symm

def conjTransposeMatrixLinearEquiv (n p : ℕ) :
    Matrix (Fin n) (Fin p) F ≃ₗ[ℝ] Matrix (Fin p) (Fin n) F where
  toFun Z := Zᴴ
  invFun Z := Zᴴ
  left_inv Z := Matrix.conjTranspose_conjTranspose Z
  right_inv Z := Matrix.conjTranspose_conjTranspose Z
  map_add' A B := Matrix.conjTranspose_add A B
  map_smul' r A := by simp

theorem matrixGaussian_map_conjTranspose (n p : ℕ) (hF : 0 < Module.finrank ℝ F) :
    (matrixGaussian F n p).map Matrix.conjTranspose = matrixGaussian F p n := by
  have h := @normalized_transport_haar
    (Matrix (Fin n) (Fin p) F) (Matrix (Fin p) (Fin n) F)
    _ _ _ _ (by exact inferInstanceAs (BorelSpace (Matrix (Fin n) (Fin p) F)))
    _ _ _ _ (by exact inferInstanceAs (BorelSpace (Matrix (Fin p) (Fin n) F)))
    ((conjTransposeMatrixLinearEquiv F n p).toContinuousLinearEquiv)
    (Wishart.FieldHermitian.rectangularLebesgue F n p) (Wishart.FieldHermitian.rectangularLebesgue F p n)
    (by exact inferInstanceAs (Measure.IsAddHaarMeasure (Wishart.FieldHermitian.rectangularLebesgue F n p)))
    (by exact inferInstanceAs (Measure.IsAddHaarMeasure (Wishart.FieldHermitian.rectangularLebesgue F p n))) (matrixKernel F) (matrixKernel F)
    (finiteDensity_matrixKernel_and_law F n p hF).1 (fun Z => by
      change matrixKernel F Zᴴ = matrixKernel F Z
      unfold matrixKernel rectangularNormSquare
      simp only [Matrix.conjTranspose_apply,norm_star]
      congr 3
      exact Finset.sum_comm)
  rw [(finiteDensity_matrixKernel_and_law F n p hF).2,
    (finiteDensity_matrixKernel_and_law F p n hF).2] at h
  exact h.2.symm

end Wishart.FieldGaussian
end
end CanonicalSource47

section CanonicalSource48
/- Source: Wishart/FieldColumnRotation.lean -/



/-!
# Actual unitary rotation of one complex or quaternion column

The zero column is included. Only pointwise existence is needed for Gaussian
integration; no measurable choice of the rotation is asserted or used.
-/

noncomputable section
open Matrix
open scoped Classical Quaternion

namespace Wishart.FieldGaussian

variable (F : Type*) [NormedRing F] [StarRing F] [CStarRing F]
  [InnerProductSpace ℝ F] [StarModule ℝ F] [FiniteDimensional ℝ F]
  [SMulCommClass ℝ F F] [IsScalarTower ℝ F F]

@[reducible] local instance compatibleScalarAlgebraStage5_3 : NormedAlgebra ℝ F where
  toAlgebra := Algebra.ofModule (fun r x y => smul_mul_assoc r x y)
    (fun r x y => mul_smul_comm r x y)
  norm_smul_le r x := (norm_smul r x).le

theorem column_star_dot_eq_norm_sq
    (hstar : ∀ a : F, star a * a = algebraMap ℝ F (‖a‖ ^ 2))
    {n : ℕ} (v : Row F n) :
    star (fun i => v i) ⬝ᵥ (fun i => v i) = algebraMap ℝ F (‖v‖ ^ 2) := by
  simp only [dotProduct,Pi.star_apply,hstar,← map_sum,PiLp.norm_sq_eq_of_L2]

theorem exists_rotate_column_of_firstColumn {n : ℕ}
    (hfirst : ∀ x : Row F (n+1), ‖x‖ = 1 →
      ∃ U : unitary (Matrix (Fin (n+1)) (Fin (n+1)) F),
        ∀ i, (U : Matrix (Fin (n+1)) (Fin (n+1)) F) i 0 = x i)
    (v : Row F (n+1)) :
    ∃ U : unitary (Matrix (Fin (n+1)) (Fin (n+1)) F),
      (U : Matrix (Fin (n+1)) (Fin (n+1)) F) *ᵥ (fun i => v i) =
        Pi.single 0 (algebraMap ℝ F ‖v‖) := by
  by_cases hv : v = 0
  · refine ⟨1,?_⟩
    simp [hv]
    rfl
  have hr : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let x : Row F (n+1) := ‖v‖⁻¹ • v
  have hx : ‖x‖ = 1 := by
    dsimp only [x]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr),inv_mul_cancel₀ hr.ne']
  obtain ⟨V,hV⟩ := hfirst x hx
  have hVe : (V : Matrix (Fin (n+1)) (Fin (n+1)) F) *ᵥ Pi.single 0 1 = fun i => x i := by
    funext i
    simpa [Matrix.mulVec,dotProduct,Pi.single_apply] using hV i
  have hback : (star V : Matrix (Fin (n+1)) (Fin (n+1)) F) *ᵥ (fun i => x i) =
      Pi.single 0 1 := by
    rw [← hVe,Matrix.mulVec_mulVec,Unitary.coe_star_mul_self,Matrix.one_mulVec]
  have hvx : (fun i => v i) = ‖v‖ • (fun i => x i) := by
    funext i
    change v i = ‖v‖ • (‖v‖⁻¹ • v i)
    rw [smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
  refine ⟨star V,?_⟩
  rw [hvx, Matrix.mulVec_smul, Unitary.coe_star, hback]
  funext i
  by_cases hi : i = 0
  · subst i
    simp [Algebra.algebraMap_eq_smul_one]
  · simp [Pi.single_apply,hi]

end Wishart.FieldGaussian

namespace Wishart.ComplexMatrix
open Wishart.FieldGaussian

theorem star_mul_self_norm_sq (a : ℂ) : star a * a = algebraMap ℝ ℂ (‖a‖ ^ 2) :=
by
  simpa only [Complex.star_def, Algebra.algebraMap_eq_smul_one, Complex.real_smul, mul_one, Complex.ofReal_pow] using Complex.conj_mul' a

theorem exists_rotate_column {n : ℕ} (v : Row ℂ (n+1)) :
    ∃ U : unitary (Matrix (Fin (n+1)) (Fin (n+1)) ℂ),
      (U : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) *ᵥ (fun i => v i) =
        Pi.single 0 (‖v‖ : ℂ) := by
  have hfirst : ∀ x : Row ℂ (n+1), ‖x‖ = 1 →
      ∃ U : unitary (Matrix (Fin (n+1)) (Fin (n+1)) ℂ),
        ∀ i, U.val i 0 = x i := by
    intro x hx
    let B : Matrix (Fin (n+1)) (Fin 1) ℂ := fun i _ => x i
    have hB : Bᴴ * B = 1 := by
      ext i j
      have hi : i = 0 := Subsingleton.elim _ _
      have hj : j = 0 := Subsingleton.elim _ _
      subst i; subst j
      change star (fun k => x k) ⬝ᵥ (fun k => x k) = 1
      have hc := column_star_dot_eq_norm_sq ℂ (fun a => by
        simpa only [Algebra.algebraMap_eq_smul_one] using star_mul_self_norm_sq a) x
      simpa only [hx, one_pow, map_one] using hc
    obtain ⟨U,hU⟩ := Wishart.FieldSpectral.exists_unitary_extension
      (show 1 ≤ n+1 by omega) B hB
    exact ⟨U,fun i => congrArg (fun M => M i 0) hU⟩
  simpa only [Algebra.algebraMap_eq_smul_one, Complex.real_smul, mul_one] using
    exists_rotate_column_of_firstColumn ℂ hfirst v

end Wishart.ComplexMatrix

namespace Wishart.QuaternionMatrix
open Wishart.FieldGaussian

theorem star_mul_self_norm_sq (a : ℍ[ℝ]) : star a * a = algebraMap ℝ ℍ[ℝ] (‖a‖ ^ 2) := by
  rw [Quaternion.star_mul_self,Quaternion.normSq_eq_norm_mul_self,pow_two]
  rfl

theorem exists_rotate_column {n : ℕ} (v : Row ℍ[ℝ] (n+1)) :
    ∃ U : unitary (Matrix (Fin (n+1)) (Fin (n+1)) ℍ[ℝ]),
      U.val *ᵥ (fun i => v i) =
        Pi.single 0 (‖v‖ : ℍ[ℝ]) := by
  have hfirst : ∀ x : Row ℍ[ℝ] (n+1), ‖x‖ = 1 →
      ∃ U : unitary (Matrix (Fin (n+1)) (Fin (n+1)) ℍ[ℝ]),
        ∀ i, U.val i 0 = x i := by
    intro x hx
    apply exists_unitary_firstColumn (fun i => x i)
    have hc := column_star_dot_eq_norm_sq ℍ[ℝ] (fun a => by
      simpa only [Algebra.algebraMap_eq_smul_one] using star_mul_self_norm_sq a) x
    simpa only [hx, one_pow, map_one] using hc
  simpa only [Algebra.algebraMap_eq_smul_one, ← Quaternion.coe_mul_eq_smul, mul_one] using
    exists_rotate_column_of_firstColumn ℍ[ℝ] hfirst v

end Wishart.QuaternionMatrix
end
end CanonicalSource48

section CanonicalSource49
/- Source: Wishart/FieldGramRecursion.lean -/



/-!
# Column elimination for the actual field Gaussian Gram law

A unitary rotation is chosen only inside each fixed first-column fibre.
Gaussian invariance then identifies the integrated fibre. Consequently the
whole pushforward law is proved without a measurable choice of rotations.
The remaining first row and residual matrix are independent by the literal
Gaussian density factorization.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped Classical Quaternion ENNReal Matrix.Norms.Frobenius

namespace Wishart.FieldGaussian

variable (F : Type*) [NormedRing F] [StarRing F] [CStarRing F]
  [InnerProductSpace ℝ F] [StarModule ℝ F] [FiniteDimensional ℝ F]
  [SMulCommClass ℝ F F] [IsScalarTower ℝ F F]
  [MeasurableSpace F] [BorelSpace F]

@[reducible] local instance compatibleScalarAlgebraStage5_4 : NormedAlgebra ℝ F where
  toAlgebra := Algebra.ofModule (fun r x y => smul_mul_assoc r x y)
    (fun r x y => mul_smul_comm r x y)
  norm_smul_le r x := (norm_smul r x).le

def matrixGram {n p : ℕ} (Z : Matrix (Fin n) (Fin p) F) : Hermitian F p :=
  ⟨Zᴴ * Z,Matrix.isHermitian_conjTranspose_mul_self Z⟩

theorem continuous_matrixGram (n p : ℕ) :
    Continuous (matrixGram F : Matrix (Fin n) (Fin p) F → Hermitian F p) := by
  apply Continuous.subtype_mk
  exact continuous_id.matrix_conjTranspose.matrix_mul continuous_id

theorem matrixGaussian_map_gram (n p : ℕ) :
    (matrixGaussian F n p).map (matrixGram F) =
      gramWithFactor F n (1 : Matrix (Fin p) (Fin p) F) := by
  unfold matrixGaussian gramWithFactor
  rw [Measure.map_map (continuous_matrixGram F n p).measurable
    (continuous_rowsMatrix F n p).measurable]
  rfl

theorem matrixGram_unitary_left {n p : ℕ}
    (U : unitary (Matrix (Fin n) (Fin n) F)) (Z : Matrix (Fin n) (Fin p) F) :
    matrixGram F ((U : Matrix (Fin n) (Fin n) F) * Z) = matrixGram F Z := by
  apply Subtype.ext
  change (U.val * Z)ᴴ * (U.val * Z) = Zᴴ * Z
  rw [Matrix.conjTranspose_mul]
  calc
    _ = Zᴴ * (U.valᴴ * U.val) * Z := by
      simp only [Matrix.mul_assoc]
    _ = _ := by
      have hU : U.valᴴ * U.val = 1 := Unitary.coe_star_mul_self U
      rw [hU, Matrix.mul_one]

def firstColumn (n : ℕ) (r : ℝ) : Row F (n+1) :=
  WithLp.toLp 2 (Pi.single 0 (algebraMap ℝ F r))

theorem continuous_firstColumn (n : ℕ) : Continuous (firstColumn F n) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (n+1) => F)).comp
  apply continuous_pi
  intro i
  by_cases hi : i = 0
  · subst i
    simpa [firstColumn] using (continuous_algebraMap ℝ F)
  · simp only [Pi.single_apply,hi,ite_false]
    exact continuous_const

theorem continuous_appendColumn (n q : ℕ) :
    Continuous (fun z : Row F n × Matrix (Fin n) (Fin q) F => appendColumn F z.1 z.2) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · exact (PiLp.continuous_apply 2 (fun _ : Fin n => F) i).comp continuous_fst
  · exact (continuous_apply k).comp ((continuous_apply i).comp continuous_snd)

theorem continuous_appendRow (n q : ℕ) :
    Continuous (fun z : Row F q × Matrix (Fin n) (Fin q) F => appendRow F z.1 z.2) := by
  exact (splitRowLinearEquiv F n q).toContinuousLinearEquiv.continuous

theorem unitary_mul_appendColumn {n q : ℕ}
    (U : unitary (Matrix (Fin n) (Fin n) F)) (v : Row F n)
    (G : Matrix (Fin n) (Fin q) F) :
    (U : Matrix (Fin n) (Fin n) F) * appendColumn F v G =
      appendColumn F (WithLp.toLp 2 (U.val *ᵥ (fun i => v i))) (U.val * G) := by
  ext i j
  refine Fin.cases ?_ (fun k => ?_) j
  · rfl
  · rfl

theorem gram_column_fibre_radial {n q : ℕ}
    (hF : 0 < Module.finrank ℝ F) (re : F →ₗ[ℝ] ℝ)
    (hstar : ∀ a : F, re (star a * a) = ‖a‖ ^ 2)
    (hrotate : ∀ v : Row F (n+1),
      ∃ U : unitary (Matrix (Fin (n+1)) (Fin (n+1)) F),
        (U : Matrix (Fin (n+1)) (Fin (n+1)) F) *ᵥ (fun i => v i) =
          Pi.single 0 (algebraMap ℝ F ‖v‖))
    (v : Row F (n+1)) :
    (matrixGaussian F (n+1) q).map (fun G => matrixGram F (appendColumn F v G)) =
      (matrixGaussian F (n+1) q).map (fun G =>
        matrixGram F (appendColumn F (firstColumn F n ‖v‖) G)) := by
  obtain ⟨U,hU⟩ := hrotate v
  have heq (G : Matrix (Fin (n+1)) (Fin q) F) :
      matrixGram F (appendColumn F v G) =
        matrixGram F (appendColumn F (firstColumn F n ‖v‖) (U.val * G)) := by
    rw [← matrixGram_unitary_left F U (appendColumn F v G),
      unitary_mul_appendColumn,hU]
    rfl
  have hg : Measurable (fun G : Matrix (Fin (n+1)) (Fin q) F =>
      matrixGram F (appendColumn F (firstColumn F n ‖v‖) G)) :=
    (continuous_matrixGram F (n+1) (q+1)).measurable.comp
      ((continuous_appendColumn F (n+1) q).measurable.comp
        (measurable_const.prodMk measurable_id))
  have hmul : Measurable (fun G : Matrix (Fin (n+1)) (Fin q) F => U.val * G) := by fun_prop
  calc
    _ = (matrixGaussian F (n+1) q).map
        ((fun G => matrixGram F (appendColumn F (firstColumn F n ‖v‖) G)) ∘
          (fun G => U.val * G)) := by
      congr 1
      exact funext heq
    _ = ((matrixGaussian F (n+1) q).map (fun G => U.val * G)).map
        (fun G => matrixGram F (appendColumn F (firstColumn F n ‖v‖) G)) :=
      (Measure.map_map hg hmul).symm
    _ = _ := by rw [matrixGaussian_map_unitary_left F hF re hstar U]

def radialGramInput {n q : ℕ} (t : ℝ) (z : Row F q)
    (H : Matrix (Fin n) (Fin q) F) : Hermitian F (q+1) :=
  matrixGram F (appendColumn F (firstColumn F n (Real.sqrt t)) (appendRow F z H))

theorem measurable_radialGramInput (n q : ℕ) :
    Measurable (fun z : ℝ × Row F q × Matrix (Fin n) (Fin q) F =>
      radialGramInput F z.1 z.2.1 z.2.2) := by
  unfold radialGramInput
  exact (continuous_matrixGram F (n+1) (q+1)).measurable.comp
    ((continuous_appendColumn F (n+1) q).measurable.comp
      (((continuous_firstColumn F n).measurable.comp
        (measurable_fst.sqrt)).prodMk
        ((continuous_appendRow F n q).measurable.comp measurable_snd)))

theorem matrixGram_recursive_law {n q : ℕ}
    (hF : 0 < Module.finrank ℝ F) (re : F →ₗ[ℝ] ℝ)
    (hstar : ∀ a : F, re (star a * a) = ‖a‖ ^ 2)
    (hrotate : ∀ v : Row F (n+1),
      ∃ U : unitary (Matrix (Fin (n+1)) (Fin (n+1)) F),
        (U : Matrix (Fin (n+1)) (Fin (n+1)) F) *ᵥ (fun i => v i) =
          Pi.single 0 (algebraMap ℝ F ‖v‖)) :
    (matrixGaussian F (n+1) (q+1)).map (matrixGram F) =
      ((gammaMeasure ((Module.finrank ℝ F : ℝ) * (n+1) / 2)
        ((Module.finrank ℝ F : ℝ) / 2)).prod
        ((gaussianRowWithFactor F (1 : Matrix (Fin q) (Fin q) F)).prod
          (matrixGaussian F n q))).map
        (fun z => radialGramInput F z.1 z.2.1 z.2.2) := by
  let T := fun v : Row F (n+1) => ‖v‖ ^ 2
  let f := fun z : Row F (n+1) × Matrix (Fin (n+1)) (Fin q) F =>
    matrixGram F (appendColumn F z.1 z.2)
  let g := fun z : ℝ × Matrix (Fin (n+1)) (Fin q) F =>
    matrixGram F (appendColumn F (firstColumn F n (Real.sqrt z.1)) z.2)
  have hf : Measurable f := (continuous_matrixGram F (n+1) (q+1)).measurable.comp
    (continuous_appendColumn F (n+1) q).measurable
  have hg : Measurable g := (continuous_matrixGram F (n+1) (q+1)).measurable.comp
    ((continuous_appendColumn F (n+1) q).measurable.comp
      (((continuous_firstColumn F n).measurable.comp
        (measurable_fst.sqrt)).prodMk measurable_snd))
  have hrad := Wishart.map_prod_eq_of_map_fibres
    (gaussianRowWithFactor F (1 : Matrix (Fin (n+1)) (Fin (n+1)) F))
    (matrixGaussian F (n+1) q) T (by fun_prop) f hf g hg (by
      filter_upwards [] with v
      simpa only [f,g,T,Real.sqrt_sq (norm_nonneg v)] using
        gram_column_fibre_radial F hF re hstar hrotate v)
  rw [gaussianRowWithFactor_one_norm_sq_gamma F (Nat.succ_pos n) hF] at hrad
  have hcolumn := congrArg (fun μ => μ.map (matrixGram F))
    (matrixGaussian_split_column F (n+1) q hF)
  rw [Measure.map_map (continuous_matrixGram F (n+1) (q+1)).measurable
    (continuous_appendColumn F (n+1) q).measurable] at hcolumn
  change ((gaussianRowWithFactor F (1 : Matrix (Fin (n+1)) (Fin (n+1)) F)).prod
    (matrixGaussian F (n+1) q)).map f = _ at hcolumn
  rw [← hcolumn, hrad]
  simp only [Nat.cast_succ]
  have hp := Measure.map_prod_map
    (gammaMeasure ((Module.finrank ℝ F : ℝ) * (n+1) / 2)
      ((Module.finrank ℝ F : ℝ) / 2))
    ((gaussianRowWithFactor F (1 : Matrix (Fin q) (Fin q) F)).prod
      (matrixGaussian F n q)) measurable_id (continuous_appendRow F n q).measurable
  simp only [Measure.map_id,matrixGaussian_split_row F n q hF] at hp
  rw [hp,Measure.map_map hg
    (measurable_id.prodMap (continuous_appendRow F n q).measurable)]
  rfl

def oneRowMatrix {q : ℕ} (z : Row F q) : Matrix (Fin 1) (Fin q) F :=
  Matrix.of fun _ j => z j

theorem continuous_oneRowMatrix (q : ℕ) :
    Continuous (oneRowMatrix F : Row F q → Matrix (Fin 1) (Fin q) F) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  exact PiLp.continuous_apply 2 (fun _ : Fin q => F)

theorem gaussianRow_map_oneRowMatrix (q : ℕ) :
    (gaussianRowWithFactor F (1 : Matrix (Fin q) (Fin q) F)).map (oneRowMatrix F) =
      matrixGaussian F 1 q := by
  have h := (measurePreserving_eval
    (fun _ : Fin 1 => gaussianRowWithFactor F (1 : Matrix (Fin q) (Fin q) F)) 0).map_eq
  unfold matrixGaussian
  conv_lhs => rw [← h]
  rw [Measure.map_map (continuous_oneRowMatrix F q).measurable
    (measurable_pi_apply 0)]
  congr 1
  funext z
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rfl

end Wishart.FieldGaussian
end
end CanonicalSource49
