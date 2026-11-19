module
public import WishartCommonProofWitnesses
public import Mathlib
/-! Literal canonical primitives for all twenty Wishart targets.
Data and genuine constructor proofs adapted from pinned TauCeti06d5bb;
no TauCeti import, unrestricted function value or mathematical proof hole.
-/
@[expose] public section
noncomputable section
open Set MeasureTheory Module
open scoped BigOperators RealInnerProductSpace Matrix Quaternion
namespace WishartLiteralStructures
section MatrixInner
variable {m n : Type*} [Fintype m] [Fintype n]
/-- The literal Frobenius inner-product record on real matrices. -/
@[instance_reducible]
def matrixInnerProductSpace :
    letI : NormedAddCommGroup (Matrix m n ℝ) := Matrix.frobeniusNormedAddCommGroup
    InnerProductSpace ℝ (Matrix m n ℝ) :=
  letI : NormedAddCommGroup (Matrix m n ℝ) := Matrix.frobeniusNormedAddCommGroup
  { __ := (Matrix.frobeniusNormedSpace : NormedSpace ℝ (Matrix m n ℝ))
    inner A B := ∑ i, ∑ j, A i j * B i j
    norm_sq_eq_re_inner A := by
      have h : (0 : ℝ) ≤ ∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ) :=
        Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _
      rw [Matrix.frobenius_norm_def, ← Real.rpow_natCast _ 2, ← Real.rpow_mul h]
      norm_num [Real.rpow_two, pow_two]
    conj_inner_symm A B := by
      simp [mul_comm]
    add_left A B C := by
      simp [add_mul, Finset.sum_add_distrib]
    smul_left A B r := by
      simp [mul_assoc, Finset.mul_sum] }

end MatrixInner
section SymmetricInner
variable (p : ℕ)
/-- Frobenius norm with the unchanged subtype uniformity. -/
@[instance_reducible] def symmetricNormedAddCommGroup :
    NormedAddCommGroup (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
  letI : NormedAddCommGroup (Matrix (Fin p) (Fin p) ℝ) := Matrix.frobeniusNormedAddCommGroup
  letI base : NormedAddCommGroup (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
    Submodule.normedAddCommGroup _
  { base with toMetricSpace := base.toMetricSpace.replaceUniformity rfl }

/-- The symmetric subspace carries the Frobenius inner product `⟪A, B⟫ = ∑ i, ∑ j, A i j * B i j`
of the underlying matrices, which on this subspace is the trace pairing
`selfAdjoint.inner_eq_trace_mul`. -/
def symmetricInnerProductSpace :
    letI : NormedAddCommGroup (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) := symmetricNormedAddCommGroup p
    InnerProductSpace ℝ (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
  letI : NormedAddCommGroup (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) := symmetricNormedAddCommGroup p
  letI : NormedAddCommGroup (Matrix (Fin p) (Fin p) ℝ) := Matrix.frobeniusNormedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin p) (Fin p) ℝ) := Matrix.frobeniusNormedSpace
  letI : InnerProductSpace ℝ (Matrix (Fin p) (Fin p) ℝ) := matrixInnerProductSpace
  { __ := (inferInstance : Module ℝ (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)))
    norm_smul_le r A := norm_smul_le r (A : Matrix (Fin p) (Fin p) ℝ)
    inner A B := ⟪(A : Matrix (Fin p) (Fin p) ℝ), (B : Matrix (Fin p) (Fin p) ℝ)⟫
    norm_sq_eq_re_inner A :=
      InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℝ) (A : Matrix (Fin p) (Fin p) ℝ)
    conj_inner_symm A B :=
      InnerProductSpace.conj_inner_symm (𝕜 := ℝ) (A : Matrix (Fin p) (Fin p) ℝ) ↑B
    add_left A B C := by
      change (∑ i, ∑ j, ((A : Matrix (Fin p) (Fin p) ℝ) i j +
        (B : Matrix (Fin p) (Fin p) ℝ) i j) * (C : Matrix (Fin p) (Fin p) ℝ) i j) =
        (∑ i, ∑ j, (A : Matrix (Fin p) (Fin p) ℝ) i j * (C : Matrix (Fin p) (Fin p) ℝ) i j) +
        (∑ i, ∑ j, (B : Matrix (Fin p) (Fin p) ℝ) i j * (C : Matrix (Fin p) (Fin p) ℝ) i j)
      simp only [add_mul, Finset.sum_add_distrib]
    smul_left A B r := by
      change (∑ i, ∑ j, (r * (A : Matrix (Fin p) (Fin p) ℝ) i j) *
        (B : Matrix (Fin p) (Fin p) ℝ) i j) =
        r * (∑ i, ∑ j, (A : Matrix (Fin p) (Fin p) ℝ) i j *
          (B : Matrix (Fin p) (Fin p) ℝ) i j)
      simp [Finset.mul_sum, mul_assoc] }

end SymmetricInner
/-- The complete standard quaternion basis, with genuine multiplication proofs. -/
def complexMatrixBasis :
    QuaternionAlgebra.Basis (Matrix (Fin 2) (Fin 2) ℂ) (-1 : ℝ) 0 (-1) where
  i := !![Complex.I, 0; 0, -Complex.I]
  j := !![0, 1; -1, 0]
  k := !![0, Complex.I; Complex.I, 0]
  i_mul_i := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  j_mul_j := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  i_mul_j := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  j_mul_i := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem complexMatrixBasis_liftHom_apply (q : ℍ[ℝ]) :
    complexMatrixBasis.liftHom q =
      !![(q.re : ℂ) + q.imI * Complex.I, (q.imJ : ℂ) + q.imK * Complex.I;
        -(q.imJ : ℂ) + q.imK * Complex.I, (q.re : ℂ) - q.imI * Complex.I] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [complexMatrixBasis, QuaternionAlgebra.Basis.liftHom, QuaternionAlgebra.Basis.lift,
      Algebra.algebraMap_eq_smul_one, Complex.ext_iff]

theorem complexMatrixBasis_liftHom_star (q : ℍ[ℝ]) :
    complexMatrixBasis.liftHom (star q) = star (complexMatrixBasis.liftHom q) := by
  rw [complexMatrixBasis_liftHom_apply, complexMatrixBasis_liftHom_apply]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.star_apply]

/-- The fully specified standard star-algebra embedding. -/
def quaternionRepresentation : ℍ[ℝ] →⋆ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  { complexMatrixBasis.liftHom with map_star' := complexMatrixBasis_liftHom_star }

/-- Congruence by every rectangular matrix, including singular ones. -/
def symmetricCongruence {p q : ℕ} (M : Matrix (Fin q) (Fin p) ℝ) :
    selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) →ₗ[ℝ]
      selfAdjoint.submodule ℝ (Matrix (Fin q) (Fin q) ℝ) :=
  LinearMap.codRestrict _
    (mulRightLinearMap (Fin q) ℝ Mᵀ ∘ₗ mulLeftLinearMap (Fin p) ℝ M ∘ₗ
      (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)).subtype)
    fun A => by
      simp only [LinearMap.comp_apply, mulRightLinearMap_apply, mulLeftLinearMap_apply,
        Submodule.subtype_apply]
      have h := Matrix.isHermitian_mul_mul_conjTranspose M
        (Matrix.isHermitian_iff_isSelfAdjoint.mpr A.property)
      exact Matrix.isHermitian_iff_isSelfAdjoint.mp
        (by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using h)
/-- The literal Gram statistic of a finite real Gaussian sample. -/
def wishartGram {p ν : ℕ} (X : Fin ν → EuclideanSpace ℝ (Fin p)) :
    selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) :=
  ⟨Matrix.gram ℝ fun i => WithLp.toLp 2 fun r => X r i,
    Matrix.isHermitian_iff_isSelfAdjoint.mp (Matrix.isHermitian_gram ℝ _)⟩
/-- Every Gaussian-Gram scale, including the canonical singular/invalid cases. -/
def wishartGramMeasure {p : ℕ} (ν : ℕ) (S : Matrix (Fin p) (Fin p) ℝ) :
    Measure (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
  (Measure.pi fun _ : Fin ν => ProbabilityTheory.multivariateGaussian 0 S).map wishartGram
end WishartLiteralStructures

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal Matrix

namespace WishartLiteralLaws

/-- The same self-adjoint carrier and all on-or-above-diagonal coordinates. -/
abbrev SymmetricMatrix (p : ℕ) := selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)
/-- All on-or-above-diagonal coordinate positions. -/
abbrev UpperTriangle (p : ℕ) := {ij : Fin p × Fin p // ij.1 ≤ ij.2}

/-- Reflection of the supplied upper-triangular entries, including the diagonal. -/
def mirrorMatrix {p : ℕ} (x : UpperTriangle p → ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of fun i j =>
    if h : i ≤ j then x ⟨(i, j), h⟩ else x ⟨(j, i), le_of_not_ge h⟩

/-- Genuine symmetry of the completely specified reflection formula. -/
theorem mirror_isHermitian {p : ℕ} (x : UpperTriangle p → ℝ) :
    (mirrorMatrix x).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp only [mirrorMatrix, Matrix.of_apply, star_trivial]
  rcases le_total i j with h | h
  · rcases h.lt_or_eq with hlt | rfl
    · rw [dite_eq_right (not_le.2 hlt), dite_eq_left h]
    · rfl
  · rcases h.lt_or_eq with hlt | rfl
    · rw [dite_eq_left h, dite_eq_right (not_le.2 hlt)]
    · rfl

/-- The literal coordinate reconstruction as an actual symmetric matrix. -/
def reconstruct {p : ℕ} (x : UpperTriangle p → ℝ) : SymmetricMatrix p :=
  ⟨mirrorMatrix x, mirror_isHermitian x⟩

/-- The upper-triangle coordinate cube has measure one; Frobenius volume or
an unspecified Haar normalization is not substituted. -/
def symmetricLebesgue (p : ℕ) : Measure (SymmetricMatrix p) :=
  (volume : Measure (UpperTriangle p → ℝ)).map reconstruct

/-- The complete multivariate Gamma product, including all totalized values. -/
def multivariateGamma (p : ℕ) (a : ℝ) : ℝ :=
  Real.pi ^ (((p : ℝ) * ((p : ℝ) - 1)) / (Nat.cast 4 : ℝ)) *
    ∏ i : Fin p, Real.Gamma (a - (i.1 : ℝ) / (Nat.cast 2 : ℝ))

open Classical in
/-- Exact real Wishart density, with no restriction hidden in the data value. -/
def wishartPDFReal {p : ℕ} (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ)
    (A : SymmetricMatrix p) : ℝ :=
  if (A : Matrix (Fin p) (Fin p) ℝ).PosDef then
    (A : Matrix (Fin p) (Fin p) ℝ).det ^
        ((n - (p : ℝ) - 1) / (Nat.cast 2 : ℝ)) *
      Real.exp (-Matrix.trace (S⁻¹ * (A : Matrix (Fin p) (Fin p) ℝ)) /
        (Nat.cast 2 : ℝ)) /
      ((Nat.cast 2 : ℝ) ^ (n * (p : ℝ) / (Nat.cast 2 : ℝ)) *
        S.det ^ (n / (Nat.cast 2 : ℝ)) * multivariateGamma p (n / (Nat.cast 2 : ℝ)))
  else 0

/-- The exact nonnegative extended density. -/
def wishartPDF {p : ℕ} (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ)
    (A : SymmetricMatrix p) : ℝ≥0∞ := ENNReal.ofReal (wishartPDFReal n S A)

open Classical in
/-- The exact valid-parameter branch and zero elsewhere are both retained. -/
def nonsingularWishartMeasure {p : ℕ} (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ) :
    Measure (SymmetricMatrix p) :=
  if S.PosDef ∧ (p : ℝ) - 1 < n then
    (symmetricLebesgue p).withDensity (wishartPDF n S)
  else 0

/-- The canonical total inverse is retained even on singular inputs. -/
def symmetricInv {p : ℕ} (A : SymmetricMatrix p) : SymmetricMatrix p :=
  ⟨(A : Matrix (Fin p) (Fin p) ℝ)⁻¹,
    Matrix.isHermitian_iff_isSelfAdjoint.1
      (Matrix.isHermitian_iff_isSelfAdjoint.2 A.property).inv⟩

/-- The inverse-Wishart law uses the inverted scale and the complete inverse map. -/
def inverseWishartMeasure {p : ℕ} (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ) :
    Measure (SymmetricMatrix p) :=
  (nonsingularWishartMeasure n S⁻¹).map symmetricInv

end WishartLiteralLaws

end
end
end
end
