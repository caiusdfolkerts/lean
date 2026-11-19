module

public import VolumePolynomials.FiniteBochner
public import VolumePolynomials.MatrixPositiveEigenvector
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.FieldSimp

@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# The weighted matrix form of the finite Bochner argument

For a symmetric matrix `M`, a positive vector `h` with positive `M h`
determines positive weights `mᵢ = (M h)ᵢ / hᵢ`. Conjugation by their square
roots turns the weighted operator into an ordinary symmetric Euclidean
operator. The maximum principle and the finite-dimensional spectral
theorem then give the full reverse Cauchy--Schwarz inequality.
-/

open Matrix Finset
open scoped BigOperators RealInnerProductSpace InnerProductSpace

namespace VolumePolynomials

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def matrixForm (M : Matrix ι ι ℝ) (x y : ι → ℝ) : ℝ :=
  ∑ i, (M *ᵥ x) i * y i

theorem euclidean_matrix_inner (M : Matrix ι ι ℝ)
    (x y : EuclideanSpace ℝ ι) :
    ⟪M.toEuclideanLin x, y⟫_ℝ = matrixForm M x.ofLp y.ofLp := by
  first
  | simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin,
      Matrix.toLin'_apply, dotProduct, Pi.star_apply, star_trivial, matrixForm]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- A matrix version of the already proved Euclidean Bochner reduction.
The positive-entry graph may have arbitrary diagonal entries. -/
theorem matrix_bochner_reverse_cauchy_schwarz
    (M : Matrix ι ι ℝ) (hsym : ∀ i j, M i j = M j i)
    (h : ι → ℝ) (hpos : ∀ i, 0 < h i) (hfix : M *ᵥ h = h)
    (hoff : ∀ i j, i ≠ j → 0 ≤ M i j)
    (hconn : ∀ i j, Relation.ReflTransGen (MatrixPositiveEdge M) i j)
    (hbochner : ∀ x : ι → ℝ,
      matrixForm M x x ≤ ∑ i, (M *ᵥ x) i ^ 2)
    (x y : ι → ℝ) (hy : 0 ≤ matrixForm M y y) :
    matrixForm M x x * matrixForm M y y ≤ matrixForm M x y ^ 2 := by
  first
  | cases isEmpty_or_nonempty ι with
    | inl hi =>
        letI := hi
        simp [matrixForm]
    | inr hi =>
        letI := hi
        let T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι := M.toEuclideanLin
        let e : EuclideanSpace ℝ ι := WithLp.toLp 2 h
        have hT : T.IsSymmetric := by
          apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
          ext i j
          simpa only [Matrix.conjTranspose_apply, star_trivial] using hsym j i
        have he : T e = e := by
          change WithLp.toLp 2 (M *ᵥ h) = WithLp.toLp 2 h
          rw [hfix]
        have hmax : ∀ (r : ℝ) (v : EuclideanSpace ℝ ι),
            v ≠ 0 → T v = r • v → r ≤ 1 := by
          intro r v hv heig
          have hv' : v.ofLp ≠ 0 := by
            intro hz
            apply hv
            apply WithLp.ofLp_injective
            exact hz
          have heig' : M *ᵥ v.ofLp = r • v.ofLp :=
            congrArg WithLp.ofLp heig
          exact matrix_eigenvalue_le_one_of_positive_fixed M hoff h hpos hfix r v.ofLp hv' heig'
        have hsimple : ∀ v : EuclideanSpace ℝ ι,
            T v = v → ∃ c : ℝ, v = c • e := by
          intro v hv
          have hv' : M *ᵥ v.ofLp = v.ofLp := congrArg WithLp.ofLp hv
          obtain ⟨c, hc⟩ := matrix_fixed_eq_smul_positive M hoff hconn h hpos hfix v.ofLp hv'
          exact ⟨c, WithLp.ofLp_injective 2 hc⟩
        have hbochner' : ∀ v : EuclideanSpace ℝ ι,
            ⟪T v, v⟫_ℝ ≤ ⟪T v, T v⟫_ℝ := by
          intro v
          rw [euclidean_matrix_inner]
          have hnorm : ⟪T v, T v⟫_ℝ = ∑ i, (M *ᵥ v.ofLp) i ^ 2 := by
            simp only [EuclideanSpace.inner_eq_star_dotProduct, T,
              Matrix.ofLp_toLpLin, Matrix.toLin'_apply, dotProduct,
              Pi.star_apply, star_trivial, pow_two]
          rw [hnorm]
          exact hbochner v.ofLp
        have hresult := finite_bochner_reverse_cauchy_schwarz T hT e he hmax hsimple hbochner'
          (WithLp.toLp 2 x) (WithLp.toLp 2 y)
          (by simpa only [T, euclidean_matrix_inner, WithLp.ofLp_toLp] using hy)
        simpa only [T, euclidean_matrix_inner, WithLp.ofLp_toLp] using hresult

def sqrtConjugate (M : Matrix ι ι ℝ) (m : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => M i j / (Real.sqrt (m i) * Real.sqrt (m j))

def sqrtWeighted (m x : ι → ℝ) : ι → ℝ := fun i => Real.sqrt (m i) * x i

theorem sqrtConjugate_mulVec (M : Matrix ι ι ℝ) (m : ι → ℝ)
    (hm : ∀ i, 0 < m i) (x : ι → ℝ) (i : ι) :
    (sqrtConjugate M m *ᵥ sqrtWeighted m x) i = (M *ᵥ x) i / Real.sqrt (m i) := by
  first
  | change (∑ j, M i j / (Real.sqrt (m i) * Real.sqrt (m j)) *
        (Real.sqrt (m j) * x j)) = (∑ j, M i j * x j) / Real.sqrt (m i)
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    field_simp [(Real.sqrt_pos.mpr (hm i)).ne', (Real.sqrt_pos.mpr (hm j)).ne']

theorem sqrtConjugate_form (M : Matrix ι ι ℝ) (m : ι → ℝ)
    (hm : ∀ i, 0 < m i) (x y : ι → ℝ) :
    matrixForm (sqrtConjugate M m) (sqrtWeighted m x) (sqrtWeighted m y) =
      matrixForm M x y := by
  first
  | unfold matrixForm
    apply Finset.sum_congr rfl
    intro i _
    rw [sqrtConjugate_mulVec M m hm x i]
    dsimp only [sqrtWeighted]
    field_simp [(Real.sqrt_pos.mpr (hm i)).ne']

theorem sqrtConjugate_norm (M : Matrix ι ι ℝ) (m : ι → ℝ)
    (hm : ∀ i, 0 < m i) (x : ι → ℝ) :
    (∑ i, (sqrtConjugate M m *ᵥ sqrtWeighted m x) i ^ 2) =
      ∑ i, (M *ᵥ x) i ^ 2 / m i := by
  first
  | apply Finset.sum_congr rfl
    intro i _
    rw [sqrtConjugate_mulVec M m hm x i, div_pow, Real.sq_sqrt (hm i).le]

/-- The weighted spectral criterion, with independently specified positive
weights and their actual eigenvector equation. -/
theorem weighted_matrix_reverse_cauchy_schwarz
    (M : Matrix ι ι ℝ) (hsym : ∀ i j, M i j = M j i)
    (m h : ι → ℝ) (hm : ∀ i, 0 < m i) (hh : ∀ i, 0 < h i)
    (hweighted : ∀ i, (M *ᵥ h) i = m i * h i)
    (hoff : ∀ i j, i ≠ j → 0 ≤ M i j)
    (hconn : ∀ i j, Relation.ReflTransGen (MatrixPositiveEdge M) i j)
    (hbochner : ∀ x : ι → ℝ,
      matrixForm M x x ≤ ∑ i, (M *ᵥ x) i ^ 2 / m i)
    (x y : ι → ℝ) (hy : 0 ≤ matrixForm M y y) :
    matrixForm M x x * matrixForm M y y ≤ matrixForm M x y ^ 2 := by
  first
  | let A := sqrtConjugate M m
    let e := sqrtWeighted m h
    have hA : ∀ i j, A i j = A j i := by
      intro i j
      dsimp only [A, sqrtConjugate]
      rw [hsym i j, mul_comm (Real.sqrt (m i))]
    have he : ∀ i, 0 < e i := fun i => mul_pos (Real.sqrt_pos.mpr (hm i)) (hh i)
    have hfix : A *ᵥ e = e := by
      funext i
      rw [sqrtConjugate_mulVec M m hm h i, hweighted i]
      change m i * h i / Real.sqrt (m i) = Real.sqrt (m i) * h i
      calc
        _ = Real.sqrt (m i) ^ 2 * h i / Real.sqrt (m i) :=
          congrArg (fun a : ℝ => a * h i / Real.sqrt (m i)) (Real.sq_sqrt (hm i).le).symm
        _ = _ := by
          field_simp [(Real.sqrt_pos.mpr (hm i)).ne']
    have hoffA : ∀ i j, i ≠ j → 0 ≤ A i j := by
      intro i j hij
      exact div_nonneg (hoff i j hij)
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    have hedges : ∀ i j, MatrixPositiveEdge M i j → MatrixPositiveEdge A i j := by
      rintro i j ⟨hne, hpos⟩
      exact ⟨hne, div_pos hpos (mul_pos (Real.sqrt_pos.mpr (hm i)) (Real.sqrt_pos.mpr (hm j)))⟩
    have hconnA : ∀ i j, Relation.ReflTransGen (MatrixPositiveEdge A) i j :=
      fun i j => Relation.ReflTransGen.mono hedges i j (hconn i j)
    have hbochnerA : ∀ v : ι → ℝ, matrixForm A v v ≤ ∑ i, (A *ᵥ v) i ^ 2 := by
      intro v
      let u : ι → ℝ := fun i => v i / Real.sqrt (m i)
      have hu : sqrtWeighted m u = v := by
        funext i
        exact mul_div_cancel₀ _ (Real.sqrt_pos.mpr (hm i)).ne'
      rw [← hu, sqrtConjugate_form M m hm, sqrtConjugate_norm M m hm]
      exact hbochner u
    have hresult := matrix_bochner_reverse_cauchy_schwarz A hA e he hfix hoffA hconnA hbochnerA
      (sqrtWeighted m x) (sqrtWeighted m y)
      (by rwa [sqrtConjugate_form M m hm])
    simpa only [A, sqrtConjugate_form M m hm] using hresult

/-- The form used by the geometric Alexandrov operator. The weights are
computed from `M` and `h`; there is no independent operator premise. -/
theorem matrix_reverse_cauchy_schwarz_of_weighted_bochner
    (M : Matrix ι ι ℝ) (hsym : ∀ i j, M i j = M j i)
    (h : ι → ℝ) (hh : ∀ i, 0 < h i) (hMh : ∀ i, 0 < (M *ᵥ h) i)
    (hoff : ∀ i j, i ≠ j → 0 ≤ M i j)
    (hconn : ∀ i j, Relation.ReflTransGen (MatrixPositiveEdge M) i j)
    (hbochner : ∀ x : ι → ℝ,
      matrixForm M x x ≤ ∑ i, (M *ᵥ x) i ^ 2 / ((M *ᵥ h) i / h i))
    (x y : ι → ℝ) (hy : 0 ≤ matrixForm M y y) :
    matrixForm M x x * matrixForm M y y ≤ matrixForm M x y ^ 2 := by
  first
  | apply weighted_matrix_reverse_cauchy_schwarz M hsym
      (fun i => (M *ᵥ h) i / h i) h
      (fun i => div_pos (hMh i) (hh i)) hh
      (fun i => (div_mul_cancel₀ _ (hh i).ne').symm) hoff hconn hbochner x y hy

end VolumePolynomials
