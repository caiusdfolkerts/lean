module
public import PaperVerification.FiniteExponentialBalance
public import PaperVerification.ToricGramDeterminant
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Tactic.Positivity
@[expose] public section
/-!
# Realizing matroid-base weights by a weighted Gram matrix

The basis set below consists precisely of nonsingular maximal column minors.
Every strictly positive probability distribution on these bases determines
widths realized by the inverse Gram matrix leverage formula.
-/

noncomputable section

namespace PaperVerification.Toric

open scoped Matrix BigOperators InnerProductSpace
open PaperVerification.CauchyBinet

variable {d n : ℕ}

/-- Unordered vector-space bases among the columns of a matrix. -/
def ColumnBasis (V : Matrix (Fin d) (Fin n) ℝ) :=
  {s : Finset (Fin n) // 0 < squaredMinor V s}

instance (V : Matrix (Fin d) (Fin n) ℝ) : Fintype (ColumnBasis V) := by
  classical
  unfold ColumnBasis
  infer_instance

lemma squaredMinor_pos_iff (V : Matrix (Fin d) (Fin n) ℝ) (s : Finset (Fin n)) :
    0 < squaredMinor V s ↔
      ∃ hs : s.card = d, (colsSubmatrix V s hs).det ≠ 0 := by
  by_cases hs : s.card = d
  · simp [squaredMinor, hs, sq_pos_iff]
  · simp [squaredMinor, hs]

/-- Incidence vector of a column basis in the real Euclidean coordinate space. -/
def basisIncidence (V : Matrix (Fin d) (Fin n) ℝ) (B : ColumnBasis V) :
    EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun j => if j ∈ B.val then 1 else 0)

@[simp] lemma basisIncidence_apply (V : Matrix (Fin d) (Fin n) ℝ)
    (B : ColumnBasis V) (j : Fin n) :
    basisIncidence V B j = if j ∈ B.val then 1 else 0 := rfl

/-- The width vector associated with a probability distribution on bases. -/
def basisBarycenter (V : Matrix (Fin d) (Fin n) ℝ) (p : ColumnBasis V → ℝ) :
    EuclideanSpace ℝ (Fin n) := ∑ B, p B • basisIncidence V B

lemma euclidean_sum_apply {ι : Type*} [Fintype ι]
    (f : ι → EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    (∑ i, f i) j = ∑ i, f i j := by
  change ((∑ i, f i).ofLp) j = _
  rw [WithLp.ofLp_sum, Finset.sum_apply]

lemma basisBarycenter_apply (V : Matrix (Fin d) (Fin n) ℝ)
    (p : ColumnBasis V → ℝ) (j : Fin n) :
    basisBarycenter V p j = ∑ B, if j ∈ B.val then p B else 0 := by
  rw [basisBarycenter, euclidean_sum_apply]
  apply Finset.sum_congr rfl
  intro B _
  simp [basisIncidence]

lemma basisIncidence_exp_inner (V : Matrix (Fin d) (Fin n) ℝ)
    (B : ColumnBasis V) (x : EuclideanSpace ℝ (Fin n)) :
    Real.exp ⟪basisIncidence V B, x⟫_ℝ = ∏ j ∈ B.val, Real.exp (x j) := by
  have hi : ⟪basisIncidence V B, x⟫_ℝ = ∑ j ∈ B.val, x j := by
    simp [basisIncidence, PiLp.inner_apply, Finset.sum_ite_mem, mul_comm]
  rw [hi, Real.exp_sum]

/-- Remove zero terms from a sum indexed by all column subsets. -/
lemma sum_columnBasis_eq (V : Matrix (Fin d) (Fin n) ℝ)
    (f : Finset (Fin n) → ℝ)
    (hf : ∀ s, squaredMinor V s = 0 → f s = 0) :
    (∑ B : ColumnBasis V, f B.val) = ∑ s, f s := by
  classical
  calc
    (∑ B : ColumnBasis V, f B.val) =
        ∑ s ∈ Finset.univ.filter (fun s => 0 < squaredMinor V s), f s := by
      exact (Finset.sum_subtype _ (by simp) f).symm
    _ = _ := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro s _ hs
      have hnot : ¬ 0 < squaredMinor V s := by simpa using hs
      exact hf s (le_antisymm (le_of_not_gt hnot) (squaredMinor_nonneg V s))

lemma weightedGram_det_eq_basis_sum (V : Matrix (Fin d) (Fin n) ℝ) (a : Fin n → ℝ) :
    (weightedGram V a).det =
      ∑ B : ColumnBasis V, squaredMinor V B.val * ∏ j ∈ B.val, a j := by
  rw [weightedGram_det]
  exact (sum_columnBasis_eq V _ (by intro s hs; simp [hs])).symm

lemma weightedGram_det_pos (V : Matrix (Fin d) (Fin n) ℝ)
    [Nonempty (ColumnBasis V)] (a : Fin n → ℝ) (ha : ∀ j, 0 < a j) :
    0 < (weightedGram V a).det := by
  rw [weightedGram_det_eq_basis_sum]
  exact Finset.sum_pos
    (fun B _ => mul_pos B.property (Finset.prod_pos (fun j _ => ha j)))
    Finset.univ_nonempty

lemma weightedGram_posDef (V : Matrix (Fin d) (Fin n) ℝ)
    [Nonempty (ColumnBasis V)] (a : Fin n → ℝ) (ha : ∀ j, 0 < a j) :
    (weightedGram V a).PosDef := by
  have hpsd : (weightedGram V a).PosSemidef := by
    have hdiag : (Matrix.diagonal a).PosSemidef :=
      Matrix.PosSemidef.diagonal (fun j => (ha j).le)
    simpa [weightedGram, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hdiag.mul_mul_conjTranspose_same V
  exact (hpsd.posDef_iff_det_ne_zero).mpr (weightedGram_det_pos V a ha).ne'

/-- Every positive convex combination of basis indicators is realized by a
positive column weighting and its inverse Gram matrix. -/
theorem basisBarycenter_realized (V : Matrix (Fin d) (Fin n) ℝ)
    [Nonempty (ColumnBasis V)]
    (p : ColumnBasis V → ℝ) (hp : ∀ B, 0 < p B) (hpsum : ∑ B, p B = 1) :
    ∃ a : Fin n → ℝ, (∀ j, 0 < a j) ∧
      ∀ j, basisBarycenter V p j =
        a j * ((fun i => V i j) ⬝ᵥ ((weightedGram V a)⁻¹ *ᵥ (fun i => V i j))) := by
  obtain ⟨x, hx⟩ := finite_exponential_barycenter
    (basisIncidence V) p hp hpsum (fun B => squaredMinor V B.val)
    (fun B => B.property)
  change (∑ B : ColumnBasis V,
    (squaredMinor V B.val * Real.exp ⟪basisIncidence V B, x⟫_ℝ) •
      (basisIncidence V B - basisBarycenter V p)) = 0 at hx
  let a : Fin n → ℝ := fun j => Real.exp (x j)
  have ha : ∀ j, 0 < a j := fun j => Real.exp_pos _
  have hdet : 0 < (weightedGram V a).det := weightedGram_det_pos V a ha
  refine ⟨a, ha, ?_⟩
  intro j
  have hj := congrArg (fun z : EuclideanSpace ℝ (Fin n) => z j) hx
  simp only [euclidean_sum_apply, PiLp.smul_apply, PiLp.sub_apply, PiLp.zero_apply,
    basisIncidence_exp_inner, basisIncidence_apply, smul_eq_mul] at hj
  change (∑ B : ColumnBasis V,
    (squaredMinor V B.val * ∏ k ∈ B.val, a k) *
      ((if j ∈ B.val then 1 else 0) - basisBarycenter V p j)) = 0 at hj
  have hmass :
      (∑ B : ColumnBasis V,
        if j ∈ B.val then squaredMinor V B.val * ∏ k ∈ B.val, a k else 0) =
        (weightedGram V a).det * basisBarycenter V p j := by
    have hsplit :
        (∑ B : ColumnBasis V,
          (squaredMinor V B.val * ∏ k ∈ B.val, a k) *
            ((if j ∈ B.val then 1 else 0) - basisBarycenter V p j)) =
          (∑ B : ColumnBasis V,
            if j ∈ B.val then squaredMinor V B.val * ∏ k ∈ B.val, a k else 0) -
            (weightedGram V a).det * basisBarycenter V p j := by
      rw [weightedGram_det_eq_basis_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro B _
      split_ifs <;> ring
    rw [hsplit] at hj
    exact sub_eq_zero.mp hj
  have hsum :
      (∑ s : Finset (Fin n),
        if j ∈ s then squaredMinor V s * ∏ k ∈ s, a k else 0) =
        (weightedGram V a).det * basisBarycenter V p j := by
    rw [← sum_columnBasis_eq V _ (by intro s hs; simp [hs])]
    exact hmass
  have hmarg := weightedGram_basis_marginal V a (isUnit_iff_ne_zero.mpr hdet.ne') j
  rw [hsum] at hmarg
  exact (mul_left_cancel₀ hdet.ne' hmarg).symm

end PaperVerification.Toric
