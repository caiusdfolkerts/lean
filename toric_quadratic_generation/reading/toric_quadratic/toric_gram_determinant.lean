module
public import PaperVerification.CauchyBinet
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
@[expose] public section
/-!
# Gram determinants and basis marginals

These identities provide the algebraic part of the lattice-covering lemma.
The leverage identity is obtained by doubling one column weight and applying
the rank-one determinant formula; no differentiation of a matrix inverse or
an unproved log-determinant identity is required.
-/

noncomputable section

namespace PaperVerification.Toric

open scoped Matrix BigOperators
open PaperVerification.CauchyBinet

variable {d n : ℕ}

/-- The positive weighted Gram matrix of a column configuration. -/
def weightedGram (V : Matrix (Fin d) (Fin n) ℝ) (a : Fin n → ℝ) :
    Matrix (Fin d) (Fin d) ℝ := V * Matrix.diagonal a * V.transpose

/-- The squared maximal minor, extended by zero to subsets of other sizes. -/
def squaredMinor (V : Matrix (Fin d) (Fin n) ℝ) (s : Finset (Fin n)) : ℝ :=
  if hs : s.card = d then (colsSubmatrix V s hs).det ^ 2 else 0

lemma squaredMinor_nonneg (V : Matrix (Fin d) (Fin n) ℝ) (s : Finset (Fin n)) :
    0 ≤ squaredMinor V s := by
  unfold squaredMinor
  split_ifs <;> positivity

lemma prod_orderEmbOfFin (s : Finset (Fin n)) (hs : s.card = d) (a : Fin n → ℝ) :
    (∏ i : Fin d, a (s.orderEmbOfFin hs i)) = ∏ j ∈ s, a j := by
  calc
    (∏ i : Fin d, a (s.orderEmbOfFin hs i)) =
        ∏ j ∈ Finset.univ.map (s.orderEmbOfFin hs).toEmbedding, a j := by
          rw [Finset.prod_map]
          rfl
    _ = _ := by rw [Finset.map_orderEmbOfFin_univ]

lemma weightedGram_apply (V : Matrix (Fin d) (Fin n) ℝ) (a : Fin n → ℝ)
    (i j : Fin d) : weightedGram V a i j = ∑ k, a k * V i k * V j k := by
  rw [weightedGram, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The weighted Cauchy–Binet expansion, with all zero minors retained. -/
theorem weightedGram_det (V : Matrix (Fin d) (Fin n) ℝ) (a : Fin n → ℝ) :
    (weightedGram V a).det =
      ∑ s : Finset (Fin n), squaredMinor V s * ∏ j ∈ s, a j := by
  classical
  rw [weightedGram, det_mul_eq_sum_minors]
  have hminor (s : Finset (Fin n)) (hs : s.card = d) :
      (colsSubmatrix (V * Matrix.diagonal a) s hs).det *
        (rowsSubmatrix V.transpose s hs).det =
          squaredMinor V s * ∏ j ∈ s, a j := by
    have hc : colsSubmatrix (V * Matrix.diagonal a) s hs =
        colsSubmatrix V s hs *
          Matrix.diagonal (fun i => a (s.orderEmbOfFin hs i)) := by
      ext i j
      simp [colsSubmatrix, Matrix.mul_diagonal]
    have hr : rowsSubmatrix V.transpose s hs = (colsSubmatrix V s hs).transpose := by
      ext i j
      rfl
    rw [hc, hr, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_transpose,
      prod_orderEmbOfFin, squaredMinor, dif_pos hs]
    ring
  calc
    (∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard d,
        if hs : s.card = d then
          (colsSubmatrix (V * Matrix.diagonal a) s hs).det *
            (rowsSubmatrix V.transpose s hs).det else 0) =
        ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard d,
          squaredMinor V s * ∏ j ∈ s, a j := by
      apply Finset.sum_congr rfl
      intro s hs
      have hcard := (Finset.mem_powersetCard.mp hs).2
      rw [dif_pos hcard]
      exact hminor s hcard
    _ = _ := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro s _ hs
      have hcard : s.card ≠ d := by
        intro heq
        exact hs (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, heq⟩)
      simp [squaredMinor, hcard]

lemma prod_update_double (a : Fin n → ℝ) (j : Fin n) (s : Finset (Fin n)) :
    (∏ k ∈ s, Function.update a j (2 * a j) k) =
      (∏ k ∈ s, a k) + if j ∈ s then ∏ k ∈ s, a k else 0 := by
  by_cases hj : j ∈ s
  · rw [Finset.prod_update_of_mem hj, if_pos hj,
      Finset.prod_eq_mul_prod_sdiff_singleton_of_mem hj a]
    ring
  · rw [Finset.prod_update_of_notMem hj, if_neg hj, add_zero]

/-- Doubling a column weight adds exactly the basis mass of subsets containing it. -/
theorem weightedGram_det_update_double (V : Matrix (Fin d) (Fin n) ℝ)
    (a : Fin n → ℝ) (j : Fin n) :
    (weightedGram V (Function.update a j (2 * a j))).det =
      (weightedGram V a).det +
        ∑ s : Finset (Fin n),
          if j ∈ s then squaredMinor V s * ∏ k ∈ s, a k else 0 := by
  rw [weightedGram_det, weightedGram_det, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  rw [prod_update_double]
  by_cases hj : j ∈ s <;> simp [hj, mul_add]

lemma weightedGram_update_double (V : Matrix (Fin d) (Fin n) ℝ)
    (a : Fin n → ℝ) (j : Fin n) :
    weightedGram V (Function.update a j (2 * a j)) = weightedGram V a +
      Matrix.replicateCol Unit (a j • fun i => V i j) *
        Matrix.replicateRow Unit (fun i => V i j) := by
  ext i k
  have hterm (r : Fin n) :
      Function.update a j (2 * a j) r * V i r * V k r =
        a r * V i r * V k r + if r = j then a j * V i j * V k j else 0 := by
    by_cases hr : r = j
    · subst r
      simp only [Function.update_self, if_true]
      ring
    · simp [Function.update_of_ne hr, hr]
  simp only [weightedGram_apply, hterm, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.add_apply,
    Matrix.mul_apply, Fintype.sum_unique, Matrix.replicateCol_apply,
    Matrix.replicateRow_apply, Pi.smul_apply, smul_eq_mul]

/-- The basis-marginal identity used to match zonotope widths to an inverse
weighted Gram matrix. The only nondegeneracy hypothesis is invertibility. -/
theorem weightedGram_basis_marginal (V : Matrix (Fin d) (Fin n) ℝ)
    (a : Fin n → ℝ) (hunit : IsUnit (weightedGram V a).det) (j : Fin n) :
    (weightedGram V a).det *
        (a j * ((fun i => V i j) ⬝ᵥ
          ((weightedGram V a)⁻¹ *ᵥ (fun i => V i j)))) =
      ∑ s : Finset (Fin n),
        if j ∈ s then squaredMinor V s * ∏ k ∈ s, a k else 0 := by
  have hdet := weightedGram_det_update_double V a j
  rw [weightedGram_update_double,
    Matrix.det_add_replicateCol_mul_replicateRow hunit] at hdet
  rw [Matrix.mul_assoc, ← Matrix.replicateCol_mulVec,
    Matrix.det_unique (n := Unit)] at hdet
  simp only [Matrix.add_apply, Matrix.one_apply_eq,
    Matrix.replicateRow_mul_replicateCol_apply,
    Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul] at hdet
  nlinarith

end PaperVerification.Toric
