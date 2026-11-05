import bier.forster.cauchy_binet
import bier.forster.subset_forms
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real

/-! # The weighted Gram determinant and its positive minor expansion -/

noncomputable section

namespace Bier.Forster

open Classical Finset Matrix

variable {k n : ℕ}

def weightedGram (U : Matrix (Fin k) (Fin n) ℝ) (w : Fin n → ℝ) :
    Matrix (Fin k) (Fin k) ℝ := U * diagonal w * Uᵀ

@[simp] theorem weightedGram_apply (U : Matrix (Fin k) (Fin n) ℝ)
    (w : Fin n → ℝ) (a b : Fin k) :
    weightedGram U w a b = ∑ i, w i * U a i * U b i := by
  rw [weightedGram, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, transpose_apply]
  apply Finset.sum_congr rfl
  intro i hi
  ring

def minorSquare (U : Matrix (Fin k) (Fin n) ℝ) (S : KSubset (Fin n) k) : ℝ :=
  (CauchyBinet.colsSubmatrix U S.val (mem_powersetCard.mp S.property).2).det ^ 2

theorem prod_orderEmb (S : Finset (Fin n)) (hS : S.card = k) (w : Fin n → ℝ) :
    (∏ i : Fin k, w (S.orderEmbOfFin hS i)) = ∏ i ∈ S, w i := by
  rw [← Finset.prod_image (f := w) (by
    intro a ha b hb hab
    exact (S.orderEmbOfFin hS).injective hab)]
  rw [Finset.image_orderEmbOfFin_univ]

theorem weightedGram_det (U : Matrix (Fin k) (Fin n) ℝ) (w : Fin n → ℝ) :
    (weightedGram U w).det = ∑ S : KSubset (Fin n) k,
      minorSquare U S * ∏ i ∈ S.val, w i := by
  rw [weightedGram, Matrix.mul_assoc, CauchyBinet.det_mul_eq_sum_minors]
  let f : Finset (Fin n) → ℝ := fun S =>
    if hS : S.card = k then (CauchyBinet.colsSubmatrix U S hS).det ^ 2 * ∏ i ∈ S, w i else 0
  have hs : (∑ S : KSubset (Fin n) k, minorSquare U S * ∏ i ∈ S.val, w i) =
      ∑ S ∈ (univ : Finset (Fin n)).powersetCard k, f S := by
    rw [← Finset.sum_coe_sort _ f]
    apply Finset.sum_congr rfl
    intro S hS
    simp [f, minorSquare, (mem_powersetCard.mp S.property).2]
  rw [hs]
  apply Finset.sum_congr rfl
  intro S hS
  have hcard : S.card = k := (mem_powersetCard.mp hS).2
  simp only [f, dif_pos hcard]
  let A := CauchyBinet.colsSubmatrix U S hcard
  have he : CauchyBinet.rowsSubmatrix (diagonal w * Uᵀ) S hcard =
      diagonal (fun i : Fin k => w (S.orderEmbOfFin hcard i)) * Aᵀ := by
    ext a b
    simp [CauchyBinet.rowsSubmatrix, CauchyBinet.colsSubmatrix, A,
      Matrix.diagonal_mul]
  rw [he, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_transpose, prod_orderEmb]
  change A.det * ((∏ i ∈ S, w i) * A.det) = _
  ring

theorem weightedGram_exp_det (U : Matrix (Fin k) (Fin n) ℝ)
    (x : zeroSumSpace (Fin n)) :
    (weightedGram U (fun i => Real.exp (x.val i))).det =
      exponentialSum (subsetForms (Fin n) k) (minorSquare U) x := by
  rw [weightedGram_det]
  unfold exponentialSum
  apply Finset.sum_congr rfl
  intro S hS
  rw [← Real.exp_sum]
  rw [subsetForms_apply]

theorem weightedGram_posSemidef (U : Matrix (Fin k) (Fin n) ℝ) (w : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) : (weightedGram U w).PosSemidef := by
  have hd : (diagonal w).PosSemidef := Matrix.posSemidef_diagonal_iff.mpr hw
  simpa only [weightedGram, conjTranspose_eq_transpose_of_trivial] using hd.mul_mul_conjTranspose_same U

theorem weightedGram_exp_posDef (U : Matrix (Fin k) (Fin n) ℝ)
    (hk : k ≤ n) (hu : ∀ S : KSubset (Fin n) k, 0 < minorSquare U S)
    (x : zeroSumSpace (Fin n)) :
    (weightedGram U (fun i => Real.exp (x.val i))).PosDef := by
  apply (weightedGram_posSemidef U _ (fun i => Real.exp_nonneg _)).posDef_iff_det_ne_zero.mpr
  rw [weightedGram_exp_det]
  apply ne_of_gt
  unfold exponentialSum
  apply Finset.sum_pos
  · intro S hS
    exact mul_pos (hu S) (Real.exp_pos _)
  · have hne : ((univ : Finset (Fin n)).powersetCard k).Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro he
      have hb := Finset.powersetCard_eq_empty.mp he
      simp only [card_univ, Fintype.card_fin] at hb
      omega
    exact Finset.univ_nonempty_iff.mpr hne.to_subtype

/-- The actual determinant attains its minimum on all zero-sum logarithmic
weights, assuming every maximal minor is nonzero. -/
theorem exists_weightedGram_minimum (U : Matrix (Fin k) (Fin n) ℝ)
    (hk : 0 < k) (hkn : k < n)
    (hu : ∀ S : KSubset (Fin n) k, 0 < minorSquare U S) :
    ∃ x : zeroSumSpace (Fin n), ∀ y : zeroSumSpace (Fin n),
      (weightedGram U (fun i => Real.exp (x.val i))).det ≤
        (weightedGram U (fun i => Real.exp (y.val i))).det := by
  simpa only [weightedGram_exp_det] using exists_subsetExponential_minimum
    (Fin n) k hk (by simpa using hkn) (minorSquare U) hu

end Bier.Forster
