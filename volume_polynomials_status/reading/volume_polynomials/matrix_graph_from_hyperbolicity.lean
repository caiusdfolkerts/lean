module

public import VolumePolynomials.MatrixMaximumPrinciple
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.Tactic.Positivity

@[expose] public section
set_option autoImplicit false

/-!
# Connectivity from one positive direction

A symmetric matrix with nonnegative off-diagonal entries, a positive vector
whose image is positive, and the reverse Cauchy--Schwarz inequality has a
connected positive-entry graph. A disconnected component would give two
orthogonal vectors with strictly positive quadratic values. This permits the
diagonal Brunn--Minkowski case to supply connectivity without a separate
polytope face-graph theorem.
-/

noncomputable section
open Finset Matrix
open scoped BigOperators

namespace VolumePolynomials

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrix_positive_graph_connected_of_reverse_cauchy_schwarz
    (B : Matrix ι ι ℝ) (hsym : ∀ i j, B i j = B j i)
    (hoff : ∀ i j, i ≠ j → 0 ≤ B i j)
    (h : ι → ℝ) (hpos : ∀ i, 0 < h i) (himage : ∀ i, 0 < (B *ᵥ h) i)
    (hrev : ∀ x y : ι → ℝ, 0 ≤ dotProduct y (B *ᵥ y) →
      dotProduct x (B *ᵥ x) * dotProduct y (B *ᵥ y) ≤ dotProduct x (B *ᵥ y) ^ 2) :
    ∀ i j, Relation.ReflTransGen (MatrixPositiveEdge B) i j := by
  first
  | classical
    intro a b
    by_contra hab
    let S : Set ι := {i | Relation.ReflTransGen (MatrixPositiveEdge B) a i}
    have ha : a ∈ S := Relation.ReflTransGen.refl
    have hb : b ∉ S := hab
    have hcross : ∀ i ∈ S, ∀ j ∉ S, B i j = 0 := by
      intro i hi j hj
      have hij : i ≠ j := by rintro rfl; exact hj hi
      apply le_antisymm _ (hoff i j hij)
      by_contra hnot
      have hposij : 0 < B i j := lt_of_not_ge hnot
      exact hj (Relation.ReflTransGen.tail hi ⟨hij, hposij⟩)
    have hcross' : ∀ i ∉ S, ∀ j ∈ S, B i j = 0 := by
      intro i hi j hj
      rw [hsym i j]
      exact hcross j hj i hi
    let x : ι → ℝ := fun i => if i ∈ S then h i else 0
    let y : ι → ℝ := fun i => if i ∈ S then 0 else h i
    have hx : ∀ i, (B *ᵥ x) i = if i ∈ S then (B *ᵥ h) i else 0 := by
      intro i
      by_cases hi : i ∈ S
      · simp only [hi, if_pos, if_true]
        apply sum_congr rfl
        intro j _
        by_cases hj : j ∈ S
        · simp only [x, hj, if_pos, if_true]
        · simp only [x, hj, if_neg, if_false, mul_zero, hcross i hi j hj, zero_mul]
      · simp only [hi, if_neg, if_false]
        apply sum_eq_zero
        intro j _
        by_cases hj : j ∈ S
        · simp only [x, hj, if_pos, if_true, hcross' i hi j hj, zero_mul]
        · simp only [x, hj, if_neg, if_false, mul_zero]
    have hy : ∀ i, (B *ᵥ y) i = if i ∈ S then 0 else (B *ᵥ h) i := by
      intro i
      by_cases hi : i ∈ S
      · simp only [hi, if_pos, if_true]
        apply sum_eq_zero
        intro j _
        by_cases hj : j ∈ S
        · simp only [y, hj, if_pos, if_true, mul_zero]
        · simp only [y, hj, if_neg, if_false, hcross i hi j hj, zero_mul]
      · simp only [hi, if_neg, if_false]
        apply sum_congr rfl
        intro j _
        by_cases hj : j ∈ S
        · simp only [y, hj, if_pos, if_true, mul_zero, hcross' i hi j hj, zero_mul]
        · simp only [y, hj, if_neg, if_false]
    have hxx : 0 < dotProduct x (B *ᵥ x) := by
      have hn : ∀ i ∈ (univ : Finset ι), 0 ≤ x i * (B *ᵥ x) i := by
        intro i _
        rw [hx]
        by_cases hi : i ∈ S
        · simpa only [x, hi, if_pos, if_true] using (mul_pos (hpos i) (himage i)).le
        · simp only [x, hi, if_neg, if_false, mul_zero, le_refl]
      exact (sum_pos_iff_of_nonneg hn).mpr ⟨a, mem_univ a, by
        simpa only [x, ha, if_pos, if_true, hx] using mul_pos (hpos a) (himage a)⟩
    have hyy : 0 < dotProduct y (B *ᵥ y) := by
      have hn : ∀ i ∈ (univ : Finset ι), 0 ≤ y i * (B *ᵥ y) i := by
        intro i _
        rw [hy]
        by_cases hi : i ∈ S
        · simp only [y, hi, if_pos, if_true, mul_zero, le_refl]
        · simpa only [y, hi, if_neg, if_false] using (mul_pos (hpos i) (himage i)).le
      exact (sum_pos_iff_of_nonneg hn).mpr ⟨b, mem_univ b, by
        simpa only [y, hb, if_neg, if_false, hy] using mul_pos (hpos b) (himage b)⟩
    have hxy : dotProduct x (B *ᵥ y) = 0 := by
      apply sum_eq_zero
      intro i _
      rw [hy]
      by_cases hi : i ∈ S <;> simp only [x, hi, if_pos, if_true, if_neg, if_false, zero_mul, mul_zero]
    have he := hrev x y hyy.le
    rw [hxy, zero_pow (by decide : 2 ≠ 0)] at he
    exact (not_le_of_gt (mul_pos hxx hyy)) he

/-- A positive lower comparison on off-diagonal entries transfers every
positive path. Only this direction of comparison is required. -/
theorem matrix_positive_graph_connected_of_dominates
    (A B : Matrix ι ι ℝ) {c : ℝ} (hc : 0 < c)
    (hdom : ∀ i j, i ≠ j → c * B i j ≤ A i j)
    (hconn : ∀ i j, Relation.ReflTransGen (MatrixPositiveEdge B) i j) :
    ∀ i j, Relation.ReflTransGen (MatrixPositiveEdge A) i j := by
  first
  | intro i j
    exact Relation.ReflTransGen.mono
      (fun a b hab => ⟨hab.1, (mul_pos hc hab.2).trans_le (hdom a b hab.1)⟩) i j (hconn i j)

end VolumePolynomials
