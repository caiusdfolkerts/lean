module
public import VolumePolynomials.MatrixMaximumPrinciple
public import Mathlib.Tactic.FieldSimp

@[expose] public section
noncomputable section

/-!
# Normalizing a positive eigenvector

Diagonal conjugation reduces the maximum principle for an operator with a
strictly positive fixed vector to the row-sum-one case. Diagonal entries may
have either sign, as they do for mixed-volume operators.
-/

namespace VolumePolynomials
open Finset Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def positiveConjugate (A : Matrix ι ι ℝ) (h : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => A i j * h j / h i

theorem positiveConjugate_row_sum (A : Matrix ι ι ℝ) (h : ι → ℝ)
    (hpos : ∀ i, 0 < h i) (hfix : A *ᵥ h = h) :
    ∀ i, ∑ j, positiveConjugate A h i j = 1 := by
  first
  | intro i
    simp only [positiveConjugate, ← sum_div]
    change (A *ᵥ h) i / h i = 1
    rw [hfix, div_self (hpos i).ne']

theorem positiveConjugate_offdiag (A : Matrix ι ι ℝ) (h : ι → ℝ)
    (hpos : ∀ i, 0 < h i) (hoff : ∀ i j, i ≠ j → 0 ≤ A i j) :
    ∀ i j, i ≠ j → 0 ≤ positiveConjugate A h i j := by
  first
  | intro i j hij
    exact div_nonneg (mul_nonneg (hoff i j hij) (hpos j).le) (hpos i).le

theorem positiveConjugate_positiveEdge_iff (A : Matrix ι ι ℝ) (h : ι → ℝ)
    (hpos : ∀ i, 0 < h i) (i j : ι) :
    MatrixPositiveEdge (positiveConjugate A h) i j ↔ MatrixPositiveEdge A i j := by
  first
  | simp only [MatrixPositiveEdge, positiveConjugate,
      div_pos_iff_of_pos_right (hpos i), mul_pos_iff_of_pos_right (hpos j)]

theorem positiveConjugate_mulVec (A : Matrix ι ι ℝ) (h : ι → ℝ)
    (hne : ∀ i, h i ≠ 0) (x : ι → ℝ) (i : ι) :
    (positiveConjugate A h *ᵥ (fun j => x j / h j)) i = (A *ᵥ x) i / h i := by
  first
  | change (∑ j, (A i j * h j / h i) * (x j / h j)) =
      (∑ j, A i j * x j) / h i
    rw [sum_div]
    apply sum_congr rfl
    intro j _
    field_simp [hne i, hne j]

/-- A positive fixed vector bounds every real eigenvalue by one. -/
theorem matrix_eigenvalue_le_one_of_positive_fixed (A : Matrix ι ι ℝ)
    (hoff : ∀ i j, i ≠ j → 0 ≤ A i j) (h : ι → ℝ)
    (hpos : ∀ i, 0 < h i) (hfix : A *ᵥ h = h)
    (r : ℝ) (x : ι → ℝ) (hx : x ≠ 0) (heig : A *ᵥ x = r • x) : r ≤ 1 := by
  first
  | let y : ι → ℝ := fun i => x i / h i
    have hy : y ≠ 0 := by
      intro hyzero
      apply hx
      funext i
      have hi : x i / h i = 0 := congrFun hyzero i
      exact (div_eq_zero_iff).mp hi |>.resolve_right (hpos i).ne'
    have hyeig : positiveConjugate A h *ᵥ y = r • y := by
      funext i
      rw [positiveConjugate_mulVec A h (fun j => (hpos j).ne'), heig]
      change (r * x i) / h i = r * (x i / h i)
      exact mul_div_assoc _ _ _
    exact matrix_eigenvalue_le_one (positiveConjugate A h)
      (positiveConjugate_offdiag A h hpos hoff)
      (positiveConjugate_row_sum A h hpos hfix) r y hy hyeig

/-- Positive-entry connectivity makes the fixed space exactly the span of the
positive fixed vector. -/
theorem matrix_fixed_eq_smul_positive [Nonempty ι] (A : Matrix ι ι ℝ)
    (hoff : ∀ i j, i ≠ j → 0 ≤ A i j)
    (hconn : ∀ i j, Relation.ReflTransGen (MatrixPositiveEdge A) i j)
    (h : ι → ℝ) (hpos : ∀ i, 0 < h i) (hfix : A *ᵥ h = h)
    (x : ι → ℝ) (hx : A *ᵥ x = x) : ∃ c : ℝ, x = c • h := by
  first
  | let y : ι → ℝ := fun i => x i / h i
    have hyfix : positiveConjugate A h *ᵥ y = y := by
      funext i
      rw [positiveConjugate_mulVec A h (fun j => (hpos j).ne'), hx]
    have hc : ∀ i j, Relation.ReflTransGen (MatrixPositiveEdge (positiveConjugate A h)) i j := by
      intro i j
      exact Relation.ReflTransGen.mono
        (fun a b hab => (positiveConjugate_positiveEdge_iff A h hpos a b).mpr hab)
        i j (hconn i j)
    obtain ⟨c, hc⟩ := matrix_fixed_eq_constant (positiveConjugate A h)
      (positiveConjugate_offdiag A h hpos hoff)
      (positiveConjugate_row_sum A h hpos hfix) hc y hyfix
    refine ⟨c, funext fun i => ?_⟩
    have hi : x i / h i = c := congrFun hc i
    exact (div_eq_iff (hpos i).ne').mp hi

end VolumePolynomials
