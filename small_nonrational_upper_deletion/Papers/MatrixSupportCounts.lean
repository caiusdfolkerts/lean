module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-!
# Supports and nonzero-entry counts for finite matrices

These generic definitions are shared by the finite algebra classification and
actual-polytope geometry. They have no geometric or certificate assumptions.

-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity
open scoped Classical BigOperators

def vectorSupport {I : Type*} [Fintype I] (v : I → ℝ) : Finset I :=
  Finset.univ.filter fun i => v i ≠ 0

@[simp] theorem mem_vectorSupport {I : Type*} [Fintype I] (v : I → ℝ) (i : I) :
    i ∈ vectorSupport v ↔ v i ≠ 0 := by simp [vectorSupport]

def totalNonzeros {I J : Type*} [Fintype I] [Fintype J] (C : I → J → ℝ) : ℕ :=
  ∑ i, (vectorSupport (C i)).card

def columnSupport {I J : Type*} [Fintype I] (C : I → J → ℝ) (j : J) : Finset I :=
  Finset.univ.filter fun i => C i j ≠ 0

def activeColumns {I J : Type*} [Fintype I] [Fintype J] (C : I → J → ℝ) : Finset J :=
  Finset.univ.filter fun j => ∃ i, C i j ≠ 0

@[simp] theorem mem_activeColumns {I J : Type*} [Fintype I] [Fintype J]
    (C : I → J → ℝ) (j : J) : j ∈ activeColumns C ↔ ∃ i, C i j ≠ 0 := by
  simp only [activeColumns, Finset.mem_filter, Finset.mem_univ, true_and]

theorem totalNonzeros_eq_sum_columns {I J : Type*} [Fintype I] [Fintype J]
    (C : I → J → ℝ) : totalNonzeros C = ∑ j, (columnSupport C j).card := by
  simp only [totalNonzeros, vectorSupport, columnSupport, Finset.card_filter]
  rw [Finset.sum_comm]

theorem four_mul_activeColumns_le {I J : Type*} [Fintype I] [Fintype J]
    (C : I → J → ℝ) (h : ∀ j ∈ activeColumns C, 4 ≤ (columnSupport C j).card) :
    4 * (activeColumns C).card ≤ totalNonzeros C := by
  rw [totalNonzeros_eq_sum_columns]
  calc
    4 * (activeColumns C).card = ∑ _j ∈ activeColumns C, 4 := by simp [mul_comm]
    _ ≤ ∑ j ∈ activeColumns C, (columnSupport C j).card :=
      Finset.sum_le_sum h
    _ ≤ ∑ j, (columnSupport C j).card :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)

end Papers.RationalityTen.ChirotopeDensity
