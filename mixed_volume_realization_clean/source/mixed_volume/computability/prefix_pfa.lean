/- Exact seven-state positive PFA for arbitrary one-sided correspondence instances. -/
module

public import mixed_volume.computability.uniform_mix
public import mixed_volume.computability.prefix_source
public import Mathlib.LinearAlgebra.Matrix.Reindex

set_option autoImplicit false

@[expose] public section
noncomputable section
open Matrix
open scoped BigOperators

namespace MixedVolume.PrefixPFA

open FractionalWords SevenState UniformMix MatrixMortality

variable {α : Type*} [Fintype α]

def family (upper lower : α → List Bool) (u v : List Bool) : Option α → M7
  | none => C u v
  | some a => C (upper a) (lower a)

theorem family_row_sum (upper lower : α → List Bool) (u v : List Bool)
    (a : Option α) (i : State) : ∑ j, family upper lower u v a i j = 1 := by
  cases a <;> exact C_row_sum _ _ _

theorem family_column_sum (upper lower : α → List Bool) (u v : List Bool)
    (a : Option α) (j : State) : ∑ i, family upper lower u v a i j = 1 := by
  cases a <;> exact C_column_sum _ _ _

def P (upper lower : α → List Bool) (u v : List Bool) (a : α) : M7 :=
  transition (family upper lower u v) (some a)

def initial (upper lower : α → List Bool) (u v : List Bool) : State → ℚ :=
  start ᵥ* transition (family upper lower u v) none

theorem P_positive (upper lower : α → List Bool) (u v : List Bool)
    (a : α) (i j : State) : 0 < P upper lower u v a i j :=
  transition_positive _ _ _ _

theorem P_row_sum (upper lower : α → List Bool) (u v : List Bool)
    (a : α) (i : State) : ∑ j, P upper lower u v a i j = 1 :=
  transition_row_sum _ (family_row_sum upper lower u v) _ _

theorem P_column_sum (upper lower : α → List Bool) (u v : List Bool)
    (a : α) (j : State) : ∑ i, P upper lower u v a i j = 1 :=
  transition_column_sum _ (family_column_sum upper lower u v) _ _

theorem initial_nonneg (upper lower : α → List Bool) (u v : List Bool) (j : State) :
    0 ≤ initial upper lower u v j :=
  start_mul_nonneg _ (fun i j => (transition_positive _ _ i j).le) j

theorem initial_sum (upper lower : α → List Bool) (u v : List Bool) :
    ∑ j, initial upper lower u v j = 1 :=
  start_mul_sum _ (transition_row_sum _ (family_row_sum upper lower u v) none)

theorem initial_product_eq (upper lower : α → List Bool) (u v : List Bool) (w : List α) :
    initial upper lower u v ᵥ* wordProduct (P upper lower u v) w =
      start ᵥ* wordProduct (transition (family upper lower u v)) (none :: w.map some) := by
  rw [initial, Matrix.vecMul_vecMul, wordProduct_cons]
  congr 2
  simp only [wordProduct, List.map_map, Function.comp_def]
  rfl

theorem family_product_score (upper lower : α → List Bool) (u v : List Bool) (w : List α) :
    (SevenState.row ᵥ* wordProduct (family upper lower u v) (none :: w.map some)) (some 0) =
      score (u ++ spell upper w) (v ++ spell lower w) := by
  rw [wordProduct_cons]
  have he : wordProduct (family upper lower u v) (w.map some) =
      wordProduct (fun a => C (upper a) (lower a)) w := by
    simp only [wordProduct, List.map_map, Function.comp_def, family]
  rw [he]
  change (SevenState.row ᵥ* (C u v *
    wordProduct (fun a => C (upper a) (lower a)) w)) (some 0) = _
  rw [wordProduct_C, ← C_append, row_C_first]

/-- Exact acceptance probability, with the prefix absorbed into the actual
initial probability distribution. The formula includes empty source words. -/
theorem acceptance (upper lower : α → List Bool) (u v : List Bool) (w : List α) :
    (initial upper lower u v ᵥ* wordProduct (P upper lower u v) w) (some 0) =
      1 / 7 + (mixing (family upper lower u v) ^ (w.length + 1) / 21) *
        score (u ++ spell upper w) (v ++ spell lower w) := by
  rw [initial_product_eq, acceptance_formula _ (family_row_sum upper lower u v)
    (family_column_sum upper lower u v), family_product_score]
  simp only [List.length_cons, List.length_map]

theorem acceptance_gt_cutpoint_iff (upper lower : α → List Bool)
    (u v : List Bool) (w : List α) :
    1 / 7 < (initial upper lower u v ᵥ* wordProduct (P upper lower u v) w) (some 0) ↔
      u ++ spell upper w = v ++ spell lower w := by
  rw [acceptance, lt_add_iff_pos_right, mul_pos_iff_of_pos_left
    (div_pos (pow_pos (mixing_pos _) _) (by norm_num)), score_pos_iff]

theorem acceptance_ge_cutpoint_iff (upper lower : α → List Bool)
    (u v : List Bool) (w : List α) :
    1 / 7 ≤ (initial upper lower u v ᵥ* wordProduct (P upper lower u v) w) (some 0) ↔
      u ++ spell upper w = v ++ spell lower w := by
  rw [acceptance, le_add_iff_nonneg_right, mul_nonneg_iff_of_pos_left
    (div_pos (pow_pos (mixing_pos _) _) (by norm_num)), score_nonneg_iff]

/-- The checked state set is explicitly equivalent to `Fin 7`, with the
designated accepting state corresponding to index zero. -/
def stateEquiv : Fin 7 ≃ State := finSuccEquivLast

@[simp] theorem stateEquiv_zero : stateEquiv 0 = some 0 := rfl

def relabelMatrix (M : M7) : Matrix (Fin 7) (Fin 7) ℚ := M.submatrix stateEquiv stateEquiv
def relabelRow (p : State → ℚ) : Fin 7 → ℚ := p ∘ stateEquiv

theorem relabelMatrix_one : relabelMatrix 1 = 1 := by
  exact Matrix.submatrix_one_equiv stateEquiv

theorem relabelMatrix_mul (M N : M7) :
    relabelMatrix (M * N) = relabelMatrix M * relabelMatrix N := by
  exact (Matrix.submatrix_mul_equiv M N stateEquiv stateEquiv stateEquiv).symm

theorem relabelRow_vecMul (p : State → ℚ) (M : M7) :
    relabelRow p ᵥ* relabelMatrix M = relabelRow (p ᵥ* M) := by
  funext j
  exact stateEquiv.sum_comp (fun i => p i * M i (stateEquiv j))

theorem relabel_wordProduct (Q : α → M7) (w : List α) :
    wordProduct (fun a => relabelMatrix (Q a)) w = relabelMatrix (wordProduct Q w) := by
  induction w with
  | nil => simp [relabelMatrix_one]
  | cons a w ih => rw [wordProduct_cons, wordProduct_cons, ih, relabelMatrix_mul]

theorem relabel_acceptance (upper lower : α → List Bool) (u v : List Bool) (w : List α) :
    (relabelRow (initial upper lower u v) ᵥ*
      wordProduct (fun a => relabelMatrix (P upper lower u v a)) w) 0 =
      (initial upper lower u v ᵥ* wordProduct (P upper lower u v) w) (some 0) := by
  rw [relabel_wordProduct, relabelRow_vecMul]
  rfl

end MixedVolume.PrefixPFA
