/- Positive doubly-stochasticization with an exact all-word acceptance formula. -/
module

public import mixed_volume.computability.seven_state
public import Mathlib.Tactic.Module

set_option autoImplicit false

@[expose] public section
noncomputable section
open Matrix
open scoped BigOperators

namespace MixedVolume.UniformMix

open SevenState MatrixMortality

def J : M7 := fun _ _ => 1 / 7
def uniform : State → ℚ := fun _ => 1 / 7

theorem J_row_sum (i : State) : ∑ j, J i j = 1 := by norm_num [J]
theorem J_column_sum (j : State) : ∑ i, J i j = 1 := by norm_num [J]

theorem J_mul (M : M7) (hc : ∀ j, ∑ i, M i j = 1) : J * M = J := by
  ext i j
  simp only [Matrix.mul_apply, J, ← Finset.mul_sum, hc, mul_one]

theorem mul_J (M : M7) (hr : ∀ i, ∑ j, M i j = 1) : M * J = J := by
  ext i j
  simp only [Matrix.mul_apply, J, ← Finset.sum_mul, hr, one_mul]

theorem J_idempotent : J * J = J := J_mul J J_column_sum

variable {α : Type*} [Fintype α]

/-- An explicit rational bound; no uncomputed maximum or existential parameter
is used in the stochastic compiler. -/
def cap (C : α → M7) : ℚ := ∑ a, ∑ i, ∑ j, |C a i j|

theorem cap_nonneg (C : α → M7) : 0 ≤ cap C := by
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro i _
  exact Finset.sum_nonneg (fun j _ => abs_nonneg _)

theorem abs_le_cap (C : α → M7) (a : α) (i j : State) : |C a i j| ≤ cap C := by
  classical
  have h1 : |C a i j| ≤ ∑ k, |C a i k| :=
    Finset.single_le_sum (f := fun k : State => |C a i k|)
      (fun k _ => abs_nonneg (C a i k)) (Finset.mem_univ j)
  have h2 : (∑ k, |C a i k|) ≤ ∑ l, ∑ k, |C a l k| :=
    Finset.single_le_sum (f := fun l : State => ∑ k : State, |C a l k|)
      (fun l _ => Finset.sum_nonneg (fun k _ => abs_nonneg (C a l k)))
      (Finset.mem_univ i)
  have h3 : (∑ l, ∑ k, |C a l k|) ≤ cap C :=
    Finset.single_le_sum (f := fun b : α => ∑ l : State, ∑ k : State, |C b l k|)
      (fun b _ => Finset.sum_nonneg
      (fun l _ => Finset.sum_nonneg (fun k _ => abs_nonneg (C b l k)))) (Finset.mem_univ a)
  exact h1.trans (h2.trans h3)

def mixing (C : α → M7) : ℚ := 1 / (7 * cap C + 8)

theorem mixing_pos (C : α → M7) : 0 < mixing C := by
  unfold mixing
  have h := cap_nonneg C
  positivity

def transition (C : α → M7) (a : α) : M7 :=
  mixing C • C a + (1 - mixing C) • J

theorem transition_positive (C : α → M7) (a : α) (i j : State) :
    0 < transition C a i j := by
  have hm := cap_nonneg C
  have ha := mixing_pos C
  have hb : -(cap C) ≤ C a i j := by
    have h := abs_le_cap C a i j
    exact (abs_le.mp h).1
  have hlow := mul_le_mul_of_nonneg_left hb ha.le
  have he : (1 - mixing C) / 7 - mixing C * cap C = mixing C := by
    unfold mixing
    field_simp
    <;> ring
  simp only [transition, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, J]
  nlinarith

theorem transition_row_sum (C : α → M7) (hr : ∀ a i, ∑ j, C a i j = 1)
    (a : α) (i : State) : ∑ j, transition C a i j = 1 := by
  simp only [transition, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum, hr, J_row_sum]
  ring

theorem transition_column_sum (C : α → M7) (hc : ∀ a j, ∑ i, C a i j = 1)
    (a : α) (j : State) : ∑ i, transition C a i j = 1 := by
  simp only [transition, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum, hc, J_column_sum]
  ring

theorem J_wordProduct (C : α → M7) (hc : ∀ a j, ∑ i, C a i j = 1)
    (w : List α) : J * wordProduct C w = J := by
  induction w with
  | nil => simp
  | cons a w ih => rw [wordProduct_cons, ← mul_assoc, J_mul (C a) (hc a), ih]

/-- This formula includes the empty word: both sides are then the identity. -/
theorem wordProduct_transition (C : α → M7)
    (hr : ∀ a i, ∑ j, C a i j = 1) (hc : ∀ a j, ∑ i, C a i j = 1)
    (w : List α) :
    wordProduct (transition C) w =
      mixing C ^ w.length • wordProduct C w + (1 - mixing C ^ w.length) • J := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [wordProduct_cons, wordProduct_cons, ih]
    simp only [transition, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, mul_J (C a) (hr a), J_wordProduct C hc w,
      J_idempotent, List.length_cons, pow_succ]
    module

/-- A fixed positive probability row. -/
def start : State → ℚ := uniform + (1 / 21 : ℚ) • SevenState.row

theorem start_sum : ∑ i, start i = 1 := by
  simp only [start, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, SevenState.row_sum, mul_zero, add_zero, uniform]
  norm_num

theorem start_positive (i : State) : 0 < start i := by
  have h := (SevenState.row_bounds i).1
  change 0 < 1 / 7 + (1 / 21) * SevenState.row i
  linarith

theorem uniform_wordProduct (C : α → M7) (hc : ∀ a j, ∑ i, C a i j = 1)
    (w : List α) : uniform ᵥ* wordProduct C w = uniform := by
  funext j
  have h := congrFun (congrFun (J_wordProduct C hc w) none) j
  simpa only [uniform, J, Matrix.mul_apply, Matrix.vecMul, dotProduct] using h

theorem start_J : start ᵥ* J = uniform := by
  funext j
  simp only [Matrix.vecMul, dotProduct, J, ← Finset.sum_mul, start_sum, one_mul, uniform]

theorem start_wordProduct (C : α → M7) (hc : ∀ a j, ∑ i, C a i j = 1)
    (w : List α) :
    start ᵥ* wordProduct C w = uniform + (1 / 21 : ℚ) • (SevenState.row ᵥ* wordProduct C w) := by
  rw [start, Matrix.add_vecMul, Matrix.smul_vecMul, uniform_wordProduct C hc w]

theorem acceptance_formula (C : α → M7)
    (hr : ∀ a i, ∑ j, C a i j = 1) (hc : ∀ a j, ∑ i, C a i j = 1)
    (w : List α) (j : State) :
    (start ᵥ* wordProduct (transition C) w) j =
      1 / 7 + (mixing C ^ w.length / 21) * (SevenState.row ᵥ* wordProduct C w) j := by
  rw [wordProduct_transition C hr hc w, Matrix.vecMul_add, Matrix.vecMul_smul,
    Matrix.vecMul_smul, start_wordProduct C hc w, start_J]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, uniform]
  ring

theorem start_mul_nonneg (M : M7) (hM : ∀ i j, 0 ≤ M i j) (j : State) :
    0 ≤ (start ᵥ* M) j := by
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (start_positive i).le (hM i j))

theorem start_mul_sum (M : M7) (hM : ∀ i, ∑ j, M i j = 1) :
    ∑ j, (start ᵥ* M) j = 1 := by
  simp only [Matrix.vecMul, dotProduct]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, hM, mul_one]
  exact start_sum

end MixedVolume.UniformMix
