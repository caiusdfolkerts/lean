module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# Finite optimization tools

Small perturbations preserve any prescribed finite list of strict
linear inequalities.  A finite graph in which every nonminimum vertex
has a strictly descending neighbour is connected.
-/

noncomputable section
namespace Papers.FiniteGraphOptimization

open Finset
open scoped Classical

theorem exists_small_positive_perturbation {I : Type*}
    (s : Finset I) (a b : I → ℝ) (ha : ∀ i ∈ s, 0 < a i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t, 0 < t → t ≤ ε →
      ∀ i ∈ s, 0 < a i + t * b i := by
  classical
  revert ha
  induction s using Finset.induction_on with
  | empty =>
      intro ha
      refine ⟨1, zero_lt_one, ?_⟩
      intro t ht htle i hi
      simp only [Finset.notMem_empty] at hi
  | @insert i s hi ih =>
      intro ha
      have hai : 0 < a i := ha i (Finset.mem_insert_self i s)
      obtain ⟨ε, hε, hbound⟩ := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
      let δ := a i / (|b i| + 1)
      have hden : 0 < |b i| + 1 := by positivity
      have hδ : 0 < δ := div_pos hai hden
      refine ⟨min ε δ, lt_min hε hδ, ?_⟩
      intro t ht htle j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · have htδ : t ≤ δ := htle.trans (min_le_right ε δ)
        have hmul : t * (|b j| + 1) ≤ a j :=
          (le_div_iff₀ hden).mp htδ
        have hab := mul_le_mul_of_nonneg_left (neg_abs_le (b j)) ht.le
        nlinarith
      · exact hbound t ht (htle.trans (min_le_left ε δ)) j hj

section Graph

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

def descendingRank (φ : V → ℝ) (v : V) : ℕ :=
  (Finset.univ.filter fun w => φ w < φ v).card

theorem descendingRank_lt {φ : V → ℝ} {v w : V} (h : φ v < φ w) :
    descendingRank φ v < descendingRank φ w := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro x hx
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ x, lt_trans (Finset.mem_filter.mp hx).2 h⟩
  · intro heq
    have hv : v ∈ Finset.univ.filter (fun x => φ x < φ w) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ v, h⟩
    rw [← heq] at hv
    exact lt_irrefl _ (Finset.mem_filter.mp hv).2

theorem connected_of_strict_descent (φ : V → ℝ) (m : V)
    (hdescent : ∀ v, v ≠ m → ∃ w, G.Adj v w ∧ φ w < φ v) :
    G.Connected := by
  have hreach : ∀ k : ℕ, ∀ v : V, descendingRank φ v = k →
      G.Reachable v m := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro v hvk
        by_cases hvm : v = m
        · subst v
          exact SimpleGraph.Reachable.rfl
        · obtain ⟨w, hvw, hwv⟩ := hdescent v hvm
          have hrank : descendingRank φ w < k := by
            rw [← hvk]
            exact descendingRank_lt hwv
          exact hvw.reachable.trans (ih _ hrank w rfl)
  letI : Nonempty V := ⟨m⟩
  exact { preconnected := fun v w =>
    (hreach _ v rfl).trans (hreach _ w rfl).symm }

end Graph
end Papers.FiniteGraphOptimization
