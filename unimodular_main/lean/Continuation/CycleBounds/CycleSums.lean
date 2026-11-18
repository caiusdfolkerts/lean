module

public import Continuation.CycleBounds.CycleDimension
public import Continuation.CycleBounds.ThomsenCeil
public import Mathlib.Data.List.OfFn
public import Mathlib.Logic.Equiv.Fin.Rotate

@[expose] public section

/-! # Cyclic sums and the Thomsen wall bound -/

noncomputable section
open scoped BigOperators
namespace Unimodular.CycleBounds
attribute [local instance] Classical.propDecidable
variable {α : Type*}

theorem pathCost_ofFn_successors (h : α → ℝ) (n : ℕ) (c : Fin (n + 1) → α) :
    pathCost h (c 0) (List.ofFn (fun i : Fin n ↦ c i.succ)) =
      ∑ i : Fin n, step h (c i.castSucc) (c i.succ) := by
  induction n with
  | zero => simp [pathCost]
  | succ n ih =>
    simpa only [List.ofFn_succ, pathCost, Fin.sum_univ_succ, Fin.castSucc_zero,
      Fin.succ_zero_eq_one, Fin.castSucc_succ] using
      (congrArg (fun z ↦ step h (c 0) (c 1) + z) (ih (fun i ↦ c i.succ)))

theorem lastVertex_ofFn_successors (n : ℕ) (c : Fin (n + 1) → α) :
    lastVertex (c 0) (List.ofFn (fun i : Fin n ↦ c i.succ)) = c (Fin.last n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [List.ofFn_succ, lastVertex, Fin.succ_last] using ih (fun i ↦ c i.succ)

/-- The cyclic-word descent count is exactly the indexed sum around the cycle. -/
theorem cyclicCost_ofFn (h : α → ℝ) (n : ℕ) (c : Fin n → α) :
    cyclicCost h (List.ofFn c) = ∑ i : Fin n, step h (c i) (c (finRotate n i)) := by
  cases n with
  | zero => simp [cyclicCost]
  | succ n =>
    have hrotate (i : Fin n) : finRotate (n + 1) i.castSucc = i.succ :=
      finRotate_of_lt i.isLt
    rw [List.ofFn_succ, cyclicCost]
    simp only [pathCost_append, pathCost, Nat.add_zero,
      lastVertex_ofFn_successors, pathCost_ofFn_successors]
    rw [Fin.sum_univ_castSucc]
    simp only [hrotate, finRotate_last]

/-- Every normalized signed circuit wall with a noncrossing component word has
intersection bounded by the actual dimension supplied by its incidence directions. -/
theorem signed_wall_le_finrank {W : Type*} [AddCommGroup W] [Module ℝ W]
    [FiniteDimensional ℝ W] (n : ℕ) (hn : 0 < n)
    (labels : Fin n → α) (h : α → ℝ) (f : α → W)
    (x : Fin n → ℝ) (ε : Fin n → ℤ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hxlo : ∀ i, -1 < x i) (hxhi : ∀ i, x i < 1)
    (hp : ∀ i, (ε i : ℝ) * x i = h (labels i) - h (labels (finRotate n i)))
    (hnc : Noncrossing (List.ofFn labels))
    (hpath : (List.ofFn labels).IsChain (IncidenceTest f)) :
    (∑ i, ε i * ⌈x i⌉) ≤ (Module.finrank ℝ W : ℤ) := by
  have hsum := wall_sum_le_descents x ε hxlo hxhi hε
  have hword : List.ofFn labels ≠ [] := fun hh ↦ hn.ne' (List.ofFn_eq_nil_iff.mp hh)
  have hbound := cyclicCost_le_finrank_of_incidence_path f h (List.ofFn labels) hnc hpath hword
  have heq : (∑ i, if 0 < (ε i : ℝ) * x i then (1 : ℤ) else 0) =
      (cyclicCost h (List.ofFn labels) : ℤ) := by
    rw [cyclicCost_ofFn, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hp i]
    simp [step, sub_pos]
  rw [heq] at hsum
  exact hsum.trans (by exact_mod_cast hbound)

#print axioms signed_wall_le_finrank
end Unimodular.CycleBounds
