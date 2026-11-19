module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Fin.Basic
public import Mathlib.SetTheory.Cardinal.Finite
import Lean.Elab.Tactic.Omega

/-!
# Subsets with a gap between successive entries

Deleting one unused position before each selected entry gives an explicit
bijection between the `s`-element independent subsets of an `n`-vertex path
and the `s`-element subsets of `Fin (n + 1 - s)`.

This is the finite combinatorial input for the attracting-cell argument.
Neither a cohomology dimension nor a geometric assertion enters its definition.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.SeparatedSubsets

/-- The actual independent subsets of the path on the ordered vertices `Fin n`. -/
abbrev Independent (n s : ℕ) :=
  {S : Finset (Fin n) // S.card = s ∧
    ∀ i ∈ S, ∀ j ∈ S, i < j → i.val + 2 ≤ j.val}

/-- Increasing parametrizations of independent subsets. -/
abbrev SpacedEmbedding (n s : ℕ) :=
  {e : Fin s ↪o Fin n // ∀ i j, i < j → (e i).val + 2 ≤ (e j).val}

/-- An order embedding is uniquely determined by its finite image. -/
def orderEmbeddingEquivSubsets (n s : ℕ) :
    (Fin s ↪o Fin n) ≃ {S : Finset (Fin n) // S.card = s} where
  toFun e := ⟨Finset.univ.map e.toEmbedding, by simp⟩
  invFun S := S.val.orderEmbOfFin S.property
  left_inv e := by
    symm
    apply Finset.orderEmbOfFin_unique'
    intro i
    exact Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩
  right_inv S := by
    apply Subtype.ext
    exact Finset.map_orderEmbOfFin_univ S.val S.property

/-- Enumerating a finite set identifies its intrinsic separation condition
with the corresponding condition on its increasing parametrization. -/
def independentEquivSpaced (n s : ℕ) : Independent n s ≃ SpacedEmbedding n s where
  toFun S := ⟨S.val.orderEmbOfFin S.property.1, by
    intro i j hij
    apply S.property.2
    · exact Finset.orderEmbOfFin_mem _ _ i
    · exact Finset.orderEmbOfFin_mem _ _ j
    · exact (S.val.orderEmbOfFin S.property.1).strictMono hij⟩
  invFun e := ⟨Finset.univ.map e.val.toEmbedding, by
    constructor
    · simp
    · intro i hi j hj hij
      obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hi
      obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp hj
      exact e.property a b (e.val.lt_iff_lt.mp hij)⟩
  left_inv S := by
    apply Subtype.ext
    exact Finset.map_orderEmbOfFin_univ S.val S.property.1
  right_inv e := by
    apply Subtype.ext
    symm
    apply Finset.orderEmbOfFin_unique'
    intro i
    exact Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩

/-- Successive gaps of size at least two accumulate across an arbitrary interval. -/
theorem spaced_distance {n s : ℕ} (e : SpacedEmbedding n s)
    (i j : Fin s) (hij : i ≤ j) :
    (e.val i).val + 2 * (j.val - i.val) ≤ (e.val j).val := by
  have H : ∀ b, ∀ hb : b < s, i.val ≤ b →
      (e.val i).val + 2 * (b - i.val) ≤ (e.val ⟨b, hb⟩).val := by
    intro b
    induction b with
    | zero =>
        intro hb hi
        have hval : i.val = 0 := by omega
        have h : i = ⟨0, hb⟩ := Fin.ext hval
        subst i
        simp
    | succ b ih =>
        intro hb hi
        by_cases he : i.val = b + 1
        · have h : i = ⟨b + 1, hb⟩ := Fin.ext he
          subst i
          simp
        · have hb' : b < s := by omega
          have hprev := ih hb' (by omega)
          have hstep := e.property ⟨b, hb'⟩ ⟨b + 1, hb⟩ (by
            change b < b + 1
            omega)
          omega
  exact H j.val j.isLt hij

theorem spaced_lower_bound {n s : ℕ} (e : SpacedEmbedding n s) (i : Fin s) :
    2 * i.val ≤ (e.val i).val := by
  have hs : 0 < s := by have := i.isLt; omega
  have h := spaced_distance e ⟨0, hs⟩ i (by change 0 ≤ i.val; omega)
  dsimp only at h
  omega

theorem compressed_bound {n s : ℕ} (e : SpacedEmbedding n s) (i : Fin s) :
    (e.val i).val - i.val < n + 1 - s := by
  have hs : 0 < s := by have := i.isLt; omega
  let j : Fin s := ⟨s - 1, by omega⟩
  have h := spaced_distance e i j (by change i.val ≤ s - 1; have := i.isLt; omega)
  have hn := (e.val j).isLt
  have hi := i.isLt
  have hl := spaced_lower_bound e i
  dsimp only [j] at h hn
  omega

theorem compressed_strictMono {n s : ℕ} (e : SpacedEmbedding n s) :
    StrictMono (fun i : Fin s => (e.val i).val - i.val) := by
  intro i j hij
  have h := spaced_distance e i j (le_of_lt hij)
  have hi := spaced_lower_bound e i
  have hj := spaced_lower_bound e j
  change i.val < j.val at hij
  change (e.val i).val - i.val < (e.val j).val - j.val
  omega

/-- Remove the `i` unused positions forced before the `i`-th selected vertex. -/
def compress {n s : ℕ} (e : SpacedEmbedding n s) : Fin s ↪o Fin (n + 1 - s) :=
  OrderEmbedding.ofStrictMono
    (fun i => ⟨(e.val i).val - i.val, compressed_bound e i⟩)
    (compressed_strictMono e)

/-- Reinsert those positions. This map is valid also for the empty subset. -/
def expand {n s : ℕ} (hs : s ≤ n + 1)
    (e : Fin s ↪o Fin (n + 1 - s)) : SpacedEmbedding n s := by
  let f : Fin s → Fin n := fun i => ⟨(e i).val + i.val, by
    have hi := i.isLt
    have he := (e i).isLt
    omega⟩
  have hf : StrictMono f := by
    intro i j hij
    have he := e.strictMono hij
    change (e i).val < (e j).val at he
    change i.val < j.val at hij
    change (e i).val + i.val < (e j).val + j.val
    omega
  refine ⟨OrderEmbedding.ofStrictMono f hf, ?_⟩
  intro i j hij
  have he := e.strictMono hij
  change (e i).val < (e j).val at he
  change i.val < j.val at hij
  change (e i).val + i.val + 2 ≤ (e j).val + j.val
  omega

/-- The gap-deletion bijection, retaining every size in the stated range. -/
def gapEquiv (n s : ℕ) (hs : s ≤ n + 1) :
    SpacedEmbedding n s ≃ (Fin s ↪o Fin (n + 1 - s)) where
  toFun := compress
  invFun := expand hs
  left_inv e := by
    apply Subtype.ext
    apply RelEmbedding.ext
    intro i
    apply Fin.ext
    change (e.val i).val - i.val + i.val = (e.val i).val
    have h := spaced_lower_bound e i
    omega
  right_inv e := by
    apply RelEmbedding.ext
    intro i
    apply Fin.ext
    change (e i).val + i.val - i.val = (e i).val
    omega

/-- An explicit bijection with ordinary subsets of the shortened interval. -/
def independentEquivSubsets (n s : ℕ) (hs : s ≤ n + 1) :
    Independent n s ≃ {S : Finset (Fin (n + 1 - s)) // S.card = s} :=
  (independentEquivSpaced n s).trans
    ((gapEquiv n s hs).trans (orderEmbeddingEquivSubsets (n + 1 - s) s))

/-- The number of actual independent `s`-subsets of a finite path. -/
theorem card_independent (n s : ℕ) (hs : s ≤ n + 1) :
    Nat.card (Independent n s) = (n + 1 - s).choose s := by
  rw [Nat.card_congr (independentEquivSubsets n s hs), Nat.card_eq_fintype_card]
  simp

end PaperVerification.SeparatedSubsets
