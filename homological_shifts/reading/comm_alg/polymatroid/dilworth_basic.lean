import CommAlg.Polymatroid.RankFunction
import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Finset.Lattice.Fold

/-! # The actual partition minimum in the homological rank formula -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def partitionCost (g : Finset V → ℕ) {A : Finset V} (P : Finpartition A) : ℕ :=
  ∑ B ∈ P.parts, (g B - 1)

/-- Minimum over all partitions of `A` into nonempty blocks. -/
def partitionRank (g : Finset V → ℕ) (A : Finset V) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (fun P : Finpartition A => partitionCost g P)

theorem partitionRank_le (g : Finset V → ℕ) {A : Finset V} (P : Finpartition A) :
    partitionRank g A ≤ partitionCost g P :=
  Finset.inf'_le _ (Finset.mem_univ P)

theorem le_partitionRank (g : Finset V → ℕ) (A : Finset V) (n : ℕ)
    (h : ∀ P : Finpartition A, n ≤ partitionCost g P) : n ≤ partitionRank g A :=
  Finset.le_inf' _ _ (fun P _ => h P)

theorem partitionRank_attained (g : Finset V → ℕ) (A : Finset V) :
    ∃ P : Finpartition A, partitionCost g P = partitionRank g A := by
  obtain ⟨P, _, hP⟩ := (Finset.inf'_le_iff Finset.univ_nonempty).mp
    (le_rfl : partitionRank g A ≤ partitionRank g A)
  exact ⟨P, le_antisymm hP (partitionRank_le g P)⟩

@[simp] theorem partitionRank_empty (g : Finset V → ℕ) : partitionRank g ∅ = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa [partitionCost] using partitionRank_le g (Finpartition.empty (Finset V))

theorem partitionRank_le_single (g : Finset V → ℕ) {A : Finset V}
    (hA : A.Nonempty) : partitionRank g A ≤ g A - 1 := by
  simpa [partitionCost] using partitionRank_le g (Finpartition.indiscrete hA.ne_empty)

def augmentedPartitionRank (g : Finset V → ℕ) (A : Finset V) : ℕ :=
  A.card + partitionRank g A

@[simp] theorem augmentedPartitionRank_empty (g : Finset V → ℕ) :
    augmentedPartitionRank g ∅ = 0 := by simp [augmentedPartitionRank]

end CommAlg.Polymatroid
