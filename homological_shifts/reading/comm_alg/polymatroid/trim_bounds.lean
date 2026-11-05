import CommAlg.Polymatroid.Dilworth

/-! # Removing the first copy of each supported variable

These are the exact exponent inequalities (3.3)--(3.6), including arbitrary
zero coordinates.  The support is the actual support of the exponent vector.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def supportPred (a : Exponent V) : Exponent V :=
  a.mapRange (fun n => n - 1) (by simp)

@[simp] theorem supportPred_apply (a : Exponent V) (j : V) :
    supportPred a j = a j - 1 := rfl

theorem supportPred_add_support (a : Exponent V) (j : V) :
    supportPred a j + (if j ∈ a.support then 1 else 0) = a j := by
  simp only [supportPred_apply, Finsupp.mem_support_iff]
  split_ifs <;> omega

theorem subsetSum_supportPred (a : Exponent V) (A : Finset V) :
    subsetSum (supportPred a) A + (A ∩ a.support).card = subsetSum a A := by
  have h := Finset.sum_congr (s₁ := A) (s₂ := A) rfl
    (fun j _ => supportPred_add_support a j)
  simpa only [Finset.sum_add_distrib, Finset.sum_boole, Finset.filter_mem_eq_inter,
    Nat.cast_id, subsetSum] using h

theorem subsetSum_support_inter (a : Exponent V) (A : Finset V) :
    subsetSum a (A ∩ a.support) = subsetSum a A := by
  apply Finset.sum_subset inter_subset_left
  intro j hjA hj
  have hn : j ∉ a.support := fun h => hj (mem_inter.mpr ⟨hjA, h⟩)
  exact Finsupp.notMem_support_iff.mp hn

theorem subsetSum_supportPred_inter (a : Exponent V) (A : Finset V) :
    subsetSum (supportPred a) (A ∩ a.support) = subsetSum (supportPred a) A := by
  apply Finset.sum_subset inter_subset_left
  intro j hjA hj
  have hn : j ∉ a.support := fun h => hj (mem_inter.mpr ⟨hjA, h⟩)
  simp [Finsupp.notMem_support_iff.mp hn]

theorem supportPred_bounds_iff_augmented (g : RankFunction V) (a : Exponent V) :
    (∀ A, subsetSum (supportPred a) A ≤ partitionRank g A) ↔
      (∀ A, subsetSum a A ≤ augmentedPartitionRank g A) := by
  constructor
  · intro h A
    have heq := subsetSum_supportPred a A
    have hc := Finset.card_le_card (inter_subset_left : A ∩ a.support ⊆ A)
    have hb := h A
    unfold augmentedPartitionRank
    omega
  · intro h A
    have hb := h (A ∩ a.support)
    have heq := subsetSum_supportPred a (A ∩ a.support)
    rw [Finset.inter_eq_left.mpr inter_subset_right, subsetSum_supportPred_inter] at heq
    have hm := partitionRank_mono g (inter_subset_left : A ∩ a.support ⊆ A)
    unfold augmentedPartitionRank at hb
    omega

/-- Exact equivalence of (3.3) and (3.6) in the paper. -/
theorem supportPred_nonempty_bounds_iff_augmented (g : RankFunction V) (a : Exponent V) :
    (∀ A, A.Nonempty → subsetSum (supportPred a) A ≤ g A - 1) ↔
      (∀ A, subsetSum a A ≤ augmentedPartitionRank g A) :=
  (nonempty_bounds_iff_partition_bounds g (supportPred a)).trans
    (supportPred_bounds_iff_augmented g a)

end CommAlg.Polymatroid
