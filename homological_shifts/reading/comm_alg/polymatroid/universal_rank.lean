import CommAlg.Polymatroid.UniformRank
import CommAlg.Polymatroid.RankInterpolation

/-! # Homological ranks with all inactive coordinates retained

For every integral polymatroid rank `g`, the rank `g+|·|` is active. Its
Dilworth truncation is exactly

  u_g(A) = min over partitions P of A of Σ(C in P) (g(C)+|C|−1).

This is the same as `|A|+D_g(A)` with integer block costs, including zero
coordinates. On active ground sets it is proved equal to the earlier formula.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def cardinalLift (g : RankFunction V) : RankFunction V := g.add (cardinalRank V)

@[simp] theorem cardinalLift_apply (g : RankFunction V) (A : Finset V) :
    cardinalLift g A = g A + A.card := rfl

theorem cardinalLift_active (g : RankFunction V) : (cardinalLift g).Active := by
  intro A hA
  have hc := card_pos.mpr hA
  change 1 ≤ g A + A.card
  omega

def universalAugmentedRank (g : RankFunction V) : RankFunction V :=
  dilworthRank (cardinalLift g) (cardinalLift_active g)

@[simp] theorem universalAugmentedRank_apply (g : RankFunction V) (A : Finset V) :
    universalAugmentedRank g A = partitionRank (cardinalLift g) A := rfl

theorem universalAugmentedRank_dominates (g : RankFunction V) :
    (universalAugmentedRank g).Dominates g := by
  intro A B hAB
  have h := augmentedPartitionRank_marginal (cardinalLift g) (cardinalLift_active g) hAB
  simp only [cardinalLift_apply, augmentedPartitionRank] at h
  change g B + partitionRank (cardinalLift g) A ≤ partitionRank (cardinalLift g) B + g A
  omega

def universalHomologicalRank (g : RankFunction V) (i : ℕ) : RankFunction V :=
  g.interpolate (universalAugmentedRank g) (universalAugmentedRank_dominates g) i

@[simp] theorem universalHomologicalRank_empty (g : RankFunction V) (i : ℕ) :
    universalHomologicalRank g i ∅ = 0 := RankFunction.map_empty _

theorem universalHomologicalRank_apply (g : RankFunction V) (i : ℕ)
    {A : Finset V} (hA : A.Nonempty) :
    universalHomologicalRank g i A = min (g A + i) (universalAugmentedRank g A) := by
  simp [universalHomologicalRank, RankFunction.interpolate_apply, shiftRankValue, hA.ne_empty]

theorem universalHomologicalRank_le_add (g : RankFunction V) (i : ℕ) (A : Finset V) :
    universalHomologicalRank g i A ≤ g A + i :=
  shiftRankValue_le_add g (universalAugmentedRank g) i A

/-- The cost identity also justifies the integer-partition interpretation
when some original rank values vanish. -/
theorem cardinalLift_cost_add_parts (g : RankFunction V) {A : Finset V}
    (P : Finpartition A) :
    partitionCost (cardinalLift g) P + P.parts.card = A.card + ∑ C ∈ P.parts, g C := by
  have h := partitionCost_add_parts (cardinalLift g) (cardinalLift_active g) P
  simpa only [cardinalLift_apply, Finset.sum_add_distrib, P.sum_card_parts, Nat.add_comm] using h

theorem cardinalLift_cost_of_active (g : RankFunction V) (hg : g.Active)
    {A : Finset V} (P : Finpartition A) :
    partitionCost (cardinalLift g) P = A.card + partitionCost g P := by
  have h1 := cardinalLift_cost_add_parts g P
  have h2 := partitionCost_add_parts g hg P
  omega

/-- The universal rank is exactly the original active-ground-set formula. -/
theorem universalAugmentedRank_eq_active (g : RankFunction V) (hg : g.Active)
    (A : Finset V) : universalAugmentedRank g A = augmentedPartitionRank g A := by
  change finiteMinimum (fun P : Finpartition A => partitionCost (cardinalLift g) P) =
    A.card + finiteMinimum (fun P : Finpartition A => partitionCost g P)
  rw [← finiteMinimum_add_const]
  congr 1
  funext P
  exact cardinalLift_cost_of_active g hg P

theorem universalHomologicalRank_eq_active (g : RankFunction V) (hg : g.Active)
    (i : ℕ) (A : Finset V) : universalHomologicalRank g i A = homologicalRank g hg i A := by
  by_cases hA : A = ∅
  · simp [hA]
  have hne := Finset.nonempty_iff_ne_empty.mpr hA
  rw [universalHomologicalRank_apply g i hne, homologicalRank_apply g hg i hne,
    universalAugmentedRank_eq_active g hg A]
  rfl

/-- Every simultaneous deletion inequality is equivalent to the upper
inequalities of the universal partition rank, with no activity assumption. -/
theorem universal_bounds_iff (g : RankFunction V) (a : Exponent V) :
    (∀ A, A.Nonempty → subsetSum a A ≤ g A + A.card - 1) ↔
      (∀ A, subsetSum a A ≤ universalAugmentedRank g A) := by
  exact nonempty_bounds_iff_partition_bounds (cardinalLift g) a

theorem universalAugmentedRank_le_cost (g : RankFunction V) {A : Finset V}
    (P : Finpartition A) : universalAugmentedRank g A ≤ partitionCost (cardinalLift g) P :=
  partitionRank_le _ P

theorem universalAugmentedRank_attained (g : RankFunction V) (A : Finset V) :
    ∃ P : Finpartition A, partitionCost (cardinalLift g) P = universalAugmentedRank g A :=
  partitionRank_attained _ A

end CommAlg.Polymatroid
