import CommAlg.Polymatroid.DilworthMarginal
import CommAlg.Polymatroid.DilworthSubmodular
import CommAlg.Polymatroid.RankInterpolation

/-! # The partition rank and homological-rank interpolation

This file completes Lemma 3.2 and the first part of Lemma 3.3 of
`Rank formulas for homological shifts of polymatroidal ideals`.
The homological interpretation itself is established in the Tor comparison
files; this module makes only its stated combinatorial claims.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The exact Dilworth partition minimum, as a proved polymatroid rank. -/
def dilworthRank (g : RankFunction V) (hg : g.Active) : RankFunction V where
  toFun := partitionRank g
  empty := partitionRank_empty g
  monotone := partitionRank_mono g
  submodular := partitionRank_submodular g hg

/-- The augmented partition rank `u_g(A)=|A|+D_g(A)`. -/
def augmentedRank (g : RankFunction V) (hg : g.Active) : RankFunction V where
  toFun := augmentedPartitionRank g
  empty := augmentedPartitionRank_empty g
  monotone := augmentedPartitionRank_mono g
  submodular A B := by
    have h := partitionRank_submodular g hg A B
    have hc := Finset.card_union_add_card_inter A B
    unfold augmentedPartitionRank
    omega

theorem augmentedRank_dominates (g : RankFunction V) (hg : g.Active) :
    (augmentedRank g hg).Dominates g :=
  fun A B hAB => augmentedPartitionRank_marginal g hg hAB

/-- The rank function in Theorem 1.2, before identifying its bases with Tor support. -/
def homologicalRank (g : RankFunction V) (hg : g.Active) (i : ℕ) : RankFunction V :=
  g.interpolate (augmentedRank g hg) (augmentedRank_dominates g hg) i

@[simp] theorem homologicalRank_empty (g : RankFunction V) (hg : g.Active) (i : ℕ) :
    homologicalRank g hg i ∅ = 0 := RankFunction.map_empty _

theorem homologicalRank_apply (g : RankFunction V) (hg : g.Active) (i : ℕ)
    {A : Finset V} (hA : A.Nonempty) :
    homologicalRank g hg i A = min (g A + i) (A.card + partitionRank g A) := by
  simp [homologicalRank, RankFunction.interpolate_apply, shiftRankValue, hA.ne_empty,
    augmentedRank, augmentedPartitionRank]

theorem sum_subsetSum_partition (a : Exponent V) {A : Finset V} (P : Finpartition A) :
    ∑ C ∈ P.parts, subsetSum a C = subsetSum a A := by
  unfold subsetSum
  calc
    (∑ C ∈ P.parts, ∑ i ∈ C, a i) = ∑ i ∈ P.parts.biUnion id, a i :=
      (Finset.sum_biUnion P.disjoint).symm
    _ = ∑ i ∈ A, a i := congrArg (fun S => ∑ i ∈ S, a i) P.biUnion_parts

/-- Additive exponents satisfy the nonempty-set bounds exactly when they
satisfy all bounds from the actual partition minimum. -/
theorem nonempty_bounds_iff_partition_bounds (g : RankFunction V) (a : Exponent V) :
    (∀ A, A.Nonempty → subsetSum a A ≤ g A - 1) ↔
      (∀ A, subsetSum a A ≤ partitionRank g A) := by
  constructor
  · intro h A
    apply le_partitionRank g A
    intro P
    rw [← sum_subsetSum_partition a P]
    exact Finset.sum_le_sum (fun C hC => h C (P.nonempty_of_mem_parts hC))
  · intro h A hA
    exact (h A).trans (partitionRank_le_single g hA)

end CommAlg.Polymatroid
