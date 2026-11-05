import CommAlg.Polymatroid.Dilworth
import CommAlg.Polymatroid.FiniteMinimum

/-! # Exact partition defects and the homological rank of twisted powers -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def partitionDefect (g : RankFunction V) {A : Finset V} (P : Finpartition A) : ℕ :=
  (∑ C ∈ P.parts, g C) - g A

def partitionSlack {A : Finset V} (P : Finpartition A) : ℕ := A.card - P.parts.card

theorem RankFunction.le_sum_partition (g : RankFunction V) {A : Finset V}
    (P : Finpartition A) : g A ≤ ∑ C ∈ P.parts, g C := by
  simpa [P.biUnion_parts] using g.biUnion_marginal ∅ P.parts

theorem partitionDefect_add_rank (g : RankFunction V) {A : Finset V}
    (P : Finpartition A) : partitionDefect g P + g A = ∑ C ∈ P.parts, g C :=
  Nat.sub_add_cancel (g.le_sum_partition P)

theorem partitionSlack_add_parts {A : Finset V} (P : Finpartition A) :
    partitionSlack P + P.parts.card = A.card := Nat.sub_add_cancel P.card_parts_le_card

theorem partitionDefect_add (g f : RankFunction V) {A : Finset V} (P : Finpartition A) :
    partitionDefect (g.add f) P = partitionDefect g P + partitionDefect f P := by
  have hg := partitionDefect_add_rank g P
  have hf := partitionDefect_add_rank f P
  have hgf := partitionDefect_add_rank (g.add f) P
  change partitionDefect (g.add f) P + (g A + f A) =
    ∑ C ∈ P.parts, (g C + f C) at hgf
  rw [Finset.sum_add_distrib] at hgf
  omega

theorem partitionDefect_scale (g : RankFunction V) (s : ℕ)
    {A : Finset V} (P : Finpartition A) :
    partitionDefect (RankFunction.scale s g) P = s * partitionDefect g P := by
  change (∑ C ∈ P.parts, s * g C) - s * g A = s * ((∑ C ∈ P.parts, g C) - g A)
  rw [← Finset.mul_sum, Nat.mul_sub_left_distrib]

theorem partitionCost_add_parts (g : RankFunction V) (hg : g.Active)
    {A : Finset V} (P : Finpartition A) :
    partitionCost g P + P.parts.card = ∑ C ∈ P.parts, g C := by
  have hp : ∀ C ∈ P.parts, (g C - 1) + 1 = g C := by
    intro C hC
    exact Nat.sub_add_cancel (hg C (P.nonempty_of_mem_parts hC))
  have hs := Finset.sum_congr rfl hp
  simpa [partitionCost, Finset.sum_add_distrib] using hs

theorem augmented_partition_cost (g : RankFunction V) (hg : g.Active)
    {A : Finset V} (P : Finpartition A) :
    A.card + partitionCost g P = g A + partitionDefect g P + partitionSlack P := by
  have hc := partitionCost_add_parts g hg P
  have hd := partitionDefect_add_rank g P
  have hs := partitionSlack_add_parts P
  omega

theorem augmentedPartitionRank_defect (g : RankFunction V) (hg : g.Active)
    (A : Finset V) :
    augmentedPartitionRank g A =
      g A + finiteMinimum (fun P : Finpartition A => partitionDefect g P + partitionSlack P) := by
  unfold augmentedPartitionRank
  change A.card + finiteMinimum (fun P : Finpartition A => partitionCost g P) = _
  rw [← finiteMinimum_add_const, ← finiteMinimum_add_const]
  congr 1
  funext P
  simpa only [Nat.add_assoc] using augmented_partition_cost g hg P

theorem homologicalRank_defect (g : RankFunction V) (hg : g.Active) (i : ℕ)
    {A : Finset V} (hA : A.Nonempty) :
    homologicalRank g hg i A = g A +
      min i (finiteMinimum (fun P : Finpartition A => partitionDefect g P + partitionSlack P)) := by
  rw [homologicalRank_apply g hg i hA]
  change min (g A + i) (augmentedPartitionRank g A) = _
  rw [augmentedPartitionRank_defect g hg A, Nat.add_min_add_left]

def twistedPowerRank (η ρ : RankFunction V) (s : ℕ) : RankFunction V :=
  η.add (RankFunction.scale s ρ)

theorem twistedPowerRank_apply (η ρ : RankFunction V) (s : ℕ) (A : Finset V) :
    twistedPowerRank η ρ s A = η A + s * ρ A := rfl

theorem twistedPower_defect (η ρ : RankFunction V) (s : ℕ)
    {A : Finset V} (P : Finpartition A) :
    partitionDefect (twistedPowerRank η ρ s) P =
      s * partitionDefect ρ P + partitionDefect η P := by
  rw [twistedPowerRank, partitionDefect_add, partitionDefect_scale, Nat.add_comm]

/-- Formula (4.1), with arbitrary fixed twist and arbitrary finite ground set. -/
theorem twistedPower_homologicalRank (η ρ : RankFunction V) (s i : ℕ)
    (hg : (twistedPowerRank η ρ s).Active) {A : Finset V} (hA : A.Nonempty) :
    homologicalRank (twistedPowerRank η ρ s) hg i A =
      twistedPowerRank η ρ s A + min i
        (finiteMinimum (fun P : Finpartition A =>
          s * partitionDefect ρ P + partitionDefect η P + partitionSlack P)) := by
  rw [homologicalRank_defect _ hg i hA]
  simp only [twistedPower_defect]

end CommAlg.Polymatroid
