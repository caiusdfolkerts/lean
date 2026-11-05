import CommAlg.Polymatroid.DilworthBasic

/-!
# Monotonicity and marginal domination of the partition rank

The partition minimum is restricted to a smaller set by intersecting every
block with that set. The augmented block cost absorbs the unit lost when an
intersection is empty. Submodularity then bounds the total marginal increase
by the sum of the block marginal increases.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Restriction of an optimal partition proves monotonicity of the actual
partition minimum. Positivity on nonempty sets is not needed here. -/
theorem partitionRank_mono (g : RankFunction V) : Monotone (partitionRank g) := by
  intro A B hAB
  obtain ⟨P, hP⟩ := partitionRank_attained g B
  calc
    partitionRank g A ≤ partitionCost g (P.restrict hAB) := partitionRank_le g _
    _ = ∑ C ∈ P.parts, (g (C ∩ A) - 1) := by
      exact P.sum_restrict hAB (fun C => g C - 1) (by simp)
    _ ≤ partitionCost g P := by
      apply Finset.sum_le_sum
      intro C hC
      exact Nat.sub_le_sub_right (g.monotone Finset.inter_subset_left) 1
    _ = partitionRank g B := hP

theorem augmentedPartitionRank_mono (g : RankFunction V) :
    Monotone (augmentedPartitionRank g) := by
  intro A B hAB
  exact Nat.add_le_add (Finset.card_le_card hAB) (partitionRank_mono g hAB)

omit [Fintype V] in
/-- Adding a finite family of sets successively bounds the total rank increase
by the sum of their increases over their intersections with the initial set.
No disjointness assumption on the family is necessary. -/
theorem RankFunction.biUnion_marginal (g : RankFunction V) (A : Finset V)
    (S : Finset (Finset V)) :
    g (A ∪ S.biUnion id) + ∑ C ∈ S, g (C ∩ A) ≤ g A + ∑ C ∈ S, g C := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert C S hCS ih =>
    have hs := g.submodular (A ∪ S.biUnion id) C
    have hm : g (C ∩ A) ≤ g ((A ∪ S.biUnion id) ∩ C) := by
      apply g.monotone
      intro x hx
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mp hx).2),
          (Finset.mem_inter.mp hx).1⟩
    have hu : A ∪ (C ∪ S.biUnion id) = (A ∪ S.biUnion id) ∪ C := by
      ext x
      simp only [Finset.mem_union]
      tauto
    simp only [Finset.biUnion_insert, id_eq, Finset.sum_insert hCS]
    rw [hu]
    omega

omit [Fintype V] in
theorem RankFunction.partition_marginal (g : RankFunction V)
    {A B : Finset V} (hAB : A ⊆ B) (P : Finpartition B) :
    g B + ∑ C ∈ P.parts, g (C ∩ A) ≤ g A + ∑ C ∈ P.parts, g C := by
  simpa only [P.biUnion_parts, Finset.union_eq_right.mpr hAB] using
    g.biUnion_marginal A P.parts

omit [Fintype V] in
/-- The cardinality part of an augmented block cost compensates for its
missing unit when restriction removes a whole block. -/
theorem augmentedBlockCost_marginal (g : RankFunction V) (hg : g.Active)
    (A C : Finset V) (hC : C.Nonempty) :
    g C + ((C ∩ A).card + (g (C ∩ A) - 1)) ≤
      (C.card + (g C - 1)) + g (C ∩ A) := by
  have hCard : (C ∩ A).card ≤ C.card := Finset.card_le_card Finset.inter_subset_left
  have hGC := hg C hC
  by_cases hCA : (C ∩ A).Nonempty
  · have hGCA := hg (C ∩ A) hCA
    omega
  · have he : C ∩ A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hCA
    have hc := Finset.card_pos.mpr hC
    simp only [he, Finset.card_empty, RankFunction.map_empty, Nat.zero_sub,
      Nat.add_zero]
    omega

/-- Lemma 3.2's complete marginal inequality in additive form, avoiding any
ambiguity from truncated natural subtraction. -/
theorem augmentedPartitionRank_marginal (g : RankFunction V) (hg : g.Active)
    {A B : Finset V} (hAB : A ⊆ B) :
    g B + augmentedPartitionRank g A ≤ augmentedPartitionRank g B + g A := by
  obtain ⟨P, hP⟩ := partitionRank_attained g B
  have hRestricted : partitionRank g A ≤ ∑ C ∈ P.parts, (g (C ∩ A) - 1) := by
    calc
      partitionRank g A ≤ partitionCost g (P.restrict hAB) := partitionRank_le g _
      _ = _ := P.sum_restrict hAB (fun C => g C - 1) (by simp)
  have hCards : ∑ C ∈ P.parts, (C ∩ A).card = A.card := by
    exact (P.sum_restrict hAB (fun C => C.card) (by simp)).symm.trans
      (P.restrict hAB).sum_card_parts
  have hLower : augmentedPartitionRank g A ≤
      ∑ C ∈ P.parts, ((C ∩ A).card + (g (C ∩ A) - 1)) := by
    rw [Finset.sum_add_distrib, hCards]
    exact Nat.add_le_add_left hRestricted A.card
  have hUpper : (∑ C ∈ P.parts, (C.card + (g C - 1))) =
      augmentedPartitionRank g B := by
    rw [Finset.sum_add_distrib, P.sum_card_parts]
    exact congrArg (fun n => B.card + n) hP
  have hBlocks : (∑ C ∈ P.parts, g C) +
      (∑ C ∈ P.parts, ((C ∩ A).card + (g (C ∩ A) - 1))) ≤
      (∑ C ∈ P.parts, (C.card + (g C - 1))) +
      (∑ C ∈ P.parts, g (C ∩ A)) := by
    simpa only [Finset.sum_add_distrib] using
      (Finset.sum_le_sum (s := P.parts) (fun C hC =>
        augmentedBlockCost_marginal g hg A C (P.nonempty_of_mem_parts hC)))
  have hRank := g.partition_marginal hAB P
  rw [hUpper] at hBlocks
  omega

end CommAlg.Polymatroid
