import CommAlg.Polymatroid.DilworthBasic

/-! # Submodularity of the partition minimum

We give a finite one-block uncrossing argument.  Intersecting a single new
block with the blocks of a partition gives a partition of the intersection;
merging those that meet it gives a partition of the union.  Induction over
the second partition yields the full submodular inequality.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem RankFunction.intersecting_cost_submodular (g : RankFunction V)
    (hg : g.Active) {A B : Finset V} (h : (A ∩ B).Nonempty) :
    (g (A ∪ B) - 1) + (g (A ∩ B) - 1) ≤ (g A - 1) + (g B - 1) := by
  have hI := hg (A ∩ B) h
  have hA := hg A (h.mono inter_subset_left)
  have hB := hg B (h.mono inter_subset_right)
  have hU := hg (A ∪ B) (h.mono (inter_subset_left.trans subset_union_left))
  have hs := g.submodular A B
  omega

theorem partitionRank_le_cover (g : RankFunction V) (S : Finset (Finset V))
    (hd : (S : Set (Finset V)).PairwiseDisjoint id) :
    partitionRank g (S.biUnion id) ≤ ∑ C ∈ S, (g C - 1) := by
  let P : Finpartition (S.biUnion id) :=
    Finpartition.ofErase S hd.supIndep (Finset.sup_eq_biUnion S id)
  have h := partitionRank_le g P
  have hs : partitionCost g P = ∑ C ∈ S, (g C - 1) := by
    change ∑ C ∈ S.erase ∅, (g C - 1) = ∑ C ∈ S, (g C - 1)
    exact Finset.sum_erase S (by simp)
  rwa [hs] at h

theorem partitionRank_disjoint_subadd (g : RankFunction V)
    {A B : Finset V} (hAB : Disjoint A B) :
    partitionRank g (A ∪ B) ≤ partitionRank g A + partitionRank g B := by
  obtain ⟨P, hP⟩ := partitionRank_attained g A
  obtain ⟨Q, hQ⟩ := partitionRank_attained g B
  have hcross : ∀ C ∈ P.parts, ∀ D ∈ Q.parts, Disjoint C D := by
    intro C hC D hD
    exact hAB.mono (P.subset hC) (Q.subset hD)
  have hd : ((P.parts ∪ Q.parts : Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint id := by
    intro C hC D hD hne
    rcases mem_union.mp hC with hC | hC <;> rcases mem_union.mp hD with hD | hD
    · exact P.disjoint hC hD hne
    · exact hcross C hC D hD
    · exact (hcross D hD C hC).symm
    · exact Q.disjoint hC hD hne
  have hpq : Disjoint P.parts Q.parts := by
    apply Finset.disjoint_left.mpr
    intro C hC hD
    exact P.ne_empty hC (disjoint_self.mp (hcross C hC C hD))
  have h := partitionRank_le_cover g (P.parts ∪ Q.parts) hd
  rw [Finset.union_biUnion, P.biUnion_parts, Q.biUnion_parts, Finset.sum_union hpq] at h
  change partitionRank g (A ∪ B) ≤ partitionCost g P + partitionCost g Q at h
  simpa only [hP, hQ] using h

theorem RankFunction.merge_cost (g : RankFunction V) (hg : g.Active)
    (C : Finset V) (R : Finset (Finset V))
    (hd : (R : Set (Finset V)).PairwiseDisjoint id)
    (hm : ∀ S ∈ R, (S ∩ C).Nonempty) :
    (g (C ∪ R.biUnion id) - 1) + ∑ S ∈ R, (g (S ∩ C) - 1) ≤
      (g C - 1) + ∑ S ∈ R, (g S - 1) := by
  induction R using Finset.induction_on with
  | empty => simp
  | @insert S R hSR ih =>
    have hdR : (R : Set (Finset V)).PairwiseDisjoint id := by
      intro X hX Y hY hne
      exact hd (mem_insert_of_mem hX) (mem_insert_of_mem hY) hne
    have hmR : ∀ X ∈ R, (X ∩ C).Nonempty :=
      fun X hX => hm X (mem_insert_of_mem hX)
    have ih' := ih hdR hmR
    have hdis : Disjoint S (R.biUnion id) := by
      rw [Finset.disjoint_biUnion_right]
      intro X hX
      exact hd (mem_insert_self _ _) (mem_insert_of_mem hX) (fun heq => hSR (heq ▸ hX))
    have hi : S ∩ (C ∪ R.biUnion id) = S ∩ C := by
      ext x
      have hx : x ∈ S → x ∉ R.biUnion id := fun hx => Finset.disjoint_left.mp hdis hx
      simp only [mem_inter, mem_union]
      tauto
    have hsub := g.intersecting_cost_submodular hg
      (A := S) (B := C ∪ R.biUnion id) (by rw [hi]; exact hm S (mem_insert_self _ _))
    rw [hi] at hsub
    have hu : C ∪ (insert S R).biUnion id = S ∪ (C ∪ R.biUnion id) := by
      ext x
      simp only [mem_union, mem_biUnion, mem_insert, id_eq]
      aesop
    rw [hu, Finset.sum_insert hSR, Finset.sum_insert hSR]
    omega

theorem partitionRank_single_submodular (g : RankFunction V) (hg : g.Active)
    (A C : Finset V) :
    partitionRank g (A ∪ C) + partitionRank g (A ∩ C) ≤
      partitionRank g A + (g C - 1) := by
  by_cases hC : C = ∅
  · simp [hC]
  have hCne : C.Nonempty := Finset.nonempty_iff_ne_empty.mpr hC
  obtain ⟨P, hP⟩ := partitionRank_attained g A
  let R := P.parts.filter (fun S => (S ∩ C).Nonempty)
  let T := P.parts.filter (fun S => ¬ (S ∩ C).Nonempty)
  let U := C ∪ R.biUnion id
  have hRsub : R ⊆ P.parts := Finset.filter_subset _ _
  have hTsub : T ⊆ P.parts := Finset.filter_subset _ _
  have hdR : (R : Set (Finset V)).PairwiseDisjoint id := by
    intro S hS D hD hne
    exact P.disjoint (hRsub hS) (hRsub hD) hne
  have hmeet : ∀ S ∈ R, (S ∩ C).Nonempty := fun S hS => (mem_filter.mp hS).2
  have hmerge := g.merge_cost hg C R hdR hmeet
  have hTU : ∀ S ∈ T, Disjoint S U := by
    intro S hS
    have hSC : Disjoint S C := by
      exact Finset.disjoint_iff_inter_eq_empty.mpr
        (Finset.not_nonempty_iff_eq_empty.mp (mem_filter.mp hS).2)
    apply Finset.disjoint_union_right.mpr
    refine ⟨hSC, ?_⟩
    rw [Finset.disjoint_biUnion_right]
    intro D hD
    apply P.disjoint (hTsub hS) (hRsub hD)
    intro heq
    exact (mem_filter.mp hS).2 (heq ▸ hmeet D hD)
  have hUne : U.Nonempty := hCne.mono subset_union_left
  have hUT : U ∉ T := by
    intro h
    exact hUne.ne_empty (disjoint_self.mp (hTU U h))
  have hdU : ((insert U T : Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint id := by
    intro S hS D hD hne
    rcases mem_insert.mp hS with rfl | hS <;> rcases mem_insert.mp hD with rfl | hD
    · exact (hne rfl).elim
    · exact (hTU D hD).symm
    · exact hTU S hS
    · exact P.disjoint (hTsub hS) (hTsub hD) hne
  have hcover : (insert U T).biUnion id = A ∪ C := by
    ext x
    constructor
    · intro hx
      obtain ⟨S, hS, hxS⟩ := mem_biUnion.mp hx
      rcases mem_insert.mp hS with rfl | hS
      · rcases mem_union.mp hxS with hxC | hxR
        · exact mem_union_right _ hxC
        · obtain ⟨D, hD, hxD⟩ := mem_biUnion.mp hxR
          exact mem_union_left _ (P.subset (hRsub hD) hxD)
      · exact mem_union_left _ (P.subset (hTsub hS) hxS)
    · intro hx
      rcases mem_union.mp hx with hxA | hxC
      · obtain ⟨S, hS, hxS⟩ := P.exists_mem hxA
        by_cases hm : (S ∩ C).Nonempty
        · exact mem_biUnion.mpr ⟨U, mem_insert_self _ _,
            mem_union_right _ (mem_biUnion.mpr ⟨S, mem_filter.mpr ⟨hS, hm⟩, hxS⟩)⟩
        · exact mem_biUnion.mpr ⟨S, mem_insert_of_mem (mem_filter.mpr ⟨hS, hm⟩), hxS⟩
      · exact mem_biUnion.mpr ⟨U, mem_insert_self _ _, mem_union_left _ hxC⟩
  have hUnion := partitionRank_le_cover g (insert U T) hdU
  rw [hcover, Finset.sum_insert hUT] at hUnion
  have hInter := partitionRank_le g (P.restrict (inter_subset_left : A ∩ C ⊆ A))
  have hrestrict : partitionCost g (P.restrict (inter_subset_left : A ∩ C ⊆ A)) =
      ∑ S ∈ R, (g (S ∩ C) - 1) := by
    unfold partitionCost
    rw [P.sum_restrict _ (fun S => g S - 1) (by simp)]
    calc
      (∑ S ∈ P.parts, (g (S ⊓ (A ∩ C)) - 1)) =
          ∑ S ∈ P.parts, (g (S ∩ C) - 1) := by
        apply Finset.sum_congr rfl
        intro S hS
        change g (S ∩ (A ∩ C)) - 1 = _
        rw [← Finset.inter_assoc, Finset.inter_eq_left.mpr (P.subset hS)]
      _ = ∑ S ∈ R, (g (S ∩ C) - 1) := by
        symm
        apply Finset.sum_subset hRsub
        intro S hS hn
        have hnot : ¬ (S ∩ C).Nonempty := fun hm => hn (mem_filter.mpr ⟨hS, hm⟩)
        rw [Finset.not_nonempty_iff_eq_empty.mp hnot]
        simp
  rw [hrestrict] at hInter
  have hcost : (∑ S ∈ R, (g S - 1)) + (∑ S ∈ T, (g S - 1)) =
      partitionCost g P :=
    Finset.sum_filter_add_sum_filter_not P.parts (fun S => (S ∩ C).Nonempty) _
  change (g U - 1) + _ ≤ _ at hmerge
  omega

theorem partitionRank_partition_submodular (g : RankFunction V) (hg : g.Active)
    (A : Finset V) (R : Finset (Finset V))
    (hd : (R : Set (Finset V)).PairwiseDisjoint id) :
    partitionRank g (A ∪ R.biUnion id) + partitionRank g (A ∩ R.biUnion id) ≤
      partitionRank g A + ∑ C ∈ R, (g C - 1) := by
  induction R using Finset.induction_on with
  | empty => simp
  | @insert C R hCR ih =>
    have hdR : (R : Set (Finset V)).PairwiseDisjoint id := by
      intro S hS T hT hne
      exact hd (mem_insert_of_mem hS) (mem_insert_of_mem hT) hne
    have hdis : Disjoint C (R.biUnion id) := by
      rw [Finset.disjoint_biUnion_right]
      intro S hS
      exact hd (mem_insert_self _ _) (mem_insert_of_mem hS) (fun h => hCR (h ▸ hS))
    have ih' := ih hdR
    have hsingle := partitionRank_single_submodular g hg (A ∪ R.biUnion id) C
    have hsmall : (A ∪ R.biUnion id) ∩ C = A ∩ C := by
      rw [Finset.union_inter_distrib_right,
        Finset.disjoint_iff_inter_eq_empty.mp hdis.symm, Finset.union_empty]
    rw [hsmall] at hsingle
    have hinter := partitionRank_disjoint_subadd g
      (hdis.mono inter_subset_right inter_subset_right :
        Disjoint (A ∩ C) (A ∩ R.biUnion id))
    have hu : A ∪ (insert C R).biUnion id = (A ∪ R.biUnion id) ∪ C := by
      simp only [Finset.biUnion_insert, id_eq]
      ac_rfl
    have hi : A ∩ (insert C R).biUnion id = (A ∩ C) ∪ (A ∩ R.biUnion id) := by
      simp only [Finset.biUnion_insert, id_eq, Finset.inter_union_distrib_left]
    rw [hu, hi, Finset.sum_insert hCR]
    omega

/-- The exact set-partition minimum is submodular in every finite ground set. -/
theorem partitionRank_submodular (g : RankFunction V) (hg : g.Active) (A B : Finset V) :
    partitionRank g (A ∪ B) + partitionRank g (A ∩ B) ≤
      partitionRank g A + partitionRank g B := by
  obtain ⟨P, hP⟩ := partitionRank_attained g B
  have h := partitionRank_partition_submodular g hg A P.parts P.disjoint
  rw [P.biUnion_parts] at h
  change _ ≤ partitionRank g A + partitionCost g P at h
  rwa [hP] at h

end CommAlg.Polymatroid
