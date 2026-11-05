import CommAlg.Polymatroid.KoszulRankCriterion
import CommAlg.Polymatroid.UniversalRank

/-!
# The Koszul rank criterion with arbitrary loops and zero rank

The actual rank/coloop criterion is first expressed by support-sensitive
indicator inequalities. These are equivalent to inequalities on the original
exponent using `g(A) + |A| - 1`, without assuming active variables.
-/

noncomputable section

open scoped Matroid

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem supportPred_indicator_bounds_iff_lift (g : RankFunction V) (a : Exponent V) :
    (∀ j ∈ a.support, ∀ A,
      subsetSum (supportPred a) A + (if j ∈ A then 1 else 0) ≤ g A) ↔
      (∀ A, A.Nonempty → subsetSum a A ≤ g A + A.card - 1) := by
  constructor
  · intro h A hA
    by_cases hW : (A ∩ a.support).Nonempty
    · obtain ⟨j, hj⟩ := hW
      obtain ⟨hjA, hjS⟩ := mem_inter.mp hj
      have hb := h j hjS A
      rw [if_pos hjA] at hb
      have he := subsetSum_supportPred a A
      have hc := card_le_card (inter_subset_left : A ∩ a.support ⊆ A)
      omega
    · have he := subsetSum_support_inter a A
      rw [not_nonempty_iff_eq_empty.mp hW, subsetSum_empty] at he
      omega
  · intro h j hj A
    by_cases hW : (A ∩ a.support).Nonempty
    · have hb := h (A ∩ a.support) hW
      have he := subsetSum_supportPred a (A ∩ a.support)
      rw [inter_eq_left.mpr inter_subset_right, subsetSum_supportPred_inter] at he
      have hg := g.monotone (inter_subset_left : A ∩ a.support ⊆ A)
      have hc : 1 ≤ (A ∩ a.support).card := card_pos.mpr hW
      split_ifs <;> omega
    · have hEmpty : A ∩ a.support = ∅ := not_nonempty_iff_eq_empty.mp hW
      have he := subsetSum_supportPred_inter a A
      rw [hEmpty, subsetSum_empty] at he
      have hjA : j ∉ A := by
        intro hjA
        have hjW := mem_inter.mpr ⟨hjA, hj⟩
        rw [hEmpty] at hjW
        exact notMem_empty j hjW
      rw [if_neg hjA]
      omega

/-- The rank and no-coloop criterion remains exact when some variables are
loops, the rank is zero, or the support is empty. -/
theorem koszulConstraint_rank_and_noColoops_iff_indicator (g : RankFunction V)
    {a : Exponent V} {i : ℕ} (ha : LowerFeasible g.lower a)
    (hDegree : a.degree = g univ + i) :
    (CommAlg.Matroid.rank (koszulConstraintMatroid g a ha) = i ∧
      CommAlg.Matroid.NoColoops (koszulConstraintMatroid g a ha)) ↔
      ∀ j ∈ a.support, ∀ A,
        subsetSum (supportPred a) A + (if j ∈ A then 1 else 0) ≤ g A := by
  by_cases hSupport : a.support.Nonempty
  · let M := koszulConstraintMatroid g a ha
    have hRank := koszulConstraint_rank_le g ha hDegree
    have hGround : M.E.Nonempty := by
      simpa only [M, koszulConstraintMatroid_ground, Finset.coe_nonempty] using hSupport
    have hDelete := CommAlg.Matroid.rank_eq_and_noColoops_iff_delete_rank M i hGround hRank
    have hStep : (CommAlg.Matroid.rank M = i ∧ CommAlg.Matroid.NoColoops M) ↔
        ∀ j ∈ a.support, ∀ U,
          i ≤ deletionSlack g a U + ((a.support.erase j) \ U).card := by
      rw [hDelete]
      constructor
      · intro h j hj
        apply (le_koszulConstraint_delete_rank g a ha j i).mp
        exact le_of_eq (h j hj).symm
      · intro h j hj
        have hLower := (le_koszulConstraint_delete_rank g a ha j i).mpr (h j hj)
        have hUpper := (CommAlg.Matroid.rank_delete_le M ({j} : Set V)).trans hRank
        exact Nat.le_antisymm hUpper hLower
    exact hStep.trans (all_deletion_costs_ge_iff g ha hDegree)
  · have hEmpty : a.support = ∅ := not_nonempty_iff_eq_empty.mp hSupport
    have ha0 : a = 0 := Finsupp.support_eq_empty.mp hEmpty
    have hi : i = 0 := by
      have hz : a.degree = 0 := by simp [ha0]
      omega
    have hRank := koszulConstraint_rank_le g ha hDegree
    have hNo : CommAlg.Matroid.NoColoops (koszulConstraintMatroid g a ha) := by
      intro j hj
      have hjg := hj.mem_ground
      simpa only [koszulConstraintMatroid_ground, hEmpty, coe_empty,
        Set.mem_empty_iff_false] using hjg
    constructor
    · intro _ j hj
      simp [hEmpty] at hj
    · intro _
      exact ⟨by omega, hNo⟩

theorem koszulConstraint_rank_and_noColoops_iff_lift (g : RankFunction V)
    {a : Exponent V} {i : ℕ} (ha : LowerFeasible g.lower a)
    (hDegree : a.degree = g univ + i) :
    (CommAlg.Matroid.rank (koszulConstraintMatroid g a ha) = i ∧
      CommAlg.Matroid.NoColoops (koszulConstraintMatroid g a ha)) ↔
      ∀ A, A.Nonempty → subsetSum a A ≤ g A + A.card - 1 :=
  (koszulConstraint_rank_and_noColoops_iff_indicator g ha hDegree).trans
    (supportPred_indicator_bounds_iff_lift g a)

theorem koszulConstraint_rank_and_noColoops_iff_universal (g : RankFunction V)
    {a : Exponent V} {i : ℕ} (ha : LowerFeasible g.lower a)
    (hDegree : a.degree = g univ + i) :
    (CommAlg.Matroid.rank (koszulConstraintMatroid g a ha) = i ∧
      CommAlg.Matroid.NoColoops (koszulConstraintMatroid g a ha)) ↔
      ∀ A, subsetSum a A ≤ universalAugmentedRank g A :=
  (koszulConstraint_rank_and_noColoops_iff_lift g ha hDegree).trans
    (universal_bounds_iff g a)

section Homology

variable [LinearOrder V] {k : Type*} [CommRing k] [Nontrivial k]

/-- The genuine chain-homology criterion, including all loop and zero-rank
cases, without an active-variable hypothesis. -/
theorem koszulConstraint_nonzeroHomology_iff_universal (g : RankFunction V)
    {a : Exponent V} {i : ℕ} (ha : LowerFeasible g.lower a)
    (hDegree : a.degree = g univ + i) :
    CommAlg.Simplicial.NonzeroHomology (k := k)
      (CommAlg.Matroid.independenceFaces (koszulConstraintMatroid g a ha)) i ↔
      ∀ A, subsetSum a A ≤ universalAugmentedRank g A := by
  rw [CommAlg.Matroid.independence_nonzeroHomology_iff]
  have h := koszulConstraint_rank_and_noColoops_iff_universal g ha hDegree
  rw [eq_comm] at h
  exact h

/-- Complete degree and inequality characterization of actual nonvanishing,
valid for an arbitrary normalized monotone submodular rank. -/
theorem koszulConstraint_nonzeroHomology_iff_universal_full (g : RankFunction V)
    {a : Exponent V} (ha : LowerFeasible g.lower a) (i : ℕ) :
    CommAlg.Simplicial.NonzeroHomology (k := k)
      (CommAlg.Matroid.independenceFaces (koszulConstraintMatroid g a ha)) i ↔
      a.degree = g univ + i ∧ ∀ A, subsetSum a A ≤ universalAugmentedRank g A := by
  constructor
  · intro h
    have hDegree := koszulConstraint_nonzeroHomology_degree g ha h
    exact ⟨hDegree, (koszulConstraint_nonzeroHomology_iff_universal g ha hDegree).mp h⟩
  · rintro ⟨hDegree, hBounds⟩
    exact (koszulConstraint_nonzeroHomology_iff_universal g ha hDegree).mpr hBounds

end Homology

end CommAlg.Polymatroid
