import CommAlg.KoszulComplex.FaceCombinatorics
import CommAlg.Polymatroid.KoszulRankCriterion

/-! # The actual Koszul faces are the constraint matroid's independent sets

The proof starts from the monomial membership condition in `koszulFaces`.
It proves both the support condition and the exact simultaneous-deletion
inequalities, before identifying any homology groups.
-/

noncomputable section

namespace CommAlg.Koszul

open Classical Finset CommAlg.Polymatroid

variable {V : Type*} [Fintype V] [LinearOrder V]

theorem faceExponent_le_iff_subset_support (s : Finset V) (a : Exponent V) :
    faceExponent s ≤ a ↔ s ⊆ a.support := by
  constructor
  · intro h j hj
    have hb := h j
    simp only [faceExponent_apply, if_pos hj] at hb
    exact Finsupp.mem_support_iff.mpr (by omega)
  · intro h j
    by_cases hj : j ∈ s
    · have hb := Finsupp.mem_support_iff.mp (h hj)
      simp only [faceExponent_apply, if_pos hj]
      omega
    · simp [hj]

theorem subsetSum_faceExponent (s U : Finset V) :
    subsetSum (faceExponent s) U = (s ∩ U).card := by
  simp only [subsetSum, faceExponent_apply, Finset.sum_boole, Finset.filter_mem_eq_inter,
    Nat.cast_id, Finset.inter_comm]

theorem subsetSum_sub_faceExponent {s : Finset V} {a : Exponent V}
    (ha : faceExponent s ≤ a) (U : Finset V) :
    subsetSum (a - faceExponent s) U + (s ∩ U).card = subsetSum a U := by
  have he := tsub_add_cancel_of_le ha
  have hs := congrArg (fun b : Exponent V => subsetSum b U) he
  have hs' : subsetSum (a - faceExponent s) U + subsetSum (faceExponent s) U = subsetSum a U := by
    simpa only [subsetSum, Finsupp.add_apply, Finset.sum_add_distrib] using hs
  rwa [subsetSum_faceExponent] at hs'

theorem lowerFeasible_sub_faceExponent_iff (g : RankFunction V)
    {a : Exponent V} (ha : LowerFeasible g.lower a) {s : Finset V}
    (hs : faceExponent s ≤ a) :
    LowerFeasible g.lower (a - faceExponent s) ↔
      ∀ U, (s ∩ U).card ≤ deletionSlack g a U := by
  constructor
  · intro h U
    have hLower := h U
    have hSub := subsetSum_sub_faceExponent hs U
    have hSlack := deletionSlack_add_lower g ha U
    omega
  · intro h U
    have hBound := h U
    have hSub := subsetSum_sub_faceExponent hs U
    have hSlack := deletionSlack_add_lower g ha U
    omega

/-- Exact equality of the original upper Koszul complex's faces with the
independent sets of the actual finite constraint matroid. -/
theorem koszulFaces_eq_independenceFaces (B : Family V) (g : RankFunction V)
    (hB : ∀ a, Contains B a ↔ LowerFeasible g.lower a)
    (a : Exponent V) (ha : LowerFeasible g.lower a) :
    koszulFaces B a = CommAlg.Matroid.independenceFaces (koszulConstraintMatroid g a ha) := by
  funext s
  apply propext
  change (faceExponent s ≤ a ∧ Contains B (a - faceExponent s)) ↔
    (koszulConstraintMatroid g a ha).Indep (s : Set V)
  rw [koszulConstraintMatroid_indep]
  constructor
  · rintro ⟨hs, hb⟩
    exact ⟨(faceExponent_le_iff_subset_support s a).mp hs,
      (lowerFeasible_sub_faceExponent_iff g ha hs).mp ((hB _).mp hb)⟩
  · rintro ⟨hs, hb⟩
    have hs' := (faceExponent_le_iff_subset_support s a).mpr hs
    exact ⟨hs', (hB _).mpr ((lowerFeasible_sub_faceExponent_iff g ha hs').mpr hb)⟩

theorem koszulFaces_contains {B : Family V} {a : Exponent V} {s : Finset V}
    (hs : koszulFaces B a s) : Contains B a := by
  obtain ⟨b, hb, hba⟩ := hs.2
  exact ⟨b, hb, hba.trans tsub_le_self⟩

theorem koszulFaces_false_of_not_contains (B : Family V) (a : Exponent V)
    (ha : ¬ Contains B a) : koszulFaces B a = fun _ => False := by
  funext s
  exact propext ⟨fun h => ha (koszulFaces_contains h), False.elim⟩

end CommAlg.Koszul
