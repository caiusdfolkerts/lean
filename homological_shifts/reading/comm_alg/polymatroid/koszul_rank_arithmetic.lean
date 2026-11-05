import CommAlg.Polymatroid.TrimBounds
import CommAlg.Polymatroid.ConstraintRank

/-!
# Exact arithmetic of the Koszul deletion constraints

These identities retain natural-valued exponents throughout. Every subtraction
in the deletion slack is justified by actual lower-inequality membership.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def deletionSlack (g : RankFunction V) (a : Exponent V) (U : Finset V) : ℕ :=
  subsetSum a U - g.lower U

theorem deletionSlack_add_lower (g : RankFunction V) {a : Exponent V}
    (ha : LowerFeasible g.lower a) (U : Finset V) :
    deletionSlack g a U + g.lower U = subsetSum a U :=
  Nat.sub_add_cancel (ha U)

@[simp] theorem deletionSlack_empty (g : RankFunction V) (a : Exponent V) :
    deletionSlack g a ∅ = 0 := by simp [deletionSlack]

theorem deletionSlack_submodular (g : RankFunction V) {a : Exponent V}
    (ha : LowerFeasible g.lower a) : SubmodularNat (deletionSlack g a) := by
  intro U W
  have hMod := subsetSum_union_inter a U W
  have hSuper := g.lower_supermodular U W
  have hU := deletionSlack_add_lower g ha U
  have hW := deletionSlack_add_lower g ha W
  have hUnion := deletionSlack_add_lower g ha (U ∪ W)
  have hInter := deletionSlack_add_lower g ha (U ∩ W)
  omega

theorem deletionSlack_univ (g : RankFunction V) {a : Exponent V} {i : ℕ}
    (hDegree : a.degree = g univ + i) : deletionSlack g a univ = i := by
  simp only [deletionSlack, subsetSum_univ, RankFunction.lower_univ, hDegree,
    Nat.add_sub_cancel_left]

theorem deletionSlack_add_complement (g : RankFunction V) {a : Exponent V} {i : ℕ}
    (ha : LowerFeasible g.lower a) (hDegree : a.degree = g univ + i) (U : Finset V) :
    deletionSlack g a U + subsetSum a Uᶜ = i + g Uᶜ := by
  have hSlack := deletionSlack_add_lower g ha U
  have hLower := g.lower_add_compl U
  have hSum := subsetSum_add_compl a U
  omega

theorem card_erase_sdiff_add_indicator (T U : Finset V) {j : V} (hj : j ∈ T) :
    ((T.erase j) \ U).card + (if j ∈ Uᶜ then 1 else 0) = (T ∩ Uᶜ).card := by
  rw [Finset.erase_sdiff_comm]
  have hSet : T \ U = T ∩ Uᶜ := by ext x; simp
  rw [hSet]
  by_cases hjU : j ∈ Uᶜ
  · rw [if_pos hjU]
    exact Finset.card_erase_add_one (Finset.mem_inter.mpr ⟨hj, hjU⟩)
  · rw [if_neg hjU, Nat.add_zero, Finset.erase_eq_of_notMem (by simp [hjU])]

/-- A rank-formula cost is at least the target degree precisely when the
support-predecessor exponent satisfies the corresponding one-unit inequality. -/
theorem deletion_cost_ge_iff_supportPred (g : RankFunction V) {a : Exponent V} {i : ℕ}
    (ha : LowerFeasible g.lower a) (hDegree : a.degree = g univ + i)
    {j : V} (hj : j ∈ a.support) (U : Finset V) :
    i ≤ deletionSlack g a U + ((a.support.erase j) \ U).card ↔
      subsetSum (supportPred a) Uᶜ + (if j ∈ Uᶜ then 1 else 0) ≤ g Uᶜ := by
  have hSlack := deletionSlack_add_complement g ha hDegree U
  have hCard := card_erase_sdiff_add_indicator a.support U hj
  have hPred := subsetSum_supportPred a Uᶜ
  rw [Finset.inter_comm Uᶜ a.support] at hPred
  omega

theorem all_deletion_costs_ge_iff (g : RankFunction V) {a : Exponent V} {i : ℕ}
    (ha : LowerFeasible g.lower a) (hDegree : a.degree = g univ + i) :
    (∀ j ∈ a.support, ∀ U, i ≤ deletionSlack g a U + ((a.support.erase j) \ U).card) ↔
      (∀ j ∈ a.support, ∀ A,
        subsetSum (supportPred a) A + (if j ∈ A then 1 else 0) ≤ g A) := by
  constructor
  · intro h j hj A
    simpa only [compl_compl] using
      (deletion_cost_ge_iff_supportPred g ha hDegree hj Aᶜ).mp (h j hj Aᶜ)
  · intro h j hj U
    exact (deletion_cost_ge_iff_supportPred g ha hDegree hj U).mpr (h j hj Uᶜ)

theorem supportPred_indicator_bounds_iff (g : RankFunction V) (hg : g.Active)
    (a : Exponent V) :
    (∀ j ∈ a.support, ∀ A,
      subsetSum (supportPred a) A + (if j ∈ A then 1 else 0) ≤ g A) ↔
      (∀ A, A.Nonempty → subsetSum (supportPred a) A ≤ g A - 1) := by
  constructor
  · intro h A hA
    by_cases hSupport : (A ∩ a.support).Nonempty
    · obtain ⟨j, hj⟩ := hSupport
      obtain ⟨hjA, hjSupport⟩ := Finset.mem_inter.mp hj
      have hb := h j hjSupport A
      rw [if_pos hjA] at hb
      omega
    · have hEmpty : A ∩ a.support = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSupport
      have hSum := subsetSum_supportPred_inter a A
      rw [hEmpty, subsetSum_empty] at hSum
      omega
  · intro h j hj A
    by_cases hjA : j ∈ A
    · have hA : A.Nonempty := ⟨j, hjA⟩
      have hb := h A hA
      have hgA := hg A hA
      rw [if_pos hjA]
      omega
    · rw [if_neg hjA, Nat.add_zero]
      by_cases hA : A.Nonempty
      · exact (h A hA).trans (Nat.sub_le _ _)
      · have he := Finset.not_nonempty_iff_eq_empty.mp hA
        simp [he]

end CommAlg.Polymatroid
