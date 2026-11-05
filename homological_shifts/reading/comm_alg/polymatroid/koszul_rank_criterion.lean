import CommAlg.Polymatroid.KoszulRankArithmetic
import CommAlg.Matroid.IndependenceHomology

/-!
# Exact rank and coloop detection for the Koszul matroid

The matroid is built from the actual nonnegative deletion slacks of a monomial
satisfying the lower rank inequalities. Its rank and coloops are Mathlib's
notions, and its homology is the actual augmented exterior-chain homology.
-/

noncomputable section

open scoped Matroid

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def koszulConstraintMatroid (g : RankFunction V) (a : Exponent V)
    (ha : LowerFeasible g.lower a) : _root_.Matroid V :=
  constraintMatroid (deletionSlack g a) (deletionSlack_submodular g ha)
    (deletionSlack_empty g a) a.support

@[simp] theorem koszulConstraintMatroid_ground (g : RankFunction V) (a : Exponent V)
    (ha : LowerFeasible g.lower a) :
    (koszulConstraintMatroid g a ha).E = (a.support : Set V) := rfl

@[simp] theorem koszulConstraintMatroid_indep (g : RankFunction V) (a : Exponent V)
    (ha : LowerFeasible g.lower a) (s : Finset V) :
    (koszulConstraintMatroid g a ha).Indep (s : Set V) ↔
      s ⊆ a.support ∧ ∀ U, (s ∩ U).card ≤ deletionSlack g a U :=
  constraintMatroid_indep _ _ _ _ _

theorem le_koszulConstraint_rank (g : RankFunction V) (a : Exponent V)
    (ha : LowerFeasible g.lower a) (R : Finset V) (hR : R ⊆ a.support) (i : ℕ) :
    i ≤ ((koszulConstraintMatroid g a ha).eRk (R : Set V)).toNat ↔
      ∀ U, i ≤ deletionSlack g a U + (R \ U).card := by
  obtain ⟨U, hU, hmin⟩ := constraint_rank_certificate (deletionSlack g a)
    (deletionSlack_submodular g ha) (deletionSlack_empty g a) a.support R hR
  change i ≤ ((constraintMatroid _ _ _ _).eRk (R : Set V)).toNat ↔ _
  rw [hU, ENat.toNat_natCast]
  exact ⟨fun h W => h.trans (hmin W), fun h => h U⟩

theorem koszulConstraint_rank_le (g : RankFunction V) {a : Exponent V} {i : ℕ}
    (ha : LowerFeasible g.lower a) (hDegree : a.degree = g univ + i) :
    CommAlg.Matroid.rank (koszulConstraintMatroid g a ha) ≤ i := by
  obtain ⟨U, hU, hmin⟩ := constraint_rank_certificate (deletionSlack g a)
    (deletionSlack_submodular g ha) (deletionSlack_empty g a)
    a.support a.support le_rfl
  have hBound := hmin univ
  have hBound' : deletionSlack g a U + (a.support \ U).card ≤ i := by
    simpa only [deletionSlack_univ g hDegree, Finset.sdiff_eq_empty_iff_subset.mpr
      (Finset.subset_univ a.support), Finset.card_empty, Nat.add_zero] using hBound
  have hRank : CommAlg.Matroid.rank (koszulConstraintMatroid g a ha) =
      deletionSlack g a U + (a.support \ U).card := by
    unfold CommAlg.Matroid.rank
    rw [← _root_.Matroid.eRk_ground]
    change ((constraintMatroid _ _ _ _).eRk (a.support : Set V)).toNat = _
    rw [hU, ENat.toNat_natCast]
  rwa [hRank]

theorem koszulConstraint_delete_rank_eq (g : RankFunction V) (a : Exponent V)
    (ha : LowerFeasible g.lower a) (j : V) :
    CommAlg.Matroid.rank ((koszulConstraintMatroid g a ha) ＼ ({j} : Set V)) =
      ((koszulConstraintMatroid g a ha).eRk ((a.support.erase j : Finset V) : Set V)).toNat := by
  have hGround : (koszulConstraintMatroid g a ha).E \ {j} =
      ((a.support.erase j : Finset V) : Set V) := by
    ext x
    simp only [koszulConstraintMatroid_ground, Set.mem_sdiff, Finset.mem_coe,
      Set.mem_singleton_iff, Finset.mem_erase]
    tauto
  unfold CommAlg.Matroid.rank
  rw [_root_.Matroid.delete_eq_restrict, _root_.Matroid.eRank_restrict, hGround]

theorem le_koszulConstraint_delete_rank (g : RankFunction V) (a : Exponent V)
    (ha : LowerFeasible g.lower a) (j : V) (i : ℕ) :
    i ≤ CommAlg.Matroid.rank ((koszulConstraintMatroid g a ha) ＼ ({j} : Set V)) ↔
      ∀ U, i ≤ deletionSlack g a U + ((a.support.erase j) \ U).card := by
  rw [koszulConstraint_delete_rank_eq]
  exact le_koszulConstraint_rank g a ha (a.support.erase j) (Finset.erase_subset _ _) i

/-- The full equivalence (3.1)--(3.3) for the actual Koszul constraint matroid. -/
theorem koszulConstraint_rank_and_noColoops_iff (g : RankFunction V) (hg : g.Active)
    {a : Exponent V} {i : ℕ} (ha : LowerFeasible g.lower a)
    (hDegree : a.degree = g univ + i) (hSupport : a.support.Nonempty) :
    (CommAlg.Matroid.rank (koszulConstraintMatroid g a ha) = i ∧
      CommAlg.Matroid.NoColoops (koszulConstraintMatroid g a ha)) ↔
      ∀ A, A.Nonempty → subsetSum (supportPred a) A ≤ g A - 1 := by
  let M := koszulConstraintMatroid g a ha
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
  exact hStep.trans ((all_deletion_costs_ge_iff g ha hDegree).trans
    (supportPred_indicator_bounds_iff g hg a))

omit [Fintype V] [DecidableEq V] in
theorem support_nonempty_of_degree_pos {a : Exponent V} (ha : 0 < a.degree) :
    a.support.Nonempty := by
  by_contra h
  have he : a.support = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  have hz : a = 0 := Finsupp.support_eq_empty.mp he
  simp [hz] at ha

/-- The positive-rank case used in the paper automatically has nonempty
support; no support condition is imposed on the theorem's input. -/
theorem koszulConstraint_rank_and_noColoops_iff_of_rank_pos
    (g : RankFunction V) (hg : g.Active) (hd : 0 < g univ)
    {a : Exponent V} {i : ℕ} (ha : LowerFeasible g.lower a)
    (hDegree : a.degree = g univ + i) :
    (CommAlg.Matroid.rank (koszulConstraintMatroid g a ha) = i ∧
      CommAlg.Matroid.NoColoops (koszulConstraintMatroid g a ha)) ↔
      ∀ A, A.Nonempty → subsetSum (supportPred a) A ≤ g A - 1 :=
  koszulConstraint_rank_and_noColoops_iff g hg ha hDegree
    (support_nonempty_of_degree_pos (by omega))

/-- No coloops forces a minimizing rank certificate to contain the whole
support. Consequently the actual rank is exactly the excess total degree.
This requires neither active variables nor positive total rank. -/
theorem koszulConstraint_rank_eq_excess_of_noColoops (g : RankFunction V)
    {a : Exponent V} (ha : LowerFeasible g.lower a)
    (hNo : CommAlg.Matroid.NoColoops (koszulConstraintMatroid g a ha)) :
    CommAlg.Matroid.rank (koszulConstraintMatroid g a ha) = a.degree - g univ := by
  obtain ⟨U, hU, hmin⟩ := constraint_rank_certificate (deletionSlack g a)
    (deletionSlack_submodular g ha) (deletionSlack_empty g a)
    a.support a.support le_rfl
  have hSupport : a.support ⊆ U := by
    intro j hj
    by_contra hjU
    exact hNo j (constraint_isColoop_of_minimizer (deletionSlack g a)
      (deletionSlack_submodular g ha) (deletionSlack_empty g a) a.support U hU
      (Finset.mem_sdiff.mpr ⟨hj, hjU⟩))
  have hRank : CommAlg.Matroid.rank (koszulConstraintMatroid g a ha) =
      deletionSlack g a U := by
    unfold CommAlg.Matroid.rank
    rw [← _root_.Matroid.eRk_ground]
    change ((constraintMatroid _ _ _ _).eRk (a.support : Set V)).toNat = _
    rw [hU, Finset.sdiff_eq_empty_iff_subset.mpr hSupport, Finset.card_empty,
      Nat.add_zero, ENat.toNat_natCast]
  have hZero : subsetSum a Uᶜ = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    exact Finsupp.notMem_support_iff.mp (fun h => (Finset.mem_compl.mp hj) (hSupport h))
  have hSum := subsetSum_add_compl a U
  rw [hZero, Nat.add_zero] at hSum
  have hSlack := deletionSlack_add_lower g ha U
  have hLower := g.lower_le U
  have hTotal := ha univ
  simp only [RankFunction.lower_univ, subsetSum_univ] at hTotal
  have hDegree : a.degree = g univ + (a.degree - g univ) := by omega
  have hUpper := koszulConstraint_rank_le g ha hDegree
  omega

section Homology

variable [LinearOrder V] {k : Type*} [CommRing k] [Nontrivial k]

/-- Field-independent nonvanishing of the genuine augmented homology of the
Koszul matroid, expressed by the exact upper subset inequalities (3.6). -/
theorem koszulConstraint_nonzeroHomology_iff_augmented (g : RankFunction V)
    (hg : g.Active) (hd : 0 < g univ) {a : Exponent V} {i : ℕ}
    (ha : LowerFeasible g.lower a) (hDegree : a.degree = g univ + i) :
    CommAlg.Simplicial.NonzeroHomology (k := k)
      (CommAlg.Matroid.independenceFaces (koszulConstraintMatroid g a ha)) i ↔
      ∀ A, subsetSum a A ≤ augmentedPartitionRank g A := by
  rw [CommAlg.Matroid.independence_nonzeroHomology_iff]
  have h := koszulConstraint_rank_and_noColoops_iff_of_rank_pos g hg hd ha hDegree
  rw [eq_comm] at h
  exact h.trans (supportPred_nonempty_bounds_iff_augmented g a)

/-- All-degree concentration follows directly from the actual constraint
matroid, without assuming a linear-resolution theorem. -/
theorem koszulConstraint_nonzeroHomology_degree (g : RankFunction V)
    {a : Exponent V} (ha : LowerFeasible g.lower a) {i : ℕ}
    (h : CommAlg.Simplicial.NonzeroHomology (k := k)
      (CommAlg.Matroid.independenceFaces (koszulConstraintMatroid g a ha)) i) :
    a.degree = g univ + i := by
  obtain ⟨hRank, hNo⟩ := (CommAlg.Matroid.independence_nonzeroHomology_iff _ _).mp h
  have hExcess := koszulConstraint_rank_eq_excess_of_noColoops g ha hNo
  have hTotal := ha univ
  simp only [RankFunction.lower_univ, subsetSum_univ] at hTotal
  omega

end Homology

end CommAlg.Polymatroid
