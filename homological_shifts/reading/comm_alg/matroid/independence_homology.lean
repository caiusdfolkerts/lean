import CommAlg.Matroid.MinorInduction
import CommAlg.Simplicial.Filling

/-!
# Homology of every finite matroid independence complex

The augmented chain complex is the genuine exterior-basis complex from
`CommAlg.Simplicial.Chains`. Induction removes an actual ground element,
using actual deletion and contraction matroids. No shellability, homology
concentration, or top-homology hypothesis is built into the statement.
-/

noncomputable section

open scoped Matroid

namespace CommAlg.Matroid

open Classical
open CommAlg.Simplicial

variable {V k : Type*} [Fintype V] [LinearOrder V] [CommRing k]

def independenceFaces (M : _root_.Matroid V) (s : Finset V) : Prop :=
  M.Indep (s : Set V)

omit [Fintype V] [LinearOrder V] in
theorem independenceFaces_downward (M : _root_.Matroid V) :
    Downward (independenceFaces M) := by
  intro s t hts hs
  exact hs.subset (by simpa using hts)

omit [Fintype V] [LinearOrder V] in
@[simp] theorem independenceFaces_empty (M : _root_.Matroid V) :
    independenceFaces M ∅ := by
  simpa only [independenceFaces, Finset.coe_empty] using M.empty_indep

omit [Fintype V] in
theorem independenceFaces_delete (M : _root_.Matroid V) (e : V) :
    independenceFaces (M ＼ ({e} : Set V)) = deletion (independenceFaces M) e := by
  funext s
  exact propext (delete_indep_finset_iff s)

omit [Fintype V] in
theorem independenceFaces_contract (M : _root_.Matroid V) {e : V} (he : M.IsNonloop e) :
    independenceFaces (M ／ ({e} : Set V)) = link (independenceFaces M) e := by
  funext s
  exact propext (contract_indep_finset_iff he s)

theorem independence_exactIn_of_coloop (M : _root_.Matroid V) {e : V}
    (he : M.IsColoop e) (i : ℕ) : ExactIn (k := k) (independenceFaces M) i := by
  apply exactIn_of_cone e
  intro s hs
  exact coloop_insert_indep_finset he hs

private theorem independence_exactIn_induction (n : ℕ) :
    ∀ M : _root_.Matroid V, M.E.ncard = n →
      ∀ i : ℕ, i ≠ rank M → ExactIn (k := k) (independenceFaces M) i := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro M hCard i hi
    by_cases hr : rank M = 0
    · apply exactIn_of_no_face
      intro s hs
      have hs0 : s = ∅ := indep_finset_eq_empty_of_rank_zero hr hs
      rw [hs0, Finset.card_empty]
      simpa only [hr, ne_eq, eq_comm] using hi
    by_cases hColoop : ∃ e, M.IsColoop e
    · obtain ⟨e, he⟩ := hColoop
      exact independence_exactIn_of_coloop M he i
    obtain ⟨e, he⟩ := exists_nonloop_of_rank_pos (Nat.pos_of_ne_zero hr)
    have hne : ¬ M.IsColoop e := fun h => hColoop ⟨e, h⟩
    have hDeleteRank := rank_delete_of_not_isColoop hne
    have hContractRank := rank_contract_add_one he
    have hDeleteCard : (M ＼ ({e} : Set V)).E.ncard < n := by
      rw [← hCard]
      exact delete_ground_ncard_lt he.mem_ground
    have hContractCard : (M ／ ({e} : Set V)).E.ncard < n := by
      rw [← hCard]
      exact contract_ground_ncard_lt he.mem_ground
    cases i with
    | zero =>
      apply exactIn_zero_of_vertex e
      simpa only [independenceFaces, Finset.coe_singleton] using he.indep
    | succ j =>
      have hDelete : ExactIn (k := k) (independenceFaces (M ＼ ({e} : Set V))) (j + 1) :=
        ih _ hDeleteCard _ rfl _ (by omega)
      have hContract : ExactIn (k := k) (independenceFaces (M ／ ({e} : Set V))) j :=
        ih _ hContractCard _ rfl _ (by omega)
      apply exactIn_of_deletion_link (independenceFaces_downward M) e j
      · rwa [← independenceFaces_delete M e]
      · rwa [← independenceFaces_contract M he]

/-- Every reduced homology group of a finite matroid independence complex
outside degree `rank M - 1` vanishes, expressed by explicit chain fillings.
The empty face has augmented chain degree zero. -/
theorem independence_exactIn_of_ne_rank (M : _root_.Matroid V) (i : ℕ)
    (hi : i ≠ rank M) : ExactIn (k := k) (independenceFaces M) i :=
  independence_exactIn_induction M.E.ncard M rfl i hi

section Nontrivial

variable [Nontrivial k]

private theorem independence_nonzero_top_induction (n : ℕ) :
    ∀ M : _root_.Matroid V, M.E.ncard = n → NoColoops M →
      NonzeroHomology (k := k) (independenceFaces M) (rank M) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro M hCard hM
    by_cases hr : rank M = 0
    · rw [hr]
      apply nonzeroHomology_zero_of_only_empty (independenceFaces_empty M)
      intro s hs
      exact indep_finset_eq_empty_of_rank_zero hr hs
    obtain ⟨e, he⟩ := exists_nonloop_of_rank_pos (Nat.pos_of_ne_zero hr)
    have hDeleteRank := rank_delete_of_not_isColoop (hM e)
    have hContractRank := rank_contract_add_one he
    have hContractCard : (M ／ ({e} : Set V)).E.ncard < n := by
      rw [← hCard]
      exact contract_ground_ncard_lt he.mem_ground
    have hContract : NonzeroHomology (k := k)
        (independenceFaces (M ／ ({e} : Set V))) (rank (M ／ ({e} : Set V))) :=
      ih _ hContractCard _ rfl hM.contract
    have hDelete : ExactIn (k := k) (independenceFaces (M ＼ ({e} : Set V)))
        (rank (M ／ ({e} : Set V))) :=
      independence_exactIn_of_ne_rank _ _ (by omega)
    have hTop := nonzeroHomology_of_link (independenceFaces_downward M) e
      (rank (M ／ ({e} : Set V)))
      (by rwa [← independenceFaces_delete M e])
      (by rwa [← independenceFaces_contract M he])
    rwa [hContractRank] at hTop

/-- A finite matroid with no coloops has an actual nonboundary cycle in its
top augmented chain degree, over every nontrivial commutative coefficient ring. -/
theorem independence_nonzero_top (M : _root_.Matroid V) (hM : NoColoops M) :
    NonzeroHomology (k := k) (independenceFaces M) (rank M) :=
  independence_nonzero_top_induction M.E.ncard M rfl hM

/-- Full homology detection for every finite matroid, including rank zero,
loops, coloops, and all coefficient characteristics. -/
theorem independence_nonzeroHomology_iff (M : _root_.Matroid V) (i : ℕ) :
    NonzeroHomology (k := k) (independenceFaces M) i ↔ i = rank M ∧ NoColoops M := by
  constructor
  · intro h
    have hNot := (nonzeroHomology_iff_not_exactIn _ _).mp h
    refine ⟨?_, ?_⟩
    · by_contra hi
      exact hNot (independence_exactIn_of_ne_rank M i hi)
    · intro e he
      exact hNot (independence_exactIn_of_coloop M he i)
  · rintro ⟨rfl, hM⟩
    exact independence_nonzero_top M hM

theorem independence_exactIn_iff (M : _root_.Matroid V) (i : ℕ) :
    ExactIn (k := k) (independenceFaces M) i ↔ i ≠ rank M ∨ ¬ NoColoops M := by
  have h := independence_nonzeroHomology_iff (k := k) M i
  rw [nonzeroHomology_iff_not_exactIn] at h
  tauto

end Nontrivial

end CommAlg.Matroid
