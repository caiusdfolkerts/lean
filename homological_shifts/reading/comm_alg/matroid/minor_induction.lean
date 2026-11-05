module

public import Mathlib.Combinatorics.Matroid.Minor.Contract
public import Mathlib.Combinatorics.Matroid.Rank.ENat
public import Mathlib.Tactic

/-!
# Finite matroid deletion and contraction for homology induction

All minors are Mathlib's actual matroids. The natural rank is the finite value
of Mathlib's extended-natural rank, and every numerical formula is derived
from base cardinalities.
-/

noncomputable section

@[expose] public section

open scoped Matroid

namespace CommAlg.Matroid

open Classical Set

variable {V : Type*} {M : _root_.Matroid V} {e : V} {I : Set V}

def rank (M : _root_.Matroid V) : ℕ := M.eRank.toNat

def NoColoops (M : _root_.Matroid V) : Prop := ∀ e, ¬ M.IsColoop e

theorem rank_eq_ncard_of_isBase {B : Set V} (hB : M.IsBase B) : rank M = B.ncard := by
  exact (congrArg ENat.toNat hB.encard_eq_eRank).symm

theorem rank_delete_of_not_isColoop (he : ¬ M.IsColoop e) :
    rank (M ＼ ({e} : Set V)) = rank M := by
  have hS : M.Spanning (M.E \ {e}) := by
    by_contra h
    exact he (_root_.Matroid.isColoop_iff_sdiff_not_spanning.mpr h)
  exact congrArg ENat.toNat hS.eRank_restrict

theorem NoColoops.contract {C : Set V} (hM : NoColoops M) : NoColoops (M ／ C) := by
  intro a ha
  exact hM a (_root_.Matroid.contract_isColoop_iff.mp ha).1

theorem noColoops_iff_coloops_eq_empty : NoColoops M ↔ M.coloops = ∅ := by
  simp [NoColoops, Set.eq_empty_iff_forall_notMem,
    ← _root_.Matroid.isColoop_iff_mem_coloops]

theorem coloop_insert_indep (he : M.IsColoop e) (hI : M.Indep I) :
    M.Indep (insert e I) := he.insert_indep_of_indep hI

section Finite

variable [Finite V]

theorem indep_ncard_le_rank (hI : M.Indep I) : I.ncard ≤ rank M := by
  obtain ⟨B, hB, hIB⟩ := hI.exists_isBase_superset
  rw [rank_eq_ncard_of_isBase hB]
  exact Set.ncard_le_ncard hIB

theorem rank_delete_le (M : _root_.Matroid V) (D : Set V) :
    rank (M ＼ D) ≤ rank M := by
  obtain ⟨B, hB⟩ := (M ＼ D).exists_isBase
  rw [rank_eq_ncard_of_isBase hB]
  exact indep_ncard_le_rank hB.indep.of_delete

theorem exists_nonloop_of_rank_pos (hr : 0 < rank M) : ∃ e, M.IsNonloop e := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  rw [rank_eq_ncard_of_isBase hB] at hr
  obtain ⟨e, he⟩ := (Set.ncard_pos (Set.toFinite B)).mp hr
  exact ⟨e, hB.indep.isNonloop_of_mem he⟩

theorem rank_pos_of_nonloop (he : M.IsNonloop e) : 0 < rank M := by
  have h := indep_ncard_le_rank he.indep
  have h' : 1 ≤ rank M := by simpa using h
  omega

theorem rank_pos_iff_exists_nonloop : 0 < rank M ↔ ∃ e, M.IsNonloop e :=
  ⟨exists_nonloop_of_rank_pos, fun ⟨_, he⟩ => rank_pos_of_nonloop he⟩

theorem indep_eq_empty_of_rank_zero (hr : rank M = 0) (hI : M.Indep I) : I = ∅ := by
  have h := indep_ncard_le_rank hI
  rw [hr] at h
  exact (Set.ncard_eq_zero (Set.toFinite I)).mp (Nat.eq_zero_of_le_zero h)

theorem rank_contract_add_one (he : M.IsNonloop e) :
    rank (M ／ ({e} : Set V)) + 1 = rank M := by
  obtain ⟨B, hB⟩ := (M ／ ({e} : Set V)).exists_isBase
  obtain ⟨hBM, hBe⟩ := he.indep.contract_isBase_iff.mp hB
  have heB : e ∉ B := Set.disjoint_singleton_right.mp hBe
  rw [rank_eq_ncard_of_isBase hB, rank_eq_ncard_of_isBase hBM,
    Set.union_singleton, Set.ncard_insert_of_notMem heB]

theorem rank_contract_eq_sub_one (he : M.IsNonloop e) :
    rank (M ／ ({e} : Set V)) = rank M - 1 := by
  have h := rank_contract_add_one he
  omega

theorem rank_delete_add_one_of_isColoop (he : M.IsColoop e) :
    rank (M ＼ ({e} : Set V)) + 1 = rank M := by
  have hC : ({e} : Set V) ⊆ M.coloops := Set.singleton_subset_iff.mpr he
  rw [← _root_.Matroid.contract_eq_delete_of_subset_coloops hC]
  exact rank_contract_add_one he.isNonloop

/-- When the ground set is nonempty and rank is at most `i`, rank `i` with
no coloops is equivalent to preservation of rank `i` after every singleton
deletion. This includes `i = 0`. -/
theorem rank_eq_and_noColoops_iff_delete_rank (M : _root_.Matroid V) (i : ℕ)
    (hE : M.E.Nonempty) (hr : rank M ≤ i) :
    (rank M = i ∧ NoColoops M) ↔
      ∀ e ∈ M.E, rank (M ＼ ({e} : Set V)) = i := by
  constructor
  · rintro ⟨hRank, hM⟩ e he
    exact (rank_delete_of_not_isColoop (hM e)).trans hRank
  · intro h
    obtain ⟨e, he⟩ := hE
    have hLower := rank_delete_le M ({e} : Set V)
    rw [h e he] at hLower
    have hRank : rank M = i := Nat.le_antisymm hr hLower
    refine ⟨hRank, ?_⟩
    intro f hf
    have hDelete := h f hf.mem_ground
    have hDrop := rank_delete_add_one_of_isColoop hf
    omega

theorem delete_ground_ncard_add_one (he : e ∈ M.E) :
    (M ＼ ({e} : Set V)).E.ncard + 1 = M.E.ncard := by
  exact Set.ncard_sdiff_singleton_add_one he

theorem contract_ground_ncard_add_one (he : e ∈ M.E) :
    (M ／ ({e} : Set V)).E.ncard + 1 = M.E.ncard := by
  exact Set.ncard_sdiff_singleton_add_one he

theorem delete_ground_ncard_lt (he : e ∈ M.E) :
    (M ＼ ({e} : Set V)).E.ncard < M.E.ncard := by
  have h := delete_ground_ncard_add_one he
  omega

theorem contract_ground_ncard_lt (he : e ∈ M.E) :
    (M ／ ({e} : Set V)).E.ncard < M.E.ncard := by
  have h := contract_ground_ncard_add_one he
  omega

end Finite

section Finset

variable [DecidableEq V]

/-- Deletion is exactly deletion of a label in the independence complex. -/
theorem delete_indep_finset_iff (s : Finset V) :
    (M ＼ ({e} : Set V)).Indep (s : Set V) ↔ M.Indep (s : Set V) ∧ e ∉ s := by
  simp only [_root_.Matroid.delete_indep_iff, Set.disjoint_singleton_right,
    Finset.mem_coe]

/-- Contraction at a nonloop is exactly the link in the independence complex. -/
theorem contract_indep_finset_iff (he : M.IsNonloop e) (s : Finset V) :
    (M ／ ({e} : Set V)).Indep (s : Set V) ↔
      M.Indep ((insert e s : Finset V) : Set V) ∧ e ∉ s := by
  simpa only [Finset.coe_insert, Finset.mem_coe, and_comm] using
    he.contractElem_indep_iff (I := (s : Set V))

theorem coloop_insert_indep_finset (he : M.IsColoop e) {s : Finset V}
    (hs : M.Indep (s : Set V)) : M.Indep ((insert e s : Finset V) : Set V) := by
  simpa only [Finset.coe_insert] using he.insert_indep_of_indep hs

variable [Finite V]

theorem indep_card_le_rank {s : Finset V} (hs : M.Indep (s : Set V)) :
    s.card ≤ rank M := by
  simpa using indep_ncard_le_rank hs

theorem indep_finset_eq_empty_of_rank_zero (hr : rank M = 0) {s : Finset V}
    (hs : M.Indep (s : Set V)) : s = ∅ := by
  have h := indep_card_le_rank hs
  rw [hr] at h
  exact Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero h)

end Finset

end CommAlg.Matroid
