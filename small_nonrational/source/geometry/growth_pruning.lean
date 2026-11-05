module
prelude
public import SparseGrowthDAG
public import Init.Data.List.Perm
public import Init.Data.List.Pairwise

@[expose] public section

/-!
# Necessary local pruning conditions

The concrete search uses three tests: remaining facet-kind budget, proper-face
compatibility with the selected cells, and absence of a third cell at a ridge.
This file proves that none of these tests removes a missing cell of an actual
target satisfying the corresponding literal boundary conditions.
-/

namespace Papers.RationalityTen.GrowthPruning

open GrowthDAG SparseGrowthDAG

variable {n r : Nat}

def kindCount (kind : Fin n → Nat) (S : List (Fin n)) (k : Nat) : Nat :=
  (S.filter fun a => decide (kind a = k)).length

theorem kindCount_mono (kind : Fin n → Nat) (S B : List (Fin n)) (k : Nat)
    (hnd : S.Nodup) (hsub : S ⊆ B) : kindCount kind S k ≤ kindCount kind B k := by
  apply List.Nodup.length_le_of_subset (List.Pairwise.filter _ hnd)
  intro a ha
  obtain ⟨haS, hak⟩ := List.mem_filter.mp ha
  exact List.mem_filter.mpr ⟨hsub haS, hak⟩

theorem kindCount_lt (kind : Fin n → Nat) (S B : List (Fin n)) (c : Fin n)
    (hnd : S.Nodup) (hsub : S ⊆ B) (hcB : c ∈ B) (hcS : c ∉ S) :
    kindCount kind S (kind c) < kindCount kind B (kind c) := by
  have hconsnd : (c :: S).Nodup := List.nodup_cons.mpr ⟨hcS, hnd⟩
  have hconssub : c :: S ⊆ B := by
    intro a ha
    rcases List.mem_cons.mp ha with heq | ha
    · exact heq ▸ hcB
    · exact hsub ha
  have hle := kindCount_mono kind (c :: S) B (kind c) hconsnd hconssub
  simpa [kindCount, Nat.succ_le_iff] using hle

theorem ridgeCount_lt_two (ridges : Fin n → Fin r → Bool)
    (B : Family n) (S : List (Fin n)) (c : Fin n) (q : Fin r)
    (hthree : NoThree ridges B) (hsub : Included (family S) B)
    (hnd : S.Nodup) (hcB : B c = true) (hcS : has S c = false)
    (hcq : ridges c q = true) :
    (S.filter fun a => ridges a q).length < 2 := by
  have hfiltered : (S.filter fun a => ridges a q).Nodup :=
    List.Pairwise.filter _ hnd
  cases hlist : S.filter (fun a => ridges a q) with
  | nil => simp
  | cons a rest =>
    cases rest with
    | nil => simp
    | cons b tail =>
      have ha : a ∈ S ∧ ridges a q = true := List.mem_filter.mp
        (by rw [hlist]; exact List.mem_cons_self)
      have hb : b ∈ S ∧ ridges b q = true := List.mem_filter.mp
        (by rw [hlist]; exact List.mem_cons_of_mem _ List.mem_cons_self)
      have haB := hsub a ((has_true S a).mpr ha.1)
      have hbB := hsub b ((has_true S b).mpr hb.1)
      have hac : a ≠ c := by
        intro heq
        have hmem : has S c = true := (has_true S c).mpr (heq ▸ ha.1)
        exact Bool.noConfusion (hcS.symm.trans hmem)
      have hbc : b ≠ c := by
        intro heq
        have hmem : has S c = true := (has_true S c).mpr (heq ▸ hb.1)
        exact Bool.noConfusion (hcS.symm.trans hmem)
      have hab : a ≠ b := by
        have hnd' : (a :: b :: tail).Nodup := hlist ▸ hfiltered
        intro heq
        exact (List.nodup_cons.mp hnd').1
          (heq.symm ▸ (List.mem_cons_self : b ∈ b :: tail))
      rcases hthree q a b c ⟨haB, ha.2⟩ ⟨hbB, hb.2⟩ ⟨hcB, hcq⟩ with
        heq | heq | heq
      · exact False.elim (hab heq)
      · exact False.elim (hac heq)
      · exact False.elim (hbc heq)

def allowed (ridgeList : Fin n → List (Fin r))
    (compatible : Fin n → Fin n → Bool) (kind : Fin n → Nat)
    (quota : Nat → Nat) (S : List (Fin n)) (c : Fin n) : Bool :=
  (decide (kindCount kind S (kind c) < quota (kind c)) &&
    S.all (fun a => compatible a c)) &&
    (ridgeList c).all fun q =>
      decide ((S.filter fun a => has (ridgeList a) q).length < 2)

/-- These explicit hypotheses are independently available for a convex boundary.
In particular, this theorem assumes no search completeness or rationality claim. -/
theorem preservesTarget (ridgeList : Fin n → List (Fin r))
    (compatible : Fin n → Fin n → Bool) (kind : Fin n → Nat)
    (quota : Nat → Nat) (B : List (Fin n))
    (hquota : ∀ k, kindCount kind B k ≤ quota k)
    (hcompatible : ∀ a b, a ∈ B → b ∈ B → a ≠ b → compatible a b = true)
    (hthree : NoThree (fun c => has (ridgeList c)) (family B)) :
    SparseGrowthDAG.PreservesTarget
      (allowed ridgeList compatible kind quota) (family B) := by
  intro S hsub hnd c hcB hcS
  have hsub' : S ⊆ B := by
    intro a ha
    exact (has_true B a).mp (hsub a ((has_true S a).mpr ha))
  have hcB' : c ∈ B := (has_true B c).mp hcB
  have hcS' : c ∉ S := by
    intro hc
    exact Bool.noConfusion (hcS.symm.trans ((has_true S c).mpr hc))
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply Bool.and_eq_true_iff.mpr
    constructor
    · exact decide_eq_true (Nat.lt_of_lt_of_le
        (kindCount_lt kind S B c hnd hsub' hcB' hcS') (hquota (kind c)))
    · apply List.all_eq_true.mpr
      intro a ha
      exact hcompatible a c (hsub' ha) hcB' (fun h => hcS' (h ▸ ha))
  · apply List.all_eq_true.mpr
    intro q hq
    exact decide_eq_true (ridgeCount_lt_two (fun a => has (ridgeList a))
      (family B) S c q hthree hsub hnd hcB hcS ((has_true _ _).mpr hq))

#print axioms preservesTarget

end Papers.RationalityTen.GrowthPruning
