module
prelude
public import FacetSat

@[expose] public section

/-!
# Counting incompatible facet classes

A boundary can contain at most one facet from a class of pairwise
incompatible candidates.  Consequently its number of facets of one kind
equals the number of occupied classes.  This lets a certificate count a
small quotient of the candidate set while preserving the exact quota.

The partition and incompatibilities are checked here.  Coloring heuristics
and the SAT encoding which use them are not trusted.
-/

namespace Papers.RationalityTen.FacetSat

open GrowthPruning

variable {n r : Nat}

structure Grouping (n : Nat) where
  count : Nat
  members : Nat → List (Fin n)
  color : Fin n → Nat

namespace Grouping

def selected (G : Grouping n) (S : List (Fin n)) (g : Nat) : Prop :=
  (G.members g).any (fun c => decide (c ∈ S)) = true

instance (G : Grouping n) (S : List (Fin n)) : DecidablePred (G.selected S) :=
  fun g => inferInstanceAs
    (Decidable ((G.members g).any (fun c => decide (c ∈ S)) = true))

def check (G : Grouping n) (kind : Fin n → Nat)
    (relation : Fin n → Fin n → Bool) (key : Nat) : Bool :=
  ((List.finRange n).all fun c =>
    if kind c = key then
      decide (G.color c < G.count) && decide (c ∈ G.members (G.color c))
    else true) &&
  (List.range G.count).all fun g =>
    (G.members g).all fun a =>
      decide (kind a = key) && decide (G.color a = g) &&
        (G.members g).all fun b => decide (a = b) || !relation a b

theorem selected_iff (G : Grouping n) (S : List (Fin n)) (g : Nat) :
    G.selected S g ↔ ∃ c, c ∈ G.members g ∧ c ∈ S := by
  simp only [selected, List.any_eq_true, decide_eq_true_eq]

theorem group_take (G : Grouping n) (S : List (Fin n)) (g : Nat)
    (c : Fin n) (hc : c ∈ G.members g) :
    c ∈ S → (G.selected S g → False) → False := by
  intro hs hn
  exact hn ((G.selected_iff S g).mpr ⟨c, hc, hs⟩)

theorem group_or (G : Grouping n) (S : List (Fin n)) (g : Nat) :
    G.selected S g → (∀ c ∈ G.members g, c ∈ S → False) → False := by
  intro hs hn
  obtain ⟨c, hc, hS⟩ := (G.selected_iff S g).mp hs
  exact hn c hc hS

theorem checked_cover (G : Grouping n) (kind : Fin n → Nat)
    (relation : Fin n → Fin n → Bool) (key : Nat)
    (hcheck : G.check kind relation key = true) (c : Fin n)
    (hkind : kind c = key) :
    G.color c < G.count ∧ c ∈ G.members (G.color c) := by
  have h := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hcheck).1 c
    (List.mem_finRange c)
  simpa only [hkind, ite_true, Bool.and_eq_true, decide_eq_true_eq] using h

theorem checked_member (G : Grouping n) (kind : Fin n → Nat)
    (relation : Fin n → Fin n → Bool) (key : Nat)
    (hcheck : G.check kind relation key = true)
    (g : Nat) (hg : g < G.count) (c : Fin n) (hc : c ∈ G.members g) :
    kind c = key ∧ G.color c = g := by
  have h := List.all_eq_true.mp
    (List.all_eq_true.mp (Bool.and_eq_true_iff.mp hcheck).2 g (List.mem_range.mpr hg))
    c hc
  have h := (Bool.and_eq_true_iff.mp h).1
  simpa only [Bool.and_eq_true, decide_eq_true_eq] using h

theorem checked_incompatible (G : Grouping n) (kind : Fin n → Nat)
    (relation : Fin n → Fin n → Bool) (key : Nat)
    (hcheck : G.check kind relation key = true)
    (g : Nat) (hg : g < G.count) (a b : Fin n)
    (ha : a ∈ G.members g) (hb : b ∈ G.members g) (hab : a ≠ b) :
    relation a b = false := by
  have h := List.all_eq_true.mp
    (List.all_eq_true.mp (Bool.and_eq_true_iff.mp hcheck).2 g (List.mem_range.mpr hg))
    a ha
  have h := List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2 b hb
  simpa only [hab, decide_false, Bool.false_or, Bool.not_eq_true'] using h

end Grouping

namespace Boundary

variable {kind : Fin n → Nat} {relation : Fin n → Fin n → Bool}
  {ridges : Fin n → Fin r → Bool} {quota : Nat → Nat} {S : List (Fin n)}

theorem group_count (H : Boundary kind relation ridges quota S)
    (G : Grouping n) (key : Nat) (hcheck : G.check kind relation key = true) :
    SequentialCounter.selectedCount (G.selected S) (List.range G.count) = quota key := by
  let B := S.filter (fun c => decide (kind c = key))
  have hm (c : Fin n) : c ∈ B ↔ c ∈ S ∧ kind c = key := by
    simp only [B, List.mem_filter, decide_eq_true_eq]
  have hn : (B.map G.color).Nodup := by
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp_of_mem (p := List.Pairwise.filter _ H.nodup)
    intro a b ha hb hab hcolor
    obtain ⟨haS, hak⟩ := (hm a).mp ha
    obtain ⟨hbS, hbk⟩ := (hm b).mp hb
    obtain ⟨hag, ham⟩ := G.checked_cover kind relation key hcheck a hak
    obtain ⟨_, hbm⟩ := G.checked_cover kind relation key hcheck b hbk
    rw [← hcolor] at hbm
    have hbad := G.checked_incompatible kind relation key hcheck (G.color a) hag
      a b ham hbm hab
    exact Bool.noConfusion ((H.pairwise a haS b hbS hab).symm.trans hbad)
  have hp : ((List.range G.count).filter (fun g => decide (G.selected S g))).Perm
      (B.map G.color) := by
    apply (List.perm_ext_iff_of_nodup
      (List.Pairwise.filter _ (List.nodup_range (n := G.count))) hn).mpr
    intro g
    constructor
    · intro hg
      obtain ⟨hg, hs⟩ := List.mem_filter.mp hg
      obtain ⟨c, hc, hS⟩ := (G.selected_iff S g).mp (of_decide_eq_true hs)
      obtain ⟨hk, hcolor⟩ := G.checked_member kind relation key hcheck g
        (List.mem_range.mp hg) c hc
      exact List.mem_map.mpr ⟨c, (hm c).mpr ⟨hS, hk⟩, hcolor⟩
    · intro hg
      obtain ⟨c, hc, hcolor⟩ := List.mem_map.mp hg
      obtain ⟨hS, hk⟩ := (hm c).mp hc
      obtain ⟨hlt, hmember⟩ := G.checked_cover kind relation key hcheck c hk
      rw [hcolor] at hlt hmember
      exact List.mem_filter.mpr ⟨List.mem_range.mpr hlt,
        decide_eq_true ((G.selected_iff S g).mpr ⟨c, hmember, hS⟩)⟩
  exact hp.length_eq.trans ((List.length_map G.color (as := B)).trans (H.exactQuota key))

end Boundary
end Papers.RationalityTen.FacetSat
