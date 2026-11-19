module

public import Papers.GraphicalZonotopes.CubeCells

@[expose] public section
noncomputable section
namespace GraphicalZonotopes.TwoHub
open Finset
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A full binary coordinate decision tree rooted at a cube cell. The `fresh`
condition expresses exactly that a coordinate is never tested twice along one
root-to-leaf path. -/
inductive CellDecisionTree : Cell I → Type _ where
  | leaf (C : Cell I) : CellDecisionTree C
  | node (C : Cell I) (i : I) (fresh : i∉C.fixed)
      (zero : CellDecisionTree (C.splitZero i))
      (one : CellDecisionTree (C.splitOne i)) : CellDecisionTree C

namespace CellDecisionTree

def leaves {C : Cell I} : CellDecisionTree C → Finset (Cell I)
  | .leaf C => {C}
  | .node _ _ _ zero one => zero.leaves∪one.leaves

def tested {C : Cell I} : CellDecisionTree C → Finset I
  | .leaf _ => ∅
  | .node _ i _ zero one => insert i (zero.tested∪one.tested)

def leafCount {C : Cell I} : CellDecisionTree C → ℕ
  | .leaf _ => 1
  | .node _ _ _ zero one => zero.leafCount+one.leafCount

theorem leaves_nonempty {C : Cell I} (T : CellDecisionTree C) : T.leaves.Nonempty := by
  induction T with
  | leaf C => exact singleton_nonempty C
  | node C i hi zero one ihz iho => exact ihz.mono subset_union_left

theorem fixed_subset {C : Cell I} (T : CellDecisionTree C) {D : Cell I}
    (hD : D∈T.leaves) : C.fixed⊆D.fixed := by
  induction T with
  | leaf C =>
      have he : D=C := mem_singleton.mp hD
      subst D
      exact Subset.rfl
  | node C i hi zero one ihz iho =>
      rcases mem_union.mp hD with hz|ho
      · exact (subset_insert i C.fixed).trans (ihz hz)
      · exact (subset_insert i C.fixed).trans (iho ho)

theorem matches_parent {C : Cell I} (T : CellDecisionTree C) {D : Cell I}
    (hD : D∈T.leaves) {Y : Finset I} (hY : D.Matches Y) : C.Matches Y := by
  induction T with
  | leaf C =>
      have he : D=C := mem_singleton.mp hD
      exact he ▸ hY
  | node C i hi zero one ihz iho =>
      rcases mem_union.mp hD with hz|ho
      · exact ((C.matches_splitZero i hi Y).mp (ihz hz)).1
      · exact ((C.matches_splitOne i hi Y).mp (iho ho)).1

theorem children_disjoint (C : Cell I) (i : I) (hi : i∉C.fixed)
    (zero : CellDecisionTree (C.splitZero i))
    (one : CellDecisionTree (C.splitOne i)) : Disjoint zero.leaves one.leaves := by
  apply disjoint_left.mpr
  intro D hz ho
  have h0 := (C.matches_splitZero i hi D.ones).mp (zero.matches_parent hz D.matches_ones)
  have h1 := (C.matches_splitOne i hi D.ones).mp (one.matches_parent ho D.matches_ones)
  exact h0.2 h1.2

theorem leaves_card {C : Cell I} (T : CellDecisionTree C) : T.leaves.card=T.leafCount := by
  induction T with
  | leaf C => simp [leaves,leafCount]
  | node C i hi zero one ihz iho =>
      rw [leaves,card_union_of_disjoint (children_disjoint C i hi zero one),ihz,iho]
      rfl

theorem exists_unique_match {C : Cell I} (T : CellDecisionTree C) {Y : Finset I}
    (hY : C.Matches Y) : ∃! D,D∈T.leaves ∧ D.Matches Y := by
  induction T with
  | leaf C =>
      refine ⟨C,⟨mem_singleton_self _,hY⟩,?_⟩
      intro D hD
      exact mem_singleton.mp hD.1
  | node C i hi zero one ihz iho =>
      by_cases hy : i∈Y
      · obtain ⟨D,hD,hu⟩ := iho ((C.matches_splitOne i hi Y).mpr ⟨hY,hy⟩)
        refine ⟨D,⟨mem_union_right _ hD.1,hD.2⟩,?_⟩
        intro E hE
        rcases mem_union.mp hE.1 with hz|ho
        · exact False.elim (((C.matches_splitZero i hi Y).mp
            (zero.matches_parent hz hE.2)).2 hy)
        · exact hu E ⟨ho,hE.2⟩
      · obtain ⟨D,hD,hu⟩ := ihz ((C.matches_splitZero i hi Y).mpr ⟨hY,hy⟩)
        refine ⟨D,⟨mem_union_left _ hD.1,hD.2⟩,?_⟩
        intro E hE
        rcases mem_union.mp hE.1 with hz|ho
        · exact hu E ⟨hz,hE.2⟩
        · exact False.elim (hy ((C.matches_splitOne i hi Y).mp
            (one.matches_parent ho hE.2)).2)

theorem uses_zero {C : Cell I} (T : CellDecisionTree C) :
    CubePartition.UsesZero T.leaves T.tested := by
  induction T with
  | leaf C => intro i hi; simp [tested] at hi
  | node C i hi zero one ihz iho =>
      intro j hj
      rcases mem_insert.mp hj with hji|hj
      · subst j
        obtain ⟨D,hD⟩ := zero.leaves_nonempty
        have hm := (C.matches_splitZero i hi D.ones).mp
          (zero.matches_parent hD D.matches_ones)
        exact ⟨D,mem_union_left _ hD,
          zero.fixed_subset hD (mem_insert_self i C.fixed),hm.2⟩
      · rcases mem_union.mp hj with hz|ho
        · obtain ⟨D,hD,hf,hn⟩ := ihz j hz
          exact ⟨D,mem_union_left _ hD,hf,hn⟩
        · obtain ⟨D,hD,hf,hn⟩ := iho j ho
          exact ⟨D,mem_union_right _ hD,hf,hn⟩

theorem root_valid (T : CellDecisionTree (Cell.root (I:=I))) :
    CubePartition.Valid T.leaves := by
  intro Y
  exact T.exists_unique_match (Cell.root_matches Y)

theorem root_proper [Nonempty I] (T : CellDecisionTree (Cell.root (I:=I)))
    (h : T.tested=univ) : ∀ C∈T.leaves,C.fixed.Nonempty := by
  have ht : T.tested.Nonempty := by rw [h]; exact univ_nonempty
  have hc : 2≤T.leaves.card := by
    cases T with
    | leaf C => simp [tested] at ht
    | node C i hi zero one =>
        rw [leaves,card_union_of_disjoint (children_disjoint Cell.root i hi zero one)]
        have hz := card_pos.mpr zero.leaves_nonempty
        have ho := card_pos.mpr one.leaves_nonempty
        omega
  exact fun C hC => T.root_valid.fixed_nonempty hc hC

end CellDecisionTree
end GraphicalZonotopes.TwoHub
