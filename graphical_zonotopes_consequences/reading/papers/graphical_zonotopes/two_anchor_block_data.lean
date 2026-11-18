module

public import Papers.GraphicalZonotopes.TwoAnchorConnector
public import Papers.GraphicalZonotopes.BookBlockCoordinates

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators
variable {H : Type*} [Fintype H] [LinearOrder H]

namespace OrderedTriple
variable (T : OrderedTriple H)

def block : BookBlock H := ⟨T.clique,mem_largeBlocks.mpr ⟨subset_univ _,by rw [T.card_clique]⟩⟩

structure OmittedBlock (C : BookBlock H) (r : ℕ)
    extends WeightedPureBlock C.1 2 (twoAnchorTarget C.1 T.a T.b) r where
  first_zero : ∀ j,blockCoordinates C.1 (column j) T.firstRow=0
  second_zero : ∀ j,blockCoordinates C.1 (column j) T.secondRow=0

def ordinaryOmittedBlock (C : BookBlock H) (hne : C.1≠T.clique) {r : ℕ}
    (P : WeightedPureBlock C.1 2 (twoAnchorTarget C.1 T.a T.b) r) : T.OmittedBlock C r := by
  refine { P with first_zero := ?_,second_zero := ?_ }
  · intro j
    have hr : rowClique T.firstRow≠C.1 := by rw [T.firstRow_clique]; exact Ne.symm hne
    change (if h : rowClique T.firstRow=C.1 then P.column j (pairAtRow C.1 T.firstRow h) else 0)=0
    exact dite_eq_right hr
  · intro j
    have hr : rowClique T.secondRow≠C.1 := by rw [T.secondRow_clique]; exact Ne.symm hne
    change (if h : rowClique T.secondRow=C.1 then P.column j (pairAtRow C.1 T.secondRow h) else 0)=0
    exact dite_eq_right hr

def connectorOmittedBlock : T.OmittedBlock T.block 1 where
  toWeightedPureBlock := T.pureBlock
  first_zero := T.pureBlock_first
  second_zero := T.pureBlock_second

def lowerRank (C : BookBlock H) : ℕ :=
  if C.1=T.clique then 1 else
  if T.a∈C.1 ∧ T.b∈C.1 then C.1.card.choose 2-1 else
  if T.a∈C.1 ∨ T.b∈C.1 then 1 else 0

def upperRank (C : BookBlock H) : ℕ :=
  if C.1=T.clique then 1 else
  if T.a∈C.1 ∨ T.b∈C.1 then C.1.card.choose 2-1 else 0

theorem lowerRank_le_upperRank (C : BookBlock H) : T.lowerRank C≤T.upperRank C := by
  have hsize := (mem_largeBlocks.mp C.2).2
  have hc : 1≤C.1.card.choose 2-1 := by
    have h := Nat.choose_le_choose 2 hsize
    norm_num [Nat.choose] at h
    omega
  unfold lowerRank upperRank
  by_cases hC : C.1=T.clique <;> by_cases ha : T.a∈C.1 <;> by_cases hb : T.b∈C.1 <;>
    simp [hC,ha,hb,hc]

/-- Each local branch count in the exact interval is realized, with both
connector test coordinates zero for every pure column. -/
theorem omittedBlock_exists (C : BookBlock H) {r : ℕ}
    (hrlo : T.lowerRank C≤r) (hrhi : r≤T.upperRank C) :
    Nonempty (T.OmittedBlock C r) := by
  classical
  by_cases hC : C.1=T.clique
  · have hCe : C=T.block := Subtype.ext hC
    subst C
    have hr : r=1 := by
      simp only [lowerRank,upperRank,block,ite_true] at hrlo hrhi
      omega
    subst r
    exact ⟨T.connectorOmittedBlock⟩
  · apply Nonempty.map (T.ordinaryOmittedBlock C hC)
    have hsize := (mem_largeBlocks.mp C.2).2
    by_cases ha : T.a∈C.1
    · by_cases hb : T.b∈C.1
      · have hr : r=C.1.card.choose 2-1 := by
          simp only [lowerRank,upperRank,ite_eq_right hC,ha,hb,true_and,true_or,ite_true] at hrlo hrhi
          omega
        subst r
        exact two_anchor_full_pure_block C.1 hsize T.ab ha hb
      · have hlo : 1≤r := by simpa only [lowerRank,ite_eq_right hC,ha,hb,
          true_and,false_or,true_or,ite_false,ite_true] using hrlo
        have hhi : r≤C.1.card.choose 2-1 := by
          simpa only [upperRank,ite_eq_right hC,ha,true_or,ite_true] using hrhi
        exact one_anchor_pure_block C.1 hsize ha hb hlo hhi
    · by_cases hb : T.b∈C.1
      · have hlo : 1≤r := by simpa only [lowerRank,ite_eq_right hC,ha,hb,
          false_and,false_or,ite_false,ite_true] using hrlo
        have hhi : r≤C.1.card.choose 2-1 := by
          simpa only [upperRank,ite_eq_right hC,hb,or_true,ite_true] using hrhi
        rw [twoAnchorTarget_symm]
        exact one_anchor_pure_block C.1 hsize hb ha hlo hhi
      · have hr : r=0 := by
          simpa only [upperRank,ite_eq_right hC,ha,hb,false_or,ite_false,Nat.le_zero] using hrhi
        subst r
        have hz : twoAnchorTarget C.1 T.a T.b=0 := by
          simp only [twoAnchorTarget,starVector_eq_zero_of_notMem C.1 ha,
            starVector_eq_zero_of_notMem C.1 hb,add_zero,map_zero,smul_zero,neg_zero]
        exact ⟨{
          column := fun j => Fin.elim0 j
          realizable := fun j => Fin.elim0 j
          weight := fun j => Fin.elim0 j
          positive := fun j => Fin.elim0 j
          bounded := fun j => Fin.elim0 j
          independent := linearIndependent_empty_type
          weighted_sum := by simpa only [Fin.sum_univ_zero] using hz.symm
        }⟩

end OrderedTriple
end BooleanModule
end GraphicalZonotopes
