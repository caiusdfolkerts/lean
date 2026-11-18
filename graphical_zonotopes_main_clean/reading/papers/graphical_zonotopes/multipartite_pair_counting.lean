module

public import Papers.GraphicalZonotopes.SmallCountModules
public import Mathlib.Data.Finset.Prod

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
namespace SmallCount
open Finset
open scoped BigOperators Classical
variable {H : Type*} [Fintype H] [LinearOrder H]

def blockUnion (blocks : Finset (Finset H)) : Finset H:=blocks.biUnion id

@[simp] theorem mem_blockUnion (blocks : Finset (Finset H)) (x : H) :
    x∈blockUnion blocks ↔ ∃ B∈blocks,x∈B := by
  simp only [blockUnion,mem_biUnion,id_eq]

def orderedPairs (U : Finset H) : Finset (H×H):=
  (U×ˢU).filter (fun p => p.1<p.2)

@[simp] theorem mem_orderedPairs (U : Finset H) (p : H×H) :
    p∈orderedPairs U ↔ p.1∈U ∧ p.2∈U ∧ p.1<p.2 := by
  simp only [orderedPairs,mem_filter,mem_product,and_assoc]

theorem orderedPairs_card (U : Finset H) :
    (orderedPairs U).card=U.card.choose 2 := card_product_filter_lt

def completePairEquiv : OrientedEdge (⊤ : SimpleGraph H)≃↥(orderedPairs (univ : Finset H)) where
  toFun e:=⟨e.1,(mem_orderedPairs _ _).mpr ⟨mem_univ _,mem_univ _,e.2.1⟩⟩
  invFun p:=⟨p.1,((mem_orderedPairs _ _).mp p.2).2.2,
    (SimpleGraph.top_adj _ _).mpr (ne_of_lt ((mem_orderedPairs _ _).mp p.2).2.2)⟩
  left_inv _:=rfl
  right_inv _:=rfl

theorem completePair_card :
    Fintype.card (OrientedEdge (⊤ : SimpleGraph H))=(Fintype.card H).choose 2 := by
  rw [Fintype.card_congr completePairEquiv,Fintype.card_coe,orderedPairs_card,card_univ]

def crossingPairValues (blocks : Finset (Finset H)) : Finset (H×H):=
  (orderedPairs (blockUnion blocks)).filter (fun p => Crosses blocks p.1 p.2)

@[simp] theorem mem_crossingPairValues (blocks : Finset (Finset H)) (p : H×H) :
    p∈crossingPairValues blocks ↔ p∈orderedPairs (blockUnion blocks) ∧
      Crosses blocks p.1 p.2 := by
  simp only [crossingPairValues,mem_filter]

theorem crossingPairs_card_values (blocks : Finset (Finset H)) :
    (crossingPairs blocks).card=(crossingPairValues blocks).card := by
  apply card_bij (fun e _ => e.1)
  · intro e he
    have hcross:=(mem_crossingPairs blocks e).mp he
    obtain ⟨A,hA,B,hB,hAB,hu,hv⟩:=hcross
    exact (mem_crossingPairValues blocks _).mpr ⟨(mem_orderedPairs _ _).mpr
      ⟨(mem_blockUnion blocks _).mpr ⟨A,hA,hu⟩,
        (mem_blockUnion blocks _).mpr ⟨B,hB,hv⟩,e.2.1⟩,
      ⟨A,hA,B,hB,hAB,hu,hv⟩⟩
  · intro e he f hf hef
    exact Subtype.ext hef
  · intro p hp
    have hp' := (mem_crossingPairValues blocks p).mp hp
    have ht:=(mem_orderedPairs _ _).mp hp'.1
    let e : OrientedEdge (⊤ : SimpleGraph H):=
      ⟨p,ht.2.2,(SimpleGraph.top_adj _ _).mpr (ne_of_lt ht.2.2)⟩
    exact ⟨e,(mem_crossingPairs blocks e).mpr hp'.2,rfl⟩

theorem orderedPairs_partition (blocks : Finset (Finset H)) :
    orderedPairs (blockUnion blocks)=crossingPairValues blocks∪blocks.biUnion orderedPairs := by
  ext p
  constructor
  · intro hp
    obtain ⟨hu,hv,hlt⟩:=(mem_orderedPairs _ _).mp hp
    obtain ⟨A,hA,huA⟩:=(mem_blockUnion blocks _).mp hu
    obtain ⟨B,hB,hvB⟩:=(mem_blockUnion blocks _).mp hv
    by_cases hAB : A=B
    · subst B
      exact mem_union_right _ (mem_biUnion.mpr ⟨A,hA,
        (mem_orderedPairs _ _).mpr ⟨huA,hvB,hlt⟩⟩)
    · exact mem_union_left _ ((mem_crossingPairValues blocks p).mpr ⟨hp,⟨A,hA,B,hB,hAB,huA,hvB⟩⟩)
  · intro hp
    rcases mem_union.mp hp with hc | hi
    · exact ((mem_crossingPairValues blocks p).mp hc).1
    · obtain ⟨A,hA,hpA⟩:=mem_biUnion.mp hi
      obtain ⟨hu,hv,hlt⟩:=(mem_orderedPairs _ _).mp hpA
      exact (mem_orderedPairs _ _).mpr
        ⟨(mem_blockUnion blocks _).mpr ⟨A,hA,hu⟩,
          (mem_blockUnion blocks _).mpr ⟨A,hA,hv⟩,hlt⟩

theorem crossing_internal_disjoint (blocks : Finset (Finset H))
    (hd : ∀ A∈blocks,∀ B∈blocks,A≠B → Disjoint A B) :
    Disjoint (crossingPairValues blocks) (blocks.biUnion orderedPairs) := by
  apply disjoint_left.mpr
  intro p hc hi
  obtain ⟨A,hA,B,hB,hAB,huA,hvB⟩:=((mem_crossingPairValues blocks p).mp hc).2
  obtain ⟨C,hC,hpC⟩:=mem_biUnion.mp hi
  obtain ⟨huC,hvC,_⟩:=(mem_orderedPairs _ _).mp hpC
  have hAC : A=C := by
    by_contra hn
    exact (disjoint_left.mp (hd A hA C hC hn)) huA huC
  have hBC : B=C := by
    by_contra hn
    exact (disjoint_left.mp (hd B hB C hC hn)) hvB hvC
  exact hAB (hAC.trans hBC.symm)

theorem internalPairs_pairwiseDisjoint (blocks : Finset (Finset H))
    (hd : ∀ A∈blocks,∀ B∈blocks,A≠B → Disjoint A B) :
    (blocks : Set (Finset H)).PairwiseDisjoint orderedPairs := by
  intro A hA B hB hAB
  apply disjoint_left.mpr
  intro p hpA hpB
  exact (disjoint_left.mp (hd A hA B hB hAB))
    ((mem_orderedPairs A p).mp hpA).1 ((mem_orderedPairs B p).mp hpB).1

/-- This count is for the literal ordered representatives of the unordered
crossing pairs. Every pair of active vertices is either crossing or belongs
to one uniquely determined part. -/
theorem crossingPairs_card_formula (blocks : Finset (Finset H))
    (hd : ∀ A∈blocks,∀ B∈blocks,A≠B → Disjoint A B) :
    (crossingPairs blocks).card=(blockUnion blocks).card.choose 2-
      ∑ B∈blocks,B.card.choose 2 := by
  have he:=congrArg Finset.card (orderedPairs_partition blocks)
  rw [orderedPairs_card,card_union_of_disjoint (crossing_internal_disjoint blocks hd),
    card_biUnion (internalPairs_pairwiseDisjoint blocks hd)] at he
  simp only [orderedPairs_card] at he
  rw [crossingPairs_card_values]
  omega

theorem crossingPairs_nonempty_gives_two (blocks : Finset (Finset H))
    (hp : (crossingPairs blocks).Nonempty) : 2≤blocks.card := by
  obtain ⟨e,he⟩:=hp
  obtain ⟨A,hA,B,hB,hAB,_,_⟩:=(mem_crossingPairs blocks e).mp he
  exact (one_lt_card.mpr ⟨A,hA,B,hB,hAB⟩)

end SmallCount
end BooleanModule
end GraphicalZonotopes
