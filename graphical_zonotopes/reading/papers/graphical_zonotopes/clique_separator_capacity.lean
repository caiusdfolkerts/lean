module

public import Papers.GraphicalZonotopes.SeparatorTheorems
public import Papers.GraphicalZonotopes.GraphModels
public import Mathlib.Data.Finset.Prod

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace Separator
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [LinearOrder V]
local instance : DecidableEq V := LinearOrder.toDecidableEq
variable {G : SimpleGraph V} {B : Finset V}

/-- A boundary edge is exactly one strictly ordered pair in the boundary clique.
The order is used only to count each unordered edge once. -/
def cliqueBoundaryEdgeEquiv (hB : G.IsClique B) :
    BoundaryEdge G B ≃ ↥((B ×ˢ B).filter (fun p : V × V => p.1 < p.2)) where
  toFun e := ⟨e.1.1,mem_filter.mpr ⟨mem_product.mpr e.2,e.1.2.1⟩⟩
  invFun p := ⟨⟨p.1,(mem_filter.mp p.2).2,
      hB ((mem_product.mp (mem_filter.mp p.2).1).1)
        ((mem_product.mp (mem_filter.mp p.2).1).2)
        (ne_of_lt (mem_filter.mp p.2).2)⟩,
      mem_product.mp (mem_filter.mp p.2).1⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem boundaryEdge_card_of_clique (hB : G.IsClique B) :
    Fintype.card (BoundaryEdge G B)=B.card.choose 2 := by
  rw [Fintype.card_congr (cliqueBoundaryEdgeEquiv hB),Fintype.card_coe]
  convert Finset.card_product_filter_lt (s := B) using 2 <;> congr 1

/-- Within a clique, the common neighbors of an edge are all boundary vertices
except its two endpoints, including every unused conditioning bit. -/
theorem boundary_commonNeighbors_of_clique (hB : G.IsClique B)
    {u v : V} (hu : u∈B) (hv : v∈B) (huv : u≠v) :
    commonNeighbors G u v∩B=(B.erase u).erase v := by
  ext w
  simp only [mem_inter,mem_commonNeighbors,mem_erase]
  constructor
  · rintro ⟨⟨huw,hvw⟩,hw⟩
    exact ⟨(G.ne_of_adj hvw).symm,(G.ne_of_adj huw).symm,hw⟩
  · rintro ⟨hwv,hwu,hw⟩
    exact ⟨⟨hB hu hw hwu.symm,hB hv hw hwv.symm⟩,hw⟩

theorem boundary_commonNeighbors_card_of_clique (hB : G.IsClique B)
    {u v : V} (hu : u∈B) (hv : v∈B) (huv : u≠v) :
    (commonNeighbors G u v∩B).card=B.card-2 := by
  rw [boundary_commonNeighbors_of_clique hB hu hv huv,
    card_erase_of_mem (mem_erase.mpr ⟨huv.symm,hv⟩),card_erase_of_mem hu]
  omega

theorem boundaryRow_card_of_clique (hB : G.IsClique B) :
    Fintype.card (BoundaryRow G B)=B.card.choose 2*2^(B.card-2) := by
  rw [boundaryRow_card]
  have he : ∀ e : BoundaryEdge G B,
      (commonNeighbors G e.1.1.1 e.1.1.2∩B).card=B.card-2 := by
    intro e
    exact boundary_commonNeighbors_card_of_clique hB e.2.1 e.2.2
      (ne_of_lt e.1.2.1)
  simp_rw [he]
  simp [boundaryEdge_card_of_clique hB,Nat.mul_comm]

private theorem small_subsets_eq :
    B.powerset.filter (fun C => ¬2≤C.card)=insert ∅ (B.image singleton) := by
  ext C
  simp only [mem_filter,mem_powerset,mem_insert,mem_image]
  constructor
  · rintro ⟨hCB,hC⟩
    have hc : C.card=0 ∨ C.card=1 := by omega
    rcases hc with hc | hc
    · exact Or.inl (card_eq_zero.mp hc)
    · obtain ⟨v,rfl⟩ := card_eq_one.mp hc
      exact Or.inr ⟨v,hCB (mem_singleton_self v),rfl⟩
  · rintro (rfl | ⟨v,hv,rfl⟩)
    · simp
    · simp [singleton_subset_iff,hv]

private theorem small_subsets_card :
    (B.powerset.filter (fun C => ¬2≤C.card)).card=B.card+1 := by
  rw [small_subsets_eq,card_insert_of_notMem]
  · rw [card_image_of_injective B singleton_injective]
  · simp

theorem boundaryCliques_card_of_clique (hB : G.IsClique B) :
    (boundaryCliques G B).card=2^B.card-B.card-1 := by
  have he : boundaryCliques G B=B.powerset.filter (fun C => 2≤C.card) := by
    ext C
    simp only [boundaryCliques,mem_filter,mem_powerset,IsCliqueCoordinate]
    constructor
    · rintro ⟨hCB,hC,_⟩
      exact ⟨hCB,hC⟩
    · rintro ⟨hCB,hC⟩
      exact ⟨hCB,hC,fun u hu v hv huv => hB (hCB hu) (hCB hv) huv⟩
  rw [he]
  have hc := card_filter_add_card_filter_not (s := B.powerset) (p := fun C => 2≤C.card)
  rw [small_subsets_card,card_powerset] at hc
  omega

/-- Theorem7.2, with exactly the connected components of the actual graph after
removing the clique. All zero coefficient slots remain in their private blocks;
only genuinely nonzero blocks are counted on the left. -/
theorem clique_separator_capacity (hB : G.IsClique B) (hs : 2≤B.card)
    (z : graphicalFunctionSpace G) (hz : ExtremeSupermodular z.1) :
    Fintype.card (Gluing.ActiveBranch
      (((functionEquiv (componentPartition G B)).symm z).2))≤cliqueCapacity B.card := by
  have h := induced_separator_capacity G B z hz
  rw [←boundaryRow_card,boundaryRow_card_of_clique hB,
    boundaryCliques_card_of_clique hB] at h
  exact h

@[simp] theorem cliqueCapacity_two : cliqueCapacity 2=1 := by norm_num [cliqueCapacity, Nat.choose]
@[simp] theorem cliqueCapacity_three : cliqueCapacity 3=3 := by norm_num [cliqueCapacity, Nat.choose]
@[simp] theorem cliqueCapacity_four : cliqueCapacity 4=14 := by norm_num [cliqueCapacity, Nat.choose]

end Separator
end GraphicalZonotopes
