module

public import Papers.GraphicalZonotopes.BookCombinatorialCounts

@[expose] public section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators
variable {H : Type*} [DecidableEq H]

def anchorBlocks (S : Finset H) (a : H) : Finset (Finset H) :=
  S.powerset.filter (fun C => a∈C ∧ 3≤C.card)

@[simp] theorem mem_anchorBlocks {S C : Finset H} {a : H} :
    C∈anchorBlocks S a ↔ C⊆S ∧ a∈C ∧ 3≤C.card := by
  simp only [anchorBlocks,mem_filter,mem_powerset]

private theorem nontrivial_erase_notMem (S : Finset H) (a : H)
    {T : Finset H} (hT : T∈nontrivialSubsets (S.erase a)) : a∉T := by
  intro h
  exact (notMem_erase a S) ((mem_powerset.mp (mem_filter.mp hT).1) h)

private theorem insert_anchor_injOn (S : Finset H) (a : H) :
    Set.InjOn (fun T : Finset H => insert a T) (↑(nontrivialSubsets (S.erase a)) : Set (Finset H)) := by
  intro T hT U hU he
  have haT := nontrivial_erase_notMem S a hT
  have haU := nontrivial_erase_notMem S a hU
  have h := congrArg (fun X : Finset H => X.erase a) he
  simpa only [erase_insert haT,erase_insert haU] using h

theorem anchorBlocks_eq_image (S : Finset H) (a : H) (ha : a∈S) :
    anchorBlocks S a=(nontrivialSubsets (S.erase a)).image (insert a) := by
  ext C
  rw [mem_anchorBlocks,mem_image]
  constructor
  · rintro ⟨hCS,haC,hC⟩
    refine ⟨C.erase a,mem_filter.mpr ⟨mem_powerset.mpr ?_,?_⟩,insert_erase haC⟩
    · intro x hx
      exact mem_erase.mpr ⟨(mem_erase.mp hx).1,hCS (mem_of_mem_erase hx)⟩
    · rw [card_erase_of_mem haC]
      omega
  · rintro ⟨T,hT,rfl⟩
    have hTS := mem_powerset.mp (mem_filter.mp hT).1
    have haT := nontrivial_erase_notMem S a hT
    refine ⟨insert_subset_iff.mpr ⟨ha,hTS.trans (erase_subset _ _)⟩,mem_insert_self _ _,?_⟩
    rw [card_insert_of_notMem haT]
    have hc := (mem_filter.mp hT).2
    omega

theorem anchorBlocks_card (S : Finset H) (a : H) (ha : a∈S) :
    (anchorBlocks S a).card=2^(S.card-1)-S.card := by
  rw [anchorBlocks_eq_image S a ha,card_image_of_injOn (insert_anchor_injOn S a),
    nontrivialSubsets_card,card_erase_of_mem ha]
  have hs : 1≤S.card := card_pos.mpr ⟨a,ha⟩
  omega

theorem blockDimensionSum_erase_add_anchor (S : Finset H) (a : H) (ha : a∈S) :
    blockDimensionSum (S.erase a)+
      (∑ C∈anchorBlocks S a,(C.card.choose 2-1))=blockDimensionSum S := by
  have hsum : (∑ C∈anchorBlocks S a,(C.card.choose 2-1))=
      ∑ T∈(S.erase a).powerset,((insert a T).card.choose 2-1) := by
    rw [anchorBlocks_eq_image S a ha,sum_image (insert_anchor_injOn S a)]
    apply sum_subset (filter_subset _ _)
    intro T hT hn
    have haT : a∉T := fun h => (notMem_erase a S) ((mem_powerset.mp hT) h)
    have hsmall : ¬2≤T.card := fun h => hn (mem_filter.mpr ⟨hT,h⟩)
    have hcases : T.card=0 ∨ T.card=1 := by omega
    rw [card_insert_of_notMem haT]
    rcases hcases with h | h <;> norm_num [h,Nat.choose]
  rw [hsum]
  conv_rhs => rw [← insert_erase ha]
  unfold blockDimensionSum
  rw [sum_powerset_insert (notMem_erase a S)]

theorem anchorBlocks_dimension_sum (S : Finset H) (a : H) (ha : a∈S) :
    (∑ C∈anchorBlocks S a,(C.card.choose 2-1))=
      cliqueCapacity S.card-cliqueCapacity (S.card-1) := by
  have h := blockDimensionSum_erase_add_anchor S a ha
  have hc := cliqueCapacity_eq_dimension_sum S
  have hd := cliqueCapacity_eq_dimension_sum (S.erase a)
  rw [card_erase_of_mem ha] at hd
  omega

end BooleanModule
end GraphicalZonotopes
