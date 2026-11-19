module

public import Papers.GraphicalZonotopes.BookDimensionUpper
public import Papers.GraphicalZonotopes.BoundaryInducedCounting

/-! # Full-dimensional separator bounds on arbitrary finite vertex types

These are the separator consequences used for the sharp actual-direction
bound in Theorem 7.12. The private pieces are genuine Möbius-coordinate
blocks, and the boundary is the induced graph, including missing edges.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.Separator
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V J : Type*} [Fintype V] [LinearOrder V] [Fintype J] [DecidableEq J]
local instance : DecidableEq V := LinearOrder.toDecidableEq
variable {G : SimpleGraph V} {B : Finset V} {A : J → Finset V}

/-- Full dimension makes every nonempty private piece active. -/
theorem private_block_nonzero_full (hn : 2 ≤ Fintype.card V) (h : Partition G B A)
    (z : graphicalFunctionSpace G) (hz : Supermodular z.1)
    (hd : FullDimension (basePolytope z.1)) (j : J) (hAj : (A j).Nonempty) :
    ((functionEquiv h).symm z).2 j ≠ 0 := by
  intro hzero
  obtain ⟨v,hvj⟩ := hAj
  have hvB : v ∉ B := fun hvB =>
    disjoint_left.mp (h.boundary_disjoint j) hvB hvj
  have hy := (mobius_cliqueSupported_iff G z.1).mpr z.2
  have hkill : ∀ C : Finset V,v ∈ C → mobius z.1 C = 0 := by
    intro C hvC
    by_cases hC : IsCliqueCoordinate G C
    · have hCB : ¬C ⊆ B := fun hCB => hvB (hCB hvC)
      obtain ⟨k,hCk,hunique⟩ := h.clique_unique_branch ⟨C,hC⟩ hCB
      have hvk : v ∈ A k := (mem_union.mp (hCk hvC)).resolve_left hvB
      have hkj : k = j := by
        by_contra hkj
        exact disjoint_left.mp (h.private_disjoint hkj) hvk hvj
      subst k
      let D : privateIndex G B A j := ⟨⟨C,hC⟩,hCB,hCk⟩
      have he := congrFun hzero D
      exact (private_coordinate_eq_mobius h z j D).symm.trans he
    · exact coefficient_zero_of_not_clique hy C hC
  have hdep : DependsOn z.1 (univ.erase v) := by
    rw [← zeta_mobius z.1]
    apply zeta_dependsOn
    intro C hC
    apply hkill C
    by_contra hvC
    apply hC
    intro w hw
    exact mem_erase.mpr ⟨fun he => hvC (he ▸ hw),mem_univ _⟩
  have hb := finrank_vectorSpan_le_support z.2.1 hz hdep
  rw [card_erase_of_mem (mem_univ v),card_univ] at hb
  change Module.finrank ℝ (vectorSpan ℝ (basePolytope z.1)) = Fintype.card V-1 at hd
  rw [hd] at hb
  omega

theorem full_partition_capacity (hn : 2 ≤ Fintype.card V) (h : Partition G B A)
    (hA : ∀ j,(A j).Nonempty) (z : graphicalFunctionSpace G)
    (hz : ExtremeSupermodular z.1) (hd : FullDimension (basePolytope z.1)) :
    Fintype.card J ≤ Fintype.card (BoundaryRow G B) - Fintype.card (boundaryIndex G B) + 1 := by
  let x := (functionEquiv h).symm z
  have hactive : ∀ j,x.2 j ≠ 0 := fun j =>
    private_block_nonzero_full hn h z hz.2.1 hd j (hA j)
  let e : Gluing.ActiveBranch x.2 ≃ J := {
    toFun := Subtype.val
    invFun := fun j => ⟨j,hactive j⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hb := separator_capacity_for_function h z hz
  rw [←boundaryRow_card,←boundaryIndex_card] at hb
  exact (Fintype.card_congr e).symm ▸ hb

theorem full_partition_clique_capacity (hn : 2 ≤ Fintype.card V) (h : Partition G B A)
    (hA : ∀ j,(A j).Nonempty) (hB : G.IsClique B)
    (z : graphicalFunctionSpace G) (hz : ExtremeSupermodular z.1)
    (hd : FullDimension (basePolytope z.1)) : Fintype.card J ≤ cliqueCapacity B.card := by
  have hb := full_partition_capacity hn h hA z hz hd
  rw [boundaryRow_card_of_clique hB,boundaryIndex_card,boundaryCliques_card_of_clique hB] at hb
  exact hb

/-- A proper induced boundary has strictly smaller capacity than the clique
on the same boundary vertices. -/
theorem proper_boundary_capacity_lt (G : SimpleGraph V) (B : Finset V)
    (hB : 3 ≤ B.card) (hnclique : ¬G.IsClique B) :
    Fintype.card (BoundaryRow G B) - Fintype.card (boundaryIndex G B) + 1 <
      cliqueCapacity B.card := by
  rw [boundaryIndex_card]
  exact boundary_capacity_lt_of_not_clique G B hB hnclique

end GraphicalZonotopes.Separator
