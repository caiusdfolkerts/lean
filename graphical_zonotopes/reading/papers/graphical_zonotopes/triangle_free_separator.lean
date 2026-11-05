module

public import Papers.GraphicalZonotopes.SeparatorFullDimension
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace Separator
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} {B : Finset V}

/-- The induced boundary contains no triangle. This is expressed directly in
the ambient graph so the vertices outside the boundary are irrelevant. -/
def TriangleFreeBoundary (G : SimpleGraph V) (B : Finset V) : Prop :=
  ∀ T : Finset V, T ⊆ B → T.card = 3 → ¬G.IsClique T

theorem commonNeighbors_boundary_eq_empty (hB : TriangleFreeBoundary G B)
    (e : BoundaryEdge G B) : commonNeighbors G e.1.1.1 e.1.1.2 ∩ B = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro w hw
  obtain ⟨hwN,hwB⟩ := mem_inter.mp hw
  obtain ⟨huw,hvw⟩ := (mem_commonNeighbors G _ _ w).mp hwN
  have ht := (SimpleGraph.is3Clique_triple_iff (G := G)).mpr ⟨e.1.2.2,huw,hvw⟩
  exact hB {e.1.1.1,e.1.1.2,w}
    (by simp only [insert_subset_iff,singleton_subset_iff]; exact ⟨e.2.1,e.2.2,hwB⟩)
    ht.card_eq ht.isClique

def boundaryEdgeClique (e : BoundaryEdge G B) : ↥(boundaryCliques G B) :=
  ⟨{e.1.1.1,e.1.1.2},by
    apply mem_filter.mpr
    refine ⟨mem_powerset.mpr ?_,?_,?_⟩
    · exact insert_subset e.2.1 (singleton_subset_iff.mpr e.2.2)
    · simp [card_pair (ne_of_lt e.1.2.1)]
    · simpa only [Finset.coe_pair] using
        (SimpleGraph.isClique_pair).mpr (fun _ => e.1.2.2)⟩

theorem boundaryEdgeClique_injective :
    Function.Injective (boundaryEdgeClique (G := G) (B := B)) := by
  intro e f hef
  have he : ({e.1.1.1,e.1.1.2} : Finset V) = {f.1.1.1,f.1.1.2} :=
    congrArg Subtype.val hef
  have h₁ : e.1.1.1 = f.1.1.1 ∨ e.1.1.1 = f.1.1.2 := by
    have hh : e.1.1.1 ∈ ({f.1.1.1,f.1.1.2} : Finset V) := by rw [← he]; simp
    simpa only [mem_insert,mem_singleton] using hh
  have h₂ : e.1.1.2 = f.1.1.1 ∨ e.1.1.2 = f.1.1.2 := by
    have hh : e.1.1.2 ∈ ({f.1.1.1,f.1.1.2} : Finset V) := by rw [← he]; simp
    simpa only [mem_insert,mem_singleton] using hh
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · rcases h₁ with h₁ | h₁
    · exact h₁
    · rcases h₂ with h₂ | h₂
      · exact False.elim (lt_asymm e.1.2.1 (by simpa only [h₁,h₂] using f.1.2.1))
      · exact False.elim ((ne_of_lt e.1.2.1) (h₁.trans h₂.symm))
  · rcases h₂ with h₂ | h₂
    · rcases h₁ with h₁ | h₁
      · exact False.elim ((ne_of_lt e.1.2.1) (h₁.trans h₂.symm))
      · exact False.elim (lt_asymm e.1.2.1 (by simpa only [h₁,h₂] using f.1.2.1))
    · exact h₂

/-- A triangle-free boundary has at most one active private block. This is
the exact specialization of Lemma 5.1 used in Corollary 5.2. -/
theorem triangle_free_boundary_capacity (hB : TriangleFreeBoundary G B)
    (z : graphicalFunctionSpace G) (hz : ExtremeSupermodular z.1) :
    Fintype.card (Gluing.ActiveBranch
      (((functionEquiv (componentPartition G B)).symm z).2)) ≤ 1 := by
  have hc := induced_separator_capacity G B z hz
  have hsum : (∑ e : BoundaryEdge G B,
      2^(commonNeighbors G e.1.1.1 e.1.1.2 ∩ B).card) = Fintype.card (BoundaryEdge G B) := by
    simp only [commonNeighbors_boundary_eq_empty hB,card_empty,pow_zero,sum_const,
      card_univ,smul_eq_mul,mul_one]
  have hcard : Fintype.card (BoundaryEdge G B) ≤ (boundaryCliques G B).card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective
      (boundaryEdgeClique (G := G) (B := B)) boundaryEdgeClique_injective
  rw [hsum,Nat.sub_eq_zero_of_le hcard,zero_add] at hc
  exact hc

end Separator

open Finset

/-- Corollary 5.2: deleting a triangle-free boundary leaves at most one
component whenever a full-dimensional indecomposable weak summand exists. -/
theorem SupportsFullIndecomposable.triangle_free_components_le_one {n : ℕ} (hn : 2 ≤ n)
    {G : SimpleGraph (Fin n)} (hG : SupportsFullIndecomposable G)
    (B : Finset (Fin n)) (hB : Separator.TriangleFreeBoundary G B) :
    Nat.card ((G.induce ((B : Set (Fin n))ᶜ)).ConnectedComponent) ≤ 1 := by
  classical
  obtain ⟨z,hz,hd⟩ := hG.exists_extreme_function hn
  let x := (Separator.functionEquiv (Separator.componentPartition G B)).symm z
  have ha : ∀ j,x.2 j ≠ 0 := fun j =>
    Separator.private_block_ne_zero_of_fullDimension hn (Separator.componentPartition G B)
      z hz.2.1 hd j (Separator.componentPart_nonempty G B j)
  let e : Gluing.ActiveBranch x.2 ≃ (Separator.outsideGraph G B).ConnectedComponent := {
    toFun := Subtype.val
    invFun := fun j => ⟨j,ha j⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hc := Separator.triangle_free_boundary_capacity hB z hz
  change Fintype.card (Gluing.ActiveBranch x.2) ≤ 1 at hc
  rw [Fintype.card_congr e] at hc
  change Nat.card ((Separator.outsideGraph G B).ConnectedComponent) ≤ 1
  rw [@Nat.card_eq_fintype_card _ (Separator.componentFintype G B)]
  exact hc

/-- The paper's literal conclusion: every set whose deletion disconnects the
graph contains all three vertices of an actual graph triangle. -/
theorem SupportsFullIndecomposable.separator_contains_triangle {n : ℕ} (hn : 2 ≤ n)
    {G : SimpleGraph (Fin n)} (hG : SupportsFullIndecomposable G)
    (B : Finset (Fin n))
    (hsep : 2 ≤ Nat.card ((G.induce ((B : Set (Fin n))ᶜ)).ConnectedComponent)) :
    ∃ T : Finset (Fin n),T ⊆ B ∧ T.card = 3 ∧ G.IsClique T := by
  by_contra h
  have hB : Separator.TriangleFreeBoundary G B := by
    intro T hTB hT hc
    exact h ⟨T,hTB,hT,hc⟩
  have hb := hG.triangle_free_components_le_one hn B hB
  omega

/-- In particular, deleting fewer than three vertices cannot disconnect a
supporting graph. This quantifies over all such vertex sets. -/
theorem SupportsFullIndecomposable.delete_lt_three_preconnected {n : ℕ} (hn : 4 ≤ n)
    {G : SimpleGraph (Fin n)} (hG : SupportsFullIndecomposable G)
    (B : Finset (Fin n)) (hB : B.card < 3) :
    (G.induce ((B : Set (Fin n))ᶜ)).Preconnected := by
  have ht : Separator.TriangleFreeBoundary G B := by
    intro T hTB hT _
    have hc := card_le_card hTB
    omega
  have hc := hG.triangle_free_components_le_one (by omega) B ht
  letI : Subsingleton ((G.induce ((B : Set (Fin n))ᶜ)).ConnectedComponent) :=
    Fintype.card_le_one_iff_subsingleton.mp
      (by simpa only [Nat.card_eq_fintype_card] using hc)
  intro u v
  exact SimpleGraph.ConnectedComponent.exact (Subsingleton.elim _ _)

end GraphicalZonotopes
