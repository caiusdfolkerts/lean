module

public import Papers.GraphicalZonotopes.ThreeTreeCliques
public import Papers.GraphicalZonotopes.TetrahedralCardinality
public import Papers.GraphicalZonotopes.RefinedSupport

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
open RefinedTriangleComponents

/-- Lemma9.2 in coefficient form, with the ambient graph allowed to be any
3-tree containing the actual directions. Full dimension and indecomposability
force every one of its tetrahedral coefficients to be nonzero. -/
theorem threeTree_all_tetrahedra_nonzero {n : ℕ} (hn : 4≤n)
    {G : SimpleGraph (Fin n)} (hG : IsThreeTree G)
    {z : SetFunction (Fin n)} (hz : ExtremeSupermodular z)
    (hgraph : Graphical G z)
    (hfull : Module.finrank ℝ (vectorSpan ℝ (basePolytope z))=n-1) :
    family (mobius z)=tetrahedra G ∧
      ∀ C∈tetrahedra G,mobius z C≠0 := by
  classical
  obtain ⟨hne,hconn,hcover,hactual⟩ :=
    full_refined_support hn hG.cliqueFree_five hz hgraph hfull
  have hy : CliqueSupported G (mobius z) :=
    (mobius_cliqueSupported_iff G z).mpr ⟨hz.1,hgraph⟩
  have hsub : family (mobius z)⊆tetrahedra G := by
    intro C hC
    obtain ⟨hfour,hnonzero⟩ := (mem_family (mobius z) C).mp hC
    apply mem_filter.mpr
    refine ⟨mem_univ _,hfour,?_⟩
    intro u hu v hv huv
    by_contra hnot
    exact hnonzero (hy.2.2 C u v hu hv huv hnot)
  have hbound := connected_tetrahedra_union_card (family (mobius z)) hne
    (fun C hC => ((mem_family (mobius z) C).mp hC).1) hconn
  rw [hcover,card_univ,Fintype.card_fin] at hbound
  have hcount : (tetrahedra G).card=n-3 := by
    simpa only [card_univ,Fintype.card_fin] using hG.tetrahedra_card
  have he : family (mobius z)=tetrahedra G :=
    eq_of_subset_of_card_le hsub (by omega)
  refine ⟨he,?_⟩
  intro C hC
  exact ((mem_family (mobius z) C).mp (he.symm ▸ hC)).2

end GraphicalZonotopes
