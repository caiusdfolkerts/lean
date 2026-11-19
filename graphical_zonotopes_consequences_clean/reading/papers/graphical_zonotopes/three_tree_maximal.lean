module

public import Papers.GraphicalZonotopes.ThreeTreeIncidence

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every clique in the active vertex set of a 3-tree extends to an
actual tetrahedron. This includes empty sets, vertices and edges, rather
than only the triangular separators used in the construction. -/
theorem ThreeTreeOn.clique_extends {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {C : Finset V} (hCS : C⊆S) (hC : G.IsClique C) :
    ∃ D∈tetrahedra G,C⊆D := by
  classical
  induction h generalizing C with
  | tetrahedron A hA =>
    exact ⟨A,by rw [tetrahedra_cliqueGraph hA]; simp,hCS⟩
  | @attach S G h u hu A hA hAS hcA ih =>
    by_cases huC : u∈C
    · refine ⟨insert u A,?_,?_⟩
      · rw [tetrahedra_after_attachment h hu hA hAS hcA]
        exact mem_insert_self _ _
      · intro v hv
        by_cases hvu : v=u
        · exact mem_insert.mpr (Or.inl hvu)
        · exact mem_insert.mpr (Or.inr
            ((attached_vertex_adj_iff h hu hAS v).mp (hC huC hv (Ne.symm hvu))))
    · have hCold : C⊆S := by
        intro v hv
        rcases mem_insert.mp (hCS hv) with he | hvS
        · exact False.elim (huC (he ▸ hv))
        · exact hvS
      obtain ⟨D,hD,hCD⟩ := ih hCold (clique_before_attachment huC hC)
      exact ⟨D,by
        rw [tetrahedra_after_attachment h hu hA hAS hcA]
        exact mem_insert_of_mem hD,hCD⟩

/-- In the full 3-tree, the finite tetrahedra used by the coefficient
formalization are exactly the ordinary maximal cliques of the paper. -/
theorem IsThreeTree.maximalClique_iff {G : SimpleGraph V} (h : IsThreeTree G)
    (C : Finset V) : Maximal G.IsClique (C : Set V) ↔ C∈tetrahedra G := by
  classical
  constructor
  · intro hmax
    obtain ⟨D,hD,hCD⟩ := h.clique_extends (subset_univ C) hmax.1
    have hDC : D⊆C := hmax.2 (mem_filter.mp hD).2.2 hCD
    have he : C=D := subset_antisymm hCD hDC
    simpa only [he] using hD
  · intro hC
    obtain ⟨hc,hcl⟩ := (mem_filter.mp hC).2
    apply SimpleGraph.IsMaximumClique.isMaximalClique C
    refine ⟨hcl,?_⟩
    intro D hD
    rw [hc]
    exact h.clique_card_le_four hD

end GraphicalZonotopes
