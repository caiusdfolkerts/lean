module

public import Unimodular.SeriesParallelGraphMinors

/-!
# Exact relabelling of a directed incidence graph

Only edge names change. Deletion, nonloop contraction and the literal
six-edge complete-graph minor are preserved. This supplies the graph
transport needed when primitive fan rays are written in an integral basis.
-/

@[expose] public section
set_option autoImplicit false

namespace Unimodular.SeriesParallel.IncidenceGraph

variable {V E E' : Type*}

def reindex (G : IncidenceGraph V E) (e : E' ≃ E) : IncidenceGraph V E' where
  source := G.source ∘ e
  target := G.target ∘ e
  edges := e ⁻¹' G.edges

theorem eq_of_components {G H : IncidenceGraph V E}
    (hs : G.source = H.source) (ht : G.target = H.target) (he : G.edges = H.edges) :
    G = H := by
  cases G
  cases H
  cases hs
  cases ht
  cases he
  rfl

theorem reindex_delete (G : IncidenceGraph V E) (e : E' ≃ E) (D : Set E) :
    (G.delete D).reindex e = (G.reindex e).delete (e ⁻¹' D) := rfl

theorem reindex_contract (G : IncidenceGraph V E) (e : E' ≃ E) (j : E) :
    (G.contract j).reindex e = (G.reindex e).contract (e.symm j) := by
  apply eq_of_components
  · funext i
    simp [reindex, contract, Function.comp_def]
  · funext i
    simp [reindex, contract, Function.comp_def]
  · ext i
    simp [reindex, contract, e.eq_symm_apply]

theorem reindex_symm (G : IncidenceGraph V E) (e : E' ≃ E) :
    (G.reindex e).reindex e.symm = G := by
  apply eq_of_components
  · funext i
    simp [reindex]
  · funext i
    simp [reindex]
  · ext i
    simp [reindex]

theorem IsMinor.reindex {G H : IncidenceGraph V E} (h : H.IsMinor G) (e : E' ≃ E) :
    (H.reindex e).IsMinor (G.reindex e) := by
  induction h with
  | refl G => exact .refl _
  | @delete G H h D ih =>
    rw [reindex_delete]
    exact .delete ih _
  | @contract G H h j hj hne ih =>
    rw [reindex_contract]
    apply IsMinor.contract ih (e.symm j)
    · change e (e.symm j) ∈ H.edges
      simpa only [Equiv.apply_symm_apply] using hj
    · change H.source (e (e.symm j)) ≠ H.target (e (e.symm j))
      simpa only [Equiv.apply_symm_apply] using hne

theorem IsK4.reindex {G : IncidenceGraph V E} (h : G.IsK4) (e : E' ≃ E) :
    (G.reindex e).IsK4 := by
  obtain ⟨v, f, he, hends⟩ := h
  refine ⟨v, f.trans e.symm.toEmbedding, ?_, ?_⟩
  · ext j
    change e j ∈ G.edges ↔ ∃ i, e.symm (f i) = j
    rw [he]
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨i, ?_⟩
      simpa only [Equiv.symm_apply_apply] using congrArg e.symm hi
    · rintro ⟨i, rfl⟩
      exact ⟨i, (e.apply_symm_apply (f i)).symm⟩
  · intro i
    change (G.source (e (e.symm (f i))) = _ ∧ G.target (e (e.symm (f i))) = _) ∨
      (G.source (e (e.symm (f i))) = _ ∧ G.target (e (e.symm (f i))) = _)
    simpa only [Equiv.apply_symm_apply] using hends i

theorem HasK4Minor.reindex {G : IncidenceGraph V E} (h : G.HasK4Minor)
    (e : E' ≃ E) : (G.reindex e).HasK4Minor := by
  obtain ⟨H, hHG, hH⟩ := h
  exact ⟨H.reindex e, hHG.reindex e, hH.reindex e⟩

theorem hasK4Minor_reindex_iff (G : IncidenceGraph V E) (e : E' ≃ E) :
    (G.reindex e).HasK4Minor ↔ G.HasK4Minor := by
  constructor
  · intro h
    simpa only [reindex_symm] using h.reindex e.symm
  · exact fun h => h.reindex e

end Unimodular.SeriesParallel.IncidenceGraph

#print axioms Unimodular.SeriesParallel.IncidenceGraph.hasK4Minor_reindex_iff
