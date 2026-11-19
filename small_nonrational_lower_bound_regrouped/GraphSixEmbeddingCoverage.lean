module
prelude
public import GraphEmbeddingCoverage
public import SharedSix0CellPoolChecked
public import SharedSix0IncidenceChecked

@[expose] public section
namespace Papers.RationalityTen.GraphEmbeddingCoverage

noncomputable def sixAllowed (quota : Nat → Nat) : Nat :=
  SharedPoolIncidence.allowedMask SharedSix0Incidence.rows quota

theorem six_allowed (quota : Nat → Nat) (c : Fin 44310) :
    (sixAllowed quota).testBit c.val = true ↔
      0 < quota (FacetUniverses.FullSix0.cells c).kind := by
  have h := SharedPoolIncidence.allowedMask_exact SharedSix0CellPool.entry
    SharedSix0Incidence.rows SharedSix0Incidence.facts
    (fun c => (SharedSix0CellPool.facts c).kind_lt) quota c
  simpa only [sixAllowed, (SharedSix0CellPool.facts c).cell_eq] using h

theorem six_edges (c : Fin 44310) (q : Fin 45)
    (h : (SharedSix0Incidence.graphRows.edges c).testBit q.val = true) :
    (SharedSix0Incidence.graphRows.vertices c).testBit
        (SharedSix0Incidence.graphRows.first q).val = true ∧
    (SharedSix0Incidence.graphRows.vertices c).testBit
        (SharedSix0Incidence.graphRows.second q).val = true := by
  have hc := SharedSix0CellPool.facts c
  have hwithin := congrArg (fun n : Nat => n.testBit q.val) hc.edge_within
  rw [FiniteMaskSets.testBit_land] at hwithin
  change (SharedSix0CellPool.entry c).edgeMask.testBit q.val = true at h
  rw [h, Bool.true_and] at hwithin
  have hw := SharedSmallGraph.within_mask_exact
    ⟨(SharedSix0CellPool.entry c).cell.vertices, hc.vertices_lt⟩ q
  rw [hw] at hwithin
  exact Bool.and_eq_true_iff.mp hwithin

#print axioms six_allowed
#print axioms six_edges
end Papers.RationalityTen.GraphEmbeddingCoverage
