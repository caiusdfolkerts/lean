module
prelude
public import GraphCaseCertificate

@[expose] public section

/-!
# Exact graph-specific candidate coverage

A local search universe is accepted only when its embedding has no duplicates
and its bit mask equals the complete induced-graph filter of the full catalogue.
-/

namespace Papers.RationalityTen.GraphEmbeddingCoverage
open ConcreteGrowth PackedGraphCertificate SharedGraphCellPool GraphCandidateCoverage
open GraphCaseCertificate GrowthBitsets

theorem coverage_of_mask {N : Nat} [NeZero N] (D : RawData)
    (cells : Fin N → Cell) (rows : IncidenceRows N 10 45)
    (complement allowed : Nat)
    (hcells : ∀ c, D.data.cells c = cells (embedding D c))
    (hnodup : ((List.finRange D.n).map (embedding (N := N) D)).Nodup)
    (hallowed : ∀ c, allowed.testBit c.val = true ↔ 0 < D.data.quota (cells c).kind)
    (hmask : eligibleMask rows allowed complement =
      ofList ((List.finRange D.n).map (embedding (N := N) D)))
    (hedges : ∀ c q, (rows.edges c).testBit q.val = true →
      (rows.vertices c).testBit (rows.first q).val = true ∧
      (rows.vertices c).testBit (rows.second q).val = true) :
    Coverage D cells rows complement := by
  refine ⟨hcells, hnodup, ?_⟩
  intro c
  have hm := mem_embedding_iff rows allowed complement
    ((List.finRange D.n).map (embedding (N := N) D)) hmask c (hedges c)
  simpa only [List.mem_map, List.mem_finRange, true_and, hallowed c] using hm

theorem small_allowed (quota : Nat → Nat) (c : Fin 6510) :
    (SharedSmallGraph.allowedMask quota).testBit c.val = true ↔
      0 < quota (FacetUniverses.FullSmall.cells c).kind := by
  change (unionValues
    (fun j : Fin 5 => if 0 < quota j.val then SharedSmallGraph.kindRows j.val else 0)
    (List.finRange 5)).testBit c.val = true ↔ _
  rw [← bitAt_eq_testBit, bitAt_unionValues]
  simp only [List.mem_finRange, true_and, bitAt_eq_testBit]
  constructor
  · rintro ⟨j, hj⟩
    by_cases hq : 0 < quota j.val
    · rw [if_pos hq, SharedSmallGraph.kind_rows_exact, decide_eq_true_eq] at hj
      simpa only [hj] using hq
    · rw [if_neg hq, Nat.zero_testBit] at hj
      exact False.elim (Bool.noConfusion hj)
  · intro hq
    let j : Fin 5 := ⟨(FacetUniverses.FullSmall.cells c).kind, SharedSmallGraph.kind_lt c⟩
    refine ⟨j, ?_⟩
    rw [if_pos hq, SharedSmallGraph.kind_rows_exact]
    exact decide_eq_true rfl

theorem small_edges (c : Fin 6510) (q : Fin 45)
    (h : (SharedSmallGraph.graphRows.edges c).testBit q.val = true) :
    (SharedSmallGraph.graphRows.vertices c).testBit
        (SharedSmallGraph.graphRows.first q).val = true ∧
    (SharedSmallGraph.graphRows.vertices c).testBit
        (SharedSmallGraph.graphRows.second q).val = true := by
  have hwithin := congrArg (fun n : Nat => n.testBit q.val) (SharedSmallGraph.edge_within c)
  rw [FiniteMaskSets.testBit_land] at hwithin
  change (SharedSmallGraph.edgeMask c).testBit q.val = true at h
  rw [h, Bool.true_and] at hwithin
  have hw := SharedSmallGraph.within_mask_exact
    ⟨(SharedSmallGraph.cells c).vertices, SharedSmallGraph.vertices_lt c⟩ q
  rw [hw] at hwithin
  exact Bool.and_eq_true_iff.mp hwithin

#print axioms coverage_of_mask
#print axioms small_allowed
#print axioms small_edges
end Papers.RationalityTen.GraphEmbeddingCoverage
