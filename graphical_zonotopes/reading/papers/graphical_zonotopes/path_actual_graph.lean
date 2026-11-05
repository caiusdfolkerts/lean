module

public import Papers.GraphicalZonotopes.PathEdges
public import Papers.GraphicalZonotopes.SummandEdges

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace Path
open scoped Pointwise

/-- Exact equality of the actual exposed-edge direction graph with the third
power of the path, in both directions and for every n ≥ 4. -/
theorem actual_direction_graph {n : ℕ} (hn : 4 ≤ n) (u v : Fin n) :
    ActualRootEdge (polytope n) u v ↔ (graph n).Adj u v := by
  constructor
  · exact basePolytope_summand_actualRootEdge (setFunction_normalized n).1
      (setFunction_supermodular n) (graph n) (by norm_num : (0 : ℝ) ≤ 2)
      (complement n) (polytope_add_complement n)
  · exact graph_edge_is_actual hn

/-- In addition, every exposed edge is parallel to one of those roots; the
direction graph does not omit non-root exposed edges. -/
theorem every_exposed_edge_is_graph_direction {n : ℕ} (hn : 4 ≤ n)
    {p q : Fin n → ℝ} (hex : IsExposedSegment (polytope n) p q) :
    ∃ u v, (graph n).Adj u v ∧ ∃ t : ℝ, t ≠ 0 ∧
      q-p = t • (basisVector v-basisVector u) :=
  basePolytope_summand_exposed_edge (setFunction_normalized n).1
    (setFunction_supermodular n) (graph n) (by norm_num : (0 : ℝ) ≤ 2)
    (complement n) (polytope_add_complement n) hex

end Path
end GraphicalZonotopes
