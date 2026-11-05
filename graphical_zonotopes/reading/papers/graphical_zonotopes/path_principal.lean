module

public import Papers.GraphicalZonotopes.PathActualGraph
public import Papers.GraphicalZonotopes.PathPlanarity

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace Path
open scoped Pointwise

/-- The complete content of Theorem 3.1 for the explicitly defined Q_n.
Planarity is witnessed by a noncrossing straight-line embedding in R². -/
def PrincipalPathClaim (n : ℕ) : Prop :=
  LatticePolytope (polytope n) ∧
  MinkowskiIndecomposable (polytope n) ∧
  Module.finrank ℝ (vectorSpan ℝ (polytope n)) = n-1 ∧
  polytope n + complement n = (2 : ℝ) • graphicalZonotope (graph n) ∧
  (∀ u v, ActualRootEdge (polytope n) u v ↔ (graph n).Adj u v) ∧
  (∀ p q, IsExposedSegment (polytope n) p q →
    ∃ u v, (graph n).Adj u v ∧ ∃ t : ℝ, t ≠ 0 ∧
      q-p = t • (basisVector v-basisVector u)) ∧
  HasPlaneStraightLineDrawing (graph n) ∧
  (graph n).CliqueFree 5 ∧
  (edgeFamily (graph n)).card = 3*n-6 ∧
  (graph n).maxDegree = min (n-1) 6

/-- Theorem 3.1, with all n ≥ 4, actual Minkowski summation, actual exposed
directions, full affine dimension, and an actual geometric plane drawing. -/
theorem principal_path_theorem {n : ℕ} (hn : 4 ≤ n) : PrincipalPathClaim n :=
  ⟨polytope_lattice n, polytope_indecomposable hn, polytope_dimension hn,
    polytope_add_complement n, actual_direction_graph hn,
    fun _ _ h => every_exposed_edge_is_graph_direction hn h,
    PathDrawing.path_plane_drawing n, graph_cliqueFree_five n,
    graph_edge_count hn, graph_maxDegree hn⟩

end Path
end GraphicalZonotopes
