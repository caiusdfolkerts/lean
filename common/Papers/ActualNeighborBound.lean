module
public import Papers.PolytopeVertexCone
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

/-! Actual graph degree is at least intrinsic dimension, from tangent span. -/

namespace Papers.Polytopes
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
variable {d : ℕ}

/-- The degree bound derived from the full actual tangent-direction span. -/
theorem actual_neighbor_card_ge_dim
    (P : ConvexPolytope d) {v : E d} (hv : v ∈ P.vertices) :
    P.dim ≤ (Papers.PolytopeVertexCone.actualNeighbors P v).card := by
  classical
  have h := finrank_range_le_card (R := ℝ)
    (fun w : Papers.PolytopeVertexCone.actualNeighbors P v => w.val - v)
  have hbound : Module.finrank ℝ (Submodule.span ℝ
      (Set.range (fun w : Papers.PolytopeVertexCone.actualNeighbors P v => w.val - v))) ≤
        (Papers.PolytopeVertexCone.actualNeighbors P v).card := by
    simpa only [Set.finrank,Fintype.card_coe] using h
  rw [← Papers.PolytopeVertexCone.neighborSpan_eq_range_span,
    Papers.PolytopeVertexCone.neighborSpan_eq_vectorSpan P hv] at hbound
  exact hbound


end Papers.Polytopes

