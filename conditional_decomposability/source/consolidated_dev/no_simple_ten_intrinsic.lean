module
public import consolidated.deletion_geometry
public import consolidated_dev.intrinsic_figure_geometry
public import consolidated_dev.simple_vertex_duality
public import consolidated_dev.simple_four_ridges
public import consolidated_dev.abstract_lower_bound
public import consolidated_dev.simple_four_combinatorics
public import consolidated_dev.simple_four_no_ten
public import consolidated_dev.actual_geometry
public import papers.simple_four_finite_obstruction

set_option Elab.async false

section BundlePart0
/- Source: Papers/NoSimpleTenIntrinsic.lean -/




@[expose] public section

/-! # Intrinsic simplicity in the actual-neighbour API -/

noncomputable section
namespace Papers.SimpleFour

open Set Module
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.PolytopeVertexCone
open scoped Classical

variable {n : ℕ}

def actualNeighborGraphEquiv (P : ConvexPolytope n) (v : VertexType P) :
    ↥(actualNeighbors P v.val) ≃ NeighborOf v where
  toFun w :=
    let hw := (mem_actualNeighbors_iff P v.val w.val).mp w.property
    ⟨⟨w.val,hw.1⟩,⟨fun h => hw.2.1 (congrArg Subtype.val h),hw.2.2⟩⟩
  invFun w := ⟨w.val.val,(mem_actualNeighbors_iff P v.val w.val.val).mpr
    ⟨w.val.property,fun h => w.property.1 (Subtype.ext h),w.property.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem actualNeighbors_card_eq_graph_degree (P : ConvexPolytope n) (v : VertexType P) :
    (actualNeighbors P v.val).card = (polytopeGraph P).degree v := by
  have h := Fintype.card_congr (actualNeighborGraphEquiv P v)
  change Fintype.card ↥(actualNeighbors P v.val) =
    Fintype.card ((polytopeGraph P).neighborSet v) at h
  rw [Fintype.card_coe,SimpleGraph.card_neighborSet_eq_degree] at h
  exact h

/-- Every finite convex polytope of intrinsic dimension four and exactly ten
actual vertices has an actual vertex of degree different from four. -/
theorem no_simple_intrinsic_four_polytope_ten_vertices
    (P : ConvexPolytope n) (hfour : P.dim = 4) (hvertices : P.vertices.card = 10)
    (hs : ∀ v ∈ P.vertices, (actualNeighbors P v).card = 4) : False := by
  apply no_simple_four_polytope_ten_vertices P hfour _ hvertices
  intro v
  rw [← actualNeighbors_card_eq_graph_degree P v]
  exact hs v.val v.property

end Papers.SimpleFour

end
end
end BundlePart0
