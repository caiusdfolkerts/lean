module
public import cubical
@[expose] public section
noncomputable section
open Set
open scoped Pointwise Classical Topology BigOperators

/-! Complete specifications of the six supplied proof-bearing record constructors.
Only mathematical data fields are constrained; all remaining fields are propositions.
These are supporting obligations for the sixteen paper results, not separate research claims. -/
namespace PalomarCubicalLower
open LeanEval.Geometry.PlatonicClassification
open Geometry

/-- Every cube vertex is exactly a sign vector. -/
theorem standardCube_vertices (d : ℕ) :
    (standardCube d).vertices = verticiIper d := by rfl

/-- The face retains exactly those original vertices that lie in the actual face. -/
theorem facePolytope_vertices {n : ℕ} (P : ConvexPolytope n) {f : Set (E n)}
    (hf : P.IsFace f) :
    (facePolytope P hf).vertices = P.vertices.filter (· ∈ f) := by rfl

/-- Full literal adjacency of the ordinary polytope edge graph. -/
theorem polytopeGraph_adj {n : ℕ} (P : ConvexPolytope n) (u v : VertexType P) :
    (polytopeGraph P).Adj u v ↔ u ≠ v ∧ ∃ F : Set (E n),
      P.IsFace F ∧ ConvexPolytope.faceDim F = 1 ∧ u.val ∈ F ∧ v.val ∈ F := by rfl

/-- Full literal adjacency of the cubical cell graph. -/
theorem cubeComplex_graph_adj {V : Type*} [Fintype V] [DecidableEq V]
    (K : Cubical.PL.CubeComplex V) (v w : V) :
    K.graph.Adj v w ↔ v ≠ w ∧ {v,w} ∈ K.faces ∧ K.dimension {v,w} = 1 := by rfl

/-- The entire order-complex face set consists of the nonempty cell chains. -/
theorem cubeComplex_orderComplex_faces {V : Type*} [Fintype V] [DecidableEq V]
    (K : Cubical.PL.CubeComplex V) :
    K.orderComplex.faces = {C | C.Nonempty ∧ ∀ F ∈ C, ∀ G ∈ C, F ≤ G ∨ G ≤ F} := by rfl

/-- The entire realization face set is the image under the explicit standard basis. -/
theorem standardRealization_faces {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : PreAbstractSimplicialComplex ι) :
    (DifferentialGeometry.Topology.Engulfing.standardRealization P).faces =
      {s | ∃ t ∈ P.faces, t.image (fun i => Pi.single i (1 : ℝ)) = s} := by rfl

end PalomarCubicalLower
