import cubical_indecomposability.actual_edges
import cubical_indecomposability.rigidity.directions
import cubical_indecomposability.rigidity.complete
import papers.parallel_maps
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Every parallel redrawing is a homothety and a translation

The algebraic certificates concern arbitrary real assignments at all 144
vertices.  This file connects their equations to the actual exposed edges
of the convex polytope, so the resulting rigidity statement has its usual
geometric meaning.
-/

set_option autoImplicit false

noncomputable section

namespace CubicalIndecomposability

open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes

/-- The primitive integer direction and the actual edge difference span
the same line.  This equality also records the precise positive factor. -/
theorem edge_difference (e : Fin 404) (i : Fin 4) :
    p (edgeVertex e 1) i - p (edgeVertex e 0) i =
      (Rigidity.multiplier e : ℝ) /
        ((q (edgeVertex e 0) 4 : ℝ) * (q (edgeVertex e 1) 4 : ℝ)) *
          (Rigidity.direction e i : ℝ) := by
  have h0 : (q (edgeVertex e 0) 4 : ℝ) ≠ 0 :=
    ne_of_gt (homogeneous_last_real_pos _)
  have h1 : (q (edgeVertex e 1) 4 : ℝ) ≠ 0 :=
    ne_of_gt (homogeneous_last_real_pos _)
  have hs :
      (q (edgeVertex e 1) i.castSucc : ℝ) * (q (edgeVertex e 0) 4 : ℝ) -
        (q (edgeVertex e 0) i.castSucc : ℝ) * (q (edgeVertex e 1) 4 : ℝ) =
          (Rigidity.multiplier e : ℝ) * (Rigidity.direction e i : ℝ) := by
    exact_mod_cast Rigidity.direction_scale e i
  simp only [p_apply]
  field_simp [h0, h1]
  nlinarith [hs]

/-- A parallel redrawing in the paper's vertex-indexed notation. The
adjacency relation is the actual edge relation of the real convex hull. -/
def IsParallelVertexAssignment (h : Fin 144 → E 4) : Prop :=
  ∀ u v, GeneralVertexStep polytope (p u) (p v) →
    ∃ a : ℝ, h v - h u = a • (p v - p u)

/-- Parallelism on actual edges implies the exact algebraic constraints. -/
theorem constraints_of_vertex_assignment (h : Fin 144 → E 4)
    (hh : IsParallelVertexAssignment h) :
    Rigidity.Constraints (fun v i => h v i) := by
  intro e i
  obtain ⟨a, ha⟩ := hh (edgeVertex e 0) (edgeVertex e 1) (declaredEdge e)
  have hc (j : Fin 4) :
      h (edgeVertex e 1) j - h (edgeVertex e 0) j =
        a * (p (edgeVertex e 1) j - p (edgeVertex e 0) j) := by
    have hj := congrArg (fun x : E 4 => x j) ha
    simpa only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] using hj
  unfold Rigidity.crossRow
  rw [hc i, hc (Rigidity.pivot e), edge_difference e i,
    edge_difference e (Rigidity.pivot e)]
  ring

/-- The rigidity formula for every real assignment to the vertices.
The domain here is exactly the vertex labels, as in equation (1) of the paper. -/
theorem parallel_vertex_assignment_formula (h : Fin 144 → E 4)
    (hh : IsParallelVertexAssignment h) (v : Fin 144) :
    h v = (h 3 0 - h 1 0) • p v + h 1 := by
  ext i
  have hi := Rigidity.constraints_homothetic (fun v i => h v i)
    (constraints_of_vertex_assignment h hh) v i
  simpa only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, p_apply,
    mul_comm, add_comm] using hi

/-- Exact classification of the vertex-indexed redrawing space. -/
theorem parallel_vertex_assignment_iff (h : Fin 144 → E 4) :
    IsParallelVertexAssignment h ↔
      ∃ a : ℝ, ∃ b : E 4, ∀ v, h v = a • p v + b := by
  constructor
  · intro hh
    exact ⟨h 3 0 - h 1 0, h 1, parallel_vertex_assignment_formula h hh⟩
  · rintro ⟨a, b, hh⟩
    intro u v _
    refine ⟨a, ?_⟩
    rw [hh v, hh u, smul_sub]
    abel

/-- Restriction of a parallel map to the enumerated vertices. -/
theorem parallel_vertex_assignment_of_map (f : E 4 → E 4)
    (hf : IsParallelMap polytope f) :
    IsParallelVertexAssignment (fun v => f (p v)) := by
  intro u v huv
  exact hf (p u) (vertex_mem _) (p v) (vertex_mem _) huv

/-- Parallelism on the listed actual edges implies all certified linear
constraints. No converse or completeness assertion is assumed here. -/
theorem constraints_of_parallel (f : E 4 → E 4)
    (hf : IsParallelMap polytope f) :
    Rigidity.Constraints (fun v i => f (p v) i) :=
  constraints_of_vertex_assignment _ (parallel_vertex_assignment_of_map f hf)

/-- A fully explicit rigidity formula.  Vertex 1 is the origin and
vertex 3 is the first coordinate unit vector, so their values determine
the translation and the scale. -/
theorem parallel_redrawing_formula (f : E 4 → E 4)
    (hf : IsParallelMap polytope f) (v : Fin 144) :
    f (p v) = (f (p 3) 0 - f (p 1) 0) • p v + f (p 1) := by
  exact parallel_vertex_assignment_formula _ (parallel_vertex_assignment_of_map f hf) v

/-- Every parallel redrawing of the actual edge graph is a uniform
scaling and a translation, with no restriction on its real edge scalars. -/
theorem parallel_redrawings_homothetic (f : E 4 → E 4)
    (hf : IsParallelMap polytope f) : IsHomothetyOnVertices polytope f := by
  refine ⟨f (p 3) 0 - f (p 1) 0, f (p 1), ?_⟩
  intro v hv
  rw [polytope_vertices] at hv
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
  exact parallel_redrawing_formula f hf i

end CubicalIndecomposability
