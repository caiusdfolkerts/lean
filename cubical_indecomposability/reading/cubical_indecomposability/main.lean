import cubical_indecomposability.cube_realization
import cubical_indecomposability.redrawings
import cubical_indecomposability.summands

/-!
# Theorem 1 of *An indecomposable cubical four-polytope*

Start here.  The witness is the ordinary real convex hull of 144 explicitly
listed rational points.  The face counts concern all exposed faces, and
each facet is proved order-isomorphic to the face lattice of a three-cube.
The rigidity assertion quantifies all real parallel redrawings.  The
Minkowski assertion quantifies arbitrary convex summands, without assuming
that those summands are themselves polytopes.
-/

set_option autoImplicit false

noncomputable section

namespace CubicalIndecomposability

open Set
open scoped Pointwise
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes

/-- The explicit polytope has two distinct extreme vertices. -/
theorem polytope_nonpoint :
    ∃ x ∈ polytope.vertices, ∃ y ∈ polytope.vertices, x ≠ y := by
  refine ⟨p 1, vertex_mem _, p 3, vertex_mem _, ?_⟩
  intro h
  have := p_injective h
  norm_num at this

/-- The strongest customary meaning of Minkowski indecomposability:
every convex summand is a translated nonnegative multiple of the polytope.
The complementary summand has the complementary scale and translation. -/
theorem minkowski_summands (A B : Set (E 4))
    (hA : Convex ℝ A) (hB : Convex ℝ B)
    (hK : polytope.toSet = A + B) :
    ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧ ∃ b : E 4,
      A = (fun x : E 4 => r • x + b) '' polytope.toSet ∧
      B = (fun x : E 4 => (1 - r) • x - b) '' polytope.toSet :=
  convex_summands_homothetic_of_parallel_rigid polytope
    parallel_redrawings_homothetic polytope_nonpoint A B hA hB hK

/-- Indecomposability in the usual polytopal formulation as well. -/
theorem minkowski_indecomposable : ¬MinkowskiDecomposable polytope := by
  intro h
  obtain ⟨f, hf, hnot⟩ := parallel_map_of_minkowski_decomposable polytope h
  exact hnot (parallel_redrawings_homothetic f hf)

/-- The paper's principal theorem, in full.  All objects and properties
in this statement have their ordinary convex-geometric definitions. -/
theorem theorem_one :
    ∃ K : ConvexPolytope 4,
      K.IsFullDim ∧ RationalCoordinates K ∧ ¬MinkowskiDecomposable K ∧ IsCubical K ∧
      faceNumber K 0 = 144 ∧ faceNumber K 1 = 404 ∧
      faceNumber K 2 = 390 ∧ faceNumber K 3 = 130 ∧
      (∀ f : E 4 → E 4, IsParallelMap K f → IsHomothetyOnVertices K f) ∧
      (∀ A B : Set (E 4), Convex ℝ A → Convex ℝ B → K.toSet = A + B →
        ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧ ∃ b : E 4,
          A = (fun x : E 4 => r • x + b) '' K.toSet ∧
          B = (fun x : E 4 => (1 - r) • x - b) '' K.toSet) := by
  refine ⟨polytope, polytope_dimension, rational_coordinates,
    minkowski_indecomposable, polytope_isCubical,
    face_vector.1, face_vector.2.1, face_vector.2.2.1, face_vector.2.2.2,
    parallel_redrawings_homothetic, minkowski_summands⟩

end CubicalIndecomposability
