module

public import Cubical.Polytope.FiguraAlVertice
public import Mathlib.Analysis.Convex.Extreme

@[expose] public section

/-!
# Thin extreme-vertex facts

These lemmas depend directly on the defining
extreme-point equation of ConvexPolytope and Mathlib's segment
characterization of an extreme point. They replace legacy helper names
that would otherwise pull the large paper proof closure into the
elementary geometry.
-/

namespace Papers.PolytopeBasicExtreme

open Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem vertex_mem_body (P : ConvexPolytope d) {v : E d}
    (hv : v ∈ P.vertices) : v ∈ P.toSet :=
  subset_convexHull ℝ _ hv

theorem vertex_mem_extreme (P : ConvexPolytope d) {v : E d}
    (hv : v ∈ P.vertices) : v ∈ P.toSet.extremePoints ℝ := by
  change v ∈ (convexHull ℝ (P.vertices : Set (E d))).extremePoints ℝ
  rw [← P.vertices_eq_extremePoints]
  exact hv

theorem extreme_point_on_segment (A : Set (E d)) {v x y : E d}
    (hv : v ∈ A.extremePoints ℝ) (hx : x ∈ A) (hy : y ∈ A)
    (hseg : v ∈ segment ℝ x y) : v = x ∨ v = y := by
  have h := (mem_extremePoints_iff_forall_segment.mp hv).2 x hx y hy hseg
  exact h.imp Eq.symm Eq.symm

end Papers.PolytopeBasicExtreme
