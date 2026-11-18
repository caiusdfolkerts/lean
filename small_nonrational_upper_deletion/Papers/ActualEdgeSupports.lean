module
public import Cubical.Polytope.FiguraAlVertice
public import Papers.ExposedEdgeCenters
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Supporting affine forms for actual polytope edges

The face and extreme-point inputs used by the projective edge lemmas are
constructed here from the ordinary ConvexPolytope and GeneralVertexStep
definitions. No exposing-form or vertex-extremality certificate is assumed.
-/

noncomputable section
namespace Papers.Polytopes

open Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem actualStep_symm {P : ConvexPolytope d} {x y : E d}
    (hx : x ∈ P.vertices) (hxy : GeneralVertexStep P x y) :
    GeneralVertexStep P y x := by
  obtain ⟨hy,hne,F,hF,hdim,hxF,hyF⟩ := hxy
  exact ⟨hx,hne.symm,F,hF,hdim,hyF,hxF⟩

theorem vertex_mem_body_extremePoints (P : ConvexPolytope d)
    {x : E d} (hx : x ∈ P.vertices) :
    x ∈ P.toSet.extremePoints ℝ := by
  change x ∈ (convexHull ℝ (P.vertices : Set (E d))).extremePoints ℝ
  rw [← P.vertices_eq_extremePoints]
  exact hx

theorem vertex_mem_body_of_mem_vertices (P : ConvexPolytope d)
    {x : E d} (hx : x ∈ P.vertices) : x ∈ P.toSet :=
  subset_convexHull ℝ _ hx

theorem actual_edge_eq_segment_of_endpoints
    (P : ConvexPolytope d) (F : Set (E d))
    (hF : P.IsFace F) (hdim : faceDim F = 1)
    {x y : E d} (hx : x ∈ P.vertices) (hy : y ∈ P.vertices)
    (hxy : x ≠ y) (hxF : x ∈ F) (hyF : y ∈ F) :
    F = segment ℝ x y := by
  obtain ⟨z,hz,hzF,hzx,hseg⟩ := spigolo_segmento P hF hdim hx hxF
  have hyseg : y ∈ segment ℝ x z := by simpa only [← hseg] using hyF
  have hends := ExposedEdgeCenters.extreme_point_on_segment P.toSet
    (vertex_mem_body_extremePoints P hy)
    (vertex_mem_body_of_mem_vertices P hx) (vertex_mem_body_of_mem_vertices P hz) hyseg
  rcases hends with hyx | hyz
  · exact (hxy hyx.symm).elim
  · simpa only [hyz] using hseg

theorem segment_isFace_of_generalVertexStep
    (P : ConvexPolytope d) {x y : E d} (hx : x ∈ P.vertices)
    (hxy : GeneralVertexStep P x y) :
    P.IsFace (segment ℝ x y) := by
  obtain ⟨F,hF,hdim,hxF,hyF⟩ := hxy.2.2
  have hseg := actual_edge_eq_segment_of_endpoints P F hF hdim
    hx hxy.1 hxy.2.1 hxF hyF
  simpa only [hseg] using hF

theorem segment_faceDim_of_generalVertexStep
    (P : ConvexPolytope d) {x y : E d} (hx : x ∈ P.vertices)
    (hxy : GeneralVertexStep P x y) :
    faceDim (segment ℝ x y) = 1 := by
  obtain ⟨F,hF,hdim,hxF,hyF⟩ := hxy.2.2
  have hseg := actual_edge_eq_segment_of_endpoints P F hF hdim
    hx hxy.1 hxy.2.1 hxF hyF
  simpa only [hseg] using hdim

/-- Every actual nonempty face has a nonnegative affine exposing form. -/
theorem exists_nonnegative_affine_face_form
    (P : ConvexPolytope d) (F : Set (E d)) (hF : P.IsFace F) :
    ∃ g : E d →ᵃ[ℝ] ℝ,
      (∀ z ∈ P.toSet, 0 ≤ g z) ∧
      (∀ z ∈ P.toSet, g z = 0 ↔ z ∈ F) := by
  obtain ⟨x,hxF⟩ := hF.2
  obtain ⟨l,hl⟩ := hF.1 hF.2
  have hx' := hxF
  rw [hl] at hx'
  let g : E d →ᵃ[ℝ] ℝ :=
    AffineMap.const ℝ (E d) (l x) - l.toLinearMap.toAffineMap
  have hg (z : E d) : g z = l x - l z := rfl
  refine ⟨g,?_,?_⟩
  · intro z hz
    rw [hg]
    exact sub_nonneg.mpr (hx'.2 z hz)
  · intro z hz
    rw [hg,sub_eq_zero]
    constructor
    · intro heq
      rw [hl]
      refine ⟨hz,?_⟩
      intro w hw
      exact (hx'.2 w hw).trans_eq heq
    · intro hzF
      rw [hl] at hzF
      exact le_antisymm (hzF.2 x hx'.1) (hx'.2 z hz)

/-- Actual edges supply precisely the forms required by the center geometry. -/
theorem exists_nonnegative_affine_edge_form
    (P : ConvexPolytope d) {x y : E d} (hx : x ∈ P.vertices)
    (hxy : GeneralVertexStep P x y) :
    ∃ g : E d →ᵃ[ℝ] ℝ,
      (∀ z ∈ P.toSet, 0 ≤ g z) ∧
      (∀ z ∈ P.toSet, g z = 0 ↔ z ∈ segment ℝ x y) :=
  exists_nonnegative_affine_face_form P (segment ℝ x y)
    (segment_isFace_of_generalVertexStep P hx hxy)

end Papers.Polytopes

