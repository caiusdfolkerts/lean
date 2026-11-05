import cubical.polytope.sotto_politopo

/-!
# Finite face sets of genuine convex polytopes

These results concern exposed geometric faces of a convex hull.  No
combinatorial incidence or face-count property is assumed in the definitions.
-/

open Set

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- A finite convex polytope has only finitely many nonempty faces. -/
theorem finite_isFace (P : ConvexPolytope n) :
    Set.Finite {F : Set (E n) | P.IsFace F} := by
  classical
  apply (P.vertices.powerset.finite_toSet.image
    (fun s : Finset (E n) => convexHull ℝ (s : Set (E n)))).subset
  intro F hF
  refine ⟨P.vertices.filter (· ∈ F), ?_, ?_⟩
  · exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  · exact (face_eq_hull_vertices P hF).symm

/-- Geometric faces are determined by the vertices they contain. -/
theorem face_eq_iff_vertices_eq (P : ConvexPolytope n)
    {F G : Set (E n)} (hF : P.IsFace F) (hG : P.IsFace G) :
    F = G ↔ (∀ v ∈ P.vertices, v ∈ F ↔ v ∈ G) := by
  classical
  constructor
  · intro h v hv
    rw [h]
  · intro h
    rw [face_eq_hull_vertices P hF, face_eq_hull_vertices P hG]
    congr 2
    ext v
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hv, hvF⟩
      exact ⟨hv, (h v hv).mp hvF⟩
    · rintro ⟨hv, hvG⟩
      exact ⟨hv, (h v hv).mpr hvG⟩

/-- Nonempty intersections of faces are common faces, geometrically. -/
theorem isFace_inter (P : ConvexPolytope n)
    {F G : Set (E n)} (hF : P.IsFace F) (hG : P.IsFace G)
    (hne : (F ∩ G).Nonempty) : P.IsFace (F ∩ G) :=
  ⟨hF.1.inter hG.1, hne⟩

/-- All nonempty faces, represented as geometric subsets. -/
noncomputable def faceSet (P : ConvexPolytope n) : Finset (Set (E n)) :=
  (finite_isFace P).toFinset

@[simp] theorem mem_faceSet (P : ConvexPolytope n) (F : Set (E n)) :
    F ∈ faceSet P ↔ P.IsFace F := by
  classical
  simp [faceSet]

/-- The number of geometric faces of affine dimension `i`. -/
noncomputable def faceNumber (P : ConvexPolytope n) (i : ℕ) : ℕ := by
  classical
  exact ((faceSet P).filter (fun F => faceDim F = i)).card

end LeanEval.Geometry.PlatonicClassification
