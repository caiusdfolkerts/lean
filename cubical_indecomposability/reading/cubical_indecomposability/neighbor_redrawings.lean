import verification_bundle
import cubical_indecomposability.deformation_dimension

/-!
# The two-neighbor rule for parallel redrawings

Lemma 3(ii) of the paper is a consequence of extremality alone: three
distinct vertices of a convex polytope cannot lie on one affine line.
Accordingly, the two directions from a vertex to two distinct neighbors
have no common nonzero vector.  Both the ambient-map and vertex-assignment
formulations below use the actual geometric edge relation.
-/

set_option autoImplicit false

noncomputable section

namespace Papers.Polytopes

open Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

/-- The direction lines from one actual vertex to two other distinct actual
vertices intersect only at zero.  Adjacency is not needed for this geometric
fact. -/
theorem vertex_direction_intersection_eq_zero (P : ConvexPolytope d)
    {x y z w : E d} (hx : x ∈ P.vertices) (hy : y ∈ P.vertices)
    (hz : z ∈ P.vertices) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hwy : ∃ a : ℝ, w = a • (y - x))
    (hwz : ∃ b : ℝ, w = b • (z - x)) : w = 0 := by
  by_contra hw
  obtain ⟨a, ha⟩ := hwy
  obtain ⟨b, hb⟩ := hwz
  have ha0 : a ≠ 0 := by
    intro h
    exact hw (by simpa only [h, zero_smul] using ha)
  have hb0 : b ≠ 0 := by
    intro h
    exact hw (by simpa only [h, zero_smul] using hb)
  apply vertices_not_collinear P hx hy hz hxy hxz hyz
  apply (collinear_iff_of_mem (show x ∈ ({x, y, z} : Set (E d)) by simp)).mpr
  refine ⟨w, ?_⟩
  intro q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with hqx | hqy | hqz
  · subst q
    exact ⟨0, by simp⟩
  · subst q
    refine ⟨a⁻¹, ?_⟩
    change y = a⁻¹ • w + x
    rw [ha, inv_smul_smul₀ ha0, sub_add_cancel]
  · subst q
    refine ⟨b⁻¹, ?_⟩
    change z = b⁻¹ • w + x
    rw [hb, inv_smul_smul₀ hb0, sub_add_cancel]

/-- **Lemma 3(ii), ambient-map formulation.** A parallel redrawing which
vanishes at two distinct neighbors of a vertex also vanishes at that vertex. -/
theorem IsParallelMap.zero_of_two_neighbors {P : ConvexPolytope d}
    {f : E d → E d} (hf : IsParallelMap P f) {x y z : E d}
    (hx : x ∈ P.vertices) (hxy : GeneralVertexStep P x y)
    (hxz : GeneralVertexStep P x z) (hyz : y ≠ z)
    (hy : f y = 0) (hz : f z = 0) : f x = 0 := by
  obtain ⟨a, ha⟩ := hf x hx y hxy.1 hxy
  obtain ⟨b, hb⟩ := hf x hx z hxz.1 hxz
  apply neg_eq_zero.mp
  apply vertex_direction_intersection_eq_zero P hx hxy.1 hxz.1
    hxy.2.1 hxz.2.1 hyz
  · exact ⟨a, by simpa only [hy, zero_sub] using ha⟩
  · exact ⟨b, by simpa only [hz, zero_sub] using hb⟩

/-- **Lemma 3(ii), vertex-assignment formulation.** This applies directly
to the redrawing space whose quotient defines the paper's `D(P)`. -/
theorem redrawing_zero_of_two_neighbors {P : ConvexPolytope d}
    (h : redrawingSpace P) {x y z : Vertex P}
    (hxy : GeneralVertexStep P x y) (hxz : GeneralVertexStep P x z)
    (hyz : y ≠ z) (hy : h y = 0) (hz : h z = 0) : h x = 0 := by
  obtain ⟨a, ha⟩ := h.property x y hxy
  obtain ⟨b, hb⟩ := h.property x z hxz
  have hyz' : (y : E d) ≠ (z : E d) := fun h => hyz (Subtype.ext h)
  apply neg_eq_zero.mp
  apply vertex_direction_intersection_eq_zero P x.property y.property z.property
    hxy.2.1 hxz.2.1 hyz'
  · exact ⟨a, by simpa only [hy, zero_sub] using ha⟩
  · exact ⟨b, by simpa only [hz, zero_sub] using hb⟩

end Papers.Polytopes
