import cubical.polytope.simplicial_boundary
import cubical.fogelsanger

/-!
# Generic rigidity of genuine simplicial convex polytopes

The geometric boundary is an actual minimal simplicial `𝔽₂` cycle, and its
support graph is proved isomorphic to the ordinary exposed-edge graph.
Fogelsanger's fully verified theorem therefore applies without additional
graph, topological, or rigidity assumptions.
-/

open Set Classical

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope Cubical.Simplicial Cubical.Rigidity

variable {n : ℕ}

theorem boundaryFacets_vertices (P : ConvexPolytope n) (hdim : 1 ≤ P.dim) :
    Cubical.Simplicial.vertices id (boundaryFacets P) = Finset.univ := by
  ext v
  simp only [Finset.mem_univ, iff_true]
  obtain ⟨F, hvF⟩ := vertex_in_facet P hdim v
  exact (mem_vertices id (boundaryFacets P) v).mpr
    ⟨faceVertices P F.val.val, (mem_boundaryFacets P _).mpr ⟨F, rfl⟩,
      (mem_faceVertices P _ v).mpr hvF⟩

theorem mem_vertexHull (P : ConvexPolytope n) (s : Finset (VertexType P))
    (v : VertexType P) (hv : v ∈ s) : v.val ∈ vertexHull P s :=
  subset_convexHull ℝ _ (Finset.mem_image_of_mem _ hv)

theorem oneSkeleton_boundary_eq (P : ConvexPolytope n) (hs : IsSimplicial P)
    (hdim : 2 ≤ P.dim) : oneSkeleton id (boundaryFacets P) = polytopeGraph P := by
  ext u v
  constructor
  · rintro ⟨hne, t, ht, hu, hv⟩
    have hsub : ({u, v} : Finset (VertexType P)) ⊆ t := by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hu, hv⟩
    have hnePair : ({u, v} : Finset (VertexType P)).Nonempty := by simp
    have hF := boundary_subsimplex_isFace P hs ht hsub hnePair
    have hdF := boundary_subsimplex_dimension P hs ht hsub hnePair
    have hc : ({u, v} : Finset (VertexType P)).card = 2 := by simp [hne]
    refine ⟨hne, vertexHull P {u, v}, hF, by omega, ?_, ?_⟩
    · exact mem_vertexHull P _ u (by simp)
    · exact mem_vertexHull P _ v (by simp)
  · rintro ⟨hne, e, he, hde, hue, hve⟩
    obtain ⟨F, hF, hdF, heF⟩ := face_contained_in_facet P he (by omega)
    let f : FacetType P := ⟨⟨F, hF⟩, hdF⟩
    exact ⟨hne, faceVertices P F, (mem_boundaryFacets P _).mpr ⟨f, rfl⟩,
      (mem_faceVertices P F u).mpr (heF hue),
      (mem_faceVertices P F v).mpr (heF hve)⟩

/-- The simplicial boundary support graph is exactly the exposed-edge graph,
up to removal of the redundant proof of support membership. -/
def boundarySupportGraphIso (P : ConvexPolytope n) (hs : IsSimplicial P)
    (hdim : 2 ≤ P.dim) :
    supportGraph id (boundaryFacets P) ≃g polytopeGraph P where
  toFun v := v.val
  invFun v := ⟨v, by rw [boundaryFacets_vertices P (by omega)]; exact Finset.mem_univ v⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by
    intro u v
    change (polytopeGraph P).Adj u.val v.val ↔
      (oneSkeleton id (boundaryFacets P)).Adj u.val v.val
    rw [oneSkeleton_boundary_eq P hs hdim]

/-- Generic infinitesimal rigidity of a simplicial convex polytope in its
intrinsic dimension, in any real finite-dimensional inner product space of
that dimension. -/
theorem IsSimplicial.genericallyRigid {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (P : ConvexPolytope n) (hs : IsSimplicial P) (hdim : 3 ≤ P.dim)
    (hH : Module.finrank ℝ H = P.dim) :
    GenericallyRigid (polytopeGraph P) H := by
  have hc := simplicial_boundary_circuit P hs (by omega)
  have hr := hc.genericallyRigid hdim (boundaryFacets_pure P hs) hH
  exact hr.of_iso (boundarySupportGraphIso P hs (by omega))

end LeanEval.Geometry.PlatonicClassification
