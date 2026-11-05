import cubical.polytope.facet_geometry
import cubical.pseudomanifold_circuit

/-! # The exact simplicial boundary of a geometric simplicial polytope -/

open Set Classical

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope
open Cubical.Simplicial

variable {n : ℕ}

def vertexHull (P : ConvexPolytope n) (s : Finset (VertexType P)) : Set (E n) :=
  convexHull ℝ ((s.image (fun v => v.val) : Finset (E n)) : Set (E n))

theorem vertexHull_mono (P : ConvexPolytope n) {s t : Finset (VertexType P)} (hst : s ⊆ t) :
    vertexHull P s ⊆ vertexHull P t :=
  convexHull_mono (Finset.coe_subset.mpr (Finset.image_subset_image hst))

@[simp] theorem vertexHull_faceVertices (P : ConvexPolytope n) {F : Set (E n)}
    (hF : P.IsFace F) : vertexHull P (faceVertices P F) = F := faceVertices_hull P hF

@[simp] theorem faceVertices_vertexHull (P : ConvexPolytope n) (s : Finset (VertexType P)) :
    faceVertices P (vertexHull P s) = s := by
  have hsub : s.image (fun v => v.val) ⊆ P.vertices := by
    rintro x hx
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
    exact v.property
  have hfilter := vertices_filter_convexHull_subset P _ hsub
  ext v
  rw [mem_faceVertices]
  have hmem := congrArg (fun T : Finset (E n) => v.val ∈ T) hfilter
  simp only [Finset.mem_filter, v.property, true_and] at hmem
  change (v.val ∈ convexHull ℝ
    ((s.image (fun v => v.val) : Finset (E n)) : Set (E n))) ↔ v ∈ s
  rw [hmem]
  constructor
  · rintro h
    obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp h
    exact (Subtype.ext hwv : w = v) ▸ hw
  · intro hv
    exact Finset.mem_image_of_mem _ hv

theorem boundaryFacets_pure (P : ConvexPolytope n) (hs : IsSimplicial P) :
    Pure P.dim id (boundaryFacets P) := by
  intro t ht
  obtain ⟨F, rfl⟩ := (mem_boundaryFacets P t).mp ht
  rw [id_eq, faceVertices_card P F.val.property]
  exact (isSimplicial_iff_facet_vertices_card P).mp hs _ F.val.property F.property

theorem face_subset_simplex_isFace (P : ConvexPolytope n)
    {F : Set (E n)} (hF : P.IsFace F)
    (hi : AffineIndependent ℝ (fun v : VertexType (facePolytope P hF) => v.val))
    (s : Finset (VertexType P)) (hs : s ⊆ faceVertices P F) (hne : s.Nonempty) :
    P.IsFace (vertexHull P s) := by
  have hsub : s.image (fun v => v.val) ⊆ (facePolytope P hF).vertices := by
    rintro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_filter.mpr ⟨v.property, (mem_faceVertices P F v).mp (hs hv)⟩
  exact isFace_of_facePolytope P hF
    (simplex_subset_isFace (facePolytope P hF) hi _ hsub (hne.image _))

theorem face_subset_simplex_dimension (P : ConvexPolytope n)
    {F : Set (E n)} (hF : P.IsFace F)
    (hi : AffineIndependent ℝ (fun v : VertexType (facePolytope P hF) => v.val))
    (s : Finset (VertexType P)) (hs : s ⊆ faceVertices P F) (hne : s.Nonempty) :
    faceDim (vertexHull P s) + 1 = s.card := by
  have hsub : s.image (fun v => v.val) ⊆ (facePolytope P hF).vertices := by
    rintro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_filter.mpr ⟨v.property, (mem_faceVertices P F v).mp (hs hv)⟩
  have h := simplex_subset_dimension (facePolytope P hF) hi _ hsub (hne.image _)
  rwa [Finset.card_image_of_injective _ Subtype.val_injective] at h

theorem boundary_subsimplex_isFace (P : ConvexPolytope n) (hs : IsSimplicial P)
    {t s : Finset (VertexType P)} (ht : t ∈ boundaryFacets P) (hst : s ⊆ t)
    (hne : s.Nonempty) : P.IsFace (vertexHull P s) := by
  obtain ⟨F, rfl⟩ := (mem_boundaryFacets P t).mp ht
  exact face_subset_simplex_isFace P F.val.property (hs _ F.val.property F.property) s hst hne

theorem boundary_subsimplex_dimension (P : ConvexPolytope n) (hs : IsSimplicial P)
    {t s : Finset (VertexType P)} (ht : t ∈ boundaryFacets P) (hst : s ⊆ t)
    (hne : s.Nonempty) : faceDim (vertexHull P s) + 1 = s.card := by
  obtain ⟨F, rfl⟩ := (mem_boundaryFacets P t).mp ht
  exact face_subset_simplex_dimension P F.val.property
    (hs _ F.val.property F.property) s hst hne

theorem simplicial_ridge_vertices_card (P : ConvexPolytope n) (hs : IsSimplicial P)
    {R : Set (E n)} (hR : P.IsFace R) (F : FacetType P) (hRF : R ⊆ F.val.val) :
    (faceVertices P R).card = faceDim R + 1 := by
  have hRQ := facePolytope_isFace_of P F.val.property hR hRF
  have h := simplex_face_vertices_card (facePolytope P F.val.property)
    (hs _ F.val.property F.property) hRQ
  rw [facePolytope_vertices_of_subface P hR F.val.property hRF] at h
  rwa [faceVertices_card P hR]

theorem ridge_vertices_mem_simplexBoundary (P : ConvexPolytope n) (hs : IsSimplicial P)
    {R : Set (E n)} (hR : P.IsFace R) (hdR : faceDim R + 2 = P.dim)
    (F : FacetType P) (hRF : R ⊆ F.val.val) :
    faceVertices P R ∈ simplexBoundary (faceVertices P F.val.val) := by
  have hsub := faceVertices_mono P hRF
  have hcR := simplicial_ridge_vertices_card P hs hR F hRF
  have hcF := boundaryFacets_pure P hs (faceVertices P F.val.val)
    ((mem_boundaryFacets P _).mpr ⟨F, rfl⟩)
  change (faceVertices P F.val.val).card = P.dim at hcF
  have hstrict : faceVertices P R ⊂ faceVertices P F.val.val := by
    apply hsub.ssubset_of_ne
    intro heq
    have h := congrArg Finset.card heq
    omega
  obtain ⟨x, hxF, hxR⟩ := Finset.exists_of_ssubset hstrict
  have heq : faceVertices P R = (faceVertices P F.val.val).erase x := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      refine Finset.mem_erase.mpr ⟨?_, hsub hy⟩
      intro hyx
      exact hxR (hyx ▸ hy)
    · rw [Finset.card_erase_of_mem hxF]
      omega
  exact Finset.mem_image.mpr ⟨x, hxF, heq.symm⟩

theorem simplexBoundary_geometric_ridge (P : ConvexPolytope n) (hs : IsSimplicial P)
    (hdim : 2 ≤ P.dim) {t r : Finset (VertexType P)}
    (ht : t ∈ boundaryFacets P) (hr : r ∈ simplexBoundary t) :
    P.IsFace (vertexHull P r) ∧ faceDim (vertexHull P r) + 2 = P.dim ∧ r ⊆ t := by
  obtain ⟨x, hx, hxr⟩ := Finset.mem_image.mp hr
  have hcT : t.card = P.dim := boundaryFacets_pure P hs t ht
  have hcR : r.card + 1 = P.dim := by
    rw [← hxr, Finset.card_erase_of_mem hx]
    omega
  have hrne : r.Nonempty := Finset.card_pos.mp (by omega)
  have hrt : r ⊆ t := hxr ▸ Finset.erase_subset x t
  have hface := boundary_subsimplex_isFace P hs ht hrt hrne
  have hdimR := boundary_subsimplex_dimension P hs ht hrt hrne
  exact ⟨hface, by omega, hrt⟩

theorem boundaryFacets_ridgeDegreeTwo (P : ConvexPolytope n) (hs : IsSimplicial P)
    (hdim : 2 ≤ P.dim) : RidgeDegreeTwo (boundaryFacets P) := by
  intro r
  by_cases hne : ((boundaryFacets P).filter (fun t => r ∈ simplexBoundary t)).Nonempty
  · right
    obtain ⟨t, ht⟩ := hne
    obtain ⟨htP, hrt⟩ := Finset.mem_filter.mp ht
    have hR := simplexBoundary_geometric_ridge P hs hdim htP hrt
    let R := vertexHull P r
    have heq : (boundaryFacets P).filter (fun t => r ∈ simplexBoundary t) =
        (Finset.univ.filter (fun F : FacetType P => R ⊆ F.val.val)).image
          (fun F => faceVertices P F.val.val) := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hsP, hrs⟩
        obtain ⟨F, rfl⟩ := (mem_boundaryFacets P s).mp hsP
        have hsub := (simplexBoundary_geometric_ridge P hs hdim
          ((mem_boundaryFacets P _).mpr ⟨F, rfl⟩) hrs).2.2
        refine ⟨F, ?_, rfl⟩
        have h := vertexHull_mono P hsub
        rwa [vertexHull_faceVertices P F.val.property] at h
      · rintro ⟨F, hRF, rfl⟩
        refine ⟨(mem_boundaryFacets P _).mpr ⟨F, rfl⟩, ?_⟩
        have h := ridge_vertices_mem_simplexBoundary P hs hR.1 hR.2.1 F hRF
        simpa only [R, faceVertices_vertexHull] using h
    have hinj : Function.Injective (fun F : FacetType P => faceVertices P F.val.val) := by
      intro F G heq
      exact Subtype.ext (Subtype.ext
        ((faceVertices_eq_iff P F.val.property G.val.property).mp heq))
    rw [heq, Finset.card_image_of_injective _ hinj]
    exact card_facets_containing_ridge P hR.1 hR.2.1
  · left
    exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hne)

theorem boundaryFacets_facetGraph_connected (P : ConvexPolytope n) (hs : IsSimplicial P)
    (hdim : 2 ≤ P.dim) : (facetGraph (boundaryFacets P)).Connected := by
  let e := facetBoundaryEquiv P
  have hstep : ∀ F G : FacetType P, facetStep P F G →
      (facetGraph (boundaryFacets P)).Reachable (e F) (e G) := by
    intro F G hFG
    by_cases heq : F = G
    · subst G
      exact SimpleGraph.Reachable.refl _
    obtain ⟨R, hR, hRF, hRG, hdR⟩ := hFG
    apply SimpleGraph.Adj.reachable
    refine ⟨fun h => heq (e.injective h), faceVertices P R, ?_, ?_⟩
    · exact ridge_vertices_mem_simplexBoundary P hs hR hdR F hRF
    · exact ridge_vertices_mem_simplexBoundary P hs hR hdR G hRG
  have hpath : ∀ F G : FacetType P,
      Relation.ReflTransGen (facetStep P) F G →
        (facetGraph (boundaryFacets P)).Reachable (e F) (e G) := by
    intro F G h
    induction h with
    | refl => exact SimpleGraph.Reachable.refl _
    | tail _ hfg ih => exact ih.trans (hstep _ _ hfg)
  refine { preconnected := ?_, nonempty := ?_ }
  · intro a b
    have h := hpath (e.symm a) (e.symm b) (facetStep_connected P hdim _ _)
    simpa only [Equiv.apply_symm_apply] using h
  · obtain ⟨t, ht⟩ := boundaryFacets_nonempty P (by omega)
    exact ⟨⟨t, ht⟩⟩

/-- The actual finite facet family of every simplicial convex polytope of
dimension at least two is a minimal augmented simplicial cycle over `𝔽₂`. -/
theorem simplicial_boundary_circuit (P : ConvexPolytope n) (hs : IsSimplicial P)
    (hdim : 2 ≤ P.dim) : IsFacetCircuit id (boundaryFacets P) :=
  facetCircuit_of_ridgeDegreeTwo_connected (boundaryFacets_ridgeDegreeTwo P hs hdim)
    (boundaryFacets_facetGraph_connected P hs hdim)

end LeanEval.Geometry.PlatonicClassification
