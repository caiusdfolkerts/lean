import cubical.polytope.facet_cover
import cubical.polytope.simplex_faces

/-! # Actual facet vertex sets and the geometric ridge diamond -/

open Set Classical

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- The vertices of a geometric face, as vertices of the original polytope. -/
def faceVertices (P : ConvexPolytope n) (F : Set (E n)) : Finset (VertexType P) :=
  Finset.univ.filter (fun v => v.val ∈ F)

@[simp] theorem mem_faceVertices (P : ConvexPolytope n) (F : Set (E n))
    (v : VertexType P) : v ∈ faceVertices P F ↔ v.val ∈ F := by
  simp [faceVertices]

def faceVerticesEquiv (P : ConvexPolytope n) {F : Set (E n)} (hF : P.IsFace F) :
    VertexType (facePolytope P hF) ≃ ↥(faceVertices P F) where
  toFun v := ⟨⟨v.val, (Finset.mem_filter.mp v.property).1⟩,
    (mem_faceVertices P F _).mpr (Finset.mem_filter.mp v.property).2⟩
  invFun v := ⟨v.val.val, Finset.mem_filter.mpr
    ⟨v.val.property, (mem_faceVertices P F v.val).mp v.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem faceVertices_card (P : ConvexPolytope n) {F : Set (E n)} (hF : P.IsFace F) :
    (faceVertices P F).card = (facePolytope P hF).vertices.card := by
  simpa only [VertexType, Fintype.card_coe] using
    (Fintype.card_congr (faceVerticesEquiv P hF)).symm

theorem faceVertices_image_val (P : ConvexPolytope n) {F : Set (E n)} (hF : P.IsFace F) :
    (faceVertices P F).image (fun v => v.val) = (facePolytope P hF).vertices := by
  ext x
  simp only [Finset.mem_image, mem_faceVertices, facePolytope, Finset.mem_filter]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.property, hv⟩
  · rintro ⟨hxP, hxF⟩
    exact ⟨⟨x, hxP⟩, hxF, rfl⟩

theorem faceVertices_hull (P : ConvexPolytope n) {F : Set (E n)} (hF : P.IsFace F) :
    convexHull ℝ (((faceVertices P F).image (fun v => v.val) : Finset (E n)) : Set (E n)) = F := by
  rw [faceVertices_image_val P hF]
  exact (face_eq_hull_vertices P hF).symm

theorem faceVertices_mono (P : ConvexPolytope n) {F G : Set (E n)} (hFG : F ⊆ G) :
    faceVertices P F ⊆ faceVertices P G := by
  intro v hv
  exact (mem_faceVertices P G v).mpr (hFG ((mem_faceVertices P F v).mp hv))

theorem faceVertices_subset_iff (P : ConvexPolytope n) {F G : Set (E n)}
    (hF : P.IsFace F) (hG : P.IsFace G) :
    faceVertices P F ⊆ faceVertices P G ↔ F ⊆ G := by
  constructor
  · intro h
    rw [← faceVertices_hull P hF, ← faceVertices_hull P hG]
    exact convexHull_mono (Finset.coe_subset.mpr (Finset.image_subset_image h))
  · exact faceVertices_mono P

theorem faceVertices_eq_iff (P : ConvexPolytope n) {F G : Set (E n)}
    (hF : P.IsFace F) (hG : P.IsFace G) :
    faceVertices P F = faceVertices P G ↔ F = G := by
  constructor
  · intro h
    exact Set.Subset.antisymm ((faceVertices_subset_iff P hF hG).mp h.subset)
      ((faceVertices_subset_iff P hG hF).mp h.symm.subset)
  · rintro rfl
    rfl

/-- The finite family of all facet vertex sets, with no multiplicities. -/
def boundaryFacets (P : ConvexPolytope n) : Finset (Finset (VertexType P)) :=
  Finset.univ.image (fun F : FacetType P => faceVertices P F.val.val)

@[simp] theorem mem_boundaryFacets (P : ConvexPolytope n) (s : Finset (VertexType P)) :
    s ∈ boundaryFacets P ↔ ∃ F : FacetType P, faceVertices P F.val.val = s := by
  simp [boundaryFacets]

def facetBoundaryEquiv (P : ConvexPolytope n) : FacetType P ≃ ↥(boundaryFacets P) :=
  Equiv.ofBijective
    (fun F => ⟨faceVertices P F.val.val, (mem_boundaryFacets P _).mpr ⟨F, rfl⟩⟩)
    ⟨by
      intro F G h
      apply Subtype.ext
      apply Subtype.ext
      exact (faceVertices_eq_iff P F.val.property G.val.property).mp
        (congrArg Subtype.val h),
    by
      intro s
      obtain ⟨F, hF⟩ := (mem_boundaryFacets P s.val).mp s.property
      exact ⟨F, Subtype.ext hF⟩⟩

theorem boundaryFacets_nonempty (P : ConvexPolytope n) (hdim : 1 ≤ P.dim) :
    (boundaryFacets P).Nonempty := by
  obtain ⟨v, hv⟩ := P.vertices_nonempty
  obtain ⟨F, _⟩ := vertex_in_facet P hdim ⟨v, hv⟩
  exact ⟨_, (mem_boundaryFacets P _).mpr ⟨F, rfl⟩⟩

theorem ridge_subset_facet_strict (P : ConvexPolytope n) {R : Set (E n)}
    (hdR : faceDim R + 2 = P.dim) (F : FacetType P) (hRF : R ⊆ F.val.val) :
    R ⊂ F.val.val := by
  apply hRF.ssubset_of_ne
  intro heq
  have h := congrArg faceDim heq
  have := F.property
  omega

/-- A geometric ridge lies in exactly two facets; the second facet and the
exhaustive classification are both obtained from the proved diamond theorem. -/
theorem facet_ridge_diamond (P : ConvexPolytope n) {R : Set (E n)}
    (hR : P.IsFace R) (hdR : faceDim R + 2 = P.dim)
    (F : FacetType P) (hRF : R ⊆ F.val.val) :
    ∃ G : FacetType P, G ≠ F ∧ R ⊆ G.val.val ∧
      ∀ H : FacetType P, R ⊆ H.val.val → H = F ∨ H = G := by
  have hRF' := ridge_subset_facet_strict P hdR F hRF
  obtain ⟨G, ⟨⟨hG, hRG, hGT⟩, hGF⟩, huniq⟩ :=
    existsUnique_other_middle P hR (toSet_isFace P) hdR.symm
      F.val.property hRF' (facet_proper P F)
  have hdRG := faceDim_lt_of_ssubset P hR hG hRG
  have hdGT := faceDim_lt_of_ssubset P hG (toSet_isFace P) hGT
  have hdG : faceDim G + 1 = P.dim := by
    change faceDim G < P.dim at hdGT
    omega
  let g : FacetType P := ⟨⟨G, hG⟩, hdG⟩
  refine ⟨g, ?_, hRG.1, ?_⟩
  · intro heq
    exact hGF (congrArg (fun f : FacetType P => f.val.val) heq)
  · intro H hRH
    by_cases hHF : H = F
    · exact Or.inl hHF
    · right
      apply Subtype.ext
      apply Subtype.ext
      apply huniq H.val.val
      refine ⟨⟨H.val.property, ridge_subset_facet_strict P hdR H hRH, facet_proper P H⟩, ?_⟩
      intro heq
      exact hHF (Subtype.ext (Subtype.ext heq))

theorem card_facets_containing_ridge (P : ConvexPolytope n) {R : Set (E n)}
    (hR : P.IsFace R) (hdR : faceDim R + 2 = P.dim) :
    (Finset.univ.filter (fun F : FacetType P => R ⊆ F.val.val)).card = 2 := by
  obtain ⟨F, hF, hdF, hRF⟩ := face_contained_in_facet P hR (by omega)
  let f : FacetType P := ⟨⟨F, hF⟩, hdF⟩
  obtain ⟨g, hgf, hRg, hall⟩ := facet_ridge_diamond P hR hdR f hRF
  have heq : Finset.univ.filter (fun F : FacetType P => R ⊆ F.val.val) = {f, g} := by
    ext H
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨hall H, fun h => h.elim (fun heq => heq ▸ hRF) (fun heq => heq ▸ hRg)⟩
  rw [heq]
  simp [hgf.symm]

end LeanEval.Geometry.PlatonicClassification
