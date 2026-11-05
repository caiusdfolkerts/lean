import bier.geometry

/-! Recover a genuine simplicial polytope realization from its proper exposed faces. -/

noncomputable section
namespace Bier
open Classical Finset Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}

/-- The hypotheses concern the actual convex hull and exposed faces. Simpliciality
and the boundary-facet presentation are conclusions of this construction. -/
def realization_of_proper_faces (K : Complex V) (P : ConvexPolytope n)
    (e : ↥K.vertices ≃ VertexType P)
    (hfaces : ∀ s : Finset ↥K.vertices,
      K.face (s.image Subtype.val) ↔ s = ∅ ∨
        (P.IsFace (vertexHull P (s.map e.toEmbedding)) ∧
          vertexHull P (s.map e.toEmbedding) ≠ P.toSet))
    (hind : ∀ s : Finset ↥K.vertices, K.face (s.image Subtype.val) → s.Nonempty →
      AffineIndependent ℝ (fun v : s => (e v.val).val)) :
    PolytopeRealization K n := by
  have hsimp : IsSimplicial P := by
    intro F hF hdF
    have hproper : F ≠ P.toSet := by
      intro he
      rw [he] at hdF
      change P.dim + 1 = P.dim at hdF
      omega
    let s := (faceVertices P F).map e.symm.toEmbedding
    have heq : s.map e.toEmbedding = faceVertices P F := by
      ext v
      simp [s]
    have hsf : K.face (s.image Subtype.val) := (hfaces s).mpr (Or.inr (by
      rw [heq, vertexHull_faceVertices P hF]
      exact ⟨hF, hproper⟩))
    let f : VertexType (facePolytope P hF) ↪ s :=
      ⟨fun v => ⟨e.symm ⟨v.val, (Finset.mem_filter.mp v.property).1⟩, by
        simp only [s, Finset.mem_map, Equiv.toEmbedding_apply]
        refine ⟨⟨v.val, (Finset.mem_filter.mp v.property).1⟩, ?_, rfl⟩
        exact (mem_faceVertices P F _).mpr (Finset.mem_filter.mp v.property).2⟩,
      by
        intro v w h
        apply Subtype.ext
        have he := e.symm.injective (congrArg Subtype.val h)
        exact congrArg (fun x : VertexType P => x.val) he⟩
    have hne : s.Nonempty := by
      obtain ⟨v, hv⟩ := (facePolytope P hF).vertices_nonempty
      exact ⟨(f ⟨v, hv⟩).val, (f ⟨v, hv⟩).property⟩
    have hi := (hind s hsf hne).comp_embedding f
    have he : ((fun v : s => (e v.val).val) ∘ f) =
        (fun v : VertexType (facePolytope P hF) => v.val) := by
      funext v
      change (e (e.symm ⟨v.val, (Finset.mem_filter.mp v.property).1⟩)).val = v.val
      rw [Equiv.apply_symm_apply]
    rwa [he] at hi
  refine ⟨P, hsimp, e, ?_⟩
  intro s
  rw [hfaces s]
  constructor
  · rintro (hzero | ⟨hF, hproper⟩)
    · exact Or.inl hzero
    · right
      have hsub : vertexHull P (s.map e.toEmbedding) ⊆ P.toSet :=
        convexHull_mono (by
          intro x hx
          obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
          exact v.property)
      have hlt := faceDim_lt_of_ssubset P hF (toSet_isFace P)
        (hsub.ssubset_of_ne hproper)
      obtain ⟨F, hF', hdF, hFF⟩ := face_contained_in_facet P hF hlt
      refine ⟨faceVertices P F, (mem_boundaryFacets P _).mpr ⟨⟨⟨F, hF'⟩, hdF⟩, rfl⟩, ?_⟩
      intro v hv
      apply (mem_faceVertices P F v).mpr
      apply hFF
      rw [← mem_faceVertices, faceVertices_vertexHull]
      exact hv
  · rintro (hzero | ⟨t, ht, hst⟩)
    · exact Or.inl hzero
    · by_cases hzero : s = ∅
      · exact Or.inl hzero
      right
      have hne : (s.map e.toEmbedding).Nonempty := (Finset.nonempty_iff_ne_empty.mpr hzero).map
      refine ⟨boundary_subsimplex_isFace P hsimp ht hst hne, ?_⟩
      intro heq
      have hd := boundary_subsimplex_dimension P hsimp ht hst hne
      rw [heq] at hd
      have hc : (s.map e.toEmbedding).card ≤ P.dim :=
        (Finset.card_le_card hst).trans_eq (boundaryFacets_pure P hsimp t ht)
      change P.dim + 1 = (s.map e.toEmbedding).card at hd
      omega

end Bier
