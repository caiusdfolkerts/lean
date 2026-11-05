import bier.stellar_coordinates
import bier.realization_from_faces

/-! Inverting a facet subdivision by deleting the actual new extreme vertex. -/
noncomputable section
namespace Bier
open Classical Finset Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
variable {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
namespace StellarFacetData
variable {K L : Complex V} {F : Finset V} {v : V}
    (h : StellarFacetData K L F v) (r : PolytopeRealization L n)

include h

theorem neighbors_nonempty : (h.neighbors r).Nonempty := by
  apply Finset.card_pos.mp
  rw [h.neighbors_card]
  exact lt_of_lt_of_le (by decide : 0 < 2) h.card_two

theorem deletion_nonempty : (r.polytope.vertices.erase (h.apex r).val).Nonempty := by
  obtain ⟨w, hw⟩ := h.neighbors_nonempty r
  refine ⟨w.val, Finset.mem_erase.mpr ⟨?_, w.property⟩⟩
  intro he
  exact h.apex_not_mem r ((Subtype.ext he : w = h.apex r) ▸ hw)

def deletedPolytope : ConvexPolytope n := deleteVertex r.polytope (h.apex r) (h.deletion_nonempty r)

/-- The retained extreme vertices are exactly the original complex's actual vertices. -/
def deletedVertexEquiv : K.vertices ≃ VertexType (h.deletedPolytope r) where
  toFun w := ⟨(r.vertexEquiv ⟨w.val, h.old_vertex_mem w.property⟩).val,
    Finset.mem_erase.mpr ⟨by
      intro he
      have he' := r.vertexEquiv.injective (Subtype.ext he)
      have hh : w.val = v := congrArg Subtype.val he'
      exact h.ghost (hh ▸ w.property), (r.vertexEquiv _).property⟩⟩
  invFun w := ⟨r.label (deleteVertexEmbedding r.polytope (h.apex r) (h.deletion_nonempty r) w), by
    have hw := r.label_mem (deleteVertexEmbedding r.polytope (h.apex r) (h.deletion_nonempty r) w)
    rw [h.vertices] at hw
    apply (Finset.mem_insert.mp hw).resolve_left
    intro he
    have he' := r.label.injective (he.trans (h.label_apex r).symm)
    exact (Finset.mem_erase.mp w.property).1 (congrArg Subtype.val he')⟩
  left_inv w := by
    apply Subtype.ext
    change (r.vertexEquiv.symm (r.vertexEquiv ⟨w.val, h.old_vertex_mem w.property⟩)).val = w.val
    rw [r.vertexEquiv.symm_apply_apply]
  right_inv w := by
    apply Subtype.ext
    change (r.vertexEquiv (r.vertexEquiv.symm
      (deleteVertexEmbedding r.polytope (h.apex r) (h.deletion_nonempty r) w))).val = w.val
    rw [r.vertexEquiv.apply_symm_apply]
    rfl

@[simp] theorem deleted_label (w : K.vertices) :
    r.label (deleteVertexEmbedding r.polytope (h.apex r) (h.deletion_nonempty r)
      (h.deletedVertexEquiv r w)) = w.val := by
  change (r.vertexEquiv.symm (r.vertexEquiv ⟨w.val, h.old_vertex_mem w.property⟩)).val = w.val
  rw [r.vertexEquiv.symm_apply_apply]

theorem outside_corner (hout : ∃ w ∈ K.vertices, w ∉ F) :
    ∃ w : VertexType r.polytope, w ∉ insert (h.apex r) (h.neighbors r) := by
  obtain ⟨w, hw, hwF⟩ := hout
  let q := r.vertexEquiv ⟨w, h.old_vertex_mem hw⟩
  refine ⟨q, ?_⟩
  intro hq
  rcases Finset.mem_insert.mp hq with he | ht
  · have hl := congrArg r.label he
    have hwe : w = v := by simpa [q] using hl
    exact h.ghost (hwe ▸ hw)
  · have hl := (r.mem_labelledVertices F q).mp ht
    exact hwF (by simpa [q] using hl)

theorem deleted_image_labels (s : Finset K.vertices) :
    ((s.map (h.deletedVertexEquiv r).toEmbedding).map
      (deleteVertexEmbedding r.polytope (h.apex r) (h.deletion_nonempty r))).image r.label =
      s.image Subtype.val := by
  ext x
  constructor
  · intro hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hq
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hu
    exact Finset.mem_image.mpr ⟨w, hw, (h.deleted_label r w).symm⟩
  · intro hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨_, Finset.mem_map.mpr
      ⟨_, Finset.mem_map.mpr ⟨w, hw, rfl⟩, rfl⟩, h.deleted_label r w⟩

theorem deleted_image_apex_not_mem (s : Finset K.vertices) :
    h.apex r ∉ (s.map (h.deletedVertexEquiv r).toEmbedding).map
      (deleteVertexEmbedding r.polytope (h.apex r) (h.deletion_nonempty r)) := by
  intro hp
  obtain ⟨q, hq, he⟩ := Finset.mem_map.mp hp
  exact (Finset.mem_erase.mp q.property).1 (congrArg Subtype.val he)

/-- Every original face is precisely a proper exposed face of the deleted hull. -/
theorem deleted_faces (hout : ∃ w ∈ K.vertices, w ∉ F) (s : Finset K.vertices) :
    K.face (s.image Subtype.val) ↔ s = ∅ ∨
      ProperVertexFace (h.deletedPolytope r) (s.map (h.deletedVertexEquiv r).toEmbedding) := by
  let C := h.cornerSystem r
  let hn := h.deletion_nonempty r
  let q := s.map (h.deletedVertexEquiv r).toEmbedding
  let a := q.map (C.inclusion hn)
  have hlabel : a.image r.label = s.image Subtype.val := h.deleted_image_labels r s
  have hpa : h.apex r ∉ a := h.deleted_image_apex_not_mem r s
  have hsub : a ⊆ h.neighbors r ↔ s.image Subtype.val ⊆ F := by
    rw [← hlabel]
    constructor
    · intro ha w hw
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
      exact (r.mem_labelledVertices F u).mp (ha hu)
    · intro ha w hw
      exact (r.mem_labelledVertices F w).mpr (ha (Finset.mem_image_of_mem _ hw))
  by_cases hz : s = ∅
  · subst s
    simp [K.empty]
  have hq : q.Nonempty := (Finset.nonempty_iff_ne_empty.mpr hz).map
  have ha : a.Nonempty := hq.map
  have hgeom := C.proper_face_iff hn r.simplicial (h.polytope_dimension r)
    (h.apex_not_mem r) (h.neighbors_nonempty r) (h.outside_corner r hout)
    (h.containing_apex r) hq
  change K.face (s.image Subtype.val) ↔ s = ∅ ∨ ProperVertexFace (C.deleted hn) q
  rw [or_iff_right hz, hgeom]
  constructor
  · intro hs
    rcases (h.old_iff _).mp hs with he | ⟨hLs, hvs⟩
    · right
      exact hsub.mpr (he ▸ Finset.Subset.refl F)
    · left
      rw [← hlabel, r.face_labels_iff] at hLs
      exact hLs.resolve_left ha.ne_empty
  · rintro (ho | ht)
    · apply (h.old_iff _).mpr
      right
      refine ⟨?_, ?_⟩
      · rw [← hlabel]
        exact (r.face_labels_iff a).mpr (Or.inr ho)
      · intro hv
        rw [← hlabel] at hv
        obtain ⟨w, hw, hwe⟩ := Finset.mem_image.mp hv
        exact hpa ((r.label.injective (hwe.trans (h.label_apex r).symm)) ▸ hw)
    · exact K.downward (hsub.mp ht) h.oldFace

/-- A realizable stellar facet subdivision has a realizable original boundary. -/
def inverseRealization (hout : ∃ w ∈ K.vertices, w ∉ F) : PolytopeRealization K n := by
  apply realization_of_proper_faces K (h.deletedPolytope r) (h.deletedVertexEquiv r)
    (h.deleted_faces r hout)
  intro s hs hne
  have hproper := ((h.deleted_faces r hout s).mp hs).resolve_left hne.ne_empty
  let C := h.cornerSystem r
  have hAI := C.proper_affineIndependent (h.deletion_nonempty r) r.simplicial
    (h.apex_not_mem r) (h.containing_apex r) hne.map hproper
  let f : s ↪ (s.map (h.deletedVertexEquiv r).toEmbedding) :=
    ⟨fun w => ⟨h.deletedVertexEquiv r w.val, Finset.mem_map.mpr ⟨w.val, w.property, rfl⟩⟩,
      fun w z hz => Subtype.ext ((h.deletedVertexEquiv r).injective (congrArg Subtype.val hz))⟩
  exact hAI.comp_embedding f

theorem polytopal_of_stellar (hout : ∃ w ∈ K.vertices, w ∉ F) (hL : Polytopal L) :
    Polytopal K := by
  obtain ⟨n, ⟨r⟩⟩ := hL
  exact ⟨n, ⟨h.inverseRealization r hout⟩⟩

theorem not_polytopal_stellar (hout : ∃ w ∈ K.vertices, w ∉ F) (hK : ¬ Polytopal K) :
    ¬ Polytopal L := fun hL => hK (h.polytopal_of_stellar hout hL)

end StellarFacetData
end Bier
