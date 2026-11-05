import bier.geometry
import bier.link

/-! Convex realizations are invariant under faithful label changes. -/

noncomputable section

namespace Bier

open Classical
open LeanEval.Geometry.PlatonicClassification

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

namespace PolytopeRealization

def transport {K : Complex V} {L : Complex W} {n : ℕ} (r : PolytopeRealization K n)
    (e : ↥L.vertices ≃ ↥K.vertices)
    (hface : ∀ s : Finset ↥L.vertices,
      L.face (s.image Subtype.val) ↔ K.face ((s.map e.toEmbedding).image Subtype.val)) :
    PolytopeRealization L n where
  polytope := r.polytope
  simplicial := r.simplicial
  vertexEquiv := e.trans r.vertexEquiv
  faces s := by
    rw [hface s, r.faces]
    simp only [Finset.map_eq_empty, Finset.map_map]
    rfl

end PolytopeRealization

namespace Complex

theorem image_mapVertexEquiv (K : Complex V) (f : V → W) (hf : Function.Injective f)
    (s : Finset ↥K.vertices) :
    (s.map (K.mapVertexEquiv f hf).toEmbedding).image Subtype.val =
      (s.image Subtype.val).image f := by
  rw [Finset.map_eq_image, Finset.image_image, Finset.image_image]
  apply Finset.image_congr
  intro v _
  exact mapVertexEquiv_apply K f hf v

theorem polytopal_map_iff (K : Complex V) (f : V → W) (hf : Function.Injective f) :
    Polytopal (K.map f) ↔ Polytopal K := by
  let e := K.mapVertexEquiv f hf
  constructor
  · rintro ⟨n, ⟨r⟩⟩
    refine ⟨n, ⟨r.transport e ?_⟩⟩
    intro s
    rw [image_mapVertexEquiv]
    exact (map_image_face_iff K f hf _).symm
  · rintro ⟨n, ⟨r⟩⟩
    refine ⟨n, ⟨r.transport e.symm ?_⟩⟩
    intro s
    have hs : (s.map e.symm.toEmbedding).map e.toEmbedding = s := by
      ext w
      simp
    have hi := image_mapVertexEquiv K f hf (s.map e.symm.toEmbedding)
    change ((s.map e.symm.toEmbedding).map e.toEmbedding).image Subtype.val = _ at hi
    rw [hs] at hi
    rw [hi, map_image_face_iff K f hf]

end Complex
end Bier
