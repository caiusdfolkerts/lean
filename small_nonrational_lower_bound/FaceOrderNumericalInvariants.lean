module

public import Papers.NineVertexFacetShapes
public import Papers.PolytopeGeometry

@[expose] public section

/-!
# Face-order invariance of facet vertex counts

These equivalences transport genuine ranked faces and the vertices on them.
In particular the nonsimplicial-facet count is the same in every realization
of the ordinary face lattice.
-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeFacetSurplus

def rankedFaceEquivOfFaceOrder {d e k : ℕ}
    {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : FaceType P ≃o FaceType Q) : Face P k ≃ Face Q k where
  toFun F := ⟨⟨(φ ⟨F.val.carrier, F.val.isFace⟩).val,
    (φ ⟨F.val.carrier, F.val.isFace⟩).property⟩,
      (faceOrderIso_dimension φ ⟨F.val.carrier, F.val.isFace⟩).trans F.property⟩
  invFun F := ⟨⟨(φ.symm ⟨F.val.carrier, F.val.isFace⟩).val,
    (φ.symm ⟨F.val.carrier, F.val.isFace⟩).property⟩,
      (faceOrderIso_dimension φ.symm ⟨F.val.carrier, F.val.isFace⟩).trans F.property⟩
  left_inv F := by
    apply Subtype.ext
    apply PolytopeFace.ext
    exact congrArg Subtype.val (φ.symm_apply_apply ⟨F.val.carrier, F.val.isFace⟩)
  right_inv F := by
    apply Subtype.ext
    apply PolytopeFace.ext
    exact congrArg Subtype.val (φ.apply_symm_apply ⟨F.val.carrier, F.val.isFace⟩)

def verticesOnEquivOfFaceOrder {d e k : ℕ}
    {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : FaceType P ≃o FaceType Q) (F : Face P k) :
    VerticesOn P F.val.carrier ≃
      VerticesOn Q ((rankedFaceEquivOfFaceOrder φ) F).val.carrier :=
  Equiv.subtypeEquiv (vertexEquivOfFaceOrder φ)
    (fun v => (imageVertex_mem_iff φ v ⟨F.val.carrier, F.val.isFace⟩).symm)

theorem ranked_face_vertices_card_of_faceOrder {d e k : ℕ}
    {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : FaceType P ≃o FaceType Q) (F : Face P k) :
    Nat.card (VerticesOn P F.val.carrier) =
      Nat.card (VerticesOn Q ((rankedFaceEquivOfFaceOrder φ) F).val.carrier) :=
  Nat.card_congr (verticesOnEquivOfFaceOrder φ F)

theorem facetVertexCount_of_faceOrder {d e : ℕ}
    {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : FaceType P ≃o FaceType Q) (F : Face P 3) :
    facetVertexCount P F = facetVertexCount Q ((rankedFaceEquivOfFaceOrder φ) F) :=
  ranked_face_vertices_card_of_faceOrder φ F

theorem nonsimplicialFacets_card_of_faceOrder {d e : ℕ}
    {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : FaceType P ≃o FaceType Q) :
    (nonsimplicialFacets P).card = (nonsimplicialFacets Q).card := by
  let b : Face P 3 ≃ Face Q 3 := rankedFaceEquivOfFaceOrder φ
  have heq : (nonsimplicialFacets P).image b = nonsimplicialFacets Q := by
    ext F
    constructor
    · intro h
      obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp h
      rw [mem_nonsimplicialFacets, ← facetVertexCount_of_faceOrder φ G]
      exact (mem_nonsimplicialFacets P G).mp hG
    · intro hF
      refine Finset.mem_image.mpr ⟨b.symm F, ?_, b.apply_symm_apply F⟩
      rw [mem_nonsimplicialFacets, facetVertexCount_of_faceOrder φ (b.symm F)]
      change 4 < facetVertexCount Q (b (b.symm F))
      rw [b.apply_symm_apply]
      exact (mem_nonsimplicialFacets Q F).mp hF
  rw [← heq, Finset.card_image_of_injective _ b.injective]

end Papers.RationalityTen.ChirotopeDensity
