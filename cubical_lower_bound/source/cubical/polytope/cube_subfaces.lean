import cubical.polytope.stacking_intervals
import cubical.polytope.cube_face_affine

/-! # Face intervals and cubicality under ordinary face-poset isomorphisms -/

open Set Classical

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n m : ℕ} {P : ConvexPolytope n} {Q : ConvexPolytope m}

def faceOrderIsoOnFace (φ : FaceType P ≃o FaceType Q) (F : FaceType P) :
    FaceType (facePolytope P F.property) ≃o FaceType (facePolytope Q (φ F).property) := by
  let e : {G : FaceType P // G ≤ F} ≃o {G : FaceType Q // G ≤ φ F} := {
    toFun G := ⟨φ G.val, φ.monotone G.property⟩
    invFun G := ⟨φ.symm G.val, by simpa only [φ.symm_apply_apply] using φ.symm.monotone G.property⟩
    left_inv G := Subtype.ext (φ.symm_apply_apply G.val)
    right_inv G := Subtype.ext (φ.apply_symm_apply G.val)
    map_rel_iff' := φ.map_rel_iff }
  exact (facePolytopeIntervalOrderIso P F).trans
    (e.trans (facePolytopeIntervalOrderIso Q (φ F)).symm)

theorem faceOrderIso_toSet (φ : FaceType P ≃o FaceType Q) :
    φ ⟨P.toSet, toSet_isFace P⟩ = ⟨Q.toSet, toSet_isFace Q⟩ := by
  apply le_antisymm
  · exact face_subset_toSet Q (φ ⟨P.toSet, toSet_isFace P⟩).property
  · have h : φ.symm ⟨Q.toSet, toSet_isFace Q⟩ ≤ ⟨P.toSet, toSet_isFace P⟩ :=
      face_subset_toSet P (φ.symm ⟨Q.toSet, toSet_isFace Q⟩).property
    simpa only [φ.apply_symm_apply] using φ.monotone h

theorem faceOrderIso_dim (φ : FaceType P ≃o FaceType Q) : Q.dim = P.dim := by
  have h := faceOrderIso_dimension φ ⟨P.toSet, toSet_isFace P⟩
  rw [faceOrderIso_toSet φ] at h
  exact h

theorem standardCube_face_isCube (d : ℕ) (hd : 1 ≤ d)
    {F : Set (E d)} (hF : (standardCube d).IsFace F) :
    CombinatoriallyEquivalent (facePolytope (standardCube d) hF) (standardCube (faceDim F)) := by
  obtain ⟨v, hv⟩ := (facePolytope (standardCube d) hF).vertices_nonempty
  obtain ⟨s, rfl⟩ := mem_verticiIper.mp (Finset.mem_filter.mp hv).1
  have hs := (Finset.mem_filter.mp hv).2
  have φ := (cubeFaceOrderIso d hd hF s hs).symm
  rw [ipercubo_face_free_card d hd hF hs] at φ
  exact ⟨φ⟩

theorem cubeEquivalent_face_isCube (d : ℕ) (hd : 1 ≤ d)
    (φ : FaceType P ≃o FaceType (standardCube d)) (F : FaceType P) :
    CombinatoriallyEquivalent (facePolytope P F.property) (standardCube (faceDim F.val)) := by
  obtain ⟨ψ⟩ := standardCube_face_isCube d hd (φ F).property
  rw [faceOrderIso_dimension φ F] at ψ
  exact ⟨(faceOrderIsoOnFace φ F).trans ψ⟩

private theorem polytope_ext_vertices (P Q : ConvexPolytope n)
    (h : P.vertices = Q.vertices) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

theorem facePolytope_of_subface_eq (P : ConvexPolytope n)
    {F K : Set (E n)} (hF : P.IsFace F) (hK : P.IsFace K) (hFK : F ⊆ K) :
    facePolytope (facePolytope P hK) (facePolytope_isFace_of P hK hF hFK) =
      facePolytope P hF :=
  polytope_ext_vertices _ _ (facePolytope_vertices_of_subface P hF hK hFK)

/-- Every nonempty proper face of a cubical polytope has the ordinary
face lattice of a cube of its actual affine dimension. -/
theorem IsCubical.properFace_isCube (P : ConvexPolytope n) (hc : IsCubical P)
    (hdim : 2 ≤ P.dim) {F : Set (E n)} (hF : P.IsFace F) (hdF : faceDim F < P.dim) :
    CombinatoriallyEquivalent (facePolytope P hF) (standardCube (faceDim F)) := by
  obtain ⟨K, hK, hdK, hFK⟩ := face_contained_in_facet P hF hdF
  obtain ⟨φ⟩ := hc K hK hdK
  have h := cubeEquivalent_face_isCube (P.dim - 1) (by omega) φ
    ⟨F, facePolytope_isFace_of P hK hF hFK⟩
  rwa [facePolytope_of_subface_eq P hF hK hFK] at h

/-- Cubicality is invariant under the ordinary nonempty face poset. -/
theorem IsCubical.of_faceOrderIso (hc : IsCubical P) (φ : FaceType P ≃o FaceType Q) :
    IsCubical Q := by
  intro F hF hdF
  let G : FaceType P := φ.symm ⟨F, hF⟩
  have hdim := faceOrderIso_dim φ
  have hdG : faceDim G.val + 1 = P.dim := by
    have h := faceOrderIso_dimension φ.symm ⟨F, hF⟩
    change faceDim G.val = faceDim F at h
    omega
  obtain ⟨ψ⟩ := hc G.val G.property hdG
  have e := faceOrderIsoOnFace φ.symm ⟨F, hF⟩
  have hfinal := e.trans ψ
  rw [← hdim] at hfinal
  exact ⟨hfinal⟩

end LeanEval.Geometry.PlatonicClassification
