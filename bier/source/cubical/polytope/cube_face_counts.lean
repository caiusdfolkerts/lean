import cubical.polytope.cube_face_geometry

/-! # Exact face and local-degree counts in cubical polytopes -/

open Set Classical

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n m : ℕ}

def vertexOrderEquivOnFace {P : ConvexPolytope n} {Q : ConvexPolytope m}
    (φ : FaceType P ≃o FaceType Q) (F : FaceType P) :
    {v : VertexType P // v.val ∈ F.val} ≃
      {v : VertexType Q // v.val ∈ (φ F).val} :=
  (vertexOrderEquiv φ).subtypeEquiv fun v => (vertexOrderEquiv_mem_iff φ v F).symm

theorem face_vertices_card_eq_of_faceOrderIso {P : ConvexPolytope n}
    {Q : ConvexPolytope m} (φ : FaceType P ≃o FaceType Q) (F : FaceType P) :
    (facePolytope P F.property).vertices.card =
      (facePolytope Q (φ F).property).vertices.card := by
  simpa [VertexType] using Fintype.card_congr
    ((faceVertexEquiv P F.property).trans
      ((vertexOrderEquivOnFace φ F).trans (faceVertexEquiv Q (φ F).property).symm))

theorem standardCube_face_vertices_card (d : ℕ) (hd : 1 ≤ d)
    {F : Set (E d)} (hF : (standardCube d).IsFace F) :
    (facePolytope (standardCube d) hF).vertices.card = 2 ^ faceDim F := by
  classical
  obtain ⟨v, hv⟩ := (facePolytope (standardCube d) hF).vertices_nonempty
  obtain ⟨s, rfl⟩ := mem_verticiIper.mp (Finset.mem_filter.mp hv).1
  have hs := (Finset.mem_filter.mp hv).2
  have heq : (facePolytope (standardCube d) hF).vertices =
      ((Finset.univ : Finset (Fin d → Bool)).filter
        (fun t => vertIper t ∈ F)).image vertIper := by
    ext x
    constructor
    · intro hx
      obtain ⟨t, rfl⟩ := mem_verticiIper.mp (Finset.mem_filter.mp hx).1
      exact Finset.mem_image.mpr ⟨t, by simp [(Finset.mem_filter.mp hx).2], rfl⟩
    · intro hx
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_filter.mpr ⟨mem_verticiIper.mpr ⟨t, rfl⟩,
        (Finset.mem_filter.mp ht).2⟩
  rw [heq, Finset.card_image_of_injective _ vertIper_injective]
  have hfilter : (Finset.univ : Finset (Fin d → Bool)).filter
      (fun t => vertIper t ∈ F) = Finset.univ.filter
      (fun t => ∀ i, i ∉ iperFaceFree F s → t i = s i) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact vertIper_mem_face_iff d hd hF hs t
  rw [hfilter, card_signs_agree, ipercubo_face_free_card d hd hF hs]

theorem cube_equivalence_face_vertices_card {d : ℕ} (P : ConvexPolytope n)
    (hd : 1 ≤ d) (φ : FaceType P ≃o FaceType (standardCube d))
    {F : Set (E n)} (hF : P.IsFace F) :
    (facePolytope P hF).vertices.card = 2 ^ faceDim F := by
  rw [face_vertices_card_eq_of_faceOrderIso φ ⟨F, hF⟩,
    standardCube_face_vertices_card d hd,
    faceOrderIso_dimension φ ⟨F, hF⟩]

theorem cube_equivalence_face_neighbor_card {d : ℕ} (P : ConvexPolytope n)
    (hd : 1 ≤ d) (φ : FaceType P ≃o FaceType (standardCube d))
    {F : Set (E n)} (hF : P.IsFace F) (v : VertexType P) (hv : v.val ∈ F) :
    Fintype.card {a : VertexType P // a.val ∈ F ∧ (polytopeGraph P).Adj v a} =
      faceDim F := by
  classical
  let ψ := cubeCodeGraphIso P hd φ
  let G : FaceType (standardCube d) := φ ⟨F, hF⟩
  have hvG : vertIper (ψ v) ∈ G.val :=
    (cubeCodeGraphIso_mem_iff P hd φ v ⟨F, hF⟩).mpr hv
  let A := iperFaceFree G.val (ψ v)
  have hA : A.card = faceDim F :=
    (ipercubo_face_free_card d hd G.property hvG).trans
      (faceOrderIso_dimension φ ⟨F, hF⟩)
  have hmem (x : VertexType P) : ψ x ∈ Cubical.Cube.FaceAt (ψ v) A ↔ x.val ∈ F := by
    change (∀ i, i ∉ A → ψ x i = ψ v i) ↔ x.val ∈ F
    rw [← vertIper_mem_face_iff d hd G.property hvG (ψ x)]
    exact cubeCodeGraphIso_mem_iff P hd φ x ⟨F, hF⟩
  let e : {a : VertexType P // a.val ∈ F ∧ (polytopeGraph P).Adj v a} ≃
      {t : Cubical.Cube.Vertex d // t ∈ Cubical.Cube.FaceAt (ψ v) A ∧
        (Cubical.Cube.graph d).Adj (ψ v) t} :=
    ψ.toEquiv.subtypeEquiv fun x =>
      and_congr (hmem x).symm ψ.map_rel_iff.symm
  calc
    _ = Fintype.card A := Fintype.card_congr
      (e.trans (Cubical.Cube.faceNeighborEquiv (ψ v) A).symm)
    _ = faceDim F := by simpa using hA

theorem facePolytope_vertices_of_subface (P : ConvexPolytope n)
    {F K : Set (E n)} (hF : P.IsFace F) (hK : P.IsFace K) (hFK : F ⊆ K) :
    (facePolytope (facePolytope P hK) (facePolytope_isFace_of P hK hF hFK)).vertices =
      (facePolytope P hF).vertices := by
  classical
  ext v
  simp only [facePolytope, Finset.mem_filter]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hFK h.2⟩, h.2⟩⟩

theorem IsCubical.face_vertices_card (P : ConvexPolytope n) (hc : IsCubical P)
    (hdim : 2 ≤ P.dim) {F : Set (E n)} (hF : P.IsFace F)
    (hdF : faceDim F < P.dim) :
    (facePolytope P hF).vertices.card = 2 ^ faceDim F := by
  obtain ⟨K, hK, hdK, hFK⟩ := face_contained_in_facet P hF hdF
  obtain ⟨φ⟩ := hc K hK hdK
  have h := cube_equivalence_face_vertices_card (facePolytope P hK) (by omega) φ
    (facePolytope_isFace_of P hK hF hFK)
  rwa [facePolytope_vertices_of_subface P hF hK hFK] at h

theorem IsCubical.face_neighbor_card (P : ConvexPolytope n) (hc : IsCubical P)
    (hdim : 2 ≤ P.dim) {F : Set (E n)} (hF : P.IsFace F)
    (hdF : faceDim F < P.dim) (v : VertexType P) (hv : v.val ∈ F) :
    Fintype.card {a : VertexType P // a.val ∈ F ∧ (polytopeGraph P).Adj v a} =
      faceDim F := by
  classical
  obtain ⟨K, hK, hdK, hFK⟩ := face_contained_in_facet P hF hdF
  obtain ⟨φ⟩ := hc K hK hdK
  let Q := facePolytope P hK
  let v' : VertexType Q := ⟨v.val, Finset.mem_filter.mpr ⟨v.property, hFK hv⟩⟩
  let e : {a : VertexType Q // a.val ∈ F ∧ (polytopeGraph Q).Adj v' a} ≃
      {a : VertexType P // a.val ∈ F ∧ (polytopeGraph P).Adj v a} := {
    toFun a := ⟨faceVertexInclusion P hK a.val, a.property.1,
      (facePolytope_graph_adj_iff P hK v' a.val).mp a.property.2⟩
    invFun a := ⟨⟨a.val.val, Finset.mem_filter.mpr ⟨a.val.property, hFK a.property.1⟩⟩,
      a.property.1, (facePolytope_graph_adj_iff P hK v' _).mpr a.property.2⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  rw [← Fintype.card_congr e]
  exact cube_equivalence_face_neighbor_card Q (by omega) φ
    (facePolytope_isFace_of P hK hF hFK) v' hv

theorem IsCubical.quadrilateral_twoFaces (P : ConvexPolytope n) (hc : IsCubical P)
    (hdim : 3 ≤ P.dim) : HasQuadrilateralTwoFaces P := by
  intro F hF hdF
  simpa [hdF] using hc.face_vertices_card P (by omega) hF (by omega)

/-- A vertex outside a cube facet is adjacent to a vertex of that facet.
This is the matching used when propagation crosses a common ridge. -/
theorem cube_equivalence_ridge_matching {d : ℕ} (P : ConvexPolytope n)
    (hd : 1 ≤ d) (φ : FaceType P ≃o FaceType (standardCube d))
    {R : Set (E n)} (hR : P.IsFace R) (hdR : faceDim R + 1 = d)
    (v : VertexType P) (hv : v.val ∉ R) :
    ∃ w : VertexType P, w.val ∈ R ∧ (polytopeGraph P).Adj v w := by
  classical
  obtain ⟨s, hs⟩ := (facePolytope P hR).vertices_nonempty
  let s' : VertexType P := ⟨s, (Finset.mem_filter.mp hs).1⟩
  have hsR : s'.val ∈ R := (Finset.mem_filter.mp hs).2
  let ψ := cubeCodeGraphIso P hd φ
  let S : FaceType (standardCube d) := φ ⟨R, hR⟩
  have hsS : vertIper (ψ s') ∈ S.val :=
    (cubeCodeGraphIso_mem_iff P hd φ s' ⟨R, hR⟩).mpr hsR
  let A := iperFaceFree S.val (ψ s')
  have hA : A.card + 1 = d := by
    rw [show A.card = faceDim R from
      (ipercubo_face_free_card d hd S.property hsS).trans
        (faceOrderIso_dimension φ ⟨R, hR⟩)]
    exact hdR
  have hmem (x : VertexType P) : ψ x ∈ Cubical.Cube.FaceAt (ψ s') A ↔ x.val ∈ R := by
    change (∀ i, i ∉ A → ψ x i = ψ s' i) ↔ x.val ∈ R
    rw [← vertIper_mem_face_iff d hd S.property hsS (ψ x)]
    exact cubeCodeGraphIso_mem_iff P hd φ x ⟨R, hR⟩
  obtain ⟨t, ht, hvt⟩ := Cubical.Cube.ridge_matching (ψ s') (ψ v) A hA
    (fun h => hv ((hmem v).mp h))
  refine ⟨ψ.symm t, ?_, ?_⟩
  · apply (hmem _).mp
    simpa using ht
  · apply ψ.map_rel_iff.mp
    simpa using hvt

end LeanEval.Geometry.PlatonicClassification
