import cubical.polytope.cube_graph
import cubical.polytope.face_graph
import cubical.polytope.bipartition

/-! # Square faces of an actual cubical polytope

The statements here start with exposed geometric faces and a face-poset
isomorphism to the standard cube. The corner identities are derived from
the free-coordinate description of cube faces.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

theorem face_contained_in_facet (P : ConvexPolytope n)
    {F : Set (E n)} (hF : P.IsFace F) (hdF : faceDim F < P.dim) :
    ∃ K : Set (E n), P.IsFace K ∧ faceDim K + 1 = P.dim ∧ F ⊆ K := by
  classical
  suffices H : ∀ k : ℕ, ∀ F : Set (E n), P.IsFace F →
      P.dim - 1 - faceDim F ≤ k → faceDim F < P.dim →
      ∃ K : Set (E n), P.IsFace K ∧ faceDim K + 1 = P.dim ∧ F ⊆ K by
    exact H (P.dim - 1 - faceDim F) F hF le_rfl hdF
  intro k
  induction k with
  | zero =>
    intro F hF hk hlt
    exact ⟨F, hF, by omega, Set.Subset.rfl⟩
  | succ k ih =>
    intro F hF hk hlt
    by_cases heq : faceDim F + 1 = P.dim
    · exact ⟨F, hF, heq, Set.Subset.rfl⟩
    · have hgap : faceDim F + 2 ≤ P.dim := by omega
      obtain ⟨G, hG, hFG, hne⟩ := interpolazione P hF hgap
      have hdFG := faceDim_lt_of_ssubset P hF hG hFG
      have hdG : faceDim G < P.dim := by
        apply faceDim_lt_of_ssubset P hG (toSet_isFace P)
        exact ⟨face_subset_toSet P hG, fun h => hne
          (Set.Subset.antisymm (face_subset_toSet P hG) h)⟩
      obtain ⟨K, hK, hdK, hGK⟩ := ih G hG (by omega) hdG
      exact ⟨K, hK, hdK, hFG.1.trans hGK⟩

def cubeCodeGraphIso {d : ℕ} (P : ConvexPolytope n) (hd : 1 ≤ d)
    (φ : FaceType P ≃o FaceType (standardCube d)) :
    polytopeGraph P ≃g Cubical.Cube.graph d :=
  (graphOrderIso φ).trans (cubeGraphIso d hd).symm

theorem cubeCodeGraphIso_val {d : ℕ} (P : ConvexPolytope n) (hd : 1 ≤ d)
    (φ : FaceType P ≃o FaceType (standardCube d)) (v : VertexType P) :
    vertIper (cubeCodeGraphIso P hd φ v) = (vertexOrderEquiv φ v).val := by
  exact congrArg Subtype.val ((cubeGraphIso d hd).apply_symm_apply
    (vertexOrderEquiv φ v))

theorem cubeCodeGraphIso_mem_iff {d : ℕ} (P : ConvexPolytope n) (hd : 1 ≤ d)
    (φ : FaceType P ≃o FaceType (standardCube d)) (v : VertexType P)
    (F : FaceType P) :
    vertIper (cubeCodeGraphIso P hd φ v) ∈ (φ F).val ↔ v.val ∈ F.val := by
  rw [cubeCodeGraphIso_val]
  exact vertexOrderEquiv_mem_iff φ v F

theorem square_corners_of_cube_equivalence {d : ℕ} (P : ConvexPolytope n)
    (hd : 1 ≤ d) (φ : FaceType P ≃o FaceType (standardCube d)) :
    HasSquareTwoFaceCorners P := by
  classical
  intro F hF hdF v a b hv ha hb hva hvb hab
  let ψ := cubeCodeGraphIso P hd φ
  let G : FaceType (standardCube d) := φ ⟨F, hF⟩
  have hvG : vertIper (ψ v) ∈ G.val :=
    (cubeCodeGraphIso_mem_iff P hd φ v ⟨F, hF⟩).mpr hv
  let A := iperFaceFree G.val (ψ v)
  have hA : A.card = 2 :=
    (ipercubo_face_free_card d hd G.property hvG).trans
      ((faceOrderIso_dimension φ ⟨F, hF⟩).trans hdF)
  have hmem (x : VertexType P) : ψ x ∈ Cubical.Cube.FaceAt (ψ v) A ↔ x.val ∈ F := by
    change (∀ i, i ∉ A → ψ x i = ψ v i) ↔ x.val ∈ F
    rw [← vertIper_mem_face_iff d hd G.property hvG (ψ x)]
    exact cubeCodeGraphIso_mem_iff P hd φ x ⟨F, hF⟩
  obtain ⟨z, hz, hzv, haz, hbz, hcorners⟩ := Cubical.Cube.square_completion
    (ψ v) (ψ a) (ψ b) A hA ((hmem a).mpr ha) ((hmem b).mpr hb)
      (ψ.map_rel_iff.mpr hva) (ψ.map_rel_iff.mpr hvb)
      (fun h => hab (ψ.injective h))
  refine ⟨ψ.symm z, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    apply hzv
    simpa using congrArg ψ h
  · apply (hmem _).mp
    simpa using hz
  · apply ψ.map_rel_iff.mp
    simpa using haz
  · apply ψ.map_rel_iff.mp
    simpa using hbz
  · intro u hu hvu
    rcases hcorners (ψ u) ((hmem u).mpr hu) (ψ.map_rel_iff.mpr hvu) with h | h
    · exact Or.inl (ψ.injective h)
    · exact Or.inr (ψ.injective h)

/-- Every two-face of a cubical polytope has the full square-corner incidence
property, as a consequence of its actual facet face posets. -/
theorem IsCubical.square_corners (P : ConvexPolytope n) (hc : IsCubical P)
    (hdim : 3 ≤ P.dim) : HasSquareTwoFaceCorners P := by
  classical
  intro F hF hdF v a b hv ha hb hva hvb hab
  obtain ⟨K, hK, hdK, hFK⟩ := face_contained_in_facet P hF (by omega)
  obtain ⟨φ⟩ := hc K hK hdK
  let Q := facePolytope P hK
  have hFQ : Q.IsFace F := facePolytope_isFace_of P hK hF hFK
  let v' : VertexType Q := ⟨v.val, Finset.mem_filter.mpr ⟨v.property, hFK hv⟩⟩
  let a' : VertexType Q := ⟨a.val, Finset.mem_filter.mpr ⟨a.property, hFK ha⟩⟩
  let b' : VertexType Q := ⟨b.val, Finset.mem_filter.mpr ⟨b.property, hFK hb⟩⟩
  have hva' : (polytopeGraph Q).Adj v' a' :=
    (facePolytope_graph_adj_iff P hK v' a').mpr hva
  have hvb' : (polytopeGraph Q).Adj v' b' :=
    (facePolytope_graph_adj_iff P hK v' b').mpr hvb
  have hab' : a' ≠ b' := fun h => hab (Subtype.ext
    (congrArg (fun x : VertexType Q => x.val) h))
  obtain ⟨z', hzv, hzF, haz, hbz, hcorners⟩ :=
    square_corners_of_cube_equivalence Q (by omega) φ F hFQ hdF
      v' a' b' hv ha hb hva' hvb' hab'
  let z := faceVertexInclusion P hK z'
  refine ⟨z, ?_, hzF, (facePolytope_graph_adj_iff P hK a' z').mp haz,
    (facePolytope_graph_adj_iff P hK b' z').mp hbz, ?_⟩
  · intro h
    exact hzv (Subtype.ext (congrArg (fun x : VertexType P => x.val) h))
  · intro u hu hvu
    let u' : VertexType Q := ⟨u.val, Finset.mem_filter.mpr ⟨u.property, hFK hu⟩⟩
    have hvu' : (polytopeGraph Q).Adj v' u' :=
      (facePolytope_graph_adj_iff P hK v' u').mpr hvu
    rcases hcorners u' hu hvu' with h | h
    · exact Or.inl (Subtype.ext (congrArg (fun x : VertexType Q => x.val) h))
    · exact Or.inr (Subtype.ext (congrArg (fun x : VertexType Q => x.val) h))

theorem IsCubical.bipartite (P : ConvexPolytope n) (hc : IsCubical P)
    (hdim : 3 ≤ P.dim) : (polytopeGraph P).Colorable 2 :=
  polytopeGraph_colorable_two_of_square_corners P (by omega)
    (hc.square_corners P hdim)

end LeanEval.Geometry.PlatonicClassification
