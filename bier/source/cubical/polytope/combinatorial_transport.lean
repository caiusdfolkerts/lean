import cubical.polytope.face_order
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Transporting vertices, incidence, and edges by a face-poset isomorphism

The maps in this file are induced by ordinary geometric singleton faces.
They identify the actual extreme vertices and actual edge graphs, without
adding a separate combinatorial correspondence to the hypotheses.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n m : ℕ} {P : ConvexPolytope n} {Q : ConvexPolytope m}

abbrev ZeroFaceType (P : ConvexPolytope n) := {F : FaceType P // faceDim F.val = 0}

def vertexZeroFace (P : ConvexPolytope n) (v : VertexType P) : ZeroFaceType P :=
  ⟨⟨{v.val}, vertex_isFace P v.property⟩, faceDim_singleton v.val⟩

theorem vertexZeroFace_bijective (P : ConvexPolytope n) :
    Function.Bijective (vertexZeroFace P) := by
  constructor
  · intro u v h
    apply Subtype.ext
    apply Set.singleton_injective
    exact congrArg (fun F : ZeroFaceType P ↦ F.val.val) h
  · rintro ⟨⟨F, hF⟩, hdim⟩
    obtain ⟨v, rfl, hv⟩ := punto_di_faccia0_e_vertice P hF hdim
    exact ⟨⟨v, hv⟩, rfl⟩

def vertexFaceEquiv (P : ConvexPolytope n) : VertexType P ≃ ZeroFaceType P :=
  Equiv.ofBijective (vertexZeroFace P) (vertexZeroFace_bijective P)

def zeroFaceOrderEquiv (φ : FaceType P ≃o FaceType Q) : ZeroFaceType P ≃ ZeroFaceType Q where
  toFun F := ⟨φ F.val, (faceOrderIso_dimension φ F.val).trans F.property⟩
  invFun F := ⟨φ.symm F.val, (faceOrderIso_dimension φ.symm F.val).trans F.property⟩
  left_inv F := Subtype.ext (φ.symm_apply_apply F.val)
  right_inv F := Subtype.ext (φ.apply_symm_apply F.val)

/-- The vertex bijection determined by a combinatorial equivalence. -/
def vertexOrderEquiv (φ : FaceType P ≃o FaceType Q) : VertexType P ≃ VertexType Q :=
  (vertexFaceEquiv P).trans ((zeroFaceOrderEquiv φ).trans (vertexFaceEquiv Q).symm)

theorem singleton_vertexOrderEquiv (φ : FaceType P ≃o FaceType Q) (v : VertexType P) :
    (φ ⟨{v.val}, vertex_isFace P v.property⟩).val = {(vertexOrderEquiv φ v).val} := by
  have h := (vertexFaceEquiv Q).apply_symm_apply
    (zeroFaceOrderEquiv φ (vertexFaceEquiv P v))
  exact (congrArg (fun F : ZeroFaceType Q ↦ F.val.val) h).symm

/-- Incidence with every face is preserved by the induced vertex bijection. -/
theorem vertexOrderEquiv_mem_iff (φ : FaceType P ≃o FaceType Q)
    (v : VertexType P) (F : FaceType P) :
    (vertexOrderEquiv φ v).val ∈ (φ F).val ↔ v.val ∈ F.val := by
  calc
    (vertexOrderEquiv φ v).val ∈ (φ F).val ↔
        {(vertexOrderEquiv φ v).val} ⊆ (φ F).val := Set.singleton_subset_iff.symm
    _ ↔ (φ ⟨{v.val}, vertex_isFace P v.property⟩).val ⊆ (φ F).val := by
      rw [singleton_vertexOrderEquiv]
    _ ↔ ({v.val} : Set (E n)) ⊆ F.val := φ.le_iff_le
    _ ↔ v.val ∈ F.val := Set.singleton_subset_iff

/-- The genuine edge graph is an invariant of the ordinary face poset. -/
def graphOrderIso (φ : FaceType P ≃o FaceType Q) : polytopeGraph P ≃g polytopeGraph Q where
  __ := vertexOrderEquiv φ
  map_rel_iff' := by
    intro u v
    change (polytopeGraph Q).Adj (vertexOrderEquiv φ u) (vertexOrderEquiv φ v) ↔
      (polytopeGraph P).Adj u v
    constructor
    · rintro ⟨hne, F, hF, hdim, hu, hv⟩
      let S : FaceType Q := ⟨F, hF⟩
      refine ⟨fun h ↦ hne (congrArg (vertexOrderEquiv φ) h),
        (φ.symm S).val, (φ.symm S).property, ?_, ?_, ?_⟩
      · exact (faceOrderIso_dimension φ.symm S).trans hdim
      · apply (vertexOrderEquiv_mem_iff φ u (φ.symm S)).mp
        simpa only [φ.apply_symm_apply] using hu
      · apply (vertexOrderEquiv_mem_iff φ v (φ.symm S)).mp
        simpa only [φ.apply_symm_apply] using hv
    · rintro ⟨hne, F, hF, hdim, hu, hv⟩
      let S : FaceType P := ⟨F, hF⟩
      refine ⟨fun h ↦ hne ((vertexOrderEquiv φ).injective h),
        (φ S).val, (φ S).property, ?_, ?_, ?_⟩
      · exact (faceOrderIso_dimension φ S).trans hdim
      · exact (vertexOrderEquiv_mem_iff φ u S).mpr hu
      · exact (vertexOrderEquiv_mem_iff φ v S).mpr hv

theorem vertices_card_eq_of_faceOrderIso (φ : FaceType P ≃o FaceType Q) :
    P.vertices.card = Q.vertices.card := by
  simpa [VertexType] using Fintype.card_congr (vertexOrderEquiv φ)

end LeanEval.Geometry.PlatonicClassification
