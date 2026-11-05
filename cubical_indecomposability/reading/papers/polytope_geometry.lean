module
public import cubical.polytope.face_order
public import Mathlib.Analysis.Convex.Between

@[expose] public section

/-!
# Geometric consequences of ordinary combinatorial equivalence

These results do not add rank, incidence, or general-position hypotheses to
the face-order isomorphism.  They extract them from the actual convex bodies.
-/

noncomputable section

open Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

namespace Papers.Polytopes

variable {d e : ℕ}

theorem vertex_mem_body (P : ConvexPolytope d) {v : E d}
    (hv : v ∈ P.vertices) : v ∈ P.toSet :=
  subset_convexHull ℝ _ hv

theorem vertex_is_extreme (P : ConvexPolytope d) {v : E d}
    (hv : v ∈ P.vertices) : v ∈ P.toSet.extremePoints ℝ := by
  change v ∈ (convexHull ℝ (P.vertices : Set (E d))).extremePoints ℝ
  rw [← P.vertices_eq_extremePoints]
  exact hv

theorem vertex_mem_segment_iff (P : ConvexPolytope d) {x y z : E d}
    (hx : x ∈ P.vertices) (hy : y ∈ P.vertices) (hz : z ∈ P.vertices) :
    z ∈ segment ℝ x y ↔ z = x ∨ z = y := by
  constructor
  · intro h
    exact ((mem_extremePoints_iff_forall_segment.mp (vertex_is_extreme P hz)).2
      x (vertex_mem_body P hx) y (vertex_mem_body P hy) h).imp Eq.symm Eq.symm
  · rintro (h | h)
    · rw [h]
      exact left_mem_segment ℝ x y
    · rw [h]
      exact right_mem_segment ℝ x y

/-- No three distinct actual vertices are collinear, in any dimension. -/
theorem vertices_not_collinear (P : ConvexPolytope d) {x y z : E d}
    (hx : x ∈ P.vertices) (hy : y ∈ P.vertices) (hz : z ∈ P.vertices)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ¬Collinear ℝ ({x, y, z} : Set (E d)) := by
  intro h
  rcases h.wbtw_or_wbtw_or_wbtw with h | h | h
  · rcases (vertex_mem_segment_iff P hx hz hy).mp h.mem_segment with h | h
    · exact hxy h.symm
    · exact hyz h
  · rcases (vertex_mem_segment_iff P hy hx hz).mp h.mem_segment with h | h
    · exact hyz h.symm
    · exact hxz h.symm
  · rcases (vertex_mem_segment_iff P hz hy hx).mp h.mem_segment with h | h
    · exact hxz h
    · exact hxy h

/-- A face's affine span cannot pick up an additional point of the body. -/
theorem body_inter_affineSpan_face (P : ConvexPolytope d)
    {F : Set (E d)} (hF : P.IsFace F) :
    P.toSet ∩ (affineSpan ℝ F : Set (E d)) = F := by
  obtain ⟨x₀, hx₀⟩ := hF.2
  obtain ⟨l, hl⟩ := hF.1 hF.2
  have hx₀' : x₀ ∈ P.toSet ∧ ∀ y ∈ P.toSet, l y ≤ l x₀ := by
    rw [hl] at hx₀
    exact hx₀
  have hconst : Set.EqOn l.toLinearMap.toAffineMap
      (AffineMap.const ℝ (E d) (l x₀)) F := by
    intro y hy
    have hy' : y ∈ P.toSet ∧ ∀ z ∈ P.toSet, l z ≤ l y := by
      rw [hl] at hy
      exact hy
    exact le_antisymm (hx₀'.2 y hy'.1) (hy'.2 x₀ hx₀'.1)
  have hspan := AffineMap.eqOn_affineSpan (k := ℝ) hconst
  apply Set.Subset.antisymm
  · rintro y ⟨hyP, hyspan⟩
    rw [hl]
    refine ⟨hyP, fun z hz => ?_⟩
    have hy : l y = l x₀ := hspan hyspan
    rw [hy]
    exact hx₀'.2 z hz
  · intro y hy
    exact ⟨hF.1.subset hy, subset_affineSpan ℝ _ hy⟩

theorem vertex_notMem_affineSpan_face (P : ConvexPolytope d)
    {F : Set (E d)} (hF : P.IsFace F) {v : E d}
    (hv : v ∈ P.vertices) (hvF : v ∉ F) : v ∉ affineSpan ℝ F := by
  intro h
  apply hvF
  rw [← body_inter_affineSpan_face P hF]
  exact ⟨vertex_mem_body P hv, h⟩

def vertexFace (P : ConvexPolytope d) (v : VertexType P) : FaceType P :=
  ⟨{v.val}, vertex_isFace P v.property⟩

@[simp] theorem vertexFace_val (P : ConvexPolytope d) (v : VertexType P) :
    (vertexFace P v).val = {v.val} := rfl

@[simp] theorem vertexFace_dim (P : ConvexPolytope d) (v : VertexType P) :
    faceDim (vertexFace P v).val = 0 := faceDim_singleton v.val

theorem vertexFace_injective (P : ConvexPolytope d) :
    Function.Injective (vertexFace P) := by
  intro v w h
  apply Subtype.ext
  exact Set.singleton_injective (congrArg Subtype.val h)

@[simp] theorem vertexFace_le_iff (P : ConvexPolytope d) (v : VertexType P)
    (F : FaceType P) : vertexFace P v ≤ F ↔ v.val ∈ F.val :=
  Set.singleton_subset_iff

theorem exists_vertex_of_zero_face (P : ConvexPolytope d) (F : FaceType P)
    (hd : faceDim F.val = 0) : ∃ v : VertexType P, vertexFace P v = F := by
  obtain ⟨v, hvF, hv⟩ := punto_di_faccia0_e_vertice P F.property hd
  exact ⟨⟨v, hv⟩, Subtype.ext hvF.symm⟩

/-- The vertex induced by an isomorphism of ordinary nonempty face posets. -/
def imageVertex {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : FaceType P ≃o FaceType Q) (v : VertexType P) : VertexType Q :=
  Classical.choose (exists_vertex_of_zero_face Q (φ (vertexFace P v))
    ((faceOrderIso_dimension φ (vertexFace P v)).trans (vertexFace_dim P v)))

@[simp] theorem imageVertex_face {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : FaceType P ≃o FaceType Q) (v : VertexType P) :
    vertexFace Q (imageVertex φ v) = φ (vertexFace P v) :=
  Classical.choose_spec (exists_vertex_of_zero_face Q (φ (vertexFace P v))
    ((faceOrderIso_dimension φ (vertexFace P v)).trans (vertexFace_dim P v)))

@[simp] theorem imageVertex_mem_iff {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : FaceType P ≃o FaceType Q) (v : VertexType P) (F : FaceType P) :
    (imageVertex φ v).val ∈ (φ F).val ↔ v.val ∈ F.val := by
  rw [← vertexFace_le_iff, imageVertex_face, φ.le_iff_le, vertexFace_le_iff]

/-- Vertex correspondence is derived from the face-order isomorphism. -/
def vertexEquivOfFaceOrder {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : FaceType P ≃o FaceType Q) : VertexType P ≃ VertexType Q where
  toFun := imageVertex φ
  invFun := imageVertex φ.symm
  left_inv v := by
    apply vertexFace_injective P
    rw [imageVertex_face, imageVertex_face, OrderIso.symm_apply_apply]
  right_inv v := by
    apply vertexFace_injective Q
    rw [imageVertex_face, imageVertex_face, OrderIso.apply_symm_apply]

theorem faceOrderIso_vertex_card {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : FaceType P ≃o FaceType Q) : P.vertices.card = Q.vertices.card := by
  classical
  simpa only [VertexType, Fintype.card_coe] using
    Fintype.card_congr (vertexEquivOfFaceOrder φ)

def wholeFace (P : ConvexPolytope d) : FaceType P :=
  ⟨P.toSet, IsExposed.refl _, by
    obtain ⟨v, hv⟩ := P.vertices_nonempty
    exact ⟨v, vertex_mem_body P hv⟩⟩

theorem le_wholeFace (P : ConvexPolytope d) (F : FaceType P) :
    F ≤ wholeFace P := F.property.1.subset

@[simp] theorem image_wholeFace {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : FaceType P ≃o FaceType Q) : φ (wholeFace P) = wholeFace Q := by
  apply le_antisymm
  · exact le_wholeFace Q _
  · have h := φ.monotone (le_wholeFace P (φ.symm (wholeFace Q)))
    simpa using h

theorem faceOrderIso_polytope_dim {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : FaceType P ≃o FaceType Q) : Q.dim = P.dim := by
  have h := faceOrderIso_dimension φ (wholeFace P)
  rw [image_wholeFace] at h
  exact h

end Papers.Polytopes
