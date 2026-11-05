module

public import Papers.PolytopeBasicExtreme

public import Papers.PolytopeEulerRadialFigure
public import Papers.TwoFaceGraph
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Data.Fintype.Card

@[expose] public section

/-!
# Finite actual faces and graph edges

Faces are ordinary exposed subsets of the original
polytope, with their ordinary affine dimension. The finite coding is used
only to obtain a finite type; equality is proved from convex hulls of the
actual vertices. Graph edges correspond to the actual one-dimensional
faces, not to a separate abstract incidence object.
-/

noncomputable section

namespace Papers.PolytopeFaceCounting

open Set Module
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeBalinski
open scoped Classical

variable {n : ℕ}

abbrev Face (P : ConvexPolytope n) (k : ℕ) :=
  {F : PolytopeFace P // faceDim F.carrier = k}

theorem face_has_vertex (P : ConvexPolytope n) {F : Set (E n)}
    (hF : P.IsFace F) : ∃ v ∈ P.vertices, v ∈ F := by
  obtain ⟨v, hv⟩ := (facePolytope P hF).vertices_nonempty
  change v ∈ P.vertices.filter (· ∈ F) at hv
  exact ⟨v, (Finset.mem_filter.mp hv).1, (Finset.mem_filter.mp hv).2⟩

theorem face_eq_of_vertex_membership (P : ConvexPolytope n)
    {F G : Set (E n)} (hF : P.IsFace F) (hG : P.IsFace G)
    (h : ∀ v : P.vertices, v.val ∈ F ↔ v.val ∈ G) : F = G := by
  rw [face_eq_hull_vertices P hF, face_eq_hull_vertices P hG]
  congr 1
  ext x
  simp only [Finset.mem_coe, Finset.mem_filter]
  by_cases hx : x ∈ P.vertices
  · simp only [hx, true_and]
    exact h ⟨x,hx⟩
  · simp [hx]

def faceCode (P : ConvexPolytope n) (k : ℕ) (F : Face P k) :
    Finset P.vertices := Finset.univ.filter fun v => v.val ∈ F.val.carrier

theorem faceCode_injective (P : ConvexPolytope n) (k : ℕ) :
    Function.Injective (faceCode P k) := by
  intro F G heq
  apply Subtype.ext
  apply PolytopeFace.ext
  apply face_eq_of_vertex_membership P F.val.isFace G.val.isFace
  intro v
  have hh : v ∈ faceCode P k F ↔ v ∈ faceCode P k G := by rw [heq]
  simpa [faceCode] using hh

instance finiteFace (P : ConvexPolytope n) (k : ℕ) : Finite (Face P k) :=
  Finite.of_injective (faceCode P k) (faceCode_injective P k)

noncomputable instance fintypeFace (P : ConvexPolytope n) (k : ℕ) : Fintype (Face P k) :=
  Fintype.ofFinite _

theorem edge_out_adj (P : ConvexPolytope n) (e : (vertexGraph P).edgeSet) :
    GeneralVertexStep P e.val.out.1.val e.val.out.2.val := by
  change s(e.val.out.1, e.val.out.2) ∈ (vertexGraph P).edgeSet
  rw [Sym2.mk_fst_out_snd_out]
  exact e.property

def edgeFace (P : ConvexPolytope n) (e : (vertexGraph P).edgeSet) : Face P 1 :=
  ⟨⟨segment ℝ e.val.out.1.val e.val.out.2.val,
      segment_isFace_of_generalVertexStep P e.val.out.1.property (edge_out_adj P e)⟩,
    segment_faceDim_of_generalVertexStep P e.val.out.1.property (edge_out_adj P e)⟩

theorem edgeFace_vertex_iff (P : ConvexPolytope n)
    (e : (vertexGraph P).edgeSet) (v : P.vertices) :
    v.val ∈ (edgeFace P e).val.carrier ↔ v ∈ e.val := by
  have hmem : v ∈ e.val ↔ v = e.val.out.1 ∨ v = e.val.out.2 := by
    conv_lhs => rw [← Sym2.mk_fst_out_snd_out e.val]
    exact Sym2.mem_iff
  rw [hmem]
  constructor
  · intro hv
    have hh := Papers.PolytopeBasicExtreme.extreme_point_on_segment P.toSet
      (Papers.PolytopeBasicExtreme.vertex_mem_extreme P v.property)
      (Papers.PolytopeBasicExtreme.vertex_mem_body P e.val.out.1.property)
      (Papers.PolytopeBasicExtreme.vertex_mem_body P e.val.out.2.property) hv
    rcases hh with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · rintro (rfl | rfl)
    · exact left_mem_segment ℝ _ _
    · exact right_mem_segment ℝ _ _

theorem edgeFace_injective (P : ConvexPolytope n) :
    Function.Injective (edgeFace P) := by
  intro e f heq
  apply Subtype.ext
  apply Sym2.ext
  intro v
  rw [← edgeFace_vertex_iff P e v, ← edgeFace_vertex_iff P f v, heq]

theorem edgeFace_surjective (P : ConvexPolytope n) :
    Function.Surjective (edgeFace P) := by
  intro F
  obtain ⟨x,hx,hxF⟩ := face_has_vertex P F.val.isFace
  obtain ⟨y,hy,hyF,hyx,hseg⟩ :=
    spigolo_segmento P F.val.isFace F.property hx hxF
  let xx : P.vertices := ⟨x,hx⟩
  let yy : P.vertices := ⟨y,hy⟩
  have hxy : GeneralVertexStep P x y :=
    ⟨hy,hyx.symm,F.val.carrier,F.val.isFace,F.property,hxF,hyF⟩
  let e : (vertexGraph P).edgeSet := ⟨s(xx,yy),hxy⟩
  refine ⟨e,?_⟩
  apply Subtype.ext
  apply PolytopeFace.ext
  apply face_eq_of_vertex_membership P (edgeFace P e).val.isFace F.val.isFace
  intro v
  rw [edgeFace_vertex_iff]
  change (v ∈ s(xx,yy)) ↔ v.val ∈ F.val.carrier
  rw [Sym2.mem_iff]
  constructor
  · rintro (rfl | rfl) <;> assumption
  · intro hv
    have hvseg : v.val ∈ segment ℝ x y := by simpa only [← hseg] using hv
    have hh := Papers.PolytopeBasicExtreme.extreme_point_on_segment P.toSet
      (Papers.PolytopeBasicExtreme.vertex_mem_extreme P v.property)
      (Papers.PolytopeBasicExtreme.vertex_mem_body P hx)
      (Papers.PolytopeBasicExtreme.vertex_mem_body P hy) hvseg
    rcases hh with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)

def edgeFaceEquiv (P : ConvexPolytope n) :
    (vertexGraph P).edgeSet ≃ Face P 1 :=
  Equiv.ofBijective (edgeFace P) ⟨edgeFace_injective P,edgeFace_surjective P⟩

/-- Edges all of whose endpoints belong to a prescribed vertex subset. -/
abbrev EdgeIn {V : Type*} (G : SimpleGraph V) (S : Set V) :=
  {e : G.edgeSet // ∀ v, v ∈ e.val → v ∈ S}

def induceEdgeEquiv {V : Type*} (G : SimpleGraph V) (S : Set V) :
    (G.induce S).edgeSet ≃ EdgeIn G S := by
  let f : (G.induce S).edgeSet → EdgeIn G S := fun e =>
    ⟨(SimpleGraph.Embedding.induce S).mapEdgeSet e, by
      intro v hv
      obtain ⟨w,hw,rfl⟩ := Sym2.mem_map.mp hv
      exact w.property⟩
  apply Equiv.ofBijective f
  constructor
  · intro e e' heq
    exact (SimpleGraph.Embedding.induce S).mapEdgeSet.injective
      (congrArg Subtype.val heq)
  · intro e
    let x : S := ⟨e.val.val.out.1,e.property _ (Sym2.out_fst_mem _)⟩
    let y : S := ⟨e.val.val.out.2,e.property _ (Sym2.out_snd_mem _)⟩
    have hxy : G.Adj x.val y.val := by
      change s(e.val.val.out.1,e.val.val.out.2) ∈ G.edgeSet
      rw [Sym2.mk_fst_out_snd_out]
      exact e.val.property
    let ee : (G.induce S).edgeSet := ⟨s(x,y),hxy⟩
    refine ⟨ee,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change s(e.val.val.out.1,e.val.val.out.2) = e.val.val
    exact Sym2.mk_fst_out_snd_out _

abbrev FaceIn (P : ConvexPolytope n) (k : ℕ) (S : Set P.vertices) :=
  {F : Face P k // ∀ v : P.vertices, v.val ∈ F.val.carrier → v ∈ S}

def edgeInFaceEquiv (P : ConvexPolytope n) (S : Set P.vertices) :
    EdgeIn (vertexGraph P) S ≃ FaceIn P 1 S where
  toFun e := ⟨edgeFaceEquiv P e.val, by
    intro v hv
    exact e.property v ((edgeFace_vertex_iff P e.val v).mp hv)⟩
  invFun F := ⟨(edgeFaceEquiv P).symm F.val, by
    intro v hv
    apply F.property v
    have hh := (edgeFace_vertex_iff P ((edgeFaceEquiv P).symm F.val) v).mpr hv
    simpa only [show edgeFace P ((edgeFaceEquiv P).symm F.val) =
      F.val from (edgeFaceEquiv P).apply_symm_apply F.val] using hh⟩
  left_inv e := Subtype.ext ((edgeFaceEquiv P).left_inv e.val)
  right_inv F := Subtype.ext ((edgeFaceEquiv P).right_inv F.val)

def inducedEdgeFaceEquiv (P : ConvexPolytope n) (S : Set P.vertices) :
    ((vertexGraph P).induce S).edgeSet ≃ FaceIn P 1 S :=
  (induceEdgeEquiv (vertexGraph P) S).trans (edgeInFaceEquiv P S)

theorem graph_edge_card_eq_one_face_card (P : ConvexPolytope n) :
    Nat.card (vertexGraph P).edgeSet = Nat.card (Face P 1) :=
  Nat.card_congr (edgeFaceEquiv P)

end Papers.PolytopeFaceCounting
