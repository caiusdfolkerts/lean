import bier.complex
import cubical.polytope.simplicial_boundary

/-!
# Genuine convex realizations of finite simplicial complexes

Only actual singleton faces are matched with extreme vertices. The boundary
correspondence is with the faces of an actual simplicial convex polytope;
no supporting-function or sign-rank conclusion is assumed in this definition.
-/

noncomputable section

namespace Bier

open Classical Finset Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {V : Type*} [Fintype V] [DecidableEq V]

structure PolytopeRealization (K : Complex V) (n : ℕ) where
  polytope : ConvexPolytope n
  simplicial : IsSimplicial polytope
  vertexEquiv : ↥K.vertices ≃ VertexType polytope
  faces : ∀ s : Finset ↥K.vertices,
    K.face (s.image Subtype.val) ↔ s = ∅ ∨
      ∃ t ∈ boundaryFacets polytope, s.map vertexEquiv.toEmbedding ⊆ t

def Polytopal (K : Complex V) : Prop := ∃ n, Nonempty (PolytopeRealization K n)

namespace PolytopeRealization

variable {K : Complex V} {n : ℕ} (r : PolytopeRealization K n)

def point (v : ↥K.vertices) : E n := (r.vertexEquiv v).val

theorem point_injective : Function.Injective r.point :=
  Subtype.val_injective.comp r.vertexEquiv.injective

def facePoints (s : Finset ↥K.vertices) : Finset (VertexType r.polytope) :=
  s.map r.vertexEquiv.toEmbedding

@[simp] theorem mem_facePoints (s : Finset ↥K.vertices) (v : ↥K.vertices) :
    r.vertexEquiv v ∈ r.facePoints s ↔ v ∈ s := by
  simp [facePoints]

def faceHull (s : Finset ↥K.vertices) : Set (E n) :=
  vertexHull r.polytope (r.facePoints s)

theorem faceHull_isFace {s : Finset ↥K.vertices}
    (hs : K.face (s.image Subtype.val)) (hne : s.Nonempty) :
    r.polytope.IsFace (r.faceHull s) := by
  obtain h0 | ⟨t, ht, hst⟩ := (r.faces s).mp hs
  · exact (hne.ne_empty h0).elim
  · exact boundary_subsimplex_isFace r.polytope r.simplicial ht hst hne.map

@[simp] theorem point_mem_faceHull (s : Finset ↥K.vertices) (v : ↥K.vertices) :
    r.point v ∈ r.faceHull s ↔ v ∈ s := by
  have he := faceVertices_vertexHull r.polytope (r.facePoints s)
  have hm := congrArg (fun t : Finset (VertexType r.polytope) => r.vertexEquiv v ∈ t) he
  simpa only [mem_faceVertices, faceHull, point, mem_facePoints] using (eq_iff_iff.mp hm)

theorem point_mem_polytope (v : ↥K.vertices) : r.point v ∈ r.polytope.toSet :=
  subset_convexHull ℝ _ (r.vertexEquiv v).property

/-- Every nonempty abstract face has an actual supporting linear functional,
strict on every vertex outside that face. -/
theorem supporting_functional {s : Finset ↥K.vertices}
    (hs : K.face (s.image Subtype.val)) (hne : s.Nonempty) :
    ∃ (l : E n →L[ℝ] ℝ) (c : ℝ),
      (∀ v, l (r.point v) ≤ c) ∧
      (∀ v, l (r.point v) = c ↔ v ∈ s) := by
  have hF := r.faceHull_isFace hs hne
  obtain ⟨l, hl⟩ := hF.1 hF.2
  obtain ⟨y, hy⟩ := hF.2
  have hymax : ∀ x ∈ r.polytope.toSet, l x ≤ l y := by
    exact (hl ▸ hy).2
  refine ⟨l, l y, fun v => hymax _ (r.point_mem_polytope v), ?_⟩
  intro v
  constructor
  · intro hv
    apply (r.point_mem_faceHull s v).mp
    rw [hl]
    exact ⟨r.point_mem_polytope v, fun x hx => (hymax x hx).trans_eq hv.symm⟩
  · intro hv
    have hmem := (r.point_mem_faceHull s v).mpr hv
    have hmax := (hl ▸ hmem).2
    exact le_antisymm (hymax _ (r.point_mem_polytope v)) (hmax y ((hl ▸ hy).1))

/-- The vertices of every face are genuinely affinely independent. -/
theorem face_affineIndependent {s : Finset ↥K.vertices}
    (hs : K.face (s.image Subtype.val)) (hne : s.Nonempty) :
    AffineIndependent ℝ (fun v : s => r.point v.val) := by
  obtain h0 | ⟨t, ht, hst⟩ := (r.faces s).mp hs
  · exact (hne.ne_empty h0).elim
  obtain ⟨F, rfl⟩ := (mem_boundaryFacets r.polytope t).mp ht
  let f : s → VertexType (facePolytope r.polytope F.val.property) := fun v =>
    ⟨r.point v.val, Finset.mem_filter.mpr ⟨(r.vertexEquiv v.val).property,
      (mem_faceVertices r.polytope F.val.val _).mp
        (hst (Finset.mem_map.mpr ⟨v.val, v.property, rfl⟩))⟩⟩
  have hf : Function.Injective f := by
    intro v w hvw
    apply Subtype.ext
    exact r.point_injective (congrArg (fun v : VertexType
      (facePolytope r.polytope F.val.property) => v.val) hvw)
  exact (r.simplicial F.val.val F.val.property F.property).comp_embedding ⟨f, hf⟩

theorem face_card_le_dim {s : Finset ↥K.vertices}
    (hs : K.face (s.image Subtype.val)) : s.card ≤ r.polytope.dim := by
  obtain rfl | ⟨t, ht, hst⟩ := (r.faces s).mp hs
  · simp
  have htcard := boundaryFacets_pure r.polytope r.simplicial t ht
  change t.card = r.polytope.dim at htcard
  have hle := Finset.card_le_card hst
  simpa only [Finset.card_map, htcard] using hle

theorem dim_le_of_face_card_bound {s : Finset ↥K.vertices}
    (hs : K.face (s.image Subtype.val)) (hne : s.Nonempty) (q : ℕ)
    (hbound : ∀ f, K.face f → f.card ≤ q) : r.polytope.dim ≤ q := by
  obtain h0 | ⟨t, ht, _⟩ := (r.faces s).mp hs
  · exact (hne.ne_empty h0).elim
  let u := t.map r.vertexEquiv.symm.toEmbedding
  have hu : u.map r.vertexEquiv.toEmbedding = t := by
    ext v
    simp [u]
  have huf : K.face (u.image Subtype.val) :=
    (r.faces u).mpr (Or.inr ⟨t, ht, hu ▸ Finset.Subset.refl t⟩)
  have hc := hbound _ huf
  rw [Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_map] at hc
  have htcard := boundaryFacets_pure r.polytope r.simplicial t ht
  change t.card = r.polytope.dim at htcard
  rwa [htcard] at hc

theorem dim_eq_face_card {s : Finset ↥K.vertices}
    (hs : K.face (s.image Subtype.val)) (hne : s.Nonempty)
    (hbound : ∀ f, K.face f → f.card ≤ s.card) : r.polytope.dim = s.card :=
  le_antisymm (r.dim_le_of_face_card_bound hs hne _ hbound) (r.face_card_le_dim hs)

end PolytopeRealization

section LinearIndependence

variable {J E' : Type*} [Fintype J] [AddCommGroup E'] [Module ℝ E']

theorem linearIndependent_of_affineIndependent_supporting (p : J → E') (z : E')
    (hp : AffineIndependent ℝ p) (l : E' →ₗ[ℝ] ℝ) (c : ℝ)
    (hl : ∀ i, l (p i) = c) (hz : l z ≠ c) :
    LinearIndependent ℝ (fun i => p i - z) := by
  rw [Fintype.linearIndependent_iff]
  intro w hw i
  have he := congrArg l hw
  simp only [map_sum, map_smul, map_sub, map_zero, hl, smul_eq_mul] at he
  rw [← Finset.sum_mul] at he
  have hw0 : ∑ j, w j = 0 := (mul_eq_zero.mp he).resolve_right (sub_ne_zero.mpr hz.symm)
  apply (affineIndependent_iff_of_fintype ℝ p).mp hp w hw0 _ i
  rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ w p hw0 z,
    Finset.weightedVSubOfPoint_apply]
  exact hw

end LinearIndependence
end Bier
