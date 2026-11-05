import bier.polytopal_relabel
import cubical.polytope.simplicial_vertex_figure

/-! Vertex links are realized by genuine convex hyperplane vertex figures. -/

noncomputable section

namespace Bier

open Classical Finset Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {V : Type*} [Fintype V] [DecidableEq V]

def boundaryComplex {n : ℕ} (P : ConvexPolytope n) : Complex (VertexType P) where
  face s := s = ∅ ∨ ∃ t ∈ boundaryFacets P, s ⊆ t
  empty := Or.inl rfl
  downward := by
    intro s t hst ht
    rcases ht with rfl | ⟨u, hu, htu⟩
    · exact Or.inl (Finset.subset_empty.mp hst)
    · exact Or.inr ⟨u, hu, hst.trans htu⟩

theorem boundaryComplex_vertex {n : ℕ} (P : ConvexPolytope n) (hd : 1 ≤ P.dim)
    (v : VertexType P) : (boundaryComplex P).face {v} := by
  obtain ⟨F, hvF⟩ := vertex_in_facet P hd v
  exact Or.inr ⟨faceVertices P F.val.val,
    (mem_boundaryFacets P _).mpr ⟨F, rfl⟩,
    Finset.singleton_subset_iff.mpr ((mem_faceVertices P _ v).mpr hvF)⟩

def boundaryComplex_realization {n : ℕ} (P : ConvexPolytope n) (hP : IsSimplicial P)
    (hd : 1 ≤ P.dim) : PolytopeRealization (boundaryComplex P) n := by
  let e : ↥(boundaryComplex P).vertices ≃ VertexType P :=
    Equiv.ofBijective Subtype.val ⟨Subtype.val_injective,
      fun v => ⟨⟨v, (Complex.mem_vertices _ _).mpr (boundaryComplex_vertex P hd v)⟩, rfl⟩⟩
  refine ⟨P, hP, e, ?_⟩
  intro s
  change ((s.image Subtype.val) = ∅ ∨ ∃ t ∈ boundaryFacets P, s.image Subtype.val ⊆ t) ↔ _
  simp only [Finset.image_eq_empty]
  rw [Finset.map_eq_image]
  rfl

theorem mem_boundary_family_link {n : ℕ} (P : ConvexPolytope n) (p : VertexType P)
    (s : Finset (VertexType P)) :
    s ∈ Cubical.Simplicial.link (boundaryFacets P) {p} ↔
      ∃ t ∈ boundaryFacets P, p ∈ t ∧ t.erase p = s := by
  simp only [Cubical.Simplicial.link, Finset.mem_image, Finset.mem_filter,
    Finset.singleton_subset_iff, Finset.sdiff_singleton_eq_erase]
  aesop

namespace PolytopeRealization

variable {K : Complex V} {n : ℕ} (r : PolytopeRealization K n)
  (v : ↥K.vertices) (D : DatiFetta r.polytope (r.vertexEquiv v).val)

def figureLabelEmbedding : VertexType D.politopo ↪ ↥K.vertices :=
  D.neighborEmbedding.trans r.vertexEquiv.symm.toEmbedding

def figureLabel (q : VertexType D.politopo) : V := (r.figureLabelEmbedding v D q).val

theorem figureLabel_injective : Function.Injective (r.figureLabel v D) :=
  Subtype.val_injective.comp (r.figureLabelEmbedding v D).injective

@[simp] theorem vertexEquiv_figureLabelEmbedding (q : VertexType D.politopo) :
    r.vertexEquiv (r.figureLabelEmbedding v D q) = D.neighborEmbedding q :=
  r.vertexEquiv.apply_symm_apply _

theorem figureLabel_ne (q : VertexType D.politopo) : r.figureLabel v D q ≠ v.val := by
  intro h
  have heq : r.figureLabelEmbedding v D q = v := Subtype.ext h
  have hh := congrArg r.vertexEquiv heq
  rw [vertexEquiv_figureLabelEmbedding] at hh
  exact D.neighborEmbedding_ne_base q hh

theorem figure_image_faces (hd : 2 ≤ r.polytope.dim) (a : Finset V) :
    (K.link v.val ((Complex.mem_vertices K _).mp v.property)).face a ↔
      ∃ s : Finset (VertexType D.politopo), (boundaryComplex D.politopo).face s ∧
        s.image (r.figureLabel v D) = a := by
  let p := r.vertexEquiv v
  have hmapFamily := D.boundary_mapFamily_eq_link r.simplicial hd
  constructor
  · intro ha
    have hvert : ∀ w ∈ a, K.face {w} := fun w hw =>
      K.downward (by simpa using Finset.mem_insert_of_mem hw) ha.2
    let b : Finset ↥K.vertices := Finset.univ.filter (fun w => w.val ∈ a)
    have hb : b.image Subtype.val = a := by
      ext w
      simp only [Finset.mem_image, b, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact hu
      · intro hw
        exact ⟨⟨w, (Complex.mem_vertices K w).mpr (hvert w hw)⟩, hw, rfl⟩
    have hface : K.face ((insert v b).image Subtype.val) := by
      rw [Finset.image_insert, hb]
      exact ha.2
    obtain hzero | ⟨T, hT, hsub⟩ := (r.faces (insert v b)).mp hface
    · exact (Finset.insert_ne_empty _ _ hzero).elim
    have hpT : p ∈ T := hsub (Finset.mem_map.mpr ⟨v, Finset.mem_insert_self _ _, rfl⟩)
    have hlink : T.erase p ∈ Cubical.Simplicial.link (boundaryFacets r.polytope) {p} :=
      (mem_boundary_family_link _ p _).mpr ⟨T, hT, hpT, rfl⟩
    rw [← hmapFamily] at hlink
    obtain ⟨U, hU, heq⟩ := (Cubical.Simplicial.mem_mapFamily _ _ _).mp hlink
    let s := U.filter (fun q => r.figureLabel v D q ∈ a)
    refine ⟨s, Or.inr ⟨U, hU, Finset.filter_subset _ _⟩, ?_⟩
    ext w
    constructor
    · rintro hw
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hw
      exact (Finset.mem_filter.mp hq).2
    · intro hw
      let wK : ↥K.vertices := ⟨w, (Complex.mem_vertices K w).mpr (hvert w hw)⟩
      have hwB : wK ∈ b := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
      have hwp : r.vertexEquiv wK ≠ p := by
        intro hh
        have hval := congrArg Subtype.val (r.vertexEquiv.injective hh)
        exact ha.1 (hval ▸ hw)
      have hwT : r.vertexEquiv wK ∈ T.erase p := Finset.mem_erase.mpr
        ⟨hwp, hsub (Finset.mem_map.mpr ⟨wK, Finset.mem_insert_of_mem hwB, rfl⟩)⟩
      rw [← heq] at hwT
      obtain ⟨q, hqU, hq⟩ := Finset.mem_map.mp hwT
      have hlabel : r.figureLabel v D q = w := by
        change (r.vertexEquiv.symm (D.neighborEmbedding q)).val = w
        rw [hq, r.vertexEquiv.symm_apply_apply]
      exact Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨hqU, hlabel.symm ▸ hw⟩, hlabel⟩
  · rintro ⟨s, hs, rfl⟩
    rcases hs with rfl | ⟨U, hU, hsU⟩
    · simpa using (K.link v.val ((Complex.mem_vertices K _).mp v.property)).empty
    have hlink : U.map D.neighborEmbedding ∈ Cubical.Simplicial.link
        (boundaryFacets r.polytope) {p} := by
      rw [← hmapFamily]
      exact (Cubical.Simplicial.mem_mapFamily _ _ _).mpr ⟨U, hU, rfl⟩
    obtain ⟨T, hT, hpT, heq⟩ := (mem_boundary_family_link _ p _).mp hlink
    refine ⟨?_, ?_⟩
    · intro hv
      obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hv
      exact r.figureLabel_ne v D q hq
    · let b := insert v (s.map (r.figureLabelEmbedding v D))
      have himage : b.image Subtype.val = insert v.val (s.image (r.figureLabel v D)) := by
        simp only [b, Finset.image_insert, Finset.map_eq_image, Finset.image_image]
        rfl
      rw [← himage]
      apply (r.faces b).mpr
      refine Or.inr ⟨T, hT, ?_⟩
      intro q hq
      obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hq
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact hpT
      · obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hw
        change r.vertexEquiv (r.figureLabelEmbedding v D z) ∈ T
        rw [vertexEquiv_figureLabelEmbedding]
        have hzU : D.neighborEmbedding z ∈ U.map D.neighborEmbedding :=
          Finset.mem_map.mpr ⟨z, hsU hz, rfl⟩
        rw [← heq] at hzU
        exact Finset.mem_of_mem_erase hzU

theorem link_polytopal (hd : 2 ≤ r.polytope.dim) :
    Polytopal (K.link v.val ((Complex.mem_vertices K _).mp v.property)) := by
  let D : DatiFetta r.polytope (r.vertexEquiv v).val :=
    Classical.choice (esiste_datiFetta r.polytope (r.vertexEquiv v).property (by
      change 1 ≤ r.polytope.dim
      omega))
  have hdim := D.politopo_dim_add_one (by omega)
  have hs := D.isSimplicial_of_simplicial r.simplicial hd
  have heq : K.link v.val ((Complex.mem_vertices K _).mp v.property) =
      (boundaryComplex D.politopo).map (r.figureLabel v D) := by
    apply Complex.ext
    funext a
    exact propext (r.figure_image_faces v D hd a)
  rw [heq]
  apply ((boundaryComplex D.politopo).polytopal_map_iff (r.figureLabel v D)
    (r.figureLabel_injective v D)).mpr
  exact ⟨n, ⟨boundaryComplex_realization D.politopo hs (by omega)⟩⟩

end PolytopeRealization
end Bier
