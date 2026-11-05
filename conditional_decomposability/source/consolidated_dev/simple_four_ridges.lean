module
public import consolidated.deletion_geometry
public import consolidated_dev.intrinsic_figure_geometry
public import consolidated_dev.simple_vertex_duality

set_option Elab.async false

section BundlePart0
/- Source: Papers/SimpleFourRidges.lean -/



@[expose] public section

/-! # Intersections of three genuine facets at a simple four-vertex -/

noncomputable section
namespace Papers.SimpleFour

open Set Module
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical

variable {n : ℕ} {P : ConvexPolytope n} {v : VertexType P}

def facetIntersection (P : ConvexPolytope n) (r : Finset (Facet P)) : Set (E n) :=
  {x | x ∈ P.toSet ∧ ∀ F ∈ r, x ∈ F.val.val}

theorem facetIntersection_isFace (P : ConvexPolytope n) (v : VertexType P)
    (r : Finset (Facet P)) (hr : r ⊆ facetStar P v) : P.IsFace (facetIntersection P r) := by
  induction r using Finset.induction_on with
  | empty => simpa [facetIntersection] using toSet_isFace P
  | @insert F r hFr ih =>
    have hr' : r ⊆ facetStar P v := fun G hG => hr (Finset.mem_insert_of_mem hG)
    have hvF := (mem_facetStar P v F).mp (hr (Finset.mem_insert_self _ _))
    have hvr : v.val ∈ facetIntersection P r :=
      ⟨subset_convexHull ℝ _ v.property,fun G hG => (mem_facetStar P v G).mp (hr' hG)⟩
    have hface := isFace_inter P (ih hr') F.val.property ⟨v.val,hvr,hvF⟩
    have heq : facetIntersection P (insert F r) = facetIntersection P r ∩ F.val.val := by
      ext x
      simp only [facetIntersection,Set.mem_setOf_eq,Finset.mem_insert,forall_eq_or_imp,
        Set.mem_inter_iff]
      tauto
    rw [heq]
    exact hface

def cornerLabels (D : DatiFetta P v.val) (hd : 2 ≤ P.dim)
    (hs : (polytopeGraph P).degree v = P.dim) (r : Finset (Facet P))
    (hr : r ⊆ facetStar P v) : Finset (VertexType D.politopo) :=
  r.attach.image (fun F => cornerEquiv D hd hs ⟨F.val,hr F.property⟩)

theorem cornerLabels_card (D : DatiFetta P v.val) (hd : 2 ≤ P.dim)
    (hs : (polytopeGraph P).degree v = P.dim) (r : Finset (Facet P))
    (hr : r ⊆ facetStar P v) : (cornerLabels D hd hs r hr).card = r.card := by
  unfold cornerLabels
  rw [Finset.card_image_of_injective]
  · simp
  · intro F G h
    have hfg := (cornerEquiv D hd hs).injective h
    apply Subtype.ext
    exact congrArg (fun x : ↥(facetStar P v) => (x.val : Facet P)) hfg

theorem mem_cornerLabels (D : DatiFetta P v.val) (hd : 2 ≤ P.dim)
    (hs : (polytopeGraph P).degree v = P.dim) (r : Finset (Facet P))
    (hr : r ⊆ facetStar P v) (q : VertexType D.politopo) :
    q ∈ cornerLabels D hd hs r hr ↔
      ∃ F : r, cornerEquiv D hd hs ⟨F.val,hr F.property⟩ = q := by
  simp [cornerLabels]

theorem exists_neighbor_in_facetIntersection (D : DatiFetta P v.val)
    (hfour : P.dim = 4) (hs : (polytopeGraph P).degree v = P.dim)
    (r : Finset (Facet P)) (hr : r ⊆ facetStar P v) (hcard : r.card = 3) :
    ∃ w : NeighborOf v, w.val.val ∈ facetIntersection P r := by
  have hd : 2 ≤ P.dim := by omega
  have htotal : Fintype.card (VertexType D.politopo) = 4 := by
    simpa only [VertexType,Fintype.card_coe,D.vertices_card_eq_degree,hs,hfour]
  have hlabel : (cornerLabels D hd hs r hr).card = 3 :=
    (cornerLabels_card D hd hs r hr).trans hcard
  obtain ⟨q,_,hq⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show (cornerLabels D hd hs r hr).card <
      (Finset.univ : Finset (VertexType D.politopo)).card by
      rw [Finset.card_univ,htotal,hlabel]
      decide)
  let w := D.neighborEquiv.symm q
  refine ⟨w,subset_convexHull ℝ _ w.val.property,?_⟩
  intro F hF
  apply (neighbor_mem_facet_iff D hd hs ⟨F,hr hF⟩ w).mpr
  rw [D.neighborEquiv.apply_symm_apply]
  intro heq
  apply hq
  exact (mem_cornerLabels D hd hs r hr q).mpr ⟨⟨F,hF⟩,heq.symm⟩

theorem face_dim_pos_of_two_vertices (P : ConvexPolytope n)
    {F : Set (E n)} (hF : P.IsFace F) (v w : VertexType P)
    (hv : v.val ∈ F) (hw : w.val ∈ F) (hne : v ≠ w) : 1 ≤ faceDim F := by
  by_contra h
  have hzero : faceDim F = 0 := by omega
  obtain ⟨q,hq,_⟩ := punto_di_faccia0_e_vertice P hF hzero
  rw [hq] at hv hw
  exact hne (Subtype.ext ((Set.mem_singleton_iff.mp hv).trans
    (Set.mem_singleton_iff.mp hw).symm))

theorem facetIntersection_slice_vertices (D : DatiFetta P v.val)
    (hd : 2 ≤ P.dim) (hs : (polytopeGraph P).degree v = P.dim)
    (r : Finset (Facet P)) (hr : r ⊆ facetStar P v) :
    vertexSet D.politopo (facetIntersection P r ∩ {x | D.l x = D.c}) =
      (cornerLabels D hd hs r hr)ᶜ := by
  ext q
  rw [mem_vertexSet,Finset.mem_compl,mem_cornerLabels]
  have hqbody : q.val ∈ P.toSet ∩ {x | D.l x = D.c} := by
    rw [← D.politopo_toSet]
    exact subset_convexHull ℝ _ q.property
  constructor
  · rintro ⟨⟨_,hqF⟩,hqlevel⟩ ⟨F,hFq⟩
    have hne := (slice_facet_vertex_iff D hd hs ⟨F.val,hr F.property⟩ q).mp
      ⟨hqF F.val F.property,hqlevel⟩
    exact hne hFq.symm
  · intro hq
    refine ⟨⟨hqbody.1,?_⟩,hqbody.2⟩
    intro F hF
    have hne : q ≠ cornerEquiv D hd hs ⟨F,hr hF⟩ := by
      intro heq
      exact hq ⟨⟨F,hF⟩,heq.symm⟩
    exact ((slice_facet_vertex_iff D hd hs ⟨F,hr hF⟩ q).mpr hne).1

theorem three_facets_intersect_in_edge (D : DatiFetta P v.val)
    (hfour : P.dim = 4) (hs : (polytopeGraph P).degree v = P.dim)
    (r : Finset (Facet P)) (hr : r ⊆ facetStar P v) (hcard : r.card = 3) :
    P.IsFace (facetIntersection P r) ∧ faceDim (facetIntersection P r) = 1 := by
  have hd : 2 ≤ P.dim := by omega
  have hK := facetIntersection_isFace P v r hr
  have hvK : v.val ∈ facetIntersection P r :=
    ⟨subset_convexHull ℝ _ v.property,fun F hF => (mem_facetStar P v F).mp (hr hF)⟩
  obtain ⟨w,hwK⟩ := exists_neighbor_in_facetIntersection D hfour hs r hr hcard
  have hKpos := face_dim_pos_of_two_vertices P hK v w.val hvK hwK w.property.1
  have hslice := D.faccia_fetta hK hvK hKpos
  have hc := simplex_face_vertices_card D.politopo (figure_independent D (by omega) hs) hslice
  rw [← vertexSet_card D.politopo hslice,facetIntersection_slice_vertices D hd hs r hr,
    Finset.card_compl,cornerLabels_card] at hc
  have htotal : Fintype.card (VertexType D.politopo) = 4 := by
    simpa only [VertexType,Fintype.card_coe,D.vertices_card_eq_degree,hs,hfour]
  rw [htotal,hcard] at hc
  have hdim := D.fetta_faceDim hK hvK hKpos
  exact ⟨hK,by omega⟩

theorem three_facet_vertex_pair (D : DatiFetta P v.val)
    (hfour : P.dim = 4) (hs : (polytopeGraph P).degree v = P.dim)
    (r : Finset (Facet P)) (hr : r ⊆ facetStar P v) (hcard : r.card = 3) :
    ∃ w : VertexType P, v ≠ w ∧ (polytopeGraph P).Adj v w ∧
      ∀ u : VertexType P, r ⊆ facetStar P u ↔ u = v ∨ u = w := by
  obtain ⟨hK,hKdim⟩ := three_facets_intersect_in_edge D hfour hs r hr hcard
  have hvK : v.val ∈ facetIntersection P r :=
    ⟨subset_convexHull ℝ _ v.property,fun F hF => (mem_facetStar P v F).mp (hr hF)⟩
  obtain ⟨w,hw,hwK,hwv,hseg⟩ := spigolo_segmento P hK hKdim v.property hvK
  let w' : VertexType P := ⟨w,hw⟩
  have hvw : v ≠ w' := fun h => hwv (congrArg Subtype.val h).symm
  refine ⟨w',hvw,⟨hvw,facetIntersection P r,hK,hKdim,hvK,hwK⟩,?_⟩
  intro u
  constructor
  · intro hu
    have huK : u.val ∈ facetIntersection P r :=
      ⟨subset_convexHull ℝ _ u.property,fun F hF => (mem_facetStar P u F).mp (hu hF)⟩
    rcases vertice_in_segmento_estremo_generico P hK hseg u.property huK with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · rintro (rfl | rfl)
    · exact hr
    · intro F hF
      exact (mem_facetStar P w' F).mpr (hwK.2 F hF)

end Papers.SimpleFour

end
end
end BundlePart0
