module
public import consolidated.deletion_geometry
public import consolidated_dev.intrinsic_figure_geometry
public import consolidated_dev.simple_vertex_duality
public import consolidated_dev.simple_four_ridges
public import consolidated_dev.abstract_lower_bound
public import consolidated_dev.simple_four_combinatorics
public import papers.simple_four_finite_obstruction

set_option Elab.async false

section BundlePart0
/- Source: Papers/SimpleFourNoTen.lean -/





@[expose] public section

/-!
# No simple four-polytope has ten vertices

The statement is intrinsic: the ambient Euclidean dimension is arbitrary.
The dual tetrahedra are the sets of actual facets through actual vertices.
Their ridge pairing is the proved geometric edge-endpoint theorem, and
their circuit links come from actual polytope and facet graph connectivity.
The lower bound then reduces to the independently kernel-computed finite
six-label obstruction.
-/

noncomputable section
namespace Papers.SimpleFour

open Set Module Cubical.Simplicial
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical

variable {n : ℕ} (P : ConvexPolytope n) (hfour : P.dim = 4)
  (hs : ∀ v : VertexType P, (polytopeGraph P).degree v = 4)

include hfour hs in
private theorem degree_eq_dimension (v : VertexType P) :
    (polytopeGraph P).degree v = P.dim := (hs v).trans hfour.symm

include hfour hs in
theorem facetStar_card_four (v : VertexType P) : (facetStar P v).card = 4 := by
  exact (facetStar_card (simpleFigure P v (by omega)) (by omega)
    (degree_eq_dimension P hfour hs v)).trans hfour

include hfour hs in
theorem actual_dual_ridgePairing : RidgePairing (facetStar P) := by
  intro v r hr
  have hsub := simplexBoundary_subset hr
  have hrc := simplexBoundary_card hr
  have hvc := facetStar_card_four P hfour hs v
  have hcard : r.card = 3 := by omega
  obtain ⟨w,hvw,_hvw,hall⟩ := three_facet_vertex_pair
    (simpleFigure P v (by omega)) hfour (degree_eq_dimension P hfour hs v)
    r hsub hcard
  refine ⟨w,hvw,?_⟩
  intro u
  rw [mem_simplexBoundary_iff]
  have huc := facetStar_card_four P hfour hs u
  constructor
  · exact fun h => (hall u).mp h.1
  · intro hu
    exact ⟨(hall u).mpr hu,by omega⟩

include hfour hs in
theorem facetStar_injective : Function.Injective (facetStar P) := by
  intro v u heq
  let D := simpleFigure P v (by omega)
  obtain ⟨q,hq⟩ := D.politopo.vertices_nonempty
  let a : NeighborOf v := D.neighborEquiv.symm ⟨q,hq⟩
  let r := facetStar P v ∩ facetStar P a.val
  have hr : r.card = 3 := by
    have h := commonFacet_card D (by omega) (degree_eq_dimension P hfour hs v) a
    change r.card + 1 = P.dim at h
    omega
  obtain ⟨w,hvw,hadj,hall⟩ := three_facet_vertex_pair D hfour
    (degree_eq_dimension P hfour hs v) r Finset.inter_subset_left hr
  have hu : r ⊆ facetStar P u := by rw [← heq]; exact Finset.inter_subset_left
  rcases (hall u).mp hu with huv | huw
  · exact huv.symm
  · subst u
    have h := commonFacet_card D (by omega) (degree_eq_dimension P hfour hs v)
      (⟨w,hadj⟩ : NeighborOf v)
    rw [← heq,Finset.inter_self,facetStar_card_four P hfour hs v,hfour] at h
    omega

include hfour hs in
theorem actual_dual_graph_connected : (indexedFacetGraph (facetStar P)).Connected := by
  have hle : polytopeGraph P ≤ indexedFacetGraph (facetStar P) := by
    intro v w hadj
    let a : NeighborOf v := ⟨w,hadj⟩
    let D := simpleFigure P v (by omega)
    have hc := commonFacet_card D (by omega) (degree_eq_dimension P hfour hs v) a
    change (facetStar P v ∩ facetStar P w).card + 1 = P.dim at hc
    have hc4 : (facetStar P v ∩ facetStar P w).card + 1 = 4 := hc.trans hfour
    have hv := facetStar_card_four P hfour hs v
    have hw := facetStar_card_four P hfour hs w
    refine ⟨hadj.1,facetStar P v ∩ facetStar P w,?_,?_⟩
    · exact mem_simplexBoundary_iff.mpr ⟨Finset.inter_subset_left,by omega⟩
    · exact mem_simplexBoundary_iff.mpr ⟨Finset.inter_subset_right,by omega⟩
  exact SimpleGraph.Connected.mono hle (polytopeGraph_connected P)

def facetVertexIndexEquiv (F : Facet P) :
    VertexType (facePolytope P F.val.property) ≃ {v : VertexType P // F ∈ facetStar P v} where
  toFun v := ⟨⟨v.val,(Finset.mem_filter.mp v.property).1⟩,
    (mem_facetStar P _ F).mpr (Finset.mem_filter.mp v.property).2⟩
  invFun v := ⟨v.val.val,Finset.mem_filter.mpr
    ⟨v.val.property,(mem_facetStar P v.val F).mp v.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

include hfour hs in
theorem actual_dual_link_graph_connected (F : Facet P) :
    (indexedFacetGraph (erasedFamily (facetStar P) F)).Connected := by
  let Q := facePolytope P F.val.property
  let e := facetVertexIndexEquiv P F
  let f : polytopeGraph Q →g indexedFacetGraph (erasedFamily (facetStar P) F) :=
    { toFun := e
      map_rel' := by
        intro x y hxy
        let v := (e x).val
        let w := (e y).val
        have hvw : (polytopeGraph P).Adj v w := by
          obtain ⟨hne,A,hA,hAdim,hxA,hyA⟩ := hxy
          refine ⟨?_,A,isFace_of_facePolytope P F.val.property hA,hAdim,hxA,hyA⟩
          intro h
          apply hne
          apply Subtype.ext
          exact congrArg (fun u : VertexType P => (u.val : E n)) h
        let D := simpleFigure P v (by omega)
        have hc := commonFacet_card D (by omega) (degree_eq_dimension P hfour hs v)
          (⟨w,hvw⟩ : NeighborOf v)
        change (facetStar P v ∩ facetStar P w).card + 1 = P.dim at hc
        have hc4 : (facetStar P v ∩ facetStar P w).card + 1 = 4 := hc.trans hfour
        have hFv : F ∈ facetStar P v := (e x).property
        have hFw : F ∈ facetStar P w := (e y).property
        have hFr : F ∈ facetStar P v ∩ facetStar P w := Finset.mem_inter.mpr ⟨hFv,hFw⟩
        have hrc := Finset.card_erase_add_one hFr
        have hvc := Finset.card_erase_add_one hFv
        have hwc := Finset.card_erase_add_one hFw
        have hv4 := facetStar_card_four P hfour hs v
        have hw4 := facetStar_card_four P hfour hs w
        refine ⟨fun h => hxy.1 (e.injective h),
          (facetStar P v ∩ facetStar P w).erase F,?_,?_⟩
        · exact mem_simplexBoundary_iff.mpr
            ⟨Finset.erase_subset_erase F Finset.inter_subset_left,by
              change _ + 1 = ((facetStar P v).erase F).card
              omega⟩
        · exact mem_simplexBoundary_iff.mpr
            ⟨Finset.erase_subset_erase F Finset.inter_subset_right,by
              change _ + 1 = ((facetStar P w).erase F).card
              omega⟩ }
  exact SimpleGraph.Connected.map f e.surjective (polytopeGraph_connected Q)

theorem facetStar_family_covers :
    vertices id (Finset.univ.image (facetStar P)) = (Finset.univ : Finset (Facet P)) := by
  rw [vertices_image]
  apply Finset.eq_univ_of_forall
  intro F
  obtain ⟨v,hv⟩ := (facePolytope P F.val.property).vertices_nonempty
  have hvP := (Finset.mem_filter.mp hv).1
  have hvF := (Finset.mem_filter.mp hv).2
  exact (mem_vertices (facetStar P) Finset.univ F).mpr
    ⟨⟨v,hvP⟩,Finset.mem_univ _,(mem_facetStar P _ F).mpr hvF⟩

/- A genuine simple polytope of intrinsic dimension four cannot have ten
actual extreme vertices, in any Euclidean ambient dimension. -/
include hfour hs in
theorem no_simple_four_polytope_ten_vertices (hvertices : P.vertices.card = 10) : False := by
  let s := Finset.univ.image (facetStar P)
  have hinj := facetStar_injective P hfour hs
  have hp := actual_dual_ridgePairing P hfour hs
  have hcard : s.card = 10 := by
    rw [Finset.card_image_of_injective _ hinj,Finset.card_univ]
    simpa only [VertexType,Fintype.card_coe] using hvertices
  have hpure : Pure 4 id s := by
    intro t ht
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp ht
    exact facetStar_card_four P hfour hs v
  have hlinks : HasCircuitLinks 4 s := dual_four_hasCircuitLinks (facetStar P) hinj hp
    (actual_dual_graph_connected P hfour hs)
    (fun F _ => actual_dual_link_graph_connected P hfour hs F)
  exact tetrahedral_circuit_not_ten s hpure hlinks
    (ridgePairing_image_degreeTwo (facetStar P) hinj hp)
    (facetStar_family_covers P) hcard

end Papers.SimpleFour

end
end
end BundlePart0
