module

public import MatroidChecked.TenFiveFacetExclusion
public import Consolidated.ActualTriangleGeometry
public import Consolidated.SmallFacetEncoding
public import RootedFamilyClosure

@[expose] public section

/-!
# The two ten-facet small-boundary budgets are impossible

Ten nonsimplicial facets, each with at most five vertices, are all
five-vertex facets. With at most one quadrilateral there are at least eight
triangular bipyramids. Their equatorial triangles and triangular ridges
contradict the graph-triangle bound. Every cell in the argument below is
an actual facet; no finite catalogue coverage is assumed.
-/

noncomputable section
namespace Papers.RationalityTen.ActualTenFiveFacetExclusion

open Finset Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeFacetSurplus
open ChirotopeDensity ActualFacetCatalogueTransport CellFacetInvariants
open MatroidChecked.FacetBoundaryEncoding MatroidChecked.BoundaryTriangleCount
open SmallFacetTriangleShapes SmallFacetTargetBudgets

local instance faceFintype (P : ConvexPolytope 4) (k : Nat) :
    Fintype (Face P k) := Fintype.ofFinite _

/-- This covers both `(m,E,q)=(10,10,0)` and `(10,10,1)` without a search. -/
theorem impossible (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (lab : P.vertices ≃ Fin 10)
    (hnonsimple : ∀ v : P.vertices, ¬ IsSimpleVertex P v)
    (hsmall : ∀ F : Face P 3, facetVertexCount P F ≤ 5)
    (hm : Nat.card (Face P 3) = 10)
    (hN : (nonsimplicialFacets P).card = 10)
    (hq : (quadrilateralFaces P).card ≤ 1) : False := by
  let labels := Fintype.equivFin (Face P 3)
  let cells : Fin (Fintype.card (Face P 3)) → Cell 10 :=
    fun i => actualCell P lab (labels.symm i)
  let E : Encoding P lab cells :=
    { index := labels
      index_spec := fun F => by simp only [cells, Equiv.symm_apply_apply] }
  have hfull : nonsimplicialFacets P = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simpa only [Finset.card_univ, ← Nat.card_eq_fintype_card, hm, hN]
      using (Nat.le_refl 10)
  have hfive (F : Face P 3) : facetVertexCount P F = 5 := by
    have hmem : F ∈ nonsimplicialFacets P := by rw [hfull]; exact Finset.mem_univ _
    have hlo := (mem_nonsimplicialFacets P F).mp hmem
    have hhi := hsmall F
    omega
  let B := E.family.filter fun i => BipyramidPredicate (cells i)
  have hBcard : B.card = (nonsimplicialFacets P \ squareFacets P).card := by
    dsimp only [B]
    rw [Encoding.family, Finset.filter_image,
      Finset.card_image_of_injective _ E.index_injective]
    congr 1
    ext F
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, E.index_spec,
      BipyramidPredicate, actualCell_vertex_card, actualCell_excess,
      Finset.mem_sdiff, mem_nonsimplicialFacets, squareFacets]
  have hB : 6 ≤ B.card := by
    rw [hBcard, Finset.card_sdiff_of_subset (squareFacets_subset_nonsimplicial P),
      squareFacets_card P hP hsmall, hN]
    omega
  have hshape (i) (hi : i ∈ E.family) : TriangleShape (cells i) := by
    obtain ⟨F, rfl⟩ := (E.mem_family i).mp hi
    rw [E.index_spec]
    exact actual_small_facet_shape P lab F (hsmall F)
  have hbase (i) (hi : i ∈ B) : ∃ T, BaseRules (cells i) T :=
    (hshape i (Finset.mem_filter.mp hi).1).base (Finset.mem_filter.mp hi).2
  let base (i) : Finset (Fin 10) :=
    if hi : i ∈ B then Classical.choose (hbase i hi) else ∅
  apply MatroidChecked.TenFiveFacetExclusion.impossible E hP
    (RootedFamilyClosure.nonsimple_neighbors hP hnonsimple)
    (E.family_card.trans hm) ?_ ?_ B (Finset.filter_subset _ _) hB
    (fun i hi => (hshape i hi).edges) ?_ base ?_
  · intro i hi
    obtain ⟨F, rfl⟩ := (E.mem_family i).mp hi
    rw [E.index_spec, actualCell_vertex_card]
    exact hfive F
  · intro i hi edge hedge
    obtain ⟨F, rfl⟩ := (E.mem_family i).mp hi
    rw [E.index_spec] at hedge
    obtain ⟨A, _, hA⟩ := (actualCell_edge_iff P lab F edge).mp hedge
    rw [← hA]
    exact (ActualFaceTransport.labels_card P lab A).trans (one_face_vertex_card P A)
  · intro i hi
    have hb : i ∈ B ↔ BipyramidPredicate (cells i) := by
      simp only [B, Finset.mem_filter, hi, true_and]
    simpa only [cellRidgeSizeCount, hb] using (hshape i hi).count
  · intro i hi
    dsimp only [base]
    rw [dif_pos hi]
    exact Classical.choose_spec (hbase i hi)

#print axioms impossible

end Papers.RationalityTen.ActualTenFiveFacetExclusion
