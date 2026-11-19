module
public import Consolidated.ActualTriangleGeometry
public import Consolidated.SixActualAssembly
public import Graph13Complete
public import GraphCaseActualCoverage

section Source0

@[expose] public section
noncomputable section
namespace Papers.RationalityTen.GraphCatalogueActualCoverage

open Finset Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeFacetSurplus Papers.PolytopeNonedgeAllocation ChirotopeDensity
open MatroidChecked.FacetBoundaryEncoding LiteralMaskGeometry
open ActualFacetInducedGraph ActualComplementGraph ActualGraphNormalization
open ActualGraphGrowthTarget ActualGraphCandidateRestriction
open GraphGrowthConstraints GraphCandidateCoverage TenGraphEdges
open GraphCaseCertificate GraphRouteSelector GraphRowSpecifications
open TriangleCountCertificate GraphCatalogue.Generated.Graph13

/-- The graph catalogues are the original complete levels, not a filtered list. -/
def catalogueEntry (level index : Nat) : GraphCatalogueCheck.State 45 :=
  if level = 10 then Level10.lookup index
  else if level = 11 then Level11.lookup index
  else if level = 12 then Level12.lookup index
  else Level13.lookup index

theorem catalogueEntry_mask (level index : Nat) :
    (catalogueEntry level index).mask = catalogueMask level index := by
  unfold catalogueEntry catalogueMask
  split <;> (try rfl)
  split <;> (try rfl)
  split <;> rfl

theorem catalogueEntry_checked (level : Nat)
    (hlevel : level = 10 ∨ level = 11 ∨ level = 12 ∨ level = 13)
    (i : Fin (catalogueSize level)) :
    GraphCatalogueCheck.stateCheck (catalogueEntry level i.val) = true := by
  rcases hlevel with rfl | rfl | rfl | rfl
  · exact Level10.entry_checked i
  · exact Level11.entry_checked i
  · exact Level12.entry_checked i
  · exact Level13.entry_checked i

/-- Universal, recursively checked coverage of all admissible graphs at
all four relevant complement sizes. -/
theorem catalogue_complete (level : Nat)
    (hlevel : level = 10 ∨ level = 11 ∨ level = 12 ∨ level = 13) :
    GraphCatalogueCore.Covers TenGraphEdges.incidence 4 Frames.renamings
      (fun i : Fin (catalogueSize level) => (catalogueEntry level i.val).edges) level := by
  rcases hlevel with rfl | rfl | rfl | rfl
  · exact level10_complete
  · exact level11_complete
  · exact level12_complete
  · exact level13_complete

/-- A complete catalogue representative is realized by actual vertex labels.
Every edge bit has its original geometric meaning after relabeling. -/
theorem exists_actual_catalogue_graph {d c : Nat} (P : ConvexPolytope d)
    (hP : P.dim = 4) (hnonsimple : ∀ v : P.vertices, ¬ IsSimpleVertex P v)
    (lab : P.vertices ≃ Fin 10) (cells : Fin c → ConcreteGrowth.Cell)
    (hwell : ∀ i, WellFormed (cells i))
    (E : Encoding P lab (fun i => decodeCell (cells i)))
    (level : Nat) (hlevel : level = 10 ∨ level = 11 ∨ level = 12 ∨ level = 13)
    (hsize : Nat.card (Nonedge P) = level) :
    ∃ i : Fin (catalogueSize level), ∃ lab' : P.vertices ≃ Fin 10,
      ∀ q : Fin 45, (catalogueMask level i.val).testBit q.val = true ↔
        maskSet (edgeMask q) ∉ actualGraphEdges P lab' := by
  have hlength : (complementEdges (literalGraphEdges cells E.family)).toList.length = level :=
    (actual_complement_length_nonedges cells hwell E hP).trans hsize
  obtain ⟨i, lab', hmodel⟩ := exists_graph_model_labeling cells hwell E hP hnonsimple
    Frames.renamings (fun i : Fin (catalogueSize level) => (catalogueEntry level i.val).edges)
    (catalogue_complete level hlevel) hlength
  refine ⟨i, lab', fun q => ?_⟩
  have hm := of_decide_eq_true
    (Bool.and_eq_true_iff.mp (catalogueEntry_checked level hlevel i)).2
  change (catalogueEntry level i.val).mask =
    GrowthBitsets.ofList (catalogueEntry level i.val).edges at hm
  calc
    (catalogueMask level i.val).testBit q.val = true ↔
        q ∈ (catalogueEntry level i.val).edges := by
      rw [← catalogueEntry_mask, hm, ← GrowthBitsets.bitAt_eq_testBit,
        GrowthBitsets.bitAt_ofList]
    _ ↔ q ∈ (intrinsicComplement P lab').toList := hmodel.mem_iff.symm
    _ ↔ maskSet (edgeMask q) ∉ actualGraphEdges P lab' := by
      rw [Finset.mem_toList, mem_intrinsicComplement]

/-- The triangle counter is unchanged when supplied with any mask having the
correct forty-five actual complement bits. -/
theorem count_eq_actual {d c : Nat} (P : ConvexPolytope d) (hP : P.dim = 4)
    (lab : P.vertices ≃ Fin 10) (cells : Fin c → ConcreteGrowth.Cell)
    (hwell : ∀ i, WellFormed (cells i))
    (E : Encoding P lab (fun i => decodeCell (cells i))) (complement : Nat)
    (hcomplement : ∀ q : Fin 45, complement.testBit q.val = true ↔
      maskSet (edgeMask q) ∉ actualGraphEdges P lab) :
    TenGraphTriangles.count complement = TenGraphTriangles.count
      (ActualGraphTriangleCount.complementMask (literalGraphEdges cells E.family)) := by
  have hbits (q : Fin 45) : complement.testBit q.val = false ↔
      maskSet (edgeMask q) ∈ (literalGraphEdges cells E.family).image maskSet := by
    rw [Bool.eq_false_iff, ne_eq, hcomplement, not_not,
      ActualGraphTriangleCount.raw_edge_mem_image_iff _
        (fun m hm => literalGraphEdges_bound cells E.family hwell hm),
      actual_graph_mask_membership cells hwell E hP (edgeMask q) (edgeMask_lt q)]
  have h := TenGraphTriangleSemantics.count_eq_triangle_card
    ((literalGraphEdges cells E.family).image maskSet) complement hbits
  rw [literalGraphEdges_image] at h
  rw [ActualGraphTriangleCount.actual_triangle_count cells hwell E]
  exact h

theorem small_triangle_bound (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 5)
    (lab : P.vertices ≃ Fin 10) (row : Row) (complement : Nat)
    (hfacets_count : row.facetCount = Nat.card (Face P 3))
    (hquota2 : row.quota.getD 2 0 = FullSmallGraphTarget.actualQuota P 2)
    (hquota4 : row.quota.getD 4 0 = 0)
    (hcomplement : ∀ q : Fin 45, complement.testBit q.val = true ↔
      maskSet (edgeMask q) ∉ actualGraphEdges P lab) :
    row.minimum ≤ TenGraphTriangles.count complement := by
  obtain ⟨E⟩ := FullSmallFacetActualCoverage.encoding_exists P lab hfacets
  have h := SmallFacetTriangleShapes.actual_all_small_triangle_lower_bound
    FacetUniverses.FullSmall.cells FacetUniverses.FullSmall.cells_wellFormed
    FacetUniverses.FullSmall.cells_kind_correct E hP hfacets
  rw [E.family_card, FullSmallGraphTarget.actual_quota_counts E hP hfacets,
    ← count_eq_actual P hP lab FacetUniverses.FullSmall.cells
      FacetUniverses.FullSmall.cells_wellFormed E complement hcomplement] at h
  simpa only [Row.minimum, hfacets_count, hquota2, hquota4, Nat.mul_zero, Nat.add_zero] using h

theorem six_triangle_bound (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (A : ActualFacetTemplateAssignment.Assignment P)
    (hcounts : ∀ j : Fin 7, j ≠ 0 →
      (SixFacetProfileRefinement.countsOf P A.kind).six j = 0)
    (lab : P.vertices ≃ Fin 10) (row : Row) (complement : Nat)
    (hfacets_count : row.facetCount = Nat.card (Face P 3))
    (hquota2 : row.quota.getD 2 0 =
      FullSix0FacetTargetBudgets.quota (SixFacetProfileRefinement.countsOf P A.kind) 2)
    (hquota4 : row.quota.getD 4 0 =
      FullSix0FacetTargetBudgets.quota (SixFacetProfileRefinement.countsOf P A.kind) 4)
    (hcomplement : ∀ q : Fin 45, complement.testBit q.val = true ↔
      maskSet (edgeMask q) ∉ actualGraphEdges P lab) :
    row.minimum ≤ TenGraphTriangles.count complement := by
  obtain ⟨E, hE⟩ := FullSix0FacetActualCoverage.encoding_with_exact_counts P lab A hcounts
  have h := SixZeroTriangleShapes.actual_six_zero_triangle_lower_bound
    FacetUniverses.FullSix0.cells FacetUniverses.FullSix0.cells_wellFormed
    FacetUniverses.FullSix0.cells_kind_correct E hP A hcounts
  rw [E.family_card, hE ⟨2, by decide⟩, hE ⟨4, by decide⟩,
    ← count_eq_actual P hP lab FacetUniverses.FullSix0.cells
      FacetUniverses.FullSix0.cells_wellFormed E complement hcomplement] at h
  simpa only [Row.minimum, hfacets_count, hquota2, hquota4] using h

theorem empty_root_impossible (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hnonsimple : ∀ v : P.vertices, ¬ IsSimpleVertex P v)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 5)
    (lab : P.vertices ≃ Fin 10) (row : Row) (complement : Nat)
    (hquota : ∀ j, row.quota.getD j 0 = FullSmallGraphTarget.actualQuota P j)
    (hmissing : row.internalMissingCount = (nonsimplicialFacets P).card)
    (hcomplement : ∀ q : Fin 45, complement.testBit q.val = true ↔
      maskSet (edgeMask q) ∉ actualGraphEdges P lab)
    (hcase : EmptyRoot row complement) : False := by
  obtain ⟨code, hcode, hcheck⟩ := hcase
  have hfun : (fun j => row.quota.getD j 0) = FullSmallGraphTarget.actualQuota P := funext hquota
  apply SharedSmallGraphActual.checked_root_excludes_actual P hP lab hnonsimple
    hfacets complement hcomplement
    (SharedSmallRootReplay.certificate (FullSmallGraphTarget.actualQuota P) code)
  · rw [SharedSmallRootReplay.certificate_eligible, hcode]
  · simpa only [SharedSmallRootReplay.check, hfun, hcode, hmissing,
      SharedSmallGraphActual.actualProblem] using hcheck

#print axioms catalogue_complete
#print axioms exists_actual_catalogue_graph
#print axioms small_triangle_bound
#print axioms six_triangle_bound
#print axioms empty_root_impossible
end Papers.RationalityTen.GraphCatalogueActualCoverage
end

end
end Source0

section Source1


@[expose] public section
noncomputable section
set_option autoImplicit false

/-! The exact numerical data of the single six-facet graph branch.
The row equality comes from the exhaustive catalogue dispatch. All geometric
counts below are recovered from the same actual facet assignment. -/

namespace Papers.RationalityTen.CompletedSix

open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeFacetSurplus
open Papers.PolytopeNonedgeAllocation Papers.PolytopeRelationBudget
open ChirotopeDensity SixFacetProfileRefinement SixBudgetEnumeration
open ActualResidualPartition

/-- Four tetrahedra, five bipyramids, four square pyramids, one six-facet. -/
def exceptionalRow : Row := ⟨14, 11, 2, [1,0,0,0,0,0,0]⟩

theorem exceptional_counts (P : ConvexPolytope 4) (C : SixCase P)
    (hrow : (countsOf P C.assignment.kind).toRow (actualAllSixFacetBudget P) =
      exceptionalRow) :
    countsOf P C.assignment.kind = countsOfRow exceptionalRow :=
  counts_eq_of_row _ _ C.refines _ hrow

theorem exceptional_budget (P : ConvexPolytope 4) (C : SixCase P)
    (hrow : (countsOf P C.assignment.kind).toRow (actualAllSixFacetBudget P) =
      exceptionalRow) :
    (actualAllSixFacetBudget P).m = 14 ∧
    (actualAllSixFacetBudget P).E = 11 ∧
    (actualAllSixFacetBudget P).q = 2 ∧
    (actualAllSixFacetBudget P).p = 0 ∧
    (actualAllSixFacetBudget P).L = 1 ∧
    (actualAllSixFacetBudget P).t = 0 := by
  have hm := congrArg Row.m hrow
  have hE := congrArg Row.E hrow
  have hq := congrArg Row.q hrow
  have hrest := (countsOf P C.assignment.kind).toRow_counts _ C.refines
  rw [hrow] at hrest
  exact ⟨hm, hE, hq, hrest.2.2.1.symm, hrest.1.symm, hrest.2.1.symm⟩

theorem exceptional_facets (P : ConvexPolytope 4) (C : SixCase P)
    (hrow : (countsOf P C.assignment.kind).toRow (actualAllSixFacetBudget P) =
      exceptionalRow) : Nat.card (Face P 3) = 14 :=
  (exceptional_budget P C hrow).1

theorem exceptional_covered_nonedges (P : ConvexPolytope 4) (C : SixCase P)
    (hrow : (countsOf P C.assignment.kind).toRow (actualAllSixFacetBudget P) =
      exceptionalRow) :
    (actualAllSixFacetBudget P).E + (actualAllSixFacetBudget P).L -
      (actualAllSixFacetBudget P).p = 12 := by
  obtain ⟨_, hE, _, hp, hL, _⟩ := exceptional_budget P C hrow
  rw [hE, hL, hp]

theorem exceptional_nonedges (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (C : SixCase P)
    (hrow : (countsOf P C.assignment.kind).toRow (actualAllSixFacetBudget P) =
      exceptionalRow) : Nat.card (Nonedge P) = 12 := by
  obtain ⟨hm, hE, hq, hp, _, _⟩ := exceptional_budget P C hrow
  change Nat.card (Face P 3) = 14 at hm
  change (nonsimplicialFacets P).card + (sixVertexFacets P).card = 11 at hE
  change (quadrilateralFaces P).card = 2 at hq
  change (pentagonalFaces P).card = 0 at hp
  have hexcess : facetExcess P = (11 : ℤ) := by
    rw [facetExcess_eq_nonsimplicial_add_six P C.small]
    exact_mod_cast hE
  have hpoly := polygonExcess_eq_quadrilaterals_add_twice_pentagons P
    (polygon_card_le_five_of_facet_card_le_six P hP C.small)
  rw [hq, hp] at hpoly
  norm_num at hpoly
  have hEuler := actual_excess_identity P hP
  rw [C.vertices, hm, hexcess, hpoly] at hEuler
  norm_num only [show Nat.choose 10 2 = 45 by decide +kernel, Nat.cast_ofNat] at hEuler
  omega

theorem exceptional_quota (P : ConvexPolytope 4) (C : SixCase P)
    (hrow : (countsOf P C.assignment.kind).toRow (actualAllSixFacetBudget P) =
      exceptionalRow) :
    ∀ j, FullSix0FacetTargetBudgets.quota (countsOf P C.assignment.kind) j =
      ([0,4,5,4,1] : List ℕ).getD j 0 := by
  rw [exceptional_counts P C hrow]
  intro j
  obtain _ | _ | _ | _ | _ | j := j <;> rfl

#print axioms exceptional_nonedges
#print axioms exceptional_quota

end Papers.RationalityTen.CompletedSix

end
end
end Source1
