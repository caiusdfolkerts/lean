module
public import Consolidated.GraphActualCompleteness
public import CompletedSmall.ActualAssembly

@[expose] public section
noncomputable section
namespace Papers.RationalityTen.GraphActualRowAssembly

open Finset Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeFacetSurplus Papers.PolytopeNonedgeAllocation Papers.PolytopeRelationBudget ChirotopeDensity
open MatroidChecked.FacetBoundaryEncoding LiteralMaskGeometry
open ActualFacetInducedGraph ActualComplementGraph ActualGraphNormalization
open ActualResidualPartition GraphCaseCertificate GraphRouteSelector GraphRowSpecifications
open GraphCaseActualCoverage GraphCatalogueActualCoverage
open ActualFacetTemplateAssignment SixFacetProfileRefinement

/-- Every graph index in this exact numerical row has a complete finite proof. -/
def VerifiedRow (code : Nat) : Prop :=
  ∀ i : Fin (rowOfCode code).graphCount, Result ((rowOfCode code).key i.val)

/-- Applying a verified graph row retains the complete geometric hypotheses. -/
theorem small_row_hasTerminal (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hnonsimple : ∀ v : P.vertices, ¬ IsSimpleVertex P v)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 5)
    (lab : P.vertices ≃ Fin 10) (code : Nat) (hcode : code ≠ 32)
    (hverified : VerifiedRow code)
    (hlength : (rowOfCode code).quota.length = 5)
    (hquota : ∀ j, (rowOfCode code).quota.getD j 0 = FullSmallGraphTarget.actualQuota P j)
    (hfacets_count : (rowOfCode code).facetCount = Nat.card (Face P 3))
    (hquota4 : (rowOfCode code).quota.getD 4 0 = 0)
    (hmissing : (rowOfCode code).internalMissingCount = (nonsimplicialFacets P).card)
    (hlevel : (rowOfCode code).level = 10 ∨ (rowOfCode code).level = 11 ∨
      (rowOfCode code).level = 12 ∨ (rowOfCode code).level = 13)
    (hsize : Nat.card (Nonedge P) = (rowOfCode code).level) :
    ActualLeafTargetCoverage.HasTerminal P := by
  obtain ⟨E⟩ := FullSmallFacetActualCoverage.encoding_exists P lab hfacets
  obtain ⟨i, lab', hcomplement⟩ := exists_actual_catalogue_graph P hP hnonsimple lab
    FacetUniverses.FullSmall.cells FacetUniverses.FullSmall.cells_wellFormed E
    (rowOfCode code).level hlevel hsize
  have hr := hverified i
  have hmin := small_triangle_bound P hP hfacets lab' (rowOfCode code)
    (TriangleCountCertificate.catalogueMask (rowOfCode code).level i.val)
    hfacets_count (hquota 2) hquota4 hcomplement
  simp only [Row.key, GraphRowSpecifications.code_eq, Result] at hr
  rcases hr with htriangle | hcase
  · exact False.elim (Nat.not_lt_of_ge hmin htriangle)
  · simp only [hcode, ite_false] at hcase
    rcases hcase with hsmall | hempty
    · exact small_hasTerminal P hP hnonsimple hfacets lab' (rowOfCode code) _
        hlength hquota hmissing hcomplement hsmall
    · exact False.elim (empty_root_impossible P hP hnonsimple hfacets lab'
        (rowOfCode code) _ hquota hmissing hcomplement hempty)

def smallCodes : List Nat := [16,19,23,24,25,26,27,28,29,30,31]

def SmallRowSpec (B : SmallFacetBudget) (code : Nat) : Prop :=
  code ≠ 32 ∧
  (rowOfCode code).quota = [0, B.m - B.E, B.E - 2 * B.q, 2 * B.q, 0] ∧
  (rowOfCode code).facetCount = B.m ∧
  (rowOfCode code).internalMissingCount = B.E ∧
  ((rowOfCode code).level = 10 ∨ (rowOfCode code).level = 11 ∨
    (rowOfCode code).level = 12 ∨ (rowOfCode code).level = 13) ∧
  (rowOfCode code).level + B.m + B.E = 35 + B.q

instance (B : SmallFacetBudget) (code : Nat) : Decidable (SmallRowSpec B code) := by
  unfold SmallRowSpec
  infer_instance

theorem small_row_spec (B : SmallFacetBudget) (hB : B ∈ SmallBudgetFamilyAssembly.graphBudgets) :
    ∃ code ∈ smallCodes, SmallRowSpec B code := by
  have h : SmallBudgetFamilyAssembly.graphBudgets.all (fun B =>
      smallCodes.any (fun code => decide (SmallRowSpec B code))) = true := by
    decide +kernel
  obtain ⟨code, hcode, hs⟩ := List.any_eq_true.mp (List.all_eq_true.mp h B hB)
  exact ⟨code, hcode, of_decide_eq_true hs⟩

theorem quota_list (m E q j : Nat) :
    ([0,m-E,E-2*q,2*q,0] : List Nat).getD j 0 = FullSmallFacetTargetBudgets.quota m E q j := by
  obtain _ | _ | _ | _ | _ | j := j <;> rfl

/-- Complete application to all eleven actual small-facet graph budgets. -/
theorem small_hasTerminal_of_verified
    (hverified : ∀ code ∈ smallCodes, VerifiedRow code)
    (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hnonsimple : ∀ v : P.vertices, ¬ IsSimpleVertex P v)
    (C : SmallCase P)
    (hB : SmallFacetBudget.mk (Nat.card (Face P 3)) (nonsimplicialFacets P).card
      (quadrilateralFaces P).card ∈ SmallBudgetFamilyAssembly.graphBudgets) :
    ActualLeafTargetCoverage.HasTerminal P := by
  let B : SmallFacetBudget := ⟨Nat.card (Face P 3), (nonsimplicialFacets P).card,
    (quadrilateralFaces P).card⟩
  obtain ⟨code, hcode, hne, hquota, hfacets, hmissing, hlevel, hsize⟩ := small_row_spec B hB
  let lab : P.vertices ≃ Fin 10 := Fintype.equivFinOfCardEq (by simpa using C.vertices)
  apply small_row_hasTerminal P hP hnonsimple C.small lab code hne (hverified code hcode)
  · rw [hquota]; rfl
  · intro j
    rw [hquota]
    exact quota_list B.m B.E B.q j
  · exact hfacets
  · rw [hquota]; rfl
  · exact hmissing
  · exact hlevel
  · have hE := facetExcess_eq_nonsimplicial_count_of_small_facets P C.small
    have hq := polygonExcess_eq_quadrilateral_count_of_small_facets P hP C.small
    have hEuler := actual_excess_identity P hP
    rw [C.vertices, hE, hq, show Nat.choose 10 2 = 45 by decide +kernel] at hEuler
    change (B.E : ℤ) = 45 - 10 - (B.m : ℤ) - (Nat.card (Nonedge P) : ℤ) + (B.q : ℤ) at hEuler
    omega

/-- The sole exceptional six-facet row is applied with its actual assignment
and exact Euler/nonedge data. -/
theorem six_hasTerminal_of_verified (hverified : VerifiedRow 32)
    (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hnonsimple : ∀ v : P.vertices, ¬ IsSimpleVertex P v)
    (C : SixCase P)
    (hrow : (countsOf P C.assignment.kind).toRow (actualAllSixFacetBudget P) =
      CompletedSix.exceptionalRow) : ActualLeafTargetCoverage.HasTerminal P := by
  have hcounts : ∀ j : Fin 7, j ≠ 0 → (countsOf P C.assignment.kind).six j = 0 := by
    rw [CompletedSix.exceptional_counts P C hrow]
    have h : ∀ j : Fin 7, j ≠ 0 →
        (CompletedSix.countsOfRow CompletedSix.exceptionalRow).six j = 0 := by
      decide +kernel
    exact h
  let lab : P.vertices ≃ Fin 10 := Fintype.equivFinOfCardEq (by simpa using C.vertices)
  obtain ⟨E⟩ := FullSix0FacetActualCoverage.encoding_exists P lab C.assignment hcounts
  obtain ⟨i, lab', hcomplement⟩ := exists_actual_catalogue_graph P hP hnonsimple lab
    FacetUniverses.FullSix0.cells FacetUniverses.FullSix0.cells_wellFormed E 12
    (Or.inr (Or.inr (Or.inl rfl))) (CompletedSix.exceptional_nonedges P hP C hrow)
  have hquota (j : Nat) : (rowOfCode 32).quota.getD j 0 =
      FullSix0FacetTargetBudgets.quota (countsOf P C.assignment.kind) j :=
    (CompletedSix.exceptional_quota P C hrow j).symm
  have hfacets : (rowOfCode 32).facetCount = Nat.card (Face P 3) :=
    (CompletedSix.exceptional_facets P C hrow).symm
  have hr := hverified i
  have hmin := six_triangle_bound P hP C.assignment hcounts lab' (rowOfCode 32)
    (TriangleCountCertificate.catalogueMask 12 i.val) hfacets (hquota 2) (hquota 4) hcomplement
  simp only [Row.key, GraphRowSpecifications.code_eq, Result] at hr
  rcases hr with htriangle | hcase
  · exact False.elim (Nat.not_lt_of_ge hmin htriangle)
  · exact six_hasTerminal P hP hnonsimple C.small C.assignment hcounts lab'
      (rowOfCode 32) _ (by decide) hquota
      (CompletedSix.exceptional_covered_nonedges P C hrow).symm hcomplement hcase

#print axioms small_hasTerminal_of_verified
#print axioms six_hasTerminal_of_verified
end Papers.RationalityTen.GraphActualRowAssembly
end
