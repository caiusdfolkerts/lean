module

public import ActualTenFiveFacetExclusion
public import CanonicalSmallFacetCoverage
public import Consolidated.SixActualAssembly

/- Source module: SmallFamilyActualEncoding -/
@[expose] public section

/-!
# Actual encodings of the rooted small-facet families

The residual case records membership in the complete list of numerical
budgets. Every listed budget has a triangular bipyramid, so its actual
boundary can be normalized at that facet. The canonical placement theorems
then give the complete encoding, with every search quota equal to its
actual facet count.
-/

noncomputable section
namespace Papers.RationalityTen.SmallFamilyActualEncoding

open Finset
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeFacetSurplus
open ChirotopeDensity
open MatroidChecked.FacetBoundaryEncoding LiteralMaskGeometry
open ActualResidualPartition

local instance faceFintype (P : ConvexPolytope 4) (k : Nat) :
    Fintype (Face P k) := Fintype.ofFinite _

/-- Membership in the exact residual budget list already supplies a
bipyramid root; no additional geometric or row-count hypothesis is used. -/
theorem root_exists (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (C : SmallCase P) :
    ∃ F : Face P 3, facetVertexCount P F = 5 ∧ facetPolygonExcess P F = 0 := by
  have hfinite : ∀ B ∈ smallFacetBudgets, 2 * B.q < B.E := by decide +kernel
  have hbound : 2 * (quadrilateralFaces P).card < (nonsimplicialFacets P).card :=
    hfinite _ C.budget
  have hsquare := SmallFacetTargetBudgets.squareFacets_card P hP C.small
  have hnonempty :
      (nonsimplicialFacets P \ SmallFacetTargetBudgets.squareFacets P).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_sdiff_of_subset
      (SmallFacetTargetBudgets.squareFacets_subset_nonsimplicial P), hsquare]
    omega
  obtain ⟨F, hF⟩ := hnonempty
  exact ⟨F, (SmallFacetTargetBudgets.mem_bipyramid_class_iff P C.small F).mp hF⟩

/-- The finite classification is the only case-specific input. Its target
has the original polytope's exact counts, and the resulting encoding
contains every genuine facet with its full vertex, edge and ridge data. -/
theorem classified_encoding (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (C : SmallCase P)
    (classification : RootedFamilyClosure.FiniteClassification
      FacetUniverses.Small.cells
      (SmallFacetTargetBudgets.quota (Nat.card (Face P 3))
        (nonsimplicialFacets P).card (quadrilateralFaces P).card)
      FacetUniverses.Small.root) :
    HasClassifiedEncoding P := by
  let lab₀ : P.vertices ≃ Fin 10 :=
    (Fintype.equivFin P.vertices).trans
      (finCongr (by simpa only [Fintype.card_coe] using C.vertices))
  obtain ⟨F, hF⟩ := root_exists P hP C
  obtain ⟨lab, E, hroot, hkinds⟩ :=
    CanonicalSmallFacetCoverage.rooted_encoding P lab₀ C.small F hF
  obtain ⟨_, hquota⟩ := RootedKindedActualEncoding.literal_target_of_tag_counts
    FacetUniverses.Small.cells E hP classification.wellFormed
    (SmallFacetTargetBudgets.partitionKind (nonsimplicialFacets P)
      (SmallFacetTargetBudgets.squareFacets P) F) hkinds
    (SmallFacetTargetBudgets.quota (Nat.card (Face P 3))
      (nonsimplicialFacets P).card (quadrilateralFaces P).card)
    (SmallFacetTargetBudgets.actual_rooted_quota_counts P hP C.small F hF)
  exact ⟨FacetUniverses.Small.cellCount, FacetUniverses.Small.cells,
    _, FacetUniverses.Small.root, classification, lab, E,
    (E.mem_family _).mpr ⟨F, hroot⟩, hquota⟩

end Papers.RationalityTen.SmallFamilyActualEncoding

end
end
/- Source module: SmallBudgetFamilyAssembly -/
@[expose] public section

/-!
# Exact assembly of the 32 small-facet budgets

The two ten-facet rows are covered by the geometric triangle contradiction.
Nineteen rows use ordinary rooted growth; eleven use graph-conditioned
growth. The partition below is checked against the original complete
32-row list, including every facet and quadrilateral count.
-/

noncomputable section
namespace Papers.RationalityTen.SmallBudgetFamilyAssembly

open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeFacetSurplus
open ChirotopeDensity ActualResidualPartition
open Nonrational.TerminalData Nonrational.TerminalVerification

def rootedBudgets : List SmallFacetBudget :=
  [⟨11, 10, 0⟩, ⟨11, 10, 1⟩, ⟨11, 11, 0⟩, ⟨11, 11, 1⟩, ⟨11, 11, 2⟩,
   ⟨12, 10, 0⟩, ⟨12, 10, 1⟩, ⟨12, 11, 0⟩, ⟨12, 11, 1⟩, ⟨12, 11, 2⟩,
   ⟨12, 12, 1⟩, ⟨12, 12, 2⟩, ⟨12, 12, 3⟩, ⟨13, 10, 0⟩,
   ⟨13, 11, 0⟩, ⟨13, 11, 1⟩, ⟨13, 12, 2⟩, ⟨13, 12, 3⟩, ⟨13, 13, 4⟩]

def graphBudgets : List SmallFacetBudget :=
  [⟨13, 10, 1⟩, ⟨13, 11, 2⟩, ⟨14, 10, 0⟩, ⟨14, 10, 1⟩,
   ⟨14, 11, 1⟩, ⟨14, 11, 2⟩, ⟨14, 12, 3⟩,
   ⟨15, 10, 0⟩, ⟨15, 10, 1⟩, ⟨15, 11, 2⟩, ⟨16, 10, 1⟩]

theorem complete (B : SmallFacetBudget) (hB : B ∈ smallFacetBudgets) :
    (B.m = 10 ∧ B.E = 10 ∧ B.q ≤ 1) ∨
      B ∈ rootedBudgets ∨ B ∈ graphBudgets := by
  have h : smallFacetBudgets.all (fun B => decide
      ((B.m = 10 ∧ B.E = 10 ∧ B.q ≤ 1) ∨
        B ∈ rootedBudgets ∨ B ∈ graphBudgets)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h B hB)

def ClassifiedBudget (B : SmallFacetBudget) : Prop :=
  Nonempty (RootedFamilyClosure.FiniteClassification FacetUniverses.Small.cells
    (SmallFacetTargetBudgets.quota B.m B.E B.q) FacetUniverses.Small.root)

/-- This assembly exposes precisely the two finite-family proof inputs.
The final small-facet theorem instantiates both with the checked catalogues. -/
theorem rationallyRealizable_of_families
    (hvalid : ∀ j, j < targetCount → ValidTarget j)
    (hrooted : ∀ B ∈ rootedBudgets, ClassifiedBudget B)
    (hgraph : ∀ (P : ConvexPolytope 4), P.IsFullDim →
      (∀ v : P.vertices, ¬ IsSimpleVertex P v) → SmallCase P →
      SmallFacetBudget.mk (Nat.card (Face P 3)) (nonsimplicialFacets P).card
        (quadrilateralFaces P).card ∈ graphBudgets → RationallyRealizable P)
    (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hnonsimple : ∀ v : P.vertices, ¬ IsSimpleVertex P v) (C : SmallCase P) :
    RationallyRealizable P := by
  rcases complete _ C.budget with ⟨hm, hN, hq⟩ | hrow | hrow
  · let lab : P.vertices ≃ Fin 10 :=
      (Fintype.equivFin P.vertices).trans
        (finCongr (by simpa only [Fintype.card_coe] using C.vertices))
    exact (ActualTenFiveFacetExclusion.impossible P hP lab hnonsimple
      C.small hm hN hq).elim
  · obtain ⟨classification⟩ := hrooted _ hrow
    exact rationallyRealizable_of_classifiedEncoding hvalid P hP hnonsimple
      (SmallFamilyActualEncoding.classified_encoding P hP C classification)
  · exact hgraph P hP hnonsimple C hrow

#print axioms complete
#print axioms rationallyRealizable_of_families

end Papers.RationalityTen.SmallBudgetFamilyAssembly

end
end
/- Source module: SmallBudgetTargetAssembly -/
@[expose] public section

/-! Complete terminal coverage for the same exhaustive 32-row small-facet
partition. The two analytic exclusions, nineteen rooted rows and eleven
graph rows retain exactly the quotas of `SmallBudgetFamilyAssembly`. -/

noncomputable section
namespace Papers.RationalityTen.SmallBudgetFamilyAssembly

open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeFacetSurplus
open ChirotopeDensity ActualResidualPartition ActualLeafTargetCoverage

theorem hasTerminal_of_families
    (hrooted : ∀ B ∈ rootedBudgets, ClassifiedBudget B)
    (hgraph : ∀ (P : ConvexPolytope 4), P.IsFullDim →
      (∀ v : P.vertices, ¬ IsSimpleVertex P v) → SmallCase P →
      SmallFacetBudget.mk (Nat.card (Face P 3)) (nonsimplicialFacets P).card
        (quadrilateralFaces P).card ∈ graphBudgets → HasTerminal P)
    (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hnonsimple : ∀ v : P.vertices, ¬ IsSimpleVertex P v) (C : SmallCase P) :
    HasTerminal P := by
  rcases complete _ C.budget with ⟨hm, hN, hq⟩ | hrow | hrow
  · let lab : P.vertices ≃ Fin 10 :=
      (Fintype.equivFin P.vertices).trans
        (finCongr (by simpa only [Fintype.card_coe] using C.vertices))
    exact (ActualTenFiveFacetExclusion.impossible P hP lab hnonsimple
      C.small hm hN hq).elim
  · obtain ⟨classification⟩ := hrooted _ hrow
    exact ActualResidualTargetAssembly.hasTerminal_of_classifiedEncoding P hP hnonsimple
      (SmallFamilyActualEncoding.classified_encoding P hP C classification)
  · exact hgraph P hP hnonsimple C hrow

#print axioms hasTerminal_of_families

end Papers.RationalityTen.SmallBudgetFamilyAssembly

end
end

#print axioms Papers.RationalityTen.SmallBudgetFamilyAssembly.hasTerminal_of_families
