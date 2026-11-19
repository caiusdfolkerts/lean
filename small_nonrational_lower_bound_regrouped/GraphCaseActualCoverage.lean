module
public import Consolidated.GraphCertificatesGeometry
public import Consolidated.FullSmallGraphAssembly
public import GraphCaseCertificate
public import GraphSixEmbeddingCoverage
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.GetD

@[expose] public section

/-!
# Actual convex boundaries in complete graph certificates

The local candidate lists are never assumed to contain an actual boundary.
Their checked complete eligible-mask equality supplies that fact. Restriction
then preserves every vertex, edge, polygon, and facet-kind count through the
existing full cell encoding.
-/
noncomputable section
namespace Papers.RationalityTen.GraphCaseActualCoverage

open Finset Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeFacetSurplus ChirotopeDensity
open MatroidChecked.FacetBoundaryEncoding LiteralMaskGeometry
open ActualFacetInducedGraph ActualComplementGraph ActualGraphNormalization
open ActualGraphGrowthTarget ActualGraphCandidateRestriction
open GraphGrowthConstraints GraphCandidateCoverage TenGraphEdges
open PackedGraphCertificate SharedGraphCellPool GraphCaseCertificate GraphRouteSelector

/-- The checked duplicate-free full embedding is an actual injection. -/
def embeddingInj {N : Nat} [NeZero N] (D : RawData)
    {cells : Fin N → ConcreteGrowth.Cell} {rows : IncidenceRows N 10 45}
    {complement : Nat} (H : Coverage D cells rows complement) : Fin D.n ↪ Fin N :=
  ⟨embedding D, fun a b h =>
    List.inj_on_of_nodup_map H.embedding_nodup
      (List.mem_finRange a) (List.mem_finRange b) h⟩

/-- Completeness of the finite induced-graph filter retains the entire
actual boundary, and exact cell equality preserves every kind count. -/
theorem restrict_encoding {d N : Nat} [NeZero N] (P : ConvexPolytope d)
    (hP : P.dim = 4) (lab : P.vertices ≃ Fin 10) (D : RawData)
    (cells : Fin N → ConcreteGrowth.Cell) (rows : IncidenceRows N 10 45)
    (hrows : RowsForCells rows cells) (hwell : ∀ i, WellFormed (cells i))
    (complement : Nat) (H : Coverage D cells rows complement)
    (E : Encoding P lab (fun i => decodeCell (cells i)))
    (hquota : ∀ j, (E.family.filter fun i => (cells i).kind = j).card = D.data.quota j)
    (hcomplement : ∀ q : Fin 45, complement.testBit q.val = true ↔
      maskSet (edgeMask q) ∉ actualGraphEdges P lab) :
    ∃ E' : Encoding P lab (fun i => decodeCell (D.data.cells i)),
      ∀ j, (E'.family.filter fun i => (D.data.cells i).kind = j).card = D.data.quota j := by
  have hraw (q : Fin 45) : complement.testBit q.val = true ↔
      edgeMask q ∉ literalGraphEdges cells E.family := by
    exact (hcomplement q).trans
      (not_congr (actual_graph_mask_membership cells hwell E hP
        (edgeMask q) (edgeMask_lt q))).symm
  have hcoverage : ∀ i ∈ E.family, ∃ j, embeddingInj D H j = i := by
    intro i hi
    apply (H.complete i).mpr
    exact ⟨E.selected_kind_quota_pos (fun i => (cells i).kind) D.data.quota
      (fun j => (hquota j).le) i hi,
      selected_induced rows cells hrows hwell E hP complement hraw i hi⟩
  obtain ⟨E', hindex⟩ := E.restrict_to_subuniverse (embeddingInj D H)
    (fun i => congrArg decodeCell (H.cells_exact i)) hcoverage
  refine ⟨E', fun j => ?_⟩
  rw [E.restricted_kind_card E' (embeddingInj D H) hindex
    (fun i => (cells i).kind) (fun i => (D.data.cells i).kind)
    (fun i => congrArg ConcreteGrowth.Cell.kind (H.cells_exact i)), hquota]

/-- The five listed quotas also determine all other kind values to be zero. -/
theorem parameters_quota (D : RawData) (row : Row) (complement : Nat)
    (H : Parameters D row complement) (hlength : row.quota.length = 5) (j : Nat) :
    D.data.quota j = row.quota.getD j 0 := by
  by_cases hj : j < 5
  · exact H.quota ⟨j, hj⟩
  · have hk : ¬ j < D.k := by rw [H.kind_count]; exact hj
    change (if j < D.k then D.quota.get j else 0) = _
    rw [if_neg hk, List.getD_eq_default _ _ (by omega)]

/-- A complete finite small-cell certificate applies to an actual all-small
polytope whenever its exact numerical row and graph agree. -/
theorem small_hasTerminal (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hnonsimple : ∀ v : P.vertices, ¬ IsSimpleVertex P v)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 5)
    (lab : P.vertices ≃ Fin 10) (row : Row) (complement : Nat)
    (hlength : row.quota.length = 5)
    (hquota : ∀ j, row.quota.getD j 0 = FullSmallGraphTarget.actualQuota P j)
    (hmissing : row.internalMissingCount = (nonsimplicialFacets P).card)
    (hcomplement : ∀ q : Fin 45, complement.testBit q.val = true ↔
      maskSet (edgeMask q) ∉ actualGraphEdges P lab)
    (hcase : Small row complement) : ActualLeafTargetCoverage.HasTerminal P := by
  obtain ⟨D, C, H, V⟩ := hcase
  have hDquota (j : Nat) : D.data.quota j = FullSmallGraphTarget.actualQuota P j :=
    (parameters_quota D row complement H hlength j).trans (hquota j)
  obtain ⟨E⟩ := FullSmallFacetActualCoverage.encoding_exists P lab hfacets
  have hEq (j : Nat) :
      (E.family.filter fun i => (FacetUniverses.FullSmall.cells i).kind = j).card =
        D.data.quota j := by
    rw [hDquota]
    exact FullSmallGraphTarget.actual_quota_counts E hP hfacets j
  obtain ⟨E', hE'⟩ := restrict_encoding P hP lab D FacetUniverses.FullSmall.cells
    SharedSmallGraph.graphRows SharedSmallGraphActual.rowsForCells
    FacetUniverses.FullSmall.cells_wellFormed complement V E hEq hcomplement
  have hwell (i : Fin D.n) : WellFormed (D.data.cells i) := by
    rw [V.cells_exact]
    exact FacetUniverses.FullSmall.cells_wellFormed _
  have HL := CertifiedGraphGeometry.literal D C
  apply CertifiedGraphGeometry.hasTerminal P hP hnonsimple D C hwell lab E' ?_ hE'
  apply ActualGraphGrowthTarget.actual_small_target (D.inputs.problem C.valid)
    D.data.cells HL hwell E' hP hnonsimple hfacets
  · intro j
    change _ = D.data.quota j.val
    refine Eq.trans ?_ (hE' j.val)
    apply congrArg Finset.card
    ext i
    simp only [Finset.mem_filter, HL.kind]
  · exact H.minimum_incidence
  · intro q
    change D.inputs.requiredEdges.testBit q.val = true ↔ _
    rw [H.required, SharedSmallGraphActual.requiredMask_bit,
      Bool.not_eq_true', Bool.eq_false_iff, ne_eq, hcomplement, not_not]
    exact (actual_graph_mask_membership D.data.cells hwell E' hP
      (edgeMask q) (edgeMask_lt q)).symm
  · exact H.internal_missing.trans hmissing

/-- The shared six-facet incidence rows describe the complete global cells. -/
theorem six_rowsForCells :
    RowsForCells SharedSix0Incidence.graphRows FacetUniverses.FullSix0.cells := by
  refine ⟨FastTenGraphEdges.first_eq, FastTenGraphEdges.second_eq, ?_, ?_⟩
  · intro i
    exact congrArg ConcreteGrowth.Cell.vertices (SharedSix0CellPool.facts i).cell_eq
  · intro i q
    have h := SharedSix0CellPool.facts i
    change (SharedSix0CellPool.entry i).edgeMask.testBit q.val = true ↔ _
    rw [h.edge_mask]
    apply LiteralGraphPairSemantics.edge_mask_bit_of_map
    rw [← h.cell_eq]
    have hmask : ∀ q : Fin 45,
        RawGraphSemanticCertificate.fastPairMask q = TenGraphEdges.edgeMask q := by
      decide +kernel
    rw [← funext hmask]
    exact h.edge_map

/-- The exceptional six-facet row uses the same complete finite interface.
The actual template assignment supplies exact counts before any filtering. -/
theorem six_hasTerminal (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hnonsimple : ∀ v : P.vertices, ¬ IsSimpleVertex P v)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 6)
    (A : ActualFacetTemplateAssignment.Assignment P)
    (hcounts : ∀ j : Fin 7, j ≠ 0 →
      (SixFacetProfileRefinement.countsOf P A.kind).six j = 0)
    (lab : P.vertices ≃ Fin 10) (row : Row) (complement : Nat)
    (hlength : row.quota.length = 5)
    (hquota : ∀ j, row.quota.getD j 0 =
      FullSix0FacetTargetBudgets.quota (SixFacetProfileRefinement.countsOf P A.kind) j)
    (hmissing : row.internalMissingCount = (actualAllSixFacetBudget P).E +
      (actualAllSixFacetBudget P).L - (actualAllSixFacetBudget P).p)
    (hcomplement : ∀ q : Fin 45, complement.testBit q.val = true ↔
      maskSet (edgeMask q) ∉ actualGraphEdges P lab)
    (hcase : Six row complement) : ActualLeafTargetCoverage.HasTerminal P := by
  obtain ⟨D, C, H, V⟩ := hcase
  have hDquota (j : Nat) : D.data.quota j =
      FullSix0FacetTargetBudgets.quota (SixFacetProfileRefinement.countsOf P A.kind) j :=
    (parameters_quota D row complement H hlength j).trans (hquota j)
  obtain ⟨E, hEq₅⟩ := FullSix0FacetActualCoverage.encoding_with_exact_counts
    P lab A hcounts
  have hEq (j : Nat) :
      (E.family.filter fun i => (FacetUniverses.FullSix0.cells i).kind = j).card =
        D.data.quota j := by
    rw [hDquota]
    by_cases hj : j < 5
    · exact hEq₅ ⟨j, hj⟩
    · have hempty : E.family.filter
          (fun i => (FacetUniverses.FullSix0.cells i).kind = j) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro i _ heq
        exact hj (heq ▸ FacetUniverses.FullSix0.cells_kind_lt_five i)
      rw [hempty, Finset.card_empty]
      unfold FullSix0FacetTargetBudgets.quota
      split <;> omega
  obtain ⟨E', hE'⟩ := restrict_encoding P hP lab D FacetUniverses.FullSix0.cells
    SharedSix0Incidence.graphRows six_rowsForCells
    FacetUniverses.FullSix0.cells_wellFormed complement V E hEq hcomplement
  have hwell (i : Fin D.n) : WellFormed (D.data.cells i) := by
    rw [V.cells_exact]
    exact FacetUniverses.FullSix0.cells_wellFormed _
  have HL := CertifiedGraphGeometry.literal D C
  apply CertifiedGraphGeometry.hasTerminal P hP hnonsimple D C hwell lab E' ?_ hE'
  apply ActualGraphGrowthTarget.actual_six_target (D.inputs.problem C.valid)
    D.data.cells HL hwell E' hP hnonsimple hfacets
  · intro j
    change _ = D.data.quota j.val
    refine Eq.trans ?_ (hE' j.val)
    apply congrArg Finset.card
    ext i
    simp only [Finset.mem_filter, HL.kind]
  · exact H.minimum_incidence
  · intro q
    change D.inputs.requiredEdges.testBit q.val = true ↔ _
    rw [H.required, SharedSmallGraphActual.requiredMask_bit,
      Bool.not_eq_true', Bool.eq_false_iff, ne_eq, hcomplement, not_not]
    exact (actual_graph_mask_membership D.data.cells hwell E' hP
      (edgeMask q) (edgeMask_lt q)).symm
  · exact H.internal_missing.trans hmissing

#print axioms restrict_encoding
#print axioms small_hasTerminal
#print axioms six_hasTerminal
end Papers.RationalityTen.GraphCaseActualCoverage
end
