module
public import FullSmallFacetActualCoverage
public import ActualGraphGrowthTarget
public import ActualGraphCandidateRestriction
public import GraphGrowthVertexCapacity
public import GraphRootExclusion
public import SharedSmallGraph
public import LiteralGraphPairSemantics

/-! Canonical source bundle; each original file retains its own scopes. -/

section BundlePart0
/- Source: FullSmallGraphTarget.lean -/








@[expose] public section

/-!
# Actual all-small boundaries in the complete graph-conditioned universe

The full 6510-cell universe is used throughout. Its complete template
coverage supplies the boundary encoding, while its kind certificates and
the geometric counting identities determine the exact quotas. A graph
filter therefore retains every actual selected cell. In particular, an
empty-root certificate excludes the actual polytope without assuming that
the search producer found a complete local candidate list.
-/

noncomputable section
namespace Papers.RationalityTen.FullSmallGraphTarget

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

abbrev cells := FacetUniverses.FullSmall.cells

def actualQuota {d : ℕ} (P : ConvexPolytope d) : ℕ → ℕ :=
  FullSmallFacetTargetBudgets.quota (Nat.card (Face P 3))
    (nonsimplicialFacets P).card (quadrilateralFaces P).card

theorem actual_quota_counts {d : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10}
    (E : Encoding P lab (fun i => decodeCell (cells i))) (hP : P.dim = 4)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 5) (j : ℕ) :
    (E.family.filter fun i => (cells i).kind = j).card = actualQuota P j := by
  rw [ActualGrowthTarget.encoded_kind_card]
  simp only [FullSmallFacetTargetBudgets.actual_kind_of_checks cells E
    FacetUniverses.FullSmall.cells_kind_correct]
  exact FullSmallFacetTargetBudgets.actual_quota_counts P hP hfacets j

/-- The graph mask is allowed to be supplied by a normalized catalogue
representative. Its agreement with the actual graph is stated explicitly,
and all other target conditions follow from the actual polytope. -/
theorem exists_target {d k : ℕ} (P : ConvexPolytope d) (hP : P.dim = 4)
    (lab : P.vertices ≃ Fin 10)
    (hnonsimple : ∀ v : P.vertices, ¬ IsSimpleVertex P v)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 5)
    (D : Problem 6510 1024 45 10 k) (H : LiteralData D cells)
    (hquota : ∀ j, D.quota j = actualQuota P j)
    (hminimum : D.minimumIncidence = 5)
    (hmissing : D.missingCount = (nonsimplicialFacets P).card)
    (hgraph : ∀ q : Fin 45, D.requiredEdges.testBit q.val = true ↔
      maskSet (edgeMask q) ∈ actualGraphEdges P lab) :
    ∃ E : Encoding P lab (fun i => decodeCell (cells i)),
      GraphGrowthConstraints.Target D E.family.toList := by
  obtain ⟨E⟩ := FullSmallFacetActualCoverage.encoding_exists P lab hfacets
  refine ⟨E, ActualGraphGrowthTarget.actual_small_target D cells H
    FacetUniverses.FullSmall.cells_wellFormed E hP hnonsimple hfacets ?_
    hminimum ?_ hmissing⟩
  · intro j
    simp only [H.kind, hquota]
    exact actual_quota_counts E hP hfacets j.val
  · intro q
    exact (hgraph q).trans (actual_graph_mask_membership cells
      FacetUniverses.FullSmall.cells_wellFormed E hP (edgeMask q) (edgeMask_lt q)).symm

/-- The complement convention used by the graph catalogue gives exactly
the required-edge condition in `exists_target`. -/
theorem exists_target_of_complement {d k : ℕ} (P : ConvexPolytope d)
    (hP : P.dim = 4) (lab : P.vertices ≃ Fin 10)
    (hnonsimple : ∀ v : P.vertices, ¬ IsSimpleVertex P v)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 5)
    (D : Problem 6510 1024 45 10 k) (H : LiteralData D cells)
    (hquota : ∀ j, D.quota j = actualQuota P j)
    (hminimum : D.minimumIncidence = 5)
    (hmissing : D.missingCount = (nonsimplicialFacets P).card)
    (complement : ℕ)
    (hrequired : ∀ q : Fin 45,
      D.requiredEdges.testBit q.val = !complement.testBit q.val)
    (hcomplement : ∀ q : Fin 45, complement.testBit q.val = true ↔
      maskSet (edgeMask q) ∉ actualGraphEdges P lab) :
    ∃ E : Encoding P lab (fun i => decodeCell (cells i)),
      GraphGrowthConstraints.Target D E.family.toList := by
  apply exists_target P hP lab hnonsimple hfacets D H hquota hminimum hmissing
  intro q
  rw [hrequired, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, hcomplement, not_not]

/-- Exact row semantics and positivity of the actual kind quota imply
membership in the complete eligible mask. No selected cell is discarded. -/
theorem selected_eligible {d k : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} (D : Problem 6510 1024 45 10 k)
    (H : LiteralData D cells) (R : IncidenceRows 6510 10 45)
    (HR : RowsForCells R cells)
    (E : Encoding P lab (fun i => decodeCell (cells i))) (hP : P.dim = 4)
    (hB : GraphGrowthConstraints.Target D E.family.toList)
    (allowed complement : ℕ)
    (hallowed : ∀ i, allowed.testBit i.val = true ↔ 0 < D.quota (cells i).kind)
    (hcomplement : ∀ q : Fin 45, complement.testBit q.val = true ↔
      maskSet (edgeMask q) ∉ actualGraphEdges P lab)
    (i : Fin 6510) (hi : i ∈ E.family) :
    (eligibleMask R allowed complement).testBit i.val = true := by
  have hraw (q : Fin 45) : complement.testBit q.val = true ↔
      edgeMask q ∉ literalGraphEdges cells E.family := by
    exact (hcomplement q).trans
      (not_congr (actual_graph_mask_membership cells
        FacetUniverses.FullSmall.cells_wellFormed E hP
        (edgeMask q) (edgeMask_lt q))).symm
  have hinduced := selected_induced R cells HR
    FacetUniverses.FullSmall.cells_wellFormed E hP complement hraw i hi
  have hedges (q : Fin 45) (hq : (R.edges i).testBit q.val = true) :
      (R.vertices i).testBit (R.first q).val = true ∧
        (R.vertices i).testBit (R.second q).val = true := by
    rw [hinduced q, Bool.and_eq_true_iff, Bool.and_eq_true_iff] at hq
    exact hq.1
  have hbudget (j : ℕ) :
      (E.family.filter fun i => (cells i).kind = j).card ≤ D.quota j := by
    have hb := hB.boundary.budget j
    have hk : D.kind = fun i => (cells i).kind := funext H.kind
    rw [hk, ActualGrowthTarget.kindCount_toList] at hb
    exact hb
  apply (eligibleMask_bit_iff R allowed complement i hedges).mpr
  exact ⟨(hallowed i).mpr
    (E.selected_kind_quota_pos (fun i => (cells i).kind) D.quota hbudget i hi), hinduced⟩

/-- A checked empty-root certificate rules out a genuine boundary in the
full universe. The vertex-capacity inequality is supplied by its separately
proved finite-set theorem, rather than assumed as a search axiom. -/
theorem checked_root_excludes {d k : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} (D : Problem 6510 1024 45 10 k)
    (H : LiteralData D cells) (R : IncidenceRows 6510 10 45)
    (HR : RowsForCells R cells)
    (E : Encoding P lab (fun i => decodeCell (cells i))) (hP : P.dim = 4)
    (hB : GraphGrowthConstraints.Target D E.family.toList)
    (allowed complement : ℕ)
    (hallowed : ∀ i, allowed.testBit i.val = true ↔ 0 < D.quota (cells i).kind)
    (hcomplement : ∀ q : Fin 45, complement.testBit q.val = true ↔
      maskSet (edgeMask q) ∉ actualGraphEdges P lab)
    (C : GraphRootExclusion.Certificate 6510 1024 45 10 k)
    (hmask : C.eligible = eligibleMask R allowed complement)
    (hcheck : GraphRootExclusion.check D C = true) : False := by
  apply GraphRootExclusion.check_sound D (vertexCapacitySound D)
    C hcheck E.family.toList hB
  intro i hi
  rw [hmask]
  exact selected_eligible D H R HR E hP hB allowed complement hallowed hcomplement
    i (Finset.mem_toList.mp hi)

#print axioms checked_root_excludes

end Papers.RationalityTen.FullSmallGraphTarget

end
end
end BundlePart0

section BundlePart1
/- Source: SharedSmallGraphActual.lean -/






@[expose] public section

/-!
# The checked shared graph data describe genuine convex boundaries

All incidence data come from the complete 6510-cell universe. The finite
checks in `SharedSmallGraph` certify the rows once; this module supplies
their mathematical interpretation and instantiates the actual target.
The only graph-specific inputs are its explicit complement mask and the
finite certificate being applied.
-/

noncomputable section
namespace Papers.RationalityTen.SharedSmallGraphActual

open Finset Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeFacetSurplus ChirotopeDensity
open MatroidChecked.FacetBoundaryEncoding LiteralMaskGeometry
open ActualFacetInducedGraph ActualComplementGraph ActualGraphNormalization
open ActualGraphGrowthTarget ActualGraphCandidateRestriction
open GraphGrowthConstraints GraphCandidateCoverage TenGraphEdges GrowthBitsets
open LiteralGraphPairSemantics

private theorem fastEdgeMask_eq (q : Fin 45) :
    SharedSmallGraph.fastEdgeMask q = TenGraphEdges.edgeMask q := by
  simp only [SharedSmallGraph.fastEdgeMask, TenGraphEdges.edgeMask,
    FastTenGraphEdges.first_eq, FastTenGraphEdges.second_eq]

theorem edge_semantics (i : Fin 6510) (q : Fin 45) :
    (SharedSmallGraph.edgeMask i).testBit q.val = true ↔
      edgeMask q ∈ (SharedSmallGraph.cells i).edges := by
  rw [SharedSmallGraph.edge_mask_eq]
  apply edge_mask_bit_of_map
  have hf : SharedSmallGraph.fastEdgeMask = TenGraphEdges.edgeMask :=
    funext fastEdgeMask_eq
  simpa only [hf] using SharedSmallGraph.edge_indices_map i

theorem missing_semantics (i : Fin 6510) (q : Fin 45) :
    (SharedSmallGraph.missingMask i).testBit q.val = true ↔
      edgeMask q ∈ EncodedNonedgeFacetCoverage.cellInternalNonedgeMasks
        (SharedSmallGraph.cells i) := by
  apply missing_mask_bit (SharedSmallGraph.cells i) (SharedSmallGraph.edgeMask i)
    (SharedSmallGraph.withinMask (SharedSmallGraph.cells i).vertices)
    (SharedSmallGraph.missingMask i) (edge_semantics i) ?_
    (SharedSmallGraph.missing_mask_eq i) q
  intro e
  simpa only [FastTenGraphEdges.first_eq, FastTenGraphEdges.second_eq] using
    SharedSmallGraph.within_mask_exact
      ⟨(SharedSmallGraph.cells i).vertices, SharedSmallGraph.vertices_lt i⟩ e

/-- Every field of the finite graph problem has its literal cell meaning. -/
theorem literalData (quota : ℕ → ℕ) (required missingCount : ℕ) :
    LiteralData (SharedSmallGraph.problem quota required missingCount)
      SharedSmallGraph.cells := by
  refine ⟨fun _ => rfl, fun _ _ => rfl, fun _ => rfl, ?_, ?_, ?_⟩
  · exact SharedSmallGraph.vertex_rows_exact
  · exact edge_semantics
  · exact missing_semantics

/-- The candidate-filter rows use the same complete cells and edge slots. -/
theorem rowsForCells : RowsForCells SharedSmallGraph.graphRows SharedSmallGraph.cells := by
  refine ⟨FastTenGraphEdges.first_eq, FastTenGraphEdges.second_eq, fun _ => rfl, ?_⟩
  exact edge_semantics

abbrev requiredMask := SharedSmallGraph.requiredMask

theorem requiredMask_bit (complement : ℕ) (q : Fin 45) :
    (requiredMask complement).testBit q.val = !complement.testBit q.val := by
  change ((FiniteMaskSets.allMask 45) ^^^ complement).testBit q.val = _
  rw [Nat.testBit_xor,
    FiniteMaskSets.allMask_bit q, Bool.true_xor]

/-- All cells whose kind has positive quota are allowed before graph
filtering. The exact five kind rows include the unused tags as well. -/
abbrev allowedMask := SharedSmallGraph.allowedMask

theorem allowedMask_bit (quota : ℕ → ℕ) (i : Fin 6510) :
    (allowedMask quota).testBit i.val = true ↔
      0 < quota (SharedSmallGraph.cells i).kind := by
  change (unionValues
    (fun j : Fin 5 => if 0 < quota j.val then SharedSmallGraph.kindRows j.val else 0)
    (List.finRange 5)).testBit i.val = true ↔ _
  rw [← bitAt_eq_testBit, bitAt_unionValues]
  simp only [List.mem_finRange, true_and, bitAt_eq_testBit]
  constructor
  · rintro ⟨j, hj⟩
    by_cases hq : 0 < quota j.val
    · rw [if_pos hq, SharedSmallGraph.kind_rows_exact, decide_eq_true_eq] at hj
      simpa only [hj] using hq
    · rw [if_neg hq, Nat.zero_testBit] at hj
      exact False.elim (Bool.noConfusion hj)
  · intro hq
    let j : Fin 5 := ⟨(SharedSmallGraph.cells i).kind, SharedSmallGraph.kind_lt i⟩
    refine ⟨j, ?_⟩
    rw [if_pos hq, SharedSmallGraph.kind_rows_exact]
    exact decide_eq_true rfl

def actualProblem {d : ℕ} (P : ConvexPolytope d) (complement : ℕ) :
    Problem 6510 1024 45 10 5 :=
  SharedSmallGraph.problem (FullSmallGraphTarget.actualQuota P)
    (requiredMask complement) (nonsimplicialFacets P).card

/-- Every actual nonsimple four-polytope with all facets of size at most
five gives a target in the complete shared universe, under any labeling.
The returned eligible-mask membership is pointwise on its entire boundary. -/
theorem actual_target {d : ℕ} (P : ConvexPolytope d) (hP : P.dim = 4)
    (lab : P.vertices ≃ Fin 10)
    (hnonsimple : ∀ v : P.vertices, ¬ IsSimpleVertex P v)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 5)
    (complement : ℕ)
    (hcomplement : ∀ q : Fin 45, complement.testBit q.val = true ↔
      maskSet (edgeMask q) ∉ actualGraphEdges P lab) :
    ∃ E : Encoding P lab (fun i => decodeCell (SharedSmallGraph.cells i)),
      GraphGrowthConstraints.Target (actualProblem P complement) E.family.toList ∧
      ∀ i ∈ E.family,
        (eligibleMask SharedSmallGraph.graphRows
          (allowedMask (FullSmallGraphTarget.actualQuota P)) complement).testBit i.val = true := by
  have H := literalData (FullSmallGraphTarget.actualQuota P)
    (requiredMask complement) (nonsimplicialFacets P).card
  obtain ⟨E, hE⟩ := FullSmallGraphTarget.exists_target_of_complement P hP lab
    hnonsimple hfacets (actualProblem P complement) H (fun _ => rfl) rfl rfl
    complement (requiredMask_bit complement) hcomplement
  refine ⟨E, hE, ?_⟩
  intro i hi
  exact FullSmallGraphTarget.selected_eligible (actualProblem P complement) H
    SharedSmallGraph.graphRows rowsForCells E hP hE
    (allowedMask (FullSmallGraphTarget.actualQuota P)) complement
    (allowedMask_bit (FullSmallGraphTarget.actualQuota P)) hcomplement i hi

/-- A successful empty-root replay is an actual nonrealizability result.
All complete-universe and incidence premises are discharged above. -/
theorem checked_root_excludes_actual {d : ℕ} (P : ConvexPolytope d)
    (hP : P.dim = 4) (lab : P.vertices ≃ Fin 10)
    (hnonsimple : ∀ v : P.vertices, ¬ IsSimpleVertex P v)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 5)
    (complement : ℕ)
    (hcomplement : ∀ q : Fin 45, complement.testBit q.val = true ↔
      maskSet (edgeMask q) ∉ actualGraphEdges P lab)
    (C : GraphRootExclusion.Certificate 6510 1024 45 10 5)
    (hmask : C.eligible = eligibleMask SharedSmallGraph.graphRows
      (allowedMask (FullSmallGraphTarget.actualQuota P)) complement)
    (hcheck : GraphRootExclusion.check (actualProblem P complement) C = true) : False := by
  obtain ⟨E, hE, hallowed⟩ := actual_target P hP lab hnonsimple hfacets complement hcomplement
  apply GraphRootExclusion.check_sound (actualProblem P complement)
    (vertexCapacitySound (actualProblem P complement)) C hcheck E.family.toList hE
  intro i hi
  rw [hmask]
  exact hallowed i (Finset.mem_toList.mp hi)

#print axioms checked_root_excludes_actual

end Papers.RationalityTen.SharedSmallGraphActual

end
end
end BundlePart1
