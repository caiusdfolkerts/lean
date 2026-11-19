module
public import GraphCaseActualCoverage

@[expose] public section
noncomputable section

/-!
# Geometric soundness of direct terminal coverage

A direct coverage proof produces the same complete leaf classification as
growth replay. The original certified relabelings carry an orbit representative
to its checked leaf. The original leaf dispositions then give the original
geometric conclusion.
-/

namespace Papers.RationalityTen.DirectGraphGeometry

open PackedGraphCertificate GraphCaseCertificate SharedGraphCellPool
open ActualGraphGrowthTarget LiteralGraphGrowthRenaming
open MatroidChecked.FacetBoundaryEncoding LiteralMaskGeometry
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes

theorem literal (D : RawData) (C : DirectCore D) :
    LiteralData (D.inputs.problem C.valid) D.data.cells := by
  rw [inputs_problem_eq D C.valid C.matrix]
  exact MatrixGraphLiteralSemantics.literalData D.data C.matrix C.literal

theorem exists_frame (D : RawData) (C : DirectCore D) (f : Fin D.g) :
    ∃ F : Frame (D.inputs.problem C.valid) D.data.cells,
      ∀ c, F.cellMap.forward c = D.maps f c := by
  rw [inputs_problem_eq D C.valid C.matrix]
  rcases C.frames f with hid | ⟨v, w, inverse, h⟩
  · exact ⟨MatrixGraphLiteralSemantics.identityFrame D.data C.matrix
      (D.maps f) hid, fun _ => rfl⟩
  · exact ⟨MatrixGraphLiteralSemantics.frame D.data C.matrix v w
      (D.maps f) inverse h, fun _ => rfl⟩

def frames (D : RawData) (C : DirectCore D) (f : Fin D.g) :
    Frame (D.inputs.problem C.valid) D.data.cells :=
  Classical.choose (exists_frame D C f)

theorem frames_forward (D : RawData) (C : DirectCore D) (f : Fin D.g) (c : Fin D.n) :
    (frames D C f).cellMap.forward c = D.maps f c :=
  Classical.choose_spec (exists_frame D C f) c

theorem applyWord_eq (D : RawData) (C : DirectCore D)
    (hwell : ∀ i, WellFormed (D.data.cells i))
    (word : List (Fin D.g)) (B : List (Fin D.n)) :
    OrbitGrowthDAG.applyWord
      (fun f => ((frames D C f).toRenaming (literal D C) hwell).boundary) word B =
      rawApplyWord D.maps word B := by
  induction word generalizing B with
  | nil => rfl
  | cons f rest ih =>
    change OrbitGrowthDAG.applyWord _ rest (B.map (frames D C f).cellMap.forward) = _
    rw [ih]
    exact congrArg (rawApplyWord D.maps rest)
      (List.map_congr_left (fun c _ => frames_forward D C f c))

def classification (D : RawData) (C : DirectCore D)
    (hwell : ∀ i, WellFormed (D.data.cells i)) :
    GraphFamilyClosure.FiniteClassification (D.inputs.problem C.valid) D.data.cells where
  literal := literal D C
  wellFormed := hwell
  generatorCount := D.g
  frames := frames D C
  root := []
  leafCount := D.l
  leaves := D.leaf
  nodup := C.leaf_nodup
  rawLeaves := fun j => (D.leaf j).map D.data.cells
  raw_exact := fun _ => rfl
  certificates := Classical.choose C.leaves_checked
  checked := Classical.choose_spec C.leaves_checked
  complete := by
    intro B hB _
    obtain ⟨j, word, hj⟩ := C.complete B hB
    refine ⟨j, word, ?_⟩
    rw [applyWord_eq]
    exact hj

theorem hasTerminal (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hnonsimple : ∀ v : P.vertices, ¬ IsSimpleVertex P v)
    (D : RawData) (C : DirectCore D) (hwell : ∀ i, WellFormed (D.data.cells i))
    (lab : P.vertices ≃ Fin 10)
    (E : Encoding P lab (fun i => decodeCell (D.data.cells i)))
    (htarget : GraphGrowthConstraints.Target (D.inputs.problem C.valid) E.family.toList)
    (hquota : ∀ t, (E.family.filter fun i => (D.data.cells i).kind = t).card =
      D.data.quota t) : ActualLeafTargetCoverage.HasTerminal P := by
  apply GraphFamilyClosure.hasTerminal_of_encoding P hP hnonsimple
    (D.inputs.problem C.valid) D.data.cells (classification D C hwell)
    lab E htarget ?_ hquota
  change GrowthDAG.Included (SparseGrowthDAG.family [])
    (SparseGrowthDAG.family E.family.toList)
  simp [GrowthDAG.Included, SparseGrowthDAG.family, SparseGrowthDAG.has]

end Papers.RationalityTen.DirectGraphGeometry

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

theorem direct_small_hasTerminal (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hnonsimple : ∀ v : P.vertices, ¬ IsSimpleVertex P v)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 5)
    (lab : P.vertices ≃ Fin 10) (row : Row) (complement : Nat)
    (hlength : row.quota.length = 5)
    (hquota : ∀ j, row.quota.getD j 0 = FullSmallGraphTarget.actualQuota P j)
    (hmissing : row.internalMissingCount = (nonsimplicialFacets P).card)
    (hcomplement : ∀ q : Fin 45, complement.testBit q.val = true ↔
      maskSet (edgeMask q) ∉ actualGraphEdges P lab)
    (hcase : DirectSmall row complement) : ActualLeafTargetCoverage.HasTerminal P := by
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
  have HL := DirectGraphGeometry.literal D C
  apply DirectGraphGeometry.hasTerminal P hP hnonsimple D C hwell lab E' ?_ hE'
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

theorem direct_six_hasTerminal (P : ConvexPolytope 4) (hP : P.IsFullDim)
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
    (hcase : DirectSix row complement) : ActualLeafTargetCoverage.HasTerminal P := by
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
  have HL := DirectGraphGeometry.literal D C
  apply DirectGraphGeometry.hasTerminal P hP hnonsimple D C hwell lab E' ?_ hE'
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

end Papers.RationalityTen.GraphCaseActualCoverage
end
