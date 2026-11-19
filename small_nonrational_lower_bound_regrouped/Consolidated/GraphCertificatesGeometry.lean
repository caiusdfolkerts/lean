module
public import ActualGraphCandidateRestriction
public import ActualGraphGrowthTarget
public import CheckedGraphGrowthFrames
public import Consolidated.GraphBoundarySemantics
public import Consolidated.SixActualAssembly
public import GraphCoreCertificate
public import SharedGraphCellPool
public import GraphGrowthVertexCapacity
public import GraphTargetCoverage
public import PackedGraphInputs
public import RawGraphSemanticCertificate

section GraphSource0

@[expose] public section

/-!
# Geometric interpretation of the compact graph certificates

The finite checker supplies literal incidence facts and frame checks. This
module translates them to the geometry interface already used by the actual
polytope boundary. No geometric conclusion is inferred from cache consistency
alone.
-/

noncomputable section
namespace Papers.RationalityTen.MatrixGraphLiteralSemantics

open MatrixGraphProblem RawGraphSemanticCertificate
open ActualGraphGrowthTarget LiteralGraphPairSemantics
open LiteralGraphGrowthRenaming

variable {n k : Nat}

theorem edge_semantics (D : MatrixGraphProblem.Data n 45 10 k)
    (hc : MatrixGraphProblem.Checked D) (hl : LiteralFacts D)
    (c : Fin n) (q : Fin 45) :
    (D.edgeMasks c).testBit q.val = true ↔
      TenGraphEdges.edgeMask q ∈ (D.cells c).edges := by
  rw [of_decide_eq_true (hc.cellFacts c).2.2.2.2.2.1]
  apply edge_mask_bit_of_map
  have hmask : ∀ q : Fin 45,
      RawGraphSemanticCertificate.fastPairMask q = TenGraphEdges.edgeMask q := by
    decide +kernel
  rw [← funext hmask]
  exact hl.edgeMap c

theorem literalData (D : MatrixGraphProblem.Data n 45 10 k)
    (hc : MatrixGraphProblem.Checked D) (hl : LiteralFacts D) :
    ActualGraphGrowthTarget.LiteralData (MatrixGraphProblem.problem D hc) D.cells := by
  refine ⟨fun _ => rfl, fun _ _ => rfl, fun _ => rfl, hl.vertices,
    edge_semantics D hc hl, ?_⟩
  intro c q
  change (D.missingMasks c).testBit q.val = true ↔ _
  rw [hl.missing, FastTenGraphEdges.first_eq, FastTenGraphEdges.second_eq,
    internal_pair_iff]
  simp only [Bool.and_eq_true_iff, Bool.not_eq_true', Bool.eq_false_iff,
    ne_eq, edge_semantics D hc hl, and_assoc]

/-- A checked cell permutation yields the original geometric frame. -/
def frame (D : MatrixGraphProblem.Data n 45 10 k)
    (hc : MatrixGraphProblem.Checked D)
    (vertexForward vertexInverse : Nat) (forward inverse : Fin n → Fin n)
    (hf : FrameFacts D.cells D.requiredEdges vertexForward vertexInverse forward inverse) :
    Frame (MatrixGraphProblem.problem D hc) D.cells :=
  CheckedGraphGrowthFrames.checkedFrame (MatrixGraphProblem.problem D hc) D.cells
    vertexForward vertexInverse hf.vertices forward inverse hf.inverse hf.cells hf.graph

/-- A literal identity map needs no repeated cell-geometry computation.
Only its forward map enters the raw node predicate. -/
def identityFrame (D : MatrixGraphProblem.Data n 45 10 k)
    (hc : MatrixGraphProblem.Checked D) (forward : Fin n → Fin n)
    (hforward : ∀ c, forward c = c) :
    Frame (MatrixGraphProblem.problem D hc) D.cells :=
  CheckedGraphGrowthFrames.frameWithForward
    (CheckedGraphGrowthFrames.identityFrame (MatrixGraphProblem.problem D hc) D.cells)
    (Equiv.refl _) forward (fun _ => rfl) hforward

#print axioms literalData
#print axioms frame
#print axioms identityFrame

end Papers.RationalityTen.MatrixGraphLiteralSemantics
end

end
end GraphSource0

section GraphSource1


@[expose] public section

/-!
# Complete geometric interpretation of a packed graph family

This module collects the independently checked parts of a graph certificate.
The computational node checks alone have no geometric conclusion: the caller
must also provide literal cell meanings, well-formed cells, genuine geometric
frames, and the complete disposition of every terminal boundary.

The resulting object is the existing `GraphFamilyClosure.FiniteClassification`.
Its completeness statement retains all edge and nonedge constraints. Thus it
can be used both for rational realizability and for the stronger alternatives
in Proposition 9 through `GraphFamilyClosure.hasTerminal_of_encoding`.
-/

noncomputable section
namespace Papers.RationalityTen.PackedGraphFamilyClosure

open ConcreteGrowth PackedGraphCertificate GraphGrowthInputs
open ActualGraphGrowthTarget LiteralGraphGrowthRenaming
open LiteralMaskGeometry

/-- Assemble a complete family without changing its computational problem or
discarding any geometric hypotheses needed by the soundness theorem. -/
def classification (D : RawData) (hvalid : Valid D.inputs)
    (hliteral : LiteralData (D.inputs.problem hvalid) D.data.cells)
    (hwell : ∀ i, WellFormed (D.data.cells i))
    (frames : Fin D.g → Frame (D.inputs.problem hvalid) D.data.cells)
    (hforward : ∀ f c, (frames f).cellMap.forward c = D.maps f c)
    (hnodes : ∀ i, RawGraphConditionedGrowth.nodeCheck
      (D.inputs.problem hvalid) D.maps D.leaf D.nodes i = true)
    (hnodup : ∀ j, (D.leaf j).Nodup)
    (certificates : Fin D.l → RawLeafCertificate.Certificate)
    (hchecked : ∀ j, RawLeafCertificate.check D.data.quota
      ((D.leaf j).map D.data.cells) (certificates j) = true) :
    GraphFamilyClosure.FiniteClassification (D.inputs.problem hvalid) D.data.cells where
  literal := hliteral
  wellFormed := hwell
  generatorCount := D.g
  frames := frames
  root := (D.nodes D.rootNode).cells
  leafCount := D.l
  leaves := D.leaf
  nodup := hnodup
  rawLeaves j := (D.leaf j).map D.data.cells
  raw_exact _ := rfl
  certificates := certificates
  checked := hchecked
  complete := by
    intro B hB hroot
    let renamings := fun f => (frames f).toRenaming hliteral hwell
    have hmaps : ∀ f c, (renamings f).boundary.cells.forward c = D.maps f c :=
      hforward
    have hchecks : ∀ i, GraphConditionedGrowth.nodeCheck
        (D.inputs.problem hvalid) renamings D.leaf D.nodes i = true := by
      intro i
      rw [← RawGraphConditionedGrowth.nodeCheck_eq
        (D.inputs.problem hvalid) D.maps renamings hmaps D.leaf D.nodes i]
      exact hnodes i
    exact GraphConditionedGrowth.complete_of_checks (D.inputs.problem hvalid)
      (GraphGrowthConstraints.vertexCapacitySound _) renamings D.leaf D.nodes
      hchecks B hB D.rootNode hroot

#print axioms classification

end Papers.RationalityTen.PackedGraphFamilyClosure
end

end
end GraphSource1

section GraphSource2

@[expose] public section

/-!
# From a complete finite certificate to geometric classification

The finite interface keeps all literal, matrix, frame and terminal facts.
This module constructs actual geometric frames, including identity maps, and
passes the full graph target to the existing classification soundness theorem.
-/

noncomputable section
namespace Papers.RationalityTen.CertifiedGraphGeometry

open PackedGraphCertificate GraphCaseCertificate SharedGraphCellPool
open ActualGraphGrowthTarget LiteralGraphGrowthRenaming
open MatroidChecked.FacetBoundaryEncoding LiteralMaskGeometry
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes

theorem literal (D : RawData) (C : Core D) :
    LiteralData (D.inputs.problem C.valid) D.data.cells := by
  rw [inputs_problem_eq D C.valid C.matrix]
  exact MatrixGraphLiteralSemantics.literalData D.data C.matrix C.literal

theorem exists_frame (D : RawData) (C : Core D) (f : Fin D.g) :
    ∃ F : Frame (D.inputs.problem C.valid) D.data.cells,
      ∀ c, F.cellMap.forward c = D.maps f c := by
  rw [inputs_problem_eq D C.valid C.matrix]
  rcases C.frames f with hid | ⟨v, w, inverse, h⟩
  · exact ⟨MatrixGraphLiteralSemantics.identityFrame D.data C.matrix
      (D.maps f) hid, fun _ => rfl⟩
  · exact ⟨MatrixGraphLiteralSemantics.frame D.data C.matrix v w
      (D.maps f) inverse h, fun _ => rfl⟩

def frames (D : RawData) (C : Core D) (f : Fin D.g) :
    Frame (D.inputs.problem C.valid) D.data.cells :=
  Classical.choose (exists_frame D C f)

theorem frames_forward (D : RawData) (C : Core D) (f : Fin D.g) (c : Fin D.n) :
    (frames D C f).cellMap.forward c = D.maps f c :=
  Classical.choose_spec (exists_frame D C f) c

def classification (D : RawData) (C : Core D)
    (hwell : ∀ i, WellFormed (D.data.cells i)) :
    GraphFamilyClosure.FiniteClassification (D.inputs.problem C.valid) D.data.cells :=
  PackedGraphFamilyClosure.classification D C.valid (literal D C) hwell
    (frames D C) (frames_forward D C) C.nodes C.leaf_nodup
    (Classical.choose C.leaves_checked) (Classical.choose_spec C.leaves_checked)

theorem hasTerminal (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hnonsimple : ∀ v : P.vertices, ¬ IsSimpleVertex P v)
    (D : RawData) (C : Core D) (hwell : ∀ i, WellFormed (D.data.cells i))
    (lab : P.vertices ≃ Fin 10)
    (E : Encoding P lab (fun i => decodeCell (D.data.cells i)))
    (htarget : GraphGrowthConstraints.Target (D.inputs.problem C.valid) E.family.toList)
    (hquota : ∀ t, (E.family.filter fun i => (D.data.cells i).kind = t).card =
      D.data.quota t) : ActualLeafTargetCoverage.HasTerminal P := by
  apply GraphFamilyClosure.hasTerminal_of_encoding P hP hnonsimple
    (D.inputs.problem C.valid) D.data.cells (classification D C hwell)
    lab E htarget ?_ hquota
  change GrowthDAG.Included (SparseGrowthDAG.family ((D.nodes D.rootNode).cells))
    (SparseGrowthDAG.family E.family.toList)
  rw [C.root_empty]
  simp [GrowthDAG.Included, SparseGrowthDAG.family, SparseGrowthDAG.has]

#print axioms literal
#print axioms exists_frame
#print axioms classification
#print axioms hasTerminal

end Papers.RationalityTen.CertifiedGraphGeometry
end

end
end GraphSource2

section GraphSource3


@[expose] public section

/-!
# The complete graph target for the remaining six-vertex facet type

The universe contains all 6,510 small cells and all 37,800 distinct embedded
copies of the required six-vertex template. The actual template assignment
and its exact counts prove coverage. The target's internal-nonedge count is
the full identity `E + L - p`, including the pentagonal correction.
-/

noncomputable section
namespace Papers.RationalityTen.FullSix0GraphTarget

open Finset Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeFacetSurplus ChirotopeDensity
open MatroidChecked.FacetBoundaryEncoding LiteralMaskGeometry
open ActualFacetInducedGraph ActualComplementGraph ActualGraphNormalization
open ActualGraphGrowthTarget ActualGraphCandidateRestriction
open ActualFacetTemplateAssignment SixFacetProfileRefinement
open GraphGrowthConstraints GraphCandidateCoverage TenGraphEdges

abbrev cells := FacetUniverses.FullSix0.cells

/-- All target conditions follow from the actual boundary. The hypotheses
about `D` state only exact finite-mask and numerical encodings. -/
theorem exists_target {d : Nat} (P : ConvexPolytope d) (hP : P.dim = 4)
    (lab : P.vertices ≃ Fin 10)
    (hnonsimple : ∀ v : P.vertices, ¬ IsSimpleVertex P v)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 6)
    (A : Assignment P)
    (hcounts : ∀ j : Fin 7, j ≠ 0 → (countsOf P A.kind).six j = 0)
    (D : Problem 44310 1024 45 10 5) (H : LiteralData D cells)
    (hquota : ∀ j, D.quota j = FullSix0FacetTargetBudgets.quota (countsOf P A.kind) j)
    (hminimum : D.minimumIncidence = 5)
    (hmissing : D.missingCount = (actualAllSixFacetBudget P).E +
      (actualAllSixFacetBudget P).L - (actualAllSixFacetBudget P).p)
    (hgraph : ∀ q : Fin 45, D.requiredEdges.testBit q.val = true ↔
      maskSet (edgeMask q) ∈ actualGraphEdges P lab) :
    ∃ E : Encoding P lab (fun i => decodeCell (cells i)),
      GraphGrowthConstraints.Target D E.family.toList := by
  obtain ⟨E, hE⟩ := FullSix0FacetActualCoverage.encoding_with_exact_counts P lab A hcounts
  refine ⟨E, ActualGraphGrowthTarget.actual_six_target D cells H
    FacetUniverses.FullSix0.cells_wellFormed E hP hnonsimple hfacets ?_
    hminimum ?_ hmissing⟩
  · intro j
    simp only [H.kind, hquota]
    exact hE j
  · intro q
    exact (hgraph q).trans (actual_graph_mask_membership cells
      FacetUniverses.FullSix0.cells_wellFormed E hP (edgeMask q) (edgeMask_lt q)).symm

theorem exists_target_of_complement {d : Nat} (P : ConvexPolytope d)
    (hP : P.dim = 4) (lab : P.vertices ≃ Fin 10)
    (hnonsimple : ∀ v : P.vertices, ¬ IsSimpleVertex P v)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 6)
    (A : Assignment P)
    (hcounts : ∀ j : Fin 7, j ≠ 0 → (countsOf P A.kind).six j = 0)
    (D : Problem 44310 1024 45 10 5) (H : LiteralData D cells)
    (hquota : ∀ j, D.quota j = FullSix0FacetTargetBudgets.quota (countsOf P A.kind) j)
    (hminimum : D.minimumIncidence = 5)
    (hmissing : D.missingCount = (actualAllSixFacetBudget P).E +
      (actualAllSixFacetBudget P).L - (actualAllSixFacetBudget P).p)
    (complement : Nat)
    (hrequired : ∀ q : Fin 45,
      D.requiredEdges.testBit q.val = !complement.testBit q.val)
    (hcomplement : ∀ q : Fin 45, complement.testBit q.val = true ↔
      maskSet (edgeMask q) ∉ actualGraphEdges P lab) :
    ∃ E : Encoding P lab (fun i => decodeCell (cells i)),
      GraphGrowthConstraints.Target D E.family.toList := by
  apply exists_target P hP lab hnonsimple hfacets A hcounts D H hquota hminimum hmissing
  intro q
  rw [hrequired, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, hcomplement, not_not]

/-- The exact induced-graph filter preserves every selected actual facet. -/
theorem selected_eligible {d : Nat} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} (D : Problem 44310 1024 45 10 5)
    (H : LiteralData D cells) (R : IncidenceRows 44310 10 45)
    (HR : RowsForCells R cells)
    (E : Encoding P lab (fun i => decodeCell (cells i))) (hP : P.dim = 4)
    (hB : GraphGrowthConstraints.Target D E.family.toList)
    (allowed complement : Nat)
    (hallowed : ∀ i, allowed.testBit i.val = true ↔ 0 < D.quota (cells i).kind)
    (hcomplement : ∀ q : Fin 45, complement.testBit q.val = true ↔
      maskSet (edgeMask q) ∉ actualGraphEdges P lab)
    (i : Fin 44310) (hi : i ∈ E.family) :
    (eligibleMask R allowed complement).testBit i.val = true := by
  have hraw (q : Fin 45) : complement.testBit q.val = true ↔
      edgeMask q ∉ literalGraphEdges cells E.family := by
    exact (hcomplement q).trans
      (not_congr (actual_graph_mask_membership cells
        FacetUniverses.FullSix0.cells_wellFormed E hP
        (edgeMask q) (edgeMask_lt q))).symm
  have hinduced := selected_induced R cells HR
    FacetUniverses.FullSix0.cells_wellFormed E hP complement hraw i hi
  have hedges (q : Fin 45) (hq : (R.edges i).testBit q.val = true) :
      (R.vertices i).testBit (R.first q).val = true ∧
        (R.vertices i).testBit (R.second q).val = true := by
    rw [hinduced q, Bool.and_eq_true_iff, Bool.and_eq_true_iff] at hq
    exact hq.1
  have hbudget (j : Nat) :
      (E.family.filter fun i => (cells i).kind = j).card ≤ D.quota j := by
    have hb := hB.boundary.budget j
    have hk : D.kind = fun i => (cells i).kind := funext H.kind
    rw [hk, ActualGrowthTarget.kindCount_toList] at hb
    exact hb
  apply (eligibleMask_bit_iff R allowed complement i hedges).mpr
  exact ⟨(hallowed i).mpr
    (E.selected_kind_quota_pos (fun i => (cells i).kind) D.quota hbudget i hi), hinduced⟩

/-- The full-universe geometry is enough to justify every graph-specific
local candidate universe once its exact eligible-mask equality is checked. -/
theorem target_and_eligible {d : Nat} (P : ConvexPolytope d)
    (hP : P.dim = 4) (lab : P.vertices ≃ Fin 10)
    (hnonsimple : ∀ v : P.vertices, ¬ IsSimpleVertex P v)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 6)
    (A : Assignment P)
    (hcounts : ∀ j : Fin 7, j ≠ 0 → (countsOf P A.kind).six j = 0)
    (D : Problem 44310 1024 45 10 5) (H : LiteralData D cells)
    (R : IncidenceRows 44310 10 45) (HR : RowsForCells R cells)
    (hquota : ∀ j, D.quota j = FullSix0FacetTargetBudgets.quota (countsOf P A.kind) j)
    (hminimum : D.minimumIncidence = 5)
    (hmissing : D.missingCount = (actualAllSixFacetBudget P).E +
      (actualAllSixFacetBudget P).L - (actualAllSixFacetBudget P).p)
    (allowed complement : Nat)
    (hallowed : ∀ i, allowed.testBit i.val = true ↔ 0 < D.quota (cells i).kind)
    (hrequired : ∀ q : Fin 45,
      D.requiredEdges.testBit q.val = !complement.testBit q.val)
    (hcomplement : ∀ q : Fin 45, complement.testBit q.val = true ↔
      maskSet (edgeMask q) ∉ actualGraphEdges P lab) :
    ∃ E : Encoding P lab (fun i => decodeCell (cells i)),
      GraphGrowthConstraints.Target D E.family.toList ∧
      ∀ i ∈ E.family, (eligibleMask R allowed complement).testBit i.val = true := by
  obtain ⟨E, hE⟩ := exists_target_of_complement P hP lab hnonsimple hfacets A hcounts
    D H hquota hminimum hmissing complement hrequired hcomplement
  exact ⟨E, hE, selected_eligible D H R HR E hP hE allowed complement hallowed hcomplement⟩

end Papers.RationalityTen.FullSix0GraphTarget

end
end
end GraphSource3
