module
prelude
public import MatrixGraphProblem
public import PackedGraphData
public import FastGeneralGraphReplay

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-!
# A compact record for a complete finite graph certificate

The record contains only natural numbers. All lists, cell maps and graph
nodes are transparent decodings of those numbers. A single metadata proof
constructs the semantic graph problem. Node blocks take that proof as an
argument, so they never repeat the metadata calculation.

This interface proves the original `RawGraphConditionedGrowth.nodeCheck`.
As with that checker, identification of the recorded cell maps with genuine
geometric relabellings belongs to the separate geometric interpretation.
-/

namespace Papers.RationalityTen.PackedGraphCertificate

open ConcreteGrowth PackedRawNatGrowth FiniteChecks GraphGrowthConstraints

/-- Fixed-width entries in one natural number, least significant entry first. -/
structure Fields where
  width : Nat
  code : Nat

def Fields.get (a : Fields) (i : Nat) : Nat :=
  take a.width (drop (a.width * i) a.code)

/-- All dimensions are positive by construction. An empty terminal catalogue
uses one unused empty leaf, exactly as in the original graph emitter. -/
structure RawData where
  cellPred : Nat
  framePred : Nat
  leafPred : Nat
  nodePred : Nat
  kindPred : Nat
  cellWidth : Nat
  frameWidth : Nat
  leafWidth : Nat
  nodeWidth : Nat
  quota : Fields
  cells : Fields
  faceMasks : Fields
  candidateMatrix : Nat
  badLists : Fields
  badMasks : Fields
  kindLists : Fields
  kindMasks : Fields
  edgeLists : Fields
  edgeMasks : Fields
  edgeMatrix : Nat
  missingLists : Fields
  missingMasks : Fields
  missingMatrix : Nat
  vertexRows : Fields
  requiredEdges : Nat
  missingCount : Nat
  minimumIncidence : Nat
  cellMaps : Nat
  inverseCellMaps : Nat
  vertexMaps : Nat
  inverseVertexMaps : Nat
  embedding : Fields
  leaves : Fields
  nodeCodes : Fields
  selectedMasks : Fields
  baseMasks : Fields
  bounds : Fields
  missingSupport : Nat
  root : Nat
  rootFrame : Nat

namespace RawData

abbrev n (D : RawData) := D.cellPred + 1
abbrev g (D : RawData) := D.framePred + 1
abbrev l (D : RawData) := D.leafPred + 1
abbrev t (D : RawData) := D.nodePred + 1
abbrev k (D : RawData) := D.kindPred + 1

def data (D : RawData) : MatrixGraphProblem.Data D.n 45 10 D.k where
  cells c := PackedGraphData.cell (D.cells.get c.val)
  quota j := if j < D.k then D.quota.get j else 0
  faceMasks c := D.faceMasks.get c.val
  candidateMatrix := D.candidateMatrix
  badLists c := PackedGraphData.finiteList D.n D.cellWidth (D.badLists.get c.val)
  badMasks c := D.badMasks.get c.val
  kindLists j := if j < D.k then
    PackedGraphData.finiteList D.n D.cellWidth (D.kindLists.get j) else []
  kindMasks j := if j < D.k then D.kindMasks.get j else 0
  edgeLists c := PackedGraphData.finiteList 45 6 (D.edgeLists.get c.val)
  edgeMasks c := D.edgeMasks.get c.val
  edgeMatrix := D.edgeMatrix
  missingLists c := PackedGraphData.finiteList 45 6 (D.missingLists.get c.val)
  missingMasks c := D.missingMasks.get c.val
  missingMatrix := D.missingMatrix
  vertexRows v := D.vertexRows.get v.val
  requiredEdges := D.requiredEdges
  missingCount := D.missingCount
  minimumIncidence := D.minimumIncidence

def maps (D : RawData) (f : Fin D.g) (c : Fin D.n) : Fin D.n :=
  Fin.ofNat D.n (take D.cellWidth
    (drop (D.cellWidth * (D.n * f.val + c.val)) D.cellMaps))

def inverseMaps (D : RawData) (f : Fin D.g) (c : Fin D.n) : Fin D.n :=
  Fin.ofNat D.n (take D.cellWidth
    (drop (D.cellWidth * (D.n * f.val + c.val)) D.inverseCellMaps))

def vertexCode (D : RawData) (f : Fin D.g) : Nat :=
  take 40 (drop (40 * f.val) D.vertexMaps)

def inverseVertexCode (D : RawData) (f : Fin D.g) : Nat :=
  take 40 (drop (40 * f.val) D.inverseVertexMaps)

def leaf (D : RawData) (j : Fin D.l) : List (Fin D.n) :=
  PackedGraphData.finiteList D.n D.cellWidth (D.leaves.get j.val)

def nodes (D : RawData) (i : Fin D.t) :
    GraphConditionedGrowth.Node D.n 1024 45 10 D.k D.g D.l D.t :=
  PackedGeneralGraphNodes.decode D.k D.cellWidth D.nodeWidth D.frameWidth D.leafWidth
    (D.nodeCodes.get i.val) (D.selectedMasks.get i.val)

/-- One option occupies each field; bit0 marks `some`, and the remaining
bits use the ordinary length-prefixed cell-list encoding. -/
def bound (D : RawData) (i : Fin D.t) : FastGraphRuleCheck.Bounds D.n :=
  (List.range D.k).map fun j =>
    let code := D.bounds.get (D.k * i.val + j)
    if take 1 code = 0 then none else
      some (PackedGraphData.finiteList D.n D.cellWidth (drop 1 code))

def base (D : RawData) (i : Fin D.t) : Nat := D.baseMasks.get i.val

def support (D : RawData) : List (Fin 45) :=
  PackedGraphData.finiteList 45 6 D.missingSupport

def rootNode (D : RawData) : Fin D.t := Fin.ofNat D.t D.root
def rootMap (D : RawData) : Fin D.g := Fin.ofNat D.g D.rootFrame

/-- These are precisely the matrix problem's cache obligations, together
with the missing-feature support and no-duplicates property of each leaf. -/
def metadataCheck (D : RawData) : Bool :=
  checkRange D.data.cellTest 0 D.n &&
    (checkRange D.data.kindTest 0 D.k &&
    (decide (D.data.candidateMatrix = PackedIncidenceMatrix.code D.data.ridgeList) &&
    (decide (D.data.edgeMatrix = PackedIncidenceMatrix.code D.data.edgeLists) &&
    (decide (D.data.missingMatrix = PackedIncidenceMatrix.code D.data.missingLists) &&
    (decide (∀ q : Fin 45, q ∈ D.support ∨ D.data.missingRows q = 0) &&
      checkRange (fun j => decide ((D.leaf (Fin.ofNat D.l j)).Nodup)) 0 D.l)))))

theorem metadata_checked (D : RawData) (h : D.metadataCheck = true) :
    MatrixGraphProblem.Checked D.data := by
  obtain ⟨hc, hk, hr, he, hm, hs, hl⟩ :=
    (by simpa only [metadataCheck, Bool.and_eq_true_iff] using h)
  exact MatrixGraphProblem.checked_of_intervals D.data
    (by simpa only [Nat.zero_add] using interval_of_check _ 0 D.n hc)
    (by simpa only [Nat.zero_add] using interval_of_check _ 0 D.k hk)
    (of_decide_eq_true hr) (of_decide_eq_true he) (of_decide_eq_true hm)

def problem (D : RawData) (h : D.metadataCheck = true) :
    Problem D.n 1024 45 10 D.k :=
  MatrixGraphProblem.problem D.data (D.metadata_checked h)

theorem support_sound (D : RawData) (h : D.metadataCheck = true) :
    FastGeneralGraphReplay.SupportsMissing (D.problem h) D.support := by
  obtain ⟨hc, hk, hr, he, hm, hs, hl⟩ :=
    (by simpa only [metadataCheck, Bool.and_eq_true_iff] using h)
  change ∀ q : Fin 45, q ∈ D.support ∨ D.data.missingRows q = 0
  exact of_decide_eq_true hs

theorem leaves_nodup (D : RawData) (h : D.metadataCheck = true) (j : Fin D.l) :
    (D.leaf j).Nodup := by
  obtain ⟨hc, hk, hr, he, hm, hs, hl⟩ :=
    (by simpa only [metadataCheck, Bool.and_eq_true_iff] using h)
  have checked := checkRange_sound _ 0 D.l hl j.val (Nat.zero_le _)
    (by simpa only [Nat.zero_add] using j.isLt)
  simpa only [Fin.ofNat_val_eq_self, decide_eq_true_eq] using checked

/-- The supplied metadata proof is used only to construct the semantic
problem. It is not re-evaluated inside this executable node predicate. -/
def nodeTest (D : RawData) (h : D.metadataCheck = true) (i : Nat) : Bool :=
  FastGeneralGraphReplay.nodeCheck (D.problem h) D.support D.maps D.bound D.base
    D.leaf D.nodes (Fin.ofNat D.t i)

theorem nodeTest_sound (D : RawData) (h : D.metadataCheck = true) (i : Nat)
    (hi : D.nodeTest h i = true) :
    RawGraphConditionedGrowth.nodeCheck (D.problem h) D.maps D.leaf D.nodes
      (Fin.ofNat D.t i) = true :=
  FastGeneralGraphReplay.nodeCheck_sound (D.problem h) D.support (D.support_sound h)
    D.maps D.bound D.base D.leaf D.nodes (Fin.ofNat D.t i) hi

theorem node_checks (D : RawData) (h : D.metadataCheck = true)
    (checked : Interval (D.nodeTest h) 0 D.t) (i : Fin D.t) :
    RawGraphConditionedGrowth.nodeCheck (D.problem h) D.maps D.leaf D.nodes i = true := by
  have hi := D.nodeTest_sound h i.val (checked i.val (Nat.zero_le _) i.isLt)
  simpa only [Fin.ofNat_val_eq_self] using hi

end RawData

/-- A batch uses one family of literal records and one metadata interval. -/
theorem batch_metadata {m : Nat} [NeZero m] (records : Fin m → RawData)
    (checked : Interval (fun i => (records (Fin.ofNat m i)).metadataCheck) 0 m)
    (i : Fin m) : (records i).metadataCheck = true :=
  fin_of_interval (fun i => (records i).metadataCheck) checked i

def batchNodeTest {m : Nat} [NeZero m] (records : Fin m → RawData)
    (metadata : ∀ i, (records i).metadataCheck = true) (i : Nat) : Bool :=
  let j := Fin.ofNat m i
  checkRange ((records j).nodeTest (metadata j)) 0 (records j).t

/-- One interval over a batch implies every original node predicate for
every graph in that batch, including its own variable dimensions. -/
theorem batch_node_checks {m : Nat} [NeZero m] (records : Fin m → RawData)
    (metadata : ∀ i, (records i).metadataCheck = true)
    (checked : Interval (batchNodeTest records metadata) 0 m)
    (j : Fin m) (i : Fin (records j).t) :
    RawGraphConditionedGrowth.nodeCheck ((records j).problem (metadata j))
      (records j).maps (records j).leaf (records j).nodes i = true := by
  have h := fin_of_interval (fun j : Fin m =>
    checkRange ((records j).nodeTest (metadata j)) 0 (records j).t) checked j
  exact (records j).node_checks (metadata j)
    (by simpa only [Nat.zero_add] using interval_of_check _ 0 _ h) i

#print axioms RawData.metadata_checked
#print axioms RawData.nodeTest_sound
#print axioms batch_node_checks

end Papers.RationalityTen.PackedGraphCertificate
