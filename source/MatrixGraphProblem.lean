module
prelude
public import GraphProblemCertificate
public import FaceOnlyCompatibility
public import FiniteChecks
public import PackedIncidenceMatrix

@[expose] public section

/-!
# Graph problems certified by packed incidence matrices

Ridge, edge and missing-edge rows are certified simultaneously by their
sparse column encodings. Only the cell-local exclusions and five kind rows
need interval checks. Every cache law has its original pointwise meaning.
-/

namespace Papers.RationalityTen.MatrixGraphProblem

open ConcreteGrowth GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming GrowthBitsets
open BatchedGrowthPruning GraphGrowthConstraints FiniteChecks

structure Data (n e v k : Nat) where
  cells : Fin n → Cell
  quota : Nat → Nat
  faceMasks : Fin n → Nat
  candidateMatrix : Nat
  badLists : Fin n → List (Fin n)
  badMasks : Fin n → Nat
  kindLists : Nat → List (Fin n)
  kindMasks : Nat → Nat
  edgeLists : Fin n → List (Fin e)
  edgeMasks : Fin n → Nat
  edgeMatrix : Nat
  missingLists : Fin n → List (Fin e)
  missingMasks : Fin n → Nat
  missingMatrix : Nat
  vertexRows : Fin v → Nat
  requiredEdges : Nat
  missingCount : Nat
  minimumIncidence : Nat

variable {n e v k : Nat}

namespace Data

def ridgeList (D : Data n e v k) := ConcreteGrowth.ridgeList D.cells
def literalCompatible (D : Data n e v k) (a b : Fin n) :=
  ConcreteGrowth.compatible (D.cells a) (D.cells b)
def kind (D : Data n e v k) (c : Fin n) := (D.cells c).kind
def testCompatible (D : Data n e v k) (a b : Fin n) :=
  FaceOnlyCompatibility.compatible (D.cells a) (D.cells b) (D.faceMasks a) (D.faceMasks b)
def candidateMasks (D : Data n e v k) (q : Fin 1024) :=
  PackedIncidenceMatrix.row n D.candidateMatrix q.val
def edgeRows (D : Data n e v k) (q : Fin e) :=
  PackedIncidenceMatrix.row n D.edgeMatrix q.val
def missingRows (D : Data n e v k) (q : Fin e) :=
  PackedIncidenceMatrix.row n D.missingMatrix q.val

def cellTest [NeZero n] (D : Data n e v k) (i : Nat) : Bool :=
  let c := Fin.ofNat n i
  decide (D.kind c < k) &&
    (FaceOnlyCompatibility.faceCheck (D.cells c) (D.faceMasks c) &&
    (decide (D.badMasks c = PrimitiveBitsetGrowth.mask (D.badLists c)) &&
    ((D.badLists c).all (fun d => !D.testCompatible c d) &&
    (has (D.kindLists (D.kind c)) c &&
    (decide (D.edgeMasks c = PrimitiveBitsetGrowth.mask (D.edgeLists c)) &&
     decide (D.missingMasks c = PrimitiveBitsetGrowth.mask (D.missingLists c)))))))

def kindTest (D : Data n e v k) (i : Nat) : Bool :=
  decide (D.kindMasks i = PrimitiveBitsetGrowth.mask (D.kindLists i)) &&
    (D.kindLists i).all (fun c => decide (D.kind c = i))

end Data

/-- The complete semantic obligations, all established by the finite checks. -/
structure Checked (D : Data n e v k) : Prop where
  cellFacts : ∀ c,
    decide (D.kind c < k) = true ∧
    FaceOnlyCompatibility.faceCheck (D.cells c) (D.faceMasks c) = true ∧
    decide (D.badMasks c = PrimitiveBitsetGrowth.mask (D.badLists c)) = true ∧
    (D.badLists c).all (fun d => !D.testCompatible c d) = true ∧
    has (D.kindLists (D.kind c)) c = true ∧
    decide (D.edgeMasks c = PrimitiveBitsetGrowth.mask (D.edgeLists c)) = true ∧
    decide (D.missingMasks c = PrimitiveBitsetGrowth.mask (D.missingLists c)) = true
  kindFacts : ∀ j, j < k →
    D.kindMasks j = PrimitiveBitsetGrowth.mask (D.kindLists j) ∧
      (D.kindLists j).all (fun c => decide (D.kind c = j)) = true
  candidateMatrix : D.candidateMatrix = PackedIncidenceMatrix.code D.ridgeList
  edgeMatrix : D.edgeMatrix = PackedIncidenceMatrix.code D.edgeLists
  missingMatrix : D.missingMatrix = PackedIncidenceMatrix.code D.missingLists

theorem checked_of_intervals [NeZero n] (D : Data n e v k)
    (hcell : Interval D.cellTest 0 n)
    (hkind : Interval D.kindTest 0 k)
    (hcandidate : D.candidateMatrix = PackedIncidenceMatrix.code D.ridgeList)
    (hedge : D.edgeMatrix = PackedIncidenceMatrix.code D.edgeLists)
    (hmissing : D.missingMatrix = PackedIncidenceMatrix.code D.missingLists) : Checked D where
  cellFacts c := by
    have h := hcell c.val (Nat.zero_le _) c.isLt
    simpa only [Data.cellTest, Fin.ofNat_val_eq_self, Bool.and_eq_true_iff] using h
  kindFacts j hj := by
    have h := hkind j (Nat.zero_le _) hj
    simpa only [Data.kindTest, Bool.and_eq_true_iff, decide_eq_true_eq] using h
  candidateMatrix := hcandidate
  edgeMatrix := hedge
  missingMatrix := hmissing

def cache (D : Data n e v k) (h : Checked D) :
    Cache D.ridgeList D.literalCompatible D.kind where
  candidates := D.candidateMasks
  incompatible := D.badMasks
  kinds := D.kindMasks
  keys := List.range k
  candidates_exact := PackedIncidenceMatrix.rows_exact_of_code D.ridgeList
    D.candidateMatrix h.candidateMatrix
  incompatible_sound := GrowthCacheCertificate.incompatible_sound
    D.literalCompatible D.testCompatible
    (fun a b hab => FaceOnlyCompatibility.necessary (D.cells a) (D.cells b)
      (D.faceMasks a) (D.faceMasks b) (h.cellFacts a).2.1 (h.cellFacts b).2.1 hab)
    D.badLists D.badMasks
    (fun c => (of_decide_eq_true (h.cellFacts c).2.2.1).trans (PrimitiveBitsetGrowth.mask_eq _))
    (fun c => (h.cellFacts c).2.2.2.1)
  kind_sound := GrowthCacheCertificate.kind_sound D.kind D.kindLists D.kindMasks (List.range k)
    (fun j hj => (h.kindFacts j (List.mem_range.mp hj)).1.trans (PrimitiveBitsetGrowth.mask_eq _))
    (fun j hj => (h.kindFacts j (List.mem_range.mp hj)).2)

def problem (D : Data n e v k) (h : Checked D) : Problem n 1024 e v k where
  ridgeList := D.ridgeList
  compatible := D.literalCompatible
  kind := D.kind
  quota := D.quota
  cache := cache D h
  kind_lt c := of_decide_eq_true (h.cellFacts c).1
  kind_exact := GraphProblemCertificate.kind_exact D.kind D.kindLists D.kindMasks k
    (fun j hj => (h.kindFacts j hj).1)
    (fun c => (h.cellFacts c).2.2.2.2.1)
    (fun j hj => (h.kindFacts j hj).2)
  vertexRows := D.vertexRows
  edges := D.edgeMasks
  missing := D.missingMasks
  edgeRows := D.edgeRows
  missingRows := D.missingRows
  edgeRows_exact := PackedIncidenceMatrix.feature_rows_exact D.edgeLists D.edgeMasks
    D.edgeMatrix h.edgeMatrix
    (fun c => of_decide_eq_true (h.cellFacts c).2.2.2.2.2.1)
  missingRows_exact := PackedIncidenceMatrix.feature_rows_exact D.missingLists D.missingMasks
    D.missingMatrix h.missingMatrix
    (fun c => of_decide_eq_true (h.cellFacts c).2.2.2.2.2.2)
  requiredEdges := D.requiredEdges
  missingCount := D.missingCount
  minimumIncidence := D.minimumIncidence

/-- Two interval checks and three sparse matrix equalities construct the
full graph problem. No candidate or edge-row support lists are required. -/
def ofChecks [NeZero n] (D : Data n e v k)
    (hcell : Interval D.cellTest 0 n)
    (hkind : Interval D.kindTest 0 k)
    (hcandidate : D.candidateMatrix = PackedIncidenceMatrix.code D.ridgeList)
    (hedge : D.edgeMatrix = PackedIncidenceMatrix.code D.edgeLists)
    (hmissing : D.missingMatrix = PackedIncidenceMatrix.code D.missingLists) : Problem n 1024 e v k :=
  problem D (checked_of_intervals D hcell hkind hcandidate hedge hmissing)

#print axioms ofChecks

end Papers.RationalityTen.MatrixGraphProblem
