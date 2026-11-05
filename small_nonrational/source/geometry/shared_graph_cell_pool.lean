module
prelude
public import PackedGraphInputs
public import RawGraphSemanticCertificate
public import GraphCandidateCoverage

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-!
# Reusing the literal facts of every global cell

A pool entry has one fixed2048-bit layout. Its geometric cell, proper-face
cache, edge and missing-edge lists, and vertex list are checked once against
the original global universe. Local graph records then need only equality
of their scalar entries with the selected pool entries. Local exclusions and
incidence matrices retain their separate exact checks.
-/

namespace Papers.RationalityTen.SharedGraphCellPool

open ConcreteGrowth PackedRawNatGrowth PackedGraphCertificate FiniteChecks
open GraphGrowthInputs GraphGrowthConstraints RawGraphSemanticCertificate
open SparseGrowthDAG

deriving instance DecidableEq for ConcreteGrowth.Cell

structure Entry where
  code : Nat

namespace Entry

def cellCode (E : Entry) := take 512 E.code
def faces (E : Entry) := take 1024 (drop 512 E.code)
def edgeCode (E : Entry) := take 128 (drop 1536 E.code)
def missingCode (E : Entry) := take 128 (drop 1664 E.code)
def edgeMask (E : Entry) := take 64 (drop 1792 E.code)
def missingMask (E : Entry) := take 64 (drop 1856 E.code)
def vertexCode (E : Entry) := take 128 (drop 1920 E.code)
def cell (E : Entry) := PackedGraphData.cell E.cellCode
def edges (E : Entry) := PackedGraphData.finiteList 45 6 E.edgeCode
def missing (E : Entry) := PackedGraphData.finiteList 45 6 E.missingCode
def vertices (E : Entry) := PackedGraphData.finiteList 10 4 E.vertexCode

def check (E : Entry) (original : Cell) (within : Nat → Nat) : Bool :=
  decide (E.cell = original) &&
  (decide (E.cell.kind < 5) &&
  (decide (E.cell.vertices < 1024) &&
  (FaceOnlyCompatibility.faceCheck E.cell E.faces &&
  (decide (E.edgeMask = PrimitiveBitsetGrowth.mask E.edges) &&
  (decide (E.missingMask = PrimitiveBitsetGrowth.mask E.missing) &&
  (decide (E.cell.vertices = PrimitiveBitsetGrowth.mask E.vertices) &&
  (decide (E.edges.map fastPairMask = E.cell.edges) &&
  (decide (E.missingMask = Nat.land (within E.cell.vertices)
      (Nat.xor (FiniteMaskSets.allMask 45) E.edgeMask)) &&
   decide (Nat.land E.edgeMask (within E.cell.vertices) = E.edgeMask)))))))))

structure Facts (E : Entry) (original : Cell) (within : Nat → Nat) : Prop where
  cell_eq : E.cell = original
  kind_lt : E.cell.kind < 5
  vertices_lt : E.cell.vertices < 1024
  faces_checked : FaceOnlyCompatibility.faceCheck E.cell E.faces = true
  edge_mask : E.edgeMask = PrimitiveBitsetGrowth.mask E.edges
  missing_mask : E.missingMask = PrimitiveBitsetGrowth.mask E.missing
  vertex_mask : E.cell.vertices = PrimitiveBitsetGrowth.mask E.vertices
  edge_map : E.edges.map fastPairMask = E.cell.edges
  missing_def : E.missingMask = Nat.land (within E.cell.vertices)
    (Nat.xor (FiniteMaskSets.allMask 45) E.edgeMask)
  edge_within : Nat.land E.edgeMask (within E.cell.vertices) = E.edgeMask

theorem facts_of_check (E : Entry) (original : Cell) (within : Nat → Nat)
    (h : E.check original within = true) : E.Facts original within := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩ :=
    (by simpa only [check, Bool.and_eq_true_iff, decide_eq_true_eq] using h)
  exact ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩

theorem missing_exact (E : Entry) (original : Cell) (within : Nat → Nat)
    (h : E.Facts original within)
    (hw : ∀ (v : Fin 1024) (q : Fin 45),
      (within v.val).testBit q.val =
        (v.val.testBit (FastTenGraphEdges.first q).val &&
         v.val.testBit (FastTenGraphEdges.second q).val)) (q : Fin 45) :
    E.missingMask.testBit q.val =
      (E.cell.vertices.testBit (FastTenGraphEdges.first q).val &&
       E.cell.vertices.testBit (FastTenGraphEdges.second q).val &&
       !E.edgeMask.testBit q.val) := by
  rw [h.missing_def, FiniteMaskSets.testBit_land, Nat.xor_eq, Nat.testBit_xor,
    FiniteMaskSets.allMask_bit q, hw ⟨E.cell.vertices, h.vertices_lt⟩ q]
  cases E.edgeMask.testBit q.val <;> rfl

end Entry

variable {N : Nat} [NeZero N]

def embedding (D : RawData) (c : Fin D.n) : Fin N :=
  Fin.ofNat N (D.embedding.get c.val)

def localEntry (D : RawData) (pool : Fin N → Entry) (c : Fin D.n) : Entry :=
  pool (embedding D c)

def alignedCheck (D : RawData) (pool : Fin N → Entry) (i : Nat) : Bool :=
  let c := Fin.ofNat D.n i
  let E := localEntry D pool c
  decide (D.embedding.get c.val < N) &&
  (decide (D.cells.get c.val = E.cellCode) &&
  (decide (D.faceMasks.get c.val = E.faces) &&
  (decide (D.edgeLists.get c.val = E.edgeCode) &&
  (decide (D.missingLists.get c.val = E.missingCode) &&
  (decide (D.edgeMasks.get c.val = E.edgeMask) &&
   decide (D.missingMasks.get c.val = E.missingMask))))))

structure Aligned (D : RawData) (pool : Fin N → Entry) (c : Fin D.n) : Prop where
  embedding_lt : D.embedding.get c.val < N
  cell_code : D.cells.get c.val = (localEntry D pool c).cellCode
  faces : D.faceMasks.get c.val = (localEntry D pool c).faces
  edge_code : D.edgeLists.get c.val = (localEntry D pool c).edgeCode
  missing_code : D.missingLists.get c.val = (localEntry D pool c).missingCode
  edge_mask : D.edgeMasks.get c.val = (localEntry D pool c).edgeMask
  missing_mask : D.missingMasks.get c.val = (localEntry D pool c).missingMask

theorem aligned_of_interval (D : RawData) (pool : Fin N → Entry)
    (h : Interval (alignedCheck D pool) 0 D.n) (c : Fin D.n) : Aligned D pool c := by
  have hc := h c.val (Nat.zero_le _) c.isLt
  obtain ⟨h1,h2,h3,h4,h5,h6,h7⟩ :=
    (by simpa only [alignedCheck, Fin.ofNat_val_eq_self, Bool.and_eq_true_iff,
      decide_eq_true_eq] using hc)
  exact ⟨h1,h2,h3,h4,h5,h6,h7⟩

namespace Aligned

variable {D : RawData} {pool : Fin N → Entry} {c : Fin D.n}

theorem cell (h : Aligned D pool c) : D.data.cells c = (localEntry D pool c).cell :=
  congrArg PackedGraphData.cell h.cell_code

theorem edges (h : Aligned D pool c) : D.data.edgeLists c = (localEntry D pool c).edges := by
  change PackedGraphData.finiteList 45 6 (D.edgeLists.get c.val) =
    PackedGraphData.finiteList 45 6 (localEntry D pool c).edgeCode
  rw [h.edge_code]

theorem missing (h : Aligned D pool c) : D.data.missingLists c = (localEntry D pool c).missing := by
  change PackedGraphData.finiteList 45 6 (D.missingLists.get c.val) =
    PackedGraphData.finiteList 45 6 (localEntry D pool c).missingCode
  rw [h.missing_code]

end Aligned

def localCheck (D : RawData) (i : Nat) : Bool :=
  let c := Fin.ofNat D.n i
  decide (D.data.badMasks c = PrimitiveBitsetGrowth.mask (D.data.badLists c)) &&
    ((D.data.badLists c).all (fun d => !D.data.testCompatible c d) &&
      (D.data.kindMasks (D.data.kind c)).testBit c.val)

/-- The expensive cell facts are reused from the pool. Every local mask and
every sparse exclusion retains its original pointwise interpretation. -/
theorem matrix_checked (D : RawData) (pool : Fin N → Entry)
    (original : Fin N → Cell) (within : Nat → Nat)
    (hpool : ∀ a, (pool a).Facts (original a) within)
    (haligned : ∀ c, Aligned D pool c) (hk : D.k = 5)
    (hlocal : Interval (localCheck D) 0 D.n)
    (hkind : Interval D.data.kindTest 0 D.k)
    (hridge : D.data.candidateMatrix = PackedIncidenceMatrix.code D.data.ridgeList)
    (hedge : D.data.edgeMatrix = PackedIncidenceMatrix.code D.data.edgeLists)
    (hmissing : D.data.missingMatrix = PackedIncidenceMatrix.code D.data.missingLists) :
    MatrixGraphProblem.Checked D.data := by
  apply MatrixGraphProblem.checked_of_intervals D.data _ hkind hridge hedge hmissing
  intro i hi hin
  let c : Fin D.n := ⟨i, hin⟩
  have ha := haligned c
  have hp := hpool (embedding D c)
  have hc := hlocal i hi hin
  have he := ha.edges
  have hm := ha.missing
  have hklt : D.data.kind c < D.k := by
    change (D.data.cells c).kind < D.k
    rw [ha.cell, hk]
    exact hp.kind_lt
  have hf : FaceOnlyCompatibility.faceCheck (D.data.cells c) (D.data.faceMasks c) = true := by
    change FaceOnlyCompatibility.faceCheck (D.data.cells c) (D.faceMasks.get c.val) = true
    rw [ha.cell, ha.faces]
    exact hp.faces_checked
  have hem : D.data.edgeMasks c = PrimitiveBitsetGrowth.mask (D.data.edgeLists c) := by
    change D.edgeMasks.get c.val = _
    rw [ha.edge_mask, he]
    exact hp.edge_mask
  have hmm : D.data.missingMasks c = PrimitiveBitsetGrowth.mask (D.data.missingLists c) := by
    change D.missingMasks.get c.val = _
    rw [ha.missing_mask, hm]
    exact hp.missing_mask
  have hfin : Fin.ofNat D.n i = c := Fin.ext (Nat.mod_eq_of_lt hin)
  have hc' : decide (D.data.badMasks c = PrimitiveBitsetGrowth.mask (D.data.badLists c)) = true ∧
      (D.data.badLists c).all (fun d => !D.data.testCompatible c d) = true ∧
      (D.data.kindMasks (D.data.kind c)).testBit c.val = true := by
    simpa only [localCheck, hfin, Bool.and_eq_true_iff] using hc
  have hkindmask : D.data.kindMasks (D.data.kind c) =
      PrimitiveBitsetGrowth.mask (D.data.kindLists (D.data.kind c)) := by
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp
      (hkind (D.data.kind c) (Nat.zero_le _) hklt)).1
  have hhas : has (D.data.kindLists (D.data.kind c)) c = true := by
    have hb := hc'.2.2
    rw [hkindmask, PrimitiveBitsetGrowth.mask_eq,
      ← GrowthBitsets.bitAt_eq_testBit, GrowthBitsets.bitAt_ofList_eq_has] at hb
    exact hb
  simp only [MatrixGraphProblem.Data.cellTest, hfin, Bool.and_eq_true_iff]
  exact ⟨decide_eq_true hklt, hf, hc'.1, hc'.2.1, hhas,
    decide_eq_true hem, decide_eq_true hmm⟩

theorem literal_cells (D : RawData) (pool : Fin N → Entry)
    (original : Fin N → Cell) (within : Nat → Nat)
    (hpool : ∀ a, (pool a).Facts (original a) within)
    (haligned : ∀ c, Aligned D pool c) (c : Fin D.n) :
    D.data.cells c = original (embedding D c) :=
  (haligned c).cell.trans (hpool (embedding D c)).cell_eq

theorem vertex_rows_of_code (D : RawData) (pool : Fin N → Entry)
    (hwidth : D.vertexRows.width = D.n)
    (hcode : D.vertexRows.code = PackedIncidenceMatrix.code
      (fun c => (localEntry D pool c).vertices)) (a : Fin 10) :
    D.data.vertexRows a = PackedIncidenceMatrix.row D.n
      (PackedIncidenceMatrix.code (fun c => (localEntry D pool c).vertices)) a.val := by
  change take D.vertexRows.width
    (drop (D.vertexRows.width * a.val) D.vertexRows.code) = _
  rw [hwidth, hcode]
  simp only [take, drop, Nat.land_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq,
    Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod, PackedIncidenceMatrix.row,
    PrimitiveBitsetGrowth.singleton_eq, Nat.shiftRight_eq']

/-- Vertex incidence is a sparse matrix using the pool's prechecked lists. -/
theorem literal_facts (D : RawData) (pool : Fin N → Entry)
    (original : Fin N → Cell) (within : Nat → Nat)
    (hpool : ∀ a, (pool a).Facts (original a) within)
    (haligned : ∀ c, Aligned D pool c)
    (hw : ∀ (v : Fin 1024) (q : Fin 45),
      (within v.val).testBit q.val =
        (v.val.testBit (FastTenGraphEdges.first q).val &&
         v.val.testBit (FastTenGraphEdges.second q).val))
    (hvertices : ∀ a : Fin 10,
      D.data.vertexRows a = PackedIncidenceMatrix.row D.n
        (PackedIncidenceMatrix.code (fun c => (localEntry D pool c).vertices)) a.val) :
    LiteralFacts D.data where
  vertices a c := by
    rw [hvertices, (haligned c).cell]
    exact PackedIncidenceMatrix.feature_rows_exact
      (fun c => (localEntry D pool c).vertices)
      (fun c => (localEntry D pool c).cell.vertices) _ rfl
      (fun c => (hpool (embedding D c)).vertex_mask) a c
  edgeMap c := by
    rw [(haligned c).edges, (haligned c).cell]
    exact (hpool (embedding D c)).edge_map
  missing c q := by
    change (D.missingMasks.get c.val).testBit q.val =
      ((D.data.cells c).vertices.testBit (FastTenGraphEdges.first q).val &&
       (D.data.cells c).vertices.testBit (FastTenGraphEdges.second q).val &&
       !(D.edgeMasks.get c.val).testBit q.val)
    rw [(haligned c).missing_mask, (haligned c).edge_mask, (haligned c).cell]
    exact Entry.missing_exact _ _ _ (hpool (embedding D c)) hw q

/-- Only proof fields differ between these two problem constructions. -/
theorem inputs_problem_eq (D : RawData) (hv : Valid D.inputs)
    (hc : MatrixGraphProblem.Checked D.data) :
    D.inputs.problem hv = MatrixGraphProblem.problem D.data hc := rfl

theorem valid_of_matrix (D : RawData) (hc : MatrixGraphProblem.Checked D.data) :
    Valid D.inputs := ofProblem_valid (MatrixGraphProblem.problem D.data hc)

#print axioms matrix_checked
#print axioms literal_cells
#print axioms literal_facts
#print axioms inputs_problem_eq

end Papers.RationalityTen.SharedGraphCellPool
