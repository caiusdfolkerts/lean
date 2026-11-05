module
prelude
public import TwoPartMaskRelabel
public import PackedGraphCertificate
public import RawGraphSemanticCertificate

@[expose] public section

/-!
# Shared, fully checked relabeling facts

Each group records one vertex permutation and only the global cell pairs on
which it is used. Its two small mask tables and its edge-slot table are checked
once. Every cell pair is then checked with the exact original cell predicate.

A local graph frame reuses these facts after checking both inverse laws and
both endpoint indices of each local cell map. Its graph bits are checked
separately. Thus shared storage removes repeated computation without weakening
the geometric meaning of any frame.
-/

namespace Papers.RationalityTen.SharedGraphFramePairs

open ConcreteGrowth PackedGraphCertificate FiniteChecks RawGraphGrowthFrames
open RawGraphSemanticCertificate

structure Group where
  vertexCode : Nat
  inverseVertexCode : Nat
  lowTable : Nat
  highTable : Nat
  edgeTable : Nat
  pairPred : Nat
  pairs : Fields

namespace Group

abbrev count (D : Group) := D.pairPred + 1

def sourceNat (D : Group) (i : Fin D.count) : Nat :=
  (D.pairs.get i.val) % 65536

def targetNat (D : Group) (i : Fin D.count) : Nat :=
  (D.pairs.get i.val >>> 16) % 65536

def source {N : Nat} [NeZero N] (D : Group) (i : Fin D.count) : Fin N :=
  Fin.ofNat N (D.sourceNat i)

def target {N : Nat} [NeZero N] (D : Group) (i : Fin D.count) : Fin N :=
  Fin.ofNat N (D.targetNat i)

def edgeSlot (D : Group) (q : Fin 45) : Fin 45 :=
  Fin.ofNat 45 ((D.edgeTable >>> (6 * q.val)) % 64)

def headerCheck (D : Group) : Bool :=
  TenGraphEdges.permutationCheck D.vertexCode D.inverseVertexCode &&
    (decide (∀ i : Fin 32, TwoPartMaskRelabel.halfLookup D.lowTable i =
      RawBoundaryMatch.renameMask (TenGraphEdges.vertexMap D.vertexCode) i.val) &&
    (decide (∀ i : Fin 32, TwoPartMaskRelabel.halfLookup D.highTable i =
      RawBoundaryMatch.renameMask (TenGraphEdges.vertexMap D.vertexCode) (i.val <<< 5)) &&
     decide (∀ q : Fin 45, D.edgeSlot q =
      TenGraphEdges.encode
        (TenGraphEdges.vertexMap D.vertexCode (TenGraphEdges.first q))
        (TenGraphEdges.vertexMap D.vertexCode (TenGraphEdges.second q)))))

def pairTest {N : Nat} [NeZero N] (D : Group) (cells : Fin N → Cell)
    (i : Nat) : Bool :=
  let j := Fin.ofNat D.count i
  decide (D.sourceNat j < N) &&
    (decide (D.targetNat j < N) &&
      CachedCellRelabel.bitsetCellCheck
        (TwoPartMaskRelabel.rename D.lowTable D.highTable)
        (cells (D.source j)) (cells (D.target j)))

structure Facts {N : Nat} [NeZero N] (D : Group) (cells : Fin N → Cell) : Prop where
  vertices : TenGraphEdges.permutationCheck D.vertexCode D.inverseVertexCode = true
  source_lt : ∀ i, D.sourceNat i < N
  target_lt : ∀ i, D.targetNat i < N
  edges : ∀ q : Fin 45, D.edgeSlot q =
    TenGraphEdges.encode
      (TenGraphEdges.vertexMap D.vertexCode (TenGraphEdges.first q))
      (TenGraphEdges.vertexMap D.vertexCode (TenGraphEdges.second q))
  pairs : ∀ i, cellRelabelCheck (TenGraphEdges.vertexMap D.vertexCode)
    (cells (D.source i)) (cells (D.target i)) = true

theorem facts_of_checks {N : Nat} [NeZero N] (D : Group) (cells : Fin N → Cell)
    (hheader : D.headerCheck = true)
    (hpair : Interval (D.pairTest cells) 0 D.count) : D.Facts cells := by
  obtain ⟨hv, hl, hh, he⟩ :=
    (by simpa only [headerCheck, Bool.and_eq_true_iff, decide_eq_true_eq] using hheader)
  have hp (i : Fin D.count) : D.sourceNat i < N ∧ D.targetNat i < N ∧
      CachedCellRelabel.bitsetCellCheck
        (TwoPartMaskRelabel.rename D.lowTable D.highTable)
        (cells (D.source i)) (cells (D.target i)) = true := by
    have h := hpair i.val (Nat.zero_le _) i.isLt
    simpa only [pairTest, Fin.ofNat_val_eq_self, Bool.and_eq_true_iff,
      decide_eq_true_eq] using h
  refine ⟨hv, fun i => (hp i).1, fun i => (hp i).2.1, he, ?_⟩
  intro i
  have h := (hp i).2.2
  rw [TwoPartMaskRelabel.cellCheck_exact _ _ _ hl hh] at h
  exact h

def graphBitCheck (D : Group) (required : Nat) (q : Fin 45) : Bool :=
  decide (required.testBit (D.edgeSlot q).val = required.testBit q.val)

def localPairCheck {n N : Nat} [NeZero N] (D : Group)
    (embedding : Fin n → Fin N) (forward inverse : Fin n → Fin n)
    (indices : Fin n → Fin D.count) (c : Fin n) : Bool :=
  inverseCheckAt forward inverse c &&
    (decide (D.source (indices c) = embedding c) &&
      decide (D.target (indices c) = embedding (forward c)))

/-- Reuse global cell facts only after checking the complete local map. -/
theorem local_frameFacts {n N : Nat} [NeZero N]
    (globalCells : Fin N → Cell) (cells : Fin n → Cell)
    (embedding : Fin n → Fin N) (hcells : ∀ c, cells c = globalCells (embedding c))
    (D : Group) (hD : D.Facts globalCells) (required : Nat)
    (forward inverse : Fin n → Fin n) (indices : Fin n → Fin D.count)
    (hgraph : ∀ q, D.graphBitCheck required q = true)
    (hlinks : ∀ c, D.localPairCheck embedding forward inverse indices c = true) :
    FrameFacts cells required D.vertexCode D.inverseVertexCode forward inverse where
  vertices := hD.vertices
  inverse c := (Bool.and_eq_true_iff.mp (hlinks c)).1
  cells c := by
    obtain ⟨hs, ht⟩ := (by
      simpa only [localPairCheck, Bool.and_eq_true_iff, decide_eq_true_eq] using
        (Bool.and_eq_true_iff.mp (hlinks c)).2)
    have h := hD.pairs (indices c)
    rw [hs, ht, ← hcells c, ← hcells (forward c)] at h
    exact h
  graph q := by
    change decide (required.testBit
      (TenGraphEdges.encode
        (TenGraphEdges.vertexMap D.vertexCode (TenGraphEdges.first q))
        (TenGraphEdges.vertexMap D.vertexCode (TenGraphEdges.second q))).val =
      required.testBit q.val) = true
    rw [← hD.edges q]
    exact hgraph q

#print axioms facts_of_checks
#print axioms local_frameFacts

end Group
end Papers.RationalityTen.SharedGraphFramePairs
