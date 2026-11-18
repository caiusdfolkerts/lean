module
prelude
public import SharedSmallGraphCellData000
public import SharedSmallGraphCellData001
public import SharedSmallGraphCellData002
public import SharedSmallGraphCellData003
public import SharedSmallGraphCellData004
public import SharedSmallGraphCellData005
public import SharedSmallGraphCellData006
public import SharedSmallGraphRowData

@[expose] public section
namespace Papers.RationalityTen.SharedSmallGraph
open Papers.RationalityTen
open ConcreteGrowth GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming GrowthBitsets
open BatchedGrowthPruning GraphGrowthConstraints FiniteChecks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def code (c : Fin cellCount) : Nat :=
  if c.val < 1024 then cellCodes000.get (c.val - 0) else
  if c.val < 2048 then cellCodes001.get (c.val - 1024) else
  if c.val < 3072 then cellCodes002.get (c.val - 2048) else
  if c.val < 4096 then cellCodes003.get (c.val - 3072) else
  if c.val < 5120 then cellCodes004.get (c.val - 4096) else
  if c.val < 6144 then cellCodes005.get (c.val - 5120) else
  cellCodes006.get (c.val - 6144)

noncomputable def edgeMask (c : Fin cellCount) : Nat := Nat.land (code c) (2^48-1)
noncomputable def missingMask (c : Fin cellCount) : Nat :=
  Nat.land (code c >>> 48) (2^48-1)
noncomputable def edgeIndices (c : Fin cellCount) : List (Fin 45) :=
  (unpackList (code c >>> 96)).1.map (Fin.ofNat 45)
noncomputable def candidateRows (q : Fin 1024) : Nat := (candidateTable.get q.val).1
noncomputable def candidateSupports (q : Fin 1024) : List (Fin cellCount) :=
  decodeSupport (candidateTable.get q.val).2
noncomputable def edgeRows (q : Fin 45) : Nat := edgeRowTable.get q.val
noncomputable def missingRows (q : Fin 45) : Nat := missingRowTable.get q.val
noncomputable def vertexRows (v : Fin 10) : Nat := vertexRowTable.get v.val
noncomputable def kindRows (j : Nat) : Nat := if j < 5 then kindRowTable.get j else 0
noncomputable def withinMask (v : Nat) : Nat := withinTable.get v

noncomputable def cellCheck (c : Fin cellCount) : Bool :=
  decide ((cells c).kind < 5) &&
  ((ridgeList cells c).all (fun q => (candidateRows q).testBit c.val) &&
  (decide (edgeMask c = PrimitiveBitsetGrowth.mask (edgeIndices c)) &&
  (decide ((edgeIndices c).map fastEdgeMask = (cells c).edges) &&
  ((List.finRange 10).all (fun v =>
    decide ((vertexRows v).testBit c.val = (cells c).vertices.testBit v.val)) &&
  ((List.finRange 5).all (fun j =>
    decide ((kindRows j.val).testBit c.val = decide ((cells c).kind = j.val))) &&
  ((List.finRange 45).all (fun q =>
    decide ((edgeRows q).testBit c.val = (edgeMask c).testBit q.val)) &&
  ((List.finRange 45).all (fun q =>
    decide ((missingRows q).testBit c.val = (missingMask c).testBit q.val)) &&
  (decide (missingMask c = Nat.land (withinMask (cells c).vertices)
    (Nat.xor (FiniteMaskSets.allMask 45) (edgeMask c))) &&
  (decide (Nat.land (edgeMask c) (withinMask (cells c).vertices) = edgeMask c) &&
  decide ((cells c).vertices < 1024))))))))))

noncomputable def candidateCheck (q : Fin 1024) : Bool :=
  decide (candidateRows q = PrimitiveBitsetGrowth.mask (candidateSupports q)) &&
  (candidateSupports q).all (fun c => has (ridgeList cells c) q)

noncomputable def withinCheck (v : Fin 1024) : Bool :=
  (List.finRange 45).all fun q => decide (
    (withinMask v.val).testBit q.val =
    (v.val.testBit (FastTenGraphEdges.first q).val &&
     v.val.testBit (FastTenGraphEdges.second q).val))
end Papers.RationalityTen.SharedSmallGraph
