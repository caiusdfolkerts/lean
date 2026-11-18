module
prelude
public import GraphPureGeometry
public import ResidualBatch.Graph
public import PackedIncidenceMatrix

/-! Reuse the literal incidence facts of a selected catalogue tuple each time
it occurs. Every geometric conclusion has its original RawData statement. -/
@[expose] public section
namespace Papers.RationalityTen.ResidualBatch.TupleSharing

open GraphPureGeometry PackedGraphCertificate RawGraphSemanticCertificate

def literalTupleCheck (t : GraphPureGeometry.Cell) : Bool :=
  let cell := PackedGraphData.cell t.cell
  decide ((PackedGraphData.finiteList 45 6 t.edgeList).map fastPairMask = cell.edges) &&
  (List.finRange 45).all (fun q =>
    decide (t.missing.testBit q.val =
      (cell.vertices.testBit (FastTenGraphEdges.first q).val &&
       cell.vertices.testBit (FastTenGraphEdges.second q).val &&
       !t.edges.testBit q.val)))

structure TupleFacts (t : GraphPureGeometry.Cell) : Prop where
  edgeMap : (PackedGraphData.finiteList 45 6 t.edgeList).map fastPairMask =
    (PackedGraphData.cell t.cell).edges
  missing : ∀ q : Fin 45, t.missing.testBit q.val =
    ((PackedGraphData.cell t.cell).vertices.testBit (FastTenGraphEdges.first q).val &&
     (PackedGraphData.cell t.cell).vertices.testBit (FastTenGraphEdges.second q).val &&
     !t.edges.testBit q.val)

theorem tupleFacts_of_check (t : GraphPureGeometry.Cell) (h : literalTupleCheck t = true) :
    TupleFacts t := by
  obtain ⟨he, hm⟩ := Bool.and_eq_true_iff.mp h
  exact ⟨of_decide_eq_true he, fun q =>
    of_decide_eq_true (List.all_eq_true.mp hm q (List.mem_finRange q))⟩

structure SlotAlignment (D : RawData) (t : Fin D.n → GraphPureGeometry.Cell) : Prop where
  cells : ∀ c, D.data.cells c = PackedGraphData.cell (t c).cell
  edgeLists : ∀ c, D.data.edgeLists c = PackedGraphData.finiteList 45 6 (t c).edgeList
  edgeMasks : ∀ c, D.data.edgeMasks c = (t c).edges
  missingMasks : ∀ c, D.data.missingMasks c = (t c).missing

theorem literal_of_shared (D : RawData) (t : Fin D.n → GraphPureGeometry.Cell)
    (alignment : SlotAlignment D t) (facts : ∀ c, TupleFacts (t c))
    (vertices : ∀ a c, (D.data.vertexRows a).testBit c.val = (D.data.cells c).vertices.testBit a.val) :
    LiteralFacts D.data where
  vertices := vertices
  edgeMap c := by rw [alignment.edgeLists, alignment.cells]; exact (facts c).edgeMap
  missing c q := by
    rw [alignment.missingMasks, alignment.cells, alignment.edgeMasks]
    exact (facts c).missing q

def vertexColumns (D : RawData) (c : Fin D.n) : List (Fin 10) :=
  (List.finRange 10).filter (fun v => (D.data.cells c).vertices.testBit v.val)

theorem vertexRows_of_code (D : RawData) (hw : D.vertexRows.width = D.n)
    (hcode : D.vertexRows.code = PackedIncidenceMatrix.code (vertexColumns D))
    (a : Fin 10) (c : Fin D.n) :
    (D.data.vertexRows a).testBit c.val = (D.data.cells c).vertices.testBit a.val := by
  have row : D.vertexRows.get a.val =
      PackedIncidenceMatrix.row D.n (PackedIncidenceMatrix.code (vertexColumns D)) a.val := by
    simp only [Fields.get, PackedRawNatGrowth.take, PackedRawNatGrowth.drop, hw, hcode,
      PackedIncidenceMatrix.row, PrimitiveBitsetGrowth.singleton_eq, Nat.one_shiftLeft,
      Nat.and_two_pow_sub_one_eq_mod]
  change (D.vertexRows.get a.val).testBit c.val = _
  rw [row, ← GrowthBitsets.bitAt_eq_testBit, PackedIncidenceMatrix.rows_exact]
  apply Bool.eq_iff_iff.mpr
  rw [SparseGrowthDAG.has_true]
  simp [vertexColumns, List.mem_finRange]

theorem literalTest_of_facts (D : RawData) (h : LiteralFacts D.data) (c : Fin D.n) :
    literalCellTest D.data c = true := by
  refine Bool.and_eq_true_iff.mpr ⟨decide_eq_true (h.edgeMap c), Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr fun a _ => decide_eq_true (h.vertices a c)
  · exact List.all_eq_true.mpr fun q _ => decide_eq_true (h.missing c q)

def sideRemainder (p : Packet) : Bool :=
  allFin (fun f => frameCheck p.data f (p.frame f)) &&
  (decide ((p.data.nodes p.data.rootNode).cells = []) &&
   allFin (fun j => RawLeafCertificate.check p.data.data.quota
     ((p.data.leaf j).map p.data.data.cells) (p.leaf j)))

theorem side_of_shared (p : Packet) (h : LiteralFacts p.data.data)
    (rest : sideRemainder p = true) : sideCheck p = true := by
  exact Bool.and_eq_true_iff.mpr ⟨List.all_eq_true.mpr
    (fun c _ => literalTest_of_facts p.data h c), rest⟩

end Papers.RationalityTen.ResidualBatch.TupleSharing
