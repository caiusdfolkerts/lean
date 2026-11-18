module
prelude
public import PackedSlot
public import TupleLiteralSharing

@[expose] public section
namespace Papers.RationalityTen.ResidualBatch.TupleSharing
open PackedGraphCertificate RawGraphSemanticCertificate

inductive Certified : List GraphPureGeometry.Cell → Prop where
  | nil : Certified []
  | cons {x xs} (head : TupleFacts x) (tail : Certified xs) : Certified (x :: xs)

theorem Certified.at_mem {xs : List GraphPureGeometry.Cell} (proof : Certified xs)
    {x} (member : x ∈ xs) : TupleFacts x := by
  induction proof with
  | nil => simp at member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with eq | mem
    · cases eq; exact head
    · exact ih mem

def slot (D : RawData) (xs : List GraphPureGeometry.Cell) (hlen : xs.length = D.n)
    (c : Fin D.n) := xs[c.val]'(by simpa only [hlen] using c.isLt)

theorem get_of_packed {α : Type} (witness : Fields) (field : α → Nat) (xs : List α)
    (code : witness.code = GraphPureGeometry.pack field witness.width xs)
    (bound : xs.all (fun t => decide (field t < 2^witness.width)) = true)
    (i : Nat) (hi : i < xs.length) : witness.get i = field xs[i] := by
  cases witness with
  | mk w v =>
    change v = GraphPureGeometry.pack field w xs at code
    subst v
    exact get_pack field w xs (fun t ht => of_decide_eq_true (List.all_eq_true.mp bound t ht)) i hi

structure PackedAlignment (D : RawData) (xs : List GraphPureGeometry.Cell) : Prop where
  length_eq : xs.length = D.n
  cellCode : D.cells.code = GraphPureGeometry.pack GraphPureGeometry.Cell.cell D.cells.width xs
  edgeListCode : D.edgeLists.code = GraphPureGeometry.pack GraphPureGeometry.Cell.edgeList D.edgeLists.width xs
  edgeCode : D.edgeMasks.code = GraphPureGeometry.pack GraphPureGeometry.Cell.edges D.edgeMasks.width xs
  missingCode : D.missingMasks.code = GraphPureGeometry.pack GraphPureGeometry.Cell.missing D.missingMasks.width xs
  cellBound : xs.all (fun t => decide (t.cell < 2^D.cells.width)) = true
  edgeListBound : xs.all (fun t => decide (t.edgeList < 2^D.edgeLists.width)) = true
  edgeBound : xs.all (fun t => decide (t.edges < 2^D.edgeMasks.width)) = true
  missingBound : xs.all (fun t => decide (t.missing < 2^D.missingMasks.width)) = true

theorem PackedAlignment.exactSlots {D : RawData} {xs} (h : PackedAlignment D xs) :
    SlotAlignment D (slot D xs h.length_eq) := by
  constructor <;> intro c
  · exact congrArg PackedGraphData.cell (get_of_packed D.cells _ xs h.cellCode h.cellBound c.val
      (by simpa only [h.length_eq] using c.isLt))
  · exact congrArg (fun code => PackedGraphData.finiteList 45 6 code)
      (get_of_packed D.edgeLists _ xs h.edgeListCode h.edgeListBound c.val
        (by simpa only [h.length_eq] using c.isLt))
  · exact get_of_packed D.edgeMasks _ xs h.edgeCode h.edgeBound c.val
      (by simpa only [h.length_eq] using c.isLt)
  · exact get_of_packed D.missingMasks _ xs h.missingCode h.missingBound c.val
      (by simpa only [h.length_eq] using c.isLt)

theorem literal_of_packed (D : RawData) (xs : List GraphPureGeometry.Cell)
    (alignment : PackedAlignment D xs) (catalogue : Certified xs)
    (width : D.vertexRows.width = D.n)
    (matrix : D.vertexRows.code = PackedIncidenceMatrix.code (vertexColumns D)) :
    LiteralFacts D.data := by
  refine literal_of_shared D (slot D xs alignment.length_eq) alignment.exactSlots ?_ (vertexRows_of_code D width matrix)
  intro c
  exact catalogue.at_mem (List.getElem_mem ..)

end Papers.RationalityTen.ResidualBatch.TupleSharing
