module

public import GraphPureGeometry
public meta import GraphGeometry
public meta import CertificateNumbers

/-! The untrusted source reader can only build natural literals, shared cell
tuples and applications of the public pure decoder. Graph certificates are
accepted by the original proof predicates. -/
public meta section
open Lean Elab Term
namespace PureGeometricRecordFiles

open GraphNumerals CertificateNumbers

initialize cachedPools : IO.Ref (Std.HashMap String (Std.HashMap Nat PoolCell)) ← IO.mkRef {}

private def poolAt (filename : String) : TermElabM (Std.HashMap Nat PoolCell) := do
  let parent := (System.FilePath.mk (← getFileName)).parent.getD "."
  let p := parent/filename
  if let some pool := (← cachedPools.get)[p.toString]? then return pool
  let some pool := readPool (← load p) | throwError "invalid shared cell pool"
  cachedPools.modify (·.insert p.toString pool)
  return pool

private def cellExpr (c : PoolCell) : Expr :=
  mkAppN (mkConst ``GraphPureGeometry.Cell.mk)
    (#[c.cell, c.faces, c.edgeList, c.missingList, c.edges, c.missing].map mkNatLit)

private def packCells (proj : Name) (width cells : Expr) : Expr :=
  mkAppN (mkConst ``GraphPureGeometry.pack)
    #[mkConst ``GraphPureGeometry.Cell, mkConst proj, width, cells]

private def incidence (column : Name) (stride cells : Expr) : Expr :=
  mkApp3 (mkConst ``GraphPureGeometry.incidence) (mkConst column) stride cells

private def recordAt (poolName : String) (i : Nat) : TermElabM Expr := do
  let data ← load (← sibling "gpack")
  unless (i + 1) * 46 ≤ data.size do throwError "record index out of range"
  let fields := data.extract (i*46) ((i+1)*46)
  let absent := #[12, 14, 15, 19, 23, 25, 27, 28, 30, 32, 33, 35]
  let mut full : Array Nat := #[]
  let mut j := 0
  for k in [:58] do
    if absent.contains k then full := full.push 0
    else
      full := full.push fields[j]!
      j := j + 1
  let count := full[0]! + 1
  let kinds := full[4]! + 1
  let width := full[43]!
  let pool ← poolAt poolName
  let mut tuples := #[]
  for k in [:count] do
    let idx := (full[44]! >>> (width*k)) &&& ((1 <<< width) - 1)
    let some cell := pool[idx]? | throwError "unknown public catalogue cell {idx}"
    tuples := tuples.push (cellExpr cell)
  let cells ← Meta.mkListLit (mkConst ``GraphPureGeometry.Cell) tuples.toList
  let n := mkNatLit count
  let mut values := full.map mkNatLit
  for (k, proj) in #[(12, ``GraphPureGeometry.Cell.cell), (14, ``GraphPureGeometry.Cell.faces),
      (25, ``GraphPureGeometry.Cell.edgeList), (27, ``GraphPureGeometry.Cell.edges),
      (30, ``GraphPureGeometry.Cell.missingList), (32, ``GraphPureGeometry.Cell.missing)] do
    values := values.set! k (packCells proj values[k-1]! cells)
  for (k, col) in #[(15, ``GraphPureGeometry.Cell.ridges), (28, ``GraphPureGeometry.Cell.edgeIndices),
      (33, ``GraphPureGeometry.Cell.missingIndices), (35, ``GraphPureGeometry.Cell.vertexIndices)] do
    values := values.set! k (incidence col n cells)
  for (s, t, arity) in #[(16, 19, count), (20, 23, kinds)] do
    values := values.set! t (mkAppN (mkConst ``GraphPureGeometry.packedMasks)
      #[values[s+1]!, values[s]!, mkNatLit arity, values[5]!, values[t-1]!])
  let ns := `Papers.RationalityTen.PackedGraphCertificate
  let ctor := ns ++ `RawData.mk
  let fieldsTy := ns ++ `Fields
  let info ← getConstInfo ctor
  Meta.forallTelescope info.type fun args _ => do
    let mut out := #[]
    let mut next := 0
    for arg in args do
      let ty ← Meta.inferType arg
      if ty.isConstOf ``Nat then
        out := out.push values[next]!
        next := next + 1
      else if ty.isConstOf fieldsTy then
        out := out.push (mkApp2 (mkConst (fieldsTy ++ `mk)) values[next]! values[next+1]!)
        next := next + 2
      else throwError "unexpected RawData constructor argument"
    unless next == values.size do throwError "unused record fields"
    return mkAppN (mkConst ctor) out

elab "pureSmallRecord% " n:num : term => recordAt "SmallFacetCells.gpool" n.getNat
elab "pureSixRecord% " n:num : term => recordAt "SixFacetCells.gpool" n.getNat

end PureGeometricRecordFiles
