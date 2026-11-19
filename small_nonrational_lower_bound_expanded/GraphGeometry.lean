module

public meta import GraphNumerals

/-! A RawData record uses the same finite cells in its vertex rows, ridge
matrix and edge/missing-edge matrices. Reconstruct those numerical fields
from the pool indexed by the record's original embedding. -/
public meta section
open Lean Elab Term
namespace GraphNumerals

structure PoolCell where
  cell : Nat
  faces : Nat
  edgeList : Nat
  missingList : Nat
  edges : Nat
  missing : Nat
  deriving Inhabited

def readPool (v : Array Nat) : Option (Std.HashMap Nat PoolCell) := do
  guard (v.size % 7 == 0)
  let mut pool := {}
  for j in [:v.size/7] do
    let i := 7*j
    pool := pool.insert v[i]! ⟨v[i+1]!, v[i+2]!, v[i+3]!, v[i+4]!, v[i+5]!, v[i+6]!⟩
  return pool

private def part (n width : Nat) : Nat := n &&& ((1 <<< width) - 1)

private def unpack (code width count : Nat) : Array Nat := Id.run do
  let mut rest := code
  let mut result := #[]
  for _ in [:count] do
    result := result.push (part rest width)
    rest := rest >>> width
  return result

private def pack (values : Array Nat) (width : Nat) : Nat :=
  values.foldr (fun x acc => (acc <<< width) ||| x) 0

private def shortList (code width : Nat) : Array Nat :=
  unpack (code >>> 16) width (part code 16)

private def ridges (c : PoolCell) : Array Nat :=
  let edgeCount := part (c.cell >>> 15) 5
  let header := c.cell >>> (20 + 10 * edgeCount)
  unpack (header >>> 5) 10 (part header 5)

private def incidence (cells : Array PoolCell) (column : PoolCell → Array Nat) : Nat := Id.run do
  let mut result := 0
  for j in [:cells.size] do
    for feature in column cells[j]! do
      result := result ||| (1 <<< (cells.size * feature + j))
  return result

private def mask (items : Array Nat) : Nat :=
  items.foldl (fun bits i => bits ||| (1 <<< i)) 0

/-- Positions in the flattened public RawData constructor. For each original
Fields value, its width precedes its code. -/
private def omitted : Array Nat :=
  #[12, 14, 15, 19, 23, 25, 27, 28, 30, 32, 33, 35]

def expandGeometry (independent : Array Nat) (pool : Std.HashMap Nat PoolCell) :
    Option (Array Nat) := do
  guard (independent.size + omitted.size == 58)
  let mut numbers := #[]
  let mut sourceIndex := 0
  for i in [:58] do
    if omitted.contains i then numbers := numbers.push 0
    else
      numbers := numbers.push independent[sourceIndex]!
      sourceIndex := sourceIndex + 1
  let count := numbers[0]! + 1
  let nKinds := numbers[4]! + 1
  let cellWidth := numbers[5]!
  let ids := unpack numbers[44]! numbers[43]! count
  let cells ← ids.mapM (fun i => pool[i]?)
  numbers := numbers.set! 12 (pack (cells.map PoolCell.cell) numbers[11]!)
  numbers := numbers.set! 14 (pack (cells.map PoolCell.faces) numbers[13]!)
  numbers := numbers.set! 25 (pack (cells.map PoolCell.edgeList) numbers[24]!)
  numbers := numbers.set! 27 (pack (cells.map PoolCell.edges) numbers[26]!)
  numbers := numbers.set! 30 (pack (cells.map PoolCell.missingList) numbers[29]!)
  numbers := numbers.set! 32 (pack (cells.map PoolCell.missing) numbers[31]!)
  numbers := numbers.set! 15 (incidence cells ridges)
  numbers := numbers.set! 28 (incidence cells (fun c => shortList c.edgeList 6))
  numbers := numbers.set! 33 (incidence cells (fun c => shortList c.missingList 6))
  numbers := numbers.set! 35 (incidence cells (fun c =>
    (Array.range 10).filter (fun i => (c.cell >>> 5).testBit i)))
  for (source, target, n) in #[(16, 18, count), (20, 22, nKinds)] do
    let codes := unpack numbers[source+1]! numbers[source]! n
    let masks := codes.map (fun code => mask (shortList code cellWidth))
    numbers := numbers.set! (target+1) (pack masks numbers[target]!)
  return numbers

elab "compactGraphRecord% " pool:str record:str : term => do
  let some entries := readPool (← expandNumerals pool.getString) | throwError "invalid cell pool"
  let some full := expandGeometry (← expandNumerals record.getString) entries |
    throwError "invalid geometric certificate"
  mkRecord full

end GraphNumerals
