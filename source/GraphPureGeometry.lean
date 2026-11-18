module

/-! Object-language decoding of the twelve redundant numerical fields.
The original RawData metadata, nodes, selected cell embeddings, geometric
frames and terminal predicates all consume the resulting record. -/
@[expose] public section

namespace GraphPureGeometry

structure Cell where
  cell : Nat
  faces : Nat
  edgeList : Nat
  missingList : Nat
  edges : Nat
  missing : Nat

def part (n width : Nat) : Nat := n &&& ((1 <<< width) - 1)

def unpack (code width : Nat) : Nat → List Nat
  | 0 => []
  | n + 1 => part code width :: unpack (code >>> width) width n

def pack {α : Type} (field : α → Nat) (width : Nat) : List α → Nat
  | [] => 0
  | x :: xs => field x ||| (pack field width xs <<< width)

def shortList (code width : Nat) : List Nat :=
  unpack (code >>> 16) width (part code 16)

def Cell.ridges (c : Cell) : List Nat :=
  let edgeCount := part (c.cell >>> 15) 5
  let header := c.cell >>> (20 + 10 * edgeCount)
  unpack (header >>> 5) 10 (part header 5)

def Cell.edgeIndices (c : Cell) : List Nat := shortList c.edgeList 6
def Cell.missingIndices (c : Cell) : List Nat := shortList c.missingList 6
def Cell.vertexIndices (c : Cell) : List Nat :=
  (List.range 10).filter (fun i => (c.cell >>> 5).testBit i)

/-- Feature f of local cell j contributes bit stride * f + j. -/
def incidence (column : Cell → List Nat) (stride : Nat) (cells : List Cell) : Nat :=
  let (_, result) := cells.foldl (fun (state : Nat × Nat) c =>
    let j := state.1
    let bits := (column c).foldl (fun a f => a ||| (1 <<< (stride * f + j))) state.2
    (j+1, bits)) (0, 0)
  result

def packedMasks (source sourceWidth count cellWidth targetWidth : Nat) : Nat :=
  let mask := fun (code : Nat) => (shortList code cellWidth).foldl
    (fun bits i => bits ||| (1 <<< i)) 0
  pack mask targetWidth (unpack source sourceWidth count)

end GraphPureGeometry
