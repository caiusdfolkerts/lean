module
prelude
public import RawNatGrowthCheck
public import ConcreteGrowth

@[expose] public section

/-!
# Bounded blocks of natural-number growth records

This is only a transparent data representation.  Every decoded node is passed
to the raw bound and completeness checks; neither the packing process nor its
input is trusted.  Blocks keep shifts local and selected masks are reconstructed
from their short lists, avoiding huge repeated mask literals.
-/

namespace Papers.RationalityTen.PackedRawNatGrowth

open RawBatchGrowth

structure Widths where
  cell : Nat
  node : Nat
  frame : Nat
  leaf : Nat

def take (width code : Nat) : Nat :=
  Nat.land code (Nat.shiftLeft 1 width - 1)

def drop (width code : Nat) : Nat := Nat.shiftRight code width

def readList (width : Nat) : Nat → Nat → List Nat × Nat
  | 0, code => ([], code)
  | count + 1, code =>
      let rest := readList width count (drop width code)
      (take width code :: rest.1, rest.2)

def readClosed (width : Nat) : Nat → Nat → List Closed × Nat
  | 0, code => ([], code)
  | count + 1, code =>
      let ridge := take 10 code
      let firstCode := drop 10 code
      let first := take width firstCode
      let secondCode := drop width firstCode
      let second := take width secondCode
      let rest := readClosed width count (drop width secondCode)
      (⟨ridge, first, second⟩ :: rest.1, rest.2)

def readChildren (widths : Widths) : Nat → Nat → List Child
  | 0, _ => []
  | count + 1, code =>
      let cell := take widths.cell code
      let nodeCode := drop widths.cell code
      let node := take widths.node nodeCode
      let frameCode := drop widths.node nodeCode
      let frame := take widths.frame frameCode
      ⟨cell, node, frame⟩ :: readChildren widths count (drop widths.frame frameCode)

def decodeAction (widths : Widths) (code : Nat) : Action :=
  let tag := take 1 code
  let rest := drop 1 code
  if tag = 0 then .terminal (take widths.leaf rest)
  else
    let ridge := take 10 rest
    let ownerCode := drop 10 rest
    let owner := take widths.cell ownerCode
    let countCode := drop widths.cell ownerCode
    let count := take 8 countCode
    let closed := readClosed widths.cell count (drop 8 countCode)
    let childCount := take 16 closed.2
    .split ridge owner closed.1 (readChildren widths childCount (drop 16 closed.2))

def decodeNode (widths : Widths) (code : Nat) : Node :=
  let count := take 5 code
  let selected := readList widths.cell count (drop 5 code)
  ⟨selected.1, RawNatGrowthCheck.mask selected.1, decodeAction widths selected.2⟩

structure Block where
  payload : Nat
  offsets : Nat

def Block.node (block : Block) (widths : Widths) (i : Nat) : Node :=
  let offset := take 32 (drop (32 * i) block.offsets)
  decodeNode widths (drop offset block.payload)

/-- The caller chooses a positive block size; any malformed choice or padding
is still subject to the ordinary decoded-node and bound checks. -/
def nodes (blocks : ConcreteGrowth.Table Block) (widths : Widths)
    (blockSize : Nat) (i : Nat) : Node :=
  (blocks.get (i / blockSize)).node widths (i % blockSize)

end Papers.RationalityTen.PackedRawNatGrowth
