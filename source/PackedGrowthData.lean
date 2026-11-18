module
prelude
public import ConcreteGrowth

@[expose] public section

/-!
# Compact natural-number storage for literal certificates

Every field occupies one base-65536 digit. Lists start with their length.
This is only a transparent data representation: unpacking is a total Lean
function, and the mathematical checker is applied to the unpacked records.
No hash, external parser, native evaluation, or asserted parsing correctness
enters a proof. The accompanying JSON and generator retain readable data.
-/

namespace Papers.RationalityTen.ConcreteGrowth

def unpackMany : Nat → Nat → List Nat × Nat
  | 0, code => ([], code)
  | count + 1, code =>
      let tail := unpackMany count (code / 65536)
      (code % 65536 :: tail.1, tail.2)

def unpackList (code : Nat) : List Nat × Nat :=
  unpackMany (code % 65536) (code / 65536)

def unpackCell (code : Nat) : Cell :=
  let kind := code % 65536
  let vertices := (code / 65536) % 65536
  let edges := unpackList (code / 4294967296)
  let ridges := unpackList edges.2
  ⟨kind, vertices, edges.1, ridges.1⟩

def unpackChoice (tag payload : Nat) : RawChoice :=
  if tag = 4 then .child payload
  else if tag = 3 then .rejected (.closedRidge payload)
  else if tag = 2 then .rejected (.incompatible payload)
  else if tag = 1 then .rejected .quota
  else .rejected .selected

def unpackRecords : Nat → Nat → List (Nat × RawChoice)
  | 0, _ => []
  | count + 1, code =>
      (code % 65536, unpackChoice ((code / 65536) % 65536)
        ((code / 4294967296) % 65536)) ::
        unpackRecords count (code / 281474976710656)

def unpackNode (code : Nat) : RawNode :=
  let selected := unpackList code
  let body := selected.2 / 65536
  let action :=
    if selected.2 % 65536 = 0 then .terminal (body % 65536)
    else .split (body % 65536) ((body / 65536) % 65536)
      (unpackRecords ((body / 4294967296) % 65536) (body / 281474976710656))
  ⟨selected.1, action⟩

end Papers.RationalityTen.ConcreteGrowth
