module
prelude
public import ConcreteGrowth

@[expose] public section

/-! Transparent packing of literal ten-label facet records. All geometric
coverage and record-validity facts are checked separately against the decoded
vertex mask, full edge list, and full ridge list. -/
namespace Papers.RationalityTen.PackedFacetCells

def take (width code : Nat) : Nat := Nat.land code (Nat.shiftLeft 1 width - 1)
def drop (width code : Nat) : Nat := Nat.shiftRight code width

def readMasks : Nat → Nat → List Nat × Nat
  | 0, code => ([], code)
  | count + 1, code =>
      let rest := readMasks count (drop 10 code)
      (take 10 code :: rest.1, rest.2)

def unpack (code : Nat) : ConcreteGrowth.Cell :=
  let kind := take 4 code
  let vertices := take 10 (drop 4 code)
  let countCode := drop 14 code
  let edges := readMasks (take 5 countCode) (drop 5 countCode)
  let ridges := readMasks (take 5 edges.2) (drop 5 edges.2)
  ⟨kind, vertices, edges.1, ridges.1⟩

end Papers.RationalityTen.PackedFacetCells
