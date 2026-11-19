module
prelude
public import RawFacetEmbedding

@[expose] public section

/-!
# Compressed rooted facet placements

A common face is placed first in both label orders. Its labels are permuted
inside the common face, and all other local vertices are injected into the
vertices outside the root. The semantic module proves that this smaller
domain contains every compatible geometric embedding.
-/

namespace Papers.RationalityTen.RawFacePlacement

open ConcreteGrowth

def count : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => (n + 1) * count n k

def digit (packed index : Nat) : Nat := (packed / 16 ^ index) % 16

structure Block where
  shared : Nat
  outside : Nat
  sourceForward : Nat
  sourceInverse : Nat
  targetForward : Nat
  targetInverse : Nat

def label (size : Nat) (B : Block) (inner outer i : Nat) : Nat :=
  let j := digit B.sourceInverse i
  digit B.targetForward
    (if j < B.shared then RawFacetEmbedding.decode B.shared B.shared inner j
      else B.shared + RawFacetEmbedding.decode B.outside (size - B.shared) outer
        (j - B.shared))

/-- Edge order is irrelevant to geometric compatibility. This set-membership
test permits the unsorted edge list produced by a literal relabeling. -/
def compatible (left right : Cell) : Bool :=
  let common := Nat.land left.vertices right.vertices
  (proper left common && proper right common) &&
    RawFacetEmbedding.sameMembers
      (left.edges.filter fun e => decide (Nat.land e common = e))
      (right.edges.filter fun e => decide (Nat.land e common = e))

def check {n : Nat} (size : Nat) (B : Block) (template root : Cell)
    (cells : Fin n → Cell) (inner outer : Nat) (witness : Fin n) : Bool :=
  let placed := RawFacetEmbedding.mapCell size (label size B inner outer) template
  (!compatible placed root) || RawFacetEmbedding.sameGeometry (cells witness) placed

def intervalCheck {n : Nat} (size : Nat) (B : Block) (template root : Cell)
    (cells : Fin n → Cell) (witness : Nat → Fin n) (code : Nat) : Bool :=
  let width := count B.outside (size - B.shared)
  check size B template root cells (code / width) (code % width) (witness code)

end Papers.RationalityTen.RawFacePlacement
