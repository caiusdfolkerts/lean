module
public import Init

@[expose] public section

/-! Exact ten-vertex boundary targets. Producer output carries no proof authority;
the separate semantic bridges certify every target by ordinary Lean proofs. -/
namespace Nonrational.TerminalData

structure RawBoundary where
  facets : List Nat
  polygons : List Nat
  deriving DecidableEq, Inhabited, Repr

inductive TargetTree where
  | leaf (value : RawBoundary)
  | branch (leftSize : Nat) (left right : TargetTree)

noncomputable def TargetTree.get : TargetTree → Nat → RawBoundary
  | .leaf value, _ => value
  | .branch k left right, i => if i < k then left.get i else right.get (i-k)

end Nonrational.TerminalData
