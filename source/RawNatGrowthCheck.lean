module
prelude
public import RawBatchGrowth

@[expose] public section

/-! Natural-number evaluation layer.  This file only defines an executable
predicate; its semantic lowering theorem is supplied separately. -/

namespace Papers.RationalityTen.RawNatGrowthCheck

open RawBatchGrowth

def union (value : α → Nat) : List α → Nat
  | [] => 0
  | a :: rest => Nat.lor (value a) (union value rest)

def mask (cells : List Nat) : Nat := union (Nat.shiftLeft 1) cells

def increasing : List Nat → Bool
  | [] | [_] => true
  | a :: b :: rest => decide (a < b) && increasing (b :: rest)

def closedCheck (candidates : Nat → Nat) (selected : Nat) (w : Closed) : Bool :=
  ((decide (w.first ≠ w.second) && selected.testBit w.first) &&
      selected.testBit w.second) &&
    ((candidates w.ridge).testBit w.first && (candidates w.ridge).testBit w.second)

def kindCount (kind : Nat → Nat) (S : List Nat) (k : Nat) : Nat :=
  (S.filter fun c => decide (kind c = k)).length

def blockedMask (candidates bad kindMasks : Nat → Nat) (keys : List Nat)
    (kind quota : Nat → Nat) (S : List Nat) (selected : Nat) (closed : List Closed) : Nat :=
  Nat.lor (Nat.lor (Nat.lor selected (union bad S))
    (union (fun k => if quota k = 0 then kindMasks k
       else if quota k ≤ kindCount kind S k then kindMasks k else 0) keys))
    (union (fun w => candidates w.ridge) closed)

def childCheck (cellMap : Nat → Nat → Nat) (nodes : Nat → Node)
    (i : Nat) (link : Child) : Bool :=
  decide (link.node < i) &&
    decide ((nodes link.node).mask = mask ((link.cell :: (nodes i).cells).map (cellMap link.frame)))

def nodeCheck (candidates bad kindMasks : Nat → Nat) (keys : List Nat)
    (kind quota : Nat → Nat) (cellMap : Nat → Nat → Nat)
    (leaves : Nat → List Nat) (nodes : Nat → Node) (i : Nat) : Bool :=
  ((increasing (nodes i).cells && decide ((nodes i).mask = mask (nodes i).cells)) &&
    match (nodes i).action with
    | .terminal j => decide ((nodes i).mask = mask (leaves j))
    | .split q a closed children =>
        ((decide (Nat.land (nodes i).mask (candidates q) = Nat.shiftLeft 1 a) &&
          closed.all (closedCheck candidates (nodes i).mask)) &&
          children.all (childCheck cellMap nodes i)) &&
        decide (Nat.land (candidates q)
          (Nat.lor (blockedMask candidates bad kindMasks keys kind quota
            (nodes i).cells (nodes i).mask closed)
              (mask (children.map Child.cell))) = candidates q))

end Papers.RationalityTen.RawNatGrowthCheck
