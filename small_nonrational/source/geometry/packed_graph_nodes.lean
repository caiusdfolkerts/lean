module
prelude
public import FastGraphConditionedGrowth
public import PackedRawNatGrowth

@[expose] public section

/-!
# Compact literal graph-search nodes

This is a representation of finite data, not an additional search rule.
Every decoded node is subsequently checked by the existing sound checker.
The selected mask is a separate argument so a child-mask lookup need not
decode the child's lists. All indexes are ordinary finite values.
-/

namespace Papers.RationalityTen.PackedGraphNodes

open GraphConditionedGrowth GraphGrowthConstraints BatchedGrowthPruning
open UnsupportedRidgePruning PackedRawNatGrowth

variable {n g l t : Nat} [NeZero n] [NeZero g] [NeZero l] [NeZero t]

def finiteList (n width count code : Nat) [NeZero n] : List (Fin n) :=
  ((readList width count code).1).map (Fin.ofNat n)

def closedList (width : Nat) : Nat → Nat → List (ClosedWitness n 1024)
  | 0, _ => []
  | count + 1, code =>
      ⟨Fin.ofNat 1024 (take 10 code),
       Fin.ofNat n (take width (drop 10 code)),
       Fin.ofNat n (take width (drop (10 + width) code))⟩ ::
      closedList width count (drop (10 + 2 * width) code)

def removalList (width : Nat) : Nat → Nat → List (Removal n 1024)
  | 0, _ => []
  | count + 1, code =>
      ⟨Fin.ofNat n (take width code),
       Fin.ofNat 1024 (take 10 (drop width code))⟩ ::
      removalList width count (drop (width + 10) code)

def childList (cellWidth nodeWidth frameWidth : Nat) :
    Nat → Nat → List (Child n g t)
  | 0, _ => []
  | count + 1, code =>
      ⟨Fin.ofNat n (take cellWidth code),
       Fin.ofNat t (take nodeWidth (drop cellWidth code)),
       Fin.ofNat g (take frameWidth (drop (cellWidth + nodeWidth) code))⟩ ::
      childList cellWidth nodeWidth frameWidth count
        (drop (cellWidth + nodeWidth + frameWidth) code)

def action (k cellWidth nodeWidth frameWidth leafWidth possible code : Nat)
    [NeZero k] : Action n 1024 45 10 k g l t :=
  let tag := take 3 code
  let payload := drop 3 code
  if tag = 0 then .terminal (Fin.ofNat l (take leafWidth payload))
  else
    let kind := tag - 1
    let argument := take 10 payload
    let owner := take cellWidth (drop 10 payload)
    let childrenCode := drop (10 + cellWidth) payload
    let children := childList cellWidth nodeWidth frameWidth
      (take 16 childrenCode) (drop 16 childrenCode)
    let rule : Rule 1024 45 10 k :=
      if kind = 0 then .ridge (Fin.ofNat 1024 argument) owner
      else if kind = 1 then .edge (Fin.ofNat 45 argument)
      else if kind = 2 then .nonedge (Fin.ofNat 45 argument) possible
      else if kind = 3 then .kindCapacity (Fin.ofNat k argument)
      else .vertexCapacity (Fin.ofNat 10 argument)
    .split rule children

def decode (k cellWidth nodeWidth frameWidth leafWidth possible code mask : Nat)
    [NeZero k] : Node n 1024 45 10 k g l t :=
  let selectedCount := take 5 code
  let selectedCode := drop 5 code
  let availabilityCode := drop (cellWidth * selectedCount) selectedCode
  let closedCode := drop n availabilityCode
  let closedCount := take 8 closedCode
  let closedFields := drop 8 closedCode
  let removalsCode := drop ((10 + 2 * cellWidth) * closedCount) closedFields
  let removalCount := take 16 removalsCode
  let removalFields := drop 16 removalsCode
  let actionCode := drop ((cellWidth + 10) * removalCount) removalFields
  { cells := finiteList n cellWidth selectedCount selectedCode
    mask := mask
    available := take n availabilityCode
    closed := closedList cellWidth closedCount closedFields
    removals := removalList cellWidth removalCount removalFields
    action := action k cellWidth nodeWidth frameWidth leafWidth possible actionCode }

end Papers.RationalityTen.PackedGraphNodes
