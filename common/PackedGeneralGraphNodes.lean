module
prelude
public import PackedGraphNodes

@[expose] public section

/-!
# Compact graph certificates with arbitrary missing-edge bounds

Each missing-edge rule retains its own certified upper bound.  In particular,
the number of missing edges of the whole graph need not equal the target
number of internal nonedges.  This file only decodes literal finite data;
the ordinary graph-search checker verifies every resulting node.
-/

namespace Papers.RationalityTen.PackedGeneralGraphNodes

open GraphConditionedGrowth GraphGrowthConstraints BatchedGrowthPruning
open UnsupportedRidgePruning PackedRawNatGrowth PackedGraphNodes

variable {n g l t : Nat} [NeZero n] [NeZero g] [NeZero l] [NeZero t]

def action (k cellWidth nodeWidth frameWidth leafWidth code : Nat)
    [NeZero k] : Action n 1024 45 10 k g l t :=
  let tag := take 3 code
  let payload := drop 3 code
  if tag = 0 then .terminal (Fin.ofNat l (take leafWidth payload))
  else
    let argument := take 10 payload
    let owner := take cellWidth (drop 10 payload)
    let possible := take 45 (drop (10 + cellWidth) payload)
    let childrenCode := drop (55 + cellWidth) payload
    let children := childList cellWidth nodeWidth frameWidth
      (take 16 childrenCode) (drop 16 childrenCode)
    let rule : Rule 1024 45 10 k :=
      if tag = 1 then .ridge (Fin.ofNat 1024 argument) owner
      else if tag = 2 then .edge (Fin.ofNat 45 argument)
      else if tag = 3 then .nonedge (Fin.ofNat 45 argument) possible
      else if tag = 4 then .kindCapacity (Fin.ofNat k argument)
      else if tag = 5 then .vertexCapacity (Fin.ofNat 10 argument)
      else .nonedgeCapacity possible
    .split rule children

def decode (k cellWidth nodeWidth frameWidth leafWidth code mask : Nat)
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
    action := action k cellWidth nodeWidth frameWidth leafWidth actionCode }

end Papers.RationalityTen.PackedGeneralGraphNodes
