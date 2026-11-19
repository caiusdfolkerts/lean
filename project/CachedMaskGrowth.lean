module
prelude
public import CounterGrowthReplay

@[expose] public section
set_option maxHeartbeats 200000

/-!
# Exact cached selected masks for exhaustive growth

Each literal selected mask is independently checked against its packed cell
list. Child checks then reuse that equality instead of repeatedly decoding
and unioning the child list. Frame zero is required to be the identity; all
other frames retain the full checked map of every selected cell.
-/

namespace Papers.RationalityTen.CachedMaskGrowth

open RawBatchGrowth RawNatGrowthCheck RawNatGrowthSoundness
open PackedRawNatGrowth StreamingRawGrowth CounterGrowthReplay

def childCheck (widths : Widths) (maps : Nat → Nat → Nat)
    (codes masks : Nat → Nat) (i : Nat) (child : Child) : Bool :=
  decide (child.node < i) &&
    decide (masks child.node =
      if child.frame = 0 then Nat.lor (Nat.shiftLeft 1 child.cell) (masks i)
      else Nat.lor (Nat.shiftLeft 1 (maps child.frame child.cell))
        (fieldUnion widths.cell (fun c => Nat.shiftLeft 1 (maps child.frame c))
          (take 5 (codes i)) (drop 5 (codes i))))

theorem childCheck_eq (widths : Widths) (maps : Nat → Nat → Nat)
    (codes masks : Nat → Nat) (identity : ∀ c, maps 0 c = c)
    (exactMasks : ∀ i, masks i = nodeMask widths (codes i))
    (i : Nat) (child : Child) :
    childCheck widths maps codes masks i child =
      childCheckPacked widths maps codes i child := by
  by_cases hz : child.frame = 0
  · simp only [childCheck, childCheckPacked, hz, eq_self, ite_true, identity,
      exactMasks, nodeMask]
  · simp only [childCheck, childCheckPacked, hz, ite_false, exactMasks]

def check (widths : Widths) (n r g k t : Nat)
    (candidates bad kindMasks : Nat → Nat) (keys : List Nat)
    (kind quota : Nat → Nat) (maps : Nat → Nat → Nat)
    (leaves : Nat → List Nat) (codes masks : Nat → Nat) (i : Nat) : Bool :=
  let code := codes i
  let count := take 5 code
  let selectedCode := drop 5 code
  let selected := masks i
  let actionCode := drop (widths.cell * count) selectedCode
  let tag := take 1 actionCode
  let rest := drop 1 actionCode
  (fieldAll widths.cell (fun c => decide (c < n)) count selectedCode &&
    orderedFields widths.cell count selectedCode) &&
  if tag = 0 then
    let leaf := take widths.leaf rest
    decide (leaf < k) && decide (selected = mask (leaves leaf))
  else
    let ridge := take 10 rest
    let ownerCode := drop 10 rest
    let owner := take widths.cell ownerCode
    let countCode := drop widths.cell ownerCode
    let closedCount := take 8 countCode
    let closedCode := drop 8 countCode
    let childrenStart := drop ((10 + widths.cell + widths.cell) * closedCount) closedCode
    let childrenCount := take 16 childrenStart
    let childrenCode := drop 16 childrenStart
    (((decide (ridge < r) && decide (owner < n)) &&
      closedAll widths.cell (fun w =>
        closedBounds n r w && closedCheck candidates selected w) closedCount closedCode) &&
      childrenAll widths (fun child =>
        childBounds n g t child && childCheck widths maps codes masks i child)
          childrenCount childrenCode) &&
    (decide (Nat.land selected (candidates ridge) = Nat.shiftLeft 1 owner) &&
      decide (Nat.land (candidates ridge)
        (Nat.lor (blockedPacked widths.cell bad kindMasks keys kind quota
          count selectedCode selected
          (closedUnion widths.cell (fun w => candidates w.ridge) closedCount closedCode))
          (childrenUnion widths (fun child => Nat.shiftLeft 1 child.cell)
            childrenCount childrenCode)) = candidates ridge))


theorem check_eq (widths : Widths) (n r g k t : Nat)
    (candidates bad kindMasks : Nat → Nat) (keys : List Nat)
    (kind quota : Nat → Nat) (maps : Nat → Nat → Nat)
    (leaves : Nat → List Nat) (codes masks : Nat → Nat)
    (identity : ∀ c, maps 0 c = c)
    (exactMasks : ∀ i, masks i = nodeMask widths (codes i)) (i : Nat) :
    check widths n r g k t candidates bad kindMasks keys kind quota
      maps leaves codes masks i =
    StreamingRawGrowth.check widths n r g k t candidates bad kindMasks keys kind quota
      maps leaves codes i := by
  simp only [check, StreamingRawGrowth.check, exactMasks,
    childCheck_eq widths maps codes masks identity exactMasks]

def countedCheck (widths : Widths) (n r g k t : Nat)
    (candidates bad kindMasks : Nat → Nat) (keys : List Nat)
    (kind quota : Nat → Nat) (maps : Nat → Nat → Nat)
    (leaves : Nat → List Nat) (codes counters masks : Nat → Nat) (i : Nat) : Bool :=
  decide (counters i = nodeCounts widths kind (codes i)) &&
    check widths n r g k t candidates bad kindMasks
      (exhaustedKeys keys quota (counters i)) kind (fun _ => 0)
      maps leaves codes masks i

theorem countedCheck_sound (widths : Widths) (n r g k t : Nat)
    (candidates bad kindMasks : Nat → Nat) (keys : List Nat)
    (kind quota : Nat → Nat) (maps : Nat → Nat → Nat)
    (leaves : Nat → List Nat) (codes counters masks : Nat → Nat)
    (identity : ∀ c, maps 0 c = c)
    (exactMasks : ∀ i, masks i = nodeMask widths (codes i)) (i : Nat)
    (checked : countedCheck widths n r g k t candidates bad kindMasks keys kind quota
      maps leaves codes counters masks i = true) :
    nodeBounds n r g k t (decodeNode widths (codes i)) = true ∧
      nodeCheck candidates bad kindMasks keys kind quota maps leaves
        (fun j => decodeNode widths (codes j)) i = true := by
  have equivalent : countedCheck widths n r g k t candidates bad kindMasks keys kind quota
      maps leaves codes counters masks i =
      CounterGrowthReplay.check widths n r g k t candidates bad kindMasks keys kind quota
        maps leaves codes counters i := by
    simp only [countedCheck, CounterGrowthReplay.check,
      check_eq widths n r g k t candidates bad kindMasks
        (exhaustedKeys keys quota (counters i)) kind (fun _ => 0)
        maps leaves codes masks identity exactMasks i]
  exact CounterGrowthReplay.check_sound widths n r g k t candidates bad kindMasks
    keys kind quota maps leaves codes counters i (equivalent ▸ checked)

#print axioms countedCheck_sound
end Papers.RationalityTen.CachedMaskGrowth
