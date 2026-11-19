module
prelude
public import SubsumedGrowth

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SubsumedStreaming
open RawBatchGrowth RawNatGrowthCheck RawNatGrowthSoundness
open PackedRawNatGrowth StreamingRawGrowth

theorem readList_nonempty (width count code : Nat) :
    (readList width count code).1 ≠ [] ↔ count ≠ 0 := by
  cases count <;> simp [readList]

def childCheckPacked (widths : Widths) (maps : Nat → Nat → Nat)
    (codes : Nat → Nat) (i : Nat) (child : Child) : Bool :=
  decide (child.node < i) &&
    (decide (Nat.land (nodeMask widths (codes child.node))
      (Nat.lor (Nat.shiftLeft 1 (maps child.frame child.cell))
        (fieldUnion widths.cell (fun c => Nat.shiftLeft 1 (maps child.frame c))
          (take 5 (codes i)) (drop 5 (codes i)))) = nodeMask widths (codes child.node)) &&
      decide (take 5 (codes child.node) ≠ 0))

theorem childCheckPacked_eq (widths : Widths) (maps : Nat → Nat → Nat)
    (codes : Nat → Nat) (i : Nat) (child : Child) :
    childCheckPacked widths maps codes i child =
      SubsumedRawGrowth.childCheck maps (fun j => decodeNode widths (codes j)) i child := by
  simp only [childCheckPacked, SubsumedRawGrowth.childCheck, nodeMask_eq, fieldUnion_eq,
    PackedRawNatGrowth.decodeNode, List.map_cons, mask, union, union_map_raw,
    readList_nonempty]

def check (widths : Widths) (n r g k t : Nat)
    (candidates bad kindMasks : Nat → Nat) (keys : List Nat)
    (kind quota : Nat → Nat) (maps : Nat → Nat → Nat)
    (leaves : Nat → List Nat) (codes : Nat → Nat) (i : Nat) : Bool :=
  let code := codes i
  let count := take 5 code
  let selectedCode := drop 5 code
  let selected := nodeMask widths code
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
        childBounds n g t child && childCheckPacked widths maps codes i child)
          childrenCount childrenCode) &&
    (decide (Nat.land selected (candidates ridge) = Nat.shiftLeft 1 owner) &&
      decide (Nat.land (candidates ridge)
        (Nat.lor (blockedPacked widths.cell bad kindMasks keys kind quota
          count selectedCode selected
          (closedUnion widths.cell (fun w => candidates w.ridge) closedCount closedCode))
          (childrenUnion widths (fun child => Nat.shiftLeft 1 child.cell)
            childrenCount childrenCode)) = candidates ridge))

theorem terminal_rearrange (s o l e : Bool) :
    ((s && o) && (l && e)) = ((s && l) && (o && e)) := by
  simp only [Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]

theorem split_rearrange (s o q a cb cc db dc p c : Bool) :
    ((s && o) && ((((q && a) && (cb && cc)) && (db && dc)) && (p && c))) =
      ((s && (((q && a) && cb) && db)) && (o && (((p && cc) && dc) && c))) := by
  simp only [Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]

set_option diagnostics true in
theorem check_eq (widths : Widths) (n r g k t : Nat)
    (candidates bad kindMasks : Nat → Nat) (keys : List Nat)
    (kind quota : Nat → Nat) (maps : Nat → Nat → Nat)
    (leaves : Nat → List Nat) (codes : Nat → Nat) (i : Nat) :
    check widths n r g k t candidates bad kindMasks keys kind quota maps leaves codes i =
      (nodeBounds n r g k t (decodeNode widths (codes i)) &&
        SubsumedRawGrowth.nodeCheck candidates bad kindMasks keys kind quota maps leaves
          (fun j => decodeNode widths (codes j)) i) := by
  cases widths
  simp only [check, nodeBounds, actionBounds, SubsumedRawGrowth.nodeCheck,
    decoded_cells, decoded_mask, decoded_action, PackedRawNatGrowth.decodeAction,
    fieldAll_eq, orderedFields_eq, nodeMask, fieldUnion_eq, readList_rest,
    closedAll_eq, closedUnion_eq, childrenAll_eq, childrenUnion_eq,
    childCheckPacked_eq, readClosed_rest, all_and, blockedPacked_eq,
    listBounds, mask, union_map_raw]
  split <;> simp_all only [Bool.and_true, eq_self, decide_true]
  · exact terminal_rearrange _ _ _ _
  · exact split_rearrange _ _ _ _ _ _ _ _ _ _

theorem check_sound (widths : Widths) (n r g k t : Nat)
    (candidates bad kindMasks : Nat → Nat) (keys : List Nat)
    (kind quota : Nat → Nat) (maps : Nat → Nat → Nat)
    (leaves : Nat → List Nat) (codes : Nat → Nat) (i : Nat)
    (h : check widths n r g k t candidates bad kindMasks keys kind quota maps leaves codes i = true) :
    nodeBounds n r g k t (decodeNode widths (codes i)) = true ∧
      SubsumedRawGrowth.nodeCheck candidates bad kindMasks keys kind quota maps leaves
        (fun j => decodeNode widths (codes j)) i = true :=
  Bool.and_eq_true_iff.mp ((check_eq widths n r g k t candidates bad kindMasks keys
    kind quota maps leaves codes i) ▸ h)


#print axioms check_sound
end Papers.RationalityTen.SubsumedStreaming
namespace Papers.RationalityTen.SubsumedCounterReplay
open RawBatchGrowth RawNatGrowthCheck RawNatGrowthSoundness
open PackedRawNatGrowth StreamingRawGrowth CounterGrowthReplay

theorem filtered_node_eq (candidates bad kindMasks kind quota : Nat → Nat)
    (keys : List Nat) (maps : Nat → Nat → Nat) (leaves : Nat → List Nat)
    (nodes : Nat → Node) (i : Nat) :
    SubsumedRawGrowth.nodeCheck candidates bad kindMasks
      (keys.filter (fun key => decide (quota key ≤ kindCount kind (nodes i).cells key)))
        kind (fun _ => 0) maps leaves nodes i =
      SubsumedRawGrowth.nodeCheck candidates bad kindMasks keys kind quota maps leaves nodes i := by
  cases h : (nodes i).action with
  | terminal entry => simp only [SubsumedRawGrowth.nodeCheck, h]
  | split ridge owner closed children =>
      simp only [SubsumedRawGrowth.nodeCheck, h, filtered_blocked_eq]

def check (widths : Widths) (n r g k t : Nat)
    (candidates bad kindMasks : Nat → Nat) (keys : List Nat)
    (kind quota : Nat → Nat) (maps : Nat → Nat → Nat)
    (leaves : Nat → List Nat) (codes counters : Nat → Nat) (i : Nat) : Bool :=
  decide (counters i = nodeCounts widths kind (codes i)) &&
    SubsumedStreaming.check widths n r g k t candidates bad kindMasks
      (exhaustedKeys keys quota (counters i)) kind (fun _ => 0) maps leaves codes i

theorem check_sound (widths : Widths) (n r g k t : Nat)
    (candidates bad kindMasks : Nat → Nat) (keys : List Nat)
    (kind quota : Nat → Nat) (maps : Nat → Nat → Nat)
    (leaves : Nat → List Nat) (codes counters : Nat → Nat) (i : Nat)
    (h : check widths n r g k t candidates bad kindMasks keys kind quota
      maps leaves codes counters i = true) :
    nodeBounds n r g k t (PackedRawNatGrowth.decodeNode widths (codes i)) = true ∧
      SubsumedRawGrowth.nodeCheck candidates bad kindMasks keys kind quota maps leaves
        (fun j => PackedRawNatGrowth.decodeNode widths (codes j)) i = true := by
  obtain ⟨hcounter, hstream⟩ := Bool.and_eq_true_iff.mp h
  have hdigits := node_digit_eq widths kind (codes i) (counters i) (of_decide_eq_true hcounter)
  have hkeys : exhaustedKeys keys quota (counters i) =
      keys.filter (fun key => decide
        (quota key ≤ kindCount kind (PackedRawNatGrowth.decodeNode widths (codes i)).cells key)) := by
    apply List.filter_congr
    intro key _
    rw [hdigits key]
  have checked := SubsumedStreaming.check_sound widths n r g k t
    candidates bad kindMasks (exhaustedKeys keys quota (counters i)) kind (fun _ => 0)
    maps leaves codes i hstream
  refine ⟨checked.1, ?_⟩
  rw [hkeys] at checked
  exact (filtered_node_eq candidates bad kindMasks kind quota keys maps leaves
    (fun j => PackedRawNatGrowth.decodeNode widths (codes j)) i) ▸ checked.2


#print axioms check_sound
end Papers.RationalityTen.SubsumedCounterReplay
