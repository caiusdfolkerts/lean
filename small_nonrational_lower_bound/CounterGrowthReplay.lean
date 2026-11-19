module
prelude
public import StreamingRawGrowth
public import NoCarryKindDigits
public import Init.Data.Nat.Bitwise.Lemmas

@[expose] public section
set_option maxHeartbeats 200000

/-!
# Exact cached quota counts

The selected list has at most 31 entries.  Its kind counts therefore fit in
the digits of a base-32 integer without carries.  A literal counter is checked
against the sum of these powers before it is used.

Only exhausted kinds enter the filtered key list.  Passing zero quotas for
those keys makes the existing streaming predicate include their masks directly,
without rescanning the selected cells.  The proof below identifies the result
with the original predicate and its original quotas; no target hypothesis is
changed.
-/

namespace Papers.RationalityTen.CounterGrowthReplay

open RawBatchGrowth RawNatGrowthCheck RawNatGrowthSoundness
open PackedRawNatGrowth StreamingRawGrowth

def packedCounts (width : Nat) (kind : Nat → Nat) (count code : Nat) : Nat :=
  foldFields width (fun c rest => 32 ^ kind c + rest) 0 count code

def nodeCounts (widths : Widths) (kind : Nat → Nat) (code : Nat) : Nat :=
  packedCounts widths.cell kind (take 5 code) (drop 5 code)

def digit (counter key : Nat) : Nat := (counter / 32 ^ key) % 32

def exhaustedKeys (keys : List Nat) (quota : Nat → Nat) (counter : Nat) : List Nat :=
  keys.filter (fun key => decide (quota key ≤ digit counter key))

theorem packedCounts_eq (width : Nat) (kind : Nat → Nat) (count code : Nat) :
    packedCounts width kind count code =
      ((readList width count code).1.map (fun c => 32 ^ kind c)).sum := by
  induction count generalizing code with
  | zero => rfl
  | succ count ih =>
      simp only [packedCounts, foldFields, readList, List.map_cons, List.sum_cons] at *
      rw [ih]

theorem readList_length (width count code : Nat) :
    (readList width count code).1.length = count := by
  induction count generalizing code with
  | zero => rfl
  | succ count ih => simp only [readList, List.length_cons, ih]

theorem selected_length_lt (widths : Widths) (code : Nat) :
    (PackedRawNatGrowth.decodeNode widths code).cells.length < 32 := by
  rw [decoded_cells, readList_length]
  change (code &&& (2 ^ 5 - 1)) < 2 ^ 5
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by decide)

theorem node_digit_eq (widths : Widths) (kind : Nat → Nat)
    (code counter : Nat) (hcounter : counter = nodeCounts widths kind code) (key : Nat) :
    digit counter key = kindCount kind (PackedRawNatGrowth.decodeNode widths code).cells key := by
  rw [hcounter]
  change ((packedCounts widths.cell kind (take 5 code) (drop 5 code)) / 32 ^ key) % 32 = _
  rw [packedCounts_eq]
  exact NoCarryKindDigits.digit_eq_count 32 (by decide) kind
    (PackedRawNatGrowth.decodeNode widths code).cells (selected_length_lt widths code) key

theorem exhausted_union (kindMasks kind quota : Nat → Nat)
    (keys selected : List Nat) :
    union (fun key => if quota key = 0 then kindMasks key
      else if quota key ≤ kindCount kind selected key then kindMasks key else 0) keys =
      union kindMasks (keys.filter (fun key => decide (quota key ≤ kindCount kind selected key))) := by
  induction keys with
  | nil => rfl
  | cons key keys ih =>
      by_cases hz : quota key = 0
      · simp [union, List.filter_cons, hz, ih]
      · by_cases h : quota key ≤ kindCount kind selected key
        · simp [union, List.filter_cons, hz, h, ih]
        · simp [union, List.filter_cons, hz, h, ih]

theorem filtered_blocked_eq (candidates bad kindMasks kind quota : Nat → Nat)
    (keys selected : List Nat) (selectedMask : Nat) (closed : List Closed) :
    blockedMask candidates bad kindMasks
      (keys.filter (fun key => decide (quota key ≤ kindCount kind selected key)))
        kind (fun _ => 0) selected selectedMask closed =
      blockedMask candidates bad kindMasks keys kind quota selected selectedMask closed := by
  simp only [blockedMask, ↓reduceIte]
  rw [← exhausted_union kindMasks kind quota keys selected]

theorem filtered_node_eq (candidates bad kindMasks kind quota : Nat → Nat)
    (keys : List Nat) (maps : Nat → Nat → Nat) (leaves : Nat → List Nat)
    (nodes : Nat → Node) (i : Nat) :
    nodeCheck candidates bad kindMasks
      (keys.filter (fun key => decide (quota key ≤ kindCount kind (nodes i).cells key)))
        kind (fun _ => 0) maps leaves nodes i =
      nodeCheck candidates bad kindMasks keys kind quota maps leaves nodes i := by
  cases h : (nodes i).action with
  | terminal entry => simp only [nodeCheck, h]
  | split ridge owner closed children =>
      simp only [nodeCheck, h, filtered_blocked_eq]

def check (widths : Widths) (n r g k t : Nat)
    (candidates bad kindMasks : Nat → Nat) (keys : List Nat)
    (kind quota : Nat → Nat) (maps : Nat → Nat → Nat)
    (leaves : Nat → List Nat) (codes counters : Nat → Nat) (i : Nat) : Bool :=
  decide (counters i = nodeCounts widths kind (codes i)) &&
    StreamingRawGrowth.check widths n r g k t candidates bad kindMasks
      (exhaustedKeys keys quota (counters i)) kind (fun _ => 0) maps leaves codes i

theorem check_sound (widths : Widths) (n r g k t : Nat)
    (candidates bad kindMasks : Nat → Nat) (keys : List Nat)
    (kind quota : Nat → Nat) (maps : Nat → Nat → Nat)
    (leaves : Nat → List Nat) (codes counters : Nat → Nat) (i : Nat)
    (h : check widths n r g k t candidates bad kindMasks keys kind quota
      maps leaves codes counters i = true) :
    nodeBounds n r g k t (PackedRawNatGrowth.decodeNode widths (codes i)) = true ∧
      nodeCheck candidates bad kindMasks keys kind quota maps leaves
        (fun j => PackedRawNatGrowth.decodeNode widths (codes j)) i = true := by
  obtain ⟨hcounter, hstream⟩ := Bool.and_eq_true_iff.mp h
  have hdigits := node_digit_eq widths kind (codes i) (counters i) (of_decide_eq_true hcounter)
  have hkeys : exhaustedKeys keys quota (counters i) =
      keys.filter (fun key => decide
        (quota key ≤ kindCount kind (PackedRawNatGrowth.decodeNode widths (codes i)).cells key)) := by
    apply List.filter_congr
    intro key _
    rw [hdigits key]
  have checked := StreamingRawGrowth.check_sound widths n r g k t
    candidates bad kindMasks (exhaustedKeys keys quota (counters i)) kind (fun _ => 0)
    maps leaves codes i hstream
  refine ⟨checked.1, ?_⟩
  rw [hkeys] at checked
  exact (filtered_node_eq candidates bad kindMasks kind quota keys maps leaves
    (fun j => PackedRawNatGrowth.decodeNode widths (codes j)) i) ▸ checked.2

#print axioms check_sound

end Papers.RationalityTen.CounterGrowthReplay
