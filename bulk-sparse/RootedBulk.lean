module
prelude
public import SubsumedStreaming
public import FiniteChecks
public import RawGrowthCacheCertificate

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.RootedBulk

open RawBatchGrowth RawNatGrowthCheck RawNatGrowthSoundness
open PackedRawNatGrowth StreamingRawGrowth CounterGrowthReplay FiniteChecks

theorem testBit_mask_mem (cells : List Nat) (index : Nat) :
    (mask cells).testBit index = true ↔ index ∈ cells := by
  rw [RawGrowthCacheCertificate.mask_bit, RawGrowthCacheCertificate.hasNat_true]

theorem mask_land_eq_iff (child extension : List Nat) :
    Nat.land (mask child) (mask extension) = mask child ↔
      ∀ c ∈ child, c ∈ extension := by
  constructor
  · intro h index hm
    have hc := (testBit_mask_mem child index).mpr hm
    have hb := congrArg (fun n : Nat => n.testBit index) h
    rw [Nat.testBit_and, hc, Bool.true_and] at hb
    exact (testBit_mask_mem extension index).mp hb
  · intro h
    apply Nat.eq_of_testBit_eq
    intro index
    rw [Nat.testBit_and]
    cases hc : (mask child).testBit index with
    | false => rfl
    | true =>
        have he := (testBit_mask_mem extension index).mpr
          (h index ((testBit_mask_mem child index).mp hc))
        rw [he]

/-- Compare short cell lists directly. The decoded child must be nonempty and
each of its cells must occur in the renamed extension. -/
def sparseChild (widths : Widths) (maps : Nat → Nat → Nat) (codes : Nat → Nat)
    (parent : List Nat) (i : Nat) (child : Child) : Bool :=
  decide (child.node < i) &&
    let code := codes child.node
    let count := take 5 code
    let selected := (readList widths.cell count (drop 5 code)).1
    let extension := maps child.frame child.cell :: parent.map (maps child.frame)
    (decide (count ≠ 0) &&
      selected.all (RawGrowthCacheCertificate.hasNat extension))

theorem sparseSubset_iff (selected extension : List Nat) :
    (selected.all (RawGrowthCacheCertificate.hasNat extension)) = true ↔
      Nat.land (mask selected) (mask extension) = mask selected := by
  simp only [List.all_eq_true, RawGrowthCacheCertificate.hasNat_true, mask_land_eq_iff]

theorem sparseChild_eq (widths : Widths) (maps : Nat → Nat → Nat)
    (codes : Nat → Nat) (i : Nat) (child : Child) :
    sparseChild widths maps codes (decodeNode widths (codes i)).cells i child =
      SubsumedStreaming.childCheckPacked widths maps codes i child := by
  rw [SubsumedStreaming.childCheckPacked_eq]
  let count := take 5 (codes child.node)
  let selected := (readList widths.cell count (drop 5 (codes child.node))).1
  let extension := (child.cell :: (decodeNode widths (codes i)).cells).map (maps child.frame)
  change (decide (child.node < i) &&
    (decide (count ≠ 0) && selected.all (RawGrowthCacheCertificate.hasNat extension))) =
    (decide (child.node < i) &&
      (decide (Nat.land (mask selected) (mask extension) = mask selected) &&
        decide (selected ≠ [])))
  have hs : (selected.all (RawGrowthCacheCertificate.hasNat extension)) =
      decide (Nat.land (mask selected) (mask extension) = mask selected) := by
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq]
    exact sparseSubset_iff selected extension
  have hn : decide (selected ≠ []) = decide (count ≠ 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact SubsumedStreaming.readList_nonempty _ _ _
  rw [hs, hn, Bool.and_comm (decide (count ≠ 0))]

/-- The existing streaming checks with the child test supplied separately. -/
def checkWithChild (widths : Widths) (n r g k t : Nat)
    (candidates bad kindMasks : Nat → Nat) (keys : List Nat)
    (kind quota : Nat → Nat) (leaves : Nat → List Nat) (code : Nat)
    (childTest : Child → Bool) : Bool :=
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
        childBounds n g t child && childTest child) childrenCount childrenCode) &&
    (decide (Nat.land selected (candidates ridge) = Nat.shiftLeft 1 owner) &&
      decide (Nat.land (candidates ridge)
        (Nat.lor (blockedPacked widths.cell bad kindMasks keys kind quota
          count selectedCode selected
          (closedUnion widths.cell (fun w => candidates w.ridge) closedCount closedCode))
          (childrenUnion widths (fun child => Nat.shiftLeft 1 child.cell)
            childrenCount childrenCode)) = candidates ridge))

def checkNode (widths : Widths) (n r g k t : Nat)
    (candidates bad kindMasks : Nat → Nat) (keys : List Nat)
    (kind quota : Nat → Nat) (maps : Nat → Nat → Nat)
    (leaves : Nat → List Nat) (codes counters : Nat → Nat) (i : Nat) : Bool :=
  let code := codes i
  decide (counters i = nodeCounts widths kind code) &&
    checkWithChild widths n r g k t candidates bad kindMasks
      (exhaustedKeys keys quota (counters i)) kind (fun _ => 0) leaves code
      (sparseChild widths maps codes (decodeNode widths code).cells i)

theorem checkNode_eq (widths : Widths) (n r g k t : Nat)
    (candidates bad kindMasks : Nat → Nat) (keys : List Nat)
    (kind quota : Nat → Nat) (maps : Nat → Nat → Nat)
    (leaves : Nat → List Nat) (codes counters : Nat → Nat) (i : Nat) :
    checkNode widths n r g k t candidates bad kindMasks keys kind quota
      maps leaves codes counters i =
    SubsumedCounterReplay.check widths n r g k t candidates bad kindMasks keys kind quota
      maps leaves codes counters i := by
  simp only [checkNode, SubsumedCounterReplay.check, checkWithChild,
    SubsumedStreaming.check, sparseChild_eq]

/-- Check a concrete range by kernel evaluation. The shared proof restores the
original node test, so downstream classification proofs import the same intervals. -/
theorem interval (widths : Widths) (n r g k t : Nat)
    (candidates bad kindMasks : Nat → Nat) (keys : List Nat)
    (kind quota : Nat → Nat) (maps : Nat → Nat → Nat)
    (leaves : Nat → List Nat) (codes counters : Nat → Nat) (start count : Nat)
    (h : checkRange (checkNode widths n r g k t candidates bad kindMasks keys kind quota
      maps leaves codes counters) start count = true) :
    Interval (SubsumedCounterReplay.check widths n r g k t candidates bad kindMasks
      keys kind quota maps leaves codes counters) start (start + count) := by
  intro i hlo hhi
  rw [← checkNode_eq]
  exact checkRange_sound _ _ _ h i hlo hhi

end Papers.RationalityTen.RootedBulk
