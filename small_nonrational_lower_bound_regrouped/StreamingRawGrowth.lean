module
prelude
public import PackedRawNatGrowth
public import RawNatGrowthSoundness

@[expose] public section
set_option maxHeartbeats 200000

/-!
# Streaming checks for packed exhaustive-growth records

The checker consumes the packed fields directly.  Its correctness theorem is
an equality with the conjunction of the existing raw index-bound check and
the existing exhaustive node check.  It changes evaluation, not proof rules.
-/

namespace Papers.RationalityTen.StreamingRawGrowth

open RawBatchGrowth RawNatGrowthCheck RawNatGrowthSoundness PackedRawNatGrowth

def foldFields (width : Nat) (step : Nat → α → α) (base : α) :
    Nat → Nat → α
  | 0, _ => base
  | count + 1, code =>
      step (take width code) (foldFields width step base count (drop width code))

def foldClosed (width : Nat) (step : Closed → α → α) (base : α) :
    Nat → Nat → α
  | 0, _ => base
  | count + 1, code =>
      let ridge := take 10 code
      let firstCode := drop 10 code
      let first := take width firstCode
      let secondCode := drop width firstCode
      let second := take width secondCode
      step ⟨ridge, first, second⟩
        (foldClosed width step base count (drop width secondCode))

def foldChildren (widths : Widths) (step : Child → α → α) (base : α) :
    Nat → Nat → α
  | 0, _ => base
  | count + 1, code =>
      let cell := take widths.cell code
      let nodeCode := drop widths.cell code
      let node := take widths.node nodeCode
      let frameCode := drop widths.node nodeCode
      let frame := take widths.frame frameCode
      step ⟨cell, node, frame⟩
        (foldChildren widths step base count (drop widths.frame frameCode))

theorem foldFields_eq (width : Nat) (step : Nat → α → α) (base : α)
    (count code : Nat) :
    foldFields width step base count code =
      ((readList width count code).1).foldr step base := by
  induction count generalizing code with
  | zero => rfl
  | succ count ih =>
      simp only [foldFields, readList, List.foldr_cons, ih]

theorem readList_rest (width count code : Nat) :
    (readList width count code).2 = drop (width * count) code := by
  induction count generalizing code with
  | zero => rfl
  | succ count ih =>
      simp only [readList]
      rw [ih]
      change (code >>> width) >>> (width * count) = code >>> (width * (count + 1))
      rw [← Nat.shiftRight_add]
      congr 1
      simp only [Nat.mul_succ, Nat.add_comm]

theorem foldClosed_eq (width : Nat) (step : Closed → α → α) (base : α)
    (count code : Nat) :
    foldClosed width step base count code =
      ((readClosed width count code).1).foldr step base := by
  induction count generalizing code with
  | zero => rfl
  | succ count ih =>
      simp only [foldClosed, readClosed, List.foldr_cons, ih]

theorem readClosed_rest (width count code : Nat) :
    (readClosed width count code).2 =
      drop ((10 + width + width) * count) code := by
  induction count generalizing code with
  | zero => rfl
  | succ count ih =>
      simp only [readClosed]
      rw [ih]
      change (((code >>> 10) >>> width) >>> width) >>>
        ((10 + width + width) * count) =
          code >>> ((10 + width + width) * (count + 1))
      simp only [← Nat.shiftRight_add]
      congr 1
      simp only [Nat.mul_succ]
      omega

theorem foldChildren_eq (widths : Widths) (step : Child → α → α) (base : α)
    (count code : Nat) :
    foldChildren widths step base count code =
      (readChildren widths count code).foldr step base := by
  induction count generalizing code with
  | zero => rfl
  | succ count ih =>
      simp only [foldChildren, readChildren, List.foldr_cons, ih]

theorem foldr_union (value : α → Nat) (xs : List α) :
    xs.foldr (fun x rest => Nat.lor (value x) rest) 0 = union value xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.foldr_cons, union, ih]

theorem foldr_all (test : α → Bool) (xs : List α) :
    xs.foldr (fun x rest => test x && rest) true = xs.all test := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.foldr_cons, List.all_cons, ih]

theorem all_and (xs : List α) (left right : α → Bool) :
    xs.all (fun x => left x && right x) = (xs.all left && xs.all right) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.all_cons, ih, Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]

theorem union_map_raw (value : β → Nat) (f : α → β) (xs : List α) :
    union value (xs.map f) = union (fun x => value (f x)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, union, ih]

def fieldUnion (width : Nat) (value : Nat → Nat) (count code : Nat) : Nat :=
  foldFields width (fun x rest => Nat.lor (value x) rest) 0 count code

def fieldAll (width : Nat) (test : Nat → Bool) (count code : Nat) : Bool :=
  foldFields width (fun x rest => test x && rest) true count code

def fieldCount (width : Nat) (kind : Nat → Nat) (key count code : Nat) : Nat :=
  foldFields width (fun x rest => if kind x = key then rest + 1 else rest) 0 count code

def orderedFields (width : Nat) : Nat → Nat → Bool
  | 0, _ => true
  | 1, _ => true
  | count + 2, code =>
      decide (take width code < take width (drop width code)) &&
        orderedFields width (count + 1) (drop width code)

theorem fieldUnion_eq (width : Nat) (value : Nat → Nat) (count code : Nat) :
    fieldUnion width value count code = union value (readList width count code).1 := by
  rw [fieldUnion, foldFields_eq, foldr_union]

theorem fieldAll_eq (width : Nat) (test : Nat → Bool) (count code : Nat) :
    fieldAll width test count code = (readList width count code).1.all test := by
  rw [fieldAll, foldFields_eq, foldr_all]

theorem fieldCount_eq (width : Nat) (kind : Nat → Nat) (key count code : Nat) :
    fieldCount width kind key count code =
      kindCount kind (readList width count code).1 key := by
  induction count generalizing code with
  | zero => rfl
  | succ count ih =>
      by_cases h : kind (take width code) = key
      · simpa [fieldCount, foldFields, readList, kindCount, List.filter_cons, h]
          using congrArg Nat.succ (ih (drop width code))
      · simpa [fieldCount, foldFields, readList, kindCount, List.filter_cons, h]
          using ih (drop width code)

theorem orderedFields_eq (width count code : Nat) :
    orderedFields width count code = increasing (readList width count code).1 := by
  induction count generalizing code with
  | zero => rfl
  | succ count ih =>
      cases count with
      | zero => rfl
      | succ count =>
          simp only [orderedFields, readList, increasing] at *
          exact congrArg (fun b =>
            decide (take width code < take width (drop width code)) && b)
              (ih (drop width code))

def nodeMask (widths : Widths) (code : Nat) : Nat :=
  fieldUnion widths.cell (Nat.shiftLeft 1) (take 5 code) (drop 5 code)

theorem nodeMask_eq (widths : Widths) (code : Nat) :
    nodeMask widths code = (decodeNode widths code).mask := by
  simp only [nodeMask, fieldUnion_eq, PackedRawNatGrowth.decodeNode, mask]

theorem decoded_cells (widths : Widths) (code : Nat) :
    (PackedRawNatGrowth.decodeNode widths code).cells =
      (readList widths.cell (take 5 code) (drop 5 code)).1 := rfl

theorem decoded_mask (widths : Widths) (code : Nat) :
    (PackedRawNatGrowth.decodeNode widths code).mask =
      mask (readList widths.cell (take 5 code) (drop 5 code)).1 := rfl

theorem decoded_action (widths : Widths) (code : Nat) :
    (PackedRawNatGrowth.decodeNode widths code).action =
      PackedRawNatGrowth.decodeAction widths
        (readList widths.cell (take 5 code) (drop 5 code)).2 := rfl

def childCheckPacked (widths : Widths) (maps : Nat → Nat → Nat)
    (codes : Nat → Nat) (i : Nat) (child : Child) : Bool :=
  decide (child.node < i) &&
    decide (nodeMask widths (codes child.node) =
      Nat.lor (Nat.shiftLeft 1 (maps child.frame child.cell))
        (fieldUnion widths.cell (fun c => Nat.shiftLeft 1 (maps child.frame c))
          (take 5 (codes i)) (drop 5 (codes i))))

theorem childCheckPacked_eq (widths : Widths) (maps : Nat → Nat → Nat)
    (codes : Nat → Nat) (i : Nat) (child : Child) :
    childCheckPacked widths maps codes i child =
      childCheck maps (fun j => decodeNode widths (codes j)) i child := by
  simp only [childCheckPacked, childCheck, nodeMask_eq, fieldUnion_eq,
    PackedRawNatGrowth.decodeNode, List.map_cons, mask, union, union_map_raw]

def blockedPacked (width : Nat) (bad kindMasks : Nat → Nat)
    (keys : List Nat) (kind quota : Nat → Nat)
    (count code selected closedUnion : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.lor selected (fieldUnion width bad count code))
    (union (fun k => if quota k = 0 then kindMasks k
      else if quota k ≤ fieldCount width kind k count code then kindMasks k else 0) keys))
    closedUnion

theorem blockedPacked_eq (width : Nat) (candidates bad kindMasks : Nat → Nat)
    (keys : List Nat) (kind quota : Nat → Nat)
    (count code selected : Nat) (closed : List Closed) :
    blockedPacked width bad kindMasks keys kind quota count code selected
      (union (fun w => candidates w.ridge) closed) =
        blockedMask candidates bad kindMasks keys kind quota
          (readList width count code).1 selected closed := by
  simp only [blockedPacked, blockedMask, fieldUnion_eq, fieldCount_eq]

def closedAll (width : Nat) (test : Closed → Bool) (count code : Nat) : Bool :=
  foldClosed width (fun w rest => test w && rest) true count code

def closedUnion (width : Nat) (value : Closed → Nat) (count code : Nat) : Nat :=
  foldClosed width (fun w rest => Nat.lor (value w) rest) 0 count code

def childrenAll (widths : Widths) (test : Child → Bool) (count code : Nat) : Bool :=
  foldChildren widths (fun c rest => test c && rest) true count code

def childrenUnion (widths : Widths) (value : Child → Nat) (count code : Nat) : Nat :=
  foldChildren widths (fun c rest => Nat.lor (value c) rest) 0 count code

theorem closedAll_eq (width : Nat) (test : Closed → Bool) (count code : Nat) :
    closedAll width test count code = (readClosed width count code).1.all test := by
  rw [closedAll, foldClosed_eq, foldr_all]

theorem closedUnion_eq (width : Nat) (value : Closed → Nat) (count code : Nat) :
    closedUnion width value count code = union value (readClosed width count code).1 := by
  rw [closedUnion, foldClosed_eq, foldr_union]

theorem childrenAll_eq (widths : Widths) (test : Child → Bool) (count code : Nat) :
    childrenAll widths test count code = (readChildren widths count code).all test := by
  rw [childrenAll, foldChildren_eq, foldr_all]

theorem childrenUnion_eq (widths : Widths) (value : Child → Nat) (count code : Nat) :
    childrenUnion widths value count code = union value (readChildren widths count code) := by
  rw [childrenUnion, foldChildren_eq, foldr_union]

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
        nodeCheck candidates bad kindMasks keys kind quota maps leaves
          (fun j => decodeNode widths (codes j)) i) := by
  cases widths
  simp only [check, nodeBounds, actionBounds, nodeCheck,
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
      nodeCheck candidates bad kindMasks keys kind quota maps leaves
        (fun j => decodeNode widths (codes j)) i = true :=
  Bool.and_eq_true_iff.mp ((check_eq widths n r g k t candidates bad kindMasks keys
    kind quota maps leaves codes i) ▸ h)

#print axioms check_eq
#print axioms check_sound

end Papers.RationalityTen.StreamingRawGrowth

