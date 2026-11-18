module
prelude
public import RawNatGrowthCheck
public import PrimitiveBitsetGrowth
public import FastGraphConditionedGrowth

@[expose] public section

/-!
# Natural-number replay, with an exact semantic interpretation

The executable records contain no `Fin` literals or proof fields.  This file
proves that their checks imply the previously justified growth checker whenever
the raw tables agree with the interpreted finite tables.  The agreement is an
explicit premise here; concrete applications must prove it, including all
index bounds.  A successful evaluation of the raw predicate alone is not a
classification theorem.
-/

namespace Papers.RationalityTen.RawNatGrowthSoundness

open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming ConcreteGrowth
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth

variable {n r g k t : Nat}

def eraseClosed (w : ClosedWitness n r) : RawBatchGrowth.Closed :=
  ⟨w.ridge.val, w.first.val, w.second.val⟩

def eraseChild (c : Child n g t) : RawBatchGrowth.Child :=
  ⟨c.cell.val, c.node.val, c.frame.val⟩

def eraseAction : Action n r g k t → RawBatchGrowth.Action
  | .terminal j => .terminal j.val
  | .split q a closed children =>
      .split q.val a.val (closed.map eraseClosed) (children.map eraseChild)

def eraseNode (node : Node n r g k t) : RawBatchGrowth.Node :=
  ⟨node.cells.map Fin.val, node.mask, eraseAction node.action⟩

theorem union_map (f : β → Nat) (u : α → β) (xs : List α) :
    RawNatGrowthCheck.union f (xs.map u) = unionValues (fun x => f (u x)) xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      simp only [List.map_cons, RawNatGrowthCheck.union, unionValues,
        List.foldr_cons] at *
      exact congrArg (Nat.lor (f (u a))) ih

theorem union_eq (f : α → Nat) (xs : List α) :
    RawNatGrowthCheck.union f xs = unionValues f xs := by
  simpa only [List.map_id, id_eq] using union_map f id xs

theorem mask_map (xs : List (Fin n)) :
    RawNatGrowthCheck.mask (xs.map Fin.val) = PrimitiveBitsetGrowth.mask xs := by
  exact union_map (Nat.shiftLeft 1) Fin.val xs

theorem increasing_map (xs : List (Fin n)) :
    RawNatGrowthCheck.increasing (xs.map Fin.val) =
      FastGraphConditionedGrowth.ascending xs := by
  have aux (lower : Fin n) (ys : List (Fin n)) :
      RawNatGrowthCheck.increasing (lower.val :: ys.map Fin.val) =
        FastGraphConditionedGrowth.ascendingFrom lower.val ys := by
    induction ys generalizing lower with
    | nil => rfl
    | cons a ys ih =>
        simp only [List.map_cons, RawNatGrowthCheck.increasing,
          FastGraphConditionedGrowth.ascendingFrom, ih]
  cases xs with
  | nil => rfl
  | cons a xs => exact aux a xs

theorem kindCount_map (rawKind : Nat → Nat) (kind : Fin n → Nat)
    (hkind : ∀ c, rawKind c.val = kind c) (xs : List (Fin n)) (j : Nat) :
    RawNatGrowthCheck.kindCount rawKind (xs.map Fin.val) j = kindCount kind xs j := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      simp only [RawNatGrowthCheck.kindCount, kindCount, List.map_cons,
        List.filter_cons, hkind] at *
      split <;> simp_all only [List.length_cons]

theorem closedCheck_erase (candidates : Nat → Nat)
    {ridgeList : Fin n → List (Fin r)}
    {compatible : Fin n → Fin n → Bool} {kind : Fin n → Nat}
    (cache : Cache ridgeList compatible kind)
    (hcandidates : ∀ q, candidates q.val = cache.candidates q)
    (selected : Nat) (w : ClosedWitness n r) :
    RawNatGrowthCheck.closedCheck candidates selected (eraseClosed w) =
      PrimitiveBitsetGrowth.closedCheck cache selected w := by
  have hne : (w.first.val ≠ w.second.val) ↔ (w.first ≠ w.second) := by
    exact not_congr Fin.val_inj
  simp only [RawNatGrowthCheck.closedCheck, PrimitiveBitsetGrowth.closedCheck,
    eraseClosed, hcandidates, hne]

theorem blockedMask_erase (candidates bad rawKind : Nat → Nat)
    {ridgeList : Fin n → List (Fin r)}
    {compatible : Fin n → Fin n → Bool} {kind : Fin n → Nat}
    (cache : Cache ridgeList compatible kind) (quota : Nat → Nat)
    (hcandidates : ∀ q, candidates q.val = cache.candidates q)
    (hbad : ∀ c, bad c.val = cache.incompatible c)
    (hkind : ∀ c, rawKind c.val = kind c)
    (xs : List (Fin n)) (selected : Nat) (closed : List (ClosedWitness n r)) :
    RawNatGrowthCheck.blockedMask candidates bad cache.kinds cache.keys rawKind quota
      (xs.map Fin.val) selected (closed.map eraseClosed) =
      blockedMask cache quota xs selected closed := by
  have hquota (j : Nat) :
      (if quota j = 0 then cache.kinds j
       else if quota j ≤ RawNatGrowthCheck.kindCount rawKind (xs.map Fin.val) j
         then cache.kinds j else 0) =
      (if quota j ≤ kindCount kind xs j then cache.kinds j else 0) := by
    rw [kindCount_map rawKind kind hkind]
    by_cases hz : quota j = 0
    · simp only [hz, Nat.zero_le, ite_true]
    · simp only [hz, ite_false]
  rw [RawNatGrowthCheck.blockedMask, blockedMask, quotaMask,
    union_map, union_map, union_eq]
  simp only [eraseClosed, hcandidates, hbad, hquota]

theorem childCheck_erase (maps : Nat → Nat → Nat)
    (rawNodes : Nat → RawBatchGrowth.Node)
    (nodes : Fin t → Node n r g k t)
    (renamingMaps : Fin g → Fin n → Fin n)
    (hmaps : ∀ f c, maps f.val c.val = (renamingMaps f c).val)
    (hnodes : ∀ i, rawNodes i.val = eraseNode (nodes i))
    (i : Fin t) (link : Child n g t) :
    RawNatGrowthCheck.childCheck maps rawNodes i.val (eraseChild link) =
      (decide (link.node.val < i.val) &&
        decide ((nodes link.node).mask = PrimitiveBitsetGrowth.mask
          ((link.cell :: (nodes i).cells).map (renamingMaps link.frame)))) := by
  have hmap :
      (link.cell.val :: (nodes i).cells.map Fin.val).map (maps link.frame.val) =
        (((link.cell :: (nodes i).cells).map (renamingMaps link.frame)).map Fin.val) := by
    simp only [← List.map_cons, List.map_map, Function.comp_def, hmaps]
  simp only [RawNatGrowthCheck.childCheck, eraseChild, hnodes, eraseNode, hmap,
    mask_map]
  rfl

theorem mask_child_cells (children : List (Child n g t)) :
    RawNatGrowthCheck.mask ((children.map eraseChild).map RawBatchGrowth.Child.cell) =
      PrimitiveBitsetGrowth.mask (children.map Child.cell) := by
  simpa only [List.map_map, Function.comp_def, eraseChild] using
    mask_map (children.map Child.cell)

/-- The interpreted node checker is justified by a raw check only after every
table lookup has been identified with its bounded semantic counterpart. -/
theorem nodeCheck_sound (candidates bad rawKind : Nat → Nat)
    (maps : Nat → Nat → Nat) (rawLeaves : Nat → List Nat)
    (rawNodes : Nat → RawBatchGrowth.Node)
    {ridgeList : Fin n → List (Fin r)}
    {compatible : Fin n → Fin n → Bool} {kind : Fin n → Nat}
    (cache : Cache ridgeList compatible kind) (quota : Nat → Nat)
    (renamings : Fin g → Renaming (fun c => has (ridgeList c)) compatible kind)
    (leaves : Fin k → List (Fin n)) (nodes : Fin t → Node n r g k t)
    (hcandidates : ∀ q, candidates q.val = cache.candidates q)
    (hbad : ∀ c, bad c.val = cache.incompatible c)
    (hkind : ∀ c, rawKind c.val = kind c)
    (hmaps : ∀ f c, maps f.val c.val = ((renamings f).cells.forward c).val)
    (hleaves : ∀ j, rawLeaves j.val = (leaves j).map Fin.val)
    (hnodes : ∀ i, rawNodes i.val = eraseNode (nodes i))
    (i : Fin t)
    (h : RawNatGrowthCheck.nodeCheck candidates bad cache.kinds cache.keys
      rawKind quota maps rawLeaves rawNodes i.val = true) :
    PrimitiveBitsetGrowth.nodeCheck cache quota renamings leaves nodes i = true := by
  have heq : RawNatGrowthCheck.nodeCheck candidates bad cache.kinds cache.keys
      rawKind quota maps rawLeaves rawNodes i.val =
      ((FastGraphConditionedGrowth.ascending (nodes i).cells &&
        decide ((nodes i).mask = PrimitiveBitsetGrowth.mask (nodes i).cells)) &&
        PrimitiveBitsetGrowth.nodeBody cache quota renamings leaves nodes i) := by
    cases ha : (nodes i).action with
    | terminal j =>
        simp only [RawNatGrowthCheck.nodeCheck, hnodes i, eraseNode, ha,
          eraseAction, increasing_map, mask_map, hleaves,
          PrimitiveBitsetGrowth.nodeBody]
    | split q a closed children =>
        simp only [RawNatGrowthCheck.nodeCheck, hnodes i, eraseNode, ha,
          eraseAction, increasing_map, mask_map, hcandidates,
          List.all_map, Function.comp_def,
          closedCheck_erase candidates cache hcandidates,
          childCheck_erase maps rawNodes nodes
            (fun f => (renamings f).cells.forward) hmaps hnodes,
          blockedMask_erase candidates bad rawKind cache quota hcandidates hbad hkind,
          mask_child_cells, PrimitiveBitsetGrowth.nodeBody,
          PrimitiveBitsetGrowth.singleton]
        rfl
  rw [heq] at h
  obtain ⟨hstate, hbody⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hordered, hmask⟩ := Bool.and_eq_true_iff.mp hstate
  exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
    ⟨decide_eq_true (FastGraphConditionedGrowth.ascending_nodup _ hordered), hmask⟩,
      hbody⟩

def listBounds (bound : Nat) (xs : List Nat) : Bool :=
  xs.all (fun a => decide (a < bound))

def closedBounds (n r : Nat) (w : RawBatchGrowth.Closed) : Bool :=
  (decide (w.ridge < r) && decide (w.first < n)) && decide (w.second < n)

def childBounds (n g t : Nat) (c : RawBatchGrowth.Child) : Bool :=
  (decide (c.cell < n) && decide (c.node < t)) && decide (c.frame < g)

def actionBounds (n r g k t : Nat) : RawBatchGrowth.Action → Bool
  | .terminal j => decide (j < k)
  | .split q a closed children =>
      ((decide (q < r) && decide (a < n)) && closed.all (closedBounds n r)) &&
        children.all (childBounds n g t)

def nodeBounds (n r g k t : Nat) (node : RawBatchGrowth.Node) : Bool :=
  listBounds n node.cells && actionBounds n r g k t node.action

theorem val_decode_list [NeZero n] (xs : List Nat) (h : listBounds n xs = true) :
    (xs.map (Fin.ofNat n)).map Fin.val = xs := by
  rw [List.map_map]
  have hm : (xs.map (fun a => (Fin.ofNat n a).val)) = xs.map id := by
    apply List.map_congr_left
    intro a ha
    exact Nat.mod_eq_of_lt (of_decide_eq_true (List.all_eq_true.mp h a ha))
  simpa only [List.map_id, Function.comp_def] using hm

theorem erase_decode_closed [NeZero n] [NeZero r] (w : RawBatchGrowth.Closed)
    (h : closedBounds n r w = true) :
    eraseClosed (RawBatchGrowth.decodeClosed (n := n) (r := r) w) = w := by
  obtain ⟨hfirst, hsecond⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hridge, hfirst⟩ := Bool.and_eq_true_iff.mp hfirst
  have hridge := Nat.mod_eq_of_lt (of_decide_eq_true hridge)
  have hfirst := Nat.mod_eq_of_lt (of_decide_eq_true hfirst)
  have hsecond := Nat.mod_eq_of_lt (of_decide_eq_true hsecond)
  cases w
  simp only [eraseClosed, RawBatchGrowth.decodeClosed, Fin.val_ofNat,
    hridge, hfirst, hsecond]

theorem erase_decode_child [NeZero n] [NeZero g] [NeZero t]
    (c : RawBatchGrowth.Child) (h : childBounds n g t c = true) :
    eraseChild (RawBatchGrowth.decodeChild (n := n) (g := g) (t := t) c) = c := by
  obtain ⟨hfirst, hframe⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hcell, hnode⟩ := Bool.and_eq_true_iff.mp hfirst
  have hcell := Nat.mod_eq_of_lt (of_decide_eq_true hcell)
  have hnode := Nat.mod_eq_of_lt (of_decide_eq_true hnode)
  have hframe := Nat.mod_eq_of_lt (of_decide_eq_true hframe)
  cases c
  simp only [eraseChild, RawBatchGrowth.decodeChild, Fin.val_ofNat,
    hcell, hnode, hframe]

theorem erase_decode_action [NeZero n] [NeZero r] [NeZero g] [NeZero k] [NeZero t]
    (a : RawBatchGrowth.Action) (h : actionBounds n r g k t a = true) :
    eraseAction (RawBatchGrowth.decodeAction (n := n) (r := r)
      (g := g) (k := k) (t := t) a) = a := by
  cases a with
  | terminal j =>
      have hj := Nat.mod_eq_of_lt (of_decide_eq_true h)
      simp only [RawBatchGrowth.decodeAction, eraseAction, Fin.val_ofNat, hj]
  | split q a closed children =>
      obtain ⟨hleft, hchildren⟩ := Bool.and_eq_true_iff.mp h
      obtain ⟨hqa, hclosed⟩ := Bool.and_eq_true_iff.mp hleft
      obtain ⟨hq, ha⟩ := Bool.and_eq_true_iff.mp hqa
      have hq := Nat.mod_eq_of_lt (of_decide_eq_true hq)
      have ha := Nat.mod_eq_of_lt (of_decide_eq_true ha)
      have hc : (closed.map (RawBatchGrowth.decodeClosed (n := n) (r := r))).map
          eraseClosed = closed := by
        rw [List.map_map]
        simpa only [List.map_id, Function.comp_def] using
          (List.map_congr_left (l := closed) (g := id) (fun w hw =>
            erase_decode_closed w (List.all_eq_true.mp hclosed w hw)))
      have hd : (children.map (RawBatchGrowth.decodeChild (n := n) (g := g)
          (t := t))).map eraseChild = children := by
        rw [List.map_map]
        simpa only [List.map_id, Function.comp_def] using
          (List.map_congr_left (l := children) (g := id) (fun c hc =>
            erase_decode_child c (List.all_eq_true.mp hchildren c hc)))
      simp only [RawBatchGrowth.decodeAction, eraseAction, Fin.val_ofNat, hq, ha,
        hc, hd]

/-- Decoding cannot silently wrap an out-of-range cell, ridge, frame, node, or
terminal index: every field is covered by the explicit executable bound check. -/
theorem erase_decode_node [NeZero n] [NeZero r] [NeZero g] [NeZero k] [NeZero t]
    (node : RawBatchGrowth.Node) (h : nodeBounds n r g k t node = true) :
    eraseNode (RawBatchGrowth.decodeNode (n := n) (r := r)
      (g := g) (k := k) (t := t) node) = node := by
  obtain ⟨hcells, haction⟩ := Bool.and_eq_true_iff.mp h
  have hc := val_decode_list node.cells hcells
  have ha := erase_decode_action node.action haction
  cases node
  simp only [RawBatchGrowth.decodeNode, eraseNode, hc, ha]

#print axioms nodeCheck_sound
#print axioms erase_decode_node

end Papers.RationalityTen.RawNatGrowthSoundness
