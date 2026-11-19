module
prelude
public import RawNatGrowthCompleteness
public import CounterGrowthReplay

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-!
# Growth certificates with nonempty subset children

A child may retain a smaller nonempty subfamily of the renamed extension.
Strictly decreasing node indices still justify induction. The resulting
closed-leaf classification has exactly the same target hypotheses and
conclusion as the full-state certificate.
-/
namespace Papers.RationalityTen.SubsumedGrowth
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming ConcreteGrowth
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
variable {n r g k t : Nat}

theorem included_of_masks (S T : List (Fin n))
    (h : Nat.land (ofList S) (ofList T) = ofList S) : Included (family S) (family T) := by
  intro c hc
  have hs : bitAt (ofList S) c.val = true := (bitAt_ofList S c).mpr ((has_true S c).mp hc)
  have ht := congrArg (fun x => bitAt x c.val) h
  rw [bitAt_and, hs, Bool.true_and] at ht
  exact (has_true T c).mpr ((bitAt_ofList T c).mp ht)

theorem nonempty_of_ne_nil (S : List (Fin n)) (h : S ≠ []) : Nonempty (family S) := by
  cases S with
  | nil => exact False.elim (h rfl)
  | cons c rest => exact ⟨c, (has_true (c::rest) c).mpr List.mem_cons_self⟩

def childCheck {ridgeList : Fin n → List (Fin r)}
    {compatible : Fin n → Fin n → Bool} {kind : Fin n → Nat}
    (renamings : Fin g → Renaming (fun c => has (ridgeList c)) compatible kind)
    (nodes : Fin t → Node n r g k t) (i : Fin t) (link : Child n g t) : Bool :=
  decide (link.node.val < i.val) &&
    (decide (Nat.land (nodes link.node).mask
      (ofList ((link.cell :: (nodes i).cells).map (renamings link.frame).cells.forward)) =
        (nodes link.node).mask) && decide ((nodes link.node).cells ≠ []))

def nodeBody {ridgeList : Fin n → List (Fin r)}
    {compatible : Fin n → Fin n → Bool} {kind : Fin n → Nat}
    (cache : Cache ridgeList compatible kind) (quota : Nat → Nat)
    (renamings : Fin g → Renaming (fun c => has (ridgeList c)) compatible kind)
    (leaves : Fin k → List (Fin n)) (nodes : Fin t → Node n r g k t) (i : Fin t) : Bool :=
  match (nodes i).action with
  | .terminal j => decide ((nodes i).mask = ofList (leaves j))
  | .split q a closed children =>
      ((decide (Nat.land (nodes i).mask (cache.candidates q) = 2^a.val) &&
        closed.all (closedWitnessCheck cache (nodes i).mask)) &&
        children.all (childCheck renamings nodes i)) &&
      decide (Nat.land (cache.candidates q)
        (Nat.lor (blockedMask cache quota (nodes i).cells (nodes i).mask closed)
          (ofList (children.map Child.cell))) = cache.candidates q)

def nodeCheck {ridgeList : Fin n → List (Fin r)}
    {compatible : Fin n → Fin n → Bool} {kind : Fin n → Nat}
    (cache : Cache ridgeList compatible kind) (quota : Nat → Nat)
    (renamings : Fin g → Renaming (fun c => has (ridgeList c)) compatible kind)
    (leaves : Fin k → List (Fin n)) (nodes : Fin t → Node n r g k t) (i : Fin t) : Bool :=
  (decide (nodes i).cells.Nodup && decide ((nodes i).mask = ofList (nodes i).cells)) &&
    nodeBody cache quota renamings leaves nodes i

theorem complete_of_checks {ridgeList : Fin n → List (Fin r)}
    {compatible : Fin n → Fin n → Bool} {kind : Fin n → Nat}
    (cache : Cache ridgeList compatible kind) (quota : Nat → Nat)
    (renamings : Fin g → Renaming (fun c => has (ridgeList c)) compatible kind)
    (leaves : Fin k → List (Fin n)) (nodes : Fin t → Node n r g k t)
    (hnodes : ∀ i, nodeCheck cache quota renamings leaves nodes i = true)
    (B : List (Fin n))
    (hB : Target (fun c => has (ridgeList c)) compatible kind quota B)
    (root : Fin t) (hroot : Included (family (nodes root).cells) (family B))
    (hne : Nonempty (family (nodes root).cells)) :
    ∃ j word, Included (family (leaves j))
      (family (OrbitGrowthDAG.applyWord renamings word B)) ∧ Nonempty (family (leaves j)) := by
  have hmasks : ∀ i, (nodes i).mask = ofList (nodes i).cells := by
    intro i
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (hnodes i)).1).2
  have main : ∀ height : Nat, ∀ i : Fin t, i.val = height →
      ∀ B : List (Fin n), Target (fun c => has (ridgeList c)) compatible kind quota B →
      Included (family (nodes i).cells) (family B) → Nonempty (family (nodes i).cells) →
      ∃ j word, Included (family (leaves j))
        (family (OrbitGrowthDAG.applyWord renamings word B)) ∧ Nonempty (family (leaves j)) := by
    intro height
    induction height using Nat.strongRecOn with
    | ind height ih =>
      intro i hi B hB hsub hnonempty
      obtain ⟨hstate,hbody⟩ := Bool.and_eq_true_iff.mp (hnodes i)
      have hnd : (nodes i).cells.Nodup :=
        of_decide_eq_true (Bool.and_eq_true_iff.mp hstate).1
      cases ha : (nodes i).action with
      | terminal j =>
        have hmask : (nodes i).mask = ofList (leaves j) :=
          of_decide_eq_true (by simpa only [nodeBody,ha] using hbody)
        have hs := sameCheck_sound _ _
          (FastBatchedGrowth.sameCheck_of_masks _ _ ((hmasks i).symm.trans hmask))
        exact ⟨j,[],same_included (fun c => (hs c).symm) hsub,
          same_nonempty (fun c => (hs c).symm) hnonempty⟩
      | split q a closed children =>
        have hh :
            ((decide (Nat.land (nodes i).mask (cache.candidates q) = 2^a.val) &&
              closed.all (closedWitnessCheck cache (nodes i).mask)) &&
              children.all (childCheck renamings nodes i)) = true ∧
            decide (Nat.land (cache.candidates q)
              (Nat.lor (blockedMask cache quota (nodes i).cells (nodes i).mask closed)
                (ofList (children.map Child.cell))) = cache.candidates q) = true :=
          Bool.and_eq_true_iff.mp (by simpa only [nodeBody,ha] using hbody)
        obtain ⟨hopenClosed,hchildren⟩ := Bool.and_eq_true_iff.mp hh.1
        obtain ⟨hopen,hclosed⟩ := Bool.and_eq_true_iff.mp hopenClosed
        obtain ⟨c,hcB,hcS,hcr⟩ := missing_cell (fun c => has (ridgeList c))
          (family B) (family (nodes i).cells) q a hsub hB.mates
          (openCheck_sound _ _ _ _
            (FastBatchedGrowth.openCheck_of_mask cache (nodes i).cells (nodes i).mask
              (hmasks i) q a (of_decide_eq_true hopen)))
        change has (nodes i).cells c = false at hcS
        have hcand : bitAt (cache.candidates q) c.val = true :=
          (cache.candidates_exact q c).trans hcr
        have hblocked := blockedMask_sound cache quota (nodes i).cells B
          (nodes i).mask closed (hmasks i) hclosed hB hsub hnd c hcB hcS
        have hcChild := bitAt_cover _ _ _ c.val (of_decide_eq_true hh.2) hcand hblocked
        have hmem : c ∈ children.map Child.cell := (bitAt_ofList _ c).mp hcChild
        obtain ⟨link,hlinkMem,hcell⟩ := List.mem_map.mp hmem
        obtain ⟨hindex,hrest⟩ := Bool.and_eq_true_iff.mp
          (List.all_eq_true.mp hchildren link hlinkMem)
        obtain ⟨hmask,hne⟩ := Bool.and_eq_true_iff.mp hrest
        have hmask := of_decide_eq_true hmask
        rw [hmasks link.node] at hmask
        have hsubset : Included (family (nodes link.node).cells)
            (family ((c :: (nodes i).cells).map (renamings link.frame).cells.forward)) := by
          simpa only [hcell] using included_of_masks _ _ hmask
        have hsubCons : Included (family (c :: (nodes i).cells)) (family B) :=
          same_included (family_cons (nodes i).cells c) (add_included hsub hcB)
        have hsubChild : Included (family (nodes link.node).cells)
            (family (B.map (renamings link.frame).cells.forward)) := by
          intro x hx
          exact (included_map (renamings link.frame).cells _ B hsubCons) x (hsubset x hx)
        have hneChild := nonempty_of_ne_nil (nodes link.node).cells (of_decide_eq_true hne)
        obtain ⟨leaf,word,hresult⟩ := ih link.node.val
          (hi ▸ of_decide_eq_true hindex) link.node rfl
          (B.map (renamings link.frame).cells.forward) (hB.rename (renamings link.frame))
          hsubChild hneChild
        exact ⟨leaf,link.frame :: word,hresult⟩
  exact main root.val root rfl B hB hroot hne


#print axioms complete_of_checks
end Papers.RationalityTen.SubsumedGrowth

namespace Papers.RationalityTen.SubsumedRawGrowth
open RawBatchGrowth RawNatGrowthCheck

def childCheck (cellMap : Nat → Nat → Nat) (nodes : Nat → Node)
    (i : Nat) (link : Child) : Bool :=
  decide (link.node < i) &&
    (decide (Nat.land (nodes link.node).mask
      (mask ((link.cell :: (nodes i).cells).map (cellMap link.frame))) =
        (nodes link.node).mask) && decide ((nodes link.node).cells ≠ []))

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

end Papers.RationalityTen.SubsumedRawGrowth

namespace Papers.RationalityTen.SubsumedRawSoundness
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming ConcreteGrowth
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth RawNatGrowthSoundness
variable {n r g k t : Nat}
theorem shift_eq (i : Nat) : Nat.shiftLeft 1 i = 2^i := PrimitiveBitsetGrowth.singleton_eq i

theorem childCheck_erase (maps : Nat → Nat → Nat)
    (rawNodes : Nat → RawBatchGrowth.Node)
    (nodes : Fin t → Node n r g k t)
    (renamingMaps : Fin g → Fin n → Fin n)
    (hmaps : ∀ f c, maps f.val c.val = (renamingMaps f c).val)
    (hnodes : ∀ i, rawNodes i.val = eraseNode (nodes i))
    (i : Fin t) (link : Child n g t) :
    SubsumedRawGrowth.childCheck maps rawNodes i.val (eraseChild link) =
      (decide (link.node.val < i.val) &&
        (decide (Nat.land (nodes link.node).mask (ofList
          ((link.cell :: (nodes i).cells).map (renamingMaps link.frame))) =
            (nodes link.node).mask) && decide ((nodes link.node).cells ≠ []))) := by
  have hmap :
      (link.cell.val :: (nodes i).cells.map Fin.val).map (maps link.frame.val) =
        (((link.cell :: (nodes i).cells).map (renamingMaps link.frame)).map Fin.val) := by
    simp only [← List.map_cons, List.map_map, Function.comp_def, hmaps]
  simp only [SubsumedRawGrowth.childCheck, eraseChild, hnodes, eraseNode, hmap,
    mask_map, PrimitiveBitsetGrowth.mask_eq]
  cases (nodes link.node).cells <;> rfl

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
    (h : SubsumedRawGrowth.nodeCheck candidates bad cache.kinds cache.keys
      rawKind quota maps rawLeaves rawNodes i.val = true) :
    SubsumedGrowth.nodeCheck cache quota renamings leaves nodes i = true := by
  have heq : SubsumedRawGrowth.nodeCheck candidates bad cache.kinds cache.keys
      rawKind quota maps rawLeaves rawNodes i.val =
      ((FastGraphConditionedGrowth.ascending (nodes i).cells &&
        decide ((nodes i).mask = ofList (nodes i).cells)) &&
        SubsumedGrowth.nodeBody cache quota renamings leaves nodes i) := by
    cases ha : (nodes i).action with
    | terminal j =>
        simp only [SubsumedRawGrowth.nodeCheck, hnodes i, eraseNode, ha,
          eraseAction, increasing_map, mask_map, hleaves,
          SubsumedGrowth.nodeBody, PrimitiveBitsetGrowth.mask_eq]
    | split q a closed children =>
        simp only [SubsumedRawGrowth.nodeCheck, hnodes i, eraseNode, ha,
          eraseAction, increasing_map, mask_map, hcandidates,
          List.all_map, Function.comp_def,
          closedCheck_erase candidates cache hcandidates,
          childCheck_erase maps rawNodes nodes
            (fun f => (renamings f).cells.forward) hmaps hnodes,
          blockedMask_erase candidates bad rawKind cache quota hcandidates hbad hkind,
          mask_child_cells, SubsumedGrowth.nodeBody, SubsumedGrowth.childCheck,
          PrimitiveBitsetGrowth.mask_eq, PrimitiveBitsetGrowth.closedCheck_eq, shift_eq]
        rfl
  rw [heq] at h
  obtain ⟨hstate, hbody⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hordered, hmask⟩ := Bool.and_eq_true_iff.mp hstate
  exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
    ⟨decide_eq_true (FastGraphConditionedGrowth.ascending_nodup _ hordered), hmask⟩,
      hbody⟩


#print axioms nodeCheck_sound
end Papers.RationalityTen.SubsumedRawSoundness
