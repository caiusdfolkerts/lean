module
prelude
public import BatchedOrbitGrowth

@[expose] public section

/-!
# Bitset tests for selected families and open ridges

The selected mask is checked once. Equality of masks then proves equality of
families, and a single intersection with a candidate mask proves that a ridge
has precisely one selected owner. This avoids reducing repeated list scans.
-/

namespace Papers.RationalityTen.FastBatchedGrowth

open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming ConcreteGrowth
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth

variable {n r g k t : Nat}

theorem sameCheck_of_masks (S T : List (Fin n)) (h : ofList S = ofList T) :
    sameCheck S T = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply List.all_eq_true.mpr
    intro c hc
    rw [← bitAt_ofList_eq_has, ← h, bitAt_ofList]
    exact hc
  · apply List.all_eq_true.mpr
    intro c hc
    rw [← bitAt_ofList_eq_has, h, bitAt_ofList]
    exact hc

theorem openCheck_of_mask {ridgeList : Fin n → List (Fin r)}
    {compatible : Fin n → Fin n → Bool} {kind : Fin n → Nat}
    (cache : Cache ridgeList compatible kind) (S : List (Fin n)) (selected : Nat)
    (hselected : selected = ofList S) (q : Fin r) (a : Fin n)
    (hopen : Nat.land selected (cache.candidates q) = 2^a.val) :
    openCheck (fun c => has (ridgeList c)) S q a = true := by
  have ha := congrArg (fun bits => bitAt bits a.val) hopen
  rw [bitAt_and, bitAt_power, decide_eq_true rfl, hselected,
    bitAt_ofList_eq_has, cache.candidates_exact] at ha
  apply Bool.and_eq_true_iff.mpr
  refine ⟨ha, List.all_eq_true.mpr ?_⟩
  intro c hc
  apply decide_eq_true
  intro hcr
  change has (ridgeList c) q = true at hcr
  have hbit := congrArg (fun bits => bitAt bits c.val) hopen
  rw [bitAt_and, hselected, bitAt_ofList_eq_has,
    (has_true S c).mpr hc, cache.candidates_exact, hcr, Bool.true_and,
    bitAt_power] at hbit
  exact (Fin.ext (of_decide_eq_true hbit.symm)).symm

def childCheck {ridgeList : Fin n → List (Fin r)}
    {compatible : Fin n → Fin n → Bool} {kind : Fin n → Nat}
    (renamings : Fin g → Renaming (fun c => has (ridgeList c)) compatible kind)
    (nodes : Fin t → Node n r g k t) (i : Fin t) (link : Child n g t) : Bool :=
  decide (link.node.val < i.val) &&
    decide ((nodes link.node).mask =
      ofList ((link.cell :: (nodes i).cells).map (renamings link.frame).cells.forward))

def nodeBody {ridgeList : Fin n → List (Fin r)}
    {compatible : Fin n → Fin n → Bool} {kind : Fin n → Nat}
    (cache : Cache ridgeList compatible kind) (quota : Nat → Nat)
    (renamings : Fin g → Renaming (fun c => has (ridgeList c)) compatible kind)
    (terminals : Fin k → List (Fin n)) (nodes : Fin t → Node n r g k t) (i : Fin t) : Bool :=
  match (nodes i).action with
  | .terminal j => decide ((nodes i).mask = ofList (terminals j)) &&
      WitnessGrowthDAG.closedCheck ridgeList (nodes i).cells
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
    (terminals : Fin k → List (Fin n)) (nodes : Fin t → Node n r g k t) (i : Fin t) : Bool :=
  (decide (nodes i).cells.Nodup && decide ((nodes i).mask = ofList (nodes i).cells)) &&
    nodeBody cache quota renamings terminals nodes i

theorem nodeCheck_sound {ridgeList : Fin n → List (Fin r)}
    {compatible : Fin n → Fin n → Bool} {kind : Fin n → Nat}
    (cache : Cache ridgeList compatible kind) (quota : Nat → Nat)
    (renamings : Fin g → Renaming (fun c => has (ridgeList c)) compatible kind)
    (terminals : Fin k → List (Fin n)) (nodes : Fin t → Node n r g k t)
    (hmasks : ∀ i, (nodes i).mask = ofList (nodes i).cells) (i : Fin t)
    (h : nodeCheck cache quota renamings terminals nodes i = true) :
    BatchedOrbitGrowth.nodeCheck cache quota renamings terminals nodes i = true := by
  obtain ⟨hstate,hbody⟩ := Bool.and_eq_true_iff.mp h
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hstate, ?_⟩
  cases ha : (nodes i).action with
  | terminal j =>
    have hh : decide ((nodes i).mask = ofList (terminals j)) = true ∧
        WitnessGrowthDAG.closedCheck ridgeList (nodes i).cells = true :=
      Bool.and_eq_true_iff.mp (by simpa only [nodeBody,ha] using hbody)
    change BatchedOrbitGrowth.nodeBody cache quota renamings terminals nodes i = true
    rw [BatchedOrbitGrowth.nodeBody,ha]
    exact Bool.and_eq_true_iff.mpr
      ⟨sameCheck_of_masks _ _ ((hmasks i).symm.trans (of_decide_eq_true hh.1)),hh.2⟩
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
    change BatchedOrbitGrowth.nodeBody cache quota renamings terminals nodes i = true
    rw [BatchedOrbitGrowth.nodeBody,ha]
    apply Bool.and_eq_true_iff.mpr
    refine ⟨Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩, hh.2⟩
    · exact Bool.and_eq_true_iff.mpr
        ⟨openCheck_of_mask cache (nodes i).cells (nodes i).mask (hmasks i) q a
          (of_decide_eq_true hopen),hclosed⟩
    · apply List.all_eq_true.mpr
      intro link hlink
      obtain ⟨hindex,hmask⟩ := Bool.and_eq_true_iff.mp
        (List.all_eq_true.mp hchildren link hlink)
      exact Bool.and_eq_true_iff.mpr ⟨hindex,
        sameCheck_of_masks _ _ ((hmasks link.node).symm.trans (of_decide_eq_true hmask))⟩

theorem complete_of_checks {ridgeList : Fin n → List (Fin r)}
    {compatible : Fin n → Fin n → Bool} {kind : Fin n → Nat}
    (cache : Cache ridgeList compatible kind) (quota : Nat → Nat)
    (renamings : Fin g → Renaming (fun c => has (ridgeList c)) compatible kind)
    (terminals : Fin k → List (Fin n)) (nodes : Fin t → Node n r g k t)
    (hnodes : ∀ i, nodeCheck cache quota renamings terminals nodes i = true)
    (B : List (Fin n))
    (hB : Target (fun c => has (ridgeList c)) compatible kind quota B)
    (root : Fin t) (hroot : Included (family (nodes root).cells) (family B))
    (hne : Nonempty (family (nodes root).cells)) :
    ∃ j word, Same (family (terminals j))
      (family (OrbitGrowthDAG.applyWord renamings word B)) := by
  have hmasks : ∀ i, (nodes i).mask = ofList (nodes i).cells := by
    intro i
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (hnodes i)).1).2
  exact BatchedOrbitGrowth.complete_of_checks cache quota renamings terminals nodes
    (fun i => nodeCheck_sound cache quota renamings terminals nodes hmasks i (hnodes i))
    B hB root hroot hne

#print axioms complete_of_checks

end Papers.RationalityTen.FastBatchedGrowth
