module
prelude
public import GraphGrowthRuleSoundness
public import SubsumptionSearch

@[expose] public section

/-!
# Complete boundary growth inside a fixed graph

Every rule supplies a genuinely missing cell of any target extending the
current family.  Checked local exclusions bound the available cells, and one
mask identity accounts for every available candidate.  A child may reuse an
earlier subfamily after a checked graph automorphism.  Strictly decreasing
indices make such reuse acyclic.  The initial family may be empty.
-/

namespace Papers.RationalityTen.GraphConditionedGrowth

open GrowthDAG SparseGrowthDAG GrowthPruning ConcreteGrowth GrowthBitsets
open BatchedGrowthPruning UnsupportedRidgePruning GraphGrowthConstraints

variable {n r e v k g l t : Nat}

structure Child (n g t : Nat) where
  cell : Fin n
  node : Fin t
  frame : Fin g

inductive Action (n r e v k g l t : Nat) where
  | terminal (leaf : Fin l)
  | split (rule : Rule r e v k) (children : List (Child n g t))

structure Node (n r e v k g l t : Nat) where
  cells : List (Fin n)
  mask : Nat
  available : Nat
  closed : List (ClosedWitness n r)
  removals : List (Removal n r)
  action : Action n r e v k g l t

def exclusions (D : Problem n r e v k) (node : Node n r e v k g l t) : Nat :=
  resultingMask (blockedMask D.cache D.quota node.cells node.mask node.closed) node.removals

def availabilityCheck (D : Problem n r e v k)
    (node : Node n r e v k g l t) : Bool :=
  (node.closed.all (closedWitnessCheck D.cache node.mask) &&
    checks D.cache node.mask
      (blockedMask D.cache D.quota node.cells node.mask node.closed) node.removals) &&
    decide (Nat.land (FiniteMaskSets.allMask n)
      (Nat.lor (exclusions D node) node.available) = FiniteMaskSets.allMask n)

theorem availabilityCheck_sound (D : Problem n r e v k)
    (node : Node n r e v k g l t) (B : List (Fin n))
    (hmask : node.mask = ofList node.cells) (hnd : node.cells.Nodup)
    (hB : GraphGrowthConstraints.Target D B)
    (hsub : Included (family node.cells) (family B))
    (hcheck : availabilityCheck D node = true) :
    Available node.cells B node.available := by
  obtain ⟨hlocal, hcover⟩ := Bool.and_eq_true_iff.mp hcheck
  obtain ⟨hclosed, hremovals⟩ := Bool.and_eq_true_iff.mp hlocal
  have hbase := blockedMask_sound D.cache D.quota node.cells B node.mask node.closed
    hmask hclosed hB.boundary hsub hnd
  have hsound := checks_sound D.cache node.cells B node.mask
    (blockedMask D.cache D.quota node.cells node.mask node.closed)
    hmask hbase hB.boundary.mates node.removals hremovals
  intro c hcB hcS
  apply FiniteMaskSets.bit_of_cover (of_decide_eq_true hcover) c
  have hcS' : has node.cells c = false := by
    apply Bool.eq_false_of_ne_true
    exact fun h => hcS ((has_true _ _).mp h)
  simpa only [exclusions, bitAt_eq_testBit] using
    hsound c ((has_true B c).mpr hcB) hcS'

def childCheck (D : Problem n r e v k)
    (renamings : Fin g → GraphGrowthConstraints.Renaming D)
    (nodes : Fin t → Node n r e v k g l t) (i : Fin t)
    (link : Child n g t) : Bool :=
  decide (link.node.val < i.val) &&
    decide (Nat.land (nodes link.node).mask
      (PrimitiveBitsetGrowth.mask
        ((link.cell :: (nodes i).cells).map
          (renamings link.frame).boundary.cells.forward)) = (nodes link.node).mask)

def nodeBody (D : Problem n r e v k)
    (renamings : Fin g → GraphGrowthConstraints.Renaming D)
    (leaves : Fin l → List (Fin n))
    (nodes : Fin t → Node n r e v k g l t) (i : Fin t) : Bool :=
  match (nodes i).action with
  | .terminal leaf =>
      (decide ((nodes i).mask = PrimitiveBitsetGrowth.mask (leaves leaf)) &&
        decide ((nodes i).mask ≠ 0)) &&
      WitnessGrowthDAG.closedCheck D.ridgeList (nodes i).cells
  | .split rule children =>
      ((availabilityCheck D (nodes i) &&
        ruleCheck D (nodes i).cells (nodes i).mask (nodes i).available rule) &&
        children.all (childCheck D renamings nodes i)) &&
      decide (Nat.land (Nat.land (candidates D rule) (nodes i).available)
        (PrimitiveBitsetGrowth.mask (children.map Child.cell)) =
          Nat.land (candidates D rule) (nodes i).available)

def nodeCheck (D : Problem n r e v k)
    (renamings : Fin g → GraphGrowthConstraints.Renaming D)
    (leaves : Fin l → List (Fin n))
    (nodes : Fin t → Node n r e v k g l t) (i : Fin t) : Bool :=
  (decide (nodes i).cells.Nodup &&
    decide ((nodes i).mask = PrimitiveBitsetGrowth.mask (nodes i).cells)) &&
  nodeBody D renamings leaves nodes i

/-- The complete checker yields equality with a recorded closed boundary,
including when the search starts from the empty family. -/
theorem complete_of_checks (D : Problem n r e v k)
    (hvertex : VertexCapacitySound D)
    (renamings : Fin g → GraphGrowthConstraints.Renaming D)
    (leaves : Fin l → List (Fin n))
    (nodes : Fin t → Node n r e v k g l t)
    (hchecks : ∀ i, nodeCheck D renamings leaves nodes i = true)
    (B : List (Fin n)) (hB : GraphGrowthConstraints.Target D B)
    (root : Fin t) (hroot : Included (family (nodes root).cells) (family B)) :
    ∃ leaf word, Same (family (leaves leaf))
      (family (OrbitGrowthDAG.applyWord (fun j => (renamings j).boundary) word B)) := by
  have hmasks : ∀ i, (nodes i).mask = ofList (nodes i).cells := by
    intro i
    have hh := of_decide_eq_true
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (hchecks i)).1).2
    simpa only [PrimitiveBitsetGrowth.mask_eq] using hh
  have main : ∀ height : Nat, ∀ i : Fin t, i.val = height →
      ∀ B, GraphGrowthConstraints.Target D B →
      Included (family (nodes i).cells) (family B) →
      ∃ leaf word, Same (family (leaves leaf))
        (family (OrbitGrowthDAG.applyWord (fun j => (renamings j).boundary) word B)) := by
    intro height
    induction height using Nat.strongRecOn with
    | ind height ih =>
      intro i hi B hB hsub
      obtain ⟨hstate, hbody⟩ := Bool.and_eq_true_iff.mp (hchecks i)
      have hnd : (nodes i).cells.Nodup :=
        of_decide_eq_true (Bool.and_eq_true_iff.mp hstate).1
      cases ha : (nodes i).action with
      | terminal leaf =>
        obtain ⟨hmaskNonempty, hclosed⟩ := Bool.and_eq_true_iff.mp
          (by simpa only [nodeBody, ha] using hbody)
        obtain ⟨hmask, hnonempty⟩ := Bool.and_eq_true_iff.mp hmaskNonempty
        have hsame : Same (family (nodes i).cells) (family (leaves leaf)) := by
          apply sameCheck_sound
          apply FastBatchedGrowth.sameCheck_of_masks
          rw [← hmasks i]
          simpa only [PrimitiveBitsetGrowth.mask_eq] using of_decide_eq_true hmask
        have hne : Nonempty (family (nodes i).cells) := by
          apply SubsumptionSearch.nonempty_of_mask_ne_zero
          rw [← hmasks i]
          exact of_decide_eq_true hnonempty
        have heq := closed_eq_target (fun c => has (D.ridgeList c))
          (family B) (family (nodes i).cells) hsub hne hB.boundary.no_three
          hB.boundary.connected (WitnessGrowthDAG.closedCheck_sound _ _ hclosed)
        exact ⟨leaf, [], fun c => (hsame c).symm.trans (heq c)⟩
      | split rule children =>
        have hh :
            ((availabilityCheck D (nodes i) &&
              ruleCheck D (nodes i).cells (nodes i).mask (nodes i).available rule) &&
              children.all (childCheck D renamings nodes i)) = true ∧
            decide (Nat.land (Nat.land (candidates D rule) (nodes i).available)
              (PrimitiveBitsetGrowth.mask (children.map Child.cell)) =
                Nat.land (candidates D rule) (nodes i).available) = true :=
          Bool.and_eq_true_iff.mp (by simpa only [nodeBody, ha] using hbody)
        obtain ⟨hlocal, hchildren⟩ := Bool.and_eq_true_iff.mp hh.1
        obtain ⟨havail, hrule⟩ := Bool.and_eq_true_iff.mp hlocal
        have havailable := availabilityCheck_sound D (nodes i) B (hmasks i)
          hnd hB hsub havail
        obtain ⟨c, hcB, hcS, hcandidate⟩ := ruleCheck_sound D hvertex
          (nodes i).cells B (nodes i).mask (nodes i).available (hmasks i)
          hB hnd hsub havailable rule hrule
        have havailable := havailable c hcB hcS
        have hbit := congrArg (fun mask => mask.testBit c.val) (of_decide_eq_true hh.2)
        have hchildBit : (ofList (children.map Child.cell)).testBit c.val = true := by
          simpa only [PrimitiveBitsetGrowth.mask_eq, FiniteMaskSets.testBit_land,
            hcandidate, havailable, Bool.true_and] using hbit
        have hmem : c ∈ children.map Child.cell := (bitAt_ofList _ c).mp
          ((bitAt_eq_testBit _ _).trans hchildBit)
        obtain ⟨link, hlink, hcell⟩ := List.mem_map.mp hmem
        obtain ⟨hearlier, hsubset⟩ := Bool.and_eq_true_iff.mp
          (List.all_eq_true.mp hchildren link hlink)
        have hchild : Included (family (nodes link.node).cells)
            (family ((c :: (nodes i).cells).map
              (renamings link.frame).boundary.cells.forward)) := by
          apply SubsumptionSearch.included_of_masks
          rw [← hmasks link.node]
          simpa only [PrimitiveBitsetGrowth.mask_eq, hcell] using of_decide_eq_true hsubset
        have hadd : Included (family (c :: (nodes i).cells)) (family B) :=
          same_included (family_cons (nodes i).cells c)
            (add_included hsub ((has_true B c).mpr hcB))
        have hmap := GrowthRenaming.included_map (renamings link.frame).boundary.cells
          (c :: (nodes i).cells) B hadd
        obtain ⟨leaf, word, hresult⟩ := ih link.node.val
          (hi ▸ of_decide_eq_true hearlier) link.node rfl
          (B.map (renamings link.frame).boundary.cells.forward)
          (hB.rename (renamings link.frame)) (fun d hd => hmap d (hchild d hd))
        exact ⟨leaf, link.frame :: word, hresult⟩
  exact main root.val root rfl B hB hroot

#print axioms complete_of_checks

end Papers.RationalityTen.GraphConditionedGrowth
