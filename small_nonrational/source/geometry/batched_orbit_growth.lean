module
prelude
public import BatchedGrowthPruning
public import OrbitGrowthDAG

@[expose] public section

/-!
# Bitset replay of complete orbit DAGs

An entire candidate set is covered by one checked bitset identity. A selected
cell, an exhausted kind, an incompatible selected cell, or an explicitly paired
ridge may exclude a candidate. Every remaining candidate must occur among the
recorded child cells. This is the same exhaustive mathematical search as the
literal successor checker, with the expensive universal loop removed.
-/

namespace Papers.RationalityTen.BatchedOrbitGrowth

open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open ConcreteGrowth GrowthBitsets BatchedGrowthPruning

variable {n r g : Nat}

structure Child (n g t : Nat) where
  cell : Fin n
  node : Fin t
  frame : Fin g

inductive Action (n r g k t : Nat) where
  | terminal (entry : Fin k)
  | split (ridge : Fin r) (witness : Fin n)
      (closed : List (ClosedWitness n r)) (children : List (Child n g t))

structure Node (n r g k t : Nat) where
  cells : List (Fin n)
  mask : Nat
  action : Action n r g k t

def childCheck {k t : Nat} {ridgeList : Fin n → List (Fin r)}
    {compatible : Fin n → Fin n → Bool} {kind : Fin n → Nat}
    (renamings : Fin g → Renaming (fun c => has (ridgeList c)) compatible kind)
    (nodes : Fin t → Node n r g k t) (i : Fin t) (link : Child n g t) : Bool :=
  decide (link.node.val < i.val) &&
    sameCheck (nodes link.node).cells
      ((link.cell :: (nodes i).cells).map (renamings link.frame).cells.forward)

def nodeBody {k t : Nat} {ridgeList : Fin n → List (Fin r)}
    {compatible : Fin n → Fin n → Bool} {kind : Fin n → Nat}
    (cache : Cache ridgeList compatible kind) (quota : Nat → Nat)
    (renamings : Fin g → Renaming (fun c => has (ridgeList c)) compatible kind)
    (terminals : Fin k → List (Fin n)) (nodes : Fin t → Node n r g k t) (i : Fin t) : Bool :=
  match (nodes i).action with
  | .terminal j => sameCheck (nodes i).cells (terminals j) &&
      WitnessGrowthDAG.closedCheck ridgeList (nodes i).cells
  | .split q a closed children =>
      ((openCheck (fun c => has (ridgeList c)) (nodes i).cells q a &&
        closed.all (closedWitnessCheck cache (nodes i).mask)) &&
        children.all (childCheck renamings nodes i)) &&
      decide (Nat.land (cache.candidates q)
        (Nat.lor (blockedMask cache quota (nodes i).cells (nodes i).mask closed)
          (ofList (children.map Child.cell))) = cache.candidates q)

def nodeCheck {k t : Nat} {ridgeList : Fin n → List (Fin r)}
    {compatible : Fin n → Fin n → Bool} {kind : Fin n → Nat}
    (cache : Cache ridgeList compatible kind) (quota : Nat → Nat)
    (renamings : Fin g → Renaming (fun c => has (ridgeList c)) compatible kind)
    (terminals : Fin k → List (Fin n)) (nodes : Fin t → Node n r g k t) (i : Fin t) : Bool :=
  (decide (nodes i).cells.Nodup && decide ((nodes i).mask = ofList (nodes i).cells)) &&
    nodeBody cache quota renamings terminals nodes i

theorem complete_of_checks {k t : Nat} {ridgeList : Fin n → List (Fin r)}
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
  have main : ∀ height : Nat, ∀ i : Fin t, i.val = height →
      ∀ B : List (Fin n), Target (fun c => has (ridgeList c)) compatible kind quota B →
      Included (family (nodes i).cells) (family B) → Nonempty (family (nodes i).cells) →
      ∃ j word, Same (family (terminals j))
        (family (OrbitGrowthDAG.applyWord renamings word B)) := by
    intro height
    induction height using Nat.strongRecOn with
    | ind height ih =>
      intro i hi B hB hsub hnonempty
      obtain ⟨hstate, hbody⟩ := Bool.and_eq_true_iff.mp (hnodes i)
      obtain ⟨hndBool, hmaskBool⟩ := Bool.and_eq_true_iff.mp hstate
      have hnd : (nodes i).cells.Nodup := of_decide_eq_true hndBool
      have hmask : (nodes i).mask = ofList (nodes i).cells := of_decide_eq_true hmaskBool
      cases ha : (nodes i).action with
      | terminal j =>
        have ht : sameCheck (nodes i).cells (terminals j) = true ∧
            WitnessGrowthDAG.closedCheck ridgeList (nodes i).cells = true :=
          Bool.and_eq_true_iff.mp (by simpa only [nodeBody, ha] using hbody)
        have hs := sameCheck_sound _ _ ht.1
        have heq := closed_eq_target (fun c => has (ridgeList c)) (family B)
          (family (nodes i).cells) hsub hnonempty hB.no_three hB.connected
          (WitnessGrowthDAG.closedCheck_sound _ _ ht.2)
        exact ⟨j, [], fun c => (hs c).symm.trans (heq c)⟩
      | split q a closed children =>
        have hs :
            ((openCheck (fun c => has (ridgeList c)) (nodes i).cells q a &&
              closed.all (closedWitnessCheck cache (nodes i).mask)) &&
              children.all (childCheck renamings nodes i)) = true ∧
            decide (Nat.land (cache.candidates q)
              (Nat.lor (blockedMask cache quota (nodes i).cells (nodes i).mask closed)
                (ofList (children.map Child.cell))) = cache.candidates q) = true :=
          Bool.and_eq_true_iff.mp (by simpa only [nodeBody, ha] using hbody)
        obtain ⟨hopenClosed, hchildren⟩ := Bool.and_eq_true_iff.mp hs.1
        obtain ⟨hopen, hclosed⟩ := Bool.and_eq_true_iff.mp hopenClosed
        obtain ⟨c, hcB, hcS, hcr⟩ := missing_cell (fun c => has (ridgeList c))
          (family B) (family (nodes i).cells) q a hsub hB.mates
          (openCheck_sound _ _ _ _ hopen)
        change has (nodes i).cells c = false at hcS
        have hcand : bitAt (cache.candidates q) c.val = true :=
          (cache.candidates_exact q c).trans hcr
        have hblocked := blockedMask_sound cache quota (nodes i).cells B
          (nodes i).mask closed hmask hclosed hB hsub hnd c hcB hcS
        have hcChild := bitAt_cover _ _ _ c.val (of_decide_eq_true hs.2) hcand hblocked
        have hmem : c ∈ children.map Child.cell := (bitAt_ofList _ c).mp hcChild
        obtain ⟨link, hlinkMem, hcell⟩ := List.mem_map.mp hmem
        have hlink := Bool.and_eq_true_iff.mp (List.all_eq_true.mp hchildren link hlinkMem)
        have hsame : Same (family (nodes link.node).cells)
            (family ((c :: (nodes i).cells).map (renamings link.frame).cells.forward)) := by
          simpa only [hcell] using sameCheck_sound _ _ hlink.2
        have hcons := family_cons (nodes i).cells c
        have hsubCons : Included (family (c :: (nodes i).cells)) (family B) :=
          same_included hcons (add_included hsub hcB)
        have hneCons : Nonempty (family (c :: (nodes i).cells)) :=
          same_nonempty hcons ⟨c, add_self _ _⟩
        have hsubChild := same_included hsame
          (included_map (renamings link.frame).cells _ B hsubCons)
        have hneChild := same_nonempty hsame
          (nonempty_map (renamings link.frame).cells _ hneCons)
        obtain ⟨terminal, word, heq⟩ := ih link.node.val
          (hi ▸ of_decide_eq_true hlink.1) link.node rfl
          (B.map (renamings link.frame).cells.forward) (hB.rename (renamings link.frame))
          hsubChild hneChild
        exact ⟨terminal, link.frame :: word, heq⟩
  exact main root.val root rfl B hB hroot hne

#print axioms complete_of_checks

end Papers.RationalityTen.BatchedOrbitGrowth
