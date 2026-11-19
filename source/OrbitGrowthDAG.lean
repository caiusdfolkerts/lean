module
prelude
public import GrowthRenaming

@[expose] public section

/-!
# Complete facet growth modulo checked renamings

Every possible successor is still recorded. A child edge may rename the enlarged
partial boundary by an explicitly invertible incidence-preserving map. The
conclusion returns the exact word of renamings taking the target boundary to a
literal terminal, so the geometric application can transport the vertex labels
and the terminal realization along precisely that word.
-/

namespace Papers.RationalityTen.OrbitGrowthDAG

open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming

variable {n r g : Nat}

inductive Choice (n r g t : Nat) where
  | rejected (reason : WitnessGrowthDAG.Rejection n r)
  | child (index : Fin t) (frame : Fin g)

inductive Action (n r g k t : Nat) where
  | terminal (entry : Fin k)
  | split (ridge : Fin r) (witness : Fin n) (records : List (Fin n × Choice n r g t))

structure Node (n r g k t : Nat) where
  cells : List (Fin n)
  action : Action n r g k t

def applyWord {ridges : Fin n → Fin r → Bool}
    {compatible : Fin n → Fin n → Bool} {kind : Fin n → Nat}
    (renamings : Fin g → Renaming ridges compatible kind) :
    List (Fin g) → List (Fin n) → List (Fin n)
  | [], B => B
  | p :: rest, B => applyWord renamings rest (B.map (renamings p).cells.forward)

def choiceCheck {k t : Nat} (ridgeList : Fin n → List (Fin r))
    (compatible testCompatible : Fin n → Fin n → Bool) (kind : Fin n → Nat)
    (quota : Nat → Nat)
    (renamings : Fin g → Renaming (fun c => has (ridgeList c)) compatible kind)
    (nodes : Fin t → Node n r g k t) (i : Fin t) (c : Fin n) : Choice n r g t → Bool
  | .rejected reason =>
      WitnessGrowthDAG.rejectionCheck ridgeList testCompatible kind quota (nodes i).cells c reason
  | .child j p => decide (j.val < i.val) &&
      sameCheck (nodes j).cells ((c :: (nodes i).cells).map (renamings p).cells.forward)

def nodeBody {k t : Nat} (ridgeList : Fin n → List (Fin r))
    (candidates : Fin r → List (Fin n))
    (compatible testCompatible : Fin n → Fin n → Bool) (kind : Fin n → Nat)
    (quota : Nat → Nat)
    (renamings : Fin g → Renaming (fun c => has (ridgeList c)) compatible kind)
    (terminals : Fin k → List (Fin n)) (nodes : Fin t → Node n r g k t) (i : Fin t) : Bool :=
  match (nodes i).action with
  | .terminal j => sameCheck (nodes i).cells (terminals j) &&
      WitnessGrowthDAG.closedCheck ridgeList (nodes i).cells
  | .split q a records =>
      (openCheck (fun c => has (ridgeList c)) (nodes i).cells q a &&
        decide (records.map Prod.fst = candidates q)) &&
      records.all fun row =>
        choiceCheck ridgeList compatible testCompatible kind quota renamings nodes i row.1 row.2

def nodeCheck {k t : Nat} (ridgeList : Fin n → List (Fin r))
    (candidates : Fin r → List (Fin n))
    (compatible testCompatible : Fin n → Fin n → Bool) (kind : Fin n → Nat)
    (quota : Nat → Nat)
    (renamings : Fin g → Renaming (fun c => has (ridgeList c)) compatible kind)
    (terminals : Fin k → List (Fin n)) (nodes : Fin t → Node n r g k t) (i : Fin t) : Bool :=
  decide (nodes i).cells.Nodup &&
    nodeBody ridgeList candidates compatible testCompatible kind quota renamings terminals nodes i

theorem complete_of_checks {k t : Nat} (ridgeList : Fin n → List (Fin r))
    (candidates : Fin r → List (Fin n))
    (compatible testCompatible : Fin n → Fin n → Bool) (kind : Fin n → Nat)
    (quota : Nat → Nat)
    (renamings : Fin g → Renaming (fun c => has (ridgeList c)) compatible kind)
    (hcompat : ∀ a b, compatible a b = true → testCompatible a b = true)
    (terminals : Fin k → List (Fin n)) (nodes : Fin t → Node n r g k t)
    (hcoverage : ∀ c, (ridgeList c).all (fun q => has (candidates q) c) = true)
    (hnodes : ∀ i, nodeCheck ridgeList candidates compatible testCompatible kind quota
      renamings terminals nodes i = true)
    (B : List (Fin n))
    (hB : Target (fun c => has (ridgeList c)) compatible kind quota B)
    (root : Fin t) (hroot : Included (family (nodes root).cells) (family B))
    (hne : Nonempty (family (nodes root).cells)) :
    ∃ j word, Same (family (terminals j)) (family (applyWord renamings word B)) := by
  have main : ∀ height : Nat, ∀ i : Fin t, i.val = height →
      ∀ B : List (Fin n), Target (fun c => has (ridgeList c)) compatible kind quota B →
      Included (family (nodes i).cells) (family B) → Nonempty (family (nodes i).cells) →
      ∃ j word, Same (family (terminals j)) (family (applyWord renamings word B)) := by
    intro height
    induction height using Nat.strongRecOn with
    | ind height ih =>
      intro i hi B hB hsub hnonempty
      have hpair : ∀ a b, a ∈ B → b ∈ B → a ≠ b → testCompatible a b = true :=
        fun a b ha hb hab => hcompat a b (hB.pairwise a b ha hb hab)
      have hallowed := preservesTarget ridgeList testCompatible kind quota B
        hB.budget hpair hB.no_three
      obtain ⟨hndBool, hbody⟩ := Bool.and_eq_true_iff.mp (hnodes i)
      have hnd : (nodes i).cells.Nodup := of_decide_eq_true hndBool
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
      | split q a records =>
        have hs :
            (openCheck (fun c => has (ridgeList c)) (nodes i).cells q a &&
              decide (records.map Prod.fst = candidates q)) = true ∧
            records.all (fun row => choiceCheck ridgeList compatible testCompatible
              kind quota renamings nodes i row.1 row.2) = true :=
          Bool.and_eq_true_iff.mp (by simpa only [nodeBody, ha] using hbody)
        obtain ⟨hopen, hrecords⟩ := Bool.and_eq_true_iff.mp hs.1
        obtain ⟨c, hcB, hcS, hcr⟩ := missing_cell (fun c => has (ridgeList c))
          (family B) (family (nodes i).cells) q a hsub hB.mates
          (openCheck_sound _ _ _ _ hopen)
        change has (nodes i).cells c = false at hcS
        have hca := hallowed _ hsub hnd c hcB hcS
        have hcand : c ∈ candidates q :=
          (has_true _ _).mp (List.all_eq_true.mp (hcoverage c) q ((has_true _ _).mp hcr))
        have hmem : c ∈ records.map Prod.fst := (of_decide_eq_true hrecords).symm ▸ hcand
        obtain ⟨row, hrow, hcell⟩ := List.mem_map.mp hmem
        have hvalid := List.all_eq_true.mp hs.2 row hrow
        cases hchoice : row.2 with
        | rejected reason =>
          have hreject : WitnessGrowthDAG.rejectionCheck ridgeList testCompatible kind quota
              (nodes i).cells c reason = true := by
            simpa only [choiceCheck, hchoice, hcell] using hvalid
          exact False.elim (WitnessGrowthDAG.rejectionCheck_sound ridgeList testCompatible kind quota
            (nodes i).cells c reason hreject hcS hca)
        | child j p =>
          have hlink : decide (j.val < i.val) = true ∧
              sameCheck (nodes j).cells
                ((c :: (nodes i).cells).map (renamings p).cells.forward) = true :=
            Bool.and_eq_true_iff.mp (by simpa only [choiceCheck, hchoice, hcell] using hvalid)
          have hsame := sameCheck_sound _ _ hlink.2
          have hcons := family_cons (nodes i).cells c
          have hsubCons : Included (family (c :: (nodes i).cells)) (family B) :=
            same_included hcons (add_included hsub hcB)
          have hneCons : Nonempty (family (c :: (nodes i).cells)) :=
            same_nonempty hcons ⟨c, add_self _ _⟩
          have hsubChild := same_included hsame
            (included_map (renamings p).cells _ B hsubCons)
          have hneChild := same_nonempty hsame
            (nonempty_map (renamings p).cells _ hneCons)
          obtain ⟨terminal, word, heq⟩ := ih j.val (hi ▸ of_decide_eq_true hlink.1) j rfl
            (B.map (renamings p).cells.forward) (hB.rename (renamings p)) hsubChild hneChild
          exact ⟨terminal, p :: word, heq⟩
  exact main root.val root rfl B hB hroot hne

#print axioms complete_of_checks

end Papers.RationalityTen.OrbitGrowthDAG
