module
prelude
public import GrowthPruning

@[expose] public section

/-!
# Growth certificates with local rejection witnesses

Each candidate across the chosen open ridge has a literal record. A record
either points to an earlier node or exhibits one violated necessary condition.
This avoids recomputing every compatibility test for candidates already ruled
out by a single selected cell. The candidate list is copied exactly, so an
unrecorded successor cannot be accepted.
-/

namespace Papers.RationalityTen.WitnessGrowthDAG

open GrowthDAG SparseGrowthDAG GrowthPruning

variable {n r : Nat}

inductive Rejection (n r : Nat) where
  | selected
  | quota
  | incompatible (cell : Fin n)
  | closedRidge (ridge : Fin r)

def rejectionCheck (ridgeList : Fin n → List (Fin r))
    (compatible : Fin n → Fin n → Bool) (kind : Fin n → Nat)
    (quota : Nat → Nat) (S : List (Fin n)) (c : Fin n) :
    Rejection n r → Bool
  | .selected => has S c
  | .quota => decide (quota (kind c) ≤ kindCount kind S (kind c))
  | .incompatible a => has S a && !compatible a c
  | .closedRidge q => has (ridgeList c) q &&
      decide (2 ≤ (S.filter fun a => has (ridgeList a) q).length)

theorem rejectionCheck_sound (ridgeList : Fin n → List (Fin r))
    (compatible : Fin n → Fin n → Bool) (kind : Fin n → Nat)
    (quota : Nat → Nat) (S : List (Fin n)) (c : Fin n) (reason : Rejection n r)
    (hcheck : rejectionCheck ridgeList compatible kind quota S c reason = true)
    (hmissing : has S c = false)
    (hallowed : GrowthPruning.allowed ridgeList compatible kind quota S c = true) : False := by
  obtain ⟨hhead, hridges⟩ := Bool.and_eq_true_iff.mp hallowed
  obtain ⟨hquota, hcompat⟩ := Bool.and_eq_true_iff.mp hhead
  cases reason with
  | selected => exact Bool.noConfusion (hmissing.symm.trans hcheck)
  | quota => exact Nat.not_le_of_lt (of_decide_eq_true hquota) (of_decide_eq_true hcheck)
  | incompatible a =>
    obtain ⟨ha, hbad⟩ := Bool.and_eq_true_iff.mp hcheck
    have hgood := List.all_eq_true.mp hcompat a ((has_true S a).mp ha)
    simp only [hgood, Bool.not_true] at hbad
    exact Bool.noConfusion hbad
  | closedRidge q =>
    obtain ⟨hq, hbad⟩ := Bool.and_eq_true_iff.mp hcheck
    have hgood := List.all_eq_true.mp hridges q ((has_true _ q).mp hq)
    exact Nat.not_le_of_lt (of_decide_eq_true hgood) (of_decide_eq_true hbad)

inductive Choice (n r t : Nat) where
  | rejected (reason : Rejection n r)
  | child (index : Fin t)

inductive Action (n r k t : Nat) where
  | terminal (entry : Fin k)
  | split (ridge : Fin r) (witness : Fin n) (records : List (Fin n × Choice n r t))

structure Node (n r k t : Nat) where
  cells : List (Fin n)
  action : Action n r k t

def closedCheck (ridgeList : Fin n → List (Fin r)) (S : List (Fin n)) : Bool :=
  S.all fun a => (ridgeList a).all fun q =>
    S.any fun b => decide (b ≠ a) && has (ridgeList b) q

theorem closedCheck_sound (ridgeList : Fin n → List (Fin r)) (S : List (Fin n))
    (hcheck : closedCheck ridgeList S = true) :
    Closed (fun a => has (ridgeList a)) (family S) := by
  intro q a ha
  have hrow := List.all_eq_true.mp hcheck a ((has_true S a).mp ha.1)
  have hmate := List.all_eq_true.mp hrow q ((has_true _ q).mp ha.2)
  obtain ⟨b, hb, hbr⟩ := List.any_eq_true.mp hmate
  obtain ⟨hba, hbr⟩ := Bool.and_eq_true_iff.mp hbr
  exact ⟨b, ⟨(has_true S b).mpr hb, hbr⟩, of_decide_eq_true hba⟩

def candidateCheck (ridgeList : Fin n → List (Fin r))
    (candidates : Fin r → List (Fin n)) : Bool :=
  decide (∀ c, (ridgeList c).all (fun q => has (candidates q) c) = true)

theorem candidateCheck_complete (ridgeList : Fin n → List (Fin r))
    (candidates : Fin r → List (Fin n))
    (hcheck : candidateCheck ridgeList candidates = true)
    (c : Fin n) (q : Fin r) (hcq : has (ridgeList c) q = true) : c ∈ candidates q :=
  (has_true _ _).mp (List.all_eq_true.mp (of_decide_eq_true hcheck c) q
    ((has_true _ q).mp hcq))

def choiceCheck {k t : Nat} (ridgeList : Fin n → List (Fin r))
    (compatible : Fin n → Fin n → Bool) (kind : Fin n → Nat)
    (quota : Nat → Nat) (nodes : Fin t → Node n r k t) (i : Fin t)
    (c : Fin n) : Choice n r t → Bool
  | .rejected reason =>
      rejectionCheck ridgeList compatible kind quota (nodes i).cells c reason
  | .child j => decide (j.val < i.val) &&
      sameCheck (nodes j).cells (c :: (nodes i).cells)

def nodeBody {k t : Nat} (ridgeList : Fin n → List (Fin r))
    (candidates : Fin r → List (Fin n))
    (compatible : Fin n → Fin n → Bool) (kind : Fin n → Nat)
    (quota : Nat → Nat) (terminals : Fin k → List (Fin n))
    (nodes : Fin t → Node n r k t) (i : Fin t) : Bool :=
  match (nodes i).action with
  | .terminal j => sameCheck (nodes i).cells (terminals j) &&
      closedCheck ridgeList (nodes i).cells
  | .split q a records =>
      (openCheck (fun c => has (ridgeList c)) (nodes i).cells q a &&
        decide (records.map Prod.fst = candidates q)) &&
      records.all fun row =>
        choiceCheck ridgeList compatible kind quota nodes i row.1 row.2

def nodeCheck {k t : Nat} (ridgeList : Fin n → List (Fin r))
    (candidates : Fin r → List (Fin n))
    (compatible : Fin n → Fin n → Bool) (kind : Fin n → Nat)
    (quota : Nat → Nat) (terminals : Fin k → List (Fin n))
    (nodes : Fin t → Node n r k t) (i : Fin t) : Bool :=
  decide (nodes i).cells.Nodup &&
    nodeBody ridgeList candidates compatible kind quota terminals nodes i

def check {k t : Nat} (ridgeList : Fin n → List (Fin r))
    (candidates : Fin r → List (Fin n))
    (compatible : Fin n → Fin n → Bool) (kind : Fin n → Nat)
    (quota : Nat → Nat) (terminals : Fin k → List (Fin n))
    (nodes : Fin t → Node n r k t) : Bool :=
  candidateCheck ridgeList candidates &&
    decide (∀ i, nodeCheck ridgeList candidates compatible kind quota terminals nodes i = true)

theorem check_complete {k t : Nat} (ridgeList : Fin n → List (Fin r))
    (candidates : Fin r → List (Fin n))
    (compatible : Fin n → Fin n → Bool) (kind : Fin n → Nat)
    (quota : Nat → Nat) (terminals : Fin k → List (Fin n))
    (nodes : Fin t → Node n r k t)
    (hcheck : check ridgeList candidates compatible kind quota terminals nodes = true)
    (B : List (Fin n)) (hquota : ∀ j, kindCount kind B j ≤ quota j)
    (hcompatible : ∀ a b, a ∈ B → b ∈ B → a ≠ b → compatible a b = true)
    (hmates : HasMate (fun c => has (ridgeList c)) (family B))
    (hthree : NoThree (fun c => has (ridgeList c)) (family B))
    (hconn : Connected (fun c => has (ridgeList c)) (family B))
    (root : Fin t) (hroot : Included (family (nodes root).cells) (family B))
    (hne : Nonempty (family (nodes root).cells)) :
    ∃ j, Same (family (terminals j)) (family B) := by
  obtain ⟨hcoverage, hnodesBool⟩ := Bool.and_eq_true_iff.mp hcheck
  have hnodes : ∀ i, nodeCheck ridgeList candidates compatible kind quota terminals nodes i = true :=
    of_decide_eq_true hnodesBool
  have hallowed := preservesTarget ridgeList compatible kind quota B hquota hcompatible hthree
  have main : ∀ height : Nat, ∀ i : Fin t, i.val = height →
      Included (family (nodes i).cells) (family B) → Nonempty (family (nodes i).cells) →
      ∃ j, Same (family (terminals j)) (family B) := by
    intro height
    induction height using Nat.strongRecOn with
    | ind height ih =>
      intro i hi hsub hnonempty
      obtain ⟨hndBool, hbody⟩ := Bool.and_eq_true_iff.mp (hnodes i)
      have hnd : (nodes i).cells.Nodup := of_decide_eq_true hndBool
      cases ha : (nodes i).action with
      | terminal j =>
        have ht : sameCheck (nodes i).cells (terminals j) = true ∧
            closedCheck ridgeList (nodes i).cells = true :=
          Bool.and_eq_true_iff.mp (by simpa only [nodeBody, ha] using hbody)
        have hs := sameCheck_sound _ _ ht.1
        have heq := closed_eq_target (fun c => has (ridgeList c)) (family B)
          (family (nodes i).cells) hsub hnonempty hthree hconn (closedCheck_sound _ _ ht.2)
        exact ⟨j, fun c => (hs c).symm.trans (heq c)⟩
      | split q a records =>
        have hs :
            (openCheck (fun c => has (ridgeList c)) (nodes i).cells q a &&
              decide (records.map Prod.fst = candidates q)) = true ∧
            records.all (fun row =>
              choiceCheck ridgeList compatible kind quota nodes i row.1 row.2) = true :=
          Bool.and_eq_true_iff.mp (by simpa only [nodeBody, ha] using hbody)
        obtain ⟨hopen, hrecords⟩ := Bool.and_eq_true_iff.mp hs.1
        obtain ⟨c, hcB, hcS, hcr⟩ := missing_cell (fun c => has (ridgeList c))
          (family B) (family (nodes i).cells) q a hsub hmates
          (openCheck_sound _ _ _ _ hopen)
        change has (nodes i).cells c = false at hcS
        have hca := hallowed _ hsub hnd c hcB hcS
        have hcand := candidateCheck_complete _ _ hcoverage c q hcr
        have hmem : c ∈ records.map Prod.fst := (of_decide_eq_true hrecords).symm ▸ hcand
        obtain ⟨row, hrow, hcell⟩ := List.mem_map.mp hmem
        have hvalid := List.all_eq_true.mp hs.2 row hrow
        cases hchoice : row.2 with
        | rejected reason =>
          have hreject : rejectionCheck ridgeList compatible kind quota
              (nodes i).cells c reason = true := by
            simpa only [choiceCheck, hchoice, hcell] using hvalid
          exact False.elim (rejectionCheck_sound ridgeList compatible kind quota
            (nodes i).cells c reason hreject hcS hca)
        | child j =>
          have hlink : decide (j.val < i.val) = true ∧
              sameCheck (nodes j).cells (c :: (nodes i).cells) = true :=
            Bool.and_eq_true_iff.mp (by simpa only [choiceCheck, hchoice, hcell] using hvalid)
          have hsame := sameCheck_sound _ _ hlink.2
          have hcons := family_cons (nodes i).cells c
          have hs' : Same (family (nodes j).cells) (add (family (nodes i).cells) c) :=
            fun d => (hsame d).trans (hcons d)
          exact ih j.val (hi ▸ of_decide_eq_true hlink.1) j rfl
            (same_included hs' (add_included hsub hcB))
            (same_nonempty hs' ⟨c, add_self _ _⟩)
  exact main root.val root rfl hroot hne


/-- Compositional replay interface: no aggregate finite universal decision is recomputed. -/
theorem complete_of_checks {k t : Nat} (ridgeList : Fin n → List (Fin r))
    (candidates : Fin r → List (Fin n))
    (compatible : Fin n → Fin n → Bool) (kind : Fin n → Nat)
    (quota : Nat → Nat) (terminals : Fin k → List (Fin n))
    (nodes : Fin t → Node n r k t)
    (hcoverage : ∀ c, (ridgeList c).all (fun q => has (candidates q) c) = true)
    (hnodes : ∀ i, nodeCheck ridgeList candidates compatible kind quota terminals nodes i = true)
    (B : List (Fin n)) (hquota : ∀ j, kindCount kind B j ≤ quota j)
    (hcompatible : ∀ a b, a ∈ B → b ∈ B → a ≠ b → compatible a b = true)
    (hmates : HasMate (fun c => has (ridgeList c)) (family B))
    (hthree : NoThree (fun c => has (ridgeList c)) (family B))
    (hconn : Connected (fun c => has (ridgeList c)) (family B))
    (root : Fin t) (hroot : Included (family (nodes root).cells) (family B))
    (hne : Nonempty (family (nodes root).cells)) :
    ∃ j, Same (family (terminals j)) (family B) := by
  have hallowed := preservesTarget ridgeList compatible kind quota B hquota hcompatible hthree
  have main : ∀ height : Nat, ∀ i : Fin t, i.val = height →
      Included (family (nodes i).cells) (family B) → Nonempty (family (nodes i).cells) →
      ∃ j, Same (family (terminals j)) (family B) := by
    intro height
    induction height using Nat.strongRecOn with
    | ind height ih =>
      intro i hi hsub hnonempty
      obtain ⟨hndBool, hbody⟩ := Bool.and_eq_true_iff.mp (hnodes i)
      have hnd : (nodes i).cells.Nodup := of_decide_eq_true hndBool
      cases ha : (nodes i).action with
      | terminal j =>
        have ht : sameCheck (nodes i).cells (terminals j) = true ∧
            closedCheck ridgeList (nodes i).cells = true :=
          Bool.and_eq_true_iff.mp (by simpa only [nodeBody, ha] using hbody)
        have hs := sameCheck_sound _ _ ht.1
        have heq := closed_eq_target (fun c => has (ridgeList c)) (family B)
          (family (nodes i).cells) hsub hnonempty hthree hconn (closedCheck_sound _ _ ht.2)
        exact ⟨j, fun c => (hs c).symm.trans (heq c)⟩
      | split q a records =>
        have hs :
            (openCheck (fun c => has (ridgeList c)) (nodes i).cells q a &&
              decide (records.map Prod.fst = candidates q)) = true ∧
            records.all (fun row =>
              choiceCheck ridgeList compatible kind quota nodes i row.1 row.2) = true :=
          Bool.and_eq_true_iff.mp (by simpa only [nodeBody, ha] using hbody)
        obtain ⟨hopen, hrecords⟩ := Bool.and_eq_true_iff.mp hs.1
        obtain ⟨c, hcB, hcS, hcr⟩ := missing_cell (fun c => has (ridgeList c))
          (family B) (family (nodes i).cells) q a hsub hmates
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
          have hreject : rejectionCheck ridgeList compatible kind quota
              (nodes i).cells c reason = true := by
            simpa only [choiceCheck, hchoice, hcell] using hvalid
          exact False.elim (rejectionCheck_sound ridgeList compatible kind quota
            (nodes i).cells c reason hreject hcS hca)
        | child j =>
          have hlink : decide (j.val < i.val) = true ∧
              sameCheck (nodes j).cells (c :: (nodes i).cells) = true :=
            Bool.and_eq_true_iff.mp (by simpa only [choiceCheck, hchoice, hcell] using hvalid)
          have hsame := sameCheck_sound _ _ hlink.2
          have hcons := family_cons (nodes i).cells c
          have hs' : Same (family (nodes j).cells) (add (family (nodes i).cells) c) :=
            fun d => (hsame d).trans (hcons d)
          exact ih j.val (hi ▸ of_decide_eq_true hlink.1) j rfl
            (same_included hs' (add_included hsub hcB))
            (same_nonempty hs' ⟨c, add_self _ _⟩)
  exact main root.val root rfl hroot hne

#print axioms check_complete
#print axioms complete_of_checks

end Papers.RationalityTen.WitnessGrowthDAG
