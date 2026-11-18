module
prelude
public import GrowthDAG
public import Init.Data.Bool

@[expose] public section

/-!
# Sparse certificates for complete facet growth

The dense checker exposes the mathematical invariant. This implementation
uses short lists for partial boundaries and precomputed ridge-incidence lists.
Their completeness is itself checked. Neither a missing successor nor an
incorrectly pruned candidate can disappear behind a producer assertion.
-/

namespace Papers.RationalityTen.SparseGrowthDAG

open GrowthDAG

variable {n r : Nat}

def has (S : List (Fin n)) (c : Fin n) : Bool :=
  S.any fun a => decide (a = c)

def family (S : List (Fin n)) : Family n := has S

theorem has_true (S : List (Fin n)) (c : Fin n) : has S c = true ↔ c ∈ S := by
  constructor
  · intro h
    obtain ⟨a, ha, heq⟩ := List.any_eq_true.mp h
    exact (of_decide_eq_true heq) ▸ ha
  · intro h
    exact List.any_eq_true.mpr ⟨c, h, decide_eq_true rfl⟩

def sameCheck (S T : List (Fin n)) : Bool :=
  S.all (has T) && T.all (has S)

theorem sameCheck_sound (S T : List (Fin n)) (h : sameCheck S T = true) :
    Same (family S) (family T) := by
  obtain ⟨hST, hTS⟩ := Bool.and_eq_true_iff.mp h
  intro c
  cases hs : has S c with
  | false =>
    cases ht : has T c with
    | false => exact hs.trans ht.symm
    | true =>
      have bad := List.all_eq_true.mp hTS c ((has_true T c).mp ht)
      exact False.elim (Bool.noConfusion (hs.symm.trans bad))
  | true =>
    have ht := List.all_eq_true.mp hST c ((has_true S c).mp hs)
    exact hs.trans ht.symm

theorem family_cons (S : List (Fin n)) (c : Fin n) :
    Same (family (c :: S)) (add (family S) c) := by
  intro d
  by_cases hdc : d = c
  · subst d
    simp [family, has, add]
  · have hcd : c ≠ d := fun h => hdc h.symm
    simp [family, has, add, hdc, hcd]

def openCheck (ridges : Fin n → Fin r → Bool) (S : List (Fin n))
    (q : Fin r) (a : Fin n) : Bool :=
  (has S a && ridges a q) &&
    S.all fun c => decide (ridges c q = true → c = a)

theorem openCheck_sound (ridges : Fin n → Fin r → Bool) (S : List (Fin n))
    (q : Fin r) (a : Fin n) (h : openCheck ridges S q a = true) :
    OpenAt ridges (family S) q a := by
  obtain ⟨hhead, htail⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨haS, har⟩ := Bool.and_eq_true_iff.mp hhead
  refine ⟨⟨haS, har⟩, ?_⟩
  intro c hc
  exact of_decide_eq_true
    (List.all_eq_true.mp htail c ((has_true S c).mp hc.1)) hc.2

def closedCheck (ridges : Fin n → Fin r → Bool) (S : List (Fin n)) : Bool :=
  S.all fun a => decide (∀ q : Fin r, ridges a q = true →
    S.any (fun b => decide (b ≠ a) && ridges b q) = true)

theorem closedCheck_sound (ridges : Fin n → Fin r → Bool) (S : List (Fin n))
    (h : closedCheck ridges S = true) : Closed ridges (family S) := by
  intro q a ha
  have hrow := List.all_eq_true.mp h a ((has_true S a).mp ha.1)
  have hmate := of_decide_eq_true hrow q ha.2
  obtain ⟨b, hb, hbr⟩ := List.any_eq_true.mp hmate
  obtain ⟨hba, hbr⟩ := Bool.and_eq_true_iff.mp hbr
  exact ⟨b, ⟨(has_true S b).mpr hb, hbr⟩, of_decide_eq_true hba⟩

/-- A false incidence may be omitted; a true one must occur in the literal list. -/
def candidateCheck (ridges : Fin n → Fin r → Bool)
    (candidates : Fin r → List (Fin n)) : Bool :=
  decide (∀ q c, ridges c q = true → has (candidates q) c = true)

theorem candidateCheck_complete (ridges : Fin n → Fin r → Bool)
    (candidates : Fin r → List (Fin n))
    (h : candidateCheck ridges candidates = true)
    (q : Fin r) (c : Fin n) (hc : ridges c q = true) : c ∈ candidates q :=
  (has_true _ _).mp (of_decide_eq_true h q c hc)

def PreservesTarget (allowed : List (Fin n) → Fin n → Bool) (B : Family n) : Prop :=
  ∀ S, Included (family S) B → S.Nodup →
    ∀ c, B c = true → has S c = false → allowed S c = true

inductive Action (n r k t : Nat) where
  | terminal (entry : Fin k)
  | split (ridge : Fin r) (witness : Fin n) (children : List (Fin n × Fin t))

structure Node (n r k t : Nat) where
  cells : List (Fin n)
  action : Action n r k t

def linkCheck {k t : Nat} (nodes : Fin t → Node n r k t)
    (parent : Fin t) (cell : Fin n) (link : Fin n × Fin t) : Bool :=
  decide (link.1 = cell ∧ link.2.val < parent.val) &&
    sameCheck (nodes link.2).cells (cell :: (nodes parent).cells)

theorem linkCheck_sound {k t : Nat} (nodes : Fin t → Node n r k t)
    (parent : Fin t) (cell : Fin n) (link : Fin n × Fin t)
    (h : linkCheck nodes parent cell link = true) :
    link.1 = cell ∧ link.2.val < parent.val ∧
      Same (family (nodes link.2).cells) (add (family (nodes parent).cells) cell) := by
  obtain ⟨hhead, htail⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨heq, hlt⟩ := of_decide_eq_true hhead
  have hs := sameCheck_sound _ _ htail
  have hc := family_cons (nodes parent).cells cell
  exact ⟨heq, hlt, fun c => (hs c).trans (hc c)⟩

def eligible (ridges : Fin n → Fin r → Bool)
    (allowed : List (Fin n) → Fin n → Bool) (S : List (Fin n))
    (q : Fin r) (c : Fin n) : Bool :=
  !has S c && ridges c q && allowed S c

def nodeBody {k t : Nat} (ridges : Fin n → Fin r → Bool)
    (candidates : Fin r → List (Fin n))
    (allowed : List (Fin n) → Fin n → Bool) (terminals : Fin k → List (Fin n))
    (nodes : Fin t → Node n r k t) (i : Fin t) : Bool :=
  match (nodes i).action with
  | .terminal j => sameCheck (nodes i).cells (terminals j) &&
      closedCheck ridges (nodes i).cells
  | .split q a links => openCheck ridges (nodes i).cells q a &&
      (candidates q).all fun c =>
        !eligible ridges allowed (nodes i).cells q c ||
          links.any (linkCheck nodes i c)

def nodeCheck {k t : Nat} (ridges : Fin n → Fin r → Bool)
    (candidates : Fin r → List (Fin n))
    (allowed : List (Fin n) → Fin n → Bool) (terminals : Fin k → List (Fin n))
    (nodes : Fin t → Node n r k t) (i : Fin t) : Bool :=
  decide (nodes i).cells.Nodup && nodeBody ridges candidates allowed terminals nodes i

def check {k t : Nat} (ridges : Fin n → Fin r → Bool)
    (candidates : Fin r → List (Fin n))
    (allowed : List (Fin n) → Fin n → Bool) (terminals : Fin k → List (Fin n))
    (nodes : Fin t → Node n r k t) : Bool :=
  candidateCheck ridges candidates &&
    decide (∀ i, nodeCheck ridges candidates allowed terminals nodes i = true)

/-- The sparse implementation has the same universal, literal membership conclusion. -/
theorem check_complete {k t : Nat} (ridges : Fin n → Fin r → Bool)
    (candidates : Fin r → List (Fin n))
    (allowed : List (Fin n) → Fin n → Bool) (terminals : Fin k → List (Fin n))
    (nodes : Fin t → Node n r k t)
    (hcheck : check ridges candidates allowed terminals nodes = true)
    (B : Family n) (hmates : HasMate ridges B) (hthree : NoThree ridges B)
    (hconn : Connected ridges B) (hallowed : PreservesTarget allowed B)
    (root : Fin t) (hroot : Included (family (nodes root).cells) B)
    (hne : Nonempty (family (nodes root).cells)) :
    ∃ j, Same (family (terminals j)) B := by
  obtain ⟨hcoverage, hnodesBool⟩ := Bool.and_eq_true_iff.mp hcheck
  have hnodes : ∀ i, nodeCheck ridges candidates allowed terminals nodes i = true :=
    of_decide_eq_true hnodesBool
  have main : ∀ height : Nat, ∀ i : Fin t, i.val = height →
      Included (family (nodes i).cells) B → Nonempty (family (nodes i).cells) →
      ∃ j, Same (family (terminals j)) B := by
    intro height
    induction height using Nat.strongRecOn with
    | ind height ih =>
      intro i hi hsub hnonempty
      obtain ⟨hndBool, hbody⟩ := Bool.and_eq_true_iff.mp (hnodes i)
      have hnd : (nodes i).cells.Nodup := of_decide_eq_true hndBool
      cases ha : (nodes i).action with
      | terminal j =>
        have ht : sameCheck (nodes i).cells (terminals j) = true ∧
            closedCheck ridges (nodes i).cells = true :=
          Bool.and_eq_true_iff.mp (by simpa only [nodeBody, ha] using hbody)
        have hs := sameCheck_sound _ _ ht.1
        have heq := closed_eq_target ridges B (family (nodes i).cells)
          hsub hnonempty hthree hconn (closedCheck_sound _ _ ht.2)
        exact ⟨j, fun c => (hs c).symm.trans (heq c)⟩
      | split q a links =>
        have hs : openCheck ridges (nodes i).cells q a = true ∧
            (candidates q).all (fun c =>
              !eligible ridges allowed (nodes i).cells q c ||
                links.any (linkCheck nodes i c)) = true :=
          Bool.and_eq_true_iff.mp (by simpa only [nodeBody, ha] using hbody)
        obtain ⟨c, hcB, hcS, hcr⟩ := missing_cell ridges B (family (nodes i).cells)
          q a hsub hmates (openCheck_sound _ _ _ _ hs.1)
        change has (nodes i).cells c = false at hcS
        have hca := hallowed _ hsub hnd c hcB hcS
        have helig : eligible ridges allowed (nodes i).cells q c = true := by
          simp only [eligible, hcS, hcr, hca]
          rfl
        have hcand := candidateCheck_complete _ _ hcoverage q c hcr
        have hrow := List.all_eq_true.mp hs.2 c hcand
        have hlinkExists : links.any (linkCheck nodes i c) = true := by
          simpa only [helig, Bool.not_true, Bool.false_or] using hrow
        obtain ⟨link, _, hlink⟩ := List.any_eq_true.mp hlinkExists
        have hl := linkCheck_sound nodes i c link hlink
        have hchild : Included (family (nodes link.2).cells) B :=
          same_included hl.2.2 (add_included hsub hcB)
        have hchildne : Nonempty (family (nodes link.2).cells) :=
          same_nonempty hl.2.2 ⟨c, add_self _ _⟩
        exact ih link.2.val (hi ▸ hl.2.1) link.2 rfl hchild hchildne
  exact main root.val root rfl hroot hne

#print axioms check_complete

end Papers.RationalityTen.SparseGrowthDAG
