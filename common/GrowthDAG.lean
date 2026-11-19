module
prelude
public import Init.Data.Nat.Lemmas
public import Init.Data.List.Lemmas
public import Init.WF
public import Init.ByCases
public import Init.Omega

@[expose] public section

/-!+# Complete boundary growth with shared subproofs

This module checks a finite, topologically ordered search DAG.  Its conclusion
is a literal catalogue-membership statement: every paired, connected boundary
which extends the initial family occurs among the terminal families.

A branch lists an earlier child for **every** admissible facet incident to its
chosen open ridge.  The checker verifies the actual child family, not a hash.
Strictly decreasing node indices prevent circular certificates.  A terminal
node must be closed and must equal its stated catalogue entry.

This is a finite-combinatorial theorem.  A geometric application must prove
that its actual facets belong to the supplied cell universe, that its ridge
incidences are paired and connected, and that each pruning rule is necessary.
No realization, rationality, or catalogue-completeness assertion is assumed
inside the checker.
-/

namespace Papers.RationalityTen.GrowthDAG

/-- A finite family of cells, represented without an order or duplicate entries. -/
abbrev Family (n : Nat) := Fin n → Bool

def Included {n : Nat} (S B : Family n) : Prop :=
  ∀ c, S c = true → B c = true

def Nonempty {n : Nat} (S : Family n) : Prop :=
  ∃ c, S c = true

/-- Pointwise equality keeps the executable checker independent of function equality. -/
def Same {n : Nat} (S T : Family n) : Prop :=
  ∀ c, S c = T c

instance {n : Nat} (S T : Family n) : Decidable (Same S T) :=
  inferInstanceAs (Decidable (∀ c, S c = T c))

def add {n : Nat} (S : Family n) (c : Fin n) : Family n :=
  fun d => if d = c then true else S d

@[simp] theorem add_self {n : Nat} (S : Family n) (c : Fin n) :
    add S c c = true := by simp [add]

theorem add_included {n : Nat} {S B : Family n} {c : Fin n}
    (hS : Included S B) (hc : B c = true) : Included (add S c) B := by
  intro d hd
  by_cases hdc : d = c
  · subst d
    exact hc
  · exact hS d (by simpa only [add, ite_eq_right hdc] using hd)

theorem same_included {n : Nat} {S T B : Family n}
    (hST : Same S T) (hT : Included T B) : Included S B := by
  intro c hc
  exact hT c ((hST c).symm.trans hc)

theorem same_nonempty {n : Nat} {S T : Family n}
    (hST : Same S T) (hT : Nonempty T) : Nonempty S := by
  obtain ⟨c, hc⟩ := hT
  exact ⟨c, (hST c).trans hc⟩

variable {n r : Nat}

/-- `ridges c q` says that ridge `q` occurs in cell `c`. -/
def Incident (ridges : Fin n → Fin r → Bool) (S : Family n)
    (q : Fin r) (c : Fin n) : Prop :=
  S c = true ∧ ridges c q = true

/-- A supplied witness makes checking an open ridge linear in the cell universe. -/
def OpenAt (ridges : Fin n → Fin r → Bool) (S : Family n)
    (q : Fin r) (a : Fin n) : Prop :=
  Incident ridges S q a ∧ ∀ c, Incident ridges S q c → c = a

instance (ridges : Fin n → Fin r → Bool) (S : Family n)
    (q : Fin r) (a : Fin n) : Decidable (OpenAt ridges S q a) :=
  inferInstanceAs (Decidable
    ((S a = true ∧ ridges a q = true) ∧
      ∀ c, (S c = true ∧ ridges c q = true) → c = a))

/-- Every occurring ridge has a second incident cell. -/
def HasMate (ridges : Fin n → Fin r → Bool) (B : Family n) : Prop :=
  ∀ q a, Incident ridges B q a →
    ∃ b, Incident ridges B q b ∧ b ≠ a

/-- No ridge has three distinct incident cells. -/
def NoThree (ridges : Fin n → Fin r → Bool) (B : Family n) : Prop :=
  ∀ q a b c, Incident ridges B q a → Incident ridges B q b →
    Incident ridges B q c → a = b ∨ a = c ∨ b = c

/-- Connectedness in the form used by rooted facet growth. -/
def Connected (ridges : Fin n → Fin r → Bool) (B : Family n) : Prop :=
  ∀ S, Included S B → Nonempty S → ¬ Same S B →
    ∃ q a b, Incident ridges S q a ∧ Incident ridges B q b ∧ S b = false

def Closed (ridges : Fin n → Fin r → Bool) (S : Family n) : Prop :=
  HasMate ridges S

instance (ridges : Fin n → Fin r → Bool) (S : Family n) :
    Decidable (Closed ridges S) :=
  inferInstanceAs (Decidable
    (∀ q a, (S a = true ∧ ridges a q = true) →
      ∃ b, (S b = true ∧ ridges b q = true) ∧ b ≠ a))

/-- In a paired connected boundary, a nonempty closed subfamily is the whole boundary. -/
theorem closed_eq_target (ridges : Fin n → Fin r → Bool) (B S : Family n)
    (hsub : Included S B) (hne : Nonempty S)
    (hthree : NoThree ridges B) (hconn : Connected ridges B)
    (hclosed : Closed ridges S) : Same S B := by
  by_cases heq : Same S B
  · exact heq
  · obtain ⟨q, a, b, ha, hb, hbS⟩ := hconn S hsub hne heq
    obtain ⟨c, hc, hca⟩ := hclosed q a ha
    have haB : Incident ridges B q a := ⟨hsub a ha.1, ha.2⟩
    have hcB : Incident ridges B q c := ⟨hsub c hc.1, hc.2⟩
    rcases hthree q a b c haB hb hcB with hab | hac | hbc
    · subst b
      exact False.elim (Bool.noConfusion (ha.1.symm.trans hbS))
    · exact False.elim (hca hac.symm)
    · subst c
      exact False.elim (Bool.noConfusion (hc.1.symm.trans hbS))

/-- The missing mate is an actual next facet of the target boundary. -/
theorem missing_cell (ridges : Fin n → Fin r → Bool) (B S : Family n)
    (q : Fin r) (a : Fin n) (hsub : Included S B)
    (hmates : HasMate ridges B) (hopen : OpenAt ridges S q a) :
    ∃ c, B c = true ∧ S c = false ∧ ridges c q = true := by
  have haB : Incident ridges B q a := ⟨hsub a hopen.1.1, hopen.1.2⟩
  obtain ⟨c, hc, hca⟩ := hmates q a haB
  have hcS : S c = false := by
    cases hval : S c with
    | false => rfl
    | true => exact False.elim (hca (hopen.2 c ⟨hval, hc.2⟩))
  exact ⟨c, hc.1, hcS, hc.2⟩

/-- The admissibility filter may prune only extensions that no target can use. -/
def PreservesTarget (allowed : Family n → Fin n → Bool) (B : Family n) : Prop :=
  ∀ S, Included S B → ∀ c, B c = true → S c = false → allowed S c = true

def Eligible (ridges : Fin n → Fin r → Bool)
    (allowed : Family n → Fin n → Bool) (S : Family n)
    (q : Fin r) (c : Fin n) : Prop :=
  S c = false ∧ ridges c q = true ∧ allowed S c = true

instance (ridges : Fin n → Fin r → Bool)
    (allowed : Family n → Fin n → Bool) (S : Family n)
    (q : Fin r) (c : Fin n) : Decidable (Eligible ridges allowed S q c) :=
  inferInstanceAs (Decidable
    (S c = false ∧ ridges c q = true ∧ allowed S c = true))

/-- Child references carry the attached cell and the earlier node index. -/
inductive Action (n r k t : Nat) where
  | terminal (entry : Fin k)
  | split (ridge : Fin r) (witness : Fin n) (children : List (Fin n × Fin t))

structure Node (n r k t : Nat) where
  family : Family n
  action : Action n r k t

/-- A reference is valid only if it points backwards and its exact family is correct. -/
def linkCheck {k t : Nat} (nodes : Fin t → Node n r k t)
    (parent : Fin t) (cell : Fin n) (link : Fin n × Fin t) : Bool :=
  decide (link.1 = cell ∧ link.2.val < parent.val ∧
    Same (nodes link.2).family (add (nodes parent).family cell))

/-- No promise made by the external search program enters this predicate. -/
def nodeCheck {k t : Nat} (ridges : Fin n → Fin r → Bool)
    (allowed : Family n → Fin n → Bool) (terminals : Fin k → Family n)
    (nodes : Fin t → Node n r k t) (i : Fin t) : Bool :=
  match (nodes i).action with
  | .terminal j =>
      decide (Same (nodes i).family (terminals j) ∧ Closed ridges (nodes i).family)
  | .split q a links =>
      decide (OpenAt ridges (nodes i).family q a ∧
        ∀ c, Eligible ridges allowed (nodes i).family q c →
          links.any (linkCheck nodes i c) = true)

def check {k t : Nat} (ridges : Fin n → Fin r → Bool)
    (allowed : Family n → Fin n → Bool) (terminals : Fin k → Family n)
    (nodes : Fin t → Node n r k t) : Bool :=
  decide (∀ i, nodeCheck ridges allowed terminals nodes i = true)

/-- A checked search DAG exhausts every target boundary extending its root.

The conclusion gives an actual terminal index and equality of cell families.
It does not assume that the listed terminal families already cover the target.
-/
theorem check_complete {k t : Nat} (ridges : Fin n → Fin r → Bool)
    (allowed : Family n → Fin n → Bool) (terminals : Fin k → Family n)
    (nodes : Fin t → Node n r k t) (hcheck : check ridges allowed terminals nodes = true)
    (B : Family n) (hmates : HasMate ridges B) (hthree : NoThree ridges B)
    (hconn : Connected ridges B) (hallowed : PreservesTarget allowed B)
    (root : Fin t) (hroot : Included (nodes root).family B)
    (hne : Nonempty (nodes root).family) :
    ∃ j, Same (terminals j) B := by
  have hnodes : ∀ i, nodeCheck ridges allowed terminals nodes i = true :=
    of_decide_eq_true hcheck
  have main : ∀ height : Nat, ∀ i : Fin t, i.val = height →
      Included (nodes i).family B → Nonempty (nodes i).family →
      ∃ j, Same (terminals j) B := by
    intro height
    induction height using Nat.strongRecOn with
    | ind height ih =>
      intro i hi hsub hnonempty
      cases ha : (nodes i).action with
      | terminal j =>
        have ht : Same (nodes i).family (terminals j) ∧
            Closed ridges (nodes i).family :=
          of_decide_eq_true (by simpa only [nodeCheck, ha] using hnodes i)
        have heq := closed_eq_target ridges B (nodes i).family
          hsub hnonempty hthree hconn ht.2
        exact ⟨j, fun c => (ht.1 c).symm.trans (heq c)⟩
      | split q a links =>
        have hs : OpenAt ridges (nodes i).family q a ∧
            ∀ c, Eligible ridges allowed (nodes i).family q c →
              links.any (linkCheck nodes i c) = true :=
          of_decide_eq_true (by simpa only [nodeCheck, ha] using hnodes i)
        obtain ⟨c, hcB, hcS, hcr⟩ :=
          missing_cell ridges B (nodes i).family q a hsub hmates hs.1
        have helig : Eligible ridges allowed (nodes i).family q c :=
          ⟨hcS, hcr, hallowed _ hsub c hcB hcS⟩
        obtain ⟨link, _, hlink⟩ := List.any_eq_true.mp (hs.2 c helig)
        have hl : link.1 = c ∧ link.2.val < i.val ∧
            Same (nodes link.2).family (add (nodes i).family c) :=
          of_decide_eq_true hlink
        have hchild : Included (nodes link.2).family B :=
          same_included hl.2.2 (add_included hsub hcB)
        have hchildne : Nonempty (nodes link.2).family :=
          same_nonempty hl.2.2 ⟨c, add_self _ _⟩
        exact ih link.2.val (hi ▸ hl.2.1) link.2 rfl hchild hchildne
  exact main root.val root rfl hroot hne

#print axioms closed_eq_target
#print axioms missing_cell
#print axioms check_complete

end Papers.RationalityTen.GrowthDAG
