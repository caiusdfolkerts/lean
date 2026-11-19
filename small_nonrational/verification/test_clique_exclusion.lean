module
prelude
public import CliqueExclusion

@[expose] public section

namespace Papers.RationalityTen.CliqueExclusion.Tests

def cycle5 (a b : Fin 5) : Bool :=
  decide ((a.val + 1) % 5 = b.val ∨ (b.val + 1) % 5 = a.val)

/-- An odd cycle needs a branch before the two-color leaves suffice. -/
def oddCycleCertificate : Certificate 5 :=
  .split ⟨0, by decide⟩ (.color 2 1 20) (.color 1 1 0)

example : check cycle5 (List.finRange 5) 3 oddCycleCertificate = true := by decide

example (vertices : List (Fin 5)) (h : Clique cycle5 vertices) : vertices.length < 3 :=
  check_sound cycle5 (List.finRange 5) 3 oddCycleCertificate (by decide)
    vertices h (fun _ _ => List.mem_finRange _)

/-- A false coloring and a non-strict target bound are both rejected. -/
example : check cycle5 (List.finRange 5) 3 (.color 1 1 0) = false := by decide
example : check cycle5 (List.finRange 5) 3 (.color 3 2 292) = false := by decide

/-- Explicit masks check both independent classes and complete coverage. -/
example : check cycle5 [1, 2, 3, 4] 3 (.classes [10, 20]) = true := by decide
example : check cycle5 [1, 2, 3, 4] 3 (.classes [2, 20]) = false := by decide
example : check cycle5 [1, 2, 3, 4] 2 (.classes [30]) = false := by decide

/-- Diagonal relation entries do not affect a clique of distinct vertices. -/
example : check (fun _ _ : Fin 1 => true) [0] 2 (.color 1 1 0) = true := by decide

/-- Duplicate candidates are harmless: the theorem requires distinct selected vertices. -/
example : check (fun _ _ : Fin 1 => true) [0, 0] 3 .size = true := by decide

def mixedRelation (a b : Fin 4) : Bool :=
  let rows := [6, 9, 9, 6]
  (rows.getD a.val 0).testBit b.val

def mixedKind (vertex : Fin 4) : Nat := if vertex.val < 2 then 0 else 1

def mixedQuota (key : Nat) : Nat := if key = 0 then 2 else if key = 1 then 1 else 0

/-- Each individual kind has enough vertices, but the joint requirements fail. -/
def mixedCertificate : QuotaCertificate 4 :=
  .split ⟨1, by decide⟩ (.size 0)
    (.split ⟨0, by decide⟩ (.size 0) (.size 1))

example : checkQuotas mixedRelation mixedKind (List.finRange 4)
    mixedQuota mixedCertificate = true := by decide

example (vertices : List (Fin 4)) (h : Clique mixedRelation vertices)
    (hq : ∀ key, mixedQuota key ≤ (ofKind mixedKind key vertices).length) : False :=
  checkQuotas_sound mixedRelation mixedKind (List.finRange 4) mixedQuota
    mixedCertificate (by decide) vertices h (fun _ _ => List.mem_finRange _) hq

/-- A branch cannot falsely remove a requirement for a different kind. -/
example : checkQuotas mixedRelation mixedKind (List.finRange 4)
    (fun key => if key = 1 then 1 else 0) mixedCertificate = false := by decide

end Papers.RationalityTen.CliqueExclusion.Tests
