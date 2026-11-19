module
prelude
public import Init
public meta import RupProofTerm

@[expose] public section

namespace Papers.RationalityTen.RupProofTerm.Tests

theorem direct (p : Nat → Prop)
    (positive : (p 1 → False) → False) (negative : p 1 → False) : False :=
  rup_proof% p #[positive, negative]
    "p cnf 1 2\n1 0\n-1 0\n"
    "3 0 1 2 0\n"

theorem chain (p : Nat → Prop)
    (h1 : (p 1 → False) → False)
    (h2 : p 1 → (p 2 → False) → False)
    (h3 : p 2 → (p 3 → False) → False)
    (h4 : p 3 → False) : False :=
  rup_proof% p #[h1, h2, h3, h4]
    "p cnf 3 4\n1 0\n-1 2 0\n-2 3 0\n-3 0\n"
    "5 2 0 1 2 0\n6 0 5 3 4 0\n"

/-- A tautological learned clause is justified directly by its hypotheses. -/
theorem tautology (p : Nat → Prop)
    (positive : (p 1 → False) → False) (negative : p 1 → False) : False :=
  rup_proof% p #[positive, negative]
    "p cnf 1 2\n1 0\n-1 0\n"
    "3 1 -1 0 0\n4 0 1 2 0\n"

/-- Deleting a clause does not remove its already proved mathematical fact. -/
theorem deletion (p : Nat → Prop)
    (positive : (p 1 → False) → False) (negative : p 1 → False) : False :=
  rup_proof% p #[positive, negative]
    "p cnf 1 2\n1 0\n-1 0\n"
    "3 d 1 0\n4 0 1 2 0\n"

/-- error: LRAT step 2: propagation does not end in a conflict -/
#guard_msgs in
example (p : Nat → Prop) (positive : (p 1 → False) → False) : False :=
  rup_proof% p #[positive] "p cnf 1 1\n1 0\n" "2 0 1 0\n"

/-- error: LRAT step 2: unknown hint 99 -/
#guard_msgs in
example (p : Nat → Prop) (positive : (p 1 → False) → False) : False :=
  rup_proof% p #[positive] "p cnf 1 1\n1 0\n" "2 0 99 0\n"

/-- error: LRAT step 2: RAT hints are not supported -/
#guard_msgs in
example (p : Nat → Prop) (positive : (p 1 → False) → False) : False :=
  rup_proof% p #[positive] "p cnf 1 1\n1 0\n" "2 0 -1 0\n"

/-- error: DIMACS clause count or terminating zero does not match the header -/
#guard_msgs in
example (p : Nat → Prop) (positive : (p 1 → False) → False) : False :=
  rup_proof% p #[positive] "p cnf 1 2\n1 0\n" "2 0 1 0\n"

#print axioms direct
#print axioms chain
#print axioms tautology

end Papers.RationalityTen.RupProofTerm.Tests
