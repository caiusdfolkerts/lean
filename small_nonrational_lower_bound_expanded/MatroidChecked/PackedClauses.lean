module
public import Mathlib.Tactic.Sat.FromLRAT

@[expose] public section

/-!
# A compact literal representation of the already checked CNF formulas

Each literal occupies one base-256 digit: `2*i` means the negative
literal with zero-based index `i`; `2*i+1` means the positive literal.
The recorded clause length preserves leading zero digits. No semantic
claim is inferred from an encoder: each public refutation adapter proves
that its decoded formula is definitionally equal to the original formula.
-/

namespace Papers.RationalityTen.MatroidChecked.PackedClauses

noncomputable def literal (b : ℕ) : Sat.Literal :=
  if b % 2 = 0 then .neg (b / 2) else .pos (b / 2)

noncomputable def clause : ℕ → ℕ → Sat.Clause
  | 0, _ => []
  | n + 1, code => literal (code % 256) :: clause n (code / 256)

noncomputable def formula (data : List (ℕ × ℕ)) : Sat.Fmla :=
  data.map fun p => clause p.1 p.2

end Papers.RationalityTen.MatroidChecked.PackedClauses
