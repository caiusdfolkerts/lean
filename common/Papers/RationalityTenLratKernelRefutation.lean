module

public import Mathlib.Tactic.Sat.FromLRAT

@[expose] public meta section

/-!
# Direct kernel proofs from literal CNF and LRAT certificates

Mathlib reconstructs each unit-propagation proof and
passes the resulting theorem declarations through Lean's kernel. This
command omits the optional enormous propositional reification theorem:
it exposes the original CNF formula and its empty-clause derivation.

Input strings are literal syntax. The command performs no runtime
evaluation of arbitrary source terms and introduces no new axiom.
A certificate refutation alone is still only a finite statement; actual
polytope-to-CNF semantics must be proved separately.
-/

open Lean Elab

/-- Given a base name, define `base.formula : Sat.Fmla` and
`base.refutation : base.formula.proof []`. -/
elab "kernel_lrat_refutation " n:ident cnf:str lrat:str : command => do
  let base := (← getCurrNamespace) ++ n.getId
  Command.liftTermElabM do
    let (_,ctx,_,proof) ← Mathlib.Tactic.Sat.fromLRATAux
      cnf.getString lrat.getString base
    let formulaName := base ++ `formula
    addDecl <| Declaration.defnDecl {
      name := formulaName
      levelParams := []
      type := mkConst ``Sat.Fmla
      value := ctx
      hints := ReducibilityHints.regular 0
      safety := DefinitionSafety.safe
    }
    addDecl <| Declaration.thmDecl {
      name := base ++ `refutation
      levelParams := []
      type := mkApp2 (mkConst ``Sat.Fmla.proof) (mkConst formulaName)
        (mkConst ``Sat.Clause.nil)
      value := proof
    }

namespace Papers.RationalityTen.LratKernelRefutation

kernel_lrat_refutation regression
  "p cnf 2 4\n1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n"
  "5 -2 0 4 3 0\n6 1 0 5 1 0\n7 0 5 2 6 0\n"

end Papers.RationalityTen.LratKernelRefutation
