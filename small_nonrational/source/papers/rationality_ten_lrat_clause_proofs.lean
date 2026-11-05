module

public import Mathlib.Tactic.Sat.FromLRAT

@[expose] public meta section

/-!
# LRAT refutations with separately checked clause proofs

This command uses Mathlib's literal parsers and `buildProofStep`. Intermediate
clause proofs are submitted to the ordinary kernel whenever their dependency
depth reaches eight; later steps refer to the resulting checked theorem.
These proof boundaries bound the size of each kernel check without repeating
the full context check at every LRAT line. They change neither the input formula
nor the inference rules.

The exported interface is the same as `kernel_lrat_refutation`:
`base.formula : Sat.Fmla` and `base.refutation : base.formula.proof []`.
Inputs are literal syntax, with no external file or evaluated source term.
-/

open Lean Elab
open Std.Internal

namespace Papers.RationalityTen.LratClauseProofs

def checkedRefutation (cnf lrat : String) (base : Name) : MetaM (Expr × Expr) := do
  let Parsec.ParseResult.success _ (_, clauses) :=
      Mathlib.Tactic.Sat.Parser.parseDimacs ⟨_, cnf.startPos⟩
    | throwError "parse CNF failed"
  if clauses.isEmpty then
    throwError "empty CNF"
  let expanded := Mathlib.Tactic.Sat.buildConj clauses 0 clauses.size
  let contextName ← mkAuxDeclName (base ++ `ctx)
  addDecl <| Declaration.defnDecl {
    name := contextName
    levelParams := []
    type := mkConst ``Sat.Fmla
    value := expanded
    hints := ReducibilityHints.regular 0
    safety := DefinitionSafety.safe
  }
  let context := mkConst contextName
  let finalName ← mkAuxDeclName (base ++ `proof)
  let Parsec.ParseResult.success _ steps :=
      Mathlib.Tactic.Sat.Parser.parseLRAT ⟨_, lrat.startPos⟩
    | throwError "parse LRAT failed"
  let initialProof := mkApp (mkConst ``Sat.Fmla.subsumes_self) context
  let mut database :=
    (Mathlib.Tactic.Sat.buildClauses clauses context 0 clauses.size
      expanded initialProof default).2
  let mut depths : Std.HashMap Nat Nat := {}
  let mut checkedSteps := 0
  let mut boundaries := 0
  for step in steps do
    match step with
    | Mathlib.Tactic.Sat.LRATStep.del ids =>
      database := ids.foldl (fun db i => db.erase i) database
      depths := ids.foldl (fun ds i => ds.erase i) depths
    | Mathlib.Tactic.Sat.LRATStep.add i literals hints =>
      let clause := Mathlib.Tactic.Sat.buildClause literals
      let proof ← match Mathlib.Tactic.Sat.buildProofStep database literals hints context clause with
        | .ok proof => pure proof
        | .error message => throwError message
      let depth := 1 + hints.foldl (fun depth i => max depth (depths[i.natAbs]?.getD 0)) 0
      let (proof, depth) ← if literals.isEmpty || depth ≥ 8 then do
        let proofName ← if literals.isEmpty then pure finalName
          else mkAuxDeclName (base ++ `clause)
        addDecl <| Declaration.thmDecl {
          name := proofName
          levelParams := []
          type := mkApp2 (mkConst ``Sat.Fmla.proof) context clause
          value := proof
        }
        boundaries := boundaries + 1
        pure (mkConst proofName, 0)
      else pure (proof, depth)
      checkedSteps := checkedSteps + 1
      if checkedSteps % 256 == 0 || literals.isEmpty then
        IO.println s!"[LRAT] {checkedSteps} steps, {boundaries} checked proof boundaries"
      if literals.isEmpty then
        return (context, proof)
      database := database.insert i {
        lits := literals
        expr := clause
        proof
      }
      depths := depths.insert i depth
  throwError "failed to prove empty clause"

elab "kernel_lrat_clause_refutation " n:ident cnf:str lrat:str : command => do
  if (← getEnv).header.trustLevel > 1 then
    throwError "LRAT reconstruction requires ordinary kernel checking"
  if (← getOptions).getBool `debug.skipKernelTC false then
    throwError "LRAT reconstruction requires debug.skipKernelTC=false"
  let base := (← getCurrNamespace) ++ n.getId
  Command.liftTermElabM do
    let (context, proof) ← checkedRefutation cnf.getString lrat.getString base
    let formulaName := base ++ `formula
    addDecl <| Declaration.defnDecl {
      name := formulaName
      levelParams := []
      type := mkConst ``Sat.Fmla
      value := context
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

kernel_lrat_clause_refutation regression
  "p cnf 2 4\n1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n"
  "5 -2 0 4 3 0\n6 1 0 5 1 0\n7 0 5 2 6 0\n"

#print axioms regression.refutation

end Papers.RationalityTen.LratClauseProofs
