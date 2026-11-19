module
public meta import Lean.Elab.Term
public meta import Lean.Meta.AppBuilder
public meta section
open Lean Elab Term
syntax (name := compactDecisionProof) "compact_decision_proof" : term
@[term_elab compactDecisionProof] def elabCompactDecisionProof : TermElab := fun _ expected => do
  let some p := expected | throwError "a decidable proposition is required"
  Lean.Meta.mkDecideProof p
