module

public meta import Audit.Print

/-! # Read-only audit of multiple principal theorems

The proof graph is shared between roots to avoid repeating common dependencies.
Every root has its own exact type and transitive axiom list. The graph includes
all local proof values reachable from any root, with the same checked-library
boundary as `Audit.Print`.
-/

public meta section
open Lean Meta Elab Command
namespace VerificationPrintAudit

elab "#print_proof_audit_bundle " "[" ids:ident,* "]" : command => do
  let mut names : Array Name := #[]
  let mut roots : Array Json := #[]
  for id in ids.getElems do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    if names.contains n then
      throwError "Duplicate audit root: {n}"
    names := names.push n
    let info ← getConstInfo n
    let axioms ← collectAxioms n
    let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
    let rejected := axioms.filter (fun a => !allowed.contains a)
    unless rejected.isEmpty do
      throwError "Unapproved axioms in {n}: {rejected}"
    let typeText ← liftTermElabM do return (← ppExpr info.type).pretty
    let expandedType ← liftTermElabM do return (← ppExpr (← whnf info.type)).pretty
    roots := roots.push <| Json.mkObj [
      ("theorem", toJson n.toString),
      ("type", toJson typeText),
      ("headUnfoldedType", toJson expandedType),
      ("axioms", toJson (axioms.qsort Name.lt |>.map Name.toString))]
  unless !names.isEmpty do
    throwError "The principal audit needs at least one theorem."
  let env := (← getEnv).setExporting false
  let (nodes, complete) := graph env names.toList
  let output := Json.mkObj [
    ("roots", Json.arr roots),
    ("completeLocalValueGraph", toJson complete),
    ("boundary", toJson "Imported non-project constants are checked-library leaves."),
    ("nodes", Json.arr nodes)]
  logInfo m!"PROOF_AUDIT_BUNDLE_JSON {output.compress}"

end VerificationPrintAudit
