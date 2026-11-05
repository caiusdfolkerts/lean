module
public meta import Lean.Elab.Command
public meta import Lean.Meta.Basic
public meta import Lean.PrettyPrinter
public meta import Lean.Util.CollectAxioms
public meta import Lean.Util.FoldConsts

/-!
# Read-only extraction of proof dependencies

This command is an audit tool. It reads the checked environment and writes
JSON; it never declares, proves, replaces, or assumes a mathematical result.
Lean's own `collectAxioms` supplies the transitive axiom list. The graph walks
local proof terms and stops at previously checked library constants. If an
imported local value was omitted from the environment, that omission is
recorded explicitly, and the graph is not labelled complete.
-/

public meta section

open Lean Meta Elab Command

namespace VerificationAudit

def origin (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!
  | none => env.mainModule

def projectModule (env : Environment) (n : Name) : Bool :=
  let m := origin env n
  m == env.mainModule || (`Papers).isPrefixOf m || (`Cubical).isPrefixOf m ||
    (`Verified).isPrefixOf m || (`Audit).isPrefixOf m || (`Consolidated).isPrefixOf m

def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient primitive"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def valueRequired : ConstantInfo → Bool
  -- Module export may represent an imported, already proved theorem by an
  -- axiom-shaped constant while retaining its genuine axiom cache. Such a
  -- project declaration has no proof body available for this graph walk.
  | .axiomInfo _ | .defnInfo _ | .thmInfo _ | .opaqueInfo _ => true
  | _ => false

partial def graph (env : Environment) (pending : List Name)
    (seen : NameSet := {}) (nodes : Array Json := #[]) : Array Json × Bool := Id.run do
  match pending with
  | [] => return (nodes, true)
  | n :: rest =>
    if seen.contains n then return graph env rest seen nodes
    let seen := seen.insert n
    let foundations : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
    let isProject := projectModule env n && !foundations.contains n
    match env.checked.get.find? n with
    | none =>
      let node := Json.mkObj [("name", toJson n.toString), ("missing", toJson true)]
      let (nodes, _) := graph env rest seen (nodes.push node)
      return (nodes, false)
    | some info =>
      let deps := if isProject then info.getUsedConstantsAsSet.toArray.qsort Name.lt else #[]
      let available := !valueRequired info || (info.value? (allowOpaque := true)).isSome
      let node := Json.mkObj [
        ("name", toJson n.toString),
        ("module", toJson (origin env n).toString),
        ("kind", toJson (kind info)),
        ("projectDeclaration", toJson isProject),
        ("valueAvailable", toJson available),
        ("dependencies", toJson (deps.map Name.toString))]
      let (nodes, complete) := graph env (deps.toList ++ rest) seen (nodes.push node)
      return (nodes, complete && (!isProject || available))

/-- Export a checked constant's type, transitive axioms, and available proof graph.
An axiom outside the three standard foundations causes a command error. -/
elab "#export_proof_audit " id:ident " to " path:str : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let info ← getConstInfo n
  let axioms ← collectAxioms n
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let rejected := axioms.filter (fun a => !allowed.contains a)
  unless rejected.isEmpty do
    throwError "Unapproved axioms in {n}: {rejected}"
  let env := (← getEnv).setExporting false
  let (nodes, complete) := graph env [n]
  let typeText ← liftTermElabM do return (← ppExpr info.type).pretty
  let expandedType ← liftTermElabM do return (← ppExpr (← whnf info.type)).pretty
  let output := Json.mkObj [
    ("theorem", toJson n.toString),
    ("type", toJson typeText),
    ("headUnfoldedType", toJson expandedType),
    ("axioms", toJson (axioms.qsort Name.lt |>.map Name.toString)),
    ("completeLocalValueGraph", toJson complete),
    ("boundary", toJson "Imported non-project constants are checked-library leaves."),
    ("nodes", Json.arr nodes)]
  let reportPath : System.FilePath := path.getString
  if let some parent := reportPath.parent then
    liftIO <| IO.FS.createDirAll parent
  liftIO <| IO.FS.writeFile reportPath (output.pretty ++ "\n")
  logInfo m!"Audit written for {n}; {nodes.size} constants; complete local values: {complete}"

end VerificationAudit
