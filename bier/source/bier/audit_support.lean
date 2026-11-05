import Lean.Elab.Command
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-! # Reproducible transitive proof audits

These elaborator commands inspect the checked Lean environment. They do
not introduce mathematical declarations or axioms. The axiom guard fails
if any audited result uses anything beyond Lean's three standard axioms.
-/

open Lean Elab Command

elab "audit_standard_axioms " n:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  let axs ← Lean.collectAxioms name
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for ax in axs do
    unless allowed.contains ax do
      throwError "Unapproved transitive axiom {ax} in {name}"
  logInfo m!"AXIOM AUDIT PASSED: {name}: {axs}"

private def dependencyModule (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => env.mainModule

private def isProjectModule (name : Name) : Bool :=
  let s := name.toString
  (s.startsWith "Bier." || s.startsWith "bier.") || (s == "Bier" || s == "bier") || (s.startsWith "Cubical." || s.startsWith "cubical.") || (s == "Cubical" || s == "cubical") ||
    (s.startsWith "DifferentialGeometry." || s.startsWith "differential_geometry.") || s.startsWith "LeanEval."

/-- Export the exact transitive declaration graph through every locally
proved module, stopping only at the pinned Lean/Mathlib library boundary. -/
elab "export_proof_dependencies " path:str "[" ns:ident,* "]" : command => do
  let roots ← ns.getElems.mapM fun n => liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  let env := (← getEnv).setExporting false
  let mut todo := roots
  let mut cursor := 0
  let mut seen : NameSet := {}
  let mut nodes : Array Json := #[]
  let mut rootInfo : Array Json := #[]
  for name in roots do
    let axs ← Lean.collectAxioms name
    let some info := env.checked.get.find? name | throwError "Missing checked root {name}"
    let ty ← liftTermElabM <| Meta.ppExpr info.type
    rootInfo := rootInfo.push <| Json.mkObj
      [("name", toJson name.toString), ("type", toJson ty.pretty),
       ("axioms", toJson (axs.map Name.toString))]
  while cursor < todo.size do
    let name := todo[cursor]!
    cursor := cursor + 1
    if seen.contains name then continue
    seen := seen.insert name
    let modName := dependencyModule env name
    let boundary := !isProjectModule modName
    let some info := env.checked.get.find? name | throwError "Missing checked dependency {name}"
    let deps := if boundary then #[] else info.getUsedConstantsAsSet.toArray.qsort Name.lt
    todo := todo ++ deps
    nodes := nodes.push <| Json.mkObj
      [("name", toJson name.toString), ("module", toJson modName.toString),
       ("library_boundary", toJson boundary), ("dependencies", toJson (deps.map Name.toString))]
  let document := Json.mkObj
    [("format", toJson "Lean checked-environment dependency graph, version 1"),
     ("boundary", toJson "All Bier, Cubical, and vendored DifferentialGeometry/LeanEval declarations are expanded; pinned Lean/Mathlib declarations are leaves."),
     ("roots", Json.arr rootInfo), ("nodes", Json.arr nodes)]
  let target : System.FilePath := path.getString
  if let some parent := target.parent then liftIO <| IO.FS.createDirAll parent
  liftIO <| IO.FS.writeFile target (document.pretty ++ "\n")
  logInfo m!"DEPENDENCY GRAPH: {nodes.size} checked declarations written to {path.getString}"
