module
public meta import Lean.Elab.Command
public meta import Lean.Util.CollectAxioms

/-!
This development command serializes the ordinary checked Lean environment.
It never adds or changes a declaration. Each checkpoint records all declarations
created in the current module and checks their complete axiom dependencies.
Final theorem audits are independent of these development checkpoints.
-/

public meta section
open Lean Elab Command

elab "#checked_checkpoint " artifact:str " record " record:str : command => do
  let env := (← getEnv).setExporting false
  let names := env.checked.get.constants.foldStage2 (fun ns n _ => ns.push n) #[]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut used : NameSet := {}
  for n in names do
    let axioms ← collectAxioms n
    let rejected := axioms.filter (fun a => !allowed.contains a)
    unless rejected.isEmpty do
      throwError "Checkpoint rejected: {n} depends on unapproved axioms {rejected}"
    for a in axioms do
      used := used.insert a
  let path : System.FilePath := artifact.getString
  if let some parent := path.parent then
    liftIO <| IO.FS.createDirAll parent
  liftIO <| Lean.writeModule env path
  let report := Json.mkObj [
    ("module", toJson env.mainModule.toString),
    ("artifact", toJson artifact.getString),
    ("localDeclarations", toJson names.size),
    ("axioms", toJson (used.toArray.qsort Name.lt |>.map Name.toString)),
    ("method", toJson "Unmodified Lean.writeModule after checking all local declaration axioms.")]
  let reportPath : System.FilePath := record.getString
  if let some parent := reportPath.parent then
    liftIO <| IO.FS.createDirAll parent
  liftIO <| IO.FS.writeFile reportPath (report.pretty ++ "\n")
  logInfo m!"Checked checkpoint saved: {path}; {names.size} local declarations"
