module
import all paper_statements
public import complete_verification
public import Lean.Util.CollectAxioms

-- Generated verification output directories.
run_cmd Lean.Elab.Command.liftIO do
  IO.FS.createDirAll ".lake/reports/audit"


/-!
# Proof-value and axiom audit for the paper statement reader

The reader's declarations are selected by their actual defining-module index.
`import all` makes their checked proof values available to the ordinary
environment inspector. Missing values and public-interface axiom stubs are
errors, not empty dependency graphs. No environment is replaced and no
mathematical declaration is added by this audit.

The emitted graph has the same schema as the foundation and extension audits.
Its source identity and successful compiler receipt are recorded separately.
-/

set_option autoImplicit false

open Lean Elab Command in
set_option maxHeartbeats 8000000 in
run_cmd do
  let env := (← getEnv).setExporting false
  let selected : Array Name := #[`paper_statements]
  let definingModule? (name : Name) : Option Name := do
    let idx ← env.getModuleIdxFor? name
    return env.header.modules[idx]!.module
  let constants := (env.constants.fold (init := #[]) fun acc name ci =>
    if (definingModule? name).any selected.contains then acc.push (name, ci)
    else acc : Array (Name × ConstantInfo)).qsort (fun a b => Name.lt a.1 b.1)
  for modName in selected do
    unless constants.any (fun (name, _) => definingModule? name == some modName) do
      throwError "No imported declarations found for reader module {modName}"
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut runtime : Array Name := #[]
  let mut roots : Array Name := #[]
  let mut rootAxioms : Array Json := #[]
  for (name, ci) in constants do
    if ci.isAxiom then
      throwError "Unapproved axiom or public-interface stub in reader module: {name}"
    if ci.isTheorem && (ci.value? true).isNone then
      throwError "Imported reader theorem lacks its checked proof value: {name}"
    if ci.isUnsafe || ci.isPartial then
      unless name.getString! == "_unsafe_rec" do
        throwError "Authored or unrecognized unsafe reader declaration: {name}"
      let some parent := env.find? name.getPrefix
        | throwError "Runtime companion lacks its safe defining declaration: {name}"
      if parent.isUnsafe || parent.isPartial || parent.isAxiom then
        throwError "Runtime companion has an unsafe or stub defining declaration: {name}"
      unless definingModule? name.getPrefix == definingModule? name do
        throwError "Runtime companion and parent have different defining modules: {name}"
      runtime := runtime.push name
      logInfo m!"COMPILER_RUNTIME_ONLY {name}"
    else
      let deps := ci.type.getUsedConstants ++
        ((ci.value? true).map Expr.getUsedConstants |>.getD #[])
      for dep in deps do
        let some info := env.find? dep
          | throwError "Proof dependency unavailable in inspection environment: {dep} in {name}"
        if info.isUnsafe || info.isPartial then
          throwError "Unsafe proof dependency {dep} in safe reader declaration {name}"
        if dep == `sorryAx || dep == `Lean.ofReduceBool || dep == `Lean.trustCompiler then
          throwError "Unapproved proof dependency {dep} in {name}"
      let axs ← collectAxioms name
      for ax in axs do
        unless allowed.contains ax do
          throwError "Unapproved transitive axiom {ax} in {name}"
      roots := roots.push name
      rootAxioms := rootAxioms.push <| Json.mkObj [
        ("theorem", toJson name.toString),
        ("axioms", toJson (axs.map Name.toString))]
  let ctors (ci : ConstantInfo) : Array Name :=
    match ci with
    | .inductInfo v => v.ctors.toArray
    | _ => #[]
  let mut names : NameSet := {}
  for (name, ci) in constants do
    names := names.insert name
    for dep in ci.type.getUsedConstants do names := names.insert dep
    for dep in (ci.value? true).map Expr.getUsedConstants |>.getD #[] do
      names := names.insert dep
    for dep in ctors ci do names := names.insert dep
  let dictionary := names.toArray.qsort Name.lt
  let mut indices : NameMap Nat := {}
  for i in [:dictionary.size] do indices := indices.insert dictionary[i]! i
  let index (name : Name) := (indices.find? name).getD 0
  let data := constants.map fun (name, ci) =>
    Json.arr #[toJson (index name), toJson (ci.type.getUsedConstants.map index),
      toJson (((ci.value? true).map Expr.getUsedConstants |>.getD #[]).map index),
      toJson ((ctors ci).map index), toJson ci.isAxiom, toJson ci.isUnsafe,
      toJson ci.isPartial]
  let ownership := constants.map fun (name, _) =>
    (definingModule? name).getD .anonymous |>.toString
  let boundaryOwnership := dictionary.map fun name => Json.arr #[
    toJson (index name), toJson ((definingModule? name).map Name.toString)]
  let graph := Json.mkObj [
    ("format", toJson "local-proof-dag-v1"),
    ("scope", toJson "paper-reader-proof-value-extraction"),
    ("extraction", toJson "checked-imported-proof-values-v1"),
    ("columns", toJson (#["name", "type", "value", "inductiveCtors",
      "axiom", "unsafe", "partial"] : Array String)),
    ("names", toJson (dictionary.map Name.toString)),
    ("nodes", Json.arr data),
    ("node_modules", toJson ownership),
    ("source_modules", toJson (selected.map Name.toString)),
    ("constant_modules", Json.arr boundaryOwnership),
    ("roots", toJson (roots.map index)),
    ("root_axioms", Json.arr rootAxioms),
    ("compiler_runtime_only", toJson (runtime.map Name.toString))]
  liftIO <| IO.FS.createDirAll ".lake/reports/audit"
  liftIO <| IO.FS.writeFile ".lake/reports/audit/reader_dependency_graph.json" (Json.compress graph)
  logInfo m!"DEPENDENCY_GRAPH {Json.compress graph}"
  logInfo m!"READER_DEPENDENCY_AUDIT_OK {constants.size} imported declarations; actual reader proof values; only propext, Classical.choice, Quot.sound; no environment mutation or new mathematical assertions."

/- Direct axiom receipts for the six additional paper-inventory endpoints
whose proof values are present in the corresponding full module graphs but
were not reached from the original final endpoint list. -/
#print axioms FourPapers.Symmetric.MatchingChains.median_rowChainMax_eq
#print axioms FourPapers.Symmetric.MatchingChains.median_packingMax_eq
#print axioms FourPapers.Symmetric.northwestAntidiagonalIdeal_colon_pivot
#print axioms FourPapers.Symmetric.JointSagbi.minorGenerators_finite
#print axioms FourPapers.Symmetric.JointSagbi.determinantGenerators_finite
#print axioms FourPapers.Symmetric.SagbiObstruction.obstruction_all_parameters
