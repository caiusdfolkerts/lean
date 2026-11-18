module
public import SegreVerified.Stage025.ProjectiveCech
import all SegreVerified.Stage025.ProjectiveCech
public import SegreVerified.Stage025.ProjectiveSections
import all SegreVerified.Stage025.ProjectiveSections
public import SegreVerified.Stage025.ProjectiveSpace
import all SegreVerified.Stage025.ProjectiveSpace
public import SegreVerified.Stage025.Euler
import all SegreVerified.Stage025.Euler
public import SegreVerified.Stage025.ExteriorKernelCore
import all SegreVerified.Stage025.ExteriorKernelCore
public import SegreVerified.Stage025.ExteriorKernel
import all SegreVerified.Stage025.ExteriorKernel
public import SegreVerified.Stage025.ExteriorTwist
import all SegreVerified.Stage025.ExteriorTwist
public import SegreVerified.Stage025.ExteriorVanishing
import all SegreVerified.Stage025.ExteriorVanishing
public import SegreVerified.Stage025.AffineChartAlgebra
import all SegreVerified.Stage025.AffineChartAlgebra
public import SegreVerified.Stage025.ChartCoordinates
import all SegreVerified.Stage025.ChartCoordinates
public import SegreVerified.Stage025.EulerCoordinates
import all SegreVerified.Stage025.EulerCoordinates
import all Lean.Util.CollectAxioms

set_option Elab.async false
set_option linter.all false

#eval do
  let toolchain ← IO.FS.readFile "lean-toolchain"
  let manifest ← IO.FS.readFile "lake-manifest.json"
  IO.println ("SEGRE_PUBLIC_ENVIRONMENT_BEGIN\n" ++ Lean.versionString ++ "\n" ++
    Lean.githash ++ "\n" ++ toolchain.trimAscii.toString ++ "\n" ++ manifest ++
    "\nSEGRE_PUBLIC_ENVIRONMENT_END")

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  unless env.header.trustLevel == 0 do
    throwError "The retained source check requires kernel trust level zero"
  let imported := exportedAxiomsExt.getState (asyncMode := .mainOnly) env
  let rows := CollectAxioms.runM (env.setExporting false) do
    #[``Nat.add_comm, ``Nat.zero_add].mapM fun name =>
      return (name, ← CollectAxioms.collectAndGet imported.find? name)
  for (name, axioms) in rows do
    unless (env.checked.get.find? name).isSome do throwError "Unchecked smoke target: {name}"
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unapproved shared-collector smoke axiom: {ax}"
  logInfo "SEGRE_SHARED_COLLECTOR_READY"


set_option Elab.async false
set_option maxErrors 0
set_option maxRecDepth 2048
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-! Stage025 aggregate ownership audit.

This module publicly re-exports eleven ordinary Lean mathematical modules.
Their mathematical declarations keep their original public names. The audit
selects their actual defining modules, including private/generated declarations,
and requires each support to be present, imported with all bodies, and nonempty.
The native frontend independently audits only this module's own declarations;
the two scopes are reported separately and must not be confused in receipts.
-/

open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  unless env.header.trustLevel == 0 do
    throwError "The Stage025 aggregate audit requires kernel trust level zero"
  unless env.mainModule == `SegreVerified.Stage025 do
    throwError "Unexpected Stage025 aggregate module identity"
  let supportModules : Array Name := #[
    `SegreVerified.Stage025.ProjectiveCech,
    `SegreVerified.Stage025.ProjectiveSections,
    `SegreVerified.Stage025.ProjectiveSpace,
    `SegreVerified.Stage025.Euler,
    `SegreVerified.Stage025.ExteriorKernelCore,
    `SegreVerified.Stage025.ExteriorKernel,
    `SegreVerified.Stage025.ExteriorTwist,
    `SegreVerified.Stage025.ExteriorVanishing,
    `SegreVerified.Stage025.AffineChartAlgebra,
    `SegreVerified.Stage025.ChartCoordinates,
    `SegreVerified.Stage025.EulerCoordinates]
  let privateEnv := env.setExporting false
  let supportIndices ← supportModules.mapM fun support => do
    let some idx := privateEnv.getModuleIdx? support
      | throwError "Required Stage025 support is not imported: {support}"
    let some entry := privateEnv.header.modules[idx]?
      | throwError "Invalid Stage025 support module index: {support}"
    unless entry.importAll do
      throwError "Stage025 support lacks full private bodies: {support}"
    return idx.toNat
  let names := (privateEnv.checked.get.constants.fold
    (fun (names : Array Name) name _ =>
      let owned := match privateEnv.getModuleIdxFor? name with
        | none => true
        | some idx => supportIndices.contains idx.toNat
      if owned then names.push name else names) #[]).qsort Name.quickLt
  let currentNames := names.filter fun name =>
    (privateEnv.getModuleIdxFor? name).isNone
  let mut supportRows : Array Json := #[]
  let mut supportDeclarationCount := 0
  let mut supportTheoremCount := 0
  for index in [:supportModules.size] do
    let support := supportModules[index]!
    let moduleIndex := supportIndices[index]!
    let supportNames := names.filter fun name =>
      (privateEnv.getModuleIdxFor? name).any (fun idx => idx.toNat == moduleIndex)
    unless supportNames.size > 0 do
      throwError "Stage025 mathematical support is empty: {support}"
    let mut theoremCount := 0
    for name in supportNames do
      let some info := env.checked.get.find? name
        | throwError "Support declaration is not kernel checked: {name}"
      if let .thmInfo _ := info then theoremCount := theoremCount + 1
    supportDeclarationCount := supportDeclarationCount + supportNames.size
    supportTheoremCount := supportTheoremCount + theoremCount
    supportRows := supportRows.push (Json.mkObj [
      ("module", toJson support.toString),
      ("import_all", toJson true),
      ("declaration_count", toJson supportNames.size),
      ("theorem_count", toJson theoremCount)])
  unless names.size == currentNames.size + supportDeclarationCount do
    throwError "Stage025 aggregate ownership counts disagree"
  -- The complete direct-hole and transitive-axiom gates apply to the union.
  for name in names do
    let some info := env.checked.get.find? name
      | throwError "Authored declaration is not kernel checked: {name}"
    if let .axiomInfo _ := info then throwError "Authored axiom: {name}"
    if info.type.hasSorry || ((info.value? (allowOpaque := true)).any (·.hasSorry)) then
      throwError "Authored declaration contains a sorry expression: {name}"
  let importedAxioms := exportedAxiomsExt.getState (asyncMode := .mainOnly) env
  let axiomRows := CollectAxioms.runM privateEnv do
    names.mapM fun name =>
      return (name, ← CollectAxioms.collectAndGet importedAxioms.find? name)
  let mut theoremCount := 0
  for (name, axioms) in axiomRows do
    let some info := env.checked.get.find? name
      | throwError "Authored declaration is not kernel checked: {name}"
    if let .axiomInfo _ := info then throwError "Authored axiom: {name}"
    if info.type.hasSorry || ((info.value? (allowOpaque := true)).any (·.hasSorry)) then
      throwError "Authored declaration contains a sorry expression: {name}"
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unapproved transitive axiom in {name}: {ax}"
    if let .thmInfo _ := info then theoremCount := theoremCount + 1
  let mut currentTheoremCount := 0
  for name in currentNames do
    let some info := env.checked.get.find? name
      | throwError "Current declaration is not kernel checked: {name}"
    if let .thmInfo _ := info then currentTheoremCount := currentTheoremCount + 1
  unless theoremCount == currentTheoremCount + supportTheoremCount do
    throwError "Stage025 aggregate theorem counts disagree"
  let report := Json.mkObj [
    ("main_module", toJson env.mainModule.toString),
    ("declaration_count", toJson names.size),
    ("theorem_count", toJson theoremCount),
    ("current_module_declaration_count", toJson currentNames.size),
    ("current_module_theorem_count", toJson currentTheoremCount),
    ("support_modules", toJson supportRows),
    ("trust_level", toJson env.header.trustLevel.toNat),
    ("allowed_axioms", toJson #["propext", "Classical.choice", "Quot.sound"]),
    ("audit_scope", toJson "Stage025_current_and_exact_support_module_origins")]
  logInfo m!"SEGRE_STAGE_KERNEL_AUDIT_PASS {report.compress}"
