module
public import volume_polynomials
import all volume_polynomials
/- BEGIN GENERATED PROJECT PRIVATE IMPORTS -/
import all volume_polynomials.all
/- END GENERATED PROJECT PRIVATE IMPORTS -/
public meta import Lean.Elab.Command
public meta import Lean.Util.CollectAxioms
public meta import Lean.Util.FoldConsts
public meta import Lean.Meta.Basic
public meta import Lean.Meta.RecExt
public meta import Lean.Compiler.Old
public meta import Lean.Data.Json

-- Generated verification output directories.
run_cmd Lean.Elab.Command.liftIO do
  IO.FS.createDirAll ".lake/reports/audit"


/-!
# Final public-principal and actual private-declaration audit

The generated import block is layout specific. The canonical release imports all
of `volume_polynomials.all`; the ordinary original-module preparation imports all
of every frozen project and vendored source. Missing private data is an error.

Required principal types are inspected in the public environment. Every stored
private project declaration is also audited, including private proofs and the
actual compiler recursion companions. A public unsafe signature is never accepted
from its spelling: classification requires the actual private definition, its
same-module safe parent, Lean's recursive-definition tag, and exact type,
universe and mutual-definition metadata. No safe logical declaration may refer
to a classified runtime companion. Authored unsafe/partial definitions and
unapproved axioms remain forbidden.

Lean 4.36 exports proved theorem signatures as opaque axiom-shaped constants;
Lean's official `collectAxioms` uses their exported proved-dependency metadata.
The stored private proof bodies are checked independently below so this public
representation cannot be confused with a newly assumed axiom. This audit is a
supplement to the complete ordinary build and original-source ownership audit,
not a replacement for either gate.
-/

set_option Elab.async false

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let privateEnv := env.setExporting false
  let publicEnv := env.setExporting true
  let required : Array Name := #[
    `VolumePolynomials.Main.semialgebraicity_iff,
    `VolumePolynomials.Main.polytope_locus_not_semialgebraic,
    `VolumePolynomials.Main.shape_forcing,
    `VolumePolynomials.Main.countable_characterization,
    `VolumePolynomials.Main.nonrealizable_strict_inequality,
    `VolumePolynomials.Main.finite_rational_certificate,
    `VolumePolynomials.Main.rational_rejection_terminates,
    `VolumePolynomials.Main.rational_polytope_reconstruction]
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut statements : Array Json := #[]
  for name in required do
    unless publicEnv.contains name do
      throwError "Required principal theorem is absent: {name}"
    let some info := publicEnv.find? name
      | throwError "Required principal declaration cannot be inspected: {name}"
    unless (← liftTermElabM <| Meta.isProp info.type) do
      throwError "Required entry point is not a proof of a proposition: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unapproved axiom {ax} occurs in required principal theorem {name}"
    let prettyType ← liftTermElabM <| Meta.ppExpr info.type
    statements := statements.push (Json.mkObj [
      ("name", toJson name.toString),
      ("type", toJson prettyType.pretty),
      ("axioms", toJson (axioms.map Name.toString)),
      ("complete_type_expression", toJson (reprStr info.type))])
  let originalModules := env.header.moduleNames.filter fun owner =>
    (`volume_polynomials).isPrefixOf owner || (`TauCeti).isPrefixOf owner
  unless !originalModules.isEmpty do
    throwError "No actual project source module was imported."
  let mut sourceEntries : List (Name × Name × ConstantInfo) := []
  let mut sourceInventories : Array Json := #[]
  for owner in originalModules do
    let some index := env.getModuleIdx? owner
      | throwError "Required original source module is absent: {owner}"
    let some imported := env.header.modules[index]?
      | throwError "Original source import metadata is absent: {owner}"
    unless imported.importAll && imported.hasData do
      throwError "Actual project private proof data was not imported with import all: {owner}"
    let some data := env.header.moduleData[index]?
      | throwError "Original source private ModuleData is absent: {owner}"
    unless data.constNames.size == data.constants.size do
      throwError "Original source constant-name/value inventory is inconsistent: {owner}"
    for name in data.constNames, ci in data.constants do
      unless name == ci.name do
        throwError "Original source constant-name/value entry is inconsistent: {owner}, {name}"
      if (privateEnv.find? name).isNone then
        throwError "An actual original-module declaration cannot be inspected: {name}"
      sourceEntries := (owner, name, ci) :: sourceEntries
    let irOnly := data.extraConstNames.filter (fun name => !data.constNames.contains name)
    sourceInventories := sourceInventories.push (Json.mkObj [
      ("original_module", toJson owner.toString),
      ("kernel_declarations", toJson data.constants.size),
      ("listed_ir_auxiliary_names", toJson (irOnly.map Name.toString))])
  let declarations := sourceEntries.map (fun (_, name, ci) => (name, ci))
  let localNames : NameSet := declarations.foldl (fun names entry => names.insert entry.1) {}
  let mut recursionHelpers : NameMap Name := {}
  let mut recursionMetadata : Array Json := #[]
  for (owner, name, ci) in sourceEntries do
    if ci.isUnsafe || ci.isPartial then
      let .defnInfo helper := ci
        | throwError "Unsafe/partial declaration is not a generated recursion definition: {name}"
      let some base := Compiler.isUnsafeRecName? name
        | throwError "Authored unsafe/partial declaration is forbidden: {name}"
      unless Compiler.mkUnsafeRecName base == name && localNames.contains base do
        throwError "A recursion helper lacks its exact local safe parent: {name}"
      let some (.defnInfo parent) := privateEnv.find? base
        | throwError "A recursion helper parent is not a local definition: {name}"
      let some (_, _, .defnInfo sourceParent) := sourceEntries.find?
          (fun (sourceOwner, sourceName, _) => sourceOwner == owner && sourceName == base)
        | throwError "A runtime recursion helper lacks its safe parent in the same original source: {owner}:{name}"
      unless sourceParent.safety == .safe && sourceParent.levelParams == parent.levelParams &&
          sourceParent.type == parent.type && sourceParent.all == parent.all do
        throwError "Stored safe-parent metadata differs from the inspected private definition: {owner}:{name}"
      unless parent.safety == .safe && helper.safety == .partial do
        throwError "A recursion helper/parent has unexpected declaration safety: {name}"
      unless (← liftCoreM <| Meta.isRecursiveDefinition base) do
        throwError "A recursion helper parent lacks Lean's official recursive-definition tag: {name}"
      unless helper.levelParams == parent.levelParams && helper.type == parent.type do
        throwError "A recursion helper changes its safe parent's type or universe parameters: {name}"
      unless helper.all == parent.all.map Compiler.mkUnsafeRecName do
        throwError "A recursion helper has inconsistent mutual-definition metadata: {name}"
      recursionHelpers := recursionHelpers.insert name base
      recursionMetadata := recursionMetadata.push (Json.mkObj [
        ("name", toJson name.toString), ("safe_base", toJson base.toString),
        ("original_module", toJson owner.toString),
        ("safe_base_original_module", toJson owner.toString),
        ("matching_original_source_owner", toJson true),
        ("safe_base_safety", toJson "safe"), ("helper_safety", toJson "partial"),
        ("official_recursive_tag", toJson true), ("matching_type", toJson true),
        ("matching_level_parameters", toJson true),
        ("level_parameters", toJson (helper.levelParams.map Name.toString)),
        ("safe_mutual_names", toJson (parent.all.map Name.toString)),
        ("helper_mutual_names", toJson (helper.all.map Name.toString)),
        ("complete_type_expression", toJson (reprStr helper.type))])
  for (name, ci) in declarations do
    unless recursionHelpers.contains name do
      for dependency in ci.getUsedConstantsAsSet do
        if recursionHelpers.contains dependency then
          throwError "A safe mathematical declaration logically depends on a runtime recursion helper: {name} -> {dependency}"
  let mut checked : Nat := 0
  let mut rows : Array Json := #[]
  let mut axiomsCache : NameMap (Array Name) := {}
  for (owner, name, ci) in sourceEntries do
    let used := ci.getUsedConstantsAsSet.toList
    -- Keep each stored source occurrence: imported generated theorem names may
    -- be merged, but this particular proof body's dependencies must be audited.
    let mut bodyAxioms : NameSet := {}
    if ci.isAxiom then
      bodyAxioms := bodyAxioms.insert name
    for dependency in name :: used do
      let dependencyAxioms ← match axiomsCache.find? dependency with
        | some axioms => pure axioms
        | none => do
            let axioms ← Lean.collectAxioms dependency
            axiomsCache := axiomsCache.insert dependency axioms
            pure axioms
      bodyAxioms := dependencyAxioms.foldl (fun acc ax => acc.insert ax) bodyAxioms
    let axioms := bodyAxioms.toArray.qsort Name.lt
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unapproved transitive axiom {ax} occurs in actual project declaration {owner}:{name}"
    checked := checked + 1
    rows := rows.push (Json.mkObj [
      ("name", toJson name.toString),
      ("original_module", toJson owner.toString),
      ("is_theorem", toJson ci.isTheorem),
      ("is_unsafe", toJson ci.isUnsafe),
      ("is_partial", toJson ci.isPartial),
      ("generated_recursion_base", toJson ((recursionHelpers.find? name).map Name.toString)),
      ("dependencies", toJson (used.map Name.toString)),
      ("axioms", toJson (axioms.map Name.toString))])
  if checked == 0 then
    throwError "No project declaration was found; an empty audit is not a successful verification."
  let report := Json.mkObj [
    ("scope", toJson "Public principal types and every actual stored private declaration in the imported project source modules, including vendored proofs and strictly classified compiler recursion companions."),
    ("compiler_gate", toJson "Valid only after a successful complete ordinary project build from source, the full source-ownership audit, and a zero exit status for this audit file."),
    ("required_statements", .arr statements),
    ("allowed_axioms", toJson (allowed.map Name.toString)),
    ("original_modules", toJson (originalModules.map Name.toString)),
    ("source_module_inventories", .arr sourceInventories),
    ("generated_recursion_helpers", .arr recursionMetadata),
    ("generated_recursion_helper_count", toJson recursionMetadata.size),
    ("safe_logical_dependency_on_runtime_helpers", toJson false),
    ("recursion_helper_audit", toJson "Actual private partial definition with official compiler name, same-source safe recursive parent, matching type/universes/mutual metadata; all nodes axiom-audited and no safe logical edge to any helper."),
    ("checked_declarations", toJson checked),
    ("declarations", .arr rows)]
  liftIO <| IO.FS.writeFile ".lake/reports/audit/imported-axiom-audit.json" report.pretty
  logInfo m!"Checked {checked} actual project declarations; all required public principal entry points are present."
