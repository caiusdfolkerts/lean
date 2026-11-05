module

import Papers.SmallNonrational
public meta import Lean.Elab.Command
public meta import Lean.Util.CollectAxioms

/-!
# Principal statements and transitive axiom gate

This audit fails if any required endpoint is missing or depends on an axiom
other than `propext`, `Classical.choice`, or `Quot.sound`. It prints the actual
kernel-environment type and axiom set for every endpoint.

Run only after a coherent source build of the complete import graph. Lean
4.35 records imported axiom dependencies in module metadata; collecting those
dependencies does not recheck imported proof bodies. The build must therefore
compile every selected source with kernel checking enabled and authenticate
its imports. The option checks below describe this audit invocation, not the
historical compiler settings of an imported artifact.
-/

set_option Elab.async false

run_cmd do
  let env ← Lean.getEnv
  let opts ← Lean.getOptions
  if env.header.trustLevel > 1 then
    throwError "Principal audit requires kernel trust level zero or one"
  if opts.getBool `debug.skipKernelTC false then
    throwError "Principal audit rejects disabled kernel type checking"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let endpoints := #[
    `Papers.SmallNonrational.theoremOne,
    `Papers.SmallNonrational.theoremTwo,
    `Papers.SmallNonrational.theoremThree,
    `Papers.SmallNonrational.corollaryFour,
    `Papers.SmallNonrational.propositionSeven,
    `Papers.SmallNonrational.propositionEight_i,
    `Papers.SmallNonrational.propositionEight_ii,
    `Papers.SmallNonrational.propositionEight_iii,
    `Papers.SmallNonrational.propositionNine,
    `Papers.SmallNonrational.lemmaEleven,
    `Papers.SmallNonrational.lemmaTwelve,
    `Papers.SmallNonrational.seventeenVertexNonrational,
    `Papers.SmallNonrational.nonrationalVertexLowerBound,
    `Papers.SmallNonrational.vertexBounds,
    `Papers.SmallNonrational.minimumVertexBounds]
  for name in endpoints do
    let some info := env.checked.get.find? name
      | throwError "Missing principal declaration {name}"
    if info.isUnsafe then
      throwError "Unsafe principal declaration {name}"
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "Unapproved transitive axiom {axiomName} in {name}"
    Lean.logInfo m!"AUDIT_STATEMENT {name} : {info.type}"
    Lean.logInfo m!"AUDIT_AXIOMS {name} : {axioms}"
  Lean.logInfo m!"PRINCIPAL_AUDIT_PASSED: {endpoints.size} declarations"
