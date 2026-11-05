module
import Consolidated.Seventeen
import Papers.SimpleDeletionPaper
import Lean.Util.CollectAxioms

/-!
Final transitive axiom gate. This is a separate ordinary module so that its
imports also check the exported artifacts and their declaration dependencies.
A successful source build must precede this audit; the gate does not replace it.
-/

run_cmd do
  let env ← Lean.getEnv
  if env.header.trustLevel > 1 then
    throwError "Final audit requires kernel checking (trust level zero or one)"
  if (← Lean.getOptions).getBool `debug.skipKernelTC false then
    throwError "Final audit rejects disabled kernel checking"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[
      ``Papers.Nonrational.Seventeen.realizable_iff_sqrt_five,
      ``Papers.Nonrational.Seventeen.seventeen_vertex_field_theorem,
      ``Papers.Nonrational.Seventeen.not_rationallyRealizable,
      ``Papers.Nonrational.Seventeen.exists_seventeen_vertex_nonrational_polytope,
      ``Papers.Polytopes.simpleDeletion_realizable_iff,
      ``Papers.Polytopes.simpleDeletionTheorem,
      ``Papers.Polytopes.simpleDeletion_rationallyDense_iff,
      ``Papers.Polytopes.simpleDeletion_dense_labeledRealizations_iff,
      ``Papers.Polytopes.simpleDeletion_fields_eq,
      ``Papers.Polytopes.paper_simple_vertex_deletion] do
    unless (env.find? name).isSome do
      throwError "Missing audited declaration {name}"
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "Unapproved transitive axiom {axiomName} in {name}"
    Lean.logInfo m!"AUDITED {name}: {axioms}"
