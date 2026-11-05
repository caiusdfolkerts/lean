module
import VerifiedTargets
import PaperProjectionAlternative
import ExceptionalTargets
import Consolidated.GPBoundaryGeometry
import Lean.Util.CollectAxioms

/-!
The finite terminal-resolution audit. Each target theorem quantifies over
every actual real polytope with that complete labelled boundary. The separate
global classification theorem supplies exhaustive coverage of the targets.
-/

run_cmd do
  let env ← Lean.getEnv
  if env.header.trustLevel > 1 then
    throwError "Terminal audit requires trust level zero or one"
  if (← Lean.getOptions).getBool `debug.skipKernelTC false then
    throwError "Terminal audit rejects disabled kernel checking"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[
      ``Papers.GrassmannPluckerFive.three_term,
      ``Papers.RationalityTen.GPFiniteGeometry.BoundaryWitness.no_actual_realization,
      ``Nonrational.TerminalVerification.valid_of_certifies,
      ``Nonrational.TerminalVerification.targets_valid,
      ``Nonrational.TerminalVerification.targets_classified,
      ``Nonrational.TerminalVerification.projection_or_appendix_of_target,
      ``Nonrational.TerminalVerification.polytope_of_certificate,
      ``Nonrational.TerminalVerification.explicit_appendix_of_facets,
      ``Nonrational.TerminalVerification.projection_or_explicit_appendix_of_target,
      ``Nonrational.TerminalVerification.paper_certifies_of_certifies,
      ``Nonrational.TerminalVerification.paper_projection_or_explicit_appendix_of_target,
      ``Nonrational.TerminalVerification.valid_1983,
      ``Nonrational.TerminalVerification.valid_1984,
      ``Nonrational.TerminalVerification.valid_1985,
      ``Nonrational.TerminalVerification.valid_1986,
      ``Nonrational.TerminalVerification.valid_1987,
      ``Nonrational.TerminalVerification.valid_1988,
      ``Nonrational.TerminalVerification.valid_1989,
      ``Nonrational.TerminalVerification.valid_1990,
      ``Nonrational.TerminalVerification.valid_1991,
      ``Nonrational.TerminalVerification.valid_1992,
      ``Nonrational.TerminalVerification.valid_1993,
      ``Nonrational.TerminalVerification.valid_1994] do
    unless (env.find? name).isSome do
      throwError "Missing terminal declaration {name}"
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "Unapproved transitive axiom {axiomName} in {name}"
    Lean.logInfo m!"AUDITED {name}: {axioms}"
