module
import Papers.LemmaFiveFieldObstruction
import Papers.IntrinsicChirotope
import Papers.RationalityTenMultiaffine
import Consolidated.ProjectionReconstruction
import Consolidated.ProjectionCertificateSoundness
import Lean.Util.CollectAxioms

/-! Transitive axiom audit of the supporting results named in the paper. -/

run_cmd do
  Lean.Elab.Command.liftIO <| IO.println "SUPPORTING_IMPORTS_READY"
  let env ← Lean.getEnv
  if env.header.trustLevel > 1 then
    throwError "Supporting-result audit requires trust level zero or one"
  if (← Lean.getOptions).getBool `debug.skipKernelTC false then
    throwError "Supporting-result audit rejects disabled kernel checking"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[
      ``Papers.Nonrational.projective_golden_root,
      ``Papers.Nonrational.lemma5_field_obstruction,
      ``Papers.Nonrational.exists_golden_root_iff,
      ``Papers.RationalityTen.ChirotopeDensity.projected_configuration_rational_density,
      ``Papers.RationalityTen.ChirotopeDensity.actual_projection_certificate_rationallyApproximable,
      ``Papers.RationalityTen.ChirotopeDensity.FiniteProjection.actual_labelled_polytope_rationallyApproximable_of_finite_projection_certificate,
      ``Papers.RationalityTen.ChirotopeDensity.projective_plane_rational_density,
      ``Papers.RationalityTen.ChirotopeDensity.rational_chirotope_dense_le_three,
      ``Papers.RationalityTen.ChirotopeDensity.SameRepresentedType.subset_rank_eq,
      ``Papers.RationalityTen.MultiaffineDensity.multiaffine_rational_zeros_dense,
      ``Papers.RationalityTen.MultiaffineDensity.multiaffine_rational_zeros_in_open] do
    Lean.Elab.Command.liftIO <| IO.println s!"AUDITING {name}"
    unless (env.find? name).isSome do
      throwError "Missing supporting declaration {name}"
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "Unapproved transitive axiom {axiomName} in {name}"
    Lean.logInfo m!"AUDITED {name}: {axioms}"
