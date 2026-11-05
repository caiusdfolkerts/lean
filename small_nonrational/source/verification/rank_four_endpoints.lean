module
import Consolidated.RankFourTheorems
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
      ``Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C76.refutation,
      ``Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C77.refutation,
      ``Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C78.refutation,
      ``Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C79.refutation,
      ``Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C80.refutation,
      ``Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C81.refutation,
      ``Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C82.refutation,
      ``Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C83.refutation,
      ``Papers.RationalityTen.MatroidChecked.C84ClauseMap.clauses_eq,
      ``Papers.RationalityTen.MatroidCatalogue.catalogue_complete_eight_rank_four,
      ``Papers.RationalityTen.MatroidChecked.vector_configuration_covered,
      ``Papers.RationalityTen.MatroidChecked.VerifiedRankFour.catalogue_density_proofs,
      ``Papers.RationalityTen.MatroidChecked.PaperRankFourTheorem.lemma11,
      ``Papers.RationalityTen.MatroidChecked.PaperRankFourTheorem.lemma11_nonbases,
      ``Papers.RationalityTen.MatroidChecked.VerifiedRankFour.lemma11_rank_four_dense,
      ``Papers.RationalityTen.MatroidChecked.VerifiedRankFour.rank_four_fewer_than_eight_dense,
      ``Papers.RationalityTen.MatroidChecked.GoldenRationalObstruction.no_rational_representation,
      ``Papers.RationalityTen.MatroidChecked.GoldenIdentification.golden_triple_independent,
      ``Papers.RationalityTen.MatroidChecked.GoldenIdentification.golden_five_spans,
      ``Papers.RationalityTen.MatroidChecked.GoldenIdentification.golden_nonbases_exact,
      ``Papers.RationalityTen.MatroidChecked.GoldenSelectedRanks.Golden.flats_card,
      ``Papers.RationalityTen.MatroidChecked.GoldenExceptionExact.exists_spanning_golden,
      ``Papers.RationalityTen.MatroidChecked.MatrixClassificationAssembly.eight_row_density_or_four_column_support,
      ``Papers.RationalityTen.MatroidChecked.MatrixClassificationAssembly.nine_column_exceptional_matrix_density] do
    unless (env.find? name).isSome do
      throwError "Missing audited declaration {name}"
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "Unapproved transitive axiom {axiomName} in {name}"
    Lean.logInfo m!"AUDITED {name}: {axioms}"
