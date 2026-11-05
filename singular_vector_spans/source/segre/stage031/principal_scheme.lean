module
public import SegreVerified.Stage031.IntrinsicScheme
public import SegreVerified.Stage031.ProjectiveReduction
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
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section ProbeLayer391



/-!
# Singular-vector geometry and all-format spanning theorems

The named sections preserve the original proof stages and local scopes.
-/

@[expose] public section

-- Emit compilation progress immediately while checking this large unit.
set_option stderrAsMessages false
-- Style linting is separate from elaboration, kernel checking, and the axiom audit.
set_option linter.all false
noncomputable section
set_option autoImplicit false


section SegreProjectiveTheorems

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

run_cmd do
  let out ← IO.getStderr
  out.putStrLn "SEGRE_STAGE Stage031.PrincipalScheme"
  out.flush

/-!
# The original embedded scheme and the principal projective span theorems

The named sections preserve the original proof stages and local scopes.
-/



section SegrePrincipalScheme

/-!
# The paper's original global scheme hypotheses

These endpoints use the actual closed singular-tuple zero-scheme on the
product of the original projective factors. Its finite and reduced predicates
are Mathlib's scheme predicates; neither is defined to mean a chart condition.
The complete chart quotient equivalences and scheme-cover arguments provide
the proved passage to the chart algebra used in the graph proof.

-/

set_option autoImplicit false
open scoped Classical BigOperators

namespace PaperVerification.Segre.PrincipalScheme

open Staircase GraphSpan CriticalGraph SingularSpan ProjectiveCharts

variable {K : Type} [Field K] [IsAlgClosed K] {k m : ℕ}
  {n : Fin (k + 1) → ℕ}

/-- Proposition 2.1, with the original global finite/reduced singular-scheme
hypotheses and all three conclusions. The distinguished last vector space has
dimension `m + 1`; every positive last dimension is therefore included. -/
theorem proposition_2_1 (A : Matrix (Cell n) (Fin (m + 1)) K)
    (hb : ∀ x : FactorPoint n K, lastContraction A x.val ≠ 0)
    (hf : AlgebraicGeometry.IsFinite
      (SingularSchemeGraphCharts.originalSingularToBase A))
    (hr : AlgebraicGeometry.IsReduced
      (SingularSchemeGraphCharts.originalSingularScheme A)) :
    singularSpan A = graphSpan A ⊓ fullCriticalSpace A ∧
      Module.finrank K (singularSpan A) =
        (Degeneration.multiplicationMatrix 1 A).rank - ∑ i, (n i + 1).choose 2 ∧
      A ∈ singularSpan A := by
  obtain ⟨hf', hr'⟩ :=
    SingularSchemeGraphCharts.graph_charts_of_original_scheme A hb hf hr
  exact GraphGeometry.proposition_2_1 A hb hf' hr'

/-- Lemma 2.2 in the actual global singular scheme, for every finite
nonnegative format and every characteristic, on an explicitly nonempty
polynomial open in all original tensor coefficients. -/
theorem lemma_2_2 (n : Fin (k + 1) → ℕ) :
    ∃ p : MvPolynomial (Cell n) K, p ≠ 0 ∧
      (∃ T : Cell n → K, MvPolynomial.eval T p ≠ 0) ∧
      ∀ T : Cell n → K, MvPolynomial.eval T p ≠ 0 →
        AlgebraicGeometry.IsFinite (LiteralCriticalZeroScheme.singularToBase K n T) ∧
          AlgebraicGeometry.IsReduced (LiteralCriticalZeroScheme.singularScheme K n T) := by
  obtain ⟨p, hp, hcert⟩ :=
    AllChartGenericity.exists_all_chart_certificate (K := K) (n := n)
  refine ⟨p, hp, AllFormatReduction.nonempty_tensor_certificate hp, ?_⟩
  intro T hT
  have hT' : MvPolynomial.aeval T p ≠ 0 := by
    simpa only [MvPolynomial.aeval_eq_eval] using hT
  apply (LiteralCriticalZeroScheme.full_finite_reduced_iff K n T).mpr
  exact ⟨fun q => (hcert T hT' q).1, fun q => (hcert T hT' q).2⟩

/-- Both assertions of Lemma 2.2 hold on one explicitly nonempty principal
open in the complete original tensor coefficient space throughout the graph
range. The base-point-free assertion concerns the literal original slices;
finiteness and reducedness concern the actual singular-tuple scheme. -/
theorem lemma_2_2_graph (n : Fin (k + 1) → ℕ) (m : ℕ)
    (hlen : sideSum n + 1 ≤ m + 1) :
    ∃ p : MvPolynomial (Cell n × Fin (m + 1)) K, p ≠ 0 ∧
      (∃ A : Matrix (Cell n) (Fin (m + 1)) K,
        MvPolynomial.eval (fun q => A q.1 q.2) p ≠ 0) ∧
      ∀ A : Matrix (Cell n) (Fin (m + 1)) K,
        MvPolynomial.eval (fun q => A q.1 q.2) p ≠ 0 →
          (∀ x : FactorPoint n K, lastContraction A x.val ≠ 0) ∧
          AlgebraicGeometry.IsFinite
            (SingularSchemeGraphCharts.originalSingularToBase A) ∧
          AlgebraicGeometry.IsReduced
            (SingularSchemeGraphCharts.originalSingularScheme A) := by
  obtain ⟨b, hb, hbase⟩ :=
    ChartBasePointFree.generic_lastContraction_ne_zero
      (K := K) (n := n) (J := Fin (m + 1))
      (by simpa only [Fintype.card_fin] using hlen)
  obtain ⟨r, hr, hfull⟩ :=
    GenericGraphChartCertificate.exists_full_chart_certificate
      (K := K) (n := n) (J := Fin (m + 1))
  refine ⟨b * r, mul_ne_zero hb hr, ?_, ?_⟩
  · by_contra h
    push_neg at h
    apply mul_ne_zero hb hr
    apply MvPolynomial.funext
    intro v
    simpa only [map_zero] using h (fun u j => v (u, j))
  · intro A hA
    rw [map_mul] at hA
    exact ⟨hbase A (mul_ne_zero_iff.mp hA).1,
      (SingularSchemeGraphCharts.original_finite_reduced_iff A).mpr
        (hfull A (mul_ne_zero_iff.mp hA).2)⟩

end PaperVerification.Segre.PrincipalScheme

end SegrePrincipalScheme


end SegreProjectiveTheorems

end
end
end ProbeLayer391


/-! Future-only kernel audit for one exported mathematical stage.

Append to the stage being checked, with Lean.Util.CollectAxioms available through
both `public import Lean.Util.CollectAxioms` and `import all Lean.Util.CollectAxioms`
in that stage's header, as required by the reviewed FullFlattenedAudit.

Every new declaration in the checked kernel environment is included: public,
private, generated and vendored declarations receive the same direct-sorry and
transitive-axiom checks. This is evidence for this stage only. Later principal
theorems need not exist yet, and the final full principal audit remains required.

This preparation does not execute the audit, export a module or alter a proof.
-/

open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  unless env.header.trustLevel == 0 do
    throwError "The stage kernel audit requires kernel trust level zero"
  let names := (env.checked.get.constants.foldStage2
    (fun (names : Array Name) name _ => names.push name) #[]).qsort Name.quickLt
  unless names.size > 0 do throwError "The stage mathematical module is empty"
  let privateEnv := env.setExporting false
  let importedAxioms := exportedAxiomsExt.getState (asyncMode := .mainOnly) env
  -- Match Lean's ordinary export audit, sharing its traversal cache across names.
  let axiomRows := CollectAxioms.runM privateEnv do
    names.mapM fun name =>
      return (name, ← CollectAxioms.collectAndGet importedAxioms.find? name)
  let mut theoremCount : Nat := 0
  for (name, axioms) in axiomRows do
    let some info := env.checked.get.find? name
      | throwError "Authored declaration is not kernel checked: {name}"
    if let .axiomInfo _ := info then throwError "Authored axiom: {name}"
    if info.type.hasSorry || ((info.value? (allowOpaque := true)).any (·.hasSorry)) then
      throwError "Authored declaration contains a sorry expression: {name}"
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unapproved transitive axiom in {name}: {ax}"
    if let .thmInfo _ := info then
      theoremCount := theoremCount + 1
  let report := Json.mkObj [
    ("main_module", toJson env.header.mainModule.toString),
    ("declaration_count", toJson names.size),
    ("theorem_count", toJson theoremCount),
    ("trust_level", toJson env.header.trustLevel.toNat),
    ("allowed_axioms", toJson #["propext", "Classical.choice", "Quot.sound"]),
    ("audit_scope", toJson "current_stage_new_declarations")]
  logInfo m!"SEGRE_STAGE_KERNEL_AUDIT_PASS {report.compress}"
