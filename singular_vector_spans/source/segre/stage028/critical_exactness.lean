module
public import SegreVerified.Stage028.GraphGenericity
public import SegreVerified.Stage028.CriticalPolynomials
public import SegreVerified.Stage027
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


section SegreGlobalCriticalSections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

run_cmd do
  let out ← IO.getStderr
  out.putStrLn "SEGRE_STAGE Stage028.CriticalExactness"
  out.flush

/-!
# Global critical sections and their literal chart equations

The named sections preserve the original proof stages and local scopes.
-/


section SegreActualCriticalExactness

/-!
# Generic exactness and image lifting for the original critical functionals

The actual coefficient-polynomial ideals are identified with the paper's
literal full and graph critical ideals by a complete variable permutation.
The resulting equivalences of full quotient algebras transfer the proved
generic finiteness certificate to the actual sheaf Koszul resolution.
The graph and balanced cohomology arguments then give lifting of every
global section of the original image sheaf on one nonzero coefficient open.
-/

set_option autoImplicit false
open scoped Classical BigOperators

namespace PaperVerification.Segre.ActualCriticalExactness

open scoped ProductChartSections

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open Staircase ProjectiveCharts AllFactorIncidence
open ActualProductKoszulTerms ActualProductChartFrames ActualWeightedExactness
open ProductResolutionImage ProductKoszulVanishing

variable (K : Type) [Field K] [Infinite K] {k : ℕ} (n : Fin (k + 1) → ℕ)

local notation "I" => (fun i => Fin (n i + 1))
set_option quotPrecheck false in local notation "X" => (product K I).scheme

abbrev fullFunctional (T : Cell n → K) : source K I ⟶ line K I 1 :=
  GlobalCriticalMap.criticalMap I (factorProjection K I) T

abbrev graphFunctional {J : Type} [Fintype J] (A : Matrix (Cell n) J K) :
    source K I ⟶ line K I 2 :=
  GraphCriticalMap.graphCriticalMap I (factorProjection K I) (fun j v => A v j)

/-- Every actual full coefficient becomes its literal pivot equation
under the complete chart-coordinate permutation. -/
theorem rename_full_coefficient (T : Cell n → K) (p : Cell n) (q : ChartVar p) :
    MvPolynomial.rename (chartVarEquiv p).symm
      (coefficientPolynomial K I 1 (fullFunctional K n T) p (chartVarEquiv p q)) =
        AllFactorPointSpan.pivotCriticalPolynomial (unitTensorEquiv T) p q := by
  change ProductChartSections.numericalProductChartSectionsEquiv n p
    (coefficient K I 1 (fullFunctional K n T) p (chartVarEquiv p q)) = _
  exact (congrArg (ProductChartSections.numericalProductChartSectionsEquiv n p)
    (full_coefficient K I T p (chartVarEquiv p q))).trans
      (ActualCriticalPolynomial.fullCoefficient_polynomial (K := K) (n := n) T p q)

/-- Every actual quadratic graph coefficient becomes its literal pivot
equation, with every slice retained. -/
theorem rename_graph_coefficient {J : Type} [Fintype J] [DecidableEq J]
    (A : Matrix (Cell n) J K) (p : Cell n) (q : ChartVar p) :
    MvPolynomial.rename (chartVarEquiv p).symm
      (coefficientPolynomial K I 2 (graphFunctional K n A) p (chartVarEquiv p q)) =
        ProjectivePointSpan.pivotCriticalPolynomial A p q := by
  change ProductChartSections.numericalProductChartSectionsEquiv n p
    (coefficient K I 2 (graphFunctional K n A) p (chartVarEquiv p q)) = _
  exact (congrArg (ProductChartSections.numericalProductChartSectionsEquiv n p)
    (graph_coefficient K I (fun j v => A v j) p (chartVarEquiv p q))).trans
      (ActualCriticalPolynomial.graphCoefficient_polynomial (K := K) (n := n) A p q)

/-- Equality of the entire actual full defining ideal, including all
nilpotents and all equations, with the literal critical chart ideal. -/
theorem map_full_ideal (T : Cell n → K) (p : Cell n) :
    (equationIdeal K I 1 (fullFunctional K n T) p).map
      (MvPolynomial.renameEquiv K (chartVarEquiv p).symm).toRingHom =
        AllFactorPointSpan.chartCriticalIdeal (unitTensorEquiv T) p := by
  rw [equationIdeal, Ideal.map_span, ← Set.range_comp,
    AllFactorPointSpan.chartCriticalIdeal_eq_pivot_span]
  apply congrArg Ideal.span
  ext f
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨(chartVarEquiv p).symm q, ?_⟩
    change AllFactorPointSpan.pivotCriticalPolynomial (unitTensorEquiv T) p
      ((chartVarEquiv p).symm q) = MvPolynomial.rename (chartVarEquiv p).symm
        (coefficientPolynomial K I 1 (fullFunctional K n T) p q)
    simpa only [Equiv.apply_symm_apply] using
      (rename_full_coefficient K n T p ((chartVarEquiv p).symm q)).symm
  · rintro ⟨q, rfl⟩
    exact ⟨chartVarEquiv p q, rename_full_coefficient K n T p q⟩

/-- Equality of the full actual quadratic graph ideal with the literal
graph critical chart ideal. -/
theorem map_graph_ideal {J : Type} [Fintype J] [DecidableEq J]
    (A : Matrix (Cell n) J K) (p : Cell n) :
    (equationIdeal K I 2 (graphFunctional K n A) p).map
      (MvPolynomial.renameEquiv K (chartVarEquiv p).symm).toRingHom =
        ProjectivePointSpan.chartCriticalIdeal A p := by
  rw [equationIdeal, Ideal.map_span, ← Set.range_comp,
    ProjectivePointSpan.chartCriticalIdeal_eq_pivot_span]
  apply congrArg Ideal.span
  ext f
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨(chartVarEquiv p).symm q, ?_⟩
    change ProjectivePointSpan.pivotCriticalPolynomial A p
      ((chartVarEquiv p).symm q) = MvPolynomial.rename (chartVarEquiv p).symm
        (coefficientPolynomial K I 2 (graphFunctional K n A) p q)
    simpa only [Equiv.apply_symm_apply] using
      (rename_graph_coefficient K n A p ((chartVarEquiv p).symm q)).symm
  · rintro ⟨q, rfl⟩
    exact ⟨chartVarEquiv p q, rename_graph_coefficient K n A p q⟩

def fullQuotientEquiv (T : Cell n → K) (p : Cell n) :
    (MvPolynomial (FrameIndex I p) K ⧸ equationIdeal K I 1 (fullFunctional K n T) p) ≃ₐ[K]
      MvPolynomial (ChartVar p) K ⧸
        AllFactorPointSpan.chartCriticalIdeal (unitTensorEquiv T) p :=
  Ideal.quotientEquivAlg _ _ (MvPolynomial.renameEquiv K (chartVarEquiv p).symm)
    (map_full_ideal K n T p).symm

def graphQuotientEquiv {J : Type} [Fintype J] [DecidableEq J]
    (A : Matrix (Cell n) J K) (p : Cell n) :
    (MvPolynomial (FrameIndex I p) K ⧸ equationIdeal K I 2 (graphFunctional K n A) p) ≃ₐ[K]
      MvPolynomial (ChartVar p) K ⧸ ProjectivePointSpan.chartCriticalIdeal A p :=
  Ideal.quotientEquivAlg _ _ (MvPolynomial.renameEquiv K (chartVarEquiv p).symm)
    (map_graph_ideal K n A p).symm

theorem full_chart_finite (T : Cell n → K) (p : Cell n)
    [Module.Finite K (MvPolynomial (ChartVar p) K ⧸
      AllFactorPointSpan.chartCriticalIdeal (unitTensorEquiv T) p)] :
    Module.Finite K (MvPolynomial (FrameIndex I p) K ⧸
      equationIdeal K I 1 (fullFunctional K n T) p) :=
  Module.Finite.of_surjective (fullQuotientEquiv K n T p).symm.toLinearMap
    (fullQuotientEquiv K n T p).symm.surjective

theorem graph_chart_finite {J : Type} [Fintype J] [DecidableEq J]
    (A : Matrix (Cell n) J K) (p : Cell n)
    [Module.Finite K (MvPolynomial (ChartVar p) K ⧸ ProjectivePointSpan.chartCriticalIdeal A p)] :
    Module.Finite K (MvPolynomial (FrameIndex I p) K ⧸
      equationIdeal K I 2 (graphFunctional K n A) p) :=
  Module.Finite.of_surjective (graphQuotientEquiv K n A p).symm.toLinearMap
    (graphQuotientEquiv K n A p).symm.surjective

/-- The original full critical Koszul complex is exact whenever its
literal critical schemes on the actual standard charts are finite. -/
theorem full_exact_of_finite (T : Cell n → K)
    (hf : ∀ p : Cell n, Module.Finite K (MvPolynomial (ChartVar p) K ⧸
      AllFactorPointSpan.chartCriticalIdeal (unitTensorEquiv T) p)) (r : ℕ) :
    (ProductWeightedKoszul.shortComplex K I 1 (fullFunctional K n T) r).Exact := by
  apply exact_of_finite_charts
  intro p
  letI := hf p
  exact full_chart_finite K n T p

/-- The original graph critical Koszul complex is exact from literal
finite graph-chart quotients, with no regularity hypothesis. -/
theorem graph_exact_of_finite {J : Type} [Fintype J] [DecidableEq J]
    (A : Matrix (Cell n) J K)
    (hf : ∀ p : Cell n, Module.Finite K (MvPolynomial (ChartVar p) K ⧸
      ProjectivePointSpan.chartCriticalIdeal A p)) (r : ℕ) :
    (ProductWeightedKoszul.shortComplex K I 2 (graphFunctional K n A) r).Exact := by
  apply exact_of_finite_charts
  intro p
  letI := hf p
  exact graph_chart_finite K n A p

theorem full_image_sections_surjective (htriangle : TriangleDimensions I)
    (T : Cell n → K)
    (hf : ∀ p : Cell n, Module.Finite K (MvPolynomial (ChartVar p) K ⧸
      AllFactorPointSpan.chartCriticalIdeal (unitTensorEquiv T) p)) :
    Function.Surjective ((factorThruImage (fullFunctional K n T)).app ⊤) := by
  apply balanced_image_sections_surjective K I
    (fun i => by simp only [Fintype.card_fin]; omega) htriangle
  intro p
  letI := hf p
  exact full_chart_finite K n T p

theorem graph_image_sections_surjective {J : Type} [Fintype J] [DecidableEq J]
    (A : Matrix (Cell n) J K)
    (hf : ∀ p : Cell n, Module.Finite K (MvPolynomial (ChartVar p) K ⧸
      ProjectivePointSpan.chartCriticalIdeal A p)) :
    Function.Surjective ((factorThruImage (graphFunctional K n A)).app ⊤) := by
  apply ProductResolutionImage.graph_image_sections_surjective K I
    (fun i => by simp only [Fintype.card_fin]; omega)
  intro p
  letI := hf p
  exact graph_chart_finite K n A p

/-- The original global line section in the literal polynomial chart
coordinates used by the point-span and critical-ideal theorems. -/
def literalChartSectionPolynomial (d : ℤ) (s : Γ(line K I d, ⊤)) (p : Cell n) :
    MvPolynomial (ChartVar p) K :=
  ProductChartSections.numericalProductChartSectionsEquiv n p
    (ActualProductChartFrames.lineFrame K I p d
      ((line K I d).presheaf.map (ActualProductChartFrames.chart K I p).leTop.op s))

private theorem mem_of_map_equiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (J : Ideal R) (L : Ideal S) (h : J.map e.toRingHom = L) (x : R) :
    x ∈ J ↔ e x ∈ L := by
  rw [← h, Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, he⟩
    exact e.injective he ▸ hy

/-- The original full functional's global range is exactly simultaneous
membership in all literal full critical ideals. -/
theorem balanced_global_range_iff_literal_ideals (htriangle : TriangleDimensions I)
    (T : Cell n → K)
    (hf : ∀ p : Cell n, Module.Finite K (MvPolynomial (ChartVar p) K ⧸
      AllFactorPointSpan.chartCriticalIdeal (unitTensorEquiv T) p))
    (s : Γ(line K I 1, ⊤)) :
    (∃ t : Γ(source K I, ⊤), (fullFunctional K n T).app ⊤ t = s) ↔
      ∀ p : Cell n, literalChartSectionPolynomial K n 1 s p ∈
        AllFactorPointSpan.chartCriticalIdeal (unitTensorEquiv T) p := by
  rw [global_range_iff_coefficient_ideals K I 1 (fullFunctional K n T)
    (full_image_sections_surjective K n htriangle T hf) s]
  apply forall_congr'
  intro p
  exact mem_of_map_equiv (MvPolynomial.renameEquiv K (chartVarEquiv p).symm).toRingEquiv
    _ _ (map_full_ideal K n T p) _

/-- The original graph functional's global range is exactly simultaneous
membership in all literal quadratic graph critical ideals. -/
theorem graph_global_range_iff_literal_ideals {J : Type} [Fintype J] [DecidableEq J]
    (A : Matrix (Cell n) J K)
    (hf : ∀ p : Cell n, Module.Finite K (MvPolynomial (ChartVar p) K ⧸
      ProjectivePointSpan.chartCriticalIdeal A p))
    (s : Γ(line K I 2, ⊤)) :
    (∃ t : Γ(source K I, ⊤), (graphFunctional K n A).app ⊤ t = s) ↔
      ∀ p : Cell n, literalChartSectionPolynomial K n 2 s p ∈
        ProjectivePointSpan.chartCriticalIdeal A p := by
  rw [global_range_iff_coefficient_ideals K I 2 (graphFunctional K n A)
    (graph_image_sections_surjective K n A hf) s]
  apply forall_congr'
  intro p
  exact mem_of_map_equiv (MvPolynomial.renameEquiv K (chartVarEquiv p).symm).toRingEquiv
    _ _ (map_graph_ideal K n A p) _

end PaperVerification.Segre.ActualCriticalExactness

namespace PaperVerification.Segre.ActualCriticalExactness

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Staircase ActualProductKoszulTerms ProductKoszulVanishing

variable (K : Type) [Field K] [Infinite K] {k : ℕ} (n : Fin (k + 1) → ℕ)
local notation "I" => (fun i => Fin (n i + 1))

/-- A genuine nonzero-polynomial open gives exactness and actual image
lifting for the balanced full critical functional. -/
theorem generic_balanced_exactness_and_lifting (htriangle : TriangleDimensions I) :
    ∃ p : MvPolynomial (Cell n) K, p ≠ 0 ∧
      ∀ T : Cell n → K, MvPolynomial.aeval T p ≠ 0 →
        (∀ r, (ProductWeightedKoszul.shortComplex K I 1 (fullFunctional K n T) r).Exact) ∧
        Function.Surjective ((factorThruImage (fullFunctional K n T)).app ⊤) := by
  obtain ⟨p, hp, hw⟩ := AllChartGenericity.exists_all_chart_certificate (K := K) (n := n)
  refine ⟨p, hp, ?_⟩
  intro T hT
  exact ⟨full_exact_of_finite K n T (fun q => (hw T hT q).1),
    full_image_sections_surjective K n htriangle T (fun q => (hw T hT q).1)⟩

/-- The entire graph-format range has a common nonzero coefficient open
on which its original weighted resolution is exact and its actual image
sheaf has surjective global-section lifting. -/
theorem generic_graph_exactness_and_lifting {J : Type} [Fintype J] [DecidableEq J]
    (hlen : sideSum n + 1 ≤ Fintype.card J) :
    ∃ p : MvPolynomial (Cell n × J) K, p ≠ 0 ∧
      ∀ A : Matrix (Cell n) J K, MvPolynomial.eval (fun q => A q.1 q.2) p ≠ 0 →
        (∀ r, (ProductWeightedKoszul.shortComplex K I 2 (graphFunctional K n A) r).Exact) ∧
        Function.Surjective ((factorThruImage (graphFunctional K n A)).app ⊤) := by
  obtain ⟨p, hp, hw⟩ := GenericGraphChartCertificate.exists_graph_chart_certificate
    (K := K) hlen
  refine ⟨p, hp, ?_⟩
  intro A hA
  exact ⟨graph_exact_of_finite K n A (fun q => ((hw A hA).2 q).1),
    graph_image_sections_surjective K n A (fun q => ((hw A hA).2 q).1)⟩

end PaperVerification.Segre.ActualCriticalExactness

end SegreActualCriticalExactness

end SegreGlobalCriticalSections

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
  -- Reject direct proof holes before computing transitive axiom closures.
  -- The complete successful audit below remains unchanged.
  for name in names do
    let some info := env.checked.get.find? name
      | throwError "Authored declaration is not kernel checked: {name}"
    if let .axiomInfo _ := info then throwError "Authored axiom: {name}"
    if info.type.hasSorry || ((info.value? (allowOpaque := true)).any (·.hasSorry)) then
      throwError "Authored declaration contains a sorry expression: {name}"
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
