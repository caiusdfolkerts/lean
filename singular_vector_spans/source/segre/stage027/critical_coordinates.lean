module
public import SegreVerified.Stage027.ProductFrames
public import SegreVerified.Stage027.GraphCriticalMap
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


section SegreCriticalBundleGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

run_cmd do
  let out ← IO.getStderr
  out.putStrLn "SEGRE_STAGE Stage027.CriticalCoordinates"
  out.flush

/-!
# The actual critical bundle and its weighted Koszul complex

The named sections preserve the original proof stages and local scopes.
-/

set_option autoImplicit false


section SegreActualCriticalFrame

/-!
# The actual critical functional in the canonical source frame

The full and graph critical maps, evaluated on a canonical source basis
vector, are the literal contraction-proportionality coordinate morphisms.
Linearity then identifies the entire functional with the linear combination
of those actual coordinate sections. This is the source-frame step needed
before identifying their coefficients with the polynomial chart equations.

-/

set_option autoImplicit false
open scoped Classical BigOperators

namespace PaperVerification.Segre.ActualCriticalFrame

open CategoryTheory Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open ActualProductKoszulTerms ActualProductChartFrames
open scoped ProductChartSections

universe u
variable (K : Type u) [Field K] {k : ℕ}
variable (I : Fin (k+1) → Type u)
variable [∀ i,Fintype (I i)] [∀ i,DecidableEq (I i)]

set_option quotPrecheck false in local notation "X" => (product K I).scheme

/-- The finite direct-sum functional has its actual componentwise section formula. -/
theorem sum_projection_app {L : (X).Modules}
    (c : ∀ i : Fin (k+1),factorKernel K I i ⟶ L)
    (U : (X).Opens) (s : Γ(source K I,U)) :
    (∑ i : Fin (k+1),Pi.π (factorKernel K I) i ≫ c i).app U s =
      ∑ i : Fin (k+1),(c i).app U ((Pi.π (factorKernel K I) i).app U s) := by
  let E := Scheme.Modules.sectionsFunctor U
  letI : E.Additive := by
    refine ⟨?_⟩
    intro M N f g
    rfl
  change (E.map (∑ i : Fin (k+1),Pi.π (factorKernel K I) i ≫ c i)).hom s = _
  rw [Functor.map_sum,ModuleCat.hom_sum,LinearMap.sum_apply]
  simp only [Functor.map_comp,ModuleCat.hom_comp,LinearMap.comp_apply] <;> rfl

/-- Every chosen source basis vector selects precisely its original factor map. -/
theorem sum_projection_sourceFrame_single {L : (X).Modules}
    (c : ∀ i : Fin (k+1),factorKernel K I i ⟶ L)
    (p : ∀ i,I i) (q : FrameIndex I p) :
    (∑ i : Fin (k+1),Pi.π (factorKernel K I) i ≫ c i).app (chart K I p)
      (sourceFrame K I p (Pi.single q 1)) =
      (c q.1).app (chart K I p) (factorSourceBasis K I p q.1 q.2) := by
  rw [sum_projection_app,Finset.sum_eq_single q.1]
  · rw [sourceFrame_single_self]
  · intro i _ hi
    rw [sourceFrame_single_other K I p q i hi,map_zero]
  · intro h
    exact (h (Finset.mem_univ q.1)).elim

/-- The genuine full critical functional has the literal full coordinate
equation on each normalized Euler basis vector. -/
theorem full_sourceFrame_single (T : (∀ i,I i) → K)
    (p : ∀ i,I i) (q : FrameIndex I p) :
    (GlobalCriticalMap.criticalMap I (factorProjection K I) T).app (chart K I p)
      (sourceFrame K I p (Pi.single q 1)) =
      (GlobalCriticalMap.criticalCoordinate I (factorProjection K I) T
        q.1 (p q.1) q.2.val).app (chart K I p) (1 : Γ(X,chart K I p)) := by
  refine (sum_projection_sourceFrame_single K I
    (fun i => GlobalCriticalMap.factorCritical I (factorProjection K I) T i) p q).trans ?_
  refine (congrArg ((GlobalCriticalMap.factorCritical I (factorProjection K I) T q.1).app
    (chart K I p)) (factorSourceBasis_apply K I p q.1 q.2)).trans ?_
  exact GlobalCriticalMap.factorCritical_coordinateWedge I (factorProjection K I) T
    q.1 (p q.1) q.2.val _ _ _

/-- The actual coefficients of the full critical functional, in the
canonical affine line frame. -/
def fullCoefficient (T : (∀ i,I i) → K) (p : ∀ i,I i) (q : FrameIndex I p) :
    Γ(X,chart K I p) :=
  lineFrame K I p 1
    ((GlobalCriticalMap.criticalCoordinate I (factorProjection K I) T
      q.1 (p q.1) q.2.val).app (chart K I p) (1 : Γ(X,chart K I p)))

/-- The whole full critical functional is the linear combination of its
literal normalized coordinate sections. -/
theorem full_sourceFrame (T : (∀ i,I i) → K) (p : ∀ i,I i)
    (v : FrameIndex I p → Γ(X,chart K I p)) :
    lineFrame K I p 1
      ((GlobalCriticalMap.criticalMap I (factorProjection K I) T).app (chart K I p)
        (sourceFrame K I p v)) =
      Fintype.linearCombination Γ(X,chart K I p) (fullCoefficient K I T p) v := by
  let a : (FrameIndex I p → Γ(X,chart K I p)) →ₗ[Γ(X,chart K I p)]
      Γ(X,chart K I p) :=
    (lineFrame K I p 1).toLinearMap.comp
      (((GlobalCriticalMap.criticalMap I (factorProjection K I) T).val.app
        (op (chart K I p))).hom.comp (sourceFrame K I p).toLinearMap)
  have he : a=Fintype.linearCombination Γ(X,chart K I p) (fullCoefficient K I T p) := by
    apply (Pi.basisFun Γ(X,chart K I p) (FrameIndex I p)).ext
    intro q
    rw [Pi.basisFun_apply,Fintype.linearCombination_apply_single,one_smul]
    change lineFrame K I p 1
      ((GlobalCriticalMap.criticalMap I (factorProjection K I) T).app (chart K I p)
        (sourceFrame K I p (Pi.single q 1))) = _
    rw [full_sourceFrame_single] <;> rfl
  exact LinearMap.congr_fun he v

variable {J : Type u} [Fintype J]

/-- The genuine graph critical functional gives precisely the graph
contraction equation on each normalized Euler basis vector. -/
theorem graph_sourceFrame_single (T : J → (∀ i,I i) → K)
    (p : ∀ i,I i) (q : FrameIndex I p) :
    (GraphCriticalMap.graphCriticalMap I (factorProjection K I) T).app (chart K I p)
      (sourceFrame K I p (Pi.single q 1)) =
      (GraphCriticalMap.graphCriticalCoordinate I (factorProjection K I) T
        q.1 (p q.1) q.2.val).app (chart K I p) (1 : Γ(X,chart K I p)) := by
  refine (sum_projection_sourceFrame_single K I
    (fun i => GraphCriticalMap.graphFactorCritical I (factorProjection K I) T i) p q).trans ?_
  refine (congrArg ((GraphCriticalMap.graphFactorCritical I (factorProjection K I) T q.1).app
    (chart K I p)) (factorSourceBasis_apply K I p q.1 q.2)).trans ?_
  exact GraphCriticalMap.graphFactorCritical_coordinateWedge I (factorProjection K I) T
    q.1 (p q.1) q.2.val _ _ _

/-- Actual graph coefficients, before the polynomial-chart identification. -/
def graphCoefficient (T : J → (∀ i,I i) → K) (p : ∀ i,I i) (q : FrameIndex I p) :
    Γ(X,chart K I p) :=
  lineFrame K I p 2
    ((GraphCriticalMap.graphCriticalCoordinate I (factorProjection K I) T
      q.1 (p q.1) q.2.val).app (chart K I p) (1 : Γ(X,chart K I p)))

/-- The entire graph functional is the exact linear combination of its
actual coordinate sections, retaining every slice and every factor. -/
theorem graph_sourceFrame (T : J → (∀ i,I i) → K) (p : ∀ i,I i)
    (v : FrameIndex I p → Γ(X,chart K I p)) :
    lineFrame K I p 2
      ((GraphCriticalMap.graphCriticalMap I (factorProjection K I) T).app (chart K I p)
        (sourceFrame K I p v)) =
      Fintype.linearCombination Γ(X,chart K I p) (graphCoefficient K I T p) v := by
  let a : (FrameIndex I p → Γ(X,chart K I p)) →ₗ[Γ(X,chart K I p)]
      Γ(X,chart K I p) :=
    (lineFrame K I p 2).toLinearMap.comp
      (((GraphCriticalMap.graphCriticalMap I (factorProjection K I) T).val.app
        (op (chart K I p))).hom.comp (sourceFrame K I p).toLinearMap)
  have he : a=Fintype.linearCombination Γ(X,chart K I p) (graphCoefficient K I T p) := by
    apply (Pi.basisFun Γ(X,chart K I p) (FrameIndex I p)).ext
    intro q
    rw [Pi.basisFun_apply,Fintype.linearCombination_apply_single,one_smul]
    change lineFrame K I p 2
      ((GraphCriticalMap.graphCriticalMap I (factorProjection K I) T).app (chart K I p)
        (sourceFrame K I p (Pi.single q 1))) = _
    rw [graph_sourceFrame_single] <;> rfl
  exact LinearMap.congr_fun he v

end PaperVerification.Segre.ActualCriticalFrame

end SegreActualCriticalFrame

end SegreCriticalBundleGeometry

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
