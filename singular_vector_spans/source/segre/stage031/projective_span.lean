module
public import SegreVerified.Stage031.ActualCriticalSpace
public import Mathlib.LinearAlgebra.Projectivization.Subspace
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


section SegreProjectiveTheorems

run_cmd do
  let out ← IO.getStderr
  out.putStrLn "SEGRE_STAGE Stage031.ProjectiveSpan"
  out.flush

/-!
# The original embedded scheme and the principal projective span theorems

The named sections preserve the original proof stages and local scopes.
-/


section SegreProjectiveSpan

/-!
# The printed projective span and its actual linear cone

The projective span here is Mathlib's independently defined span of projective
points. It is proved equal to the projectivization of the ordinary linear
span, using the existing order equivalence between actual projective subspaces
and linear subspaces. No projective codimension is defined to equal a desired
linear defect. The numerical comparison subtracts one from the dimensions of
the two actual nonzero cones, after nonzeroness is obtained on a refined
nonempty coefficient open.

-/

set_option autoImplicit false
open scoped Classical LinearAlgebra.Projectivization

namespace PaperVerification.Segre.ProjectiveSpan

section General

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The original nonzero vectors, regarded as actual projective points. -/
def projectiveImage (s : Set V) : Set (Projectivization K V) :=
  {p | ∃ (v : V) (hv : v ≠ 0), v ∈ s ∧ p = Projectivization.mk K v hv}

/-- Mathlib's projective span agrees with projectivization of the ordinary
linear span. This is a proved equality of the whole projective subspaces. -/
theorem span_projectiveImage (s : Set V) :
    Projectivization.Subspace.span (projectiveImage (K := K) s) =
      (Submodule.span K s).projectivization := by
  apply le_antisymm
  · apply Projectivization.Subspace.span_le_subspace_iff.mpr
    rintro p ⟨v, hv, hvs, rfl⟩
    exact (Submodule.mk_mem_projectivization_iff _ hv).mpr
      (Submodule.subset_span hvs)
  · have h : Submodule.span K s ≤
        (Projectivization.Subspace.span (projectiveImage (K := K) s)).submodule := by
      apply Submodule.span_le.mpr
      intro v hvs
      by_cases hv : v = 0
      · subst v
        exact Submodule.zero_mem _
      · apply (Projectivization.Subspace.mem_submodule_iff _ hv).mpr
        exact Projectivization.Subspace.subset_span _ ⟨v, hv, hvs, rfl⟩
    have hp := (Submodule.projectivization (K := K) (V := V)).monotone h
    simpa only [Submodule.projectivization, OrderIso.symm_apply_apply] using hp

variable [Module.Finite K V]

/-- A genuine nonzero vector in the smaller subspace makes both projective
spaces nonempty, so subtracting one from both cone dimensions preserves the
codimension. This statement uses the actual projective-subspace correspondence. -/
theorem projective_dimension_difference (S H : Submodule K V) (hSH : S ≤ H)
    (v : V) (hvS : v ∈ S) (hv : v ≠ 0) :
    (Module.finrank K H.projectivization.submodule - 1) -
        (Module.finrank K S.projectivization.submodule - 1) =
      Module.finrank K H - Module.finrank K S := by
  have hS : 0 < Module.finrank K S :=
    (Module.finrank_pos_iff_exists_ne_zero (R := K) (M := S)).mpr
      ⟨⟨v, hvS⟩, fun h => hv (congrArg Subtype.val h)⟩
  have hdim := Submodule.finrank_mono hSH
  have hH' : H.projectivization.submodule = H :=
    (Projectivization.Subspace.submodule (K := K) (V := V)).apply_symm_apply H
  have hS' : S.projectivization.submodule = S :=
    (Projectivization.Subspace.submodule (K := K) (V := V)).apply_symm_apply S
  rw [hH', hS']
  omega

end General

section ActualTensors

variable (K : Type*) [Field K] {I : Type*} [Fintype I] [DecidableEq I]
variable (σ : I → Type*) [∀ i, Fintype (σ i)]

/-- Actual singular rank-one projective points of the original tensor. -/
def singularPoints (T : ActualTensorSpan.Tensor K σ) :
    Set (Projectivization K (ActualTensorSpan.Tensor K σ)) :=
  projectiveImage (ActualTensorSpan.singularRankOneSet K σ T)

/-- The projective span of the original singular points is the
projectivization of their independently defined ordinary linear span. -/
theorem singular_projective_span (T : ActualTensorSpan.Tensor K σ) :
    Projectivization.Subspace.span (singularPoints K σ T) =
      (ActualTensorSpan.singularSpan K σ T).projectivization :=
  span_projectiveImage (ActualTensorSpan.singularRankOneSet K σ T)

/-- The literal projective singular span is contained in the literal
projective critical space, without a genericity or nonisotropy premise. -/
theorem singular_projective_span_le (T : ActualTensorSpan.Tensor K σ) :
    Projectivization.Subspace.span (singularPoints K σ T) ≤
      (ActualTensorCriticalSpace.criticalSpace K σ T).projectivization := by
  rw [singular_projective_span]
  exact (Submodule.projectivization (K := K)
    (V := ActualTensorSpan.Tensor K σ)).monotone
      (ActualTensorCriticalSpace.singularSpan_le_criticalSpace K σ T)

/-- Full linear span and full projective span are exactly equivalent as
equalities of actual subspaces. -/
theorem projective_full_span_iff (T : ActualTensorSpan.Tensor K σ) :
    Projectivization.Subspace.span (singularPoints K σ T) =
        (ActualTensorCriticalSpace.criticalSpace K σ T).projectivization ↔
      ActualTensorSpan.singularSpan K σ T =
        ActualTensorCriticalSpace.criticalSpace K σ T := by
  rw [singular_projective_span]
  exact (Submodule.projectivization (K := K)
    (V := ActualTensorSpan.Tensor K σ)).injective.eq_iff

/-- Membership of a nonzero tensor gives a point in the genuine projective
span, and proves the projective-to-linear codimension comparison. -/
theorem projective_defect_of_tensor_membership
    (T : ActualTensorSpan.Tensor K σ) (hT : T ≠ 0)
    (hmem : T ∈ ActualTensorSpan.singularSpan K σ T) :
    Projectivization.mk K T hT ∈
        Projectivization.Subspace.span (singularPoints K σ T) ∧
      (Module.finrank K
          (ActualTensorCriticalSpace.criticalSpace K σ T).projectivization.submodule - 1) -
        (Module.finrank K
          (Projectivization.Subspace.span (singularPoints K σ T)).submodule - 1) =
        Module.finrank K (ActualTensorCriticalSpace.criticalSpace K σ T) -
          Module.finrank K (ActualTensorSpan.singularSpan K σ T) := by
  rw [singular_projective_span]
  exact ⟨(Submodule.mk_mem_projectivization_iff _ hT).mpr hmem,
    projective_dimension_difference _ _
      (ActualTensorCriticalSpace.singularSpan_le_criticalSpace K σ T) T hmem hT⟩

end ActualTensors

end PaperVerification.Segre.ProjectiveSpan

end SegreProjectiveSpan

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
