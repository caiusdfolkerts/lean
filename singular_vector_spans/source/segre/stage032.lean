module
public import SegreVerified.Stage030.TensorSpan
public import SegreVerified.Stage032.Rigidity
public import SegreVerified.Stage032.AsymptoticGrowth
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

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators TensorProduct

/-! Explicit finite-sum and all-arity formulations of the singular-tensor span theorem. -/

namespace PaperVerification.Segre.FiniteLinearCombination

/-- Membership in the span of parametrized generators is equivalent to an
explicit finite linear combination of those same generators. The parameters
retain their defining property; no coefficient is required to be nonzero. -/
theorem mem_span_parametrized_iff
    {R M A : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (g : A → M) (P : A → Prop) (x : M) :
    x ∈ Submodule.span R {y : M | ∃ a : A, P a ∧ y = g a} ↔
      ∃ (m : ℕ) (a : Fin m → A) (c : Fin m → R),
        (∀ j, P (a j)) ∧ x = ∑ j, c j • g (a j) := by
  classical
  constructor
  · intro hx
    obtain ⟨m, c, v, hv⟩ := Submodule.mem_span_set'.mp hx
    choose a ha he using fun j => (v j).property
    refine ⟨m, a, c, ha, ?_⟩
    calc
      x = ∑ j, c j • (v j : M) := hv.symm
      _ = ∑ j, c j • g (a j) :=
        Finset.sum_congr rfl (fun j _ => congrArg (fun z : M => c j • z) (he j))
  · rintro ⟨m, a, c, ha, rfl⟩
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨a j, ha j, rfl⟩))

end PaperVerification.Segre.FiniteLinearCombination

namespace PaperVerification.Segre.ActualTensorSpan

variable (K : Type*) [Field K] {I : Type*} [Fintype I] [DecidableEq I]
variable (σ : I → Type*) [∀ i, Fintype (σ i)]

/-- An exact reformulation of membership in the actual singular span using a
finite list of actual singular tuples and a finite sum in the tensor product. -/
theorem mem_singularSpan_iff_finite_linear_combination (T : Tensor K σ) :
    T ∈ singularSpan K σ T ↔
      ∃ (m : ℕ) (v : Fin m → (∀ i, σ i → K)) (c : Fin m → K),
        (∀ j, IsSingularTuple K σ T (v j)) ∧
          T = ∑ j, c j • PiTensorProduct.tprod K (v j) :=
  FiniteLinearCombination.mem_span_parametrized_iff
    (fun v : ∀ i, σ i → K => PiTensorProduct.tprod K v)
    (IsSingularTuple K σ T) T

end PaperVerification.Segre.ActualTensorSpan

namespace PaperVerification.Segre.PrincipalTensor

open Staircase

variable {K : Type} [Field K] [IsAlgClosed K]

/-- Theorem 1.3 as an explicit finite linear combination. The polynomial and
its nonempty principal open are exactly the witnesses supplied by theorem_1_3.
Every factor vector is nonzero and satisfies the original tensor-contraction
equations. Coefficients may vanish, and an empty sum can represent only zero. -/
theorem theorem_1_3_finite_linear_combination
    (r : ℕ) (n : Fin (r + 1) → ℕ) :
    ∃ p : MvPolynomial (Cell n) K, p ≠ 0 ∧
      (∃ T : ActualTensorSpan.Tensor K (fun i => Fin (n i + 1)),
        MvPolynomial.eval
          (ActualTensorSpan.coefficients K (fun i => Fin (n i + 1)) T) p ≠ 0) ∧
      ∀ T : ActualTensorSpan.Tensor K (fun i => Fin (n i + 1)),
        MvPolynomial.eval
          (ActualTensorSpan.coefficients K (fun i => Fin (n i + 1)) T) p ≠ 0 →
        ∃ (m : ℕ) (v : Fin m → (∀ i, Fin (n i + 1) → K)) (c : Fin m → K),
          (∀ j i, v j i ≠ 0) ∧
          (∀ j i, ∃ a : K,
            ActualTensorSpan.tensorContraction K (fun i => Fin (n i + 1))
              (v j) i T = a • v j i) ∧
          T = ∑ j, c j • PiTensorProduct.tprod K (v j) := by
  obtain ⟨p, hp, hnonempty, hspan⟩ := theorem_1_3 (K := K) r n
  refine ⟨p, hp, hnonempty, ?_⟩
  intro T hT
  obtain ⟨m, v, c, hv, hsum⟩ :=
    (ActualTensorSpan.mem_singularSpan_iff_finite_linear_combination
      K (fun i => Fin (n i + 1)) T).mp (hspan T hT)
  exact ⟨m, v, c, fun j => (hv j).1, fun j => (hv j).2, hsum⟩

end PaperVerification.Segre.PrincipalTensor

/-!
# The empty tensor format

The paper's usual nonempty formats are already covered by `theorem_1_3`.
This supplementary endpoint includes the empty finite index as well, using
Mathlib's actual empty tensor product and its pure-tensor spanning theorem.
-/

namespace PaperVerification.Segre.ActualTensorSpan

variable (K : Type*) [Field K] {I : Type*} [Fintype I] [DecidableEq I] [IsEmpty I]
variable (σ : I → Type*) [∀ i, Fintype (σ i)]

/-- In the actual empty tensor product, every pure tensor satisfies all
singular-tuple conditions, and pure tensors span the whole tensor product. -/
theorem singularSpan_eq_top_of_isEmpty (T : Tensor K σ) :
    singularSpan K σ T = ⊤ := by
  apply top_unique
  rw [← PiTensorProduct.span_tprod_eq_top (R := K) (s := fun i => σ i → K)]
  apply Submodule.span_le.mpr
  rintro _ ⟨v, rfl⟩
  apply Submodule.subset_span
  refine ⟨v, ?_, rfl⟩
  constructor <;> intro i <;> exact isEmptyElim i

end PaperVerification.Segre.ActualTensorSpan

namespace PaperVerification.Segre.PrincipalTensor

open Staircase

variable {K : Type} [Field K] [IsAlgClosed K]

/-- Theorem 1.3 for every natural number of factors, including the empty
format. For a nonempty format this is exactly the original endpoint; for
zero factors the actual singular span is the whole empty tensor product. -/
theorem theorem_1_3_all_arities (r : ℕ) (n : Fin r → ℕ) :
    ∃ p : MvPolynomial (Cell n) K, p ≠ 0 ∧
      (∃ T : ActualTensorSpan.Tensor K (fun i => Fin (n i + 1)),
        MvPolynomial.eval
          (ActualTensorSpan.coefficients K (fun i => Fin (n i + 1)) T) p ≠ 0) ∧
      ∀ T : ActualTensorSpan.Tensor K (fun i => Fin (n i + 1)),
        MvPolynomial.eval
          (ActualTensorSpan.coefficients K (fun i => Fin (n i + 1)) T) p ≠ 0 →
          T ∈ ActualTensorSpan.singularSpan K (fun i => Fin (n i + 1)) T := by
  cases r with
  | zero =>
      refine ⟨1, one_ne_zero, ⟨0, ?_⟩, ?_⟩
      · simp
      · intro T _
        rw [ActualTensorSpan.singularSpan_eq_top_of_isEmpty]
        exact Submodule.mem_top
  | succ r =>
      exact theorem_1_3 r n

end PaperVerification.Segre.PrincipalTensor

end
end

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
