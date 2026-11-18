module
public import SegreVerified.Stage030.QuantitativeBounds
public import Mathlib.Analysis.Asymptotics.Lemmas
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

namespace PaperVerification.Segre.AsymptoticGrowth

open Asymptotics Filter

/-- The exact three-factor threshold on page 17. -/
def threeFactorThreshold (e : ℕ) : ℕ :=
  2 * e + 2 * ⌈Real.sqrt (7 * (e : ℝ))⌉₊

/-- The reciprocal of the integer ceiling of half the factor count. -/
def rootExponent (k : ℕ) : ℝ :=
  1 / (((k + 1) / 2 : ℕ) : ℝ)

/-- The exact threshold for a fixed number of at least four smaller factors. -/
def manyFactorThreshold (k e : ℕ) : ℕ :=
  e + 2 * ⌈(((k + 1) * e : ℕ) : ℝ) ^ rootExponent k⌉₊ + 4 * k - 2

theorem rootExponent_eq_printed (k : ℕ) :
    rootExponent k = 1 / ((⌈(k : ℝ) / 2⌉ : ℤ) : ℝ) := by
  rw [ExcessAsymptotic.ceil_half_cast, Int.cast_natCast]
  rfl

/-- Natural and ordinary integer ceilings give the same printed threshold. -/
theorem three_factor_threshold_cast (e : ℕ) :
    (threeFactorThreshold e : ℝ) =
      2 * (e : ℝ) + 2 * ((⌈Real.sqrt (7 * (e : ℝ))⌉ : ℤ) : ℝ) := by
  have hc : (⌈Real.sqrt (7 * (e : ℝ))⌉₊ : ℝ) =
      ((⌈Real.sqrt (7 * (e : ℝ))⌉ : ℤ) : ℝ) := by
    exact_mod_cast Int.natCast_ceil_eq_ceil (Real.sqrt_nonneg (7 * (e : ℝ)))
  simp only [threeFactorThreshold, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, hc]

theorem three_factor_error (e : ℕ) :
    (threeFactorThreshold e : ℝ) - 2 * (e : ℝ) =
      2 * (⌈Real.sqrt (7 * (e : ℝ))⌉₊ : ℝ) := by
  simp only [threeFactorThreshold, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

theorem many_factor_error (k e : ℕ) (hk : 4 ≤ k) :
    (manyFactorThreshold k e : ℝ) - (e : ℝ) =
      2 * (⌈(((k + 1) * e : ℕ) : ℝ) ^ rootExponent k⌉₊ : ℝ) +
        4 * (k : ℝ) - 2 := by
  have hsub : 2 ≤
      e + 2 * ⌈(((k + 1) * e : ℕ) : ℝ) ^ rootExponent k⌉₊ + 4 * k := by
    omega
  unfold manyFactorThreshold
  rw [Nat.cast_sub hsub]
  push_cast
  ring

/-- The complete real expression is the one printed on page 17, including
the ordinary ceiling in the root exponent and the final subtraction. -/
theorem many_factor_threshold_cast (k e : ℕ) (hk : 4 ≤ k) :
    (manyFactorThreshold k e : ℝ) =
      (e : ℝ) + 2 *
        ((⌈(((k : ℝ) + 1) * (e : ℝ)) ^
          (1 / ((⌈(k : ℝ) / 2⌉ : ℤ) : ℝ))⌉ : ℤ) : ℝ) +
        4 * (k : ℝ) - 2 := by
  have hc : (⌈(((k + 1) * e : ℕ) : ℝ) ^ rootExponent k⌉₊ : ℝ) =
      ((⌈(((k + 1) * e : ℕ) : ℝ) ^ rootExponent k⌉ : ℤ) : ℝ) := by
    exact_mod_cast Int.natCast_ceil_eq_ceil
      (Real.rpow_nonneg (Nat.cast_nonneg ((k + 1) * e)) (rootExponent k))
  have hr : (((k + 1) * e : ℕ) : ℝ) ^ rootExponent k =
      (((k : ℝ) + 1) * (e : ℝ)) ^
        (1 / ((⌈(k : ℝ) / 2⌉ : ℤ) : ℝ)) := by
    simp only [rootExponent_eq_printed, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have h := many_factor_error k e hk
  rw [hc, hr] at h
  linarith

theorem three_factor_error_nonneg (e : ℕ) :
    0 ≤ (threeFactorThreshold e : ℝ) - 2 * (e : ℝ) := by
  rw [three_factor_error]
  positivity

theorem three_factor_error_le (e : ℕ) (he : 1 ≤ e) :
    (threeFactorThreshold e : ℝ) - 2 * (e : ℝ) ≤ 8 * Real.sqrt (e : ℝ) := by
  rw [three_factor_error]
  have hc := Nat.ceil_lt_add_one (Real.sqrt_nonneg (7 * (e : ℝ)))
  have hseven : Real.sqrt (7 : ℝ) ≤ 3 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hs := mul_le_mul_of_nonneg_right hseven (Real.sqrt_nonneg (e : ℝ))
  rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 7)] at hs
  have he' : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
  have hroot : 1 ≤ Real.sqrt (e : ℝ) := Real.one_le_sqrt.mpr he'
  linarith

theorem many_factor_error_nonneg (k e : ℕ) (hk : 4 ≤ k) :
    0 ≤ (manyFactorThreshold k e : ℝ) - (e : ℝ) := by
  rw [many_factor_error k e hk]
  have hk' : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hc : 0 ≤ (⌈(((k + 1) * e : ℕ) : ℝ) ^ rootExponent k⌉₊ : ℝ) :=
    Nat.cast_nonneg _
  linarith

theorem many_factor_error_le (k e : ℕ) (hk : 4 ≤ k) (he : 1 ≤ e) :
    (manyFactorThreshold k e : ℝ) - (e : ℝ) ≤
      (2 * ((k + 1 : ℕ) : ℝ) ^ rootExponent k + 4 * (k : ℝ)) *
        (e : ℝ) ^ rootExponent k := by
  rw [many_factor_error k e hk]
  have hc := Nat.ceil_lt_add_one
    (Real.rpow_nonneg (Nat.cast_nonneg ((k + 1) * e)) (rootExponent k))
  have hm : (((k + 1) * e : ℕ) : ℝ) ^ rootExponent k =
      ((k + 1 : ℕ) : ℝ) ^ rootExponent k * (e : ℝ) ^ rootExponent k := by
    rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  have he' : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
  have hp : 1 ≤ (e : ℝ) ^ rootExponent k :=
    Real.one_le_rpow he' (by unfold rootExponent; positivity)
  calc
    _ ≤ 2 * (((k + 1) * e : ℕ) : ℝ) ^ rootExponent k + 4 * (k : ℝ) := by
      linarith
    _ = 2 * (((k + 1 : ℕ) : ℝ) ^ rootExponent k *
          (e : ℝ) ^ rootExponent k) + 4 * (k : ℝ) := by rw [hm]
    _ ≤ 2 * (((k + 1 : ℕ) : ℝ) ^ rootExponent k *
          (e : ℝ) ^ rootExponent k) + 4 * (k : ℝ) * (e : ℝ) ^ rootExponent k := by
      apply add_le_add le_rfl
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hp
        (show (0 : ℝ) ≤ 4 * (k : ℝ) by positivity)
    _ = _ := by ring

/-- The exact three-factor sufficient threshold is `2e + O(sqrt e)`
as the natural excess tends to infinity. -/
theorem three_factor_growth :
    (fun e : ℕ => (threeFactorThreshold e : ℝ) - 2 * (e : ℝ)) =O[atTop]
      (fun e : ℕ => Real.sqrt (e : ℝ)) := by
  apply IsBigO.of_bound 8
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with e he
  simp only [Real.norm_eq_abs, abs_of_nonneg (three_factor_error_nonneg e),
    abs_of_nonneg (Real.sqrt_nonneg (e : ℝ))]
  exact three_factor_error_le e he

/-- For every fixed `k ≥ 4`, the exact sufficient threshold is
`e + O_k(e^(1/ceil(k/2)))`, with the literal ordinary ceiling in the exponent. -/
theorem many_factor_growth (k : ℕ) (hk : 4 ≤ k) :
    (fun e : ℕ => (manyFactorThreshold k e : ℝ) - (e : ℝ)) =O[atTop]
      (fun e : ℕ => (e : ℝ) ^ (1 / ((⌈(k : ℝ) / 2⌉ : ℤ) : ℝ))) := by
  rw [← rootExponent_eq_printed k]
  apply IsBigO.of_bound
    (2 * ((k + 1 : ℕ) : ℝ) ^ rootExponent k + 4 * (k : ℝ))
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with e he
  simp only [Real.norm_eq_abs, abs_of_nonneg (many_factor_error_nonneg k e hk),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg e) (rootExponent k))]
  exact many_factor_error_le k e hk he

end PaperVerification.Segre.AsymptoticGrowth

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
