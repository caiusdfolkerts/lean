module
public import SegreVerified.Stage029
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


section SegreAsymptoticBounds

run_cmd do
  let out ← IO.getStderr
  out.putStrLn "SEGRE_STAGE SegreAsymptoticBounds"
  out.flush

/-!
# Explicit bounds following Theorem 6.3

These arithmetic lemmas turn the exact diagonal-core criterion into the two
real-root ceiling bounds on the final page of the paper. All inequalities are
proved uniformly in their natural-number parameters.
-/

set_option autoImplicit false


namespace PaperVerification.Segre.AsymptoticBounds

theorem three_factor_threshold (e q : ℕ) (he : 2 ≤ e) (hq : 7 * e ≤ q ^ 2) :
    3 * (2 * (q + 2) + 2 * (e - 2)) + e ≤
      ((q + 2) + 1) ^ (3 / 2) + ((q + 2) + 1) ^ ((3 + 1) / 2) := by
  have hs : e - 2 + 2 = e := Nat.sub_add_cancel he
  norm_num
  nlinarith

theorem three_factor_bound_exact (e q : ℕ) (he : 2 ≤ e) :
    2 * (q + 2) + 2 * (e - 2) = 2 * e + 2 * q := by
  have hs : e - 2 + 2 = e := Nat.sub_add_cancel he
  omega

/-- The first three binomial terms suffice, uniformly in the exponent. -/
theorem power_increment_lower_bound (t h q : ℕ) (hq : 2 ≤ q) :
    t ^ q + 2 * t * h + h ^ 2 ≤ (t + h) ^ q := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hq
  induction r with
  | zero => simp only [add_zero]; nlinarith
  | succ r ih =>
    by_cases hzero : t + h = 0
    · have ht : t = 0 := by omega
      have hh : h = 0 := by omega
      simp [ht, hh]
    · have hpos : 1 ≤ t + h := by omega
      have hmul := Nat.mul_le_mul_right (t + h) (ih (by omega))
      have hb : 2 * t * h + h ^ 2 ≤ (2 * t * h + h ^ 2) * (t + h) :=
        Nat.le_mul_of_pos_right _ hpos
      rw [show 2 + (r + 1) = (2 + r) + 1 by omega,
        pow_succ t (2 + r), pow_succ (t + h) (2 + r)]
      nlinarith [Nat.zero_le (t ^ (2 + r) * h)]

theorem many_factor_threshold (k e t : ℕ) (hk : 4 ≤ k) (he : 2 ≤ e)
    (ht : (k + 1) * e ≤ t ^ ((k + 1) / 2)) :
    k * (2 * (t + 2 * k) + (e - 2)) + e ≤
      ((t + 2 * k) + 1) ^ (k / 2) + ((t + 2 * k) + 1) ^ ((k + 1) / 2) := by
  have hq : 2 ≤ (k + 1) / 2 := by omega
  have hp := power_increment_lower_bound t (2 * k + 1) ((k + 1) / 2) hq
  have hs : e - 2 + 2 = e := Nat.sub_add_cancel he
  have heq : t + (2 * k + 1) = (t + 2 * k) + 1 := by omega
  rw [heq] at hp
  nlinarith [Nat.zero_le (((t + 2 * k) + 1) ^ (k / 2))]

theorem many_factor_bound_exact (k e t : ℕ) (he : 2 ≤ e) :
    2 * (t + 2 * k) + (e - 2) = e + 2 * t + 4 * k - 2 := by
  omega

theorem ceil_sqrt_bound (e : ℕ) :
    7 * e ≤ (⌈Real.sqrt (7 * (e : ℝ))⌉₊) ^ 2 := by
  have hceil := Nat.le_ceil (Real.sqrt (7 * (e : ℝ)))
  have hnonneg := Real.sqrt_nonneg (7 * (e : ℝ))
  have hsquare := Real.sq_sqrt (show 0 ≤ 7 * (e : ℝ) by positivity)
  have hreal : 7 * (e : ℝ) ≤ (⌈Real.sqrt (7 * (e : ℝ))⌉₊ : ℝ) ^ 2 := by
    nlinarith
  exact_mod_cast hreal

/-- The natural ceiling here is exactly the paper's ordinary integer ceiling. -/
theorem ceil_sqrt_cast (e : ℕ) :
    (⌈Real.sqrt (7 * (e : ℝ))⌉₊ : ℤ) = ⌈Real.sqrt (7 * (e : ℝ))⌉ :=
  Int.natCast_ceil_eq_ceil (Real.sqrt_nonneg _)

theorem ceil_root_cast (a q : ℕ) :
    (⌈(a : ℝ) ^ (1 / (q : ℝ))⌉₊ : ℤ) = ⌈(a : ℝ) ^ (1 / (q : ℝ))⌉ :=
  Int.natCast_ceil_eq_ceil (Real.rpow_nonneg (Nat.cast_nonneg a) _)

/-- Rounding up a nonnegative real root preserves its integer power bound. -/
theorem ceil_root_bound (a q : ℕ) (hq : q ≠ 0) :
    a ≤ (⌈(a : ℝ) ^ (1 / (q : ℝ))⌉₊) ^ q := by
  have hnonneg : 0 ≤ (a : ℝ) ^ (1 / (q : ℝ)) := Real.rpow_nonneg (by positivity) _
  have hpow := pow_le_pow_left₀ hnonneg
    (Nat.le_ceil ((a : ℝ) ^ (1 / (q : ℝ)))) q
  have hroot : ((a : ℝ) ^ (1 / (q : ℝ))) ^ q = (a : ℝ) := by
    simpa only [one_div] using Real.rpow_inv_natCast_pow (x := (a : ℝ)) (by positivity) hq
  rw [hroot] at hpow
  exact_mod_cast hpow

/-- The square-root bound stated after Theorem 6.3. -/
theorem three_factor_sqrt_threshold (e : ℕ) (he : 2 ≤ e) :
    3 * (2 * e + 2 * ⌈Real.sqrt (7 * (e : ℝ))⌉₊) + e ≤
      (⌈Real.sqrt (7 * (e : ℝ))⌉₊ + 3) ^ (3 / 2) +
      (⌈Real.sqrt (7 * (e : ℝ))⌉₊ + 3) ^ ((3 + 1) / 2) := by
  have h := three_factor_threshold e _ he (ceil_sqrt_bound e)
  rw [three_factor_bound_exact e _ he] at h
  simpa only [Nat.add_assoc] using h

/-- The root bound for at least four small factors, after Theorem 6.3. -/
theorem many_factor_root_threshold (k e : ℕ) (hk : 4 ≤ k) (he : 2 ≤ e) :
    let t := ⌈(((k + 1) * e : ℕ) : ℝ) ^ (1 / (((k + 1) / 2 : ℕ) : ℝ))⌉₊
    k * (e + 2 * t + 4 * k - 2) + e ≤
      (t + 2 * k + 1) ^ (k / 2) + (t + 2 * k + 1) ^ ((k + 1) / 2) := by
  dsimp only
  have h := many_factor_threshold k e _ hk he
    (ceil_root_bound ((k + 1) * e) ((k + 1) / 2) (by omega))
  rw [many_factor_bound_exact k e _ he] at h
  exact h

end PaperVerification.Segre.AsymptoticBounds

end SegreAsymptoticBounds

end
end
end ProbeLayer391

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


section SegreExcessAsymptotic

run_cmd do
  let out ← IO.getStderr
  out.putStrLn "SEGRE_STAGE SegreExcessAsymptotic"
  out.flush

/-!
# The real-root ceiling bounds after Theorem 6.3

The arithmetic bounds are applied to the complete diagonal-core theorem, then
to the actual full-slice multiplication map. The hypotheses retain the exact
ceilings printed on the final page of the paper. The natural ceiling agrees
with the integer ceiling by `AsymptoticBounds.ceil_sqrt_cast` and
`AsymptoticBounds.ceil_root_cast`; `ceil_half_cast` identifies the exponent.
-/

set_option autoImplicit false


namespace PaperVerification.Segre.ExcessAsymptotic

open Staircase RankParameters GenericRigidity DiagonalCore ExcessSixThree

/-- The natural exponent used by the diagonal criterion is literally the
ordinary integer ceiling of half the number of factors. -/
theorem ceil_half_cast (k : ℕ) :
    ⌈(k : ℝ) / 2⌉ = (((k + 1) / 2 : ℕ) : ℤ) := by
  have hlow : k ≤ 2 * ((k + 1) / 2) := by omega
  have hhigh : 2 * ((k + 1) / 2) < k + 2 := by omega
  have hlowReal : (k : ℝ) ≤ 2 * (((k + 1) / 2 : ℕ) : ℝ) := by
    exact_mod_cast hlow
  have hhighReal : 2 * (((k + 1) / 2 : ℕ) : ℝ) < (k : ℝ) + 2 := by
    exact_mod_cast hhigh
  apply Int.ceil_eq_iff.mpr
  simp only [Int.cast_natCast]
  constructor <;> linarith

variable {K : Type*} [Field K] [Infinite K]

/-- The complete three-factor rigidity consequence at the printed square-root
threshold, with no upper bound on the dimensions or the excess. -/
theorem three_factor_sqrt_graph_rigidity (e : ℕ) (he : 2 ≤ e)
    (n : Fin 3 → ℕ)
    (hn : ∀ i, 2 * e + 2 * ⌈Real.sqrt (7 * (e : ℝ))⌉₊ ≤ n i) :
    GenericallyRigid K (Fin (sideSum n + e)) (chainGraph n) := by
  let q := ⌈Real.sqrt (7 * (e : ℝ))⌉₊
  refine section_6_3_graph_rigidity 3 e (q + 2) (by omega) he ?_ ?_ n ?_
  · change 2 ≤ q + 2
    omega
  · change 3 * (2 * (q + 2) + 2 * (e - 2)) + e ≤ _
    exact AsymptoticBounds.three_factor_threshold e q he
      (AsymptoticBounds.ceil_sqrt_bound e)
  · intro i
    change 2 * (q + 2) + 2 * (e - 2) ≤ n i
    rw [AsymptoticBounds.three_factor_bound_exact e q he]
    exact hn i

/-- The corresponding full multiplication kernel contains exactly the Koszul
relations on a nonzero polynomial open in all original slice coefficients. -/
theorem three_factor_sqrt_exactness_certificate (e : ℕ) (he : 2 ≤ e)
    (n : Fin 3 → ℕ)
    (hn : ∀ i, 2 * e + 2 * ⌈Real.sqrt (7 * (e : ℝ))⌉₊ ≤ n i) :
    ∃ f : MvPolynomial (Cell n × Option (Fin (sideSum n + e))) K, f ≠ 0 ∧
      ∀ A : Matrix (Cell n) (Option (Fin (sideSum n + e))) K,
        MvPolynomial.eval (fun j => A j.1 j.2) f ≠ 0 →
          Function.Surjective A.vecMul ∧
          (Degeneration.multiplicationMatrix 1 A).rank =
            Fintype.card (Cell n) * (sideSum n + e + 1) -
              (sideSum n + e + 1).choose 2 ∧
          LinearMap.ker (KoszulRank.multiplication A) =
            LinearMap.range (KoszulDimension.koszulMatrix A) := by
  have h := HigherExcessRank.exactness_certificate_of_rigid
    (three_factor_sqrt_graph_rigidity (K := K) e he n hn)
  simpa only [Fintype.card_option, Fintype.card_fin] using h

/-- The exact real-root threshold for every fixed number of factors at least
four, retaining all larger tuples of factor dimensions. -/
theorem many_factor_root_graph_rigidity (k e : ℕ) (hk : 4 ≤ k) (he : 2 ≤ e)
    (n : Fin k → ℕ)
    (hn : ∀ i,
      e + 2 * ⌈(((k + 1) * e : ℕ) : ℝ) ^
        (1 / (((k + 1) / 2 : ℕ) : ℝ))⌉₊ + 4 * k - 2 ≤ n i) :
    GenericallyRigid K (Fin (sideSum n + e)) (chainGraph n) := by
  let t := ⌈(((k + 1) * e : ℕ) : ℝ) ^
    (1 / (((k + 1) / 2 : ℕ) : ℝ))⌉₊
  have hmin : minimumSide k = 1 := by
    simp only [minimumSide, if_neg (show k ≠ 3 by omega)]
  refine section_6_3_graph_rigidity k e (t + 2 * k) (by omega) he ?_ ?_ n ?_
  · rw [hmin]
    omega
  · simp only [threshold, hmin, one_mul]
    exact AsymptoticBounds.many_factor_threshold k e t hk he
      (AsymptoticBounds.ceil_root_bound ((k + 1) * e) ((k + 1) / 2) (by omega))
  · intro i
    simp only [threshold, hmin, one_mul]
    rw [AsymptoticBounds.many_factor_bound_exact k e t he]
    exact hn i

/-- Full degree-two Koszul exactness throughout the printed root-bound range. -/
theorem many_factor_root_exactness_certificate (k e : ℕ) (hk : 4 ≤ k) (he : 2 ≤ e)
    (n : Fin k → ℕ)
    (hn : ∀ i,
      e + 2 * ⌈(((k + 1) * e : ℕ) : ℝ) ^
        (1 / (((k + 1) / 2 : ℕ) : ℝ))⌉₊ + 4 * k - 2 ≤ n i) :
    ∃ f : MvPolynomial (Cell n × Option (Fin (sideSum n + e))) K, f ≠ 0 ∧
      ∀ A : Matrix (Cell n) (Option (Fin (sideSum n + e))) K,
        MvPolynomial.eval (fun j => A j.1 j.2) f ≠ 0 →
          Function.Surjective A.vecMul ∧
          (Degeneration.multiplicationMatrix 1 A).rank =
            Fintype.card (Cell n) * (sideSum n + e + 1) -
              (sideSum n + e + 1).choose 2 ∧
          LinearMap.ker (KoszulRank.multiplication A) =
            LinearMap.range (KoszulDimension.koszulMatrix A) := by
  have h := HigherExcessRank.exactness_certificate_of_rigid
    (many_factor_root_graph_rigidity (K := K) k e hk he n hn)
  simpa only [Fintype.card_option, Fintype.card_fin] using h

end PaperVerification.Segre.ExcessAsymptotic

end SegreExcessAsymptotic

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
