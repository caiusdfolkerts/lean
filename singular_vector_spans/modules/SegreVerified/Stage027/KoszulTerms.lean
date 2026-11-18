module
public import SegreVerified.Stage025.ExteriorVanishing
public import SegreVerified.Stage026
public import Lean.Util.CollectAxioms
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
set_option maxHeartbeats 600000

run_cmd do
  let out ← IO.getStderr
  out.putStrLn "SEGRE_STAGE Stage027.KoszulTerms"
  out.flush

/-!
# The actual critical bundle and its weighted Koszul complex

The named sections preserve the original proof stages and local scopes.
-/

set_option autoImplicit false

section SegreFullProductKoszulTerms

/-!
# The full finite product terms in the singular-section Koszul argument

The objects here are literal finite coproducts of the actual external products
of actual exterior Euler sheaves. Every tuple of exterior degrees summing to
r occurs. We prove the whole coproduct's cohomology gap, in both graph and
balanced formats, and prove that the entire term is zero beyond the sum of
the projective dimensions. No termwise vanishing or comparison theorem is
assumed.

Identification with the corresponding exterior power of the singular
section's source is a separate construction.
-/

set_option autoImplicit false

namespace PaperVerification.Segre.FullProductKoszulTerms

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open TauCeti.AlgebraicGeometry.Scheme.Modules
open FixedProductCohomology ProductKoszulVanishing TwistedExteriorEuler
open scoped BigOperators

universe u

/-- All exterior-degree tuples of the specified total degree. -/
abbrev Degrees (k r : ℕ) := {p : Fin (k + 1) → ℕ // (∑ i, p i) = r}

theorem degree_le_total {k r : ℕ} (p : Degrees k r) (i : Fin (k + 1)) :
    p.val i ≤ r := by
  calc
    p.val i ≤ ∑ j, p.val j :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    _ = r := p.property

/-- The index is finite because every coordinate is at most the fixed total;
no decomposition is omitted by replacing it with a bounded index. -/
instance finiteDegrees (k r : ℕ) : Finite (Degrees k r) := by
  let f : Degrees k r → (Fin (k + 1) → Fin (r + 1)) :=
    fun p i => ⟨p.val i, Nat.lt_succ_of_le (degree_le_total p i)⟩
  apply Finite.of_injective f
  intro p q h
  apply Subtype.ext
  funext i
  exact congrArg Fin.val (congrFun h i)

/-- Finite coproducts of genuine sheaves with vanishing cohomology have
vanishing cohomology. This uses the actual additive cohomology functor. -/
theorem cohomology_coproduct_subsingleton {X : Scheme.{u}} {ι : Type}
    [Finite ι] (M : ι → X.Modules) (q : ℕ)
    (hM : ∀ i, Subsingleton (Cohomology (M i) q)) :
    Subsingleton (Cohomology (∐ M) q) := by
  let H := cohomologyFunctor X q
  have hz (i : ι) : IsZero (H.obj (M i)) := by
    letI : Subsingleton (H.obj (M i)) := hM i
    exact AddCommGrpCat.isZero_of_subsingleton _
  have hsum : IsZero (∐ fun i => H.obj (M i)) := by
    rw [IsZero.iff_id_eq_zero]
    apply Sigma.hom_ext
    intro i
    simpa only [Category.comp_id, comp_zero] using
      (hz i).eq_of_src (Sigma.ι (fun j => H.obj (M j)) i) 0
  exact AddCommGrpCat.subsingleton_of_isZero
    (hsum.of_iso (PreservesCoproduct.iso H M))

variable (K : Type u) [Field K]

/-- The complete actual exterior-product term for an arbitrary twist rule. -/
def fullTerm {k : ℕ} (I : Fin (k + 1) → Type u)
    [∀ i, Fintype (I i)] [∀ i, DecidableEq (I i)] (r : ℕ)
    (t : (Fin (k + 1) → ℕ) → Fin (k + 1) → ℤ) :
    (CoveredScheme.finiteProduct (fun i => projectiveScheme K (I i))).scheme.Modules :=
  ∐ fun p : Degrees k r => exteriorProduct K I p.val (t p.val)

/-- The graph-format gap for the whole term, including every summand. -/
theorem graph_fullTerm_cohomology_vanishes {k : ℕ}
    (I : Fin (k + 1) → Type u) [∀ i, Fintype (I i)] [∀ i, DecidableEq (I i)]
    (hI : ∀ i, 0 < Fintype.card (I i)) (r q : ℕ) (hr : 2 ≤ r) (hq : q < r) :
    Subsingleton (Cohomology
      (fullTerm K I r (fun p i => 2 * (p i : ℤ) - 2 * (r : ℤ) + 2)) q) := by
  apply cohomology_coproduct_subsingleton
  intro p
  exact graph_format_cohomology_vanishes K I hI p.val r q hr p.property hq

/-- The balanced-format gap for the whole term, with the full triangle
inequalities and without a restriction on the characteristic. -/
theorem balanced_fullTerm_cohomology_vanishes {k : ℕ}
    (I : Fin (k + 1) → Type u) [∀ i, Fintype (I i)] [∀ i, DecidableEq (I i)]
    (hI : ∀ i, 0 < Fintype.card (I i)) (htriangle : TriangleDimensions I)
    (r q : ℕ) (hr : 2 ≤ r) (hq : q < r) :
    Subsingleton (Cohomology
      (fullTerm K I r (fun p i => 1 + 2 * (p i : ℤ) - (r : ℤ))) q) := by
  apply cohomology_coproduct_subsingleton
  intro p
  exact balanced_format_cohomology_vanishes K I hI htriangle
    p.val r q hr p.property hq

/-- A zero factor makes the literal finite external tensor product zero. -/
theorem finiteExternalTensor_isZero {k : ℕ}
    (A : Fin (k + 1) → CoveredScheme K) (M : ∀ i, (A i).scheme.Modules)
    (hM : ∃ i, IsZero (M i)) : IsZero (CoveredScheme.finiteExternalTensor A M) := by
  induction k with
  | zero =>
      obtain ⟨i, hi⟩ := hM
      have he : i = (0 : Fin 1) := Fin.eq_zero i
      subst i
      exact hi
  | succ k ih =>
      obtain ⟨i, hi⟩ := hM
      let B := CoveredScheme.finiteProduct (fun j : Fin (k + 1) => A j.succ)
      let N := CoveredScheme.finiteExternalTensor (fun j : Fin (k + 1) => A j.succ)
        (fun j => M j.succ)
      change IsZero
        (((AlgebraicGeometry.Scheme.Modules.pullback (pullback.fst (A 0).toBase B.toBase)).obj (M 0)) ⊗
          ((AlgebraicGeometry.Scheme.Modules.pullback (pullback.snd (A 0).toBase B.toBase)).obj N))
      induction i using Fin.cases with
      | zero =>
          exact (tensorRight _).map_isZero
            ((AlgebraicGeometry.Scheme.Modules.pullback (pullback.fst (A 0).toBase B.toBase)).map_isZero hi)
      | succ i =>
          have hN : IsZero N := ih _ _ ⟨i, hi⟩
          exact (tensorLeft _).map_isZero
            ((AlgebraicGeometry.Scheme.Modules.pullback (pullback.snd (A 0).toBase B.toBase)).map_isZero hN)

/-- Above the sum of the actual projective dimensions every summand has a
zero exterior factor, so the complete term is zero, for every twist rule. -/
theorem fullTerm_isZero_of_degree_gt {k : ℕ}
    (I : Fin (k + 1) → Type u) [∀ i, Fintype (I i)] [∀ i, DecidableEq (I i)]
    (hI : ∀ i, 0 < Fintype.card (I i)) (r : ℕ)
    (hr : (∑ i, (Fintype.card (I i) - 1)) < r)
    (t : (Fin (k + 1) → ℕ) → Fin (k + 1) → ℤ) :
    IsZero (fullTerm K I r t) := by
  change IsZero (∐ fun p : Degrees k r => exteriorProduct K I p.val (t p.val))
  have hz (p : Degrees k r) : IsZero (exteriorProduct K I p.val (t p.val)) := by
    obtain ⟨i, hi⟩ : ∃ i, Fintype.card (I i) ≤ p.val i := by
      by_contra hn
      have hle (i : Fin (k + 1)) : p.val i ≤ Fintype.card (I i) - 1 := by
        have hh : p.val i < Fintype.card (I i) :=
          Nat.lt_of_not_ge (fun h => hn ⟨i, h⟩)
        omega
      have hs : (∑ i, p.val i) ≤ ∑ i, (Fintype.card (I i) - 1) :=
        Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hle i)
      have hrs : r ≤ ∑ i, (Fintype.card (I i) - 1) :=
        p.property ▸ hs
      exact (Nat.not_le_of_gt hr) hrs
    exact finiteExternalTensor_isZero K _ _
      ⟨i, ExteriorCohomology.exteriorKernelTwist_isZero (hI i) (p.val i) hi _⟩
  rw [IsZero.iff_id_eq_zero]
  apply Sigma.hom_ext
  intro p
  simpa only [Category.comp_id, comp_zero] using
    (hz p).eq_of_src (Sigma.ι
      (fun s : Degrees k r => exteriorProduct K I s.val (t s.val)) p) 0

end PaperVerification.Segre.FullProductKoszulTerms

end SegreFullProductKoszulTerms

run_cmd do
  let out ← IO.getStderr
  out.putStrLn "SEGRE_PROGRESS Stage027.ExteriorCoordinates product-vanishing"
  out.flush


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
