module
public import SegreVerified.Stage030.TensorCoordinates
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
  out.putStrLn "SEGRE_STAGE Stage031.CriticalFactorReindex"
  out.flush

/-!
# The original embedded scheme and the principal projective span theorems

The named sections preserve the original proof stages and local scopes.
-/


section SegreCriticalFactorReindex

/-!
# Literal critical spaces under every factor permutation

The all-factor operator below is the ordinary coordinate critical operator:
one coordinate is replaced while all other tensor indices are summed. Its
identification with the sliced operator retains both the small-factor and
last-factor equations. Together with the already constructed transport of
singular pure tensors, this proves invariance of full span and codimension
under permutations that may move the designated last factor.

-/

set_option autoImplicit false
open scoped Classical BigOperators

namespace PaperVerification.Segre.CriticalFactorReindex

open TensorFactorReindex

section ArbitraryFactors

variable {I I' K : Type*} [Fintype I] [DecidableEq I]
  [Fintype I'] [DecidableEq I'] [Field K]
variable {σ : I → Type*} [∀ i, Fintype (σ i)]

/-- The original ordered critical coordinate, with the complete sum over
all remaining factor coordinates. The indicator merely avoids introducing
a separate index type for the remaining coordinates. -/
def coefficient (T B : (∀ i : I, σ i) → K) (i : I) (a b : σ i) : K :=
  ∑ v : ∀ i, σ i,
    if v i = a then T v * B (Function.update v i b) -
      T (Function.update v i b) * B v else 0

/-- Every original critical equation, before restriction to pure tensors. -/
def criticalOperator (T : (∀ i : I, σ i) → K) :
    ((∀ i : I, σ i) → K) →ₗ[K] ((Σ i : I, σ i × σ i) → K) where
  toFun B q := coefficient T B q.1 q.2.1 q.2.2
  map_add' B C := by
    funext q
    unfold coefficient
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    by_cases h : v q.1 = q.2.1 <;> simp [h] <;> ring
  map_smul' c B := by
    funext q
    simp only [coefficient, RingHom.id_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    by_cases h : v q.1 = q.2.1 <;> simp [h] <;> ring

/-- The full critical space in the ordinary, unsliced coefficient array. -/
def criticalSpace (T : (∀ i : I, σ i) → K) :
    Submodule K ((∀ i : I, σ i) → K) :=
  LinearMap.ker (criticalOperator T)

theorem mem_criticalSpace (T B : (∀ i : I, σ i) → K) :
    B ∈ criticalSpace T ↔ ∀ i a b, coefficient T B i a b = 0 := by
  change ((fun q : Σ i : I, σ i × σ i => coefficient T B q.1 q.2.1 q.2.2) = 0) ↔ _
  constructor
  · intro h i a b
    exact congrFun h ⟨i, a, b⟩
  · intro h
    funext q
    exact h q.1 q.2.1 q.2.2

/-- Factor permutation commutes with replacement of one coordinate. -/
theorem cellEquiv_update (e : I' ≃ I) (v : ∀ i : I', σ (e i))
    (i : I') (b : σ (e i)) :
    cellEquiv e (Function.update v i b) =
      Function.update (cellEquiv e v) (e i) b := by
  funext j
  obtain ⟨j, rfl⟩ := e.surjective j
  by_cases h : j = i
  · subst j
    simp only [cellEquiv_apply, Function.update_self]
  · have he : e j ≠ e i := fun he => h (e.injective he)
    simp only [cellEquiv_apply, Function.update_of_ne h, Function.update_of_ne he]

/-- Every critical coordinate is transported exactly, including its sign. -/
theorem coefficient_reindex (e : I' ≃ I) (T B : (∀ i : I, σ i) → K)
    (i : I') (a b : σ (e i)) :
    coefficient (tensorEquiv e T) (tensorEquiv e B) i a b =
      coefficient T B (e i) a b := by
  unfold coefficient
  apply Fintype.sum_equiv (cellEquiv e)
  intro v
  change (if v i = a then
    T (cellEquiv e v) * B (cellEquiv e (Function.update v i b)) -
      T (cellEquiv e (Function.update v i b)) * B (cellEquiv e v) else 0) =
    (if cellEquiv e v (e i) = a then
      T (cellEquiv e v) * B (Function.update (cellEquiv e v) (e i) b) -
        T (Function.update (cellEquiv e v) (e i) b) * B (cellEquiv e v) else 0)
  rw [cellEquiv_apply, cellEquiv_update]

/-- The complete critical-space membership condition is invariant under
every permutation of factors. -/
theorem mem_criticalSpace_reindex (e : I' ≃ I) (T B : (∀ i : I, σ i) → K) :
    tensorEquiv e B ∈ criticalSpace (tensorEquiv e T) ↔ B ∈ criticalSpace T := by
  rw [mem_criticalSpace, mem_criticalSpace]
  simp only [coefficient_reindex]
  constructor
  · intro h i
    obtain ⟨j, rfl⟩ := e.surjective i
    exact h j
  · intro h i
    exact h (e i)

/-- Equality of the entire transported critical submodule. -/
theorem criticalSpace_reindex (e : I' ≃ I) (T : (∀ i : I, σ i) → K) :
    criticalSpace (tensorEquiv e T) = (criticalSpace T).map (tensorEquiv e).toLinearMap := by
  ext B
  constructor
  · intro hB
    refine ⟨(tensorEquiv e).symm B, ?_, (tensorEquiv e).apply_symm_apply B⟩
    apply (mem_criticalSpace_reindex e T ((tensorEquiv e).symm B)).mp
    simpa only [LinearEquiv.apply_symm_apply] using hB
  · rintro ⟨C, hC, rfl⟩
    exact (mem_criticalSpace_reindex e T C).mpr hC

/-- The original critical-space dimension is preserved. -/
theorem finrank_criticalSpace_reindex (e : I' ≃ I) (T : (∀ i : I, σ i) → K) :
    Module.finrank K (criticalSpace (tensorEquiv e T)) =
      Module.finrank K (criticalSpace T) := by
  rw [criticalSpace_reindex, LinearEquiv.finrank_map_eq]

/-- The dimension of the literal singular pure-tensor span is preserved. -/
theorem finrank_incidenceSpan_reindex (e : I' ≃ I) (T : (∀ i : I, σ i) → K) :
    Module.finrank K (incidenceSpan (tensorEquiv e T)) =
      Module.finrank K (incidenceSpan T) := by
  rw [incidenceSpan_reindex, LinearEquiv.finrank_map_eq]

/-- The codimension used in Corollary 1.2 is invariant under arbitrary
factor permutations, including permutations of the final factor. -/
theorem defect_reindex (e : I' ≃ I) (T : (∀ i : I, σ i) → K) :
    Module.finrank K (criticalSpace (tensorEquiv e T)) -
        Module.finrank K (incidenceSpan (tensorEquiv e T)) =
      Module.finrank K (criticalSpace T) - Module.finrank K (incidenceSpan T) := by
  rw [finrank_criticalSpace_reindex, finrank_incidenceSpan_reindex]

/-- Full span is invariant under every factor permutation as an equality
of actual subspaces, rather than merely an equality of their dimensions. -/
theorem full_span_reindex (e : I' ≃ I) (T : (∀ i : I, σ i) → K) :
    incidenceSpan (tensorEquiv e T) = criticalSpace (tensorEquiv e T) ↔
      incidenceSpan T = criticalSpace T := by
  rw [incidenceSpan_reindex, criticalSpace_reindex]
  exact (Submodule.map_injective_of_injective (tensorEquiv e).injective).eq_iff

/-- Any complete generic defect theorem transfers to the permuted full
coefficient space by a proved injective polynomial variable permutation. -/
theorem generic_defect_reindex (e : I' ≃ I) (d : ℕ)
    (h : ∃ p : MvPolynomial (∀ i : I, σ i) K, p ≠ 0 ∧
      ∀ T, MvPolynomial.eval T p ≠ 0 →
        Module.finrank K (criticalSpace T) - Module.finrank K (incidenceSpan T) = d) :
    ∃ p : MvPolynomial (∀ i : I', σ (e i)) K, p ≠ 0 ∧
      ∀ T, MvPolynomial.eval T p ≠ 0 →
        Module.finrank K (criticalSpace T) - Module.finrank K (incidenceSpan T) = d := by
  obtain ⟨p, hp, hw⟩ := h
  let q := MvPolynomial.rename (cellEquiv e).symm p
  have hq : q ≠ 0 := by
    intro hz
    apply hp
    apply MvPolynomial.rename_injective _ (cellEquiv e).symm.injective
    simpa only [map_zero] using hz
  refine ⟨q, hq, ?_⟩
  intro T hT
  have heval : MvPolynomial.eval ((tensorEquiv e).symm T) p ≠ 0 := by
    change MvPolynomial.eval (fun x => T ((cellEquiv e).symm x)) p ≠ 0
    simpa only [q, MvPolynomial.eval_rename, Function.comp_def] using hT
  have hd := hw ((tensorEquiv e).symm T) heval
  have he := defect_reindex e ((tensorEquiv e).symm T)
  have hround : tensorEquiv e ((tensorEquiv e).symm T) = T :=
    (tensorEquiv e).apply_symm_apply T
  have hdim := congrArg
    (fun U : (∀ i : I', σ (e i)) → K =>
      Module.finrank K (criticalSpace U) - Module.finrank K (incidenceSpan U)) hround
  exact hdim.symm.trans (he.trans hd)

end ArbitraryFactors

section Slices

open Staircase Monomials CriticalGraph SingularSpan FullGraphChartReindex
open TensorFactorSplitting

variable {I J K : Type} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Field K] {n : I → ℕ}

theorem update_originalCell_none (v : Cell n) (j b : J) :
    Function.update ((originalCellEquiv (n := n) (J := J)).symm (v, j)) none b =
      (originalCellEquiv (n := n) (J := J)).symm (v, b) := by
  funext o
  cases o with
  | none => rw [Function.update_self] <;> rfl
  | some i => rw [Function.update_of_ne (by simp)] <;> rfl

theorem update_originalCell_some (v : Cell n) (j : J) (i : I) (b : Fin (n i + 1)) :
    Function.update ((originalCellEquiv (n := n) (J := J)).symm (v, j)) (some i) b =
      (originalCellEquiv (n := n) (J := J)).symm (Function.update v i b, j) := by
  funext o
  cases o with
  | none => rw [Function.update_of_ne (by simp)] <;> rfl
  | some h =>
      by_cases hh : h = i
      · subst h
        rw [Function.update_self]
        change b = Function.update v i b i
        rw [Function.update_self]
      · rw [Function.update_of_ne (by simpa only [ne_eq, Option.some.injEq] using hh)]
        change v h = Function.update v i b h
        rw [Function.update_of_ne hh]

theorem update_assemble (i : I) (a b : Fin (n i + 1)) (w : OtherCell n i) :
    Function.update (assemble i a w) i b = assemble i b w := by
  funext h
  by_cases hh : h = i
  · subst h
    rw [Function.update_self, assemble_same]
  · rw [Function.update_of_ne hh]
    exact (assemble_other i a w ⟨h, hh⟩).trans (assemble_other i b w ⟨h, hh⟩).symm

/-- The all-factor equation for the separated factor is precisely the
original last critical equation. -/
theorem coefficient_none (A B : Matrix (Cell n) J K) (a b : J) :
    coefficient (originalTensor A) (originalTensor B) none a b =
      lastCriticalOperator A B (a, b) := by
  classical
  unfold coefficient
  rw [← Equiv.sum_comp (originalCellEquiv (n := n) (J := J)).symm,
    Fintype.sum_prod_type]
  simp only [update_originalCell_none]
  change (∑ v : Cell n, ∑ j : J,
    if j = a then A v j * B v b - A v b * B v j else 0) = _
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] <;> rfl

/-- Every remaining all-factor equation is precisely the corresponding
original small-factor critical equation, with the complete sum over slices. -/
theorem coefficient_some (A B : Matrix (Cell n) J K) (i : I)
    (a b : Fin (n i + 1)) :
    coefficient (originalTensor A) (originalTensor B) (some i) a b =
      CriticalGraph.criticalOperator A B ⟨i, a, b⟩ := by
  classical
  unfold coefficient
  rw [← Equiv.sum_comp (originalCellEquiv (n := n) (J := J)).symm,
    Fintype.sum_prod_type]
  simp only [update_originalCell_some]
  change (∑ v : Cell n, ∑ j : J,
    if v i = a then A v j * B (Function.update v i b) j -
      A (Function.update v i b) j * B v j else 0) = _
  rw [← Equiv.sum_comp (Equiv.piSplitAt i (fun h => Fin (n h + 1))).symm,
    Fintype.sum_prod_type]
  change (∑ a', ∑ w : OtherCell n i, ∑ j : J,
    if assemble i a' w i = a then
      A (assemble i a' w) j * B (Function.update (assemble i a' w) i b) j -
      A (Function.update (assemble i a' w) i b) j * B (assemble i a' w) j else 0) = _
  simp only [assemble_same, update_assemble, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] <;> rfl

/-- All critical equations in the unsliced tensor are exactly both sets
of critical equations in the sliced tensor; no factor is omitted. -/
theorem originalTensor_mem_criticalSpace_iff (A B : Matrix (Cell n) J K) :
    originalTensor B ∈ criticalSpace (originalTensor A) ↔ B ∈ fullCriticalSpace A := by
  rw [mem_criticalSpace]
  change (∀ i a b, coefficient (originalTensor A) (originalTensor B) i a b = 0) ↔
    CriticalGraph.criticalOperator A B = 0 ∧ lastCriticalOperator A B = 0
  constructor
  · intro h
    constructor
    · funext q
      exact (coefficient_some A B q.1 q.2.1 q.2.2).symm.trans (h (some q.1) q.2.1 q.2.2)
    · funext q
      exact (coefficient_none A B q.1 q.2).symm.trans (h none q.1 q.2)
  · rintro ⟨hs, hl⟩ i a b
    cases i with
    | none => rw [coefficient_none]; exact congrFun hl (a, b)
    | some i => rw [coefficient_some]; exact congrFun hs ⟨i, a, b⟩

/-- The full critical subspace is transported through the original
coefficient reshaping, matching the existing singular-span equivalence. -/
theorem fullCriticalSpace_eq_map (A : Matrix (Cell n) J K) :
    fullCriticalSpace A =
      (criticalSpace (originalTensor A)).map matrixEquiv.toLinearMap := by
  ext B
  constructor
  · intro hB
    exact ⟨originalTensor B, (originalTensor_mem_criticalSpace_iff A B).mpr hB,
      matrixEquiv_originalTensor B⟩
  · rintro ⟨T, hT, rfl⟩
    apply (originalTensor_mem_criticalSpace_iff A (matrixEquiv T)).mp
    change T ∈ criticalSpace (originalTensor A) at hT
    rw [show originalTensor (matrixEquiv T) = T from matrixEquiv.symm_apply_apply T]
    exact hT

/-- The literal matrix-space defect is the full unsliced tensor defect. -/
theorem defect_originalTensor (A : Matrix (Cell n) J K) :
    Module.finrank K (criticalSpace (originalTensor A)) -
        Module.finrank K (incidenceSpan (originalTensor A)) =
      Module.finrank K (fullCriticalSpace A) - Module.finrank K (singularSpan A) := by
  rw [fullCriticalSpace_eq_map, singularSpan_eq_map_incidenceSpan,
    LinearEquiv.finrank_map_eq, LinearEquiv.finrank_map_eq]

/-- A full-coefficient sliced defect certificate gives the same defect
on the original unsliced coefficient space. -/
theorem generic_defect_of_slices (d : ℕ)
    (h : ∃ p : MvPolynomial (Cell n × J) K, p ≠ 0 ∧
      ∀ A : Matrix (Cell n) J K,
        MvPolynomial.eval (fun q => A q.1 q.2) p ≠ 0 →
          Module.finrank K (fullCriticalSpace A) - Module.finrank K (singularSpan A) = d) :
    ∃ p : MvPolynomial (∀ i : Option I, FullFactor n J i) K, p ≠ 0 ∧
      ∀ T, MvPolynomial.eval T p ≠ 0 →
        Module.finrank K (criticalSpace T) - Module.finrank K (incidenceSpan T) = d := by
  obtain ⟨p, hp, hw⟩ := h
  refine ⟨TensorFactorSplitting.certificatePullback p,
    TensorFactorSplitting.certificatePullback_ne_zero hp, ?_⟩
  intro T hT
  have he : originalTensor (matrixEquiv T) = T := matrixEquiv.symm_apply_apply T
  rw [← he, defect_originalTensor]
  apply hw
  rwa [← TensorFactorSplitting.eval_certificatePullback]

end Slices
end PaperVerification.Segre.CriticalFactorReindex

end SegreCriticalFactorReindex


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
