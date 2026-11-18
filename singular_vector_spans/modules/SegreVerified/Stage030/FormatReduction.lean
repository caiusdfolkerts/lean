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

@[expose] public section
noncomputable section
set_option autoImplicit false

section SegreTensorCoordinateReindex

/-!
# Independent coordinate permutations in all factors

Only coordinate permutations are used: these preserve the paper's fixed
coordinate bilinear forms. The result is not a claim of invariance under an
arbitrary change of basis. It lets dependent factor reindexing be connected to
the numerical and `Option` presentations with exact type-safe equivalences.

-/

set_option autoImplicit false
open scoped Classical BigOperators

namespace PaperVerification.Segre.TensorCoordinateReindex

open TangentKernel TensorFactorReindex

variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K]
variable {σ τ : I → Type*} [∀ i, Fintype (σ i)] [∀ i, Fintype (τ i)]

def tensorEquiv (e : ∀ i, τ i ≃ σ i) :
    ((∀ i, σ i) → K) ≃ₗ[K] ((∀ i, τ i) → K) where
  toFun T a := T (Equiv.piCongrRight e a)
  invFun T a := T ((Equiv.piCongrRight e).symm a)
  left_inv T := by funext a; simp
  right_inv T := by funext a; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def vectors (e : ∀ i, τ i ≃ σ i) (v : ∀ i, σ i → K) :
    ∀ i, τ i → K := fun i a => v i (e i a)

theorem vectors_nonzero (e : ∀ i, τ i ≃ σ i) (v : ∀ i, σ i → K)
    (hv : ∀ i, v i ≠ 0) : ∀ i, vectors e v i ≠ 0 := by
  intro i h
  apply hv i
  funext a
  have ha := congrFun h ((e i).symm a)
  simpa only [vectors, Equiv.apply_symm_apply, Pi.zero_apply] using ha

theorem tensorEquiv_pureTensor (e : ∀ i, τ i ≃ σ i) (v : ∀ i, σ i → K) :
    tensorEquiv e (pureTensor v) = pureTensor (vectors e v) := rfl

theorem incidence_zero_reindex (e : ∀ i, τ i ≃ σ i)
    (v : ∀ i, σ i → K) (T : (∀ i, σ i) → K) (hv : ∀ i, v i ≠ 0) :
    singularIncidenceMap (vectors e v) (tensorEquiv e T) = 0 ↔
      singularIncidenceMap v T = 0 := by
  rw [singularIncidenceMap_eq_zero_iff_of_nonzero _ _ (vectors_nonzero e v hv),
    singularIncidenceMap_eq_zero_iff_of_nonzero _ _ hv]
  constructor
  · intro h i
    obtain ⟨c, hc⟩ := h i
    refine ⟨c, ?_⟩
    funext a
    have ha := congrFun hc ((e i).symm a)
    change contraction (fun i b => v i (e i b))
      (fun b => T (Equiv.piCongrRight e b)) i ((e i).symm a) =
        c * v i (e i ((e i).symm a)) at ha
    rw [CriticalChartReindex.contraction_piCongr, Equiv.apply_symm_apply] at ha
    exact ha
  · intro h i
    obtain ⟨c, hc⟩ := h i
    refine ⟨c, ?_⟩
    funext a
    change contraction (fun i b => v i (e i b))
      (fun b => T (Equiv.piCongrRight e b)) i a = c * v i (e i a)
    rw [CriticalChartReindex.contraction_piCongr]
    exact congrFun hc (e i a)

theorem incidenceGenerators_reindex (e : ∀ i, τ i ≃ σ i) (T : (∀ i, σ i) → K) :
    incidenceGenerators (tensorEquiv e T) = tensorEquiv e '' incidenceGenerators T := by
  ext B
  constructor
  · rintro ⟨v', hv', hs', rfl⟩
    let v : ∀ i, σ i → K := fun i a => v' i ((e i).symm a)
    have hvr : vectors e v = v' := by
      funext i a
      exact congrArg (v' i) ((e i).symm_apply_apply a)
    have hv : ∀ i, v i ≠ 0 := by
      intro i h
      apply hv' i
      funext a
      have ha := congrFun h (e i a)
      simpa only [v, Equiv.symm_apply_apply, Pi.zero_apply] using ha
    refine ⟨pureTensor v, ?_, ?_⟩
    · refine ⟨v, hv, ?_, rfl⟩
      apply (incidence_zero_reindex e v T hv).mp
      rw [hvr]
      exact hs'
    · rw [tensorEquiv_pureTensor, hvr]
  · rintro ⟨C, ⟨v, hv, hs, rfl⟩, rfl⟩
    refine ⟨vectors e v, vectors_nonzero e v hv,
      (incidence_zero_reindex e v T hv).mpr hs, tensorEquiv_pureTensor e v⟩

theorem incidenceSpan_reindex (e : ∀ i, τ i ≃ σ i) (T : (∀ i, σ i) → K) :
    incidenceSpan (tensorEquiv e T) =
      (incidenceSpan T).map (tensorEquiv e).toLinearMap := by
  rw [incidenceSpan, incidenceGenerators_reindex, incidenceSpan, Submodule.map_span]
  rfl

theorem tensor_mem_span_reindex (e : ∀ i, τ i ≃ σ i) (T : (∀ i, σ i) → K) :
    tensorEquiv e T ∈ incidenceSpan (tensorEquiv e T) ↔ T ∈ incidenceSpan T := by
  rw [incidenceSpan_reindex]
  constructor
  · rintro ⟨B, hB, he⟩
    exact (tensorEquiv e).injective he ▸ hB
  · intro h
    exact ⟨T, h, rfl⟩

/-- An actual nonzero principal-open certificate transfers through the
complete coordinate permutation, without an additional rank assumption. -/
theorem generic_tensor_mem_span_reindex (e : ∀ i, τ i ≃ σ i)
    (h : ∃ p : MvPolynomial (∀ i, τ i) K, p ≠ 0 ∧
      ∀ T, MvPolynomial.eval T p ≠ 0 → T ∈ incidenceSpan T) :
    ∃ p : MvPolynomial (∀ i, σ i) K, p ≠ 0 ∧
      ∀ T, MvPolynomial.eval T p ≠ 0 → T ∈ incidenceSpan T := by
  obtain ⟨p, hp, hmem⟩ := h
  let q := MvPolynomial.rename (Equiv.piCongrRight e) p
  have hq : q ≠ 0 := by
    intro hq
    apply hp
    apply MvPolynomial.rename_injective _ (Equiv.piCongrRight e).injective
    simpa only [map_zero] using hq
  refine ⟨q, hq, ?_⟩
  intro T hT
  apply (tensor_mem_span_reindex e T).mp
  apply hmem
  change MvPolynomial.eval (T ∘ Equiv.piCongrRight e) p ≠ 0
  rwa [← MvPolynomial.eval_rename]

end PaperVerification.Segre.TensorCoordinateReindex

end SegreTensorCoordinateReindex

section SegreAllFormatReduction

/-!
# The exhaustive format reduction for tensor membership

Every factor can serve as the distinguished graph factor. Its removal uses
the explicit `Fin.succAbove` permutation, and the resulting certificate is
pulled back to the entire original tensor coefficient space. The remaining
case is exactly the system of triangle inequalities in Section 2.2.

The final assembly lemmas name the balanced and graph inputs explicitly;
they are coordinate reductions, not stand-alone proofs of Theorem 1.3.
-/

set_option autoImplicit false
open scoped Classical BigOperators

namespace PaperVerification.Segre.AllFormatReduction

open Staircase Monomials GraphSpan CriticalGraph SingularSpan
open TensorFactorReindex FullGraphChartReindex

variable {K : Type} [Field K] [Infinite K]

/-- The literal projective dimensions after removing a chosen factor. -/
def smallerDimensions {k : ℕ} (n : Fin (k+1) → ℕ) (i : Fin (k+1)) : Fin k → ℕ :=
  fun j => n (i.succAbove j)

def chosenFactorEquiv {k : ℕ} (i : Fin (k+1)) : Option (Fin k) ≃ Fin (k+1) :=
  (finSuccEquiv' i).symm

/-- Only the dependent presentation changes; the individual coordinates
remain the same finite ordinals. -/
def chosenCoordinateEquiv {k : ℕ} (n : Fin (k+1) → ℕ) (i : Fin (k+1)) :
    ∀ o : Option (Fin k),
      FullFactor (smallerDimensions n i) (Fin (n i+1)) o ≃
        Fin (n (chosenFactorEquiv i o)+1) := by
  intro o
  cases o <;> exact Equiv.refl _

theorem sum_smallerDimensions {k : ℕ} (n : Fin (k+1) → ℕ) (i : Fin (k+1)) :
    sideSum (smallerDimensions n i) = ∑ j ∈ Finset.univ.erase i, n j := by
  rw [Finset.sum_subtype (p := fun j : Fin (k+1) => j ≠ i)
    (Finset.univ.erase i) (by simp)]
  unfold sideSum
  apply Fintype.sum_equiv (finSuccAboveEquiv i)
  intro j
  rfl

/-- A generic graph-span membership theorem, for a factor in any position,
transfers to the original tensor coordinates and the actual singular span. -/
theorem generic_mem_span_chosen_factor {k : ℕ} (n : Fin (k+1) → ℕ) (i : Fin (k+1))
    (hgraph : ∃ p : MvPolynomial (Cell (smallerDimensions n i) × Fin (n i+1)) K,
      p ≠ 0 ∧ ∀ A : Matrix (Cell (smallerDimensions n i)) (Fin (n i+1)) K,
        MvPolynomial.eval (fun q => A q.1 q.2) p ≠ 0 → A ∈ singularSpan A) :
    ∃ p : MvPolynomial (Cell n) K, p ≠ 0 ∧
      ∀ T : Cell n → K, MvPolynomial.eval T p ≠ 0 → T ∈ incidenceSpan T := by
  have hoption := TensorFactorSplitting.generic_tensor_mem_span_of_graph hgraph
  have hcoordinate := TensorCoordinateReindex.generic_tensor_mem_span_reindex
    (chosenCoordinateEquiv n i) hoption
  exact TensorFactorReindex.generic_tensor_mem_span_reindex
    (chosenFactorEquiv i) hcoordinate

/-- The balanced range or a valid graph range exhausts every nonempty
numeric format. No sorting, positive-dimension, or bounded-size restriction
is present. -/
theorem balanced_or_graph {k : ℕ} (n : Fin (k+1) → ℕ) :
    (∀ i, n i ≤ ∑ j ∈ Finset.univ.erase i, n j) ∨
      ∃ i, sideSum (smallerDimensions n i)+1 ≤ n i+1 := by
  by_cases h : ∀ i, n i ≤ ∑ j ∈ Finset.univ.erase i, n j
  · exact Or.inl h
  · right
    push_neg at h
    obtain ⟨i, hi⟩ := h
    refine ⟨i, ?_⟩
    rw [sum_smallerDimensions]
    omega

/-- A tensor of order one is already a singular rank-one tensor whenever
it is nonzero; zero belongs to the span as well. This also treats every
one-dimensional vector factor in this base case. -/
theorem matrix_mem_span_no_small_factors
    {I J : Type} [Fintype I] [DecidableEq I] [IsEmpty I]
    [Fintype J] [DecidableEq J] {n : I → ℕ}
    (A : Matrix (Cell n) J K) : A ∈ singularSpan A := by
  by_cases hA : A = 0
  · rw [hA]
    exact Submodule.zero_mem _
  let x : FactorPoint n K := ⟨fun q => isEmptyElim q.1, fun i => isEmptyElim i⟩
  let v : Cell n := fun i => isEmptyElim i
  let y : J → K := A v
  have hy : y ≠ 0 := by
    intro h
    apply hA
    ext w j
    have hw : w = v := Subsingleton.elim _ _
    simpa only [y, hw, Pi.zero_apply, Matrix.zero_apply] using congrFun h j
  have hs : IsSingularTuple A x y := by
    refine ⟨hy, fun i => isEmptyElim i, 1, ?_⟩
    intro j
    rw [lastContraction, eval_segreForm]
    simp only [eval_cell_eq_prod, Fintype.prod_empty, mul_one, one_mul]
    change (∑ w : Cell n, A w j) = A v j
    apply Finset.sum_eq_single v
    · intro w _ hw
      exact (hw (Subsingleton.elim w v)).elim
    · intro hv
      exact (hv (Finset.mem_univ v)).elim
  have he : A = rankOneTensor x.val y := by
    ext w j
    simp only [rankOneTensor, eval_cell_eq_prod, Fintype.prod_empty, one_mul]
    exact congrArg (fun w => A w j) (Subsingleton.elim _ _)
  exact Submodule.subset_span ⟨x, y, hs, he⟩

theorem generic_one_factor (n : Fin 1 → ℕ) :
    ∃ p : MvPolynomial (Cell n) K, p ≠ 0 ∧
      ∀ T : Cell n → K, MvPolynomial.eval T p ≠ 0 → T ∈ incidenceSpan T := by
  apply generic_mem_span_chosen_factor n 0
  refine ⟨1, one_ne_zero, ?_⟩
  intro A _
  exact matrix_mem_span_no_small_factors A

/-- The exhaustive last step in Section 2.2. The two geometric inputs must
already be established for their full parameter ranges and literal spans. -/
theorem generic_all_formats_of_geometric_branches
    (hbalanced : ∀ (k : ℕ) (n : Fin (k+1) → ℕ),
      (∀ i, n i ≤ ∑ j ∈ Finset.univ.erase i, n j) →
      ∃ p : MvPolynomial (Cell n) K, p ≠ 0 ∧
        ∀ T : Cell n → K, MvPolynomial.eval T p ≠ 0 → T ∈ incidenceSpan T)
    (hgraph : ∀ (k : ℕ) (n : Fin (k+1) → ℕ) (m : ℕ),
      sideSum n+1 ≤ m+1 →
      ∃ p : MvPolynomial (Cell n × Fin (m+1)) K, p ≠ 0 ∧
        ∀ A : Matrix (Cell n) (Fin (m+1)) K,
          MvPolynomial.eval (fun q => A q.1 q.2) p ≠ 0 → A ∈ singularSpan A)
    (k : ℕ) (n : Fin (k+1) → ℕ) :
    ∃ p : MvPolynomial (Cell n) K, p ≠ 0 ∧
      ∀ T : Cell n → K, MvPolynomial.eval T p ≠ 0 → T ∈ incidenceSpan T := by
  cases k with
  | zero => exact generic_one_factor n
  | succ k =>
    rcases balanced_or_graph n with hb | ⟨i, hi⟩
    · exact hbalanced (k+1) n hb
    · exact generic_mem_span_chosen_factor n i
        (hgraph k (smallerDimensions n i) (n i) hi)

/-- Each nonzero polynomial in a finite tensor coefficient space defines
an actual nonempty open over the field in the paper. -/
theorem nonempty_tensor_certificate {k : ℕ} {n : Fin (k+1) → ℕ}
    {p : MvPolynomial (Cell n) K} (hp : p ≠ 0) :
    ∃ T : Cell n → K, MvPolynomial.eval T p ≠ 0 := by
  by_contra! h
  apply hp
  apply MvPolynomial.funext
  intro T
  rw [h T, map_zero]

end PaperVerification.Segre.AllFormatReduction

end SegreAllFormatReduction

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
