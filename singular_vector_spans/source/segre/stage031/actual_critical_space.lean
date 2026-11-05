module
public import SegreVerified.Stage031.CriticalFactorReindex
public import SegreVerified.Stage030.ActualTensor
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

section SegreActualTensorCriticalSpace

/-!
# The full critical space in the genuine tensor product

The coefficient formula is proved to be the unique linear map whose value
on every actual pure tensor is the alternating expression in the original
tensor contractions. This universal characterization identifies the critical
space independently of the chosen storage of coefficients. The resulting
subspace is then transported to the sliced matrix used in the paper, keeping
both the small-factor equations and the distinguished-factor equations.

-/

set_option autoImplicit false
open scoped Classical BigOperators TensorProduct

namespace PaperVerification.Segre.ActualTensorCriticalSpace

open ActualTensorSpan

section ArbitraryFactors

variable (K : Type*) [Field K] {I : Type*} [Fintype I] [DecidableEq I]
variable (σ : I → Type*) [∀ i, Fintype (σ i)]

/-- One coordinate together with all remaining coordinates is a full index. -/
def splitCell (i : I) (a : σ i) (w : ∀ j : {j // j ≠ i}, σ j.val) : ∀ j, σ j :=
  (Equiv.piSplitAt i σ).symm (a, w)

@[simp] theorem splitCell_same (i : I) (a : σ i)
    (w : ∀ j : {j // j ≠ i}, σ j.val) : splitCell σ i a w i = a := by
  simp [splitCell, Equiv.piSplitAt]

theorem splitCell_other (i : I) (a : σ i)
    (w : ∀ j : {j // j ≠ i}, σ j.val) (j : {j // j ≠ i}) :
    splitCell σ i a w j.val = w j := by
  simp [splitCell, Equiv.piSplitAt, j.property]

theorem update_splitCell (i : I) (a b : σ i)
    (w : ∀ j : {j // j ≠ i}, σ j.val) :
    Function.update (splitCell σ i a w) i b = splitCell σ i b w := by
  funext j
  by_cases h : j = i
  · subst j
    simp only [Function.update_self, splitCell_same]
  · rw [Function.update_of_ne h]
    exact (splitCell_other σ i a w ⟨j, h⟩).trans
      (splitCell_other σ i b w ⟨j, h⟩).symm

theorem otherProduct_splitCell (v : ∀ i, σ i → K) (i : I) (a b : σ i)
    (w : ∀ j : {j // j ≠ i}, σ j.val) :
    TangentKernel.otherProduct v i (splitCell σ i a w) =
      TangentKernel.otherProduct v i (splitCell σ i b w) := by
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  rw [splitCell_other σ i a w ⟨j, hji⟩, splitCell_other σ i b w ⟨j, hji⟩]

theorem pureTensor_splitCell (v : ∀ i, σ i → K) (i : I) (a : σ i)
    (w : ∀ j : {j // j ≠ i}, σ j.val) :
    TangentKernel.pureTensor v (splitCell σ i a w) =
      v i a * TangentKernel.otherProduct v i (splitCell σ i a w) := by
  unfold TangentKernel.pureTensor TangentKernel.otherProduct
  rw [← Finset.mul_prod_erase Finset.univ (fun j => v j (splitCell σ i a w j))
    (Finset.mem_univ i), splitCell_same]

/-- The full contraction sum is exactly its coordinate-fibre sum. -/
theorem contraction_split (v : ∀ i, σ i → K) (T : (∀ i, σ i) → K)
    (i : I) (a : σ i) :
    TangentKernel.contraction v T i a =
      ∑ w : (∀ j : {j // j ≠ i}, σ j.val),
        T (splitCell σ i a w) * TangentKernel.otherProduct v i (splitCell σ i a w) := by
  unfold TangentKernel.contraction
  rw [← Equiv.sum_comp (Equiv.piSplitAt i σ).symm, Fintype.sum_prod_type,
    Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  change (∑ b : σ i, if splitCell σ i b w i = a then
    T (splitCell σ i b w) * TangentKernel.otherProduct v i (splitCell σ i b w)
      else 0) = _
  simp only [splitCell_same, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- Exact pure-tensor value of every original critical equation. No
nonisotropy, characteristic restriction, or nonzero-vector premise is used. -/
theorem coefficient_pureTensor (T : (∀ i, σ i) → K) (v : ∀ i, σ i → K)
    (i : I) (a b : σ i) :
    CriticalFactorReindex.coefficient T (TangentKernel.pureTensor v) i a b =
      v i b * TangentKernel.contraction v T i a -
        v i a * TangentKernel.contraction v T i b := by
  unfold CriticalFactorReindex.coefficient
  rw [← Equiv.sum_comp (Equiv.piSplitAt i σ).symm, Fintype.sum_prod_type,
    Finset.sum_comm]
  change (∑ w : (∀ j : {j // j ≠ i}, σ j.val), ∑ c : σ i,
    if splitCell σ i c w i = a then
      T (splitCell σ i c w) *
          TangentKernel.pureTensor v (Function.update (splitCell σ i c w) i b) -
        T (Function.update (splitCell σ i c w) i b) *
          TangentKernel.pureTensor v (splitCell σ i c w) else 0) = _
  simp only [splitCell_same, update_splitCell, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  rw [contraction_split, contraction_split, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro w _
  rw [pureTensor_splitCell, pureTensor_splitCell,
    otherProduct_splitCell K σ v i b a w]
  ring

/-- The complete linear critical operator on the actual tensor product.
Its intrinsic pure-tensor characterization and uniqueness are proved below. -/
def criticalOperator (T : Tensor K σ) :
    Tensor K σ →ₗ[K] ((Σ i, σ i × σ i) → K) :=
  (CriticalFactorReindex.criticalOperator (coefficients K σ T)).comp
    (coefficients K σ).toLinearMap

/-- The operator is the original alternating contraction expression on
every pure tensor, including tuples with zero or isotropic factors. -/
theorem criticalOperator_tprod (T : Tensor K σ) (v : ∀ i, σ i → K)
    (i : I) (a b : σ i) :
    criticalOperator K σ T (PiTensorProduct.tprod K v) ⟨i, a, b⟩ =
      v i b * tensorContraction K σ v i T a -
        v i a * tensorContraction K σ v i T b := by
  change CriticalFactorReindex.coefficient (coefficients K σ T)
    (coefficients K σ (PiTensorProduct.tprod K v)) i a b = _
  rw [coefficients_tprod, coefficient_pureTensor]
  simp only [tensorContraction_eq_coordinates]

/-- The original pure-tensor contraction formula determines the entire
linear operator uniquely, by the universal property of the tensor product. -/
theorem criticalOperator_unique (T : Tensor K σ)
    (L : Tensor K σ →ₗ[K] ((Σ i, σ i × σ i) → K))
    (hL : ∀ (v : ∀ i, σ i → K) (i : I) (a b : σ i),
      L (PiTensorProduct.tprod K v) ⟨i, a, b⟩ =
        v i b * tensorContraction K σ v i T a -
          v i a * tensorContraction K σ v i T b) :
    L = criticalOperator K σ T := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  funext q
  exact (hL v q.1 q.2.1 q.2.2).trans
    (criticalOperator_tprod K σ T v q.1 q.2.1 q.2.2).symm

/-- The original full critical subspace of the actual tensor space. -/
def criticalSpace (T : Tensor K σ) : Submodule K (Tensor K σ) :=
  LinearMap.ker (criticalOperator K σ T)

/-- The original tensor itself satisfies all complete critical equations. -/
theorem tensor_mem_criticalSpace (T : Tensor K σ) : T ∈ criticalSpace K σ T := by
  change criticalOperator K σ T T = 0
  funext q
  change CriticalFactorReindex.coefficient (coefficients K σ T)
    (coefficients K σ T) q.1 q.2.1 q.2.2 = 0
  unfold CriticalFactorReindex.coefficient
  apply Finset.sum_eq_zero
  intro c _
  split_ifs <;> ring

/-- Every actual singular pure tensor lies in the complete critical space,
so the difference of dimensions below is a genuine subspace codimension. -/
theorem singularSpan_le_criticalSpace (T : Tensor K σ) :
    ActualTensorSpan.singularSpan K σ T ≤ criticalSpace K σ T := by
  apply Submodule.span_le.mpr
  rintro B ⟨v, ⟨_, hv⟩, rfl⟩
  change criticalOperator K σ T (PiTensorProduct.tprod K v) = 0
  funext q
  rw [criticalOperator_tprod]
  obtain ⟨c, hc⟩ := hv q.1
  simp only [hc, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  ring

/-- Equality of the whole critical submodule under the genuine tensor
coefficient equivalence, with every original critical equation retained. -/
theorem coefficient_map_criticalSpace (T : Tensor K σ) :
    CriticalFactorReindex.criticalSpace (coefficients K σ T) =
      (criticalSpace K σ T).map (coefficients K σ).toLinearMap := by
  ext B
  constructor
  · intro hB
    refine ⟨(coefficients K σ).symm B, ?_, (coefficients K σ).apply_symm_apply B⟩
    change CriticalFactorReindex.criticalOperator (coefficients K σ T)
      (coefficients K σ ((coefficients K σ).symm B)) = 0
    change CriticalFactorReindex.criticalOperator (coefficients K σ T) B = 0 at hB
    simpa only [LinearEquiv.apply_symm_apply] using hB
  · rintro ⟨C, hC, rfl⟩
    exact hC

/-- The numerical defect of the coefficient presentation is exactly the
codimension in the original genuine tensor critical space. -/
theorem defect_coefficients (T : Tensor K σ) :
    Module.finrank K (CriticalFactorReindex.criticalSpace (coefficients K σ T)) -
        Module.finrank K (TensorFactorReindex.incidenceSpan (coefficients K σ T)) =
      Module.finrank K (criticalSpace K σ T) -
        Module.finrank K (ActualTensorSpan.singularSpan K σ T) := by
  rw [coefficient_map_criticalSpace, incidenceSpan_eq_map_singularSpan,
    LinearEquiv.finrank_map_eq, LinearEquiv.finrank_map_eq]

/-- Full span in coefficients is precisely full span in the original
actual tensor product, as equality of entire subspaces. -/
theorem full_span_coefficients_iff (T : Tensor K σ) :
    TensorFactorReindex.incidenceSpan (coefficients K σ T) =
        CriticalFactorReindex.criticalSpace (coefficients K σ T) ↔
      ActualTensorSpan.singularSpan K σ T = criticalSpace K σ T := by
  rw [coefficient_map_criticalSpace, incidenceSpan_eq_map_singularSpan]
  exact (Submodule.map_injective_of_injective (coefficients K σ).injective).eq_iff

end ArbitraryFactors

section Slices

open Staircase FullGraphChartReindex TensorFactorSplitting

variable (K : Type) [Field K] {I J : Type} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] (n : I → ℕ)

/-- The actual tensor product is canonically the matrix of its slices. -/
def slicedCoefficients : Tensor K (FullFactor n J) ≃ₗ[K] Matrix (Cell n) J K :=
  (coefficients K (FullFactor n J)).trans (matrixEquiv (n := n) (J := J))

theorem originalTensor_slicedCoefficients (T : Tensor K (FullFactor n J)) :
    originalTensor (slicedCoefficients K n T) = coefficients K (FullFactor n J) T :=
  (matrixEquiv (n := n) (J := J)).symm_apply_apply _

/-- The sliced full critical space is exactly the original tensor critical
space, including the equations from the separated last factor. -/
theorem fullCriticalSpace_eq_map_actual (T : Tensor K (FullFactor n J)) :
    CriticalGraph.fullCriticalSpace (slicedCoefficients K n T) =
      (criticalSpace K (FullFactor n J) T).map (slicedCoefficients K n).toLinearMap := by
  rw [CriticalFactorReindex.fullCriticalSpace_eq_map,
    originalTensor_slicedCoefficients, coefficient_map_criticalSpace,
    ← Submodule.map_comp]
  rfl

/-- The sliced singular span is the exact ordinary span of original
singular pure tensors in the genuine tensor product. -/
theorem singularSpan_eq_map_actual (T : Tensor K (FullFactor n J)) :
    SingularSpan.singularSpan (slicedCoefficients K n T) =
      (ActualTensorSpan.singularSpan K (FullFactor n J) T).map
        (slicedCoefficients K n).toLinearMap := by
  rw [TensorFactorSplitting.singularSpan_eq_map_incidenceSpan,
    originalTensor_slicedCoefficients, incidenceSpan_eq_map_singularSpan,
    ← Submodule.map_comp]
  rfl

/-- General correspondence for every defect endpoint in sliced notation,
including Corollary 1.2 and the defects in Theorems 6.1 and 6.3. -/
theorem defect_slicedCoefficients (T : Tensor K (FullFactor n J)) :
    Module.finrank K (CriticalGraph.fullCriticalSpace (slicedCoefficients K n T)) -
        Module.finrank K (SingularSpan.singularSpan (slicedCoefficients K n T)) =
      Module.finrank K (criticalSpace K (FullFactor n J) T) -
        Module.finrank K (ActualTensorSpan.singularSpan K (FullFactor n J) T) := by
  rw [fullCriticalSpace_eq_map_actual, singularSpan_eq_map_actual,
    LinearEquiv.finrank_map_eq, LinearEquiv.finrank_map_eq]

/-- General correspondence for every full-span endpoint in sliced notation. -/
theorem full_span_slicedCoefficients_iff (T : Tensor K (FullFactor n J)) :
    SingularSpan.singularSpan (slicedCoefficients K n T) =
        CriticalGraph.fullCriticalSpace (slicedCoefficients K n T) ↔
      ActualTensorSpan.singularSpan K (FullFactor n J) T =
        criticalSpace K (FullFactor n J) T := by
  rw [fullCriticalSpace_eq_map_actual, singularSpan_eq_map_actual]
  exact (Submodule.map_injective_of_injective (slicedCoefficients K n).injective).eq_iff

end Slices
end PaperVerification.Segre.ActualTensorCriticalSpace

end SegreActualTensorCriticalSpace

end
end

/-! Kernel audit of every declaration defined by this module.

Private and generated declarations receive the same sorry and transitive-axiom
checks as the public theorems. The root audit additionally checks the complete
project and its principal theorem inventory.
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
