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

section SegreActualTensorSpan

/-!
# Genuine tensor products and the literal singular rank-one span

The coefficient-array space is canonically identified with Mathlib's actual
finite tensor product using the tensor product of the standard coordinate
bases. The contraction below is independently defined by tensoring the
original coordinate-pairing functionals and the one remaining coordinate
evaluation functional. Its agreement with the coefficient fibre sum is
proved on the entire tensor space.

Consequently, the coordinate incidence span is exactly the ordinary linear
span of actual pure tensors satisfying all original contraction conditions.
No span equality or singularity condition is built into the coefficient
equivalence.

-/

set_option autoImplicit false
open scoped Classical BigOperators TensorProduct

namespace PaperVerification.Segre.ActualTensorSpan

open TensorFactorReindex

variable (K : Type*) [Field K] {I : Type*} [Fintype I] [DecidableEq I]
variable (σ : I → Type*) [∀ i,Fintype (σ i)]

/-- The paper's tensor space, using the actual universal tensor product. -/
abbrev Tensor := ⨂[K] i, (σ i → K)

/-- The actual tensor product of the standard coordinate bases. -/
def tensorBasis : Module.Basis (∀ i,σ i) K (Tensor K σ) :=
  Basis.piTensorProduct (fun i => Pi.basisFun K (σ i))

/-- Every tensor entry, in the tensor product of the original coordinate bases. -/
def coefficients : Tensor K σ ≃ₗ[K] ((∀ i,σ i) → K) :=
  (tensorBasis K σ).equivFun

/-- The actual pure tensor has precisely the product of the original factor
coordinates, with no change of scalar normalization. -/
theorem coefficients_tprod (v : ∀ i,σ i → K) :
    coefficients K σ (PiTensorProduct.tprod K v)=TangentKernel.pureTensor v := by
  funext a
  simp only [coefficients,tensorBasis,Module.Basis.equivFun_apply,
    Basis.piTensorProduct_repr_tprod_apply,Pi.basisFun_repr,
    TangentKernel.pureTensor]

/-- Nonzero vectors in every factor give a genuinely nonzero pure tensor. -/
theorem tprod_ne_zero_of_vectors_ne_zero (v : ∀ i,σ i → K)
    (hv : ∀ i,v i≠0) : PiTensorProduct.tprod K v≠0 := by
  have hx : ∀ i,∃ a,v i a≠0 := by
    intro i
    by_contra! h
    exact hv i (funext h)
  choose a ha using hx
  intro hT
  have hc := congrArg (fun T : Tensor K σ => coefficients K σ T a) hT
  simp only [coefficients_tprod,map_zero,Pi.zero_apply,TangentKernel.pureTensor] at hc
  exact (Finset.prod_ne_zero_iff.mpr (fun i _ => ha i)) hc

/-- Literal contraction: all other slots are evaluated against their
coordinate bilinear pairings, and the remaining slot against a coordinate
functional. This uses the actual tensor product of dual maps. -/
def tensorContraction (v : ∀ i,σ i → K) (i : I) :
    Tensor K σ →ₗ[K] (σ i → K) :=
  LinearMap.pi (fun a => PiTensorProduct.dualDistrib
    (PiTensorProduct.tprod K
      (Function.update (fun j => TangentKernel.pairing (v j)) i
        (LinearMap.proj a : (σ i → K) →ₗ[K] K))))

theorem tensorContraction_apply (v : ∀ i,σ i → K) (i : I)
    (T : Tensor K σ) (a : σ i) :
    tensorContraction K σ v i T a=
      PiTensorProduct.dualDistrib
        (PiTensorProduct.tprod K
          (Function.update (fun j => TangentKernel.pairing (v j)) i
            (LinearMap.proj a : (σ i → K) →ₗ[K] K))) T := rfl

/-- On every actual pure tensor, contraction is the product of the original
bilinear pairings in all other slots times the remaining factor vector. -/
theorem tensorContraction_tprod (v w : ∀ i,σ i → K) (i : I) :
    tensorContraction K σ v i (PiTensorProduct.tprod K w)=
      (∏ j ∈ Finset.univ.erase i,TangentKernel.pairing (v j) (w j)) • w i := by
  funext a
  rw [tensorContraction_apply,PiTensorProduct.dualDistrib_apply]
  let g : I → K := fun j =>
    (Function.update (fun j => TangentKernel.pairing (v j)) i
      (LinearMap.proj a : (σ i → K) →ₗ[K] K)) j (w j)
  change (∏ j,g j)=_
  rw [← Finset.mul_prod_erase Finset.univ g (Finset.mem_univ i)]
  have ho : (∏ j ∈ Finset.univ.erase i,g j)=
      ∏ j ∈ Finset.univ.erase i,TangentKernel.pairing (v j) (w j) := by
    apply Finset.prod_congr rfl
    intro j hj
    dsimp only [g]
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  have hi : g i=w i a := by simp [g]
  rw [ho,hi]
  change w i a * (∏ j ∈ Finset.univ.erase i,TangentKernel.pairing (v j) (w j))=
    (∏ j ∈ Finset.univ.erase i,TangentKernel.pairing (v j) (w j))*w i a
  exact mul_comm _ _

/-- The literal contraction on a tensor of coordinate basis vectors. -/
theorem tensorContraction_basis (v : ∀ i,σ i → K) (i : I)
    (a : σ i) (b : ∀ i,σ i) :
    tensorContraction K σ v i (tensorBasis K σ b) a=
      if b i=a then TangentKernel.otherProduct v i b else 0 := by
  rw [tensorContraction_apply,tensorBasis,Basis.piTensorProduct_apply,
    PiTensorProduct.dualDistrib_apply]
  let g : I → K := fun j =>
    (Function.update (fun j => TangentKernel.pairing (v j)) i
      (LinearMap.proj a : (σ i → K) →ₗ[K] K)) j (Pi.basisFun K (σ j) (b j))
  change (∏ j,g j)=_
  rw [← Finset.mul_prod_erase Finset.univ g (Finset.mem_univ i)]
  have ho : (∏ j ∈ Finset.univ.erase i,g j)=TangentKernel.otherProduct v i b := by
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j≠i := (Finset.mem_erase.mp hj).1
    simp [g,Function.update_of_ne hji,Pi.basisFun_apply,
      TangentKernel.pairing,Pi.single_apply]
  rw [ho]
  simp [g,Pi.basisFun_apply,Pi.single_apply,eq_comm,ite_mul]

/-- The genuine tensor contraction is the full original coefficient fibre
sum for every tensor, not merely for pure tensors or a finite test family. -/
theorem tensorContraction_eq_coordinates (v : ∀ i,σ i → K)
    (i : I) (T : Tensor K σ) :
    tensorContraction K σ v i T=
      TangentKernel.contraction v (coefficients K σ T) i := by
  funext a
  conv_lhs => rw [← (tensorBasis K σ).sum_equivFun T]
  simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
    tensorContraction_basis]
  change (∑ b : (∀ i,σ i), coefficients K σ T b *
      (if b i=a then TangentKernel.otherProduct v i b else 0))=_
  unfold TangentKernel.contraction
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : b i=a <;> simp only [h,if_true,if_false,mul_zero]

/-- All original nonzero factor vectors satisfy every genuine tensor
contraction proportionality condition. -/
def IsSingularTuple (T : Tensor K σ) (v : ∀ i,σ i → K) : Prop :=
  (∀ i,v i≠0) ∧ ∀ i,∃ c : K,tensorContraction K σ v i T=c • v i

/-- Exact equivalence with the independently defined complete coefficient
incidence map, including isotropic vectors and characteristic two. -/
theorem isSingularTuple_iff_incidence (T : Tensor K σ) (v : ∀ i,σ i → K) :
    IsSingularTuple K σ T v ↔
      (∀ i,v i≠0) ∧ TangentKernel.singularIncidenceMap v (coefficients K σ T)=0 := by
  constructor
  · rintro ⟨hv,hs⟩
    refine ⟨hv,?_⟩
    rw [TangentKernel.singularIncidenceMap_eq_zero_iff_of_nonzero _ _ hv]
    intro i
    obtain ⟨c,hc⟩ := hs i
    refine ⟨c,?_⟩
    rw [← tensorContraction_eq_coordinates]
    exact hc
  · rintro ⟨hv,hs⟩
    refine ⟨hv,?_⟩
    rw [TangentKernel.singularIncidenceMap_eq_zero_iff_of_nonzero _ _ hv] at hs
    intro i
    obtain ⟨c,hc⟩ := hs i
    refine ⟨c,?_⟩
    rw [tensorContraction_eq_coordinates]
    exact hc

/-- Actual singular rank-one tensors in the actual tensor product. -/
def singularRankOneSet (T : Tensor K σ) : Set (Tensor K σ) :=
  {B | ∃ v : ∀ i,σ i → K,IsSingularTuple K σ T v ∧ B=PiTensorProduct.tprod K v}

/-- Their ordinary linear span inside the original tensor product. -/
def singularSpan (T : Tensor K σ) : Submodule K (Tensor K σ) :=
  Submodule.span K (singularRankOneSet K σ T)

theorem singularRankOneSet_ne_zero (T : Tensor K σ) {B : Tensor K σ}
    (hB : B ∈ singularRankOneSet K σ T) : B≠0 := by
  obtain ⟨v,hv,rfl⟩ := hB
  exact tprod_ne_zero_of_vectors_ne_zero K σ v hv.1

/-- The entire genuine generator set, not only its dimension, is preserved. -/
theorem coefficient_image_singularRankOneSet (T : Tensor K σ) :
    coefficients K σ '' singularRankOneSet K σ T=
      TensorFactorReindex.incidenceGenerators (coefficients K σ T) := by
  ext B
  constructor
  · rintro ⟨C,⟨v,hv,rfl⟩,rfl⟩
    obtain ⟨hne,hs⟩ := (isSingularTuple_iff_incidence K σ T v).mp hv
    exact ⟨v,hne,hs,coefficients_tprod K σ v⟩
  · rintro ⟨v,hne,hs,rfl⟩
    refine ⟨PiTensorProduct.tprod K v,?_,coefficients_tprod K σ v⟩
    exact ⟨v,(isSingularTuple_iff_incidence K σ T v).mpr ⟨hne,hs⟩,rfl⟩

/-- Exact transport of the ordinary singular rank-one span. -/
theorem incidenceSpan_eq_map_singularSpan (T : Tensor K σ) :
    TensorFactorReindex.incidenceSpan (coefficients K σ T)=
      (singularSpan K σ T).map (coefficients K σ).toLinearMap := by
  rw [singularSpan, Submodule.map_span]
  change TensorFactorReindex.incidenceSpan (coefficients K σ T) =
    Submodule.span K (coefficients K σ '' singularRankOneSet K σ T)
  rw [coefficient_image_singularRankOneSet]
  rfl

/-- The coefficient reformulation of tensor membership is mathematically
equivalent to membership of the original tensor in its actual singular span. -/
theorem mem_singularSpan_iff (T : Tensor K σ) :
    T ∈ singularSpan K σ T ↔
      coefficients K σ T ∈ TensorFactorReindex.incidenceSpan (coefficients K σ T) := by
  rw [incidenceSpan_eq_map_singularSpan]
  constructor
  · intro hT
    exact ⟨T,hT,rfl⟩
  · rintro ⟨S,hS,hST⟩
    exact (coefficients K σ).injective hST ▸ hS

/-- A full coefficient-space principal-open certificate gives the identical
generic assertion on the actual tensor product, with an actual nonempty open. -/
theorem generic_actual_tensor_membership
    (h : ∃ p : MvPolynomial (∀ i,σ i) K,p≠0 ∧
      (∃ A : (∀ i,σ i) → K,MvPolynomial.eval A p≠0) ∧
      ∀ A : (∀ i,σ i) → K,MvPolynomial.eval A p≠0 →
        A ∈ TensorFactorReindex.incidenceSpan A) :
    ∃ p : MvPolynomial (∀ i,σ i) K,p≠0 ∧
      (∃ T : Tensor K σ,MvPolynomial.eval (coefficients K σ T) p≠0) ∧
      ∀ T : Tensor K σ,MvPolynomial.eval (coefficients K σ T) p≠0 →
        T ∈ singularSpan K σ T := by
  obtain ⟨p,hp,⟨A,hA⟩,hmem⟩ := h
  refine ⟨p,hp,?_,?_⟩
  · refine ⟨(coefficients K σ).symm A,?_⟩
    simpa only [LinearEquiv.apply_symm_apply] using hA
  · intro T hT
    exact (mem_singularSpan_iff K σ T).mpr (hmem (coefficients K σ T) hT)

end PaperVerification.Segre.ActualTensorSpan

end SegreActualTensorSpan

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
