module
public import SegreVerified.Stage023
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
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
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


section SegreGlobalCriticalSections

run_cmd do
  let out ← IO.getStderr
  out.putStrLn "SEGRE_STAGE Stage028.ExternalSections"
  out.flush

/-!
# Global critical sections and their literal chart equations

The named sections preserve the original proof stages and local scopes.
-/


section SegreFiniteTensorLinear

/-!
# The canonical comparison of finite tensor products

The algebraic Segre ring uses `PiTensorProduct`; the geometric construction
uses the literal right-associated tensor object in `ModuleCat`, including
the unit in length zero. This file constructs their canonical equivalence
from the universal properties and proves its formula on every pure tensor.
No dimension count or chosen isomorphism enters the construction.

-/

set_option autoImplicit false

namespace PaperVerification.Segre.FiniteTensorLinear

open CategoryTheory MonoidalCategory
open scoped TensorProduct

universe u
variable {K : Type u} [CommRing K]

section HeadTail

variable {k : ℕ} (M : Fin (k + 1) → ModuleCat.{u} K)

/-- The multilinear map separating the first factor from the remaining
factors, with their literal `Fin` indexing. -/
def headTailMultilinear :
    MultilinearMap K (fun i => M i)
      (M 0 ⊗[K] (⨂[K] i : Fin k, M i.succ)) :=
  LinearMap.uncurryLeft
    { toFun := fun x =>
        ((TensorProduct.mk K (M 0) (⨂[K] i : Fin k, M i.succ)) x).compMultilinearMap
          (PiTensorProduct.tprod K)
      map_add' := by
        intro x y
        ext m
        simp
      map_smul' := by
        intro c x
        ext m
        simp }

/-- Split off the actual first factor of a finite tensor product. -/
def headTail : (⨂[K] i : Fin (k + 1), M i) →ₗ[K]
    M 0 ⊗[K] (⨂[K] i : Fin k, M i.succ) :=
  PiTensorProduct.lift (headTailMultilinear M)

@[simp] theorem headTail_tprod (m : ∀ i, M i) :
    headTail M (PiTensorProduct.tprod K m) =
      m 0 ⊗ₜ[K] PiTensorProduct.tprod K (fun i : Fin k => m i.succ) := by
  rw [headTail, PiTensorProduct.lift.tprod]
  rfl

/-- Reassemble the first factor and the remaining pure tensor, by the two
universal properties. -/
def consTensor : M 0 ⊗[K] (⨂[K] i : Fin k, M i.succ) →ₗ[K]
    (⨂[K] i : Fin (k + 1), M i) :=
  TensorProduct.lift
    ((PiTensorProduct.lift (R := K) (s := fun i : Fin k => M i.succ)).toLinearMap.comp
      (PiTensorProduct.tprod K (s := fun i : Fin (k + 1) => M i)).curryLeft)

@[simp] theorem consTensor_tmul_tprod (x : M 0) (m : ∀ i : Fin k, M i.succ) :
    consTensor M (x ⊗ₜ[K] PiTensorProduct.tprod K m) =
      PiTensorProduct.tprod K (Fin.cons x m) := by
  simp [consTensor]

/-- The comparison is an equivalence, proved on the generating pure tensors. -/
def headTailEquiv : (⨂[K] i : Fin (k + 1), M i) ≃ₗ[K]
    M 0 ⊗[K] (⨂[K] i : Fin k, M i.succ) :=
  LinearEquiv.ofLinearMap (headTail M) (consTensor M)
    (by
      apply TensorProduct.ext'
      intro x y
      induction y using PiTensorProduct.induction_on with
      | smul_tprod c m =>
          simp [TensorProduct.tmul_smul]
      | add y z hy hz =>
          simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hy hz)
    (by
      apply PiTensorProduct.ext
      ext m
      change consTensor M (headTail M (PiTensorProduct.tprod K m)) =
        PiTensorProduct.tprod K m
      rw [headTail_tprod, consTensor_tmul_tprod]
      exact congrArg (PiTensorProduct.tprod K) (Fin.cons_self_tail m))

@[simp] theorem headTailEquiv_tprod (m : ∀ i, M i) :
    headTailEquiv M (PiTensorProduct.tprod K m) =
      m 0 ⊗ₜ[K] PiTensorProduct.tprod K (fun i : Fin k => m i.succ) :=
  headTail_tprod M m

end HeadTail

/-- The pure element of the literal right-associated tensor object. -/
def pure : {k : ℕ} → (M : Fin k → ModuleCat.{u} K) →
    ((i : Fin k) → M i) → FiniteTensor.tensorObj (C := ModuleCat.{u} K) M
  | 0, _, _ => (1 : K)
  | k + 1, M, m => m 0 ⊗ₜ[K] pure (fun i : Fin k => M i.succ) (fun i => m i.succ)

/-- The canonical finite tensor-product equivalence in every length. -/
def piEquiv : {k : ℕ} → (M : Fin k → ModuleCat.{u} K) →
    ((⨂[K] i : Fin k, M i) ≃ₗ[K] FiniteTensor.tensorObj (C := ModuleCat.{u} K) M)
  | 0, _ => PiTensorProduct.isEmptyEquiv (Fin 0)
  | k + 1, M =>
      (headTailEquiv M).trans
        (TensorProduct.congr (LinearEquiv.refl K (M 0))
          (piEquiv (fun i : Fin k => M i.succ)))

@[simp] theorem piEquiv_tprod {k : ℕ} (M : Fin k → ModuleCat.{u} K)
    (m : ∀ i, M i) :
    piEquiv M (PiTensorProduct.tprod K m) = pure M m := by
  induction k with
  | zero =>
      change PiTensorProduct.isEmptyEquiv (R := K) (Fin 0)
        (PiTensorProduct.tprod K m) = (1 : K)
      exact PiTensorProduct.isEmptyEquiv_apply_tprod (R := K) (Fin 0) m
  | succ k ih =>
      simp only [piEquiv, LinearEquiv.trans_apply, headTailEquiv_tprod, pure]
      erw [TensorProduct.congr_tmul]
      rw [LinearEquiv.refl_apply, ih]

/-- The categorical finite section map has exactly the expected pure-tensor
value on the scalar unit. -/
@[simp] theorem sectionMap_one {k : ℕ} (M : Fin k → ModuleCat.{u} K)
    (s : (i : Fin k) → (𝟙_ (ModuleCat.{u} K) ⟶ M i)) :
    FiniteTensor.sectionMap M s (1 : K) = pure M (fun i => s i 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [FiniteTensor.sectionMap, ModuleCat.comp_apply,
        ModuleCat.MonoidalCategory.leftUnitor_inv_apply, pure]
      erw [ModuleCat.MonoidalCategory.tensorHom_tmul]
      rw [ih]

/-- In particular the universal algebraic tensor is mapped to the very
section map used by the actual geometric critical section. -/
theorem piEquiv_tprod_eq_sectionMap {k : ℕ} (M : Fin k → ModuleCat.{u} K)
    (s : (i : Fin k) → (𝟙_ (ModuleCat.{u} K) ⟶ M i)) :
    piEquiv M (PiTensorProduct.tprod K (fun i => s i 1)) =
      FiniteTensor.sectionMap M s (1 : K) := by
  rw [piEquiv_tprod, sectionMap_one]

end PaperVerification.Segre.FiniteTensorLinear

end SegreFiniteTensorLinear

section SegreTensorKernelIntersection

/-!
# The canonical tensor of two kernels

This is the elementwise degree-zero Künneth argument needed for actual
section maps. It identifies the image of the tensor of the two kernel
inclusions with the simultaneous kernel of the two tensor differentials.
The maps are the canonical tensor maps, rather than a chosen abstract
isomorphism of vector spaces.
-/


namespace PaperVerification.Segre.TensorKernelIntersection

open TensorProduct

variable {K M M' N N' : Type*} [Field K]
  [AddCommGroup M] [Module K M] [AddCommGroup M'] [Module K M']
  [AddCommGroup N] [Module K N] [AddCommGroup N'] [Module K N']

/-- The two tensor maps act on different factors and commute. -/
theorem tensor_maps_commute (f : M →ₗ[K] M') (g : N →ₗ[K] N') :
    (g.lTensor M').comp (f.rTensor N) =
      (f.rTensor N').comp (g.lTensor M) := by
  ext m n
  rfl

/-- Two exact augmentations give every simultaneous tensor cycle. The first
augmentation is injective; no surjectivity of either differential is required. -/
theorem exists_tensor_preimage
    {A B : Type*} [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
    (iA : A →ₗ[K] M) (f : M →ₗ[K] M') (iB : B →ₗ[K] N) (g : N →ₗ[K] N')
    (hiA : Function.Injective iA) (hexf : Function.Exact iA f)
    (hexg : Function.Exact iB g)
    (z : M ⊗[K] N) (hf : f.rTensor N z = 0) (hg : g.lTensor M z = 0) :
    ∃ w : A ⊗[K] B, TensorProduct.map iA iB w = z := by
  obtain ⟨a, ha⟩ := (Module.Flat.rTensor_exact N hexf z).mp hf
  have ha0 : g.lTensor A a = 0 := by
    apply Module.Flat.rTensor_preserves_injective_linearMap (M := N') iA hiA
    rw [map_zero]
    have h := LinearMap.congr_fun (tensor_maps_commute iA g) a
    simp only [LinearMap.comp_apply] at h
    rw [ha, hg] at h
    exact h.symm
  obtain ⟨w, hw⟩ := (Module.Flat.lTensor_exact A hexg a).mp ha0
  refine ⟨w, ?_⟩
  have he : TensorProduct.map iA iB =
      (iA.rTensor N).comp (iB.lTensor A) := by
    ext m n
    rfl
  rw [he, LinearMap.comp_apply, hw, ha]

/-- Every simultaneous cycle comes from the actual tensor of kernels. -/
theorem exists_tensor_kernel (f : M →ₗ[K] M') (g : N →ₗ[K] N')
    (z : M ⊗[K] N) (hf : f.rTensor N z = 0) (hg : g.lTensor M z = 0) :
    ∃ w : (LinearMap.ker f) ⊗[K] (LinearMap.ker g),
      TensorProduct.map (LinearMap.ker f).subtype (LinearMap.ker g).subtype w = z :=
  exists_tensor_preimage (LinearMap.ker f).subtype f (LinearMap.ker g).subtype g
    (LinearMap.ker f).injective_subtype f.exact_subtype_ker_map g.exact_subtype_ker_map
    z hf hg

/-- Tensoring the two kernel inclusions is injective over a field. -/
theorem tensor_kernel_injective (f : M →ₗ[K] M') (g : N →ₗ[K] N') :
    Function.Injective
      (TensorProduct.map (LinearMap.ker f).subtype (LinearMap.ker g).subtype) := by
  have he : TensorProduct.map (LinearMap.ker f).subtype (LinearMap.ker g).subtype =
      ((LinearMap.ker f).subtype.rTensor N).comp
        ((LinearMap.ker g).subtype.lTensor (LinearMap.ker f)) := by
    ext m n
    rfl
  rw [he]
  exact (Module.Flat.rTensor_preserves_injective_linearMap
    (M := N) (LinearMap.ker f).subtype (LinearMap.ker f).injective_subtype).comp
      (Module.Flat.lTensor_preserves_injective_linearMap
        (M := LinearMap.ker f) (LinearMap.ker g).subtype
        (LinearMap.ker g).injective_subtype)

/-- The full image statement, with the exact canonical maps. -/
theorem range_tensor_kernel (f : M →ₗ[K] M') (g : N →ₗ[K] N') :
    LinearMap.range
        (TensorProduct.map (LinearMap.ker f).subtype (LinearMap.ker g).subtype) =
      LinearMap.ker (f.rTensor N) ⊓ LinearMap.ker (g.lTensor M) := by
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    constructor
    · change f.rTensor N
        (TensorProduct.map (LinearMap.ker f).subtype (LinearMap.ker g).subtype w) = 0
      have he : (f.rTensor N).comp
          (TensorProduct.map (LinearMap.ker f).subtype (LinearMap.ker g).subtype) = 0 := by
        ext m n
        simp
      exact LinearMap.congr_fun he w
    · change g.lTensor M
        (TensorProduct.map (LinearMap.ker f).subtype (LinearMap.ker g).subtype w) = 0
      have he : (g.lTensor M).comp
          (TensorProduct.map (LinearMap.ker f).subtype (LinearMap.ker g).subtype) = 0 := by
        ext m n
        simp
      exact LinearMap.congr_fun he w
  · intro z hz
    exact exists_tensor_kernel f g z hz.1 hz.2

end PaperVerification.Segre.TensorKernelIntersection

end SegreTensorKernelIntersection

section SegreExternalGlobalSections

/-!
# Canonical global sections of an external tensor product

This construction uses ordinary sheaf gluing and flatness over the coefficient
field. On each affine rectangle the external-product map is the genuine
pullback and tensor map. Compatibility on overlaps identifies its image with
the tensor of the two spaces of compatible local sections.
-/

set_option autoImplicit false

namespace PaperVerification.Segre.ExternalGlobalSections

open CategoryTheory Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules ExternalSections
open scoped TensorProduct

universe u
variable (K : Type u) [Field K]
variable {X : Scheme.{u}} [X.Over (Spec (.of K))]

/-- Restriction of actual sections to an arbitrary family of smaller opens. -/
def restriction {ι : Type u} (M : X.Modules) (U : ι → X.Opens)
    (W : X.Opens) (hUW : ∀ i, U i ≤ W) :
    sections K M W →ₗ[K] (∀ i, sections K M (U i)) :=
  LinearMap.pi fun i =>
    (((sectionsBasePresheafFunctor K).obj M).map (homOfLE (hUW i)).op).hom

@[simp] theorem restriction_apply {ι : Type u} (M : X.Modules) (U : ι → X.Opens)
    (W : X.Opens) (hUW : ∀ i, U i ≤ W) (s : sections K M W) (i : ι) :
    restriction K M U W hUW s i = M.presheaf.map (homOfLE (hUW i)).op s := rfl

/-- Sections agreeing on a cover are equal. -/
theorem restriction_injective {ι : Type u} (M : X.Modules) (U : ι → X.Opens)
    (W : X.Opens) (hUW : ∀ i, U i ≤ W) (hcover : W ≤ ⨆ i, U i) :
    Function.Injective (restriction K M U W hUW) := by
  intro s t h
  exact TopCat.Sheaf.eq_of_locally_eq'
    (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
    U W (fun i => homOfLE (hUW i)) hcover s t (fun i => congrFun h i)

/-- The literal differences of sections on pairwise intersections. -/
def difference {ι : Type u} (M : X.Modules) (U : ι → X.Opens) :
    (∀ i, sections K M (U i)) →ₗ[K]
      (∀ p : ι × ι, sections K M (U p.1 ⊓ U p.2)) :=
  LinearMap.pi fun p =>
    ((((sectionsBasePresheafFunctor K).obj M).map (homOfLE inf_le_left).op).hom.comp
      (LinearMap.proj p.1)) -
    ((((sectionsBasePresheafFunctor K).obj M).map (homOfLE inf_le_right).op).hom.comp
      (LinearMap.proj p.2))

@[simp] theorem difference_apply {ι : Type u} (M : X.Modules) (U : ι → X.Opens)
    (s : ∀ i, sections K M (U i)) (p : ι × ι) :
    difference K M U s p =
      M.presheaf.map (homOfLE inf_le_left).op (s p.1) -
      M.presheaf.map (homOfLE inf_le_right).op (s p.2) := rfl

/-- Restricting along either path between the same opens gives the same
section. The comparison is proved before specializing any rectangle. -/
theorem restriction_paths {Y : Scheme.{u}} (Q : Y.Modules)
    {W U V₁ V₂ : Y.Opens} (h₁ : U ≤ V₁) (h₂ : V₁ ≤ W)
    (h₃ : U ≤ V₂) (h₄ : V₂ ≤ W) (s : Γ(Q,W)) :
    Q.presheaf.map (homOfLE h₁).op (Q.presheaf.map (homOfLE h₂).op s) =
      Q.presheaf.map (homOfLE h₃).op (Q.presheaf.map (homOfLE h₄).op s) := by
  rw [← CategoryTheory.Functor.map_comp_apply, ← CategoryTheory.Functor.map_comp_apply]
  rfl

/-- Sheaf gluing gives exactness of the actual restriction/difference pair. -/
theorem restriction_difference_exact {ι : Type u} (M : X.Modules)
    (U : ι → X.Opens) (W : X.Opens) (hUW : ∀ i, U i ≤ W)
    (hcover : W ≤ ⨆ i, U i) :
    Function.Exact (restriction K M U W hUW) (difference K M U) := by
  intro s
  constructor
  · intro hs
    have hc : TopCat.Presheaf.IsCompatible M.presheaf U s := by
      intro i j
      have h := congrFun hs (i, j)
      exact sub_eq_zero.mp h
    obtain ⟨t, ht, _⟩ := TopCat.Sheaf.existsUnique_gluing'
      (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
      U W (fun i => homOfLE (hUW i)) hcover s hc
    exact ⟨t, funext ht⟩
  · rintro ⟨t, rfl⟩
    funext p
    rw [difference_apply, restriction_apply, restriction_apply, Pi.zero_apply, sub_eq_zero]
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← Functor.map_comp]
    rfl

section External

variable {Y P : Scheme.{u}}
  [Y.Over (Spec (.of K))] [P.Over (Spec (.of K))]
  (f : P ⟶ X) (g : P ⟶ Y)
  [f.IsOver (Spec (.of K))] [g.IsOver (Spec (.of K))]
  (H : IsPullback f g (X ↘ Spec (.of K)) (Y ↘ Spec (.of K)))
  (M : X.Modules) (N : Y.Modules) [M.IsQuasicoherent] [N.IsQuasicoherent]

/-- The base-linear restriction formula also holds after forgetting scalars.
The carrier and restriction maps are those of the original sheaf. -/
theorem externalProduct_restrict_tmul_presheaf {U U' : X.Opens} {V V' : Y.Opens}
    (hU : U' ≤ U) (hV : V' ≤ V) (m : sections K M U) (n : sections K N V) :
    (externalTensor f g M N).presheaf.map
        (homOfLE (inf_le_inf (f.preimage_mono hU) (g.preimage_mono hV))).op
        (externalProduct K f g M N U V (m ⊗ₜ[K] n)) =
      externalProduct K f g M N U' V'
        ((M.presheaf.map (homOfLE hU).op m) ⊗ₜ[K]
          (N.presheaf.map (homOfLE hV).op n)) := by
  have h := externalProduct_restrict_tmul K f g M N hU hV m n
  change (externalTensor f g M N).presheaf.map
      (homOfLE (inf_le_inf (f.preimage_mono hU) (g.preimage_mono hV))).op
      (externalProduct K f g M N U V (m ⊗ₜ[K] n)) =
    externalProduct K f g M N U' V'
      ((M.presheaf.map (homOfLE hU).op m) ⊗ₜ[K]
        (N.presheaf.map (homOfLE hV).op n)) at h
  exact h

/-- Tensoring two finite families of actual affine sections gives precisely
all section families on the corresponding affine rectangles. -/
def coverTensorEquiv {ι κ : Type u} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (U : ι → X.Opens) (V : κ → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j)) :
    (∀ i, sections K M (U i)) ⊗[K] (∀ j, sections K N (V j)) ≃ₗ[K]
      (∀ i j, sections K (externalTensor f g M N) (rectangle f g (U i) (V j))) :=
  (TensorProduct.piLeft K (∀ j, sections K N (V j))
    (fun i => sections K M (U i))).trans
      (LinearEquiv.piCongrRight fun i =>
        (TensorProduct.piRight K K (sections K M (U i))
          (fun j => sections K N (V j))).trans
            (LinearEquiv.piCongrRight fun j =>
              LinearEquiv.ofBijective (externalProduct K f g M N (U i) (V j))
                (AffineRectangleTensor.externalProduct_bijective K f g H M N
                  (U i) (V j) (hU i) (hV j))))

@[simp] theorem coverTensorEquiv_tmul {ι κ : Type u} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (U : ι → X.Opens) (V : κ → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
    (m : ∀ i, sections K M (U i)) (n : ∀ j, sections K N (V j)) (i : ι) (j : κ) :
    coverTensorEquiv K f g H M N U V hU hV (m ⊗ₜ[K] n) i j =
      externalProduct K f g M N (U i) (V j) (m i ⊗ₜ[K] n j) := rfl

/-- Restriction to two families is intertwined by the genuine external-product
map and the genuine affine rectangle comparisons. -/
theorem coverTensorEquiv_restriction {ι κ : Type u} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (U : ι → X.Opens) (V : κ → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
    (W : X.Opens) (Z : Y.Opens) (hUW : ∀ i, U i ≤ W) (hVZ : ∀ j, V j ≤ Z)
    (t : sections K M W ⊗[K] sections K N Z) (i : ι) (j : κ) :
    coverTensorEquiv K f g H M N U V hU hV
        (TensorProduct.map (restriction K M U W hUW) (restriction K N V Z hVZ) t) i j =
      (externalTensor f g M N).presheaf.map
        (homOfLE (inf_le_inf (f.preimage_mono (hUW i)) (g.preimage_mono (hVZ j)))).op
        (externalProduct K f g M N W Z t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul m n =>
      simpa only [TensorProduct.map_tmul, coverTensorEquiv_tmul, restriction_apply] using
        (externalProduct_restrict_tmul_presheaf K f g M N (hUW i) (hVZ j) m n).symm
  | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]

/-- The first overlap differential is the difference of actual restrictions
on rectangles. -/
theorem coverTensorEquiv_difference_left {ι κ : Type u} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (U : ι → X.Opens) (V : κ → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
    (hUU : ∀ p : ι × ι, IsAffineOpen (U p.1 ⊓ U p.2))
    (t : (∀ i, sections K M (U i)) ⊗[K] (∀ j, sections K N (V j)))
    (i i' : ι) (j : κ) :
    coverTensorEquiv K f g H M N (fun p : ι × ι => U p.1 ⊓ U p.2) V hUU hV
        ((difference K M U).rTensor (∀ j, sections K N (V j)) t) (i, i') j =
      (externalTensor f g M N).presheaf.map
        (homOfLE (inf_le_inf (f.preimage_mono inf_le_left) le_rfl)).op
        (coverTensorEquiv K f g H M N U V hU hV t i j) -
      (externalTensor f g M N).presheaf.map
        (homOfLE (inf_le_inf (f.preimage_mono inf_le_right) le_rfl)).op
        (coverTensorEquiv K f g H M N U V hU hV t i' j) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul m n =>
      rw [LinearMap.rTensor_tmul, coverTensorEquiv_tmul, difference_apply,
        TensorProduct.sub_tmul, map_sub, coverTensorEquiv_tmul, coverTensorEquiv_tmul]
      have h₁ := externalProduct_restrict_tmul_presheaf K f g M N
        (U := U i) (U' := U i ⊓ U i') (V := V j) (V' := V j)
        inf_le_left le_rfl (m i) (n j)
      have h₂ := externalProduct_restrict_tmul_presheaf K f g M N
        (U := U i') (U' := U i ⊓ U i') (V := V j) (V' := V j)
        inf_le_right le_rfl (m i') (n j)
      simpa only [CategoryTheory.homOfLE_refl, CategoryTheory.op_id,
        CategoryTheory.Functor.map_id, ConcreteCategory.id_apply] using
        congrArg₂ (fun a b => a - b) h₁.symm h₂.symm
  | add a b ha hb =>
      simp only [map_add, Pi.add_apply, ha, hb]
      abel

/-- The second overlap differential is the other difference of actual
restrictions on rectangles. -/
theorem coverTensorEquiv_difference_right {ι κ : Type u} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (U : ι → X.Opens) (V : κ → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
    (hVV : ∀ p : κ × κ, IsAffineOpen (V p.1 ⊓ V p.2))
    (t : (∀ i, sections K M (U i)) ⊗[K] (∀ j, sections K N (V j)))
    (i : ι) (j j' : κ) :
    coverTensorEquiv K f g H M N U (fun p : κ × κ => V p.1 ⊓ V p.2) hU hVV
        ((difference K N V).lTensor (∀ i, sections K M (U i)) t) i (j, j') =
      (externalTensor f g M N).presheaf.map
        (homOfLE (inf_le_inf le_rfl (g.preimage_mono inf_le_left))).op
        (coverTensorEquiv K f g H M N U V hU hV t i j) -
      (externalTensor f g M N).presheaf.map
        (homOfLE (inf_le_inf le_rfl (g.preimage_mono inf_le_right))).op
        (coverTensorEquiv K f g H M N U V hU hV t i j') := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul m n =>
      rw [LinearMap.lTensor_tmul, coverTensorEquiv_tmul, difference_apply,
        TensorProduct.tmul_sub, map_sub, coverTensorEquiv_tmul, coverTensorEquiv_tmul]
      have h₁ := externalProduct_restrict_tmul_presheaf K f g M N
        (U := U i) (U' := U i) (V := V j) (V' := V j ⊓ V j')
        le_rfl inf_le_left (m i) (n j)
      have h₂ := externalProduct_restrict_tmul_presheaf K f g M N
        (U := U i) (U' := U i) (V := V j') (V' := V j ⊓ V j')
        le_rfl inf_le_right (m i) (n j')
      simpa only [CategoryTheory.homOfLE_refl, CategoryTheory.op_id,
        CategoryTheory.Functor.map_id, ConcreteCategory.id_apply] using
        congrArg₂ (fun a b => a - b) h₁.symm h₂.symm
  | add a b ha hb =>
      simp only [map_add, Pi.add_apply, ha, hb]
      abel

include H in
/-- The actual external-product map is injective over any two finite affine
covers. No cohomology comparison is assumed. -/
theorem externalProduct_injective_of_covers {ι κ : Type u} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (U : ι → X.Opens) (V : κ → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
    (W : X.Opens) (Z : Y.Opens) (hUW : ∀ i, U i ≤ W) (hVZ : ∀ j, V j ≤ Z)
    (hcoverU : W ≤ ⨆ i, U i) (hcoverV : Z ≤ ⨆ j, V j) :
    Function.Injective (externalProduct K f g M N W Z) := by
  intro s t h
  apply TensorProduct.map_injective_of_flat_flat
    (restriction K M U W hUW) (restriction K N V Z hVZ)
    (restriction_injective K M U W hUW hcoverU)
    (restriction_injective K N V Z hVZ hcoverV)
  apply (coverTensorEquiv K f g H M N U V hU hV).injective
  funext i j
  rw [coverTensorEquiv_restriction, coverTensorEquiv_restriction, h]

/-- The actual rectangles cover the rectangle of the two covered opens. -/
theorem rectangle_cover {ι κ : Type u}
    (U : ι → X.Opens) (V : κ → Y.Opens) (W : X.Opens) (Z : Y.Opens)
    (hcoverU : W ≤ ⨆ i, U i) (hcoverV : Z ≤ ⨆ j, V j) :
    rectangle f g W Z ≤ ⨆ p : ι × κ, rectangle f g (U p.1) (V p.2) := by
  intro x hx
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcoverU hx.1)
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcoverV hx.2)
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨(i, j), hi, hj⟩

include H in
/-- The full canonical section tensor map is bijective over finite affine
covers with affine pairwise intersections. These hypotheses are available on
the actual projective products, over every field. -/
theorem externalProduct_bijective_of_covers {ι κ : Type u} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (U : ι → X.Opens) (V : κ → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
    (hUU : ∀ p : ι × ι, IsAffineOpen (U p.1 ⊓ U p.2))
    (hVV : ∀ p : κ × κ, IsAffineOpen (V p.1 ⊓ V p.2))
    (W : X.Opens) (Z : Y.Opens) (hUW : ∀ i, U i ≤ W) (hVZ : ∀ j, V j ≤ Z)
    (hcoverU : W ≤ ⨆ i, U i) (hcoverV : Z ≤ ⨆ j, V j) :
    Function.Bijective (externalProduct K f g M N W Z) := by
  refine ⟨externalProduct_injective_of_covers K f g H M N U V hU hV
    W Z hUW hVZ hcoverU hcoverV, ?_⟩
  intro s
  let Q := externalTensor f g M N
  let e := coverTensorEquiv K f g H M N U V hU hV
  let s₀ : ∀ i j, sections K Q (rectangle f g (U i) (V j)) := fun i j =>
    Q.presheaf.map
      (homOfLE (inf_le_inf (f.preimage_mono (hUW i)) (g.preimage_mono (hVZ j)))).op s
  let z := e.symm s₀
  have hz : e z = s₀ := e.apply_symm_apply s₀
  have hzL : (difference K M U).rTensor (∀ j, sections K N (V j)) z = 0 := by
    apply (coverTensorEquiv K f g H M N
      (fun p : ι × ι => U p.1 ⊓ U p.2) V hUU hV).injective
    simp only [map_zero]
    funext p j
    rw [coverTensorEquiv_difference_left]
    change Q.presheaf.map _ (e z p.1 j) - Q.presheaf.map _ (e z p.2 j) = 0
    rw [hz]
    dsimp only [s₀]
    rw [sub_eq_zero]
    exact restriction_paths Q _ _ _ _ s
  have hzR : (difference K N V).lTensor (∀ i, sections K M (U i)) z = 0 := by
    apply (coverTensorEquiv K f g H M N U
      (fun p : κ × κ => V p.1 ⊓ V p.2) hU hVV).injective
    simp only [map_zero]
    funext i p
    rw [coverTensorEquiv_difference_right]
    change Q.presheaf.map _ (e z i p.1) - Q.presheaf.map _ (e z i p.2) = 0
    rw [hz]
    dsimp only [s₀]
    rw [sub_eq_zero]
    exact restriction_paths Q _ _ _ _ s
  obtain ⟨t, ht⟩ := TensorKernelIntersection.exists_tensor_preimage
    (restriction K M U W hUW) (difference K M U)
    (restriction K N V Z hVZ) (difference K N V)
    (restriction_injective K M U W hUW hcoverU)
    (restriction_difference_exact K M U W hUW hcoverU)
    (restriction_difference_exact K N V Z hVZ hcoverV) z hzL hzR
  refine ⟨t, ?_⟩
  apply TopCat.Sheaf.eq_of_locally_eq'
    (⟨Q.presheaf, Q.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat P)
    (fun p : ι × κ => rectangle f g (U p.1) (V p.2))
    (rectangle f g W Z)
    (fun p => homOfLE (inf_le_inf (f.preimage_mono (hUW p.1))
      (g.preimage_mono (hVZ p.2))))
    (rectangle_cover f g U V W Z hcoverU hcoverV)
  intro p
  have h := coverTensorEquiv_restriction K f g H M N U V hU hV
    W Z hUW hVZ t p.1 p.2
  rw [ht] at h
  have hz' := congrFun (congrFun hz p.1) p.2
  exact h.symm.trans hz'

end External
end PaperVerification.Segre.ExternalGlobalSections

end SegreExternalGlobalSections

section SegreFiniteGlobalSections

/-!
# Global sections on the fixed finite product

The comparison is assembled from the canonical section tensor maps. It is
an isomorphism of modules over the original coefficient field on the actual
iterated scheme product used by the cohomology and critical-map arguments.
-/

set_option autoImplicit false

namespace PaperVerification.Segre.FixedProductCohomology.CoveredScheme

open AlgebraicGeometry
universe u
variable {K : Type u} [Field K]

instance over (A : CoveredScheme K) : A.scheme.Over (Spec (.of K)) := ⟨A.toBase⟩

end PaperVerification.Segre.FixedProductCohomology.CoveredScheme

namespace PaperVerification.Segre.FiniteGlobalSections

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open FixedProductCohomology ExternalSections ExternalGlobalSections

universe u
variable {K : Type u} [Field K]

/-- The canonical global-section tensor comparison on the actual binary
covered product. -/
def binaryGlobalSectionsIso (A B : CoveredScheme K)
    (M : A.scheme.Modules) (N : B.scheme.Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] :
    sections K M ⊤ ⊗ sections K N ⊤ ≅
      sections K (CoveredScheme.externalTensor A B M N) ⊤ := by
  classical
  letI : Fintype A.index := Fintype.ofFinite A.index
  letI : Fintype B.index := Fintype.ofFinite B.index
  let p := pullback.fst A.toBase B.toBase
  let q := pullback.snd A.toBase B.toBase
  letI : (pullback A.toBase B.toBase).Over (Spec (.of K)) := ⟨p ≫ A.toBase⟩
  letI : p.IsOver (Spec (.of K)) := ⟨rfl⟩
  letI : q.IsOver (Spec (.of K)) := ⟨(pullback.condition (f := A.toBase) (g := B.toBase)).symm⟩
  have H : IsPullback p q A.toBase B.toBase := IsPullback.of_hasPullback _ _
  let e := LinearEquiv.ofBijective (externalProduct K p q M N ⊤ ⊤)
    (externalProduct_bijective_of_covers K p q H M N A.opens B.opens A.affine B.affine
      (fun ij => (A.affine ij.1).inf (A.affine ij.2))
      (fun ij => (B.affine ij.1).inf (B.affine ij.2))
      ⊤ ⊤ (fun _ => le_top) (fun _ => le_top)
      (by rw [A.covers]) (by rw [B.covers]))
  have htop : rectangle p q ⊤ ⊤ = (⊤ : (CoveredScheme.product A B).scheme.Opens) := by
    simp [rectangle]
  exact e.toModuleIso ≪≫
    (((sectionsBasePresheafFunctor K).obj (CoveredScheme.externalTensor A B M N)).mapIso
      (eqToIso htop).op).symm

/-- Canonical global sections of the full external product, for every
nonempty finite family and every quasicoherent factor sheaf. -/
def finiteGlobalSectionsIso : {k : ℕ} →
    (A : Fin (k + 1) → CoveredScheme K) →
    (M : ∀ i, (A i).scheme.Modules) →
    (∀ i, (M i).IsQuasicoherent) →
      (FiniteTensor.tensorObj (C := ModuleCat.{u} K) (fun i => sections K (M i) ⊤) ≅
        sections K (CoveredScheme.finiteExternalTensor A M) ⊤)
  | 0, A, M, _ => ρ_ (sections K (M 0) ⊤)
  | k + 1, A, M, hM => by
      letI : (M 0).IsQuasicoherent := hM 0
      let B := CoveredScheme.finiteProduct (fun i : Fin (k + 1) => A i.succ)
      let N := CoveredScheme.finiteExternalTensor
        (fun i : Fin (k + 1) => A i.succ) (fun i => M i.succ)
      letI : N.IsQuasicoherent :=
        CoveredScheme.finiteExternalTensor_quasicoherent _ _ (fun i => hM i.succ)
      exact (Iso.refl (sections K (M 0) ⊤) ⊗ᵢ
        finiteGlobalSectionsIso (fun i : Fin (k + 1) => A i.succ)
          (fun i => M i.succ) (fun i => hM i.succ)) ≪≫
          binaryGlobalSectionsIso (A 0) B (M 0) N

end PaperVerification.Segre.FiniteGlobalSections

end SegreFiniteGlobalSections

end SegreGlobalCriticalSections

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
