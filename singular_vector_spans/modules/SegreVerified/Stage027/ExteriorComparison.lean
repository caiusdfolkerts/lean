module
public import SegreVerified.Stage027.CriticalEuler
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
set_option maxErrors 1
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
  out.putStrLn "SEGRE_STAGE Stage027.ExteriorComparison"
  out.flush

/-!
# The actual critical bundle and its weighted Koszul complex

The named sections preserve the original proof stages and local scopes.
-/

set_option autoImplicit false

section SegreUnitPivotKernel

/-!
# A literal basis for a functional kernel with a unit coordinate

The functional is arbitrary. Its value on a specified coordinate vector is
proved to be one. Restriction to all other coordinates then gives an explicit
linear equivalence from the actual kernel to the full free coordinate module.
The inverse subtracts the functional value in the pivot coordinate.

No rank or freeness assertion is assumed. This construction is valid over
every commutative ring, including the zero ring. It will be applied to the
actual normalized Euler functional over rings of sections on projective
charts.
-/

set_option autoImplicit false

namespace PaperVerification.Segre.UnitPivotKernel

variable {I R : Type*} [DecidableEq I] [CommRing R]

/-- Coordinates other than the specified pivot. -/
abbrev OffPivot (p : I) := {i : I // i ≠ p}

/-- Insert a zero in the pivot coordinate, keeping every other coordinate. -/
def insertZero (p : I) : (OffPivot p → R) →ₗ[R] (I → R) where
  toFun v i := if h : i = p then 0 else v ⟨i, h⟩
  map_add' v w := by
    funext i
    by_cases h : i = p <;> simp [h]
  map_smul' c v := by
    funext i
    by_cases h : i = p <;> simp [h]

/-- Discard only the pivot coordinate. -/
def erasePivot (p : I) : (I → R) →ₗ[R] (OffPivot p → R) :=
  LinearMap.pi (fun i => LinearMap.proj i.val)

@[simp] theorem insertZero_pivot (p : I) (v : OffPivot p → R) :
    insertZero p v p = 0 := by simp [insertZero]

@[simp] theorem insertZero_nonpivot (p : I) (v : OffPivot p → R) (i : OffPivot p) :
    insertZero p v i.val = v i := by simp [insertZero, i.property]

@[simp] theorem erasePivot_apply (p : I) (v : I → R) (i : OffPivot p) :
    erasePivot p v i = v i.val := rfl

/-- The discarded component is exactly its scalar multiple of the pivot vector. -/
theorem insertZero_erasePivot (p : I) (v : I → R) :
    insertZero p (erasePivot p v) = v - v p • Pi.single p (1 : R) := by
  funext i
  by_cases h : i = p
  · subst i
    simp [insertZero]
  · simp [insertZero, erasePivot, h, Ne.symm h, Pi.single_apply]

variable (p : I) (φ : (I → R) →ₗ[R] R)
variable (hφ : φ (Pi.single p (1 : R)) = 1)

/-- The literal inverse: extend by zero, then remove the functional value
in the pivot coordinate. -/
def lift : (OffPivot p → R) →ₗ[R] LinearMap.ker φ :=
  ((insertZero p) - (φ.comp (insertZero p)).smulRight (Pi.single p (1 : R))).codRestrict
    (LinearMap.ker φ) (by
      intro v
      change φ (insertZero p v - φ (insertZero p v) • Pi.single p (1 : R)) = 0
      rw [map_sub, _root_.map_smul, hφ, smul_eq_mul, mul_one, sub_self])

@[simp] theorem lift_val (v : OffPivot p → R) :
    (lift p φ hφ v).val =
      insertZero p v - φ (insertZero p v) • Pi.single p (1 : R) := rfl

/-- Coordinates of an actual kernel vector, without any quotient or auxiliary relation. -/
def coordinates : LinearMap.ker φ →ₗ[R] (OffPivot p → R) :=
  (erasePivot p).comp (LinearMap.ker φ).subtype

@[simp] theorem coordinates_apply (v : LinearMap.ker φ) (i : OffPivot p) :
    coordinates p φ v i = v.val i.val := rfl

@[simp] theorem coordinates_lift (v : OffPivot p → R) :
    coordinates p φ (lift p φ hφ v) = v := by
  funext i
  change ((insertZero p v - φ (insertZero p v) • Pi.single p (1 : R)) : I → R) i.val = v i
  simp only [Pi.sub_apply, Pi.smul_apply, insertZero_nonpivot, smul_eq_mul,
    Pi.single_apply, if_neg i.property, mul_zero, sub_zero]

@[simp] theorem lift_coordinates (v : LinearMap.ker φ) :
    lift p φ hφ (coordinates p φ v) = v := by
  apply Subtype.ext
  change insertZero p (erasePivot p v.val) -
    φ (insertZero p (erasePivot p v.val)) • Pi.single p (1 : R) = v.val
  rw [insertZero_erasePivot, map_sub, _root_.map_smul, hφ]
  have hv : φ v.val = 0 := v.property
  rw [hv, smul_eq_mul, mul_one, zero_sub, neg_smul, sub_neg_eq_add]
  exact sub_add_cancel _ _

/-- The complete free-coordinate description of the actual functional kernel. -/
def coordinatesEquiv : LinearMap.ker φ ≃ₗ[R] (OffPivot p → R) where
  __ := coordinates p φ
  invFun := lift p φ hφ
  left_inv := lift_coordinates p φ hφ
  right_inv := coordinates_lift p φ hφ

@[simp] theorem coordinatesEquiv_apply (v : LinearMap.ker φ) (i : OffPivot p) :
    coordinatesEquiv p φ hφ v i = v.val i.val := rfl

@[simp] theorem coordinatesEquiv_symm_apply (v : OffPivot p → R) :
    (coordinatesEquiv p φ hφ).symm v = lift p φ hφ v := rfl

/-- A genuine basis, indexed by exactly the nonpivot coordinates. -/
def kernelBasis [Finite I] : Module.Basis (OffPivot p) R (LinearMap.ker φ) :=
  Module.Basis.ofEquivFun (coordinatesEquiv p φ hφ)

@[simp] theorem kernelBasis_repr [Finite I] (v : LinearMap.ker φ) (i : OffPivot p) :
    (kernelBasis p φ hφ).repr v i = v.val i.val := rfl

end PaperVerification.Segre.UnitPivotKernel

end SegreUnitPivotKernel

section SegreEulerCriticalFrame

/-!
# A concrete local frame of the actual positive Euler kernel

Every open contained in a standard projective chart has the full, explicit
coordinate-wedge basis of the genuine Euler-kernel section module. The
coordinate critical equations are the values of the actual critical
functional on this basis. The result holds over the actual structure-sheaf
ring, in every characteristic, with no freeness or comparison premise.

The sheaf-theoretic finite-product Koszul globalization remains a separate
obligation; a basis of these sections is not asserted to solve that problem.
-/

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

namespace PaperVerification.Segre.EulerCriticalFrame

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open ProjectiveCech EulerSheaf EulerSections EulerCriticalFunctional EulerCriticalChart
open scoped BigOperators

universe u
variable {I K : Type u} [Fintype I] [DecidableEq I] [Field K]

local notation "𝒜" => MvPolynomial.homogeneousSubmodule I K
local notation "X" => Proj (MvPolynomial.homogeneousSubmodule I K)
local notation "O1" => Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule I K) (1 : ℤ)

variable (p : I) (U : (Proj (MvPolynomial.homogeneousSubmodule I K)).Opens) (hU : U ≤ coordinateOpen (K := K) p)

/-- The actual normalized Euler map takes the pivot vector to one. -/
theorem normalizedEuler_pivot :
    normalizedEuler p U hU (Pi.single p (1 : Γ(X, U))) = 1 := by
  change (∑ i, normalizedCoordinate p U hU i *
    (Pi.single p (1 : Γ(X, U)) : I → Γ(X, U)) i) = 1
  rw [Finset.sum_eq_single p]
  · simp only [Pi.single_eq_same, mul_one, normalizedCoordinate_pivot]
  · intro i _ hi
    simp only [Pi.single_apply, if_neg hi, mul_zero]
  · intro hp
    exact (hp (Finset.mem_univ p)).elim

/-- An explicit free-coordinate equivalence for the actual section module. -/
def chartFreeEquiv :
    Γ(eulerKernel (I := I) (K := K) 2, U) ≃ₗ[Γ(X, U)]
      (UnitPivotKernel.OffPivot p → Γ(X, U)) :=
  (chartKernelEquiv p U hU).trans
    (UnitPivotKernel.coordinatesEquiv p (normalizedEuler p U hU)
      (normalizedEuler_pivot p U hU))

@[simp] theorem chartFreeEquiv_apply
    (s : Γ(eulerKernel (I := I) (K := K) 2, U)) (i : UnitPivotKernel.OffPivot p) :
    chartFreeEquiv p U hU s i = (chartKernelEquiv p U hU s).val i.val := rfl

/-- The literal global coordinate-wedge sections become the standard free basis
on every open of the pivot chart. -/
theorem chartFreeEquiv_coordinateWedge (q : UnitPivotKernel.OffPivot p) :
    chartFreeEquiv p U hU (coordinateWedge p q.val U) =
      Pi.single q (1 : Γ(X, U)) := by
  funext j
  rw [chartFreeEquiv_apply, chartKernelEquiv_val, chartSourceEquiv_apply,
    coordinateWedge_image, coordinatePair, map_sub]
  simp only [Pi.sub_apply, coordinateSingle_component]
  rw [Pi.single_apply, Pi.single_apply, if_neg j.property, sub_zero]
  by_cases hq : q.val = j.val
  · have hq' : q = j := Subtype.ext hq
    subst q
    rw [if_pos rfl, Pi.single_eq_same]
    exact normalizedCoordinate_pivot p U hU
  · have hq' : q ≠ j := fun h => hq (congrArg Subtype.val h)
    rw [if_neg (Ne.symm hq), map_zero, Pi.single_eq_of_ne' hq']

/-- A genuine basis of the full section module, of size exactly `card I - 1`. -/
def chartBasis : Module.Basis (UnitPivotKernel.OffPivot p) Γ(X, U)
    Γ(eulerKernel (I := I) (K := K) 2, U) :=
  Module.Basis.ofEquivFun (chartFreeEquiv p U hU)

@[simp] theorem chartBasis_repr
    (s : Γ(eulerKernel (I := I) (K := K) 2, U)) (i : UnitPivotKernel.OffPivot p) :
    (chartBasis p U hU).repr s i = (chartKernelEquiv p U hU s).val i.val := rfl

/-- This basis is exactly the expected coordinate wedges, not an arbitrary chosen basis. -/
@[simp] theorem chartBasis_apply (i : UnitPivotKernel.OffPivot p) :
    chartBasis p U hU i = coordinateWedge p i.val U := by
  have h := congrFun (Module.Basis.coe_ofEquivFun (chartFreeEquiv p U hU)) i
  change chartBasis p U hU i = (chartFreeEquiv p U hU).symm (Pi.single i 1) at h
  rw [h]
  apply (chartFreeEquiv p U hU).injective
  rw [LinearEquiv.apply_symm_apply, chartFreeEquiv_coordinateWedge]

/-- Every actual section has the full coordinate-wedge expansion. -/
theorem chartSection_expansion (s : Γ(eulerKernel (I := I) (K := K) 2, U)) :
    ∑ i : UnitPivotKernel.OffPivot p,
      (chartKernelEquiv p U hU s).val i.val • coordinateWedge p i.val U = s := by
  simpa only [chartBasis_repr, chartBasis_apply] using (chartBasis p U hU).sum_repr s

/-- The critical equations are precisely the coefficients of the actual functional
in the actual local free frame. -/
theorem normalizedCriticalMap_chartBasis (t : ℤ)
    (c : I → (O1 ⟶ Proj.twistingSheaf 𝒜 t)) (i : UnitPivotKernel.OffPivot p) :
    normalizedCriticalMap p U hU t c (chartBasis p U hU i) =
      criticalCoordinate p U hU t c i.val := by
  rw [chartBasis_apply, normalizedCriticalMap_coordinateWedge]

end PaperVerification.Segre.EulerCriticalFrame

end SegreEulerCriticalFrame

namespace PaperVerification.Segre.SchemeTensorPresentation

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite

universe u

/-- The existing sheafification functor, expressed on a variable scheme. -/
abbrev schemeSheafification (Y : Scheme.{u}) :
    PresheafOfModulesOfCommRing.{u} Y.presheaf ⥤ Y.Modules :=
  show PresheafOfModules.{u} Y.ringCatSheaf.obj ⥤
      SheafOfModules.{u} Y.ringCatSheaf from
    PresheafOfModules.sheafification.{u}
      (R₀ := Y.ringCatSheaf.obj) (R := Y.ringCatSheaf)
      (𝟙 Y.ringCatSheaf.obj)

/-- The canonical strong monoidal structure on the identical functor. -/
instance schemeSheafificationMonoidal (Y : Scheme.{u}) :
    (schemeSheafification Y).Monoidal :=
  TauCeti.SheafOfModules.sheafificationMonoidal Y.sheaf

/-- The existing sheafification adjunction, exposed before specialization. -/
instance schemeSheafificationIsLeftAdjoint (Y : Scheme.{u}) :
    (schemeSheafification Y).IsLeftAdjoint :=
  (TauCeti.SheafOfModules.sheafificationForgetAdjunction Y.sheaf).isLeftAdjoint

/-- This actual left adjoint preserves zero morphisms. -/
instance schemeSheafificationPreservesZeroMorphisms (Y : Scheme.{u}) :
    (schemeSheafification Y).PreservesZeroMorphisms := by
  infer_instance

/-- The existing exact sheafification functor preserves finite limits. -/
instance schemeSheafificationPreservesFiniteLimits (Y : Scheme.{u}) :
    Limits.PreservesFiniteLimits (schemeSheafification Y) :=
  inferInstanceAs
    (Limits.PreservesFiniteLimits
      (PresheafOfModules.sheafification.{u}
        (R₀ := Y.ringCatSheaf.obj) (R := Y.ringCatSheaf)
        (𝟙 Y.ringCatSheaf.obj)))

/-- Bilinearity of the actual tensor-section map, in native section spaces. -/
theorem tensorSection_smul_right {Y : Scheme.{u}} {M N : Y.Modules}
    (U : Y.Opens) (a : Γ(Y, U)) (s : Γ(M, U)) (t : Γ(N, U)) :
    SheafCoefficientContraction.tensorSection Y.sheaf M N (op U) s (a • t) =
      a • SheafCoefficientContraction.tensorSection Y.sheaf M N (op U) s t := by
  have h : EulerTwistComparison.tensorSectionOn (Y := Y) U s (a • t) =
      a • EulerTwistComparison.tensorSectionOn (Y := Y) U s t := by
    unfold EulerTwistComparison.tensorSectionOn
    rw [TensorProduct.tmul_smul]
    exact _root_.map_smul _ _ _
  exact (tensorSection_eq (Y := Y) U s (a • t)).trans
    (h.trans ((congrArg (fun z : Γ(M ⊗ N, U) => a • z)
      (tensorSection_eq (Y := Y) U s t)).symm))

open scoped TensorProduct BigOperators

/-- The actual tensor-section map is linear in its first section argument. -/
theorem tensorSection_sum_smul_left {Y : Scheme.{u}} {M N : Y.Modules}
    {ι : Type*} [Fintype ι] (U : Y.Opens)
    (a : ι → Γ(Y, U)) (s : ι → Γ(M, U)) (t : Γ(N, U)) :
    SheafCoefficientContraction.tensorSection Y.sheaf M N (op U)
      (∑ i, a i • s i) t =
        ∑ i, a i • SheafCoefficientContraction.tensorSection Y.sheaf M N
          (op U) (s i) t := by
  have h : EulerTwistComparison.tensorSectionOn (Y := Y) U
      (∑ i, a i • s i) t =
        ∑ i, a i • EulerTwistComparison.tensorSectionOn (Y := Y) U (s i) t := by
    unfold EulerTwistComparison.tensorSectionOn
    simp only [TensorProduct.sum_tmul, ← TensorProduct.smul_tmul',
      map_sum, _root_.map_smul]
  have hs : (∑ i, a i • EulerTwistComparison.tensorSectionOn (Y := Y) U (s i) t) =
      ∑ i, a i • SheafCoefficientContraction.tensorSection Y.sheaf M N
        (op U) (s i) t := by
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun z : Γ(M ⊗ N, U) => a i • z)
      (tensorSection_eq (Y := Y) U (s i) t).symm
  exact (tensorSection_eq (Y := Y) U (∑ i, a i • s i) t).trans (h.trans hs)

end PaperVerification.Segre.SchemeTensorPresentation

namespace PaperVerification.Segre.SchemeCoefficientComparison

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory Opposite
open AlgebraicGeometry.Scheme.Modules
open SheafCoefficientContraction
open scoped TensorProduct BigOperators

universe u
variable {Y : Scheme.{u}} (M L : Y.Modules)

/-- The actual exterior inclusion induced by the kernel injection. -/
def presheafKernelInclusion (φ : M ⟶ L) (p : ℕ) :
    (PresheafOfModulesOfCommRing.exteriorPower (R := Y.presheaf) (p + 1)).obj
        (kernel φ).val ⟶
      (PresheafOfModulesOfCommRing.exteriorPower (R := Y.presheaf) (p + 1)).obj M.val :=
  (PresheafOfModulesOfCommRing.exteriorPower (R := Y.presheaf) (p + 1)).map
    (kernel.ι φ).val

/-- The full coefficient contraction kills every actual kernel wedge. -/
theorem presheafKernelInclusion_contraction (φ : M ⟶ L) (p : ℕ) :
    presheafKernelInclusion M L φ p ≫
        presheafContraction (R := Y.presheaf) φ.val p =
      (0 :
        (PresheafOfModulesOfCommRing.exteriorPower (R := Y.presheaf) (p + 1)).obj
            (kernel φ).val ⟶
          (PresheafOfModulesOfCommRing.exteriorPower (R := Y.presheaf) p).obj M.val ⊗
            L.val) := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext (R := Y.presheaf.obj U)
  apply exteriorPower.linearMap_ext (R := Y.presheaf.obj U) (n := p + 1)
  apply AlternatingMap.ext
  intro v
  change CoefficientContraction.contraction (R := Y.presheaf.obj U)
    (φ.val.app' U).hom p
    (exteriorPower.map (R := Y.presheaf.obj U) (p + 1)
      ((kernel.ι φ).val.app' U).hom
      (exteriorPower.ιMulti (Y.presheaf.obj U) (p + 1) v)) = 0
  rw [exteriorPower.map_apply_ιMulti, CoefficientContraction.contraction_ιMulti]
  apply Finset.sum_eq_zero
  intro i _
  have h := congrArg
    (fun f : kernel φ ⟶ L => (f.val.app' U).hom (v i))
    (kernel.condition φ)
  change (φ.val.app' U).hom (((kernel.ι φ).val.app' U).hom (v i)) = 0 at h
  let w : ⋀[Y.presheaf.obj U]^p (M.val.obj U) :=
    exteriorPower.ιMulti (Y.presheaf.obj U) p
      (i.removeNth (fun j => ((kernel.ι φ).val.app' U).hom (v j)))
  change (-1 : ℤ) ^ (i : ℕ) •
    (w ⊗ₜ[Y.presheaf.obj U]
      (φ.val.app' U).hom (((kernel.ι φ).val.app' U).hom (v i))) = 0
  have ht :
      w ⊗ₜ[Y.presheaf.obj U]
          (φ.val.app' U).hom (((kernel.ι φ).val.app' U).hom (v i)) =
        (0 : (⋀[Y.presheaf.obj U]^p (M.val.obj U)) ⊗[Y.presheaf.obj U] (L.val.obj U)) :=
    (congrArg (fun l : L.val.obj U => w ⊗ₜ[Y.presheaf.obj U] l) h).trans
      (TensorProduct.tmul_zero (R := Y.presheaf.obj U) (L.val.obj U) w)
  exact (congrArg
    (fun z : (⋀[Y.presheaf.obj U]^p (M.val.obj U)) ⊗[Y.presheaf.obj U] (L.val.obj U) =>
      (-1 : ℤ) ^ (i : ℕ) • z) ht).trans (smul_zero _)

/-- Evaluation of the actual presheaf kernel is its full algebraic kernel. -/
def presheafKernelSectionsEquiv
    {P Q : PresheafOfModulesOfCommRing.{u} Y.presheaf}
    (φ : P ⟶ Q) (U : Y.Opens) :
    (kernel φ).obj (op U) ≃ₗ[Γ(Y, U)] LinearMap.ker (φ.app (op U)).hom :=
  ((PreservesKernel.iso (PresheafOfModules.evaluation Y.ringCatSheaf.obj (op U)) φ) ≪≫
    ModuleCat.kernelIsoKer
      ((PresheafOfModules.evaluation Y.ringCatSheaf.obj (op U)).map φ)).toLinearEquiv

/-- The chosen kernel comparison retains the actual kernel inclusion. -/
theorem presheafKernelSectionsEquiv_val
    {P Q : PresheafOfModulesOfCommRing.{u} Y.presheaf}
    (φ : P ⟶ Q) (U : Y.Opens) (z : (kernel φ).obj (op U)) :
    (presheafKernelSectionsEquiv (Y := Y) φ U z).val =
      (kernel.ι φ).app (op U) z := by
  let F := PresheafOfModules.evaluation Y.ringCatSheaf.obj (op U)
  have h : ((PreservesKernel.iso F φ) ≪≫ ModuleCat.kernelIsoKer (F.map φ)).hom ≫
      ModuleCat.ofHom (F.map φ).hom.ker.subtype = F.map (kernel.ι φ) := by
    simp only [Iso.trans_hom, Category.assoc, ModuleCat.kernelIsoKer_hom_ker_subtype]
    erw [PreservesKernel.iso_hom, kernelComparison_comp_ι]
  exact ConcreteCategory.congr_hom h z

/-- The original coefficient-target comparison, on an arbitrary scheme. -/
def coefficientTargetIso (p : ℕ) :
    (SchemeTensorPresentation.schemeSheafification Y).obj
        ((PresheafOfModulesOfCommRing.exteriorPower (R := Y.presheaf) p).obj M.val ⊗
          L.val) ≅
      (SheafOfModules.exteriorPower Y.sheaf p).obj M ⊗ L :=
  (Functor.Monoidal.μIso (SchemeTensorPresentation.schemeSheafification Y)
    ((PresheafOfModulesOfCommRing.exteriorPower (R := Y.presheaf) p).obj M.val)
      L.val).symm ≪≫
      ((SheafOfModules.exteriorPowerIso (R := Y.sheaf) p M).symm ⊗ᵢ
        TauCeti.SheafOfModules.sheafificationIso Y.ringCatSheaf L)

/-- Its actual adjunction transpose is the exterior unit followed by the
canonical tensor comparison. -/
theorem coefficientTargetIso_transpose (p : ℕ) :
    (TauCeti.SheafOfModules.sheafificationForgetAdjunction Y.sheaf).homEquiv
        ((PresheafOfModulesOfCommRing.exteriorPower (R := Y.presheaf) p).obj M.val ⊗ L.val)
        ((SheafOfModules.exteriorPower Y.sheaf p).obj M ⊗ L)
        (coefficientTargetIso M L p).hom =
      (exteriorUnit Y.sheaf M p ⊗ₘ 𝟙 L.val) ≫
        Functor.LaxMonoidal.μ (SheafOfModules.forget Y.ringCatSheaf)
          ((SheafOfModules.exteriorPower Y.sheaf p).obj M) L := by
  let A := TauCeti.SheafOfModules.sheafificationForgetAdjunction Y.sheaf
  let E := SheafOfModules.exteriorPowerIso (R := Y.sheaf) p M
  let c := (TauCeti.SheafOfModules.sheafificationIso Y.ringCatSheaf L).hom
  have hE : A.homEquiv _ _ E.inv = exteriorUnit Y.sheaf M p := by
    exact A.homEquiv_unit _ _ E.inv
  have hc : A.homEquiv _ _ c = 𝟙 L.val := by
    have hcout := TauCeti.SheafOfModules.sheafificationForgetAdjunction_counit_app
      Y.sheaf L
    exact (congrArg (A.homEquiv _ _) hcout).symm.trans
      ((A.homEquiv_unit _ _ (A.counit.app L)).trans (A.right_triangle_components L))
  have h := A.homEquiv_δ_comp_tensorHom_comp E.inv c
    (𝟙 (((SheafOfModules.exteriorPower Y.sheaf p).obj M) ⊗ L))
  rw [hE, hc] at h
  simp only [Category.comp_id, CategoryTheory.Functor.map_id] at h
  simpa only [coefficientTargetIso, Iso.trans_hom,
    Iso.symm_hom, tensorIso_hom, Functor.Monoidal.μIso_inv] using h

/-- The literal sheafified coefficient differential, named before specialization. -/
def differential (φ : M ⟶ L) (p : ℕ) :
    (SheafOfModules.exteriorPower Y.sheaf (p + 1)).obj M ⟶
      (SheafOfModules.exteriorPower Y.sheaf p).obj M ⊗ L :=
  (SheafOfModules.exteriorPowerIso (R := Y.sheaf) (p + 1) M).hom ≫
    (SchemeTensorPresentation.schemeSheafification Y).map
      (presheafContraction (R := Y.presheaf) φ.val p) ≫
      (coefficientTargetIso M L p).hom

/-- Exact sheafification and the coefficient-contraction adjunction define
the same actual differential, before any concrete scheme is substituted. -/
theorem differential_eq_contraction (φ : M ⟶ L) (p : ℕ) :
    differential M L φ p = contraction Y.sheaf φ p := by
  let A := TauCeti.SheafOfModules.sheafificationForgetAdjunction Y.sheaf
  let E := SheafOfModules.exteriorPowerIso (R := Y.sheaf) (p + 1) M
  change E.hom ≫
      ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).map
        (presheafContraction (R := Y.presheaf) φ.val p) ≫
          (coefficientTargetIso M L p).hom) =
    E.hom ≫ (A.homEquiv _ _).symm (presheafTargetMap Y.sheaf φ p)
  apply congrArg (fun f => E.hom ≫ f)
  apply (A.homEquiv _ _).injective
  rw [A.homEquiv_naturality_left, coefficientTargetIso_transpose,
    Equiv.apply_symm_apply]
  rfl

/-- Exact sheafification transports the literal presheaf contraction
kernel to the kernel of the same coefficient-valued sheaf differential. -/
def cycleComparisonIso (φ : M ⟶ L) (p : ℕ) :
    (SchemeTensorPresentation.schemeSheafification Y).obj
        (kernel (presheafContraction (R := Y.presheaf) φ.val p)) ≅
      kernel (differential M L φ p) := by
  let F := SchemeTensorPresentation.schemeSheafification Y
  letI : PreservesFiniteLimits F :=
    SchemeTensorPresentation.schemeSheafificationPreservesFiniteLimits Y
  let D := presheafContraction (R := Y.presheaf) φ.val p
  let E := SheafOfModules.exteriorPowerIso (R := Y.sheaf) (p + 1) M
  let T := coefficientTargetIso M L p
  have hD : F.map D ≫ T.hom = E.inv ≫ differential M L φ p := by
    dsimp only [F, D, E, T]
    simp only [differential, Category.assoc, Iso.inv_hom_id_assoc]
  exact PreservesKernel.iso F D ≪≫
    kernel.mapIso (F.map D) (differential M L φ p) E.symm T hD

end PaperVerification.Segre.SchemeCoefficientComparison


section SegrePositiveExteriorEuler

/-!
# The actual exterior kernel of the positive Euler map

The canonical exterior inclusion of the actual kernel of
O(1)^I → O(2) is identified with the kernel of the actual coefficient-valued
exterior contraction. The sectionwise map is independent of every chart.
On every subopen of a coordinate chart, the genuine twisting trivialization
and the literal coordinate unit vector make it bijective in every degree.
The coordinate cover and exact sheafification then prove the global
isomorphism. The tensor target is identified by the existing strong monoidal
sheafification comparison.

There is no local-freeness, exterior-kernel, exactness, or comparison premise
in the final isomorphism.
-/

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

namespace PaperVerification.Segre.PositiveExteriorEuler

open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory Opposite TopologicalSpace
open EulerSheaf EulerSections EulerCriticalFunctional EulerCriticalChart
open EulerCriticalFrame
open scoped TensorProduct BigOperators

universe u
variable {I K : Type u} [Fintype I] [DecidableEq I] [Field K]

local notation "𝒜" => MvPolynomial.homogeneousSubmodule I K
local notation "X" => Proj (MvPolynomial.homogeneousSubmodule I K)
local notation "M" => positiveEulerSource (I := I) (K := K)
local notation "L" => Proj.twistingSheaf 𝒜 (2 : ℤ)
local notation "B" => eulerKernel (I := I) (K := K) 2

/-- The actual sectionwise coefficient contraction, with coefficients in O(2). -/
abbrev presheafDifferential (p : ℕ) :=
  SheafCoefficientContraction.presheafContraction (R := (X).presheaf)
    (eulerMap (I := I) (K := K) 2).val p

/-- The actual exterior inclusion before sheafification. -/
def presheafInclusion (p : ℕ) :
    (PresheafOfModulesOfCommRing.exteriorPower (R := (X).presheaf) (p + 1)).obj (B).val ⟶
      (PresheafOfModulesOfCommRing.exteriorPower (R := (X).presheaf) (p + 1)).obj (M).val :=
  SchemeCoefficientComparison.presheafKernelInclusion
    (Y := X) M L (eulerMap (I := I) (K := K) 2) p

/-- Actual Euler-kernel wedges are killed by the full coefficient contraction. -/
theorem presheafInclusion_differential (p : ℕ) :
    presheafInclusion (I := I) (K := K) p ≫
      presheafDifferential (I := I) (K := K) p = 0 := by
  exact SchemeCoefficientComparison.presheafKernelInclusion_contraction
    (Y := X) M L (eulerMap (I := I) (K := K) 2) p

/-- The canonical map to the literal presheaf contraction kernel. -/
def presheafKernelMap (p : ℕ) :
    (PresheafOfModulesOfCommRing.exteriorPower (R := (X).presheaf) (p + 1)).obj (B).val ⟶
      kernel (presheafDifferential (I := I) (K := K) p) :=
  kernel.lift _ (presheafInclusion (I := I) (K := K) p) (presheafInclusion_differential (I := I) (K := K) p)

run_cmd do
  (← IO.getStdout).flush
  let out ← IO.getStderr
  out.putStrLn "SEGRE_PROGRESS Stage027.ExteriorComparison before-cycle-sections-equiv"
  out.flush

/-- Evaluation of the actual presheaf kernel is the actual full algebraic kernel. -/
def cycleSectionsEquiv (p : ℕ) (U : (X).Opens) :
    (kernel (presheafDifferential (I := I) (K := K) p)).obj (op U) ≃ₗ[Γ(X, U)]
      LinearMap.ker (CoefficientContraction.contraction (R := Γ(X, U))
        ((eulerMap 2).val.app (op U)).hom p) :=
  SchemeCoefficientComparison.presheafKernelSectionsEquiv (Y := X)
    (presheafDifferential (I := I) (K := K) p) U

run_cmd do
  (← IO.getStdout).flush
  let out ← IO.getStderr
  out.putStrLn "SEGRE_PROGRESS Stage027.ExteriorComparison before-cycle-sections-value"
  out.flush

@[simp]
theorem cycleSectionsEquiv_val (p : ℕ) (U : (X).Opens)
    (z : (kernel (presheafDifferential (I := I) (K := K) p)).obj (op U)) :
    (cycleSectionsEquiv (I := I) (K := K) p U z).val =
      (kernel.ι (presheafDifferential (I := I) (K := K) p)).app (op U) z := by
  exact SchemeCoefficientComparison.presheafKernelSectionsEquiv_val (Y := X)
    (presheafDifferential (I := I) (K := K) p) U z

run_cmd do
  (← IO.getStdout).flush
  let out ← IO.getStderr
  out.putStrLn "SEGRE_PROGRESS Stage027.ExteriorComparison before-presheaf-kernel-value"
  out.flush

@[simp]
theorem presheafKernelMap_val (p : ℕ) (U : (X).Opens)
    (z : ⋀[Γ(X, U)]^(p + 1) Γ(B, U)) :
    (cycleSectionsEquiv (I := I) (K := K) p U ((presheafKernelMap (I := I) (K := K) p).app (op U) z)).val =
      exteriorPower.map (R := Γ(X, U)) (p + 1)
        ((kernel.ι (eulerMap 2)).val.app (op U)).hom z := by
  exact
    (cycleSectionsEquiv_val (I := I) (K := K) p U
      ((presheafKernelMap (I := I) (K := K) p).app (op U) z)).trans
      (congrArg
        (fun f :
          (PresheafOfModulesOfCommRing.exteriorPower (R := (X).presheaf) (p + 1)).obj
              (B).val ⟶
            (PresheafOfModulesOfCommRing.exteriorPower (R := (X).presheaf) (p + 1)).obj
              (M).val => (f.app' (op U)).hom z)
        (kernel.lift_ι (presheafDifferential (I := I) (K := K) p)
          (presheafInclusion (I := I) (K := K) p)
          (presheafInclusion_differential (I := I) (K := K) p)))

run_cmd do
  (← IO.getStdout).flush
  let out ← IO.getStderr
  out.putStrLn "SEGRE_PROGRESS Stage027.ExteriorComparison before-presheaf-kernel-chart"
  out.flush

/-- The whole canonical map is bijective over every subopen of every standard
coordinate chart. The coefficient frame and unit-value vector are constructed. -/
theorem presheafKernelMap_bijective_on_chart (p : ℕ) (j : I) (U : (X).Opens)
    (hU : U ≤ ProjectiveCech.coordinateOpen (K := K) j) :
    Function.Bijective ((presheafKernelMap (I := I) (K := K) p).app (op U)) := by
  let φ : Γ((∏ᶜ fun _ : I => Proj.twistingSheaf 𝒜 (2 - 1)), U) →ₗ[Γ(X, U)]
      Γ(Proj.twistingSheaf 𝒜 2, U) :=
    ((eulerMap (I := I) (K := K) 2).val.app (op U)).hom
  let e := kernelSectionsEquiv (I := I) (K := K) 2 U
  let eext := LinearEquiv.ofBijective (exteriorPower.map (p + 1) e.toLinearMap)
    (exteriorPower.map_bijective e.bijective)
  let ecoeff := (chartTrivialization j U hU 2).symm
  let m := (chartSourceEquiv j U hU).symm (Pi.single j (1 : Γ(X, U)))
  have hm : CoefficientKernel.normalizedFunctional ecoeff φ m = 1 := by
    change (chartTrivialization j U hU 2).symm
      ((eulerMap 2).app U ((chartSourceEquiv j U hU).symm (Pi.single j 1))) = 1
    rw [← euler_chart_commutes, LinearEquiv.apply_symm_apply]
    exact normalizedEuler_pivot j U hU
  let esplit := CoefficientKernel.splitExteriorKernelEquiv ecoeff φ m hm p
  let ecycle := cycleSectionsEquiv (I := I) (K := K) p U
  have he : (LinearMap.ker φ).subtype ∘ₗ e.toLinearMap =
      ((kernel.ι (eulerMap (I := I) (K := K) 2)).val.app (op U)).hom := by
    apply LinearMap.ext
    intro x
    exact kernelSectionsEquiv_val (I := I) (K := K) 2 U x
  have hextmap :
      exteriorPower.map (R := Γ(X, U)) (p + 1)
        ((kernel.ι (eulerMap (I := I) (K := K) 2)).val.app (op U)).hom =
      exteriorPower.map (R := Γ(X, U)) (p + 1) (LinearMap.ker φ).subtype ∘ₗ
        exteriorPower.map (R := Γ(X, U)) (p + 1) e.toLinearMap :=
    (congrArg
      (fun f : Γ(B, U) →ₗ[Γ(X, U)] Γ(M, U) =>
        exteriorPower.map (R := Γ(X, U)) (p + 1) f) he).symm.trans
      (exteriorPower.map_comp (R := Γ(X, U)) (n := p + 1)
        e.toLinearMap (LinearMap.ker φ).subtype)
  have hcomp (z : ⋀[Γ(X, U)]^(p + 1) Γ(B, U)) :
      ecycle ((presheafKernelMap (I := I) (K := K) p).app (op U) z) = esplit (eext z) := by
    have hl :
        (ecycle ((presheafKernelMap (I := I) (K := K) p).app (op U) z)).val =
          exteriorPower.map (R := Γ(X, U)) (p + 1)
            ((kernel.ι (eulerMap (I := I) (K := K) 2)).val.app (op U)).hom z :=
      presheafKernelMap_val (I := I) (K := K) p U z
    have hmapped :
        exteriorPower.map (R := Γ(X, U)) (p + 1)
            ((kernel.ι (eulerMap (I := I) (K := K) 2)).val.app (op U)).hom z =
          exteriorPower.map (R := Γ(X, U)) (p + 1)
            (LinearMap.ker φ).subtype (eext z) :=
      LinearMap.congr_fun hextmap z
    have hr : (esplit (eext z)).val =
        exteriorPower.map (R := Γ(X, U)) (p + 1)
          (LinearMap.ker φ).subtype (eext z) :=
      CoefficientKernel.splitExteriorKernelEquiv_val ecoeff φ m hm p (eext z)
    exact Subtype.ext (hl.trans (hmapped.trans hr.symm))
  have hb : Function.Bijective
      (fun z => ecycle ((presheafKernelMap (I := I) (K := K) p).app (op U) z)) := by
    simp_rw [hcomp]
    exact esplit.bijective.comp eext.bijective
  constructor
  · intro x y h
    exact hb.1 (congrArg ecycle h)
  · intro y
    obtain ⟨z, hz⟩ := hb.2 (ecycle y)
    exact ⟨z, ecycle.injective hz⟩

run_cmd do
  (← IO.getStdout).flush
  let out ← IO.getStderr
  out.putStrLn "SEGRE_PROGRESS Stage027.ExteriorComparison after-presheaf-kernel-chart"
  out.flush

instance presheafKernelMap_locallyInjective (p : ℕ) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf (X).ringCatSheaf.obj).map
        (presheafKernelMap (I := I) (K := K) p)) :=
  SheafExteriorKernel.locallyInjective_of_injective_on_cover_subopens
    ((PresheafOfModules.toPresheaf (X).ringCatSheaf.obj).map
      (presheafKernelMap (I := I) (K := K) p))
    (ProjectiveCech.coordinateOpen (I := I) (K := K))
    (ProjectiveCech.coordinate_cover (I := I) (K := K))
    (fun j U hU => (presheafKernelMap_bijective_on_chart p j U hU).1)

instance presheafKernelMap_locallySurjective (p : ℕ) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf (X).ringCatSheaf.obj).map
        (presheafKernelMap (I := I) (K := K) p)) :=
  SheafExteriorKernel.locallySurjective_of_surjective_on_cover_subopens
    ((PresheafOfModules.toPresheaf (X).ringCatSheaf.obj).map
      (presheafKernelMap (I := I) (K := K) p))
    (ProjectiveCech.coordinateOpen (I := I) (K := K))
    (ProjectiveCech.coordinate_cover (I := I) (K := K))
    (fun j U hU => (presheafKernelMap_bijective_on_chart p j U hU).2)

abbrev sheafification : PresheafOfModulesOfCommRing (X).presheaf ⥤ (X).Modules :=
  SchemeTensorPresentation.schemeSheafification X

/-- The existing strong monoidal structure on the actual sheafification functor. -/
local instance sheafificationMonoidal :
    (sheafification (I := I) (K := K)).Monoidal :=
  SchemeTensorPresentation.schemeSheafificationMonoidal X

run_cmd do
  (← IO.getStdout).flush
  let out ← IO.getStderr
  out.putStrLn "SEGRE_PROGRESS Stage027.ExteriorComparison before-sheafified-kernel-is-iso"
  out.flush

instance sheafifiedKernelMap_isIso (p : ℕ) :
    IsIso ((sheafification (I := I) (K := K)).map (presheafKernelMap (I := I) (K := K) p)) := by
  have h : (Opens.grothendieckTopology X).W.inverseImage
      (PresheafOfModules.toPresheaf (X).ringCatSheaf.obj)
      (presheafKernelMap (I := I) (K := K) p) :=
    (Opens.grothendieckTopology X).W_of_isLocallyBijective
      ((PresheafOfModules.toPresheaf (X).ringCatSheaf.obj).map
        (presheafKernelMap (I := I) (K := K) p))
  rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
    (𝟙 (X).ringCatSheaf.obj)] at h
  exact h

run_cmd do
  (← IO.getStdout).flush
  let out ← IO.getStderr
  out.putStrLn "SEGRE_PROGRESS Stage027.ExteriorComparison before-coefficient-target-iso"
  out.flush

/-- The genuine tensor target of the coefficient contraction, with the
canonical strong monoidal comparison made explicit. -/
def coefficientTargetIso (p : ℕ) :
    (sheafification (I := I) (K := K)).obj
        ((PresheafOfModulesOfCommRing.exteriorPower (R := (X).presheaf) p).obj (M).val ⊗
          (L).val) ≅
      (SheafOfModules.exteriorPower (X).sheaf p).obj M ⊗ L :=
  SchemeCoefficientComparison.coefficientTargetIso (Y := X) M L p

run_cmd do
  (← IO.getStdout).flush
  let out ← IO.getStderr
  out.putStrLn "SEGRE_PROGRESS Stage027.ExteriorComparison before-positive-differential"
  out.flush

/-- The actual coefficient-valued exterior contraction on the positive
Euler source, defined by the literal presheaf deletion formula. -/
def differential (p : ℕ) :
    (SheafOfModules.exteriorPower (X).sheaf (p + 1)).obj M ⟶
      (SheafOfModules.exteriorPower (X).sheaf p).obj M ⊗ L :=
  SchemeCoefficientComparison.differential
    (Y := X) M L (eulerMap (I := I) (K := K) 2) p

run_cmd do
  (← IO.getStdout).flush
  let out ← IO.getStderr
  out.putStrLn "SEGRE_PROGRESS Stage027.ExteriorComparison before-positive-exterior-kernel-iso"
  out.flush

/-- The full exterior power of the actual positive Euler kernel is the
kernel of the actual coefficient-valued differential, in every degree. -/
def positiveExteriorKernelIso (p : ℕ) :
    (SheafOfModules.exteriorPower (X).sheaf (p + 1)).obj B ≅
      kernel (differential (I := I) (K := K) p) := by
  let F := sheafification (I := I) (K := K)
  let k := presheafKernelMap (I := I) (K := K) p
  letI : IsIso (F.map k) :=
    sheafifiedKernelMap_isIso (I := I) (K := K) p
  exact (SheafOfModules.exteriorPowerIso (R := (X).sheaf) (p + 1) B) ≪≫
    asIso (F.map k) ≪≫
      SchemeCoefficientComparison.cycleComparisonIso
        (Y := X) M L (eulerMap (I := I) (K := K) 2) p

end PaperVerification.Segre.PositiveExteriorEuler

end SegrePositiveExteriorEuler

section SegrePositiveExteriorComparison

/-!
# The positive Euler kernel uses the genuine coefficient differential

The exterior-kernel construction obtained by exact sheafification and the
coefficient-valued differential obtained by the sheafification adjunction
are identified as actual morphisms. The comparison is the monoidal
adjunction identity for the genuine tensor product, with its source,
target, unit and counit all explicit.

This removes a possible ambiguity between the two constructions: the
resulting kernel isomorphism targets the same canonical differential
whose local formula is the signed coefficient-deletion sum. No
comparison identity is added as a premise.
-/

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

namespace PaperVerification.Segre.PositiveExteriorComparison

open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory
open EulerSheaf EulerCriticalFunctional
open SheafCoefficientContraction
open scoped TensorProduct BigOperators

universe u
variable {I K : Type u} [Fintype I] [DecidableEq I] [Field K]

local notation "𝒜" => MvPolynomial.homogeneousSubmodule I K
local notation "X" => Proj (MvPolynomial.homogeneousSubmodule I K)
local notation "M" => positiveEulerSource (I := I) (K := K)
local notation "L" => Proj.twistingSheaf 𝒜 (2 : ℤ)

run_cmd do
  (← IO.getStdout).flush
  let out ← IO.getStderr
  out.putStrLn "SEGRE_PROGRESS Stage027.ExteriorComparison before-differential-equality"
  out.flush

/-- Equality of the complete actual differentials, not an isomorphism of
abstract kernels or a matching dimension formula. -/
theorem positiveDifferential_eq_contraction (p : ℕ) :
    PositiveExteriorEuler.differential (I := I) (K := K) p =
      contraction (X).sheaf (eulerMap (I := I) (K := K) 2) p := by
  exact SchemeCoefficientComparison.differential_eq_contraction
    (Y := X) M L (eulerMap (I := I) (K := K) 2) p

run_cmd do
  (← IO.getStdout).flush
  let out ← IO.getStderr
  out.putStrLn "SEGRE_PROGRESS Stage027.ExteriorComparison before-canonical-kernel-iso"
  out.flush

/-- Every exterior power of the actual positive Euler kernel is the full
kernel of the canonical coefficient-valued sheaf differential. -/
def positiveExteriorKernelIso (p : ℕ) :
    (SheafOfModules.exteriorPower (X).sheaf (p + 1)).obj
        (eulerKernel (I := I) (K := K) 2) ≅
      kernel (contraction (X).sheaf (eulerMap (I := I) (K := K) 2) p) :=
  PositiveExteriorEuler.positiveExteriorKernelIso p ≪≫
    kernelIsoOfEq (positiveDifferential_eq_contraction p)

run_cmd do
  (← IO.getStdout).flush
  let out ← IO.getStderr
  out.putStrLn "SEGRE_PROGRESS Stage027.ExteriorComparison before-positive-wedge-section"
  out.flush

/-- The differential occurring in that kernel is the full signed
coefficient deletion map on every wedge of actual local sections. -/
theorem positiveDifferential_wedgeSection (p : ℕ) (U : (X).Opens)
    (v : Fin (p + 1) → Γ(M, U)) :
    Scheme.Modules.Hom.app («X» := X)
      (PositiveExteriorEuler.differential (I := I) (K := K) p) U
        (wedgeSection (X).sheaf M (p + 1) (Opposite.op U) v) =
      ∑ i : Fin (p + 1), (-1 : ℤ) ^ (i : ℕ) •
        tensorSection (X).sheaf
          ((SheafOfModules.exteriorPower (X).sheaf p).obj M) L (Opposite.op U)
            (wedgeSection (X).sheaf M p (Opposite.op U) (i.removeNth v))
            ((eulerMap 2).app U (v i)) := by
  rw [positiveDifferential_eq_contraction]
  exact contraction_wedgeSection (X).sheaf (eulerMap 2) p (Opposite.op U) v

end PaperVerification.Segre.PositiveExteriorComparison

end SegrePositiveExteriorComparison

namespace PaperVerification.Segre.KernelIsoTransport

open CategoryTheory Limits

universe v w
variable {C : Type v} [Category.{w} C]

/-- Select the two unchanged degree cases before substituting object families. -/
def natCasesIso (F G : ℕ → C) (e0 : F 0 ≅ G 0)
    (es : ∀ r : ℕ, F (r + 1) ≅ G (r + 1)) (p : ℕ) : F p ≅ G p := by
  cases p with
  | zero => exact e0
  | succ r => exact es r

/-- Transport the same two kernel isomorphisms through the same functor and
commuting square. Every constituent map is the original canonical map. -/
def throughFunctor [HasZeroMorphisms C] [HasKernels C]
    (F : C ⥤ C) [F.PreservesZeroMorphisms]
    {A B M N P Q : C} (f : M ⟶ N) (g : P ⟶ Q)
    [PreservesLimit (parallelPair g 0) F]
    (eA : A ≅ kernel f) (eB : B ≅ kernel g)
    (eM : M ≅ F.obj P) (eN : N ≅ F.obj Q)
    (h : f ≫ eN.hom = eM.hom ≫ F.map g) : A ≅ F.obj B :=
  eA ≪≫ kernel.mapIso f (F.map g) eM eN h ≪≫
    (PreservesKernel.iso F g).symm ≪≫ F.mapIso eB.symm

end PaperVerification.Segre.KernelIsoTransport

namespace PaperVerification.Segre.SchemeKernelIsoTransport

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory

universe u

/-- The canonical kernel transport through an invertible actual sheaf tensor
factor. Its constituent maps are precisely those of `throughFunctor`. -/
def throughTensor {Y : Scheme.{u}} (L : Y.Modules)
    [(tensorRight L).IsEquivalence]
    {A B M N P Q : Y.Modules} (f : M ⟶ N) (g : P ⟶ Q)
    (eA : A ≅ kernel f) (eB : B ≅ kernel g)
    (eM : M ≅ P ⊗ L) (eN : N ≅ Q ⊗ L)
    (h : f ≫ eN.hom = eM.hom ≫ (tensorRight L).map g) :
    A ≅ B ⊗ L := by
  letI : (tensorRight L).PreservesZeroMorphisms := inferInstance
  letI : PreservesLimit (parallelPair g 0) (tensorRight L) := inferInstance
  exact KernelIsoTransport.throughFunctor (C := Y.Modules)
    (tensorRight L) f g eA eB eM eN h

end PaperVerification.Segre.SchemeKernelIsoTransport

namespace PaperVerification.Segre.SchemeExteriorZeroComparison

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

/-- Assemble the unchanged zero-degree comparison before scheme specialization. -/
def throughUnit {Y : Scheme.{u}} (M : Y.Modules) {L Z : Y.Modules}
    (a : (𝟙_ Y.Modules) ≅ L) (b : Z ≅ L) :
    (SheafOfModules.exteriorPower Y.sheaf 0).obj M ≅ Z :=
  (SheafOfModules.exteriorPowerZeroIso Y.sheaf).app M ≪≫ a ≪≫ b.symm

end PaperVerification.Segre.SchemeExteriorZeroComparison

section SegreEulerExteriorTwist

/-!
# Exterior powers of the actual positive Euler kernel

The actual global positive coefficient contraction is intertwined with
the correctly twisted negative Euler contraction. The square is proved
on a basis of all coordinate subopens, using full section-module frames
and the complete signed deletion formulas. Its source and target
isomorphisms were constructed from actual coordinate minors and actual
multiplication of twisting sheaves.

Taking the entire kernels therefore gives
  exteriorPower p (ker(O(1)^I → O(2))) ≅ Ω^p(2p)
in every exterior degree, including zero and degrees above the dimension.
Here Ω^p(2p) is the independently defined actual exterior power of the
ordinary Euler kernel, tensored by the actual twisting sheaf. No exterior
twist identity, kernel comparison, or compatibility square is assumed.

-/

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

namespace PaperVerification.Segre.EulerExteriorTwist

open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory Opposite TopologicalSpace
open EulerSheaf EulerSections ExteriorEuler TwistedExteriorEuler EulerCriticalChart
open ExteriorCoordinateTwist ExteriorCoordinateSections EulerExteriorTwistMaps
open SheafCoefficientContraction SheafCoefficientComplex
open scoped TensorProduct BigOperators

section AbstractScalarDifferential

open TauCeti.SheafOfModules (ringCatSheaf)

universe u
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {R : Sheaf J CommRingCat.{u}}
variable {M : SheafOfModules.{u} (ringCatSheaf R)}

run_cmd do
  (← IO.getStdout).flush
  let out ← IO.getStderr
  out.putStrLn "SEGRE_PROGRESS Stage027.ExteriorComparison before-scalar-exterior-unit"
  out.flush

/-- The scalar differential commutes with the actual exterior sheafification
unit, with both canonical exterior comparison isomorphisms retained. -/
@[reassoc] theorem exteriorUnit_scalarDifferential
    (φ : M ⟶ SheafOfModules.unit (ringCatSheaf R)) (r : ℕ) :
    exteriorUnit R M (r + 1) ≫ (SheafKoszul.differential φ r).val =
      SheafKoszul.presheafDifferential φ r ≫ exteriorUnit R M r := by
  let S := PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)
  let F := SheafOfModules.forget (ringCatSheaf R)
  let A : S ⊣ F := TauCeti.SheafOfModules.sheafificationForgetAdjunction R
  let e₁ := SheafOfModules.exteriorPowerIso (R := R) (r + 1) M
  let e₀ := SheafOfModules.exteriorPowerIso (R := R) r M
  let d := SheafKoszul.presheafDifferential (R := R) φ r
  change (A.unit.app _ ≫ F.map e₁.inv) ≫
      F.map (e₁.hom ≫ S.map d ≫ e₀.inv) =
    d ≫ (A.unit.app _ ≫ F.map e₀.inv)
  rw [Category.assoc, ← F.map_comp, Iso.inv_hom_id_assoc, F.map_comp]
  exact (A.unit.naturality_assoc d (F.map e₀.inv)).symm

end AbstractScalarDifferential


universe u
variable {I K : Type u} [Fintype I] [DecidableEq I] [LinearOrder I] [Field K]

local notation "𝒜" => MvPolynomial.homogeneousSubmodule I K
local notation "X" => Proj (MvPolynomial.homogeneousSubmodule I K)

run_cmd do
  (← IO.getStdout).flush
  let out ← IO.getStderr
  out.putStrLn "SEGRE_PROGRESS Stage027.ExteriorComparison before-coordinate-subopens"
  out.flush

/-- All subopens of all genuine standard coordinate charts. -/
def ChartSubopen := Σ j : I,
  { U : (X).Opens // U ≤ ProjectiveCech.coordinateOpen (K := K) j }

/-- Their underlying opens form a basis of the actual projective topology. -/
theorem coordinateSubopens_isBasis :
    Opens.IsBasis (Set.range (fun p : ChartSubopen (I := I) (K := K) => p.2.val)) := by
  apply Opens.isBasis_iff_nbhd.mpr
  intro U x hxU
  have hx : x ∈ (⨆ j, ProjectiveCech.coordinateOpen (I := I) (K := K) j) := by
    rw [ProjectiveCech.coordinate_cover]
    trivial
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hx
  refine ⟨U ⊓ ProjectiveCech.coordinateOpen (K := K) j,
    ⟨⟨j, ⟨_, inf_le_right⟩⟩, rfl⟩, ⟨hxU, hj⟩, inf_le_left⟩

/-- Equality of actual sheaf morphisms is checked on the complete section
modules of those coordinate subopens. -/
theorem hom_ext_coordinateSubopens {M N : (X).Modules} {f g : M ⟶ N}
    (h : ∀ (j : I) (U : (X).Opens)
      (hU : U ≤ ProjectiveCech.coordinateOpen (K := K) j), f.app U = g.app U) :
    f = g := by
  apply (SheafOfModules.toSheaf (X).ringCatSheaf).map_injective
  apply CategoryTheory.Sheaf.hom_ext
  apply TopCat.Sheaf.hom_ext _ _ (coordinateSubopens_isBasis (I := I) (K := K))
  rintro ⟨j, ⟨U, hU⟩⟩
  ext z
  exact ConcreteCategory.congr_hom (h j U hU) z

run_cmd do
  (← IO.getStdout).flush
  let out ← IO.getStderr
  out.putStrLn "SEGRE_PROGRESS Stage027.ExteriorComparison before-chart-trivialization-zero"
  out.flush

/-- The degree-zero local frame is the independently defined actual
structure-sheaf / O(0) identification. -/
theorem chartTrivialization_zero (j : I) (U : (X).Opens)
    (hU : U ≤ ProjectiveCech.coordinateOpen (K := K) j) :
    chartTrivialization j U hU 0 = Proj.sectionsLinearEquivTwistingSheafZero 𝒜 U := by
  apply LinearEquiv.ext
  intro a
  apply Proj.twistingSheaf.ext
  intro x
  change
    (Proj.twistingSheaf.chartSectionsLinearEquiv 0 (MvPolynomial.X j)
      (MvPolynomial.isHomogeneous_X (R := K) j) U hU a).val x =
    (Proj.sectionsLinearEquivTwistingSheafZero 𝒜 U a).val x
  erw [Proj.twistingSheaf.chartSectionsLinearEquiv_apply_apply,
    Proj.sectionsLinearEquivTwistingSheafZero_apply_apply]
  simp only [Proj.twistingSheaf.chartGenerator_apply, Int.toNat_zero, neg_zero, pow_zero]
  change (a.val x).val * Localization.mk (1 : MvPolynomial I K) 1 = (a.val x).val
  rw [Localization.mk_one_eq_algebraMap, map_one, mul_one]

run_cmd do
  (← IO.getStdout).flush
  let out ← IO.getStderr
  out.putStrLn "SEGRE_PROGRESS Stage027.ExteriorComparison before-normalized-euler-frames"
  out.flush

/-- The actual positive Euler map, in the actual forward frame. -/
theorem positiveEuler_frame (j : I) (U : (X).Opens)
    (hU : U ≤ ProjectiveCech.coordinateOpen (K := K) j) (v : I → Γ(X, U)) :
    (eulerMap (I := I) (K := K) 2).app U
      (ExteriorCoordinateTwist.chartSourceEquiv 1 j U hU v) =
        chartTrivialization j U hU 2 (normalizedEuler j U hU v) := by
  apply (chartTrivialization j U hU 2).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  exact EulerContractionChart.eulerMap_in_frame j U hU 2 v

/-- The actual scalar negative Euler functional has exactly the same
normalized coordinate coefficients. -/
theorem negativeFunctional_frame (j : I) (U : (X).Opens)
    (hU : U ≤ ProjectiveCech.coordinateOpen (K := K) j) (v : I → Γ(X, U)) :
    eulerFunctional (I := I) (K := K) U
      (ExteriorCoordinateTwist.chartSourceEquiv (-1) j U hU v) =
        normalizedEuler j U hU v := by
  have h := EulerContractionChart.eulerMap_in_frame j U hU 0 v
  rw [chartTrivialization_zero] at h
  exact h

run_cmd do
  (← IO.getStdout).flush
  let out ← IO.getStderr
  out.putStrLn "SEGRE_PROGRESS Stage027.ExteriorComparison before-negative-differential-wedge"
  out.flush

/-- The actual scalar sheaf differential has its full sectionwise
deletion formula. The equality follows from naturality of the genuine
sheafification unit. -/
theorem negativeDifferential_wedge (r : ℕ) (U : (X).Opens)
    (v : Fin (r + 1) → Γ(eulerSource (I := I) (K := K), U)) :
    (Scheme.Modules.Hom.app («X» := X)
      (SheafKoszul.differential (R := (X).sheaf) (unitEulerMap (I := I) (K := K)) r) U)
      (wedgeSection (X).sheaf eulerSource (r + 1) (op U) v) =
        ∑ i : Fin (r + 1),
          ((-1 : Γ(X, U)) ^ (i : ℕ) * eulerFunctional U (v i)) •
            wedgeSection (X).sheaf eulerSource r (op U) (i.removeNth v) := by
  have h := exteriorUnit_scalarDifferential
    (R := (X).sheaf) (unitEulerMap (I := I) (K := K)) r
  have hv := congrArg
    (fun f :
      ((PresheafOfModulesOfCommRing.exteriorPower (R := (X).presheaf) (r + 1)).obj
        (eulerSource (I := I) (K := K)).val) ⟶
      ((SheafOfModules.exteriorPower (X).sheaf r).obj
        (eulerSource (I := I) (K := K))).val =>
      (f.app' (op U)).hom (exteriorPower.ιMulti Γ(X, U) (r + 1) v)) h
  change (Scheme.Modules.Hom.app («X» := X)
    (SheafKoszul.differential (R := (X).sheaf) unitEulerMap r) U)
      (wedgeSection (X).sheaf eulerSource (r + 1) (op U) v) =
    (exteriorUnit (X).sheaf eulerSource r).app (op U)
      (TauCeti.koszulDifferential
        (SheafKoszul.sectionFunctional (R := (X).sheaf) unitEulerMap (op U)) r
        (exteriorPower.ιMulti Γ(X, U) (r + 1) v)) at hv
  let E : (⋀[Γ(X, U)]^r Γ(eulerSource (I := I) (K := K), U)) →ₗ[Γ(X, U)]
      Γ((SheafOfModules.exteriorPower (X).sheaf r).obj
        (eulerSource (I := I) (K := K)), U) :=
    ((exteriorUnit (X).sheaf (eulerSource (I := I) (K := K)) r).app' (op U)).hom
  have hφ := congrArg
    (fun φ : Module.Dual Γ(X, U) Γ(eulerSource (I := I) (K := K), U) =>
      TauCeti.koszulDifferential φ r
        (exteriorPower.ιMulti Γ(X, U) (r + 1) v))
    (sectionFunctional_unitEulerMap (I := I) (K := K) U)
  have hδ := TauCeti.koszulDifferential_ιMulti (R := Γ(X, U))
    (eulerFunctional (I := I) (K := K) U) r v
  have hsum :
      E (∑ i : Fin (r + 1),
        ((-1 : Γ(X, U)) ^ (i : ℕ) * eulerFunctional U (v i)) •
          exteriorPower.ιMulti Γ(X, U) r (i.removeNth v)) =
      ∑ i : Fin (r + 1),
        ((-1 : Γ(X, U)) ^ (i : ℕ) * eulerFunctional U (v i)) •
          E (exteriorPower.ιMulti Γ(X, U) r (i.removeNth v)) := by
    simp only [map_sum, _root_.map_smul]
  exact hv.trans ((congrArg E (hφ.trans hδ)).trans hsum)

/-- The negative differential in the complete chart exterior frame. -/
theorem negativeDifferential_frame (r : ℕ) (j : I) (U : (X).Opens)
    (hU : U ≤ ProjectiveCech.coordinateOpen (K := K) j)
    (v : Fin (r + 1) → I → Γ(X, U)) :
    (Scheme.Modules.Hom.app («X» := X)
      (SheafKoszul.differential (R := (X).sheaf) (unitEulerMap (I := I) (K := K)) r) U)
      (framedWedge (-1) (r + 1) j U hU v) =
        ∑ i : Fin (r + 1),
          ((-1 : Γ(X, U)) ^ (i : ℕ) * normalizedEuler j U hU (v i)) •
            framedWedge (-1) r j U hU (i.removeNth v) := by
  let w : Fin (r + 1) → Γ(eulerSource (I := I) (K := K), U) :=
    fun i => ExteriorCoordinateTwist.chartSourceEquiv (-1) j U hU (v i)
  have h := negativeDifferential_wedge (I := I) (K := K) r U w
  refine h.trans ?_
  apply Finset.sum_congr rfl
  intro i _
  have hc := congrArg
    (fun a : Γ(X, U) => (-1 : Γ(X, U)) ^ (i : ℕ) * a)
    (negativeFunctional_frame (I := I) (K := K) j U hU (v i))
  have hw :
      wedgeSection (X).sheaf (eulerSource (I := I) (K := K)) r (op U)
        (i.removeNth w) =
      framedWedge (-1) r j U hU (i.removeNth v) := rfl
  exact congrArg₂
    (fun (a : Γ(X, U))
      (z : Γ((SheafOfModules.exteriorPower (X).sheaf r).obj
        (eulerSource (I := I) (K := K)), U)) => a • z) hc hw

/-- The positive differential in the same complete chart exterior frame. -/
theorem positiveDifferential_frame (r : ℕ) (j : I) (U : (X).Opens)
    (hU : U ≤ ProjectiveCech.coordinateOpen (K := K) j)
    (v : Fin (r + 1) → I → Γ(X, U)) :
    (Scheme.Modules.Hom.app («X» := X)
      (contraction (X).sheaf (eulerMap (I := I) (K := K) 2) r) U)
      (framedWedge 1 (r + 1) j U hU v) =
        ∑ i : Fin (r + 1), (-1 : ℤ) ^ (i : ℕ) •
          framedTensorWedge 1 r 2 j U hU (i.removeNth v)
            (normalizedEuler j U hU (v i)) := by
  let w : Fin (r + 1) → Γ(coordinateSource (I := I) (K := K) 1, U) :=
    fun i => ExteriorCoordinateTwist.chartSourceEquiv 1 j U hU (v i)
  have h := contraction_wedgeSection (X).sheaf
    (M := coordinateSource (I := I) (K := K) 1)
    (L := Proj.twistingSheaf 𝒜 2)
    (eulerMap (I := I) (K := K) 2) r (op U) w
  refine h.trans ?_
  apply Finset.sum_congr rfl
  intro i _
  have ht := congrArg
    (fun a : Γ(Proj.twistingSheaf 𝒜 2, U) =>
      SheafCoefficientContraction.tensorSection (X).sheaf
        (exteriorCoordinates (I := I) (K := K) 1 r)
        (Proj.twistingSheaf 𝒜 2) (op U)
        (framedWedge 1 r j U hU (i.removeNth v)) a)
    (positiveEuler_frame (I := I) (K := K) j U hU (v i))
  exact congrArg
    (fun z : Γ(exteriorCoordinates (I := I) (K := K) 1 r ⊗
      Proj.twistingSheaf 𝒜 2, U) => (-1 : ℤ) ^ (i : ℕ) • z) ht

/-- An arbitrary coefficient in the true line frame is the corresponding
scalar multiple of the generator tensor. -/
theorem framedTensorWedge_scalar (t : ℤ) (r : ℕ) (d : ℤ) (j : I) (U : (X).Opens)
    (hU : U ≤ ProjectiveCech.coordinateOpen (K := K) j)
    (v : Fin r → I → Γ(X, U)) (a : Γ(X, U)) :
    framedTensorWedge t r d j U hU v a =
      a • framedTensorWedge t r d j U hU v 1 := by
  have ha : chartTrivialization j U hU d a =
      a • chartTrivialization j U hU d 1 := by
    rw [← _root_.map_smul, smul_eq_mul, mul_one]
  exact (congrArg
    (fun l : Γ(Proj.twistingSheaf 𝒜 d, U) =>
      SheafCoefficientContraction.tensorSection (X).sheaf
        (exteriorCoordinates (I := I) (K := K) t r)
        (Proj.twistingSheaf 𝒜 d) (op U)
        (framedWedge t r j U hU v) l) ha).trans
      (SchemeTensorPresentation.tensorSection_smul_right (Y := X) U a
        (framedWedge t r j U hU v) (chartTrivialization j U hU d 1))

run_cmd do
  (← IO.getStdout).flush
  let out ← IO.getStderr
  out.putStrLn "SEGRE_PROGRESS Stage027.ExteriorComparison before-twisted-negative-frame"
  out.flush

/-- The actual twist functor preserves the complete negative differential
formula on the genuine generator tensors. -/
theorem twistedNegativeDifferential_frame (r : ℕ) (d : ℤ) (j : I) (U : (X).Opens)
    (hU : U ≤ ProjectiveCech.coordinateOpen (K := K) j)
    (v : Fin (r + 1) → I → Γ(X, U)) :
    ((twistFunctor d).map
      (SheafKoszul.differential (R := (X).sheaf) (unitEulerMap (I := I) (K := K)) r)).app U
        (framedTensorWedge (-1) (r + 1) d j U hU v 1) =
      ∑ i : Fin (r + 1),
        ((-1 : Γ(X, U)) ^ (i : ℕ) * normalizedEuler j U hU (v i)) •
          framedTensorWedge (-1) r d j U hU (i.removeNth v) 1 := by
  let t : Γ(Proj.twistingSheaf 𝒜 d, U) := chartTrivialization j U hU d 1
  have hm := SchemeTensorPresentation.tensorRight_map_tensorSection
    (Y := X)
    (M := exteriorCoordinates (I := I) (K := K) (-1) (r + 1))
    (A := exteriorCoordinates (I := I) (K := K) (-1) r)
    (L := Proj.twistingSheaf 𝒜 d)
    (SheafKoszul.differential (R := (X).sheaf)
      (unitEulerMap (I := I) (K := K)) r) U
    (framedWedge (-1) (r + 1) j U hU v) t
  have hd := congrArg
    (fun z : Γ(exteriorCoordinates (I := I) (K := K) (-1) r, U) =>
      SheafCoefficientContraction.tensorSection (X).sheaf
        (exteriorCoordinates (I := I) (K := K) (-1) r)
        (Proj.twistingSheaf 𝒜 d) (op U) z t)
    (negativeDifferential_frame (I := I) (K := K) r j U hU v)
  have hs := SchemeTensorPresentation.tensorSection_sum_smul_left
    (Y := X)
    (M := exteriorCoordinates (I := I) (K := K) (-1) r)
    (N := Proj.twistingSheaf 𝒜 d) U
    (fun i : Fin (r + 1) =>
      (-1 : Γ(X, U)) ^ (i : ℕ) * normalizedEuler j U hU (v i))
    (fun i : Fin (r + 1) => framedWedge (-1) r j U hU (i.removeNth v)) t
  exact hm.trans (hd.trans hs)

run_cmd do
  (← IO.getStdout).flush
  let out ← IO.getStderr
  out.putStrLn "SEGRE_PROGRESS Stage027.ExteriorComparison before-contraction-square"
  out.flush

/-- Equality of the actual global positive contraction and the actual
twisted negative contraction, through the independently constructed
global source and target isomorphisms. -/
theorem contraction_comparison_square (r : ℕ) :
    contraction (X).sheaf (eulerMap (I := I) (K := K) 2) r ≫
        (targetComparison r).hom =
      (sourceComparison (r + 1)).hom ≫
        (twistFunctor (2 * ((r + 1 : ℕ) : ℤ))).map
          (SheafKoszul.differential (R := (X).sheaf) unitEulerMap r) := by
  apply hom_ext_coordinateSubopens
  intro j U hU
  let E := actualExteriorFrame (I := I) (K := K) 1 (r + 1) j U hU
  suffices h :
      (((contraction (X).sheaf (eulerMap 2) r ≫ (targetComparison r).hom).val.app (op U)).hom ∘ₗ
        E.toLinearMap) =
      ((((sourceComparison (r + 1)).hom ≫
        (twistFunctor (2 * ((r + 1 : ℕ) : ℤ))).map
          (SheafKoszul.differential (R := (X).sheaf) unitEulerMap r)).val.app (op U)).hom ∘ₗ E.toLinearMap) by
    apply ConcreteCategory.hom_ext
    intro z
    obtain ⟨w, rfl⟩ := E.surjective z
    exact LinearMap.congr_fun h w
  apply exteriorPower.linearMap_ext (R := Γ(X, U)) (n := r + 1)
  apply AlternatingMap.ext
  intro v
  change (targetComparison r).hom.app U
      ((Scheme.Modules.Hom.app («X» := X)
        (contraction (X).sheaf (eulerMap 2) r) U)
        (E (exteriorPower.ιMulti Γ(X, U) (r + 1) v))) =
    ((twistFunctor (2 * ((r + 1 : ℕ) : ℤ))).map
      (SheafKoszul.differential (R := (X).sheaf) unitEulerMap r)).app U
        ((sourceComparison (r + 1)).hom.app U
          (E (exteriorPower.ιMulti Γ(X, U) (r + 1) v)))
  have hE : E (exteriorPower.ιMulti Γ(X, U) (r + 1) v) =
      framedWedge 1 (r + 1) j U hU v :=
    actualExteriorFrame_ιMulti 1 (r + 1) j U hU v
  rw [hE, positiveDifferential_frame, sourceComparison_frame,
    twistedNegativeDifferential_frame]
  simp only [map_sum, map_zsmul, targetComparison_frame]
  apply Finset.sum_congr rfl
  intro i _
  rw [framedTensorWedge_scalar, ← Int.cast_smul_eq_zsmul Γ(X, U),
    Int.cast_pow, Int.cast_neg, Int.cast_one, smul_smul]

run_cmd do
  (← IO.getStdout).flush
  let out ← IO.getStderr
  out.putStrLn "SEGRE_PROGRESS Stage027.ExteriorComparison before-positive-twist-iso"
  out.flush

run_cmd do
  (← IO.getStdout).flush
  let out ← IO.getStderr
  out.putStrLn "SEGRE_PROGRESS Stage027.ExteriorComparison before-positive-twist-zero"
  out.flush

/-- The degree-zero exterior comparison, obtained from the tensor unit. -/
def positiveExteriorTwistZeroIso :
    (SheafOfModules.exteriorPower (X).sheaf 0).obj
        (eulerKernel (I := I) (K := K) 2) ≅
      exteriorKernelTwist 0 (2 * (0 : ℤ)) :=
  SchemeExteriorZeroComparison.throughUnit (Y := X)
    (eulerKernel (I := I) (K := K) 2)
    (Proj.unitIsoTwistingSheafZero 𝒜)
    (exteriorKernelTwistZeroIso (I := I) (K := K) 0)

run_cmd do
  (← IO.getStdout).flush
  let out ← IO.getStderr
  out.putStrLn "SEGRE_PROGRESS Stage027.ExteriorComparison before-positive-twist-successor"
  out.flush

/-- The positive-degree comparison induced by the commuting contraction square. -/
def positiveExteriorTwistSuccIso (r : ℕ) :
    (SheafOfModules.exteriorPower (X).sheaf (r + 1)).obj
        (eulerKernel (I := I) (K := K) 2) ≅
      exteriorKernelTwist (I := I) (K := K) (r + 1) (2 * ((r + 1 : ℕ) : ℤ)) :=
  SchemeKernelIsoTransport.throughTensor (Y := X)
    (Proj.twistingSheaf 𝒜 (2 * ((r + 1 : ℕ) : ℤ)))
    (contraction (X).sheaf (eulerMap (I := I) (K := K) 2) r)
    (SheafKoszul.differential (R := (X).sheaf) (unitEulerMap (I := I) (K := K)) r)
    (PositiveExteriorComparison.positiveExteriorKernelIso (I := I) (K := K) r)
    (exteriorEulerKernelIso (I := I) (K := K) r)
    (sourceComparison (I := I) (K := K) (r + 1))
    (targetComparison (I := I) (K := K) r)
    (contraction_comparison_square (I := I) (K := K) r)

run_cmd do
  (← IO.getStdout).flush
  let out ← IO.getStderr
  out.putStrLn "SEGRE_PROGRESS Stage027.ExteriorComparison before-positive-twist-assembly"
  out.flush

/-- The positive Euler-kernel exterior power is the actual ordinary Euler
exterior power twisted by twice its exterior degree. -/
def positiveExteriorTwistIso (p : ℕ) :
    (SheafOfModules.exteriorPower (X).sheaf p).obj
        (eulerKernel (I := I) (K := K) 2) ≅
      exteriorKernelTwist p (2 * (p : ℤ)) :=
  KernelIsoTransport.natCasesIso
    (fun n => (SheafOfModules.exteriorPower (X).sheaf n).obj
      (eulerKernel (I := I) (K := K) 2))
    (fun n => exteriorKernelTwist (I := I) (K := K) n (2 * (n : ℤ)))
    (positiveExteriorTwistZeroIso (I := I) (K := K))
    (fun r => positiveExteriorTwistSuccIso (I := I) (K := K) r) p

run_cmd do
  (← IO.getStdout).flush
  let out ← IO.getStderr
  out.putStrLn "SEGRE_PROGRESS Stage027.ExteriorComparison before-positive-additional-twist"
  out.flush

/-- Every additional integer twist is included by actual associativity
and multiplication of twisting sheaves. This is the factor needed in the
full graph and balanced Koszul terms. -/
def positiveExteriorAdditionalTwistIso (p : ℕ) (d : ℤ) :
    (SheafOfModules.exteriorPower (X).sheaf p).obj
        (eulerKernel (I := I) (K := K) 2) ⊗ Proj.twistingSheaf 𝒜 d ≅
      exteriorKernelTwist p (2 * (p : ℤ) + d) :=
  (positiveExteriorTwistIso p ⊗ᵢ Iso.refl _) ≪≫
    (α_ ((SheafOfModules.exteriorPower (X).sheaf p).obj (eulerKernel 0))
      (Proj.twistingSheaf 𝒜 (2 * (p : ℤ))) (Proj.twistingSheaf 𝒜 d)) ≪≫
    (Iso.refl _ ⊗ᵢ twistingTensorIso (2 * (p : ℤ)) d)

end PaperVerification.Segre.EulerExteriorTwist

end SegreEulerExteriorTwist

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
