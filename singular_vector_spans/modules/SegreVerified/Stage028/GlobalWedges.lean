module
public import SegreVerified.Stage028.LineSections
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
set_option maxHeartbeats 2000000
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


section SegreGlobalCriticalSections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

run_cmd do
  let out ← IO.getStderr
  out.putStrLn "SEGRE_STAGE Stage028.GlobalWedges"
  out.flush

/-!
# Global critical sections and their literal chart equations

The named sections preserve the original proof stages and local scopes.
-/


section SegreTensorSingleFactor

/-!
# A finite tensor with one nonunit factor

The isomorphism is constructed from the actual factor unit isomorphisms and
the actual associatively ordered finite tensor. Both algebraic pure tensors
and sheaf pure sections retain their precise selected-factor formula.
-/

set_option autoImplicit false

namespace PaperVerification.Segre.TensorSingleFactor

open CategoryTheory MonoidalCategory
open FixedProductProjections FiniteTensorSections SheafCoefficientContraction
open TauCeti.SheafOfModules (ringCatSheaf)
open scoped TensorProduct

universe u v

section Category

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The actual finite tensor of unit objects is the unit; no braiding is
needed because the selected factor retains its original position. -/
def unitsIso : {l : ℕ} → (M : Fin l → C) → (∀ i,M i ≅ 𝟙_ C) →
    (FiniteTensor.tensorObj M ≅ 𝟙_ C)
  | 0,_,_ => Iso.refl _
  | l+1,M,e => (e 0 ⊗ᵢ unitsIso (fun i : Fin l => M i.succ) (fun i => e i.succ)) ≪≫ λ_ _

/-- Keep exactly one specified factor and collapse every other factor by
its supplied actual unit isomorphism. -/
def singleIso : {l : ℕ} → (M : Fin l → C) → (i : Fin l) →
    (∀ j,j≠i → (M j ≅ 𝟙_ C)) → (FiniteTensor.tensorObj M ≅ M i)
  | 0,_,i,_ => Fin.elim0 i
  | l+1,M,i,e => Fin.cases
      (fun e => (Iso.refl _ ⊗ᵢ unitsIso (fun j : Fin l => M j.succ)
        (fun j => e j.succ (Fin.succ_ne_zero j))) ≪≫ ρ_ _)
      (fun j e => (e 0 (Ne.symm (Fin.succ_ne_zero j)) ⊗ᵢ
        singleIso (fun h : Fin l => M h.succ) j
          (fun h hh => e h.succ (fun he => hh (Fin.succ_inj.mp he)))) ≪≫ λ_ _)
      i e

end Category

section Modules

variable {K : Type u} [CommRing K]

theorem unitsIso_pure {l : ℕ} (M : Fin l → ModuleCat.{u} K)
    (e : ∀ i,M i ≅ 𝟙_ (ModuleCat.{u} K)) (s : ∀ i,M i)
    (hs : ∀ i,(e i).hom (s i)=1) :
    (unitsIso M e).hom (FiniteTensorLinear.pure M s)=1 := by
  induction l with
  | zero => rfl
  | succ l ih =>
      change (e 0).hom (s 0) •
        (unitsIso (fun j : Fin l => M j.succ) (fun j => e j.succ)).hom
          (FiniteTensorLinear.pure (fun j => M j.succ) (fun j => s j.succ)) = 1
      rw [hs 0, ih _ _ _ (fun j => hs j.succ), one_smul]

theorem singleIso_pure {l : ℕ} (M : Fin l → ModuleCat.{u} K) (i : Fin l)
    (e : ∀ j,j≠i → (M j ≅ 𝟙_ (ModuleCat.{u} K))) (s : ∀ j,M j)
    (hs : ∀ j (h : j≠i),(e j h).hom (s j)=1) :
    (singleIso M i e).hom (FiniteTensorLinear.pure M s)=s i := by
  induction l with
  | zero => exact Fin.elim0 i
  | succ l ih =>
      induction i using Fin.cases with
      | zero =>
          change (unitsIso (fun j : Fin l => M j.succ)
            (fun j => e j.succ (Fin.succ_ne_zero j))).hom
              (FiniteTensorLinear.pure (fun j => M j.succ) (fun j => s j.succ)) • s 0 = s 0
          rw [unitsIso_pure _ _ _ (fun j => hs j.succ (Fin.succ_ne_zero j)), one_smul]
      | succ i =>
          change (e 0 (Ne.symm (Fin.succ_ne_zero i))).hom (s 0) •
            (singleIso (fun j : Fin l => M j.succ) i
              (fun j hj => e j.succ (fun he => hj (Fin.succ_inj.mp he)))).hom
              (FiniteTensorLinear.pure (fun j => M j.succ) (fun j => s j.succ)) = s i.succ
          rw [hs, ih _ _ _ _ (fun j hj => hs j.succ
            (fun he => hj (Fin.succ_inj.mp he))), one_smul]

end Modules

section Sheaves

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (R : Sheaf J CommRingCat.{u})
set_option hygiene false in
set_option quotPrecheck false in local notation "Sh" => SheafOfModules.{u} (ringCatSheaf R)

theorem unitsIso_section {l : ℕ} (M : Fin l → Sh)
    (e : ∀ i,M i ≅ 𝟙_ Sh) (U : Cᵒᵖ) (s : ∀ i,(M i).val.obj U)
    (hs : ∀ i,(e i).hom.val.app U (s i)=(1 : R.obj.obj U)) :
    (unitsIso M e).hom.val.app U (finiteTensorSection R M U s)=(1 : R.obj.obj U) := by
  induction l with
  | zero => rfl
  | succ l ih =>
      with_unfolding_all simp only [unitsIso,finiteTensorSection,Iso.trans_hom,tensorIso_hom,
        SheafOfModules.comp_val,PresheafOfModules.comp_app,ConcreteCategory.comp_apply,
        SheafCoefficientComplex.tensorSection_map,hs,ih,
        tensorSection_leftUnitor,one_smul]
      erw [SheafCoefficientComplex.tensorSection_map R]
      rw [hs, ih _ _ _ (fun i => hs i.succ)]
      exact (tensorSection_leftUnitor R (𝟙_ Sh) U (1 : R.obj.obj U) (1 : R.obj.obj U)).trans (one_smul _ _)

theorem singleIso_section {l : ℕ} (M : Fin l → Sh) (i : Fin l)
    (e : ∀ j,j≠i → (M j ≅ 𝟙_ Sh)) (U : Cᵒᵖ) (s : ∀ j,(M j).val.obj U)
    (hs : ∀ j (h : j≠i),(e j h).hom.val.app U (s j)=(1 : R.obj.obj U)) :
    (singleIso M i e).hom.val.app U (finiteTensorSection R M U s)=s i := by
  induction l with
  | zero => exact Fin.elim0 i
  | succ l ih =>
      induction i using Fin.cases with
      | zero =>
          with_unfolding_all simp only [singleIso,Fin.cases_zero,finiteTensorSection,Iso.trans_hom,
            tensorIso_hom,SheafOfModules.comp_val,PresheafOfModules.comp_app,ConcreteCategory.comp_apply,
            SheafCoefficientComplex.tensorSection_map,Iso.refl_hom,
            SheafOfModules.id_val,PresheafOfModules.id_app,ConcreteCategory.id_apply,
            unitsIso_section R _ _ _ _ (fun j => hs j.succ (Fin.succ_ne_zero j)),
            tensorSection_rightUnitor,one_smul]
          erw [SheafCoefficientComplex.tensorSection_map R]
          simp only [SheafOfModules.id_val, PresheafOfModules.id_app, ConcreteCategory.id_apply]
          rw [unitsIso_section R _ _ _ _ (fun j => hs j.succ (Fin.succ_ne_zero j))]
          exact (tensorSection_rightUnitor R (M 0) U (s 0) (1 : R.obj.obj U)).trans
            (one_smul _ _)
      | succ i =>
          with_unfolding_all simp only [singleIso,Fin.cases_succ,finiteTensorSection,Iso.trans_hom,
            tensorIso_hom,SheafOfModules.comp_val,PresheafOfModules.comp_app,ConcreteCategory.comp_apply,
            SheafCoefficientComplex.tensorSection_map,hs,
            ih _ _ _ _ (fun j hj => hs j.succ
              (fun he => hj (Fin.succ_inj.mp he))),
            tensorSection_leftUnitor,one_smul]
          erw [SheafCoefficientComplex.tensorSection_map R]
          rw [hs, ih _ _ _ _ (fun j hj => hs j.succ
            (fun he => hj (Fin.succ_inj.mp he)))]
          exact (tensorSection_leftUnitor R (M i.succ) U (1 : R.obj.obj U) (s i.succ)).trans
            (one_smul _ _)

end Sheaves

end PaperVerification.Segre.TensorSingleFactor

end SegreTensorSingleFactor

section SegreSingleFactorGlobalSections

/-!
# Global sections of a single projection pullback

The full finite external-product H⁰ theorem specializes to one arbitrary
factor and structure sheaves on every other projective factor. The resulting
linear equivalence is proved to be the actual pullback of global sections.
No connectedness, chosen H⁰ comparison, or dimension equality is assumed.

-/


attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

namespace PaperVerification.Segre.SingleFactorGlobalSections


open CategoryTheory Limits MonoidalCategory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open FixedProductCohomology FixedProductProjections FinitePullbackSections
open ExternalSections TensorSingleFactor PullbackTensorSections
open scoped TensorProduct

universe u
variable {K : Type u} [Field K]

section ProjectiveFunctions

variable (J : Type u) [Fintype J] [DecidableEq J] [Nonempty J]

/-- Degree-zero homogeneous polynomials are exactly the constants, with
the actual coefficient map as inverse. -/
def constantHomogeneousEquiv : K ≃ₗ[K] MvPolynomial.homogeneousSubmodule J K 0 where
  toFun c := ⟨MvPolynomial.C c,MvPolynomial.isHomogeneous_C J c⟩
  invFun p := MvPolynomial.constantCoeff p.val
  left_inv c := MvPolynomial.constantCoeff_C J c
  right_inv p := Subtype.ext ((MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp
    ((MvPolynomial.totalDegree_zero_iff_isHomogeneous J).mpr p.property)).symm
  map_add' c d := Subtype.ext (map_add MvPolynomial.C c d)
  map_smul' c d := Subtype.ext (by
    change MvPolynomial.C (c*d)=c • MvPolynomial.C d
    simp only [map_mul,Algebra.smul_def,MvPolynomial.algebraMap_eq])

set_option quotPrecheck false in local notation "Y" => (ProductKoszulVanishing.projectiveScheme K J).scheme

/-- The genuine global functions of projective space are the coefficient
field, through the degree-zero homogeneous section map. -/
def projectiveFunctionsFrame : sections K (𝟙_ (Y).Modules) ⊤ ≃ₗ[K] K :=
  ((((sectionsBasePresheafFunctor K).mapIso
      (Proj.unitIsoTwistingSheafZero (MvPolynomial.homogeneousSubmodule J K))).app
      (op ⊤)).toLinearEquiv).trans
    ((GlobalSectionsScalarComparison.identityEquiv K
      (Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule J K) 0)).symm.trans
      ((ProjectiveGlobalSections.homogeneousGlobalSectionsLinearEquiv
        (I := J) (K := K) 0).symm.trans
        (constantHomogeneousEquiv (K := K) J).symm))

/-- The field coordinate retains the actual unit section. -/
theorem projectiveFunctionsFrame_one :
    projectiveFunctionsFrame (K := K) J (1 : Γ(Y,⊤))=1 := by
  change (constantHomogeneousEquiv (K := K) J).symm
    ((ProjectiveGlobalSections.homogeneousGlobalSectionsLinearEquiv 0).symm
      ((Proj.unitIsoTwistingSheafZero
        (MvPolynomial.homogeneousSubmodule J K)).hom.val.app (op ⊤) (1 : Γ(Y,⊤))))=1
  apply (constantHomogeneousEquiv (K := K) J).injective
  rw [LinearEquiv.apply_symm_apply]
  apply (ProjectiveGlobalSections.homogeneousGlobalSectionsLinearEquiv 0).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Proj.twistingSheaf.ext
  intro x
  simp only [Proj.unitIsoTwistingSheafZero_hom_app_apply,
    Proj.sectionsLinearEquivTwistingSheafZero_apply_apply,
    ProjectiveGlobalSections.homogeneousGlobalSectionsLinearEquiv_apply,
    Proj.toTwistingSheaf_apply_apply,constantHomogeneousEquiv,
    Localization.mk_one_eq_algebraMap,map_one]
  rfl

end ProjectiveFunctions

section OneFactor

variable {l : ℕ} (A : Fin (l+1) → CoveredScheme K)
variable (M : ∀ i,(A i).scheme.Modules) (hM : ∀ i,(M i).IsQuasicoherent)
variable (i : Fin (l+1)) (e : ∀ j,j≠i → (M j ≅ 𝟙_ (A j).scheme.Modules))
variable (c : ∀ j,sections K (𝟙_ (A j).scheme.Modules) ⊤ ≃ₗ[K] K)
variable (hc : ∀ j,c j (1 : Γ((A j).scheme,⊤))=1)

set_option quotPrecheck false in local notation "X" => (CoveredScheme.finiteProduct A).scheme

/-- The actual unit identifications on the global section factors. -/
def algebraUnitIso (j : Fin (l+1)) (h : j≠i) :
    sections K (M j) ⊤ ≅ 𝟙_ (ModuleCat.{u} K) :=
  (((sectionsBasePresheafFunctor K).mapIso (e j h)).app (op ⊤)) ≪≫ (c j).toModuleIso

/-- The actual unit identifications after projection pullback. -/
def geometricUnitIso (j : Fin (l+1)) (h : j≠i) :
    (Scheme.Modules.pullback (projection A j)).obj (M j) ≅ 𝟙_ (X).Modules :=
  (Scheme.Modules.pullback (projection A j)).mapIso (e j h) ≪≫ pullbackObjUnitIso (projection A j)

/-- The complete H⁰ comparison for one arbitrary factor, constructed from
the full external-product theorem and actual unit isomorphisms. -/
def oneFactorSectionsEquiv :
    sections K (M i) ⊤ ≃ₗ[K] sections K ((Scheme.Modules.pullback (projection A i)).obj (M i)) ⊤ :=
  ((singleIso (fun j => sections K (M j) ⊤) i (algebraUnitIso A M i e c)).symm ≪≫
    finitePullbackGlobalSectionsIso A M hM ≪≫
    (((sectionsBasePresheafFunctor K).mapIso
      (singleIso (fun j => (Scheme.Modules.pullback (projection A j)).obj (M j)) i
        (geometricUnitIso A M i e))).app (op ⊤))).toLinearEquiv

include hc in
/-- The comparison is the literal pullback map on every global section.
The arbitrary choices in irrelevant tensor factors cancel through their
actual unit isomorphisms. -/
theorem oneFactorSectionsEquiv_apply (s : sections K (M i) ⊤) :
    oneFactorSectionsEquiv A M hM i e c s=
      (projection A i).pullbackSectionsLE (M i) ⊤ ⊤ (by simp) s := by
  let t : ∀ j,sections K (M j) ⊤ := Function.update
    (fun j => if h : j≠i then (algebraUnitIso A M i e c j h).inv 1 else 0) i s
  have hti : t i=s := by simp only [t, Function.update_self]
  have ht (j : Fin (l+1)) (h : j≠i) :
      (algebraUnitIso A M i e c j h).hom (t j)=1 := by
    simp only [t,Function.update_of_ne h,dif_pos h]
    exact ConcreteCategory.congr_hom (algebraUnitIso A M i e c j h).inv_hom_id 1
  have hs : (singleIso (fun j => sections K (M j) ⊤) i
      (algebraUnitIso A M i e c)).inv s=
        FiniteTensorLinear.pure (fun j => sections K (M j) ⊤) t := by
    have he := singleIso_pure (fun j => sections K (M j) ⊤) i
      (algebraUnitIso A M i e c) t ht
    rw [hti] at he
    rw [← he]
    exact ConcreteCategory.congr_hom
      (singleIso (fun j => sections K (M j) ⊤) i
        (algebraUnitIso A M i e c)).hom_inv_id _
  have hgeom (j : Fin (l+1)) (h : j≠i) :
      (geometricUnitIso A M i e j h).hom.app ⊤
        ((projection A j).pullbackSectionsLE (M j) ⊤ ⊤ (by simp) (t j))=(1 : Γ(X,⊤)) := by
    have hj : (e j h).hom.app ⊤ (t j)=(1 : Γ((A j).scheme,⊤)) := by
      apply (c j).injective
      rw [hc j]
      exact ht j h
    simp only [geometricUnitIso,Iso.trans_hom,Functor.mapIso_hom,
      Scheme.Modules.Hom.comp_app,ConcreteCategory.comp_apply]
    rw [Scheme.Hom.pullbackSectionsLE_naturality,hj,pullbackUnit_sectionLE,map_one]
  dsimp only [oneFactorSectionsEquiv]
  rw [Iso.toLinearEquiv_apply,Iso.trans_hom,Iso.trans_hom,ModuleCat.comp_apply,
    ModuleCat.comp_apply,Iso.symm_hom,hs,finitePullbackGlobalSectionsIso_pure]
  change (singleIso _ i (geometricUnitIso A M i e)).hom.val.app (op ⊤)
    (FiniteTensorSections.finiteTensorSection (X).sheaf _ (op ⊤)
      (fun j => (projection A j).pullbackSectionsLE (M j) ⊤ ⊤ (by simp) (t j)))=_
  rw [singleIso_section (X).sheaf _ i _ (op ⊤) _ hgeom,hti]

include hM e c hc in
/-- Every global section of the actual projection pullback is the pullback
of an actual global section of the selected original factor. -/
theorem projectionPullback_surjective :
    Function.Surjective ((projection A i).pullbackSectionsLE (M i) ⊤ ⊤ (by simp)) := by
  intro z
  obtain ⟨s,hs⟩ := (oneFactorSectionsEquiv A M hM i e c).surjective z
  exact ⟨s,(oneFactorSectionsEquiv_apply A M hM i e c hc s).symm.trans hs⟩

end OneFactor

section ProjectiveFactor

variable {l : ℕ} (J : Fin (l+1) → Type u)
variable [∀ j,Fintype (J j)] [∀ j,DecidableEq (J j)] [∀ j,Nonempty (J j)]
local notation "A" => (fun j => ProductKoszulVanishing.projectiveScheme K (J j))

/-- The complete single-factor pullback theorem for actual projective
products and every quasicoherent sheaf on the selected factor. -/
theorem projective_projectionPullback_surjective (i : Fin (l+1))
    (N : (A i).scheme.Modules) [N.IsQuasicoherent] :
    Function.Surjective ((projection A i).pullbackSectionsLE N ⊤ ⊤ (by simp)) := by
  let M : ∀ j,(A j).scheme.Modules := Function.update (fun j => 𝟙_ (A j).scheme.Modules) i N
  have hM : ∀ j,(M j).IsQuasicoherent := by
    intro j
    by_cases h : j=i
    · subst j
      simpa only [M,Function.update_self] using (inferInstance : N.IsQuasicoherent)
    · simp only [M,Function.update_of_ne h]
      infer_instance
  let e : ∀ j,j≠i → (M j ≅ 𝟙_ (A j).scheme.Modules) :=
    fun j h => eqToIso (Function.update_of_ne h N (fun j => 𝟙_ (A j).scheme.Modules))
  have h := projectionPullback_surjective A M hM i e
    (fun j => projectiveFunctionsFrame (K := K) (J j))
    (fun j => projectiveFunctionsFrame_one (K := K) (J j))
  have hMi : M i = N := by
    dsimp only [M]
    exact @Function.update_self (Fin (l+1)) (fun j => (A j).scheme.Modules)
      _ i N (fun j => 𝟙_ (A j).scheme.Modules)
  rw (config := { transparency := .all }) [hMi] at h
  exact h

end ProjectiveFactor

end PaperVerification.Segre.SingleFactorGlobalSections

end SegreSingleFactorGlobalSections

section SegreGlobalEulerWedges

/-!
# The actual coordinate wedges span every global Euler-kernel section

The complete homogeneous-polynomial kernel comparison identifies the actual
Euler-kernel section space with alternating coefficient matrices. Strict
upper entries give its coordinates, and the inverse coordinate vectors are
the literal global sections x_q e_p-x_p e_q. This includes dimension-zero
projective spaces and fields of characteristic two.

-/


attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

namespace PaperVerification.Segre.GlobalEulerWedges

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open EulerSheaf EulerSections EulerCriticalFunctional ActualQuadraticEuler
open QuadraticEuler ProjectiveGlobalSections
open scoped BigOperators

universe u
variable {I K : Type u} [Fintype I] [DecidableEq I] [Field K] [Nonempty I]

local notation "𝒜" => MvPolynomial.homogeneousSubmodule I K
local notation "X" => Proj (MvPolynomial.homogeneousSubmodule I K)

local instance globalFunctionsAlgebra : Algebra K Γ(X,⊤) :=
  (Scheme.Modules.baseRingToGlobalSections K X).toAlgebra

local instance globalSectionsTower (M : (X).Modules) : IsScalarTower K Γ(X,⊤) Γ(M,⊤) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

/-- The actual degree-one section equivalence sends the literal coordinate
section back to the literal coordinate polynomial. -/
theorem coordinateSection_polynomial (a : I) :
    (homogeneousGlobalSectionsLinearEquiv (I := I) (K := K) 1).symm
      (coordinateSection a ⊤)=⟨MvPolynomial.X a,MvPolynomial.isHomogeneous_X (R := K) a⟩ := by
  apply (homogeneousGlobalSectionsLinearEquiv (I := I) (K := K) 1).injective
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The alternating coefficient matrix is computed by the actual global
Euler source and the actual polynomial coefficient functions. -/
theorem alternating_coeff (s : Γ(eulerKernel (I := I) (K := K) 2,⊤)) (i j : I) :
    ((alternatingGlobalKernelEquiv (I := I) (K := K)).symm s).val i j=
      (((homogeneousGlobalSectionsLinearEquiv (I := I) (K := K) 1).symm
        (productSectionsEquiv (fun _ : I => Proj.twistingSheaf 𝒜 1) ⊤
          ((kernel.ι (eulerMap 2)).app ⊤ s) i)).val).coeff (Finsupp.single j 1) := by
  let A := (alternatingGlobalKernelEquiv (I := I) (K := K)).symm s
  have he : actualPolynomialKernelEquiv (kernelGlobalEquiv s)=alternatingKernelEquiv A := by
    have h := (alternatingGlobalKernelEquiv (I := I) (K := K)).apply_symm_apply s
    change kernelGlobalEquiv.symm (actualPolynomialKernelEquiv.symm
      (alternatingKernelEquiv A)) = s at h
    have hh := congrArg (fun z => actualPolynomialKernelEquiv (kernelGlobalEquiv z)) h
    simpa only [LinearEquiv.apply_symm_apply] using hh.symm
  have hp := congrArg (fun z : LinearMap.ker (polynomialEuler (I := I) (K := K)) =>
    (z.val i).val.coeff (Finsupp.single j 1)) he
  have hcoeff : ((alternatingKernelEquiv A).val i).val.coeff
      (Finsupp.single j 1) = A.val i j := linearForm_coeff (A.val i) j
  rw [hcoeff] at hp
  change (sourceGlobalEquiv (kernelGlobalEquiv s).val i).val.coeff
    (Finsupp.single j 1) = A.val i j at hp
  have hv : (kernelGlobalEquiv s).val = (kernel.ι (eulerMap 2)).app ⊤ s :=
    kernelSectionsEquiv_val 2 ⊤ s
  rw [hv] at hp
  exact hp.symm

/-- Every entry of the actual wedge's coefficient matrix, with the exact
orientation used by the critical functional. -/
theorem coordinateWedge_coeff (p q i j : I) :
    ((alternatingGlobalKernelEquiv (I := I) (K := K)).symm (coordinateWedge (K := K) p q ⊤)).val i j=
      (if i=q then if j=p then (1 : K) else 0 else 0) -
        (if i=p then if j=q then 1 else 0 else 0) := by
  rw [alternating_coeff,coordinateWedge_image,coordinatePair,map_sub]
  simp only [Pi.sub_apply,coordinateSingle_component,map_sub]
  by_cases hiq : i=q <;> by_cases hip : i=p
  all_goals simp_all [Pi.single_apply,coordinateSection_polynomial (K := K),
    MvPolynomial.coeff_X,Finsupp.single_left_inj one_ne_zero, eq_comm]
  all_goals erw [coordinateSection_polynomial (K := K)]
  all_goals simp only [MvPolynomial.coeff_X,Finsupp.single_left_inj one_ne_zero]

variable [LinearOrder I]

/-- Strict upper coefficient entries are coordinates on the entire actual
global Euler-kernel section space. -/
def coordinates : Γ(eulerKernel (I := I) (K := K) 2,⊤) ≃ₗ[K]
    ({q : I×I // q.1<q.2} → K) :=
  (alternatingGlobalKernelEquiv (I := I) (K := K)).symm.trans alternatingCoordinates

/-- The literal coordinate wedges, in the correct orientation, are exactly
the coordinate vectors of the full global section space. -/
theorem coordinates_wedge (p : {q : I×I // q.1<q.2}) :
    coordinates (K := K) (coordinateWedge (K := K) p.val.2 p.val.1 ⊤)=Pi.single p (1 : K) := by
  funext q
  change ((alternatingGlobalKernelEquiv (I := I) (K := K)).symm
    (coordinateWedge (K := K) p.val.2 p.val.1 ⊤)).val q.val.1 q.val.2=
      Pi.single (M := fun _ : {q : I×I // q.1<q.2} => K) p (1 : K) q
  rw [coordinateWedge_coeff (K := K)]
  by_cases h : q=p
  · subst q
    simp [ne_of_lt p.property,Ne.symm (ne_of_lt p.property)]
  · have hfirst : ¬ (q.val.1=p.val.1 ∧ q.val.2=p.val.2) := by
      rintro ⟨h₁,h₂⟩
      exact h (Subtype.ext (Prod.ext h₁ h₂))
    have hsecond : ¬ (q.val.1=p.val.2 ∧ q.val.2=p.val.1) := by
      rintro ⟨h₁,h₂⟩
      have hlt := q.property
      rw [h₁,h₂] at hlt
      exact (not_lt_of_ge p.property.le) hlt
    simp only [Pi.single_apply,if_neg h]
    split_ifs <;> simp_all

/-- The exact expansion of every global section in the actual coordinate
wedges. No dimension comparison is used as a substitute for spanning. -/
theorem section_eq_sum_wedges (s : Γ(eulerKernel (I := I) (K := K) 2,⊤)) :
    s=∑ p : {q : I×I // q.1<q.2}, coordinates (K := K) s p • coordinateWedge (K := K) p.val.2 p.val.1 ⊤ := by
  apply (coordinates (I := I) (K := K)).injective
  rw [map_sum]
  simp only [_root_.map_smul,coordinates_wedge]
  funext q
  simp [Pi.smul_apply,Pi.single_apply]

/-- The span is the whole actual global section space. -/
theorem span_coordinateWedges :
    Submodule.span K (Set.range (fun p : {q : I×I // q.1<q.2} =>
      coordinateWedge (K := K) p.val.2 p.val.1 ⊤))=⊤ := by
  apply top_unique
  intro s _
  rw [section_eq_sum_wedges s]
  apply Submodule.sum_mem
  intro p _
  exact Submodule.smul_mem _ (coordinates (K := K) s p)
    (Submodule.subset_span (Set.mem_range_self p))

end PaperVerification.Segre.GlobalEulerWedges

end SegreGlobalEulerWedges

section SegreProductGlobalWedges

/-!
# The whole critical source H⁰ is spanned by the actual global wedges

Global sections of every projection pullback are proved to come from the
factor, and every factor section has the complete coordinate-wedge
expansion. Consequently the image of any actual critical functional on H⁰
is precisely the span of its values on the actual global coordinate wedges.
This is a statement about the full global section module, without a
genericity or independence premise.

-/

set_option autoImplicit false

namespace PaperVerification.Segre.SchemeProductSections

open AlgebraicGeometry CategoryTheory Limits Opposite
open AlgebraicGeometry.Scheme.Modules

universe u v
variable (K : Type (max u v)) [CommRing K] {Y : Scheme.{max u v}}
  [Y.Over (Spec (.of K))]

local instance : HasLimitsOfSize.{u,u} Y.Modules := hasLimitsOfSizeShrink.{u,u} _

/-- The canonical product-section comparison over the original coefficient ring. -/
def productSectionsBaseEquiv {J : Type u} (M : J → Y.Modules) (U : Y.Opens) :
    ExternalSections.sections K (∏ᶜ M) U ≃ₗ[K]
      ((j : J) → ExternalSections.sections K (M j) U) := by
  let e := productSectionsEquiv M U
  refine
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := ?_ }
  intro c s
  have he := e.map_smul ((Y.baseRingToStructurePresheaf K).app (op U) c) s
  exact he

@[simp] theorem productSectionsBaseEquiv_apply {J : Type u}
    (M : J → Y.Modules) (U : Y.Opens)
    (s : ExternalSections.sections K (∏ᶜ M) U) (j : J) :
    productSectionsBaseEquiv K M U s j = (Pi.π M j).app U s :=
  productSectionsEquiv_apply M U s j

end PaperVerification.Segre.SchemeProductSections

namespace PaperVerification.Segre.ProductGlobalWedges

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open FixedProductCohomology FixedProductProjections ProductKoszulVanishing
open ActualProductKoszulTerms EulerSheaf EulerSections EulerCriticalFunctional
open SingleFactorGlobalSections ExternalSections
open scoped BigOperators

universe u
variable (K : Type u) [Field K] {k : ℕ}
variable (I : Fin (k+1) → Type u)
variable [∀ i,Fintype (I i)] [∀ i,DecidableEq (I i)]
variable [∀ i,Nonempty (I i)] [∀ i,LinearOrder (I i)]

set_option quotPrecheck false in local notation "X" => (product K I).scheme

local instance globalFunctionsAlgebra : Algebra K Γ(X,⊤) :=
  (Scheme.Modules.baseRingToGlobalSections K X).toAlgebra

local instance globalSectionsTower (M : (X).Modules) : IsScalarTower K Γ(X,⊤) Γ(M,⊤) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

instance factorProjection_isOver (i : Fin (k+1)) :
    (factorProjection K I i).IsOver (Spec (.of K)) :=
  ⟨projection_toBase (fun i => projectiveScheme K (I i)) i⟩

/-- The actual source section decomposition, over the original coefficient
field, retains every pulled-back Euler-kernel factor. -/
def sourceSectionsEquiv : sections K (source K I) ⊤ ≃ₗ[K]
    (∀ i,sections K ((Scheme.Modules.pullback (factorProjection K I i)).obj
      (eulerKernel (I := I i) (K := K) 2)) ⊤) :=
  SchemeProductSections.productSectionsBaseEquiv K
    (fun i => (Scheme.Modules.pullback (factorProjection K I i)).obj
      (eulerKernel (I := I i) (K := K) 2)) ⊤

/-- The index set of the complete alternating global source coordinates. -/
abbrev WedgeIndex := Σ i : Fin (k+1), {p : I i×I i // p.1<p.2}

/-- Insert the literal pullback of a literal factor coordinate wedge in the
corresponding summand of the actual global source section module. -/
def sourceWedge (i : Fin (k+1)) (p : {q : I i×I i // q.1<q.2}) :
    sections K (source K I) ⊤ :=
  (sourceSectionsEquiv K I).symm (Pi.single i
    ((factorProjection K I i).pullbackSectionsLE
      (eulerKernel (I := I i) (K := K) 2) ⊤ ⊤ (by simp)
      (coordinateWedge p.val.2 p.val.1 ⊤)))

/-- Ordered coordinate pairs, with repetitions retained, give the literal
source sections matching the paper's full critical operator. -/
def orderedSourceWedge (q : Σ i : Fin (k+1), I i×I i) :
    sections K (source K I) ⊤ :=
  (sourceSectionsEquiv K I).symm (Pi.single q.1
    ((factorProjection K I q.1).pullbackSectionsLE
      (eulerKernel (I := I q.1) (K := K) 2) ⊤ ⊤ (by simp)
      (coordinateWedge q.2.2 q.2.1 ⊤)))

theorem sourceWedge_component (i j : Fin (k+1)) (p : {q : I i×I i // q.1<q.2}) :
    sourceSectionsEquiv K I (sourceWedge K I i p) j=
      Pi.single (M := fun j => sections K ((Scheme.Modules.pullback (factorProjection K I j)).obj
      (eulerKernel (I := I j) (K := K) 2)) ⊤) i
        ((factorProjection K I i).pullbackSectionsLE
          (eulerKernel (I := I i) (K := K) 2) ⊤ ⊤ (by simp)
          (coordinateWedge p.val.2 p.val.1 ⊤)) j := by
  rw [sourceWedge,LinearEquiv.apply_symm_apply]

/-- Every genuine global source section is a finite linear combination of
the actual global wedges. The proof covers the full section space. -/
theorem exists_wedge_expansion (s : sections K (source K I) ⊤) :
    ∃ c : WedgeIndex I → K,
      s=∑ i : Fin (k+1), ∑ p : {q : I i×I i // q.1<q.2},
        c ⟨i,p⟩ • sourceWedge K I i p := by
  letI : ∀ i, (eulerKernel (I := I i) (K := K) 2).IsQuasicoherent :=
    fun i => positiveEulerKernel_quasicoherent K (I i)
  have hpre (i : Fin (k+1)) :
      ∃ t : Γ(eulerKernel (I := I i) (K := K) 2,⊤),
        (factorProjection K I i).pullbackSectionsLE
          (eulerKernel (I := I i) (K := K) 2) ⊤ ⊤ (by simp) t=
          sourceSectionsEquiv K I s i :=
    projective_projectionPullback_surjective I i
      (eulerKernel (I := I i) (K := K) 2) (sourceSectionsEquiv K I s i)
  choose t ht using hpre
  refine ⟨fun ip => GlobalEulerWedges.coordinates (t ip.1) ip.2,?_⟩
  apply (sourceSectionsEquiv K I).injective
  rw [map_sum]
  simp only [map_sum,_root_.map_smul]
  funext j
  simp only [Finset.sum_apply,Pi.smul_apply,sourceWedge_component]
  rw [Finset.sum_eq_single j]
  · simp only [Pi.single_eq_same]
    rw [← ht j]
    have he := congrArg
      (GlobalSectionsScalarComparison.identityEquiv K
        (eulerKernel (I := I j) (K := K) 2))
      (GlobalEulerWedges.section_eq_sum_wedges (t j))
    simp only [map_sum, _root_.map_smul] at he
    have hm := congrArg
      (pullbackBaseLE K (factorProjection K I j)
        (eulerKernel (I := I j) (K := K) 2) ⊤ ⊤ (by simp)) he
    simp only [map_sum, _root_.map_smul] at hm
    simpa only [GlobalSectionsScalarComparison.identityEquiv_apply,
      pullbackBaseLE_apply] using hm
  · intro i _ hij
    simp [Pi.single_apply,hij,Ne.symm hij]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

/-- The span is all of the genuine global critical source H⁰. -/
theorem span_sourceWedges :
    Submodule.span K (Set.range (fun ip : WedgeIndex I => sourceWedge K I ip.1 ip.2))=⊤ := by
  apply top_unique
  intro s _
  obtain ⟨c,rfl⟩ := exists_wedge_expansion K I s
  apply Submodule.sum_mem
  intro i _
  apply Submodule.sum_mem
  intro p _
  exact Submodule.smul_mem _ (c ⟨i,p⟩)
    (Submodule.subset_span (Set.mem_range_self (⟨i,p⟩ : WedgeIndex I)))

/-- Consequently the entire H⁰ image of an actual source functional is
exactly the span of its actual coordinate-wedge values. -/
theorem global_range_eq_span_wedges (L : (X).Modules) (φ : source K I ⟶ L) :
    LinearMap.range (((sectionsBasePresheafFunctor K).map φ).app (op ⊤)).hom=
      Submodule.span K (Set.range (fun ip : WedgeIndex I =>
        (((sectionsBasePresheafFunctor K).map φ).app (op ⊤) (sourceWedge K I ip.1 ip.2)))) := by
  let f := (((sectionsBasePresheafFunctor K).map φ).app (op ⊤)).hom
  rw [← Submodule.map_top f,← span_sourceWedges K I,Submodule.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨x,⟨ip,rfl⟩,rfl⟩
    exact ⟨ip,rfl⟩
  · rintro ⟨ip,rfl⟩
    exact ⟨sourceWedge K I ip.1 ip.2,⟨ip,rfl⟩,rfl⟩

/-- The same full image is generated by all ordered critical coordinates,
including the automatically zero diagonal ones. No independence or choice
of orientation is hidden in the statement. -/
theorem global_range_eq_span_ordered_wedges (L : (X).Modules) (φ : source K I ⟶ L) :
    LinearMap.range (((sectionsBasePresheafFunctor K).map φ).app (op ⊤)).hom=
      Submodule.span K (Set.range (fun q : Σ i : Fin (k+1), I i×I i =>
        (((sectionsBasePresheafFunctor K).map φ).app (op ⊤) (orderedSourceWedge K I q)))) := by
  apply le_antisymm
  · rw [global_range_eq_span_wedges K I L φ]
    apply Submodule.span_le.mpr
    rintro y ⟨ip,rfl⟩
    exact Submodule.subset_span ⟨⟨ip.1,ip.2.val⟩,rfl⟩
  · apply Submodule.span_le.mpr
    rintro y ⟨q,rfl⟩
    exact ⟨orderedSourceWedge K I q,rfl⟩

end PaperVerification.Segre.ProductGlobalWedges

end SegreProductGlobalWedges

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
set_option maxHeartbeats 2000000 in
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
