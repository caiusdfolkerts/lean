module
public import SegreVerified.Stage025.ExteriorTwist
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
  out.putStrLn "SEGRE_STAGE Stage027.ExteriorCoordinates"
  out.flush

/-!
# The actual critical bundle and its weighted Koszul complex

The named sections preserve the original proof stages and local scopes.
-/

set_option autoImplicit false

section SegreExteriorCoordinateTwist

/-!
# Exterior powers of every coordinate twisting sheaf

For every integer t and every exterior degree p, the actual exterior power
of the full coordinate sheaf O(t)^I is identified with the actual finite
product O(p*t) indexed by p-element coordinate subsets. The map consists
of literal coordinate minors and is proved to be an isomorphism on the
standard projective cover. No exterior-of-line-bundle comparison is assumed.

This extends the negative-twist coordinate-minor construction to all twists.
-/

set_option autoImplicit false



attribute [local instance] MvPolynomial.gradedAlgebra

namespace PaperVerification.Segre.ExteriorCoordinateTwist

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open EulerSheaf EulerSections ExteriorEuler
open ProjectiveSpectrum.TwistingSheaf
open scoped BigOperators

universe u
variable {I K : Type u} [Fintype I] [DecidableEq I] [LinearOrder I] [Field K]

local notation "𝒜" => MvPolynomial.homogeneousSubmodule I K
local notation "X" => Proj (MvPolynomial.homogeneousSubmodule I K)

/-- The actual finite product of coordinate copies of O(t). -/
def coordinateSource (t : ℤ) : (X).Modules :=
  ∏ᶜ fun _ : I => Proj.twistingSheaf 𝒜 t

variable (t : ℤ)

/-- All localization-valued functions on an open, without a homogeneous restriction. -/
abbrev AmbientSections (U : (X).Opens) := ∀ x : U, Localizations 𝒜 x.val

/-- Structure-sheaf functions act by their literal values in the localizations. -/
def structureValueHom (U : (X).Opens) : Γ(X,U) →+* AmbientSections (I := I) (K := K) U where
  toFun a x := (a.val x).val
  map_one' := by funext x; exact HomogeneousLocalization.val_one
  map_mul' a b := by funext x; exact HomogeneousLocalization.val_mul _ _
  map_zero' := by funext x; exact HomogeneousLocalization.val_zero
  map_add' a b := by funext x; exact HomogeneousLocalization.val_add _ _

instance ambientSectionsAlgebra (U : (X).Opens) :
    Algebra Γ(X,U) (AmbientSections (I := I) (K := K) U) :=
  (structureValueHom U).toAlgebra

/-- The actual value map is linear over the full ring of functions on the open. -/
def sectionValueLinear (t : ℤ) (U : (X).Opens) :
    Γ(Proj.twistingSheaf 𝒜 t,U) →ₗ[Γ(X,U)] AmbientSections (I := I) (K := K) U where
  toFun s := s.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A product of p genuine sections of O(t) has the actual twist p*t. -/
theorem product_twist {J : Type*} (s : Finset J) (U : (X).Opens)
    (f : J → AmbientSections (I := I) (K := K) U)
    (hf : ∀ j∈s, (isLocallyFraction 𝒜 t).pred (f j)) :
    (isLocallyFraction 𝒜 ((s.card : ℤ) * t)).pred (∏ j∈s, f j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
      change (isLocallyFraction 𝒜 0).pred (1 : AmbientSections (I := I) (K := K) U)
      have h : (fun x : U => (1 : Γ(X,U)).val x |>.val) =
          (1 : AmbientSections (I := I) (K := K) U) := by
        funext x
        exact HomogeneousLocalization.val_one
      exact h ▸ isLocallyFraction_val (1 : Γ(X,U))
  | @insert j s hj ih =>
      erw [Finset.card_insert_of_notMem hj,Finset.prod_insert hj]
      have hp := isLocallyFraction_mul (hf j (Finset.mem_insert_self _ _))
        (ih (fun a ha => hf a (Finset.mem_insert_of_mem ha)))
      have hdeg : t + (s.card : ℤ) * t = ((s.card + 1 : ℕ) : ℤ) * t := by
        push_cast
        ring
      simpa only [hdeg] using hp

/-- The row of a selected p×p coordinate minor, as a linear map of full section modules. -/
def minorRows (p : ℕ) (s : Set.powersetCard I p) (U : (X).Opens) :
    Γ(coordinateSource (I := I) (K := K) t,U) →ₗ[Γ(X,U)] (Fin p → AmbientSections (I := I) (K := K) U) :=
  LinearMap.pi (fun j => (sectionValueLinear t U).comp
    ((LinearMap.proj (Set.powersetCard.ofFinEmbEquiv.symm s j)).comp
      (productSectionsEquiv (fun _ : I => Proj.twistingSheaf 𝒜 t) U).toLinearMap))

/-- The literal coordinate determinant, as an alternating map into all localization functions. -/
def rawMinor (p : ℕ) (s : Set.powersetCard I p) (U : (X).Opens) :
    Γ(coordinateSource (I := I) (K := K) t,U) [⋀^Fin p]→ₗ[Γ(X,U)]
      AmbientSections (I := I) (K := K) U :=
  ({ toMultilinearMap := (Matrix.detRowAlternating (n := Fin p)
        (R := AmbientSections (I := I) (K := K) U)).toMultilinearMap.restrictScalars Γ(X,U)
     map_eq_zero_of_eq' := fun v i j h hij =>
       (Matrix.detRowAlternating (n := Fin p)
         (R := AmbientSections (I := I) (K := K) U)).map_eq_zero_of_eq v h hij } :
      (Fin p → AmbientSections (I := I) (K := K) U) [⋀^Fin p]→ₗ[Γ(X,U)]
        AmbientSections (I := I) (K := K) U).compLinearMap (minorRows t p s U)

@[simp] theorem rawMinor_apply (p : ℕ) (s : Set.powersetCard I p) (U : (X).Opens)
    (v : Fin p → Γ(coordinateSource (I := I) (K := K) t,U)) :
    rawMinor t p s U v=Matrix.det (fun i j =>
      (productSectionsEquiv (fun _ : I => Proj.twistingSheaf 𝒜 t) U (v i)
        (Set.powersetCard.ofFinEmbEquiv.symm s j)).val) := rfl

/-- Every coordinate minor has exactly the required twist, including p=0. -/
theorem rawMinor_homogeneous (p : ℕ) (s : Set.powersetCard I p) (U : (X).Opens)
    (v : Fin p → Γ(coordinateSource (I := I) (K := K) t,U)) :
    (isLocallyFraction 𝒜 ((p : ℤ) * t)).pred (rawMinor t p s U v) := by
  erw [rawMinor_apply t,Matrix.det_apply]
  apply (sectionsAddSubgroup 𝒜 ((p : ℤ) * t) U).sum_mem
  intro σ _
  change (Equiv.Perm.sign σ) •
      (∏ j, (productSectionsEquiv (fun _ : I => Proj.twistingSheaf 𝒜 t) U (v (σ j))
        (Set.powersetCard.ofFinEmbEquiv.symm s j)).val) ∈ sectionsAddSubgroup 𝒜 ((p : ℤ) * t) U
  rw [Units.smul_def]
  apply AddSubgroup.zsmul_mem
  apply (mem_sectionsAddSubgroup_iff _).mpr
  simpa only [Finset.card_univ,Fintype.card_fin] using
    product_twist t (Finset.univ : Finset (Fin p)) U _ (fun j _ =>
      (productSectionsEquiv (fun _ : I => Proj.twistingSheaf 𝒜 t) U (v (σ j))
        (Set.powersetCard.ofFinEmbEquiv.symm s j)).property)

/-- The actual minor section as an alternating map into O(p*t). -/
def minorAlternating (p : ℕ) (s : Set.powersetCard I p) (U : (X).Opens) :
    Γ(coordinateSource (I := I) (K := K) t,U) [⋀^Fin p]→ₗ[Γ(X,U)]
      Γ(Proj.twistingSheaf 𝒜 ((p : ℤ) * t),U) where
  toFun v := ⟨rawMinor t p s U v,rawMinor_homogeneous t p s U v⟩
  map_update_add' v i a b := Subtype.ext ((rawMinor t p s U).map_update_add v i a b)
  map_update_smul' v i r a := Subtype.ext ((rawMinor t p s U).map_update_smul v i r a)
  map_eq_zero_of_eq' v i j h hij := Subtype.ext ((rawMinor t p s U).map_eq_zero_of_eq v h hij)

/-- All actual minor sections together, on the entire exterior power of the section module. -/
def minorLinear (p : ℕ) (U : (X).Opens) :
    (⋀[Γ(X,U)]^p Γ(coordinateSource (I := I) (K := K) t,U)) →ₗ[Γ(X,U)]
      Γ((∏ᶜ fun _ : Set.powersetCard I p => Proj.twistingSheaf 𝒜 ((p : ℤ) * t)),U) :=
  (productSectionsEquiv (fun _ : Set.powersetCard I p => Proj.twistingSheaf 𝒜 ((p : ℤ) * t)) U).symm.toLinearMap.comp
      (LinearMap.pi (fun s => exteriorPower.alternatingMapLinearEquiv (minorAlternating t p s U)))

@[simp] theorem minorLinear_ιMulti (p : ℕ) (U : (X).Opens)
    (v : Fin p → Γ(coordinateSource (I := I) (K := K) t,U)) (s : Set.powersetCard I p) :
    productSectionsEquiv (fun _ : Set.powersetCard I p => Proj.twistingSheaf 𝒜 ((p : ℤ) * t)) U
      (minorLinear t p U (exteriorPower.ιMulti Γ(X,U) p v)) s=minorAlternating t p s U v := by
  simp only [minorLinear,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,
    LinearMap.pi_apply,exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]

/-- The complete coordinate-chart trivialization of the actual Euler source sections. -/
def chartSourceEquiv (j : I) (U : (X).Opens) (hU : U≤ProjectiveCech.coordinateOpen (K := K) j) :
    (I → Γ(X,U)) ≃ₗ[Γ(X,U)] Γ(coordinateSource (I := I) (K := K) t,U) :=
  (LinearEquiv.piCongrRight (fun _ : I => Proj.twistingSheaf.chartSectionsLinearEquiv t
    (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X (R := K) j) U hU)).trans
      (productSectionsEquiv (fun _ : I => Proj.twistingSheaf 𝒜 t) U).symm

@[simp] theorem chartSourceEquiv_component (j : I) (U : (X).Opens)
    (hU : U≤ProjectiveCech.coordinateOpen (K := K) j) (v : I → Γ(X,U)) (i : I) :
    productSectionsEquiv (fun _ : I => Proj.twistingSheaf 𝒜 t) U
      (chartSourceEquiv t j U hU v) i=
      Proj.twistingSheaf.chartSectionsLinearEquiv t (MvPolynomial.X j)
        (MvPolynomial.isHomogeneous_X (R := K) j) U hU (v i) := by
  exact congrFun
    ((productSectionsEquiv (fun _ : I => Proj.twistingSheaf 𝒜 t) U).apply_symm_apply
      (fun i => Proj.twistingSheaf.chartSectionsLinearEquiv t (MvPolynomial.X j)
        (MvPolynomial.isHomogeneous_X (R := K) j) U hU (v i))) i

/-- The pth power of the genuine chart generator of O(t) is the
genuine chart generator of O(p*t), for every integer t. -/
theorem chartGenerator_power (j : I) (U : (X).Opens)
    (hU : U≤ProjectiveCech.coordinateOpen (K := K) j) (p : ℕ) (x : U) :
    (Proj.twistingSheaf.chartGenerator ((p : ℤ) * t) (MvPolynomial.X j)
      (MvPolynomial.isHomogeneous_X (R := K) j) U hU).val x =
      ((Proj.twistingSheaf.chartGenerator t (MvPolynomial.X j)
        (MvPolynomial.isHomogeneous_X (R := K) j) U hU).val x)^p := by
  induction p with
  | zero =>
      have hzero : ((0 : ℕ) : ℤ) * t = 0 := by simp
      erw [hzero, Proj.twistingSheaf.chartGenerator_apply]
      simp only [neg_zero, Int.toNat_zero, pow_zero]
      change (Localization.mk (1 : MvPolynomial I K) 1 : Localizations 𝒜 x.val) = 1
      rw [Localization.mk_one_eq_algebraMap,map_one]
  | succ p ih =>
      have h := Proj.twistingSheaf.mul_chartGenerator_apply ((p : ℤ) * t)
        (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X (R := K) j) U hU t x
      change (Proj.twistingSheaf.chartGenerator t (MvPolynomial.X j)
          (MvPolynomial.isHomogeneous_X (R := K) j) U hU).val x *
        (Proj.twistingSheaf.chartGenerator ((p : ℤ) * t) (MvPolynomial.X j)
          (MvPolynomial.isHomogeneous_X (R := K) j) U hU).val x =
        (Proj.twistingSheaf.chartGenerator (t + (p : ℤ) * t) (MvPolynomial.X j)
          (MvPolynomial.isHomogeneous_X (R := K) j) U hU).val x at h
      have hd : ((p + 1 : ℕ) : ℤ) * t = t + (p : ℤ) * t := by push_cast; ring
      rw [ih] at h
      erw [hd]
      simpa only [pow_succ'] using h.symm

/-- In chart coordinates, the actual minor section is the determinant times the genuine
standard generator of O(p*t). -/
theorem minorAlternating_on_chart (p : ℕ) (s : Set.powersetCard I p) (j : I) (U : (X).Opens)
    (hU : U≤ProjectiveCech.coordinateOpen (K := K) j) (v : Fin p → I → Γ(X,U)) :
    minorAlternating t p s U (fun a => chartSourceEquiv t j U hU (v a))=
      Proj.twistingSheaf.chartSectionsLinearEquiv ((p : ℤ) * t) (MvPolynomial.X j)
        (MvPolynomial.isHomogeneous_X (R := K) j) U hU
          (Matrix.det (fun a b => v a (Set.powersetCard.ofFinEmbEquiv.symm s b))) := by
  apply Proj.twistingSheaf.ext
  intro x
  let σ : Γ(X,U) →+* Localizations 𝒜 x.val := (Pi.evalRingHom _ x).comp (structureValueHom U)
  let g := (Proj.twistingSheaf.chartGenerator t (MvPolynomial.X j)
    (MvPolynomial.isHomogeneous_X (R := K) j) U hU).val x
  change (Pi.evalRingHom _ x) (Matrix.det (fun a b =>
      (productSectionsEquiv (fun _ : I => Proj.twistingSheaf 𝒜 t) U
        (chartSourceEquiv t j U hU (v a)) (Set.powersetCard.ofFinEmbEquiv.symm s b)).val))=_
  erw [RingHom.map_det]
  have hchart (n : ℤ) (a : Γ(X,U)) :
      (Proj.twistingSheaf.chartSectionsLinearEquiv n (MvPolynomial.X j)
        (MvPolynomial.isHomogeneous_X (R := K) j) U hU a).val x =
        σ a * (Proj.twistingSheaf.chartGenerator n (MvPolynomial.X j)
          (MvPolynomial.isHomogeneous_X (R := K) j) U hU).val x :=
    Proj.twistingSheaf.chartSectionsLinearEquiv_apply_apply n (MvPolynomial.X j)
      (MvPolynomial.isHomogeneous_X (R := K) j) U hU a x
  have hmat : (Pi.evalRingHom (fun x : U => Localizations 𝒜 x.val) x).mapMatrix
      (fun a b => (productSectionsEquiv (fun _ : I => Proj.twistingSheaf 𝒜 t) U
        (chartSourceEquiv t j U hU (v a))
          (Set.powersetCard.ofFinEmbEquiv.symm s b)).val) =
      (fun a b => σ (v a (Set.powersetCard.ofFinEmbEquiv.symm s b)) * g) := by
    ext a b
    change (productSectionsEquiv (fun _ : I => Proj.twistingSheaf 𝒜 t) U
      (chartSourceEquiv t j U hU (v a))
        (Set.powersetCard.ofFinEmbEquiv.symm s b)).val x = _
    erw [chartSourceEquiv_component]
    exact hchart t _
  erw [hmat, hchart]
  change Matrix.det (fun a b => σ (v a (Set.powersetCard.ofFinEmbEquiv.symm s b))*g)=
    σ (Matrix.det (fun a b => v a (Set.powersetCard.ofFinEmbEquiv.symm s b))) *
      (Proj.twistingSheaf.chartGenerator ((p : ℤ) * t) (MvPolynomial.X j)
        (MvPolynomial.isHomogeneous_X (R := K) j) U hU).val x
  have hm : (fun a b => σ (v a (Set.powersetCard.ofFinEmbEquiv.symm s b))*g)=
      g • (fun a b => σ (v a (Set.powersetCard.ofFinEmbEquiv.symm s b))) := by
    ext a b
    exact mul_comm _ _
  have hd : Matrix.det (fun a b => σ (v a (Set.powersetCard.ofFinEmbEquiv.symm s b))) =
      σ (Matrix.det (fun a b => v a (Set.powersetCard.ofFinEmbEquiv.symm s b))) := by
    calc
      Matrix.det (fun a b => σ (v a (Set.powersetCard.ofFinEmbEquiv.symm s b))) =
          (σ.mapMatrix (fun a b => v a (Set.powersetCard.ofFinEmbEquiv.symm s b))).det := by
        apply congrArg Matrix.det
        ext a b
        rfl
      _ = σ (Matrix.det (fun a b => v a (Set.powersetCard.ofFinEmbEquiv.symm s b))) :=
        (σ.map_det _).symm
  erw [hm, Matrix.det_smul, Fintype.card_fin, hd, chartGenerator_power t]
  exact mul_comm _ _

/-- The full standard trivialization of the target copies of O(p*t). -/
def chartTargetEquiv (p : ℕ) (j : I) (U : (X).Opens)
    (hU : U≤ProjectiveCech.coordinateOpen (K := K) j) :
    (Set.powersetCard I p → Γ(X,U)) ≃ₗ[Γ(X,U)]
      Γ((∏ᶜ fun _ : Set.powersetCard I p => Proj.twistingSheaf 𝒜 ((p : ℤ) * t)),U) :=
  (LinearEquiv.piCongrRight (fun _ : Set.powersetCard I p =>
    Proj.twistingSheaf.chartSectionsLinearEquiv ((p : ℤ) * t) (MvPolynomial.X j)
      (MvPolynomial.isHomogeneous_X (R := K) j) U hU)).trans
        (productSectionsEquiv (fun _ : Set.powersetCard I p => Proj.twistingSheaf 𝒜 ((p : ℤ) * t)) U).symm

/-- The target trivialization has the expected component in every minor coordinate. -/
@[simp] theorem chartTargetEquiv_component (p : ℕ) (j : I) (U : (X).Opens)
    (hU : U ≤ ProjectiveCech.coordinateOpen (K := K) j)
    (v : Set.powersetCard I p → Γ(X,U)) (s : Set.powersetCard I p) :
    productSectionsEquiv
      (fun _ : Set.powersetCard I p => Proj.twistingSheaf 𝒜 ((p : ℤ) * t)) U
      (chartTargetEquiv t p j U hU v) s =
      Proj.twistingSheaf.chartSectionsLinearEquiv ((p : ℤ) * t) (MvPolynomial.X j)
        (MvPolynomial.isHomogeneous_X (R := K) j) U hU (v s) := by
  exact congrFun
    ((productSectionsEquiv
      (fun _ : Set.powersetCard I p => Proj.twistingSheaf 𝒜 ((p : ℤ) * t)) U).apply_symm_apply
      (fun s => Proj.twistingSheaf.chartSectionsLinearEquiv ((p : ℤ) * t) (MvPolynomial.X j)
        (MvPolynomial.isHomogeneous_X (R := K) j) U hU (v s))) s

/-- The induced exterior-power chart equivalence. -/
def chartExteriorEquiv (p : ℕ) (j : I) (U : (X).Opens)
    (hU : U≤ProjectiveCech.coordinateOpen (K := K) j) :
    (⋀[Γ(X,U)]^p (I → Γ(X,U))) ≃ₗ[Γ(X,U)]
      ⋀[Γ(X,U)]^p Γ(coordinateSource (I := I) (K := K) t,U) :=
  LinearEquiv.ofBijective (exteriorPower.map p (chartSourceEquiv t j U hU).toLinearMap)
    (exteriorPower.map_bijective (chartSourceEquiv t j U hU).bijective)

/-- On the whole exterior module, coordinate minors are precisely the standard exterior-basis
coordinates followed by the target chart trivialization. -/
theorem minorLinear_on_chart (p : ℕ) (j : I) (U : (X).Opens)
    (hU : U≤ProjectiveCech.coordinateOpen (K := K) j) :
    (minorLinear t p U).comp (chartExteriorEquiv t p j U hU).toLinearMap=
      (chartTargetEquiv t p j U hU).toLinearMap.comp
        ((Pi.basisFun Γ(X,U) I).exteriorPower p).equivFun.toLinearMap := by
  apply exteriorPower.linearMap_ext
  ext v
  apply (productSectionsEquiv (fun _ : Set.powersetCard I p => Proj.twistingSheaf 𝒜 ((p : ℤ) * t)) U).injective
  funext s
  change productSectionsEquiv (fun _ : Set.powersetCard I p => Proj.twistingSheaf 𝒜 ((p : ℤ) * t)) U
      (minorLinear t p U (exteriorPower.map p (chartSourceEquiv t j U hU).toLinearMap
        (exteriorPower.ιMulti Γ(X,U) p v))) s=_
  erw [exteriorPower.map_apply_ιMulti,minorLinear_ιMulti t]
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, chartTargetEquiv_component]
  change minorAlternating t p s U (fun a => chartSourceEquiv t j U hU (v a))=
    Proj.twistingSheaf.chartSectionsLinearEquiv ((p : ℤ) * t) (MvPolynomial.X j)
      (MvPolynomial.isHomogeneous_X (R := K) j) U hU
        (((Pi.basisFun Γ(X,U) I).exteriorPower p).equivFun (exteriorPower.ιMulti Γ(X,U) p v) s)
  erw [Module.Basis.equivFun_apply,exteriorPower.basis_repr_apply,
    exteriorPower.ιMultiDual_apply_ιMulti]
  simp only [Module.Basis.coord_apply,Pi.basisFun_repr,Matrix.of_apply]
  exact minorAlternating_on_chart t p s j U hU v


run_cmd do
  let out ← IO.getStderr
  out.putStrLn "SEGRE_PROGRESS Stage027.ExteriorCoordinates minor-chart"
  out.flush

/-- All coordinate minors give a bijection on every chart subopen, in all exterior degrees. -/
theorem minorLinear_bijective_on_chart (p : ℕ) (j : I) (U : (X).Opens)
    (hU : U≤ProjectiveCech.coordinateOpen (K := K) j) :
    Function.Bijective (minorLinear t (I := I) (K := K) p U) := by
  let e := chartExteriorEquiv t p j U hU
  have hb : Function.Bijective ((minorLinear t p U).comp e.toLinearMap) := by
    rw [minorLinear_on_chart t]
    exact (chartTargetEquiv t p j U hU).bijective.comp
      ((Pi.basisFun Γ(X,U) I).exteriorPower p).equivFun.bijective
  constructor
  · intro x y h
    obtain ⟨x,rfl⟩ := e.surjective x
    obtain ⟨y,rfl⟩ := e.surjective y
    exact congrArg e (hb.1 h)
  · intro y
    obtain ⟨x,hx⟩ := hb.2 y
    exact ⟨e x,hx⟩

/-- The actual value of a minor section is the determinant of the actual local values. -/
theorem minorAlternating_apply_point (p : ℕ) (s : Set.powersetCard I p) (U : (X).Opens)
    (v : Fin p → Γ(coordinateSource (I := I) (K := K) t,U)) (x : U) :
    (minorAlternating t p s U v).val x=Matrix.det (fun a b =>
      (productSectionsEquiv (fun _ : I => Proj.twistingSheaf 𝒜 t) U (v a)
        (Set.powersetCard.ofFinEmbEquiv.symm s b)).val x) := by
  change (Pi.evalRingHom (fun x : U => Localizations 𝒜 x.val) x)
    (Matrix.det (fun a b =>
      (productSectionsEquiv (fun _ : I => Proj.twistingSheaf 𝒜 t) U (v a)
        (Set.powersetCard.ofFinEmbEquiv.symm s b)).val)) = _
  exact (Pi.evalRingHom (fun x : U => Localizations 𝒜 x.val) x).map_det _

/-- The actual minor sections commute with restrictions to all smaller opens. -/
theorem minorAlternating_res (p : ℕ) (s : Set.powersetCard I p) {U V : (X).Opens}
    (i : V ⟶ U) (v : Fin p → Γ(coordinateSource (I := I) (K := K) t,U)) :
    (Proj.twistingSheaf 𝒜 ((p : ℤ) * t)).presheaf.map i.op (minorAlternating t p s U v)=
      minorAlternating t p s V (fun a => (coordinateSource (I := I) (K := K) t).presheaf.map i.op (v a)) := by
  apply Proj.twistingSheaf.ext
  intro x
  change (minorAlternating t p s U v).val ⟨x.val,i.le x.property⟩=_
  erw [minorAlternating_apply_point t,minorAlternating_apply_point t]
  apply congrArg Matrix.det
  funext a b
  erw [productSectionsEquiv_res]
  rfl

/-- The complete minor map commutes with restriction on every pure exterior generator. -/
theorem minorLinear_res_ιMulti (p : ℕ) {U V : (X).Opens} (i : V ⟶ U)
    (v : Fin p → Γ(coordinateSource (I := I) (K := K) t,U)) :
    (∏ᶜ fun _ : Set.powersetCard I p => Proj.twistingSheaf 𝒜 ((p : ℤ) * t)).presheaf.map i.op
        (minorLinear t p U (exteriorPower.ιMulti Γ(X,U) p v)) =
      minorLinear t p V (exteriorPower.ιMulti Γ(X,V) p
        (fun a => (coordinateSource (I := I) (K := K) t).presheaf.map i.op (v a))) := by
  apply (productSectionsEquiv
    (fun _ : Set.powersetCard I p => Proj.twistingSheaf 𝒜 ((p : ℤ) * t)) V).injective
  funext s
  erw [productSectionsEquiv_res, minorLinear_ιMulti t, minorLinear_ιMulti t]
  exact minorAlternating_res t p s i v

/-- The full coordinate-minor comparison as a morphism from the sectionwise exterior presheaf. -/
def presheafMinorMap (p : ℕ) :
    ((PresheafOfModulesOfCommRing.exteriorPower (R := (X).presheaf) p).obj
      (coordinateSource (I := I) (K := K) t).val) ⟶
        (∏ᶜ fun _ : Set.powersetCard I p => Proj.twistingSheaf 𝒜 ((p : ℤ) * t)).val :=
  ExteriorTwist.exteriorSheafHomOfGenerators (Y := X)
    (M := coordinateSource (I := I) (K := K) t)
    (N := ∏ᶜ fun _ : Set.powersetCard I p => Proj.twistingSheaf 𝒜 ((p : ℤ) * t))
    p (minorLinear (I := I) (K := K) t p)
    (minorLinear_res_ιMulti (I := I) (K := K) t p)

instance presheafMinorMap_locallyInjective (p : ℕ) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf (X).ringCatSheaf.obj).map
        (presheafMinorMap t (I := I) (K := K) p)) :=
  SheafExteriorKernel.locallyInjective_of_injective_on_cover_subopens
    ((PresheafOfModules.toPresheaf (X).ringCatSheaf.obj).map
      (presheafMinorMap t (I := I) (K := K) p))
    (ProjectiveCech.coordinateOpen (I := I) (K := K))
    (ProjectiveCech.coordinate_cover (I := I) (K := K))
    (fun j U hU => (minorLinear_bijective_on_chart t p j U hU).1)

instance presheafMinorMap_locallySurjective (p : ℕ) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf (X).ringCatSheaf.obj).map
        (presheafMinorMap t (I := I) (K := K) p)) :=
  SheafExteriorKernel.locallySurjective_of_surjective_on_cover_subopens
    ((PresheafOfModules.toPresheaf (X).ringCatSheaf.obj).map
      (presheafMinorMap t (I := I) (K := K) p))
    (ProjectiveCech.coordinateOpen (I := I) (K := K))
    (ProjectiveCech.coordinate_cover (I := I) (K := K))
    (fun j U hU => (minorLinear_bijective_on_chart t p j U hU).2)

instance presheafMinorMap_sheafification_isIso (p : ℕ) :
    IsIso ((PresheafOfModules.sheafification (𝟙 (X).ringCatSheaf.obj)).map
      (presheafMinorMap t (I := I) (K := K) p)) := by
  have h : (Opens.grothendieckTopology X).W.inverseImage
      (PresheafOfModules.toPresheaf (X).ringCatSheaf.obj)
      (presheafMinorMap t (I := I) (K := K) p) :=
    (Opens.grothendieckTopology X).W_of_isLocallyBijective
      ((PresheafOfModules.toPresheaf (X).ringCatSheaf.obj).map
        (presheafMinorMap t (I := I) (K := K) p))
  rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
    (𝟙 (X).ringCatSheaf.obj)] at h
  exact h

omit [LinearOrder I] in
/-- The full actual exterior source sheaf is the expected finite product of O(p*t), with the
isomorphism defined by genuine coordinate minors in every characteristic. -/
def coordinateExteriorIso (p : ℕ) :
    (SheafOfModules.exteriorPower (X).sheaf p).obj (coordinateSource (I := I) (K := K) t) ≅
      ∏ᶜ fun _ : Set.powersetCard I p => Proj.twistingSheaf 𝒜 ((p : ℤ) * t) := by
  classical
  letI : LinearOrder I := LinearOrder.lift' (Fintype.equivFin I) (Fintype.equivFin I).injective
  letI : IsIso ((PresheafOfModules.sheafification (𝟙 (X).ringCatSheaf.obj)).map
      (presheafMinorMap (I := I) (K := K) t p)) :=
    presheafMinorMap_sheafification_isIso (I := I) (K := K) t p
  exact SheafOfModules.exteriorPowerIso (R := (X).sheaf) p
      (coordinateSource (I := I) (K := K) t) ≪≫
    asIso ((PresheafOfModules.sheafification (𝟙 (X).ringCatSheaf.obj)).map (presheafMinorMap (I := I) (K := K) t p)) ≪≫
    TauCeti.SheafOfModules.sheafificationIso (X).ringCatSheaf
      (∏ᶜ fun _ : Set.powersetCard I p => Proj.twistingSheaf 𝒜 ((p : ℤ) * t))

end PaperVerification.Segre.ExteriorCoordinateTwist

end SegreExteriorCoordinateTwist

run_cmd do
  let out ← IO.getStderr
  out.putStrLn "SEGRE_PROGRESS Stage027.ExteriorCoordinates coordinate-twist"
  out.flush


section SegreExteriorCoordinateSections

/-!
# Actual chart sections of the coordinate exterior sheaves

The sheafified coordinate-minor isomorphism is evaluated along the actual
sheafification unit. This proves that on every subopen of a coordinate
chart, taking the exterior power of the full section module gives exactly
the full section module of the actual exterior-power sheaf.

The equality records the actual maps, so it can transport contraction
formulas through sheafification. It does not replace either side by a
vector space of the expected dimension.
-/

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

namespace PaperVerification.Segre.ExteriorCoordinateSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory Opposite
open AlgebraicGeometry.Scheme.Modules
open EulerSheaf EulerSections ExteriorCoordinateTwist
open SheafCoefficientContraction
open scoped TensorProduct BigOperators

section AbstractAdjunction

variable {C D : Type*} [Category C] [Category D]
variable {S : C ⥤ D} {F : D ⥤ C}

/-- Transporting a sheafification map through an arbitrary isomorphism and
then evaluating the adjunction counit preserves its original unit value. -/
theorem unit_comp_cancelIso_map_counit (A : S ⊣ F)
    {P : C} {M N : D} (e : M ≅ S.obj P) (g : P ⟶ F.obj N) :
    (A.unit.app P ≫ F.map e.inv) ≫
      F.map (e.hom ≫ S.map g ≫ A.counit.app N) = g := by
  rw [Category.assoc, ← F.map_comp, Iso.inv_hom_id_assoc, F.map_comp]
  exact (A.unit.naturality_assoc g (F.map (A.counit.app N))).symm.trans
    ((congrArg (g ≫ ·) (A.right_triangle_components N)).trans (Category.comp_id g))

end AbstractAdjunction

section AbstractExteriorUnit

open TauCeti.SheafOfModules (ringCatSheaf)
open SheafCoefficientContraction

universe u
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (R : Sheaf J CommRingCat.{u})
variable (M N : SheafOfModules.{u} (ringCatSheaf R))

/-- The canonical exterior unit computes the sheafification of every map
from the sectionwise exterior power to an actual sheaf. -/
theorem exteriorUnit_comp_sheafified_map (p : ℕ)
    (g : (PresheafOfModulesOfCommRing.exteriorPower (R := R.obj) p).obj M.val ⟶ N.val) :
    exteriorUnit R M p ≫
      ((SheafOfModules.exteriorPowerIso (R := R) p M).hom ≫
        (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map g ≫
        (TauCeti.SheafOfModules.sheafificationIso (ringCatSheaf R) N).hom).val = g := by
  let S : PresheafOfModules.{u} (ringCatSheaf R).obj ⥤
      SheafOfModules.{u} (ringCatSheaf R) :=
    PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)
  let F := SheafOfModules.forget (ringCatSheaf R)
  let A : S ⊣ F := TauCeti.SheafOfModules.sheafificationForgetAdjunction R
  let P := (PresheafOfModulesOfCommRing.exteriorPower (R := R.obj) p).obj M.val
  let e : (SheafOfModules.exteriorPower R p).obj M ≅ S.obj P :=
    SheafOfModules.exteriorPowerIso (R := R) p M
  change (A.unit.app P ≫ F.map e.inv) ≫
    F.map (e.hom ≫ S.map g ≫
      (TauCeti.SheafOfModules.sheafificationIso (ringCatSheaf R) N).hom) = g
  rw [← TauCeti.SheafOfModules.sheafificationForgetAdjunction_counit_app R N]
  exact unit_comp_cancelIso_map_counit A e g

end AbstractExteriorUnit


universe u
variable {I K : Type u} [Fintype I] [DecidableEq I] [LinearOrder I] [Field K]

local notation "𝒜" => MvPolynomial.homogeneousSubmodule I K
local notation "X" => Proj (MvPolynomial.homogeneousSubmodule I K)

/-- The coordinate-minor isomorphism with the ordering used to orient its
exterior coordinates displayed in the surrounding data. -/
def coordinateIso (t : ℤ) (p : ℕ) :
    (SheafOfModules.exteriorPower (X).sheaf p).obj
        (coordinateSource (I := I) (K := K) t) ≅
      ∏ᶜ fun _ : Set.powersetCard I p => Proj.twistingSheaf 𝒜 ((p : ℤ) * t) := by
  letI : IsIso ((PresheafOfModules.sheafification (𝟙 (X).ringCatSheaf.obj)).map
      (presheafMinorMap (I := I) (K := K) t p)) :=
    presheafMinorMap_sheafification_isIso (I := I) (K := K) t p
  exact SheafOfModules.exteriorPowerIso (R := (X).sheaf) p
      (coordinateSource (I := I) (K := K) t) ≪≫
    asIso ((PresheafOfModules.sheafification (𝟙 (X).ringCatSheaf.obj)).map
      (presheafMinorMap (I := I) (K := K) t p)) ≪≫
      TauCeti.SheafOfModules.sheafificationIso (X).ringCatSheaf
        (∏ᶜ fun _ : Set.powersetCard I p => Proj.twistingSheaf 𝒜 ((p : ℤ) * t))

/-- The global isomorphism restricts to the literal minor map on every
sectionwise exterior module. -/
@[reassoc]
theorem exteriorUnit_coordinateIso (t : ℤ) (p : ℕ) :
    exteriorUnit (X).sheaf (coordinateSource (I := I) (K := K) t) p ≫
      (coordinateIso t p).hom.val = presheafMinorMap t p := by
  simpa only [coordinateIso, Iso.trans_hom, asIso_hom] using
    (exteriorUnit_comp_sheafified_map (X).sheaf
      (coordinateSource (I := I) (K := K) t)
      (∏ᶜ fun _ : Set.powersetCard I p =>
        Proj.twistingSheaf 𝒜 ((p : ℤ) * t)) p
      (presheafMinorMap (I := I) (K := K) t p))

@[simp]
theorem coordinateIso_exteriorUnit (t : ℤ) (p : ℕ) (U : (X).Opens)
    (z : ⋀[Γ(X, U)]^p Γ(coordinateSource (I := I) (K := K) t, U)) :
    Scheme.Modules.Hom.app («X» := X)
      (coordinateIso (I := I) (K := K) t p).hom U
      ((exteriorUnit (X).sheaf (coordinateSource (I := I) (K := K) t) p).app (op U) z) =
        minorLinear t p U z := by
  have h := congrArg
    (fun f : (PresheafOfModulesOfCommRing.exteriorPower (R := (X).presheaf) p).obj
        (coordinateSource (I := I) (K := K) t).val ⟶
        (∏ᶜ fun _ : Set.powersetCard I p => Proj.twistingSheaf 𝒜 ((p : ℤ) * t)).val =>
      (f.app' (op U)).hom)
    (exteriorUnit_coordinateIso (I := I) (K := K) t p)
  exact LinearMap.congr_fun h z

/-- The complete induced equivalence on actual sheaf sections. -/
def coordinateSectionsEquiv (t : ℤ) (p : ℕ) (U : (X).Opens) :
    Γ((SheafOfModules.exteriorPower (X).sheaf p).obj
      (coordinateSource (I := I) (K := K) t), U) ≃ₗ[Γ(X, U)]
      Γ((∏ᶜ fun _ : Set.powersetCard I p =>
        Proj.twistingSheaf 𝒜 ((p : ℤ) * t)), U) :=
  ((SheafOfModules.evaluation (X).ringCatSheaf (op U)).mapIso
    (coordinateIso t p)).toLinearEquiv

@[simp]
theorem coordinateSectionsEquiv_exteriorUnit (t : ℤ) (p : ℕ) (U : (X).Opens)
    (z : ⋀[Γ(X, U)]^p Γ(coordinateSource (I := I) (K := K) t, U)) :
    coordinateSectionsEquiv t p U
      ((exteriorUnit (X).sheaf (coordinateSource t) p).app (op U) z) =
        minorLinear t p U z :=
  coordinateIso_exteriorUnit t p U z

/-- Every actual exterior sheaf section on a coordinate chart comes from
the actual exterior module of sections, and the expression is unique. -/
theorem exteriorUnit_bijective_on_chart (t : ℤ) (p : ℕ)
    (j : I) (U : (X).Opens) (hU : U ≤ ProjectiveCech.coordinateOpen (K := K) j) :
    Function.Bijective
      ((exteriorUnit (X).sheaf (coordinateSource (I := I) (K := K) t) p).app (op U)) := by
  let e := coordinateSectionsEquiv (I := I) (K := K) t p U
  have hb : Function.Bijective (fun z =>
      e ((exteriorUnit (X).sheaf (coordinateSource t) p).app (op U) z)) := by
    simp only [e, coordinateSectionsEquiv_exteriorUnit]
    exact minorLinear_bijective_on_chart t p j U hU
  constructor
  · intro x y h
    exact hb.1 (congrArg e h)
  · intro y
    obtain ⟨z, hz⟩ := hb.2 (e y)
    exact ⟨z, e.injective hz⟩

/-- A full sectionwise exterior/sheaf exterior equivalence on each
coordinate chart, with its forward map canonically prescribed. -/
def exteriorSectionEquiv (t : ℤ) (p : ℕ)
    (j : I) (U : (X).Opens) (hU : U ≤ ProjectiveCech.coordinateOpen (K := K) j) :
    (⋀[Γ(X, U)]^p Γ(coordinateSource (I := I) (K := K) t, U)) ≃ₗ[Γ(X, U)]
      Γ((SheafOfModules.exteriorPower (X).sheaf p).obj (coordinateSource t), U) :=
  LinearEquiv.ofBijective
    ((exteriorUnit (X).sheaf (coordinateSource t) p).app' (op U)).hom
    (exteriorUnit_bijective_on_chart t p j U hU)

@[simp]
theorem exteriorSectionEquiv_ιMulti (t : ℤ) (p : ℕ)
    (j : I) (U : (X).Opens) (hU : U ≤ ProjectiveCech.coordinateOpen (K := K) j)
    (v : Fin p → Γ(coordinateSource (I := I) (K := K) t, U)) :
    exteriorSectionEquiv t p j U hU (exteriorPower.ιMulti Γ(X, U) p v) =
      wedgeSection (X).sheaf (coordinateSource t) p (op U) v := rfl

/-- The actual exterior sheaf has the complete exterior coordinate frame
on the entire chart section module. -/
def actualExteriorFrame (t : ℤ) (p : ℕ)
    (j : I) (U : (X).Opens) (hU : U ≤ ProjectiveCech.coordinateOpen (K := K) j) :
    (⋀[Γ(X, U)]^p (I → Γ(X, U))) ≃ₗ[Γ(X, U)]
      Γ((SheafOfModules.exteriorPower (X).sheaf p).obj
        (coordinateSource (I := I) (K := K) t), U) :=
  (chartExteriorEquiv t p j U hU).trans
    (exteriorSectionEquiv t p j U hU)

/-- Every frame vector is the actual wedge of the genuine twisting
frames, including degrees zero and degrees above the coordinate rank. -/
@[simp]
theorem actualExteriorFrame_ιMulti (t : ℤ) (p : ℕ)
    (j : I) (U : (X).Opens) (hU : U ≤ ProjectiveCech.coordinateOpen (K := K) j)
    (v : Fin p → I → Γ(X, U)) :
    actualExteriorFrame t p j U hU (exteriorPower.ιMulti Γ(X, U) p v) =
      wedgeSection (X).sheaf (coordinateSource t) p (op U)
        (fun i => chartSourceEquiv t j U hU (v i)) := by
  change exteriorSectionEquiv t p j U hU
      (exteriorPower.map p (chartSourceEquiv t j U hU).toLinearMap
        (exteriorPower.ιMulti Γ(X, U) p v)) = _
  rw [exteriorPower.map_apply_ιMulti, exteriorSectionEquiv_ιMulti]
  rfl

end PaperVerification.Segre.ExteriorCoordinateSections

end SegreExteriorCoordinateSections

run_cmd do
  let out ← IO.getStderr
  out.putStrLn "SEGRE_PROGRESS Stage027.ExteriorCoordinates exterior-sections"
  out.flush


section SegreCoefficientKernel

/-!
# Exterior kernels for coefficient-valued contractions

The exterior power of the literal kernel of a map to a rank-one module
maps canonically into the literal coefficient-contraction kernel. Whenever
a specified trivialization makes one vector evaluate to one, this canonical
map is an isomorphism in every exterior degree. Its forward map does not
depend on the trivialization or the splitting vector.

This is the algebraic chart theorem for the positive Euler kernel. All
rings are arbitrary commutative rings. The trivialization and unit value
are explicit local data.
-/

set_option autoImplicit false

namespace PaperVerification.Segre.CoefficientKernel

open scoped TensorProduct

universe u v w
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {L : Type w} [AddCommGroup L] [Module R L]

/-- The actual scalar functional in the specified coefficient frame. -/
def normalizedFunctional (e : L ≃ₗ[R] R) (φ : M →ₗ[R] L) : Module.Dual R M :=
  e.toLinearMap ∘ₗ φ

/-- The literal kernel does not change after a coefficient trivialization. -/
def normalizedKernelEquiv (e : L ≃ₗ[R] R) (φ : M →ₗ[R] L) :
    LinearMap.ker φ ≃ₗ[R] LinearMap.ker (normalizedFunctional e φ) where
  toFun x := ⟨x.val, by
    change e (φ x.val) = 0
    rw [x.property, map_zero]⟩
  invFun x := ⟨x.val, by
    apply e.injective
    change normalizedFunctional e φ x.val = e 0
    rw [x.property, map_zero]⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Actual normalization of the coefficient tensor factor. -/
def tensorCoefficientEquiv (e : L ≃ₗ[R] R) (n : ℕ) :
    ((⋀[R]^n M) ⊗[R] L) ≃ₗ[R] ⋀[R]^n M :=
  (TensorProduct.congr (LinearEquiv.refl R (⋀[R]^n M)) e).trans
    (TensorProduct.rid R (⋀[R]^n M))

/-- After normalization, the full coefficient contraction equals the actual
scalar Koszul differential, as a linear map. -/
theorem normalize_contraction (e : L ≃ₗ[R] R) (φ : M →ₗ[R] L) (n : ℕ) :
    (tensorCoefficientEquiv e n).toLinearMap ∘ₗ
        CoefficientContraction.contraction φ n =
      TauCeti.koszulDifferential (normalizedFunctional e φ) n := by
  have h := CoefficientContraction.contraction_natural
    (LinearMap.id : M →ₗ[R] M) e.toLinearMap φ (normalizedFunctional e φ)
    (by rw [LinearMap.comp_id]; rfl) n
  simp only [exteriorPower.map_id, LinearMap.comp_id] at h
  change (TensorProduct.rid R (⋀[R]^n M)).toLinearMap ∘ₗ
    (TensorProduct.map (LinearMap.id : (⋀[R]^n M) →ₗ[R] ⋀[R]^n M)
      e.toLinearMap ∘ₗ CoefficientContraction.contraction φ n) = _
  rw [h, CoefficientContraction.scalar_contraction_eq]

/-- The two full contraction kernels have identical underlying vectors. -/
def normalizedCycleEquiv (e : L ≃ₗ[R] R) (φ : M →ₗ[R] L) (n : ℕ) :
    LinearMap.ker (CoefficientContraction.contraction φ n) ≃ₗ[R]
      LinearMap.ker (TauCeti.koszulDifferential (normalizedFunctional e φ) n) where
  toFun x := ⟨x.val, by
    have h := LinearMap.congr_fun (normalize_contraction e φ n) x.val
    change tensorCoefficientEquiv e n
      (CoefficientContraction.contraction φ n x.val) =
        TauCeti.koszulDifferential (normalizedFunctional e φ) n x.val at h
    rw [x.property, map_zero] at h
    exact h.symm⟩
  invFun x := ⟨x.val, by
    apply (tensorCoefficientEquiv e n).injective
    have h := LinearMap.congr_fun (normalize_contraction e φ n) x.val
    change tensorCoefficientEquiv e n
      (CoefficientContraction.contraction φ n x.val) =
        TauCeti.koszulDifferential (normalizedFunctional e φ) n x.val at h
    rw [h, x.property, map_zero]⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Zero coefficient maps have zero full exterior contraction. -/
theorem contraction_zero (n : ℕ) :
    CoefficientContraction.contraction (0 : M →ₗ[R] L) n = 0 :=
  (CoefficientContraction.contractionLinear n).map_zero

/-- The canonical exterior inclusion lands in coefficient-contraction cycles. -/
theorem contraction_exterior_kernel (φ : M →ₗ[R] L) (n : ℕ) :
    CoefficientContraction.contraction φ n ∘ₗ
      exteriorPower.map (n + 1) (LinearMap.ker φ).subtype = 0 := by
  have h := CoefficientContraction.contraction_natural
    (LinearMap.ker φ).subtype (LinearMap.id : L →ₗ[R] L)
    (0 : LinearMap.ker φ →ₗ[R] L) φ (by
      ext x
      exact x.property) n
  rw [contraction_zero, LinearMap.comp_zero] at h
  exact h.symm

/-- The actual canonical map, defined without any frame or splitting choice. -/
def exteriorKernelMap (φ : M →ₗ[R] L) (n : ℕ) :
    (⋀[R]^(n + 1) (LinearMap.ker φ)) →ₗ[R]
      LinearMap.ker (CoefficientContraction.contraction φ n) :=
  (exteriorPower.map (n + 1) (LinearMap.ker φ).subtype).codRestrict _ (fun z => by
    have h := LinearMap.congr_fun (contraction_exterior_kernel φ n) z
    exact h)

@[simp]
theorem exteriorKernelMap_val (φ : M →ₗ[R] L) (n : ℕ)
    (z : ⋀[R]^(n + 1) (LinearMap.ker φ)) :
    (exteriorKernelMap φ n z).val =
      exteriorPower.map (n + 1) (LinearMap.ker φ).subtype z := rfl

/-- A specified local coefficient frame and a unit value construct the full
inverse. No freeness or finite generation of the source module is required. -/
def splitExteriorKernelEquiv (e : L ≃ₗ[R] R) (φ : M →ₗ[R] L)
    (m : M) (hm : normalizedFunctional e φ m = 1) (n : ℕ) :
    (⋀[R]^(n + 1) (LinearMap.ker φ)) ≃ₗ[R]
      LinearMap.ker (CoefficientContraction.contraction φ n) :=
  (LinearEquiv.ofBijective
    (exteriorPower.map (n + 1) (normalizedKernelEquiv e φ).toLinearMap)
    (exteriorPower.map_bijective (normalizedKernelEquiv e φ).bijective)).trans
      ((SplitKoszul.exteriorKernelEquiv (normalizedFunctional e φ) m hm n).trans
        (normalizedCycleEquiv e φ n).symm)

/-- The isomorphism's forward map is the canonical exterior inclusion,
independent of every local choice. This is the overlap compatibility needed
to pass from chart splittings to the actual sheaf morphism. -/
theorem splitExteriorKernelEquiv_val (e : L ≃ₗ[R] R) (φ : M →ₗ[R] L)
    (m : M) (hm : normalizedFunctional e φ m = 1) (n : ℕ)
    (z : ⋀[R]^(n + 1) (LinearMap.ker φ)) :
    (splitExteriorKernelEquiv e φ m hm n z).val =
      exteriorPower.map (n + 1) (LinearMap.ker φ).subtype z := by
  change exteriorPower.map (n + 1) (LinearMap.ker (normalizedFunctional e φ)).subtype
    (exteriorPower.map (n + 1) (normalizedKernelEquiv e φ).toLinearMap z) = _
  have hmap :
      (LinearMap.ker (normalizedFunctional e φ)).subtype ∘ₗ
          (normalizedKernelEquiv e φ).toLinearMap =
        (LinearMap.ker φ).subtype := by
    ext x
    rfl
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, hmap]

theorem splitExteriorKernelEquiv_toLinearMap
    (e : L ≃ₗ[R] R) (φ : M →ₗ[R] L) (m : M)
    (hm : normalizedFunctional e φ m = 1) (n : ℕ) :
    (splitExteriorKernelEquiv e φ m hm n).toLinearMap = exteriorKernelMap φ n := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  exact splitExteriorKernelEquiv_val e φ m hm n z

/-- The actual canonical map is bijective on every split rank-one chart. -/
theorem exteriorKernelMap_bijective (e : L ≃ₗ[R] R) (φ : M →ₗ[R] L)
    (m : M) (hm : normalizedFunctional e φ m = 1) (n : ℕ) :
    Function.Bijective (exteriorKernelMap φ n) := by
  rw [← splitExteriorKernelEquiv_toLinearMap e φ m hm n]
  exact (splitExteriorKernelEquiv e φ m hm n).bijective

end PaperVerification.Segre.CoefficientKernel

end SegreCoefficientKernel

run_cmd do
  let out ← IO.getStderr
  out.putStrLn "SEGRE_PROGRESS Stage027.ExteriorCoordinates coefficient-kernel"
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
