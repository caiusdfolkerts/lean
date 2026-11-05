module
public import SegreVerified.Stage027.ExteriorCoordinates
public import SegreVerified.Stage025.EulerCoordinates
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
  (← IO.getStdout).flush
  let out ← IO.getStderr
  out.putStrLn "SEGRE_STAGE Stage027.CriticalCharts"
  out.flush

/-!
# The actual critical bundle and its weighted Koszul complex

The named sections preserve the original proof stages and local scopes.
-/

set_option autoImplicit false

section SegreEulerCriticalFunctional

/-!
# The actual Euler-kernel critical functional

The source is the actual categorical kernel of the coordinate Euler map
`O(1)^(n+1) -> O(2)`. Coordinate wedges are constructed as actual sections
of this kernel. Restricting an arbitrary family of coefficient morphisms to
the kernel evaluates on the wedge `(p,q)` as `x_p c_q - x_q c_p`.

The same formula is proved after genuine sheaf pullback and restriction to
any smaller open. This is the global map needed on a product of projective
spaces. The tensor-specific coefficient morphisms and the identification of
this kernel with the twisted Euler kernel remain separate constructions.

-/

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

namespace PaperVerification.Segre.EulerCriticalFunctional

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open EulerSheaf EulerSections
open scoped BigOperators

universe u
variable {I K : Type u} [Fintype I] [DecidableEq I] [Field K]

local notation "𝒜" => MvPolynomial.homogeneousSubmodule I K
local notation "X" => Proj (MvPolynomial.homogeneousSubmodule I K)
local notation "O1" => Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule I K) (1 : ℤ)

/-- The genuine middle sheaf of the degree-two Euler map. -/
def positiveEulerSource : (X).Modules := ∏ᶜ fun _ : I => O1

/-- A section in one summand of the actual finite sheaf product. -/
def coordinateSingle (i : I) (U : (X).Opens) (s : Γ(O1, U)) :
    Γ(positiveEulerSource (I := I) (K := K), U) :=
  (productSectionsEquiv (fun _ : I => O1) U).symm (Pi.single i s)

@[simp]
theorem coordinateSingle_component (i j : I) (U : (X).Opens) (s : Γ(O1, U)) :
    productSectionsEquiv (fun _ : I => O1) U (coordinateSingle i U s) j =
      (Pi.single i s : I → Γ(O1, U)) j := by
  exact congrFun
    ((productSectionsEquiv (fun _ : I => O1) U).apply_symm_apply
      (Pi.single i s : I → Γ(O1, U))) j

/-- The Euler map evaluates the selected summand by literal coordinate multiplication. -/
theorem eulerMap_coordinateSingle (i : I) (U : (X).Opens) (s : Γ(O1, U)) :
    (eulerMap (I := I) (K := K) 2).app U (coordinateSingle i U s) =
      coordinateMulSections i 2 U s := by
  erw [eulerMap_app]
  change (∑ j : I, coordinateMulSections j 2 U
    (productSectionsEquiv (fun _ : I => O1) U (coordinateSingle i U s) j)) = _
  simp only [coordinateSingle_component]
  rw [Finset.sum_eq_single i]
  · simp only [Pi.single_eq_same]
  · intro j _ hji
    simp [Pi.single_apply, hji, Ne.symm hji]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- The literal alternating coordinate vector in the full Euler source. -/
def coordinatePair (p q : I) (U : (X).Opens) :
    Γ(positiveEulerSource (I := I) (K := K), U) :=
  coordinateSingle q U (coordinateSection p U) -
    coordinateSingle p U (coordinateSection q U)

/-- The relation is checked as an identity of actual twisting-sheaf sections. -/
theorem coordinatePair_mem_kernel (p q : I) (U : (X).Opens) :
    (eulerMap (I := I) (K := K) 2).app U (coordinatePair p q U) = 0 := by
  rw [coordinatePair, map_sub, eulerMap_coordinateSingle, eulerMap_coordinateSingle]
  apply Proj.twistingSheaf.ext
  intro x
  change (coordinateSection q U).val x * (coordinateSection p U).val x -
    (coordinateSection p U).val x * (coordinateSection q U).val x = 0
  ring

/-- The actual global Euler-kernel section represented by `x_p e_q-x_q e_p`. -/
def coordinateWedge (p q : I) (U : (X).Opens) :
    Γ(eulerKernel (I := I) (K := K) 2, U) :=
  (kernelSectionsEquiv 2 U).symm
    ⟨coordinatePair p q U, coordinatePair_mem_kernel p q U⟩

@[simp]
theorem coordinateWedge_image (p q : I) (U : (X).Opens) :
    (kernel.ι (eulerMap (I := I) (K := K) 2)).app U (coordinateWedge p q U) =
      coordinatePair p q U := by
  rw [← kernelSectionsEquiv_val, coordinateWedge, LinearEquiv.apply_symm_apply]

section Functional

variable {M : (Proj (MvPolynomial.homogeneousSubmodule I K)).Modules}

/-- The complete coefficient map on the actual Euler source. -/
def coefficientMap (c : I → (O1 ⟶ M)) :
    positiveEulerSource (I := I) (K := K) ⟶ M :=
  ∑ i, Pi.π (fun _ : I => O1) i ≫ c i

/-- The coefficient family restricted to the actual Euler kernel. -/
def criticalFunctional (c : I → (O1 ⟶ M)) :
    eulerKernel (I := I) (K := K) 2 ⟶ M :=
  kernel.ι (eulerMap 2) ≫ coefficientMap c

theorem coefficientMap_app (c : I → (O1 ⟶ M)) (U : (X).Opens)
    (s : Γ(positiveEulerSource (I := I) (K := K), U)) :
    (coefficientMap c).app U s =
      ∑ i, (c i).app U (productSectionsEquiv (fun _ : I => O1) U s i) := by
  let F := Scheme.Modules.sectionsFunctor U
  letI : F.Additive := by
    refine ⟨?_⟩
    intro M N f g
    rfl
  change (F.map (∑ i, Pi.π (fun _ : I => O1) i ≫ c i)).hom s = _
  rw [Functor.map_sum, ModuleCat.hom_sum, LinearMap.sum_apply]
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply,
    productSectionsEquiv_apply]
  rfl

@[simp]
theorem coefficientMap_coordinateSingle (c : I → (O1 ⟶ M))
    (i : I) (U : (X).Opens) (s : Γ(O1, U)) :
    (coefficientMap c).app U (coordinateSingle i U s) = (c i).app U s := by
  erw [coefficientMap_app]
  simp only [coordinateSingle_component]
  rw [Finset.sum_eq_single i]
  · simp only [Pi.single_eq_same]
  · intro j _ hji
    simp [Pi.single_apply, hji, Ne.symm hji]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- The actual critical equation on an actual coordinate wedge, in every characteristic. -/
theorem criticalFunctional_coordinateWedge (c : I → (O1 ⟶ M))
    (p q : I) (U : (X).Opens) :
    (criticalFunctional c).app U (coordinateWedge p q U) =
      (c q).app U (coordinateSection p U) -
        (c p).app U (coordinateSection q U) := by
  change (coefficientMap c).app U
    ((kernel.ι (eulerMap 2)).app U (coordinateWedge p q U)) = _
  rw [coordinateWedge_image, coordinatePair, map_sub,
    coefficientMap_coordinateSingle, coefficientMap_coordinateSingle]

end Functional

section Pullback

variable {Y : Scheme.{u}}
  (f : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule I K)) {N : Y.Modules}

/-- Coefficient morphisms on a genuine source scheme, with the actual pulled-back domain. -/
def pullbackCoefficientMap (c : I → ((Scheme.Modules.pullback f).obj O1 ⟶ N)) :
    (Scheme.Modules.pullback f).obj (positiveEulerSource (I := I) (K := K)) ⟶ N :=
  ∑ i, (Scheme.Modules.pullback f).map (Pi.π (fun _ : I => O1) i) ≫ c i

/-- The actual critical functional on the pulled-back Euler kernel. -/
def pullbackCriticalFunctional (c : I → ((Scheme.Modules.pullback f).obj O1 ⟶ N)) :
    (Scheme.Modules.pullback f).obj (eulerKernel (I := I) (K := K) 2) ⟶ N :=
  (Scheme.Modules.pullback f).map (kernel.ι (eulerMap 2)) ≫ pullbackCoefficientMap f c

/-- The map commutes with genuine pullback of each full Euler-source section. -/
theorem pullbackCoefficientMap_app (c : I → ((Scheme.Modules.pullback f).obj O1 ⟶ N))
    (U : (X).Opens) (V : Y.Opens) (hV : V ≤ f ⁻¹ᵁ U)
    (s : Γ(positiveEulerSource (I := I) (K := K), U)) :
    (pullbackCoefficientMap f c).app V
      (f.pullbackSectionsLE positiveEulerSource U V hV s) =
      ∑ i, (c i).app V (f.pullbackSectionsLE O1 U V hV
        (productSectionsEquiv (fun _ : I => O1) U s i)) := by
  let E := Scheme.Modules.sectionsFunctor V
  letI : E.Additive := by
    refine ⟨?_⟩
    intro M N f g
    rfl
  change (E.map (∑ i, (Scheme.Modules.pullback f).map (Pi.π (fun _ : I => O1) i) ≫ c i)).hom
    (f.pullbackSectionsLE positiveEulerSource U V hV s) = _
  rw [Functor.map_sum, ModuleCat.hom_sum, LinearMap.sum_apply]
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro i _
  erw [f.pullbackSectionsLE_naturality positiveEulerSource U V hV
    (Pi.π (fun _ : I => O1) i) s]
  erw [productSectionsEquiv_apply]
  rfl

@[simp]
theorem pullbackCoefficientMap_coordinateSingle
    (c : I → ((Scheme.Modules.pullback f).obj O1 ⟶ N))
    (i : I) (U : (X).Opens) (V : Y.Opens) (hV : V ≤ f ⁻¹ᵁ U) (s : Γ(O1, U)) :
    (pullbackCoefficientMap f c).app V
      (f.pullbackSectionsLE positiveEulerSource U V hV (coordinateSingle i U s)) =
        (c i).app V (f.pullbackSectionsLE O1 U V hV s) := by
  rw [pullbackCoefficientMap_app]
  simp only [coordinateSingle_component]
  rw [Finset.sum_eq_single i]
  · simp only [Pi.single_eq_same]
  · intro j _ hji
    simp [Pi.single_apply, hji, Ne.symm hji]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- On every smaller pullback chart the actual sheaf map is exactly the
coordinate contraction-proportionality expression, with its literal sign. -/
theorem pullbackCriticalFunctional_coordinateWedge
    (c : I → ((Scheme.Modules.pullback f).obj O1 ⟶ N))
    (p q : I) (U : (X).Opens) (V : Y.Opens) (hV : V ≤ f ⁻¹ᵁ U) :
    (pullbackCriticalFunctional f c).app V
      (f.pullbackSectionsLE (eulerKernel 2) U V hV (coordinateWedge p q U)) =
      (c q).app V (f.pullbackSectionsLE O1 U V hV (coordinateSection p U)) -
        (c p).app V (f.pullbackSectionsLE O1 U V hV (coordinateSection q U)) := by
  change (pullbackCoefficientMap f c).app V
    (((Scheme.Modules.pullback f).map (kernel.ι (eulerMap 2))).app V
      (f.pullbackSectionsLE (eulerKernel 2) U V hV (coordinateWedge p q U))) = _
  have hι :
      (((Scheme.Modules.pullback f).map (kernel.ι (eulerMap 2))).app V
        (f.pullbackSectionsLE (eulerKernel 2) U V hV (coordinateWedge p q U))) =
      f.pullbackSectionsLE positiveEulerSource U V hV (coordinatePair p q U) :=
    (f.pullbackSectionsLE_naturality (eulerKernel 2) U V hV
      (kernel.ι (eulerMap 2)) (coordinateWedge p q U)).trans
        (congrArg (f.pullbackSectionsLE positiveEulerSource U V hV)
          (coordinateWedge_image p q U))
  refine (congrArg ((pullbackCoefficientMap f c).app V) hι).trans ?_
  calc
    (pullbackCoefficientMap f c).app V
        (f.pullbackSectionsLE positiveEulerSource U V hV (coordinatePair p q U)) =
      (pullbackCoefficientMap f c).app V
          (f.pullbackSectionsLE positiveEulerSource U V hV
            (coordinateSingle q U (coordinateSection p U))) -
        (pullbackCoefficientMap f c).app V
          (f.pullbackSectionsLE positiveEulerSource U V hV
            (coordinateSingle p U (coordinateSection q U))) := by
      change (pullbackCoefficientMap f c).app V
        (f.pullbackSectionsLE positiveEulerSource U V hV
          (coordinateSingle q U (coordinateSection p U) -
            coordinateSingle p U (coordinateSection q U))) = _
      rw [map_sub, map_sub]
    _ = _ := congrArg₂ (fun a b : Γ(N, V) => a - b)
      (pullbackCoefficientMap_coordinateSingle f c q U V hV (coordinateSection p U))
      (pullbackCoefficientMap_coordinateSingle f c p U V hV (coordinateSection q U))

end Pullback
end PaperVerification.Segre.EulerCriticalFunctional

end SegreEulerCriticalFunctional

run_cmd do
  (← IO.getStdout).flush
  let out ← IO.getStderr
  out.putStrLn "SEGRE_PROGRESS Stage027.CriticalEuler critical-functional"
  out.flush

section SegreEulerCriticalChart

/-!
# Actual chart coordinates for the Euler-kernel critical functional

On every open contained in a standard projective chart, the genuine twisting
sheaves have their canonical local-fraction trivializations. These give an
explicit equivalence from the sections of the actual Euler kernel to the
kernel of the coordinate dot product over the actual ring of sections.

The restricted coefficient map then has image exactly the ideal generated by
its normalized contraction-proportionality equations. Neither the kernel
comparison nor the image identity is an assumption.

Tensor-specific global coefficient morphisms and finite-product assembly
are developed in later sections and used by the final span argument.
-/

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

namespace PaperVerification.Segre.EulerCriticalChart

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open ProjectiveCech EulerSheaf EulerSections EulerCriticalFunctional
open scoped BigOperators

universe u
variable {I K : Type u} [Fintype I] [DecidableEq I] [Field K]

local notation "𝒜" => MvPolynomial.homogeneousSubmodule I K
local notation "X" => Proj (MvPolynomial.homogeneousSubmodule I K)
local notation "O1" => Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule I K) (1 : ℤ)

variable (p : I) (U : (Proj (MvPolynomial.homogeneousSubmodule I K)).Opens) (hU : U ≤ coordinateOpen (K := K) p)

/-- The chart coordinate map has its literal local-fraction value. -/
theorem chartTrivialization_apply_apply (t : ℤ) (a : Γ(X, U)) (x : U) :
    (chartTrivialization p U hU t a).val x =
      (a.val x).val *
        (Proj.twistingSheaf.chartGenerator t (MvPolynomial.X p)
          (MvPolynomial.isHomogeneous_X (R := K) p) U hU).val x :=
  Proj.twistingSheaf.chartSectionsLinearEquiv_apply_apply t (MvPolynomial.X p)
    (MvPolynomial.isHomogeneous_X (R := K) p) U hU a x

/-- Multiplication in the structure sheaf is multiplication in each localization. -/
theorem structureSection_mul_apply (a b : Γ(X, U)) (x : U) :
    ((a * b).val x).val = (a.val x).val * (b.val x).val :=
  HomogeneousLocalization.val_mul _ _

/-- The local trivialization respects the literal multiplication of degree-one sections. -/
theorem chartTrivialization_mul (a b : Γ(X, U)) :
    Proj.twistingSheaf.mul 𝒜 U 1 1
      (chartTrivialization p U hU 1 a) (chartTrivialization p U hU 1 b) =
        chartTrivialization p U hU 2 (a * b) := by
  apply Proj.twistingSheaf.ext
  intro x
  let G (t : ℤ) := (Proj.twistingSheaf.chartGenerator («𝒜» := 𝒜) t (MvPolynomial.X p)
    (MvPolynomial.isHomogeneous_X (R := K) p) U hU).val x
  have hG : G 1 * G 1 = G 2 :=
    Proj.twistingSheaf.mul_chartGenerator_apply («𝒜» := 𝒜) (1 : ℤ) (MvPolynomial.X p)
      (MvPolynomial.isHomogeneous_X (R := K) p) U hU 1 x
  erw [Proj.twistingSheaf.mul_apply, chartTrivialization_apply_apply,
    chartTrivialization_apply_apply, chartTrivialization_apply_apply]
  erw [structureSection_mul_apply]
  change ((a.val x).val * G 1) * ((b.val x).val * G 1) =
    ((a.val x).val * (b.val x).val) * G 2
  rw [← hG]
  ring

/-- Coordinate multiplication becomes multiplication by the actual coordinate ratio. -/
theorem normalized_coordinateMul (i : I) (s : Γ(O1, U)) :
    (chartTrivialization p U hU 2).symm (coordinateMulSections i 2 U s) =
      normalizedCoordinate p U hU i * (chartTrivialization p U hU 1).symm s := by
  apply (chartTrivialization p U hU 2).injective
  rw [LinearEquiv.apply_symm_apply, ← chartTrivialization_mul]
  rw [normalizedCoordinate, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]
  rfl

/-- Full product-section coordinates in the actual local trivialization. -/
def chartSourceEquiv :
    Γ(positiveEulerSource (I := I) (K := K), U) ≃ₗ[Γ(X, U)] (I → Γ(X, U)) :=
  (productSectionsEquiv (fun _ : I => O1) U).trans
    (LinearEquiv.piCongrRight (fun _ : I => (chartTrivialization p U hU 1).symm))

@[simp]
theorem chartSourceEquiv_apply
    (s : Γ(positiveEulerSource (I := I) (K := K), U)) (i : I) :
    chartSourceEquiv p U hU s i = (chartTrivialization p U hU 1).symm
      (productSectionsEquiv (fun _ : I => O1) U s i) := rfl

/-- The actual normalized Euler dot product over the chart ring. -/
def normalizedEuler : (I → Γ(X, U)) →ₗ[Γ(X, U)] Γ(X, U) where
  toFun a := ∑ i, normalizedCoordinate p U hU i * a i
  map_add' a b := by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a v := by
    change (∑ i, normalizedCoordinate p U hU i * (a * v i)) =
      a * ∑ i, normalizedCoordinate p U hU i * v i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- The genuine Euler map is intertwined with the literal coordinate dot product. -/
theorem euler_chart_commutes
    (s : Γ(positiveEulerSource (I := I) (K := K), U)) :
    normalizedEuler p U hU (chartSourceEquiv p U hU s) =
      (chartTrivialization p U hU 2).symm ((eulerMap 2).app U s) := by
  change (∑ i, normalizedCoordinate p U hU i *
    (chartTrivialization p U hU 1).symm
      (productSectionsEquiv (fun _ : I => O1) U s i)) = _
  rw [eulerMap_app, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (normalized_coordinateMul p U hU i _).symm

/-- The full section kernel is transported to the exact normalized Euler kernel. -/
theorem map_kernel_eq_normalized :
    (LinearMap.ker ((eulerMap (I := I) (K := K) 2).val.app (op U)).hom).map
      (chartSourceEquiv p U hU).toLinearMap = LinearMap.ker (normalizedEuler p U hU) := by
  ext a
  constructor
  · rintro ⟨s, hs, rfl⟩
    change normalizedEuler p U hU (chartSourceEquiv p U hU s) = 0
    rw [euler_chart_commutes]
    change (eulerMap 2).app U s = 0 at hs
    rw [hs, map_zero]
  · intro ha
    refine ⟨(chartSourceEquiv p U hU).symm a, ?_,
      (chartSourceEquiv p U hU).apply_symm_apply a⟩
    change (eulerMap 2).app U ((chartSourceEquiv p U hU).symm a) = 0
    apply (chartTrivialization p U hU 2).symm.injective
    rw [map_zero, ← euler_chart_commutes, LinearEquiv.apply_symm_apply]
    exact ha

/-- Actual Euler-kernel sections, with no comparison-equivalence premise. -/
def chartKernelEquiv :
    Γ(eulerKernel (I := I) (K := K) 2, U) ≃ₗ[Γ(X, U)]
      LinearMap.ker (normalizedEuler p U hU) :=
  (kernelSectionsEquiv 2 U).trans
    ((chartSourceEquiv p U hU).ofSubmodules _ _ (map_kernel_eq_normalized p U hU))

@[simp]
theorem chartKernelEquiv_val (s : Γ(eulerKernel (I := I) (K := K) 2, U)) :
    (chartKernelEquiv p U hU s).val =
      chartSourceEquiv p U hU ((kernel.ι (eulerMap 2)).app U s) := by
  dsimp only [chartKernelEquiv, LinearEquiv.trans_apply]
  erw [LinearEquiv.ofSubmodules_apply, kernelSectionsEquiv_val]

section CriticalCoefficients

variable (t : ℤ)
  (c : I → (Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule I K) (1 : ℤ) ⟶
    Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule I K) t))

/-- The actual coefficient of a sheaf morphism in the canonical local trivializations. -/
def normalizedCoefficient (i : I) : Γ(X, U) :=
  (chartTrivialization p U hU t).symm
    ((c i).app U (chartTrivialization p U hU 1 (1 : Γ(X, U))))

/-- Every section map is multiplication by its literal normalized coefficient. -/
theorem normalized_coefficient_app (i : I) (s : Γ(O1, U)) :
    (chartTrivialization p U hU t).symm ((c i).app U s) =
      (chartTrivialization p U hU 1).symm s * normalizedCoefficient p U hU t c i := by
  have hs : s = (chartTrivialization p U hU 1).symm s •
      chartTrivialization p U hU 1 (1 : Γ(X, U)) := by
    rw [← _root_.map_smul, smul_eq_mul, mul_one, LinearEquiv.apply_symm_apply]
  conv_lhs => rw [hs]
  rw [Scheme.Modules.Hom.app_smul, _root_.map_smul]
  rfl

/-- The critical functional on actual kernel sections, with the actual codomain trivialized. -/
def normalizedCriticalMap :
    Γ(eulerKernel (I := I) (K := K) 2, U) →ₗ[Γ(X, U)] Γ(X, U) :=
  (chartTrivialization p U hU t).symm.toLinearMap.comp ((criticalFunctional c).val.app (op U)).hom

/-- Exact coordinate formula on every actual Euler-kernel section. -/
theorem normalizedCriticalMap_apply (s : Γ(eulerKernel (I := I) (K := K) 2, U)) :
    normalizedCriticalMap p U hU t c s =
      ∑ i, (chartKernelEquiv p U hU s).val i * normalizedCoefficient p U hU t c i := by
  change (chartTrivialization p U hU t).symm
    ((coefficientMap c).app U ((kernel.ι (eulerMap 2)).app U s)) = _
  rw [coefficientMap_app, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [normalized_coefficient_app, chartKernelEquiv_val, chartSourceEquiv_apply]

/-- The literal chart critical equations. The pivot equation is automatically zero. -/
def criticalCoordinate (i : I) : Γ(X, U) :=
  normalizedCoefficient p U hU t c i -
    normalizedCoordinate p U hU i * normalizedCoefficient p U hU t c p

/-- Each chart critical equation is the value on an actual coordinate-wedge section. -/
theorem normalizedCriticalMap_coordinateWedge (i : I) :
    normalizedCriticalMap p U hU t c (coordinateWedge p i U) =
      criticalCoordinate p U hU t c i := by
  change (chartTrivialization p U hU t).symm
    ((criticalFunctional c).app U (coordinateWedge p i U)) = _
  rw [criticalFunctional_coordinateWedge, map_sub,
    normalized_coefficient_app, normalized_coefficient_app]
  change normalizedCoordinate p U hU p * normalizedCoefficient p U hU t c i -
    normalizedCoordinate p U hU i * normalizedCoefficient p U hU t c p = _
  rw [normalizedCoordinate_pivot, one_mul]
  rfl

/-- Every value is the explicit linear combination of the actual chart equations. -/
theorem normalizedCriticalMap_eq_sum_criticalCoordinates
    (s : Γ(eulerKernel (I := I) (K := K) 2, U)) :
    normalizedCriticalMap p U hU t c s =
      ∑ i, (chartKernelEquiv p U hU s).val i * criticalCoordinate p U hU t c i := by
  rw [normalizedCriticalMap_apply]
  have hz := (chartKernelEquiv p U hU s).property
  change (∑ i, normalizedCoordinate p U hU i *
    (chartKernelEquiv p U hU s).val i) = 0 at hz
  simp only [criticalCoordinate, mul_sub, Finset.sum_sub_distrib]
  have hsum : (∑ i, (chartKernelEquiv p U hU s).val i *
      (normalizedCoordinate p U hU i * normalizedCoefficient p U hU t c p)) = 0 := by
    calc
      _ = (∑ i, normalizedCoordinate p U hU i *
          (chartKernelEquiv p U hU s).val i) * normalizedCoefficient p U hU t c p := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := by rw [hz, zero_mul]
  rw [hsum, sub_zero]

/-- The image of the genuine kernel functional is exactly the ideal generated by
all normalized critical equations on the chart. This is an equality of full
submodules over the actual structure-sheaf ring, not a pointwise zero-set assertion. -/
theorem normalizedCriticalMap_range :
    LinearMap.range (normalizedCriticalMap p U hU t c) =
      Submodule.span Γ(X, U) (Set.range (criticalCoordinate p U hU t c)) := by
  apply le_antisymm
  · rintro y ⟨s, rfl⟩
    rw [normalizedCriticalMap_eq_sum_criticalCoordinates]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ ((chartKernelEquiv p U hU s).val i)
      (Submodule.subset_span (Set.mem_range_self i))
  · apply Submodule.span_le.mpr
    rintro y ⟨i, rfl⟩
    exact ⟨coordinateWedge p i U, normalizedCriticalMap_coordinateWedge p U hU t c i⟩

end CriticalCoefficients
end PaperVerification.Segre.EulerCriticalChart

end SegreEulerCriticalChart

run_cmd do
  (← IO.getStdout).flush
  let out ← IO.getStderr
  out.putStrLn "SEGRE_PROGRESS Stage027.CriticalEuler critical-chart"
  out.flush

section SegreEulerContractionChart

/-!
# The actual Euler contraction in every twisting chart

Every integer twist of the coordinate Euler map has the same normalized
functional over the genuine ring of sections of a standard chart. The
comparison intertwines the full coefficient-valued exterior differential
in every degree, not merely its kernel dimension or its value on a
distinguished vector. In particular, the positive and negative Euler
complexes have the same literal local matrices after the appropriate
line-bundle frames are applied.

All source and coefficient frames below are the actual local-fraction
trivializations. No comparison or exactness hypothesis is assumed.
-/

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

namespace PaperVerification.Segre.EulerContractionChart

open AlgebraicGeometry CategoryTheory Limits Opposite
open EulerSheaf EulerSections EulerCriticalChart
open scoped TensorProduct BigOperators

universe u
variable {I K : Type u} [Fintype I] [DecidableEq I] [Field K]

local notation "𝒜" => MvPolynomial.homogeneousSubmodule I K
local notation "X" => Proj (MvPolynomial.homogeneousSubmodule I K)

variable (j : I) (U : (Proj (MvPolynomial.homogeneousSubmodule I K)).Opens)
  (hU : U ≤ ProjectiveCech.coordinateOpen (K := K) j)

/-- The genuine chart frame respects multiplication for all integer degrees. -/
theorem chartTrivialization_mul_all (m n : ℤ) (a b : Γ(X, U)) :
    Proj.twistingSheaf.mul 𝒜 U m n
        (chartTrivialization j U hU m a)
        (chartTrivialization j U hU n b) =
      chartTrivialization j U hU (m + n) (a * b) := by
  apply Proj.twistingSheaf.ext
  intro x
  let G (d : ℤ) := (Proj.twistingSheaf.chartGenerator d (MvPolynomial.X j)
    (MvPolynomial.isHomogeneous_X (R := K) j) U hU).val x
  have hG : G m * G n = G (m + n) :=
    Proj.twistingSheaf.mul_chartGenerator_apply n (MvPolynomial.X j)
      (MvPolynomial.isHomogeneous_X (R := K) j) U hU m x
  erw [Proj.twistingSheaf.mul_apply, chartTrivialization_apply_apply,
    chartTrivialization_apply_apply, chartTrivialization_apply_apply]
  erw [structureSection_mul_apply]
  change ((a.val x).val * G m) * ((b.val x).val * G n) =
    ((a.val x).val * (b.val x).val) * G (m + n)
  rw [← hG]
  ring

/-- Coordinate multiplication has the same actual coordinate ratio at
every twist, including the negative Euler source. -/
theorem normalized_coordinateMul_all (t : ℤ) (i : I)
    (s : Γ(Proj.twistingSheaf 𝒜 (t - 1), U)) :
    (chartTrivialization j U hU t).symm
        (coordinateMulSections i t U s) =
      normalizedCoordinate j U hU i *
        (chartTrivialization j U hU (t - 1)).symm s := by
  apply (chartTrivialization j U hU t).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Proj.twistingSheaf.ext
  intro x
  let G (d : ℤ) := (Proj.twistingSheaf.chartGenerator d (MvPolynomial.X j)
    (MvPolynomial.isHomogeneous_X (R := K) j) U hU).val x
  have hG : G 1 * G (t - 1) = G t := by
    have h := Proj.twistingSheaf.mul_chartGenerator_apply (t - 1)
      (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X (R := K) j) U hU 1 x
    change G 1 * G (t - 1) = G (1 + (t - 1)) at h
    simpa only [show (1 : ℤ) + (t - 1) = t by omega] using h
  have hi := congrArg
    (fun z : Γ(Proj.twistingSheaf 𝒜 1, U) => z.val x)
    ((chartTrivialization j U hU 1).apply_symm_apply (coordinateSection i U))
  have hs := congrArg
    (fun z : Γ(Proj.twistingSheaf 𝒜 (t - 1), U) => z.val x)
    ((chartTrivialization j U hU (t - 1)).apply_symm_apply s)
  change (coordinateSection i U).val x * s.val x = _
  rw [← hi, ← hs]
  erw [chartTrivialization_apply_apply, chartTrivialization_apply_apply,
    chartTrivialization_apply_apply]
  erw [structureSection_mul_apply]
  change (((normalizedCoordinate j U hU i).val x).val * G 1) *
      ((((chartTrivialization j U hU (t - 1)).symm s).val x).val * G (t - 1)) =
    (((normalizedCoordinate j U hU i).val x).val *
      (((chartTrivialization j U hU (t - 1)).symm s).val x).val) * G t
  rw [← hG]
  ring

/-- The complete coordinate source frame, in the forward direction. -/
def sourceFrame (t : ℤ) :
    (I → Γ(X, U)) ≃ₗ[Γ(X, U)]
      Γ((∏ᶜ fun _ : I => Proj.twistingSheaf 𝒜 (t - 1)), U) :=
  (LinearEquiv.piCongrRight
    (fun _ : I => chartTrivialization j U hU (t - 1))).trans
      (productSectionsEquiv
        (fun _ : I => Proj.twistingSheaf 𝒜 (t - 1)) U).symm

@[simp]
theorem sourceFrame_component (t : ℤ) (v : I → Γ(X, U)) (i : I) :
    productSectionsEquiv (fun _ : I => Proj.twistingSheaf 𝒜 (t - 1)) U
      (sourceFrame j U hU t v) i =
        chartTrivialization j U hU (t - 1) (v i) := by
  exact congrFun (LinearEquiv.apply_symm_apply _ _) i

/-- The whole actual Euler map is conjugate to the same normalized dot
product, for every integer twist. -/
theorem eulerMap_in_frame (t : ℤ) (v : I → Γ(X, U)) :
    (chartTrivialization j U hU t).symm
      ((eulerMap (I := I) (K := K) t).app U (sourceFrame j U hU t v)) =
        normalizedEuler j U hU v := by
  rw [eulerMap_app, map_sum]
  change (∑ i, (chartTrivialization j U hU t).symm
    (coordinateMulSections i t U
      (productSectionsEquiv (fun _ : I => Proj.twistingSheaf 𝒜 (t - 1)) U
        (sourceFrame j U hU t v) i))) =
    ∑ i, normalizedCoordinate j U hU i * v i
  apply Finset.sum_congr rfl
  intro i _
  rw [normalized_coordinateMul_all, sourceFrame_component,
    LinearEquiv.symm_apply_apply]

/-- The corresponding complete source frame on each actual exterior module. -/
def exteriorSourceFrame (t : ℤ) (r : ℕ) :
    (⋀[Γ(X, U)]^r (I → Γ(X, U))) ≃ₗ[Γ(X, U)]
      ⋀[Γ(X, U)]^r
        Γ((∏ᶜ fun _ : I => Proj.twistingSheaf 𝒜 (t - 1)), U) :=
  LinearEquiv.ofBijective
    (exteriorPower.map r (sourceFrame j U hU t).toLinearMap)
    (exteriorPower.map_bijective (sourceFrame j U hU t).bijective)

@[simp]
theorem exteriorSourceFrame_ιMulti (t : ℤ) (r : ℕ)
    (v : Fin r → I → Γ(X, U)) :
    exteriorSourceFrame j U hU t r (exteriorPower.ιMulti Γ(X, U) r v) =
      exteriorPower.ιMulti Γ(X, U) r (fun i => sourceFrame j U hU t (v i)) :=
  exteriorPower.map_apply_ιMulti _ _

/-- Normalize both the exterior source factor and the actual coefficient line. -/
def targetFrame (t : ℤ) (r : ℕ) :
    ((⋀[Γ(X, U)]^r
      Γ((∏ᶜ fun _ : I => Proj.twistingSheaf 𝒜 (t - 1)), U)) ⊗[Γ(X, U)]
        Γ(Proj.twistingSheaf 𝒜 t, U)) ≃ₗ[Γ(X, U)]
      ⋀[Γ(X, U)]^r (I → Γ(X, U)) :=
  (CoefficientKernel.tensorCoefficientEquiv
    (chartTrivialization j U hU t).symm r).trans
      (exteriorSourceFrame j U hU t r).symm

/-- The full differential has exactly the same normalized Koszul matrix
at every twist. This is equality of the actual whole linear maps. -/
theorem contraction_in_frame (t : ℤ) (r : ℕ) :
    (targetFrame j U hU t r).toLinearMap ∘ₗ
      CoefficientContraction.contraction (R := Γ(X, U))
        ((eulerMap (I := I) (K := K) t).val.app (op U)).hom r ∘ₗ
          (exteriorSourceFrame j U hU t (r + 1)).toLinearMap =
      TauCeti.koszulDifferential (normalizedEuler j U hU) r := by
  let φ : Γ((∏ᶜ fun _ : I => Proj.twistingSheaf 𝒜 (t - 1)), U) →ₗ[Γ(X, U)]
      Γ(Proj.twistingSheaf 𝒜 t, U) :=
    ((eulerMap (I := I) (K := K) t).val.app (op U)).hom
  let c := (chartTrivialization j U hU t).symm
  have hφ : CoefficientKernel.normalizedFunctional c φ ∘ₗ
      (sourceFrame j U hU t).toLinearMap = normalizedEuler j U hU := by
    apply LinearMap.ext
    intro v
    exact eulerMap_in_frame j U hU t v
  have hδ := TauCeti.koszulDifferential_comp_map
    (normalizedEuler j U hU) hφ r
  apply LinearMap.ext
  intro z
  change (exteriorSourceFrame j U hU t r).symm
    (CoefficientKernel.tensorCoefficientEquiv c r
      (CoefficientContraction.contraction φ r
        (exteriorSourceFrame j U hU t (r + 1) z))) =
      TauCeti.koszulDifferential (normalizedEuler j U hU) r z
  have hn := LinearMap.congr_fun
    (CoefficientKernel.normalize_contraction c φ r)
      (exteriorSourceFrame j U hU t (r + 1) z)
  change CoefficientKernel.tensorCoefficientEquiv c r
      (CoefficientContraction.contraction φ r
        (exteriorSourceFrame j U hU t (r + 1) z)) =
    TauCeti.koszulDifferential (CoefficientKernel.normalizedFunctional c φ) r
      (exteriorSourceFrame j U hU t (r + 1) z) at hn
  have hz := LinearMap.congr_fun hδ z
  change TauCeti.koszulDifferential (CoefficientKernel.normalizedFunctional c φ) r
      (exteriorSourceFrame j U hU t (r + 1) z) =
    exteriorSourceFrame j U hU t r
      (TauCeti.koszulDifferential (normalizedEuler j U hU) r z) at hz
  exact (congrArg (exteriorSourceFrame j U hU t r).symm hn).trans
    ((congrArg (exteriorSourceFrame j U hU t r).symm hz).trans
      ((exteriorSourceFrame j U hU t r).symm_apply_apply _))

/-- In particular, the positive and negative Euler differentials retain
identical complete matrices after their actual coefficient frames. -/
theorem positive_negative_contraction_same_matrix (r : ℕ) :
    (targetFrame j U hU 2 r).toLinearMap ∘ₗ
      CoefficientContraction.contraction (R := Γ(X, U))
        ((eulerMap (I := I) (K := K) 2).val.app (op U)).hom r ∘ₗ
          (exteriorSourceFrame j U hU 2 (r + 1)).toLinearMap =
    (targetFrame j U hU 0 r).toLinearMap ∘ₗ
      CoefficientContraction.contraction (R := Γ(X, U))
        ((eulerMap (I := I) (K := K) 0).val.app (op U)).hom r ∘ₗ
          (exteriorSourceFrame j U hU 0 (r + 1)).toLinearMap := by
  exact (contraction_in_frame j U hU 2 r).trans
    (contraction_in_frame j U hU 0 r).symm

end PaperVerification.Segre.EulerContractionChart

end SegreEulerContractionChart

run_cmd do
  (← IO.getStdout).flush
  let out ← IO.getStderr
  out.putStrLn "SEGRE_PROGRESS Stage027.CriticalEuler contraction-chart"
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
