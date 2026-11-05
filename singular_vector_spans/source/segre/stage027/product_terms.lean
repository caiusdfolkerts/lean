module
public import SegreVerified.Stage027.ExteriorComparison
public import SegreVerified.Stage027.TensorSections
public import SegreVerified.Stage027.KoszulTerms
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

run_cmd do
  let out ← IO.getStderr
  out.putStrLn "SEGRE_STAGE Stage027.ProductTerms"
  out.flush

/-!
# The actual critical bundle and its weighted Koszul complex

The named sections preserve the original proof stages and local scopes.
-/

set_option autoImplicit false

section SegreSchemeProductSections

namespace PaperVerification.Segre.SchemeProductSections

open CategoryTheory Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules

universe u v
variable {X : Scheme.{max u v}}

local instance : HasLimitsOfSize.{u, u} X.Modules := hasLimitsOfSizeShrink.{u, u} _

/-- Taking sections of the actual product sheaf gives the product of the
section modules, on an arbitrary scheme. -/
def productSectionsEquiv {J : Type u} (M : J → X.Modules) (U : X.Opens) :
    Γ((∏ᶜ M), U) ≃ₗ[Γ(X, U)] ((j : J) → Γ(M j, U)) :=
  ((PreservesProduct.iso (SheafOfModules.evaluation X.ringCatSheaf (op U)) M) ≪≫
    ModuleCat.piIsoPi
      (fun j => (SheafOfModules.evaluation X.ringCatSheaf (op U)).obj (M j))).toLinearEquiv

/-- Each coordinate of the section comparison is the original sheaf
product projection. -/
@[simp] theorem productSectionsEquiv_apply {J : Type u}
    (M : J → X.Modules) (U : X.Opens) (s : Γ((∏ᶜ M), U)) (j : J) :
    productSectionsEquiv M U s j = (Pi.π M j).app U s := by
  have he :
      ((PreservesProduct.iso (SheafOfModules.evaluation X.ringCatSheaf (op U)) M) ≪≫
        ModuleCat.piIsoPi
          (fun j => (SheafOfModules.evaluation X.ringCatSheaf (op U)).obj (M j))).hom ≫
        ModuleCat.ofHom (LinearMap.proj j) =
      (SheafOfModules.evaluation X.ringCatSheaf (op U)).map (Pi.π M j) := by
    simp only [Iso.trans_hom, Category.assoc, ModuleCat.piIsoPi_hom_ker_subtype]
    exact piComparison_comp_π (SheafOfModules.evaluation X.ringCatSheaf (op U)) M j
  exact ConcreteCategory.congr_hom he s

/-- The actual product-section coordinates commute with restrictions. -/
theorem productSectionsEquiv_res {J : Type u} (M : J → X.Modules)
    {U V : X.Opens} (i : V ⟶ U) (s : Γ((∏ᶜ M), U)) (j : J) :
    productSectionsEquiv M V ((∏ᶜ M).presheaf.map i.op s) j =
      (M j).presheaf.map i.op (productSectionsEquiv M U s j) := by
  rw [productSectionsEquiv_apply, productSectionsEquiv_apply]
  exact PresheafOfModules.naturality_apply (Pi.π M j).val i.op s

/-- Finite products of quasicoherent modules are quasicoherent, allowing
the finite index type to lie in a smaller universe than the scheme. -/
theorem finiteProduct_quasicoherent {J : Type u} [Finite J]
    (M : J → X.Modules) [∀ j, (M j).IsQuasicoherent] :
    (∏ᶜ M).IsQuasicoherent := by
  classical
  letI : Fintype J := Fintype.ofFinite J
  letI : HasBiproduct M := HasBiproduct.of_hasProduct M
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((biproduct.isoCoproduct M).symm ≪≫ biproduct.isoProduct M)
    (inferInstanceAs (∐ M).IsQuasicoherent)

end PaperVerification.Segre.SchemeProductSections

end SegreSchemeProductSections

section SegreTensorCriticalMap

/-!
# Full tensor coefficients as actual morphisms

The coefficient attached to a factor and a coordinate is the literal sum
over all tensor entries with that coordinate. Its source is that factor,
and its target is the actual finite tensor product. The coordinate-wedge
expression is proved as an equality of actual morphisms, with every tensor
entry present. Specialization to scalar endomorphisms of twisting sheaves
supplies the global singular-vector functional.

-/

set_option autoImplicit false

namespace PaperVerification.Segre.TensorCriticalMap

open CategoryTheory MonoidalCategory
open scoped BigOperators

universe u v w
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
variable {k : ℕ} (M : Fin k → C) (ι : Fin k → Type w)
variable [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
variable (s : (i : Fin k) → ι i → (𝟙_ C ⟶ M i))

/-- The actual full tensor index, with no truncation of its coordinates. -/
abbrev TensorIndex := (i : Fin k) → ι i

/-- The literal tensor coordinate section. -/
def tensorCoordinate (a : TensorIndex ι) : 𝟙_ C ⟶ FiniteTensor.tensorObj M :=
  FiniteTensor.sectionMap M (fun i => s i (a i))

/-- Insert the factor itself, multiplying by all the other coordinate sections. -/
def coordinateInsertion (a : TensorIndex ι) (i : Fin k) :
    M i ⟶ FiniteTensor.tensorObj M :=
  FiniteTensor.insertMap M (fun j => s j (a j)) i (𝟙 (M i))

/-- Evaluation of insertion is the actual tensor coordinate with one entry replaced. -/
theorem coordinate_comp_insertion (a : TensorIndex ι) (i : Fin k) (p : ι i) :
    s i p ≫ coordinateInsertion M ι s a i =
      tensorCoordinate M ι s (Function.update a i p) := by
  rw [coordinateInsertion, FiniteTensor.section_comp_insertMap, Category.comp_id]
  unfold tensorCoordinate
  congr 1
  funext j
  by_cases hji : j = i
  · subst j
    simp only [Function.update_self]
  · simp only [Function.update_of_ne hji]

/-- The full coefficient map. For sheaves, `T a` will be multiplication by
the actual scalar coefficient of the tensor entry `a`. -/
def coefficient
    (T : TensorIndex ι → (FiniteTensor.tensorObj M ⟶ FiniteTensor.tensorObj M))
    (i : Fin k) (q : ι i) : M i ⟶ FiniteTensor.tensorObj M :=
  ∑ a : TensorIndex ι,
    if a i = q then coordinateInsertion M ι s a i ≫ T a else 0

/-- Every coefficient has the expected full contraction formula on coordinate sections. -/
theorem coefficient_coordinate
    (T : TensorIndex ι → (FiniteTensor.tensorObj M ⟶ FiniteTensor.tensorObj M))
    (i : Fin k) (p q : ι i) :
    s i p ≫ coefficient M ι s T i q =
      ∑ a : TensorIndex ι,
        if a i = q then tensorCoordinate M ι s (Function.update a i p) ≫ T a else 0 := by
  rw [coefficient, Preadditive.comp_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a i = q
  · simp only [if_pos ha]
    rw [← Category.assoc, coordinate_comp_insertion]
  · simp only [if_neg ha, CategoryTheory.Limits.comp_zero]

/-- The actual alternating coordinate equation, including its sign in all characteristics. -/
def criticalEquation
    (T : TensorIndex ι → (FiniteTensor.tensorObj M ⟶ FiniteTensor.tensorObj M))
    (i : Fin k) (p q : ι i) : 𝟙_ C ⟶ FiniteTensor.tensorObj M :=
  s i p ≫ coefficient M ι s T i q - s i q ≫ coefficient M ι s T i p

/-- The complete coordinate-wedge expression is proved entry by entry. -/
theorem criticalEquation_expansion
    (T : TensorIndex ι → (FiniteTensor.tensorObj M ⟶ FiniteTensor.tensorObj M))
    (i : Fin k) (p q : ι i) :
    criticalEquation M ι s T i p q =
      ∑ a : TensorIndex ι,
        ((if a i = q then tensorCoordinate M ι s (Function.update a i p) ≫ T a else 0) -
          (if a i = p then tensorCoordinate M ι s (Function.update a i q) ≫ T a else 0)) := by
  rw [criticalEquation, coefficient_coordinate, coefficient_coordinate,
    Finset.sum_sub_distrib]

@[simp]
theorem criticalEquation_self
    (T : TensorIndex ι → (FiniteTensor.tensorObj M ⟶ FiniteTensor.tensorObj M))
    (i : Fin k) (p : ι i) : criticalEquation M ι s T i p p = 0 := by
  simp only [criticalEquation, sub_self]

/-- Antisymmetry follows from the actual subtraction, with no division by two. -/
theorem criticalEquation_swap
    (T : TensorIndex ι → (FiniteTensor.tensorObj M ⟶ FiniteTensor.tensorObj M))
    (i : Fin k) (p q : ι i) :
    criticalEquation M ι s T i q p = -criticalEquation M ι s T i p q := by
  simp only [criticalEquation, neg_sub]

end PaperVerification.Segre.TensorCriticalMap

end SegreTensorCriticalMap

section SegreGlobalCriticalMap

/-!
# The actual full-product singular-vector functional

For any scheme mapping to the projective factors, this file constructs the
literal tensor line bundle, its coordinate sections, and the coefficient
morphisms belonging to every entry of an arbitrary tensor. Restricting those
morphisms to the genuinely pulled-back Euler kernels gives the global
critical functional. Its value on every pulled-back coordinate wedge is the
literal contraction-proportionality equation.

The sections are constructed by genuine pullback and restriction, not by
postulating a polynomial-to-section comparison. No characteristic restriction,
genericity hypothesis, cohomology comparison, or span identity is assumed.
The geometric principal theorems combine this construction with the
regular-Koszul and cohomological arguments.
-/

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

namespace PaperVerification.Segre.GlobalCriticalMap

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open EulerSheaf EulerSections EulerCriticalFunctional
open scoped BigOperators

universe u
variable {I K : Type u} [Fintype I] [DecidableEq I] [Field K]

local notation "𝒜" => MvPolynomial.homogeneousSubmodule I K
local notation "X" => Proj (MvPolynomial.homogeneousSubmodule I K)
local notation "O1" => Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule I K) (1 : ℤ)

section ActualPullbackCoordinates

variable {Y : Scheme.{u}}
  (f : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule I K))

/-- The compatible family of genuinely pulled-back coordinate sections. -/
def pullbackCoordinateFamily (a : I) : ((AlgebraicGeometry.Scheme.Modules.pullback f).obj O1).sections :=
  PresheafOfModules.sectionsMk
    (fun U => f.pullbackSectionsLE O1 ⊤ U.unop (by simp) (coordinateSection a ⊤))
    (by
      intro U V g
      change ((AlgebraicGeometry.Scheme.Modules.pullback f).obj O1).presheaf.map g
          (f.pullbackSectionsLE O1 ⊤ U.unop (by simp) (coordinateSection a ⊤)) =
        f.pullbackSectionsLE O1 ⊤ V.unop (by simp) (coordinateSection a ⊤)
      simp only [Scheme.Hom.pullbackSectionsLE_apply]
      rw [← Functor.map_comp_apply]
      exact congrArg
        (fun j : op (f ⁻¹ᵁ (⊤ : (X).Opens)) ⟶ V =>
          ((AlgebraicGeometry.Scheme.Modules.pullback f).obj O1).presheaf.map j
            (f.pullbackSections O1 ⊤ (coordinateSection a ⊤)))
        (Subsingleton.elim _ _))

/-- The same family equals pullback from every smaller projective open. -/
theorem pullbackCoordinateFamily_eval (a : I)
    (U : (X).Opens) (V : Y.Opens) (hV : V ≤ f ⁻¹ᵁ U) :
    (pullbackCoordinateFamily f a).val (op V) =
      f.pullbackSectionsLE O1 U V hV (coordinateSection a U) := by
  change f.pullbackSectionsLE O1 ⊤ V (by simp) (coordinateSection a ⊤) = _
  have hcoord : (O1).presheaf.map U.leTop.op (coordinateSection a ⊤) =
      coordinateSection a U := by
    apply Proj.twistingSheaf.ext
    intro x
    rfl
  have hres := f.pullbackSections_restrict O1 ⊤ U.leTop (coordinateSection a ⊤)
  rw [hcoord] at hres
  simp only [Scheme.Hom.pullbackSectionsLE_apply]
  rw [← hres, ← Functor.map_comp_apply]
  exact congrArg
    (fun j : op (f ⁻¹ᵁ (⊤ : (X).Opens)) ⟶ op V =>
      ((AlgebraicGeometry.Scheme.Modules.pullback f).obj O1).presheaf.map j
        (f.pullbackSections O1 ⊤ (coordinateSection a ⊤)))
    (Subsingleton.elim _ _)

/-- The actual coordinate morphism from the structure sheaf to the pulled-back line. -/
def pullbackCoordinateHom (a : I) : 𝟙_ Y.Modules ⟶ (AlgebraicGeometry.Scheme.Modules.pullback f).obj O1 :=
  ((AlgebraicGeometry.Scheme.Modules.pullback f).obj O1).unitHomEquiv.symm (pullbackCoordinateFamily f a)

/-- Evaluation at one gives exactly the usual pulled-back projective coordinate. -/
theorem pullbackCoordinateHom_app_one (a : I)
    (U : (X).Opens) (V : Y.Opens) (hV : V ≤ f ⁻¹ᵁ U) :
    (pullbackCoordinateHom f a).app V (1 : Γ(Y, V)) =
      f.pullbackSectionsLE O1 U V hV (coordinateSection a U) := by
  change (((AlgebraicGeometry.Scheme.Modules.pullback f).obj O1).unitHomEquiv.symm
    (pullbackCoordinateFamily f a)).val.app (op V) (1 : Γ(Y, V)) = _
  rw [TauCeti.SheafOfModules.unitHomEquiv_symm_val_app, one_smul]
  exact pullbackCoordinateFamily_eval f a U V hV

end ActualPullbackCoordinates

section FullProduct

variable {k : ℕ} (J : Fin k → Type u)
variable [∀ i, Fintype (J i)] [∀ i, DecidableEq (J i)]
variable {P : Scheme.{u}} [P.Over (Spec (.of K))]
variable (f : (i : Fin k) → P ⟶ Proj (MvPolynomial.homogeneousSubmodule (J i) K))

/-- The actual factor line bundles on the common source. -/
def factorLine (i : Fin k) : P.Modules :=
  (AlgebraicGeometry.Scheme.Modules.pullback (f i)).obj (Proj.twistingSheaf
    (MvPolynomial.homogeneousSubmodule (J i) K) (1 : ℤ))

/-- The actual line bundle O(1,...,1), as a finite tensor of pullbacks. -/
def tensorLine : P.Modules := FiniteTensor.tensorObj (factorLine J f)

/-- All actual coordinate morphisms of all pulled-back factor lines. -/
def factorCoordinate (i : Fin k) (a : J i) : 𝟙_ P.Modules ⟶ factorLine J f i :=
  pullbackCoordinateHom (f i) a

/-- Multiplication by an actual coefficient of the base field. -/
def scalarEndomorphism (c : K) : tensorLine J f ⟶ tensorLine J f :=
  globalSectionsSmul (tensorLine J f) (baseRingToGlobalSections K P c)

/-- The complete coefficient morphism, indexed by the literal full tensor. -/
def tensorCoefficient (T : ((i : Fin k) → J i) → K)
    (i : Fin k) (a : J i) : factorLine J f i ⟶ tensorLine J f :=
  TensorCriticalMap.coefficient (factorLine J f) J (factorCoordinate J f)
    (fun z => scalarEndomorphism J f (T z)) i a

/-- The genuine critical functional from the i-th pulled-back Euler kernel. -/
def factorCritical (T : ((i : Fin k) → J i) → K) (i : Fin k) :
    (AlgebraicGeometry.Scheme.Modules.pullback (f i)).obj (eulerKernel (I := J i) (K := K) 2) ⟶ tensorLine J f :=
  pullbackCriticalFunctional (f i) (tensorCoefficient J f T i)

/-- The genuine finite product of all pulled-back positive Euler kernels. -/
def criticalSource : P.Modules :=
  ∏ᶜ fun i : Fin k => (AlgebraicGeometry.Scheme.Modules.pullback (f i)).obj (eulerKernel (I := J i) (K := K) 2)

/-- The actual global critical functional, with every factor included. -/
def criticalMap (T : ((i : Fin k) → J i) → K) :
    criticalSource J f ⟶ tensorLine J f :=
  ∑ i : Fin k,
    Pi.π (fun j : Fin k =>
      (AlgebraicGeometry.Scheme.Modules.pullback (f j)).obj (eulerKernel (I := J j) (K := K) 2)) i ≫
        factorCritical J f T i

/-- The actual coordinate equation as a global section morphism. -/
def criticalCoordinate (T : ((i : Fin k) → J i) → K)
    (i : Fin k) (a b : J i) : 𝟙_ P.Modules ⟶ tensorLine J f :=
  TensorCriticalMap.criticalEquation (factorLine J f) J (factorCoordinate J f)
    (fun z => scalarEndomorphism J f (T z)) i a b

/-- On every actual pullback chart, the global functional on a coordinate
wedge is the actual tensor contraction-proportionality equation. -/
theorem factorCritical_coordinateWedge
    (T : ((i : Fin k) → J i) → K) (i : Fin k) (a b : J i)
    (U : (Proj (MvPolynomial.homogeneousSubmodule (J i) K)).Opens)
    (V : P.Opens) (hV : V ≤ (f i) ⁻¹ᵁ U) :
    (factorCritical J f T i).app V
      ((f i).pullbackSectionsLE (eulerKernel (I := J i) (K := K) 2) U V hV
        (coordinateWedge a b U)) =
      (criticalCoordinate J f T i a b).app V (1 : Γ(P, V)) := by
  rw [factorCritical, pullbackCriticalFunctional_coordinateWedge]
  change _ = (tensorCoefficient J f T i b).app V
      ((pullbackCoordinateHom (f i) a).app V (1 : Γ(P, V))) -
    (tensorCoefficient J f T i a).app V
      ((pullbackCoordinateHom (f i) b).app V (1 : Γ(P, V)))
  rw [pullbackCoordinateHom_app_one (f i) a U V hV,
    pullbackCoordinateHom_app_one (f i) b U V hV]
  rfl

/-- The full tensor-entry expansion is an equality of actual sheaf morphisms. -/
theorem criticalCoordinate_expansion
    (T : ((i : Fin k) → J i) → K) (i : Fin k) (a b : J i) :
    criticalCoordinate J f T i a b =
      ∑ z : (j : Fin k) → J j,
        ((if z i = b then
            TensorCriticalMap.tensorCoordinate (factorLine J f) J (factorCoordinate J f)
              (Function.update z i a) ≫ scalarEndomorphism J f (T z) else 0) -
          (if z i = a then
            TensorCriticalMap.tensorCoordinate (factorLine J f) J (factorCoordinate J f)
              (Function.update z i b) ≫ scalarEndomorphism J f (T z) else 0)) :=
  TensorCriticalMap.criticalEquation_expansion _ _ _ _ _ _ _

end FullProduct
end PaperVerification.Segre.GlobalCriticalMap

end SegreGlobalCriticalMap

section SegreActualProductKoszulTerms

/-!
# The actual full Koszul terms on the projective product

The exterior powers in this file are those of the literal source of the
critical functional. Their complete degree decomposition is identified
with the full coproduct used in the product cohomology calculation.
Every pullback and line twist is accounted for by a proved isomorphism.
-/


attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false


namespace PaperVerification.Segre.ActualProductKoszulTerms

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open TauCeti.AlgebraicGeometry.Scheme.Modules
open FixedProductCohomology FixedProductProjections ProductKoszulVanishing
open TwistedExteriorEuler EulerExteriorTwist EulerSheaf
open FullProductKoszulTerms PullbackExteriorMap
open scoped BigOperators

universe u
variable (K : Type u) [Field K] {k : ℕ}
variable (I : Fin (k + 1) → Type u)
variable [∀ i, Fintype (I i)] [∀ i, DecidableEq (I i)]

/-- The genuine iterated product of the projective spaces. -/
abbrev product : CoveredScheme K :=
  CoveredScheme.finiteProduct (fun i => projectiveScheme K (I i))

set_option quotPrecheck false in local notation "X" => (product K I).scheme

/-- The genuine projection used by both the critical map and cohomology. -/
abbrev factorProjection (i : Fin (k + 1)) :
    X ⟶ Proj (MvPolynomial.homogeneousSubmodule (I i) K) :=
  projection (fun i => projectiveScheme K (I i)) i

/-- The actual source, namely the finite product of pulled-back Ω¹(2). -/
abbrev source : (X).Modules :=
  GlobalCriticalMap.criticalSource I (factorProjection K I)

/-- The line of uniform multidegree t, built from the actual projections. -/
def line (t : ℤ) : (X).Modules :=
  FiniteTensor.tensorObj (fun i => (Scheme.Modules.pullback (factorProjection K I i)).obj
    (Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (I i) K) t))

/-- The actual degree-r term for a functional from the source to O(d,…,d). -/
def term (d : ℤ) (r : ℕ) : (X).Modules :=
  (SheafOfModules.exteriorPower (X).sheaf r).obj (source K I) ⊗
    line K I (d * (1 - (r : ℤ)))

instance positiveEulerKernel_quasicoherent (J : Type u) [Fintype J] [DecidableEq J] :
    (eulerKernel (I := J) (K := K) 2).IsQuasicoherent := by
  letI : (∏ᶜ fun _ : J =>
      Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule J K) ((2 : ℤ) - 1)).IsQuasicoherent :=
    EulerQuasicoherent.finiteProduct_quasicoherent _
  exact @Scheme.Modules.isQuasicoherent_kernel
    (Proj (MvPolynomial.homogeneousSubmodule J K)) _ _
    (eulerMap (I := J) (K := K) 2) inferInstance inferInstance

instance source_quasicoherent : (source K I).IsQuasicoherent := by
  letI : ∀ i, (eulerKernel (I := I i) (K := K) 2).IsQuasicoherent :=
    fun i => positiveEulerKernel_quasicoherent K (I i)
  letI : ∀ i, ((Scheme.Modules.pullback (factorProjection K I i)).obj
      (eulerKernel (I := I i) (K := K) 2)).IsQuasicoherent := fun i => inferInstance
  exact SchemeProductSections.finiteProduct_quasicoherent _

/-- The actual line of degree zero is the tensor unit, including every
factor's zero-twist comparison. -/
def lineZeroIso : line K I 0 ≅ 𝟙_ (X).Modules :=
  tensorFamilyIso (fun i =>
    (Scheme.Modules.pullback (factorProjection K I i)).mapIso
      (Proj.unitIsoTwistingSheafZero
        (MvPolynomial.homogeneousSubmodule (I i) K)).symm ≪≫
      pullbackObjUnitIso (factorProjection K I i)) ≪≫
    FiniteTensor.tensorUnitsIso (k + 1)

/-- Pullback tensor comparison using its proved right-quasicoherent instance. -/
def pullbackTensorRightIso {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    (M N : Z.Modules) [N.IsQuasicoherent] :
    (Scheme.Modules.pullback f).obj (M ⊗ N) ≅
      (Scheme.Modules.pullback f).obj M ⊗ (Scheme.Modules.pullback f).obj N := by
  letI : IsIso (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) M N) :=
    Scheme.Modules.isIso_pullback_δ_of_isQuasicoherent_right f M N
  exact asIso (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) M N)

/-- Multiplication of the literal product lines is built factor by factor
from actual pullback tensor maps and actual multiplication of twists. -/
def lineAddIso (a b : ℤ) : line K I a ⊗ line K I b ≅ line K I (a + b) := by
  letI : ∀ i, (Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (I i) K) b).IsQuasicoherent :=
    fun i => Proj.isQuasicoherent_twistingSheaf _ _
  exact FiniteTensor.tensorPointwiseIso _ _ ≪≫
    tensorFamilyIso (fun i =>
      (pullbackTensorRightIso (factorProjection K I i)
        (Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (I i) K) a)
        (Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (I i) K) b)).symm ≪≫
      (Scheme.Modules.pullback (factorProjection K I i)).mapIso
        (twistingTensorIso (I := I i) (K := K) a b))

/-- The augmentation target is the original coefficient line. -/
def termZeroIso (d : ℤ) : term K I d 0 ≅ line K I d := by
  simpa only [term, Nat.cast_zero, sub_zero, mul_one] using
    (((SheafOfModules.exteriorPowerZeroIso (X).sheaf).app (source K I) ⊗ᵢ
      Iso.refl (line K I d)) ≪≫ λ_ (line K I d))

/-- The first actual term is exactly the original source of the critical
map; its zero line twist contributes only the canonical unit. -/
def termOneIso (d : ℤ) : term K I d 1 ≅ source K I := by
  simpa only [term, Nat.cast_one, sub_self, mul_zero] using
    (((SheafOfModules.exteriorPowerOneIso (X).sheaf).app (source K I) ⊗ᵢ
      lineZeroIso K I) ≪≫ ρ_ (source K I))

/-- Every summand of the full exterior decomposition, with its actual
line factor, is the actual external product of Ωᵖ(2p+t). -/
def summandIso (p : Fin (k + 1) → ℕ) (t : ℤ) :
    FiniteTensor.tensorObj (fun i =>
      (SheafOfModules.exteriorPower (X).sheaf (p i)).obj
        ((Scheme.Modules.pullback (factorProjection K I i)).obj
          (eulerKernel (I := I i) (K := K) 2))) ⊗ line K I t ≅
      exteriorProduct K I p (fun i => 2 * (p i : ℤ) + t) := by
  -- The determinant coordinates use an ordering only to construct an
  -- isomorphism. Choose it internally; no ordering is required of the
  -- original projective coordinate types in the statement.
  letI : ∀ i, LinearOrder (I i) := fun i =>
    LinearOrder.lift' (Fintype.equivFin (I i)) (Fintype.equivFin (I i)).injective
  letI : ∀ i, (eulerKernel (I := I i) (K := K) 2).IsQuasicoherent :=
    fun i => positiveEulerKernel_quasicoherent K (I i)
  letI : ∀ i, (Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (I i) K) t).IsQuasicoherent :=
    fun i => Proj.isQuasicoherent_twistingSheaf _ _
  exact FiniteTensor.tensorPointwiseIso _ _ ≪≫
    tensorFamilyIso (fun i =>
      ((pullbackExteriorIso (factorProjection K I i)
        (eulerKernel (I := I i) (K := K) 2) (p i)).symm ⊗ᵢ Iso.refl _) ≪≫
      (pullbackTensorRightIso (factorProjection K I i)
        ((SheafOfModules.exteriorPower (projectiveScheme K (I i)).scheme.sheaf
          (p i)).obj (eulerKernel (I := I i) (K := K) 2))
        (Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (I i) K) t)).symm ≪≫
      (Scheme.Modules.pullback (factorProjection K I i)).mapIso
        (positiveExteriorAdditionalTwistIso (I := I i) (K := K) (p i) t)) ≪≫
    (finiteExternalTensorIso (fun i => projectiveScheme K (I i))
      (fun i => exteriorKernelTwist (I := I i) (K := K) (p i)
        (2 * (p i : ℤ) + t)) (fun i =>
        EulerQuasicoherent.exteriorKernelTwist_quasicoherent
          (I := I i) (K := K) (p i) (2 * (p i : ℤ) + t))).symm

/-- The literal exterior term, including every exterior-degree tuple, is
the complete geometric term used in the cohomology gap. -/
def termIso (d : ℤ) (r : ℕ) :
    term K I d r ≅ fullTerm K I r
      (fun p i => 2 * (p i : ℤ) + d * (1 - (r : ℤ))) :=
  ((FiniteSheafExteriorFull.actualFiniteExteriorFullIso (X).sheaf
    (fun i => (Scheme.Modules.pullback (factorProjection K I i)).obj
      (eulerKernel (I := I i) (K := K) 2)) r).symm ⊗ᵢ Iso.refl _) ≪≫
    PreservesCoproduct.iso (tensorRight (line K I (d * (1 - (r : ℤ))))) _ ≪≫
    Sigma.mapIso (fun p : Degrees k r => summandIso K I p.val (d * (1 - (r : ℤ))))

/-- The full graph term has the complete q<r cohomology gap. -/
theorem graph_term_cohomology_vanishes
    (hI : ∀ i, 0 < Fintype.card (I i)) (r q : ℕ) (hr : 2 ≤ r) (hq : q < r) :
    Subsingleton (Cohomology (term K I 2 r) q) := by
  have he : (fun (p : Fin (k + 1) → ℕ) i => 2 * (p i : ℤ) + 2 * (1 - (r : ℤ))) =
      (fun p i => 2 * (p i : ℤ) - 2 * (r : ℤ) + 2) := by
    funext p i
    ring
  have hv := graph_fullTerm_cohomology_vanishes K I hI r q hr hq
  rw [← he] at hv
  let e := (cohomologyFunctor X q).mapIso (termIso K I 2 r)
  exact ⟨fun x y => (ConcreteCategory.bijective_of_isIso e.hom).1 (hv.elim _ _)⟩

/-- The full balanced term has the same cohomology gap under exactly the
paper's triangle inequalities. -/
theorem balanced_term_cohomology_vanishes
    (hI : ∀ i, 0 < Fintype.card (I i)) (htriangle : TriangleDimensions I)
    (r q : ℕ) (hr : 2 ≤ r) (hq : q < r) :
    Subsingleton (Cohomology (term K I 1 r) q) := by
  have he : (fun (p : Fin (k + 1) → ℕ) i => 2 * (p i : ℤ) + 1 * (1 - (r : ℤ))) =
      (fun p i => 1 + 2 * (p i : ℤ) - (r : ℤ)) := by
    funext p i
    ring
  have hv := balanced_fullTerm_cohomology_vanishes K I hI htriangle r q hr hq
  rw [← he] at hv
  let e := (cohomologyFunctor X q).mapIso (termIso K I 1 r)
  exact ⟨fun x y => (ConcreteCategory.bijective_of_isIso e.hom).1 (hv.elim _ _)⟩

/-- There are no omitted high exterior terms: the actual term is zero
strictly above the sum of the projective dimensions. -/
theorem term_isZero_of_degree_gt
    (hI : ∀ i, 0 < Fintype.card (I i)) (d : ℤ) (r : ℕ)
    (hr : (∑ i, (Fintype.card (I i) - 1)) < r) :
    IsZero (term K I d r) :=
  (fullTerm_isZero_of_degree_gt K I hI r hr _).of_iso (termIso K I d r)

end PaperVerification.Segre.ActualProductKoszulTerms

end SegreActualProductKoszulTerms


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
