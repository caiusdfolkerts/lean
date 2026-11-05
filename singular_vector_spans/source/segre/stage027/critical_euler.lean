module
public import SegreVerified.Stage027.CriticalCharts
public import SegreVerified.Stage025.ExteriorVanishing
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
  out.putStrLn "SEGRE_STAGE Stage027.CriticalEuler"
  out.flush

/-!
# The actual critical bundle and its weighted Koszul complex

The named sections preserve the original proof stages and local scopes.
-/

set_option autoImplicit false

section SegreProductIsoProjection

namespace PaperVerification.Segre.ProductIsoProjection

open CategoryTheory Limits

universe w v₁ v₂ u₁ u₂

/-- A functor preserving a product, followed by component isomorphisms,
has the expected composite as each projection. -/
theorem hom_comp_projection {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) {J : Type w}
    (A : J → C) (B : J → D) [HasProduct A] [HasProductsOfShape J D]
    [PreservesLimit (Discrete.functor A) F]
    {M : C} (e : M ≅ ∏ᶜ A) (f : ∀ j, F.obj (A j) ≅ B j) (j : J) :
    (F.mapIso e ≪≫ PreservesProduct.iso F A ≪≫ Pi.mapIso f).hom ≫ Pi.π B j =
      F.map (e.hom ≫ Pi.π A j) ≫ (f j).hom := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc,
    Pi.mapIso_hom_π, PreservesProduct.iso_hom, piComparison_comp_π_assoc,
    ← Functor.map_comp_assoc]

end PaperVerification.Segre.ProductIsoProjection

end SegreProductIsoProjection

section SegreSchemeTensorProductCoordinates

namespace PaperVerification.Segre.SchemeTensorProductCoordinates

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory

universe u
variable {Y : Scheme.{u}} {J : Type u}

/-- Transport a product coordinate system through tensoring, then through
its actual component isomorphisms. This is the original composite. -/
def coordinateIso (L : Y.Modules) (A B : J → Y.Modules)
    [PreservesLimit (Discrete.functor A) (tensorRight L)]
    {M : Y.Modules} (e : M ≅ ∏ᶜ A)
    (f : ∀ j, A j ⊗ L ≅ B j) : M ⊗ L ≅ ∏ᶜ B :=
  (tensorRight L).mapIso e ≪≫
    PreservesProduct.iso (tensorRight L) A ≪≫ Pi.mapIso f

/-- The construction is literally the original functor/product composite. -/
theorem coordinateIso_eq_composite (L : Y.Modules) (A B : J → Y.Modules)
    [PreservesLimit (Discrete.functor A) (tensorRight L)]
    {M : Y.Modules} (e : M ≅ ∏ᶜ A)
    (f : ∀ j, A j ⊗ L ≅ B j) :
    coordinateIso L A B e f =
      (tensorRight L).mapIso e ≪≫
        PreservesProduct.iso (tensorRight L) A ≪≫ Pi.mapIso f := rfl

/-- Each projection is the actual tensor of the original projection,
followed by the specified component isomorphism. -/
@[reassoc] theorem coordinateIso_hom_π (L : Y.Modules) (A B : J → Y.Modules)
    [PreservesLimit (Discrete.functor A) (tensorRight L)]
    {M : Y.Modules} (e : M ≅ ∏ᶜ A)
    (f : ∀ j, A j ⊗ L ≅ B j) (j : J) :
    (coordinateIso L A B e f).hom ≫ Pi.π B j =
      (tensorRight L).map (e.hom ≫ Pi.π A j) ≫ (f j).hom :=
  ProductIsoProjection.hom_comp_projection (tensorRight L) A B e f j

end PaperVerification.Segre.SchemeTensorProductCoordinates

end SegreSchemeTensorProductCoordinates

section SegreSchemeTensorPresentation

namespace PaperVerification.Segre.SchemeTensorPresentation

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite

universe u
variable {Y : Scheme.{u}} {M N P : Y.Modules}

/-- The site and scheme presentations use the identical pure-section map. -/
theorem tensorSection_eq (U : Y.Opens) (s : Γ(M, U)) (t : Γ(N, U)) :
    SheafCoefficientContraction.tensorSection Y.sheaf M N (op U) s t =
      EulerTwistComparison.tensorSectionOn (Y := Y) U s t := rfl

/-- Transport the presentation identity before specializing the scheme. -/
theorem hom_app_tensorSection (f : M ⊗ N ⟶ P) (U : Y.Opens)
    (s : Γ(M, U)) (t : Γ(N, U)) :
    (Scheme.Modules.Hom.app f U)
      (SheafCoefficientContraction.tensorSection Y.sheaf M N (op U) s t) =
      (Scheme.Modules.Hom.app f U)
        (EulerTwistComparison.tensorSectionOn (Y := Y) U s t) :=
  congrArg (fun z : Γ(M ⊗ N, U) => (Scheme.Modules.Hom.app f U) z)
    (tensorSection_eq (Y := Y) U s t)

/-- Pure tensors commute with the actual tensor of two sheaf morphisms. -/
theorem map_tensorSection {M' N' : Y.Modules} (f : M ⟶ M') (g : N ⟶ N')
    (U : Y.Opens) (s : Γ(M, U)) (t : Γ(N, U)) :
    (Scheme.Modules.Hom.app (f ⊗ₘ g) U)
      (SheafCoefficientContraction.tensorSection Y.sheaf M N (op U) s t) =
      SheafCoefficientContraction.tensorSection Y.sheaf M' N' (op U)
        (Scheme.Modules.Hom.app f U s) (Scheme.Modules.Hom.app g U t) :=
  (hom_app_tensorSection (Y := Y) (f ⊗ₘ g) U s t).trans
    ((EulerTwistComparison.tensorSectionOn_map (Y := Y) f g U s t).trans
      (tensorSection_eq (Y := Y) (M := M') (N := N') U
        (Scheme.Modules.Hom.app f U s) (Scheme.Modules.Hom.app g U t)).symm)

/-- Evaluate composition in the native scheme section spaces. -/
theorem comp_app_apply (f : M ⟶ N) (g : N ⟶ P) (U : Y.Opens)
    (s : Γ(M, U)) :
    Scheme.Modules.Hom.app (f ≫ g) U s =
      Scheme.Modules.Hom.app g U (Scheme.Modules.Hom.app f U s) := rfl

/-- Tensoring a morphism on the right acts on genuine pure sections by
that morphism on the first factor. Prove this before specializing the
scheme, so applications do not unfold the concrete projective scheme. -/
theorem tensorRight_map_tensorSection {A L : Y.Modules}
    (a : M ⟶ A) (U : Y.Opens) (s : Γ(M, U)) (t : Γ(L, U)) :
    Scheme.Modules.Hom.app ((tensorRight L).map a) U
      (SheafCoefficientContraction.tensorSection Y.sheaf M L (op U) s t) =
      SheafCoefficientContraction.tensorSection Y.sheaf A L (op U)
        (Scheme.Modules.Hom.app a U s) t := by
  let z : Γ(M ⊗ L, U) :=
    SheafCoefficientContraction.tensorSection Y.sheaf M L (op U) s t
  have he := congrArg (β := Γ(A ⊗ L, U))
    (fun f : M ⊗ L ⟶ A ⊗ L =>
      Scheme.Modules.Hom.app (M := M ⊗ L) (N := A ⊗ L) f U z)
    (MonoidalCategory.tensorHom_id a L)
  have hid : Scheme.Modules.Hom.app (𝟙 L) U t = t := rfl
  exact he.symm.trans ((map_tensorSection (Y := Y) a (𝟙 L) U s t).trans
    (congrArg (fun v : Γ(L, U) =>
      SheafCoefficientContraction.tensorSection Y.sheaf A L (op U)
        (Scheme.Modules.Hom.app a U s) v) hid))

/-- A projection identity of sheaf morphisms gives its full tensor-section formula. -/
theorem projected_tensor {A L B Q : Y.Modules}
    (a : M ⟶ A) (b : A ⊗ L ⟶ B) (g : M ⊗ L ⟶ Q) (π : Q ⟶ B)
    (h : g ≫ π = (tensorRight L).map a ≫ b) (U : Y.Opens)
    (s : Γ(M, U)) (t : Γ(L, U)) :
    Scheme.Modules.Hom.app π U (Scheme.Modules.Hom.app g U
      (SheafCoefficientContraction.tensorSection Y.sheaf M L (op U) s t)) =
      Scheme.Modules.Hom.app b U
        (SheafCoefficientContraction.tensorSection Y.sheaf A L (op U)
          (Scheme.Modules.Hom.app a U s) t) := by
  have hh := congrArg
    (fun f : M ⊗ L ⟶ B => Scheme.Modules.Hom.app f U
      (SheafCoefficientContraction.tensorSection Y.sheaf M L (op U) s t)) h
  have hm : Scheme.Modules.Hom.app (M := M ⊗ L) (N := A ⊗ L)
      ((tensorRight L).map a) U
      (SheafCoefficientContraction.tensorSection Y.sheaf M L (op U) s t) =
      SheafCoefficientContraction.tensorSection Y.sheaf A L (op U)
        (Scheme.Modules.Hom.app a U s) t :=
    tensorRight_map_tensorSection (Y := Y) a U s t
  exact (comp_app_apply (Y := Y) g π U _).symm.trans
    (hh.trans ((comp_app_apply (Y := Y) ((tensorRight L).map a) b U _).trans
      (congrArg (fun z : Γ(A ⊗ L, U) => Scheme.Modules.Hom.app b U z) hm)))

end PaperVerification.Segre.SchemeTensorPresentation

end SegreSchemeTensorPresentation

section SegreEulerExteriorTwistMaps

/-!
# Global coordinate comparisons for the exterior Euler complexes

Coordinate minors and actual multiplication of twisting sheaves identify
the positive exterior source with the corresponding twist of the
negative exterior source. The target comparison is constructed
independently from the same genuine tensor and product isomorphisms.

The full chart formulas on every wedge and every coefficient are proved.
These formulas are used in the next module to establish equality of the
actual contraction morphisms. No compatibility square is assumed here.
-/

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

namespace PaperVerification.Segre.EulerExteriorTwistMaps

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory Opposite
open AlgebraicGeometry.Scheme.Modules
open EulerSheaf EulerSections ExteriorCoordinateTwist ExteriorCoordinateSections
open EulerCriticalChart TwistedExteriorEuler EulerTwistComparison
open SheafCoefficientContraction SheafCoefficientComplex
open scoped TensorProduct BigOperators

universe u
variable {I K : Type u} [Fintype I] [DecidableEq I] [LinearOrder I] [Field K]

local notation "𝒜" => MvPolynomial.homogeneousSubmodule I K
local notation "X" => Proj (MvPolynomial.homogeneousSubmodule I K)

/-- The actual exterior coordinate sheaf. -/
abbrev exteriorCoordinates (t : ℤ) (r : ℕ) : (X).Modules :=
  (SheafOfModules.exteriorPower (X).sheaf r).obj
    (coordinateSource (I := I) (K := K) t)

/-- The actual wedge in the complete chart frame. -/
def framedWedge (t : ℤ) (r : ℕ) (j : I) (U : (X).Opens)
    (hU : U ≤ ProjectiveCech.coordinateOpen (K := K) j)
    (v : Fin r → I → Γ(X, U)) : Γ(exteriorCoordinates t r, U) :=
  wedgeSection (X).sheaf (coordinateSource t) r (op U)
    (fun i => ExteriorCoordinateTwist.chartSourceEquiv t j U hU (v i))

/-- The actual tensor with an arbitrary coefficient in its genuine frame. -/
def framedTensorWedge (t : ℤ) (r : ℕ) (d : ℤ) (j : I) (U : (X).Opens)
    (hU : U ≤ ProjectiveCech.coordinateOpen (K := K) j)
    (v : Fin r → I → Γ(X, U)) (a : Γ(X, U)) :
    Γ(exteriorCoordinates t r ⊗ Proj.twistingSheaf 𝒜 d, U) :=
  SheafCoefficientContraction.tensorSection (X).sheaf (exteriorCoordinates t r)
    (Proj.twistingSheaf 𝒜 d) (op U)
      (framedWedge t r j U hU v) (chartTrivialization j U hU d a)

/-- The ordered determinant defining one exterior coordinate. -/
def minorCoordinate (r : ℕ) (s : Set.powersetCard I r) (U : (X).Opens)
    (v : Fin r → I → Γ(X, U)) : Γ(X, U) :=
  Matrix.det (fun a b => v a (Set.powersetCard.ofFinEmbEquiv.symm s b))

/-- Product isomorphisms act on the actual section coordinates as their
displayed individual factors. -/
theorem productMapIso_sections {J : Type u} (A B : J → (X).Modules)
    (e : ∀ i, A i ≅ B i) (U : (X).Opens) (z : Γ((∏ᶜ A), U)) (i : J) :
    productSectionsEquiv B U ((Pi.mapIso e).hom.app U z) i =
      (e i).hom.app U (productSectionsEquiv A U z i) := by
  rw [productSectionsEquiv_apply, productSectionsEquiv_apply]
  exact ConcreteCategory.congr_hom
    (congrArg (fun f => f.app U) (Pi.mapIso_hom_π e i)) z

/-- An equality of integer twists changes no actual chart frame. -/
theorem castTwistIso_frame {m n : ℤ} (h : m = n) (j : I) (U : (X).Opens)
    (hU : U ≤ ProjectiveCech.coordinateOpen (K := K) j) (a : Γ(X, U)) :
    (castTwistIso (I := I) (K := K) h).hom.app U
      (chartTrivialization j U hU m a) =
        chartTrivialization j U hU n a := by
  subst n
  rfl

/-- The global coordinate isomorphism has the literal determinant frame
formula on every wedge of full chart sections. -/
theorem coordinateIso_frame (t : ℤ) (r : ℕ) (j : I) (U : (X).Opens)
    (hU : U ≤ ProjectiveCech.coordinateOpen (K := K) j)
    (v : Fin r → I → Γ(X, U)) (s : Set.powersetCard I r) :
    productSectionsEquiv
        (fun _ : Set.powersetCard I r => Proj.twistingSheaf 𝒜 ((r : ℤ) * t)) U
      ((Scheme.Modules.Hom.app («X» := X)
        (coordinateIso (I := I) (K := K) t r).hom U) (framedWedge t r j U hU v)) s =
        chartTrivialization j U hU ((r : ℤ) * t) (minorCoordinate r s U v) := by
  change productSectionsEquiv _ U
      ((Scheme.Modules.Hom.app («X» := X)
        (coordinateIso (I := I) (K := K) t r).hom U)
        ((exteriorUnit (X).sheaf (coordinateSource t) r).app (op U)
          (exteriorPower.ιMulti Γ(X, U) r
            (fun i => ExteriorCoordinateTwist.chartSourceEquiv t j U hU (v i))))) s = _
  erw [coordinateIso_exteriorUnit, minorLinear_ιMulti,
    minorAlternating_on_chart]
  rfl

/-- The actual twisted exterior source is the full product of the actual
summed twisting sheaves. -/
def twistedCoordinateIso (t : ℤ) (r : ℕ) (d : ℤ) :
    exteriorCoordinates (I := I) (K := K) t r ⊗ Proj.twistingSheaf 𝒜 d ≅
      ∏ᶜ fun _ : Set.powersetCard I r =>
        Proj.twistingSheaf 𝒜 ((r : ℤ) * t + d) :=
  SchemeTensorProductCoordinates.coordinateIso (Y := X)
    (Proj.twistingSheaf 𝒜 d)
    (fun _ : Set.powersetCard I r => Proj.twistingSheaf 𝒜 ((r : ℤ) * t))
    (fun _ : Set.powersetCard I r => Proj.twistingSheaf 𝒜 ((r : ℤ) * t + d))
    (coordinateIso (I := I) (K := K) t r)
    (fun _ => twistingTensorIso (I := I) (K := K) ((r : ℤ) * t) d)

@[reassoc]
theorem twistedCoordinateIso_hom_π (t : ℤ) (r : ℕ) (d : ℤ)
    (s : Set.powersetCard I r) :
    (twistedCoordinateIso (I := I) (K := K) t r d).hom ≫ Pi.π _ s =
      (twistFunctor d).map
        ((coordinateIso t r).hom ≫ Pi.π _ s) ≫
          (twistingTensorIso ((r : ℤ) * t) d).hom := by
  exact SchemeTensorProductCoordinates.coordinateIso_hom_π (Y := X)
    (Proj.twistingSheaf 𝒜 d)
    (fun _ : Set.powersetCard I r => Proj.twistingSheaf 𝒜 ((r : ℤ) * t))
    (fun _ : Set.powersetCard I r => Proj.twistingSheaf 𝒜 ((r : ℤ) * t + d))
    (coordinateIso (I := I) (K := K) t r)
    (fun _ => twistingTensorIso (I := I) (K := K) ((r : ℤ) * t) d) s

/-- The tensor isomorphism uses actual multiplication on every local
tensor, with the generic sheaf tensor notation made explicit. -/
theorem twistingTensorIso_localTensor (m n : ℤ) (U : (X).Opens)
    (s : Γ(Proj.twistingSheaf 𝒜 m, U)) (t : Γ(Proj.twistingSheaf 𝒜 n, U)) :
    (twistingTensorIso m n).hom.app U
      (SheafCoefficientContraction.tensorSection (X).sheaf
        (Proj.twistingSheaf 𝒜 m) (Proj.twistingSheaf 𝒜 n) (op U) s t) =
      Proj.twistingSheaf.mul 𝒜 U m n s t :=
  (SchemeTensorPresentation.hom_app_tensorSection
    (Y := X)
    (M := Proj.twistingSheaf 𝒜 m) (N := Proj.twistingSheaf 𝒜 n)
    (twistingTensorIso (I := I) (K := K) m n).hom U s t).trans
      (EulerTwistComparison.twistingTensorIso_tensorSection
        (I := I) (K := K) m n U s t)

/-- The whole twisted-coordinate isomorphism has the prescribed actual
multiplication formula in every individual coordinate. -/
theorem twistedCoordinateIso_component (t : ℤ) (r : ℕ) (d : ℤ) (U : (X).Opens)
    (z : Γ(exteriorCoordinates (I := I) (K := K) t r, U))
    (l : Γ(Proj.twistingSheaf 𝒜 d, U)) (s : Set.powersetCard I r) :
    productSectionsEquiv
        (fun _ : Set.powersetCard I r => Proj.twistingSheaf 𝒜 ((r : ℤ) * t + d)) U
      ((twistedCoordinateIso t r d).hom.app U
        (SheafCoefficientContraction.tensorSection (X).sheaf
          (exteriorCoordinates t r) (Proj.twistingSheaf 𝒜 d) (op U) z l)) s =
      Proj.twistingSheaf.mul 𝒜 U ((r : ℤ) * t) d
        (productSectionsEquiv _ U ((Scheme.Modules.Hom.app («X» := X)
        (coordinateIso (I := I) (K := K) t r).hom U) z) s) l := by
  let a : exteriorCoordinates (I := I) (K := K) t r ⟶
      Proj.twistingSheaf 𝒜 ((r : ℤ) * t) :=
    (coordinateIso t r).hom ≫ Pi.π _ s
  have h := SchemeTensorPresentation.projected_tensor (Y := X) a
    (twistingTensorIso (I := I) (K := K) ((r : ℤ) * t) d).hom
    (twistedCoordinateIso (I := I) (K := K) t r d).hom (Pi.π _ s)
    (twistedCoordinateIso_hom_π t r d s) U z l
  have ha : Scheme.Modules.Hom.app («X» := X) a U z =
      productSectionsEquiv
        (fun _ : Set.powersetCard I r => Proj.twistingSheaf 𝒜 ((r : ℤ) * t)) U
        ((Scheme.Modules.Hom.app («X» := X)
          (coordinateIso (I := I) (K := K) t r).hom U) z) s :=
    (SchemeTensorPresentation.comp_app_apply (Y := X)
      (coordinateIso (I := I) (K := K) t r).hom (Pi.π _ s) U z).trans
      (productSectionsEquiv_apply
        (fun _ : Set.powersetCard I r => Proj.twistingSheaf 𝒜 ((r : ℤ) * t)) U
        ((Scheme.Modules.Hom.app («X» := X)
          (coordinateIso (I := I) (K := K) t r).hom U) z) s).symm
  exact (productSectionsEquiv_apply
    (fun _ : Set.powersetCard I r => Proj.twistingSheaf 𝒜 ((r : ℤ) * t + d)) U
    ((twistedCoordinateIso t r d).hom.app U
      (SheafCoefficientContraction.tensorSection (X).sheaf
        (exteriorCoordinates t r) (Proj.twistingSheaf 𝒜 d) (op U) z l)) s).trans
      (h.trans ((twistingTensorIso_localTensor ((r : ℤ) * t) d U
        (Scheme.Modules.Hom.app («X» := X) a U z) l).trans
          (congrArg (fun v : Γ(Proj.twistingSheaf 𝒜 ((r : ℤ) * t), U) =>
            Proj.twistingSheaf.mul 𝒜 U ((r : ℤ) * t) d v l) ha)))

theorem twistedCoordinateIso_frame (t : ℤ) (r : ℕ) (d : ℤ) (j : I) (U : (X).Opens)
    (hU : U ≤ ProjectiveCech.coordinateOpen (K := K) j)
    (v : Fin r → I → Γ(X, U)) (a : Γ(X, U)) (s : Set.powersetCard I r) :
    productSectionsEquiv
        (fun _ : Set.powersetCard I r => Proj.twistingSheaf 𝒜 ((r : ℤ) * t + d)) U
      ((twistedCoordinateIso t r d).hom.app U (framedTensorWedge t r d j U hU v a)) s =
        chartTrivialization j U hU ((r : ℤ) * t + d)
          (minorCoordinate r s U v * a) := by
  rw [framedTensorWedge, twistedCoordinateIso_component, coordinateIso_frame,
    EulerContractionChart.chartTrivialization_mul_all]

/-- The untwisted coordinate comparison with an explicit harmless degree equality. -/
def coordinateIsoTo (t : ℤ) (r : ℕ) (a : ℤ) (h : (r : ℤ) * t = a) :
    exteriorCoordinates (I := I) (K := K) t r ≅
      ∏ᶜ fun _ : Set.powersetCard I r => Proj.twistingSheaf 𝒜 a :=
  coordinateIso t r ≪≫ Pi.mapIso (fun _ => castTwistIso h)

/-- The twisted coordinate comparison with the actual final degree fixed. -/
def twistedCoordinateIsoTo (t : ℤ) (r : ℕ) (d a : ℤ)
    (h : (r : ℤ) * t + d = a) :
    exteriorCoordinates (I := I) (K := K) t r ⊗ Proj.twistingSheaf 𝒜 d ≅
      ∏ᶜ fun _ : Set.powersetCard I r => Proj.twistingSheaf 𝒜 a :=
  twistedCoordinateIso t r d ≪≫ Pi.mapIso (fun _ => castTwistIso h)

theorem coordinateIsoTo_frame (t : ℤ) (r : ℕ) (a : ℤ) (h : (r : ℤ) * t = a)
    (j : I) (U : (X).Opens) (hU : U ≤ ProjectiveCech.coordinateOpen (K := K) j)
    (v : Fin r → I → Γ(X, U)) (s : Set.powersetCard I r) :
    productSectionsEquiv (fun _ : Set.powersetCard I r => Proj.twistingSheaf 𝒜 a) U
      ((coordinateIsoTo t r a h).hom.app U (framedWedge t r j U hU v)) s =
        chartTrivialization j U hU a (minorCoordinate r s U v) := by
  change productSectionsEquiv _ U
    ((Pi.mapIso (fun _ : Set.powersetCard I r => castTwistIso h)).hom.app U
      ((Scheme.Modules.Hom.app («X» := X)
        (coordinateIso (I := I) (K := K) t r).hom U) (framedWedge t r j U hU v))) s = _
  rw [productMapIso_sections, coordinateIso_frame, castTwistIso_frame]

theorem twistedCoordinateIsoTo_frame (t : ℤ) (r : ℕ) (d a : ℤ)
    (h : (r : ℤ) * t + d = a)
    (j : I) (U : (X).Opens) (hU : U ≤ ProjectiveCech.coordinateOpen (K := K) j)
    (v : Fin r → I → Γ(X, U)) (c : Γ(X, U)) (s : Set.powersetCard I r) :
    productSectionsEquiv (fun _ : Set.powersetCard I r => Proj.twistingSheaf 𝒜 a) U
      ((twistedCoordinateIsoTo t r d a h).hom.app U
        (framedTensorWedge t r d j U hU v c)) s =
      chartTrivialization j U hU a (minorCoordinate r s U v * c) := by
  change productSectionsEquiv _ U
    ((Pi.mapIso (fun _ : Set.powersetCard I r => castTwistIso h)).hom.app U
      ((twistedCoordinateIso t r d).hom.app U
        (framedTensorWedge t r d j U hU v c))) s = _
  rw [productMapIso_sections, twistedCoordinateIso_frame, castTwistIso_frame]

/-- The complete global source comparison. -/
def sourceComparison (r : ℕ) :
    exteriorCoordinates (I := I) (K := K) 1 r ≅
      exteriorCoordinates (-1) r ⊗ Proj.twistingSheaf 𝒜 (2 * (r : ℤ)) :=
  coordinateIsoTo 1 r r (by ring) ≪≫
    (twistedCoordinateIsoTo (-1) r (2 * (r : ℤ)) r (by ring)).symm

/-- The complete global target comparison for the degree-r contraction. -/
def targetComparison (r : ℕ) :
    exteriorCoordinates (I := I) (K := K) 1 r ⊗ Proj.twistingSheaf 𝒜 2 ≅
      exteriorCoordinates (-1) r ⊗ Proj.twistingSheaf 𝒜 (2 * ((r + 1 : ℕ) : ℤ)) :=
  twistedCoordinateIsoTo 1 r 2 ((r : ℤ) + 2) (by ring) ≪≫
    (twistedCoordinateIsoTo (-1) r (2 * ((r + 1 : ℕ) : ℤ))
      ((r : ℤ) + 2) (by push_cast; ring)).symm

/-- The actual global source comparison multiplies the r negative frame
vectors by the genuine degree-2r line frame. -/
theorem sourceComparison_frame (r : ℕ) (j : I) (U : (X).Opens)
    (hU : U ≤ ProjectiveCech.coordinateOpen (K := K) j)
    (v : Fin r → I → Γ(X, U)) :
    (sourceComparison (I := I) (K := K) r).hom.app U (framedWedge 1 r j U hU v) =
      framedTensorWedge (-1) r (2 * (r : ℤ)) j U hU v 1 := by
  let e := twistedCoordinateIsoTo (I := I) (K := K) (-1) r (2 * (r : ℤ)) r
    (by ring)
  apply (((SheafOfModules.evaluation (X).ringCatSheaf (op U)).mapIso e).toLinearEquiv).injective
  change ((sourceComparison r).hom ≫ e.hom).app U (framedWedge 1 r j U hU v) =
    e.hom.app U (framedTensorWedge (-1) r (2 * (r : ℤ)) j U hU v 1)
  have he : (sourceComparison r).hom ≫ e.hom =
      (coordinateIsoTo (I := I) (K := K) 1 r r (by ring)).hom := by
    simp only [sourceComparison, e, Iso.trans_hom, Iso.symm_hom,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [he]
  apply (productSectionsEquiv
    (fun _ : Set.powersetCard I r => Proj.twistingSheaf 𝒜 (r : ℤ)) U).injective
  funext s
  rw [coordinateIsoTo_frame, twistedCoordinateIsoTo_frame, mul_one]

/-- The actual global target comparison preserves the complete scalar
coefficient in the corresponding genuine line frame. -/
theorem targetComparison_frame (r : ℕ) (j : I) (U : (X).Opens)
    (hU : U ≤ ProjectiveCech.coordinateOpen (K := K) j)
    (v : Fin r → I → Γ(X, U)) (a : Γ(X, U)) :
    (targetComparison (I := I) (K := K) r).hom.app U
      (framedTensorWedge 1 r 2 j U hU v a) =
        framedTensorWedge (-1) r (2 * ((r + 1 : ℕ) : ℤ)) j U hU v a := by
  let e := twistedCoordinateIsoTo (I := I) (K := K) (-1) r
    (2 * ((r + 1 : ℕ) : ℤ)) ((r : ℤ) + 2) (by push_cast; ring)
  apply (((SheafOfModules.evaluation (X).ringCatSheaf (op U)).mapIso e).toLinearEquiv).injective
  change ((targetComparison r).hom ≫ e.hom).app U
      (framedTensorWedge 1 r 2 j U hU v a) =
    e.hom.app U
      (framedTensorWedge (-1) r (2 * ((r + 1 : ℕ) : ℤ)) j U hU v a)
  have he : (targetComparison r).hom ≫ e.hom =
      (twistedCoordinateIsoTo (I := I) (K := K) 1 r 2 ((r : ℤ) + 2) (by ring)).hom := by
    simp only [targetComparison, e, Iso.trans_hom, Iso.symm_hom,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [he]
  apply (productSectionsEquiv
    (fun _ : Set.powersetCard I r => Proj.twistingSheaf 𝒜 ((r : ℤ) + 2)) U).injective
  funext s
  rw [twistedCoordinateIsoTo_frame, twistedCoordinateIsoTo_frame]

end PaperVerification.Segre.EulerExteriorTwistMaps

end SegreEulerExteriorTwistMaps

run_cmd do
  (← IO.getStdout).flush
  let out ← IO.getStderr
  out.putStrLn "SEGRE_PROGRESS Stage027.CriticalEuler exterior-twist-maps"
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
