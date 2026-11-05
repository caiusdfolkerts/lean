module

public import PaperVerification.ToricBaseSectionNaturality
public import PaperVerification.ToricFractionDifferentials
public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower

@[expose] public section

/-!
# Intrinsic Kähler sheaves and their ordinary exterior powers

These constructions are defined on every scheme over the base ring,
independently of a fan or a rational differential trivialization. The
cotangent sheaf is the sheafification of the universal Kähler presheaf.
Its universal property for derivations into every actual module sheaf is
proved from the universal algebraic derivation and the sheafification
adjunction. Exterior powers are the sheafifications of the ordinary
sectionwise exterior modules.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

universe u v

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite
open PaperVerification.ToricCharacters
open scoped Classical BaseSections

section Exterior

variable {C : Type u} [Category C] (R : Cᵒᵖ⥤CommRingCat.{v})
    (M : PresheafOfModulesOfCommRing.{v} R) (n : ℕ)

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
set_option backward.isDefEq.respectTransparency false in
def presheafExteriorPowerMap {U V : Cᵒᵖ} (f : U⟶V) :
    (M.obj U).exteriorPower n⟶
      (ModuleCat.restrictScalars (R.map f).hom).obj ((M.obj V).exteriorPower n) := by
  letI := (R.map f).hom.toAlgebra
  letI := Module.compHom (M.obj V) (R.map f).hom
  letI : IsScalarTower (R.obj U) (R.obj V) (M.obj V) := IsScalarTower.of_compHom _ _ _
  exact ModuleCat.ofHom (X := (M.obj U).exteriorPower n)
    (Y := (ModuleCat.restrictScalars (R.map f).hom).obj ((M.obj V).exteriorPower n))
    (exteriorScalarExtensionMap (R := R.obj U) (S := R.obj V)
      (M := M.obj U) (N := M.obj V) (n := n) (M.map f).hom)

@[simp] theorem presheafExteriorPowerMap_wedge {U V : Cᵒᵖ} (f : U⟶V)
    (x : Fin n→M.obj U) :
    presheafExteriorPowerMap R M n f (exteriorPower.ιMulti (R.obj U) n x)=
      exteriorPower.ιMulti (R.obj V) n (fun i=>M.map f (x i)) := by
  letI := (R.map f).hom.toAlgebra
  letI := Module.compHom (M.obj V) (R.map f).hom
  letI : IsScalarTower (R.obj U) (R.obj V) (M.obj V) := IsScalarTower.of_compHom _ _ _
  exact exteriorScalarExtensionMap_wedge (R := R.obj U) (S := R.obj V)
    (M := M.obj U) (N := M.obj V) (n := n) (M.map f).hom x

set_option maxHeartbeats 2000000 in
theorem presheafExteriorPowerMap_id (U : Cᵒᵖ) :
    presheafExteriorPowerMap R M n (𝟙 U) =
      (ModuleCat.restrictScalarsId' (R.map (𝟙 U)).hom
        (congrArg CommRingCat.Hom.hom (R.map_id U))).inv.app
          ((M.obj U).exteriorPower n) := by
  apply ModuleCat.exteriorPower.hom_ext (R := R.obj U) (M := M.obj U)
    (N := (ModuleCat.restrictScalars (R.map (𝟙 U)).hom).obj ((M.obj U).exteriorPower n))
  apply ModuleCat.AlternatingMap.ext
  intro x
  change presheafExteriorPowerMap R M n (𝟙 U)
    (exteriorPower.ιMulti (R.obj U) n x) = exteriorPower.ιMulti (R.obj U) n x
  rw [presheafExteriorPowerMap_wedge]
  congr 1
  funext i
  exact congrArg (fun φ => φ (x i)) (M.map_id U)

set_option maxHeartbeats 2000000 in
theorem presheafExteriorPowerMap_comp {U V W : Cᵒᵖ} (f : U⟶V) (g : V⟶W) :
    presheafExteriorPowerMap R M n (f ≫ g) =
      presheafExteriorPowerMap R M n f ≫
        (ModuleCat.restrictScalars (R.map f).hom).map (presheafExteriorPowerMap R M n g) ≫
          (ModuleCat.restrictScalarsComp' (R.map f).hom (R.map g).hom
            (R.map (f ≫ g)).hom (congrArg CommRingCat.Hom.hom (R.map_comp f g))).inv.app
              ((M.obj W).exteriorPower n) := by
  apply ModuleCat.exteriorPower.hom_ext (R := R.obj U) (M := M.obj U)
    (N := (ModuleCat.restrictScalars (R.map (f ≫ g)).hom).obj ((M.obj W).exteriorPower n))
  apply ModuleCat.AlternatingMap.ext
  intro x
  change presheafExteriorPowerMap R M n (f ≫ g)
    (exteriorPower.ιMulti (R.obj U) n x) =
      presheafExteriorPowerMap R M n g
        (presheafExteriorPowerMap R M n f (exteriorPower.ιMulti (R.obj U) n x))
  calc
    _ = exteriorPower.ιMulti (R.obj W) n
        (fun i : Fin n => (show M.obj W from M.map (f ≫ g) (x i))) :=
      presheafExteriorPowerMap_wedge R M n (f ≫ g) x
    _ = exteriorPower.ιMulti (R.obj W) n
        (fun i : Fin n => (show M.obj W from M.map g (M.map f (x i)))) :=
      congrArg (fun y : Fin n → M.obj W => exteriorPower.ιMulti (R.obj W) n y)
        (funext (fun i => PresheafOfModules.map_comp_apply M f g (x i)))
    _ = presheafExteriorPowerMap R M n g
        (exteriorPower.ιMulti (R.obj V) n
          (fun i : Fin n => (show M.obj V from M.map f (x i)))) :=
      (presheafExteriorPowerMap_wedge R M n g
        (fun i : Fin n => (show M.obj V from M.map f (x i)))).symm
    _ = _ := congrArg (presheafExteriorPowerMap R M n g)
      (presheafExteriorPowerMap_wedge R M n f x).symm

set_option backward.isDefEq.respectTransparency false in
def presheafExteriorPower : PresheafOfModulesOfCommRing.{v} R :=
  PresheafOfModulesOfCommRing.mk (R := R)
    (fun U=>(M.obj U).exteriorPower n)
    (fun f=>presheafExteriorPowerMap R M n f)
    (presheafExteriorPowerMap_id R M n)
    (fun f g=>presheafExteriorPowerMap_comp R M n f g)

@[simp] theorem presheafExteriorPower_map_wedge {U V : Cᵒᵖ} (f : U⟶V)
    (x : Fin n→M.obj U) :
    (presheafExteriorPower R M n).map f (exteriorPower.ιMulti (R.obj U) n x)=
      exteriorPower.ιMulti (R.obj V) n (fun i=>M.map f (x i)) :=
  presheafExteriorPowerMap_wedge R M n f x

variable {M} {N : PresheafOfModulesOfCommRing.{v} R}

set_option maxHeartbeats 2000000 in
def presheafExteriorPowerHom (f : M⟶N) :
    presheafExteriorPower R M n⟶presheafExteriorPower R N n :=
  PresheafOfModulesOfCommRing.homMk (R := R)
    (fun U=>ModuleCat.exteriorPower.map (R := R.obj U) (f.app U) n)
    (by
      intro U V g
      apply ModuleCat.exteriorPower.hom_ext (R := R.obj U) (M := M.obj U)
        (N := (ModuleCat.restrictScalars (R.map g).hom).obj ((N.obj V).exteriorPower n))
      apply ModuleCat.AlternatingMap.ext
      intro x
      change ModuleCat.exteriorPower.map (R := R.obj V) (f.app V) n
          (presheafExteriorPowerMap R M n g (exteriorPower.ιMulti (R.obj U) n x)) =
        presheafExteriorPowerMap R N n g
          (ModuleCat.exteriorPower.map (R := R.obj U) (f.app U) n
            (exteriorPower.ιMulti (R.obj U) n x))
      calc
        _ = ModuleCat.exteriorPower.map (R := R.obj V) (f.app V) n
            (exteriorPower.ιMulti (R.obj V) n
              (fun i : Fin n => (show M.obj V from M.map g (x i)))) :=
          congrArg (ModuleCat.exteriorPower.map (R := R.obj V) (f.app V) n)
            (presheafExteriorPowerMap_wedge R M n g x)
        _ = exteriorPower.ιMulti (R.obj V) n
            (fun i : Fin n => f.app V (M.map g (x i))) :=
          ModuleCat.exteriorPower.map_mk (R := R.obj V) (f.app V)
            (fun i : Fin n => (show M.obj V from M.map g (x i)))
        _ = exteriorPower.ιMulti (R.obj V) n
            (fun i : Fin n => (show N.obj V from N.map g (f.app U (x i)))) :=
          congrArg (fun y : Fin n → N.obj V => exteriorPower.ιMulti (R.obj V) n y)
            (funext (fun i => PresheafOfModules.naturality_apply f g (x i)))
        _ = presheafExteriorPowerMap R N n g
            (exteriorPower.ιMulti (R.obj U) n (fun i : Fin n => f.app U (x i))) :=
          (presheafExteriorPowerMap_wedge R N n g (fun i => f.app U (x i))).symm
        _ = _ := congrArg (presheafExteriorPowerMap R N n g)
          (ModuleCat.exteriorPower.map_mk (R := R.obj U) (f.app U) x).symm)

def presheafExteriorPowerFunctor :
    PresheafOfModulesOfCommRing.{v} R⥤PresheafOfModulesOfCommRing.{v} R where
  obj M := presheafExteriorPower R M n
  map f := presheafExteriorPowerHom R n f
  map_id M := by
    ext U : 1
    change ModuleCat.exteriorPower.map (R := R.obj U) (𝟙 (M.obj U)) n = 𝟙 _
    exact (ModuleCat.exteriorPower.functor (R.obj U) n).map_id (M.obj U)
  map_comp f g := by
    ext U : 1
    change ModuleCat.exteriorPower.map (R := R.obj U) (f.app U ≫ g.app U) n =
      ModuleCat.exteriorPower.map (R := R.obj U) (f.app U) n ≫
        ModuleCat.exteriorPower.map (R := R.obj U) (g.app U) n
    exact (ModuleCat.exteriorPower.functor (R.obj U) n).map_comp (f.app U) (g.app U)

end Exterior

section Schemes

variable (k : Type u) [CommRing k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))]

/-- The actual constant base-ring presheaf maps into the actual structure
presheaf through the given structural morphism of the scheme. -/
def scalarPresheafMap :
    (Functor.const X.Opensᵒᵖ).obj (CommRingCat.of k)⟶X.presheaf where
  app U := CommRingCat.ofHom (BaseSections.scalarMap k X U.unop)
  naturality U V f := by
    ext c
    exact (BaseSections.scalarMap_restrict k f.unop.le c).symm

def differentialPresheaf : PresheafOfModulesOfCommRing.{u} X.presheaf :=
  PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'
    (scalarPresheafMap k X)

def differentialPresheafDerivation :
    (differentialPresheaf k X).Derivation' (scalarPresheafMap k X) :=
  PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation'
    (scalarPresheafMap k X)

def differentialPresheafUniversal :
    (differentialPresheafDerivation k X).Universal :=
  PresheafOfModulesOfCommRing.DifferentialsConstruction.isUniversal'
    (scalarPresheafMap k X)

/-- The intrinsic relative Kähler sheaf. -/
def differentialSheaf : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (differentialPresheaf k X)

def differentialSheafUnit : differentialPresheaf k X⟶(differentialSheaf k X).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app _

def differentialSheafDerivation :
    PresheafOfModulesOfCommRing.Derivation' (R := X.presheaf)
      (differentialSheaf k X).val (scalarPresheafMap k X) :=
  (differentialPresheafDerivation k X).postcomp (differentialSheafUnit k X)

def differentialPresheafHomEquiv (M : PresheafOfModulesOfCommRing.{u} X.presheaf) :
    (differentialPresheaf k X⟶M) ≃ M.Derivation' (scalarPresheafMap k X) where
  toFun f := (differentialPresheafDerivation k X).postcomp f
  invFun d := (differentialPresheafUniversal k X).desc d
  left_inv f := (differentialPresheafUniversal k X).postcomp_injective _ _
    ((differentialPresheafUniversal k X).fac _)
  right_inv d := (differentialPresheafUniversal k X).fac d

/-- The defining universal property of the actual sheaf of Kähler
differentials, for every actual sheaf of structure modules. -/
def differentialSheafHomEquiv (M : X.Modules) :
    (differentialSheaf k X⟶M) ≃
      PresheafOfModulesOfCommRing.Derivation' (R := X.presheaf) M.val
        (scalarPresheafMap k X) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv
    (differentialPresheaf k X) M).trans (differentialPresheafHomEquiv k X M.val)

theorem differentialSheafHomEquiv_apply (M : X.Modules)
    (f : differentialSheaf k X⟶M) :
    differentialSheafHomEquiv k X M f=
      (differentialSheafDerivation k X).postcomp f.val := by
  ext U r
  change (((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).homEquiv (differentialPresheaf k X) M f).app U)
      ((differentialPresheafDerivation k X).d r) =
    f.val.app U (((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).unit.app (differentialPresheaf k X)).app U
      ((differentialPresheafDerivation k X).d r))
  rw [Adjunction.homEquiv_unit]
  rfl

/-- The ordinary exterior power of a module sheaf, constructed by
sheafifying the ordinary exterior powers of its section modules. -/
def sheafExteriorPower (M : X.Modules) (n : ℕ) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (presheafExteriorPower X.presheaf M.val n)

def sheafExteriorPowerIso {M N : X.Modules} (e : M≅N) (n : ℕ) :
    sheafExteriorPower X M n≅sheafExteriorPower X N n :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    ((presheafExteriorPowerFunctor X.presheaf n).mapIso
      ((SheafOfModules.forget _).mapIso e))

/-- The intrinsic top differential sheaf; on a smooth n-dimensional
scheme this is its ordinary canonical invertible sheaf. -/
def topDifferentialSheaf (n : ℕ) : X.Modules :=
  sheafExteriorPower X (differentialSheaf k X) n

end Schemes
end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.differentialSheafHomEquiv
