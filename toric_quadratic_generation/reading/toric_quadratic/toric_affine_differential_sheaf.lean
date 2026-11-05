module

public import PaperVerification.ToricIntrinsicDifferentialSheaf
public import PaperVerification.ToricModuleBasisComparison
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Localization.Module

@[expose] public section

/-!
# The intrinsic differential sheaf on an actual affine scheme

On every principal open D(f), the universal Kähler module of the actual
regular-function ring and the sections of the actual tilde module are
both localizations of Ω[R/k]. Their unique localization isomorphism
commutes with the actual restriction maps. Extending on the principal
open basis and sheafifying proves the affine comparison, without
postulating quasi-coherence of the differential sheaf.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

attribute [local instance] SMulCommClass.of_commMonoid

variable (k R : Type u) [CommRing k] [CommRing R] [Algebra k R]

local notation "X" => Spec (CommRingCat.of R)
local notation "ΩR" => KaehlerDifferential k R
local notation "M" => ModuleCat.of R ΩR
local notation "P" => differentialPresheaf k X
local notation "Q" => tilde (R := CommRingCat.of R) M

local instance affineBaseSectionsAlgebra (U : (X).Opens) : Algebra k Γ(X,U) :=
  BaseSections.sectionsAlgebra k X U

local instance affineCoordinateAlgebra (U : (X).Opens) : Algebra R Γ(X,U) :=
  inferInstanceAs (Algebra R
    ((Spec.structureSheaf (CommRingCat.of R)).presheaf.obj (op U)))

local instance affinePrincipalLocalization (f : R) :
    IsLocalization.Away f Γ(X,PrimeSpectrum.basicOpen f) :=
  inferInstanceAs (IsLocalization.Away (f : CommRingCat.of R)
    ((Spec.structureSheaf (CommRingCat.of R)).obj.obj (op (PrimeSpectrum.basicOpen f))))

local instance affineTildeSectionsModule (U : (X).Opens) : Module R Γ(Q,U) :=
  (((modulesSpecToSheaf (R := CommRingCat.of R)).obj Q).presheaf.obj (op U)).isModule

local instance affineTildeSectionsScalarTower (U : (X).Opens) :
    IsScalarTower R Γ(X,U) Γ(Q,U) :=
  IsScalarTower.of_compHom R Γ(X,U) Γ(Q,U)

local instance affineTildeToBasic_isLocalized (f : R) :
    IsLocalizedModule (.powers f)
      (show ΩR →ₗ[R] Γ(Q,PrimeSpectrum.basicOpen f) from
        (tilde.toOpen (R := CommRingCat.of R) M (PrimeSpectrum.basicOpen f)).hom) :=
  IsLocalizedModule.of_linearEquiv (.powers f)
    (StructureSheaf.toOpenₗ (CommRingCat.of R) M (PrimeSpectrum.basicOpen f))
    ((tilde.modulesSpecToSheafIso (R := CommRingCat.of R) M).app _).toLinearEquiv.symm

theorem affine_base_scalar_tower (U : (X).Opens) :
    IsScalarTower k R Γ(X,U) := by
  apply IsScalarTower.of_algebraMap_eq
  intro c
  change BaseSections.scalarMap k X U c=
    algebraMap R Γ(X,U) (algebraMap k R c)
  change BaseSections.scalarMap k X U c=
    (X).presheaf.map (homOfLE le_top).op
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv (algebraMap k R c))
  rw [← BaseSections.scalarMap_affine_top,
    BaseSections.scalarMap_restrict]

local instance affineBaseScalarTower (U : (X).Opens) : IsScalarTower k R Γ(X,U) :=
  affine_base_scalar_tower k R U

local instance affineDifferentialModule (U : (X).Opens) :
    Module R ((P).obj (op U)) :=
  inferInstanceAs (Module R (KaehlerDifferential k Γ(X,U)))

local instance affineDifferentialScalarTower (U : (X).Opens) :
    IsScalarTower R Γ(X,U) ((P).obj (op U)) :=
  inferInstanceAs (IsScalarTower R Γ(X,U) (KaehlerDifferential k Γ(X,U)))

local instance affineDifferentialBaseModule (U : (X).Opens) :
    Module k ((P).obj (op U)) :=
  inferInstanceAs (Module k (KaehlerDifferential k Γ(X,U)))

local instance affineDifferentialBaseScalarTower (U : (X).Opens) :
    IsScalarTower k R ((P).obj (op U)) :=
  inferInstanceAs (IsScalarTower k R (KaehlerDifferential k Γ(X,U)))

/-- The canonical algebraic differential map into the actual principal
open's differential module. -/
def affineDifferentialToBasic (f : R) :
    ΩR→ₗ[R](P).obj (op (PrimeSpectrum.basicOpen f)) :=
  KaehlerDifferential.map k k R Γ(X,PrimeSpectrum.basicOpen f)

instance affineDifferentialToBasic_isLocalized (f : R) :
    IsLocalizedModule.Away f (affineDifferentialToBasic k R f) := by
  change IsLocalizedModule (.powers f)
    (KaehlerDifferential.map k k R Γ(X,PrimeSpectrum.basicOpen f))
  infer_instance

@[simp] theorem affineDifferentialToBasic_D (f r : R) :
    affineDifferentialToBasic k R f (KaehlerDifferential.D k R r)=
      CommRingCat.KaehlerDifferential.d
        (f := (scalarPresheafMap k X).app (op (PrimeSpectrum.basicOpen f)))
        (algebraMap R Γ(X,PrimeSpectrum.basicOpen f) r) :=
  KaehlerDifferential.map_D k k R Γ(X,PrimeSpectrum.basicOpen f) r

/-- The actual principal-open Kähler/tilde comparison. It is linear
over Γ(D(f),O), not only over the original affine coordinate ring. -/
def affineDifferentialBasicEquiv (f : R) :
    (P).obj (op (PrimeSpectrum.basicOpen f))≃ₗ[Γ(X,PrimeSpectrum.basicOpen f)]
      Γ(Q,PrimeSpectrum.basicOpen f) :=
  (IsLocalizedModule.linearEquiv (.powers f)
    (affineDifferentialToBasic k R f)
    (show ΩR →ₗ[R] Γ(Q,PrimeSpectrum.basicOpen f) from
      (tilde.toOpen (R := CommRingCat.of R) M (PrimeSpectrum.basicOpen f)).hom)).extendScalarsOfIsLocalization
      (.powers f) Γ(X,PrimeSpectrum.basicOpen f)

@[simp] theorem affineDifferentialBasicEquiv_toOpen (f : R) (ω : ΩR) :
    affineDifferentialBasicEquiv k R f (affineDifferentialToBasic k R f ω)=
      tilde.toOpen (R := CommRingCat.of R) M (PrimeSpectrum.basicOpen f) ω :=
  IsLocalizedModule.linearEquiv_apply (.powers f)
    (affineDifferentialToBasic k R f)
    (show ΩR →ₗ[R] Γ(Q,PrimeSpectrum.basicOpen f) from
      (tilde.toOpen (R := CommRingCat.of R) M (PrimeSpectrum.basicOpen f)).hom) ω

theorem affine_algebraMap_restrict {U V : (X).Opens} (h : V≤U) (r : R) :
    (X).presheaf.map (homOfLE h).op (algebraMap R Γ(X,U) r)=
      algebraMap R Γ(X,V) r := by
  change (X).presheaf.map (homOfLE h).op
      ((X).presheaf.map (homOfLE le_top).op ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) =
    (X).presheaf.map (homOfLE le_top).op ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)
  exact congrArg (fun φ=>φ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))
    ((X).presheaf.map_comp (homOfLE le_top).op (homOfLE h).op).symm

def affineDifferentialBasicRestriction (f g : R)
    (h : PrimeSpectrum.basicOpen g≤PrimeSpectrum.basicOpen f) :
    (P).obj (op (PrimeSpectrum.basicOpen f))→ₗ[R]
      (P).obj (op (PrimeSpectrum.basicOpen g)) where
  toFun := (P).map (homOfLE h).op
  map_add' := map_add ((P).map (homOfLE h).op).hom
  map_smul' r ω := by
    let φ : (P).obj (op (PrimeSpectrum.basicOpen f)) →
        (P).obj (op (PrimeSpectrum.basicOpen g)) :=
      fun η => (P).map (homOfLE h).op η
    change φ (r • ω) = r • φ ω
    calc
      _ = φ (algebraMap R Γ(X,PrimeSpectrum.basicOpen f) r • ω) :=
        congrArg φ
          (IsScalarTower.algebraMap_smul Γ(X,PrimeSpectrum.basicOpen f) r ω).symm
      _ = (X).presheaf.map (homOfLE h).op
          (algebraMap R Γ(X,PrimeSpectrum.basicOpen f) r) • φ ω :=
        (P).map_smul (homOfLE h).op (algebraMap R Γ(X,PrimeSpectrum.basicOpen f) r) ω
      _ = algebraMap R Γ(X,PrimeSpectrum.basicOpen g) r • φ ω :=
        congrArg (fun c : Γ(X,PrimeSpectrum.basicOpen g) => c • φ ω)
          (affine_algebraMap_restrict R h r)
      _ = r • φ ω :=
        IsScalarTower.algebraMap_smul Γ(X,PrimeSpectrum.basicOpen g) r (φ ω)

theorem affineDifferentialBasicRestriction_toBasic (f g : R)
    (h : PrimeSpectrum.basicOpen g≤PrimeSpectrum.basicOpen f) :
    (affineDifferentialBasicRestriction k R f g h).comp
      (affineDifferentialToBasic k R f)=affineDifferentialToBasic k R g := by
  apply Derivation.liftKaehlerDifferential_unique
  ext r
  change (P).map (homOfLE h).op
    (affineDifferentialToBasic k R f (KaehlerDifferential.D k R r))=
      affineDifferentialToBasic k R g (KaehlerDifferential.D k R r)
  calc
    _ = (P).map (homOfLE h).op
        (CommRingCat.KaehlerDifferential.d
          (f := (scalarPresheafMap k X).app (op (PrimeSpectrum.basicOpen f)))
          (algebraMap R Γ(X,PrimeSpectrum.basicOpen f) r)) :=
      congrArg ((P).map (homOfLE h).op) (affineDifferentialToBasic_D k R f r)
    _ = CommRingCat.KaehlerDifferential.d
        (f := (scalarPresheafMap k X).app (op (PrimeSpectrum.basicOpen g)))
        ((X).presheaf.map (homOfLE h).op
          (algebraMap R Γ(X,PrimeSpectrum.basicOpen f) r)) :=
      PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'_map_d
        (scalarPresheafMap k X) (homOfLE h).op
        (algebraMap R Γ(X,PrimeSpectrum.basicOpen f) r)
    _ = CommRingCat.KaehlerDifferential.d
        (f := (scalarPresheafMap k X).app (op (PrimeSpectrum.basicOpen g)))
        (algebraMap R Γ(X,PrimeSpectrum.basicOpen g) r) :=
      congrArg (CommRingCat.KaehlerDifferential.d
        (f := (scalarPresheafMap k X).app (op (PrimeSpectrum.basicOpen g))))
        (affine_algebraMap_restrict R h r)
    _ = _ := (affineDifferentialToBasic_D k R g r).symm

/-- The unique localization comparison commutes with all inclusions
between genuine principal opens. -/
theorem affineDifferentialBasicEquiv_natural (f g : R)
    (h : PrimeSpectrum.basicOpen g≤PrimeSpectrum.basicOpen f)
    (ω : (P).obj (op (PrimeSpectrum.basicOpen f))) :
    affineDifferentialBasicEquiv k R g ((P).map (homOfLE h).op ω)=
      (Q).presheaf.map (homOfLE h).op (affineDifferentialBasicEquiv k R f ω) := by
  let L : (P).obj (op (PrimeSpectrum.basicOpen f))→ₗ[R]
      Γ(Q,PrimeSpectrum.basicOpen g) :=
    (affineDifferentialBasicEquiv k R g).toLinearMap.restrictScalars R ∘ₗ
      affineDifferentialBasicRestriction k R f g h
  let H : (P).obj (op (PrimeSpectrum.basicOpen f))→ₗ[R]
      Γ(Q,PrimeSpectrum.basicOpen g) :=
    (((modulesSpecToSheaf (R := CommRingCat.of R)).obj Q).presheaf.map (homOfLE h).op).hom ∘ₗ
      (affineDifferentialBasicEquiv k R f).toLinearMap.restrictScalars R
  have hLH : L=H := by
    apply IsLocalizedModule.ext (.powers f) (affineDifferentialToBasic k R f)
    · intro z
      obtain ⟨m,hm⟩ := z.property
      change IsUnit (algebraMap R (Module.End R Γ(Q,PrimeSpectrum.basicOpen g)) z.val)
      rw [← hm,map_pow]
      exact ((Q).isUnit_algebraMap_end_of_le_basicOpen f h).pow m
    · ext η
      change affineDifferentialBasicEquiv k R g
        ((affineDifferentialBasicRestriction k R f g h)
          (affineDifferentialToBasic k R f η))=
        (Q).presheaf.map (homOfLE h).op
          (affineDifferentialBasicEquiv k R f (affineDifferentialToBasic k R f η))
      rw [show (affineDifferentialBasicRestriction k R f g h)
          (affineDifferentialToBasic k R f η)=affineDifferentialToBasic k R g η from
        congrArg (fun l=>l η) (affineDifferentialBasicRestriction_toBasic k R f g h),
        affineDifferentialBasicEquiv_toOpen,affineDifferentialBasicEquiv_toOpen]
      exact (congrArg (fun l=>l η)
        (tilde.toOpen_res (R := CommRingCat.of R) M (PrimeSpectrum.basicOpen f)
          (PrimeSpectrum.basicOpen g) (homOfLE h))).symm
  exact congrArg (fun l=>l ω) hLH

set_option maxHeartbeats 2000000 in
/-- The intrinsic sheafification of universal differentials is the
ordinary tilde sheaf of the ordinary algebraic Kähler module. -/
def affineDifferentialSheafIso : differentialSheaf k X≅tilde (R := CommRingCat.of R) M :=
  basisModuleSheafificationIso («X» := Spec (CommRingCat.of R))
    (fun f : R=>PrimeSpectrum.basicOpen f)
    PrimeSpectrum.isBasis_basic_opens P Q
    (fun f=>(affineDifferentialBasicEquiv k R f).toLinearMap)
    (affineDifferentialBasicEquiv_natural k R)
    (fun f=>(affineDifferentialBasicEquiv k R f).bijective)

set_option maxHeartbeats 2000000 in
theorem affineDifferentialSheafIso_basic (f : R)
    (ω : (P).obj (op (PrimeSpectrum.basicOpen f))) :
    (affineDifferentialSheafIso k R).hom.app (PrimeSpectrum.basicOpen f)
      ((differentialSheafUnit k X).app (op (PrimeSpectrum.basicOpen f)) ω)=
        affineDifferentialBasicEquiv k R f ω := by
  exact basisModuleSheafificationIso_app («X» := Spec (CommRingCat.of R))
    (fun f : R=>PrimeSpectrum.basicOpen f) PrimeSpectrum.isBasis_basic_opens P Q
    (fun f=>(affineDifferentialBasicEquiv k R f).toLinearMap)
    (affineDifferentialBasicEquiv_natural k R)
    (fun f=>(affineDifferentialBasicEquiv k R f).bijective) f ω

/-- The comparison sends the actual differential of the restriction of
r to the actual restriction of the algebraic differential d r. -/
theorem affineDifferentialSheafIso_D (f r : R) :
    (affineDifferentialSheafIso k R).hom.app (PrimeSpectrum.basicOpen f)
      ((differentialSheafDerivation k X).d
        («X» := op (PrimeSpectrum.basicOpen f))
        (algebraMap R Γ(X,PrimeSpectrum.basicOpen f) r))=
      tilde.toOpen (R := CommRingCat.of R) M (PrimeSpectrum.basicOpen f) (KaehlerDifferential.D k R r) := by
  change (affineDifferentialSheafIso k R).hom.app (PrimeSpectrum.basicOpen f)
    ((differentialSheafUnit k X).app (op (PrimeSpectrum.basicOpen f))
      (CommRingCat.KaehlerDifferential.d
        (f := (scalarPresheafMap k X).app (op (PrimeSpectrum.basicOpen f)))
        (algebraMap R Γ(X,PrimeSpectrum.basicOpen f) r))) = _
  rw [← affineDifferentialToBasic_D k R f r,
    affineDifferentialSheafIso_basic,affineDifferentialBasicEquiv_toOpen]

end PaperVerification.ToricSchemes
