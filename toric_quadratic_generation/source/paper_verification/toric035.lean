module

public import Lean.Elab.BuiltinEvalCommand
public meta import Lean.Elab.BuiltinEvalCommand
public import Lean.Util.CollectAxioms
public meta import Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public meta import Lean.Util.FoldConsts
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.OfCommRing
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import paper_verification.toric010
public import paper_verification.toric013
public import paper_verification.toric034

@[expose] public section


-- BEGIN ORIGINAL PaperVerification.ToricModuleBasisComparison
section Source_ToricModuleBasisComparison

-- original header: module

-- original header: public import PaperVerification.ToricModuleFrameGluing
-- original header: public import Mathlib.Algebra.Category.ModuleCat.Presheaf.OfCommRing
-- original header: public import Mathlib.Topology.Sheaves.SheafCondition.Sites
-- original header: public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization

-- original header: @[expose] public section

/-!
# Module comparisons constructed on an actual topological basis

Compatible module maps on basis opens extend uniquely to a map from a
module presheaf into a module sheaf. If the maps on the basis are
bijective, the extension becomes an isomorphism after actual
sheafification. No quasi-coherence or stalk comparison is assumed.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

universe u v

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

variable {X : Scheme.{u}} {ι : Type v} (B : ι→X.Opens)
    (hB : Opens.IsBasis (Set.range B))
    (P : PresheafOfModulesOfCommRing.{u} X.presheaf) (Q : X.Modules)
    (β : ∀ i,P.obj (op (B i))→ₗ[Γ(X,B i)] Γ(Q,B i))
    (hβ : ∀ i j (h : B j≤B i) (s : P.obj (op (B i))),
      β j (P.map (homOfLE h).op s)=Q.presheaf.map (homOfLE h).op (β i s))

def basisModuleComparisonOnBasis :
    (inducedFunctor B).op⋙P.presheaf ⟶ (inducedFunctor B).op⋙Q.presheaf where
  app i := AddCommGrpCat.ofHom (β i.unop).toAddMonoidHom
  naturality i j f := by
    ext s
    exact hβ i.unop j.unop f.unop.hom.le s

def basisModuleComparisonAdditive : P.presheaf⟶Q.presheaf :=
  TopCat.Sheaf.restrictHomEquivHom P.presheaf ⟨Q.presheaf,Q.isSheaf⟩ hB
    (basisModuleComparisonOnBasis B P Q β hβ)

@[simp] theorem basisModuleComparisonAdditive_app (i : ι)
    (s : P.obj (op (B i))) :
    (basisModuleComparisonAdditive B hB P Q β hβ).app (op (B i)) s=β i s := by
  exact congrArg
    (fun f : P.presheaf.obj (op (B i)) ⟶ Q.presheaf.obj (op (B i)) => f s)
    (TopCat.Sheaf.extend_hom_app P.presheaf ⟨Q.presheaf,Q.isSheaf⟩ hB
      (basisModuleComparisonOnBasis B P Q β hβ) i)

theorem basisModuleComparisonAdditive_smul (U : X.Opens)
    (a : Γ(X,U)) (s : P.obj (op U)) :
    (basisModuleComparisonAdditive B hB P Q β hβ).app (op U) (a • s)=
      a • (basisModuleComparisonAdditive B hB P Q β hβ).app (op U) s := by
  let φ := basisModuleComparisonAdditive B hB P Q β hβ
  apply TopCat.Presheaf.IsSheaf.section_ext Q.isSheaf
  intro x hx
  obtain ⟨V,⟨i,rfl⟩,hi,hVU⟩ := Opens.isBasis_iff_nbhd.mp hB hx
  refine ⟨B i,hVU,hi,?_⟩
  erw [← NatTrans.naturality_apply φ (homOfLE hVU).op,
    Q.map_smul,← NatTrans.naturality_apply φ (homOfLE hVU).op]
  change φ.app (op (B i)) (P.map (homOfLE hVU).op (a • s))=
    X.presheaf.map (homOfLE hVU).op a • φ.app (op (B i)) (P.map (homOfLE hVU).op s)
  dsimp only [φ]
  rw [basisModuleComparisonAdditive_app,basisModuleComparisonAdditive_app]
  exact (congrArg (β i) (P.map_smul (homOfLE hVU).op a s)).trans
    ((β i).map_smul _ _)

/-- The extension is genuinely linear over the section ring on every
open, as follows from the actual sheaf separation axiom. -/
def basisModuleComparison : P⟶Q.val :=
  PresheafOfModulesOfCommRing.homMk (R := X.presheaf)
    (fun U => ModuleCat.ofHom
      ({ toFun := (basisModuleComparisonAdditive B hB P Q β hβ).app U
         map_add' := map_add _
         map_smul' := basisModuleComparisonAdditive_smul B hB P Q β hβ U.unop } :
        P.obj U →ₗ[Γ(X,U.unop)] Γ(Q,U.unop)))
    (by
      intro U V f
      ext s
      exact NatTrans.naturality_apply
        (basisModuleComparisonAdditive B hB P Q β hβ) f s)

@[simp] theorem basisModuleComparison_app (i : ι)
    (s : P.obj (op (B i))) :
    (basisModuleComparison B hB P Q β hβ).app (op (B i)) s=β i s :=
  basisModuleComparisonAdditive_app B hB P Q β hβ i s

theorem basisModuleComparison_locallyInjective
    (hinj : ∀ i,Function.Injective (β i)) :
    CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        (basisModuleComparison B hB P Q β hβ)) := by
  constructor
  intro U s t h x hx
  obtain ⟨V,⟨i,rfl⟩,hi,hVU⟩ := Opens.isBasis_iff_nbhd.mp hB hx
  refine ⟨B i,homOfLE hVU,?_,hi⟩
  apply hinj i
  change β i (P.map (homOfLE hVU).op s) = β i (P.map (homOfLE hVU).op t)
  calc
    _ = (basisModuleComparison B hB P Q β hβ).app (op (B i))
          (P.map (homOfLE hVU).op s) :=
      (basisModuleComparison_app B hB P Q β hβ i _).symm
    _ = Q.val.map (homOfLE hVU).op
          ((basisModuleComparison B hB P Q β hβ).app U s) :=
      PresheafOfModules.naturality_apply _ _ _
    _ = Q.val.map (homOfLE hVU).op
          ((basisModuleComparison B hB P Q β hβ).app U t) :=
      congrArg (Q.presheaf.map (homOfLE hVU).op) h
    _ = (basisModuleComparison B hB P Q β hβ).app (op (B i))
          (P.map (homOfLE hVU).op t) :=
      (PresheafOfModules.naturality_apply
        (basisModuleComparison B hB P Q β hβ) (homOfLE hVU).op t).symm
    _ = β i (P.map (homOfLE hVU).op t) :=
      basisModuleComparison_app B hB P Q β hβ i _

theorem basisModuleComparison_locallySurjective
    (hsurj : ∀ i,Function.Surjective (β i)) :
    CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        (basisModuleComparison B hB P Q β hβ)) := by
  constructor
  intro U s x hx
  obtain ⟨V,⟨i,rfl⟩,hi,hVU⟩ := Opens.isBasis_iff_nbhd.mp hB hx
  obtain ⟨t,ht⟩ := hsurj i (Q.presheaf.map (homOfLE hVU).op s)
  exact ⟨B i,homOfLE hVU,⟨t,(basisModuleComparison_app B hB P Q β hβ i t).trans ht⟩,hi⟩

theorem basisModuleComparison_sheafification_isIso
    (hbij : ∀ i,Function.Bijective (β i)) :
    IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (basisModuleComparison B hB P Q β hβ)) := by
  letI := basisModuleComparison_locallyInjective B hB P Q β hβ (fun i=>(hbij i).1)
  letI := basisModuleComparison_locallySurjective B hB P Q β hβ (fun i=>(hbij i).2)
  have hW := (Opens.grothendieckTopology X).W_of_isLocallyBijective
    ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
      (basisModuleComparison B hB P Q β hβ))
  change ((Opens.grothendieckTopology X).W.inverseImage
    (PresheafOfModules.toPresheaf X.ringCatSheaf.obj))
      (basisModuleComparison B hB P Q β hβ) at hW
  rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
    (𝟙 X.ringCatSheaf.obj)] at hW
  exact hW

/-- The canonical comparison with the actual sheafification. -/
def basisModuleSheafificationIso (hbij : ∀ i,Function.Bijective (β i)) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P≅Q := by
  letI := basisModuleComparison_sheafification_isIso B hB P Q β hβ hbij
  exact asIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (basisModuleComparison B hB P Q β hβ)) ≪≫
    asIso ((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).counit.app Q)

theorem basisModuleSheafificationIso_unit (hbij : ∀ i,Function.Bijective (β i)) :
    (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).unit.app P ≫
      (basisModuleSheafificationIso B hB P Q β hβ hbij).hom.val=
        basisModuleComparison B hB P Q β hβ := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  have h : (adj.homEquiv P Q).symm (basisModuleComparison B hB P Q β hβ)=
      (basisModuleSheafificationIso B hB P Q β hβ hbij).hom := by
    rw [Adjunction.homEquiv_counit]
    rfl
  have he := congrArg (adj.homEquiv P Q) h
  ext U s
  have he' := congrArg (fun φ => φ.app U s) he
  simp only [Equiv.apply_symm_apply,Adjunction.homEquiv_unit,
    PresheafOfModules.comp_app,ConcreteCategory.comp_apply] at he'
  dsimp only [Functor.comp_obj,Functor.comp_map,SheafOfModules.forget,
    PresheafOfModules.restrictScalars,PresheafOfModules.restrictScalarsObj,
    ModuleCat.restrictScalars,ModuleCat.RestrictScalars.obj',
    ModuleCat.RestrictScalars.map'] at he'
  exact he'.symm

/-- The comparison after the actual sheafification unit agrees with
its specified linear map on every member of the genuine open basis. -/
theorem basisModuleSheafificationIso_app (hbij : ∀ i,Function.Bijective (β i))
    (i : ι) (s : P.obj (op (B i))) :
    (basisModuleSheafificationIso B hB P Q β hβ hbij).hom.app (B i)
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit.app P).app (op (B i)) s) = β i s := by
  have h := congrArg (fun φ : P ⟶ Q.val => φ.app (op (B i)) s)
    (basisModuleSheafificationIso_unit B hB P Q β hβ hbij)
  have h' : (basisModuleSheafificationIso B hB P Q β hβ hbij).hom.app (B i)
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit.app P).app (op (B i)) s) =
      (basisModuleComparison B hB P Q β hβ).app (op (B i)) s := by
    change (basisModuleSheafificationIso B hB P Q β hβ hbij).hom.app (B i)
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit.app P).app (op (B i)) s) =
      (basisModuleComparison B hB P Q β hβ).app (op (B i)) s at h
    exact h
  exact h'.trans (basisModuleComparison_app B hB P Q β hβ i s)

end PaperVerification.ToricSchemes
end
end Source_ToricModuleBasisComparison
-- END ORIGINAL PaperVerification.ToricModuleBasisComparison


-- BEGIN ORIGINAL PaperVerification.ToricAffineDifferentialSheaf
section Source_ToricAffineDifferentialSheaf

-- original header: module

-- original header: public import PaperVerification.ToricIntrinsicDifferentialSheaf
-- original header: public import PaperVerification.ToricModuleBasisComparison
-- original header: public import Mathlib.AlgebraicGeometry.Modules.Tilde
-- original header: public import Mathlib.RingTheory.Etale.Kaehler
-- original header: public import Mathlib.RingTheory.Localization.Module

-- original header: @[expose] public section

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
end
end Source_ToricAffineDifferentialSheaf
-- END ORIGINAL PaperVerification.ToricAffineDifferentialSheaf


-- BEGIN ORIGINAL PaperVerification.ToricAffineExteriorSheaf
section Source_ToricAffineExteriorSheaf

-- original header: module

-- original header: public import PaperVerification.ToricAffineDifferentialSheaf
-- original header: public import PaperVerification.ToricLogarithmicVolume

-- original header: @[expose] public section

/-!
# Actual top exterior powers of free affine module sheaves

The comparison is proved for every finite free module of the stated
rank, including rank zero. The top exterior coefficient on each
principal open is computed in the genuinely localized basis. These
coefficients commute with actual restriction and therefore give the
ordinary tilde/exterior comparison after sheafification. In the toric
application the input basis is the already computed Kähler basis of a
genuine polynomial chart.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open PaperVerification.ToricCharacters
open scoped Classical

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

variable (R : CommRingCat.{u}) (M : ModuleCat.{u} R) {n : ℕ}
    (b : Module.Basis (Fin n) R M)

local notation "X" => Spec R
local notation "Q" => tilde M
local notation "W" => ModuleCat.of R (⋀[R]^n M)
local notation "P" => presheafExteriorPower
  (PresheafedSpace.presheaf (SheafedSpace.toPresheafedSpace
    (LocallyRingedSpace.toSheafedSpace (Scheme.toLocallyRingedSpace (Spec R)))))
  (SheafOfModules.val (tilde M)) n

local instance tildeToOpen_isLocalized (f : R) :
    IsLocalizedModule (.powers f)
      (show M →ₗ[R] Γ(Q,PrimeSpectrum.basicOpen f) from
        (tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom) :=
  inferInstanceAs (IsLocalizedModule.Away f
    (tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom)

def tildeLocalizedBasis (f : R) :
    Module.Basis (Fin n) Γ(X,PrimeSpectrum.basicOpen f) Γ(Q,PrimeSpectrum.basicOpen f) :=
  b.ofIsLocalizedModule Γ(X,PrimeSpectrum.basicOpen f) (.powers f)
    (show M →ₗ[R] Γ(Q,PrimeSpectrum.basicOpen f) from
      (tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom)

@[simp] theorem tildeLocalizedBasis_apply (f : R) (i : Fin n) :
    tildeLocalizedBasis R M b f i=tilde.toOpen M (PrimeSpectrum.basicOpen f) (b i) :=
  Module.Basis.ofIsLocalizedModule_apply _ _ _ _ _

theorem tildeLocalizedBasis_restrict (f g : R)
    (h : PrimeSpectrum.basicOpen g≤PrimeSpectrum.basicOpen f) (i : Fin n) :
    (Q).presheaf.map (homOfLE h).op (tildeLocalizedBasis R M b f i)=
      tildeLocalizedBasis R M b g i := by
  rw [tildeLocalizedBasis_apply,tildeLocalizedBasis_apply]
  exact congrArg (fun φ=>φ (b i))
    (tilde.toOpen_res M (PrimeSpectrum.basicOpen f) (PrimeSpectrum.basicOpen g) (homOfLE h))

/-- The actual global frame of the tilde top module coming from the
ordinary determinant coefficient of the given basis. -/
def tildeTopBasisFrame : tilde W≅SheafOfModules.unit (X).ringCatSheaf :=
  (tilde.functor R).mapIso (basisTopExteriorEquiv b).toModuleIso ≪≫ tildeSelf

def tildeTopBasisCoordinates (U : (X).Opens) : Γ(tilde W,U)≃ₗ[Γ(X,U)] Γ(X,U) :=
  ((PresheafOfModules.evaluation (X).ringCatSheaf.obj (op U)).mapIso
    ((SheafOfModules.forget _).mapIso (tildeTopBasisFrame R M b))).toLinearEquiv

theorem tildeTopBasisCoordinates_restrict {U V : (X).Opens} (h : V≤U)
    (s : Γ(tilde W,U)) :
    tildeTopBasisCoordinates R M b V ((tilde W).presheaf.map (homOfLE h).op s)=
      (X).presheaf.map (homOfLE h).op (tildeTopBasisCoordinates R M b U s) :=
  PresheafOfModules.naturality_apply (tildeTopBasisFrame R M b).hom.val
    (homOfLE h).op s

theorem tildeTopBasisCoordinates_toOpen (U : (X).Opens) (ω : ⋀[R]^n M) :
    tildeTopBasisCoordinates R M b U (tilde.toOpen W U ω)=
      algebraMap R Γ(X,U) (basisTopExteriorEquiv b ω) := by
  calc
    _ = tilde.toOpen (ModuleCat.of R R) U (basisTopExteriorEquiv b ω) := by
      exact congrArg (fun φ=>φ ω)
        (tilde.toOpen_map_app (basisTopExteriorEquiv b).toModuleIso.hom U)
    _ = _ := rfl

/-- The coefficient comparison is an equivalence over the actual
principal-open structure ring. -/
def affineTopExteriorBasicEquiv (f : R) :
    (P).obj (op (PrimeSpectrum.basicOpen f))≃ₗ[Γ(X,PrimeSpectrum.basicOpen f)]
      Γ(tilde W,PrimeSpectrum.basicOpen f) :=
  (basisTopExteriorEquiv (tildeLocalizedBasis R M b f)).trans
    (tildeTopBasisCoordinates R M b (PrimeSpectrum.basicOpen f)).symm

theorem localizedTopCoefficient_restrict (f g : R)
    (h : PrimeSpectrum.basicOpen g≤PrimeSpectrum.basicOpen f)
    (ω : (P).obj (op (PrimeSpectrum.basicOpen f))) :
    basisTopExteriorEquiv (tildeLocalizedBasis R M b g) ((P).map (homOfLE h).op ω)=
      (X).presheaf.map (homOfLE h).op
        (basisTopExteriorEquiv (tildeLocalizedBasis R M b f) ω) := by
  let c := basisTopExteriorEquiv (tildeLocalizedBasis R M b f) ω
  have hω : ω=c • exteriorPower.ιMulti Γ(X,PrimeSpectrum.basicOpen f) n
      (tildeLocalizedBasis R M b f) :=
    topExterior_eq_smul_basis (tildeLocalizedBasis R M b f) ω
  calc
    basisTopExteriorEquiv (tildeLocalizedBasis R M b g) ((P).map (homOfLE h).op ω)=
        basisTopExteriorEquiv (tildeLocalizedBasis R M b g)
          ((P).map (homOfLE h).op
            (c • exteriorPower.ιMulti Γ(X,PrimeSpectrum.basicOpen f) n
              (tildeLocalizedBasis R M b f))) := congrArg _ (congrArg _ hω)
    _ = basisTopExteriorEquiv (tildeLocalizedBasis R M b g)
        ((X).presheaf.map (homOfLE h).op c •
          (P).map (homOfLE h).op
            (exteriorPower.ιMulti Γ(X,PrimeSpectrum.basicOpen f) n
              (tildeLocalizedBasis R M b f))) :=
      congrArg (fun z : (P).obj (op (PrimeSpectrum.basicOpen g)) =>
        basisTopExteriorEquiv (tildeLocalizedBasis R M b g) z)
        ((P).map_smul (homOfLE h).op c
          (exteriorPower.ιMulti Γ(X,PrimeSpectrum.basicOpen f) n
            (tildeLocalizedBasis R M b f)))
    _ = basisTopExteriorEquiv (tildeLocalizedBasis R M b g)
        ((X).presheaf.map (homOfLE h).op c •
          exteriorPower.ιMulti Γ(X,PrimeSpectrum.basicOpen g) n
            (tildeLocalizedBasis R M b g)) := by
      have hw : (P).map (homOfLE h).op
          (exteriorPower.ιMulti Γ(X,PrimeSpectrum.basicOpen f) n
            (tildeLocalizedBasis R M b f)) =
          exteriorPower.ιMulti Γ(X,PrimeSpectrum.basicOpen g) n
            (tildeLocalizedBasis R M b g) := by
        calc
          _ = exteriorPower.ιMulti Γ(X,PrimeSpectrum.basicOpen g) n
              (fun i : Fin n => (Q).val.map (homOfLE h).op
                (tildeLocalizedBasis R M b f i)) :=
            presheafExteriorPower_map_wedge (X).presheaf (Q).val n
              (homOfLE h).op (tildeLocalizedBasis R M b f)
          _ = _ := congrArg
            (fun v : Fin n → Γ(Q,PrimeSpectrum.basicOpen g) =>
              exteriorPower.ιMulti Γ(X,PrimeSpectrum.basicOpen g) n v)
            (funext (fun i => tildeLocalizedBasis_restrict R M b f g h i))
      exact congrArg (fun z : (P).obj (op (PrimeSpectrum.basicOpen g)) =>
        basisTopExteriorEquiv (tildeLocalizedBasis R M b g)
          ((X).presheaf.map (homOfLE h).op c • z)) hw
    _ = (X).presheaf.map (homOfLE h).op c *
        basisTopExteriorEquiv (tildeLocalizedBasis R M b g)
          (exteriorPower.ιMulti Γ(X,PrimeSpectrum.basicOpen g) n
            (tildeLocalizedBasis R M b g)) :=
      (basisTopExteriorEquiv (tildeLocalizedBasis R M b g)).map_smul _ _
    _ = (X).presheaf.map (homOfLE h).op c * 1 :=
      congrArg (fun r : Γ(X,PrimeSpectrum.basicOpen g) =>
        (X).presheaf.map (homOfLE h).op c * r)
        (basisTopExteriorEquiv_basis (tildeLocalizedBasis R M b g))
    _ = (X).presheaf.map (homOfLE h).op c := mul_one _

theorem affineTopExteriorBasicEquiv_natural (f g : R)
    (h : PrimeSpectrum.basicOpen g≤PrimeSpectrum.basicOpen f)
    (ω : (P).obj (op (PrimeSpectrum.basicOpen f))) :
    affineTopExteriorBasicEquiv R M b g ((P).map (homOfLE h).op ω)=
      (tilde W).presheaf.map (homOfLE h).op (affineTopExteriorBasicEquiv R M b f ω) := by
  apply (tildeTopBasisCoordinates R M b (PrimeSpectrum.basicOpen g)).injective
  rw [tildeTopBasisCoordinates_restrict]
  simp only [affineTopExteriorBasicEquiv,LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  exact localizedTopCoefficient_restrict R M b f g h ω

theorem tildeLocalizedBasis_det (f : R) (v : Fin n→M) :
    (tildeLocalizedBasis R M b f).det
        (fun i=>tilde.toOpen M (PrimeSpectrum.basicOpen f) (v i))=
      algebraMap R Γ(X,PrimeSpectrum.basicOpen f) (b.det v) := by
  have hm : (tildeLocalizedBasis R M b f).toMatrix
      (fun i=>tilde.toOpen M (PrimeSpectrum.basicOpen f) (v i))=
        (algebraMap R Γ(X,PrimeSpectrum.basicOpen f)).mapMatrix (b.toMatrix v) := by
    funext i j
    exact b.ofIsLocalizedModule_repr_apply
      Γ(X,PrimeSpectrum.basicOpen f) (.powers f)
      (show M →ₗ[R] Γ(Q,PrimeSpectrum.basicOpen f) from
        (tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom) (v j) i
  rw [Module.Basis.det_apply,hm,← RingHom.map_det,← Module.Basis.det_apply]

/-- The comparison is the ordinary wedge map on actual restricted
sections; the coefficient construction has not changed the exterior map. -/
theorem affineTopExteriorBasicEquiv_wedge (f : R) (v : Fin n→M) :
    affineTopExteriorBasicEquiv R M b f
      (exteriorPower.ιMulti Γ(X,PrimeSpectrum.basicOpen f) n
        (fun i=>tilde.toOpen M (PrimeSpectrum.basicOpen f) (v i)))=
      tilde.toOpen W (PrimeSpectrum.basicOpen f) (exteriorPower.ιMulti R n v) := by
  apply (tildeTopBasisCoordinates R M b (PrimeSpectrum.basicOpen f)).injective
  rw [tildeTopBasisCoordinates_toOpen]
  simp only [affineTopExteriorBasicEquiv,LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  exact (basisTopExteriorEquiv_wedge (tildeLocalizedBasis R M b f)
    (fun i => tilde.toOpen M (PrimeSpectrum.basicOpen f) (v i))).trans
      ((tildeLocalizedBasis_det R M b f v).trans
        (congrArg (algebraMap R Γ(X,PrimeSpectrum.basicOpen f))
          (basisTopExteriorEquiv_wedge b v)).symm)

/-- Actual top exterior power commutes with the actual affine tilde
construction. The source is the sheafification definition of the
ordinary exterior module of the actual section modules. -/
def affineTopExteriorSheafIso :
    sheafExteriorPower X (tilde M) n≅tilde W :=
  basisModuleSheafificationIso (fun f : R=>PrimeSpectrum.basicOpen f)
    PrimeSpectrum.isBasis_basic_opens P (tilde W)
    (fun f=>(affineTopExteriorBasicEquiv R M b f).toLinearMap)
    (affineTopExteriorBasicEquiv_natural R M b)
    (fun f=>(affineTopExteriorBasicEquiv R M b f).bijective)

theorem affineTopExteriorSheafIso_basic (f : R)
    (ω : (P).obj (op (PrimeSpectrum.basicOpen f))) :
    (affineTopExteriorSheafIso R M b).hom.app (PrimeSpectrum.basicOpen f)
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 (X).ringCatSheaf.obj)).unit.app P).app (op (PrimeSpectrum.basicOpen f)) ω)=
        affineTopExteriorBasicEquiv R M b f ω := by
  have h := basisModuleSheafificationIso_unit
    (fun f : R=>PrimeSpectrum.basicOpen f) PrimeSpectrum.isBasis_basic_opens P (tilde W)
    (fun f=>(affineTopExteriorBasicEquiv R M b f).toLinearMap)
    (affineTopExteriorBasicEquiv_natural R M b)
    (fun f=>(affineTopExteriorBasicEquiv R M b f).bijective)
  exact (congrArg (fun φ=>φ.app (op (PrimeSpectrum.basicOpen f)) ω) h).trans
    (basisModuleComparison_app _ _ _ _ _ _ f ω)

theorem affineTopExteriorSheafIso_wedge (f : R) (v : Fin n→M) :
    (affineTopExteriorSheafIso R M b).hom.app (PrimeSpectrum.basicOpen f)
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 (X).ringCatSheaf.obj)).unit.app P).app (op (PrimeSpectrum.basicOpen f))
          (exteriorPower.ιMulti Γ(X,PrimeSpectrum.basicOpen f) n
            (fun i=>tilde.toOpen M (PrimeSpectrum.basicOpen f) (v i))))=
        tilde.toOpen W (PrimeSpectrum.basicOpen f) (exteriorPower.ιMulti R n v) := by
  rw [affineTopExteriorSheafIso_basic,affineTopExteriorBasicEquiv_wedge]

end PaperVerification.ToricSchemes

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory

variable (k R : Type u) [CommRing k] [CommRing R] [Algebra k R] {n : ℕ}
    (b : Module.Basis (Fin n) R (KaehlerDifferential k R))

/-- The ordinary intrinsic top differential sheaf on the affine chart
is the tilde of the ordinary top algebraic Kähler module. -/
def affineTopDifferentialSheafIso :
    topDifferentialSheaf k (Spec (CommRingCat.of R)) n≅
      tilde (R := CommRingCat.of R) (ModuleCat.of R (⋀[R]^n (KaehlerDifferential k R))) :=
  sheafExteriorPowerIso (Spec (CommRingCat.of R))
    (affineDifferentialSheafIso k R) n ≪≫
      affineTopExteriorSheafIso (CommRingCat.of R)
        (ModuleCat.of R (KaehlerDifferential k R)) b

end PaperVerification.ToricSchemes
end
end Source_ToricAffineExteriorSheaf
-- END ORIGINAL PaperVerification.ToricAffineExteriorSheaf


