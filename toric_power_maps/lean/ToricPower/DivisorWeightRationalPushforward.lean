module

public import ToricPower.FanRayPrimitive

public import ToricPower.DivisorWeightCartierAtlas
public import ToricPower.PowerSheafCore

/-!
# Rational-function construction of divisor pushforward maps

This source builds the actual morphism `s ↦ χᵘ Fℓ*(s)` between Cartier
sheaves. The map into rational functions is canonical; regularity of its
image is checked by local equations. Thus agreement on overlaps follows
from equality of rational functions.

The generic rational pullback and injective factorization proof bodies are
adapted from BondalThomsen at commit
9a2bdcdcf6b25710459f7f476c9c62de3039b7bb. The provenance manifest records
all source segments. This file is a development draft until its exact
source hash has a successful ordinary Lean compiler record.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open TauCeti.Toric

attribute [local instance] CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts

namespace ToricPower

universe schemeUniverse indexUniverse

variable {SchemeModel : Scheme.{schemeUniverse}} [IsIntegral SchemeModel]

noncomputable def rationalPullback (morphism : SchemeModel ⟶ SchemeModel)
    (generic : morphism (genericPoint SchemeModel) = genericPoint SchemeModel) :
    SchemeModel.functionField →+* SchemeModel.functionField :=
  (eqToHom (congrArg SchemeModel.presheaf.stalk generic.symm) ≫
    morphism.stalkMap (genericPoint SchemeModel)).hom

omit [IsIntegral SchemeModel] in
private theorem germ_transport (domain : SchemeModel.Opens) {first second : SchemeModel}
    (equal : first = second) (member : first ∈ domain) :
    SchemeModel.presheaf.germ domain first member ≫
        eqToHom (congrArg SchemeModel.presheaf.stalk equal) =
      SchemeModel.presheaf.germ domain second (equal ▸ member) := by
  subst second
  simp

theorem rationalPullback_germ (morphism : SchemeModel ⟶ SchemeModel)
    (generic : morphism (genericPoint SchemeModel) = genericPoint SchemeModel)
    (domain : SchemeModel.Opens) [Nonempty domain] [Nonempty (morphism ⁻¹ᵁ domain)]
    (regularSection : Γ(SchemeModel, domain)) :
    rationalPullback morphism generic (SchemeModel.germToFunctionField domain regularSection) =
      SchemeModel.germToFunctionField (morphism ⁻¹ᵁ domain)
        (morphism.app domain regularSection) := by
  have member := TauCeti.AlgebraicGeometry.Scheme.genericPoint_mem domain
  have pulled_member : morphism (genericPoint SchemeModel) ∈ domain := generic.symm ▸ member
  have equation := morphism.germ_stalkMap_apply domain (genericPoint SchemeModel)
    pulled_member regularSection
  have transported := germ_transport domain generic.symm member
  change (morphism.stalkMap (genericPoint SchemeModel)).hom
      ((eqToHom (congrArg SchemeModel.presheaf.stalk generic.symm)).hom
        (SchemeModel.germToFunctionField domain regularSection)) = _
  have applied := congrArg (fun map => map.hom regularSection) transported
  have applied' : (eqToHom (congrArg SchemeModel.presheaf.stalk generic.symm)).hom
      (SchemeModel.germToFunctionField domain regularSection) =
    SchemeModel.presheaf.germ domain (morphism (genericPoint SchemeModel)) pulled_member
      regularSection := applied
  rw [applied']
  exact equation

theorem genericPoint_fixed_of_surjective (morphism : SchemeModel ⟶ SchemeModel)
    (surjective : Function.Surjective morphism) :
    morphism (genericPoint SchemeModel) = genericPoint SchemeModel := by
  apply IsGenericPoint.eq _ (genericPoint_spec SchemeModel)
  convert (genericPoint_spec SchemeModel).image morphism.continuous using 1
  rw [Set.image_univ, surjective.range_eq, closure_univ]

theorem rationalPullback_germLE (morphism : SchemeModel ⟶ SchemeModel)
    (generic : morphism (genericPoint SchemeModel) = genericPoint SchemeModel)
    (domain source : SchemeModel.Opens) [Nonempty domain] [Nonempty source]
    (contained : source ≤ morphism ⁻¹ᵁ domain) (regularSection : Γ(SchemeModel, domain)) :
    rationalPullback morphism generic (SchemeModel.germToFunctionField domain regularSection) =
      SchemeModel.germToFunctionField source
        (morphism.appLE domain source contained regularSection) := by
  let : Nonempty (morphism ⁻¹ᵁ domain) := by
    obtain ⟨point⟩ := (inferInstance : Nonempty source)
    exact ⟨⟨point.val, contained point.property⟩⟩
  rw [rationalPullback_germ morphism generic]
  exact (SchemeModel.presheaf.germ_res_apply (homOfLE contained)
    (genericPoint SchemeModel) (TauCeti.AlgebraicGeometry.Scheme.genericPoint_mem source)
      (morphism.app domain regularSection)).symm

theorem rationalPullback_openImmersionGerm {Chart : Scheme.{schemeUniverse}}
    [Nonempty Chart] (inclusion : Chart ⟶ SchemeModel) [IsOpenImmersion inclusion]
    (morphism : SchemeModel ⟶ SchemeModel)
    (generic : morphism (genericPoint SchemeModel) = genericPoint SchemeModel)
    (chartMap : Chart ⟶ Chart) (square : inclusion ≫ morphism = chartMap ≫ inclusion)
    (preserved : morphism ⁻¹ᵁ inclusion.opensRange = inclusion.opensRange)
    (regularSection : Γ(Chart, ⊤)) :
    rationalPullback morphism generic (openImmersionGerm inclusion regularSection) =
      openImmersionGerm inclusion (chartMap.appTop regularSection) := by
  let : Nonempty inclusion.opensRange := by
    obtain ⟨point⟩ := (inferInstance : Nonempty Chart)
    exact ⟨⟨inclusion point, point, rfl⟩⟩
  have inclusion_contains : ⊤ ≤ inclusion ⁻¹ᵁ inclusion.opensRange := by
    rintro point _
    exact ⟨point, rfl⟩
  have preserved_contains : inclusion.opensRange ≤ morphism ⁻¹ᵁ inclusion.opensRange :=
    preserved.symm.le
  have first := Scheme.Hom.appLE_comp_appLE inclusion morphism
    inclusion.opensRange inclusion.opensRange ⊤ preserved_contains inclusion_contains
  have second := Scheme.Hom.appLE_comp_appLE chartMap inclusion
    inclusion.opensRange ⊤ ⊤ inclusion_contains le_top
  simp only [square] at first
  have composite : morphism.appLE inclusion.opensRange inclusion.opensRange preserved_contains ≫
      (IsOpenImmersion.ΓIsoTop inclusion).inv =
    (IsOpenImmersion.ΓIsoTop inclusion).inv ≫ chartMap.appTop := by
    rw [openImmersion_sectionsIso_inv]
    have top_map : chartMap.appLE ⊤ ⊤ le_top = chartMap.appTop := by
      exact chartMap.appLE_eq_app
    rw [top_map] at second
    exact first.trans second.symm
  have identified : (IsOpenImmersion.ΓIsoTop inclusion).hom ≫
      morphism.appLE inclusion.opensRange inclusion.opensRange preserved_contains =
    chartMap.appTop ≫ (IsOpenImmersion.ΓIsoTop inclusion).hom := by
    rw [← Iso.comp_inv_eq, Category.assoc, composite]
    simp
  unfold openImmersionGerm
  dsimp only [RingHom.comp_apply]
  rw [rationalPullback_germLE morphism generic inclusion.opensRange inclusion.opensRange
    preserved_contains]
  exact congrArg (fun map => SchemeModel.germToFunctionField inclusion.opensRange
    (map.hom regularSection)) identified

theorem rationalPullback_nonempty_preimage (morphism : SchemeModel ⟶ SchemeModel)
    (generic : morphism (genericPoint SchemeModel) = genericPoint SchemeModel)
    (domain : SchemeModel.Opens) [Nonempty domain] : Nonempty (morphism ⁻¹ᵁ domain) := by
  refine ⟨⟨genericPoint SchemeModel, ?_⟩⟩
  change morphism (genericPoint SchemeModel) ∈ domain
  rw [generic]
  exact TauCeti.AlgebraicGeometry.Scheme.genericPoint_mem domain

theorem rationalPullback_stalk (morphism : SchemeModel ⟶ SchemeModel)
    (generic : morphism (genericPoint SchemeModel) = genericPoint SchemeModel)
    (point : SchemeModel) (localSection : SchemeModel.presheaf.stalk (morphism point)) :
    rationalPullback morphism generic
        (algebraMap (SchemeModel.presheaf.stalk (morphism point)) SchemeModel.functionField
          localSection) =
      algebraMap (SchemeModel.presheaf.stalk point) SchemeModel.functionField
        (morphism.stalkMap point localSection) := by
  obtain ⟨domain, member, regularSection, represent⟩ :=
    SchemeModel.presheaf.exists_germ_eq localSection
  let : Nonempty domain := ⟨⟨morphism point, member⟩⟩
  let : Nonempty (morphism ⁻¹ᵁ domain) := ⟨⟨point, member⟩⟩
  rw [← represent, Scheme.algebraMap_germ_eq_germToFunctionField,
    morphism.germ_stalkMap_apply,
    Scheme.algebraMap_germ_eq_germToFunctionField]
  exact rationalPullback_germ morphism generic domain regularSection

theorem rationalPullback_mem_stalkRange (morphism : SchemeModel ⟶ SchemeModel)
    (generic : morphism (genericPoint SchemeModel) = genericPoint SchemeModel)
    (point : SchemeModel) {rational : SchemeModel.functionField}
    (regular : rational ∈
      (algebraMap (SchemeModel.presheaf.stalk (morphism point)) SchemeModel.functionField).range) :
    rationalPullback morphism generic rational ∈
      (algebraMap (SchemeModel.presheaf.stalk point) SchemeModel.functionField).range := by
  obtain ⟨localSection, rfl⟩ := regular
  exact ⟨morphism.stalkMap point localSection,
    (rationalPullback_stalk morphism generic point localSection).symm⟩

noncomputable def rationalSectionsPullback (morphism : SchemeModel ⟶ SchemeModel)
    (generic : morphism (genericPoint SchemeModel) = genericPoint SchemeModel)
    (domain : SchemeModel.Opens) :
    Γ(TauCeti.AlgebraicGeometry.Scheme.rationalFunctions SchemeModel, domain) →+
      Γ(TauCeti.AlgebraicGeometry.Scheme.rationalFunctions SchemeModel,
        morphism ⁻¹ᵁ domain) := by
  classical
  exact if nonempty : Nonempty domain then
    letI := nonempty
    letI := rationalPullback_nonempty_preimage morphism generic domain
    (TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv
      (morphism ⁻¹ᵁ domain)).symm.toAddMonoidHom.comp
        ((rationalPullback morphism generic).toAddMonoidHom.comp
          (TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv domain).toAddMonoidHom)
  else 0

theorem rationalSectionsPullback_equiv (morphism : SchemeModel ⟶ SchemeModel)
    (generic : morphism (genericPoint SchemeModel) = genericPoint SchemeModel)
    (domain : SchemeModel.Opens) [Nonempty domain] [Nonempty (morphism ⁻¹ᵁ domain)]
    (rationalSection :
      Γ(TauCeti.AlgebraicGeometry.Scheme.rationalFunctions SchemeModel, domain)) :
    TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv (morphism ⁻¹ᵁ domain)
        (rationalSectionsPullback morphism generic domain rationalSection) =
      rationalPullback morphism generic
        (TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv domain rationalSection) := by
  classical
  rw [rationalSectionsPullback, dite_eq_left (inferInstance : Nonempty domain)]
  exact LinearEquiv.apply_symm_apply _ _

theorem rationalSectionsPullback_smul (morphism : SchemeModel ⟶ SchemeModel)
    (generic : morphism (genericPoint SchemeModel) = genericPoint SchemeModel)
    (domain : SchemeModel.Opens) (coefficient : Γ(SchemeModel, domain))
    (rationalSection :
      Γ(TauCeti.AlgebraicGeometry.Scheme.rationalFunctions SchemeModel, domain)) :
    rationalSectionsPullback morphism generic domain (coefficient • rationalSection) =
      morphism.app domain coefficient •
        rationalSectionsPullback morphism generic domain rationalSection := by
  classical
  by_cases nonempty : Nonempty domain
  · let := nonempty
    let := rationalPullback_nonempty_preimage morphism generic domain
    apply (TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv _).injective
    simp only [rationalSectionsPullback_equiv, map_smul, Algebra.smul_def,
      RingHom.algebraMap_toAlgebra, map_mul, rationalPullback_germ]
  · simp [rationalSectionsPullback, nonempty]

theorem rationalSectionsPullback_restrict (morphism : SchemeModel ⟶ SchemeModel)
    (generic : morphism (genericPoint SchemeModel) = genericPoint SchemeModel)
    {domain smaller : SchemeModel.Opens} (inclusion : smaller ⟶ domain)
    (rationalSection :
      Γ(TauCeti.AlgebraicGeometry.Scheme.rationalFunctions SchemeModel, domain)) :
    rationalSectionsPullback morphism generic smaller
        ((TauCeti.AlgebraicGeometry.Scheme.rationalFunctions SchemeModel).presheaf.map
          inclusion.op rationalSection) =
      (TauCeti.AlgebraicGeometry.Scheme.rationalFunctions SchemeModel).presheaf.map
        ((Opens.map morphism.base).map inclusion).op
        (rationalSectionsPullback morphism generic domain rationalSection) := by
  classical
  by_cases nonempty : Nonempty smaller
  · let := nonempty
    let : Nonempty domain := by
      obtain ⟨point, member⟩ := nonempty
      exact ⟨⟨point, inclusion.le member⟩⟩
    let := rationalPullback_nonempty_preimage morphism generic smaller
    let := rationalPullback_nonempty_preimage morphism generic domain
    apply (TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv _).injective
    simp only [rationalSectionsPullback_equiv,
      TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv_map]
  · have empty : smaller = ⊥ := by
      apply bot_unique
      intro point member
      exact False.elim (nonempty ⟨⟨point, member⟩⟩)
    have pulled_empty : morphism ⁻¹ᵁ smaller = ⊥ := by simp [empty]
    let := TauCeti.AlgebraicGeometry.Scheme.subsingleton_rationalFunctions
      (morphism ⁻¹ᵁ smaller) pulled_empty
    exact Subsingleton.elim _ _

noncomputable def rationalSheafToPushforward (morphism : SchemeModel ⟶ SchemeModel)
    (generic : morphism (genericPoint SchemeModel) = genericPoint SchemeModel) :
    TauCeti.AlgebraicGeometry.Scheme.rationalFunctions SchemeModel ⟶
      (Scheme.Modules.pushforward morphism).obj
        (TauCeti.AlgebraicGeometry.Scheme.rationalFunctions SchemeModel) where
  val :=
    { app := fun domain => { hom' :=
        { toFun := rationalSectionsPullback morphism generic domain.unop
          map_add' := (rationalSectionsPullback morphism generic domain.unop).map_add
          map_smul' := fun coefficient rationalSection =>
            rationalSectionsPullback_smul morphism generic domain.unop coefficient rationalSection } }
      naturality := by
        intro domain smaller inclusion
        ext rationalSection
        exact rationalSectionsPullback_restrict morphism generic inclusion.unop rationalSection }

noncomputable def residueFactorLinearMap {Scalars Source Middle Target : Type*}
    [Semiring Scalars] [AddCommMonoid Source] [AddCommMonoid Middle]
    [AddCommMonoid Target] [Module Scalars Source] [Module Scalars Middle]
    [Module Scalars Target] (morphism : Source →ₗ[Scalars] Target)
    (inclusion : Middle →ₗ[Scalars] Target) (injective : Function.Injective inclusion)
    (in_range : ∀ element, morphism element ∈ inclusion.range) :
    Source →ₗ[Scalars] Middle :=
  (LinearEquiv.ofInjective inclusion injective).symm.toLinearMap.comp
    (morphism.codRestrict inclusion.range in_range)

theorem residueFactorLinearMap_inclusion {Scalars Source Middle Target : Type*}
    [Semiring Scalars] [AddCommMonoid Source] [AddCommMonoid Middle]
    [AddCommMonoid Target] [Module Scalars Source] [Module Scalars Middle]
    [Module Scalars Target] (morphism : Source →ₗ[Scalars] Target)
    (inclusion : Middle →ₗ[Scalars] Target) (injective : Function.Injective inclusion)
    (in_range : ∀ element, morphism element ∈ inclusion.range) (element : Source) :
    inclusion (residueFactorLinearMap morphism inclusion injective in_range element) =
      morphism element :=
  LinearEquiv.ofInjective_symm_apply inclusion (h := injective) _

noncomputable def residueFactorSheafHom {SchemeModel : Scheme.{schemeUniverse}}
    {Source Middle Target : SchemeModel.Modules} (morphism : Source ⟶ Target)
    (inclusion : Middle ⟶ Target)
    (injective : ∀ domain, Function.Injective (Scheme.Modules.Hom.app inclusion domain))
    (in_range : ∀ domain element,
      morphism.val.app (op domain) element ∈
        (inclusion.val.app (op domain)).hom.range) : Source ⟶ Middle where
  val :=
    { app := fun domain => ModuleCat.ofHom
        (residueFactorLinearMap (morphism.val.app domain).hom
          (inclusion.val.app domain).hom
          (injective domain.unop) (in_range domain.unop))
      naturality := by
        intro domain smaller restriction
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro element
        apply injective smaller.unop
        have inclusion_naturality := ConcreteCategory.congr_hom
          (inclusion.mapPresheaf.naturality restriction)
          (residueFactorLinearMap (morphism.val.app domain).hom
            (inclusion.val.app domain).hom
            (injective domain.unop) (in_range domain.unop) element)
        have morphism_naturality := ConcreteCategory.congr_hom
          (morphism.mapPresheaf.naturality restriction) element
        simp only [ConcreteCategory.comp_apply, Scheme.Modules.mapPresheaf_app]
          at inclusion_naturality morphism_naturality
        change Scheme.Modules.Hom.app inclusion smaller.unop
            (residueFactorLinearMap (morphism.val.app smaller).hom
              (inclusion.val.app smaller).hom
              (injective smaller.unop) (in_range smaller.unop)
              (Source.presheaf.map restriction element)) =
          Scheme.Modules.Hom.app inclusion smaller.unop
            (Middle.presheaf.map restriction
              ((residueFactorLinearMap (morphism.val.app domain).hom
                (inclusion.val.app domain).hom
                (injective domain.unop) (in_range domain.unop)) element))
        have smaller_factor := residueFactorLinearMap_inclusion
          (morphism.val.app smaller).hom (inclusion.val.app smaller).hom
          (injective smaller.unop) (in_range smaller.unop)
          (Source.presheaf.map restriction element)
        have domain_factor := residueFactorLinearMap_inclusion
          (morphism.val.app domain).hom (inclusion.val.app domain).hom
          (injective domain.unop) (in_range domain.unop) element
        exact smaller_factor.trans (morphism_naturality.trans
          ((congrArg (Target.presheaf.map restriction) domain_factor).symm.trans
            inclusion_naturality.symm)) }

theorem residueFactorSheafHom_inclusion {SchemeModel : Scheme.{schemeUniverse}}
    {Source Middle Target : SchemeModel.Modules} (morphism : Source ⟶ Target)
    (inclusion : Middle ⟶ Target)
    (injective : ∀ domain, Function.Injective (Scheme.Modules.Hom.app inclusion domain))
    (in_range : ∀ domain element,
      morphism.val.app (op domain) element ∈
        (inclusion.val.app (op domain)).hom.range) :
    residueFactorSheafHom morphism inclusion injective in_range ≫ inclusion = morphism := by
  apply Scheme.Modules.hom_ext
  intro domain
  ext element
  exact residueFactorLinearMap_inclusion (morphism.val.app (op domain)).hom
    (inclusion.val.app (op domain)).hom (injective domain) (in_range domain) element

/-- Pull back a rational section and multiply by a fixed rational function.
The codomain uses the actual scheme-module direct image. -/
def cartierRationalMap (morphism : SchemeModel ⟶ SchemeModel)
    (generic : morphism (genericPoint SchemeModel) = genericPoint SchemeModel)
    (source : TauCeti.AlgebraicGeometry.Scheme.CartierDivisor SchemeModel)
    (coefficient : SchemeModel.functionField) :
    source.sheaf ⟶ (Scheme.Modules.pushforward morphism).obj
      (TauCeti.AlgebraicGeometry.Scheme.rationalFunctions SchemeModel) :=
  source.sheafι ≫ rationalSheafToPushforward morphism generic ≫
    (Scheme.Modules.pushforward morphism).map
      (TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsMul SchemeModel coefficient)

theorem cartierRationalMap_value (morphism : SchemeModel ⟶ SchemeModel)
    (generic : morphism (genericPoint SchemeModel) = genericPoint SchemeModel)
    (source : TauCeti.AlgebraicGeometry.Scheme.CartierDivisor SchemeModel)
    (coefficient : SchemeModel.functionField) (domain : SchemeModel.Opens)
    [Nonempty domain] [Nonempty (morphism ⁻¹ᵁ domain)] (s : Γ(source.sheaf, domain)) :
    TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv (morphism ⁻¹ᵁ domain)
        (Scheme.Modules.Hom.app (cartierRationalMap morphism generic source coefficient)
          domain s) =
      coefficient * rationalPullback morphism generic
        (TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv domain
          (Scheme.Modules.Hom.app source.sheafι domain s)) := by
  change TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv _
    (Scheme.Modules.Hom.app
      (TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsMul SchemeModel coefficient) _
      (rationalSectionsPullback morphism generic domain
        (Scheme.Modules.Hom.app source.sheafι domain s))) = _
  rw [TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv_rationalFunctionsMul_app,
    rationalSectionsPullback_equiv]

/-- Local regularity data for a morphism between Cartier sheaves. The last
field is precisely the regularity of the image of a local generator, after
multiplication by the target's local equation. -/
structure CartierResidueCompatibility (morphism : SchemeModel ⟶ SchemeModel)
    (generic : morphism (genericPoint SchemeModel) = genericPoint SchemeModel)
    (source target : TauCeti.AlgebraicGeometry.Scheme.CartierDivisor SchemeModel)
    (coefficient : SchemeModel.functionField) where
  Index : Type indexUniverse
  chart : Index → SchemeModel.Opens
  covers : IsOpenCover chart
  sourceEquation : Index → SchemeModel.functionFieldˣ
  targetEquation : Index → SchemeModel.functionFieldˣ
  source_local : ∀ index point, point ∈ chart index →
    source.IsLocalEquationAt point (sourceEquation index)
  target_local : ∀ index point, point ∈ chart index →
    target.IsLocalEquationAt point (targetEquation index)
  preserved : ∀ index, morphism ⁻¹ᵁ chart index = chart index
  regular_ratio : ∀ index point, point ∈ chart index →
    (targetEquation index : SchemeModel.functionField) * coefficient *
      rationalPullback morphism generic
        (((sourceEquation index)⁻¹ : SchemeModel.functionFieldˣ) : SchemeModel.functionField) ∈
      (algebraMap (SchemeModel.presheaf.stalk point) SchemeModel.functionField).range

namespace CartierResidueCompatibility

variable {morphism : SchemeModel ⟶ SchemeModel}
  {generic : morphism (genericPoint SchemeModel) = genericPoint SchemeModel}
  {source target : TauCeti.AlgebraicGeometry.Scheme.CartierDivisor SchemeModel}
  {coefficient : SchemeModel.functionField}
  (compatibility : CartierResidueCompatibility morphism generic source target coefficient)

include compatibility

theorem rationalMap_mem (domain : SchemeModel.Opens) (s : Γ(source.sheaf, domain)) :
    Scheme.Modules.Hom.app (cartierRationalMap morphism generic source coefficient) domain s ∈
      target.sections (morphism ⁻¹ᵁ domain) := by
  apply TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.mem_sections_iff_exists.mpr
  intro point point_member
  letI : Nonempty domain := ⟨⟨morphism point, point_member⟩⟩
  letI : Nonempty (morphism ⁻¹ᵁ domain) := ⟨⟨point, point_member⟩⟩
  obtain ⟨index, chart_member⟩ := compatibility.covers.exists_mem point
  have image_member : morphism point ∈ compatibility.chart index := by
    change point ∈ morphism ⁻¹ᵁ compatibility.chart index
    rw [compatibility.preserved index]
    exact chart_member
  refine ⟨compatibility.targetEquation index,
    compatibility.target_local index point chart_member, ?_⟩
  rw [cartierRationalMap_value]
  have local_regular :=
    (TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.mem_sections.mp
      (source.sheafι_app_mem domain s)) (morphism point) point_member
      (compatibility.sourceEquation index)
      (compatibility.source_local index (morphism point) image_member)
  have pulled_regular := rationalPullback_mem_stalkRange morphism generic point local_regular
  have product := (algebraMap (SchemeModel.presheaf.stalk point)
    SchemeModel.functionField).range.mul_mem
      (compatibility.regular_ratio index point chart_member) pulled_regular
  have unit_cancel :
      rationalPullback morphism generic
          (((compatibility.sourceEquation index)⁻¹ : SchemeModel.functionFieldˣ) :
            SchemeModel.functionField) *
        rationalPullback morphism generic
          (compatibility.sourceEquation index : SchemeModel.functionField) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have normalized :
      ((compatibility.targetEquation index : SchemeModel.functionField) * coefficient *
        rationalPullback morphism generic
          (((compatibility.sourceEquation index)⁻¹ : SchemeModel.functionFieldˣ) :
            SchemeModel.functionField)) *
        rationalPullback morphism generic
          ((compatibility.sourceEquation index : SchemeModel.functionField) *
            TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv domain
              (Scheme.Modules.Hom.app source.sheafι domain s)) =
      (compatibility.targetEquation index : SchemeModel.functionField) *
        (coefficient * rationalPullback morphism generic
          (TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv domain
            (Scheme.Modules.Hom.app source.sheafι domain s))) := by
    rw [map_mul]
    simp only [mul_assoc]
    rw [← mul_assoc (rationalPullback morphism generic
      (((compatibility.sourceEquation index)⁻¹ : SchemeModel.functionFieldˣ) :
        SchemeModel.functionField)), unit_cancel, one_mul]
  exact normalized ▸ product

/-- The global sheaf map is obtained by factoring through the actual
pointwise injective inclusion into rational functions. Naturalness is proved,
so no separate gluing or compatibility axiom is supplied. -/
def sheafMap : source.sheaf ⟶ (Scheme.Modules.pushforward morphism).obj target.sheaf :=
  residueFactorSheafHom (cartierRationalMap morphism generic source coefficient)
    ((Scheme.Modules.pushforward morphism).map target.sheafι)
    (fun domain => target.sheafι_app_injective (morphism ⁻¹ᵁ domain))
    (fun domain s => by
      change Scheme.Modules.Hom.app (cartierRationalMap morphism generic source coefficient)
        domain s ∈ Set.range (Scheme.Modules.Hom.app target.sheafι (morphism ⁻¹ᵁ domain))
      rw [target.range_sheafι_app]
      exact compatibility.rationalMap_mem domain s)

theorem sheafMap_ι :
    compatibility.sheafMap ≫ (Scheme.Modules.pushforward morphism).map target.sheafι =
      cartierRationalMap morphism generic source coefficient :=
  residueFactorSheafHom_inclusion _ _ _ _

end CartierResidueCompatibility

section ToricResidues

universe u v

variable {N : Type u} {V : Type v} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

/-- The literal floor coefficients of the paper's residue summand, defined
on every intrinsic fan ray. -/
def toricResidueCoefficients (fan : Fan i) (b : fan.Ray → ℤ) (ell : ℕ)
    (character : N →+ ℤ) : fan.Ray → ℤ :=
  fun ρ => (b ρ + character (fanRayPrimitiveGenerator fan ρ)) / (ell : ℤ)

theorem toricResidueCoefficients_chart {κ : Type*} [Fintype κ]
    (fan : Fan i) (basis : Module.Basis κ ℤ (N →+ ℤ)) (b : fan.Ray → ℤ)
    (ell : ℕ) (character : N →+ ℤ) (cone : fan.cones) :
    coneDivisorCoefficients fan (toricResidueCoefficients fan b ell character) cone =
      powerCoefficient (characterRayMatrix fan.lattice (fan.isToricCone cone.property) basis)
        (coneDivisorCoefficients fan b cone) (ell : ℤ) (basis.equivFun character) := by
  funext ρ
  simp only [coneDivisorCoefficients, toricResidueCoefficients, powerCoefficient,
    fanRayPrimitiveGenerator_ofToricRay, characterRayMatrix_apply]

def normalizedToricResidueCharacter (fan : Fan i) (regular : fan.IsRegular)
    (b : fan.Ray → ℤ) (ell : ℕ) (character : N →+ ℤ) (cone : fan.cones) : N →+ ℤ :=
  coneDivisorCharacter fan regular b cone + character -
    ell • coneDivisorCharacter fan regular (toricResidueCoefficients fan b ell character) cone

theorem normalizedToricResidueCharacter_ray (fan : Fan i) (regular : fan.IsRegular)
    (b : fan.Ray → ℤ) (ell : ℕ) (character : N →+ ℤ) (cone : fan.cones)
    (ρ : ToricRay cone.val) :
    normalizedToricResidueCharacter fan regular b ell character cone
        (primitiveGenerator fan.lattice (fan.isToricCone cone.property) ρ) =
      (coneDivisorCoefficients fan b cone ρ +
        character (primitiveGenerator fan.lattice (fan.isToricCone cone.property) ρ)) %
          (ell : ℤ) := by
  simp only [normalizedToricResidueCharacter, AddMonoidHom.sub_apply,
    AddMonoidHom.add_apply, AddMonoidHom.smul_apply, coneDivisorCharacter_ray,
    coneDivisorCoefficients, toricResidueCoefficients,
    fanRayPrimitiveGenerator_ofToricRay, nsmul_eq_mul]
  have h := Int.emod_add_mul_ediv
    (b (Fan.Ray.ofToricRay fan cone ρ) +
      character (primitiveGenerator fan.lattice (fan.isToricCone cone.property) ρ)) (ell : ℤ)
  omega

theorem normalizedToricResidueCharacter_mem (fan : Fan i) (regular : fan.IsRegular)
    (b : fan.Ray → ℤ) (ell : ℕ) (hell : 0 < ell) (character : N →+ ℤ)
    (cone : fan.cones) :
    normalizedToricResidueCharacter fan regular b ell character cone ∈
      dualSemigroup fan.lattice cone.val := by
  rw [mem_dualSemigroup_iff_primitiveGenerator fan.lattice (fan.isToricCone cone.property)]
  intro ρ
  rw [normalizedToricResidueCharacter_ray]
  exact Int.emod_nonneg _ (by exact_mod_cast hell.ne')

def normalizedToricResidueMonomial (fan : Fan i) (regular : fan.IsRegular)
    (b : fan.Ray → ℤ) (ell : ℕ) (hell : 0 < ell) (character : N →+ ℤ)
    (cone : fan.cones) : affineCoordinateRing fan.lattice cone.val :=
  MonoidAlgebra.single (Multiplicative.ofAdd
    (⟨normalizedToricResidueCharacter fan regular b ell character cone,
      normalizedToricResidueCharacter_mem fan regular b ell hell character cone⟩ :
        dualSemigroup fan.lattice cone.val)) 1

theorem chartCoordinateGerm_monomial (fan : Fan i) (nonempty : Nonempty fan.cones)
    (cone : fan.cones) (character : N →+ ℤ)
    (member : character ∈ dualSemigroup fan.lattice cone.val) :
    chartCoordinateGerm fan nonempty cone
      (MonoidAlgebra.single (Multiplicative.ofAdd
        (⟨character, member⟩ : dualSemigroup fan.lattice cone.val)) 1) =
      (rationalCharacterUnit fan nonempty character :
        (letI := toricSchemeIntegral fan nonempty; fan.algebraicRealization.functionField)) := by
  rw [chartCoordinateGerm_torus, faceAffineCoordinateRingMap_single]
  rfl

theorem chartCoordinateGerm_mem_stalkRange (fan : Fan i) (nonempty : Nonempty fan.cones)
    (cone : fan.cones) (coordinate : affineCoordinateRing fan.lattice cone.val)
    (point : fan.algebraicRealization)
    (contains : point ∈ (fan.affineToricChartι cone).opensRange) :
    letI := toricSchemeIntegral fan nonempty
    chartCoordinateGerm fan nonempty cone coordinate ∈
      (algebraMap (fan.algebraicRealization.presheaf.stalk point)
        fan.algebraicRealization.functionField).range := by
  letI := toricSchemeIntegral fan nonempty
  letI : Nonempty (fan.affineToricChartι cone).opensRange := ⟨⟨point, contains⟩⟩
  refine ⟨fan.algebraicRealization.presheaf.germ _ point contains
    (chartCoordinateSectionsEquiv fan cone coordinate), ?_⟩
  rw [Scheme.algebraMap_germ_eq_germToFunctionField]
  rfl

def toricZeroCone (fan : Fan i) (nonempty : Nonempty fan.cones) : fan.cones :=
  ⟨⊥, fan.bot_mem nonempty.some.property⟩

theorem denseTorusι_eq_zeroChart (fan : Fan i) (nonempty : Nonempty fan.cones) :
    fan.denseTorusι nonempty = fan.affineToricChartι (toricZeroCone fan nonempty) := by
  have h := fan.denseTorusι_face (toricZeroCone fan nonempty)
  simpa only [toricZeroCone, faceAffineToricSchemeMap_id, Category.id_comp] using h

theorem chartCoordinateGerm_zero (fan : Fan i) (nonempty : Nonempty fan.cones) :
    chartCoordinateGerm fan nonempty (toricZeroCone fan nonempty) =
      toricLaurentGerm fan nonempty := by
  unfold chartCoordinateGerm toricLaurentGerm
  dsimp only [toricZeroCone]
  congr 2
  exact (denseTorusι_eq_zeroChart fan nonempty).symm

theorem toricPower_genericPoint (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (ell : ℕ) (hell : 0 < ell) :
    letI := toricSchemeIntegral fan nonempty
    toricPowerMap fan ell (genericPoint fan.algebraicRealization) =
      genericPoint fan.algebraicRealization := by
  letI := toricSchemeIntegral fan nonempty
  letI := toricPowerMap_surjective fan regular ell hell
  exact genericPoint_fixed_of_surjective _ (toricPowerMap fan ell).surjective

def toricPowerFunctionField (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (ell : ℕ) (hell : 0 < ell) :
    letI := toricSchemeIntegral fan nonempty
    fan.algebraicRealization.functionField →+* fan.algebraicRealization.functionField := by
  letI := toricSchemeIntegral fan nonempty
  exact rationalPullback (toricPowerMap fan ell)
    (toricPower_genericPoint fan nonempty regular ell hell)

theorem toricPower_preimage_chartOpen (fan : Fan i) (ell : ℕ) (hell : 0 < ell)
    (cone : fan.cones) :
    (toricPowerMap fan ell) ⁻¹ᵁ (fan.affineToricChartι cone).opensRange =
      (fan.affineToricChartι cone).opensRange := by
  apply TopologicalSpace.Opens.ext
  exact toricPowerMap_preimage_chart fan ell hell cone

theorem toricPowerFunctionField_chartCoordinate (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular) (ell : ℕ) (hell : 0 < ell)
    (cone : fan.cones) (coordinate : affineCoordinateRing fan.lattice cone.val) :
    toricPowerFunctionField fan nonempty regular ell hell
        (chartCoordinateGerm fan nonempty cone coordinate) =
      chartCoordinateGerm fan nonempty cone (chartPowerRingHom fan cone ell coordinate) := by
  letI := toricSchemeIntegral fan nonempty
  have germ := rationalPullback_openImmersionGerm (fan.affineToricChartι cone)
    (toricPowerMap fan ell) (toricPower_genericPoint fan nonempty regular ell hell)
    (affinePowerMap fan ell cone) (toricPowerMap_affine_chart fan ell hell cone)
    (toricPower_preimage_chartOpen fan ell hell cone)
    (affineGlobalSectionsEquiv (affineCoordinateRing fan.lattice cone.val) coordinate)
  have affine := Scheme.ΓSpecIso_inv_naturality (chartPowerRingHom fan cone ell)
  have affine_apply := (ConcreteCategory.congr_hom affine coordinate).symm
  simp only [ConcreteCategory.comp_apply] at affine_apply
  have affine_apply' : (affinePowerMap fan ell cone).appTop
      (affineGlobalSectionsEquiv (affineCoordinateRing fan.lattice cone.val) coordinate) =
    affineGlobalSectionsEquiv (affineCoordinateRing fan.lattice cone.val)
      (chartPowerRingHom fan cone ell coordinate) := by
    change (affinePowerMap fan ell cone).appTop
        ((Scheme.ΓSpecIso _).inv coordinate) =
      (Scheme.ΓSpecIso _).inv (chartPowerRingHom fan cone ell coordinate)
    rw [affinePowerMap, affineToricSchemeMap_def]
    exact affine_apply
  exact germ.trans (congrArg (openImmersionGerm (fan.affineToricChartι cone)) affine_apply')

theorem toricPowerFunctionField_character (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (ell : ℕ) (hell : 0 < ell) (character : N →+ ℤ) :
    Units.map (toricPowerFunctionField fan nonempty regular ell hell).toMonoidHom
        (rationalCharacterUnit fan nonempty character) =
      rationalCharacterUnit fan nonempty (ell • character) := by
  letI := toricSchemeIntegral fan nonempty
  apply Units.ext
  change toricPowerFunctionField fan nonempty regular ell hell
      (toricLaurentGerm fan nonempty
        (MonoidAlgebra.single (Multiplicative.ofAdd
          (⟨character, by rw [dualSemigroup_bot]; trivial⟩ : dualSemigroup fan.lattice ⊥)) 1)) =
    toricLaurentGerm fan nonempty
      (MonoidAlgebra.single (Multiplicative.ofAdd
        (⟨ell • character, by rw [dualSemigroup_bot]; trivial⟩ : dualSemigroup fan.lattice ⊥)) 1)
  rw [← chartCoordinateGerm_zero]
  let monomial : affineCoordinateRing fan.lattice (toricZeroCone fan nonempty).val :=
    MonoidAlgebra.single (Multiplicative.ofAdd
      (⟨character, by
        change character ∈ dualSemigroup fan.lattice ⊥
        rw [dualSemigroup_bot]
        trivial⟩ : dualSemigroup fan.lattice (toricZeroCone fan nonempty).val)) 1
  have h := toricPowerFunctionField_chartCoordinate fan nonempty regular ell hell
    (toricZeroCone fan nonempty) monomial
  refine h.trans ?_
  dsimp only [monomial]
  rw [chartPowerRingHom_apply, MonoidAlgebra.mapDomain_single]
  rfl

theorem normalizedToricResidueMonomial_germ (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular) (b : fan.Ray → ℤ)
    (ell : ℕ) (hell : 0 < ell) (character : N →+ ℤ) (cone : fan.cones) :
    chartCoordinateGerm fan nonempty cone
        (normalizedToricResidueMonomial fan regular b ell hell character cone) =
      (rationalCharacterUnit fan nonempty
        (normalizedToricResidueCharacter fan regular b ell character cone) :
          (letI := toricSchemeIntegral fan nonempty; fan.algebraicRealization.functionField)) :=
  chartCoordinateGerm_monomial fan nonempty cone _ _

theorem toricResidue_ratio_eq_character (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b : fan.Ray → ℤ) (ell : ℕ) (hell : 0 < ell)
    (character : N →+ ℤ) (cone : fan.cones) :
    letI := toricSchemeIntegral fan nonempty
    (rationalCharacterUnit fan nonempty (coneDivisorCharacter fan regular b cone) :
        fan.algebraicRealization.functionField) *
      (rationalCharacterUnit fan nonempty character : fan.algebraicRealization.functionField) *
      toricPowerFunctionField fan nonempty regular ell hell
        (((rationalCharacterUnit fan nonempty
          (coneDivisorCharacter fan regular (toricResidueCoefficients fan b ell character) cone))⁻¹ :
            fan.algebraicRealization.functionFieldˣ) : fan.algebraicRealization.functionField) =
      (rationalCharacterUnit fan nonempty
        (normalizedToricResidueCharacter fan regular b ell character cone) :
          fan.algebraicRealization.functionField) := by
  letI := toricSchemeIntegral fan nonempty
  have units_equality :
      rationalCharacterUnit fan nonempty (coneDivisorCharacter fan regular b cone) *
        rationalCharacterUnit fan nonempty character *
        Units.map (toricPowerFunctionField fan nonempty regular ell hell).toMonoidHom
          ((rationalCharacterUnit fan nonempty
            (coneDivisorCharacter fan regular (toricResidueCoefficients fan b ell character) cone))⁻¹) =
      rationalCharacterUnit fan nonempty
        (normalizedToricResidueCharacter fan regular b ell character cone) := by
    rw [← rationalCharacterUnit_neg, toricPowerFunctionField_character,
      ← rationalCharacterUnit_add, ← rationalCharacterUnit_add]
    congr 1
    simp only [normalizedToricResidueCharacter, smul_neg, sub_eq_add_neg]
  exact congrArg Units.val units_equality

/-- Every local regularity requirement for the global residue morphism is
proved from the literal Euclidean remainder formula. -/
def toricResidueCompatibility (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b : fan.Ray → ℤ) (ell : ℕ) (hell : 0 < ell)
    (character : N →+ ℤ) :
    letI := toricSchemeIntegral fan nonempty
    CartierResidueCompatibility (toricPowerMap fan ell)
      (toricPower_genericPoint fan nonempty regular ell hell)
      (invariantCartierDivisor fan nonempty regular (toricResidueCoefficients fan b ell character))
      (invariantCartierDivisor fan nonempty regular b)
      (rationalCharacterUnit fan nonempty character : fan.algebraicRealization.functionField) := by
  letI := toricSchemeIntegral fan nonempty
  let sourceAtlas := invariantDivisorCharacterAtlas fan regular
    (toricResidueCoefficients fan b ell character)
  let targetAtlas := invariantDivisorCharacterAtlas fan regular b
  refine {
    Index := fan.cones
    chart := fun cone => (fan.affineToricChartι cone).opensRange
    covers := (targetAtlas.cartierEquationAtlas nonempty).covers
    sourceEquation := fun cone => rationalCharacterUnit fan nonempty
      (coneDivisorCharacter fan regular (toricResidueCoefficients fan b ell character) cone)
    targetEquation := fun cone => rationalCharacterUnit fan nonempty
      (coneDivisorCharacter fan regular b cone)
    source_local := fun cone point member =>
      (sourceAtlas.cartierEquationAtlas nonempty).equation_isLocalEquationAt cone point member
    target_local := fun cone point member =>
      (targetAtlas.cartierEquationAtlas nonempty).equation_isLocalEquationAt cone point member
    preserved := toricPower_preimage_chartOpen fan ell hell
    regular_ratio := ?_ }
  intro cone point member
  change (rationalCharacterUnit fan nonempty (coneDivisorCharacter fan regular b cone) :
      fan.algebraicRealization.functionField) *
    (rationalCharacterUnit fan nonempty character : fan.algebraicRealization.functionField) *
    toricPowerFunctionField fan nonempty regular ell hell
      (((rationalCharacterUnit fan nonempty
        (coneDivisorCharacter fan regular (toricResidueCoefficients fan b ell character) cone))⁻¹ :
          fan.algebraicRealization.functionFieldˣ) : fan.algebraicRealization.functionField) ∈ _
  rw [toricResidue_ratio_eq_character]
  have h := chartCoordinateGerm_mem_stalkRange fan nonempty cone
    (normalizedToricResidueMonomial fan regular b ell hell character cone) point member
  rw [normalizedToricResidueMonomial_germ] at h
  exact h

/-- The global residue summand morphism for arbitrary invariant divisors on
arbitrary smooth toric fans. It is the rational-monomial map on every open. -/
def toricResidueSheafMap (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b : fan.Ray → ℤ) (ell : ℕ) (hell : 0 < ell)
    (character : N →+ ℤ) :
    letI := toricSchemeIntegral fan nonempty
    (invariantCartierDivisor fan nonempty regular
      (toricResidueCoefficients fan b ell character)).sheaf ⟶
      (Scheme.Modules.pushforward (toricPowerMap fan ell)).obj
        (invariantCartierDivisor fan nonempty regular b).sheaf := by
  letI := toricSchemeIntegral fan nonempty
  exact (toricResidueCompatibility fan nonempty regular b ell hell character).sheafMap

theorem toricResidueSheafMap_rational (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b : fan.Ray → ℤ) (ell : ℕ) (hell : 0 < ell)
    (character : N →+ ℤ) :
    letI := toricSchemeIntegral fan nonempty
    toricResidueSheafMap fan nonempty regular b ell hell character ≫
      (Scheme.Modules.pushforward (toricPowerMap fan ell)).map
        (invariantCartierDivisor fan nonempty regular b).sheafι =
      cartierRationalMap (toricPowerMap fan ell)
        (toricPower_genericPoint fan nonempty regular ell hell)
        (invariantCartierDivisor fan nonempty regular
          (toricResidueCoefficients fan b ell character))
        (rationalCharacterUnit fan nonempty character : fan.algebraicRealization.functionField) := by
  letI := toricSchemeIntegral fan nonempty
  exact (toricResidueCompatibility fan nonempty regular b ell hell character).sheafMap_ι

section FiniteResidueFamily

variable {κ : Type u} [Fintype κ]

def toricResidueSheafFamily (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (basis : Module.Basis κ ℤ (N →+ ℤ))
    (b : fan.Ray → ℤ) (ell : ℕ) : LatticeResidues κ ell → fan.algebraicRealization.Modules :=
  fun residue =>
    letI := toricSchemeIntegral fan nonempty
    (invariantCartierDivisor fan nonempty regular
      (toricResidueCoefficients fan b ell
        (basis.equivFun.symm (latticeResidueRepresentative residue)))).sheaf

/-- The canonical global splitting morphism. Its local isomorphism property
is a separate theorem obtained from the affine residue decomposition. -/
def toricResidueSheafSum (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (basis : Module.Basis κ ℤ (N →+ ℤ))
    (b : fan.Ray → ℤ) (ell : ℕ) (hell : 0 < ell) :
    letI := toricSchemeIntegral fan nonempty
    (⨁ toricResidueSheafFamily fan nonempty regular basis b ell) ⟶
      (Scheme.Modules.pushforward (toricPowerMap fan ell)).obj
        (invariantCartierDivisor fan nonempty regular b).sheaf :=
  biproduct.desc (fun residue => toricResidueSheafMap fan nonempty regular b ell hell
    (basis.equivFun.symm (latticeResidueRepresentative residue)))

theorem toricResidueSheafSum_summand (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (basis : Module.Basis κ ℤ (N →+ ℤ))
    (b : fan.Ray → ℤ) (ell : ℕ) (hell : 0 < ell) (residue : LatticeResidues κ ell) :
    letI := toricSchemeIntegral fan nonempty
    biproduct.ι (toricResidueSheafFamily fan nonempty regular basis b ell) residue ≫
      toricResidueSheafSum fan nonempty regular basis b ell hell =
        toricResidueSheafMap fan nonempty regular b ell hell
          (basis.equivFun.symm (latticeResidueRepresentative residue)) := by
  simp only [toricResidueSheafSum, biproduct.ι_desc]

end FiniteResidueFamily

end ToricResidues

end ToricPower
