module

public import ToricPower.DivisorWeightCartierAtlas

/-!
# Local frames on actual scheme charts

These formulas compare sections on the slice site of an open image with
sections on its actual chart scheme. They also give extensionality of
maps out of the structure sheaf by the value of the global section one.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace ToricPower

universe schemeUniverse

@[simp] theorem commRingIsoToRingEquiv_apply {R S : CommRingCat.{schemeUniverse}}
    (e : R ≅ S) (x : R) : e.commRingCatIsoToRingEquiv x = e.hom x := rfl

theorem restrictFunctor_map_app {Source Target : Scheme.{schemeUniverse}} (inclusion : Source ⟶ Target)
    [IsOpenImmersion inclusion] {sourceSheaf targetSheaf : Target.Modules}
    (comparison : sourceSheaf ⟶ targetSheaf) (domain : Source.Opens) :
    Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctor inclusion).map comparison) domain =
      Scheme.Modules.Hom.app comparison (inclusion ''ᵁ domain) := by
  rfl


theorem restrictUnitIso_app {Source Target : Scheme.{schemeUniverse}} (inclusion : Source ⟶ Target)
    [IsOpenImmersion inclusion] (domain : Source.Opens)
    (sectionValue : Γ(Target, inclusion ''ᵁ domain)) :
    Scheme.Modules.Hom.app (Scheme.Modules.restrictUnitIso inclusion).hom domain sectionValue =
      (inclusion.appIso domain).hom sectionValue := by
  rfl

theorem restrictFunctorAdjCounitIso_app {Source Target : Scheme.{schemeUniverse}}
    (inclusion : Source ⟶ Target) [IsOpenImmersion inclusion]
    (moduleSheaf : Source.Modules) (domain : Source.Opens)
    (sectionValue : Γ(moduleSheaf, inclusion ⁻¹ᵁ inclusion ''ᵁ domain)) :
    Scheme.Modules.Hom.app
        ((Scheme.Modules.restrictFunctorAdjCounitIso inclusion).app moduleSheaf).hom domain
        sectionValue =
      moduleSheaf.presheaf.map (eqToHom (inclusion.preimage_image_eq domain).symm).op
        sectionValue := by
  rfl


theorem cartierOverToAffine_image {Source Target : Scheme.{schemeUniverse}}
    (inclusion : Source ⟶ Target) [IsOpenImmersion inclusion] (domain : Source.Opens) :
    inclusion ''ᵁ domain =
      inclusion.opensRange.ι ''ᵁ inclusion.isoOpensRange.hom ''ᵁ domain := by
  ext point
  change point ∈ Set.image inclusion (domain : Set Source) ↔
    point ∈ Set.image inclusion.opensRange.ι
      (Set.image inclusion.isoOpensRange.hom (domain : Set Source))
  have image := congrArg (fun morphism : Source ⟶ Target =>
    Set.image morphism (domain : Set Source)) inclusion.isoOpensRange_hom_ι
  simpa only [Set.image_image, Scheme.Hom.comp_apply] using
    Set.ext_iff.mp image.symm point

theorem cartierOverToAffineRestrictionIso_sections {Source Target : Scheme.{schemeUniverse}}
    (inclusion : Source ⟶ Target) [IsOpenImmersion inclusion]
    (moduleSheaf : Target.Modules) (domain : Source.Opens)
    (sectionValue : Γ((cartierOverToAffine inclusion).obj
      (moduleSheaf.over inclusion.opensRange), domain)) :
    Scheme.Modules.Hom.app (cartierOverToAffineRestrictionIso inclusion moduleSheaf).hom
      domain sectionValue =
    moduleSheaf.presheaf.map (eqToHom (cartierOverToAffine_image inclusion domain)).op
      sectionValue := by
  simp only [cartierOverToAffineRestrictionIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, Iso.symm_hom, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    restrictFunctor_map_app, Scheme.Modules.restrictFunctorComp_inv_app_app,
    Scheme.Modules.restrictFunctorCongr_hom_app_app]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  congr 2

theorem cartierOverToAffineRestrictionIso_inv_sections {Source Target : Scheme.{schemeUniverse}}
    (inclusion : Source ⟶ Target) [IsOpenImmersion inclusion]
    (moduleSheaf : Target.Modules) (domain : Source.Opens)
    (sectionValue : Γ(moduleSheaf.restrict inclusion, domain)) :
    Scheme.Modules.Hom.app (cartierOverToAffineRestrictionIso inclusion moduleSheaf).inv
      domain sectionValue =
    moduleSheaf.presheaf.map (eqToHom (cartierOverToAffine_image inclusion domain).symm).op
      sectionValue := by
  have cancellation := ConcreteCategory.congr_hom
    (congrArg (fun comparison => Scheme.Modules.Hom.app comparison domain)
      (cartierOverToAffineRestrictionIso inclusion moduleSheaf).inv_hom_id) sectionValue
  change Scheme.Modules.Hom.app (cartierOverToAffineRestrictionIso inclusion moduleSheaf).hom
    domain (Scheme.Modules.Hom.app (cartierOverToAffineRestrictionIso inclusion moduleSheaf).inv
      domain sectionValue) = sectionValue at cancellation
  apply (ConcreteCategory.bijective_of_isIso
    (moduleSheaf.presheaf.map (eqToHom (cartierOverToAffine_image inclusion domain)).op)).injective
  calc
    _ = sectionValue :=
      (cartierOverToAffineRestrictionIso_sections inclusion moduleSheaf domain _).symm.trans
        cancellation
    _ = _ := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      simp only [← op_comp, eqToHom_trans, eqToHom_refl, op_id]
      exact (ConcreteCategory.congr_hom (moduleSheaf.presheaf.map_id _) sectionValue).symm

theorem cartierOverToAffine_map_sections {Source Target : Scheme.{schemeUniverse}}
    (inclusion : Source ⟶ Target) [IsOpenImmersion inclusion]
    {sourceSheaf targetSheaf : SheafOfModules (Target.ringCatSheaf.over inclusion.opensRange)}
    (comparison : sourceSheaf ⟶ targetSheaf) (domain : Source.Opens)
    (sectionValue : Γ((cartierOverToAffine inclusion).obj sourceSheaf, domain)) :
    Scheme.Modules.Hom.app ((cartierOverToAffine inclusion).map comparison) domain
      sectionValue =
    comparison.val.app
      (op ((Opens.overEquivalence inclusion.opensRange).symm.functor.obj
        (inclusion.isoOpensRange.hom ''ᵁ domain))) sectionValue := by
  rfl

theorem restrictUnitIso_inv_sections {Source Target : Scheme.{schemeUniverse}}
    (inclusion : Source ⟶ Target) [IsOpenImmersion inclusion] (domain : Source.Opens)
    (sectionValue : Γ(Source, domain)) :
    Scheme.Modules.Hom.app (Scheme.Modules.restrictUnitIso inclusion).inv domain sectionValue =
      (inclusion.appIso domain).inv sectionValue := by
  rfl

theorem cartierOverToAffineFrame_sections {Source Target : Scheme.{schemeUniverse}}
    (inclusion : Source ⟶ Target) [IsOpenImmersion inclusion]
    (moduleSheaf : Target.Modules)
    (frame : (SheafOfModules.unit Target.ringCatSheaf).over inclusion.opensRange ≅
      moduleSheaf.over inclusion.opensRange)
    (domain : Source.Opens) (coefficient : Γ(Source, domain)) :
    Scheme.Modules.Hom.app (cartierOverToAffineFrame inclusion moduleSheaf frame).hom domain
      coefficient =
    moduleSheaf.presheaf.map (eqToHom (cartierOverToAffine_image inclusion domain)).op
      (frame.hom.val.app
        (op ((Opens.overEquivalence inclusion.opensRange).symm.functor.obj
          (inclusion.isoOpensRange.hom ''ᵁ domain)))
        (Target.presheaf.map (eqToHom (cartierOverToAffine_image inclusion domain).symm).op
          ((inclusion.appIso domain).inv coefficient))) := by
  change Scheme.Modules.Hom.app
    (cartierOverToAffineRestrictionIso inclusion moduleSheaf).hom domain
    (Scheme.Modules.Hom.app ((cartierOverToAffine inclusion).map frame.hom) domain
      (Scheme.Modules.Hom.app
        (cartierOverToAffineRestrictionIso inclusion (SheafOfModules.unit Target.ringCatSheaf)).inv
        domain (Scheme.Modules.Hom.app (Scheme.Modules.restrictUnitIso inclusion).inv
          domain coefficient))) = _
  simp only [
    restrictUnitIso_inv_sections, cartierOverToAffineRestrictionIso_inv_sections,
    cartierOverToAffine_map_sections, cartierOverToAffineRestrictionIso_sections]
  rfl

theorem cartierOverToAffineFrame_image_sections {Source Target : Scheme.{schemeUniverse}}
    (inclusion : Source ⟶ Target) [IsOpenImmersion inclusion]
    (moduleSheaf : Target.Modules)
    (frame : (SheafOfModules.unit Target.ringCatSheaf).over inclusion.opensRange ≅
      moduleSheaf.over inclusion.opensRange)
    (domain : Source.Opens) (coefficient : Γ(Source, domain)) :
    Scheme.Modules.Hom.app (cartierOverToAffineFrame inclusion moduleSheaf frame).hom domain
      coefficient =
    frame.hom.val.app (op (Over.mk (homOfLE (inclusion.image_le_opensRange domain))))
      ((inclusion.appIso domain).inv coefficient) := by
  rw [cartierOverToAffineFrame_sections]
  let original : Over inclusion.opensRange :=
    Over.mk (homOfLE (inclusion.image_le_opensRange domain))
  let transported := (Opens.overEquivalence inclusion.opensRange).symm.functor.obj
    (inclusion.isoOpensRange.hom ''ᵁ domain)
  let reindex : original ⟶ transported :=
    Over.homMk (eqToHom (cartierOverToAffine_image inclusion domain))
  have naturality := ConcreteCategory.congr_hom
    (frame.hom.val.naturality reindex.op)
    (Target.presheaf.map (eqToHom (cartierOverToAffine_image inclusion domain).symm).op
      ((inclusion.appIso domain).inv coefficient))
  change frame.hom.val.app (op original)
      (Target.presheaf.map (eqToHom (cartierOverToAffine_image inclusion domain)).op
        (Target.presheaf.map (eqToHom (cartierOverToAffine_image inclusion domain).symm).op
          ((inclusion.appIso domain).inv coefficient))) =
    moduleSheaf.presheaf.map (eqToHom (cartierOverToAffine_image inclusion domain)).op
      (frame.hom.val.app (op transported)
        (Target.presheaf.map (eqToHom (cartierOverToAffine_image inclusion domain).symm).op
          ((inclusion.appIso domain).inv coefficient))) at naturality
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp] at naturality
  simp only [← op_comp, eqToHom_trans, eqToHom_refl, op_id] at naturality
  rw [Target.presheaf.map_id] at naturality
  simp only [ConcreteCategory.id_apply] at naturality
  exact naturality.symm

theorem cartierOverToAffineFrame_top_sections {Source Target : Scheme.{schemeUniverse}}
    (inclusion : Source ⟶ Target) [IsOpenImmersion inclusion]
    (moduleSheaf : Target.Modules)
    (frame : (SheafOfModules.unit Target.ringCatSheaf).over inclusion.opensRange ≅
      moduleSheaf.over inclusion.opensRange)
    (coefficient : Γ(Target, inclusion.opensRange)) :
    Scheme.Modules.Hom.app (cartierOverToAffineFrame inclusion moduleSheaf frame).hom ⊤
      ((inclusion.appIso ⊤).hom
        (Target.presheaf.map (eqToHom inclusion.image_top_eq_opensRange).op coefficient)) =
    moduleSheaf.presheaf.map (eqToHom inclusion.image_top_eq_opensRange).op
      (frame.hom.val.app (op (Over.mk (𝟙 inclusion.opensRange))) coefficient) := by
  rw [cartierOverToAffineFrame_image_sections]
  have cancellation := ConcreteCategory.congr_hom (inclusion.appIso ⊤).hom_inv_id
    (Target.presheaf.map (eqToHom inclusion.image_top_eq_opensRange).op coefficient)
  change (inclusion.appIso ⊤).inv ((inclusion.appIso ⊤).hom _) = _ at cancellation
  rw [cancellation]
  let reindex : Over.mk (homOfLE (inclusion.image_le_opensRange ⊤)) ⟶
      Over.mk (𝟙 inclusion.opensRange) :=
    Over.homMk (eqToHom inclusion.image_top_eq_opensRange)
  exact ConcreteCategory.congr_hom (frame.hom.val.naturality reindex.op) coefficient

theorem cartierOverToAffineFrame_comp_top_sections {Source Target : Scheme.{schemeUniverse}}
    (inclusion : Source ⟶ Target) [IsOpenImmersion inclusion]
    {sourceSheaf targetSheaf : Target.Modules}
    (frame : (SheafOfModules.unit Target.ringCatSheaf).over inclusion.opensRange ≅
      sourceSheaf.over inclusion.opensRange)
    (comparison : sourceSheaf ⟶ targetSheaf)
    (coefficient : Γ(Target, inclusion.opensRange)) :
    Scheme.Modules.Hom.app
      ((cartierOverToAffineFrame inclusion sourceSheaf frame).hom ≫
        (Scheme.Modules.restrictFunctor inclusion).map comparison) ⊤
      ((inclusion.appIso ⊤).hom
        (Target.presheaf.map (eqToHom inclusion.image_top_eq_opensRange).op coefficient)) =
    targetSheaf.presheaf.map (eqToHom inclusion.image_top_eq_opensRange).op
      (Scheme.Modules.Hom.app comparison inclusion.opensRange
        (frame.hom.val.app (op (Over.mk (𝟙 inclusion.opensRange))) coefficient)) := by
  change Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctor inclusion).map comparison) ⊤
    (Scheme.Modules.Hom.app (cartierOverToAffineFrame inclusion sourceSheaf frame).hom ⊤ _) = _
  rw [cartierOverToAffineFrame_top_sections, restrictFunctor_map_app]
  exact ConcreteCategory.congr_hom
    (comparison.mapPresheaf.naturality (eqToHom inclusion.image_top_eq_opensRange).op)
    (frame.hom.val.app (op (Over.mk (𝟙 inclusion.opensRange))) coefficient)


theorem schemeHom_comp_apply {SchemeModel : Scheme.{schemeUniverse}}
    {sourceSheaf middleSheaf targetSheaf : SchemeModel.Modules}
    (first : sourceSheaf ⟶ middleSheaf) (second : middleSheaf ⟶ targetSheaf)
    (domain : SchemeModel.Opens) (sectionValue : Γ(sourceSheaf, domain)) :
    Scheme.Modules.Hom.app (first ≫ second) domain sectionValue =
      Scheme.Modules.Hom.app second domain
        (Scheme.Modules.Hom.app first domain sectionValue) := by
  rfl

theorem openImmersion_appIso_top_sections {Source Target : Scheme.{schemeUniverse}}
    (inclusion : Source ⟶ Target) [IsOpenImmersion inclusion]
    (coefficient : Γ(Source, ⊤)) :
    (inclusion.appIso ⊤).hom
      (Target.presheaf.map (eqToHom inclusion.image_top_eq_opensRange).op
        ((IsOpenImmersion.ΓIsoTop inclusion).hom coefficient)) = coefficient := by
  change (IsOpenImmersion.ΓIsoTop inclusion).inv
    ((IsOpenImmersion.ΓIsoTop inclusion).hom coefficient) = coefficient
  exact ConcreteCategory.congr_hom (IsOpenImmersion.ΓIsoTop inclusion).hom_inv_id coefficient

theorem scheme_appLE_restrict_sections {Source Target : Scheme.{schemeUniverse}}
    (morphism : Source ⟶ Target) {domain larger : Target.Opens}
    (contained : domain ≤ larger) (openSubset : Source.Opens)
    (preimage : openSubset ≤ morphism ⁻¹ᵁ domain)
    (sectionValue : Γ(Target, larger)) :
    morphism.appLE domain openSubset preimage
      (Target.presheaf.map (homOfLE contained).op sectionValue) =
    morphism.appLE larger openSubset
      (preimage.trans (Scheme.Hom.preimage_mono morphism contained)) sectionValue := by
  exact ConcreteCategory.congr_hom
    (Scheme.Hom.map_appLE morphism preimage (homOfLE contained).op) sectionValue

theorem openImmersion_appLE_top_sections {Source Target : Scheme.{schemeUniverse}}
    (inclusion : Source ⟶ Target) [IsOpenImmersion inclusion]
    (preimage : ⊤ ≤ inclusion ⁻¹ᵁ inclusion.opensRange)
    (coefficient : Γ(Source, ⊤)) :
    inclusion.appLE inclusion.opensRange ⊤ preimage
      ((IsOpenImmersion.ΓIsoTop inclusion).hom coefficient) = coefficient := by
  rw [← openImmersion_sectionsIso_inv]
  exact ConcreteCategory.congr_hom (IsOpenImmersion.ΓIsoTop inclusion).hom_inv_id coefficient

theorem unitSheafHom_ext_top {SchemeModel : Scheme.{schemeUniverse}} {moduleSheaf : SchemeModel.Modules}
    {first second : SheafOfModules.unit SchemeModel.ringCatSheaf ⟶ moduleSheaf}
    (same : Scheme.Modules.Hom.app first ⊤ (1 : Γ(SchemeModel, ⊤)) =
      Scheme.Modules.Hom.app second ⊤ (1 : Γ(SchemeModel, ⊤))) : first = second := by
  apply moduleSheaf.unitHomEquiv.injective
  apply PresheafOfModules.sections_ext
  intro domain
  have firstRestriction := (moduleSheaf.unitHomEquiv first).property
    (homOfLE (show domain.unop ≤ ⊤ from le_top)).op
  have secondRestriction := (moduleSheaf.unitHomEquiv second).property
    (homOfLE (show domain.unop ≤ ⊤ from le_top)).op
  rw [← firstRestriction, ← secondRestriction]
  exact congrArg (moduleSheaf.val.map
    (homOfLE (show domain.unop ≤ ⊤ from le_top)).op) same

theorem tildeUnit_toOpen_one (coordinateRing : CommRingCat.{schemeUniverse}) :
    tilde.toOpen (ModuleCat.of coordinateRing coordinateRing) ⊤ (1 : coordinateRing) =
      (1 : Γ(Spec coordinateRing, ⊤)) := by
  change StructureSheaf.toOpenₗ coordinateRing coordinateRing ⊤ 1 = 1
  exact StructureSheaf.const_one ⊤



end ToricPower
