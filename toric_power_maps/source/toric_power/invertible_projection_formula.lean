module

public import ToricPower.CoherentPullback

/-! ## Source module `ToricPower.InvertibleProjectionFormula`
Original SHA256: 067b6a75115af2d5f9c183a820513a2b2b37adc06d9f1033c1d690e3a0c4ab14.
Original sources are retained in `third_party/coherent_sources`.
-/
section CoherentSource11

/-!
# Actual projection formula for invertible sheaves

These recovered proof bodies construct the ordinary scheme-module projection
map and prove it is an isomorphism for every invertible target sheaf. No
finite, flat, completeness, generation, or supplied projection-formula
hypothesis is used. The sheaf-theoretic dependencies are the actual
scheme-module constructions in this project. Verification status is supplied
by the ordinary Lean build records.
-/

/-! Source: `BondalThomsen/Toric/Frobenius/MultiplicationProjectionFormula.lean` at commit9a2bdcdcf6b25710459f7f476c9c62de3039b7bb.
Original SHA256: be1feb17428fe9fb5b03ed4964356356d8a819c811f971845b90b588178826be. Only the general scheme-module portion is used. -/
section ProjectionSource1

@[expose] public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry TopologicalSpace Opposite

namespace BondalThomsen

universe u

noncomputable section

variable {Source Target : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
def projectionSectionAction (morphism : Source ⟶ Target)
    (source_module : Source.Modules) (open_set : Target.Opens)
    (scalar : Γ(Source, morphism ⁻¹ᵁ open_set))
    (element : source_module.val.obj (op (morphism ⁻¹ᵁ open_set))) :
    source_module.val.obj (op (morphism ⁻¹ᵁ open_set)) :=
  letI : Module (Γ(Source, morphism ⁻¹ᵁ open_set))
      (source_module.val.obj (op (morphism ⁻¹ᵁ open_set))) :=
    (source_module.val.obj (op (morphism ⁻¹ᵁ open_set))).isModule
  scalar • element

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
def projectionActionPresheaf (morphism : Source ⟶ Target)
    (target_module : Target.Modules) (source_module : Source.Modules)
    (comparison : target_module ⟶ (Scheme.Modules.pushforward morphism).obj source_module) :
    target_module.val ⊗
      ((Scheme.Modules.pushforward morphism).obj
        (SheafOfModules.unit Source.ringCatSheaf)).val ⟶
      ((Scheme.Modules.pushforward morphism).obj source_module).val where
  app open_set := by
    letI : Module (Γ(Source, morphism ⁻¹ᵁ open_set.unop))
        (source_module.val.obj (op (morphism ⁻¹ᵁ open_set.unop))) :=
      (source_module.val.obj (op (morphism ⁻¹ᵁ open_set.unop))).isModule
    exact ModuleCat.MonoidalCategory.tensorLift
      (fun element scalar => projectionSectionAction morphism source_module open_set.unop
        scalar (comparison.val.app open_set element))
      (by intros; simp [projectionSectionAction, smul_add])
      (by
        intro scalar element coefficient
        change Γ(Source, morphism ⁻¹ᵁ open_set.unop) at coefficient
        let image : source_module.val.obj (op (morphism ⁻¹ᵁ open_set.unop)) :=
          comparison.val.app open_set element
        dsimp [projectionSectionAction]
        rw [map_smul]
        change (coefficient : Γ(Source, morphism ⁻¹ᵁ open_set.unop)) •
            ((morphism.app open_set.unop) scalar • image) =
          (morphism.app open_set.unop) scalar •
            ((coefficient : Γ(Source, morphism ⁻¹ᵁ open_set.unop)) • image)
        exact smul_comm _ _ _)
      (by intros; simp [projectionSectionAction, add_smul])
      (by
        intro scalar element coefficient
        change Γ(Source, morphism ⁻¹ᵁ open_set.unop) at coefficient
        let image : source_module.val.obj (op (morphism ⁻¹ᵁ open_set.unop)) :=
          comparison.val.app open_set element
        dsimp [projectionSectionAction]
        change ((morphism.app open_set.unop) scalar *
            (coefficient : Source.ringCatSheaf.obj.obj
              (op (morphism ⁻¹ᵁ open_set.unop)))) • image =
          (morphism.app open_set.unop) scalar •
            ((coefficient : Γ(Source, morphism ⁻¹ᵁ open_set.unop)) • image)
        exact mul_smul _ _ _)
  naturality {first_open second_open} inclusion := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro element scalar
    change Γ(Source, morphism ⁻¹ᵁ first_open.unop) at scalar
    let : Module (Γ(Source, morphism ⁻¹ᵁ first_open.unop))
        (source_module.val.obj (op (morphism ⁻¹ᵁ first_open.unop))) :=
      (source_module.val.obj (op (morphism ⁻¹ᵁ first_open.unop))).isModule
    let : Module (Γ(Source, morphism ⁻¹ᵁ second_open.unop))
        (source_module.val.obj (op (morphism ⁻¹ᵁ second_open.unop))) :=
      (source_module.val.obj (op (morphism ⁻¹ᵁ second_open.unop))).isModule
    dsimp [PresheafOfModulesOfCommRing.Monoidal.tensorObj,
      PresheafOfModulesOfCommRing.Monoidal.tensorObjMap,
      ModuleCat.MonoidalCategory.tensorLift, ModuleCat.RestrictScalars.map']
    change projectionSectionAction morphism source_module second_open.unop
        ((Source.presheaf.map ((Opens.map morphism.base).map inclusion.unop).op) scalar)
        (comparison.val.app second_open (target_module.val.map inclusion element)) =
      source_module.val.map ((Opens.map morphism.base).map inclusion.unop).op
        (projectionSectionAction morphism source_module first_open.unop scalar
          (comparison.val.app first_open element))
    have naturality := PresheafOfModules.naturality_apply comparison.val inclusion element
    dsimp [ModuleCat.RestrictScalars.map'] at naturality
    rw [naturality]
    exact (source_module.val.map_smul _ scalar _).symm

set_option backward.isDefEq.respectTransparency false in
def projectionAction (morphism : Source ⟶ Target)
    (target_module : Target.Modules) (source_module : Source.Modules)
    (comparison : target_module ⟶ (Scheme.Modules.pushforward morphism).obj source_module) :
    target_module ⊗ (Scheme.Modules.pushforward morphism).obj
      (SheafOfModules.unit Source.ringCatSheaf) ⟶
        (Scheme.Modules.pushforward morphism).obj source_module :=
  (SheafOfModules.tensorUnderlyingIso (R := Target.sheaf) _ _).hom ≫
    ((PresheafOfModules.sheafificationAdjunction (𝟙 Target.ringCatSheaf.obj)).homEquiv
      _ _).symm (projectionActionPresheaf morphism target_module source_module comparison)

def schemeProjectionFormulaMap (morphism : Source ⟶ Target)
    (target_module : Target.Modules) :
    target_module ⊗ (Scheme.Modules.pushforward morphism).obj
      (SheafOfModules.unit Source.ringCatSheaf) ⟶
        (Scheme.Modules.pushforward morphism).obj
          ((Scheme.Modules.pullback morphism).obj target_module) :=
  projectionAction morphism target_module _
    ((Scheme.Modules.pullbackPushforwardAdjunction morphism).unit.app target_module)

def projectionOpenPushforwardIso (morphism : Source ⟶ Target) (open_set : Target.Opens) :
    Scheme.Modules.pushforward (morphism ⁻¹ᵁ open_set).ι ⋙
        Scheme.Modules.pushforward morphism ≅
      Scheme.Modules.pushforward (morphism ∣_ open_set) ⋙
        Scheme.Modules.pushforward open_set.ι :=
  Scheme.Modules.pushforwardComp _ _ ≪≫
    Scheme.Modules.pushforwardCongr (morphismRestrict_ι morphism open_set).symm ≪≫
    (Scheme.Modules.pushforwardComp _ _).symm

set_option backward.isDefEq.respectTransparency false in
def projectionOpenPullbackIso (morphism : Source ⟶ Target) (open_set : Target.Opens) :
    Scheme.Modules.restrictFunctor open_set.ι ⋙
        Scheme.Modules.pullback (morphism ∣_ open_set) ≅
      Scheme.Modules.pullback morphism ⋙
        Scheme.Modules.restrictFunctor (morphism ⁻¹ᵁ open_set).ι :=
  (conjugateIsoEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction morphism).comp
      (Scheme.Modules.restrictAdjunction (morphism ⁻¹ᵁ open_set).ι))
    ((Scheme.Modules.restrictAdjunction open_set.ι).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (morphism ∣_ open_set)))).symm
    (projectionOpenPushforwardIso morphism open_set)

set_option backward.isDefEq.respectTransparency false in
def projectionOpenSourceTrivialization (morphism : Source ⟶ Target)
    (open_set : Target.Opens) (target_module : Target.Modules)
    (trivialization : target_module.restrict open_set.ι ≅
      SheafOfModules.unit open_set.toScheme.ringCatSheaf) :
    ((Scheme.Modules.pullback morphism).obj target_module).restrict
        (morphism ⁻¹ᵁ open_set).ι ≅
      SheafOfModules.unit (morphism ⁻¹ᵁ open_set).toScheme.ringCatSheaf :=
  (projectionOpenPullbackIso morphism open_set).symm.app target_module ≪≫
    (Scheme.Modules.pullback (morphism ∣_ open_set)).mapIso trivialization ≪≫
    Scheme.Modules.pullbackObjUnitIso (morphism ∣_ open_set)

set_option backward.isDefEq.respectTransparency false in
lemma projectionOpenSourceTrivialization_unit (morphism : Source ⟶ Target)
    (open_set : Target.Opens) (target_module : Target.Modules)
    (trivialization : target_module.restrict open_set.ι ≅
      SheafOfModules.unit open_set.toScheme.ringCatSheaf) :
    (Scheme.Modules.pullbackPushforwardAdjunction morphism).unit.app target_module ≫
        (Scheme.Modules.pushforward morphism).map
          ((Scheme.Modules.restrictAdjunction (morphism ⁻¹ᵁ open_set).ι).unit.app _ ≫
            (Scheme.Modules.pushforward (morphism ⁻¹ᵁ open_set).ι).map
              (projectionOpenSourceTrivialization morphism open_set target_module
                trivialization).hom) ≫
        (projectionOpenPushforwardIso morphism open_set).hom.app _ =
      (Scheme.Modules.restrictAdjunction open_set.ι).unit.app target_module ≫
        (Scheme.Modules.pushforward open_set.ι).map
          (trivialization.hom ≫
            SheafOfModules.unitToPushforwardObjUnit
              (morphism ∣_ open_set).toRingCatSheafHom) := by
  let global_adjunction := (Scheme.Modules.pullbackPushforwardAdjunction morphism).comp
    (Scheme.Modules.restrictAdjunction (morphism ⁻¹ᵁ open_set).ι)
  let local_adjunction := (Scheme.Modules.restrictAdjunction open_set.ι).comp
    (Scheme.Modules.pullbackPushforwardAdjunction (morphism ∣_ open_set))
  have conjugate : conjugateEquiv global_adjunction local_adjunction
      (projectionOpenPullbackIso morphism open_set).hom =
      (projectionOpenPushforwardIso morphism open_set).hom :=
    (conjugateEquiv global_adjunction local_adjunction).apply_symm_apply _
  have mapped := Adjunction.homEquiv_conjugateEquiv global_adjunction local_adjunction
    (projectionOpenPullbackIso morphism open_set).hom
    (projectionOpenSourceTrivialization morphism open_set target_module trivialization).hom
  rw [conjugate] at mapped
  have local_transpose : local_adjunction.homEquiv _ _
      ((projectionOpenPullbackIso morphism open_set).hom.app target_module ≫
        (projectionOpenSourceTrivialization morphism open_set target_module trivialization).hom) =
      (Scheme.Modules.restrictAdjunction open_set.ι).unit.app target_module ≫
        (Scheme.Modules.pushforward open_set.ι).map
          (trivialization.hom ≫ SheafOfModules.unitToPushforwardObjUnit
            (morphism ∣_ open_set).toRingCatSheafHom) := by
    have cancel : (projectionOpenPullbackIso morphism open_set).hom.app target_module ≫
        (projectionOpenSourceTrivialization morphism open_set target_module trivialization).hom =
      (Scheme.Modules.pullback (morphism ∣_ open_set)).map trivialization.hom ≫
        (Scheme.Modules.pullbackObjUnitIso (morphism ∣_ open_set)).hom := by
      change (projectionOpenPullbackIso morphism open_set).hom.app target_module ≫
          ((projectionOpenPullbackIso morphism open_set).inv.app target_module ≫
            (Scheme.Modules.pullback (morphism ∣_ open_set)).map trivialization.hom ≫
              (Scheme.Modules.pullbackObjUnitIso (morphism ∣_ open_set)).hom) = _
      simp
    rw [cancel]
    change (Scheme.Modules.restrictAdjunction open_set.ι).homEquiv _ _
      ((Scheme.Modules.pullbackPushforwardAdjunction (morphism ∣_ open_set)).homEquiv _ _
        ((Scheme.Modules.pullback (morphism ∣_ open_set)).map trivialization.hom ≫
          (Scheme.Modules.pullbackObjUnitIso (morphism ∣_ open_set)).hom)) = _
    rw [Adjunction.homEquiv_naturality_left]
    have unit_transpose :=
      Scheme.Modules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitIso_hom
        (morphism ∣_ open_set)
    change (Scheme.Modules.pullbackPushforwardAdjunction (morphism ∣_ open_set)).homEquiv
      (SheafOfModules.unit open_set.toScheme.ringCatSheaf)
      (SheafOfModules.unit (morphism ⁻¹ᵁ open_set).toScheme.ringCatSheaf)
      (Scheme.Modules.pullbackObjUnitIso (morphism ∣_ open_set)).hom = _ at unit_transpose
    trans (Scheme.Modules.restrictAdjunction open_set.ι).homEquiv _ _
      (trivialization.hom ≫ SheafOfModules.unitToPushforwardObjUnit
        (morphism ∣_ open_set).toRingCatSheafHom)
    · exact congrArg (fun transpose =>
        (Scheme.Modules.restrictAdjunction open_set.ι).homEquiv _ _
          (trivialization.hom ≫ transpose)) unit_transpose
    · rfl
  rw [local_transpose] at mapped
  change (Scheme.Modules.pullbackPushforwardAdjunction morphism).homEquiv _ _
      ((Scheme.Modules.restrictAdjunction (morphism ⁻¹ᵁ open_set).ι).homEquiv _ _
        (projectionOpenSourceTrivialization morphism open_set target_module trivialization).hom) ≫
      (projectionOpenPushforwardIso morphism open_set).hom.app _ = _ at mapped
  simpa only [Adjunction.homEquiv_unit, Category.assoc] using mapped

end

end BondalThomsen


-- Close scopes implicitly ended by the original source EOF.
end
end ProjectionSource1

/-! Source: `BondalThomsen/Toric/Cohomology/InvertibleProjectionFormula.lean` at commit9a2bdcdcf6b25710459f7f476c9c62de3039b7bb.
Original SHA256: 5873451938427b0725a98f9c5f137a368158c4e1d27a6164b5cd9da457ec7e35. Only the general scheme-module portion is used. -/
section ProjectionSource2

@[expose] public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry TopologicalSpace Opposite

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen

universe u

noncomputable section

variable {Source Target : Scheme.{u}}

def projectionOpenModuleComparison (morphism : Source ⟶ Target)
    (open_set : Target.Opens) (source_module : Source.Modules)
    (trivialization : source_module.restrict (morphism ⁻¹ᵁ open_set).ι ≅
      SheafOfModules.unit (morphism ⁻¹ᵁ open_set).toScheme.ringCatSheaf) :
    (Scheme.Modules.pushforward morphism).obj source_module ⟶
      (Scheme.Modules.pushforward open_set.ι).obj
        ((Scheme.Modules.pushforward (morphism ∣_ open_set)).obj
          (SheafOfModules.unit (morphism ⁻¹ᵁ open_set).toScheme.ringCatSheaf)) :=
  (Scheme.Modules.pushforward morphism).map
      ((Scheme.Modules.restrictAdjunction (morphism ⁻¹ᵁ open_set).ι).unit.app source_module ≫
        (Scheme.Modules.pushforward (morphism ⁻¹ᵁ open_set).ι).map trivialization.hom) ≫
    (projectionOpenPushforwardIso morphism open_set).hom.app _

def projectionOpenUnitComparison (morphism : Source ⟶ Target)
    (open_set : Target.Opens) :=
  projectionOpenModuleComparison morphism open_set
    (SheafOfModules.unit Source.ringCatSheaf)
    (Scheme.Modules.restrictUnitIso (morphism ⁻¹ᵁ open_set).ι)

lemma projectionOpenPreimage_eq (morphism : Source ⟶ Target)
    (open_set : Target.Opens) (target_open : Target.Opens) :
    (morphism ⁻¹ᵁ open_set).ι ⁻¹ᵁ (morphism ⁻¹ᵁ target_open) =
      (morphism ∣_ open_set) ⁻¹ᵁ (open_set.ι ⁻¹ᵁ target_open) := by
  rw [← Scheme.Hom.comp_preimage, ← morphismRestrict_ι,
    Scheme.Hom.comp_preimage]

set_option backward.isDefEq.respectTransparency false in
lemma projectionOpenPushforwardIso_app (morphism : Source ⟶ Target)
    (open_set : Target.Opens)
    (local_module : (morphism ⁻¹ᵁ open_set).toScheme.Modules)
    (target_open : Target.Opens) :
    ((projectionOpenPushforwardIso morphism open_set).hom.app local_module).app target_open =
      local_module.presheaf.map
        (eqToHom (projectionOpenPreimage_eq morphism open_set target_open).symm).op := by
  simp only [projectionOpenPushforwardIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforwardComp_hom_app_app,
    Scheme.Modules.pushforwardComp_inv_app_app, Scheme.Modules.pushforwardCongr_hom_app_app,
    Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
lemma projectionOpenModuleComparison_smul (morphism : Source ⟶ Target)
    (open_set : Target.Opens) (source_module : Source.Modules)
    (trivialization : source_module.restrict (morphism ⁻¹ᵁ open_set).ι ≅
      SheafOfModules.unit (morphism ⁻¹ᵁ open_set).toScheme.ringCatSheaf)
    (target_open : Target.Opens) (scalar : Γ(Source, morphism ⁻¹ᵁ target_open))
    (element : source_module.val.obj (op (morphism ⁻¹ᵁ target_open))) :
    (projectionOpenModuleComparison morphism open_set source_module trivialization).val.app
        (op target_open) (projectionSectionAction morphism source_module target_open scalar element) =
      (show Γ((morphism ⁻¹ᵁ open_set).toScheme,
          (morphism ∣_ open_set) ⁻¹ᵁ (open_set.ι ⁻¹ᵁ target_open)) from
        (projectionOpenUnitComparison morphism open_set).val.app (op target_open) scalar) *
      (show Γ((morphism ⁻¹ᵁ open_set).toScheme,
          (morphism ∣_ open_set) ⁻¹ᵁ (open_set.ι ⁻¹ᵁ target_open)) from
        (projectionOpenModuleComparison morphism open_set source_module trivialization).val.app
          (op target_open) element) := by
  let source_open := morphism ⁻¹ᵁ open_set
  let local_open := source_open.ι ⁻¹ᵁ (morphism ⁻¹ᵁ target_open)
  let unit_map := (Scheme.Modules.restrictAdjunction source_open.ι).unit.app source_module
  let : Module (Γ(source_open.toScheme, local_open))
      ((source_module.restrict source_open.ι).val.obj (op local_open)) :=
    ((source_module.restrict source_open.ι).val.obj (op local_open)).isModule
  let image : (source_module.restrict source_open.ι).val.obj (op local_open) :=
    unit_map.val.app (op (morphism ⁻¹ᵁ target_open)) element
  have scalar_action : unit_map.val.app (op (morphism ⁻¹ᵁ target_open))
      (projectionSectionAction morphism source_module target_open scalar element) =
      (source_open.ι.app (morphism ⁻¹ᵁ target_open)) scalar • image :=
    (unit_map.val.app _).hom.map_smul scalar element
  have local_action : trivialization.hom.val.app (op local_open)
      ((source_open.ι.app (morphism ⁻¹ᵁ target_open)) scalar • image) =
      (source_open.ι.app (morphism ⁻¹ᵁ target_open)) scalar *
        (show Γ(source_open.toScheme, local_open) from
          trivialization.hom.val.app (op local_open) image) :=
    (trivialization.hom.val.app _).hom.map_smul _ _
  have comparison_apply (argument : source_module.val.obj (op (morphism ⁻¹ᵁ target_open))) :
      (projectionOpenModuleComparison morphism open_set source_module trivialization).val.app
          (op target_open) argument =
        (source_open.toScheme.presheaf.map
          (eqToHom (projectionOpenPreimage_eq morphism open_set target_open).symm).op)
            (trivialization.hom.val.app (op local_open)
              (unit_map.val.app (op (morphism ⁻¹ᵁ target_open)) argument)) := by
    change ((projectionOpenPushforwardIso morphism open_set).hom.app
        (SheafOfModules.unit source_open.toScheme.ringCatSheaf)).app target_open
          (trivialization.hom.val.app (op local_open)
            (unit_map.val.app (op (morphism ⁻¹ᵁ target_open)) argument)) = _
    rw [projectionOpenPushforwardIso_app]
    rfl
  rw [comparison_apply, scalar_action, local_action, comparison_apply]
  change source_open.toScheme.presheaf.map _ (_ * _) =
    _ * source_open.toScheme.presheaf.map _ _
  rw [map_mul]
  congr 1
  change _ = ((projectionOpenPushforwardIso morphism open_set).hom.app
      (SheafOfModules.unit source_open.toScheme.ringCatSheaf)).app target_open
        ((Scheme.Modules.restrictUnitIso source_open.ι).hom.val.app (op local_open)
          (((Scheme.Modules.restrictAdjunction source_open.ι).unit.app
            (SheafOfModules.unit Source.ringCatSheaf)).val.app
              (op (morphism ⁻¹ᵁ target_open)) scalar))
  rw [projectionOpenPushforwardIso_app]
  change source_open.toScheme.presheaf.map _
      (source_open.ι.app (morphism ⁻¹ᵁ target_open) scalar) =
    source_open.toScheme.presheaf.map _
      ((source_open.ι.appIso local_open).hom
        (Source.presheaf.map
          (homOfLE (source_open.ι.image_preimage_le (morphism ⁻¹ᵁ target_open))).op scalar))
  congr 1
  have equality := source_open.ι.app_appIso_inv (morphism ⁻¹ᵁ target_open)
  have evaluated := congrArg (fun arrow => arrow scalar) equality
  have mapped := congrArg (fun value => (source_open.ι.appIso local_open).hom value) evaluated
  change (source_open.ι.appIso local_open).hom
      ((source_open.ι.appIso local_open).inv
        (source_open.ι.app (morphism ⁻¹ᵁ target_open) scalar)) = _ at mapped
  rw [Iso.inv_hom_id_apply] at mapped
  exact mapped

set_option backward.isDefEq.respectTransparency false in
lemma projectionOpenModuleComparison_app_isIso (morphism : Source ⟶ Target)
    (open_set : Target.Opens) (source_module : Source.Modules)
    (trivialization : source_module.restrict (morphism ⁻¹ᵁ open_set).ι ≅
      SheafOfModules.unit (morphism ⁻¹ᵁ open_set).toScheme.ringCatSheaf)
    (subopen : open_set.toScheme.Opens) :
    IsIso ((projectionOpenModuleComparison morphism open_set source_module trivialization).val.app
      (op (open_set.ι ''ᵁ subopen))) := by
  have image_eq : (morphism ⁻¹ᵁ open_set).ι ''ᵁ
      ((morphism ⁻¹ᵁ open_set).ι ⁻¹ᵁ (morphism ⁻¹ᵁ (open_set.ι ''ᵁ subopen))) =
      morphism ⁻¹ᵁ (open_set.ι ''ᵁ subopen) := by
    rw [← image_morphismRestrict_preimage morphism open_set subopen,
      Scheme.Hom.preimage_image_eq]
  have inclusion_eq : homOfLE ((morphism ⁻¹ᵁ open_set).ι.image_preimage_le
      (morphism ⁻¹ᵁ (open_set.ι ''ᵁ subopen))) = eqToHom image_eq := Subsingleton.elim _ _
  let unit_iso : IsIso (((Scheme.Modules.restrictAdjunction
      (morphism ⁻¹ᵁ open_set).ι).unit.app source_module).app
        (morphism ⁻¹ᵁ (open_set.ι ''ᵁ subopen))) := by
    rw [Scheme.Modules.restrictAdjunction_unit_app_app, inclusion_eq]
    infer_instance
  let : IsIso (((Scheme.Modules.restrictAdjunction
      (morphism ⁻¹ᵁ open_set).ι).unit.app source_module).val.app
        (op (morphism ⁻¹ᵁ (open_set.ι ''ᵁ subopen)))) := by
    let : IsIso ((forget₂ (ModuleCat _) AddCommGrpCat).map
        (((Scheme.Modules.restrictAdjunction (morphism ⁻¹ᵁ open_set).ι).unit.app
          source_module).val.app (op (morphism ⁻¹ᵁ (open_set.ι ''ᵁ subopen))))) := unit_iso
    exact isIso_of_reflects_iso _ (forget₂ (ModuleCat _) AddCommGrpCat)
  let : IsIso ((projectionOpenPushforwardIso morphism open_set).hom.app
      (SheafOfModules.unit (morphism ⁻¹ᵁ open_set).toScheme.ringCatSheaf)).val :=
    inferInstanceAs (IsIso ((SheafOfModules.forget _).map
      ((projectionOpenPushforwardIso morphism open_set).hom.app _)))
  let : IsIso trivialization.hom.val :=
    inferInstanceAs (IsIso ((SheafOfModules.forget _).map trivialization.hom))
  let : IsIso ((Scheme.Modules.pushforward (morphism ⁻¹ᵁ open_set).ι).map
      trivialization.hom).val :=
    inferInstanceAs (IsIso ((SheafOfModules.forget _).map
      ((Scheme.Modules.pushforward (morphism ⁻¹ᵁ open_set).ι).map trivialization.hom)))
  let : IsIso (((Scheme.Modules.pushforward (morphism ⁻¹ᵁ open_set).ι).map
      trivialization.hom).val.app (op (morphism ⁻¹ᵁ (open_set.ι ''ᵁ subopen)))) :=
    inferInstanceAs (IsIso ((PresheafOfModules.evaluation _ _).map
      ((Scheme.Modules.pushforward (morphism ⁻¹ᵁ open_set).ι).map trivialization.hom).val))
  let : IsIso (((projectionOpenPushforwardIso morphism open_set).hom.app
      (SheafOfModules.unit (morphism ⁻¹ᵁ open_set).toScheme.ringCatSheaf)).val.app
        (op (open_set.ι ''ᵁ subopen))) :=
    inferInstanceAs (IsIso ((PresheafOfModules.evaluation _ _).map
      ((projectionOpenPushforwardIso morphism open_set).hom.app _).val))
  change IsIso ((ModuleCat.restrictScalars (morphism.app
      (open_set.ι ''ᵁ subopen)).hom).map
        (((Scheme.Modules.restrictAdjunction (morphism ⁻¹ᵁ open_set).ι).unit.app
          source_module).val.app (op (morphism ⁻¹ᵁ (open_set.ι ''ᵁ subopen))) ≫
          ((Scheme.Modules.pushforward (morphism ⁻¹ᵁ open_set).ι).map
            trivialization.hom).val.app (op (morphism ⁻¹ᵁ (open_set.ι ''ᵁ subopen)))) ≫
      ((projectionOpenPushforwardIso morphism open_set).hom.app
        (SheafOfModules.unit (morphism ⁻¹ᵁ open_set).toScheme.ringCatSheaf)).val.app
          (op (open_set.ι ''ᵁ subopen)))
  infer_instance

def projectionOpenTargetComparison (open_set : Target.Opens) (target_module : Target.Modules)
    (trivialization : target_module.restrict open_set.ι ≅
      SheafOfModules.unit open_set.toScheme.ringCatSheaf) :
    target_module ⟶ (Scheme.Modules.pushforward open_set.ι).obj
      (SheafOfModules.unit open_set.toScheme.ringCatSheaf) :=
  (Scheme.Modules.restrictAdjunction open_set.ι).unit.app target_module ≫
    (Scheme.Modules.pushforward open_set.ι).map trivialization.hom

set_option backward.isDefEq.respectTransparency false in
lemma projectionOpenTargetComparison_app_isIso (open_set : Target.Opens)
    (target_module : Target.Modules)
    (trivialization : target_module.restrict open_set.ι ≅
      SheafOfModules.unit open_set.toScheme.ringCatSheaf)
    (subopen : open_set.toScheme.Opens) :
    IsIso ((projectionOpenTargetComparison open_set target_module trivialization).val.app
      (op (open_set.ι ''ᵁ subopen))) := by
  have image_eq : open_set.ι ''ᵁ (open_set.ι ⁻¹ᵁ (open_set.ι ''ᵁ subopen)) =
      open_set.ι ''ᵁ subopen := by rw [Scheme.Hom.preimage_image_eq]
  have inclusion_eq : homOfLE (open_set.ι.image_preimage_le (open_set.ι ''ᵁ subopen)) =
      eqToHom image_eq := Subsingleton.elim _ _
  let unit_iso : IsIso (((Scheme.Modules.restrictAdjunction open_set.ι).unit.app
      target_module).app (open_set.ι ''ᵁ subopen)) := by
    rw [Scheme.Modules.restrictAdjunction_unit_app_app, inclusion_eq]
    infer_instance
  let : IsIso (((Scheme.Modules.restrictAdjunction open_set.ι).unit.app
      target_module).val.app (op (open_set.ι ''ᵁ subopen))) := by
    let : IsIso ((forget₂ (ModuleCat _) AddCommGrpCat).map
        (((Scheme.Modules.restrictAdjunction open_set.ι).unit.app target_module).val.app
          (op (open_set.ι ''ᵁ subopen)))) := unit_iso
    exact isIso_of_reflects_iso _ (forget₂ (ModuleCat _) AddCommGrpCat)
  let : IsIso ((Scheme.Modules.pushforward open_set.ι).map trivialization.hom).val :=
    inferInstanceAs (IsIso ((SheafOfModules.forget _).map
      ((Scheme.Modules.pushforward open_set.ι).map trivialization.hom)))
  let : IsIso (((Scheme.Modules.pushforward open_set.ι).map trivialization.hom).val.app
      (op (open_set.ι ''ᵁ subopen))) :=
    inferInstanceAs (IsIso ((PresheafOfModules.evaluation _ _).map
      ((Scheme.Modules.pushforward open_set.ι).map trivialization.hom).val))
  change IsIso (_ ≫ _)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
lemma projectionOpenStructureComparison_app_isIso (open_set : Target.Opens)
    (subopen : open_set.toScheme.Opens) :
    IsIso ((SheafOfModules.unitToPushforwardObjUnit open_set.ι.toRingCatSheafHom).val.app
      (op (open_set.ι ''ᵁ subopen))) := by
  have equality := open_set.ι.appIso_hom subopen
  let : IsIso (open_set.toScheme.presheaf.map
      (eqToHom (open_set.ι.preimage_image_eq subopen).symm).op) := inferInstance
  let : IsIso (open_set.ι.app (open_set.ι ''ᵁ subopen) ≫
      open_set.toScheme.presheaf.map
        (eqToHom (open_set.ι.preimage_image_eq subopen).symm).op) := by
    rw [← equality]
    infer_instance
  let : IsIso (open_set.ι.app (open_set.ι ''ᵁ subopen)) :=
    IsIso.of_isIso_comp_right _ (open_set.toScheme.presheaf.map
      (eqToHom (open_set.ι.preimage_image_eq subopen).symm).op)
  let : IsIso ((forget₂ (ModuleCat _) AddCommGrpCat).map
      ((SheafOfModules.unitToPushforwardObjUnit open_set.ι.toRingCatSheafHom).val.app
        (op (open_set.ι ''ᵁ subopen)))) :=
    inferInstanceAs (IsIso (((forget₂ CommRingCat RingCat) ⋙
      forget₂ RingCat AddCommGrpCat).map (open_set.ι.app (open_set.ι ''ᵁ subopen))))
  exact isIso_of_reflects_iso _ (forget₂ (ModuleCat _) AddCommGrpCat)

set_option backward.isDefEq.respectTransparency false in
lemma projectionActionPresheaf_app_isIso_on_trivializing_open
    (morphism : Source ⟶ Target) (open_set : Target.Opens)
    (target_module : Target.Modules)
    (trivialization : target_module.restrict open_set.ι ≅
      SheafOfModules.unit open_set.toScheme.ringCatSheaf)
    (subopen : open_set.toScheme.Opens) :
    IsIso ((projectionActionPresheaf morphism target_module
      ((Scheme.Modules.pullback morphism).obj target_module)
      ((Scheme.Modules.pullbackPushforwardAdjunction morphism).unit.app target_module)).app
        (op (open_set.ι ''ᵁ subopen))) := by
  let target_open := open_set.ι ''ᵁ subopen
  let : CommRing (Target.ringCatSheaf.obj.obj (op target_open)) :=
    inferInstanceAs (CommRing (Γ(Target, target_open)))
  let source_module := (Scheme.Modules.pullback morphism).obj target_module
  let source_trivialization :=
    projectionOpenSourceTrivialization morphism open_set target_module trivialization
  let target_comparison :=
    (projectionOpenTargetComparison open_set target_module trivialization).val.app (op target_open)
  let source_comparison := (projectionOpenModuleComparison morphism open_set source_module
    source_trivialization).val.app (op target_open)
  let unit_comparison := (projectionOpenUnitComparison morphism open_set).val.app (op target_open)
  let structure_comparison :=
    (SheafOfModules.unitToPushforwardObjUnit open_set.ι.toRingCatSheafHom).val.app (op target_open)
  let : IsIso target_comparison :=
    projectionOpenTargetComparison_app_isIso open_set target_module trivialization subopen
  let : IsIso source_comparison :=
    projectionOpenModuleComparison_app_isIso morphism open_set source_module
      source_trivialization subopen
  let : IsIso unit_comparison :=
    projectionOpenModuleComparison_app_isIso morphism open_set _ _ subopen
  let : IsIso structure_comparison :=
    projectionOpenStructureComparison_app_isIso open_set subopen
  let coordinate := target_comparison ≫ inv structure_comparison
  let canonical := (projectionActionPresheaf morphism target_module source_module
    ((Scheme.Modules.pullbackPushforwardAdjunction morphism).unit.app target_module)).app
      (op target_open)
  have equality : canonical ≫ source_comparison =
      (coordinate ⊗ₘ unit_comparison) ≫ (λ_ _).hom := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro element scalar
    change Γ(Source, morphism ⁻¹ᵁ target_open) at scalar
    change source_comparison
        (projectionSectionAction morphism source_module target_open scalar
          (((Scheme.Modules.pullbackPushforwardAdjunction morphism).unit.app
            target_module).val.app (op target_open) element)) =
      (show Γ(Target, target_open) from coordinate element) • unit_comparison scalar
    rw [projectionOpenModuleComparison_smul]
    have comparison_unit := projectionOpenSourceTrivialization_unit morphism open_set
      target_module trivialization
    have evaluated := congrArg (fun arrow => arrow.val.app (op target_open) element) comparison_unit
    change source_comparison
      (((Scheme.Modules.pullbackPushforwardAdjunction morphism).unit.app target_module).val.app
        (op target_open) element) =
      (morphism ∣_ open_set).app (open_set.ι ⁻¹ᵁ target_open)
        (target_comparison element) at evaluated
    rw [evaluated]
    have coordinate_eq : structure_comparison (coordinate element) =
        target_comparison element := by
      change structure_comparison (inv structure_comparison (target_comparison element)) = _
      exact Iso.inv_hom_id_apply (asIso structure_comparison) _
    rw [← coordinate_eq]
    change _ * _ = (morphism ∣_ open_set).app (open_set.ι ⁻¹ᵁ target_open)
      (open_set.ι.app target_open (coordinate element)) * _
    exact mul_comm _ _
  let : IsIso coordinate := inferInstanceAs (IsIso (target_comparison ≫ inv structure_comparison))
  let : IsIso (canonical ≫ source_comparison) := by
    rw [equality]
    infer_instance
  exact IsIso.of_isIso_comp_right canonical source_comparison

set_option backward.isDefEq.respectTransparency false in
lemma projectionActionPresheaf_over_isIso (morphism : Source ⟶ Target)
    (open_set : Target.Opens) (target_module : Target.Modules)
    (trivialization : target_module.restrict open_set.ι ≅
      SheafOfModules.unit open_set.toScheme.ringCatSheaf) :
    IsIso ((PresheafOfModules.pushforward (F := Over.forget open_set)
      (TauCeti.SheafOfModules.pushforwardRingIso
        (J := (Opens.grothendieckTopology Target).over open_set)
        (K := Opens.grothendieckTopology Target) (Over.forget open_set)
        Target.ringCatSheaf).inv).map
        (projectionActionPresheaf morphism target_module
          ((Scheme.Modules.pullback morphism).obj target_module)
          ((Scheme.Modules.pullbackPushforwardAdjunction morphism).unit.app target_module))) := by
  rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
  rw [NatTrans.isIso_iff_isIso_app]
  intro local_open
  let ambient_open := local_open.unop.left
  let subopen := open_set.ι ⁻¹ᵁ ambient_open
  have image_eq : open_set.ι ''ᵁ subopen = ambient_open := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr (leOfHom local_open.unop.hom)]
  have section_iso := projectionActionPresheaf_app_isIso_on_trivializing_open
    morphism open_set target_module trivialization subopen
  rw [image_eq] at section_iso
  let := section_iso
  exact inferInstanceAs (IsIso ((forget₂ (ModuleCat _) AddCommGrpCat).map
    ((projectionActionPresheaf morphism target_module
      ((Scheme.Modules.pullback morphism).obj target_module)
      ((Scheme.Modules.pullbackPushforwardAdjunction morphism).unit.app target_module)).app
        (op ambient_open))))

set_option backward.isDefEq.respectTransparency false in
lemma schemeProjectionFormulaMap_over_isIso (morphism : Source ⟶ Target)
    (open_set : Target.Opens) (target_module : Target.Modules)
    (trivialization : target_module.restrict open_set.ι ≅
      SheafOfModules.unit open_set.toScheme.ringCatSheaf) :
    IsIso ((SheafOfModules.overFunctor Target.ringCatSheaf open_set).map
      (schemeProjectionFormulaMap morphism target_module)) := by
  let section_action := projectionActionPresheaf morphism target_module
    ((Scheme.Modules.pullback morphism).obj target_module)
    ((Scheme.Modules.pullbackPushforwardAdjunction morphism).unit.app target_module)
  let sheafify := PresheafOfModules.sheafification (𝟙 Target.ringCatSheaf.obj)
  let restrict := SheafOfModules.overFunctor Target.ringCatSheaf open_set
  let : IsIso ((PresheafOfModules.pushforward (F := Over.forget open_set)
      (TauCeti.SheafOfModules.pushforwardRingIso
        (J := (Opens.grothendieckTopology Target).over open_set)
        (K := Opens.grothendieckTopology Target) (Over.forget open_set)
        Target.ringCatSheaf).inv).map section_action) :=
    projectionActionPresheaf_over_isIso morphism open_set target_module trivialization
  have naturality := TauCeti.SheafOfModules.overSheafificationIso_inv_naturality
    Target.ringCatSheaf section_action open_set
  let : IsIso (restrict.map (sheafify.map section_action)) := by
    have : IsIso ((TauCeti.SheafOfModules.overSheafificationIso Target.ringCatSheaf _
        open_set).inv ≫ restrict.map (sheafify.map section_action)) := by
      rw [← naturality]
      infer_instance
    exact IsIso.of_isIso_comp_left
      (TauCeti.SheafOfModules.overSheafificationIso Target.ringCatSheaf _ open_set).inv _
  change IsIso (restrict.map (projectionAction morphism target_module _ _))
  unfold projectionAction
  rw [Adjunction.homEquiv_counit, Functor.map_comp, Functor.map_comp]
  infer_instance

set_option backward.isDefEq.respectTransparency false in

theorem schemeProjectionFormulaMap_isIso_of_isInvertible (morphism : Source ⟶ Target)
    (target_module : Target.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible Target target_module] :
    IsIso (schemeProjectionFormulaMap morphism target_module) := by
  let trivializations := TauCeti.SheafOfModules.LocalTrivializations.ofIsInvertible target_module
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf Target.ringCatSheaf)]
  apply CategoryTheory.Sheaf.isIso_of_coversTop trivializations.coversTop
  intro index
  let local_iso := (TauCeti.SheafOfModules.LocalTrivializations.unitIsoRestrict
    (trivializations.iso index)).symm
  let := schemeProjectionFormulaMap_over_isIso morphism (trivializations.X index)
    target_module local_iso
  exact inferInstanceAs (IsIso ((SheafOfModules.toSheaf _).map
    ((SheafOfModules.overFunctor Target.ringCatSheaf (trivializations.X index)).map
      (schemeProjectionFormulaMap morphism target_module))))

set_option backward.isDefEq.respectTransparency false in

def schemeInvertibleProjectionFormulaIso (morphism : Source ⟶ Target)
    (bundle : TauCeti.AlgebraicGeometry.InvertibleSheaf Target) :
    (Scheme.Modules.pushforward morphism).obj
        ((Scheme.Modules.pullback morphism).obj bundle.obj) ≅
      bundle.obj ⊗ (Scheme.Modules.pushforward morphism).obj
        (SheafOfModules.unit Source.ringCatSheaf) :=
  letI := schemeProjectionFormulaMap_isIso_of_isInvertible morphism bundle.obj
  (asIso (schemeProjectionFormulaMap morphism bundle.obj)).symm

@[simp]
lemma schemeInvertibleProjectionFormulaIso_inv (morphism : Source ⟶ Target)
    (bundle : TauCeti.AlgebraicGeometry.InvertibleSheaf Target) :
    (schemeInvertibleProjectionFormulaIso morphism bundle).inv =
      schemeProjectionFormulaMap morphism bundle.obj := rfl

end

end BondalThomsen

-- Close scopes implicitly ended by the original source EOF.
end
end ProjectionSource2

/-! ## Objectwise retraction for an actual invertible sheaf -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry

namespace ToricPower

universe u

/-- Any splitting of the pushed-forward structure sheaf gives an actual
retract `L ↪ f_* f^* L ↠ L` for each invertible sheaf. The splitting is not
required to coincide with an adjunction unit, and no flatness hypothesis is
used. -/
def invertibleSheafRetractPushforwardPullback {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    (r : Retract (SheafOfModules.unit Y.ringCatSheaf)
      ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)))
    (L : TauCeti.AlgebraicGeometry.InvertibleSheaf Y) :
    Retract L.obj ((Scheme.Modules.pushforward f).obj
      ((Scheme.Modules.pullback f).obj L.obj)) :=
  (Retract.ofIso (ρ_ L.obj).symm).trans
    ((r.map (tensorLeft L.obj)).trans
      (Retract.ofIso (BondalThomsen.schemeInvertibleProjectionFormulaIso f L).symm))

end ToricPower


-- Close scopes implicitly ended by the original source EOF.
end
end CoherentSource11
