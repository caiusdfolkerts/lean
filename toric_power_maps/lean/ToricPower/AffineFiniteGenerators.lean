module

public import ToricPower.CoherentCategory
public import ToricPower.CartierAtlasSectionGluing

/-!
# Finite generators on the actual affine-open slice

A finite presentation on an affine scheme is transported to its actual
slice site. The exported generating family is an epimorphism of sheaves,
not just a statement that a selected collection of global elements spans.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Scheme.Modules

namespace ToricPower

universe u

variable {X : Scheme.{u}}

local instance affineGeneratorsFromSpecIsOpenImmersion (U : X.affineOpens) :
    IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec

/-- A coherent sheaf has a finite generating family on every affine-open
slice, with its actual epimorphism retained. -/
theorem exists_finite_generatingSections_over_affine
    (M : X.Modules) [M.IsFinitePresentation] (U : X.affineOpens) :
    ∃ G : (M.over U.1).GeneratingSections, G.IsFiniteType := by
  let K := M.restrict U.2.fromSpec
  letI : K.IsFinitePresentation := finitePresentation_restrict U.2.fromSpec M
  obtain ⟨P, hP⟩ := K.exists_isFinite_presentation_of_isAffine
  letI := hP
  let F : SheafOfModules (Spec Γ(X, U.1)).ringCatSheaf ⥤
      SheafOfModules U.1.toScheme.ringCatSheaf := restrictFunctor U.2.isoSpec.hom
  letI : PreservesColimitsOfSize.{u,u} F :=
    (restrictAdjunction U.2.isoSpec.hom).leftAdjoint_preservesColimits
  let e : F.obj K ≅ M.restrict U.1.ι :=
    ((restrictFunctorComp U.2.isoSpec.hom U.2.fromSpec).app M).symm ≪≫
      (restrictFunctorCongr U.2.isoSpec_hom_fromSpec).app M
  let Q := @SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _ e.hom
    (Iso.isIso_hom e) (P.map F (restrictUnitIso U.2.isoSpec.hom).symm)
  have hQ : Q.IsFinite := by
    exact SheafOfModules.instIsFiniteOfIsIso _ _
  letI := hQ
  let H : SheafOfModules U.1.toScheme.ringCatSheaf ⥤
      SheafOfModules (X.ringCatSheaf.over U.1) := (overEquiv U.1).inverse
  letI : PreservesColimitsOfSize.{u,u} H :=
    (overEquiv U.1).symm.toAdjunction.leftAdjoint_preservesColimits
  let e' : H.obj (M.restrict U.1.ι) ≅ M.over U.1 :=
    (overEquiv U.1).inverse.mapIso ((overFunctorEquiv U.1).app M).symm ≪≫
      ((overEquiv U.1).unitIso.app (M.over U.1)).symm
  let Q' := (Q.map H (U.1.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm).ofIsIso
    e'.hom
  have hQ' : Q'.IsFinite := by
    exact SheafOfModules.instIsFiniteOfIsIso _ _
  letI := hQ'
  exact ⟨Q'.generators, inferInstance⟩

/-- A compatible section family on an open slice is determined by its
value on the terminal object of that slice. -/
theorem overModuleSection_top (M : X.Modules) (U : X.Opens)
    (s : (M.over U).sections) :
    overModuleSection M U (s.val (op (Over.mk (𝟙 U)))) = s := by
  apply PresheafOfModules.sections_ext
  intro W
  exact s.property (Over.homMk W.unop.hom : W.unop ⟶ Over.mk (𝟙 U)).op

/-- The `a`th actual generator morphism is the section map belonging to
its value on the whole affine open. -/
theorem generatingSections_ι_π (M : X.Modules) (U : X.Opens)
    (G : (M.over U).GeneratingSections) (a : G.I) :
    SheafOfModules.ιFree a ≫ G.π =
      overSectionHom M U ((G.s a).val (op (Over.mk (𝟙 U)))) := by
  rw [overSectionHom, overModuleSection_top]
  exact (SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply G.π a).symm.trans
    (congrArg (M.over U).unitHomEquiv.symm
      (congrFun ((M.over U).freeHomEquiv.apply_symm_apply G.s) a))

end ToricPower

end
