module

public import ToricPower.AffineFiniteGenerators

/-!
# Finite generators from a coherent affine restriction

Only the displayed affine restriction is required to be coherent.
The ambient sheaf may be an infinite quasicoherent open direct image.
The construction retains a genuine finite generating epimorphism on
the image-open slice.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme.Modules

namespace ToricPower

universe u

/-- A finite presentation on the actual affine restriction produces
finite generating sections on its actual image open. -/
theorem exists_finite_generatingSections_of_affine_restriction
    {A X : Scheme.{u}} [IsAffine A] (j : A ⟶ X) [IsOpenImmersion j]
    (M : X.Modules) [(M.restrict j).IsFinitePresentation] :
    ∃ G : (M.over j.opensRange).GeneratingSections, G.IsFiniteType := by
  obtain ⟨P,hP⟩ := (M.restrict j).exists_isFinite_presentation_of_isAffine
  letI := hP
  let F := restrictFunctor j.isoOpensRange.inv
  letI : PreservesColimitsOfSize.{u,u} F :=
    (restrictAdjunction j.isoOpensRange.inv).leftAdjoint_preservesColimits
  let e : F.obj (M.restrict j) ≅ M.restrict j.opensRange.ι :=
    ((restrictFunctorComp j.isoOpensRange.inv j).app M).symm ≪≫
      (restrictFunctorCongr (Scheme.Hom.isoOpensRange_inv_comp j)).app M
  let Q := @SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _ e.hom
    (Iso.isIso_hom e) (P.map F (restrictUnitIso j.isoOpensRange.inv).symm)
  have hQ : Q.IsFinite := by exact SheafOfModules.instIsFiniteOfIsIso _ _
  letI := hQ
  let H : j.opensRange.toScheme.Modules ⥤
      SheafOfModules (X.ringCatSheaf.over j.opensRange) := (overEquiv j.opensRange).inverse
  letI : PreservesColimitsOfSize.{u,u} H :=
    (overEquiv j.opensRange).symm.toAdjunction.leftAdjoint_preservesColimits
  let e' : H.obj (M.restrict j.opensRange.ι) ≅ M.over j.opensRange :=
    (overEquiv j.opensRange).inverse.mapIso ((overFunctorEquiv j.opensRange).app M).symm ≪≫
      ((overEquiv j.opensRange).unitIso.app (M.over j.opensRange)).symm
  let Q' := (Q.map H
    (j.opensRange.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm).ofIsIso e'.hom
  have hQ' : Q'.IsFinite := by exact SheafOfModules.instIsFiniteOfIsIso _ _
  letI := hQ'
  exact ⟨Q'.generators,inferInstance⟩

end ToricPower

end
