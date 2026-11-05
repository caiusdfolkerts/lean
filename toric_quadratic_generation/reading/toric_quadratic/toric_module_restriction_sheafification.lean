module

public import PaperVerification.ToricIntrinsicDifferentialSheaf
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

@[expose] public section

/-!
# Actual module sheafification on an open subscheme

Restriction to an open subscheme is the literal restriction on the open
image, with scalars transported by the structure-sheaf isomorphism. It
preserves local bijections because the open-image functor is
cocontinuous. Consequently it commutes with actual module
sheafification, including its universal map.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

variable {X Y : Scheme.{u}} (j : X⟶Y) [IsOpenImmersion j]

set_option backward.defeqAttrib.useBackward true in
def openPresheafRestrict :
    PresheafOfModulesOfCommRing.{u} Y.presheaf⥤
      PresheafOfModulesOfCommRing.{u} X.presheaf :=
  let α : X.presheaf⟶j.opensFunctor.op⋙Y.presheaf :=
    { app U := (j.appIso U.unop).inv }
  PresheafOfModules.pushforward (Functor.whiskerRight α (forget₂ CommRingCat RingCat))

@[simp] theorem openPresheafRestrict_sheaf_val (M : Y.Modules) :
    (openPresheafRestrict j).obj M.val=(M.restrict j).val := rfl

@[simp] theorem openPresheafRestrict_map_apply
    {P Q : PresheafOfModulesOfCommRing.{u} Y.presheaf} (f : P⟶Q)
    (U : X.Opens) (s : P.obj (op (j ''ᵁ U))) :
    ((openPresheafRestrict j).map f).app (op U) s=f.app (op (j ''ᵁ U)) s := rfl

theorem openPresheafRestrict_locallyInjective
    {P Q : PresheafOfModulesOfCommRing.{u} Y.presheaf} (f : P⟶Q)
    [CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology Y)
      ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map f)] :
    CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        ((openPresheafRestrict j).map f)) := by
  change CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
    (Functor.whiskerLeft j.opensFunctor.op
      ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map f))
  exact CategoryTheory.Presheaf.isLocallyInjective_whisker
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) j.opensFunctor
    ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map f)

theorem openPresheafRestrict_locallySurjective
    {P Q : PresheafOfModulesOfCommRing.{u} Y.presheaf} (f : P⟶Q)
    [CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y)
      ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map f)] :
    CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        ((openPresheafRestrict j).map f)) := by
  change CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
    (Functor.whiskerLeft j.opensFunctor.op
      ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map f))
  exact CategoryTheory.Presheaf.isLocallySurjective_whisker
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) j.opensFunctor
    ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map f)

variable (P : PresheafOfModulesOfCommRing.{u} Y.presheaf)

def openRestrictionSheafificationUnit : (openPresheafRestrict j).obj P⟶
    (Scheme.Modules.restrict
      ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj P) j).val :=
  (openPresheafRestrict j).map
    ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app P)

instance openRestrictionSheafificationUnit_locallyInjective :
    CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        (openRestrictionSheafificationUnit j P)) := by
  letI : CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology Y)
      ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 Y.ringCatSheaf.obj)).unit.app P)) := by
    change CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology Y)
      (CategoryTheory.toSheafify (Opens.grothendieckTopology Y) P.presheaf)
    infer_instance
  exact openPresheafRestrict_locallyInjective j
    ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app P)

instance openRestrictionSheafificationUnit_locallySurjective :
    CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        (openRestrictionSheafificationUnit j P)) := by
  letI : CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y)
      ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 Y.ringCatSheaf.obj)).unit.app P)) := by
    change CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y)
      (CategoryTheory.toSheafify (Opens.grothendieckTopology Y) P.presheaf)
    infer_instance
  exact openPresheafRestrict_locallySurjective j
    ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app P)

instance openRestrictionSheafificationUnit_sheafification_isIso :
    IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (openRestrictionSheafificationUnit j P)) := by
  have hW := (Opens.grothendieckTopology X).W_of_isLocallyBijective
    ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
      (openRestrictionSheafificationUnit j P))
  change ((Opens.grothendieckTopology X).W.inverseImage
    (PresheafOfModules.toPresheaf X.ringCatSheaf.obj))
      (openRestrictionSheafificationUnit j P) at hW
  rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
    (𝟙 X.ringCatSheaf.obj)] at hW
  exact hW

/-- The canonical comparison, derived from actual sheafification of a
locally bijective restriction map. -/
def openRestrictionSheafificationIso :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
      ((openPresheafRestrict j).obj P) ≅
        Scheme.Modules.restrict
          ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj P) j :=
  asIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    (openRestrictionSheafificationUnit j P)) ≪≫
      (asIso (PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).counit).app
          (Scheme.Modules.restrict
            ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj P) j)

set_option backward.isDefEq.respectTransparency.types false in
theorem openRestrictionSheafificationIso_unit :
    (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).unit.app ((openPresheafRestrict j).obj P) ≫
      (openRestrictionSheafificationIso j P).hom.val=
        openRestrictionSheafificationUnit j P := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let Q : X.Modules := Scheme.Modules.restrict
    ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj P) j
  have h : (adj.homEquiv ((openPresheafRestrict j).obj P) Q).symm
      (openRestrictionSheafificationUnit j P) =
        (openRestrictionSheafificationIso j P).hom := rfl
  have he := congrArg (adj.homEquiv ((openPresheafRestrict j).obj P) Q) h.symm
  exact he.trans
    ((adj.homEquiv ((openPresheafRestrict j).obj P) Q).apply_symm_apply
      (openRestrictionSheafificationUnit j P))

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.openRestrictionSheafificationIso
