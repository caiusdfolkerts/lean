module

public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Quotient

/-!
# Descent of a right-derived comparison through a quotient

A natural transformation between functors on a quotient is determined
by its precomposition with the quotient functor. Full faithfulness of
that precomposition also reflects the Kan-extension universal property.
This gives a short, explicit bridge from complexes to their homotopy
category, with the actual comparison isomorphisms retained.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace ToricPower

universe u v u' v' w z w' z'

variable {C : Type u} [Category.{v} C]
  {K : Type u'} [Category.{v'} K]
  {D : Type w} [Category.{z} D]
  {E : Type w'} [Category.{z'} E]

/-- An isomorphism of localization functors transports the universal
comparison by its actual inverse. -/
theorem rightKanExtension_baseIso {L L' : C ⥤ D} (e : L ≅ L')
    {F : C ⥤ E} (R : D ⥤ E) (β : F ⟶ L' ⋙ R)
    [R.IsLeftKanExtension β] :
    R.IsLeftKanExtension (β ≫ whiskerRight e.inv R) := by
  let Φ := leftExtensionEquivalenceOfIso₁ e.symm F
  have h := (isUniversalOfIsLeftKanExtension R β).isInitialObj
    Φ.functor (LeftExtension.mk R β)
  refine ⟨⟨IsInitial.ofIso h ?_⟩⟩
  exact StructuredArrow.isoMk (Iso.refl _) (by
    ext X
    simp [Φ, leftExtensionEquivalenceOfIso₁])

/-- Faithfulness of restriction on natural transformations suffices to
reflect the left Kan-extension universal property. -/
theorem rightKanExtension_of_precomp (q : C ⥤ K)
    [((whiskeringLeft C K E).obj q).Faithful]
    {L : K ⥤ D} {F : K ⥤ E} (R : D ⥤ E) (α : F ⟶ L ⋙ R)
    [R.IsLeftKanExtension
      (whiskerLeft q α ≫ (Functor.associator q L R).inv)] :
    R.IsLeftKanExtension α := by
  let Φ := LeftExtension.precomp L F q
  letI : Φ.Full := by dsimp [Φ, LeftExtension.precomp]; infer_instance
  letI : Φ.Faithful := by dsimp [Φ, LeftExtension.precomp]; infer_instance
  refine ⟨⟨IsInitial.isInitialOfObj Φ (LeftExtension.mk R α) ?_⟩⟩
  exact IsInitial.ofIso
    (isUniversalOfIsLeftKanExtension R
      (whiskerLeft q α ≫ (Functor.associator q L R).inv))
    (StructuredArrow.isoMk (Iso.refl _) (by
      ext X
      simp [Φ, LeftExtension.precomp]))

variable (q : C ⥤ K)
  [((whiskeringLeft C K E).obj q).Full]
  [((whiskeringLeft C K E).obj q).Faithful]
  {L : K ⥤ D} {L' : C ⥤ D} (eL : q ⋙ L ≅ L')
  {F : K ⥤ E} {F' : C ⥤ E} (eF : q ⋙ F ≅ F')
  (R : D ⥤ E) (β : F' ⟶ L' ⋙ R)

/-- The descended comparison, obtained by the actual fully faithful
restriction functor on natural transformations. -/
def rightKanQuotientComparison : F ⟶ L ⋙ R :=
  ((whiskeringLeft C K E).obj q).preimage
    (eF.hom ≫ β ≫ whiskerRight eL.inv R ≫ (Functor.associator q L R).hom)

@[simp]
theorem rightKanQuotientComparison_app (X : C) :
    (rightKanQuotientComparison q eL eF R β).app (q.obj X) =
      eF.hom.app X ≫ β.app X ≫ R.map (eL.inv.app X) := by
  have h := congr_app (Functor.map_preimage ((whiskeringLeft C K E).obj q)
    (eF.hom ≫ β ≫ whiskerRight eL.inv R ≫ (Functor.associator q L R).hom)) X
  simpa [rightKanQuotientComparison] using h

/-- The descended comparison has the full universal property whenever
the original one does. This is a theorem, not an assumed descent. -/
theorem rightKanQuotientComparison_isLeftKanExtension
    [R.IsLeftKanExtension β] :
    R.IsLeftKanExtension (rightKanQuotientComparison q eL eF R β) := by
  haveI := rightKanExtension_baseIso eL R β
  haveI : R.IsLeftKanExtension (eF.hom ≫ β ≫ whiskerRight eL.inv R) :=
    (isLeftKanExtension_iff_of_iso₂
      (eF.hom ≫ β ≫ whiskerRight eL.inv R)
      (β ≫ whiskerRight eL.inv R) eF (Iso.refl R) (by simp)).mpr inferInstance
  have he :
      whiskerLeft q (rightKanQuotientComparison q eL eF R β) ≫
        (Functor.associator q L R).inv = eF.hom ≫ β ≫ whiskerRight eL.inv R := by
    ext X
    simp only [NatTrans.comp_app, whiskerLeft_app, rightKanQuotientComparison_app,
      Functor.associator_inv_app, Category.comp_id, whiskerRight_app]
  haveI : R.IsLeftKanExtension
      (whiskerLeft q (rightKanQuotientComparison q eL eF R β) ≫
        (Functor.associator q L R).inv) := by rw [he]; infer_instance
  exact rightKanExtension_of_precomp q R (rightKanQuotientComparison q eL eF R β)

end ToricPower

end
