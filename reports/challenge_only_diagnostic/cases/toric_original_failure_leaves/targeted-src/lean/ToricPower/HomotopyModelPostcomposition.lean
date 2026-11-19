module

public import ToricPower.AdditiveHomotopyDerivedFunctor
public import ToricPower.MappedCochainComplexPresentation

/-!
# Mapping genuine homotopy models, with the full map comparison

The supplied model isomorphisms live in the homotopy category. Applying
an additive coefficient functor and then localizing preserves their
naturality, for every chain map realizing the original homotopy map.
The construction is independent of any concrete inverse-Nakayama
presentation.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
namespace ToricPower

universe u v u' v' w
variable {C : Type u} [Category.{v} C]
  {A : Type u'} [Category.{v'} A] [Abelian A] [HasDerivedCategory.{w} A]
  (T : A ⥤ A) [T.Additive] (F : C ⥤ HomotopyCategory A (.up ℤ))
  (models : C → CochainComplex A ℤ)
  (comparison : ∀ X, F.obj X ≅ (HomotopyCategory.quotient A (.up ℤ)).obj (models X))

def mappedHomotopyModelIso (X : C) :
    (F ⋙ additiveHomotopyDerived T).obj X ≅
      DerivedCategory.Q.obj (SerrePairing.mappedCochainComplex T (models X)) :=
  (additiveHomotopyDerived T).mapIso (comparison X) ≪≫
    (additiveHomotopyDerivedFactors T).app (models X) ≪≫
      eqToIso (congrArg DerivedCategory.Q.obj
        (SerrePairing.mappedCochainComplex_eq T (models X)))

theorem mappedHomotopyModelIso_naturality {X Y : C} (f : X ⟶ Y)
    (h : models X ⟶ models Y)
    (lifts : F.map f ≫ (comparison Y).hom =
      (comparison X).hom ≫ (HomotopyCategory.quotient A (.up ℤ)).map h) :
    (F ⋙ additiveHomotopyDerived T).map f ≫
        (mappedHomotopyModelIso T F models comparison Y).hom =
      (mappedHomotopyModelIso T F models comparison X).hom ≫
        DerivedCategory.Q.map ((T.mapHomologicalComplex (.up ℤ)).map h) := by
  simp only [mappedHomotopyModelIso, Iso.trans_hom, CategoryTheory.Functor.mapIso_hom,
    eqToIso.hom, eqToHom_refl, Category.comp_id, CategoryTheory.Functor.comp_map,
    Category.assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc, lifts,
    CategoryTheory.Functor.map_comp, Category.assoc]
  have natural := (additiveHomotopyDerivedFactors T).hom.naturality h
  change (additiveHomotopyDerived T).map
      ((HomotopyCategory.quotient A (.up ℤ)).map h) ≫
        (additiveHomotopyDerivedFactors T).hom.app (models Y) =
      (additiveHomotopyDerivedFactors T).hom.app (models X) ≫
        DerivedCategory.Q.map ((T.mapHomologicalComplex (.up ℤ)).map h) at natural
  simpa only [Iso.app_hom, Category.assoc] using
    congrArg (fun g => (additiveHomotopyDerived T).map (comparison X).hom ≫ g) natural

/-- A whole-functor presentation is applied before evaluating an object.
This also accommodates any equal reassociation of the actual composite. -/
def presentedMappedHomotopyModelIso (K : C ⥤ DerivedCategory A)
    (presentation : K ≅ F ⋙ additiveHomotopyDerived T) (X : C) :
    K.obj X ≅ DerivedCategory.Q.obj (SerrePairing.mappedCochainComplex T (models X)) :=
  presentation.app X ≪≫ mappedHomotopyModelIso T F models comparison X

theorem presentedMappedHomotopyModelIso_naturality
    (K : C ⥤ DerivedCategory A) (presentation : K ≅ F ⋙ additiveHomotopyDerived T)
    {X Y : C} (f : X ⟶ Y) (h : models X ⟶ models Y)
    (lifts : F.map f ≫ (comparison Y).hom =
      (comparison X).hom ≫ (HomotopyCategory.quotient A (.up ℤ)).map h) :
    K.map f ≫ (presentedMappedHomotopyModelIso T F models comparison K presentation Y).hom =
      (presentedMappedHomotopyModelIso T F models comparison K presentation X).hom ≫
        DerivedCategory.Q.map ((T.mapHomologicalComplex (.up ℤ)).map h) := by
  simp only [presentedMappedHomotopyModelIso, Iso.trans_hom, Iso.app_hom, Category.assoc]
  rw [← Category.assoc, presentation.hom.naturality, Category.assoc,
    mappedHomotopyModelIso_naturality T F models comparison f h lifts]

end ToricPower
end
