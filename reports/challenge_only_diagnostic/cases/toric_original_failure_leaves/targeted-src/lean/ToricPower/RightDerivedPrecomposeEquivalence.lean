module

public import ToricPower.CategoricalFoundations
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived

/-!
# Precomposing an unbounded derived functor by an exact equivalence

The comparison is the original unit on the termwise transformed
complex. The proof uses the actual equivalence on complexes and its
actual induced derived equivalence, preserving the universal property.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace ToricPower

universe u v w z

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory A]
  {D : Type w} [Category.{z} D] [Abelian D] [HasDerivedCategory D]
  (E : A ≌ A) [E.functor.Additive]
  (H : A ⥤ D) [H.Additive]
  (RH : DerivedCategory A ⥤ DerivedCategory D)
  (α : H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RH)

/-- The literal comparison on the transformed coefficient complex. -/
def rightDerivedPrecomposeEquivalenceUnit :
    (E.functor ⋙ H).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ E.functor.mapDerivedCategory ⋙ RH :=
  whiskerLeft (E.functor.mapHomologicalComplex (.up ℤ)) α ≫
    whiskerRight E.functor.mapDerivedCategoryFactors.inv RH

/-- An exact equivalence transports the entire unbounded
right-derived universal property. -/
theorem rightDerivedPrecomposeEquivalence_isRightDerivedFunctor
    [RH.IsRightDerivedFunctor α (HomologicalComplex.quasiIso A (.up ℤ))] :
    (E.functor.mapDerivedCategory ⋙ RH).IsRightDerivedFunctor
      (rightDerivedPrecomposeEquivalenceUnit E H RH α)
      (HomologicalComplex.quasiIso A (.up ℤ)) := by
  let W := HomologicalComplex.quasiIso A (.up ℤ)
  let Φ : LocalizerMorphism W W :=
    { functor := E.functor.mapHomologicalComplex (.up ℤ)
      map := fun _ _ f hf => by
        letI : QuasiIso f := hf
        exact inferInstanceAs (QuasiIso ((E.functor.mapHomologicalComplex (.up ℤ)).map f)) }
  letI : Φ.functor.IsEquivalence :=
    inferInstanceAs ((E.mapHomologicalComplex (.up ℤ)).functor.IsEquivalence)
  letI : E.functor.mapDerivedCategory.IsEquivalence :=
    inferInstanceAs (E.mapDerivedCategory.functor.IsEquivalence)
  letI : CatCommSq Φ.functor DerivedCategory.Q DerivedCategory.Q E.functor.mapDerivedCategory :=
    ⟨E.functor.mapDerivedCategoryFactors.symm⟩
  letI : Φ.IsLocalizedEquivalence := LocalizerMorphism.IsLocalizedEquivalence.mk' Φ
    DerivedCategory.Q DerivedCategory.Q E.functor.mapDerivedCategory
  exact (Φ.isRightDerivedFunctor_iff_precomp DerivedCategory.Q DerivedCategory.Q
    E.functor.mapDerivedCategory E.functor.mapDerivedCategoryFactors.symm
    (rightDerivedPrecomposeEquivalenceUnit E H RH α) α (Iso.refl _) (Iso.refl _)
    (by
      ext K
      simp only [rightDerivedPrecomposeEquivalenceUnit, NatTrans.comp_app,
        Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.refl_inv,
        Iso.refl_hom, NatTrans.id_app, Functor.associator_inv_app,
        Functor.associator_hom_app, Category.id_comp, Category.comp_id]
      change _ = 𝟙 _ ≫ α.app ((E.functor.mapHomologicalComplex (.up ℤ)).obj K) ≫
        RH.map (E.functor.mapDerivedCategoryFactors.inv.app K) ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id])).mp inferInstance

end ToricPower

end
