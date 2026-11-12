module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
public import ToricPower.Cohomology.FreeYoneda

/-! Naturality of Ext adjunction and evaluation of the cohomology
bifunctor, separated from concrete equivalences of sites. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
namespace ToricPower
universe w v₁ v₂ u₁ u₂

/-- An exact adjunction gives a natural isomorphism of covariant Ext
functors with fixed first argument. -/
def extRightFunctorIso {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    [HasExt.{w} C] [HasExt.{w} D] {F : C ⥤ D} {G : D ⥤ C}
    [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (adj : F ⊣ G) (X : C) (n : ℕ) :
    (extFunctor n).obj (op (F.obj X)) ≅ G ⋙ (extFunctor n).obj (op X) :=
  NatIso.ofComponents (fun Y => (adj.extEquiv (X := X) (Y := Y) (n := n)).toAddCommGrpIso)
    (by
      intro Y Z f
      ext x
      exact adj.extEquiv_naturality_right₀ x f)

/-- Evaluating a flipped composite bifunctor is evaluation at its chosen
first argument. This is proved with both functors abstract. -/
def flipCompEvaluationIso {A B C D : Type*} [Category A] [Category B]
    [Category C] [Category D] (F : A ⥤ B) (G : B ⥤ C ⥤ D) (a : A) :
    (F ⋙ G).flip ⋙ (evaluation A D).obj a ≅ G.obj (F.obj a) :=
  NatIso.ofComponents (fun _ => Iso.refl _)

/-- Cohomology on an object is the covariant Ext functor from its free
abelian representable sheaf, naturally in the coefficient sheaf. -/
def cohomologyEvaluationIsoExt {C : Type u₁} [Category.{v₁} C]
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{v₁}]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{v₁})] (n : ℕ) (U : C) :
    Sheaf.cohomologyPresheafFunctor J n ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (op U) ≅
    (extFunctor n).obj (op ((TauCeti.CategoryTheory.freeYonedaSheafFunctor J).obj U)) :=
  Functor.isoWhiskerRight
      (eqToIso (TauCeti.CategoryTheory.cohomologyPresheafFunctor_eq J n))
      ((evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (op U)) ≪≫
    flipCompEvaluationIso (TauCeti.CategoryTheory.freeYonedaSheafFunctor J).op
      (extFunctor n) (op U)

end ToricPower
