module

public import ToricPower.CovariantRepresentableEvaluation

/-!
# Source naturality of actual represented evaluation

Precomposing the genuine incidence generator by `c ⟶ d` and acting
on the inverse label by that same arrow give the same evaluation map.
This is the source-variable compatibility needed for a natural
representable comparison, before taking cellular cochains or homology.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace ToricPower.Cellular

universe u v

variable (k : Type u) [Field k] {C : Type u} [Category.{u} C]

/-- Literal precomposition of free representable incidence modules. -/
def representablePrecompose {c d : C} (f : c ⟶ d) :
    representable k d ⟶ representable k c :=
  fromValue k (representable k c) d (ModuleCat.freeMk f)

@[simp]
theorem representablePrecompose_freeMk {c d e : C} (f : c ⟶ d) (g : d ⟶ e) :
    (representablePrecompose k f).app e (ModuleCat.freeMk g) =
      ModuleCat.freeMk (f ≫ g) := by
  rw [representablePrecompose, fromValue_app_freeMk, representable_map_freeMk]

/-- The genuine contravariant functor of all free representables. -/
def representableFunctor : Cᵒᵖ ⥤ (C ⥤ ModuleCat.{u} k) where
  obj c := representable k c.unop
  map f := representablePrecompose k f.unop
  map_id c := by
    apply NatTrans.ext
    funext d
    apply ModuleCat.free_hom_ext
    intro f
    change (representablePrecompose k (𝟙 c.unop)).app d
      (ModuleCat.freeMk (f : c.unop ⟶ d)) = ModuleCat.freeMk f
    rw [representablePrecompose_freeMk, Category.id_comp]
  map_comp f g := by
    apply NatTrans.ext
    funext e
    apply ModuleCat.free_hom_ext
    intro h
    change (representablePrecompose k (g.unop ≫ f.unop)).app e
        (ModuleCat.freeMk (h : _ ⟶ e)) =
      (representablePrecompose k g.unop).app e
        ((representablePrecompose k f.unop).app e (ModuleCat.freeMk h))
    rw [representablePrecompose_freeMk, representablePrecompose_freeMk]
    change ModuleCat.freeMk ((g.unop ≫ f.unop) ≫ h) =
      (representablePrecompose k g.unop).app e (ModuleCat.freeMk (f.unop ≫ h))
    rw [representablePrecompose_freeMk, Category.assoc]

variable {B : Type v} [Category.{u} B] [Preadditive B] [Linear k B]
  [MonoidalCategory B] [MonoidalPreadditive B] [MonoidalLinear k B]
  [HasCoproducts.{u} B]
  (Q R : C ⥤ B)
  [∀ c, PreservesColimitsOfSize.{u,u} ((tensoringRight B).obj (R.obj c))]

/-- The actual source-incidence square: precomposition in the free
representable agrees with the original map of the inverse label. -/
theorem representedTensorEvaluation_source {c d : C} (f : c ⟶ d) (e : C) :
    (covariantCopowerMap k Q (representablePrecompose k f)).app e ▷ R.obj c ≫
        representedTensorEvaluation k Q R c e =
      vectorCopower k (Q.obj e) ((representable k d).obj e) ◁ R.map f ≫
        representedTensorEvaluation k Q R d e := by
  apply map_vectorCopower_free_hom_ext k ((tensoringRight B).obj (R.obj c))
    (Q.obj e) (d ⟶ e)
  intro g
  change vectorCopowerInclusion k (Q.obj e) ((representable k d).obj e)
      (ModuleCat.freeMk g) ▷ R.obj c ≫ _ =
    vectorCopowerInclusion k (Q.obj e) ((representable k d).obj e)
      (ModuleCat.freeMk g) ▷ R.obj c ≫ _
  rw [← Category.assoc, ← comp_whiskerRight]
  change
    (vectorCopowerInclusion k (Q.obj e) ((representable k d).obj e) (ModuleCat.freeMk g) ≫
      (vectorCopowerFunctor k (Q.obj e)).map ((representablePrecompose k f).app e)) ▷
        R.obj c ≫ representedTensorEvaluation k Q R c e = _
  rw [vectorCopowerInclusion_map, representablePrecompose_freeMk,
    representedTensorEvaluation_generator]
  rw [← Category.assoc, ← whisker_exchange, Category.assoc,
    representedTensorEvaluation_generator, ← whiskerLeft_comp, ← Functor.map_comp]

end ToricPower.Cellular

end
