module

public import ToricPower.Cohomology.SheafLongExactSequence

/-! Exactness after an arbitrary coefficient functor, with every short-complex
projection normalized before specializing to a concrete site. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Sheaf

namespace ToricPower.SheafCohomology

universe w v u u' v'
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
  {D : Type u'} [Category.{v'} D] [Limits.HasZeroMorphisms D]
  (F : D ⥤ Sheaf J AddCommGrpCat.{v}) [F.PreservesZeroMorphisms]
  {S : ShortComplex D} (hS : (S.map F).ShortExact)

/-- The connecting morphism, on the explicit images of the coefficient objects. -/
def connectingMap (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    H (F.obj S.X₃) n₀ →+ H (F.obj S.X₁) n₁ :=
  H.δ hS n₀ n₁ h

/-- Exactness immediately before the connecting map. -/
theorem exact_map_connecting (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (H.map (F.map S.g) n₀) (connectingMap F hS n₀ n₁ h) := by
  simpa only [connectingMap, ShortComplex.map_X₁, ShortComplex.map_X₂,
    ShortComplex.map_X₃, ShortComplex.map_g] using H.exact_map_δ hS n₀ n₁ h

/-- Exactness immediately after the connecting map. -/
theorem exact_connecting_map (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (connectingMap F hS n₀ n₁ h) (H.map (F.map S.f) n₁) := by
  simpa only [connectingMap, ShortComplex.map_X₁, ShortComplex.map_X₂,
    ShortComplex.map_X₃, ShortComplex.map_f] using H.exact_δ_map hS n₀ n₁ h

/-- The same connecting map, with the canonical cohomology-functor
objects supplying both additive-group structures. -/
def functorConnectingMap (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ((F ⋙ functorH J n₀).obj S.X₃) →+ ((F ⋙ functorH J n₁).obj S.X₁) :=
  (show (F ⋙ functorH J n₀).obj S.X₃ ⟶ (F ⋙ functorH J n₁).obj S.X₁ from
    AddCommGrpCat.ofHom (connectingMap F hS n₀ n₁ h)).hom

/-- Exactness before the connecting map in canonical functor coordinates. -/
theorem exact_functor_map_connecting (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (((F ⋙ functorH J n₀).map S.g).hom)
      (functorConnectingMap F hS n₀ n₁ h) := by
  simpa only [functorConnectingMap, CategoryTheory.Functor.comp_obj,
    CategoryTheory.Functor.comp_map, functorH, AddCommGrpCat.hom_ofHom] using
    exact_map_connecting F hS n₀ n₁ h

/-- Exactness after the connecting map in canonical functor coordinates. -/
theorem exact_functor_connecting_map (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (functorConnectingMap F hS n₀ n₁ h)
      (((F ⋙ functorH J n₁).map S.f).hom) := by
  simpa only [functorConnectingMap, CategoryTheory.Functor.comp_obj,
    CategoryTheory.Functor.comp_map, functorH, AddCommGrpCat.hom_ofHom] using
    exact_connecting_map F hS n₀ n₁ h

end ToricPower.SheafCohomology
