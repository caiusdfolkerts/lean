module
public import ToricPower.Cohomology.SheafFunctorExact

/-! Naturality of the actual connecting map, before specialization to schemes. -/

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

/-- A morphism of short exact coefficient sequences commutes with the
canonical connecting map in every degree. -/
theorem functorConnectingMap_naturality {S₁ S₂ : ShortComplex D}
    (h₁ : (S₁.map F).ShortExact) (h₂ : (S₂.map F).ShortExact) (φ : S₁ ⟶ S₂)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (x : (F ⋙ functorH J n₀).obj S₁.X₃) :
    ((F ⋙ functorH J n₁).map φ.τ₁).hom (functorConnectingMap F h₁ n₀ n₁ h x) =
      functorConnectingMap F h₂ n₀ n₁ h (((F ⋙ functorH J n₀).map φ.τ₃).hom x) := by
  simpa only [functorConnectingMap, connectingMap, CategoryTheory.Functor.comp_obj,
    CategoryTheory.Functor.comp_map, functorH, AddCommGrpCat.hom_ofHom,
    CategoryTheory.Functor.mapShortComplex_map_τ₁,
    CategoryTheory.Functor.mapShortComplex_map_τ₃,
    ShortComplex.map_X₁, ShortComplex.map_X₃] using
    (H.δ_naturality.{w, v, v, u} n₀ n₁ h h₁ h₂ (F.mapShortComplex.map φ) x).symm

end ToricPower.SheafCohomology
