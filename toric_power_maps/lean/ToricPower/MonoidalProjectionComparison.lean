module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
# The canonical projection comparison of a monoidal adjunction

The comparison is defined from the actual adjunction unit and the tensor
map of its right adjoint. Its component at the monoidal unit is always
invertible when the left adjoint preserves that unit. This supplies the
rank-one calculation in the affine projection formula.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace ToricPower

universe u v w z

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type w} [Category.{z} D] [MonoidalCategory D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [G.LaxMonoidal]

/-- The canonical map `M ⊗ G(N) → G(F(M) ⊗ N)`, natural in `M`. -/
def monoidalProjectionComparison (N : D) :
    tensorRight (G.obj N) ⟶ F ⋙ tensorRight N ⋙ G where
  app M := adj.unit.app M ▷ G.obj N ≫ μ G (F.obj M) N
  naturality {M M'} f := by
    change f ▷ G.obj N ≫ adj.unit.app M' ▷ G.obj N ≫ μ G (F.obj M') N =
      (adj.unit.app M ▷ G.obj N ≫ μ G (F.obj M) N) ≫ G.map (F.map f ▷ N)
    rw [← comp_whiskerRight_assoc, ← adj.unit_naturality f, comp_whiskerRight_assoc,
      μ_natural_left]
    simp only [Category.assoc]

/-- It is also natural in the coefficient from the source category. -/
theorem monoidalProjectionComparison_naturality_right {N N' : D} (g : N ⟶ N') (M : C) :
    M ◁ G.map g ≫ (monoidalProjectionComparison adj N').app M =
      (monoidalProjectionComparison adj N).app M ≫ G.map (F.obj M ◁ g) := by
  dsimp only [monoidalProjectionComparison]
  rw [whisker_exchange_assoc]
  simp only [Functor.comp_obj]
  rw [μ_natural_right G (F.obj M) g]
  simp only [Category.assoc]

variable [F.OplaxMonoidal] [adj.IsMonoidal]

/-- The actual unit component becomes the left unitor after the canonical
pullback-unit identification. -/
theorem monoidalProjectionComparison_unit (N : D) :
    (monoidalProjectionComparison adj N).app (𝟙_ C) ≫
      G.map (η F ▷ N) ≫ G.map (λ_ N).hom = (λ_ (G.obj N)).hom := by
  dsimp only [monoidalProjectionComparison]
  simp only [Category.assoc]
  rw [← μ_natural_left_assoc G (η F) N, ← comp_whiskerRight_assoc,
    adj.unit_app_unit_comp_map_η]
  exact (Functor.LaxMonoidal.left_unitality G N).symm

/-- No tensor comparison for the left adjoint is assumed invertible: only
its actual unit comparison is needed for this component. -/
theorem monoidalProjectionComparison_unit_isIso [IsIso (η F)] (N : D) :
    IsIso ((monoidalProjectionComparison adj N).app (𝟙_ C)) := by
  have h : IsIso ((monoidalProjectionComparison adj N).app (𝟙_ C) ≫
      G.map (η F ▷ N) ≫ G.map (λ_ N).hom) := by
    rw [monoidalProjectionComparison_unit]
    infer_instance
  exact (isIso_comp_right_iff _ (G.map (η F ▷ N) ≫ G.map (λ_ N).hom)).mp h

end ToricPower

end
