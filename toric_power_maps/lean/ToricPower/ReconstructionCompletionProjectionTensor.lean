module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
# Tensor compatibility of the actual affine-unit projection

The projection formula is compatible with the full tensor evaluation,
including the original associator and the original adjunction unit.
This is the map-level identity needed when an inverse-twist section is
evaluated before passing to sections on an overlap.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal

namespace ToricPower

universe u v u' v'

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]

/-- The right-unit action of a lax monoidal functor is associative with
its tensor map. -/
@[reassoc]
theorem reconstruction_lax_unitAction (G : D ⥤ C) [G.LaxMonoidal] (P R : D) :
    G.obj P ◁ (μ G R (𝟙_ D) ≫ G.map (ρ_ R).hom) ≫ μ G P R =
      (α_ (G.obj P) (G.obj R) (G.obj (𝟙_ D))).inv ≫
        μ G P R ▷ G.obj (𝟙_ D) ≫ μ G (P ⊗ R) (𝟙_ D) ≫
          G.map (ρ_ (P ⊗ R)).hom := by
  rw [whiskerLeft_comp, Category.assoc, μ_natural_right]
  have unit : P ◁ (ρ_ R).hom = (α_ P R (𝟙_ D)).inv ≫ (ρ_ (P ⊗ R)).hom := by
    monoidal
  rw [unit, G.map_comp, ← Category.assoc _ _ (G.map (ρ_ (P ⊗ R)).hom),
    ← Category.assoc _ _ (G.map (ρ_ (P ⊗ R)).hom),
    Functor.LaxMonoidal.associativity_inv]
  simp only [Category.assoc]

variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
  [F.Monoidal] [G.LaxMonoidal] [adj.IsMonoidal]

/-- The original adjunction unit preserves the actual tensorator. -/
theorem reconstruction_adjunction_unit_tensor (P R : C) :
    adj.unit.app (P ⊗ R) =
      (adj.unit.app P ⊗ₘ adj.unit.app R) ≫ μ G (F.obj P) (F.obj R) ≫
        G.map (μ F P R) := by
  have actual := congrArg (fun a => a ≫ G.map (μ F P R))
    (adj.unit_app_tensor_comp_map_δ P R)
  simpa only [Category.assoc, ← G.map_comp, δ_μ, G.map_id,
    Functor.comp_obj, Functor.id_obj, Category.comp_id] using actual

/-- Normalizing a unit-source adjunct retains the original right-adjoint
section exactly. -/
theorem reconstruction_normalizedUnitAdjunct (T : D) (t : 𝟙_ C ⟶ G.obj T) :
    ε G ≫ G.map (ε F ≫ (adj.homEquiv (𝟙_ C) T).symm t) = t := by
  rw [← adj.unit_app_unit_comp_map_η, G.map_comp]
  simp only [Category.assoc, η_ε_map_assoc]
  exact (adj.homEquiv (𝟙_ C) T).apply_symm_apply t

/-- Tensoring an original right-adjoint section and then using its
actual tensor map is the normalized pullback adjunct. -/
@[reassoc]
theorem reconstruction_unitTensorPushAdjunct (P : C) (T : D)
    (t : 𝟙_ C ⟶ G.obj T) :
    (ρ_ P).inv ≫ P ◁ t ≫ adj.unit.app P ▷ G.obj T ≫ μ G (F.obj P) T =
      adj.homEquiv P (F.obj P ⊗ T)
        ((ρ_ (F.obj P)).inv ≫ (F.obj P) ◁
          (ε F ≫ (adj.homEquiv (𝟙_ C) T).symm t)) := by
  let a := ε F ≫ (adj.homEquiv (𝟙_ C) T).symm t
  have normalized : ε G ≫ G.map a = t := reconstruction_normalizedUnitAdjunct adj T t
  rw [← tensorHom_def'_assoc]
  conv_lhs => rw [← normalized]
  rw [← tensorHom_comp_whiskerLeft_assoc]
  change (ρ_ P).inv ≫ (adj.unit.app P ⊗ₘ ε G) ≫
    G.obj (F.obj P) ◁ G.map a ≫ μ G (F.obj P) T = _
  rw [μ_natural_right]
  rw [tensorHom_ε_comp_μ_assoc G, rightUnitor_naturality_assoc]
  simp only [Iso.inv_hom_id_assoc]
  rw [Adjunction.homEquiv_apply, G.map_comp]

/-- The canonical projection against the right adjoint of the unit. -/
def reconstructionUnitProjection (P : C) :
    P ⊗ G.obj (𝟙_ D) ⟶ G.obj (F.obj P) :=
  adj.unit.app P ▷ G.obj (𝟙_ D) ≫ μ G (F.obj P) (𝟙_ D) ≫
    G.map (ρ_ (F.obj P)).hom

/-- The projection of an evaluated tensor is the original tensor of
the projected coefficient and the original pullback unit. -/
theorem reconstructionUnitProjection_tensor (P R : C) :
    (α_ P R (G.obj (𝟙_ D))).inv ≫ reconstructionUnitProjection adj (P ⊗ R) =
      P ◁ reconstructionUnitProjection adj R ≫
        adj.unit.app P ▷ G.obj (F.obj R) ≫
          μ G (F.obj P) (F.obj R) ≫ G.map (μ F P R) := by
  unfold reconstructionUnitProjection
  rw [reconstruction_adjunction_unit_tensor,
    comp_whiskerRight, comp_whiskerRight]
  simp only [Category.assoc]
  rw [μ_natural_left_assoc, ← G.map_comp,
    rightUnitor_naturality, G.map_comp]
  have association := associator_inv_naturality
    (adj.unit.app P) (adj.unit.app R) (𝟙 (G.obj (𝟙_ D)))
  simp only [tensorHom_id, Functor.comp_obj, Functor.id_obj] at association
  rw [← reassoc_of% association]
  rw [← reconstruction_lax_unitAction_assoc]
  rw [tensorHom_comp_whiskerLeft_assoc, tensorHom_def']
  simp only [whiskerLeft_comp, Category.assoc]

/-- The precise adjunct of evaluation of an inverse-twist unit section. -/
theorem reconstructionUnitProjection_evaluation (P R : C)
    (x : 𝟙_ C ⟶ R ⊗ G.obj (𝟙_ D)) :
    (ρ_ P).inv ≫ P ◁ x ≫ (α_ P R (G.obj (𝟙_ D))).inv ≫
        reconstructionUnitProjection adj (P ⊗ R) =
      adj.homEquiv P (F.obj (P ⊗ R))
        ((ρ_ (F.obj P)).inv ≫ (F.obj P) ◁
          (ε F ≫ (adj.homEquiv (𝟙_ C) (F.obj R)).symm
            (x ≫ reconstructionUnitProjection adj R)) ≫ μ F P R) := by
  rw [reconstructionUnitProjection_tensor, ← whiskerLeft_comp_assoc,
    reconstruction_unitTensorPushAdjunct_assoc,
    ← adj.homEquiv_naturality_right]
  simp only [Category.assoc]

end ToricPower

end
