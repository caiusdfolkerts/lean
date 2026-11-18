module

public import ToricPower.SchemePullbackSectionCoherence

/-! # Tensor insertion on an actual affine overlap

The specified successive pullback tensor maps become the tensor map of
ordinary restriction along the composite, with the original target map.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory MonoidalCategory
open AlgebraicGeometry.Scheme.Modules

namespace ToricPower

universe u

variable {X Y Z : Scheme.{u}} (j : X ⟶ Y) (f : Y ⟶ Z)
  [IsOpenImmersion j] [IsOpenImmersion f]

/-- Two ordinary restriction comparisons equal the canonical pullback
composition followed by the single ordinary restriction comparison. -/
@[reassoc]
theorem reconstruction_pullback_restriction_comp (M : Z.Modules) :
    (restrictFunctorIsoPullback j).inv.app ((pullback f).obj M) ≫
        (restrictFunctor j).map ((restrictFunctorIsoPullback f).inv.app M) ≫
        (restrictFunctorComp j f).inv.app M =
      (pullbackComp j f).hom.app M ≫
        (restrictFunctorIsoPullback (j ≫ f)).inv.app M := by
  rw [← (restrictFunctorIsoPullback j).inv.naturality_assoc,
    ← pullback_restriction_comp j f M]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    Functor.map_id, Category.id_comp]
  erw [(pullback j).map_id]
  simp only [Category.id_comp]

/-- The actual tensor insertions compose through the actual pullback
composition map, in the direction used by tensor evaluation. -/
@[reassoc]
theorem reconstruction_pullback_tensor_comp (M N : Z.Modules) :
    (pullbackTensorIsoOfOpenImmersion j ((pullback f).obj M) ((pullback f).obj N)).inv ≫
        (pullback j).map (pullbackTensorIsoOfOpenImmersion f M N).inv ≫
        (pullbackComp j f).hom.app (M ⊗ N) =
      ((pullbackComp j f).hom.app M ⊗ₘ (pullbackComp j f).hom.app N) ≫
        (pullbackTensorIsoOfOpenImmersion (j ≫ f) M N).inv := by
  apply (cancel_mono (pullbackTensorIsoOfOpenImmersion (j ≫ f) M N).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    pullbackTensorIsoOfOpenImmersion_hom]
  rw [TauCeti.AlgebraicGeometry.pullbackComp_hom_app_comp_δ]
  rw [← pullbackTensorIsoOfOpenImmersion_hom,
    ← pullbackTensorIsoOfOpenImmersion_hom]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id, Functor.map_id,
    Category.id_comp, Iso.inv_hom_id_assoc]
  erw [(pullback j).map_id]
  simp only [Category.id_comp, Iso.inv_hom_id_assoc,
    ← pullbackTensorIsoOfOpenImmersion_hom]
  simp only [Iso.inv_hom_id, Category.comp_id]

/-- Tensor insertion followed by the canonical ordinary-restriction
comparison is the tensor of the two comparisons. -/
@[reassoc]
theorem reconstruction_pullback_tensor_restriction (M N : Y.Modules) :
    (pullbackTensorIsoOfOpenImmersion j M N).inv ≫
        (restrictFunctorIsoPullback j).inv.app (M ⊗ N) =
      ((restrictFunctorIsoPullback j).inv.app M ⊗ₘ
        (restrictFunctorIsoPullback j).inv.app N) ≫
        Functor.LaxMonoidal.μ (restrictFunctor j) M N := by
  rw [restrictFunctorIsoPullback_inv_tensor,
    ← pullbackTensorIsoOfOpenImmersion_hom]
  simp only [Iso.inv_hom_id_assoc]

/-- The complete successive affine tensor evaluation, including an
arbitrary original target map, in literal ordinary overlap restriction. -/
@[reassoc]
theorem reconstruction_pullback_tensor_comp_map (M N P : Z.Modules)
    (β : M ⊗ N ⟶ P) :
    (pullbackTensorIsoOfOpenImmersion j ((pullback f).obj M) ((pullback f).obj N)).inv ≫
        (pullback j).map
          ((pullbackTensorIsoOfOpenImmersion f M N).inv ≫ (pullback f).map β) ≫
        (restrictFunctorIsoPullback j).inv.app ((pullback f).obj P) ≫
        (restrictFunctor j).map ((restrictFunctorIsoPullback f).inv.app P) ≫
        (restrictFunctorComp j f).inv.app P =
      (((pullbackComp j f).hom.app M ≫
          (restrictFunctorIsoPullback (j ≫ f)).inv.app M) ⊗ₘ
        ((pullbackComp j f).hom.app N ≫
          (restrictFunctorIsoPullback (j ≫ f)).inv.app N)) ≫
        Functor.LaxMonoidal.μ (restrictFunctor (j ≫ f)) M N ≫
        (restrictFunctor (j ≫ f)).map β := by
  rw [reconstruction_pullback_restriction_comp]
  simp only [Functor.map_comp, Category.assoc]
  have natural := (pullbackComp j f).hom.naturality β
  simp only [Functor.comp_map] at natural
  rw [reassoc_of% natural,
    (restrictFunctorIsoPullback (j ≫ f)).inv.naturality]
  rw [reconstruction_pullback_tensor_comp_assoc,
    reconstruction_pullback_tensor_restriction_assoc]
  simp only [tensorHom_comp_tensorHom_assoc]

end ToricPower

end
