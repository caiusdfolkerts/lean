module

public import ToricPower.ReconstructionCompletionSquareTensorAdjunct
public import ToricPower.ReconstructionCompletionPullbackTensorCompose

/-! # The actual normalized tensor evaluation on the displayed overlap

The target is ordinary restriction along the displayed composite of
the overlap inclusion with the second chart. This avoids replacing the
overlap by an equal open or changing the original adjunct.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory MonoidalCategory
open AlgebraicGeometry.Scheme.Modules

namespace ToricPower

universe u

section Composition

variable {X Y Z : Scheme.{u}} (j : X ⟶ Y) (f : Y ⟶ Z)
  [IsOpenImmersion j] [IsOpenImmersion f]

/-- Successive tensor insertions followed directly by composition and
ordinary restriction retain the original target morphism. -/
@[reassoc]
theorem reconstruction_pullback_tensor_comp_direct_map (M N P : Z.Modules)
    (β : M ⊗ N ⟶ P) :
    (pullbackTensorIsoOfOpenImmersion j ((pullback f).obj M) ((pullback f).obj N)).inv ≫
        (pullback j).map
          ((pullbackTensorIsoOfOpenImmersion f M N).inv ≫ (pullback f).map β) ≫
        (pullbackComp j f).hom.app P ≫
        (restrictFunctorIsoPullback (j ≫ f)).inv.app P =
      (((pullbackComp j f).hom.app M ≫
          (restrictFunctorIsoPullback (j ≫ f)).inv.app M) ⊗ₘ
        ((pullbackComp j f).hom.app N ≫
          (restrictFunctorIsoPullback (j ≫ f)).inv.app N)) ≫
        Functor.LaxMonoidal.μ (restrictFunctor (j ≫ f)) M N ≫
        (restrictFunctor (j ≫ f)).map β := by
  have natural := (pullbackComp j f).hom.naturality β
  simp only [Functor.comp_map] at natural
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% natural, (restrictFunctorIsoPullback (j ≫ f)).inv.naturality]
  rw [reconstruction_pullback_tensor_comp_assoc,
    reconstruction_pullback_tensor_restriction_assoc]
  simp only [tensorHom_comp_tensorHom_assoc]

end Composition

section Square

variable {X X' Y Y' : Scheme.{u}}
  (f : X ⟶ Y) (g : X' ⟶ Y') (j : X' ⟶ X) (k : Y' ⟶ Y)
  [IsOpenImmersion f] [IsOpenImmersion j] [IsOpenImmersion k]

/-- The original normalized local adjunct, evaluated on an arbitrary
first section, equals the tensor of the two sections pulled to the
displayed overlap, followed by the original restricted target map. -/
@[reassoc]
theorem normalizedSquareTensorAdjunct_overlap
    (square : j ≫ f = g ≫ k) (Q R J : Y.Modules)
    (a : 𝟙_ Y'.Modules ⟶ (pullback k).obj Q)
    (t : 𝟙_ X.Modules ⟶ (pullback f).obj R)
    (β : Q ⊗ R ⟶ J) :
    (pullbackObjUnitIso g).inv ≫
        ((pullbackPushforwardAdjunction g).homEquiv _ _).symm
          (a ≫ (pullback k).map
            ((pullbackPushforwardAdjunction f).homEquiv _ _
              ((ρ_ ((pullback f).obj Q)).inv ≫ ((pullback f).obj Q) ◁ t ≫
                (pullbackTensorIsoOfOpenImmersion f Q R).inv ≫ (pullback f).map β)) ≫
            (restrictFunctorIsoPullback k).inv.app ((pushforward f).obj ((pullback f).obj J)) ≫
            pushforwardRestrictionMap f g j k square ((pullback f).obj J)) ≫
        (restrictFunctorIsoPullback j).hom.app ((pullback f).obj J) ≫
        (pullbackComp j f).hom.app J ≫
        (restrictFunctorIsoPullback (j ≫ f)).inv.app J =
      (λ_ (𝟙_ X'.Modules)).inv ≫
        (((pullbackObjUnitIso g).inv ≫ (pullback g).map a ≫
            (pullbackComp g k).hom.app Q ≫ (pullbackCongr square.symm).hom.app Q ≫
            (restrictFunctorIsoPullback (j ≫ f)).inv.app Q) ⊗ₘ
          ((pullbackObjUnitIso j).inv ≫ (pullback j).map t ≫
            (pullbackComp j f).hom.app R ≫
            (restrictFunctorIsoPullback (j ≫ f)).inv.app R)) ≫
        Functor.LaxMonoidal.μ (restrictFunctor (j ≫ f)) Q R ≫
        (restrictFunctor (j ≫ f)).map β := by
  rw [normalizedSquareTensorAdjunct_map_assoc]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp_assoc, reconstruction_pullback_tensor_comp_direct_map]
  simp only [tensorHom_comp_tensorHom_assoc, pullbackSquareIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc,
    Iso.inv_hom_id_app_assoc]

end Square

end ToricPower

end
