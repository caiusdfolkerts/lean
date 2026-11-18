module

public import ToricPower.SchemeAdjunctSquareSections
public import ToricPower.SchemePullbackTensorCoherence
public import ToricPower.SchemeRestrictionTensor

/-!
# The local adjunct of genuine tensor evaluation

An arbitrary local section of the first factor and the normalized
adjunct of the second factor give their actual tensor on the overlap.
The statement keeps the base-change mate and all unit comparisons.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory MonoidalCategory

namespace ToricPower

section Monoidal

universe u v u' v'

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]

/-- A lax monoidal functor carries tensor action on any unit-source
map to the tensor of that map and the normalized image section. -/
@[reassoc]
theorem reconstruction_lax_unitSource_tensorAction
    (F : C ⥤ D) [F.LaxMonoidal] (P R : C)
    (a : 𝟙_ D ⟶ F.obj P) (b : 𝟙_ C ⟶ R) :
    a ≫ F.map ((ρ_ P).inv ≫ P ◁ b) =
      (λ_ (𝟙_ D)).inv ≫
        (a ⊗ₘ (Functor.LaxMonoidal.ε F ≫ F.map b)) ≫
        Functor.LaxMonoidal.μ F P R := by
  rw [Functor.map_comp]
  symm
  rw [← tensorHom_comp_whiskerLeft_assoc,
    Functor.LaxMonoidal.μ_natural_right,
    Functor.LaxMonoidal.tensorHom_ε_comp_μ_assoc,
    rightUnitor_naturality_assoc, ← unitors_equal, Iso.inv_hom_id_assoc]

end Monoidal

section SchemeSquare

universe u

variable {X X' Y Y' : Scheme.{u}}
  (f : X ⟶ Y) (g : X' ⟶ Y') (j : X' ⟶ X) (k : Y' ⟶ Y)
  [IsOpenImmersion f] [IsOpenImmersion j] [IsOpenImmersion k]

/-- The actual normalized local adjunct of tensor evaluation is the
tensor of its two pulled local sections, followed by the original map.
No inverse of either section is used. -/
@[reassoc]
theorem normalizedSquareTensorAdjunct_map
    (square : j ≫ f = g ≫ k) (Q R J : Y.Modules)
    (a : 𝟙_ Y'.Modules ⟶ (Scheme.Modules.pullback k).obj Q)
    (t : 𝟙_ X.Modules ⟶ (Scheme.Modules.pullback f).obj R)
    (β : Q ⊗ R ⟶ J) :
    (Scheme.Modules.pullbackObjUnitIso g).inv ≫
        ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).symm
          (a ≫ (Scheme.Modules.pullback k).map
            ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
              ((ρ_ ((Scheme.Modules.pullback f).obj Q)).inv ≫
                ((Scheme.Modules.pullback f).obj Q) ◁ t ≫
                (Scheme.Modules.pullbackTensorIsoOfOpenImmersion f Q R).inv ≫
                (Scheme.Modules.pullback f).map β)) ≫
            (Scheme.Modules.restrictFunctorIsoPullback k).inv.app
              ((Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj J)) ≫
            pushforwardRestrictionMap f g j k square ((Scheme.Modules.pullback f).obj J)) =
      (λ_ (𝟙_ X'.Modules)).inv ≫
        (((Scheme.Modules.pullbackObjUnitIso g).inv ≫
            (Scheme.Modules.pullback g).map a ≫
            (pullbackSquareIso f g j k square).hom.app Q) ⊗ₘ
          ((Scheme.Modules.pullbackObjUnitIso j).inv ≫
            (Scheme.Modules.pullback j).map t)) ≫
        (Scheme.Modules.pullbackTensorIsoOfOpenImmersion j
          ((Scheme.Modules.pullback f).obj Q) ((Scheme.Modules.pullback f).obj R)).inv ≫
        (Scheme.Modules.pullback j).map
          (Scheme.Modules.pullbackTensorIsoOfOpenImmersion f Q R).inv ≫
        (Scheme.Modules.pullback j).map ((Scheme.Modules.pullback f).map β) ≫
        (Scheme.Modules.restrictFunctorIsoPullback j).inv.app
          ((Scheme.Modules.pullback f).obj J) := by
  letI : (Scheme.Modules.pullback j).Monoidal :=
    Functor.Monoidal.ofOplaxMonoidal (Scheme.Modules.pullback j)
  have unit : Functor.LaxMonoidal.ε (Scheme.Modules.pullback j) =
      (Scheme.Modules.pullbackObjUnitIso j).inv := by
    rw [← Functor.Monoidal.inv_η]
    simp only [Scheme.Modules.pullback_η, IsIso.Iso.inv_hom]
  have tensor : Functor.LaxMonoidal.μ (Scheme.Modules.pullback j)
      ((Scheme.Modules.pullback f).obj Q) ((Scheme.Modules.pullback f).obj R) =
      (Scheme.Modules.pullbackTensorIsoOfOpenImmersion j
        ((Scheme.Modules.pullback f).obj Q) ((Scheme.Modules.pullback f).obj R)).inv := by
    rw [← Functor.Monoidal.inv_δ]
    rfl
  have action := reconstruction_lax_unitSource_tensorAction (Scheme.Modules.pullback j)
    ((Scheme.Modules.pullback f).obj Q) ((Scheme.Modules.pullback f).obj R)
    ((Scheme.Modules.pullbackObjUnitIso g).inv ≫
      (Scheme.Modules.pullback g).map a ≫
      (pullbackSquareIso f g j k square).hom.app Q) t
  rw [unit, tensor] at action
  rw [normalizedSquareAdjunct_map]
  rw [← (Scheme.Modules.restrictFunctorIsoPullback j).inv.naturality]
  have finished := congrArg (fun z => z ≫
    (Scheme.Modules.pullback j).map
      (Scheme.Modules.pullbackTensorIsoOfOpenImmersion f Q R).inv ≫
    (Scheme.Modules.pullback j).map ((Scheme.Modules.pullback f).map β) ≫
    (Scheme.Modules.restrictFunctorIsoPullback j).inv.app
      ((Scheme.Modules.pullback f).obj J)) action
  simpa only [Functor.map_comp, Category.assoc] using finished

end SchemeSquare

end ToricPower

end
