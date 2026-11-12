module

public import ToricPower.SchemeExternalSectionDiagram
public import ToricPower.SchemeRestrictionTensor
public import ToricPower.CovariantRepresentableEvaluation

/-!
# The exterior diagram on an actual open chart

The original open-pullback tensor comparison and the two specified
pullback squares identify every exterior coefficient, naturally in
all source arrows. The comparison is constructed from the canonical
maps, rather than by choosing new frames for the target complex.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory MonoidalCategory

namespace ToricPower

universe u
variable {X Y U V W : Scheme.{u}}
  (p q : Y ⟶ X) (j : W ⟶ Y) [IsOpenImmersion j]
  (a : U ⟶ X) (b : V ⟶ X) (f : W ⟶ U) (g : W ⟶ V)
  (first : Scheme.Modules.pullback p ⋙ Scheme.Modules.pullback j ≅
    Scheme.Modules.pullback a ⋙ Scheme.Modules.pullback f)
  (second : Scheme.Modules.pullback q ⋙ Scheme.Modules.pullback j ≅
    Scheme.Modules.pullback b ⋙ Scheme.Modules.pullback g)
  {C : Type u} [Category.{u} C] (Q R : C ⥤ X.Modules)

/-- The full coefficient diagram comparison on the literal open chart. -/
def schemeExteriorChartDiagramIso :
    Cellular.covariantTensorDiagram
        (Q ⋙ Scheme.Modules.pullback p) (R ⋙ Scheme.Modules.pullback q) ⋙
          Scheme.Modules.pullback j ≅
      schemeExteriorDiagram f g
        (Q ⋙ Scheme.Modules.pullback a) (R ⋙ Scheme.Modules.pullback b) :=
  NatIso.ofComponents (fun c =>
    Scheme.Modules.pullbackTensorIsoOfOpenImmersion j
      ((Scheme.Modules.pullback p).obj (Q.obj c))
      ((Scheme.Modules.pullback q).obj (R.obj c)) ≪≫
        tensorIso (first.app (Q.obj c)) (second.app (R.obj c))) (by
    intro c d h
    change (Scheme.Modules.pullback j).map
        ((Scheme.Modules.pullback p).map (Q.map h) ⊗ₘ
          (Scheme.Modules.pullback q).map (R.map h)) ≫
        Functor.OplaxMonoidal.δ (Scheme.Modules.pullback j) _ _ ≫
          (first.hom.app (Q.obj d) ⊗ₘ second.hom.app (R.obj d)) =
      Functor.OplaxMonoidal.δ (Scheme.Modules.pullback j) _ _ ≫
        (first.hom.app (Q.obj c) ⊗ₘ second.hom.app (R.obj c)) ≫
          ((Scheme.Modules.pullback f).map ((Scheme.Modules.pullback a).map (Q.map h)) ⊗ₘ
            (Scheme.Modules.pullback g).map ((Scheme.Modules.pullback b).map (R.map h)))
    rw [← Functor.OplaxMonoidal.δ_natural_assoc, tensorHom_comp_tensorHom,
      tensorHom_comp_tensorHom]
    congr 1
    exact congrArg₂ (fun l r => l ⊗ₘ r)
      (first.hom.naturality (Q.map h)) (second.hom.naturality (R.map h)))

end ToricPower

end
