module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.EssentialImage

/-! # Coproduct preservation detected through an essentially surjective factor

A fully faithful functor reflects the colimit of every actual cofan.
If its composite with an essentially surjective presentation preserves
coproducts, both the presentation and the functor preserve them. The
argument is applied only to discrete diagrams, whose objects lift
independently; no lifting of arbitrary diagram arrows is assumed.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe u v u' v' u'' v'' w
variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C]
  {D : Type u'} [Category.{v'} D] {E : Type u''} [Category.{v''} E]
  (Q : C ⥤ D) [Q.EssSurj] (B : D ⥤ E) [B.Full] [B.Faithful]

theorem preservesCoproducts_of_essentiallySurjective_factor (I : Type w)
    [PreservesColimitsOfShape (Discrete I) (Q ⋙ B)] :
    PreservesColimitsOfShape (Discrete I) B := by
  letI : PreservesColimitsOfShape (Discrete I) Q :=
    preservesColimitsOfShape_of_reflects_of_preserves Q B
  suffices all : ∀ family : I → D, PreservesColimit (Discrete.functor family) B from
    by
      letI := all
      exact preservesColimitsOfShape_of_discrete B
  intro family
  let K := Discrete.functor (fun i : I => Q.objPreimage (family i))
  letI : PreservesColimit (K ⋙ Q) B := by
    apply preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves Q (colimit.isColimit K))
    exact isColimitOfPreserves (Q ⋙ B) (colimit.isColimit K)
  let e : K ⋙ Q ≅ Discrete.functor family :=
    Discrete.natIso (fun i => Q.objObjPreimageIso (family i.as))
  exact preservesColimit_of_iso_diagram B e

end ToricPower
end
