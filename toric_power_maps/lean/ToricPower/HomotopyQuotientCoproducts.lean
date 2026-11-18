module

public import ToricPower.HomotopyCategoryCoproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# The quotient functor preserves actual coproducts

The degreewise complex coproduct and the already verified homotopy
coproduct are represented by exactly the same cocone maps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace ToricPower.CoproductComplex

universe u v w t
variable {A : Type u} [Category.{v} A] [Preadditive A] [HasCoproducts.{w} A]
  {J : Type t} {shape : ComplexShape J} {I : Type w}

def cofan (K : I → HomologicalComplex A shape) : Cofan K :=
  Cofan.mk (obj K) (ι K)

def isColimit (K : I → HomologicalComplex A shape) : IsColimit (cofan K) :=
  Cofan.IsColimit.mk _ (fun s => desc K s.inj)
    (fun s i => ι_desc K s.inj i)
    (fun s m same => hom_ext K (fun i => (same i).trans (ι_desc K s.inj i).symm))

theorem quotient_preservesCoproduct (K : I → HomologicalComplex A shape) :
    PreservesColimit (Discrete.functor K) (HomotopyCategory.quotient A shape) := by
  apply preservesColimit_of_preserves_colimit_cocone (isColimit K)
  exact (isColimitMapCoconeCofanMkEquiv (HomotopyCategory.quotient A shape) K (ι K)).symm
    (homotopyIsColimit K)

end ToricPower.CoproductComplex

end
