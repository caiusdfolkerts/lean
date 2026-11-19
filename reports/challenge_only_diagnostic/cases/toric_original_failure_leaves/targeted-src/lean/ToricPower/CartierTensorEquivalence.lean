module

public import ToricPower.CartierTensorProduct

/-!
# The actual tensor equivalence of Cartier module sheaves

Multiplication of rational sections identifies O(D) tensor O(-D) with the
structure sheaf in both orders. These actual isomorphisms give inverse
exact tensor functors on all module sheaves. No coherence, flatness, or
finite-presentation hypothesis is added to a module being tensored.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace ToricPower

universe u v

section TensorInverse

variable {A : Type u} [Category.{v} A] [MonoidalCategory A]

/-- Tensoring successively by two objects whose product is the unit is
the identity, with the actual associator and multiplication isomorphism. -/
def tensorLeftCompIsoId {L M : A} (e : M ⊗ L ≅ 𝟙_ A) :
    tensorLeft L ⋙ tensorLeft M ≅ 𝟭 A :=
  (tensorLeftTensor M L).symm ≪≫
    (tensoringLeft A).mapIso e ≪≫ leftUnitorNatIso A

/-- Two actual inverse tensor isomorphisms produce the actual tensor
equivalence. `Equivalence.mk` supplies the coherent unit normalization. -/
def tensorEquivalenceOfInverse (L M : A)
    (eML : M ⊗ L ≅ 𝟙_ A) (eLM : L ⊗ M ≅ 𝟙_ A) : A ≌ A :=
  CategoryTheory.Equivalence.mk (tensorLeft L) (tensorLeft M)
    (tensorLeftCompIsoId eML).symm (tensorLeftCompIsoId eLM)

@[simp]
theorem tensorEquivalenceOfInverse_functor (L M : A)
    (eML : M ⊗ L ≅ 𝟙_ A) (eLM : L ⊗ M ≅ 𝟙_ A) :
    (tensorEquivalenceOfInverse L M eML eLM).functor = tensorLeft L := rfl

end TensorInverse

section Cartier

open TauCeti.AlgebraicGeometry.Scheme
open TauCeti.AlgebraicGeometry.Scheme.CartierDivisor

variable {X : Scheme.{u}} [IsIntegral X]

/-- The actual tensor product `O(-D) ⊗ O(D)` is the structure sheaf,
by multiplication of rational sections and the normalized zero divisor. -/
def cartierNegTensorIsoUnit (D : CartierDivisor X) :
    (-D).sheaf ⊗ D.sheaf ≅ 𝟙_ X.Modules :=
  tensorSheafIso (-D) D ≪≫
    eqToIso (congrArg (fun E : CartierDivisor X => E.sheaf) (neg_add_cancel D)) ≪≫
      (unitIsoSheafZero X).symm

/-- The actual tensor product `O(D) ⊗ O(-D)` is the structure sheaf. -/
def cartierTensorNegIsoUnit (D : CartierDivisor X) :
    D.sheaf ⊗ (-D).sheaf ≅ 𝟙_ X.Modules :=
  tensorSheafIso D (-D) ≪≫
    eqToIso (congrArg (fun E : CartierDivisor X => E.sheaf) (add_neg_cancel D)) ≪≫
      (unitIsoSheafZero X).symm

/-- Tensoring actual module sheaves by the actual Cartier sheaf. -/
def cartierTensorEquivalence (D : CartierDivisor X) : X.Modules ≌ X.Modules :=
  tensorEquivalenceOfInverse D.sheaf (-D).sheaf
    (cartierNegTensorIsoUnit D) (cartierTensorNegIsoUnit D)

@[simp]
theorem cartierTensorEquivalence_functor (D : CartierDivisor X) :
    (cartierTensorEquivalence D).functor = tensorLeft D.sheaf := rfl

instance cartierTensor_preservesLimits (D : CartierDivisor X) :
    PreservesLimits (tensorLeft D.sheaf) :=
  (cartierTensorEquivalence D).symm.toAdjunction.rightAdjoint_preservesLimits

instance cartierTensor_preservesColimits (D : CartierDivisor X) :
    PreservesColimits (tensorLeft D.sheaf) :=
  (cartierTensorEquivalence D).toAdjunction.leftAdjoint_preservesColimits

instance cartierTensorEquivalence_additive (D : CartierDivisor X) :
    (cartierTensorEquivalence D).functor.Additive :=
  (cartierTensorEquivalence D).functor.additive_of_preserves_binary_products

end Cartier

end ToricPower

end
