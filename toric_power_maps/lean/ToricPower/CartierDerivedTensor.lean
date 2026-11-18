module

public import ToricPower.CartierTensorEquivalence
public import ToricPower.CoherentFoundations

/-!
# The actual Cartier tensor autoequivalence

Multiplication of rational Cartier sections gives the two inverse tensor
isomorphisms for `O(D)` and `O(-D)`. The resulting equivalence is the actual
tensor functor on module sheaves. It restricts to actual coherent sheaves
and induces the corresponding equivalence of the literal bounded coherent
derived category. In particular, no flatness or derived tensor comparison
is introduced as an additional hypothesis.

-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace ToricPower

universe u v

section Cartier

open TauCeti.AlgebraicGeometry.Scheme
open TauCeti.AlgebraicGeometry.Scheme.CartierDivisor

variable {X : Scheme.{u}} [IsIntegral X]

instance cartierSheaf_finitePresentation (D : CartierDivisor X) :
    D.sheaf.IsFinitePresentation := by
  letI : TauCeti.SheafOfModules.IsInvertible (R := X.ringCatSheaf) D.sheaf :=
    D.isInvertible_sheaf
  infer_instance

theorem cartierTensor_finitePresentation (D : CartierDivisor X)
    (M : X.Modules) [M.IsFinitePresentation] :
    (D.sheaf ⊗ M).IsFinitePresentation :=
  TauCeti.SheafOfModules.isFinitePresentation_tensorObj (R := X.sheaf)

/-- Finite presentation is preserved and reflected by this actual
tensor equivalence, using its actual inverse `O(-D) ⊗ -`. -/
theorem cartierTensor_finitePresentation_iff (D : CartierDivisor X)
    (M : X.Modules) :
    (D.sheaf ⊗ M).IsFinitePresentation ↔ M.IsFinitePresentation := by
  constructor
  · intro h
    letI := h
    exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
      ((cartierTensorEquivalence D).unitIso.app M).symm
      (cartierTensor_finitePresentation (-D) (D.sheaf ⊗ M))
  · intro h
    letI := h
    exact cartierTensor_finitePresentation D M

/-- The same actual tensor equivalence on the category of coherent
sheaves, before passing to complexes. -/
def coherentCartierTensorEquivalence (D : CartierDivisor X) : Coh X ≌ Coh X :=
  (cartierTensorEquivalence D).congrFullSubcategory
    (P := (SheafOfModules.isFinitePresentation X.ringCatSheaf : ObjectProperty X.Modules))
    (Q := (SheafOfModules.isFinitePresentation X.ringCatSheaf : ObjectProperty X.Modules)) (by
    ext M
    exact cartierTensor_finitePresentation_iff D M)

instance coherentCartierTensor_additive (D : CartierDivisor X) :
    (coherentCartierTensorEquivalence D).functor.Additive :=
  (coherentCartierTensorEquivalence D).functor.additive_of_preserves_binary_products

@[simp]
theorem coherentCartierTensor_obj_underlying (D : CartierDivisor X) (M : Coh X) :
    ((coherentCartierTensorEquivalence D).functor.obj M).obj = D.sheaf ⊗ M.obj := rfl

local instance cartierTensorStandardDerivedCategory [IsLocallyNoetherian X] :
    HasDerivedCategory.{u + 1} (Coh X) := HasDerivedCategory.standard _

/-- The literal bounded coherent derived tensor autoequivalence. It is
induced by an actual exact sheaf functor, so its value on complexes is
ordinary termwise tensoring by this invertible sheaf. -/
def cartierBoundedDerivedTensorEquivalence [IsLocallyNoetherian X]
    (D : CartierDivisor X) : DbCoh X ≌ DbCoh X :=
  (coherentCartierTensorEquivalence D).mapBoundedDerivedCategory

/-- The derived tensor of an actual degree-zero coherent sheaf is the
actual degree-zero tensor sheaf. -/
def cartierBoundedDerivedTensorSingleIso [IsLocallyNoetherian X]
    (D : CartierDivisor X) (M : Coh X) :
    (cartierBoundedDerivedTensorEquivalence D).functor.obj (coherentSingle X M) ≅
      coherentSingle X ((coherentCartierTensorEquivalence D).functor.obj M) := by
  change (coherentCartierTensorEquivalence D).mapBoundedDerivedCategory.functor.obj
      (coherentSingle X M) ≅ _
  rw [CategoryTheory.Equivalence.mapBoundedDerivedCategory_functor]
  exact ((coherentCartierTensorEquivalence D).functor.mapBoundedDerivedCategorySingleFunctor 0).app M

end Cartier

end ToricPower

end
