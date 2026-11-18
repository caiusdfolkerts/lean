module

public import ToricPower.QuasicoherentCategory
public import ToricPower.CartierDerivedTensor

/-!
# Cartier tensoring on unbounded quasicoherent derived categories

The actual Cartier tensor equivalence preserves and reflects
quasicoherence. Its restriction therefore gives an exact equivalence of
the abelian quasicoherent category and an equivalence of its unbounded
derived category. This construction uses the literal sheaf tensor
product and the checked rational-section multiplication isomorphisms.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open TauCeti.AlgebraicGeometry.Scheme

namespace ToricPower

universe u

variable {X : Scheme.{u}} [IsIntegral X]

/-- Tensoring with the actual Cartier sheaf preserves quasicoherence. -/
theorem cartierTensor_quasicoherent (D : CartierDivisor X)
    (M : X.Modules) [M.IsQuasicoherent] :
    (D.sheaf ⊗ M).IsQuasicoherent := by
  exact Scheme.Modules.isQuasicoherent_tensorObj X D.sheaf M

/-- Reflection follows by applying the actual inverse tensor functor. -/
theorem cartierTensor_quasicoherent_iff (D : CartierDivisor X) (M : X.Modules) :
    (D.sheaf ⊗ M).IsQuasicoherent ↔ M.IsQuasicoherent := by
  constructor
  · intro h
    letI := h
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      ((cartierTensorEquivalence D).unitIso.app M).symm
      (cartierTensor_quasicoherent (-D) (D.sheaf ⊗ M))
  · intro h
    letI := h
    exact cartierTensor_quasicoherent D M

/-- The equivalence is the actual tensor functor on actual quasicoherent
sheaves; no finite-presentation condition is imposed on its objects. -/
def quasicoherentCartierTensorEquivalence (D : CartierDivisor X) : QCoh X ≌ QCoh X :=
  (cartierTensorEquivalence D).congrFullSubcategory
    (P := (SheafOfModules.isQuasicoherent X.ringCatSheaf : ObjectProperty X.Modules))
    (Q := (SheafOfModules.isQuasicoherent X.ringCatSheaf : ObjectProperty X.Modules)) (by
      ext M
      exact cartierTensor_quasicoherent_iff D M)

instance quasicoherentCartierTensor_additive (D : CartierDivisor X) :
    (quasicoherentCartierTensorEquivalence D).functor.Additive :=
  (quasicoherentCartierTensorEquivalence D).functor.additive_of_preserves_binary_products

@[simp]
theorem quasicoherentCartierTensor_obj_underlying (D : CartierDivisor X) (M : QCoh X) :
    ((quasicoherentCartierTensorEquivalence D).functor.obj M).obj =
      D.sheaf ⊗ M.obj := rfl

local instance quasicoherentCartierDerivedCategory :
    HasDerivedCategory.{u+1} (QCoh X) := HasDerivedCategory.standard _

/-- The exact tensor equivalence extends to the full unbounded derived
category of quasicoherent sheaves. -/
def quasicoherentCartierDerivedTensorEquivalence (D : CartierDivisor X) :
    DerivedQCoh X ≌ DerivedQCoh X :=
  (quasicoherentCartierTensorEquivalence D).mapDerivedCategory

/-- The underlying induced derived functor is the one obtained from
termwise tensoring and the ordinary derived localization. -/
theorem quasicoherentCartierDerivedTensor_functor (D : CartierDivisor X) :
    (quasicoherentCartierDerivedTensorEquivalence D).functor =
      (quasicoherentCartierTensorEquivalence D).functor.mapDerivedCategory := rfl

/-- On an arbitrary complex, including an unbounded one, this is the
actual localization of the termwise tensor complex. -/
def quasicoherentCartierDerivedTensorComplexIso (D : CartierDivisor X)
    (K : CochainComplex (QCoh X) ℤ) :
    (quasicoherentCartierDerivedTensorEquivalence D).functor.obj
        (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj
        (((quasicoherentCartierTensorEquivalence D).functor.mapHomologicalComplex
          (.up ℤ)).obj K) :=
  (quasicoherentCartierTensorEquivalence D).functor.mapDerivedCategoryFactors.app K

end ToricPower

end
