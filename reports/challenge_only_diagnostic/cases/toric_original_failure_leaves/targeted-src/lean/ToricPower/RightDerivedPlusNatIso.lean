module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-!
# Natural isomorphisms of bounded-below right-derived functors

This small adapter transports an actual ordinary natural isomorphism
through Mathlib's right-derived natural transformations.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace ToricPower

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
  {F G : A ⥤ B} [F.Additive] [G.Additive]

/-- The genuine derived natural isomorphism induced by an ordinary one. -/
def rightDerivedPlusNatIso (e : F ≅ G) :
    F.rightDerivedFunctorPlus ≅ G.rightDerivedFunctorPlus where
  hom := e.hom.rightDerivedFunctorPlus
  inv := e.inv.rightDerivedFunctorPlus
  hom_inv_id := by
    rw [← NatTrans.rightDerivedFunctorPlus_comp, e.hom_inv_id,
      NatTrans.rightDerivedFunctorPlus_id]
  inv_hom_id := by
    rw [← NatTrans.rightDerivedFunctorPlus_comp, e.inv_hom_id,
      NatTrans.rightDerivedFunctorPlus_id]

end ToricPower
