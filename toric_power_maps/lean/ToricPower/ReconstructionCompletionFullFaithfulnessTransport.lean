module

public import ToricPower.ReconstructionCompletionDerivedBridge

/-! # Full faithfulness through the original normalized interface

The typed realization interface is identified with the given normalized
realization before the original adjunction is used. No identification with
a separately chosen counit is required.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace ToricPower

variable {C D : Type*} [Category* C] [Category* D]
  (L : C ⥤ D) (R : D ⥤ C) (adj : L ⊣ R) (E : D ≌ D)
  (N : C ⥤ D)

/-- A genuine reconstruction through an isomorphic realization interface
proves full faithfulness of the original normalized right adjoint. -/
def normalizedReconstructionFullyFaithfulOfInterface
    (interface : N ≅ L ⋙ E.functor)
    (comparison : R ⋙ N ≅ E.functor) :
    (E.inverse ⋙ R).FullyFaithful :=
  normalizedReconstructionFullyFaithful L R adj E
    (Functor.isoWhiskerLeft R interface.symm ≪≫ comparison)

end ToricPower

end
