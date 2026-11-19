module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Monad.Adjunction

/-! # Localization of an actual coresolution comparison

The ordinary comparison and the two factorization isomorphisms determine
the derived reconstruction isomorphism.  The final categorical step
uses the given adjunction and its normalization equivalence.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace ToricPower

section Localization

variable {A D : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
  [Category* D]
  (R T : DerivedCategory A ⥤ D)
  (C : CochainComplex A ℤ ⥤ CochainComplex A ℤ)
  (F G : CochainComplex A ℤ ⥤ D)
  (a : F ⟶ G)

/-- Invertibility on the actual replacement gives a natural derived
isomorphism, with no identification with a separately chosen counit. -/
def derivedComparisonOfCoresolution
    (objects : ∀ K, IsIso (a.app (C.obj K)))
    (sourceFactors : DerivedCategory.Q ⋙ R ≅ C ⋙ F)
    (targetFactors : DerivedCategory.Q ⋙ T ≅ C ⋙ G) : R ≅ T := by
  let component (K : CochainComplex A ℤ) :
      (C ⋙ F).obj K ≅ (C ⋙ G).obj K := by
    letI := objects K
    exact asIso (a.app (C.obj K))
  let e : C ⋙ F ≅ C ⋙ G := NatIso.ofComponents component (by
    intro K M f
    change F.map (C.map f) ≫ a.app (C.obj M) =
      a.app (C.obj K) ≫ G.map (C.map f)
    exact a.naturality (C.map f))
  exact (Localization.whiskeringLeftFunctor' DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ)) D).preimageIso
      (sourceFactors ≪≫ e ≪≫ targetFactors.symm)

end Localization

section Normalization

variable {C D : Type*} [Category* C] [Category* D]
  (L : C ⥤ D) (R : D ⥤ C) (adj : L ⊣ R) (E : D ≌ D)

/-- A reconstruction isomorphism for the normalized realization proves
full faithfulness of its actual normalized right adjoint. -/
def normalizedReconstructionFullyFaithful
    (comparison : R ⋙ (L ⋙ E.functor) ≅ E.functor) :
    (E.inverse ⋙ R).FullyFaithful :=
  (adj.comp E.toAdjunction).fullyFaithfulROfCompIsoId
    (Functor.associator E.inverse R (L ⋙ E.functor) ≪≫
      Functor.isoWhiskerLeft E.inverse comparison ≪≫ E.counitIso)

end Normalization

end ToricPower

end
