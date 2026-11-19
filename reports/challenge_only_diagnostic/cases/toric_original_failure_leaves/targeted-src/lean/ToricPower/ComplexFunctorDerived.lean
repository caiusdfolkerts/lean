module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-! # Localization of a specified quasi-isomorphism-preserving complex functor -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

variable {A B : Type*} [Category* A] [Abelian A] [Category* B] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]
  (F G : CochainComplex A ℤ ⥤ CochainComplex B ℤ)
  (preserves : ∀ {K L : CochainComplex A ℤ} (f : K ⟶ L), QuasiIso f → QuasiIso (F.map f))

def complexFunctorDerived : DerivedCategory A ⥤ DerivedCategory B :=
  Localization.lift (W := HomologicalComplex.quasiIso A (.up ℤ))
    (F ⋙ DerivedCategory.Q) (fun K L f hf => by
      letI := preserves f hf
      exact inferInstanceAs (IsIso (DerivedCategory.Q.map (F.map f)))) DerivedCategory.Q

def complexFunctorDerivedFactors :
    DerivedCategory.Q ⋙ complexFunctorDerived F preserves ≅ F ⋙ DerivedCategory.Q :=
  Localization.fac _ _ _

include preserves in
theorem complexFunctor_preservesQuasiIso_of_iso (e : F ≅ G)
    {K L : CochainComplex A ℤ} (f : K ⟶ L) (hf : QuasiIso f) :
    QuasiIso (G.map f) := by
  letI := preserves f hf
  haveI : QuasiIso (e.inv.app K ≫ F.map f ≫ e.hom.app L) := inferInstance
  have equation : e.inv.app K ≫ F.map f ≫ e.hom.app L = G.map f := by
    rw [e.hom.naturality, e.inv_hom_id_app_assoc]
  rwa [equation] at this

variable (preservesG : ∀ {K L : CochainComplex A ℤ} (f : K ⟶ L),
  QuasiIso f → QuasiIso (G.map f))

def complexFunctorDerivedIso (e : F ≅ G) :
    complexFunctorDerived F preserves ≅ complexFunctorDerived G preservesG := by
  apply (Localization.whiskeringLeftFunctor' DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ)) (DerivedCategory B)).preimageIso
  exact complexFunctorDerivedFactors F preserves ≪≫
    Functor.isoWhiskerRight e DerivedCategory.Q ≪≫
      (complexFunctorDerivedFactors G preservesG).symm

end ToricPower

end
