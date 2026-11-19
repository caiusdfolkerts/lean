module

public import ToricPower.CategoricalFoundations

/-!
# Transporting a specified complex comparison through localization

This elementary wrapper keeps the complex model, its factorization,
and the two exact endofunctors abstract. The induced natural isomorphism
is obtained from the fully faithful localization restriction functor.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

variable {A B : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
  [Category* B] [Abelian B] [HasDerivedCategory B]
  (F : CochainComplex A ℤ ⥤ CochainComplex B ℤ)
  (G : DerivedCategory A ⥤ DerivedCategory B)
  (factor : DerivedCategory.Q ⋙ G ≅ F ⋙ DerivedCategory.Q)
  (T : A ⥤ A) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  (P : B ⥤ B) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]

/-- The localized comparison uses the actual given model and the
canonical factor maps of both exact functors. -/
def derivedComplexIntertwiningIso
    (comparison : F ⋙ P.mapHomologicalComplex (.up ℤ) ≅
      T.mapHomologicalComplex (.up ℤ) ⋙ F) :
    G ⋙ P.mapDerivedCategory ≅ T.mapDerivedCategory ⋙ G := by
  apply (Localization.whiskeringLeftFunctor' (DerivedCategory.Q (C := A))
    (HomologicalComplex.quasiIso A (.up ℤ)) (DerivedCategory B)).preimageIso
  exact Functor.isoWhiskerRight factor P.mapDerivedCategory ≪≫
    Functor.isoWhiskerLeft F P.mapDerivedCategoryFactors ≪≫
    Functor.isoWhiskerRight comparison DerivedCategory.Q ≪≫
    Functor.isoWhiskerLeft (T.mapHomologicalComplex (.up ℤ)) factor.symm ≪≫
    Functor.isoWhiskerRight T.mapDerivedCategoryFactors.symm G

end ToricPower

end
