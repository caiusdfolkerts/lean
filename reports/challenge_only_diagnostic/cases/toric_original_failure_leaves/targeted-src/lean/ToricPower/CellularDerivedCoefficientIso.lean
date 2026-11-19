module

public import ToricPower.CellularDerivedRealization
public import ToricPower.CategoricalFoundations

/-!
# Coefficient comparisons for the actual finite-cone derived realization

Both isomorphisms retain the original finite cone replacement and its
factorization through localization. Exact postcomposition is compared
using the actual termwise complex functor, with no bounded-input premise.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace ToricPower.Cellular

universe u v w

variable (k : Type u) [Field k] {C : Type u} [Category.{u} C]
  {B : Type v} [Category.{u} B] [Abelian B] [HasDerivedCategory B]
  [HasDerivedCategory (C ⥤ ModuleCat.{u} k)]
  (H H' : (C ⥤ ModuleCat.{u} k) ⥤ B) [H.Additive] [H'.Additive]

/-- An actual coefficient natural isomorphism induces the specified
isomorphism of the genuine derived realization models. -/
def finiteConeRealizationCoefficientIso (e : H ≅ H') (m : ℕ) :
    finiteConeRealizationStageDerived k H m ≅ finiteConeRealizationStageDerived k H' m := by
  apply (Localization.whiskeringLeftFunctor'
    (DerivedCategory.Q (C := C ⥤ ModuleCat.{u} k))
    (HomologicalComplex.quasiIso (C ⥤ ModuleCat.{u} k) (.up ℤ)) (DerivedCategory B)).preimageIso
  exact finiteConeRealizationStageDerivedFactors k H m ≪≫
    isoWhiskerRight (isoWhiskerLeft (finiteConeResolution k m).functor
      (NatIso.mapHomologicalComplex e (.up ℤ))) DerivedCategory.Q ≪≫
    (finiteConeRealizationStageDerivedFactors k H' m).symm

variable {D : Type w} [Category.{u} D] [Abelian D] [HasDerivedCategory D]
  (T : B ⥤ D) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]

/-- Exact postcomposition agrees with actual termwise realization
followed by its induced functor on the full derived category. -/
def finiteConeRealizationPostcomposeIso (m : ℕ) :
    finiteConeRealizationStageDerived k (H ⋙ T) m ≅
      finiteConeRealizationStageDerived k H m ⋙ T.mapDerivedCategory := by
  apply (Localization.whiskeringLeftFunctor'
    (DerivedCategory.Q (C := C ⥤ ModuleCat.{u} k))
    (HomologicalComplex.quasiIso (C ⥤ ModuleCat.{u} k) (.up ℤ)) (DerivedCategory D)).preimageIso
  exact finiteConeRealizationStageDerivedFactors k (H ⋙ T) m ≪≫
    isoWhiskerRight (isoWhiskerLeft (finiteConeResolution k m).functor
      (Functor.mapHomologicalComplexCompIso (Iso.refl (H ⋙ T)) (.up ℤ)).symm)
      DerivedCategory.Q ≪≫
    isoWhiskerLeft ((finiteConeResolution k m).functor ⋙ H.mapHomologicalComplex (.up ℤ))
      T.mapDerivedCategoryFactors.symm ≪≫
    isoWhiskerRight (finiteConeRealizationStageDerivedFactors k H m).symm T.mapDerivedCategory

end ToricPower.Cellular

end

