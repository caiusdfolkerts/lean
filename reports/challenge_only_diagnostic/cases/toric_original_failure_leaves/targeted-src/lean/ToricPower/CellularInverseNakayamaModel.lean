module

public import ToricPower.CellularDerivedInverseNakayama
public import ToricPower.RightDerivedModelComparison

/-!
# The canonical inverse-Nakayama comparison on an injective model

This interface accepts an ordinary bounded-below injective complex and
its actual derived isomorphism. It keeps the model independent from any
particular finite-model record while retaining the actual right-derived
unit and its localization functor.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex

namespace ToricPower.Cellular

universe u w
variable (k : Type u) [Field k] {C : Type u} [Category.{u} C]
  [HasDerivedCategory.{w} (C ⥤ ModuleCat.{u} k)]

attribute [local instance 2000] Abelian.toPreadditive
attribute [local instance 2000] Preadditive.preadditiveHasZeroMorphisms

def inverseNakayamaPlusModelIso
    (J : CochainComplex.Plus (C ⥤ ModuleCat.{u} k))
    [∀ q, Injective (J.obj.X q)]
    (X : DerivedCategory.Plus (C ⥤ ModuleCat.{u} k))
    (e : DerivedCategory.Plus.Q.obj J ≅ X) :=
  rightDerivedFunctorPlusModelIso
    (inverseNakayama k (C := C)) J X e

def inverseNakayamaModelIso
    (J : CochainComplex.Plus (C ⥤ ModuleCat.{u} k))
    [∀ q, Injective (J.obj.X q)]
    (X : DerivedCategory.Plus (C ⥤ ModuleCat.{u} k))
    (e : DerivedCategory.Plus.Q.obj J ≅ X) :=
  rightDerivedFunctorPlusModelAmbientIso
    (inverseNakayama k (C := C)) J X e

/-- The canonical comparison is preserved as an opaque existence
statement, including its exact defining equation. -/
theorem inverseNakayamaModel_nonempty
    (J : CochainComplex.Plus (C ⥤ ModuleCat.{u} k))
    [∀ q, Injective (J.obj.X q)]
    (X : DerivedCategory.Plus (C ⥤ ModuleCat.{u} k))
    (e : DerivedCategory.Plus.Q.obj J ≅ X) :
    Nonempty { comparison :
        ((inverseNakayama k (C := C)).rightDerivedFunctorPlus.obj X).obj ≅
          DerivedCategory.Q.obj
            (((inverseNakayama k (C := C)).mapHomologicalComplex (.up ℤ)).obj J.obj) //
      comparison = inverseNakayamaModelIso k J X e } :=
  ⟨⟨inverseNakayamaModelIso k J X e, rfl⟩⟩

end ToricPower.Cellular

end
