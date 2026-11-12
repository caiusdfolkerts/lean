module

public import ToricPower.CellularHomotopyInverseModelIso
public import ToricPower.HomotopyDerivedComplexComparison
public import ToricPower.MappedCochainComplexPresentation
public import ToricPower.HomotopyModelPostcomposition
public import ToricPower.CellularSealedInverseComplex

/-!
# Actual finite-model comparison for the homotopy inverse-Nakayama functor

The comparison is ordinary additive functoriality of complexes followed
by actual localization. Its naturality follows from the unique lift in
the K-injective homotopy category. No right-derived comparison is assumed.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CochainComplex

namespace ToricPower.Cellular

universe u w
variable (k : Type u) [Field k] {C : Type u} [Category.{u} C]
  [Finite C] [∀ c d : C, Finite (c ⟶ d)]
  [HasDerivedCategory.{w} (C ⥤ ModuleCat.{u} k)]

attribute [local instance 2000] Abelian.toPreadditive
attribute [local instance 2000] Preadditive.preadditiveHasZeroMorphisms

/-- The functorial comparison retains the generic mapped-complex
presentation supplied by the signed-pairing API. -/
def finiteInverseNakayamaSealedPresentationIso :
    finiteInverseNakayama k (C := C) ≅
      (finiteHomotopyFunctor k ⋙ kInjectiveHomotopyInclusion (C ⥤ ModuleCat k)) ⋙
        additiveHomotopyDerived (sealedInverseNakayama k) := Iso.refl _

def finiteInversePairingModelIso (X : FiniteDerivedDiagrams k (C := C)) :
    (finiteInverseNakayama k).obj X ≅
      DerivedCategory.Q.obj
        (SerrePairing.mappedCochainComplex (sealedInverseNakayama k)
          (finiteChosenModel k X).complex) :=
  presentedMappedHomotopyModelIso (sealedInverseNakayama k)
    (finiteHomotopyFunctor k ⋙ kInjectiveHomotopyInclusion (C ⥤ ModuleCat k))
    (fun X => (finiteChosenModel k X).complex) (finiteHomotopyModelIso k)
    (finiteInverseNakayama k) (finiteInverseNakayamaSealedPresentationIso k) X

end ToricPower.Cellular
end
