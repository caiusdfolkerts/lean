module

public import ToricPower.CellularSealedInverseNakayama
public import ToricPower.CellularFiniteInjectiveSerre
public import ToricPower.SerrePairingDerivedComplex
public import Mathlib.Data.Int.Interval

/-!
# The actual finite-injective pairing in the sealed presentation

All coefficient-level facts are transported together along the proved
equality to ordinary inverse Nakayama. This includes the pairing, its
map compatibility, and finite projectivity. The signed complex pairing
therefore keeps the complete mathematical content of the original one.
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

attribute [local instance 2000] Abelian.toPreadditive
attribute [local instance 2000] Preadditive.preadditiveHasZeroMorphisms

/-- The complete finite-coefficient data, including the actual map
compatibility needed for a functorial signed complex pairing. -/
structure FiniteInverseCoefficientData (T : (C ⥤ ModuleCat.{u} k) ⥤ C ⥤ ModuleCat.{u} k) where
  pairing : ∀ (J : C ⥤ ModuleCat.{u} k) [Injective J]
    [∀ c, FiniteDimensional k (J.obj c)], SerrePairing.CodomainPairing k T J
  compatible : ∀ (J K : C ⥤ ModuleCat.{u} k)
    [Injective J] [Injective K]
    [∀ c, FiniteDimensional k (J.obj c)] [∀ c, FiniteDimensional k (K.obj c)]
    (f : J ⟶ K), SerrePairing.Compatible k (pairing J) (pairing K) f
  projective : ∀ (J : C ⥤ ModuleCat.{u} k) [Injective J]
    [∀ c, FiniteDimensional k (J.obj c)], Projective (T.obj J)
  finite : ∀ (J : C ⥤ ModuleCat.{u} k)
    [∀ c, FiniteDimensional k (J.obj c)] (c : C),
    FiniteDimensional k ((T.obj J).obj c)

def ordinaryFiniteInverseCoefficientData :
    FiniteInverseCoefficientData k (inverseNakayama k (C := C)) where
  pairing J := finiteInjectivePairing k J
  compatible J K _ _ _ _ f := finiteInjectivePairing_compatible k J K f
  projective J := inverseNakayama_projective_of_finite_injective k J
  finite J _ c := inverseNakayama_finite k J c

/-- Transport is by the proved equality of the whole coefficient
functors, including every pairing map and its compatibility proof. -/
def sealedFiniteInverseCoefficientData :
    FiniteInverseCoefficientData k (sealedInverseNakayama k (C := C)) :=
  (congrArg (FiniteInverseCoefficientData k) (sealedInverseNakayama_eq k)).mpr
    (ordinaryFiniteInverseCoefficientData k)

def sealedFiniteInjectivePairing (J : C ⥤ ModuleCat.{u} k) [Injective J]
    [∀ c, FiniteDimensional k (J.obj c)] :
    SerrePairing.CodomainPairing k (sealedInverseNakayama k) J :=
  (sealedFiniteInverseCoefficientData k).pairing J

theorem sealedFiniteInjectivePairing_compatible (J K : C ⥤ ModuleCat.{u} k)
    [Injective J] [Injective K]
    [∀ c, FiniteDimensional k (J.obj c)] [∀ c, FiniteDimensional k (K.obj c)]
    (f : J ⟶ K) :
    SerrePairing.Compatible k (sealedFiniteInjectivePairing k J)
      (sealedFiniteInjectivePairing k K) f :=
  (sealedFiniteInverseCoefficientData k).compatible J K f

instance sealedInverseNakayama_projective (J : C ⥤ ModuleCat.{u} k) [Injective J]
    [∀ c, FiniteDimensional k (J.obj c)] :
    Projective ((sealedInverseNakayama k).obj J) :=
  (sealedFiniteInverseCoefficientData k).projective J

instance sealedInverseNakayama_finite (J : C ⥤ ModuleCat.{u} k)
    [∀ c, FiniteDimensional k (J.obj c)] (c : C) :
    FiniteDimensional k (((sealedInverseNakayama k).obj J).obj c) :=
  (sealedFiniteInverseCoefficientData k).finite J c

end ToricPower.Cellular
end
