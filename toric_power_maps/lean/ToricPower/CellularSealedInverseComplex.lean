module

public import ToricPower.CellularFiniteModelData
public import ToricPower.CellularSealedInversePairing
public import ToricPower.CellularInverseInjectiveComplex

/-!
# Bounded projective complexes and signed pairings in the sealed presentation

The source model is the original actual finite injective complex.
Termwise inverse Nakayama is finite projective by the transported,
proved coefficient data. Both support bounds are unchanged, and the
generic signed complex duality applies to every unbounded source.
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

namespace FiniteInjectiveModel
variable {k} {X : DerivedCategory (C ⥤ ModuleCat.{u} k)}
  (M : FiniteInjectiveModel k X)

abbrev sealedInverseComplex : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ :=
  SerrePairing.mappedCochainComplex (sealedInverseNakayama k) M.complex

instance sealedInverseComplex_projective (q : ℤ) :
    Projective (M.sealedInverseComplex.X q) :=
  sealedInverseNakayama_projective k (M.complex.X q)

instance sealedInverseComplex_finite (q : ℤ) (c : C) :
    FiniteDimensional k ((M.sealedInverseComplex.X q).obj c) :=
  sealedInverseNakayama_finite k (M.complex.X q) c

instance sealedInverseComplex_strictlyGE : M.sealedInverseComplex.IsStrictlyGE M.lower := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro q hq
  exact (sealedInverseNakayama k).map_isZero
    (M.complex.isZero_of_isStrictlyGE M.lower q hq)

instance sealedInverseComplex_strictlyLE : M.sealedInverseComplex.IsStrictlyLE M.upper := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro q hq
  exact (sealedInverseNakayama k).map_isZero
    (M.complex.isZero_of_isStrictlyLE M.upper q hq)

instance sealedInverseComplex_isKProjective : M.sealedInverseComplex.IsKProjective :=
  CochainComplex.isKProjective_of_projective M.sealedInverseComplex M.upper

end FiniteInjectiveModel

/-- The duality is the proved signed Hom-complex duality, with the
genuine K-injective and K-projective localization comparisons. -/
def sealedModelDerivedSerreEquiv
    {X : DerivedCategory (C ⥤ ModuleCat.{u} k)} (M : FiniteInjectiveModel k X)
    (E : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ) :=
  SerrePairing.finiteDerivedSerreEquiv k (sealedInverseNakayama k) M.complex
    (fun q => sealedFiniteInjectivePairing k (M.complex.X q)) E
    (fun p q => sealedFiniteInjectivePairing_compatible k
      (M.complex.X p) (M.complex.X q) (M.complex.d p q))
    (Finset.Icc M.lower M.upper)
    (boundedComplex_isZero_outside_interval k M.complex M.lower M.upper)

end ToricPower.Cellular
end
