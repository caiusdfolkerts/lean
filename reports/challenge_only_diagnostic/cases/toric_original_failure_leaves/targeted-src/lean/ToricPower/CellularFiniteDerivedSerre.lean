module

public import ToricPower.CellularInverseInjectiveComplex

/-!
# The actual inverse-Serre equivalence on a finite injective complex

The general signed pairing is specialized to the actual incidence
inverse-Nakayama functor. Both localization comparisons and the complete
Hom-complex sign calculation are checked in the generic theorem. The
source complex remains arbitrary and may be unbounded.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex
open CochainComplex.HomComplex

namespace ToricPower.Cellular

universe u w
variable (k : Type u) [Field k] {C : Type u} [Category.{u} C]
  [Finite C] [∀ c d : C, Finite (c ⟶ d)]
  [HasDerivedCategory.{w} (C ⥤ ModuleCat.{u} k)]

/- Select the same literal parent instances as the generic abelian
Hom-complex API. Local instance aliases would introduce distinct constants
inside quotient-module types, forcing expensive normalization. -/
attribute [local instance 2000] Abelian.toPreadditive
attribute [local instance 2000] Preadditive.preadditiveHasZeroMorphisms

def finiteInjectiveDerivedSerreEquiv
    (J : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ)
    [∀ q, Injective (J.X q)] [∀ q c, FiniteDimensional k ((J.X q).obj c)]
    (a b : ℤ) [J.IsStrictlyGE a] [J.IsStrictlyLE b]
    (E : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ) :=
  letI : J.IsKInjective := finiteInjectiveComplex_isKInjective k J a
  letI : (SerrePairing.mappedCochainComplex (inverseNakayama k) J).IsKProjective :=
    finiteInjectiveComplex_inverse_isKProjective k J b
  SerrePairing.finiteDerivedSerreEquiv.{u,u+1,w} k (inverseNakayama k) J
    (finiteInjectiveComplexPairing k J) E
    (finiteInjectiveComplexPairing_compatible k J)
    (Finset.Icc a b) (boundedComplex_isZero_outside_interval k J a b)


end ToricPower.Cellular

end
