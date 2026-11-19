module

public import ToricPower.SerrePairingDerivedComplex
public import ToricPower.CellularFiniteInjectiveSerre
public import Mathlib.Data.Int.Interval

/-!
# Serre pairing for bounded finite injective incidence complexes

For an actual bounded complex of finite-dimensional injective diagrams,
termwise inverse Nakayama gives an actual bounded projective complex.
The derived pairing holds against every unbounded complex, with scalar
duality on the Hom space whose source is this projective complex.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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

omit [HasDerivedCategory.{w} (C ⥤ ModuleCat.{u} k)] in
theorem finiteInjectiveComplex_isKInjective
    (J : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ)
    [∀ q, Injective (J.X q)] (a : ℤ) [J.IsStrictlyGE a] :
    J.IsKInjective := CochainComplex.isKInjective_of_injective J a

omit [HasDerivedCategory.{w} (C ⥤ ModuleCat.{u} k)] in
theorem finiteInjectiveComplex_inverse_isKProjective
    (J : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ)
    [∀ q, Injective (J.X q)] [∀ q c, FiniteDimensional k ((J.X q).obj c)]
    (b : ℤ) [J.IsStrictlyLE b] :
    (SerrePairing.mappedCochainComplex (inverseNakayama k) J).IsKProjective := by
  let P := SerrePairing.mappedCochainComplex (inverseNakayama k) J
  letI (q : ℤ) : Projective (P.X q) := inverseNakayama_projective_of_finite_injective k (J.X q)
  letI : P.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro q hq
    exact (inverseNakayama k).map_isZero (J.isZero_of_isStrictlyLE b q hq)
  exact CochainComplex.isKProjective_of_projective P b

omit [HasDerivedCategory.{w} (C ⥤ ModuleCat.{u} k)] in
theorem boundedComplex_isZero_outside_interval
    (J : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ)
    (a b : ℤ) [J.IsStrictlyGE a] [J.IsStrictlyLE b]
    (q : ℤ) (hq : q ∉ Finset.Icc a b) : IsZero (J.X q) := by
  by_cases h : q < a
  · exact J.isZero_of_isStrictlyGE a q h
  · exact J.isZero_of_isStrictlyLE b q (by
      simp only [Finset.mem_Icc] at hq
      omega)

omit [HasDerivedCategory.{w} (C ⥤ ModuleCat.{u} k)] in
def finiteInjectiveComplexPairing
    (J : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ)
    [∀ q, Injective (J.X q)] [∀ q c, FiniteDimensional k ((J.X q).obj c)] :
    ∀ q, SerrePairing.CodomainPairing k (inverseNakayama k) (J.X q) :=
  fun q => finiteInjectivePairing k (J.X q)

omit [HasDerivedCategory.{w} (C ⥤ ModuleCat.{u} k)] in
theorem finiteInjectiveComplexPairing_compatible
    (J : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ)
    [∀ q, Injective (J.X q)] [∀ q c, FiniteDimensional k ((J.X q).obj c)] :
    ∀ p q, SerrePairing.Compatible k
      (finiteInjectiveComplexPairing k J p) (finiteInjectiveComplexPairing k J q)
      (J.d p q) :=
  fun p q => finiteInjectivePairing_compatible k (J.X p) (J.X q) (J.d p q)

omit [HasDerivedCategory.{w} (C ⥤ ModuleCat.{u} k)] in
/-- A named complex keeps the canonical termwise inverse-Nakayama
presentation stable across the localization comparison. -/
def finiteInverseComplex
    (J : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ) :
    CochainComplex (C ⥤ ModuleCat.{u} k) ℤ :=
  SerrePairing.mappedCochainComplex (inverseNakayama k) J

omit [HasDerivedCategory.{w} (C ⥤ ModuleCat.{u} k)] in
theorem finiteInverseComplex_isKProjective
    (J : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ)
    [∀ q, Injective (J.X q)] [∀ q c, FiniteDimensional k ((J.X q).obj c)]
    (b : ℤ) [J.IsStrictlyLE b] :
    (finiteInverseComplex k J).IsKProjective :=
  finiteInjectiveComplex_inverse_isKProjective k J b

end ToricPower.Cellular

end
