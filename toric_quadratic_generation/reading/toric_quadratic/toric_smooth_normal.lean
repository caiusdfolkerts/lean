module

public import PaperVerification.ToricEtaleNormal
public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

@[expose] public section

/-!
# Integral closedness derived from ordinary smoothness

The local presentation theorem for smooth algebras gives standard étale
charts over polynomial rings. The preceding étale result proves integral
closedness on these charts. Localization and the actual local criterion
then prove it for the original algebra. On an integral scheme smooth over
a field, this applies to every affine coordinate ring and every actual
stalk. Normality is consequently a conclusion, not an additional input.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory
open scoped nonZeroDivisors

variable (k S : Type*) [Field k] [CommRing S] [IsDomain S]
    [Algebra k S] [Algebra.Smooth k S]

include k

/-- Every prime has a genuine principal neighborhood with integrally
closed coordinate ring. The local algebra structure over a polynomial
ring is supplied by the smooth local presentation theorem. -/
theorem exists_integrallyClosed_away_of_smooth (p : Ideal S) [p.IsPrime] :
    ∃ f : S, f ∉ p ∧ IsIntegrallyClosed (Localization.Away f) := by
  obtain ⟨f,hfp,n,ha,ht,he⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := k) (p := p)
  letI : Algebra (MvPolynomial (Fin n) k) (Localization.Away f) := ha
  letI : IsScalarTower k (MvPolynomial (Fin n) k) (Localization.Away f) := ht
  letI : Algebra.IsStandardEtale (MvPolynomial (Fin n) k) (Localization.Away f) := he
  have hf : f ≠ 0 := fun h => hfp (h ▸ p.zero_mem)
  letI : IsDomain (Localization.Away f) := Localization.Away.isDomain hf
  exact ⟨f,hfp,isIntegrallyClosed_of_etale
    (MvPolynomial (Fin n) k) (Localization.Away f)⟩

/-- Normality of a smooth affine integral algebra, with no normality or
regularity hypothesis on that algebra. -/
theorem isIntegrallyClosed_of_smooth_field : IsIntegrallyClosed S := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro p hp0 hp
  obtain ⟨f,hfp,hfNormal⟩ := exists_integrallyClosed_away_of_smooth k S p
  have hf : f ≠ 0 := fun h => hfp (h ▸ p.zero_mem)
  let A := Localization.Away f
  letI : IsDomain A := Localization.Away.isDomain hf
  letI : IsIntegrallyClosed A := hfNormal
  have hdis : Disjoint (Submonoid.powers f : Set S) (p : Set S) := by
    exact (Ideal.disjoint_powers_iff_notMem_of_isPrime (I := p) f).mpr hfp
  let q : Ideal A := p.map (algebraMap S A)
  letI : q.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f) A p
      inferInstance hdis
  have hq : q.comap (algebraMap S A) = p :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers f) A
      inferInstance hdis
  letI : IsIntegrallyClosed (Localization.AtPrime q) :=
    isIntegrallyClosed_of_isLocalization (Localization.AtPrime q)
      q.primeCompl q.primeCompl_le_nonZeroDivisors
  let e := IsLocalization.localizationLocalizationAtPrimeIsoLocalization
    (Submonoid.powers f) q
  have hn : IsIntegrallyClosed (Localization.AtPrime (q.comap (algebraMap S A))) :=
    (inferInstance : IsIntegrallyClosed (Localization.AtPrime q)).of_equiv
      e.symm.toRingEquiv
  let p' : PrimeSpectrum S := ⟨q.comap (algebraMap S A),inferInstance⟩
  let p₀ : PrimeSpectrum S := ⟨p,inferInstance⟩
  have hpEq : p'=p₀ := PrimeSpectrum.ext hq
  exact (congrArg
    (fun z : PrimeSpectrum S => IsIntegrallyClosed (Localization.AtPrime z.asIdeal))
    hpEq).mp hn

omit k

section Schemes

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [Smooth f]

include f

/-- The actual ring of functions on each nonempty affine open of an
integral scheme smooth over a field is integrally closed. -/
theorem smooth_affineOpen_isIntegrallyClosed (U : X.Opens)
    (hU : IsAffineOpen U) [Nonempty U] : IsIntegrallyClosed Γ(X,U) := by
  let R := Γ(Spec (.of k),⊤)
  let e : R ≃+* k := (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv
  letI : Field R := (e.isField (Field.toIsField k)).toField
  have hpre : U ≤ f ⁻¹ᵁ (⊤ : (Spec (.of k)).Opens) := by simp
  letI : Algebra R Γ(X,U) := (f.appLE ⊤ U hpre).hom.toAlgebra
  letI : Algebra.Smooth R Γ(X,U) :=
    (f.smooth_appLE (isAffineOpen_top _) hU hpre).toAlgebra
  exact isIntegrallyClosed_of_smooth_field R Γ(X,U)

/-- Integral closedness of each literal local ring follows from an actual
affine neighborhood and the stalk localization theorem. -/
theorem smooth_stalk_isIntegrallyClosed (x : X) :
    IsIntegrallyClosed (X.presheaf.stalk x) := by
  obtain ⟨_,⟨U,hU,rfl⟩,hxU,-⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ x) isOpen_univ
  letI : Nonempty U := ⟨⟨x,hxU⟩⟩
  letI : IsIntegrallyClosed Γ(X,U) := smooth_affineOpen_isIntegrallyClosed f U hU
  letI : Algebra Γ(X,U) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x,hxU⟩
  let p := hU.primeIdealOf ⟨x,hxU⟩
  letI : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal :=
    hU.isLocalization_stalk ⟨x,hxU⟩
  exact isIntegrallyClosed_of_isLocalization (X.presheaf.stalk x)
    p.asIdeal.primeCompl p.asIdeal.primeCompl_le_nonZeroDivisors

end Schemes

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.isIntegrallyClosed_of_smooth_field
#print axioms PaperVerification.ToricSchemes.smooth_stalk_isIntegrallyClosed
