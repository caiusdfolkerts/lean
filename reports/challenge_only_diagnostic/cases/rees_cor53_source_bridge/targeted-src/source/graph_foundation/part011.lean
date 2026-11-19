module
public import graph_foundation.part010

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.ActualIdealCoordinates -/
section

/-! # The filtered kernel is the actual ideal Koszul complex

The kernel of the polynomial quotient map is explicitly identified with
the coordinate module whose coefficients belong to the literal ideal.
The differential is multiplication by each polynomial variable followed
by exterior contraction. Its filtration is proved equal to the one given
by the monic triangular ideal basis.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 750000
noncomputable section

namespace FourPapers.Sublattice
open Classical CategoryTheory MvPolynomial CommAlg CommAlg.Koszul CommAlg.Polymatroid
open FourPapers.Universal FourPapers.FilteredHomology
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

def emptyCoefficientPolynomialEquiv :
    CoefficientQuotient (k := k) (∅ : Family V) ≃ₐ[MvPolynomial V k] MvPolynomial V k :=
  (Ideal.quotientEquivAlgOfEq (MvPolynomial V k)
    ((forbiddenIdeal_eq_monomialIdeal (k := k) (∅ : Family V)).trans (by
      simp only [monomialIdeal, Finset.coe_empty, Set.image_empty, Ideal.span_empty]))).trans
    (AlgEquiv.quotientBot (MvPolynomial V k) (MvPolynomial V k))

@[simp] lemma emptyCoefficientPolynomialEquiv_monomial (a : Exponent V) :
    emptyCoefficientPolynomialEquiv (quotientMonomial (k := k) (∅ : Family V) a) =
      monomial a (1 : k) := by
  simp only [emptyCoefficientPolynomialEquiv, AlgEquiv.trans_apply, quotientMonomial,
    Ideal.quotientEquivAlgOfEq_mk, AlgEquiv.quotientBot_mk]

def emptyCoefficientLinearEquiv :
    CoefficientQuotient (k := k) (∅ : Family V) ≃ₗ[k] MvPolynomial V k :=
  (emptyCoefficientPolynomialEquiv (k := k) (V := V)).toLinearEquiv.restrictScalars k

lemma ambientCoefficientProjection_polynomial (P : QuotientGroebnerData V k)
    (c : CoefficientQuotient (k := k) (∅ : Family V)) :
    P.coefficientEquiv ((polynomialQuotientData P.order).coefficientFactor P bot_le c) =
      Ideal.Quotient.mk P.ideal (emptyCoefficientPolynomialEquiv c) := by
  have he : P.coefficientEquiv.toLinearMap.comp
      ((polynomialQuotientData P.order).coefficientFactor P bot_le) =
      (Ideal.Quotient.mkₐ k P.ideal).toLinearMap.comp
        (emptyCoefficientLinearEquiv (k := k) (V := V)).toLinearMap := by
    apply (quotientMonomialBasis (k := k) (∅ : Family V)).ext
    intro a
    change P.coefficientEquiv
        ((polynomialQuotientData P.order).coefficientFactor P bot_le
          (quotientMonomialBasis (k := k) (∅ : Family V) a)) =
      Ideal.Quotient.mk P.ideal
        (emptyCoefficientPolynomialEquiv
          (quotientMonomialBasis (k := k) (∅ : Family V) a))
    rw [QuotientGroebnerData.coefficientFactor_basis,
      LinearEquiv.apply_symm_apply, quotientMonomialBasis_apply,
      emptyCoefficientPolynomialEquiv_monomial]
  exact LinearMap.congr_fun he c

lemma ambientKoszulProjection_polynomial (P : QuotientGroebnerData V k) (p : ℕ)
    (x : AmbientKoszulCoordinates (k := k) (V := V) p) (F : Set.powersetCard V p) :
    P.coefficientEquiv (ambientKoszulProjection P p x F) =
      Ideal.Quotient.mk P.ideal (emptyCoefficientPolynomialEquiv (x F)) := by
  rw [ambientKoszulProjection, QuotientGroebnerData.koszulFactor_eq_mapRange]
  exact ambientCoefficientProjection_polynomial P (x F)

def idealAmbientCoefficientMap (J : Ideal (MvPolynomial V k)) :
    J →ₗ[MvPolynomial V k] CoefficientQuotient (k := k) (∅ : Family V) :=
  emptyCoefficientPolynomialEquiv.symm.toLinearMap.comp J.subtype

def idealCoordinatesToAmbient (J : Ideal (MvPolynomial V k)) (p : ℕ) :
    (Set.powersetCard V p →₀ J) →ₗ[k] AmbientKoszulCoordinates (k := k) (V := V) p :=
  (Finsupp.mapRange.linearMap (idealAmbientCoefficientMap J)).restrictScalars k

@[simp] lemma idealCoordinatesToAmbient_apply (J : Ideal (MvPolynomial V k)) (p : ℕ)
    (x : Set.powersetCard V p →₀ J) (F : Set.powersetCard V p) :
    idealCoordinatesToAmbient J p x F = emptyCoefficientPolynomialEquiv.symm (x F).val := rfl

lemma idealCoordinatesToAmbient_injective (J : Ideal (MvPolynomial V k)) (p : ℕ) :
    Function.Injective (idealCoordinatesToAmbient J p) := by
  intro x y h
  apply Finsupp.ext
  intro F
  apply Subtype.ext
  apply emptyCoefficientPolynomialEquiv.symm.injective
  exact congrArg (fun z : AmbientKoszulCoordinates (k := k) (V := V) p => z F) h

lemma idealCoordinatesToAmbient_mem_kernel (P : QuotientGroebnerData V k) (p : ℕ)
    (x : Set.powersetCard V p →₀ P.ideal) :
    idealCoordinatesToAmbient P.ideal p x ∈ LinearMap.ker (ambientKoszulProjection P p) := by
  change ambientKoszulProjection P p (idealCoordinatesToAmbient P.ideal p x) = 0
  apply Finsupp.ext
  intro F
  apply P.coefficientEquiv.injective
  rw [Finsupp.zero_apply, map_zero, ambientKoszulProjection_polynomial, idealCoordinatesToAmbient_apply,
    AlgEquiv.apply_symm_apply]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (x F).property

def idealCoordinatesToKernel (P : QuotientGroebnerData V k) (p : ℕ) :
    (Set.powersetCard V p →₀ P.ideal) →ₗ[k]
      LinearMap.ker (ambientKoszulProjection P p) :=
  (idealCoordinatesToAmbient P.ideal p).codRestrict _
    (idealCoordinatesToAmbient_mem_kernel P p)

theorem idealCoordinatesToKernel_surjective (P : QuotientGroebnerData V k) (p : ℕ) :
    Function.Surjective (idealCoordinatesToKernel P p) := by
  intro x
  have hx (F : Set.powersetCard V p) : emptyCoefficientPolynomialEquiv (x.val F) ∈ P.ideal := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [← ambientKoszulProjection_polynomial P p x.val F]
    rw [congrArg (fun z => z F) x.property, Finsupp.zero_apply, map_zero]
  let y : Set.powersetCard V p →₀ P.ideal :=
    (Finsupp.linearEquivFunOnFinite k P.ideal (Set.powersetCard V p)).symm
      (fun F => ⟨emptyCoefficientPolynomialEquiv (x.val F), hx F⟩)
  refine ⟨y, ?_⟩
  apply Subtype.ext
  ext F
  change emptyCoefficientPolynomialEquiv.symm (emptyCoefficientPolynomialEquiv (x.val F)) = x.val F
  exact AlgEquiv.symm_apply_apply _ _

/-- The equivalence acts coefficientwise on the actual ideal, without
identifying the ideal with its initial monomials. -/
def idealCoordinatesKernelEquiv (P : QuotientGroebnerData V k) (p : ℕ) :
    (Set.powersetCard V p →₀ P.ideal) ≃ₗ[k]
      LinearMap.ker (ambientKoszulProjection P p) :=
  LinearEquiv.ofBijective (idealCoordinatesToKernel P p)
    ⟨fun x y h => idealCoordinatesToAmbient_injective P.ideal p
        (congrArg Subtype.val h), idealCoordinatesToKernel_surjective P p⟩

@[simp] lemma idealCoordinatesKernelEquiv_val (P : QuotientGroebnerData V k) (p : ℕ)
    (x : Set.powersetCard V p →₀ P.ideal) :
    (idealCoordinatesKernelEquiv P p x).val = idealCoordinatesToAmbient P.ideal p x := rfl

def actualIdealCoordinateDifferential (J : Ideal (MvPolynomial V k)) (p : ℕ) :
    (Set.powersetCard V (p+1) →₀ J) →ₗ[k] (Set.powersetCard V p →₀ J) :=
  (coordinateDifferential (X : V → MvPolynomial V k)
    (ModuleCat.of (MvPolynomial V k) J) p).restrictScalars k

def actualIdealPreviousDifferential (J : Ideal (MvPolynomial V k)) : ∀ p : ℕ,
    (Set.powersetCard V p →₀ J) →ₗ[k] (Set.powersetCard V p.pred →₀ J)
  | 0 => 0
  | p+1 => actualIdealCoordinateDifferential J p

theorem idealCoordinatesToAmbient_differential (J : Ideal (MvPolynomial V k)) (p : ℕ)
    (x : Set.powersetCard V (p+1) →₀ J) :
    quotientDifferential (k := k) ∅ p (idealCoordinatesToAmbient J (p+1) x) =
      idealCoordinatesToAmbient J p (actualIdealCoordinateDifferential J p x) :=
  coordinateDifferential_mapRange (X : V → MvPolynomial V k)
    (ModuleCat.of (MvPolynomial V k) J)
    (ModuleCat.of (MvPolynomial V k) (CoefficientQuotient (k := k) (∅ : Family V)))
    (idealAmbientCoefficientMap J) p x

theorem idealCoordinatesKernelEquiv_differential (P : QuotientGroebnerData V k) (p : ℕ)
    (x : Set.powersetCard V p →₀ P.ideal) :
    ambientKernelDifferential P p (idealCoordinatesKernelEquiv P p x) =
      idealCoordinatesKernelEquiv P p.pred (actualIdealPreviousDifferential P.ideal p x) := by
  apply Subtype.ext
  cases p with
  | zero =>
      change (0 : AmbientKoszulCoordinates (k := k) (V := V) 0) =
        idealCoordinatesToAmbient P.ideal 0 (0 : Set.powersetCard V 0 →₀ P.ideal)
      exact (map_zero (idealCoordinatesToAmbient P.ideal 0)).symm
  | succ p => exact idealCoordinatesToAmbient_differential P.ideal p x


/-- Coefficients in the empty monomial quotient are literal polynomial
coefficients. This identifies the ambient filtration without a choice of
normal form. -/
theorem emptyCoefficientPolynomialEquiv_repr
    (c : CoefficientQuotient (k := k) (∅ : Family V))
    (a : {a : Exponent V // QuotientAllowed (∅ : Family V) a}) :
    (quotientMonomialBasis (k := k) (∅ : Family V)).repr c a =
      (emptyCoefficientPolynomialEquiv c).coeff a.val := by
  have he : (quotientMonomialBasis (k := k) (∅ : Family V)).coord a =
      (MvPolynomial.lcoeff k a.val).comp
        (emptyCoefficientLinearEquiv (k := k) (V := V)).toLinearMap := by
    apply (quotientMonomialBasis (k := k) (∅ : Family V)).ext
    intro b
    change (quotientMonomialBasis (k := k) (∅ : Family V)).repr
        (quotientMonomialBasis (k := k) (∅ : Family V) b) a =
      (emptyCoefficientPolynomialEquiv
        (quotientMonomialBasis (k := k) (∅ : Family V) b)).coeff a.val
    rw [Module.Basis.repr_self, quotientMonomialBasis_apply,
      emptyCoefficientPolynomialEquiv_monomial]
    simp only [Finsupp.single_apply, coeff_monomial, Subtype.ext_iff]
  exact LinearMap.congr_fun he c

theorem idealCoordinatesToAmbient_repr (J : Ideal (MvPolynomial V k)) (p : ℕ)
    (x : Set.powersetCard V p →₀ J) (a : QuotientIndex (∅ : Family V) p) :
    (quotientCoefficientBasis (k := k) (∅ : Family V) p).repr
      (idealCoordinatesToAmbient J p x) a = (x a.1).val.coeff a.2.val := by
  rw [quotientCoefficientBasis, Finsupp.basis_repr,
    emptyCoefficientPolynomialEquiv_repr, idealCoordinatesToAmbient_apply,
    AlgEquiv.apply_symm_apply]

section Nontrivial
variable [Nontrivial k]

abbrev ActualIdealIndex (P : QuotientGroebnerData V k) (p : ℕ) :=
  Σ F : Set.powersetCard V p, NonstandardIndex P.order P.ideal

def actualIdealCoefficientBasis (P : QuotientGroebnerData V k) (p : ℕ) :
    Module.Basis (ActualIdealIndex P p) k (Set.powersetCard V p →₀ P.ideal) :=
  Finsupp.basis (fun _ => groebnerIdealBasis P.order P.ideal P.generators
    P.groebner P.unitLeading)

def actualIdealDegree {P : QuotientGroebnerData V k} {p : ℕ}
    (a : ActualIdealIndex P p) : Exponent V := a.2.val + faceExponent a.1.val

@[simp] theorem actualIdealCoefficientBasis_apply (P : QuotientGroebnerData V k)
    (p : ℕ) (a : ActualIdealIndex P p) :
    actualIdealCoefficientBasis P p a = Finsupp.single a.1
      (idealLift P.order P.ideal P.generators P.groebner P.unitLeading a.2) := by
  simp only [actualIdealCoefficientBasis, Finsupp.coe_basis, groebnerIdealBasis_apply]

@[simp] theorem actualIdealCoefficientBasis_repr (P : QuotientGroebnerData V k)
    (p : ℕ) (x : Set.powersetCard V p →₀ P.ideal) (a : ActualIdealIndex P p) :
    (actualIdealCoefficientBasis P p).repr x a = (x a.1).val.coeff a.2.val := by
  rw [actualIdealCoefficientBasis, Finsupp.basis_repr, groebnerIdealBasis_repr]

def actualIdealCoordinateFiltration (P : QuotientGroebnerData V k) (w : V → ℕ)
    (p : ℕ) : Filtration (K := k) (Set.powersetCard V p →₀ P.ideal) :=
  basisFiltration (actualIdealCoefficientBasis P p)
    (fun a => Finsupp.weight w (actualIdealDegree a))

/-- A triangular ideal basis vector has no ambient terms of larger
coefficient-plus-exterior weight. -/
theorem idealCoordinatesToAmbient_basis_weight
    (P : QuotientGroebnerData V k) (w : V → ℕ)
    (htail : ∀ g ∈ P.generators, g ≠ 0 →
      ∀ a ∈ (monomial (P.order.degree g) 1-g).support,
        Finsupp.weight w a < Finsupp.weight w (P.order.degree g))
    (p : ℕ) (a : ActualIdealIndex P p) (n : ℕ)
    (ha : Finsupp.weight w (actualIdealDegree a) < n) :
    idealCoordinatesToAmbient P.ideal p (actualIdealCoefficientBasis P p a) ∈
      (quotientCoordinateFiltration (∅ : Family V) w p).level n := by
  rw [quotientCoordinateFiltration, basisFiltration_mem]
  intro b hb
  rw [idealCoordinatesToAmbient_repr, actualIdealCoefficientBasis_apply]
  by_cases hF : a.1 = b.1
  · rw [Finsupp.single_apply, if_pos hF]
    change (monomial a.2.val (1 : k) -
      P.groebner.normalForm P.unitLeading (monomial a.2.val 1)).coeff b.2.val = 0
    have hw : Finsupp.weight w a.2.val < Finsupp.weight w b.2.val := by
      simp only [actualIdealDegree, quotientDegree, map_add, hF] at ha hb
      omega
    rw [coeff_sub, coeff_monomial, if_neg (by
      intro hab
      exact (lt_irrefl _) (hab ▸ hw)), zero_sub, neg_eq_zero]
    by_contra hc
    have hnf := groebner_normalForm_strictly_lowers_of_tails P.order P.ideal
      P.generators P.groebner P.unitLeading w htail a.2.val a.2.property
    have hlt := (mem_restrictSupport_iff k).mp hnf (mem_support_iff.mpr hc)
    exact (lt_asymm hw hlt)
  · rw [Finsupp.single_apply, if_neg hF]
    rfl

/-- The actual ideal basis filtration agrees with the filtration induced
from its literal inclusion into the polynomial Koszul complex. -/
theorem actualIdealCoordinateFiltration_mem_iff
    (P : QuotientGroebnerData V k) (w : V → ℕ)
    (htail : ∀ g ∈ P.generators, g ≠ 0 →
      ∀ a ∈ (monomial (P.order.degree g) 1-g).support,
        Finsupp.weight w a < Finsupp.weight w (P.order.degree g))
    (p n : ℕ) (x : Set.powersetCard V p →₀ P.ideal) :
    x ∈ (actualIdealCoordinateFiltration P w p).level n ↔
      idealCoordinatesToAmbient P.ideal p x ∈
        (quotientCoordinateFiltration (∅ : Family V) w p).level n := by
  constructor
  · intro hx
    have hle : (actualIdealCoordinateFiltration P w p).level n ≤
        ((quotientCoordinateFiltration (∅ : Family V) w p).level n).comap
          (idealCoordinatesToAmbient P.ideal p) := by
      apply Submodule.span_le.mpr
      rintro y ⟨a, ha, rfl⟩
      exact idealCoordinatesToAmbient_basis_weight P w htail p a n ha
    exact hle hx
  · intro hx
    rw [actualIdealCoordinateFiltration, basisFiltration_mem]
    intro a ha
    have h := (basisFiltration_mem
      (quotientCoefficientBasis (k := k) (∅ : Family V) p)
      (fun b => Finsupp.weight w (quotientDegree b)) n
      (idealCoordinatesToAmbient P.ideal p x)).mp hx
      ⟨a.1, ⟨a.2.val, emptyFamily_allowed a.2.val⟩⟩ ha
    simpa only [idealCoordinatesToAmbient_repr, actualIdealCoefficientBasis_repr] using h

theorem actualIdealCoordinateFiltration_kernel_iff
    (P : QuotientGroebnerData V k) (w : V → ℕ)
    (htail : ∀ g ∈ P.generators, g ≠ 0 →
      ∀ a ∈ (monomial (P.order.degree g) 1-g).support,
        Finsupp.weight w a < Finsupp.weight w (P.order.degree g))
    (p n : ℕ) (x : Set.powersetCard V p →₀ P.ideal) :
    x ∈ (actualIdealCoordinateFiltration P w p).level n ↔
      idealCoordinatesKernelEquiv P p x ∈
        (kernelFiltration (quotientCoordinateFiltration (∅ : Family V) w p)
          (ambientKoszulProjection P p)).level n :=
  actualIdealCoordinateFiltration_mem_iff P w htail p n x

/-- Transport of actual kernel cycle lifts to the literal ideal Koszul
complex. Every map and filtration in the conclusion has been identified
coefficientwise above. -/
theorem actualIdealCoordinate_lifts_of_kernel
    (P : QuotientGroebnerData V k) (w : V → ℕ)
    (htail : ∀ g ∈ P.generators, g ≠ 0 →
      ∀ a ∈ (monomial (P.order.degree g) 1-g).support,
        Finsupp.weight w a < Finsupp.weight w (P.order.degree g))
    (p : ℕ)
    (hlift : LiftsCycles
      (kernelFiltration (quotientCoordinateFiltration ∅ w p) (ambientKoszulProjection P p))
      (kernelFiltration (quotientCoordinateFiltration ∅ w p.pred)
        (ambientKoszulProjection P p.pred)) (ambientKernelDifferential P p)) :
    LiftsCycles (actualIdealCoordinateFiltration P w p)
      (actualIdealCoordinateFiltration P w p.pred)
      (actualIdealPreviousDifferential P.ideal p) := by
  intro n x hx hdx
  have hx' := (actualIdealCoordinateFiltration_kernel_iff P w htail p (n+1) x).mp hx
  have hdx' := (actualIdealCoordinateFiltration_kernel_iff P w htail p.pred n
    (actualIdealPreviousDifferential P.ideal p x)).mp hdx
  rw [← idealCoordinatesKernelEquiv_differential] at hdx'
  obtain ⟨y, hy, hdy, herr⟩ := hlift n (idealCoordinatesKernelEquiv P p x) hx' hdx'
  let z := (idealCoordinatesKernelEquiv P p).symm y
  have he : idealCoordinatesKernelEquiv P p z = y :=
    LinearEquiv.apply_symm_apply _ y
  refine ⟨z, ?_, ?_, ?_⟩
  · exact (actualIdealCoordinateFiltration_kernel_iff P w htail p (n+1) z).mpr (by simpa only [he] using hy)
  · apply (idealCoordinatesKernelEquiv P p.pred).injective
    rw [map_zero, ← idealCoordinatesKernelEquiv_differential, he, hdy]
  · apply (actualIdealCoordinateFiltration_kernel_iff P w htail p n (x-z)).mpr
    have hsub := map_sub (idealCoordinatesKernelEquiv P p) x z
    rw [he] at hsub
    rw [hsub]
    exact herr

end Nontrivial

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Symmetric.Vendor.RingTheory.MvPolynomial.Groebner.Finite -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Finite Gröbner bases

Every ideal in a polynomial ring with finitely many variables over a Noetherian ring has a
finite Gröbner basis. More generally, any Gröbner basis contains a finite Gröbner basis whenever
its leading-term ideal is finitely generated. Over a field, rescaling the nonzero members gives
a finite monic Gröbner basis.

The extraction uses Mathlib's `Submodule.fg_span_iff_fg_span_finset_subset` and the Hilbert
basis theorem. These are existence results, without a choice of completion algorithm or a
claim that the resulting basis is reduced.

## References

* D. Cox, J. Little, D. O'Shea, *Ideals, Varieties, and Algorithms*, Chapter 2, §5:
  existence of finite Gröbner bases.
-/

section
namespace MonomialOrder

open MvPolynomial

variable {σ R : Type*} (m : MonomialOrder σ)

section CommSemiring

variable [CommSemiring R] {m} {G : Set (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)}

/-- A Gröbner basis contains a finite Gröbner basis if its leading-term ideal is finitely
generated. No finiteness assumption on the variable type or coefficient ring is needed here. -/
theorem IsGroebnerBasis.exists_finset_subset (h : m.IsGroebnerBasis G I)
    (hfg : (Ideal.span (m.leadingTerm '' (I : Set (MvPolynomial σ R)))).FG) :
    ∃ B : Finset (MvPolynomial σ R), (B : Set _) ⊆ G ∧ m.IsGroebnerBasis B I := by
  classical
  rw [h.span_leadingTerm_image] at hfg
  obtain ⟨T, hTG, hT⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset (m.leadingTerm '' G)).1 hfg
  obtain ⟨B, hBG, hBT⟩ := Finset.subset_set_image_iff.1 hTG
  refine ⟨B, hBG, .mk (hBG.trans h.subset) ?_⟩
  rw [h.span_leadingTerm_image]
  simpa only [← hBT, Finset.coe_image] using hT

end CommSemiring

section Noetherian

variable [CommRing R] [IsNoetherianRing R] [Finite σ]

/-- Every ideal over a Noetherian coefficient ring in finitely many variables has a finite
Gröbner basis, for any monomial order. -/
theorem exists_finset_isGroebnerBasis (I : Ideal (MvPolynomial σ R)) :
    ∃ G : Finset (MvPolynomial σ R), m.IsGroebnerBasis G I := by
  obtain ⟨G, -, hG⟩ := (m.isGroebnerBasis_self I).exists_finset_subset
    (IsNoetherian.noetherian _)
  exact ⟨G, hG⟩

end Noetherian

section Field

variable {k : Type*} [Field k] [Finite σ]

/-- Every ideal in finitely many variables over a field has a finite monic Gröbner basis.
All members are nonzero; for the zero ideal the empty basis is allowed. -/
theorem exists_finset_monic_isGroebnerBasis (I : Ideal (MvPolynomial σ k)) :
    ∃ G : Finset (MvPolynomial σ k), (∀ g ∈ G, m.Monic g) ∧ m.IsGroebnerBasis G I := by
  classical
  obtain ⟨B, hB⟩ := m.exists_finset_isGroebnerBasis I
  let normalize (p : MvPolynomial σ k) := C (m.leadingCoeff p)⁻¹ * p
  have hdegree (p : MvPolynomial σ k) (hp : p ≠ 0) :
      m.degree (normalize p) = m.degree p := by
    dsimp only [normalize]
    rw [m.degree_mul (C_ne_zero.2 (inv_ne_zero (m.leadingCoeff_ne_zero_iff.2 hp))) hp,
      m.degree_C, zero_add]
  have hmonic (p : MvPolynomial σ k) (hp : p ≠ 0) : m.Monic (normalize p) := by
    simp [normalize, Monic, m.leadingCoeff_ne_zero_iff.2 hp]
  have hGmonic : ∀ g ∈ (B.erase 0).image normalize, m.Monic g := by
    intro g hg
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hg
    exact hmonic p (Finset.mem_erase.1 hp).1
  refine ⟨(B.erase 0).image normalize, hGmonic, ?_⟩
  apply (m.isGroebnerBasis_iff_forall_exists_degree_le_degree
    (fun g hg _ ↦ (hGmonic g hg).leadingCoeff_eq_one.symm ▸ isUnit_one)).2
  refine ⟨?_, ?_⟩
  · intro g hg
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hg
    exact I.mul_mem_left _ (hB.subset (Finset.mem_erase.1 hp).2)
  · intro p hp hp0
    obtain ⟨b, hb, hb0, hbp⟩ := hB.exists_degree_le_degree hp hp0
    exact ⟨normalize b, Finset.mem_image.2 ⟨b, Finset.mem_erase.2 ⟨hb0, hb⟩, rfl⟩,
      (hmonic b hb0).ne_zero, (hdegree b hb0) ▸ hbp⟩

end Field

end MonomialOrder

end
end

/- BEGIN EXACT BODY: FourPapers.Symmetric.Vendor.RingTheory.MvPolynomial.Groebner.Reduced -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Reduced monic Gröbner bases

A reduced monic Gröbner basis contains no zero polynomial, all its elements are monic, and
no monomial of any basis element is divisible by the leading monomial of another element.
The restriction applies to the entire support, including the leading monomial.

## Main results

* `MonomialOrder.IsReducedGroebnerBasis.eq`: two reduced monic Gröbner bases of the same ideal
  are equal as sets. The proof first matches their minimal leading exponents, then uses
  cancellation of equal monic leading terms to identify the polynomials.
* `MonomialOrder.IsGroebnerBasis.exists_isReducedGroebnerBasis`: an ideal with a Gröbner basis
  whose nonzero members have unit leading coefficients has a reduced monic Gröbner basis. Its
  elements are `X^a - r`, for `a` minimal for divisibility among the leading exponents of `I`
  and `r` a remainder of `X^a`.
* `MonomialOrder.existsUnique_isReducedGroebnerBasis`: over a field, every ideal has exactly
  one reduced monic Gröbner basis.
* `MonomialOrder.IsReducedGroebnerBasis.finite`: in finitely many variables a reduced monic
  Gröbner basis is finite, by Dickson's lemma.

Apart from finiteness, neither the variable type nor the bases need be finite. The coefficients
may be any commutative ring, including a ring with zero divisors; only the field corollaries
assume a field.

## References

* D. Cox, J. Little, D. O'Shea, *Ideals, Varieties, and Algorithms*, Chapter 2, §7,
  Theorem 5: existence and uniqueness of the reduced Gröbner basis.
-/

section
namespace MonomialOrder

open MvPolynomial

variable {σ R : Type*}

section CommSemiring

variable [CommSemiring R] {m : MonomialOrder σ}
  {G H : Set (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)}

/-- A reduced monic Gröbner basis of `I`: a Gröbner basis consisting of nonzero monic
polynomials, with every monomial of each element irreducible by all the other elements.
The nonzero condition is explicit so that the definition also works over the zero ring. -/
structure IsReducedGroebnerBasis (m : MonomialOrder σ) (G : Set (MvPolynomial σ R))
    (I : Ideal (MvPolynomial σ R)) : Prop where
  /-- The set is a Gröbner basis of the ideal. -/
  isGroebnerBasis : m.IsGroebnerBasis G I
  /-- Zero is not a basis element. -/
  ne_zero : ∀ g ∈ G, g ≠ 0
  /-- Every basis element has leading coefficient one. -/
  monic : ∀ g ∈ G, m.Monic g
  /-- No term of a basis element is divisible by another basis element's leading monomial. -/
  not_degree_le : ∀ g ∈ G, ∀ c ∈ g.support, ∀ h ∈ G, h ≠ g → ¬ m.degree h ≤ c

/-- In a reduced basis, divisibility between leading monomials forces the basis elements
to be equal. In particular the leading exponents are pairwise incomparable. -/
theorem IsReducedGroebnerBasis.eq_of_degree_le (hG : m.IsReducedGroebnerBasis G I)
    {g h : MvPolynomial σ R} (hg : g ∈ G) (hh : h ∈ G)
    (hle : m.degree h ≤ m.degree g) : h = g := by
  by_contra hne
  exact hG.not_degree_le g hg _ (m.degree_mem_support (hG.ne_zero g hg)) h hh hne hle

/-- Every leading exponent of a reduced basis occurs in any Gröbner basis of the same ideal.
This expresses minimality of its leading exponents, without assuming the other basis is
reduced or monic. -/
theorem IsReducedGroebnerBasis.exists_degree_eq (hG : m.IsReducedGroebnerBasis G I)
    (hH : m.IsGroebnerBasis H I) {g : MvPolynomial σ R} (hg : g ∈ G) :
    ∃ h ∈ H, h ≠ 0 ∧ m.degree h = m.degree g := by
  obtain ⟨h, hh, hh0, hhg⟩ := hH.exists_degree_le_degree
    (hG.isGroebnerBasis.subset hg) (hG.ne_zero g hg)
  obtain ⟨g', hg', _, hg'h⟩ := hG.isGroebnerBasis.exists_degree_le_degree (hH.subset hh) hh0
  have heq := hG.eq_of_degree_le hg hg' (hg'h.trans hhg)
  subst g'
  exact ⟨h, hh, hh0, le_antisymm hhg hg'h⟩

/-- The empty set is a reduced monic Gröbner basis of the zero ideal. -/
@[simp]
theorem isReducedGroebnerBasis_empty (m : MonomialOrder σ) :
    m.IsReducedGroebnerBasis (∅ : Set (MvPolynomial σ R)) ⊥ := by
  refine ⟨IsGroebnerBasis.mk (Set.empty_subset _) ?_, by simp, by simp, by simp⟩
  simp

/-- A reduced monic Gröbner basis is empty exactly when its ideal is zero. -/
theorem IsReducedGroebnerBasis.eq_empty_iff (hG : m.IsReducedGroebnerBasis G I) :
    G = ∅ ↔ I = ⊥ := by
  constructor
  · intro h
    rw [Submodule.eq_bot_iff]
    intro p hp
    by_contra hp0
    obtain ⟨g, hg, _⟩ := hG.isGroebnerBasis.exists_degree_le_degree hp hp0
    simp [h] at hg
  · intro h
    apply Set.eq_empty_of_forall_notMem
    intro g hg
    apply hG.ne_zero g hg
    simpa [h] using hG.isGroebnerBasis.subset hg

/-- **Finiteness of reduced Gröbner bases.** In finitely many variables a reduced monic
Gröbner basis is finite. -/
theorem IsReducedGroebnerBasis.finite [Finite σ] (hG : m.IsReducedGroebnerBasis G I) :
    G.Finite := by
  have hinj : Set.InjOn m.degree G := fun _ hg _ hh hgh ↦ hG.eq_of_degree_le hh hg hgh.le
  refine Set.Finite.of_finite_image ?_ hinj
  refine WellQuasiOrderedLE.finite_of_isAntichain ?_
  rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩ hne hle
  exact hne (congrArg m.degree (hG.eq_of_degree_le hh hg hle))

end CommSemiring

section CommRing

variable [CommRing R] {m : MonomialOrder σ}
  {G H : Set (MvPolynomial σ R)} {I J : Ideal (MvPolynomial σ R)}

/-- Elements of two reduced monic Gröbner bases of the same ideal with the same leading
exponent are equal. -/
theorem IsReducedGroebnerBasis.eq_of_degree_eq (hG : m.IsReducedGroebnerBasis G I)
    (hH : m.IsReducedGroebnerBasis H I) {g h : MvPolynomial σ R} (hg : g ∈ G) (hh : h ∈ H)
    (hdeg : m.degree g = m.degree h) : g = h := by
  classical
  by_contra hne
  have hdiff : g - h ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨b, hb, _, hbd⟩ := hG.isGroebnerBasis.exists_degree_le_degree
    (I.sub_mem (hG.isGroebnerBasis.subset hg) (hH.isGroebnerBasis.subset hh)) hdiff
  have htop : m.degree g ≤ m.degree (g - h) := by
    rcases Finset.mem_union.mp (support_sub σ g h (m.degree_mem_support hdiff)) with hc | hc
    · have hbg : b = g := by
        by_contra hbg
        exact hG.not_degree_le g hg _ hc b hb hbg hbd
      simpa [hbg] using hbd
    · obtain ⟨b', hb', _, hb'd⟩ := hG.exists_degree_eq hH.isGroebnerBasis hb
      have hb'h : b' = h := by
        by_contra hb'h
        exact hH.not_degree_le h hh _ hc b' hb' hb'h (hb'd ▸ hbd)
      rwa [← hb'd, hb'h, ← hdeg] at hbd
  have heq : m.degree (g - h) = m.degree g := m.toSyn.injective <|
    le_antisymm (by simpa [hdeg] using (m.degree_sub_le (f := g) (g := h)))
      (m.toSyn_monotone htop)
  have hz : (g - h).coeff (m.degree g) = 0 := by
    rw [coeff_sub, (hG.monic g hg).coeff_degree, hdeg, (hH.monic h hh).coeff_degree,
      sub_self]
  exact (mem_support_iff.mp (heq ▸ m.degree_mem_support hdiff)) hz

/-- **Uniqueness of the reduced monic Gröbner basis.** Any two reduced monic Gröbner bases
of the same ideal are equal, over an arbitrary commutative coefficient ring. -/
theorem IsReducedGroebnerBasis.eq (hG : m.IsReducedGroebnerBasis G I)
    (hH : m.IsReducedGroebnerBasis H I) : G = H := by
  apply Set.Subset.antisymm
  · intro g hg
    obtain ⟨h, hh, _, hdeg⟩ := hG.exists_degree_eq hH.isGroebnerBasis hg
    exact (hG.eq_of_degree_eq hH hg hh hdeg.symm) ▸ hh
  · intro h hh
    obtain ⟨g, hg, _, hdeg⟩ := hH.exists_degree_eq hG.isGroebnerBasis hh
    exact (hH.eq_of_degree_eq hG hh hg hdeg.symm) ▸ hg

/-- Reduced monic Gröbner bases agree exactly when the ideals they describe agree. -/
theorem IsReducedGroebnerBasis.eq_iff_ideal_eq (hG : m.IsReducedGroebnerBasis G I)
    (hH : m.IsReducedGroebnerBasis H J) : G = H ↔ I = J := by
  refine ⟨fun h ↦ ?_, fun h ↦ hG.eq (h ▸ hH)⟩
  rw [hG.isGroebnerBasis.ideal_eq_span, hH.isGroebnerBasis.ideal_eq_span, h]

/-- **Existence of the reduced monic Gröbner basis.** An ideal with a Gröbner basis whose
nonzero members have unit leading coefficients has a reduced monic Gröbner basis.

For each exponent `a` minimal, for divisibility, among the leading exponents of nonzero elements
of `I`, the basis element is `X^a - r`, where `r` is a remainder of `X^a` on division by `G`. -/
theorem IsGroebnerBasis.exists_isReducedGroebnerBasis (h : m.IsGroebnerBasis G I)
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) :
    ∃ H, m.IsReducedGroebnerBasis H I := by
  classical
  -- The leading exponents of the nonzero elements of `I`.
  let D : Set (σ →₀ ℕ) := m.degree '' {p | p ∈ I ∧ p ≠ 0}
  choose r hr using fun a : σ →₀ ℕ ↦ exists_isRemainder hG (monomial a (1 : R))
  let red (a : σ →₀ ℕ) : MvPolynomial σ R := monomial a 1 - r a
  have hred {a : σ →₀ ℕ} (ha : a ∈ D) :
      red a ∈ I ∧ red a ≠ 0 ∧ m.degree (red a) = a ∧ m.Monic (red a) := by
    obtain ⟨p, ⟨hp, hp0⟩, rfl⟩ := ha
    exact h.monic_monomial_sub_of_isRemainder (hr _) hp hp0 rfl
  refine ⟨red '' {a | Minimal (· ∈ D) a}, ⟨?_, ?_, ?_, ?_⟩⟩
  · refine (isGroebnerBasis_iff_forall_exists_degree_le_degree ?_).2 ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ -
      rw [(hred ha.prop).2.2.2.leadingCoeff_eq_one]
      exact isUnit_one
    · rintro _ ⟨a, ha, rfl⟩
      exact (hred ha.prop).1
    · intro p hp hp0
      obtain ⟨a, hap, ha⟩ := exists_minimal_le_of_wellFoundedLT (· ∈ D) (m.degree p)
        ⟨p, ⟨hp, hp0⟩, rfl⟩
      exact ⟨red a, ⟨a, ha, rfl⟩, (hred ha.prop).2.1, by rw [(hred ha.prop).2.2.1]; exact hap⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact (hred ha.prop).2.1
  · rintro _ ⟨a, ha, rfl⟩
    exact (hred ha.prop).2.2.2
  · rintro _ ⟨a, ha, rfl⟩ c hc _ ⟨b, hb, rfl⟩ hne hle
    rw [(hred hb.prop).2.2.1] at hle
    rcases Finset.mem_union.1 (support_sub σ _ _ hc) with hc | hc
    · -- The other leading exponent divides `a`, so by minimality of `a` the two are equal.
      rw [Finset.mem_singleton.1 (support_monomial_subset hc)] at hle
      exact hne (congrArg red (le_antisymm hle (ha.le_of_le hb.prop hle)))
    · obtain ⟨q, ⟨hq, hq0⟩, hqb⟩ := hb.prop
      exact h.not_degree_le_of_isRemainder (hr a) hc hq hq0 (hqb ▸ hle)

end CommRing

section Field

variable {k : Type*} [Field k]

/-- Over a field, every ideal has a reduced monic Gröbner basis. -/
theorem exists_isReducedGroebnerBasis (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ k)) :
    ∃ G, m.IsReducedGroebnerBasis G I :=
  (isGroebnerBasis_self I).exists_isReducedGroebnerBasis fun _ _ hg ↦ m.isUnit_leadingCoeff.2 hg

/-- Over a field, every ideal has exactly one reduced monic Gröbner basis. -/
theorem existsUnique_isReducedGroebnerBasis (m : MonomialOrder σ)
    (I : Ideal (MvPolynomial σ k)) : ∃! G, m.IsReducedGroebnerBasis G I :=
  let ⟨G, hG⟩ := m.exists_isReducedGroebnerBasis I
  ⟨G, hG, fun _ hH ↦ hH.eq hG⟩

end Field

end MonomialOrder

end
end

/- BEGIN EXACT BODY: FourPapers.Symmetric.Vendor.RingTheory.MvPolynomial.Groebner.Homogeneous -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Gröbner bases of homogeneous ideals

Let `w : σ → M` be a weight with values in an additive commutative monoid, which grades
`MvPolynomial σ R` by `MvPolynomial.weightedHomogeneousSubmodule R w` (for `w = 1` this is the
grading by total degree), and let `m` be any monomial order. The leading monomial of `f` lies in
the weighted homogeneous component of `f` of weight `weight w (m.degree f)`, and that component
has the same leading term as `f`
(`MonomialOrder.leadingTerm_weightedHomogeneousComponent_weight_degree`). So for an ideal `I`
which is homogeneous for this grading, replacing each member of a Gröbner basis by this component
gives a Gröbner basis of `I` consisting of weighted homogeneous polynomials, the reduced monic
Gröbner basis of `I` consists of weighted homogeneous polynomials, and the normal form modulo `I`
preserves weighted homogeneous components.

Consequently the image of each weighted homogeneous piece in the quotient `MvPolynomial σ R ⧸ I`
has a basis of the standard monomials of that weight. Since an ideal and its ideal of leading
terms have the same standard monomials, this piece is linearly isomorphic to the corresponding
piece for the ideal of leading terms: over a field, every graded piece of the quotient has the same
dimension as for the initial monomial ideal. No monomial order is assumed to be compatible with
the weight.

## Main results

* `MonomialOrder.IsGroebnerBasis.image_weightedHomogeneousComponent`: the weighted homogeneous
  components containing the leading monomials of the members of a Gröbner basis of a homogeneous
  ideal form a Gröbner basis of the same ideal.
* `MonomialOrder.isHomogeneous_iff_exists_isGroebnerBasis_isWeightedHomogeneous`: an ideal is
  homogeneous if and only if it has a Gröbner basis of weighted homogeneous polynomials, and
  `MonomialOrder.exists_finset_isGroebnerBasis_isWeightedHomogeneous` provides a finite one over a
  Noetherian ring in finitely many variables.
* `MonomialOrder.IsReducedGroebnerBasis.isWeightedHomogeneous`: the members of the reduced monic
  Gröbner basis of a homogeneous ideal are weighted homogeneous.
* `MonomialOrder.IsGroebnerBasis.normalForm_weightedHomogeneousComponent`: the normal form
  commutes with weighted homogeneous components.
* `MonomialOrder.IsGroebnerBasis.basisMapWeightedHomogeneousSubmodule`: the standard monomials of
  weight `n` give a basis of the image of the weight `n` piece in the quotient.
* `MonomialOrder.IsGroebnerBasis.mapWeightedHomogeneousSubmoduleEquivSpanLeadingTerm` and
  `MonomialOrder.finrank_map_weightedHomogeneousSubmodule_span_leadingTerm`: these pieces are the
  same for `I` and for its ideal of leading terms.

## References

* D. Cox, J. Little, D. O'Shea, *Ideals, Varieties, and Algorithms*, Chapter 8, §3, Theorem 2
  (reduced Gröbner bases of homogeneous ideals), and Chapter 9, §3, Proposition 9 (the Hilbert
  function of an ideal and of its ideal of leading terms).
* B. Sturmfels, *Gröbner Bases and Convex Polytopes*, University Lecture Series 8, AMS, 1996,
  Chapter 1.
-/

section
namespace MonomialOrder

open MvPolynomial Finsupp

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {σ R M : Type*} [AddCommMonoid M] {m : MonomialOrder σ} (w : σ → M)

section CommSemiring

variable [CommSemiring R]

variable [DecidableEq M] {w} {G : Set (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)}

/-- Let `I` be homogeneous for the grading by the weight `w`. Replacing each member `g` of a
Gröbner basis of `I` by its weighted homogeneous component of the weight of its leading monomial
gives a Gröbner basis of `I`. -/
theorem IsGroebnerBasis.image_weightedHomogeneousComponent
    (hI : I.IsHomogeneous (weightedHomogeneousSubmodule R w)) (h : m.IsGroebnerBasis G I) :
    m.IsGroebnerBasis ((fun g ↦ weightedHomogeneousComponent w (weight w (m.degree g)) g) '' G)
      I := by
  refine .mk ?_ ?_
  · rintro _ ⟨g, hg, rfl⟩
    exact weightedHomogeneousComponent_mem_of_mem R w hI (h.subset hg) _
  · rw [Set.image_image]
    simpa using h.span_leadingTerm_image

/-- An ideal which is homogeneous for the grading by the weight `w` has a Gröbner basis
consisting of weighted homogeneous polynomials. -/
theorem exists_isGroebnerBasis_isWeightedHomogeneous
    (hI : I.IsHomogeneous (weightedHomogeneousSubmodule R w)) :
    ∃ G, m.IsGroebnerBasis G I ∧ ∀ g ∈ G, IsWeightedHomogeneous w g (weight w (m.degree g)) :=
  ⟨_, (isGroebnerBasis_self I).image_weightedHomogeneousComponent hI, by
    rintro _ ⟨g, -, rfl⟩
    exact m.isWeightedHomogeneous_weightedHomogeneousComponent_weight_degree w g⟩

/-- The ideal of leading terms is homogeneous for the grading by every weight. -/
theorem isHomogeneous_span_leadingTerm (w : σ → M) (I : Ideal (MvPolynomial σ R)) :
    (Ideal.span (m.leadingTerm '' I)).IsHomogeneous (weightedHomogeneousSubmodule R w) :=
  Ideal.homogeneous_span _ _ <| by
    rintro _ ⟨p, -, rfl⟩
    exact ⟨_, isWeightedHomogeneous_monomial w _ _ rfl⟩

end CommSemiring

section CommRing

variable [CommRing R] [DecidableEq M] {w} {G : Set (MvPolynomial σ R)}
  {I : Ideal (MvPolynomial σ R)}

/-- An ideal with a Gröbner basis consisting of weighted homogeneous polynomials is homogeneous. -/
theorem IsGroebnerBasis.isHomogeneous (h : m.IsGroebnerBasis G I)
    (hG : ∀ g ∈ G, ∃ n, IsWeightedHomogeneous w g n) :
    I.IsHomogeneous (weightedHomogeneousSubmodule R w) := by
  rw [h.ideal_eq_span]
  exact Ideal.homogeneous_span _ _ hG

/-- **Gröbner bases of homogeneous ideals.** An ideal is homogeneous for the grading by the weight
`w` if and only if it has a Gröbner basis consisting of weighted homogeneous polynomials. -/
theorem isHomogeneous_iff_exists_isGroebnerBasis_isWeightedHomogeneous :
    I.IsHomogeneous (weightedHomogeneousSubmodule R w) ↔
      ∃ G, m.IsGroebnerBasis G I ∧ ∀ g ∈ G, IsWeightedHomogeneous w g (weight w (m.degree g)) :=
  ⟨exists_isGroebnerBasis_isWeightedHomogeneous, fun ⟨_, h, hG⟩ ↦
    h.isHomogeneous fun g hg ↦ ⟨_, hG g hg⟩⟩

/-- Over a Noetherian ring in finitely many variables, an ideal which is homogeneous for the
grading by the weight `w` has a finite Gröbner basis consisting of weighted homogeneous
polynomials. -/
theorem exists_finset_isGroebnerBasis_isWeightedHomogeneous [IsNoetherianRing R] [Finite σ]
    (hI : I.IsHomogeneous (weightedHomogeneousSubmodule R w)) :
    ∃ G : Finset (MvPolynomial σ R), m.IsGroebnerBasis G I ∧
      ∀ g ∈ G, IsWeightedHomogeneous w g (weight w (m.degree g)) := by
  classical
  obtain ⟨G, hG⟩ := m.exists_finset_isGroebnerBasis I
  refine ⟨G.image fun g ↦ weightedHomogeneousComponent w (weight w (m.degree g)) g, ?_, ?_⟩
  · rw [Finset.coe_image]
    exact hG.image_weightedHomogeneousComponent hI
  · intro g hg
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 hg
    exact m.isWeightedHomogeneous_weightedHomogeneousComponent_weight_degree w g

/-- The members of a reduced monic Gröbner basis of an ideal which is homogeneous for the grading by
the weight `w` are weighted homogeneous. -/
theorem IsReducedGroebnerBasis.isWeightedHomogeneous (hG : m.IsReducedGroebnerBasis G I)
    (hI : I.IsHomogeneous (weightedHomogeneousSubmodule R w)) {g : MvPolynomial σ R}
    (hg : g ∈ G) : IsWeightedHomogeneous w g (weight w (m.degree g)) := by
  set φ := fun g : MvPolynomial σ R ↦ weightedHomogeneousComponent w (weight w (m.degree g)) g
  -- The weighted homogeneous components `φ g` again form a reduced monic Gröbner basis of `I`,
  -- so by uniqueness they are the members of `G`.
  have hφ : m.IsReducedGroebnerBasis (φ '' G) I := by
    refine ⟨hG.isGroebnerBasis.image_weightedHomogeneousComponent hI, ?_, ?_, ?_⟩
    · rintro _ ⟨g, hg, rfl⟩
      rw [← m.leadingCoeff_ne_zero_iff, leadingCoeff_weightedHomogeneousComponent_weight_degree,
        m.leadingCoeff_ne_zero_iff]
      exact hG.ne_zero g hg
    · rintro _ ⟨g, hg, rfl⟩
      exact (m.leadingCoeff_weightedHomogeneousComponent_weight_degree w g).trans (hG.monic g hg)
    · classical
      rintro _ ⟨g, hg, rfl⟩ c hc _ ⟨h, hh, rfl⟩ hne
      rw [degree_weightedHomogeneousComponent_weight_degree]
      rw [support_weightedHomogeneousComponent] at hc
      exact hG.not_degree_le g hg c (Finset.mem_filter.1 hc).1 h hh (by rintro rfl; exact hne rfl)
  obtain ⟨g, -, rfl⟩ := (hG.eq hφ ▸ hg : g ∈ φ '' G)
  exact m.isWeightedHomogeneous_weightedHomogeneousComponent_weight_degree w g

variable (h : m.IsGroebnerBasis G I) (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g))
  (hI : I.IsHomogeneous (weightedHomogeneousSubmodule R w))

include h hG hI

/-- For an ideal which is homogeneous for the grading by the weight `w`, the normal form commutes
with taking weighted homogeneous components. -/
theorem IsGroebnerBasis.normalForm_weightedHomogeneousComponent (n : M) (f : MvPolynomial σ R) :
    h.normalForm hG (weightedHomogeneousComponent w n f) =
      weightedHomogeneousComponent w n (h.normalForm hG f) := by
  classical
  refine (h.normalForm_eq_iff hG).2 ⟨?_, ?_⟩
  · have hf := (mem_restrictSupport_iff R).1 (h.normalForm_mem_restrictSupport hG f)
    rw [mem_restrictSupport_iff, support_weightedHomogeneousComponent, Finset.coe_filter]
    exact fun c hc ↦ hf hc.1
  · rw [← map_sub]
    exact weightedHomogeneousComponent_mem_of_mem R w hI (h.sub_normalForm_mem hG f) n

/-- For an ideal which is homogeneous for the grading by the weight `w`, the normal form of a
weighted homogeneous polynomial is weighted homogeneous of the same weight. -/
theorem IsGroebnerBasis.isWeightedHomogeneous_normalForm {n : M} {f : MvPolynomial σ R}
    (hf : IsWeightedHomogeneous w f n) : IsWeightedHomogeneous w (h.normalForm hG f) n := by
  rw [← weightedHomogeneousComponent_eq_self hf, h.normalForm_weightedHomogeneousComponent hG hI]
  exact weightedHomogeneousComponent_isWeightedHomogeneous _ _

/-- For an ideal `I` which is homogeneous for the grading by the weight `w`, the quotient map
restricts to a linear isomorphism from the polynomials supported on the standard monomials of `I`
of weight `n` onto the image in `MvPolynomial σ R ⧸ I` of the weighted homogeneous polynomials of
weight `n`. -/
noncomputable def IsGroebnerBasis.restrictSupportEquivMapWeightedHomogeneousSubmodule (n : M) :
    restrictSupport R (m.standardMonomials I ∩ {c | weight w c = n}) ≃ₗ[R]
      (weightedHomogeneousSubmodule R w n).map (Ideal.Quotient.mkₐ R I).toLinearMap :=
  LinearEquiv.ofBijective
    (LinearMap.codRestrict
      ((weightedHomogeneousSubmodule R w n).map (Ideal.Quotient.mkₐ R I).toLinearMap)
      ((Ideal.Quotient.mkₐ R I).toLinearMap ∘ₗ Submodule.subtype _)
      fun r ↦ Submodule.mem_map_of_mem <| by
        rw [weightedHomogeneousSubmodule_eq_finsupp_supported]
        exact restrictSupport_mono R Set.inter_subset_right r.2)
    ⟨fun r₁ r₂ hr ↦ Subtype.ext <| eq_of_sub_mem_of_mem_restrictSupport
        (restrictSupport_mono R Set.inter_subset_left r₁.2)
        (restrictSupport_mono R Set.inter_subset_left r₂.2)
        (Ideal.Quotient.eq.1 (congrArg Subtype.val hr)),
      by
        rintro ⟨_, f, hf, rfl⟩
        refine ⟨⟨h.normalForm hG f, ?_⟩, Subtype.ext (h.mk_normalForm hG f)⟩
        have h₁ := (mem_restrictSupport_iff R).1 (h.normalForm_mem_restrictSupport hG f)
        have h₂ :=
          h.isWeightedHomogeneous_normalForm hG hI ((mem_weightedHomogeneousSubmodule ..).1 hf)
        rw [mem_restrictSupport_iff]
        exact fun c hc ↦ ⟨h₁ hc, h₂ (MvPolynomial.mem_support_iff.1 hc)⟩⟩

/-- `MonomialOrder.IsGroebnerBasis.restrictSupportEquivMapWeightedHomogeneousSubmodule` is the
quotient map. -/
@[simp]
theorem IsGroebnerBasis.restrictSupportEquivMapWeightedHomogeneousSubmodule_apply_coe (n : M)
    (r : restrictSupport R (m.standardMonomials I ∩ {c | weight w c = n})) :
    (h.restrictSupportEquivMapWeightedHomogeneousSubmodule hG hI n r : MvPolynomial σ R ⧸ I) =
      Ideal.Quotient.mk I (r : MvPolynomial σ R) :=
  (rfl)

/-- The inverse of
`MonomialOrder.IsGroebnerBasis.restrictSupportEquivMapWeightedHomogeneousSubmodule` sends the
class of `f` to the normal form of `f`. -/
@[simp]
theorem IsGroebnerBasis.coe_restrictSupportEquivMapWeightedHomogeneousSubmodule_symm_mk (n : M)
    {f : MvPolynomial σ R}
    (hf : Ideal.Quotient.mk I f ∈
      (weightedHomogeneousSubmodule R w n).map (Ideal.Quotient.mkₐ R I).toLinearMap) :
    ((h.restrictSupportEquivMapWeightedHomogeneousSubmodule hG hI n).symm
        ⟨Ideal.Quotient.mk I f, hf⟩ : MvPolynomial σ R) = h.normalForm hG f := by
  set r := (h.restrictSupportEquivMapWeightedHomogeneousSubmodule hG hI n).symm
    ⟨Ideal.Quotient.mk I f, hf⟩
  have hr := congrArg Subtype.val
    ((h.restrictSupportEquivMapWeightedHomogeneousSubmodule hG hI n).apply_symm_apply
      ⟨Ideal.Quotient.mk I f, hf⟩)
  rw [restrictSupportEquivMapWeightedHomogeneousSubmodule_apply_coe] at hr
  exact ((h.normalForm_eq_iff hG).2
    ⟨restrictSupport_mono R Set.inter_subset_left r.2, Ideal.Quotient.eq.1 hr.symm⟩).symm

/-- **The graded standard monomial basis.** For an ideal `I` which is homogeneous for the grading
by the weight `w`, the images of the standard monomials of `I` of weight `n` form a basis of the
image in `MvPolynomial σ R ⧸ I` of the weighted homogeneous polynomials of weight `n`. -/
noncomputable def IsGroebnerBasis.basisMapWeightedHomogeneousSubmodule (n : M) :
    Module.Basis ↥(m.standardMonomials I ∩ {c | weight w c = n}) R
      ((weightedHomogeneousSubmodule R w n).map (Ideal.Quotient.mkₐ R I).toLinearMap) :=
  (basisRestrictSupport R _).map (h.restrictSupportEquivMapWeightedHomogeneousSubmodule hG hI n)

/-- The basis vectors of `MonomialOrder.IsGroebnerBasis.basisMapWeightedHomogeneousSubmodule` are
the classes of the standard monomials. -/
@[simp]
theorem IsGroebnerBasis.basisMapWeightedHomogeneousSubmodule_apply_coe (n : M)
    (c : ↥(m.standardMonomials I ∩ {c | weight w c = n})) :
    (h.basisMapWeightedHomogeneousSubmodule hG hI n c : MvPolynomial σ R ⧸ I) =
      Ideal.Quotient.mk I (monomial (c : σ →₀ ℕ) 1) := by
  simp [basisMapWeightedHomogeneousSubmodule]

/-- The coordinates of a class in
`MonomialOrder.IsGroebnerBasis.basisMapWeightedHomogeneousSubmodule` are the coefficients of the
normal form of any representative. -/
@[simp]
theorem IsGroebnerBasis.basisMapWeightedHomogeneousSubmodule_repr_mk (n : M)
    {f : MvPolynomial σ R}
    (hf : Ideal.Quotient.mk I f ∈
      (weightedHomogeneousSubmodule R w n).map (Ideal.Quotient.mkₐ R I).toLinearMap)
    (c : ↥(m.standardMonomials I ∩ {c | weight w c = n})) :
    (h.basisMapWeightedHomogeneousSubmodule hG hI n).repr ⟨Ideal.Quotient.mk I f, hf⟩ c =
      (h.normalForm hG f).coeff c := by
  simp [basisMapWeightedHomogeneousSubmodule]

/-- **The Hilbert function of the ideal of leading terms.** For an ideal `I` which is homogeneous
for the grading by the weight `w`, the images of the weighted homogeneous polynomials of weight `n`
in `MvPolynomial σ R ⧸ I` and in the quotient by the ideal of leading terms of `I` are linearly
isomorphic. -/
noncomputable def IsGroebnerBasis.mapWeightedHomogeneousSubmoduleEquivSpanLeadingTerm (n : M) :
    (weightedHomogeneousSubmodule R w n).map (Ideal.Quotient.mkₐ R I).toLinearMap ≃ₗ[R]
      (weightedHomogeneousSubmodule R w n).map
        (Ideal.Quotient.mkₐ R (Ideal.span (m.leadingTerm '' I))).toLinearMap :=
  (h.restrictSupportEquivMapWeightedHomogeneousSubmodule hG hI n).symm ≪≫ₗ
    LinearEquiv.ofEq _ _ (by rw [standardMonomials_span_leadingTerm]) ≪≫ₗ
    (h.image_leadingTerm hG).restrictSupportEquivMapWeightedHomogeneousSubmodule
      (isUnit_leadingCoeff_of_mem_image_leadingTerm hG) (isHomogeneous_span_leadingTerm w I) n

/-- `MonomialOrder.IsGroebnerBasis.mapWeightedHomogeneousSubmoduleEquivSpanLeadingTerm` sends the
class of `f` modulo `I` to the class of the normal form of `f` modulo the ideal of leading terms. -/
@[simp]
theorem IsGroebnerBasis.mapWeightedHomogeneousSubmoduleEquivSpanLeadingTerm_apply_coe (n : M)
    {f : MvPolynomial σ R}
    (hf : Ideal.Quotient.mk I f ∈
      (weightedHomogeneousSubmodule R w n).map (Ideal.Quotient.mkₐ R I).toLinearMap) :
    (h.mapWeightedHomogeneousSubmoduleEquivSpanLeadingTerm hG hI n ⟨Ideal.Quotient.mk I f, hf⟩ :
        MvPolynomial σ R ⧸ Ideal.span (m.leadingTerm '' (I : Set (MvPolynomial σ R)))) =
      Ideal.Quotient.mk (Ideal.span (m.leadingTerm '' I)) (h.normalForm hG f) := by
  simp [mapWeightedHomogeneousSubmoduleEquivSpanLeadingTerm]

/-- The inverse of
`MonomialOrder.IsGroebnerBasis.mapWeightedHomogeneousSubmoduleEquivSpanLeadingTerm` sends the
class of `f` modulo the ideal of leading terms to the class modulo `I` of the normal form of `f`
for the leading terms of `G`. -/
@[simp]
theorem IsGroebnerBasis.mapWeightedHomogeneousSubmoduleEquivSpanLeadingTerm_symm_apply_coe (n : M)
    {f : MvPolynomial σ R}
    (hf : Ideal.Quotient.mk (Ideal.span (m.leadingTerm '' (I : Set (MvPolynomial σ R)))) f ∈
      (weightedHomogeneousSubmodule R w n).map
        (Ideal.Quotient.mkₐ R (Ideal.span (m.leadingTerm '' I))).toLinearMap) :
    ((h.mapWeightedHomogeneousSubmoduleEquivSpanLeadingTerm hG hI n).symm
        ⟨Ideal.Quotient.mk (Ideal.span (m.leadingTerm '' (I : Set (MvPolynomial σ R)))) f, hf⟩ :
          MvPolynomial σ R ⧸ I) =
      Ideal.Quotient.mk I
        ((h.image_leadingTerm hG).normalForm
          (isUnit_leadingCoeff_of_mem_image_leadingTerm hG) f) := by
  simp [mapWeightedHomogeneousSubmoduleEquivSpanLeadingTerm]

end CommRing

section Field

variable {k : Type*} [Field k] [DecidableEq M] {w} {I : Ideal (MvPolynomial σ k)}

/-- Over a field, for an ideal `I` which is homogeneous for the grading by the weight `w`, the
dimension of the image in `MvPolynomial σ k ⧸ I` of the weighted homogeneous polynomials of weight
`n` is the number of standard monomials of `I` of weight `n`. -/
theorem finrank_map_weightedHomogeneousSubmodule (m : MonomialOrder σ)
    (hI : I.IsHomogeneous (weightedHomogeneousSubmodule k w)) (n : M) :
    Module.finrank k
        ((weightedHomogeneousSubmodule k w n).map (Ideal.Quotient.mkₐ k I).toLinearMap) =
      Nat.card ↥(m.standardMonomials I ∩ {c | weight w c = n}) :=
  Module.finrank_eq_nat_card_basis <| (isGroebnerBasis_self I).basisMapWeightedHomogeneousSubmodule
    (fun _ _ hg ↦ m.isUnit_leadingCoeff.2 hg) hI n

/-- Over a field, an ideal `I` which is homogeneous for the grading by the weight `w` and its ideal
of leading terms have quotients whose weighted homogeneous pieces have the same dimensions. -/
theorem finrank_map_weightedHomogeneousSubmodule_span_leadingTerm
    (hI : I.IsHomogeneous (weightedHomogeneousSubmodule k w)) (n : M) :
    Module.finrank k ((weightedHomogeneousSubmodule k w n).map
        (Ideal.Quotient.mkₐ k (Ideal.span (m.leadingTerm '' I))).toLinearMap) =
      Module.finrank k
        ((weightedHomogeneousSubmodule k w n).map (Ideal.Quotient.mkₐ k I).toLinearMap) :=
  ((isGroebnerBasis_self I).mapWeightedHomogeneousSubmoduleEquivSpanLeadingTerm
    (fun _ _ hg ↦ m.isUnit_leadingCoeff.2 hg) hI n).finrank_eq.symm

end Field

end MonomialOrder

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphGradedIdealBasis -/
section

/-! # Homogeneous bases of the actual ideal and quotient

The triangular ideal basis `X^a - normalForm (X^a)` is homogeneous whenever
the ideal is homogeneous. Restricting it to any weight therefore gives a
basis of the actual intersection with that homogeneous polynomial component.
For a positive natural-number weight in finitely many variables, this basis
is finite. All statements are over the coefficient ring itself.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section

namespace FourPapers.Sublattice

open Classical MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {R V A : Type*} [CommRing R] [Nontrivial R]
  [AddCommMonoid A] [DecidableEq A]
  (m : MonomialOrder V) (J : Ideal (MvPolynomial V R))
  (G : Set (MvPolynomial V R)) (hG : m.IsGroebnerBasis G J)
  (hu : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g))
  (w : V → A)
  (hJ : J.IsHomogeneous (weightedHomogeneousSubmodule R w))

/-- The degree component is an actual submodule of the original ideal. -/
def idealWeightedComponent (q : A) : Submodule R J :=
  (weightedHomogeneousSubmodule R w q).comap (J.restrictScalars R).subtype

@[simp] lemma mem_idealWeightedComponent (q : A) (f : J) :
    f ∈ idealWeightedComponent J w q ↔ IsWeightedHomogeneous w f.val q :=
  Iff.rfl

include hJ in
theorem idealLift_isWeightedHomogeneous (a : NonstandardIndex m J) :
    IsWeightedHomogeneous w (idealLift m J G hG hu a).val
      (Finsupp.weight w a.val) := by
  have ha : IsWeightedHomogeneous w (monomial a.val (1 : R))
      (Finsupp.weight w a.val) := isWeightedHomogeneous_monomial w _ _ rfl
  exact ha.sub (hG.isWeightedHomogeneous_normalForm hu hJ ha)

include hJ in
/-- The basis grading agrees with the polynomial grading, including both
directions of the membership assertion. -/
theorem groebnerIdealBasis_piece_eq (q : A) :
    CommAlg.Grading.Piece (groebnerIdealBasis m J G hG hu)
      (fun a => Finsupp.weight w a.val) q = idealWeightedComponent J w q := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, rfl⟩
    change groebnerIdealBasis m J G hG hu a ∈ idealWeightedComponent J w q
    rw [mem_idealWeightedComponent, groebnerIdealBasis_apply]
    change Finsupp.weight w a.val = q at ha
    simpa only [ha] using idealLift_isWeightedHomogeneous m J G hG hu w hJ a
  · intro f hf
    rw [CommAlg.Grading.mem_piece]
    intro a ha
    rw [groebnerIdealBasis_repr] at ha
    exact hf ha

/-- The nonstandard monomials of weight `q`, lifted by the exact normal
form, form a basis of the actual weight-`q` ideal component. -/
def groebnerWeightedIdealBasis (q : A) :
    Module.Basis {a : NonstandardIndex m J // Finsupp.weight w a.val = q}
      R (idealWeightedComponent J w q) :=
  (CommAlg.Grading.restrictedBasis (groebnerIdealBasis m J G hG hu)
    (fun a => Finsupp.weight w a.val = q)).map
      (LinearEquiv.ofEq _ _ (groebnerIdealBasis_piece_eq m J G hG hu w hJ q))

@[simp] theorem groebnerWeightedIdealBasis_apply (q : A)
    (a : {a : NonstandardIndex m J // Finsupp.weight w a.val = q}) :
    (groebnerWeightedIdealBasis m J G hG hu w hJ q a).val.val =
      monomial a.val.val 1 - hG.normalForm hu (monomial a.val.val 1) := by
  change (CommAlg.Grading.restrictedBasis (groebnerIdealBasis m J G hG hu)
    (fun a => Finsupp.weight w a.val = q) a).val.val = _
  rw [CommAlg.Grading.restrictedBasis_val, groebnerIdealBasis_apply]
  rfl

include hG hu hJ in
theorem groebnerWeightedIdeal_free (q : A) :
    Module.Free R (idealWeightedComponent J w q) :=
  Module.Free.of_basis (groebnerWeightedIdealBasis m J G hG hu w hJ q)

/-- The quotient component is the actual image of the polynomial component
under the quotient map. -/
def quotientWeightedComponent (q : A) : Submodule R (MvPolynomial V R ⧸ J) :=
  (weightedHomogeneousSubmodule R w q).map (Ideal.Quotient.mkₐ R J).toLinearMap

include hG hu hJ in
theorem groebnerWeightedQuotient_free (q : A) :
    Module.Free R (quotientWeightedComponent J w q) :=
  Module.Free.of_basis (hG.basisMapWeightedHomogeneousSubmodule hu hJ q)

section FinitePieces

variable [Finite V]
  (v : V → ℕ) (hv : ∀ x, v x ≠ 0)
  (hJv : J.IsHomogeneous (weightedHomogeneousSubmodule R v))

include hv in
theorem groebnerWeightedIdealIndex_finite (q : ℕ) :
    Finite {a : NonstandardIndex m J // Finsupp.weight v a.val = q} := by
  letI : Finite {a : V →₀ ℕ // Finsupp.weight v a = q} :=
    (Finsupp.finite_of_nat_weight_eq v hv q).to_subtype
  apply Finite.of_injective
    (fun a : {a : NonstandardIndex m J // Finsupp.weight v a.val = q} =>
      (⟨a.val.val, a.property⟩ : {a : V →₀ ℕ // Finsupp.weight v a = q}))
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun c : {a : V →₀ ℕ // Finsupp.weight v a = q} => c.val) hab

include hG hu hv hJv in
theorem groebnerWeightedIdeal_finite (q : ℕ) :
    Module.Finite R (idealWeightedComponent J v q) := by
  letI := groebnerWeightedIdealIndex_finite m J v hv q
  exact Module.Finite.of_basis (groebnerWeightedIdealBasis m J G hG hu v hJv q)

include hG hu hv hJv in
theorem groebnerWeightedQuotient_finite (q : ℕ) :
    Module.Finite R (quotientWeightedComponent J v q) := by
  have hfinite : (m.standardMonomials J ∩ {a : V →₀ ℕ | Finsupp.weight v a = q}).Finite :=
    (Finsupp.finite_of_nat_weight_eq v hv q).subset Set.inter_subset_right
  letI := hfinite.to_subtype
  exact Module.Finite.of_basis (hG.basisMapWeightedHomogeneousSubmodule hu hJv q)

include hG hu hv hJv in
/-- Both the ideal and its quotient are free over the coefficient ring,
with finite bases in every positive weighted degree. -/
theorem groebnerWeightedPieces_finite_free (q : ℕ) :
    (Module.Free R (idealWeightedComponent J v q) ∧
      Module.Finite R (idealWeightedComponent J v q)) ∧
    (Module.Free R (quotientWeightedComponent J v q) ∧
      Module.Finite R (quotientWeightedComponent J v q)) :=
  ⟨⟨groebnerWeightedIdeal_free m J G hG hu v hJv q,
      groebnerWeightedIdeal_finite m J G hG hu v hv hJv q⟩,
    ⟨groebnerWeightedQuotient_free m J G hG hu v hJv q,
      groebnerWeightedQuotient_finite m J G hG hu v hv hJv q⟩⟩

end FinitePieces
end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.GradingProjectionMap -/
section

section
set_option autoImplicit false
noncomputable section
namespace FourPapers
open Classical CommAlg
variable {k X Y I J A B : Type*} [CommRing k]
  [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]

/-- Basis projections commute with any injective change of degree, including
integer degree shifts. The hypothesis concerns the actual map on every basis
vector; no associated-graded map is substituted for it. -/
theorem shiftedProjection_commutes (b : Module.Basis I k X) (c : Module.Basis J k Y)
    (deg : I → A) (degree : J → B) (shift : A → B) (hshift : Function.Injective shift)
    (f : X →ₗ[k] Y)
    (hf : ∀i,f (b i)∈Grading.Piece c degree (shift (deg i))) (a : A) :
    f.comp (Grading.projection b deg a)=
      (Grading.projection c degree (shift a)).comp f := by
  apply b.ext
  intro i
  simp only [LinearMap.comp_apply,Grading.projection_basis]
  by_cases hi : deg i=a
  · rw [if_pos hi]
    exact (Grading.projection_eq_self (hi ▸ hf i)).symm
  · rw [if_neg hi,map_zero]
    exact (Grading.projection_eq_zero
      (show shift a≠shift (deg i) from fun h => hi (hshift h).symm) (hf i)).symm

/-- A diagonal basis projection preserves every subspace spanned by a subset
of that basis. In particular it preserves each level of a separate weight
filtration. -/
theorem projection_preserves_basisSpan (b : Module.Basis I k X) (deg : I → A)
    (a : A) (P : Set I) (x : X) (hx : x∈Submodule.span k (b '' P)) :
    Grading.projection b deg a x∈Submodule.span k (b '' P) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i,hi,rfl⟩ := hx
    rw [Grading.projection_basis]
    split_ifs
    · exact Submodule.subset_span ⟨i,hi,rfl⟩
    · exact Submodule.zero_mem _
  | zero => simpa only [map_zero] using Submodule.zero_mem _
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul a x hx ih => simpa only [map_smul] using Submodule.smul_mem _ a ih

/-- A genuine lift can be projected to the prescribed auxiliary and exterior
degree while retaining its exact leading term and every basis weight bound. -/
theorem homogeneous_cycle_lift (b : Module.Basis I k X) (deg : I → A)
    (shift : A → A) (hshift : Function.Injective shift) (D : Module.End k X)
    (hD : ∀i,D (b i)∈Grading.Piece b deg (shift (deg i)))
    (a : A) (P : Set I) (x y : X) (hx : x∈Grading.Piece b deg a)
    (hy : D y=0) (herror : x-y∈Submodule.span k (b '' P)) :
    ∃z : X,z∈Grading.Piece b deg a ∧ D z=0 ∧ x-z∈Submodule.span k (b '' P) := by
  refine ⟨Grading.projection b deg a y,Grading.projection_mem b deg a y,?_,?_⟩
  · have hh := LinearMap.congr_fun (shiftedProjection_commutes b b deg deg shift hshift D hD a) y
    simpa only [LinearMap.comp_apply,hy,map_zero] using hh
  · have hh := projection_preserves_basisSpan b deg a P (x-y) herror
    simpa only [map_sub,Grading.projection_eq_self hx] using hh

end FourPapers
end

end
end

/- BEGIN EXACT BODY: FourPapers.Common.FilteredFreeHomology -/
section

/-! # Integral freeness from a finite filtration and actual cycle lifts

Free quotient modules are projective, so each step of a finite filtration
splits as a module.  This argument works over an arbitrary commutative ring;
there is no field-dimension or torsion-free inference in the proof.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.FilteredHomology

open Classical

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- A chosen section of the literal quotient map gives the ordinary direct
product splitting, with residual component `x - s [x]`. -/
def quotientSectionEquiv (P : Submodule R M) (s : (M ⧸ P) →ₗ[R] M)
    (hs : ∀ x, P.mkQ (s x) = x) : (P × (M ⧸ P)) ≃ₗ[R] M where
  toFun x := x.1.val + s x.2
  invFun x :=
    (⟨x - s (P.mkQ x), by
      apply (Submodule.Quotient.mk_eq_zero P).mp
      change P.mkQ (x - s (P.mkQ x)) = 0
      rw [map_sub, hs, sub_self]⟩, P.mkQ x)
  left_inv x := by
    have hx : P.mkQ x.1.val = 0 := (Submodule.Quotient.mk_eq_zero P).mpr x.1.property
    apply Prod.ext
    · apply Subtype.ext
      simp only [map_add, hx, hs, zero_add, add_sub_cancel_right]
    · simp only [map_add, hx, hs, zero_add]
  right_inv x := sub_add_cancel x (s (P.mkQ x))
  map_add' x y := by
    change (x.1.val + y.1.val) + s (x.2 + y.2) =
      (x.1.val + s x.2) + (y.1.val + s y.2)
    rw [map_add]
    abel
  map_smul' r x := by
    change r • x.1.val + s (r • x.2) = r • (x.1.val + s x.2)
    rw [map_smul, smul_add]

theorem free_of_free_submodule_and_quotient (P : Submodule R M)
    [Module.Free R P] [Module.Free R (M ⧸ P)] : Module.Free R M := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property P.mkQ
    (LinearMap.id : (M ⧸ P) →ₗ[R] (M ⧸ P)) P.mkQ_surjective
  exact Module.Free.of_equiv (quotientSectionEquiv P s (fun x => LinearMap.congr_fun hs x))

theorem finite_of_finite_submodule_and_free_quotient (P : Submodule R M)
    [Module.Finite R P] [Module.Finite R (M ⧸ P)] [Module.Free R (M ⧸ P)] :
    Module.Finite R M := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property P.mkQ
    (LinearMap.id : (M ⧸ P) →ₗ[R] (M ⧸ P)) P.mkQ_surjective
  exact Module.Finite.equiv (quotientSectionEquiv P s (fun x => LinearMap.congr_fun hs x))

/-- If every successive quotient in a finite exhaustive filtration is free,
then the actual filtered module is free. -/
theorem free_of_free_grades (F : Filtration (K := R) M) (N : ℕ)
    (hN : F.level N = ⊤)
    (hfree : ∀ n < N, Module.Free R (Grade F n)) : Module.Free R M := by
  have hlevel : ∀ n ≤ N, Module.Free R (F.level n) := by
    intro n
    induction n with
    | zero =>
        intro _
        rw [F.zero]
        infer_instance
    | succ n ih =>
        intro hn
        letI : Module.Free R (F.level n) := ih (Nat.le_of_succ_le hn)
        letI : Module.Free R (lowerInLevel F n) :=
          Module.Free.of_equiv (Submodule.comapSubtypeEquivOfLe
            (F.mono (Nat.le_succ n))).symm
        letI : Module.Free R (Grade F n) := hfree n (Nat.lt_of_succ_le hn)
        exact free_of_free_submodule_and_quotient (lowerInLevel F n)
  have htop := hlevel N le_rfl
  rw [hN] at htop
  letI : Module.Free R (⊤ : Submodule R M) := htop
  exact Module.Free.of_equiv Submodule.topEquiv

theorem finite_of_finite_free_grades (F : Filtration (K := R) M) (N : ℕ)
    (hN : F.level N = ⊤)
    (hfree : ∀ n < N, Module.Free R (Grade F n))
    (hfinite : ∀ n < N, Module.Finite R (Grade F n)) : Module.Finite R M := by
  have hlevel : ∀ n ≤ N, Module.Finite R (F.level n) := by
    intro n
    induction n with
    | zero =>
        intro _
        rw [F.zero]
        infer_instance
    | succ n ih =>
        intro hn
        letI : Module.Finite R (F.level n) := ih (Nat.le_of_succ_le hn)
        letI : Module.Finite R (lowerInLevel F n) :=
          Module.Finite.equiv (Submodule.comapSubtypeEquivOfLe
            (F.mono (Nat.le_succ n))).symm
        letI : Module.Free R (Grade F n) := hfree n (Nat.lt_of_succ_le hn)
        letI : Module.Finite R (Grade F n) := hfinite n (Nat.lt_of_succ_le hn)
        exact finite_of_finite_submodule_and_free_quotient (lowerInLevel F n)
  have htop := hlevel N le_rfl
  rw [hN] at htop
  letI : Module.Finite R (⊤ : Submodule R M) := htop
  exact Module.Finite.equiv Submodule.topEquiv

variable {X Y Z : Type*} [AddCommGroup X] [Module R X]
  [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z]

/-- Literal leading-cycle lifts and free homology of the leading complex
imply freeness of the actual homology over the coefficient ring. -/
theorem homology_free_of_leading_free
    (F : Filtration (K := R) X) (G : Filtration (K := R) Y)
    (H : Filtration (K := R) Z) (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z)
    (hf : Preserves F G f) (hg : Preserves G H g) (hfg : g.comp f = 0)
    (N : ℕ) (hN : G.level N = ⊤)
    (liftf : LiftsCycles F G f) (liftg : LiftsCycles G H g)
    (hfree : ∀ n < N, Module.Free R (GradedHomology F G H f g hf hg hfg n)) :
    Module.Free R (Homology f g hfg) := by
  have htop : (homologyFiltration G f g hfg).level N = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨z, rfl⟩ := (LinearMap.range (boundaryMap f g hfg)).mkQ_surjective x
    refine ⟨z, ?_, rfl⟩
    change z.val ∈ G.level N
    rw [hN]
    trivial
  apply free_of_free_grades (homologyFiltration G f g hfg) N htop
  intro n hn
  letI := hfree n hn
  exact Module.Free.of_equiv
    (associatedHomologyEquiv F G H f g hf hg hfg n liftf liftg).symm

theorem homology_finite_of_leading_finite_free
    (F : Filtration (K := R) X) (G : Filtration (K := R) Y)
    (H : Filtration (K := R) Z) (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z)
    (hf : Preserves F G f) (hg : Preserves G H g) (hfg : g.comp f = 0)
    (N : ℕ) (hN : G.level N = ⊤)
    (liftf : LiftsCycles F G f) (liftg : LiftsCycles G H g)
    (hfree : ∀ n < N, Module.Free R (GradedHomology F G H f g hf hg hfg n))
    (hfinite : ∀ n < N, Module.Finite R (GradedHomology F G H f g hf hg hfg n)) :
    Module.Finite R (Homology f g hfg) := by
  have htop : (homologyFiltration G f g hfg).level N = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨z, rfl⟩ := (LinearMap.range (boundaryMap f g hfg)).mkQ_surjective x
    refine ⟨z, ?_, rfl⟩
    change z.val ∈ G.level N
    rw [hN]
    trivial
  apply finite_of_finite_free_grades (homologyFiltration G f g hfg) N htop
  · intro n hn
    letI := hfree n hn
    exact Module.Free.of_equiv
      (associatedHomologyEquiv F G H f g hf hg hfg n liftf liftg).symm
  · intro n hn
    letI := hfinite n hn
    exact Module.Finite.equiv
      (associatedHomologyEquiv F G H f g hf hg hfg n liftf liftg).symm

end FourPapers.FilteredHomology

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphIdealGrading -/
section

/-! # The actual homogeneous ideal Koszul strands

The ordinary-degree submodules are identified through the literal ideal
inclusion with the polynomial Koszul grading. Their variable-weight
filtration is finite, their chain modules are finite free, and the actual
cycle lifts restrict to every ordinary degree by homogeneous projection.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section

namespace FourPapers.Sublattice
open Classical CategoryTheory CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial
open FourPapers.Universal FourPapers.FilteredHomology
attribute [local instance] MvPolynomial.weightedGradedAlgebra
/-- Degree preservation on basis vectors extends to their homogeneous
spans. Only the literal additive-monoid structures are needed. -/
lemma map_mem_piece_of_basis_monoid
    {R X Y I J A : Type*} [CommRing R]
    [AddCommMonoid X] [Module R X] [AddCommMonoid Y] [Module R Y]
    (b : Module.Basis I R X) (c : Module.Basis J R Y)
    (deg : I → A) (degree : J → A) (f : X →ₗ[R] Y)
    (hf : ∀ i, f (b i) ∈ Grading.Piece c degree (deg i))
    (a : A) {x : X} (hx : x ∈ Grading.Piece b deg a) :
    f x ∈ Grading.Piece c degree a := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      change deg i = a at hi
      rw [← hi]
      exact hf i
  | zero => simpa only [map_zero] using (Grading.Piece c degree a).zero_mem
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul r x hx ih => simpa only [map_smul] using Submodule.smul_mem _ r ih

/-- A homogeneous basis projection preserves every span of a subset of
that basis. No additive-group structure is needed for this span argument. -/
lemma projection_preserves_basisSpan_monoid
    {R X I A : Type*} [CommRing R] [AddCommMonoid X] [Module R X]
    (b : Module.Basis I R X) (degree : I → A) (a : A) (S : Set I)
    (x : X) (hx : x ∈ Submodule.span R (b '' S)) :
    Grading.projection b degree a x ∈ Submodule.span R (b '' S) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      rw [Grading.projection_basis]
      split_ifs
      · exact Submodule.subset_span ⟨i, hi, rfl⟩
      · exact Submodule.zero_mem _
  | zero => simpa only [map_zero] using Submodule.zero_mem _
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul r x hx ih => simpa only [map_smul] using Submodule.smul_mem _ r ih

/-- A coordinate restriction preserves support bounds when its indices cover
all nonzero ambient coordinates. This is a statement about finite functions. -/
lemma finsupp_support_subset_iff_of_restrict
    {R I J : Type*} [Zero R] (u : J →₀ R) (v : I →₀ R) (e : J → I)
    (hcoord : ∀ j, u j = v (e j))
    (hcover : ∀ i ∈ v.support, ∃ j, e j = i) (s : Set I) :
    (↑u.support : Set J) ⊆ e ⁻¹' s ↔ (↑v.support : Set I) ⊆ s := by
  constructor
  · intro hu i hi
    obtain ⟨j, rfl⟩ := hcover i hi
    apply hu
    apply Finsupp.mem_support_iff.mpr
    intro hz
    exact Finsupp.mem_support_iff.mp hi ((hcoord j).symm.trans hz)
  · intro hv j hj
    apply hv
    apply Finsupp.mem_support_iff.mpr
    intro hz
    exact Finsupp.mem_support_iff.mp hj ((hcoord j).trans hz)

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

/-- Literal coordinate subtraction agrees with addition of the negative
scalar multiple. This avoids transporting a linear map between inherited
additive-group presentations of the same finitely supported module. -/
theorem actualIdealCoordinate_sub_eq_add_neg_one_smul (P : QuotientGroebnerData V k)
    (p : ℕ) (x y : Set.powersetCard V p →₀ P.ideal) :
    x-y = x + (-1 : k) • y := by
  apply Finsupp.ext
  intro F
  apply Subtype.ext
  change (x F).val - (y F).val = (x F).val + (-1 : k) • (y F).val
  rw [neg_one_smul, sub_eq_add_neg]

abbrev actualIdealOrdinaryPiece (P : QuotientGroebnerData V k) (q p : ℕ) :
    Submodule k (Set.powersetCard V p →₀ P.ideal) :=
  Grading.Piece (actualIdealCoefficientBasis P p) (fun a => (actualIdealDegree a).degree) q

local instance ordinaryPieceAddCommGroup (P : QuotientGroebnerData V k) (q p : ℕ) :
    AddCommGroup (actualIdealOrdinaryPiece P q p) :=
  Submodule.addCommGroup (R := k) (M := Set.powersetCard V p →₀ P.ideal)
    (module_M := inferInstance) (actualIdealOrdinaryPiece P q p)

local instance ordinaryPieceModule (P : QuotientGroebnerData V k) (q p : ℕ) :
    Module k (actualIdealOrdinaryPiece P q p) :=
  Submodule.module (R := k) (M := Set.powersetCard V p →₀ P.ideal)
    (actualIdealOrdinaryPiece P q p)

def actualIdealOrdinaryBasis (P : QuotientGroebnerData V k) (q p : ℕ) :
    Module.Basis {a : ActualIdealIndex P p // (actualIdealDegree a).degree = q}
      k (actualIdealOrdinaryPiece P q p) :=
  Grading.restrictedBasis (actualIdealCoefficientBasis P p)
    (fun a => (actualIdealDegree a).degree = q)

def actualIdealOrdinaryFiltration (P : QuotientGroebnerData V k) (w : V → ℕ)
    (q p : ℕ) : Filtration (K := k) (actualIdealOrdinaryPiece P q p) :=
  basisFiltration (K := k) (X := actualIdealOrdinaryPiece P q p)
    (actualIdealOrdinaryBasis P q p)
    (fun a => Finsupp.weight w (actualIdealDegree a.val))

@[simp] theorem actualIdealOrdinaryBasis_val (P : QuotientGroebnerData V k)
    (q p : ℕ) (a : {a : ActualIdealIndex P p // (actualIdealDegree a).degree = q}) :
    (actualIdealOrdinaryBasis P q p a).val = actualIdealCoefficientBasis P p a.val :=
  Grading.restrictedBasis_val (actualIdealCoefficientBasis P p)
    (fun a => (actualIdealDegree a).degree = q) a

/-- Restriction of the monic coefficient basis preserves its literal coordinates. -/
theorem actualIdealOrdinaryBasis_repr (P : QuotientGroebnerData V k)
    (q p : ℕ) (x : actualIdealOrdinaryPiece P q p)
    (a : {a : ActualIdealIndex P p // (actualIdealDegree a).degree = q}) :
    (actualIdealOrdinaryBasis P q p).repr x a =
      (actualIdealCoefficientBasis P p).repr x.val a.val := by
  have he : (actualIdealOrdinaryBasis P q p).coord a =
      ((actualIdealCoefficientBasis P p).coord a.val).comp
        (actualIdealOrdinaryPiece P q p).subtype := by
    apply (actualIdealOrdinaryBasis P q p).ext
    intro j
    simp only [Module.Basis.coord_apply, LinearMap.comp_apply, Submodule.subtype_apply,
      actualIdealOrdinaryBasis_val, Module.Basis.repr_self, Finsupp.single_apply]
    simp only [Subtype.ext_iff]
  exact LinearMap.congr_fun he x

/-- The weight filtration on a homogeneous strand is the restriction of the
actual ideal-coordinate filtration. This compares the literal subtype bases. -/
theorem actualIdealOrdinaryFiltration_mem_iff (P : QuotientGroebnerData V k)
    (w : V → ℕ) (q p n : ℕ) (x : actualIdealOrdinaryPiece P q p) :
    x ∈ (actualIdealOrdinaryFiltration P w q p).level n ↔
      x.val ∈ (actualIdealCoordinateFiltration P w p).level n := by
  change x ∈ Submodule.span k ((actualIdealOrdinaryBasis P q p) ''
      {a | Finsupp.weight w (actualIdealDegree a.val) < n}) ↔
    x.val ∈ Submodule.span k ((actualIdealCoefficientBasis P p) ''
      {a | Finsupp.weight w (actualIdealDegree a) < n})
  rw [(actualIdealOrdinaryBasis P q p).mem_span_image,
    (actualIdealCoefficientBasis P p).mem_span_image]
  refine finsupp_support_subset_iff_of_restrict
    ((actualIdealOrdinaryBasis P q p).repr x)
    ((actualIdealCoefficientBasis P p).repr x.val) Subtype.val
    (fun a => actualIdealOrdinaryBasis_repr P q p x a) ?_
    {a | Finsupp.weight w (actualIdealDegree a) < n}
  intro a ha
  have hd : (actualIdealDegree a).degree = q :=
    (Grading.mem_piece (actualIdealCoefficientBasis P p)
      (fun a => (actualIdealDegree a).degree) q x.val).mp x.property a
        (Finsupp.mem_support_iff.mp ha)
  exact ⟨⟨a, hd⟩, rfl⟩

theorem idealCoordinatesToAmbient_basis_ordinary (P : QuotientGroebnerData V k)
    (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule k (fun _ : V => (1 : ℕ))))
    (p : ℕ) (a : ActualIdealIndex P p) :
    idealCoordinatesToAmbient P.ideal p (actualIdealCoefficientBasis P p a) ∈
      Grading.Piece (quotientCoefficientBasis (k := k) (∅ : Family V) p)
        (fun b => (quotientDegree b).degree) (actualIdealDegree a).degree := by
  rw [Grading.mem_piece]
  intro b hb
  rw [idealCoordinatesToAmbient_repr, actualIdealCoefficientBasis_apply] at hb
  by_cases hF : a.1 = b.1
  · rw [Finsupp.single_apply, if_pos hF] at hb
    have hd := idealLift_isWeightedHomogeneous P.order P.ideal P.generators
      P.groebner P.unitLeading (fun _ : V => (1 : ℕ)) hJ a.2 hb
    have hd' : b.2.val.degree = a.2.val.degree := by
      simpa only [← Finsupp.degree_eq_weight_one] using hd
    simp only [quotientDegree, actualIdealDegree, map_add, hd', hF]
  · rw [Finsupp.single_apply, if_neg hF] at hb
    exact (hb rfl).elim

/-- The polynomial grading is the actual ordinary grading of the ideal,
not merely a label assigned to its monic basis. -/
theorem actualIdealOrdinaryPiece_mem_iff (P : QuotientGroebnerData V k)
    (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule k (fun _ : V => (1 : ℕ))))
    (q p : ℕ) (x : Set.powersetCard V p →₀ P.ideal) :
    x ∈ actualIdealOrdinaryPiece P q p ↔
      idealCoordinatesToAmbient P.ideal p x ∈
        Grading.Piece (quotientCoefficientBasis (k := k) (∅ : Family V) p)
          (fun b => (quotientDegree b).degree) q := by
  constructor
  · exact map_mem_piece_of_basis_monoid (R := k)
      (X := Set.powersetCard V p →₀ P.ideal)
      (Y := AmbientKoszulCoordinates (k := k) (V := V) p)
      (I := ActualIdealIndex P p) (J := QuotientIndex (∅ : Family V) p) (A := ℕ)
      (actualIdealCoefficientBasis P p)
      (quotientCoefficientBasis (k := k) (∅ : Family V) p)
      (fun a => (actualIdealDegree a).degree) (fun a => (quotientDegree a).degree)
      (idealCoordinatesToAmbient P.ideal p)
      (idealCoordinatesToAmbient_basis_ordinary P hJ p) q
  · intro hx
    rw [Grading.mem_piece]
    intro a ha
    have h := (Grading.mem_piece
      (quotientCoefficientBasis (k := k) (∅ : Family V) p)
      (fun b => (quotientDegree b).degree) q _).mp hx
      ⟨a.1, ⟨a.2.val, emptyFamily_allowed a.2.val⟩⟩
    apply h
    simpa only [idealCoordinatesToAmbient_repr, actualIdealCoefficientBasis_repr] using ha

theorem actualIdealCoordinateDifferential_ordinary (P : QuotientGroebnerData V k)
    (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule k (fun _ : V => (1 : ℕ))))
    (q p : ℕ) (x : Set.powersetCard V (p+1) →₀ P.ideal)
    (hx : x ∈ actualIdealOrdinaryPiece P q (p+1)) :
    actualIdealCoordinateDifferential P.ideal p x ∈ actualIdealOrdinaryPiece P q p := by
  apply (actualIdealOrdinaryPiece_mem_iff P hJ q p _).mpr
  rw [← idealCoordinatesToAmbient_differential]
  exact map_mem_piece_of_basis_monoid
    (quotientCoefficientBasis (k := k) (∅ : Family V) (p+1))
    (quotientCoefficientBasis (k := k) (∅ : Family V) p)
    (fun a => (quotientDegree a).degree) (fun a => (quotientDegree a).degree)
    (quotientDifferential (k := k) (∅ : Family V) p)
    (quotientDifferential_basis_regraded (k := k) (∅ : Family V) Finsupp.degree p) q
    ((actualIdealOrdinaryPiece_mem_iff P hJ q (p+1) x).mp hx)

def actualIdealOrdinaryDifferential (P : QuotientGroebnerData V k)
    (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule k (fun _ : V => (1 : ℕ))))
    (q p : ℕ) : actualIdealOrdinaryPiece P q (p+1) →ₗ[k] actualIdealOrdinaryPiece P q p :=
  ((actualIdealCoordinateDifferential P.ideal p).domRestrict
    (actualIdealOrdinaryPiece P q (p+1))).codRestrict
      (actualIdealOrdinaryPiece P q p)
      (fun x => actualIdealCoordinateDifferential_ordinary P hJ q p x.val x.property)

@[simp] theorem actualIdealOrdinaryDifferential_val (P : QuotientGroebnerData V k)
    (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule k (fun _ : V => (1 : ℕ))))
    (q p : ℕ) (x : actualIdealOrdinaryPiece P q (p+1)) :
    (actualIdealOrdinaryDifferential P hJ q p x).val =
      actualIdealCoordinateDifferential P.ideal p x.val := rfl

def actualIdealOrdinaryPrevious (P : QuotientGroebnerData V k)
    (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule k (fun _ : V => (1 : ℕ))))
    (q : ℕ) : ∀ p : ℕ,
      actualIdealOrdinaryPiece P q p →ₗ[k] actualIdealOrdinaryPiece P q p.pred
  | 0 => 0
  | p+1 => actualIdealOrdinaryDifferential P hJ q p

@[simp] theorem actualIdealOrdinaryPrevious_val (P : QuotientGroebnerData V k)
    (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule k (fun _ : V => (1 : ℕ))))
    (q p : ℕ) (x : actualIdealOrdinaryPiece P q p) :
    (actualIdealOrdinaryPrevious P hJ q p x).val =
      actualIdealPreviousDifferential P.ideal p x.val := by
  cases p <;> rfl

theorem actualIdealCoordinateDifferential_comp (J : Ideal (MvPolynomial V k)) (p : ℕ) :
    (actualIdealPreviousDifferential J p).comp (actualIdealCoordinateDifferential J p) = 0 := by
  cases p with
  | zero => simp only [actualIdealPreviousDifferential, LinearMap.zero_comp]
  | succ p =>
      apply LinearMap.ext
      intro x
      exact LinearMap.congr_fun (coordinateDifferential_comp
        (X : V → MvPolynomial V k) (ModuleCat.of (MvPolynomial V k) J) p) x

theorem actualIdealOrdinaryDifferential_comp (P : QuotientGroebnerData V k)
    (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule k (fun _ : V => (1 : ℕ))))
    (q p : ℕ) :
    (actualIdealOrdinaryPrevious P hJ q p).comp
      (actualIdealOrdinaryDifferential P hJ q p) = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (actualIdealOrdinaryPrevious P hJ q p
    (actualIdealOrdinaryDifferential P hJ q p x)).val = 0
  rw [actualIdealOrdinaryPrevious_val, actualIdealOrdinaryDifferential_val]
  exact LinearMap.congr_fun (actualIdealCoordinateDifferential_comp P.ideal p) x.val

abbrev actualIdealOrdinaryHomology (P : QuotientGroebnerData V k)
    (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule k (fun _ : V => (1 : ℕ))))
    (q p : ℕ) :=
  Homology (actualIdealOrdinaryDifferential P hJ q p)
    (actualIdealOrdinaryPrevious P hJ q p) (actualIdealOrdinaryDifferential_comp P hJ q p)

theorem actualIdealCoordinateDifferential_preserves (P : QuotientGroebnerData V k)
    (w : V → ℕ)
    (htail : ∀ g ∈ P.generators, g ≠ 0 →
      ∀ a ∈ (monomial (P.order.degree g) 1-g).support,
        Finsupp.weight w a < Finsupp.weight w (P.order.degree g)) (p : ℕ) :
    Preserves (actualIdealCoordinateFiltration P w (p+1))
      (actualIdealCoordinateFiltration P w p) (actualIdealCoordinateDifferential P.ideal p) := by
  intro n x hx
  apply (actualIdealCoordinateFiltration_mem_iff P w htail p n _).mpr
  rw [← idealCoordinatesToAmbient_differential]
  exact basisHomogeneous_preserves _ _ _ _ _
    (quotientDifferential_basis_regraded (∅ : Family V) (Finsupp.weight w) p) n _
    ((actualIdealCoordinateFiltration_mem_iff P w htail (p+1) n x).mp hx)

theorem actualIdealOrdinaryDifferential_preserves (P : QuotientGroebnerData V k)
    (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule k (fun _ : V => (1 : ℕ))))
    (w : V → ℕ)
    (htail : ∀ g ∈ P.generators, g ≠ 0 →
      ∀ a ∈ (monomial (P.order.degree g) 1-g).support,
        Finsupp.weight w a < Finsupp.weight w (P.order.degree g)) (q p : ℕ) :
    Preserves (actualIdealOrdinaryFiltration P w q (p+1))
      (actualIdealOrdinaryFiltration P w q p) (actualIdealOrdinaryDifferential P hJ q p) := by
  intro n x hx
  apply (actualIdealOrdinaryFiltration_mem_iff P w q p n
    (actualIdealOrdinaryDifferential P hJ q p x)).mpr
  rw [actualIdealOrdinaryDifferential_val]
  exact actualIdealCoordinateDifferential_preserves P w htail p n x.val
    ((actualIdealOrdinaryFiltration_mem_iff P w q (p+1) n x).mp hx)

theorem actualIdealOrdinaryPrevious_preserves (P : QuotientGroebnerData V k)
    (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule k (fun _ : V => (1 : ℕ))))
    (w : V → ℕ)
    (htail : ∀ g ∈ P.generators, g ≠ 0 →
      ∀ a ∈ (monomial (P.order.degree g) 1-g).support,
        Finsupp.weight w a < Finsupp.weight w (P.order.degree g)) (q p : ℕ) :
    Preserves (actualIdealOrdinaryFiltration P w q p)
      (actualIdealOrdinaryFiltration P w q p.pred) (actualIdealOrdinaryPrevious P hJ q p) := by
  cases p with
  | zero => intro n x hx; exact Submodule.zero_mem _
  | succ p => exact actualIdealOrdinaryDifferential_preserves P hJ w htail q p

/-- A lift in the whole actual ideal complex can be projected to the
prescribed ordinary degree without changing its leading weight. -/
theorem actualIdealOrdinaryPrevious_lifts (P : QuotientGroebnerData V k)
    (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule k (fun _ : V => (1 : ℕ))))
    (w : V → ℕ) (q p : ℕ)
    (hlift : LiftsCycles (actualIdealCoordinateFiltration P w p)
      (actualIdealCoordinateFiltration P w p.pred) (actualIdealPreviousDifferential P.ideal p)) :
    LiftsCycles (actualIdealOrdinaryFiltration P w q p)
      (actualIdealOrdinaryFiltration P w q p.pred) (actualIdealOrdinaryPrevious P hJ q p) := by
  intro n x hx hdx
  have hdx' : actualIdealPreviousDifferential P.ideal p x.val ∈
      (actualIdealCoordinateFiltration P w p.pred).level n := by
    rw [← actualIdealOrdinaryPrevious_val P hJ q p x]
    exact (actualIdealOrdinaryFiltration_mem_iff P w q p.pred n
      (actualIdealOrdinaryPrevious P hJ q p x)).mp hdx
  obtain ⟨y, hy, hdy, herr⟩ := hlift n x.val
    ((actualIdealOrdinaryFiltration_mem_iff P w q p (n+1) x).mp hx) hdx'
  let z : actualIdealOrdinaryPiece P q p :=
    ⟨Grading.projection (actualIdealCoefficientBasis P p)
      (fun a => (actualIdealDegree a).degree) q y, Grading.projection_mem _ _ _ _⟩
  refine ⟨z, ?_, ?_, ?_⟩
  · apply (actualIdealOrdinaryFiltration_mem_iff P w q p (n+1) z).mpr
    exact projection_preserves_basisSpan_monoid (R := k)
      (X := Set.powersetCard V p →₀ P.ideal) (I := ActualIdealIndex P p) (A := ℕ)
      (actualIdealCoefficientBasis P p) (fun a => (actualIdealDegree a).degree) q
      {a | Finsupp.weight w (actualIdealDegree a) < n+1} y hy
  · apply Subtype.ext
    cases p with
    | zero => rfl
    | succ p =>
        have hc := LinearMap.congr_fun (fineProjection_commutes (R := k)
          (X := Set.powersetCard V (p+1) →₀ P.ideal)
          (Y := Set.powersetCard V p →₀ P.ideal)
          (I := ActualIdealIndex P (p+1)) (J := ActualIdealIndex P p) (Γ := ℕ)
          (actualIdealCoefficientBasis P (p+1)) (actualIdealCoefficientBasis P p)
          (fun a => (actualIdealDegree a).degree) (fun a => (actualIdealDegree a).degree)
          (actualIdealCoordinateDifferential P.ideal p)
          (fun a => actualIdealCoordinateDifferential_ordinary P hJ _ p _
            (Grading.basis_mem_piece _ _ a)) q) y
        have hdy' : actualIdealCoordinateDifferential P.ideal p y = 0 := hdy
        change actualIdealCoordinateDifferential P.ideal p
          (Grading.projection (actualIdealCoefficientBasis P (p+1))
            (fun a => (actualIdealDegree a).degree) q y) = 0
        simpa only [LinearMap.comp_apply, hdy', map_zero] using hc
  · apply (actualIdealOrdinaryFiltration_mem_iff P w q p n (x-z)).mpr
    change x.val - Grading.projection (actualIdealCoefficientBasis P p)
      (fun a => (actualIdealDegree a).degree) q y ∈
        (actualIdealCoordinateFiltration P w p).level n
    have hh : Grading.projection (actualIdealCoefficientBasis P p)
        (fun a => (actualIdealDegree a).degree) q (x.val-y) ∈
          (actualIdealCoordinateFiltration P w p).level n :=
      projection_preserves_basisSpan_monoid (R := k)
        (X := Set.powersetCard V p →₀ P.ideal) (I := ActualIdealIndex P p) (A := ℕ)
        (actualIdealCoefficientBasis P p) (fun a => (actualIdealDegree a).degree) q
        {a | Finsupp.weight w (actualIdealDegree a) < n} (x.val-y) herr
    rw [actualIdealCoordinate_sub_eq_add_neg_one_smul P p x.val y,
      map_add, map_smul, Grading.projection_eq_self x.property,
      ← actualIdealCoordinate_sub_eq_add_neg_one_smul P p x.val
        (Grading.projection (actualIdealCoefficientBasis P p)
          (fun a => (actualIdealDegree a).degree) q y)] at hh
    exact hh

theorem exponent_weight_le_degree_mul (w : V → ℕ) (M : ℕ) (hM : ∀ v, w v ≤ M)
    (α : Exponent V) : Finsupp.weight w α ≤ M * α.degree := by
  induction α using Finsupp.induction_linear with
  | zero => simp
  | add α β ihα ihβ =>
      simpa only [map_add, Nat.mul_add] using Nat.add_le_add ihα ihβ
  | single v n =>
      simp only [Finsupp.weight_single, Finsupp.degree_single, nsmul_eq_mul]
      change n * w v ≤ M * n
      exact (Nat.mul_le_mul_left n (hM v)).trans_eq (Nat.mul_comm n M)

theorem actualIdealOrdinaryFiltration_top (P : QuotientGroebnerData V k)
    (w : V → ℕ) (M : ℕ) (hM : ∀ v, w v ≤ M) (q p : ℕ) :
    (actualIdealOrdinaryFiltration P w q p).level (M*q+1) = ⊤ := by
  apply top_unique
  intro x _
  rw [actualIdealOrdinaryFiltration, basisFiltration_mem]
  intro a ha
  have hb := exponent_weight_le_degree_mul w M hM (actualIdealDegree a.val)
  rw [a.property] at hb
  omega

theorem actualIdealOrdinaryPiece_free (P : QuotientGroebnerData V k) (q p : ℕ) :
    Module.Free k (actualIdealOrdinaryPiece P q p) :=
  Module.Free.of_basis (actualIdealOrdinaryBasis P q p)

theorem actualIdealOrdinaryPiece_finite (P : QuotientGroebnerData V k) (q p : ℕ) :
    Module.Finite k (actualIdealOrdinaryPiece P q p) := by
  let I := {a : ActualIdealIndex P p // (actualIdealDegree a).degree = q}
  let Q := {a : Exponent V // a.degree ≤ q}
  letI : Finite Q := (Finsupp.finite_of_degree_le q).to_subtype
  have hb (a : I) : a.val.2.val.degree ≤ q :=
    (degree_mono (le_add_of_nonneg_right zero_le :
      a.val.2.val ≤ actualIdealDegree a.val)).trans_eq a.property
  let f : I → Q × Set.powersetCard V p := fun a => (⟨a.val.2.val, hb a⟩, a.val.1)
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Sigma.ext (congrArg Prod.snd hab)
    exact heq_of_eq (Subtype.ext (congrArg (fun z : Q × Set.powersetCard V p => z.1.val) hab))
  letI : Finite I := Finite.of_injective f hf
  exact Module.Finite.of_basis (actualIdealOrdinaryBasis P q p)

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.InitialIdealBasis -/
section

/-! # The monomial basis of the actual initial ideal

This uses the same index type as the triangular basis of the original ideal.
The resulting comparison is an actual linear equivalence, with both sets of
coordinates equal to the stated polynomial coefficients.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice

open Classical MvPolynomial
open scoped BigOperators

variable {K V : Type*} [CommRing K] [Nontrivial K]
  (m : MonomialOrder V) (J : Ideal (MvPolynomial V K))
  (G : Set (MvPolynomial V K)) (hG : m.IsGroebnerBasis G J)
  (hu : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g))

abbrev initialIdealForBasis := Ideal.span (m.leadingTerm '' (J : Set (MvPolynomial V K)))

def initialMonomial (a : NonstandardIndex m J) : initialIdealForBasis m J :=
  ⟨monomial a.val 1,
    (monomial_mem_initial_iff_not_standard m J G hG hu a.val).mpr a.property⟩

def initialCoefficientMap : initialIdealForBasis m J →ₗ[K] (NonstandardIndex m J →₀ K) :=
  (Finsupp.lsubtypeDomain {a : V →₀ ℕ | a ∉ m.standardMonomials J}).comp
    ((MvPolynomial.basisMonomials V K).repr.toLinearMap.comp
      ((initialIdealForBasis m J).restrictScalars K).subtype)

@[simp] theorem initialCoefficientMap_apply (f : initialIdealForBasis m J)
    (a : NonstandardIndex m J) : initialCoefficientMap m J f a = f.val.coeff a.val := rfl

theorem initialCoefficientMap_monomial (a : NonstandardIndex m J) :
    initialCoefficientMap m J (initialMonomial m J G hG hu a) = Finsupp.single a 1 := by
  ext b
  rw [initialCoefficientMap_apply]
  change (monomial a.val (1 : K)).coeff b.val = _
  simp only [coeff_monomial, Finsupp.single_apply, Subtype.mk.injEq]
  split_ifs with h₁ h₂ h₂
  · rfl
  · exact (h₂ (Subtype.ext h₁)).elim
  · exact (h₁ (congrArg Subtype.val h₂)).elim
  · rfl

theorem initialMonomial_linearIndependent :
    LinearIndependent K (initialMonomial m J G hG hu) := by
  apply LinearIndependent.of_comp (initialCoefficientMap m J)
  have he : initialCoefficientMap m J ∘ initialMonomial m J G hG hu =
      fun a : NonstandardIndex m J => Finsupp.single a (1 : K) :=
    funext (initialCoefficientMap_monomial m J G hG hu)
  rw [he]
  exact Finsupp.linearIndependent_single_one K (NonstandardIndex m J)

theorem initialMonomial_spans :
    (⊤ : Submodule K (initialIdealForBasis m J)) ≤
      Submodule.span K (Set.range (initialMonomial m J G hG hu)) := by
  let T := Submodule.span K (Set.range (initialMonomial m J G hG hu))
  intro x _
  have hx : x.val ∈ T.map ((initialIdealForBasis m J).restrictScalars K).subtype := by
    rw [x.val.as_sum]
    apply Submodule.sum_mem
    intro a ha
    have hmon := monomial_mem_initial_of_coeff_ne_zero m J G hG hu x.val x.property a
      (mem_support_iff.mp ha)
    let ai : NonstandardIndex m J :=
      ⟨a, (monomial_mem_initial_iff_not_standard m J G hG hu a).mp hmon⟩
    have hm : monomial a (1 : K) ∈
        T.map ((initialIdealForBasis m J).restrictScalars K).subtype :=
      ⟨initialMonomial m J G hG hu ai, Submodule.subset_span ⟨ai, rfl⟩, rfl⟩
    simpa only [smul_monomial, smul_eq_mul, mul_one] using
      (T.map ((initialIdealForBasis m J).restrictScalars K).subtype).smul_mem
      (x.val.coeff a) hm
  obtain ⟨y, hy, he⟩ := hx
  exact (Subtype.ext he : y = x) ▸ hy

def initialIdealBasis : Module.Basis (NonstandardIndex m J) K (initialIdealForBasis m J) :=
  Module.Basis.mk (initialMonomial_linearIndependent m J G hG hu)
    (initialMonomial_spans m J G hG hu)

@[simp] theorem initialIdealBasis_apply (a : NonstandardIndex m J) :
    initialIdealBasis m J G hG hu a = initialMonomial m J G hG hu a :=
  Module.Basis.mk_apply _ _ _

theorem initialIdealBasis_repr (f : initialIdealForBasis m J) (a : NonstandardIndex m J) :
    (initialIdealBasis m J G hG hu).repr f a = f.val.coeff a.val := by
  have he : initialCoefficientMap m J = (initialIdealBasis m J G hG hu).repr.toLinearMap := by
    apply (initialIdealBasis m J G hG hu).ext
    intro b
    change initialCoefficientMap m J (initialIdealBasis m J G hG hu b) =
      (initialIdealBasis m J G hG hu).repr (initialIdealBasis m J G hG hu b)
    rw [(initialIdealBasis m J G hG hu).repr_self, initialIdealBasis_apply,
      initialCoefficientMap_monomial]
  exact (congrArg (fun h : initialIdealForBasis m J →ₗ[K] (NonstandardIndex m J →₀ K) => h f a) he).symm

/-- This equivalence preserves every nonstandard polynomial coefficient.
Its source is the original ideal and its target is the actual initial ideal. -/
def idealInitialLinearEquiv : J ≃ₗ[K] initialIdealForBasis m J :=
  (groebnerIdealBasis m J G hG hu).repr.trans (initialIdealBasis m J G hG hu).repr.symm

@[simp] theorem idealInitialLinearEquiv_basis (a : NonstandardIndex m J) :
    idealInitialLinearEquiv m J G hG hu (idealLift m J G hG hu a) =
      initialMonomial m J G hG hu a := by
  change (initialIdealBasis m J G hG hu).repr.symm
    ((groebnerIdealBasis m J G hG hu).repr (idealLift m J G hG hu a)) = _
  rw [← groebnerIdealBasis_apply, Module.Basis.repr_self, Module.Basis.repr_symm_single,
    one_smul, initialIdealBasis_apply]

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.ParityHomology -/
section

/-! The ordinary cycles-modulo-boundaries algebra, using the parity involution
to state the Koszul Leibniz identity on elements of arbitrary degree. This is the
same quotient construction as the graded formulation in TauCeti's DG algebra
library; no grading, exactness, or generation property is assumed here. -/

section
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace FourPapers
variable (K A : Type*) [CommRing K] [Ring A] [Algebra K A]

structure ParityDifferential where
  d : A →ₗ[K] A
  parity : A →ₐ[K] A
  square_zero : ∀ x, d (d x) = 0
  parity_square : ∀ x, parity (parity x) = x
  anticommute : ∀ x, d (parity x) = -parity (d x)
  map_one : d 1 = 0
  leibniz : ∀ x y, d (x * y) = d x * y + parity x * d y

namespace ParityDifferential
variable {K A} (D : ParityDifferential K A)

def cycles : Subalgebra K A :=
  (LinearMap.ker D.d).toSubalgebra D.map_one (by
    intro x y hx hy
    change D.d (x * y) = 0
    rw [D.leibniz, show D.d x = 0 from hx, show D.d y = 0 from hy]
    simp)

@[simp] lemma mem_cycles (x : A) : x ∈ D.cycles ↔ D.d x = 0 := Iff.rfl

/-- Canonical noncommutative structures, selected directly so that nested
differential algebras do not trigger searches for commutative shortcuts. -/
instance (priority := 1100) cyclesRing : Ring D.cycles := Subalgebra.toRing D.cycles

instance (priority := 1100) cyclesAlgebra : Algebra K D.cycles := Subalgebra.algebra D.cycles

lemma parity_cycle {x : A} (hx : D.d x = 0) : D.d (D.parity x) = 0 := by
  rw [D.anticommute, hx, map_zero, neg_zero]

def boundaries : TwoSidedIdeal D.cycles :=
  TwoSidedIdeal.mk' {z : D.cycles | z.val ∈ LinearMap.range D.d}
    (by exact ⟨0, map_zero _⟩)
    (fun {x y} hx hy => by
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by simpa only [map_add, ha, hb, Subalgebra.coe_add]⟩)
    (fun {x} hx => by
      obtain ⟨a, ha⟩ := hx
      exact ⟨-a, by simpa only [map_neg, ha, Subalgebra.coe_neg]⟩)
    (fun {x y} hy => by
      obtain ⟨b, hb⟩ := hy
      refine ⟨D.parity x.val * b, ?_⟩
      change D.d (D.parity x.val * b) = x.val * y.val
      rw [D.leibniz, D.parity_cycle x.property, D.parity_square, hb]
      simp)
    (fun {x y} hx => by
      obtain ⟨a, ha⟩ := hx
      refine ⟨a * y.val, ?_⟩
      change D.d (a * y.val) = x.val * y.val
      rw [D.leibniz, show D.d y.val = 0 from y.property, ha]
      simp)

@[simp] lemma mem_boundaries (z : D.cycles) :
    z ∈ D.boundaries ↔ z.val ∈ LinearMap.range D.d :=
  TwoSidedIdeal.mem_mk' _ _ _ _ _ _ _

abbrev Homology := D.cycles ⧸ D.boundaries.asIdeal

instance (priority := 1100) homologyRing : Ring D.Homology :=
  Ideal.Quotient.ring D.boundaries.asIdeal

instance (priority := 1100) homologyAlgebra : Algebra K D.Homology :=
  Ideal.Quotient.algebra K (A := D.cycles) (I := D.boundaries.asIdeal)

def classMap : D.cycles →ₐ[K] D.Homology := Ideal.Quotient.mkₐ K D.boundaries.asIdeal

@[simp] lemma classMap_eq_zero (z : D.cycles) :
    D.classMap z = 0 ↔ ∃ b : A, D.d b = z.val := by
  change Ideal.Quotient.mk D.boundaries.asIdeal z = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, TwoSidedIdeal.mem_asIdeal, D.mem_boundaries]
  rfl

lemma classMap_surjective : Function.Surjective D.classMap :=
  Ideal.Quotient.mk_surjective

/-- Equality of the two quotient classes is exactly the usual condition that
their difference is an actual boundary. -/
lemma classMap_eq_iff (x y : D.cycles) :
    D.classMap x = D.classMap y ↔ ∃ b : A, D.d b = x.val - y.val := by
  rw [←sub_eq_zero, ←map_sub, D.classMap_eq_zero]
  rfl

/-- The quotient here is the ordinary vector/module quotient of cycles by the
image of the differential, not a quotient by a larger generated ideal. -/
lemma boundaries_exact_range :
    D.boundaries.asIdeal.restrictScalars K =
      (LinearMap.range D.d).comap D.cycles.val.toLinearMap := by
  ext z
  exact (TwoSidedIdeal.mem_asIdeal.trans (D.mem_boundaries z))

end ParityDifferential
end FourPapers

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.GradedCoefficientAlgebra -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 150000
noncomputable section

namespace FourPapers
open Classical
variable {K A Γ : Type*} [CommRing K] [Ring A] [Algebra K A] [AddMonoid Γ]

/-- The algebra consisting of finite sums whose coefficient of degree `g`
belongs to the specified module. Its multiplication is literal convolution. -/
def gradedCoefficientAlgebra (P : Γ → Submodule K A) (h1 : (1 : A) ∈ P 0)
    (hmul : ∀ a b, ∀ x ∈ P a, ∀ y ∈ P b, x * y ∈ P (a + b)) :
    Subalgebra K (AddMonoidAlgebra A Γ) where
  carrier := {x | ∀ g, x.coeff g ∈ P g}
  zero_mem' := by intro g; simp
  add_mem' hx hy := by intro g; exact (P g).add_mem (hx g) (hy g)
  one_mem' := by
    intro g
    by_cases hg : (0 : Γ) = g
    · subst g; simpa using h1
    · simp [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, hg]
  mul_mem' hx hy := by
    intro g
    rw [AddMonoidAlgebra.coeff_mul]
    apply Submodule.sum_mem
    intro a _
    apply Submodule.sum_mem
    intro b _
    dsimp only
    split_ifs with hab
    · subst g; exact hmul a b _ (hx a) _ (hy b)
    · exact (P g).zero_mem
  algebraMap_mem' c := by
    intro g
    change (AddMonoidAlgebra.single 0 (algebraMap K A c)).coeff g ∈ P g
    by_cases hg : (0 : Γ) = g
    · subst g
      simpa only [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same, Algebra.smul_def, mul_one]
        using (P 0).smul_mem c h1
    · simp [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, hg]

variable (P : Γ → Submodule K A) (h1 : (1 : A) ∈ P 0)
  (hmul : ∀ a b, ∀ x ∈ P a, ∀ y ∈ P b, x * y ∈ P (a + b))

@[simp] lemma mem_gradedCoefficientAlgebra (x : AddMonoidAlgebra A Γ) :
    x ∈ gradedCoefficientAlgebra P h1 hmul ↔ ∀ g, x.coeff g ∈ P g := Iff.rfl

lemma single_mem_gradedCoefficientAlgebra (g : Γ) (x : P g) :
    AddMonoidAlgebra.single g x.val ∈ gradedCoefficientAlgebra P h1 hmul := by
  intro a
  by_cases h : g = a
  · subst a; simpa using x.property
  · simp [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, h]

def coefficientSingle (g : Γ) : P g →ₗ[K] gradedCoefficientAlgebra P h1 hmul :=
  ((AddMonoidAlgebra.lsingle g).comp (P g).subtype).codRestrict
    (gradedCoefficientAlgebra P h1 hmul).toSubmodule
    (single_mem_gradedCoefficientAlgebra P h1 hmul g)

@[simp] lemma coefficientSingle_val (g : Γ) (x : P g) :
    (coefficientSingle P h1 hmul g x).val = AddMonoidAlgebra.single g x.val := rfl

@[simp] lemma coefficientSingle_coeff (g a : Γ) (x : P g) :
    (coefficientSingle P h1 hmul g x).val.coeff a = if g = a then x.val else 0 := by
  simp [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

lemma coefficientSingle_injective (g : Γ) :
    Function.Injective (coefficientSingle P h1 hmul g) := by
  intro x y h
  apply Subtype.ext
  have hh := congrArg (fun z : gradedCoefficientAlgebra P h1 hmul => z.val.coeff g) h
  simpa only [coefficientSingle_coeff, ↓reduceIte] using hh

def coefficientAt (g : Γ) : gradedCoefficientAlgebra P h1 hmul →ₗ[K] P g where
  toFun x := ⟨x.val.coeff g, x.property g⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma coefficient_decomposition (x : gradedCoefficientAlgebra P h1 hmul) :
    (∑ g ∈ x.val.coeff.support,
      coefficientSingle P h1 hmul g (coefficientAt P h1 hmul g x)) = x := by
  apply Subtype.ext
  change (gradedCoefficientAlgebra P h1 hmul).val
    (∑ g ∈ x.val.coeff.support, coefficientSingle P h1 hmul g
      (coefficientAt P h1 hmul g x)) = x.val
  rw [map_sum]
  change (∑ g ∈ x.val.coeff.support, AddMonoidAlgebra.single g (x.val.coeff g)) = x.val
  exact AddMonoidAlgebra.sum_coeff_single x.val

namespace ParityDifferential
variable (D : ParityDifferential K A)

def coefficientDifferential : AddMonoidAlgebra A Γ →ₗ[K] AddMonoidAlgebra A Γ where
  toFun := AddMonoidAlgebra.map D.d.toAddMonoidHom
  map_add' := AddMonoidAlgebra.map_add _
  map_smul' c x := by
    ext g
    exact D.d.map_smul c (x.coeff g)

@[simp] lemma coefficientDifferential_coeff (x : AddMonoidAlgebra A Γ) (g : Γ) :
    (D.coefficientDifferential x).coeff g = D.d (x.coeff g) := rfl

@[simp] lemma coefficientDifferential_single (g : Γ) (x : A) :
    D.coefficientDifferential (AddMonoidAlgebra.single g x) =
      AddMonoidAlgebra.single g (D.d x) := AddMonoidAlgebra.map_single _ _ _

lemma coefficientDifferential_leibniz (x y : AddMonoidAlgebra A Γ) :
    D.coefficientDifferential (x * y) = D.coefficientDifferential x * y +
      AddMonoidAlgebra.mapAlgHom Γ D.parity x * D.coefficientDifferential y := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x z hx hz =>
    simp only [add_mul, map_add, hx, hz]
    abel
  | single a r =>
    induction y using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add y z hy hz =>
      simp only [mul_add, map_add, hy, hz]
      abel
    | single b s =>
      simp only [AddMonoidAlgebra.single_mul_single, coefficientDifferential_single,
        AddMonoidAlgebra.mapAlgHom_single, D.leibniz, AddMonoidAlgebra.single_add]

def onMonoidAlgebra : ParityDifferential K (AddMonoidAlgebra A Γ) where
  d := D.coefficientDifferential
  parity := AddMonoidAlgebra.mapAlgHom Γ D.parity
  square_zero x := by ext g; exact D.square_zero (x.coeff g)
  parity_square x := by ext g; simpa using D.parity_square (x.coeff g)
  anticommute x := by ext g; simpa using D.anticommute (x.coeff g)
  map_one := by
    rw [AddMonoidAlgebra.one_def, coefficientDifferential_single, D.map_one]
    exact AddMonoidAlgebra.single_zero 0
  leibniz := D.coefficientDifferential_leibniz

/-- Restrict the actual differential and parity to a stable subalgebra. -/
def restrict (S : Subalgebra K A)
    (hd : ∀ x ∈ S, D.d x ∈ S) (hp : ∀ x ∈ S, D.parity x ∈ S) :
    ParityDifferential K S where
  d := (D.d.domRestrict S.toSubmodule).codRestrict S.toSubmodule (fun x => hd x.val x.property)
  parity := (D.parity.comp S.val).codRestrict S (fun x => hp x.val x.property)
  square_zero x := Subtype.ext (D.square_zero x.val)
  parity_square x := Subtype.ext (D.parity_square x.val)
  anticommute x := Subtype.ext (D.anticommute x.val)
  map_one := Subtype.ext D.map_one
  leibniz x y := Subtype.ext (D.leibniz x.val y.val)

end ParityDifferential
end FourPapers

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.GradedCoefficientBasis -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 200000
noncomputable section
namespace FourPapers
open Classical
variable {K A Γ : Type*} [CommRing K] [Ring A] [Algebra K A] [AddMonoid Γ]
variable (P : Γ → Submodule K A) (h1 : (1 : A) ∈ P 0)
  (hmul : ∀ a b, ∀ x ∈ P a, ∀ y ∈ P b, x * y ∈ P (a + b))

def gradedCoefficientToDFinsupp :
    gradedCoefficientAlgebra P h1 hmul →ₗ[K] (Π₀ g, P g) where
  toFun x :=
    { toFun := fun g => coefficientAt P h1 hmul g x
      support' := Trunc.mk ⟨x.val.coeff.support.val, fun g => by
        by_cases hg : g ∈ x.val.coeff.support
        · exact Or.inl hg
        · apply Or.inr
          apply Subtype.ext
          exact Finsupp.notMem_support_iff.mp hg⟩ }
  map_add' _ _ := by ext g; rfl
  map_smul' _ _ := by ext g; rfl

@[simp] lemma gradedCoefficientToDFinsupp_apply
    (x : gradedCoefficientAlgebra P h1 hmul) (g : Γ) :
    gradedCoefficientToDFinsupp P h1 hmul x g = coefficientAt P h1 hmul g x := rfl

lemma gradedCoefficientToDFinsupp_single (g : Γ) (x : P g) :
    gradedCoefficientToDFinsupp P h1 hmul (coefficientSingle P h1 hmul g x) =
      DFinsupp.single g x := by
  apply DFinsupp.ext
  intro a
  by_cases ha : g = a
  · subst a
    rw [DFinsupp.single_eq_same]
    apply Subtype.ext
    change (coefficientSingle P h1 hmul g x).val.coeff g = x.val
    simp
  · rw [DFinsupp.single_eq_of_ne (Ne.symm ha)]
    apply Subtype.ext
    change (coefficientSingle P h1 hmul g x).val.coeff a = 0
    simp [ha]

lemma gradedCoefficientToDFinsupp_injective :
    Function.Injective (gradedCoefficientToDFinsupp P h1 hmul) := by
  intro x y h
  apply Subtype.ext
  apply AddMonoidAlgebra.coeff_injective
  ext g
  exact congrArg (fun z : Π₀ a, P a => (z g).val) h

lemma gradedCoefficientToDFinsupp_surjective :
    Function.Surjective (gradedCoefficientToDFinsupp P h1 hmul) := by
  intro z
  apply DFinsupp.induction z
  · exact ⟨0,map_zero _⟩
  · intro g x f _ _ hf
    obtain ⟨y,rfl⟩ := hf
    refine ⟨coefficientSingle P h1 hmul g x + y, ?_⟩
    rw [map_add, gradedCoefficientToDFinsupp_single]

def gradedCoefficientDFinsuppEquiv :
    gradedCoefficientAlgebra P h1 hmul ≃ₗ[K] (Π₀ g, P g) :=
  LinearEquiv.ofBijective (gradedCoefficientToDFinsupp P h1 hmul)
    ⟨gradedCoefficientToDFinsupp_injective P h1 hmul,
      gradedCoefficientToDFinsupp_surjective P h1 hmul⟩

@[simp] lemma gradedCoefficientDFinsuppEquiv_symm_single (g : Γ) (x : P g) :
    (gradedCoefficientDFinsuppEquiv P h1 hmul).symm (DFinsupp.single g x) =
      coefficientSingle P h1 hmul g x := by
  apply (gradedCoefficientDFinsuppEquiv P h1 hmul).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (gradedCoefficientToDFinsupp_single P h1 hmul g x).symm

def gradedCoefficientBasis {ι : Γ → Type*} (b : ∀ g, Module.Basis (ι g) K (P g)) :
    Module.Basis (Σ g, ι g) K (gradedCoefficientAlgebra P h1 hmul) :=
  (DFinsupp.basis b).map (gradedCoefficientDFinsuppEquiv P h1 hmul).symm

lemma gradedCoefficientBasis_apply {ι : Γ → Type*} (b : ∀ g, Module.Basis (ι g) K (P g))
    (g : Γ) (i : ι g) :
    gradedCoefficientBasis P h1 hmul b ⟨g,i⟩ = coefficientSingle P h1 hmul g (b g i) := by
  rw [gradedCoefficientBasis, Module.Basis.map_apply]
  have h : (DFinsupp.basis b) ⟨g,i⟩ = DFinsupp.single g (b g i) := by
    apply (DFinsupp.basis b).repr.injective
    ext a
    rcases a with ⟨r,t⟩
    rw [Module.Basis.repr_self]
    change (Finsupp.single (⟨g,i⟩ : Sigma ι) (1 : K)) ⟨r,t⟩ =
      (b r).repr ((DFinsupp.single g (b g i) : Π₀ a, P a) r) t
    by_cases ha : g = r
    · subst r
      simp [Finsupp.single_apply, Sigma.mk.inj_iff]
    · have hh : (⟨g,i⟩ : Sigma ι) ≠ ⟨r,t⟩ := fun e => ha (congrArg Sigma.fst e)
      simp [ha,hh]
  rw [h, gradedCoefficientDFinsuppEquiv_symm_single]

@[simp] lemma gradedCoefficientBasis_repr {ι : Γ → Type*}
    (b : ∀ g, Module.Basis (ι g) K (P g))
    (x : gradedCoefficientAlgebra P h1 hmul) (g : Γ) (i : ι g) :
    (gradedCoefficientBasis P h1 hmul b).repr x ⟨g, i⟩ =
      (b g).repr (coefficientAt P h1 hmul g x) i := rfl

end FourPapers

end
end
end


end
