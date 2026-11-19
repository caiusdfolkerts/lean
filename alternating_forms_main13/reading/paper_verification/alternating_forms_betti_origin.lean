module

public import PaperVerification.AlternatingFormsBettiGrading

/-!
# The Betti formulas with the coefficient field at the origin

The residue quotient is identified with the original coefficient field as
a module over the actual polynomial ring. Functoriality of ordinary Tor
then gives the complete formulas with that coefficient-field argument.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace PaperVerification.AlternatingForms

open CategoryTheory CategoryTheory.Limits

universe u

variable {K M : Type u} [Field K] [AddCommGroup M] [Module K M]
  [FiniteDimensional K M]

/-- Ordinary Mathlib Tor with the actual coefficient field, on which both
polynomial variables act as zero. -/
def exteriorPolynomialTorAtOrigin (f g : ⋀[K]^2 M) (i : ℕ) : ModuleCat K :=
  (ModuleCat.restrictScalars (algebraMap K (PairPolynomial K))).obj
    (((Tor (ModuleCat (PairPolynomial K)) i).obj
      (ModuleCat.of (PairPolynomial K) (ExteriorPairModule f g))).obj
        (ModuleCat.of (PairPolynomial K) (PairOriginModule K)))

/-- Naturality in the second argument identifies the two literal Tor
objects through the proved polynomial-linear residue-field isomorphism. -/
def exteriorPolynomialTorOriginIso (f g : ⋀[K]^2 M) (i : ℕ) :
    exteriorPolynomialTor f g i ≅ exteriorPolynomialTorAtOrigin f g i :=
  (ModuleCat.restrictScalars (algebraMap K (PairPolynomial K))).mapIso
    (((Tor (ModuleCat (PairPolynomial K)) i).obj
      (ModuleCat.of (PairPolynomial K) (ExteriorPairModule f g))).mapIso
        (pairResidueOriginEquiv K).toModuleIso)

instance exteriorPolynomialTorAtOrigin_finite (f g : ⋀[K]^2 M) (i : ℕ) :
    FiniteDimensional K (exteriorPolynomialTorAtOrigin f g i) :=
  Module.Finite.equiv (exteriorPolynomialTorOriginIso f g i).toLinearEquiv

/-- Transport along the actual residue-field comparison preserves the
internal grading already justified on the homogeneous tensor resolution. -/
def exteriorOriginTorGrading (f g : ⋀[K]^2 M) (i : ℕ) :
    TauCeti.InternalGrading K (exteriorPolynomialTorAtOrigin f g i) :=
  (exteriorTorGrading f g i).map (exteriorPolynomialTorOriginIso f g i).toLinearEquiv

def exteriorOriginBettiPolynomial (f g : ⋀[K]^2 M) (i : ℕ) : LaurentPolynomial ℤ :=
  finiteHilbertLaurent (exteriorOriginTorGrading f g i)

theorem exteriorOriginBettiPolynomial_eq (f g : ⋀[K]^2 M) (i : ℕ) :
    exteriorOriginBettiPolynomial f g i = exteriorBettiPolynomial f g i :=
  finiteHilbertLaurent_map _ _

/-- Proposition 5.4 with the coefficient field itself as the second Tor
argument, in every homological degree and with all internal shifts intact. -/
theorem paper_proposition_5_4_origin (f g : ⋀[K]^2 M) :
    exteriorOriginBettiPolynomial f g 0 = exteriorQuotientHilbert f g ∧
    exteriorOriginBettiPolynomial f g 2 =
      LaurentPolynomial.T ((Module.finrank K M : ℤ) + 4) *
        LaurentPolynomial.invert (exteriorQuotientHilbert f g) ∧
    exteriorOriginBettiPolynomial f g 1 =
      exteriorQuotientHilbert f g +
        LaurentPolynomial.T ((Module.finrank K M : ℤ) + 4) *
          LaurentPolynomial.invert (exteriorQuotientHilbert f g) -
        (1 - LaurentPolynomial.T 2) ^ 2 *
          (1 + LaurentPolynomial.T 1) ^ Module.finrank K M ∧
    ∀ i : ℕ, 2 < i → IsZero (exteriorPolynomialTorAtOrigin f g i) ∧
      exteriorOriginBettiPolynomial f g i = 0 := by
  obtain ⟨h₀, h₂, h₁, hi⟩ := paper_proposition_5_4 f g
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [exteriorOriginBettiPolynomial_eq] using h₀
  · simpa only [exteriorOriginBettiPolynomial_eq] using h₂
  · simpa only [exteriorOriginBettiPolynomial_eq] using h₁
  · intro i h
    refine ⟨(hi i h).1.of_iso (exteriorPolynomialTorOriginIso f g i).symm, ?_⟩
    simpa only [exteriorOriginBettiPolynomial_eq] using (hi i h).2

theorem exteriorOriginBettiPolynomial_is_ordinary (f g : ⋀[K]^2 M) (i : ℕ) :
    ∃! B : Polynomial ℤ, B.toLaurent = exteriorOriginBettiPolynomial f g i := by
  rw [exteriorOriginBettiPolynomial_eq]
  exact exteriorBettiPolynomial_is_ordinary f g i

end PaperVerification.AlternatingForms
