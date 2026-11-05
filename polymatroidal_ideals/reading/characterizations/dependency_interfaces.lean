import CommAlg.Polymatroid.HomologicalInterval

/-!
# Arbitrary polynomial generators in the exact Rees generation bound

This supplemental interface identifies generation by all homogeneous polynomial
elements through a given Rees degree with generation by the corresponding
monomials. Consequently the exact bound of Homological Shifts, Theorem 4.4,
is the least bound even when arbitrary polynomial generators are allowed.
The underlying ideal is the genuine homological-shift ideal in Mathlib's
ordinary Rees algebra; its coefficients need not themselves be monomials.
-/

noncomputable section

namespace Characterizations.DependencyInterfaces

open Classical Finset CommAlg CommAlg.Polymatroid

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

/-- All homogeneous polynomial elements of the positive-power homological-shift
module whose Rees degree is at most `q`. -/
def boundedHomologicalPolynomials (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i q : ℕ) : Set (reesAlgebra I) :=
  {p | ∃ s f, s ≤ q ∧ f ∈ homologicalPowerPiece I hI i s ∧
    p.val = Polynomial.monomial s f}

theorem boundedHomologicalMonomials_subset_polynomials
    (I : Ideal (MvPolynomial V k)) (hI : IsPolymatroidalIdeal I) (i q : ℕ) :
    boundedHomologicalPowerMonomials I hI i q ⊆
      boundedHomologicalPolynomials I hI i q := by
  rintro p ⟨s, a, ha, hs, he⟩
  exact ⟨s, MvPolynomial.monomial a 1, hs, ha, he⟩

theorem boundedHomologicalPolynomial_span_eq_monomials_rank
    (ρ : RankFunction V) (hI : IsPolymatroidalIdeal (rankIdeal k ρ)) (i q : ℕ) :
    Ideal.span (boundedHomologicalPolynomials (rankIdeal k ρ) hI i q) =
      Ideal.span (boundedHomologicalPowerMonomials (rankIdeal k ρ) hI i q) := by
  apply le_antisymm
  · rw [boundedHomologicalPowerMonomials_rank]
    apply Ideal.span_le.mpr
    rintro p ⟨s, f, hs, hf, he⟩
    rw [homologicalPowerPiece_rank] at hf
    have hfPow := powerShiftPiece_le_pow (k := k) ρ i s hf
    have hp : p = liftReesCoefficient ρ s f hfPow := Subtype.ext he
    rw [hp]
    by_cases hs0 : s = 0
    · have hf0 : f = 0 := by simpa only [hs0, powerShiftPiece_zero, Ideal.mem_bot] using hf
      have hz : liftReesCoefficient ρ s f hfPow = 0 := by
        apply Subtype.ext
        simp [liftReesCoefficient, hf0]
      rw [hz]
      exact Ideal.zero_mem _
    · apply liftReesCoefficient_mem_of_bases ρ i (by omega) _ _ f hf
      intro a ha haPow
      have hmem : MvPolynomial.monomial a (1 : k) ∈ powerShiftPiece ρ i s := by
        rw [powerShiftPiece_pos ρ i (by omega), rankShiftIdeal_eq_monomialIdeal,
          monomial_mem_iff]
        exact ⟨a, ha, le_rfl⟩
      exact Ideal.subset_span ⟨s, a, hmem, hs, rfl⟩
  · exact Ideal.span_mono (boundedHomologicalMonomials_subset_polynomials _ hI i q)

/-- Arbitrary polynomial homogeneous generators give exactly the same bounded
span as all bounded monomials. This includes the zero and unit ideals. -/
theorem boundedHomologicalPolynomial_span_eq_monomials
    (I : Ideal (MvPolynomial V k)) (hI : IsPolymatroidalIdeal I) (i q : ℕ) :
    Ideal.span (boundedHomologicalPolynomials I hI i q) =
      Ideal.span (boundedHomologicalPowerMonomials I hI i q) := by
  rcases hI.eq_bot_or_rank with h0 | ⟨ρ, he⟩
  · subst I
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro p ⟨s, f, hs, hf, he⟩
      have hf0 : f = 0 := by
        by_cases hs0 : s = 0
        · simpa [homologicalPowerPiece, hs0] using hf
        · simpa [homologicalPowerPiece, hs0, Ideal.bot_pow hs0] using hf
      have hp : p = 0 := by
        apply Subtype.ext
        simpa [hf0] using he
      rw [hp]
      exact Ideal.zero_mem _
    · exact Ideal.span_mono (boundedHomologicalMonomials_subset_polynomials _ hI i q)
  · subst I
    exact boundedHomologicalPolynomial_span_eq_monomials_rank ρ hI i q

/-- The exact least Rees generation bound permits arbitrary polynomial
homogeneous generators and arbitrary polynomial coefficients in the Rees ring. -/
theorem homologicalPower_polynomial_generation_bound_iff
    (I : Ideal (MvPolynomial V k)) (hI : IsPolymatroidalIdeal I)
    (ρ : RankFunction V) (he : I = rankIdeal k ρ) (hρ : ρ.Active)
    (i : ℕ) (hi0 : 0 < i) (hi : i ≤ eventualOffset ρ univ) (q : ℕ) :
    homologicalPowerIdeal I hI i = Ideal.span (boundedHomologicalPolynomials I hI i q) ↔
      globalPowerThreshold ρ i ≤ q := by
  rw [boundedHomologicalPolynomial_span_eq_monomials]
  exact homologicalPower_generation_bound_iff I hI ρ he hρ i hi0 hi q

end Characterizations.DependencyInterfaces
