import CommAlg.IntegralClosure.HomologicalRees
import CommAlg.Polymatroid.PowerShiftNewGenerators

/-!
# Theorem 4.4 for genuine homological shifts in the ordinary Rees algebra

All module pieces below are the homological shifts defined by the nonzero
multigraded components of the actual derived tensor functor. Minimality means
minimality under divisibility by actual Rees monomials, including degree-zero
polynomial factors. Generation is an equality of actual ideal spans.
-/

noncomputable section

namespace CommAlg

open Classical Finset Polymatroid

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

def IsMinimalHomologicalPowerMonomial (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i s : ℕ) (a : Exponent V) : Prop :=
  MvPolynomial.monomial a (1 : k) ∈ homologicalPowerPiece I hI i s ∧
    ∀ r b, r ≤ s → b ≤ a →
      MvPolynomial.monomial b (1 : k) ∈ homologicalPowerPiece I hI i r →
      MvPolynomial.monomial (a - b) (1 : k) ∈ I ^ (s - r) →
      r = s ∧ b = a

/-- The actual module monomials through a specified Rees degree. -/
def boundedHomologicalPowerMonomials (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i q : ℕ) : Set (reesAlgebra I) :=
  {p | ∃ s a, MvPolynomial.monomial a (1 : k) ∈ homologicalPowerPiece I hI i s ∧
    s ≤ q ∧ p.val = Polynomial.monomial s (MvPolynomial.monomial a 1)}

def minimalHomologicalPowerMonomials (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i : ℕ) : Set (reesAlgebra I) :=
  {p | ∃ s a, IsMinimalHomologicalPowerMonomial I hI i s a ∧
    p.val = Polynomial.monomial s (MvPolynomial.monomial a 1)}

theorem isMinimalHomologicalPowerMonomial_rank (ρ : RankFunction V)
    (hI : IsPolymatroidalIdeal (rankIdeal k ρ)) (i s : ℕ) (a : Exponent V) :
    IsMinimalHomologicalPowerMonomial (rankIdeal k ρ) hI i s a ↔
      IsMinimalShiftReesMonomial (k := k) ρ i s a := by
  simp only [IsMinimalHomologicalPowerMonomial, IsMinimalShiftReesMonomial,
    homologicalPowerPiece_rank]

theorem boundedHomologicalPowerMonomials_rank (ρ : RankFunction V)
    (hI : IsPolymatroidalIdeal (rankIdeal k ρ)) (i q : ℕ) :
    boundedHomologicalPowerMonomials (rankIdeal k ρ) hI i q =
      boundedShiftReesSet (k := k) ρ i q := by
  ext p
  constructor
  · rintro ⟨s, a, ha, hs, he⟩
    rw [homologicalPowerPiece_rank] at ha
    exact ⟨s, a, ha, hs, Subtype.ext he⟩
  · rintro ⟨s, a, ha, hs, rfl⟩
    exact ⟨s, a, by simpa only [homologicalPowerPiece_rank] using ha, hs, rfl⟩

theorem minimalHomologicalPowerMonomials_rank (ρ : RankFunction V)
    (hI : IsPolymatroidalIdeal (rankIdeal k ρ)) (i : ℕ) :
    minimalHomologicalPowerMonomials (rankIdeal k ρ) hI i =
      minimalShiftReesSet (k := k) ρ i := by
  ext p
  constructor
  · rintro ⟨s, a, ha, he⟩
    have ha' := (isMinimalHomologicalPowerMonomial_rank ρ hI i s a).mp ha
    exact ⟨s, a, ha', Subtype.ext he⟩
  · rintro ⟨s, a, ha, rfl⟩
    exact ⟨s, a, (isMinimalHomologicalPowerMonomial_rank ρ hI i s a).mpr ha, rfl⟩

/-- The semantic minimal monomials really generate the whole homological Rees ideal. -/
theorem homologicalPowerIdeal_eq_span_minimal (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (ρ : RankFunction V) (he : I = rankIdeal k ρ)
    (i : ℕ) :
    homologicalPowerIdeal I hI i = Ideal.span (minimalHomologicalPowerMonomials I hI i) := by
  subst I
  rw [homologicalPowerIdeal_rank, minimalHomologicalPowerMonomials_rank]
  exact shiftReesIdeal_eq_span_minimal ρ i

/-- The zero-module branch of Theorem 4.4, for the genuine homological Rees ideal. -/
theorem homologicalPowerIdeal_eq_bot_of_above (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (ρ : RankFunction V) (he : I = rankIdeal k ρ)
    (hρ : ρ.Active) (i : ℕ) (hi : eventualOffset ρ univ < i) :
    homologicalPowerIdeal I hI i = ⊥ := by
  subst I
  rw [homologicalPowerIdeal_rank]
  exact shiftReesIdeal_eq_bot_of_above ρ hρ i hi

/-- Every positive power has a nonzero shift exactly at and after the first threshold. -/
theorem homologicalShift_power_nonzero_iff (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (ρ : RankFunction V) (he : I = rankIdeal k ρ)
    (hρ : ρ.Active) (i : ℕ) (hi : i ≤ eventualOffset ρ univ)
    (s : ℕ) (hs : 1 ≤ s) :
    homologicalShiftIdeal (I ^ s) (hI.pow s) i ≠ ⊥ ↔ powerThreshold ρ i univ ≤ s := by
  subst I
  rw [homologicalShiftIdeal_eq_rankShiftIdeal _ _ (ρ.scale s)
    (rankIdeal_scale k ρ s).symm]
  exact powerShiftIdeal_ne_bot_iff_threshold ρ hρ i hi hs

/-- The exact interval of actual minimal monomial module-generator degrees. -/
theorem homologicalPower_minimal_degree_iff (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (ρ : RankFunction V) (he : I = rankIdeal k ρ)
    (hρ : ρ.Active) (i : ℕ) (hi0 : 0 < i) (hi : i ≤ eventualOffset ρ univ) (s : ℕ) :
    (∃ a, IsMinimalHomologicalPowerMonomial I hI i s a) ↔
      powerThreshold ρ i univ ≤ s ∧ s ≤ globalPowerThreshold ρ i := by
  subst I
  simp only [isMinimalHomologicalPowerMonomial_rank]
  exact minimalShiftRees_degree_iff ρ hρ i hi0 hi s

/-- The exact least bound is an equality of spans in Mathlib's ordinary Rees algebra. -/
theorem homologicalPower_generation_bound_iff (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (ρ : RankFunction V) (he : I = rankIdeal k ρ)
    (hρ : ρ.Active) (i : ℕ) (hi0 : 0 < i) (hi : i ≤ eventualOffset ρ univ) (q : ℕ) :
    homologicalPowerIdeal I hI i = Ideal.span (boundedHomologicalPowerMonomials I hI i q) ↔
      globalPowerThreshold ρ i ≤ q := by
  subst I
  rw [homologicalPowerIdeal_rank, boundedHomologicalPowerMonomials_rank]
  exact shiftReesIdeal_generation_bound_iff ρ hρ i hi0 hi q

/-- The paper's individual new-generator criterion, with genuine Betti support as input. -/
theorem homologicalPower_minimal_iff_rank_violation (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (ρ : RankFunction V) (he : I = rankIdeal k ρ)
    (hρ : ρ.Active) (i : ℕ) (hi0 : 0 < i) (hi : i ≤ eventualOffset ρ univ)
    (s : ℕ) (hrs : powerThreshold ρ i univ < s) (a : Exponent V)
    (ha : Koszul.GradedBettiNonzero (k := k) (rankBases (ρ.scale s)) a i) :
    IsMinimalHomologicalPowerMonomial I hI i s a ↔
      ∃ A : Finset V, A.Nonempty ∧
        s * ρ A + powerCorrection ρ i (s - 1) A < subsetSum a A := by
  subst I
  rw [isMinimalHomologicalPowerMonomial_rank]
  exact minimalShiftRees_iff_rank_violation ρ hρ i hi0 hi s hrs a
    ((gradedBettiNonzero_rankBases_iff _ _ _).mp ha)

end CommAlg
