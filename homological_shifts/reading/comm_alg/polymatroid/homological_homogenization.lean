import CommAlg.Polymatroid.IdealBridge
import CommAlg.Polymatroid.HomogenizedIdeal
import Mathlib.Order.WithBot

/-! # Homogenization of the genuine total Betti support

This module proves the actual polynomial-ideal identity, the exact derived-Tor
base description, its degree, exchange property, and canonical rank. The
projective-dimension identification of the rank gap is supplied separately by
the checked projective-resolution and linear-quotient argument.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

local instance : LinearOrder (Option V) := (inferInstance : LinearOrder (WithBot V))

/-- The literal sum in Theorem 5.1 in the polynomial ring with the extra
variable `none`. Original variables are included by `some`. -/
def homogenizedHomologicalIdeal (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (p : ℕ) : Ideal (MvPolynomial (Option V) k) :=
  ∑ i ∈ Finset.range (p + 1),
    Ideal.span {MvPolynomial.X (R := k) none ^ (p - i)} *
      Ideal.map (MvPolynomial.rename some).toRingHom (homologicalShiftIdeal I hI i)

/-- The equality is between actual ideals, and the summands are the genuine
homological-shift ideals defined from Mathlib's derived Tor. -/
theorem homogenizedHomologicalIdeal_eq_rankIdeal (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (g : RankFunction V) (he : I = rankIdeal k g) :
    homogenizedHomologicalIdeal I hI (shiftLength g) =
      rankIdeal k (homogenizedShiftRank g) := by
  unfold homogenizedHomologicalIdeal
  simp_rw [homologicalShiftIdeal_eq_rankShiftIdeal I hI g he]
  exact homogenizedShiftIdeal_eq_rankIdeal k g

/-- The precise base description in terms of all nonzero actual Tor
multidegrees, with both implications checked. -/
theorem homogenized_rankBase_iff_actualBetti (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (g : RankFunction V) (he : I = rankIdeal k g)
    (e : Exponent (Option V)) :
    IsRankBase (homogenizedShiftRank g) e ↔
      ∃ i ≤ shiftLength g, ∃ a : Exponent V,
        Koszul.GradedBettiNonzero (k := k) (idealGenerators I hI) a i ∧
          e = a.optionElim (shiftLength g - i) := by
  rw [idealGenerators_eq_of_presentation I hI (rankBases g) (rankBases_polymatroidal g) he]
  simp_rw [gradedBettiNonzero_rankBases_iff]
  exact isRankBase_homogenizedShift_iff g e

theorem homogenizedHomologicalIdeal_polymatroidal (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (g : RankFunction V) (he : I = rankIdeal k g) :
    IsPolymatroidalIdeal (homogenizedHomologicalIdeal I hI (shiftLength g)) := by
  rw [homogenizedHomologicalIdeal_eq_rankIdeal I hI g he]
  exact isPolymatroidalIdeal_rankIdeal _

theorem homogenizedHomologicalIdeal_generators (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (g : RankFunction V) (he : I = rankIdeal k g) :
    idealGenerators (homogenizedHomologicalIdeal I hI (shiftLength g))
      (homogenizedHomologicalIdeal_polymatroidal I hI g he) =
        rankBases (homogenizedShiftRank g) :=
  idealGenerators_eq_of_presentation _ _ _ (rankBases_polymatroidal _)
    (homogenizedHomologicalIdeal_eq_rankIdeal I hI g he)

/-- Every minimal generator has precisely the asserted total degree. -/
theorem homogenizedHomologicalIdeal_degree (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (g : RankFunction V) (he : I = rankIdeal k g) :
    Equigenerated (idealGenerators (homogenizedHomologicalIdeal I hI (shiftLength g))
      (homogenizedHomologicalIdeal_polymatroidal I hI g he)) (g univ + shiftLength g) := by
  rw [homogenizedHomologicalIdeal_generators I hI g he]
  have hd := rankBases_equigenerated (homogenizedShiftRank g)
  have hr : homogenizedShiftRank g univ = g univ + shiftLength g := by
    rw [homogenizedShiftRank, RankFunction.homogenize_univ, ← shiftLength_add_degree]
    omega
  rwa [hr] at hd

/-- The displayed rank is canonical, recovered by maximization over the
actual minimal generator exponents. -/
theorem homogenizedHomologicalIdeal_canonicalRank (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (g : RankFunction V) (he : I = rankIdeal k g)
    (A : Finset (Option V)) :
    upperRank (idealGenerators (homogenizedHomologicalIdeal I hI (shiftLength g))
      (homogenizedHomologicalIdeal_polymatroidal I hI g he)) A = homogenizedShiftRank g A := by
  rw [homogenizedHomologicalIdeal_generators I hI g he, upperRank_rankBases]

@[simp] theorem homogenizedShiftRank_on_original (g : RankFunction V) (A : Finset V) :
    homogenizedShiftRank g (A.image some) = universalAugmentedRank g A := by
  exact RankFunction.homogenize_some g _ _ A

@[simp] theorem homogenizedShiftRank_with_new_variable (g : RankFunction V) (A : Finset V) :
    homogenizedShiftRank g A.insertNone = shiftLength g + g A := by
  exact RankFunction.homogenize_insertNone g _ _ A

theorem homogenizedShiftRank_active_original (g : RankFunction V) (hg : g.Active)
    (A : Finset V) : homogenizedShiftRank g (A.image some) = A.card + partitionRank g A := by
  rw [homogenizedShiftRank_on_original, universalAugmentedRank_eq_active g hg A]
  rfl

/-- The exact Betti support is independent of the coefficient field (in fact,
it is independent of every nontrivial commutative coefficient ring). -/
theorem gradedBettiNonzero_rankBases_field_independent
    {l : Type u} [CommRing l] [Nontrivial l] (g : RankFunction V) (a : Exponent V) (i : ℕ) :
    Koszul.GradedBettiNonzero (k := k) (rankBases g) a i ↔
      Koszul.GradedBettiNonzero (k := l) (rankBases g) a i := by
  rw [gradedBettiNonzero_rankBases_iff, gradedBettiNonzero_rankBases_iff]

end CommAlg.Polymatroid
