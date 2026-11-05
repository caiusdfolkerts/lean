import CommAlg.Polymatroid.IdealBridge
import CommAlg.Polymatroid.PowerShiftInterval
import CommAlg.KoszulComplex.BettiNumbers

/-! # The ideal-level rank formula and numerical Betti correspondence -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

/-- Theorem 1.2 as a literal equality of actual homological-shift ideals. -/
theorem homologicalShiftIdeal_partitionFormula (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (g : RankFunction V) (he : I = rankIdeal k g)
    (hg : g.Active) (i : ℕ) :
    homologicalShiftIdeal I hI i =
      if homologicalRank g hg i univ = g univ + i then
        rankIdeal k (homologicalRank g hg i) else ⊥ := by
  rw [homologicalShiftIdeal_of_presentation I hI (rankBases g) (rankBases_polymatroidal g) he]
  exact homologicalShift_rankBases_active g hg i

theorem homologicalShiftIdeal_generators (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (g : RankFunction V) (he : I = rankIdeal k g) (i : ℕ) :
    idealGenerators (homologicalShiftIdeal I hI i) (homologicalShiftIdeal_polymatroidal I hI i) =
      rankShiftFamily g i := by
  apply idealGenerators_eq_of_presentation _ _ _ (rankShiftFamily_polymatroidal g i)
  rw [homologicalShiftIdeal_eq_rankShiftIdeal I hI g he i, rankShiftIdeal_eq_monomialIdeal]

/-- The rank displayed in the main theorem is the canonical rank of the
actual minimal generators whenever the homological shift is nonzero. -/
theorem homologicalShiftIdeal_canonicalRank (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (g : RankFunction V) (he : I = rankIdeal k g) (i : ℕ)
    (hne : homologicalShiftIdeal I hI i ≠ ⊥) (A : Finset V) :
    upperRank (idealGenerators (homologicalShiftIdeal I hI i)
      (homologicalShiftIdeal_polymatroidal I hI i)) A = universalHomologicalRank g i A := by
  rw [homologicalShiftIdeal_generators I hI g he i]
  apply rankShiftFamily_upperRank
  rw [homologicalShiftIdeal_eq_rankShiftIdeal I hI g he i] at hne
  exact (rankShiftIdeal_ne_bot_iff g i).mp hne

section Field

variable {l : Type u} [Field l]

/-- The numerical multigraded Betti numbers have precisely the stated
rank-family support; finite-dimensionality is independently proved. -/
theorem bettiNumber_rankBases_pos_iff (g : RankFunction V) (a : Exponent V) (i : ℕ) :
    0 < Koszul.bettiNumber (k := l) (rankBases g) a i ↔ a ∈ rankShiftFamily g i := by
  rw [Koszul.bettiNumber_pos_iff, gradedBettiNonzero_rankBases_iff]

theorem bettiNumber_ideal_pos_iff (I : Ideal (MvPolynomial V l))
    (hI : IsPolymatroidalIdeal I) (g : RankFunction V) (he : I = rankIdeal l g)
    (a : Exponent V) (i : ℕ) :
    0 < Koszul.bettiNumber (k := l) (idealGenerators I hI) a i ↔
      a ∈ rankShiftFamily g i := by
  rw [idealGenerators_eq_of_presentation I hI (rankBases g) (rankBases_polymatroidal g) he,
    bettiNumber_rankBases_pos_iff]

end Field

end CommAlg.Polymatroid
