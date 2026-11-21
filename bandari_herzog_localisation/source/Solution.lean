module
public import Mathlib
public import characterizations

/-! # The Bandari–Herzog localisation conjecture -/

@[expose] public noncomputable section
namespace BandariHerzog
open Classical CommAlg.Polymatroid Characterizations
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

/-- Theorem 1.1 of the supplied paper. -/
theorem localisation_conjecture {I : Ideal (MvPolynomial V k)}
    (hI : IsMonomialIdeal I) (_hne : I ≠ ⊥) :
    IsPolymatroidalIdeal I ↔
      ∀ U : Finset V, HasLinearResolution (monomialLocalization k I U) := by
  exact Characterizations.monomialIdeal_polymatroidal_iff_local_linear hI

/-- Theorem 1.2 of the supplied paper. -/
theorem intersection_type {B : Family V} (hB : B.Nonempty) (ha : Antichain B)
    (hl : LocallyEquigenerated B)
    (hi : ∃ e : Finset V → ℕ, monomialIdeal k B =
      ⨅ U : Finset V, (variableIdeal (k := k) U) ^ e U) : IsPolymatroidal B := by
  exact (Characterizations.polymatroidal_iff_intersectionType_localEquigenerated (k := k) hB ha).2 ⟨hl, hi⟩

/-- Lemma 2.1 of the supplied paper. -/
theorem lower_rank_supermodular {B : Family V} (hB : B.Nonempty)
    (hl : LocallyEquigenerated B) (A C : Finset V) :
    lowerRank B A + lowerRank B C ≤ lowerRank B (A ∪ C) + lowerRank B (A ∩ C) := by
  exact CommAlg.Polymatroid.lowerRank_supermodular hB hl A C

/-- Closing socle criterion, page 4 of the supplied paper. -/
theorem local_socle_criterion {B : Family V} (hB : B.Nonempty) (ha : Antichain B) :
    IsPolymatroidal B ↔ LocallyEquigenerated B ∧
      ∀ U : Finset V, monomialIdeal k (localFamily B U) ≠ ⊤ →
        SocleConcentrated (monomialIdeal k (localFamily B U)) (lowerRank B U - 1) := by
  exact Characterizations.polymatroidal_iff_local_socles k hB ha

end BandariHerzog
