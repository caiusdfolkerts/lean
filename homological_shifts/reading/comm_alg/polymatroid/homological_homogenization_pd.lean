import CommAlg.Polymatroid.HomologicalHomogenization
import CommAlg.ProjectiveDimension.RankIdeal

/-! # Theorem 5.1 with the actual projective dimension

This final statement combines the genuine Tor support, the actual ideal sum,
and Mathlib's categorical projective dimension.  All conclusions refer to the
unique minimal monomial generators of that sum.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset CategoryTheory

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

local instance : LinearOrder (Option V) := (inferInstance : LinearOrder (WithBot V))

/-- The complete homogenization assertion, including the actual projective
dimension and both directions of the characterization of every minimal
generator by a nonzero actual Tor multidegree.  Loops and the unit ideal are
allowed in addition to the paper's nonzero proper active case. -/
theorem homological_homogenization (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (g : RankFunction V) (he : I = rankIdeal k g) :
    ∃ p : ℕ,
      p = shiftLength g ∧
      projectiveDimension (ModuleCat.of (MvPolynomial V k) I) = (p : WithBot ℕ∞) ∧
      ∃ hH : IsPolymatroidalIdeal (homogenizedHomologicalIdeal I hI p),
        Equigenerated (idealGenerators (homogenizedHomologicalIdeal I hI p) hH)
          (g univ + p) ∧
        (∀ A : Finset (Option V),
          upperRank (idealGenerators (homogenizedHomologicalIdeal I hI p) hH) A =
            homogenizedShiftRank g A) ∧
        (∀ e : Exponent (Option V),
          e ∈ idealGenerators (homogenizedHomologicalIdeal I hI p) hH ↔
            ∃ i ≤ p, ∃ a : Exponent V,
              Koszul.GradedBettiNonzero (k := k) (idealGenerators I hI) a i ∧
                e = a.optionElim (p - i)) := by
  refine ⟨shiftLength g, rfl,
    CommAlg.ProjectiveDimension.polymatroidalIdeal_projectiveDimension I g he,
    homogenizedHomologicalIdeal_polymatroidal I hI g he,
    homogenizedHomologicalIdeal_degree I hI g he,
    homogenizedHomologicalIdeal_canonicalRank I hI g he, ?_⟩
  intro e
  rw [homogenizedHomologicalIdeal_generators I hI g he, mem_rankBases]
  exact homogenized_rankBase_iff_actualBetti I hI g he e

/-- No rank presentation is an additional hypothesis on an actual nonzero
polymatroidal ideal: it is constructed from its exchange generators. -/
theorem homological_homogenization_exists_rank (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (hne : I ≠ ⊥) :
    ∃ g : RankFunction V, I = rankIdeal k g ∧
      projectiveDimension (ModuleCat.of (MvPolynomial V k) I) =
        (shiftLength g : WithBot ℕ∞) ∧
      IsPolymatroidalIdeal (homogenizedHomologicalIdeal I hI (shiftLength g)) := by
  obtain ⟨g, he⟩ := hI.exists_rank hne
  exact ⟨g, he,
    CommAlg.ProjectiveDimension.polymatroidalIdeal_projectiveDimension I g he,
    homogenizedHomologicalIdeal_polymatroidal I hI g he⟩

end CommAlg.Polymatroid
