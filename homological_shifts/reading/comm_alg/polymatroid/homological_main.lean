import CommAlg.KoszulComplex.GradedTor
import CommAlg.Polymatroid.KoszulRankFormula
import CommAlg.Polymatroid.IdealProducts

/-! # The main homological-shift rank theorem

The left-hand sides below use the nonzero multigraded components of
Mathlib's actual derived tensor functor. The proof identifies their
homogeneous Koszul complexes with genuine matroid independence chains,
then applies the fully proved rank and coloop criterion.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

/-- All multigraded Betti support, with no degree, activity, or rank restriction. -/
theorem gradedBettiNonzero_rankBases_iff (g : RankFunction V) (a : Exponent V) (i : ℕ) :
    Koszul.GradedBettiNonzero (k := k) (rankBases g) a i ↔ a ∈ rankShiftFamily g i := by
  rw [Koszul.gradedBettiNonzero_iff_faces]
  exact koszulFaces_nonzeroHomology_iff_rankShiftFamily g a i

/-- Theorem 1.2, including zero layers, zero rank and inactive variables. -/
theorem homologicalShift_rankBases (g : RankFunction V) (i : ℕ) :
    Koszul.homologicalShift (k := k) (rankBases g) i = rankShiftIdeal k g i := by
  simp only [Koszul.homologicalShift, rankShiftIdeal_eq_monomialIdeal, monomialIdeal,
    gradedBettiNonzero_rankBases_iff]
  rfl

/-- The paper's partition-rank presentation on the active ground set. -/
theorem homologicalShift_rankBases_active (g : RankFunction V) (hg : g.Active) (i : ℕ) :
    Koszul.homologicalShift (k := k) (rankBases g) i =
      if homologicalRank g hg i univ = g univ + i then
        rankIdeal k (homologicalRank g hg i) else ⊥ := by
  rw [homologicalShift_rankBases, rankShiftIdeal]
  have he : universalHomologicalRank g i = homologicalRank g hg i := by
    apply RankFunction.ext_fun
    exact universalHomologicalRank_eq_active g hg i
  rw [he]

/-- Every nonempty equigenerated exchange family is covered by the rank theorem. -/
theorem homologicalShift_canonical (B : Family V) (hBne : B.Nonempty) (d : ℕ)
    (hdeg : Equigenerated B d) (hB : IsPolymatroidal B) (i : ℕ) :
    Koszul.homologicalShift (k := k) B i =
      rankShiftIdeal k (canonicalRank B hBne d hdeg hB) i := by
  simpa only [rankBases_canonical B hBne d hdeg hB] using
    (homologicalShift_rankBases (k := k) (canonicalRank B hBne d hdeg hB) i)

theorem gradedBettiNonzero_empty (a : Exponent V) (i : ℕ) :
    ¬ Koszul.GradedBettiNonzero (k := k) (∅ : Family V) a i := by
  rw [Koszul.gradedBettiNonzero_iff_faces, Simplicial.nonzeroHomology_iff_not_exactIn]
  apply not_not.mpr
  apply Simplicial.exactIn_of_no_face
  intro s hs
  obtain ⟨b, hb, _⟩ := Koszul.koszulFaces_contains hs
  exact (notMem_empty b hb).elim

/-- The zero ideal case, including every homological degree. -/
theorem homologicalShift_empty (i : ℕ) :
    Koszul.homologicalShift (k := k) (∅ : Family V) i = ⊥ := by
  simp [Koszul.homologicalShift, gradedBettiNonzero_empty]

/-- Homological shifts are polymatroidal, including the zero ideal. -/
theorem homologicalShift_polymatroidal (B : Family V) (hB : IsPolymatroidal B) (i : ℕ) :
    ∃ C : Family V, IsPolymatroidal C ∧
      Koszul.homologicalShift (k := k) B i = monomialIdeal k C := by
  by_cases hBne : B.Nonempty
  · obtain ⟨d, hdeg⟩ := hB.1
    let g := canonicalRank B hBne d hdeg hB
    refine ⟨rankShiftFamily g i, rankShiftFamily_polymatroidal g i, ?_⟩
    rw [homologicalShift_canonical B hBne d hdeg hB i, rankShiftIdeal_eq_monomialIdeal]
  · have he : B = ∅ := not_nonempty_iff_eq_empty.mp hBne
    subst B
    exact ⟨∅, hB, by simp [homologicalShift_empty, monomialIdeal]⟩

end CommAlg.Polymatroid
