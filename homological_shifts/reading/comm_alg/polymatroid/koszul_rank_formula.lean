import CommAlg.KoszulComplex.FaceMatroid
import CommAlg.Polymatroid.KoszulRankUniversal
import CommAlg.Polymatroid.RankShiftFormula

/-! # The full rank formula for the actual upper Koszul complex

Every degree and every normalized monotone submodular rank is included.
The subsequent derived-Tor theorem transports this exact statement to
the homological shift ideal.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [LinearOrder V]

theorem mem_rankShiftFamily_iff_lower (g : RankFunction V) (i : ℕ) (a : Exponent V) :
    a ∈ rankShiftFamily g i ↔ a.degree = g univ + i ∧
      LowerFeasible g.lower a ∧ UpperFeasible (universalAugmentedRank g) a := by
  rw [mem_rankShiftFamily_iff]
  constructor
  · rintro ⟨hdeg, hb⟩
    refine ⟨hdeg, ?_, ?_⟩
    · intro U
      have hcomp := hb Uᶜ
      have hR := universalHomologicalRank_le_add g i Uᶜ
      have hL := g.lower_add_compl U
      have hS := subsetSum_add_compl a U
      omega
    · intro A
      exact (hb A).trans (shiftRankValue_le_u g (universalAugmentedRank g) i A)
  · rintro ⟨hdeg, hLower, hUpper⟩
    refine ⟨hdeg, ?_⟩
    intro A
    by_cases hA : A = ∅
    · simp [hA]
    rw [universalHomologicalRank_apply g i (Finset.nonempty_iff_ne_empty.mpr hA)]
    apply le_min
    · have hcomp := hLower Aᶜ
      have hL := g.lower_add_compl Aᶜ
      have hS := subsetSum_add_compl a A
      simp only [compl_compl] at hL
      omega
    · exact hUpper A

section Homology

variable {k : Type*} [CommRing k] [Nontrivial k]

theorem koszulFaces_nonzeroHomology_iff_rankShiftFamily
    (g : RankFunction V) (a : Exponent V) (i : ℕ) :
    Simplicial.NonzeroHomology (k := k) (Koszul.koszulFaces (rankBases g) a) i ↔
      a ∈ rankShiftFamily g i := by
  by_cases ha : Contains (rankBases g) a
  · have hLower := (contains_rankBases_iff g a).mp ha
    rw [Koszul.koszulFaces_eq_independenceFaces (rankBases g) g
      (contains_rankBases_iff g) a hLower,
      koszulConstraint_nonzeroHomology_iff_universal_full g hLower i,
      mem_rankShiftFamily_iff_lower]
    simp only [hLower, true_and]
    rfl
  · have hn : ¬ Simplicial.NonzeroHomology (k := k)
        (Koszul.koszulFaces (rankBases g) a) i := by
      rw [Simplicial.nonzeroHomology_iff_not_exactIn]
      apply not_not.mpr
      apply Simplicial.exactIn_of_no_face
      intro s hs
      exact (ha (Koszul.koszulFaces_contains hs)).elim
    have hm : a ∉ rankShiftFamily g i := by
      intro hm
      exact ha ((contains_rankBases_iff g a).mpr
        ((mem_rankShiftFamily_iff_lower g i a).mp hm).2.1)
    simp only [hn, hm]

end Homology

end CommAlg.Polymatroid
