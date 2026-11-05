import CommAlg.Polymatroid.PowerShiftLeastGeneration

/-! # The explicit inequalities selecting new minimal Rees generators -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V k : Type*} [Fintype V] [DecidableEq V] [CommRing k] [Nontrivial k]

/-- The post-Theorem-4.4 criterion identifies each individual new generator,
not only the degrees in which generators exist. -/
theorem minimalShiftRees_iff_rank_violation (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) (hi0 : 0 < i) (hi : i ≤ eventualOffset ρ univ) (s : ℕ)
    (hrs : powerThreshold ρ i univ < s) (a : Exponent V)
    (ha : a ∈ rankShiftFamily (ρ.scale s) i) :
    IsMinimalShiftReesMonomial (k := k) ρ i s a ↔
      ∃ A : Finset V, A.Nonempty ∧
        s * ρ A + powerCorrection ρ i (s - 1) A < subsetSum a A := by
  have hr := powerThreshold_pos ρ hi0 hi
  have hs : 0 < s := by omega
  have hs1 : 1 ≤ s - 1 := by omega
  have hprev : (rankShiftFamily (ρ.scale (s - 1)) i).Nonempty :=
    (powerShiftFamily_nonempty_iff_threshold ρ hρ i hi hs1).mpr (by omega)
  have htotal := (rankShiftFamily_nonempty_iff _ _).mp hprev
  let g := ρ.add (universalHomologicalRank (ρ.scale (s - 1)) i)
  have hdeg : a.degree = g univ := by
    have haD := rankShiftFamily_equigenerated (ρ.scale s) i a ha
    change a.degree = ρ univ + universalHomologicalRank (ρ.scale (s - 1)) i univ
    rw [htotal]
    change a.degree = ρ univ + ((s - 1) * ρ univ + i)
    change a.degree = s * ρ univ + i at haD
    have hss : s - 1 + 1 = s := by omega
    nlinarith
  have hprod : rankIdeal k ρ * powerShiftPiece ρ i (s - 1) = rankIdeal k g := by
    rw [powerShiftPiece_pos ρ i hs1, rankShiftIdeal, if_pos htotal, ← rankIdeal_add]
  have hg (A : Finset V) : g A = s * ρ A + powerCorrection ρ i (s - 1) A := by
    change ρ A + universalHomologicalRank (ρ.scale (s - 1)) i A = _
    rw [power_homologicalRank ρ hρ i hs1]
    have hss : s - 1 + 1 = s := by omega
    nlinarith
  rw [minimalShiftRees_iff ρ i hs a, and_iff_right ha, hprod,
    monomial_mem_rankIdeal_iff, ← upperFeasible_iff_lowerFeasible g hdeg]
  change (¬ ∀ A, subsetSum a A ≤ g A) ↔ _
  constructor
  · intro hn
    obtain ⟨A, hA⟩ := not_forall.mp hn
    have hne : A.Nonempty := by
      by_contra h
      have he := not_nonempty_iff_eq_empty.mp h
      simp [he] at hA
    exact ⟨A, hne, by simpa [hg A] using Nat.lt_of_not_ge hA⟩
  · rintro ⟨A, _, hA⟩ hb
    have h := hb A
    rw [hg] at h
    omega

end CommAlg.Polymatroid
