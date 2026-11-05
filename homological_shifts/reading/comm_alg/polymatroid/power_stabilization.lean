import CommAlg.Polymatroid.PartitionDefect
import CommAlg.Polymatroid.AffineMinimum

/-! # The exact rank identity behind uniform stabilization of twisted powers -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem twistedPower_active (η ρ : RankFunction V)
    (h : (twistedPowerRank η ρ 1).Active) {s : ℕ} (hs : 1 ≤ s) :
    (twistedPowerRank η ρ s).Active := by
  intro A hA
  have h1 := h A hA
  simp only [twistedPowerRank_apply, Nat.one_mul] at h1 ⊢
  nlinarith

/-- Uniform stabilization retains arbitrary fixed twists and the entire
range `s ≥ i`. Its application to shift ideals uses the separate Tor theorem. -/
theorem twistedPower_homologicalRank_succ (η ρ : RankFunction V) (i s : ℕ)
    (hs : i ≤ s) (h0 : (twistedPowerRank η ρ s).Active)
    (h1 : (twistedPowerRank η ρ (s + 1)).Active) (A : Finset V) :
    homologicalRank (twistedPowerRank η ρ (s + 1)) h1 i A =
      ρ A + homologicalRank (twistedPowerRank η ρ s) h0 i A := by
  by_cases hA : A = ∅
  · simp [hA]
  have hA' := Finset.nonempty_iff_ne_empty.mpr hA
  rw [twistedPower_homologicalRank η ρ (s + 1) i h1 hA',
    twistedPower_homologicalRank η ρ s i h0 hA']
  have hcap := cappedAffineMinimum_stable i
    (fun P : Finpartition A => partitionDefect ρ P)
    (fun P => partitionDefect η P + partitionSlack P) hs
  simp only [cappedAffineMinimum, ← Nat.add_assoc] at hcap
  rw [hcap]
  simp only [twistedPowerRank_apply, Nat.add_mul, Nat.one_mul]
  omega

/-- The total-rank nonvanishing conditions agree for consecutive powers
throughout the uniform stabilization range. -/
theorem twistedPower_total_rank_eq_iff (η ρ : RankFunction V) (i s : ℕ)
    (hs : i ≤ s) (h0 : (twistedPowerRank η ρ s).Active)
    (h1 : (twistedPowerRank η ρ (s + 1)).Active) :
    homologicalRank (twistedPowerRank η ρ (s + 1)) h1 i univ =
        twistedPowerRank η ρ (s + 1) univ + i ↔
      homologicalRank (twistedPowerRank η ρ s) h0 i univ =
        twistedPowerRank η ρ s univ + i := by
  rw [twistedPower_homologicalRank_succ η ρ i s hs h0 h1 univ]
  simp only [twistedPowerRank_apply, Nat.add_mul, Nat.one_mul]
  omega

end CommAlg.Polymatroid
