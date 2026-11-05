import CommAlg.Polymatroid.PartitionThreshold
import CommAlg.Polymatroid.ShiftMultiplication

/-!
# Exact nonvanishing and consecutive ideal equality for power shifts

The partition thresholds are connected here to the actual polynomial ideals
on the right-hand side of the graded-Tor formula. Canonical ranks, recovered
from their integer bases, detect equality of those ideals.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem RankFunction.Active.scale {ρ : RankFunction V} (hρ : ρ.Active)
    {s : ℕ} (hs : 1 ≤ s) : (RankFunction.scale s ρ).Active := by
  intro A hA
  have h := hρ A hA
  change 1 ≤ s * ρ A
  nlinarith

@[simp] theorem powerCorrection_empty (ρ : RankFunction V) (i s : ℕ) :
    powerCorrection ρ i s ∅ = 0 := by
  have h := (powerCorrection_eq_eventual_iff ρ i s ∅).mpr (by simp)
  simpa [eventualCorrection, eventualOffset] using h

theorem power_homologicalRank (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) {s : ℕ} (hs : 1 ≤ s) (A : Finset V) :
    universalHomologicalRank (RankFunction.scale s ρ) i A =
      s * ρ A + powerCorrection ρ i s A := by
  by_cases hA : A = ∅
  · simp [hA]
  have hne := nonempty_iff_ne_empty.mpr hA
  rw [universalHomologicalRank_eq_active _ (hρ.scale hs),
    homologicalRank_defect _ (hρ.scale hs) i hne]
  simp only [partitionDefect_scale]
  rfl

theorem powerShiftFamily_nonempty_iff (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) {s : ℕ} (hs : 1 ≤ s) :
    (rankShiftFamily (RankFunction.scale s ρ) i).Nonempty ↔
      powerCorrection ρ i s univ = i := by
  rw [rankShiftFamily_nonempty_iff, power_homologicalRank ρ hρ i hs univ]
  change s * ρ univ + powerCorrection ρ i s univ = s * ρ univ + i ↔ _
  exact Nat.add_left_cancel_iff

theorem powerShiftFamily_nonempty_iff_threshold (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) (hi : i ≤ eventualOffset ρ univ) {s : ℕ} (hs : 1 ≤ s) :
    (rankShiftFamily (RankFunction.scale s ρ) i).Nonempty ↔
      powerThreshold ρ i univ ≤ s := by
  rw [powerShiftFamily_nonempty_iff ρ hρ i hs,
    powerCorrection_eq_degree_iff ρ i s univ hi]

theorem powerShiftFamily_empty_of_above (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) (hi : eventualOffset ρ univ < i) {s : ℕ} (hs : 1 ≤ s) :
    rankShiftFamily (RankFunction.scale s ρ) i = ∅ := by
  apply not_nonempty_iff_eq_empty.mp
  rw [powerShiftFamily_nonempty_iff ρ hρ i hs]
  exact ne_of_lt (powerCorrection_lt_degree ρ i s univ hi)

theorem power_homologicalRank_add_eq_iff (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) {s : ℕ} (hs : 1 ≤ s) :
    ρ.add (universalHomologicalRank (RankFunction.scale s ρ) i) =
        universalHomologicalRank (RankFunction.scale (s + 1) ρ) i ↔
      globalPowerThreshold ρ i ≤ s := by
  rw [← all_powerCorrection_step_eq_iff]
  constructor
  · intro h A
    have he := congrArg (fun g : RankFunction V => g A) h
    change ρ A + universalHomologicalRank (RankFunction.scale s ρ) i A =
      universalHomologicalRank (RankFunction.scale (s + 1) ρ) i A at he
    rw [power_homologicalRank ρ hρ i hs,
      power_homologicalRank ρ hρ i (by omega)] at he
    nlinarith
  · intro h
    apply RankFunction.ext_fun
    intro A
    change ρ A + universalHomologicalRank (RankFunction.scale s ρ) i A =
      universalHomologicalRank (RankFunction.scale (s + 1) ρ) i A
    rw [power_homologicalRank ρ hρ i hs,
      power_homologicalRank ρ hρ i (by omega), h A]
    nlinarith

section Ideals

variable {k : Type*} [CommSemiring k] [Nontrivial k]

theorem monomialIdeal_ne_bot_iff (B : Family V) :
    monomialIdeal k B ≠ ⊥ ↔ B.Nonempty := by
  constructor
  · intro h
    by_contra hn
    have he := not_nonempty_iff_eq_empty.mp hn
    exact h (by simp [he, monomialIdeal])
  · rintro ⟨a, ha⟩ hbot
    have hm : MvPolynomial.monomial a (1 : k) ∈ monomialIdeal k B :=
      Ideal.subset_span ⟨a, ha, rfl⟩
    rw [hbot] at hm
    simpa using hm

theorem rankShiftIdeal_ne_bot_iff (g : RankFunction V) (i : ℕ) :
    rankShiftIdeal k g i ≠ ⊥ ↔ (rankShiftFamily g i).Nonempty := by
  rw [rankShiftIdeal_eq_monomialIdeal, monomialIdeal_ne_bot_iff]

theorem powerShiftIdeal_ne_bot_iff_threshold (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) (hi : i ≤ eventualOffset ρ univ) {s : ℕ} (hs : 1 ≤ s) :
    rankShiftIdeal k (RankFunction.scale s ρ) i ≠ ⊥ ↔
      powerThreshold ρ i univ ≤ s := by
  rw [rankShiftIdeal_ne_bot_iff, powerShiftFamily_nonempty_iff_threshold ρ hρ i hi hs]

theorem powerShiftIdeal_eq_bot_of_above (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) (hi : eventualOffset ρ univ < i) {s : ℕ} (hs : 1 ≤ s) :
    rankShiftIdeal k (RankFunction.scale s ρ) i = ⊥ := by
  rw [rankShiftIdeal_eq_monomialIdeal, powerShiftFamily_empty_of_above ρ hρ i hi hs]
  simp [monomialIdeal]

theorem powerShiftIdeal_mul_le (ρ : RankFunction V) (i n s : ℕ) :
    (rankIdeal k ρ) ^ n * rankShiftIdeal k (RankFunction.scale s ρ) i ≤
      rankShiftIdeal k (RankFunction.scale (n + s) ρ) i := by
  have h := rankIdeal_mul_rankShiftIdeal_le (k := k)
    (RankFunction.scale n ρ) (RankFunction.scale s ρ) i
  have he : (RankFunction.scale n ρ).add (RankFunction.scale s ρ) =
      RankFunction.scale (n + s) ρ := by
    apply RankFunction.ext_fun
    intro A
    change n * ρ A + s * ρ A = (n + s) * ρ A
    exact (Nat.add_mul n s (ρ A)).symm
  rwa [rankIdeal_scale, he] at h

/-- After the first nonzero piece, consecutive actual ideals agree under
the Rees action exactly at and beyond the global threshold. -/
theorem powerShiftIdeal_mul_eq_iff (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) (hi : i ≤ eventualOffset ρ univ) {s : ℕ} (hs : 1 ≤ s)
    (hr : powerThreshold ρ i univ ≤ s) :
    rankIdeal k ρ * rankShiftIdeal k (RankFunction.scale s ρ) i =
        rankShiftIdeal k (RankFunction.scale (s + 1) ρ) i ↔
      globalPowerThreshold ρ i ≤ s := by
  have h0 := (rankShiftFamily_nonempty_iff _ i).mp
    ((powerShiftFamily_nonempty_iff_threshold ρ hρ i hi hs).mpr hr)
  have h1 := (rankShiftFamily_nonempty_iff _ i).mp
    ((powerShiftFamily_nonempty_iff_threshold ρ hρ i hi (by omega)).mpr
      (show powerThreshold ρ i univ ≤ s + 1 by omega))
  rw [rankShiftIdeal, if_pos h0, rankShiftIdeal, if_pos h1, ← rankIdeal_add]
  rw [(rankIdeal_injective k).eq_iff]
  exact power_homologicalRank_add_eq_iff ρ hρ i hs

end Ideals

end CommAlg.Polymatroid
