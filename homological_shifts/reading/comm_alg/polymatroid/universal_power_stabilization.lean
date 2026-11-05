import CommAlg.Polymatroid.PowerStabilization
import CommAlg.Polymatroid.RankShiftFormula
import CommAlg.Polymatroid.MultiRank

/-! # Uniform stabilization without an activity restriction

The universal partition rank treats inactive variables with their correct
integer block costs. Its defect formula proves the entire range `s ≥ i` for
arbitrary twists, and the resulting identities are equalities of actual
polynomial ideals, including the vanishing shift cases.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem cardinalLift_partition_cost_defect (g : RankFunction V)
    {A : Finset V} (P : Finpartition A) :
    partitionCost (cardinalLift g) P = g A + partitionDefect g P + partitionSlack P := by
  have hc := cardinalLift_cost_add_parts g P
  have hd := partitionDefect_add_rank g P
  have hs := partitionSlack_add_parts P
  omega

theorem universalAugmentedRank_defect (g : RankFunction V) (A : Finset V) :
    universalAugmentedRank g A =
      g A + finiteMinimum (fun P : Finpartition A => partitionDefect g P + partitionSlack P) := by
  change finiteMinimum (fun P : Finpartition A => partitionCost (cardinalLift g) P) = _
  rw [← finiteMinimum_add_const]
  congr 1
  funext P
  simpa only [Nat.add_assoc] using cardinalLift_partition_cost_defect g P

theorem universalHomologicalRank_defect (g : RankFunction V) (i : ℕ)
    {A : Finset V} (hA : A.Nonempty) :
    universalHomologicalRank g i A = g A +
      min i (finiteMinimum (fun P : Finpartition A => partitionDefect g P + partitionSlack P)) := by
  rw [universalHomologicalRank_apply g i hA, universalAugmentedRank_defect,
    Nat.add_min_add_left]

theorem twistedPower_universalHomologicalRank (η ρ : RankFunction V) (s i : ℕ)
    {A : Finset V} (hA : A.Nonempty) :
    universalHomologicalRank (twistedPowerRank η ρ s) i A =
      twistedPowerRank η ρ s A + min i
        (finiteMinimum (fun P : Finpartition A =>
          s * partitionDefect ρ P + partitionDefect η P + partitionSlack P)) := by
  rw [universalHomologicalRank_defect _ i hA]
  simp only [twistedPower_defect]

/-- The rank identity is valid for all ranks, including loops and the unit
ideal, with no deletion of coordinates. -/
theorem twistedPower_universalHomologicalRank_succ (η ρ : RankFunction V) (i s : ℕ)
    (hs : i ≤ s) (A : Finset V) :
    universalHomologicalRank (twistedPowerRank η ρ (s + 1)) i A =
      ρ A + universalHomologicalRank (twistedPowerRank η ρ s) i A := by
  by_cases hA : A = ∅
  · simp [hA]
  have hA' := Finset.nonempty_iff_ne_empty.mpr hA
  rw [twistedPower_universalHomologicalRank η ρ (s + 1) i hA',
    twistedPower_universalHomologicalRank η ρ s i hA']
  have hcap := cappedAffineMinimum_stable i
    (fun P : Finpartition A => partitionDefect ρ P)
    (fun P => partitionDefect η P + partitionSlack P) hs
  simp only [cappedAffineMinimum, ← Nat.add_assoc] at hcap
  rw [hcap]
  simp only [twistedPowerRank_apply, Nat.add_mul, Nat.one_mul]
  omega

theorem twistedPower_universalRank_succ (η ρ : RankFunction V) (i s : ℕ)
    (hs : i ≤ s) :
    universalHomologicalRank (twistedPowerRank η ρ (s + 1)) i =
      ρ.add (universalHomologicalRank (twistedPowerRank η ρ s) i) := by
  apply RankFunction.ext_fun
  exact twistedPower_universalHomologicalRank_succ η ρ i s hs

theorem twistedPower_universalTotal_rank_eq_iff (η ρ : RankFunction V) (i s : ℕ)
    (hs : i ≤ s) :
    universalHomologicalRank (twistedPowerRank η ρ (s + 1)) i univ =
        twistedPowerRank η ρ (s + 1) univ + i ↔
      universalHomologicalRank (twistedPowerRank η ρ s) i univ =
        twistedPowerRank η ρ s univ + i := by
  rw [twistedPower_universalHomologicalRank_succ η ρ i s hs univ]
  simp only [twistedPowerRank_apply, Nat.add_mul, Nat.one_mul]
  omega

section Ideals

variable (k : Type*) [CommSemiring k]

/-- The complete ideal identity underlying Theorem 1.1, including arbitrary
fixed twists and all zero shift layers. -/
theorem twistedPower_rankShiftIdeal_succ (η ρ : RankFunction V) (i s : ℕ)
    (hs : i ≤ s) :
    rankShiftIdeal k (twistedPowerRank η ρ (s + 1)) i =
      rankIdeal k ρ * rankShiftIdeal k (twistedPowerRank η ρ s) i := by
  by_cases h0 : universalHomologicalRank (twistedPowerRank η ρ s) i univ =
      twistedPowerRank η ρ s univ + i
  · have h1 := (twistedPower_universalTotal_rank_eq_iff η ρ i s hs).mpr h0
    rw [rankShiftIdeal, if_pos h1, rankShiftIdeal, if_pos h0,
      twistedPower_universalRank_succ η ρ i s hs, rankIdeal_add]
  · have h1 : ¬ universalHomologicalRank (twistedPowerRank η ρ (s + 1)) i univ =
        twistedPowerRank η ρ (s + 1) univ + i :=
      fun h => h0 ((twistedPower_universalTotal_rank_eq_iff η ρ i s hs).mp h)
    simp [rankShiftIdeal, h1, h0]

theorem rankIdeal_twistedPower (η ρ : RankFunction V) (s : ℕ) :
    rankIdeal k (twistedPowerRank η ρ s) = rankIdeal k η * rankIdeal k ρ ^ s := by
  rw [twistedPowerRank, rankIdeal_add, rankIdeal_scale]

theorem power_rankShiftIdeal_succ (ρ : RankFunction V) (i s : ℕ) (hs : i ≤ s) :
    rankShiftIdeal k (ρ.scale (s + 1)) i =
      rankIdeal k ρ * rankShiftIdeal k (ρ.scale s) i := by
  have he (n : ℕ) : twistedPowerRank zeroRank ρ n = ρ.scale n := by
    apply RankFunction.ext_fun
    intro A
    simp [twistedPowerRank_apply, RankFunction.scale]
  simpa only [he] using twistedPower_rankShiftIdeal_succ k zeroRank ρ i s hs

end Ideals

section SeveralColors

variable {J : Type*} [Fintype J] [DecidableEq J]

theorem multiRank_erase_decompose (ρ : J → RankFunction V) (s : J →₀ ℕ) (j : J) :
    multiRank ρ s = (multiRank ρ (s.erase j)).add ((ρ j).scale (s j)) := by
  have he : s.erase j + Finsupp.single j (s j) = s := by
    ext x
    by_cases hx : x = j
    · subst x; simp
    · simp [Finsupp.erase_apply, hx, Ne.symm hx]
  conv_lhs => rw [← he]
  rw [multiRank_add, multiRank_single]

theorem twistedMultiRank_erase_decompose (η : RankFunction V)
    (ρ : J → RankFunction V) (s : J →₀ ℕ) (j : J) :
    η.add (multiRank ρ s) =
      twistedPowerRank (η.add (multiRank ρ (s.erase j))) (ρ j) (s j) := by
  rw [multiRank_erase_decompose ρ s j]
  apply RankFunction.ext_fun
  intro A
  change η A + (multiRank ρ (s.erase j) A + s j * ρ j A) =
    (η A + multiRank ρ (s.erase j) A) + s j * ρ j A
  omega

theorem twistedMultiRank_succ_decompose (η : RankFunction V)
    (ρ : J → RankFunction V) (s : J →₀ ℕ) (j : J) :
    η.add (multiRank ρ (s + Finsupp.single j 1)) =
      twistedPowerRank (η.add (multiRank ρ (s.erase j))) (ρ j) (s j + 1) := by
  rw [twistedMultiRank_erase_decompose η ρ (s + Finsupp.single j 1) j]
  have he : (s + Finsupp.single j 1).erase j = s.erase j := by
    ext x
    by_cases hx : x = j
    · subst x; simp
    · simp [Finsupp.erase_apply, hx, Ne.symm hx]
  simp only [he, Finsupp.add_apply, Finsupp.single_eq_same]

/-- Corollary 4.1 at the rank-ideal level: each coordinate stabilizes in the
same complete range, with all other colors absorbed into an arbitrary twist. -/
theorem multi_rankShiftIdeal_succ (k : Type*) [CommSemiring k]
    (η : RankFunction V) (ρ : J → RankFunction V) (s : J →₀ ℕ)
    (i : ℕ) (j : J) (hs : i ≤ s j) :
    rankShiftIdeal k (η.add (multiRank ρ (s + Finsupp.single j 1))) i =
      rankIdeal k (ρ j) * rankShiftIdeal k (η.add (multiRank ρ s)) i := by
  rw [twistedMultiRank_succ_decompose, twistedMultiRank_erase_decompose η ρ s j]
  exact twistedPower_rankShiftIdeal_succ k _ _ i (s j) hs

end SeveralColors

end CommAlg.Polymatroid
