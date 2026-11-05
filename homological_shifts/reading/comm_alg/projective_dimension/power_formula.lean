import CommAlg.ProjectiveDimension.RankIdeal
import CommAlg.Polymatroid.PowerShiftInterval

/-! # Corollary 4.3: exact projective dimensions of powers

The left-hand side is Mathlib's categorical projective dimension of the
actual polynomial ideal. The minimum ranges over every set partition.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem shiftLength_active_defect (g : RankFunction V) (hg : g.Active) :
    shiftLength g =
      finiteMinimum (fun P : Finpartition (univ : Finset V) =>
        partitionDefect g P + partitionSlack P) := by
  have h := shiftLength_add_degree g
  rw [universalAugmentedRank_eq_active g hg,
    augmentedPartitionRank_defect g hg] at h
  omega

theorem shiftLength_scale_partition (ρ : RankFunction V) (hρ : ρ.Active)
    (s : ℕ) (hs : 1 ≤ s) :
    shiftLength (ρ.scale s) =
      finiteMinimum (fun P : Finpartition (univ : Finset V) =>
        s * partitionDefect ρ P + partitionSlack P) := by
  rw [shiftLength_active_defect _ (hρ.scale hs)]
  simp only [partitionDefect_scale]

theorem partitionMinimum_eq_eventual (ρ : RankFunction V) (s : ℕ)
    (hs : eventualOffset ρ (univ : Finset V) ≤ s) :
    finiteMinimum (fun P : Finpartition (univ : Finset V) =>
      s * partitionDefect ρ P + partitionSlack P) = eventualOffset ρ univ := by
  apply le_antisymm
  · obtain ⟨P, hd, hb⟩ := eventualOffset_attained ρ (univ : Finset V)
    simpa only [hd, hb, Nat.mul_zero, Nat.zero_add] using
      finiteMinimum_le (fun P : Finpartition (univ : Finset V) =>
        s * partitionDefect ρ P + partitionSlack P) P
  · apply le_finiteMinimum
    intro P
    by_cases hd : partitionDefect ρ P = 0
    · exact (eventualOffset_le_slack ρ P hd).trans (Nat.le_add_left _ _)
    · have hpos : 1 ≤ partitionDefect ρ P := by omega
      nlinarith

theorem shiftLength_scale_eventual (ρ : RankFunction V) (hρ : ρ.Active)
    (s : ℕ) (hs : max 1 (eventualOffset ρ univ) ≤ s) :
    shiftLength (ρ.scale s) = eventualOffset ρ univ := by
  rw [shiftLength_scale_partition ρ hρ s ((le_max_left _ _).trans hs)]
  exact partitionMinimum_eq_eventual ρ s ((le_max_right _ _).trans hs)

end CommAlg.Polymatroid

namespace CommAlg.ProjectiveDimension

open Classical Finset CategoryTheory CommAlg.Polymatroid

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

/-- Formula (4.3), with no additional restriction on the number of variables or powers. -/
theorem rankIdeal_power_projectiveDimension (ρ : RankFunction V) (hρ : ρ.Active)
    (s : ℕ) (hs : 1 ≤ s) :
    projectiveDimension (ModuleCat.of (MvPolynomial V k) ↥((rankIdeal k ρ) ^ s)) =
      (finiteMinimum (fun P : Finpartition (univ : Finset V) =>
        s * partitionDefect ρ P + partitionSlack P) : WithBot ℕ∞) := by
  rw [← rankIdeal_scale, rankIdeal_projectiveDimension,
    shiftLength_scale_partition ρ hρ s hs]

/-- The eventual projective dimension is attained by the paper's stated uniform bound. -/
theorem rankIdeal_power_projectiveDimension_eventual (ρ : RankFunction V) (hρ : ρ.Active)
    (s : ℕ) (hs : max 1 (eventualOffset ρ univ) ≤ s) :
    projectiveDimension (ModuleCat.of (MvPolynomial V k) ↥((rankIdeal k ρ) ^ s)) =
      (eventualOffset ρ univ : WithBot ℕ∞) := by
  rw [← rankIdeal_scale, rankIdeal_projectiveDimension,
    shiftLength_scale_eventual ρ hρ s hs]

/-- Literal ideal form of Corollary 4.3 for any proved rank presentation. -/
theorem polymatroidal_power_projectiveDimension (I : Ideal (MvPolynomial V k))
    (ρ : RankFunction V) (hI : I = rankIdeal k ρ) (hρ : ρ.Active)
    (s : ℕ) (hs : 1 ≤ s) :
    projectiveDimension (ModuleCat.of (MvPolynomial V k) ↥(I ^ s)) =
      (finiteMinimum (fun P : Finpartition (univ : Finset V) =>
        s * partitionDefect ρ P + partitionSlack P) : WithBot ℕ∞) := by
  subst I
  exact rankIdeal_power_projectiveDimension ρ hρ s hs

theorem polymatroidal_power_projectiveDimension_eventual (I : Ideal (MvPolynomial V k))
    (ρ : RankFunction V) (hI : I = rankIdeal k ρ) (hρ : ρ.Active)
    (s : ℕ) (hs : max 1 (eventualOffset ρ univ) ≤ s) :
    projectiveDimension (ModuleCat.of (MvPolynomial V k) ↥(I ^ s)) =
      (eventualOffset ρ univ : WithBot ℕ∞) := by
  subst I
  exact rankIdeal_power_projectiveDimension_eventual ρ hρ s hs

end CommAlg.ProjectiveDimension
