import CommAlg.Polymatroid.PowerShiftRees

/-! # Exact degrees of the minimal monomial generators of the actual Rees ideal -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V k : Type*} [Fintype V] [DecidableEq V] [CommRing k] [Nontrivial k]

theorem exists_monomial_generator_notMem_iff (B : Family V)
    (J : Ideal (MvPolynomial V k)) (hJ : J ≤ monomialIdeal k B) :
    (∃ a ∈ B, MvPolynomial.monomial a (1 : k) ∉ J) ↔ J ≠ monomialIdeal k B := by
  constructor
  · rintro ⟨a, ha, hn⟩ he
    apply hn
    rw [he]
    exact Ideal.subset_span ⟨a, ha, rfl⟩
  · intro h
    by_contra hn
    push_neg at hn
    apply h
    apply le_antisymm hJ
    apply Ideal.span_le.mpr
    rintro f ⟨a, ha, rfl⟩
    exact hn a ha

theorem preceding_powerShift_product_le (ρ : RankFunction V) (i : ℕ)
    {s : ℕ} (hs : 0 < s) :
    rankIdeal k ρ * powerShiftPiece ρ i (s - 1) ≤ powerShiftPiece ρ i s := by
  have h := powerShiftPiece_action (k := k) ρ i 1 (s - 1)
  simpa only [pow_one, Nat.add_sub_of_le hs] using h

theorem exists_minimalShiftRees_iff (ρ : RankFunction V) (i : ℕ)
    {s : ℕ} (hs : 0 < s) :
    (∃ a, IsMinimalShiftReesMonomial (k := k) ρ i s a) ↔
      rankIdeal k ρ * powerShiftPiece ρ i (s - 1) ≠ powerShiftPiece ρ i s := by
  simp_rw [minimalShiftRees_iff ρ i hs]
  have he : powerShiftPiece (k := k) ρ i s =
      monomialIdeal k (rankShiftFamily (RankFunction.scale s ρ) i) := by
    rw [powerShiftPiece_pos ρ i hs, rankShiftIdeal_eq_monomialIdeal]
  rw [he]
  exact exists_monomial_generator_notMem_iff _ _
    (he ▸ preceding_powerShift_product_le ρ i hs)

theorem powerShiftPiece_eq_bot_before (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) (hi : i ≤ eventualOffset ρ univ) {s : ℕ}
    (hs : s < powerThreshold ρ i univ) : powerShiftPiece (k := k) ρ i s = ⊥ := by
  by_cases hs0 : s = 0
  · simp [hs0]
  · rw [powerShiftPiece_pos ρ i (by omega)]
    by_contra hn
    have hr := (powerShiftIdeal_ne_bot_iff_threshold ρ hρ i hi (by omega)).mp hn
    omega

theorem powerShiftPiece_ne_bot_at (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) (hi0 : 0 < i) (hi : i ≤ eventualOffset ρ univ) :
    powerShiftPiece (k := k) ρ i (powerThreshold ρ i univ) ≠ ⊥ := by
  have hr := powerThreshold_pos ρ hi0 hi
  rw [powerShiftPiece_pos ρ i hr]
  exact (powerShiftIdeal_ne_bot_iff_threshold ρ hρ i hi hr).mpr le_rfl

/-- Theorem 4.4's exact interval, for semantic minimal monomials of the genuine
Rees ideal. Every degree in the interval occurs and every other degree is absent. -/
theorem minimalShiftRees_degree_iff (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) (hi0 : 0 < i) (hi : i ≤ eventualOffset ρ univ) (s : ℕ) :
    (∃ a, IsMinimalShiftReesMonomial (k := k) ρ i s a) ↔
      powerThreshold ρ i univ ≤ s ∧ s ≤ globalPowerThreshold ρ i := by
  have hr : 1 ≤ powerThreshold ρ i univ := powerThreshold_pos ρ hi0 hi
  have hrS := powerThreshold_le_global ρ i univ
  by_cases hs0 : s = 0
  · subst s
    constructor
    · rintro ⟨a, ha⟩
      have hp := minimalShiftRees_positive ha
      omega
    · omega
  have hs : 0 < s := by omega
  rw [exists_minimalShiftRees_iff ρ i hs]
  by_cases hsr : s < powerThreshold ρ i univ
  · have hz := powerShiftPiece_eq_bot_before (k := k) ρ hρ i hi hsr
    have hp : rankIdeal k ρ * powerShiftPiece ρ i (s - 1) = ⊥ := by
      apply le_antisymm _ bot_le
      exact hz ▸ preceding_powerShift_product_le ρ i hs
    rw [hz, hp]
    constructor
    · intro h
      exact (h rfl).elim
    · intro h
      omega
  by_cases hsrEq : s = powerThreshold ρ i univ
  · have hp : powerShiftPiece (k := k) ρ i (s - 1) = ⊥ :=
      powerShiftPiece_eq_bot_before ρ hρ i hi (by omega)
    have hn : powerShiftPiece (k := k) ρ i s ≠ ⊥ := by
      rw [hsrEq]
      exact powerShiftPiece_ne_bot_at ρ hρ i hi0 hi
    rw [hp, Ideal.mul_bot]
    constructor
    · intro _
      omega
    · intro _ he
      exact hn he.symm
  have hprev : 1 ≤ s - 1 := by omega
  have hprevr : powerThreshold ρ i univ ≤ s - 1 := by omega
  have he := powerShiftIdeal_mul_eq_iff (k := k) ρ hρ i hi hprev hprevr
  rw [powerShiftPiece_pos ρ i hprev, powerShiftPiece_pos ρ i hs]
  have hsucc : s - 1 + 1 = s := by omega
  rw [hsucc] at he
  simp only [ne_eq, he]
  omega

theorem powerShiftPiece_eq_bot_of_above (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) (hi : eventualOffset ρ univ < i) (s : ℕ) :
    powerShiftPiece (k := k) ρ i s = ⊥ := by
  by_cases hs : s = 0
  · simp [hs]
  · rw [powerShiftPiece_pos ρ i (by omega)]
    exact powerShiftIdeal_eq_bot_of_above ρ hρ i hi (by omega)

/-- Above the eventual projective-dimension offset the entire actual Rees
ideal, and therefore its graded module, is zero. -/
theorem shiftReesIdeal_eq_bot_of_above (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) (hi : eventualOffset ρ univ < i) : shiftReesIdeal (k := k) ρ i = ⊥ := by
  apply bot_unique
  intro p hp
  change p = 0
  apply Subtype.ext
  apply Polynomial.ext
  intro s
  have h := hp s
  rw [powerShiftPiece_eq_bot_of_above ρ hρ i hi s] at h
  simpa using h

/-- The endpoints satisfy all of the quantitative bounds in Theorem 4.4. -/
theorem powerShift_generator_endpoints (ρ : RankFunction V) (i : ℕ)
    (hi0 : 0 < i) (hi : i ≤ eventualOffset ρ univ) :
    1 ≤ powerThreshold ρ i univ ∧
      powerThreshold ρ i univ ≤ globalPowerThreshold ρ i ∧
      globalPowerThreshold ρ i ≤ i :=
  ⟨powerThreshold_pos ρ hi0 hi, powerThreshold_le_global ρ i univ,
    globalPowerThreshold_le ρ i⟩

end CommAlg.Polymatroid
