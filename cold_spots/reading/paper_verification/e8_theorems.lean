module
public import PaperVerification.DnTheorems
public import PaperVerification.DnSigns
public import PaperVerification.ThetaEmpirical
@[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

theorem folded_equality_signs_iff_E8_hole {α : ℝ} (hα : 0 < α) (x : Fin 8 → ℝ) :
    FoldedThetaEquality x ∧ FoldedSignCondition α x ↔ E8FoldedHole x := by
  have hb0 : 0 < alternatingGaussian α 0 ^ 8 := pow_pos (alternatingGaussian_zero_pos hα) 8
  have hbq : 0 < alternatingGaussian α (1 / 4) ^ 8 :=
    pow_pos (alternatingGaussian_pos hα (by norm_num) (by norm_num)) 8
  constructor
  · rintro ⟨hx, hi, hh⟩
    rcases hx with h0 | hq | hhf | hbal
    · apply Or.inl
      refine ⟨h0, ?_⟩
      rw [folded_B_constant α x 0 h0] at hi
      exact hi.resolve_left hb0.ne'
    · apply Or.inr ∘ Or.inr ∘ Or.inr
      refine ⟨hq, ?_, ?_⟩
      · rw [folded_B_constant α x (1 / 4) hq] at hi
        exact hi.resolve_left hbq.ne'
      · rw [folded_D_constant α x (1 / 4) hq,
          show (1 / 4 : ℝ) - 1 / 2 = -(1 / 4) by ring, alternatingGaussian_even] at hh
        exact hh.resolve_left hbq.ne'
    · apply Or.inr ∘ Or.inl
      refine ⟨hhf, ?_⟩
      rw [folded_D_constant α x (1 / 2) hhf, sub_self] at hh
      exact hh.resolve_left hb0.ne'
    · exact Or.inr (Or.inr (Or.inl hbal))
  · rintro (⟨h0, hi⟩ | ⟨hh, hp⟩ | hbal | ⟨hq, hi, hh⟩)
    · refine ⟨Or.inl h0, Or.inr hi, Or.inl ?_⟩
      rw [folded_D_constant α x 0 h0, zero_sub, alternatingGaussian_even,
        alternatingGaussian_half, zero_pow (by decide : 8 ≠ 0)]
    · refine ⟨Or.inr (Or.inr (Or.inl hh)), Or.inl ?_, Or.inr hp⟩
      rw [folded_B_constant α x (1 / 2) hh, alternatingGaussian_half, zero_pow (by decide : 8 ≠ 0)]
    · obtain ⟨hb,hd⟩ := folded_alternating_zero_of_balanced (by decide : 0 < 8) hbal
      exact ⟨Or.inr (Or.inr (Or.inr hbal)), Or.inl hb, Or.inl hd⟩
    · exact ⟨Or.inr (Or.inl hq), Or.inr hi, Or.inr hh⟩

lemma thetaMomentNumerator_eight {α : ℝ} (hα : 0 < α) (x : Fin 8 → ℝ) :
    thetaMomentNumerator hα (foldedEmpirical (by decide : 0 < 8) x) =
      foldedAProduct α x + foldedCProduct α x - foldedBProduct α x - foldedDProduct α x := by
  rw [thetaMomentNumerator_empirical]
  norm_num

/-- The full exceptional dimension-eight equality analysis in canonical folded
coordinates, including both parity restrictions on the quarter family. -/
theorem dPlusGaussian_eight_eq_min_iff {α : ℝ} (hα : 0 < α) (x : Fin 8 → ℝ) :
    dPlusGaussian α x = (gaussian α 0 * gaussian α (1 / 2)) ^ 4 ↔ E8FoldedHole x := by
  rw [← folded_equality_signs_iff_E8_hole hα x,
    ← folded_theta_equality_iff (by decide : 0 < 8) hα x,
    ← dPlusGaussian_eq_folded_lower_iff hα x, thetaMomentNumerator_eight]
  have hbase := theta_geometric_mean_inequality hα (foldedEmpirical (by decide : 0 < 8) x)
  rw [thetaMomentNumerator_eight] at hbase
  have hfold := dPlusGaussian_folded_lower hα x
  constructor
  · intro heq
    constructor <;> linarith
  · rintro ⟨h₁,h₂⟩
    linarith

theorem dPlusGaussian_eight_lower {α : ℝ} (hα : 0 < α) (x : Fin 8 → ℝ) :
    (gaussian α 0 * gaussian α (1 / 2)) ^ 4 ≤ dPlusGaussian α x := by
  have h := dPlusGaussian_lower (by decide : 8 ≤ 8) hα x
  norm_num at h
  exact h

/-- The E8 part of Theorem 1.1, for every point in the real ambient space and
every positive Gaussian parameter. -/
theorem coldSpot_E8_iff_deepHole {α : ℝ} (hα : 0 < α) (x : Fin 8 → ℝ) :
    IsColdSpot (dPlusSet 8) α x ↔ IsDeepHole (dPlusSet 8) x := by
  rw [isDeepHole_E8_iff, ← dPlusGaussian_eight_eq_min_iff hα]
  constructor
  · intro h
    obtain ⟨y,hy⟩ := exists_balancedHalfGrid (by decide : Even 8)
    have hxy := h y
    rw [setGaussian_dPlus_eq (by decide : 0 < 8) hα,
      setGaussian_dPlus_eq (by decide : 0 < 8) hα,
      dPlusGaussian_of_balanced (by decide : 0 < 8) hα hy] at hxy
    norm_num at hxy
    exact le_antisymm hxy (dPlusGaussian_eight_lower hα x)
  · intro heq y
    rw [setGaussian_dPlus_eq (by decide : 0 < 8) hα,
      setGaussian_dPlus_eq (by decide : 0 < 8) hα, heq]
    exact dPlusGaussian_eight_lower hα y

/-- The entire D_n^+ family in Theorem 1.1, with no omitted dimension or
additional geometric or analytic hypothesis. -/
theorem coldSpot_dPlus_iff_deepHole {n : ℕ} (hn : 8 ≤ n) (heven : Even n)
    {α : ℝ} (hα : 0 < α) (x : Fin n → ℝ) :
    IsColdSpot (dPlusSet n) α x ↔ IsDeepHole (dPlusSet n) x := by
  rcases eq_or_lt_of_le hn with rfl | hlt
  · exact coldSpot_E8_iff_deepHole hα x
  · exact coldSpot_dPlus_iff_deepHole_above_eight hlt heven hα x

lemma even_dimension_half_cast {n : ℕ} (heven : Even n) :
    (n : ℝ) / 2 = ((n / 2 : ℕ) : ℝ) := by
  obtain ⟨k,rfl⟩ := heven
  rw [show (k + k) / 2 = k by omega]
  push_cast
  ring

/-- Theorem 3.3's attained minimum in the paper's integer-exponent notation. -/
theorem dPlusGaussian_minimum {n : ℕ} (hn : 8 ≤ n) (heven : Even n)
    {α : ℝ} (hα : 0 < α) :
    (∀ x, (gaussian α 0 * gaussian α (1 / 2)) ^ (n / 2) ≤ setGaussian (dPlusSet n) α x) ∧
    (∃ x, setGaussian (dPlusSet n) α x = (gaussian α 0 * gaussian α (1 / 2)) ^ (n / 2)) := by
  have hn0 : 0 < n := by omega
  constructor
  · intro x
    rw [setGaussian_dPlus_eq hn0 hα]
    have h := dPlusGaussian_lower hn hα x
    rwa [even_dimension_half_cast heven, Real.rpow_natCast] at h
  · obtain ⟨x,hx⟩ := exists_balancedHalfGrid heven
    refine ⟨x, ?_⟩
    rw [setGaussian_dPlus_eq hn0 hα, dPlusGaussian_of_balanced hn0 hα hx,
      even_dimension_half_cast heven, Real.rpow_natCast]

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.coldSpot_dPlus_iff_deepHole
#print axioms PaperVerification.ColdSpots.dPlusGaussian_minimum
