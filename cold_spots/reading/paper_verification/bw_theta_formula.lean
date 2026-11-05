module

public import PaperVerification.BWNormalized

@[expose] public section
/-! # The printed Barnes–Wall minimum value

The value is computed at the explicit complementary quarter-coordinate witness.
The calculation uses the already proved actual Gaussian profile identity and
retains the sixteen cosets, so no separate unverified theta identity is needed.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

/-- The parity character is exactly the integer power printed in the paper. -/
theorem paritySign_eq_neg_one_zpow (z : ℤ) : paritySign z = (-1 : ℝ) ^ z := by
  exact (neg_one_zpow_eq_ite (α := ℝ) (n := z)).symm

/-- Literal correspondence with the alternating theta series of Section 2. -/
theorem alternatingGaussian_eq_literal (α t : ℝ) :
    alternatingGaussian α t =
      ∑' z : ℤ, (-1 : ℝ) ^ z * Real.exp (-α * ((z : ℝ) - t) ^ 2) := by
  unfold alternatingGaussian
  apply tsum_congr
  intro z
  rw [paritySign_eq_neg_one_zpow]

theorem paritySign_eq_of_even_iff {a b : ℤ} (h : Even a ↔ Even b) : paritySign a = paritySign b := by
  unfold paritySign
  by_cases ha : Even a
  · simp [ha, h.mp ha]
  · simp [ha, show ¬Even b from fun hb => ha (h.mpr hb)]

theorem paritySign_sq (a : ℤ) : paritySign a ^ 2 = 1 := by
  unfold paritySign
  split_ifs <;> norm_num

/-- The exact two-valued theta profile of every integral-sum quarter vector. -/
theorem gaussian_quarter_integerSum {α : ℝ} (hα : 0 < α) {x : Fin 8 → ℝ}
    (hx : QuarterGrid8 x) (hs : IntegerSum8 x) :
    setGaussian (dPlusSet 8) α x = gaussian α (1 / 4) ^ 8 +
      paritySign (∑ i, roundedInt x i) * alternatingGaussian α (1 / 4) ^ 8 := by
  have hr := (quarterGrid_iff_folded x).mp hx
  have hp := paritySign_eq_of_even_iff (quarter_parities_equiv hx hs)
  rw [setGaussian_dPlus_eq (by decide : 0 < 8) hα, dPlusGaussian_signed_fold hα]
  have hA : foldedAProduct α x = gaussian α (1 / 4) ^ 8 := by simp [foldedAProduct, hr]
  have hC : foldedCProduct α x = gaussian α (1 / 4) ^ 8 := by
    have he : (1 / 4 : ℝ) - 1 / 2 = -(1 / 4 : ℝ) := by ring
    simp only [foldedCProduct, hr, he, gaussian_even, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  have hB : foldedBProduct α x = alternatingGaussian α (1 / 4) ^ 8 := by simp [foldedBProduct, hr]
  have hD : foldedDProduct α x = alternatingGaussian α (1 / 4) ^ 8 := by
    have he : (1 / 4 : ℝ) - 1 / 2 = -(1 / 4 : ℝ) := by ring
    simp only [foldedDProduct, hr, he, alternatingGaussian_even, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  rw [hA, hB, hC, hD, ← hp]
  ring

theorem quarter_unit_profile_product {α : ℝ} (hα : 0 < α) {x : Fin 8 → ℝ}
    (hx : QuarterGrid8 x) (hs : IntegerSum8 x) :
    setGaussian (dPlusSet 8) α (x + e8FirstVector) * setGaussian (dPlusSet 8) α x =
      gaussian α (1 / 4) ^ 16 - alternatingGaussian α (1 / 4) ^ 16 := by
  have hg : -e8FirstVector ∈ bwMSet := bwMSet_neg e8FirstVector_mem_bwM
  have hx' : QuarterGrid8 (x + e8FirstVector) := by
    simpa only [sub_neg_eq_add] using quarterGrid_sub_bwM hx hg
  have hs' : IntegerSum8 (x + e8FirstVector) := by
    simpa only [sub_neg_eq_add] using integerSum_sub hs (bwM_integerSum hg)
  rw [gaussian_quarter_integerSum hα hx' hs', gaussian_quarter_integerSum hα hx hs]
  have hsum : (∑ i, roundedInt (x + e8FirstVector) i) = (∑ i, roundedInt x i) + 1 := by
    rw [e8FirstVector_eq_intVec, roundedInt_add_intVec]
    simp [Finset.sum_add_distrib, sum_bitUnit]
  rw [hsum, paritySign_add_one]
  have hp := paritySign_sq (∑ i, roundedInt x i)
  calc
    _ = gaussian α (1 / 4) ^ 16 - paritySign (∑ i, roundedInt x i) ^ 2 *
        alternatingGaussian α (1 / 4) ^ 16 := by ring
    _ = _ := by rw [hp, one_mul]

/-- Equation (28), exactly in its printed scalar notation. -/
theorem bwGammaMinimum_eq_quarter {α : ℝ} (hα : 0 < α) :
    bwGammaMinimum α = 16 * (gaussian α (1 / 4) ^ 16 - alternatingGaussian α (1 / 4) ^ 16) := by
  rw [← setGaussian_bwGamma_witness hα, setGaussian_bwGamma_eq_sum_profiles hα]
  have hq (q : BWQuotient) :
      bwThetaProfile α (bwQuarterPoint + e8FirstVector) q * bwThetaProfile α bwQuarterPoint q =
      gaussian α (1 / 4) ^ 16 - alternatingGaussian α (1 / 4) ^ 16 := by
    have hg := bwRepresentative_mem q
    have h := quarter_unit_profile_product hα (quarterGrid_sub_bwM bwQuarterPoint_quarterGrid hg)
      (integerSum_sub bwQuarterPoint_integerSum (bwM_integerSum hg))
    have heq : bwQuarterPoint - bwRepresentative q + e8FirstVector =
        bwQuarterPoint + e8FirstVector - bwRepresentative q := by abel
    simpa only [bwThetaProfile, heq] using h
  simp only [hq, Finset.sum_const, Finset.card_univ, card_bwQuotient, nsmul_eq_mul, Nat.cast_ofNat]

/-- The paper's attained minimum in the usual BW16 normalization. -/
theorem bw16_gaussian_minimum_literal {α : ℝ} (hα : 0 < α) :
    (∀ z : Fin 16 → ℝ,
      16 * (gaussian (2 * α) (1 / 4) ^ 16 - alternatingGaussian (2 * α) (1 / 4) ^ 16) ≤
        setGaussian bw16Set α z) ∧
      ∃ z, setGaussian bw16Set α z =
        16 * (gaussian (2 * α) (1 / 4) ^ 16 - alternatingGaussian (2 * α) (1 / 4) ^ 16) := by
  simpa only [bwGammaMinimum_eq_quarter (by positivity : 0 < 2 * α)] using bw16_gaussian_minimum hα

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.bwGammaMinimum_eq_quarter
#print axioms PaperVerification.ColdSpots.bw16_gaussian_minimum_literal
#print axioms PaperVerification.ColdSpots.alternatingGaussian_eq_literal
