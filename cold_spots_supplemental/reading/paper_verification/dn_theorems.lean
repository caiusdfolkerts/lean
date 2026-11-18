module
public import PaperVerification.DnEquality
public import PaperVerification.ThetaInequality
@[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

/-- Theorem 3.3's lower bound over every dimension n>=8 and every positive alpha. -/
theorem dPlusGaussian_lower {n : ℕ} (hn : 8 ≤ n) {α : ℝ} (hα : 0 < α)
    (x : Fin n → ℝ) :
    (gaussian α 0 * gaussian α (1 / 2)) ^ ((n : ℝ) / 2) ≤ dPlusGaussian α x :=
  dPlusGaussian_lower_of_theta hn hα x (theta_geometric_mean_inequality hα _)

/-- The exact Gaussian equality set in every dimension strictly above eight. -/
theorem dPlusGaussian_eq_min_iff_balanced {n : ℕ} (hn : 8 < n) {α : ℝ} (hα : 0 < α)
    (x : Fin n → ℝ) :
    dPlusGaussian α x = (gaussian α 0 * gaussian α (1 / 2)) ^ ((n : ℝ) / 2) ↔
      BalancedHalfGrid x := by
  constructor
  · intro heq
    obtain ⟨_, _, hA, hC⟩ := dPlusGaussian_equality_products_of_theta hn hα x
      (theta_geometric_mean_inequality hα _) heq
    exact balanced_of_folded_product_equalities hα x hA hC
  · exact dPlusGaussian_of_balanced (by omega) hα

/-- The literal half-integer-grid equality set in equation (10), including the
usual count of noninteger coordinates and the whole even dimension range n>8. -/
theorem dPlusGaussian_eq_min_iff_paperHalfGrid {n : ℕ} (hn : 8 < n) (heven : Even n)
    {α : ℝ} (hα : 0 < α) (x : Fin n → ℝ) :
    dPlusGaussian α x = (gaussian α 0 * gaussian α (1 / 2)) ^ ((n : ℝ) / 2) ↔
      PaperHalfGrid x := by
  rw [dPlusGaussian_eq_min_iff_balanced hn hα x, balancedHalfGrid_iff_paperHalfGrid heven x]

/-- The D_n^+ part of Theorem 1.1 above dimension eight, stated for the actual
infinite lattice Gaussian and actual Euclidean deep-hole predicate. -/
theorem coldSpot_dPlus_iff_deepHole_above_eight {n : ℕ} (hn : 8 < n) (heven : Even n)
    {α : ℝ} (hα : 0 < α) (x : Fin n → ℝ) :
    IsColdSpot (dPlusSet n) α x ↔ IsDeepHole (dPlusSet n) x :=
  coldSpot_dPlus_iff_deepHole_of_theta hn heven hα (theta_geometric_mean_inequality hα) x

end PaperVerification.ColdSpots
