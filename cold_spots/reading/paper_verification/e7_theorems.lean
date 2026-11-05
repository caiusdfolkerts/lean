module
public import PaperVerification.E7Transfer
public import PaperVerification.E8Theorems
@[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

/-- The E7* part of Theorem 1.1, in its true orthogonal-complement ambient space.
`e7DualSet_eq_projected` proves that the summed lattice is exactly the integral dual. -/
theorem coldSpot_E7_dual_iff_deepHole {α : ℝ} (hα : 0 < α) (x : zeroSumSpace) :
    IsE7ColdSpot α x ↔ IsE7DeepHole x :=
  e7_coldSpot_iff_deepHole_of_E8 hα (coldSpot_E8_iff_deepHole hα) x

/-- The full analytic minimum and equality claim in Theorem 6.2. -/
theorem e7Dual_gaussian_minimum {α : ℝ} (hα : 0 < α) :
    (∀ x, (gaussian α 0 * gaussian α (1 / 2)) ^ 4 / gaussian (2 * α) (1 / 4) ≤
      e7Gaussian α x) ∧
    (∀ x, e7Gaussian α x =
      (gaussian α 0 * gaussian α (1 / 2)) ^ 4 / gaussian (2 * α) (1 / 4) ↔ IsE7DeepHole x) :=
  e7Gaussian_minimum_of_E8 hα (coldSpot_E8_iff_deepHole hα)

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.coldSpot_E7_dual_iff_deepHole
#print axioms PaperVerification.ColdSpots.e7Dual_gaussian_minimum
