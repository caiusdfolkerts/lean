module

public import wishart.verified.overlap_obstruction

@[expose] public section

noncomputable section
open Matrix MeasureTheory ProbabilityTheory TauCeti.Probability

namespace WishartAudit

/- Literal coordinates for the three rank-one compression factors on page 12.
The measure here is the ordinary nonsingular Wishart measure, not a measure
defined by assuming the required moments or covariance identity. -/

theorem overlap_covariance_exact {α : ℝ} (hα : 1 < α) (a : ℝ) :
    covariance
      (fun X : selfAdjoint.submodule ℝ (Matrix (Fin 2) (Fin 2) ℝ) =>
        (X : Matrix (Fin 2) (Fin 2) ℝ) 0 0)
      (fun X =>
        dotProduct ![a, 1] ((X : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![a, 1]) *
        dotProduct ![-a, 1] ((X : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![-a, 1]))
      (nonsingularWishartMeasure α (1 : Matrix (Fin 2) (Fin 2) ℝ)) =
      4 * α * a ^ 2 * (α - 2 + (α + 2) * a ^ 2) := by
  exact Wishart.OverlapObstruction.covariance_rank_one_overlap hα a

theorem overlap_covariance_negative_exact {α a : ℝ}
    (hα₁ : 1 < α) (hα₂ : α < 2)
    (ha : 0 < a ^ 2) (hsmall : a ^ 2 < (2 - α) / (α + 2)) :
    covariance
      (fun X : selfAdjoint.submodule ℝ (Matrix (Fin 2) (Fin 2) ℝ) =>
        (X : Matrix (Fin 2) (Fin 2) ℝ) 0 0)
      (fun X =>
        dotProduct ![a, 1] ((X : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![a, 1]) *
        dotProduct ![-a, 1] ((X : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![-a, 1]))
      (nonsingularWishartMeasure α (1 : Matrix (Fin 2) (Fin 2) ℝ)) < 0 := by
  exact Wishart.OverlapObstruction.covariance_rank_one_overlap_neg hα₁ hα₂ ha hsmall

end WishartAudit
