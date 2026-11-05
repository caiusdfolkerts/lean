module

public import PaperVerification.ToricPrimitiveRelations
public import Mathlib.Data.Finset.Max

@[expose] public section

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan.PrimitiveRelation

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} (R : «Σ».PrimitiveRelation)

/-- The actual least positive coefficient on a nonempty focus. -/
def minimumCoefficient (hne : R.negative.Nonempty) : ℕ :=
  R.coefficient (Classical.choose (R.negative.exists_min_image R.coefficient hne))

theorem minimumCoefficient_spec (hne : R.negative.Nonempty) :
    0 < R.minimumCoefficient hne ∧
      (∃ p ∈ R.negative, R.coefficient p = R.minimumCoefficient hne) ∧
      ∀ v ∈ R.negative, R.minimumCoefficient hne ≤ R.coefficient v := by
  let p := Classical.choose (R.negative.exists_min_image R.coefficient hne)
  have hp := Classical.choose_spec (R.negative.exists_min_image R.coefficient hne)
  exact ⟨R.coefficient_pos p hp.1, ⟨p, hp.1, rfl⟩, hp.2⟩

end PaperVerification.ToricGeometry.SmoothCompleteFan.PrimitiveRelation
