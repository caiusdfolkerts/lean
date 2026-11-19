module

public import VolumePolynomials.Holonomy
public import Mathlib.NumberTheory.Niven
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

@[expose] public section
noncomputable section

namespace VolumePolynomials.Holonomy

/-- The paper's angle is chosen in `(0, π)`, so the area formula has positive sine denominator. -/
def angle : ℝ := Real.arccos (1 / 3)

theorem cos_angle : Real.cos angle = 1 / 3 := by
  first
  | exact Real.cos_arccos (by norm_num) (by norm_num)

theorem angle_pos : 0 < angle := Real.arccos_pos.mpr (by norm_num)

theorem angle_lt_pi : angle < Real.pi := Real.arccos_lt_pi.mpr (by norm_num)

theorem sin_angle_pos : 0 < Real.sin angle := Real.sin_pos_of_pos_of_lt_pi angle_pos angle_lt_pi

/-- The angular parameter in Theorem 7.3 is not a rational multiple of π. -/
theorem angle_not_rational_multiple_pi {θ : ℝ} (hθ : Real.cos θ = 1 / 3) :
    ¬ ∃ q : ℚ, θ = q * Real.pi := by
  first
  | intro hrat
    have hn := niven hrat (show ∃ q : ℚ, Real.cos θ = q from ⟨1 / 3, by simpa using hθ⟩)
    norm_num [hθ] at hn


end VolumePolynomials.Holonomy
