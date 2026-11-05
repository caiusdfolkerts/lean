module

public import VolumePolynomials.BinaryMixedInequalities
public import VolumePolynomials.BinaryBoundaryRealization

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace VolumePolynomials.BinarySimplex

/-- Proposition A.1, in the literal binomial normalization of the paper,
with all nonnegative weights and all degenerate zero patterns retained. -/
theorem appendix_A_realization_iff {d : ℕ} (hd : 0 < d) (a : ℕ → ℝ) :
    (∃ K L : Body d, Realizes d a K L) ↔ BinarySequences.Criterion d a := by
  first
  | constructor
    · rintro ⟨K, L, h⟩
      exact BinaryMixed.criterion_of_realizes hd h
    · intro h
      obtain ⟨k, lam, hk, hlam, hreal⟩ := appendix_A_sufficiency hd h
      exact ⟨AxisSimplex.axisBody k, AxisSimplex.axisBody lam, hreal⟩

end VolumePolynomials.BinarySimplex
