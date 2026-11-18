module

public import ToricPower.DivisorWeightCartier

/-!
# Values of coefficient transport

Equality of coefficient vectors changes only the proof of admissibility of a
Laurent section. The underlying Laurent polynomial is unchanged in either
direction. These opaque value lemmas keep later geometric computations small.
-/

@[expose] public noncomputable section

namespace ToricPower

variable {ι κ : Type*} [Fintype κ]

/-- Coefficient transport preserves the underlying Laurent polynomial. -/
theorem divisorCoefficientEqLinearEquiv_apply_val (R : Type*) [Semiring R]
    (A : ι → κ → ℤ) (ell : ℕ) (b c : ι → ℤ) (hbc : b = c)
    (x : DivisorSectionModule R A b ell) :
    (divisorCoefficientEqLinearEquiv R A ell b c hbc x).val = x.val := rfl

/-- The inverse transport preserves the same polynomial. -/
theorem divisorCoefficientEqLinearEquiv_symm_apply_val (R : Type*) [Semiring R]
    (A : ι → κ → ℤ) (ell : ℕ) (b c : ι → ℤ) (hbc : b = c)
    (x : DivisorSectionModule R A c ell) :
    ((divisorCoefficientEqLinearEquiv R A ell b c hbc).symm x).val = x.val := rfl

end ToricPower
