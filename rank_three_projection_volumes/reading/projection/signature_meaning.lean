module

public import Mathlib.LinearAlgebra.QuadraticForm.Signature
public import Mathlib.Data.Real.Basic

/-!
# Signature as the signs in a diagonalization

The positive and negative indices used by the main theorem are exactly the
usual counts of positive and negative diagonal coefficients. The radical
dimension is exactly the count of zero coefficients. This equivalence follows
from Mathlib's existence and uniqueness statements for Sylvester's law of
inertia, with no additional spectral or geometric hypothesis.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace RankThreeProjection

open QuadraticMap

/-- The three indices in the principal statement are precisely the usual
diagonal-sign signature. A diagonalization is a genuine linear isometry of
quadratic forms, and its existence is supplied by Mathlib. -/
theorem signature_iff_diagonal_sign_counts
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (Q : QuadraticForm ℝ E) (p m z : ℕ) :
    (sigPos Q = p ∧ sigNeg Q = m ∧ Module.finrank ℝ Q.radical = z) ↔
      ∃ w : Fin (Module.finrank ℝ E) → ℝ,
        Equivalent Q (weightedSumSquares ℝ w) ∧
        {i | 0 < w i}.ncard = p ∧ {i | w i < 0}.ncard = m ∧
        {i | w i = 0}.ncard = z := by
  letI : Invertible (2 : ℝ) := invertibleOfNonzero (two_ne_zero : (2 : ℝ) ≠ 0)
  constructor
  · intro h
    obtain ⟨w, hw⟩ := Q.equivalent_weightedSumSquares
    exact ⟨w, hw,
      (QuadraticForm.sigPos_of_equiv_weightedSumSquares hw).symm.trans h.1,
      (QuadraticForm.sigNeg_of_equiv_weightedSumSquares hw).symm.trans h.2.1,
      (QuadraticForm.finrank_radical_of_equiv_weightedSumSquares hw).symm.trans h.2.2⟩
  · rintro ⟨w, hw, hp, hm, hz⟩
    exact ⟨(QuadraticForm.sigPos_of_equiv_weightedSumSquares hw).trans hp,
      (QuadraticForm.sigNeg_of_equiv_weightedSumSquares hw).trans hm,
      (QuadraticForm.finrank_radical_of_equiv_weightedSumSquares hw).trans hz⟩

end RankThreeProjection
