module

public import Ellipsoid.JacobianBlocks

@[expose] public section

noncomputable section

open Matrix Finset
open scoped BigOperators

namespace EllipsoidVerification

def jacobianHeadMoment {n : ℕ} (e : Coefficients n) (k j : Fin (n - 1)) : ℝ :=
  ∑ l : Fin (n + 1), if (l.val : ℝ) < internalDegree k then
    (internalDegree k - l.val) * e l *
      mellinMoment e (2 * internalDegree j - internalDegree k + 2 * l.val) else 0

def jacobianTailMoment {n : ℕ} (e : Coefficients n) (k j : Fin (n - 1)) : ℝ :=
  ∑ l : Fin (n + 1), if internalDegree k < (l.val : ℝ) then
    (l.val - internalDegree k) * e l *
      mellinMoment e (2 * internalDegree j - internalDegree k + 2 * l.val) else 0

/-- The diagonal uses the average of the two equal expressions. The equality
of those expressions is proved by the Mellin integration-by-parts identity. -/
def balancedJacobian {n : ℕ} (e : Coefficients n) :
    Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ := fun k j =>
  if k < j then (1 / 2 : ℝ) * jacobianHeadMoment e k j
  else if j < k then (1 / 2 : ℝ) * jacobianTailMoment e k j
  else (1 / 4 : ℝ) * (jacobianHeadMoment e k j + jacobianTailMoment e k j)

def jacobianRescaling {n : ℕ} (e : Coefficients n) : Fin (n - 1) → ℝ :=
  fun k => mellinMoment e (3 * internalDegree k)

theorem jacobianRescaling_pos {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) (k : Fin (n - 1)) : 0 < jacobianRescaling e k :=
  mellinMoment_pos he (by nlinarith [internalDegree_pos k])
    (by nlinarith [internalDegree_lt k])

theorem jacobianCoefficientBlock_symm {n : ℕ} (e : Coefficients n) (l : Fin (n + 1)) :
    (jacobianCoefficientBlock e l).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, jacobianCoefficientBlock, min_comm, max_comm]

set_option backward.isDefEq.respectTransparency false in
theorem symmetricPart_balancedJacobian_decomposition {n : ℕ} (e : Coefficients n) :
    symmetricPart (Matrix.diagonal (jacobianRescaling e) * balancedJacobian e) =
      (1 / 4 : ℝ) • ∑ l : Fin (n + 1), e l • jacobianCoefficientBlock e l := by
  ext i j
  wlog hij : i ≤ j generalizing i j
  · have hji := this j i (le_of_not_ge hij)
    simpa only [symmetricPart, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply,
      Matrix.diagonal_mul, Matrix.sum_apply, smul_eq_mul,
      (jacobianCoefficientBlock_symm e _).apply, add_comm] using hji
  have hdeg : internalDegree i ≤ internalDegree j := by
    dsimp [internalDegree]
    have hnat : i.val ≤ j.val := hij
    have hreal : (i.val : ℝ) ≤ (j.val : ℝ) := by exact_mod_cast hnat
    linarith only [hreal]
  rcases eq_or_lt_of_le hij with rfl | hijlt
  · simp only [symmetricPart, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply,
      Matrix.diagonal_mul, balancedJacobian, lt_self_iff_false, if_false,
      Matrix.sum_apply, smul_eq_mul, jacobianRescaling]
    unfold jacobianHeadMoment jacobianTailMoment
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    simp only [jacobianCoefficientBlock, min_self, max_self]
    split_ifs <;> first | (exfalso; linarith) | ring
  · have hnlt : ¬ j < i := not_lt.mpr hij
    simp only [symmetricPart, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply,
      Matrix.diagonal_mul, balancedJacobian, hijlt, hnlt, if_true, if_false,
      Matrix.sum_apply, smul_eq_mul, jacobianRescaling]
    unfold jacobianHeadMoment jacobianTailMoment
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    simp only [jacobianCoefficientBlock, min_eq_left hdeg, max_eq_right hdeg]
    split_ifs <;> first | (exfalso; linarith) | ring

/-- Proposition 4.2 for the explicit, balanced derivative formula. -/
theorem symmetricPart_balancedJacobian_posDef {n : ℕ} (hn : 0 < n)
    {e : Coefficients n} (he : coefficientAdmissible e) :
    (symmetricPart (Matrix.diagonal (jacobianRescaling e) * balancedJacobian e)).PosDef := by
  rw [symmetricPart_balancedJacobian_decomposition]
  apply Matrix.PosDef.smul _ (by norm_num)
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Fin (n + 1)))]
  apply Matrix.PosDef.posSemidef_add
  · apply Matrix.posSemidef_sum
    intro l hl
    exact (jacobianCoefficientBlock_posSemidef hn he l).smul (he.1 l)
  · exact (jacobianCoefficientBlock_zero_posDef hn he).smul he.2.1

theorem balancedJacobian_principal_minors_pos {n : ℕ} (hn : 0 < n)
    {e : Coefficients n} (he : coefficientAdmissible e) :
    principalJacobianPositive (balancedJacobian e) := by
  intro s
  exact principal_minor_pos_of_diagonal_stability (jacobianRescaling_pos he)
    (symmetricPart_balancedJacobian_posDef hn he) s

end EllipsoidVerification
