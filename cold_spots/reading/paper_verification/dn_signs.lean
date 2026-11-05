module
public import PaperVerification.DnEquality
@[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

lemma alternatingGaussian_fold_sign (α t : ℝ) (q : ℤ) :
    alternatingGaussian α t = paritySign q * alternatingGaussian α |t - (q : ℝ)| := by
  have h := alternatingGaussian_int_period α (t - (q : ℝ)) q
  rw [sub_add_cancel] at h
  rw [alternatingGaussian_abs_argument]
  exact h

lemma alternatingGaussian_halfRounded_sign {n : ℕ} (α : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    alternatingGaussian α (x i - 1 / 2) =
      paritySign (halfRoundedInt x i) * alternatingGaussian α (foldedRadius x i - 1 / 2) := by
  rw [alternatingGaussian_fold_sign α (x i - 1 / 2) (halfRoundedInt x i)]
  have habs : |x i - 1 / 2 - (halfRoundedInt x i : ℝ)| = 1 / 2 - foldedRadius x i := by
    convert abs_sub_halfRoundedInt x i using 1 <;> congr 1 <;> ring
  rw [habs, show (1 / 2 : ℝ) - foldedRadius x i = -(foldedRadius x i - 1 / 2) by ring,
    alternatingGaussian_even]

theorem signed_integer_product_fold {n : ℕ} (α : ℝ) (x : Fin n → ℝ) :
    (∏ i, alternatingGaussian α (x i)) =
      paritySign (∑ i, roundedInt x i) * foldedBProduct α x := by
  have hi (i : Fin n) : alternatingGaussian α (x i) =
      paritySign (roundedInt x i) * alternatingGaussian α (foldedRadius x i) :=
    alternatingGaussian_fold_sign α (x i) (roundedInt x i)
  simp_rw [hi]
  rw [Finset.prod_mul_distrib, ← paritySign_sum]
  rfl

theorem signed_half_product_fold {n : ℕ} (α : ℝ) (x : Fin n → ℝ) :
    (∏ i, alternatingGaussian α (x i - 1 / 2)) =
      paritySign (∑ i, halfRoundedInt x i) * foldedDProduct α x := by
  rw [show (∏ i, alternatingGaussian α (x i - 1 / 2)) =
      ∏ i, paritySign (halfRoundedInt x i) *
        alternatingGaussian α (foldedRadius x i - 1 / 2) by
    apply Finset.prod_congr rfl
    intro i _
    exact alternatingGaussian_halfRounded_sign α x i]
  rw [Finset.prod_mul_distrib, ← paritySign_sum]
  rfl

theorem dPlusGaussian_signed_fold {n : ℕ} {α : ℝ} (hα : 0 < α) (x : Fin n → ℝ) :
    dPlusGaussian α x = (1 / 2) *
      (foldedAProduct α x + foldedCProduct α x +
        paritySign (∑ i, roundedInt x i) * foldedBProduct α x +
        paritySign (∑ i, halfRoundedInt x i) * foldedDProduct α x) := by
  rw [dPlusGaussian_eq_product hα, signed_integer_product_fold, signed_half_product_fold]
  have ha : (∏ i, gaussian α (x i)) = foldedAProduct α x := by
    apply Finset.prod_congr rfl
    intro i _
    exact gaussian_fold α (x i)
  have hc : (∏ i, gaussian α (x i - 1 / 2)) = foldedCProduct α x := by
    apply Finset.prod_congr rfl
    intro i _
    exact gaussian_halfshift_fold α (x i)
  rw [ha,hc]
  ring

def FoldedSignCondition {n : ℕ} (α : ℝ) (x : Fin n → ℝ) : Prop :=
  (foldedBProduct α x = 0 ∨ ¬Even (∑ i, roundedInt x i)) ∧
  (foldedDProduct α x = 0 ∨ ¬Even (∑ i, halfRoundedInt x i))

theorem dPlusGaussian_eq_folded_lower_iff {n : ℕ} {α : ℝ} (hα : 0 < α)
    (x : Fin n → ℝ) :
    dPlusGaussian α x = (1 / 2) * (foldedAProduct α x + foldedCProduct α x -
      foldedBProduct α x - foldedDProduct α x) ↔ FoldedSignCondition α x := by
  rw [dPlusGaussian_signed_fold hα]
  unfold FoldedSignCondition paritySign
  have hb := foldedBProduct_nonneg hα x
  have hd := foldedDProduct_nonneg hα x
  by_cases hi : Even (∑ i, roundedInt x i) <;>
    by_cases hh : Even (∑ i, halfRoundedInt x i) <;>
    simp only [hi, hh, if_true, if_false, not_true_eq_false, not_false_eq_true,
      or_false, or_true, and_true, true_and]
  all_goals constructor <;> intro h
  all_goals first | exact ⟨by linarith, by linarith⟩ | rcases h with ⟨h₁,h₂⟩; linarith | linarith | trivial

lemma folded_alternating_zero_of_balanced {n : ℕ} (hn : 0 < n) {α : ℝ}
    {x : Fin n → ℝ} (hx : BalancedHalfGrid x) :
    foldedBProduct α x = 0 ∧ foldedDProduct α x = 0 := by
  classical
  obtain ⟨⟨i,hi⟩,⟨j,hj⟩⟩ := balanced_has_both_endpoints hn hx
  constructor
  · exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hj, alternatingGaussian_half])
  · exact Finset.prod_eq_zero (Finset.mem_univ i) (by
      rw [hi, zero_sub, alternatingGaussian_even, alternatingGaussian_half])

lemma folded_B_constant {n : ℕ} (α : ℝ) (x : Fin n → ℝ) (t : ℝ)
    (ht : ∀ i, foldedRadius x i = t) :
    foldedBProduct α x = alternatingGaussian α t ^ n := by
  simp [foldedBProduct, ht]

lemma folded_D_constant {n : ℕ} (α : ℝ) (x : Fin n → ℝ) (t : ℝ)
    (ht : ∀ i, foldedRadius x i = t) :
    foldedDProduct α x = alternatingGaussian α (t - 1 / 2) ^ n := by
  simp [foldedDProduct, ht]

end PaperVerification.ColdSpots
