module
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
@[expose] public section
set_option autoImplicit false

/-!
# Sign structure of a positive hollow matrix kernel

Every nonzero kernel vector has at least two positive coordinates and at
least two negative coordinates.  Its positive and negative parts have equal
positive self- and cross-pairings.  No rank condition is needed for these
facts; they are the linear algebra used for the two zonotopes in Proposition
4.2 of the projection-volume paper.
-/
namespace VolumeVerification.PositiveHollowKernel
open scoped BigOperators Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

theorem entries_nonnegative (P : Matrix ι ι ℝ)
    (hdiag : ∀ i, P i i = 0) (hpos : ∀ i j, i ≠ j → 0 < P i j) :
    ∀ i j, 0 ≤ P i j := by
  intro i j
  by_cases hij : i = j
  · subst j
    rw [hdiag]
  · exact (hpos i j hij).le

theorem exists_positive (P : Matrix ι ι ℝ)
    (hdiag : ∀ i, P i i = 0) (hpos : ∀ i j, i ≠ j → 0 < P i j)
    (w : ι → ℝ) (hw : P *ᵥ w = 0) (hne : w ≠ 0) :
    ∃ i, 0 < w i := by
  classical
  by_contra hex
  have hnonpos : ∀ i, w i ≤ 0 := by
    intro i
    exact le_of_not_gt (fun hi => hex ⟨i, hi⟩)
  obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
    by_contra hj
    push_neg at hj
    exact hne (funext hj)
  have hjneg : w j < 0 := lt_of_le_of_ne (hnonpos j) hj
  obtain ⟨i, hij⟩ := exists_ne j
  have hsum : (∑ k, P i k * w k) < 0 := by
    apply Finset.sum_neg'
    · intro k _
      exact mul_nonpos_of_nonneg_of_nonpos
        (entries_nonnegative P hdiag hpos i k) (hnonpos k)
    · exact ⟨j, Finset.mem_univ j, mul_neg_of_pos_of_neg (hpos i j hij) hjneg⟩
  have hzero : (∑ k, P i k * w k) = 0 := congrFun hw i
  linarith

theorem exists_negative (P : Matrix ι ι ℝ)
    (hdiag : ∀ i, P i i = 0) (hpos : ∀ i j, i ≠ j → 0 < P i j)
    (w : ι → ℝ) (hw : P *ᵥ w = 0) (hne : w ≠ 0) :
    ∃ i, w i < 0 := by
  have hker : P *ᵥ (-w) = 0 := by rw [Matrix.mulVec_neg, hw, neg_zero]
  obtain ⟨i, hi⟩ := exists_positive P hdiag hpos (-w) hker (neg_ne_zero.mpr hne)
  exact ⟨i, neg_pos.mp hi⟩

theorem exists_two_positive (P : Matrix ι ι ℝ)
    (hdiag : ∀ i, P i i = 0) (hpos : ∀ i j, i ≠ j → 0 < P i j)
    (w : ι → ℝ) (hw : P *ᵥ w = 0) (hne : w ≠ 0) :
    ∃ i j, i ≠ j ∧ 0 < w i ∧ 0 < w j := by
  obtain ⟨i, hi⟩ := exists_positive P hdiag hpos w hw hne
  obtain ⟨k, hk⟩ := exists_negative P hdiag hpos w hw hne
  have hik : i ≠ k := by
    intro h
    subst k
    linarith
  by_contra hex
  have hnonpos : ∀ j, j ≠ i → w j ≤ 0 := by
    intro j hji
    exact le_of_not_gt (fun hj => hex ⟨i, j, Ne.symm hji, hi, hj⟩)
  have hsum : (∑ j, P i j * w j) < 0 := by
    apply Finset.sum_neg'
    · intro j _
      by_cases hji : j = i
      · subst j
        rw [hdiag, zero_mul]
      · exact mul_nonpos_of_nonneg_of_nonpos
          (entries_nonnegative P hdiag hpos i j) (hnonpos j hji)
    · exact ⟨k, Finset.mem_univ k, mul_neg_of_pos_of_neg (hpos i k hik) hk⟩
  have hzero : (∑ j, P i j * w j) = 0 := congrFun hw i
  linarith

theorem exists_two_negative (P : Matrix ι ι ℝ)
    (hdiag : ∀ i, P i i = 0) (hpos : ∀ i j, i ≠ j → 0 < P i j)
    (w : ι → ℝ) (hw : P *ᵥ w = 0) (hne : w ≠ 0) :
    ∃ i j, i ≠ j ∧ w i < 0 ∧ w j < 0 := by
  have hker : P *ᵥ (-w) = 0 := by rw [Matrix.mulVec_neg, hw, neg_zero]
  obtain ⟨i, j, hij, hi, hj⟩ :=
    exists_two_positive P hdiag hpos (-w) hker (neg_ne_zero.mpr hne)
  exact ⟨i, j, hij, neg_pos.mp hi, neg_pos.mp hj⟩

def positivePart (w : ι → ℝ) : ι → ℝ := fun i => max (w i) 0

def negativePart (w : ι → ℝ) : ι → ℝ := fun i => max (-w i) 0

theorem positivePart_sub_negativePart (w : ι → ℝ) :
    positivePart w - negativePart w = w := by
  funext i
  change max (w i) 0 - max (-w i) 0 = w i
  rcases le_total 0 (w i) with hi | hi
  · rw [max_eq_left hi, max_eq_right (neg_nonpos.mpr hi), sub_zero]
  · rw [max_eq_right hi, max_eq_left (neg_nonneg.mpr hi)]
    simp

theorem positivePart_mulVec_eq_negativePart (P : Matrix ι ι ℝ)
    (w : ι → ℝ) (hw : P *ᵥ w = 0) :
    P *ᵥ positivePart w = P *ᵥ negativePart w := by
  apply sub_eq_zero.mp
  rw [← Matrix.mulVec_sub, positivePart_sub_negativePart, hw]

theorem positive_self_pairing (P : Matrix ι ι ℝ)
    (hdiag : ∀ i, P i i = 0) (hpos : ∀ i j, i ≠ j → 0 < P i j)
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i)
    (i j : ι) (hij : i ≠ j) (hi : 0 < x i) (hj : 0 < x j) :
    0 < x ⬝ᵥ (P *ᵥ x) := by
  have hP := entries_nonnegative P hdiag hpos
  have hrow (k : ι) : 0 ≤ (P *ᵥ x) k :=
    Finset.sum_nonneg (fun l _ => mul_nonneg (hP k l) (hx l))
  change 0 < ∑ k, x k * (P *ᵥ x) k
  apply Finset.sum_pos'
  · intro k _
    exact mul_nonneg (hx k) (hrow k)
  · refine ⟨i, Finset.mem_univ i, mul_pos hi ?_⟩
    apply Finset.sum_pos'
    · intro k _
      exact mul_nonneg (hP i k) (hx k)
    · exact ⟨j, Finset.mem_univ j, mul_pos (hpos i j hij) hj⟩

/-- The two nonnegative coefficient vectors used to construct the comparison
zonotopes have equal, strictly positive self- and mixed pairings. -/
theorem parts_equal_positive_pairings (P : Matrix ι ι ℝ)
    (hsymm : ∀ i j, P i j = P j i)
    (hdiag : ∀ i, P i i = 0) (hpos : ∀ i j, i ≠ j → 0 < P i j)
    (w : ι → ℝ) (hw : P *ᵥ w = 0) (hne : w ≠ 0) :
    ∃ a : ℝ, 0 < a ∧
      positivePart w ⬝ᵥ (P *ᵥ positivePart w) = a ∧
      positivePart w ⬝ᵥ (P *ᵥ negativePart w) = a ∧
      negativePart w ⬝ᵥ (P *ᵥ negativePart w) = a := by
  have hsymmP : Pᵀ = P := by
    ext i j
    exact hsymm j i
  have hsymm_pair (x y : ι → ℝ) : x ⬝ᵥ (P *ᵥ y) = y ⬝ᵥ (P *ᵥ x) := by
    simpa only [hsymmP] using Matrix.dotProduct_transpose_mulVec P x y
  have he := positivePart_mulVec_eq_negativePart P w hw
  obtain ⟨i, j, hij, hi, hj⟩ := exists_two_positive P hdiag hpos w hw hne
  have ha : 0 < positivePart w ⬝ᵥ (P *ᵥ positivePart w) := by
    apply positive_self_pairing P hdiag hpos _ (fun k => le_max_right _ _) i j hij
    · exact lt_of_lt_of_le hi (le_max_left _ _)
    · exact lt_of_lt_of_le hj (le_max_left _ _)
  refine ⟨positivePart w ⬝ᵥ (P *ᵥ positivePart w), ha, rfl, ?_, ?_⟩
  · rw [he]
  · calc
      negativePart w ⬝ᵥ (P *ᵥ negativePart w) =
          negativePart w ⬝ᵥ (P *ᵥ positivePart w) := by rw [he]
      _ = positivePart w ⬝ᵥ (P *ᵥ negativePart w) := hsymm_pair _ _
      _ = positivePart w ⬝ᵥ (P *ᵥ positivePart w) := by rw [he]

end VolumeVerification.PositiveHollowKernel
