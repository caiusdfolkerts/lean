module
public import Mathlib.Algebra.Order.Round
public import Mathlib.Algebra.Group.Int.Even
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
@[expose] public section
/-! # Integer coordinate rounding and exact parity repair

These are geometric statements about actual integer coordinate tuples. All sums
are squared Euclidean distances, written in coordinates. They do not assume any
of the covering or Gaussian-minimum conclusions.
-/

namespace PaperVerification.ColdSpots

open scoped BigOperators

variable {n : ℕ}

/-- Change one integer coordinate by an integer step. -/
def alterCoordinate (q : Fin n → ℤ) (j : Fin n) (e : ℤ) : Fin n → ℤ :=
  fun i => q i + if i = j then e else 0

theorem sum_alterCoordinate (q : Fin n → ℤ) (j : Fin n) (e : ℤ) :
    (∑ i, alterCoordinate q j e i) = (∑ i, q i) + e := by
  simp [alterCoordinate, Finset.sum_add_distrib]

/-- Exact change in squared Euclidean distance under one coordinate step. -/
theorem sq_sum_alterCoordinate (x : Fin n → ℝ) (q : Fin n → ℤ) (j : Fin n) (e : ℤ) :
    (∑ i, (x i - (alterCoordinate q j e i : ℝ)) ^ 2) =
      (∑ i, (x i - (q i : ℝ)) ^ 2) +
        ((e : ℝ) ^ 2 - 2 * (e : ℝ) * (x j - (q j : ℝ))) := by
  calc
    _ = ∑ i, ((x i - (q i : ℝ)) ^ 2 +
        if i = j then (e : ℝ) ^ 2 - 2 * (e : ℝ) * (x j - (q j : ℝ)) else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases h : i = j
      · subst i
        simp only [alterCoordinate, ↓reduceIte, Int.cast_add]
        ring
      · simp [alterCoordinate, h]
    _ = _ := by simp [Finset.sum_add_distrib]

/-- Parity can be repaired at any coordinate at additional squared cost
`1 - 2 * |x j - q j|`, provided that coordinate was rounded within one half. -/
theorem exists_even_parity_repair (x : Fin n → ℝ) (q : Fin n → ℤ) (j : Fin n)
    (hj : |x j - (q j : ℝ)| ≤ 1 / 2) :
    ∃ z : Fin n → ℤ, Even (∑ i, z i) ∧
      (∑ i, (x i - (z i : ℝ)) ^ 2) ≤
        (∑ i, (x i - (q i : ℝ)) ^ 2) + 1 - 2 * |x j - (q j : ℝ)| := by
  by_cases he : Even (∑ i, q i)
  · exact ⟨q, he, by linarith⟩
  · by_cases hd : 0 ≤ x j - (q j : ℝ)
    · refine ⟨alterCoordinate q j 1, ?_, ?_⟩
      · rw [sum_alterCoordinate]
        exact Int.even_add_one.mpr he
      · rw [sq_sum_alterCoordinate, abs_of_nonneg hd]
        norm_num <;> linarith
    · refine ⟨alterCoordinate q j (-1), ?_, ?_⟩
      · rw [sum_alterCoordinate]
        simpa only [sub_eq_add_neg] using Int.even_sub_one.mpr he
      · rw [sq_sum_alterCoordinate, abs_of_neg (lt_of_not_ge hd)]
        norm_num <;> linarith


/-- Distinct integers are separated by at least one in the real metric. -/
theorem one_le_abs_int_sub (q z : ℤ) (hne : q ≠ z) :
    1 ≤ |(q : ℝ) - (z : ℝ)| := by
  rcases lt_or_gt_of_ne hne with h | h
  · have hz : (q : ℝ) + 1 ≤ (z : ℝ) := by
      exact_mod_cast (Int.add_one_le_iff.mpr h)
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have hz : (z : ℝ) + 1 ≤ (q : ℝ) := by
      exact_mod_cast (Int.add_one_le_iff.mpr h)
    rw [abs_of_nonneg (by linarith)]
    linarith

/-- Moving away from a nearest integer has at least the parity-repair cost. -/
theorem sq_sub_int_lower (x : ℝ) (q z : ℤ)
    (hq : |x - (q : ℝ)| ≤ 1 / 2) (hne : q ≠ z) :
    (x - (q : ℝ)) ^ 2 + 1 - 2 * |x - (q : ℝ)| ≤ (x - (z : ℝ)) ^ 2 := by
  have hz := one_le_abs_int_sub q z hne
  have htri : |(q : ℝ) - (z : ℝ)| ≤ |x - (q : ℝ)| + |x - (z : ℝ)| := by
    calc
      _ = |(x - (z : ℝ)) - (x - (q : ℝ))| := by congr 1 <;> ring
      _ ≤ |x - (z : ℝ)| + |x - (q : ℝ)| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          (abs_sub_le (x - (z : ℝ)) 0 (x - (q : ℝ)))
      _ = _ := add_comm _ _
  have ha : 0 ≤ |x - (z : ℝ)| - (1 - |x - (q : ℝ)|) := by linarith
  have hb : 0 ≤ |x - (z : ℝ)| + (1 - |x - (q : ℝ)|) := by
    linarith [abs_nonneg (x - (z : ℝ))]
  have hp := mul_nonneg ha hb
  nlinarith only [hp, sq_abs (x - (q : ℝ)), sq_abs (x - (z : ℝ))]

/-- A coordinate within one half of an integer is indeed nearest to that integer. -/
theorem sq_sub_int_nearest (x : ℝ) (q z : ℤ) (hq : |x - (q : ℝ)| ≤ 1 / 2) :
    (x - (q : ℝ)) ^ 2 ≤ (x - (z : ℝ)) ^ 2 := by
  by_cases heq : q = z
  · simp [heq]
  · linarith [sq_sub_int_lower x q z hq heq]

/-- Lower bound for the even integer coset. It contains the exact parity cost,
so it can be paired with the explicit rounding witness above. -/
theorem even_integer_sq_lower (x : Fin n → ℝ) (q z : Fin n → ℤ) (M : ℝ)
    (hq : ∀ i, |x i - (q i : ℝ)| ≤ 1 / 2)
    (hM : ∀ i, |x i - (q i : ℝ)| ≤ M) (hz : Even (∑ i, z i)) :
    (∑ i, (x i - (q i : ℝ)) ^ 2) + (if Even (∑ i, q i) then 0 else 1 - 2 * M) ≤
      ∑ i, (x i - (z i : ℝ)) ^ 2 := by
  classical
  by_cases he : Even (∑ i, q i)
  · simp only [if_pos he, add_zero]
    exact Finset.sum_le_sum fun i _ => sq_sub_int_nearest (x i) (q i) (z i) (hq i)
  · simp only [if_neg he]
    have hneq : q ≠ z := by
      intro heq
      exact he (by simpa only [heq] using hz)
    obtain ⟨j, hj⟩ : ∃ j, q j ≠ z j := not_forall.mp (fun h => hneq (funext h))
    have hs : (∑ i, ((x i - (q i : ℝ)) ^ 2 + if i = j then 1 - 2 * M else 0)) ≤
        ∑ i, (x i - (z i : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hij : i = j
      · subst i
        simp only [↓reduceIte]
        linarith [sq_sub_int_lower (x j) (q j) (z j) (hq j) hj, hM j]
      · simp only [if_neg hij, add_zero]
        exact sq_sub_int_nearest (x i) (q i) (z i) (hq i)
    simpa [Finset.sum_add_distrib] using hs

/-- Coordinatewise nearest integer, breaking ties as in Mathlib's `round`. -/
noncomputable def roundedInt (x : Fin n → ℝ) : Fin n → ℤ := fun i => round (x i)

/-- Distance of each coordinate to its nearest integer. -/
noncomputable def foldedRadius (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => |x i - (roundedInt x i : ℝ)|

theorem foldedRadius_nonneg (x : Fin n → ℝ) (i : Fin n) : 0 ≤ foldedRadius x i :=
  abs_nonneg _

theorem foldedRadius_le_half (x : Fin n → ℝ) (i : Fin n) : foldedRadius x i ≤ 1 / 2 :=
  abs_sub_round (x i)

theorem sq_sub_roundedInt (x : Fin n → ℝ) (i : Fin n) :
    (x i - (roundedInt x i : ℝ)) ^ 2 = (foldedRadius x i) ^ 2 := by
  simp [foldedRadius, sq_abs]

/-- The integer part of a nearest half-integer coordinate. -/
noncomputable def halfRoundedInt (x : Fin n → ℝ) : Fin n → ℤ :=
  fun i => roundedInt x i + if 0 ≤ x i - (roundedInt x i : ℝ) then 0 else -1

/-- The distance to a nearest half integer is exactly one half minus the distance
to a nearest integer, including all tied-rounding endpoints. -/
theorem abs_sub_halfRoundedInt (x : Fin n → ℝ) (i : Fin n) :
    |x i - ((halfRoundedInt x i : ℝ) + 1 / 2)| = 1 / 2 - foldedRadius x i := by
  have hr := foldedRadius_le_half x i
  unfold foldedRadius at hr ⊢
  by_cases hd : 0 ≤ x i - (roundedInt x i : ℝ)
  · rw [abs_of_nonneg hd] at hr ⊢
    have hh : x i - ((roundedInt x i : ℝ) + 1 / 2) ≤ 0 := by linarith
    simp only [halfRoundedInt, if_pos hd, add_zero]
    rw [abs_of_nonpos hh]
    ring
  · have hneg := lt_of_not_ge hd
    rw [abs_of_neg hneg] at hr ⊢
    have hh : 0 ≤ x i - ((roundedInt x i : ℝ) - 1 + 1 / 2) := by linarith
    simp only [halfRoundedInt, if_neg hd, Int.cast_add, Int.cast_neg, Int.cast_one]
    rw [show (roundedInt x i : ℝ) + -1 + 1 / 2 =
      (roundedInt x i : ℝ) - 1 + 1 / 2 by ring, abs_of_nonneg hh]
    ring

theorem exists_even_integer_bound (x : Fin n → ℝ) (j : Fin n) :
    ∃ z : Fin n → ℤ, Even (∑ i, z i) ∧
      (∑ i, (x i - (z i : ℝ)) ^ 2) ≤
        (∑ i, (foldedRadius x i) ^ 2) + 1 - 2 * foldedRadius x j := by
  obtain ⟨z, he, hz⟩ := exists_even_parity_repair x (roundedInt x) j
    (foldedRadius_le_half x j)
  refine ⟨z, he, ?_⟩
  simpa only [foldedRadius, sq_abs] using hz

/-- The analogous parity repair in the all-half-integer coset has cost `2r_j`. -/
theorem exists_even_half_integer_bound (x : Fin n → ℝ) (j : Fin n) :
    ∃ z : Fin n → ℤ, Even (∑ i, z i) ∧
      (∑ i, (x i - ((z i : ℝ) + 1 / 2)) ^ 2) ≤
        (∑ i, (1 / 2 - foldedRadius x i) ^ 2) + 2 * foldedRadius x j := by
  have hrepr (i : Fin n) :
      |(x i - 1 / 2) - (halfRoundedInt x i : ℝ)| = 1 / 2 - foldedRadius x i := by
    convert abs_sub_halfRoundedInt x i using 1 <;> congr 1 <;> ring
  have hj : |(x j - 1 / 2) - (halfRoundedInt x j : ℝ)| ≤ 1 / 2 := by
    rw [hrepr]
    linarith [foldedRadius_nonneg x j]
  obtain ⟨z, he, hz⟩ := exists_even_parity_repair (fun i => x i - 1 / 2)
    (halfRoundedInt x) j hj
  refine ⟨z, he, ?_⟩
  have hsq (i : Fin n) : ((x i - 1 / 2) - (halfRoundedInt x i : ℝ)) ^ 2 =
      (1 / 2 - foldedRadius x i) ^ 2 := by
    rw [← hrepr, sq_abs]
  have htrans (i : Fin n) : (x i - ((z i : ℝ) + 1 / 2)) ^ 2 =
      ((x i - 1 / 2) - (z i : ℝ)) ^ 2 := by ring
  simp only [hsq, hrepr] at hz
  simp only [htrans]
  linarith


/-- Zero folded radius means exactly an integer coordinate. -/
theorem foldedRadius_eq_zero_iff (x : Fin n → ℝ) (i : Fin n) :
    foldedRadius x i = 0 ↔ ∃ z : ℤ, x i = (z : ℝ) := by
  constructor
  · intro h
    exact ⟨roundedInt x i, sub_eq_zero.mp (abs_eq_zero.mp h)⟩
  · rintro ⟨z, hz⟩
    simp [foldedRadius, roundedInt, hz]

/-- Radius one half means exactly a nonintegral half-integer coordinate. -/
theorem foldedRadius_eq_half_iff (x : Fin n → ℝ) (i : Fin n) :
    foldedRadius x i = 1 / 2 ↔ ∃ z : ℤ, x i = (z : ℝ) + 1 / 2 := by
  constructor
  · intro h
    have ht := sub_half_lt_round (x i)
    change x i - 1 / 2 < (roundedInt x i : ℝ) at ht
    unfold foldedRadius at h
    by_cases hd : 0 ≤ x i - (roundedInt x i : ℝ)
    · rw [abs_of_nonneg hd] at h
      linarith
    · rw [abs_of_neg (lt_of_not_ge hd)] at h
      refine ⟨roundedInt x i - 1, ?_⟩
      push_cast
      linarith
  · rintro ⟨z, hz⟩
    have hh : round (1 / 2 : ℝ) = 1 := by norm_num [round_eq]
    unfold foldedRadius roundedInt
    rw [hz, round_intCast_add, hh]
    push_cast
    have h : (z : ℝ) + 1 / 2 - ((z : ℝ) + 1) = -(1 / 2 : ℝ) := by ring
    rw [h]
    norm_num

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.exists_even_integer_bound
#print axioms PaperVerification.ColdSpots.exists_even_half_integer_bound
