import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Dist
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Exact numerical consequences of the asymmetric bounds

These are identities and implications about real-valued face counts.  Their
incidence and rigidity hypotheses remain explicit; they are not substituted
for the geometric theorems of the paper.
-/

namespace Cubical.Counting

/-- Integral form of taking the larger asymmetric count. -/
theorem strengthened_nat (d b w e c : ℕ) (hd : 1 ≤ d)
    (hb : d * b + w ≤ e + c) (hw : b + d * w ≤ e + c) :
    (d + 1) * (b + w) + (d - 1) * Nat.dist b w ≤ 2 * e + 2 * c := by
  have hdsub : d - 1 + 1 = d := Nat.sub_add_cancel hd
  rcases le_total b w with hbw | hwb
  · rw [Nat.dist_eq_sub_of_le hbw]
    have hsub : w - b + b = w := Nat.sub_add_cancel hbw
    have hmul := congrArg (fun x : ℕ => d * x) hsub
    have hmul' := congrArg (fun x : ℕ => x * (w - b)) hdsub
    nlinarith
  · rw [Nat.dist_eq_sub_of_le_right hwb]
    have hsub : b - w + w = b := Nat.sub_add_cancel hwb
    have hmul := congrArg (fun x : ℕ => d * x) hsub
    have hmul' := congrArg (fun x : ℕ => x * (b - w)) hdsub
    nlinarith

theorem max_asymmetric (d b w : ℝ) (hd : 1 ≤ d) :
    max (d * b + w) (b + d * w) =
      (d + 1) / 2 * (b + w) + (d - 1) / 2 * |b - w| := by
  rcases le_total b w with hbw | hwb
  · rw [abs_of_nonpos (sub_nonpos.mpr hbw), max_eq_right (by nlinarith)]
    ring
  · rw [abs_of_nonneg (sub_nonneg.mpr hwb), max_eq_left (by nlinarith)]
    ring

theorem strengthened_of_asymmetric (d b w e c : ℝ) (hd : 1 ≤ d)
    (hb : d * b + w ≤ e + c) (hw : b + d * w ≤ e + c) :
    (d + 1) / 2 * (b + w) - c + (d - 1) / 2 * |b - w| ≤ e := by
  have h : max (d * b + w) (b + d * w) ≤ e + c := max_le hb hw
  rw [max_asymmetric d b w hd] at h
  linarith

theorem unstrengthened_of_asymmetric (d b w e c : ℝ)
    (hb : d * b + w ≤ e + c) (hw : b + d * w ≤ e + c) :
    (d + 1) / 2 * (b + w) - c ≤ e := by
  nlinarith

/-- The three-dimensional quadrilateral-incidence and Euler calculation. -/
theorem dimension_three (n e f : ℝ)
    (hinc : 2 * e = 4 * f) (heuler : n - e + f = 2) :
    e = 2 * n - 4 ∧ f = n - 2 := by
  constructor <;> linarith

/-- The binomial identity used in the cubical MPW reduction. -/
theorem mpw_coefficient (d i : ℕ) (hi : 1 ≤ i) (hid : i ≤ d) :
    ((d : ℝ) + 1) * (d - 1).choose (i - 1) -
      ((i : ℝ) - 1) * d.choose i =
      (d.choose i : ℝ) + (d - 1).choose (i - 1) := by
  have hd : 1 ≤ d := hi.trans hid
  have hnat : i * d.choose i = d * (d - 1).choose (i - 1) := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
    simpa [Nat.mul_comm] using (Nat.add_one_mul_choose_eq k j).symm
  have hreal : (i : ℝ) * d.choose i = (d : ℝ) * (d - 1).choose (i - 1) := by
    exact_mod_cast hnat
  nlinarith

/-- Substitution in the incidence sum, including the imbalance correction. -/
theorem intermediate_faces (d i : ℕ) (hi : 1 ≤ i) (hid : i ≤ d)
    (n e f delta : ℝ)
    (hedge : ((d : ℝ) + 1) * n - 2 ^ d + ((d : ℝ) - 1) * delta ≤ 2 * e)
    (hinc : 2 * ((d - 1).choose (i - 1) : ℝ) * e -
      ((i : ℝ) - 1) * d.choose i * n ≤ 2 ^ i * f) :
    ((d.choose i : ℝ) + (d - 1).choose (i - 1)) * n -
      2 ^ d * (d - 1).choose (i - 1) +
      ((d : ℝ) - 1) * (d - 1).choose (i - 1) * delta ≤ 2 ^ i * f := by
  have hc : (0 : ℝ) ≤ (d - 1).choose (i - 1) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hedge hc
  have hcoeff := mpw_coefficient d i hi hid
  have hcoeffn := congrArg (fun x : ℝ ↦ x * n) hcoeff
  nlinarith

/-- The corresponding facet substitution, prior to division by `2^(d-1)`. -/
theorem facets (d : ℕ) (hd : 3 ≤ d) (n e f delta : ℝ)
    (hedge : ((d : ℝ) + 1) * n - 2 ^ d + ((d : ℝ) - 1) * delta ≤ 2 * e)
    (hinc : 2 * ((d : ℝ) - 2) * e -
      (d : ℝ) * ((d : ℝ) - 3) * n ≤ 2 ^ (d - 1) * f) :
    (2 * (d : ℝ) - 2) * n - ((d : ℝ) - 2) * 2 ^ d +
      ((d : ℝ) - 1) * ((d : ℝ) - 2) * delta ≤ 2 ^ (d - 1) * f := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hmul := mul_le_mul_of_nonneg_left hedge (by linarith : 0 ≤ (d : ℝ) - 2)
  nlinarith

end Cubical.Counting
