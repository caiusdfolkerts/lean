module

public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

/-!
# The finite recurrence in Section 4.3

This file proves the algebraic consequence of the generating-function identity in
Section 4.3 of `Hilbert series of exterior algebras modulo two quadrics`.
The power-series identity and the inverse identity are explicit hypotheses here;
they are not asserted as axioms, and the identification with the paper's symmetric
polynomials is a separate task.  In particular these theorems do not assert the
cohomology presentation.

The result is useful over every characteristic-zero field and in every number of
variables: a consecutive block of `s` zero relations forces all later relations to
vanish, and a polynomial inverse then forces the Chern polynomial to equal one.
-/

@[expose] public section

set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open Finset

variable {K : Type*} [Field K] [CharZero K]

/-- The even part of a coefficient sequence, with its original exponents. -/
noncomputable def evenRelationSeries (R : ℕ → K) : PowerSeries K :=
  PowerSeries.mk fun n => if Even n then R n else 0

/-- The odd part of a coefficient sequence, with its original exponents. -/
noncomputable def oddRelationSeries (R : ℕ → K) : PowerSeries K :=
  PowerSeries.mk fun n => if Even n then 0 else R n

/-- The Euler differential operator `t d/dt` on a power series. -/
noncomputable def eulerSeries (B : PowerSeries K) : PowerSeries K :=
  PowerSeries.X * PowerSeries.derivative B

@[simp] theorem coeff_evenRelationSeries (R : ℕ → K) (n : ℕ) :
    PowerSeries.coeff n (evenRelationSeries R) = if Even n then R n else 0 :=
  PowerSeries.coeff_mk _ _

@[simp] theorem coeff_oddRelationSeries (R : ℕ → K) (n : ℕ) :
    PowerSeries.coeff n (oddRelationSeries R) = if Even n then 0 else R n :=
  PowerSeries.coeff_mk _ _

@[simp] theorem coeff_eulerSeries (B : PowerSeries K) (n : ℕ) :
    PowerSeries.coeff n (eulerSeries B) = (n : K) * PowerSeries.coeff n B := by
  cases n with
  | zero => simp [eulerSeries]
  | succ n =>
    simp only [eulerSeries, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
    push_cast
    ring

/-- The numerical coefficient `A_{m,i}` in equation (7). -/
noncomputable def chernRecurrenceWeight (m i : ℕ) : K :=
  if Even (m - i) then (m + i : ℕ) else 2

/-- Taking coefficients of the actual formal differential identity gives exactly
the recurrence printed as equation (7), including its parity-dependent factor. -/
theorem chern_recurrence_of_series_identity (C : Polynomial K) (R : ℕ → K)
    (hidentity :
      (C : PowerSeries K) * (eulerSeries (evenRelationSeries R) +
          2 * oddRelationSeries R) +
        2 * eulerSeries (C : PowerSeries K) * evenRelationSeries R = 0)
    (m : ℕ) :
    ∑ i ∈ range (m + 1), C.coeff i * chernRecurrenceWeight m i * R (m - i) = 0 := by
  classical
  have h := congrArg (PowerSeries.coeff m) hidentity
  rw [map_add, PowerSeries.coeff_mul, PowerSeries.coeff_mul, map_zero] at h
  simp only [map_add,
    Polynomial.coeff_coe, PowerSeries.coeff_natCast_mul, PowerSeries.coeff_ofNat_mul,
    coeff_eulerSeries, coeff_evenRelationSeries, coeff_oddRelationSeries] at h
  rw [← Finset.sum_add_distrib] at h
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hcast : ((m - i : ℕ) : K) + (i : K) = (m : K) := by
    exact_mod_cast Nat.sub_add_cancel hi'
  unfold chernRecurrenceWeight
  split_ifs with he
  · push_cast
    linear_combination -(C.coeff i * R (m - i)) * hcast
  · ring

/-- A length-`s` zero window propagates forever under the Section 4.3 recurrence.
The positivity of `w` is essential because the leading even coefficient at zero
is zero. -/
theorem chern_recurrence_vanishing_propagates {s w : ℕ} (hw : 0 < w)
    (C : Polynomial K) (hC0 : C.coeff 0 = 1) (hdegree : C.natDegree ≤ s)
    (R : ℕ → K)
    (hrecurrence : ∀ m : ℕ,
      ∑ i ∈ range (m + 1), C.coeff i * chernRecurrenceWeight m i * R (m - i) = 0)
    (hwindow : ∀ m, w ≤ m → m < w + s → R m = 0) :
    ∀ m, w ≤ m → R m = 0 := by
  classical
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hwm
    by_cases hm : m < w + s
    · exact hwindow m hwm hm
    have hsum := hrecurrence m
    have hrest : ∀ i ∈ range (m + 1), i ≠ 0 →
        C.coeff i * chernRecurrenceWeight m i * R (m - i) = 0 := by
      intro i hi hi0
      by_cases his : i ≤ s
      · have hi' : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        have him : m - i < m := by omega
        have hwi : w ≤ m - i := by omega
        rw [ih (m - i) him hwi, mul_zero]
      · have hci : C.coeff i = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdegree (by omega))
        rw [hci, zero_mul, zero_mul]
    rw [Finset.sum_eq_single 0 (fun i hi hi0 => hrest i hi hi0)
      (by simp), hC0, one_mul, Nat.sub_zero] at hsum
    have hlead : chernRecurrenceWeight (K := K) m 0 ≠ 0 := by
      unfold chernRecurrenceWeight
      split_ifs
      · simpa using (Nat.cast_ne_zero.mpr (show m ≠ 0 by omega) : (m : K) ≠ 0)
      · norm_num
    exact (mul_eq_zero.mp hsum).resolve_left hlead

/-- A formal power series whose coefficients vanish from `w` onwards is the
actual image of its polynomial truncation. -/
theorem powerSeries_eq_trunc_of_tail_zero (B : PowerSeries K) (w : ℕ)
    (hzero : ∀ m, w ≤ m → PowerSeries.coeff m B = 0) :
    B = (PowerSeries.trunc w B : Polynomial K) := by
  ext m
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  by_cases hm : m < w
  · simp [hm]
  · simp [hm, hzero m (by omega)]

/-- The polynomial argument in Section 4.3: a finite relation window, together
with the two stated generating-function identities, forces `C(t)=1`.

There is no assumption that the relation sequence eventually vanishes; that fact
is proved from the recurrence.  `Q` will be `C(-t)` in the application. -/
theorem chern_polynomial_eq_one_of_window {s w : ℕ} (hw : 0 < w)
    (C Q : Polynomial K) (hC0 : C.coeff 0 = 1) (hdegree : C.natDegree ≤ s)
    (R : ℕ → K)
    (hidentity :
      (C : PowerSeries K) * (eulerSeries (evenRelationSeries R) +
          2 * oddRelationSeries R) +
        2 * eulerSeries (C : PowerSeries K) * evenRelationSeries R = 0)
    (hinverse : evenRelationSeries R * (C : PowerSeries K) * (Q : PowerSeries K) = 1)
    (hwindow : ∀ m, w ≤ m → m < w + s → R m = 0) : C = 1 := by
  classical
  have htail := chern_recurrence_vanishing_propagates hw C hC0 hdegree R
    (chern_recurrence_of_series_identity C R hidentity) hwindow
  have hBtail : ∀ m, w ≤ m → PowerSeries.coeff m (evenRelationSeries R) = 0 := by
    intro m hm
    simp [htail m hm]
  let B : Polynomial K := PowerSeries.trunc w (evenRelationSeries R)
  have hB : evenRelationSeries R = (B : PowerSeries K) :=
    powerSeries_eq_trunc_of_tail_zero _ _ hBtail
  have hproduct : B * C * Q = 1 := by
    apply Polynomial.coe_injective K
    simpa only [Polynomial.coe_mul, Polynomial.coe_one, ← hB] using hinverse
  have hunit : IsUnit C := by
    apply isUnit_iff_dvd_one.mpr
    refine ⟨B * Q, ?_⟩
    calc
      1 = B * C * Q := hproduct.symm
      _ = C * (B * Q) := by ring
  rw [Polynomial.eq_C_of_natDegree_eq_zero (Polynomial.natDegree_eq_zero_of_isUnit hunit),
    hC0, Polynomial.C_1]

end PaperVerification.AlternatingForms
