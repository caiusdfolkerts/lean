module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Polynomial.Basic

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace EllipsoidVerification

/-- Coefficients of a degree-`n` polynomial in the squared variable. -/
abbrev Coefficients (n : ℕ) := Fin (n + 1) → ℝ

def coefficientPolynomial {n : ℕ} (e : Coefficients n) (t : ℝ) : ℝ :=
  ∑ j : Fin (n + 1), e j * t ^ (2 * j.val)

def coefficientHead {n : ℕ} (e : Coefficients n) (k : ℕ) (t : ℝ) : ℝ :=
  ∑ j : Fin (n + 1), if j.val < k then e j * t ^ (2 * j.val) else 0

def coefficientDerivative {n : ℕ} (e : Coefficients n) (t : ℝ) : ℝ :=
  ∑ j : Fin (n + 1), (2 * j.val : ℝ) * e j * t ^ (2 * j.val - 1)

def coefficientHeadDerivative {n : ℕ} (e : Coefficients n) (k : ℕ) (t : ℝ) : ℝ :=
  ∑ j : Fin (n + 1), if j.val < k then
    (2 * j.val : ℝ) * e j * t ^ (2 * j.val - 1) else 0

/-- The integral in equation (3), without any real-rootedness assumption. -/
def coefficientTransform {n : ℕ} (e : Coefficients n) (k : ℕ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), (1 / 2 : ℝ) * Real.rpow t (-(k : ℝ)) *
    (coefficientHead e k t * coefficientDerivative e t -
      coefficientHeadDerivative e k t * coefficientPolynomial e t) *
    Real.rpow (coefficientPolynomial e t) (-(3 / 2 : ℝ))

def mellinMoment {n : ℕ} (e : Coefficients n) (r : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), Real.rpow t (r - 1) *
    Real.rpow (coefficientPolynomial e t) (-(3 / 2 : ℝ))

def coefficientAdmissible {n : ℕ} (e : Coefficients n) : Prop :=
  (∀ j, 0 ≤ e j) ∧ 0 < e 0 ∧ 0 < e (Fin.last n)

/-- There are `m` free internal coefficients and degree `m+1`. -/
def fixedEndpoints (m : ℕ) (e0 en : ℝ) (x : Fin m → ℝ) : Coefficients (m + 1) :=
  fun j => if h0 : j.val = 0 then e0 else
    if hn : j.val = m + 1 then en else x ⟨j.val - 1, by omega⟩

def coefficientMap (m : ℕ) (e0 en : ℝ) (x : Fin m → ℝ) : Fin m → ℝ :=
  fun k => coefficientTransform (fixedEndpoints m e0 en x) (k.val + 1)

def principalJacobianPositive {m : ℕ} (J : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  ∀ s : Finset (Fin m), 0 < (J.submatrix (fun i : s => i.val) (fun i : s => i.val)).det

def coefficientJacobian {n : ℕ} (e : Coefficients n)
    (k j : Fin (n - 1)) : ℝ :=
  let kk := k.val + 1
  let jj := j.val + 1
  (1 / 2 : ℝ) * if k ≤ j then
    ∑ l : Fin (n + 1), if l.val < kk then
      ((kk : ℝ) - l.val) * e l *
        mellinMoment e (2 * (jj : ℝ) - (kk : ℝ) + 2 * (l.val : ℝ)) else 0
  else
    ∑ l : Fin (n + 1), if kk < l.val then
      ((l.val : ℝ) - kk) * e l *
        mellinMoment e (2 * (jj : ℝ) - (kk : ℝ) + 2 * (l.val : ℝ)) else 0

theorem coefficientPolynomial_nonneg {n : ℕ} {e : Coefficients n}
    (he : ∀ j, 0 ≤ e j) (t : ℝ) : 0 ≤ coefficientPolynomial e t := by
  exact Finset.sum_nonneg fun j _ => mul_nonneg (he j) (even_two_mul j.val |>.pow_nonneg t)

theorem coefficientPolynomial_ge_constant {n : ℕ} {e : Coefficients n}
    (he : ∀ j, 0 ≤ e j) (t : ℝ) : e 0 ≤ coefficientPolynomial e t := by
  have h := Finset.single_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin (n + 1)))) =>
      mul_nonneg (he j) (even_two_mul j.val |>.pow_nonneg t)) (Finset.mem_univ 0)
  simpa [coefficientPolynomial] using h

theorem coefficientPolynomial_pos {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) (t : ℝ) : 0 < coefficientPolynomial e t :=
  he.2.1.trans_le (coefficientPolynomial_ge_constant he.1 t)

theorem coefficientPolynomial_ge_leading {n : ℕ} {e : Coefficients n}
    (he : ∀ j, 0 ≤ e j) (t : ℝ) :
    e (Fin.last n) * t ^ (2 * n) ≤ coefficientPolynomial e t := by
  exact Finset.single_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin (n + 1)))) =>
      mul_nonneg (he j) (even_two_mul j.val |>.pow_nonneg t)) (Finset.mem_univ (Fin.last n))

theorem fixedEndpoints_zero (m : ℕ) (e0 en : ℝ) (x : Fin m → ℝ) :
    fixedEndpoints m e0 en x 0 = e0 := by simp [fixedEndpoints]

theorem fixedEndpoints_last (m : ℕ) (e0 en : ℝ) (x : Fin m → ℝ) :
    fixedEndpoints m e0 en x (Fin.last (m + 1)) = en := by simp [fixedEndpoints]

theorem fixedEndpoints_internal (m : ℕ) (e0 en : ℝ) (x : Fin m → ℝ) (i : Fin m) :
    fixedEndpoints m e0 en x ⟨i.val + 1, by omega⟩ = x i := by
  simp [fixedEndpoints, show i.val ≠ m by omega]

theorem fixedEndpoints_admissible {m : ℕ} {e0 en : ℝ} {x : Fin m → ℝ}
    (h0 : 0 < e0) (hn : 0 < en) (hx : 0 ≤ x) :
    coefficientAdmissible (fixedEndpoints m e0 en x) := by
  refine ⟨?_, by simpa [fixedEndpoints_zero] using h0,
    by simpa [fixedEndpoints_last] using hn⟩
  intro j
  unfold fixedEndpoints
  split_ifs <;> first | exact h0.le | exact hn.le | exact hx _

@[fun_prop] theorem continuous_coefficientPolynomial {n : ℕ} (e : Coefficients n) :
    Continuous (coefficientPolynomial e) := by
  unfold coefficientPolynomial
  fun_prop

@[fun_prop] theorem continuous_coefficientPolynomial_coefficients {n : ℕ} (t : ℝ) :
    Continuous (fun e : Coefficients n => coefficientPolynomial e t) := by
  unfold coefficientPolynomial
  fun_prop

end EllipsoidVerification
