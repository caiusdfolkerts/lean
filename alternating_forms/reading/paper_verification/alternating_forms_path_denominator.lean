module

public import PaperVerification.MatrixPowerSeriesResolvent
public import PaperVerification.PowerSeriesInverseDeterminant
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.Data.Nat.Choose.Basic

/-!
# The signed path matching polynomial and the printed determinant

The denominator for a path with n vertices satisfies P₀=P₁=1 and
Pₙ₊₂=Pₙ₊₁-zPₙ.  Its coefficients are proved, for all n and j, to be
(-1)^j choose(n-j,j).  The reciprocal coefficient determinant therefore
becomes exactly the binomial Hessenberg matrix printed in Theorem 1.1.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix Classical

namespace PaperVerification.AlternatingForms.PathDeterminant

def pathDenominator : ℕ → PowerSeries ℤ
  | 0 => 1
  | 1 => 1
  | n+2 => pathDenominator (n+1) - PowerSeries.X * pathDenominator n

@[simp] theorem pathDenominator_zero : pathDenominator 0 = 1 := rfl
@[simp] theorem pathDenominator_one : pathDenominator 1 = 1 := rfl

theorem pathDenominator_recurrence (n : ℕ) :
    pathDenominator (n+2) = pathDenominator (n+1) - PowerSeries.X * pathDenominator n := rfl

theorem pathDenominator_coeff (n j : ℕ) :
    PowerSeries.coeff j (pathDenominator n) = (-1 : ℤ)^j * ((n-j).choose j : ℤ) := by
  induction n using Nat.twoStepInduction generalizing j with
  | zero =>
      cases j <;> simp [pathDenominator]
  | one =>
      cases j with
      | zero => simp [pathDenominator]
      | succ j =>
          have he : 1-(j+1) = 0 := by omega
          simp [pathDenominator, he]
  | more n h0 h1 =>
      cases j with
      | zero => simp only [pathDenominator_recurrence, map_sub,
          PowerSeries.coeff_zero_X_mul, sub_zero, h1, pow_zero, Nat.sub_zero,
          Nat.choose_zero_right, Nat.cast_one, mul_one]
      | succ j =>
          rw [pathDenominator_recurrence, map_sub, PowerSeries.coeff_succ_X_mul, h1, h0]
          by_cases hj : j ≤ n
          · rw [show n+1-(j+1)=n-j by omega, show n+2-(j+1)=n-j+1 by omega,
              Nat.choose_succ_succ, Nat.cast_add]
            simp only [pow_succ]
            ring
          · have h0' : n-j=0 := by omega
            have h1' : n+1-(j+1)=0 := by omega
            have h2' : n+2-(j+1)<j+1 := by omega
            have h2'' : (n+1-j).choose (j+1) = 0 :=
              Nat.choose_eq_zero_of_lt (by omega)
            have hj0 : j ≠ 0 := by omega
            have hz : Nat.choose 0 j = 0 := Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hj0)
            simp [h0', h1', Nat.choose_eq_zero_of_lt h2', h2'', hz]

@[simp] theorem pathDenominator_constantCoeff (n : ℕ) :
    (pathDenominator n).constantCoeff = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, pathDenominator_coeff]
  simp

/-- Replacement z↦z², as an actual power-series algebra homomorphism. -/
def expandedPathDenominator (n : ℕ) : PowerSeries ℤ :=
  PowerSeries.expand 2 (by decide) (pathDenominator n)

@[simp] theorem expandedPathDenominator_zero : expandedPathDenominator 0 = 1 := by
  simp [expandedPathDenominator]

@[simp] theorem expandedPathDenominator_one : expandedPathDenominator 1 = 1 := by
  simp [expandedPathDenominator]

theorem expandedPathDenominator_recurrence (n : ℕ) :
    expandedPathDenominator (n+2) = expandedPathDenominator (n+1) -
      PowerSeries.X^2 * expandedPathDenominator n := by
  simp only [expandedPathDenominator, pathDenominator_recurrence, map_sub, map_mul,
    PowerSeries.expand_X]

@[simp] theorem expandedPathDenominator_constantCoeff (n : ℕ) :
    (expandedPathDenominator n).constantCoeff = 1 := by
  simp only [expandedPathDenominator, PowerSeries.constantCoeff_expand,
    pathDenominator_constantCoeff]

theorem expandedPathDenominator_inverse (n : ℕ) :
    PowerSeries.invOfUnit (expandedPathDenominator n) 1 =
      PowerSeries.expand 2 (by decide) (PowerSeries.invOfUnit (pathDenominator n) 1) := by
  let φ := PowerSeries.expand 2 (by decide) (PowerSeries.invOfUnit (pathDenominator n) 1)
  have hm : expandedPathDenominator n * φ = 1 := by
    dsimp only [φ]
    rw [expandedPathDenominator, ← map_mul,
      PowerSeries.mul_invOfUnit _ 1 (pathDenominator_constantCoeff n), map_one]
  calc
    PowerSeries.invOfUnit (expandedPathDenominator n) 1 =
        PowerSeries.invOfUnit (expandedPathDenominator n) 1 * 1 := (mul_one _).symm
    _ = PowerSeries.invOfUnit (expandedPathDenominator n) 1 *
        (expandedPathDenominator n * φ) := by rw [hm]
    _ = φ := by
      rw [← mul_assoc, PowerSeries.invOfUnit_mul _ 1
        (expandedPathDenominator_constantCoeff n), one_mul]

theorem expandedPathDenominator_inverse_coeff (n s : ℕ) :
    PowerSeries.coeff (2*s) (PowerSeries.invOfUnit (expandedPathDenominator n) 1) =
      PowerSeries.coeff s (PowerSeries.invOfUnit (pathDenominator n) 1) := by
  rw [expandedPathDenominator_inverse, PowerSeries.coeff_expand_mul]

/-- Ordinary binomial coefficients outside their printed integer range are
zero.  The guard retains the negative-bottom case instead of truncating it
to a spurious coefficient choose(_,0)=1. -/
def paperMatrix (w s : ℕ) : Matrix (Fin s) (Fin s) ℤ :=
  fun i j => if i.val ≤ j.val+1 then
    ((w+i.val-j.val).choose (j.val+1-i.val) : ℤ) else 0

theorem inverseCoefficientMatrix_pathDenominator (w s : ℕ) :
    PowerSeriesInverseDeterminant.inverseCoefficientMatrix (pathDenominator (w+1)) s =
      paperMatrix w s := by
  ext i j
  by_cases hij : i.val ≤ j.val+1
  · simp only [PowerSeriesInverseDeterminant.inverseCoefficientMatrix, paperMatrix,
      hij, if_true, pathDenominator_coeff]
    have htop : w+1-(j.val+1-i.val)=w+i.val-j.val := by omega
    rw [htop]
    have hsign : (-1 : ℤ)^i.val * ((-1 : ℤ)^(j.val+1) *
        (-1 : ℤ)^(j.val+1-i.val)) = 1 := by
      rw [← pow_add, ← pow_add, show i.val+(j.val+1+(j.val+1-i.val))=2*(j.val+1) by omega,
        pow_mul]
      simp
    calc
      (-1 : ℤ)^i.val * ((-1 : ℤ)^(j.val+1) *
          ((-1 : ℤ)^(j.val+1-i.val) * ((w+i.val-j.val).choose (j.val+1-i.val) : ℤ))) =
        ((-1 : ℤ)^i.val * ((-1 : ℤ)^(j.val+1) * (-1 : ℤ)^(j.val+1-i.val))) *
          ((w+i.val-j.val).choose (j.val+1-i.val) : ℤ) := by ring
      _ = _ := by rw [hsign, one_mul]
  · simp only [PowerSeriesInverseDeterminant.inverseCoefficientMatrix, paperMatrix,
      hij, if_false, mul_zero]

theorem pathDenominator_inverse_coeff_eq_det (w s : ℕ) :
    PowerSeries.coeff s (PowerSeries.invOfUnit (pathDenominator (w+1)) 1) =
      (paperMatrix w s).det := by
  rw [PowerSeriesInverseDeterminant.coeff_inverse_eq_det _ (pathDenominator_constantCoeff _),
    inverseCoefficientMatrix_pathDenominator]

end PaperVerification.AlternatingForms.PathDeterminant
