module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Formal generating series of an actual finite transfer matrix

The coefficient of degree N is the actual matrix power T^N.  The resolvent
identity is proved coefficient by coefficient, with no convergence or
invertibility assumption on T.  A row certificate then determines a selected
entry of the inverse. This new source awaits compilation and audit.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix

namespace PaperVerification.MatrixPowerSeries

variable {R I : Type*} [CommRing R] [Fintype I] [DecidableEq I]

/-- Every entry is the formal series of the corresponding entries of T^N. -/
def seriesMatrix (T : Matrix I I R) : Matrix I I (PowerSeries R) :=
  Matrix.of fun i j ↦ PowerSeries.mk fun N ↦ (T^N) i j

@[simp] theorem coeff_seriesMatrix (T : Matrix I I R) (N : ℕ) (i j : I) :
    PowerSeries.coeff N (seriesMatrix T i j)=(T^N) i j :=
  by simp only [seriesMatrix,Matrix.of_apply,PowerSeries.coeff_mk]

/-- The actual matrix I-zT over the formal power-series ring. -/
def resolventMatrix (T : Matrix I I R) : Matrix I I (PowerSeries R) :=
  1-(PowerSeries.X : PowerSeries R) • T.map (PowerSeries.C (R := R))

theorem series_equation (T : Matrix I I R) (i j : I) :
    seriesMatrix T i j-PowerSeries.X*
        (∑ k,PowerSeries.C (T i k)*seriesMatrix T k j)=
      PowerSeries.C ((1 : Matrix I I R) i j) := by
  apply PowerSeries.ext
  intro N
  cases N with
  | zero => simp [seriesMatrix]
  | succ N =>
      simp [coeff_seriesMatrix,PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_C_mul,pow_succ',Matrix.mul_apply]

/-- The coefficient-defined series is a right inverse of the actual resolvent. -/
theorem resolvent_mul_series (T : Matrix I I R) :
    resolventMatrix T*seriesMatrix T=1 := by
  rw [resolventMatrix,sub_mul,one_mul,Matrix.smul_mul]
  apply Matrix.ext
  intro i j
  change seriesMatrix T i j-PowerSeries.X*
      ((T.map (PowerSeries.C (R := R))*seriesMatrix T) i j)=
        (1 : Matrix I I (PowerSeries R)) i j
  rw [Matrix.mul_apply]
  simp only [Matrix.map_apply]
  rw [series_equation]
  by_cases h : i=j <;> simp [Matrix.one_apply,h]

/-- A row certificate computes an inverse entry by associativity of the
actual finite matrix product. It is not a determinant or inverse assumption. -/
theorem row_certificate_entry (T : Matrix I I R) (row : I → PowerSeries R)
    (D : PowerSeries R) (first : I)
    (hrow : row ᵥ* resolventMatrix T=Pi.single first D) (last : I) :
    D*seriesMatrix T first last=row last := by
  have h := congrFun (Matrix.vecMul_vecMul row (resolventMatrix T) (seriesMatrix T)) last
  rw [hrow,resolvent_mul_series,Matrix.single_vecMul,Matrix.vecMul_one] at h
  exact h

/-- A unit-constant row certificate gives the entire formal inverse entry. -/
theorem series_entry_of_row_certificate (T : Matrix I I R) (row : I → PowerSeries R)
    (D : PowerSeries R) (first last : I) (height : ℕ)
    (hrow : row ᵥ* resolventMatrix T=Pi.single first D)
    (hlast : row last=PowerSeries.X^height) (hD : PowerSeries.constantCoeff D=1) :
    seriesMatrix T first last=PowerSeries.X^height*PowerSeries.invOfUnit D 1 := by
  have hentry := row_certificate_entry T row D first hrow last
  rw [hlast] at hentry
  calc
    seriesMatrix T first last = 1*seriesMatrix T first last := (one_mul _).symm
    _ = (PowerSeries.invOfUnit D 1*D)*seriesMatrix T first last := by
      rw [PowerSeries.invOfUnit_mul D 1 hD]
    _ = PowerSeries.invOfUnit D 1*(D*seriesMatrix T first last) := mul_assoc _ _ _
    _ = PowerSeries.invOfUnit D 1*PowerSeries.X^height := by rw [hentry]
    _ = PowerSeries.X^height*PowerSeries.invOfUnit D 1 := mul_comm _ _

/-- All coefficients, including the unbounded length parameter, follow from
the formal row certificate. -/
theorem power_entry_of_row_certificate (T : Matrix I I R) (row : I → PowerSeries R)
    (D : PowerSeries R) (first last : I) (height : ℕ)
    (hrow : row ᵥ* resolventMatrix T=Pi.single first D)
    (hlast : row last=PowerSeries.X^height) (hD : PowerSeries.constantCoeff D=1)
    (s : ℕ) :
    (T^(s+height)) first last=PowerSeries.coeff s (PowerSeries.invOfUnit D 1) := by
  have h := congrArg (PowerSeries.coeff (s+height))
    (series_entry_of_row_certificate T row D first last height hrow hlast hD)
  rwa [coeff_seriesMatrix,PowerSeries.coeff_X_pow_mul] at h

end PaperVerification.MatrixPowerSeries
