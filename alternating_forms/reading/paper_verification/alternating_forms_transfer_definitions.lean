module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# The exact transfer matrix and denominator in Proposition5.1

There are `h+1` height states.  Matrix rows are source states and columns
are target states: up steps have weight one, down steps weight `u*v`,
height-zero loops weight `v`, and positive-height loops total weight `u+v`.
The denominator is an actual polynomial, defined by the printed recurrence;
its inverse is the formal power-series inverse with constant coefficient one.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.BigradedTransfer

variable {R : Type*} [CommRing R]

/-- The actual finite weighted adjacency matrix, with source-to-target orientation. -/
def transferMatrix (h : ℕ) (u v : R) : Matrix (Fin (h+1)) (Fin (h+1)) R :=
  fun i j =>
    (if i=j then (if i.val=0 then v else u+v) else 0) +
    (if i.val+1=j.val then 1 else 0) +
    (if j.val+1=i.val then u*v else 0)

/-- The paper's polynomials `D_m(z;u,v)`, including `D_0=1`. -/
def denominator (u v : R) : ℕ → Polynomial R
  | 0 => 1
  | 1 => 1-Polynomial.C v*Polynomial.X
  | m+2 => (1-Polynomial.C (u+v)*Polynomial.X)*denominator u v (m+1)-
      Polynomial.C (u*v)*Polynomial.X^2*denominator u v m

@[simp] theorem denominator_zero (u v : R) : denominator u v 0=1 := rfl
@[simp] theorem denominator_one (u v : R) :
    denominator u v 1=1-Polynomial.C v*Polynomial.X := rfl

theorem denominator_recurrence (u v : R) (m : ℕ) :
    denominator u v (m+2)=
      (1-Polynomial.C (u+v)*Polynomial.X)*denominator u v (m+1)-
        Polynomial.C (u*v)*Polynomial.X^2*denominator u v m := rfl

@[simp] theorem denominator_constantCoeff (u v : R) (m : ℕ) :
    Polynomial.constantCoeff (denominator u v m)=1 := by
  induction m using Nat.twoStepInduction with
  | zero => simp [denominator]
  | one => simp [denominator]
  | more m h0 h1 =>
      have h1' : (denominator u v (m+1)).coeff 0=1 := h1
      simp [denominator,h1']

/-- The reciprocal as a formal series; the preceding theorem proves the
unit constant term required for the inverse identities. -/
def inverseDenominator (u v : R) (m : ℕ) : PowerSeries R :=
  PowerSeries.invOfUnit (denominator u v m : PowerSeries R) 1

end PaperVerification.AlternatingForms.BigradedTransfer
