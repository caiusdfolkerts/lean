module

public import PaperVerification.AlternatingFormsTransferDefinitions
public import PaperVerification.MatrixPowerSeriesResolvent
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

/-!
# The all-length transfer formula in Proposition 5.1

An explicit continuant row multiplies the actual resolvent to a singleton
row. The coefficient-defined matrix series then gives the reciprocal of the
paper's exact denominator. No determinant evaluation or bounded computation
is assumed. This source is pending compilation.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix

namespace PaperVerification.AlternatingForms.BigradedTransfer

variable {R : Type*} [CommRing R]

/-- The ordinary continuants with the same interior recurrence. -/
def continuant (u v : R) : ℕ → Polynomial R
  | 0 => 1
  | 1 => 1-Polynomial.C (u+v)*Polynomial.X
  | m+2 => (1-Polynomial.C (u+v)*Polynomial.X)*continuant u v (m+1)-
      Polynomial.C (u*v)*Polynomial.X^2*continuant u v m

@[simp] theorem continuant_zero (u v : R) : continuant u v 0=1 := rfl
@[simp] theorem continuant_one (u v : R) :
    continuant u v 1=1-Polynomial.C (u+v)*Polynomial.X := rfl

theorem continuant_recurrence (u v : R) (m : ℕ) :
    continuant u v (m+2)=
      (1-Polynomial.C (u+v)*Polynomial.X)*continuant u v (m+1)-
        Polynomial.C (u*v)*Polynomial.X^2*continuant u v m := rfl

/-- Changing the height-zero diagonal from u+v to v gives precisely D. -/
theorem denominator_eq_continuant (u v : R) (m : ℕ) :
    denominator u v (m+1)=continuant u v (m+1)+
      Polynomial.C u*Polynomial.X*continuant u v m := by
  induction m using Nat.twoStepInduction with
  | zero => simp only [Nat.zero_add,denominator_one,continuant_one,continuant_zero,map_add]; ring
  | one =>
      rw [denominator_recurrence,continuant_recurrence]
      simp only [Nat.zero_add,Nat.add_zero,denominator_one,denominator_zero,continuant_one,continuant_zero,map_add]
      ring
  | more m h0 h1 =>
      rw [denominator_recurrence u v (m+1),h1,h0,
        continuant_recurrence u v (m+1),continuant_recurrence u v m]
      ring

def previous {h : ℕ} (j : Fin (h+1)) : Fin (h+1) :=
  ⟨j.val-1,(Nat.sub_le j.val 1).trans_lt j.isLt⟩

def next {h : ℕ} (j : Fin (h+1)) (hj : j.val<h) : Fin (h+1) :=
  ⟨j.val+1,Nat.succ_lt_succ hj⟩

/-- Exact multiplication of a row by the tridiagonal transfer matrix,
including both boundary states. -/
theorem vecMul_transferMatrix (h : ℕ) (u v : R) (row : Fin (h+1) → R)
    (j : Fin (h+1)) :
    (row ᵥ* transferMatrix h u v) j=
      row j*(if j.val=0 then v else u+v)+
      (if hj : 0<j.val then row (previous j) else 0)+
      (if hj : j.val<h then row (next j hj)*(u*v) else 0) := by
  classical
  have hd : (∑ i,row i*(if i=j then (if i.val=0 then v else u+v) else 0))=
      row j*(if j.val=0 then v else u+v) := by
    simp [mul_ite]
  have hu : (∑ i : Fin (h+1),row i*(if i.val+1=j.val then 1 else 0))=
      (if hj : 0<j.val then row (previous j) else 0) := by
    by_cases hj : 0<j.val
    · rw [dif_pos hj,Finset.sum_eq_single (previous j)]
      · have he : (previous j).val+1=j.val := by dsimp [previous]; omega
        simp only [he,ite_true,mul_one]
      · intro i hi hne
        have he : i.val+1≠j.val := by
          intro he
          apply hne
          apply Fin.ext
          dsimp [previous]
          omega
        simp only [he,ite_false,mul_zero]
      · simp
    · rw [dif_neg hj]
      apply Finset.sum_eq_zero
      intro i hi
      have he : i.val+1≠j.val := by omega
      simp only [he,ite_false,mul_zero]
  have hl : (∑ i : Fin (h+1),row i*(if j.val+1=i.val then u*v else 0))=
      (if hj : j.val<h then row (next j hj)*(u*v) else 0) := by
    by_cases hj : j.val<h
    · rw [dif_pos hj,Finset.sum_eq_single (next j hj)]
      · simp only [next,ite_true]
      · intro i hi hne
        have he : j.val+1≠i.val := by
          intro he
          apply hne
          apply Fin.ext
          exact he.symm
        simp only [he,ite_false,mul_zero]
      · simp
    · rw [dif_neg hj]
      apply Finset.sum_eq_zero
      intro i hi
      have he : j.val+1≠i.val := by have hi' := i.isLt; omega
      simp only [he,ite_false,mul_zero]
  simp only [Matrix.vecMul,dotProduct,transferMatrix,mul_add,Finset.sum_add_distrib]
  rw [hd,hu,hl]

/-- Coefficient extension changes only u and v in the actual matrix. -/
theorem transferMatrix_map_C (h : ℕ) (u v : R) :
    (transferMatrix h u v).map PowerSeries.C=
      transferMatrix h (PowerSeries.C u) (PowerSeries.C v) := by
  classical
  apply Matrix.ext
  intro i j
  simp only [Matrix.map_apply,transferMatrix,map_add,map_mul]
  split_ifs <;> simp

/-- The explicit row of continuants; all entries are genuine formal series. -/
def continuantRow (h : ℕ) (u v : R) (j : Fin (h+1)) : PowerSeries R :=
  PowerSeries.X^j.val*(continuant u v (h-j.val) : PowerSeries R)

@[simp] theorem continuantRow_last (h : ℕ) (u v : R) :
    continuantRow h u v (Fin.last h)=PowerSeries.X^h := by
  simp [continuantRow]

/-- The entry of the actual resolvent product, before inserting the row certificate. -/
theorem row_resolvent_apply (h : ℕ) (u v : R)
    (row : Fin (h+1) → PowerSeries R) (j : Fin (h+1)) :
    (row ᵥ* MatrixPowerSeries.resolventMatrix (transferMatrix h u v)) j=
      row j-PowerSeries.X*(
        row j*(if j.val=0 then PowerSeries.C v else PowerSeries.C u+PowerSeries.C v)+
        (if hj : 0<j.val then row (previous j) else 0)+
        (if hj : j.val<h then row (next j hj)*(PowerSeries.C u*PowerSeries.C v) else 0)) := by
  rw [MatrixPowerSeries.resolventMatrix,Matrix.vecMul_sub,Matrix.vecMul_one,
    Matrix.vecMul_smul,transferMatrix_map_C]
  change row j-PowerSeries.X*(row ᵥ* transferMatrix h (PowerSeries.C u) (PowerSeries.C v)) j=_
  rw [vecMul_transferMatrix]


/-- The same recurrence in the actual power-series ring. -/
theorem continuant_series_recurrence (u v : R) (m : ℕ) :
    (continuant u v (m+2) : PowerSeries R)=
      (1-(PowerSeries.C u+PowerSeries.C v)*PowerSeries.X)*
          (continuant u v (m+1) : PowerSeries R)-
        (PowerSeries.C u*PowerSeries.C v)*PowerSeries.X^2*
          (continuant u v m : PowerSeries R) := by
  simp only [continuant_recurrence,Polynomial.coe_sub,Polynomial.coe_mul,
    Polynomial.coe_one,Polynomial.coe_C,Polynomial.coe_X,Polynomial.coe_pow,
    map_add,map_mul,Polynomial.coe_add]

theorem denominator_series_eq_continuant (u v : R) (m : ℕ) :
    (denominator u v (m+1) : PowerSeries R)=
      (continuant u v (m+1) : PowerSeries R)+
        PowerSeries.C u*PowerSeries.X*(continuant u v m : PowerSeries R) := by
  rw [denominator_eq_continuant]
  simp only [Polynomial.coe_add,Polynomial.coe_mul,Polynomial.coe_C,Polynomial.coe_X]

/-- The explicit row certificate at every height, including the single-state case. -/
theorem continuantRow_resolvent (h : ℕ) (u v : R) :
    continuantRow h u v ᵥ* MatrixPowerSeries.resolventMatrix (transferMatrix h u v)=
      Pi.single 0 (denominator u v (h+1) : PowerSeries R) := by
  classical
  funext j
  rw [row_resolvent_apply]
  by_cases hj0 : j=0
  · subst j
    cases h with
    | zero =>
        simp only [continuantRow,Fin.val_zero,Nat.sub_zero,pow_zero,
          continuant_zero,Polynomial.coe_one,one_mul,Nat.lt_irrefl,
          ite_true,dite_false,add_zero,Pi.single_eq_same,Nat.zero_add,
          denominator_one,Polynomial.coe_sub,Polynomial.coe_mul,
          Polynomial.coe_C,Polynomial.coe_X]
        ring
    | succ h =>
        have H : (continuant u v (h+1) : PowerSeries R)-PowerSeries.X*(
            (continuant u v (h+1) : PowerSeries R)*PowerSeries.C v+
            PowerSeries.X*(continuant u v h : PowerSeries R)*
              (PowerSeries.C u*PowerSeries.C v))=
            (denominator u v (h+2) : PowerSeries R) := by
          rw [show h+2=(h+1)+1 by omega,denominator_series_eq_continuant]
          rw [show h+1+1=h+2 by omega,continuant_series_recurrence]
          ring
        simpa [continuantRow,next,previous] using H
  · have hjv : j.val≠0 := fun hz ↦ hj0 (Fin.ext hz)
    have hjp : 0<j.val := Nat.pos_of_ne_zero hjv
    have hrhs : (Pi.single (0 : Fin (h+1))
        (denominator u v (h+1) : PowerSeries R) : Fin (h+1) → PowerSeries R) j=0 := by
      simp [Pi.single_apply,hj0,Ne.symm hj0]
    rw [hrhs]
    by_cases hjh : j.val<h
    · have hk0 : h-j.val=(h-j.val-1)+1 := by omega
      have hkm : h-(j.val-1)=(h-j.val-1)+2 := by omega
      have hkp : h-(j.val+1)=h-j.val-1 := by omega
      have hp0 : (PowerSeries.X : PowerSeries R)^j.val=
          PowerSeries.X^(j.val-1)*PowerSeries.X := by
        conv_lhs => rw [show j.val=(j.val-1)+1 by omega,pow_succ]
      have hp1 : (PowerSeries.X : PowerSeries R)^(j.val+1)=
          PowerSeries.X^(j.val-1)*PowerSeries.X^2 := by
        rw [pow_succ,hp0]
        ring
      have H : (PowerSeries.X : PowerSeries R)^j.val*
            (continuant u v (h-j.val) : PowerSeries R)-PowerSeries.X*(
              PowerSeries.X^j.val*(continuant u v (h-j.val) : PowerSeries R)*
                (PowerSeries.C u+PowerSeries.C v)+
              PowerSeries.X^(j.val-1)*(continuant u v (h-(j.val-1)) : PowerSeries R)+
              PowerSeries.X^(j.val+1)*(continuant u v (h-(j.val+1)) : PowerSeries R)*
                (PowerSeries.C u*PowerSeries.C v))=0 := by
        rw [hk0,hkm,hkp,continuant_series_recurrence,hp0,hp1]
        ring
      simpa [continuantRow,previous,next,hjv,hjp,hjh] using H
    · have hjlast : j.val=h := by have hj' := j.isLt; omega
      have hp : (PowerSeries.X : PowerSeries R)^j.val=
          PowerSeries.X^(j.val-1)*PowerSeries.X := by
        conv_lhs => rw [show j.val=(j.val-1)+1 by omega,pow_succ]
      have hk0 : h-j.val=0 := by omega
      have hkm : h-(j.val-1)=1 := by omega
      have H : (PowerSeries.X : PowerSeries R)^j.val*
            (continuant u v (h-j.val) : PowerSeries R)-PowerSeries.X*(
              PowerSeries.X^j.val*(continuant u v (h-j.val) : PowerSeries R)*
                (PowerSeries.C u+PowerSeries.C v)+
              PowerSeries.X^(j.val-1)*(continuant u v (h-(j.val-1)) : PowerSeries R))=0 := by
        rw [hk0,hkm]
        simp only [continuant_zero,continuant_one,Polynomial.coe_one,
          Polynomial.coe_sub,Polynomial.coe_mul,Polynomial.coe_C,Polynomial.coe_X,
          map_add,Polynomial.coe_add,mul_one]
        rw [hp]
        ring
      simpa [continuantRow,previous,next,hjv,hjp,hjh] using H

/-- The row certificate proves the full generating-function identity. -/
theorem transfer_series_denominator (h : ℕ) (u v : R) :
    (denominator u v (h+1) : PowerSeries R)*
      PowerSeries.mk (fun N ↦ (transferMatrix h u v^N) 0 (Fin.last h))=
        PowerSeries.X^h := by
  have H := MatrixPowerSeries.row_certificate_entry (transferMatrix h u v)
    (continuantRow h u v) (denominator u v (h+1) : PowerSeries R) 0
    (continuantRow_resolvent h u v) (Fin.last h)
  rw [continuantRow_last] at H
  exact H

/-- The exact unrestricted coefficient formula used in Proposition5.1. -/
theorem transfer_power_entry (h s : ℕ) (u v : R) :
    (transferMatrix h u v^(s+h)) 0 (Fin.last h)=
      PowerSeries.coeff s (inverseDenominator u v (h+1)) := by
  apply MatrixPowerSeries.power_entry_of_row_certificate (transferMatrix h u v)
    (continuantRow h u v) (denominator u v (h+1) : PowerSeries R) 0 (Fin.last h) h
    (continuantRow_resolvent h u v) (continuantRow_last h u v)
  change Polynomial.constantCoeff (denominator u v (h+1))=1
  exact denominator_constantCoeff u v (h+1)

end PaperVerification.AlternatingForms.BigradedTransfer
