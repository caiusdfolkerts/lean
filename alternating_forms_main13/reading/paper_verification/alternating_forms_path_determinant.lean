module

public import PaperVerification.AlternatingFormsPathDenominator
public import PaperVerification.AlternatingFormsStripWalks

/-!
# The printed determinant counts the actual strip walks

An explicit continuant row certifies the inverse endpoint entry of the
path-graph resolvent.  Its coefficients count Mathlib's actual graph walks.
Together with the finite triangular-matrix adjugate calculation, this gives
the complete determinant identity in Theorem 1.1, in all parameter sizes.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix Classical

namespace PaperVerification.AlternatingForms.PathDeterminant

def previous {w : ℕ} (j : Fin (w+1)) : Fin (w+1) :=
  ⟨j.val-1, (Nat.sub_le _ _).trans_lt j.isLt⟩

def next {w : ℕ} (j : Fin (w+1)) (hj : j.val < w) : Fin (w+1) :=
  ⟨j.val+1, Nat.succ_lt_succ hj⟩

theorem path_neighbor_sum {R : Type*} [CommRing R] (w : ℕ)
    (j : Fin (w+1)) (f : Fin (w+1) → R) :
    (∑ i : Fin (w+1), if i.val+1=j.val ∨ j.val+1=i.val then f i else 0) =
      (if h : 0 < j.val then f (previous j) else 0) +
      (if h : j.val < w then f (next j h) else 0) := by
  have hs (i : Fin (w+1)) :
      (if i.val+1=j.val ∨ j.val+1=i.val then f i else 0) =
        (if i.val+1=j.val then f i else 0) +
        (if j.val+1=i.val then f i else 0) := by
    by_cases h₁ : i.val+1=j.val
    · have h₂ : ¬j.val+1=i.val := by omega
      simp [h₁, h₂]
    · by_cases h₂ : j.val+1=i.val <;> simp [h₁, h₂]
  simp_rw [hs]
  rw [Finset.sum_add_distrib]
  congr 1
  · by_cases hj : 0 < j.val
    · rw [dif_pos hj]
      have hv (i : Fin (w+1)) : i.val+1=j.val ↔ i=previous j := by
        constructor
        · intro hi
          apply Fin.ext
          dsimp [previous]
          omega
        · rintro rfl
          dsimp [previous]
          omega
      simp_rw [hv]
      simp
    · have hz (i : Fin (w+1)) : ¬i.val+1=j.val := by omega
      simp [hz, hj]
  · by_cases hj : j.val < w
    · rw [dif_pos hj]
      have hv (i : Fin (w+1)) : j.val+1=i.val ↔ i=next j hj := by
        constructor
        · intro hi
          apply Fin.ext
          exact hi.symm
        · rintro rfl
          rfl
      simp_rw [hv]
      simp
    · have hz (i : Fin (w+1)) : ¬j.val+1=i.val := by have hi := i.isLt; omega
      simp [hz, hj]

theorem vecMul_pathMatrix {R : Type*} [CommRing R] (w : ℕ)
    (row : Fin (w+1) → R) (j : Fin (w+1)) :
    (row ᵥ* (SimpleGraph.pathGraph (w+1)).adjMatrix R) j =
      (if h : 0 < j.val then row (previous j) else 0) +
      (if h : j.val < w then row (next j h) else 0) := by
  simp only [Matrix.vecMul, dotProduct, SimpleGraph.adjMatrix_apply,
    SimpleGraph.pathGraph_adj, mul_ite, mul_one, mul_zero]
  exact path_neighbor_sum w j row

def pathMatrix (w : ℕ) : Matrix (Fin (w+1)) (Fin (w+1)) ℤ :=
  (SimpleGraph.pathGraph (w+1)).adjMatrix ℤ

theorem pathMatrix_map_C (w : ℕ) :
    (pathMatrix w).map (PowerSeries.C (R := ℤ)) =
      (SimpleGraph.pathGraph (w+1)).adjMatrix (PowerSeries ℤ) := by
  ext i j
  simp only [pathMatrix, Matrix.map_apply, SimpleGraph.adjMatrix_apply]
  split_ifs <;> simp

theorem row_resolvent_apply (w : ℕ) (row : Fin (w+1) → PowerSeries ℤ)
    (j : Fin (w+1)) :
    (row ᵥ* MatrixPowerSeries.resolventMatrix (pathMatrix w)) j =
      row j - PowerSeries.X *
        ((if h : 0 < j.val then row (previous j) else 0) +
         (if h : j.val < w then row (next j h) else 0)) := by
  rw [MatrixPowerSeries.resolventMatrix, Matrix.vecMul_sub, Matrix.vecMul_one,
    Matrix.vecMul_smul, pathMatrix_map_C]
  change row j - PowerSeries.X *
    (row ᵥ* (SimpleGraph.pathGraph (w+1)).adjMatrix (PowerSeries ℤ)) j = _
  rw [vecMul_pathMatrix]

def pathRow (w : ℕ) (j : Fin (w+1)) : PowerSeries ℤ :=
  PowerSeries.X^j.val * expandedPathDenominator (w-j.val)

@[simp] theorem pathRow_last (w : ℕ) : pathRow w (Fin.last w) = PowerSeries.X^w := by
  simp [pathRow]

theorem pathRow_resolvent (w : ℕ) :
    pathRow w ᵥ* MatrixPowerSeries.resolventMatrix (pathMatrix w) =
      Pi.single 0 (expandedPathDenominator (w+1)) := by
  funext j
  rw [row_resolvent_apply]
  by_cases hj0 : j=0
  · subst j
    cases w with
    | zero => simp [pathRow]
    | succ w =>
        have H : expandedPathDenominator (w+1) - PowerSeries.X *
            (PowerSeries.X * expandedPathDenominator w) = expandedPathDenominator (w+2) := by
          rw [expandedPathDenominator_recurrence]
          ring
        simpa [pathRow, previous, next] using H
  · have hjv : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
    have hjp : 0 < j.val := Nat.pos_of_ne_zero hjv
    have hrhs : (Pi.single (0 : Fin (w+1)) (expandedPathDenominator (w+1)) :
        Fin (w+1) → PowerSeries ℤ) j = 0 := by
      simp [Pi.single_apply, hj0, Ne.symm hj0]
    rw [hrhs]
    by_cases hjw : j.val < w
    · have hk0 : w-j.val = (w-j.val-1)+1 := by omega
      have hkm : w-(j.val-1) = (w-j.val-1)+2 := by omega
      have hkp : w-(j.val+1) = w-j.val-1 := by omega
      have hp0 : (PowerSeries.X : PowerSeries ℤ)^j.val =
          PowerSeries.X^(j.val-1)*PowerSeries.X := by
        conv_lhs => rw [show j.val=(j.val-1)+1 by omega, pow_succ]
      have hp1 : (PowerSeries.X : PowerSeries ℤ)^(j.val+1) =
          PowerSeries.X^(j.val-1)*PowerSeries.X^2 := by
        rw [pow_succ, hp0]
        ring
      have H : (PowerSeries.X : PowerSeries ℤ)^j.val * expandedPathDenominator (w-j.val) -
          PowerSeries.X *
            (PowerSeries.X^(j.val-1)*expandedPathDenominator (w-(j.val-1)) +
             PowerSeries.X^(j.val+1)*expandedPathDenominator (w-(j.val+1))) = 0 := by
        rw [hk0, hkm, hkp, expandedPathDenominator_recurrence, hp0, hp1]
        ring
      simpa [pathRow, previous, next, hjp, hjw] using H
    · have hjlast : j.val=w := by have hj := j.isLt; omega
      have hp : (PowerSeries.X : PowerSeries ℤ)^j.val =
          PowerSeries.X^(j.val-1)*PowerSeries.X := by
        conv_lhs => rw [show j.val=(j.val-1)+1 by omega, pow_succ]
      have hk0 : w-j.val=0 := by omega
      have hkm : w-(j.val-1)=1 := by omega
      have H : (PowerSeries.X : PowerSeries ℤ)^j.val * expandedPathDenominator (w-j.val) -
          PowerSeries.X * (PowerSeries.X^(j.val-1)*expandedPathDenominator (w-(j.val-1))) = 0 := by
        rw [hk0, hkm, expandedPathDenominator_zero, expandedPathDenominator_one,
          mul_one, mul_one, hp]
        ring
      simpa [pathRow, previous, next, hjp, hjw] using H

theorem pathMatrix_power_endpoint (w s : ℕ) :
    (pathMatrix w^(w+2*s)) 0 (Fin.last w) =
      PowerSeries.coeff s (PowerSeries.invOfUnit (pathDenominator (w+1)) 1) := by
  have h := MatrixPowerSeries.power_entry_of_row_certificate (pathMatrix w) (pathRow w)
    (expandedPathDenominator (w+1)) 0 (Fin.last w) w
    (pathRow_resolvent w) (pathRow_last w) (expandedPathDenominator_constantCoeff _) (2*s)
  rw [expandedPathDenominator_inverse_coeff] at h
  simpa only [Nat.add_comm (2*s) w] using h

/-- The full unrestricted walk count is connected to the finite determinant. -/
theorem walkCount_eq_determinant (w s : ℕ) :
    (StripWalks.walkCount w (w+2*s) : ℤ) = (paperMatrix w s).det := by
  have hc := SimpleGraph.adjMatrix_pow_apply_eq_card_walk
    (G := SimpleGraph.pathGraph (w+1)) (α := ℤ) (w+2*s) 0 (Fin.last w)
  have he : (StripWalks.walkCount w (w+2*s) : ℤ) =
      (pathMatrix w^(w+2*s)) 0 (Fin.last w) := hc.symm
  rw [he, pathMatrix_power_endpoint, pathDenominator_inverse_coeff_eq_det]

/-- The exact determinant identity printed in Theorem 1.1, including s=0.
The hypothesis only ensures that the printed endpoint width is nonnegative. -/
theorem paperWalkCount_determinant (n s : ℕ) (hs : 2*s ≤ n+2) :
    (StripWalks.paperWalkCount n s : ℤ) = (paperMatrix (n+2-2*s) s).det := by
  have h := walkCount_eq_determinant (n+2-2*s) s
  simpa only [StripWalks.paperWalkCount, Nat.sub_add_cancel hs] using h

end PaperVerification.AlternatingForms.PathDeterminant
