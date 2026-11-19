module

public import VolumePolynomials.HigherLiftSupport
public import VolumePolynomials.HigherLiftConverse
public import VolumePolynomials.ClosedVolumeLocus
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Basic

@[expose] public section

set_option autoImplicit false
noncomputable section

/-! The literal affine coefficient slice in every dimension at least three.
Its coordinate formulas prove both continuity and polynomial preimage
compatibility. Its fibers refer to the original realization locus. -/

open Set MeasureTheory MvPolynomial
open scoped BigOperators

namespace VolumePolynomials.HigherLift

@[simp] theorem coefficients_zero (α s z : ℝ) :
    coefficients 0 α s z = CubicSlice.coefficients α s z := by
  first
  | have hc : correction 0 = 1 := by norm_num [correction]
    simp only [coefficients, polynomial, pow_zero, one_mul, hc, CubicSlice.coefficients]

theorem mem_volumeLocus_of_cubic_all (k : ℕ) {α s z : ℝ}
    (h : CubicSlice.coefficients α s z ∈ VolumeLocus 3 3) :
    coefficients k α s z ∈ VolumeLocus 3 (3 + k) := by
  first
  | rcases k with _ | k
    · simpa only [coefficients_zero] using h
    · exact mem_volumeLocus_of_cubic h (Nat.succ_pos k)

def sliceTerm (k : ℕ) : Fin 7 → MvPolynomial (Fin 2) ℝ :=
  ![C (6 * correction k) * X 0, C (6 * correction k) * X 0,
    C 3, C 3, C 3 * X 0, C 3, C 6 * X 1]

theorem eval_sliceTerm (k : ℕ) (p : Fin 2 → ℝ) (j : Fin 7) :
    MvPolynomial.eval p (sliceTerm k j) = termCoefficient k (2 * p 0) (p 0) (p 1) j := by
  first
  | fin_cases j <;> simp only [sliceTerm, termCoefficient, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_val_zero', Matrix.cons_val_succ',
      MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X] <;> ring

def sliceCoordinate (k : ℕ) (β : MultiIndex 3 (3 + k)) : MvPolynomial (Fin 2) ℝ :=
  ∑ j : Fin 7, if termExponent k j = exponent β then sliceTerm k j else 0

theorem eval_sliceCoordinate (k : ℕ) (p : Fin 2 → ℝ) (β : MultiIndex 3 (3 + k)) :
    MvPolynomial.eval p (sliceCoordinate k β) = coefficients k (2 * p 0) (p 0) (p 1) β := by
  first
  | classical
    rw [sliceCoordinate, MvPolynomial.eval_sum, coefficients_eq_terms]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs
    · exact eval_sliceTerm k p j
    · exact map_zero _

def coefficientSlice (k : ℕ) : Set (Fin 2 → ℝ) :=
  {p | coefficients k (2 * p 0) (p 0) (p 1) ∈ VolumeLocus 3 (3 + k)}

theorem coefficientSlice_eq_preimage (k : ℕ) :
    coefficientSlice k = (fun p β => MvPolynomial.eval p (sliceCoordinate k β)) ⁻¹'
      VolumeLocus 3 (3 + k) := by
  first
  | ext p
    simp only [Set.mem_preimage, coefficientSlice, Set.mem_setOf_eq,
      eval_sliceCoordinate]

theorem continuous_slice_map (k : ℕ) :
    Continuous (fun p : Fin 2 → ℝ => coefficients k (2 * p 0) (p 0) (p 1)) := by
  first
  | apply continuous_pi
    intro β
    have heq : (fun p : Fin 2 → ℝ => coefficients k (2 * p 0) (p 0) (p 1) β) =
        fun p => MvPolynomial.eval p (sliceCoordinate k β) := by
      first
      | funext p
        exact (eval_sliceCoordinate k p β).symm
    rw [heq]
    exact (sliceCoordinate k β).continuous_eval

theorem isClosed_coefficientSlice (k : ℕ) : IsClosed (coefficientSlice k) :=
  (isClosed_volumeLocus 3 (3 + k) (by omega)).preimage (continuous_slice_map k)

theorem isSemialgebraic_coefficientSlice (k : ℕ)
    (h : TauCeti.IsSemialgebraic (VolumeLocus 3 (3 + k))) :
    TauCeti.IsSemialgebraic (coefficientSlice k) := by
  first
  | rw [coefficientSlice_eq_preimage]
    exact h.preimage_eval (sliceCoordinate k)

def fiberValues (k : ℕ) (s : ℝ) : Set ℝ :=
  {z | coefficients k (2 * s) s z ∈ VolumeLocus 3 (3 + k)}

def boundaryValue (k : ℕ) (s : ℝ) : ℝ := sInf (fiberValues k s)

theorem fiberValues_closed (k : ℕ) (s : ℝ) : IsClosed (fiberValues k s) := by
  first
  | have hc : Continuous (fun z : ℝ => (![s, z] : Fin 2 → ℝ)) := by fun_prop
    exact (isClosed_coefficientSlice k).preimage hc

theorem fiberValues_nonnegative {k : ℕ} {s z : ℝ} (hz : z ∈ fiberValues k s) : 0 ≤ z := by
  first
  | obtain ⟨K, hK⟩ := hz
    exact triple_parameter_nonnegative hK

theorem fiberValues_bddBelow (k : ℕ) (s : ℝ) : BddBelow (fiberValues k s) :=
  ⟨0, fun _ hz => fiberValues_nonnegative hz⟩

theorem boundaryValue_attained_of_nonempty (k : ℕ) (s : ℝ)
    (hne : (fiberValues k s).Nonempty) :
    boundaryValue k s ∈ fiberValues k s ∧
      ∀ z ∈ fiberValues k s, boundaryValue k s ≤ z := by
  first
  | exact ⟨(fiberValues_closed k s).csInf_mem hne (fiberValues_bddBelow k s),
      fun _ hz => csInf_le (fiberValues_bddBelow k s) hz⟩

end VolumePolynomials.HigherLift
