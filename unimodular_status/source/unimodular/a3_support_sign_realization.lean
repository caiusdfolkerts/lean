module

public import Unimodular.A3SignPatterns
public import Unimodular.A3SupportForms
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

/-!
# Integral realization of every feasible support-form sign pattern

UNVERIFIED DEVELOPMENT SOURCE until its exact pinned native check succeeds.
The heights below are actual integers on the twelve labelled roots. Their
six forms are the literal linear forms from Section 7.1. This module does
not identify the resulting choices with projective fans; that geometric
support-function implication is proved separately.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Unimodular.A3SignPatterns

variable {I : Type*} [Fintype I]

def balancedInteger (s : I → SignType) (i : I) : ℤ :=
  (if s i = 1 then ((negativeIndices s).card : ℤ) else 0) -
  (if s i = -1 then ((positiveIndices s).card : ℤ) else 0)

@[simp] theorem cast_balancedInteger (s : I → SignType) (i : I) :
    (balancedInteger s i : ℝ) = balancedWeight s i := by
  simp [balancedInteger, balancedWeight]

/-- Sign feasibility in a zero-sum hyperplane already has an integral
witness. The assertion includes every finite index type, including the
empty type. -/
theorem exists_integral_zero_sum_with_sign_iff (s : I → SignType) :
    (∃ z : I → ℤ, (∑ i, z i) = 0 ∧
      ∀ i, SignType.sign (z i : ℝ) = s i) ↔ Admissible s := by
  constructor
  · rintro ⟨z, hz, hs⟩
    apply (exists_zero_sum_with_sign_iff s).mp
    refine ⟨fun i => (z i : ℝ), ?_, hs⟩
    change (∑ i, (z i : ℝ)) = 0
    exact_mod_cast hz
  · rintro (hz | ⟨hp, hn⟩)
    · exact ⟨fun _ => 0, by simp, fun i => by simpa [hz i] using sign_zero (α := ℝ)⟩
    · have hs : (∑ i, (balancedInteger s i : ℝ)) = 0 := by
        simpa only [cast_balancedInteger] using sum_balancedWeight s
      refine ⟨balancedInteger s, ?_, ?_⟩
      · exact_mod_cast hs
      · intro i
        simpa only [cast_balancedInteger] using balancedWeight_sign s hp hn i

end Unimodular.A3SignPatterns

namespace Unimodular.A3SupportForms

open A3SignPatterns

abbrev IntegralHeights := RayIndex → ℤ

/-- The signs of the unique linear relation, in the paper's cut order. -/
def coefficientSigns : Fin 6 → SignType := ![1, -1, 1, 1, -1, 1]

theorem coefficientSigns_ne_zero (i : Fin 6) : coefficientSigns i ≠ 0 := by
  fin_cases i <;> decide

theorem coefficientSigns_sq (i : Fin 6) :
    coefficientSigns i * coefficientSigns i = 1 := by
  fin_cases i <;> decide

theorem coefficientSigns_real_sq (i : Fin 6) :
    (coefficientSigns i : ℝ) * (coefficientSigns i : ℝ) = 1 := by
  fin_cases i <;> norm_num [coefficientSigns]

theorem sign_coefficientSigns (i : Fin 6) :
    SignType.sign (coefficientSigns i : ℝ) = coefficientSigns i := by
  fin_cases i <;> norm_num [coefficientSigns]

theorem relation_eq_sum (y : Fin 6 → ℝ) :
    relation y = ∑ i, (coefficientSigns i : ℝ) * y i := by
  simp [relation, coefficientSigns, Fin.sum_univ_succ]
  ring

/-- The same integral right inverse as the real `liftMatrix`. -/
def integralLiftMatrix (z : Fin 6 → ℤ) : Matrix (Fin 4) (Fin 4) ℤ :=
  ![![0, 0, -z 2, -z 1 + z 5],
    ![0, 0, -z 4, -z 3],
    ![0, -z 5, 0, 0],
    ![0, 0, 0, 0]]

def integralLift (z : Fin 6 → ℤ) : IntegralHeights :=
  fun e => integralLiftMatrix z e.val.1 e.val.2

theorem cast_integralLift (z : Fin 6 → ℤ) :
    (fun e => (integralLift z e : ℝ)) = lift (fun i => (z i : ℝ)) := by
  funext e
  rcases e with ⟨⟨i, j⟩, hij⟩
  fin_cases i <;> fin_cases j <;>
    simp [integralLift, integralLiftMatrix, lift, liftMatrix]

/-- Exact integral sign realization of the six literal square forms. No
additional symmetry between the heights of opposite roots is imposed. -/
theorem exists_integral_heights_with_sign_iff (s : Fin 6 → SignType) :
    (∃ h : IntegralHeights, ∀ i,
      SignType.sign (forms (fun e => (h e : ℝ)) i) = s i) ↔
      Admissible (fun i => coefficientSigns i * s i) := by
  constructor
  · rintro ⟨h, hs⟩
    apply (exists_zero_sum_with_sign_iff
      (fun i => coefficientSigns i * s i)).mp
    refine ⟨fun i => (coefficientSigns i : ℝ) * forms (fun e => (h e : ℝ)) i,
      ?_, ?_⟩
    · rw [← relation_eq_sum]
      exact relation_forms _
    · intro i
      rw [sign_mul, sign_coefficientSigns, hs i]
  · intro hs
    obtain ⟨z, hz, hsign⟩ :=
      (exists_integral_zero_sum_with_sign_iff
        (fun i => coefficientSigns i * s i)).mpr hs
    let w : Fin 6 → ℤ := fun i => (coefficientSigns i : ℤ) * z i
    have hw : relation (fun i => (w i : ℝ)) = 0 := by
      rw [relation_eq_sum]
      calc
        (∑ i, (coefficientSigns i : ℝ) * (w i : ℝ)) = ∑ i, (z i : ℝ) := by
          apply Finset.sum_congr rfl
          intro i hi
          simp only [w, Int.cast_mul, SignType.intCast_cast, ← mul_assoc,
            coefficientSigns_real_sq, one_mul]
        _ = 0 := by exact_mod_cast hz
    refine ⟨integralLift w, ?_⟩
    intro i
    rw [cast_integralLift, forms_lift_of_relation_zero hw]
    change SignType.sign (((coefficientSigns i : ℤ) * z i : ℤ) : ℝ) = s i
    rw [Int.cast_mul, SignType.intCast_cast, sign_mul, sign_coefficientSigns, hsign i]
    rw [← mul_assoc, coefficientSigns_sq, one_mul]

/-- Adding any integral constant changes none of the six forms. -/
theorem forms_add_integral_constant (h : IntegralHeights) (N : ℤ) :
    forms (fun e => ((h e + N : ℤ) : ℝ)) = forms (fun e => (h e : ℝ)) := by
  have heq : (fun e => ((h e + N : ℤ) : ℝ)) =
      (fun e => (h e : ℝ)) + (fun _ => (N : ℝ)) := by
    funext e
    simp
  rw [heq, map_add, forms_constant, add_zero]

/-- Every feasible sign pattern has strictly positive integral heights.
This is an algebraic normalization, not a substitute for the remaining
strict support-function inequalities between different cut facets. -/
theorem exists_positive_integral_heights_with_sign_iff (s : Fin 6 → SignType) :
    (∃ h : IntegralHeights, (∀ e, 0 < h e) ∧ ∀ i,
      SignType.sign (forms (fun e => (h e : ℝ)) i) = s i) ↔
      Admissible (fun i => coefficientSigns i * s i) := by
  classical
  constructor
  · rintro ⟨h, hpos, hs⟩
    exact (exists_integral_heights_with_sign_iff s).mp ⟨h, hs⟩
  · intro hs
    obtain ⟨h, hsign⟩ := (exists_integral_heights_with_sign_iff s).mpr hs
    let N : ℤ := 1 + ∑ e, |h e|
    refine ⟨fun e => h e + N, ?_, ?_⟩
    · intro e
      have hb : |h e| ≤ ∑ j, |h j| :=
        Finset.single_le_sum (fun j _ => abs_nonneg (h j)) (Finset.mem_univ e)
      have hn := neg_le_abs (h e)
      dsimp only [N]
      linarith
    · intro i
      rw [forms_add_integral_constant]
      exact hsign i

end Unimodular.A3SupportForms

#print axioms Unimodular.A3SignPatterns.exists_integral_zero_sum_with_sign_iff
#print axioms Unimodular.A3SupportForms.exists_integral_heights_with_sign_iff
#print axioms Unimodular.A3SupportForms.forms_add_integral_constant
#print axioms Unimodular.A3SupportForms.exists_positive_integral_heights_with_sign_iff
#check "UNIMODULAR_A3_INTEGRAL_SUPPORT_SIGNS_EOF_V1"
