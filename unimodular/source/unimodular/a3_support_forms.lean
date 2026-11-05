module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators

/-! UNVERIFIED exact support-value map in Section 7.1. Its domain has one
coordinate for each of the twelve ordered, unequal root labels. The range
and all linear relations are computed by an explicit right inverse, not
by numerical rank tests. This module alone makes no projectivity claim:
the geometric support-function criterion and square subdivision
classification remain separate dependencies. -/

namespace Unimodular.A3SupportForms

abbrev RayIndex := {p : Fin 4 × Fin 4 // p.1 ≠ p.2}
abbrev Heights := RayIndex → ℝ

def height (h : Heights) (i j : Fin 4) : ℝ :=
  if hij : i ≠ j then h ⟨(i, j), hij⟩ else 0

/-- The six rows are in source-cut order 01,02,03,12,13,23, exactly as
in the paper. No symmetry between h_ij and h_ji is imposed. -/
def forms : Heights →ₗ[ℝ] (Fin 6 → ℝ) where
  toFun h := ![
    height h 0 2 + height h 1 3 - height h 0 3 - height h 1 2,
    height h 0 1 + height h 2 3 - height h 0 3 - height h 2 1,
    height h 0 1 + height h 3 2 - height h 0 2 - height h 3 1,
    height h 1 0 + height h 2 3 - height h 1 3 - height h 2 0,
    height h 1 0 + height h 3 2 - height h 1 2 - height h 3 0,
    height h 2 0 + height h 3 1 - height h 2 1 - height h 3 0]
  map_add' h k := by
    ext i
    fin_cases i <;> simp [height] <;> ring
  map_smul' a h := by
    ext i
    fin_cases i <;> simp [height, smul_eq_mul] <;> ring

def relation : (Fin 6 → ℝ) →ₗ[ℝ] ℝ where
  toFun y := y 0 - y 1 + y 2 + y 3 - y 4 + y 5
  map_add' y z := by simp; ring
  map_smul' a y := by simp [smul_eq_mul]; ring

def relationSigns : Fin 6 → ℝ := ![1, -1, 1, 1, -1, 1]

theorem relation_forms (h : Heights) : relation (forms h) = 0 := by
  simp [relation, forms]
  ring

/-- Five freely chosen heights give a right inverse on the displayed
hyperplane. The unused diagonal entries are not support variables. -/
def liftMatrix (y : Fin 6 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  ![![0, 0, -y 2, -y 1 + y 5],
    ![0, 0, -y 4, -y 3],
    ![0, -y 5, 0, 0],
    ![0, 0, 0, 0]]

def lift (y : Fin 6 → ℝ) : Heights :=
  fun e => liftMatrix y e.val.1 e.val.2

theorem forms_lift (y : Fin 6 → ℝ) :
    forms (lift y) = ![y 1 - y 2 - y 3 + y 4 - y 5,
      y 1, y 2, y 3, y 4, y 5] := by
  ext i
  fin_cases i <;> simp [forms, height, lift, liftMatrix] <;> ring

theorem forms_lift_of_relation_zero {y : Fin 6 → ℝ} (hy : relation y = 0) :
    forms (lift y) = y := by
  rw [forms_lift]
  change y 0 - y 1 + y 2 + y 3 - y 4 + y 5 = 0 at hy
  ext i
  fin_cases i <;> simp <;> linarith

/-- Exact image: every point of the five-dimensional hyperplane is the
six-tuple of square forms of actual root support heights. -/
theorem exists_heights_iff (y : Fin 6 → ℝ) :
    (∃ h : Heights, forms h = y) ↔ relation y = 0 := by
  constructor
  · rintro ⟨h, rfl⟩
    exact relation_forms h
  · intro hy
    exact ⟨lift y, forms_lift_of_relation_zero hy⟩

theorem range_forms : LinearMap.range forms = LinearMap.ker relation := by
  ext y
  exact exists_heights_iff y

/-- Every linear relation is a scalar multiple of (1,-1,1,1,-1,1).
This is the full uniqueness assertion following equation (7.1). -/
theorem all_relations (c : Fin 6 → ℝ) :
    (∀ h : Heights, ∑ i, c i * forms h i = 0) ↔
      ∃ t : ℝ, c = t • relationSigns := by
  constructor
  · intro hc
    have h1 := hc (lift ![0, 1, 0, 0, 0, 0])
    have h2 := hc (lift ![0, 0, 1, 0, 0, 0])
    have h3 := hc (lift ![0, 0, 0, 1, 0, 0])
    have h4 := hc (lift ![0, 0, 0, 0, 1, 0])
    have h5 := hc (lift ![0, 0, 0, 0, 0, 1])
    norm_num [forms_lift, Fin.sum_univ_succ] at h1 h2 h3 h4 h5
    refine ⟨c 0, ?_⟩
    ext i
    fin_cases i <;> simp [relationSigns, smul_eq_mul] <;> linarith
  · rintro ⟨t, rfl⟩ h
    calc
      (∑ i, (t • relationSigns) i * forms h i) = t * relation (forms h) := by
        simp [relationSigns, relation, Fin.sum_univ_succ, smul_eq_mul]
        ring
      _ = 0 := by rw [relation_forms, mul_zero]

theorem forms_constant (a : ℝ) : forms (fun _ => a) = 0 := by
  ext i
  fin_cases i <;> simp [forms, height]

/-- Any feasible square-form tuple can be realized as an arbitrarily
small linear perturbation of the canonical constant support heights.
Preservation of geometric old-wall inequalities requires a separate
finite strict-inequality argument, not merely this algebraic identity. -/
theorem perturbation_forms (a t : ℝ) (h : Heights) :
    forms ((fun _ => a) + t • h) = t • forms h := by
  rw [map_add, map_smul, forms_constant, zero_add]

end Unimodular.A3SupportForms

#print axioms Unimodular.A3SupportForms.relation_forms
#print axioms Unimodular.A3SupportForms.exists_heights_iff
#print axioms Unimodular.A3SupportForms.range_forms
#print axioms Unimodular.A3SupportForms.all_relations
#print axioms Unimodular.A3SupportForms.perturbation_forms

#check "UNIMODULAR_A3_SUPPORT_FORMS_EOF_V1"
