module
public import Consolidated.MatrixNormalization
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases
public import MatroidCatalogue.N8R4
public import MatroidChecked.ChartRealization
public import MatroidChecked.ExactDensity
public import MatroidChecked.GoldenIdentification
public import MatroidChecked.GoldenRationalObstruction
public import MatroidChecked.MinorFormulaSpecialization
public import Papers.ExceptionalSupportBounds
public import Papers.RankFourCertificateNormalization
public import Papers.RationalElimination
public import Papers.RelationMatrixDensity
public import Papers.ResidualPolynomialDensity
public import Papers.SmallRelationMatrixCriteria

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.all false

/- Source: Charts/Case569.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart569
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 6 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![-(X (none) * X (some (some (some (some (none)))))) - (X (some (some (none)))) + (1), -(X (none) * X (some (some (some (some (none)))))) - (X (some (some (some (none))))) + (1), X (none) - (1), X (some (none)) + (X (some (some (none)))) - (1), X (some (none)) + (X (some (some (some (none))))) - (1), X (some (none)) * X (some (some (some (some (none))))) - (X (some (some (none))) * X (some (some (some (none)))))]
noncomputable def U0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![X (none), X (some (none)), X (some (some (none))), X (some (some (some (none)))), X (some (some (some (some (none)))))]
noncomputable def R0 : Fin 6 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![X (none) * X (some (some (some (some (none))))) + (X (some (some (none)))) - (1), X (none) * X (some (some (some (some (none))))) + (X (some (some (some (none))))) - (1), X (none) - (1), X (some (none)) + (X (some (some (none)))) - (1), X (some (none)) + (X (some (some (some (none))))) - (1), X (some (none)) * X (some (some (some (some (none))))) - (X (some (some (none))) * X (some (some (some (none)))))]

noncomputable def reductions0 (j : Fin 6) : FactorReduction U0 (E0 j) (R0 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring

noncomputable def nextE0 : Fin 6 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (some (none)) + (X (some (some (some (none))))) - (1), X (some (some (none))) + (X (some (some (some (none))))) - (1), 0, X (none) + (X (some (none))) - (1), X (none) + (X (some (some (none)))) - (1), X (none) * X (some (some (some (none)))) - (X (some (none)) * X (some (some (none))))]
noncomputable def nextU0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![1, X (none), X (some (none)), X (some (some (none))), X (some (some (some (none))))]

noncomputable def step0 : LinearStep (Option (Option (Option (Option (Fin 0))))) 6 5 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := 1
  b := -(1)
  pivot := 2
  pivot_identity := by simp [R0, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1, 1, 1, 0, 0, 0]
  equation_quotient := ![X (some (some (some (some (none))))), X (some (some (some (some (none))))), 1, 0, 0, 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![1, 0, 0, 0, 0]
  unit_quotient := ![1, 0, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 6 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (some (none)) + (X (some (some (some (none))))) - (1), X (some (some (none))) + (X (some (some (some (none))))) - (1), 0, X (none) + (X (some (none))) - (1), X (none) + (X (some (some (none)))) - (1), X (none) * X (some (some (some (none)))) - (X (some (none)) * X (some (some (none))))]
noncomputable def U1 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![1, X (none), X (some (none)), X (some (some (none))), X (some (some (some (none))))]
noncomputable def R1 : Fin 6 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (some (none)) + (X (some (some (some (none))))) - (1), X (some (some (none))) + (X (some (some (some (none))))) - (1), 0, X (none) + (X (some (none))) - (1), X (none) + (X (some (some (none)))) - (1), X (none) * X (some (some (some (none)))) - (X (some (none)) * X (some (some (none))))]

noncomputable def reductions1 (j : Fin 6) : FactorReduction U1 (E1 j) (R1 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring

noncomputable def nextE1 : Fin 6 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none) + (X (some (some (none)))) - (1), X (some (none)) + (X (some (some (none)))) - (1), 0, 0, -(X (none)) + (X (some (none))), -(X (none) * X (some (none))) - (X (none) * X (some (some (none)))) + (X (some (some (none))))]
noncomputable def nextU1 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![1, -(X (none)) + (1), X (none), X (some (none)), X (some (some (none)))]

noncomputable def step1 : LinearStep (Option (Option (Option (Fin 0)))) 6 5 where
  sourceE := R1
  sourceU := U1
  targetE := nextE1
  targetU := nextU1
  a := 1
  b := X (none) - (1)
  pivot := 3
  pivot_identity := by simp [R1, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 0, 0, 1, 1, 1]
  equation_quotient := ![0, 0, 0, 1, 1, X (some (some (some (none))))]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring
  unit_power := ![0, 1, 0, 0, 0]
  unit_quotient := ![0, 1, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring

noncomputable def E2 : Fin 6 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none) + (X (some (some (none)))) - (1), X (some (none)) + (X (some (some (none)))) - (1), 0, 0, -(X (none)) + (X (some (none))), -(X (none) * X (some (none))) - (X (none) * X (some (some (none)))) + (X (some (some (none))))]
noncomputable def U2 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![1, -(X (none)) + (1), X (none), X (some (none)), X (some (some (none)))]
noncomputable def R2 : Fin 6 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none) + (X (some (some (none)))) - (1), X (some (none)) + (X (some (some (none)))) - (1), 0, 0, X (none) - (X (some (none))), X (none) * X (some (none)) + (X (none) * X (some (some (none)))) - (X (some (some (none))))]

noncomputable def reductions2 (j : Fin 6) : FactorReduction U2 (E2 j) (R2 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring

noncomputable def nextE2 : Fin 6 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, X (none) + (X (some (none))) - (1), 0, 0, -(X (none)) - (X (some (none))) + (1), -(X (none) * X (some (none))) + (X (none)) - ((X (some (none))) ^ 2)]
noncomputable def nextU2 : Fin 5 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![1, X (some (none)), -(X (some (none))) + (1), X (none), X (some (none))]

noncomputable def step2 : LinearStep (Option (Option (Fin 0))) 6 5 where
  sourceE := R2
  sourceU := U2
  targetE := nextE2
  targetU := nextU2
  a := 1
  b := X (some (none)) - (1)
  pivot := 0
  pivot_identity := by simp [R2, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1, 0, 0, 0, 1, 1]
  equation_quotient := ![1, 0, 0, 0, 1, X (some (none)) + (X (some (some (none))))]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring
  unit_power := ![0, 1, 1, 0, 0]
  unit_quotient := ![0, -(1), 1, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring

noncomputable def E3 : Fin 6 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, X (none) + (X (some (none))) - (1), 0, 0, -(X (none)) - (X (some (none))) + (1), -(X (none) * X (some (none))) + (X (none)) - ((X (some (none))) ^ 2)]
noncomputable def U3 : Fin 5 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![1, X (some (none)), -(X (some (none))) + (1), X (none), X (some (none))]
noncomputable def R3 : Fin 6 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, X (none) + (X (some (none))) - (1), 0, 0, X (none) + (X (some (none))) - (1), X (none) * X (some (none)) - (X (none)) + ((X (some (none))) ^ 2)]

noncomputable def reductions3 (j : Fin 6) : FactorReduction U3 (E3 j) (R3 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring

noncomputable def nextE3 : Fin 6 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 0, 0, 2 * X (none) - (1)]
noncomputable def nextU3 : Fin 5 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![1, X (none), -(X (none)) + (1), -(X (none)) + (1), X (none)]

noncomputable def step3 : LinearStep (Option (Fin 0)) 6 5 where
  sourceE := R3
  sourceU := U3
  targetE := nextE3
  targetU := nextU3
  a := 1
  b := X (none) - (1)
  pivot := 1
  pivot_identity := by simp [R3, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 1, 0, 0, 1, 1]
  equation_quotient := ![0, 1, 0, 0, 1, X (some (none)) - (1)]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R3, U3, nextE3, nextU3, map_ofNat] <;> ring
  unit_power := ![0, 0, 0, 1, 0]
  unit_quotient := ![0, 0, 0, 1, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R3, U3, nextE3, nextU3, map_ofNat] <;> ring

noncomputable def E4 : Fin 6 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 0, 0, 2 * X (none) - (1)]
noncomputable def U4 : Fin 5 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![1, X (none), -(X (none)) + (1), -(X (none)) + (1), X (none)]
noncomputable def R4 : Fin 6 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 0, 0, 2 * X (none) - (1)]

noncomputable def reductions4 (j : Fin 6) : FactorReduction U4 (E4 j) (R4 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring

noncomputable def nextE4 : Fin 6 → MvPolynomial (Fin 0) ℚ :=
  ![0, 0, 0, 0, 0, 0]
noncomputable def nextU4 : Fin 5 → MvPolynomial (Fin 0) ℚ :=
  ![1, 1, 1, 1, 1]

noncomputable def step4 : LinearStep (Fin 0) 6 5 where
  sourceE := R4
  sourceU := U4
  targetE := nextE4
  targetU := nextU4
  a := 2
  b := -(1)
  pivot := 5
  pivot_identity := by simp [R4, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := C ((1 : ℚ) / 2)
      identity := by
        simp only [Fin.prod_univ_zero]
        calc
          (1 : _) = C (((1 : ℚ) / 2) * 2) := by norm_num
          _ = C ((1 : ℚ) / 2) * 2 := by simp only [map_mul, map_ofNat]
          _ = _ := by simp only [map_ofNat] <;> ring }
  equation_power := ![0, 0, 0, 0, 0, 1]
  equation_quotient := ![0, 0, 0, 0, 0, 2]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R4, U4, nextE4, nextU4, map_ofNat] <;> ring
  unit_power := ![0, 1, 1, 1, 1]
  unit_quotient := ![0, 1, -(1), -(1), 1]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R4, U4, nextE4, nextU4, map_ofNat] <;> ring

noncomputable def E5 : Fin 6 → MvPolynomial (Fin 0) ℚ :=
  ![0, 0, 0, 0, 0, 0]
noncomputable def U5 : Fin 5 → MvPolynomial (Fin 0) ℚ :=
  ![1, 1, 1, 1, 1]
noncomputable def R5 : Fin 6 → MvPolynomial (Fin 0) ℚ :=
  ![0, 0, 0, 0, 0, 0]

noncomputable def reductions5 (j : Fin 6) : FactorReduction U5 (E5 j) (R5 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U5, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E5, R5]<;> ring
    · simp [E5, R5]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U5, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E5, R5]<;> ring
    · simp [E5, R5]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U5, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E5, R5]<;> ring
    · simp [E5, R5]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U5, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E5, R5]<;> ring
    · simp [E5, R5]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U5, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E5, R5]<;> ring
    · simp [E5, R5]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U5, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E5, R5]<;> ring
    · simp [E5, R5]<;> ring

theorem dense5 : RationallyDenseSystem E5 U5 := by
  apply dense_system_of_factor_reductions E5 R5 U5 reductions5
  apply zero_equations_system_dense R5 U5
  intro j; fin_cases j <;> rfl

theorem dense4 : RationallyDenseSystem E4 U4 := by
  apply dense_system_of_factor_reductions E4 R4 U4 reductions4
  exact step4.preserves_density dense5

theorem dense3 : RationallyDenseSystem E3 U3 := by
  apply dense_system_of_factor_reductions E3 R3 U3 reductions3
  exact step3.preserves_density dense4

theorem dense2 : RationallyDenseSystem E2 U2 := by
  apply dense_system_of_factor_reductions E2 R2 U2 reductions2
  exact step2.preserves_density dense3

theorem dense1 : RationallyDenseSystem E1 U1 := by
  apply dense_system_of_factor_reductions E1 R1 U1 reductions1
  exact step1.preserves_density dense2

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  exact step0.preserves_density dense1

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart569
end

/- Source: ChartTables/Case569.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart569
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Option (Option (Option (Fin 0)))))) :=
  ![![.one, .one, .one, .zero], ![.one, .variable (none), .zero, .one], ![.one, .zero, .variable (some (none)), .variable (some (some (none)))], ![.zero, .one, .variable (some (some (some (none)))), .variable (some (some (some (some (none)))))]]

noncomputable def chartPositions : (Option (Option (Option (Option (Option (Fin 0)))))) → Coordinate × Coordinate :=
  Option.elim' (1, 1) (Option.elim' (2, 2) (Option.elim' (2, 3) (Option.elim' (3, 2) (Option.elim' (3, 3) (Fin.elim0)))))

noncomputable def chartUnitVariables : Fin 5 → (Option (Option (Option (Option (Option (Fin 0)))))) :=
  ![none, some (none), some (some (none)), some (some (some (none))), some (some (some (some (none))))]

noncomputable def chartLabelCode : ℕ := 16431240

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, true, true, true, true, false, true, true, true, true, true, true, true, false, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, false, true, true, true, true, true, true, true, true, false, true, true, false, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, false, false, false, false, true, false, false, false, false, false, false, false, true, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, true, false, false, false, false, false, false, false, false, true, false, false, true, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 569)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 569) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨32, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (32 : Fin 70)
      rw [minorFormula_at_32]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨64, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (64 : Fin 70)
      rw [minorFormula_at_64]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨55, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (55 : Fin 70)
      rw [minorFormula_at_55]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨67, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (67 : Fin 70)
      rw [minorFormula_at_67]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨51, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (51 : Fin 70)
      rw [minorFormula_at_51]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨14, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (14 : Fin 70)
      rw [minorFormula_at_14]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
  · intro i hi
    fin_cases i
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (1 : Fin 70) = _
      rw [minorFormula_at_1]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (6 : Fin 70) = _
      rw [minorFormula_at_6]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨5, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (14 : Fin 70)
      rw [minorFormula_at_14]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (17 : Fin 70) = _
      rw [minorFormula_at_17]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (32 : Fin 70)
      rw [minorFormula_at_32]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (38 : Fin 70) = _
      rw [minorFormula_at_38]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨4, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (51 : Fin 70)
      rw [minorFormula_at_51]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨2, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (55 : Fin 70)
      rw [minorFormula_at_55]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨1, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (64 : Fin 70)
      rw [minorFormula_at_64]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨3, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (67 : Fin 70)
      rw [minorFormula_at_67]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(4,1),(4,2),(5,3),(1,7)]

theorem chart_schedule : Papers.MatrixGaugeNormalization.checkSchedule chartForestRoots chartForestSteps = true := by
  decide +kernel

theorem chart_steps_are_ones : ∀ e ∈ chartForestSteps,
    (∃ i j : Coordinate, e = (firstFour i, lastFour j) ∧ chartEntries i j = .one) ∨
    (∃ i j : Coordinate, e = (lastFour j, firstFour i) ∧ chartEntries i j = .one) := by
  decide +kernel

theorem chart_ones_are_steps : ∀ i j : Coordinate, chartEntries i j = .one →
    (firstFour i, lastFour j) ∈ chartForestSteps ∨
    (lastFour j, firstFour i) ∈ chartForestSteps := by
  decide +kernel

theorem chart_all_nonbases : ∀ i, chartBasisMark i ≠ true → chartRequiredZero i = true := by
  decide +kernel

noncomputable def chart_certificate : ChartCertificate (Option (Option (Option (Option (Option (Fin 0)))))) 6 5
    (MatroidCatalogue.N8R4.family 569) where
  entries := chartEntries
  positions := chartPositions
  unitVariables := chartUnitVariables
  labelCode := chartLabelCode
  basisMark := chartBasisMark
  requiredZero := chartRequiredZero
  polynomials := chartMinorPolynomials
  equations := E0
  units := U0
  roots := chartForestRoots
  steps := chartForestSteps
  parameters := chart_parameters
  minors := chart_minors
  pattern := chart_pattern
  first_basis := chart_first_basis
  constraints := chart_entry_constraints
  equation_table := chart_equations
  units_exact := chart_units_exact
  required_nonbasis := chart_required_nonbasis
  schedule := chart_schedule
  steps_are_ones := chart_steps_are_ones
  ones_are_steps := chart_ones_are_steps

/-- Every real representation of this catalogue entry has rational zero-minor-preserving approximations. -/
theorem family_rationally_dense : MatroidChecked.ChartRealization.FamilyRationallyDense
    (MatroidCatalogue.N8R4.family 569) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart569
end

/- Source: Charts/Case570.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart570
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![-(X (some (some (none)))) - (X (some (some (some (some (none)))))) + (1), X (none) - (1), X (none) * X (some (none)) + (X (some (some (some (none))))) - (1), X (some (none)) * X (some (some (some (some (none))))) - (X (some (some (none))) * X (some (some (some (none))))), X (some (some (some (none)))) + (X (some (some (some (some (none)))))) - (1)]
noncomputable def U0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![X (none), X (some (none)), X (some (some (none))), X (some (some (some (none)))), X (some (some (some (some (none)))))]
noncomputable def R0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![X (some (some (none))) + (X (some (some (some (some (none)))))) - (1), X (none) - (1), X (none) * X (some (none)) + (X (some (some (some (none))))) - (1), X (some (none)) * X (some (some (some (some (none))))) - (X (some (some (none))) * X (some (some (some (none))))), X (some (some (some (none)))) + (X (some (some (some (some (none)))))) - (1)]

noncomputable def reductions0 (j : Fin 5) : FactorReduction U0 (E0 j) (R0 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring

noncomputable def nextE0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (some (none)) + (X (some (some (some (none))))) - (1), 0, X (none) + (X (some (some (none)))) - (1), X (none) * X (some (some (some (none)))) - (X (some (none)) * X (some (some (none)))), X (some (some (none))) + (X (some (some (some (none))))) - (1)]
noncomputable def nextU0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![1, X (none), X (some (none)), X (some (some (none))), X (some (some (some (none))))]

noncomputable def step0 : LinearStep (Option (Option (Option (Option (Fin 0))))) 5 5 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := 1
  b := -(1)
  pivot := 1
  pivot_identity := by simp [R0, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 1, 1, 0, 0]
  equation_quotient := ![0, 1, X (some (none)), 0, 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![1, 0, 0, 0, 0]
  unit_quotient := ![1, 0, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (some (none)) + (X (some (some (some (none))))) - (1), 0, X (none) + (X (some (some (none)))) - (1), X (none) * X (some (some (some (none)))) - (X (some (none)) * X (some (some (none)))), X (some (some (none))) + (X (some (some (some (none))))) - (1)]
noncomputable def U1 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![1, X (none), X (some (none)), X (some (some (none))), X (some (some (some (none))))]
noncomputable def R1 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (some (none)) + (X (some (some (some (none))))) - (1), 0, X (none) + (X (some (some (none)))) - (1), X (none) * X (some (some (some (none)))) - (X (some (none)) * X (some (some (none)))), X (some (some (none))) + (X (some (some (some (none))))) - (1)]

noncomputable def reductions1 (j : Fin 5) : FactorReduction U1 (E1 j) (R1 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring

noncomputable def nextE1 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none) + (X (some (some (none)))) - (1), 0, 0, -(X (none) * X (some (none))) - (X (some (none)) * X (some (some (none)))) + (X (some (some (none)))), X (some (none)) + (X (some (some (none)))) - (1)]
noncomputable def nextU1 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![1, -(X (some (none))) + (1), X (none), X (some (none)), X (some (some (none)))]

noncomputable def step1 : LinearStep (Option (Option (Option (Fin 0)))) 5 5 where
  sourceE := R1
  sourceU := U1
  targetE := nextE1
  targetU := nextU1
  a := 1
  b := X (some (none)) - (1)
  pivot := 2
  pivot_identity := by simp [R1, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 0, 1, 1, 0]
  equation_quotient := ![0, 0, 1, X (some (some (some (none)))), 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring
  unit_power := ![0, 1, 0, 0, 0]
  unit_quotient := ![0, 1, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring

noncomputable def E2 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none) + (X (some (some (none)))) - (1), 0, 0, -(X (none) * X (some (none))) - (X (some (none)) * X (some (some (none)))) + (X (some (some (none)))), X (some (none)) + (X (some (some (none)))) - (1)]
noncomputable def U2 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![1, -(X (some (none))) + (1), X (none), X (some (none)), X (some (some (none)))]
noncomputable def R2 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none) + (X (some (some (none)))) - (1), 0, 0, X (none) * X (some (none)) + (X (some (none)) * X (some (some (none)))) - (X (some (some (none)))), X (some (none)) + (X (some (some (none)))) - (1)]

noncomputable def reductions2 (j : Fin 5) : FactorReduction U2 (E2 j) (R2 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring

noncomputable def nextE2 : Fin 5 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, 0, 0, X (none) - (X (some (none))), X (none) + (X (some (none))) - (1)]
noncomputable def nextU2 : Fin 5 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![1, -(X (none)) + (1), -(X (some (none))) + (1), X (none), X (some (none))]

noncomputable def step2 : LinearStep (Option (Option (Fin 0))) 5 5 where
  sourceE := R2
  sourceU := U2
  targetE := nextE2
  targetU := nextU2
  a := 1
  b := X (some (none)) - (1)
  pivot := 0
  pivot_identity := by simp [R2, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1, 0, 0, 1, 0]
  equation_quotient := ![1, 0, 0, X (some (none)), 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring
  unit_power := ![0, 0, 1, 0, 0]
  unit_quotient := ![0, 0, 1, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring

noncomputable def E3 : Fin 5 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, 0, 0, X (none) - (X (some (none))), X (none) + (X (some (none))) - (1)]
noncomputable def U3 : Fin 5 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![1, -(X (none)) + (1), -(X (some (none))) + (1), X (none), X (some (none))]
noncomputable def R3 : Fin 5 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, 0, 0, X (none) - (X (some (none))), X (none) + (X (some (none))) - (1)]

noncomputable def reductions3 (j : Fin 5) : FactorReduction U3 (E3 j) (R3 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring

noncomputable def nextE3 : Fin 5 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 0, 2 * X (none) - (1)]
noncomputable def nextU3 : Fin 5 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![1, -(X (none)) + (1), -(X (none)) + (1), X (none), X (none)]

noncomputable def step3 : LinearStep (Option (Fin 0)) 5 5 where
  sourceE := R3
  sourceU := U3
  targetE := nextE3
  targetU := nextU3
  a := 1
  b := -(X (none))
  pivot := 3
  pivot_identity := by simp [R3, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 0, 0, 1, 1]
  equation_quotient := ![0, 0, 0, 1, 1]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R3, U3, nextE3, nextU3, map_ofNat] <;> ring
  unit_power := ![0, 1, 0, 1, 0]
  unit_quotient := ![0, -(1), 0, 1, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R3, U3, nextE3, nextU3, map_ofNat] <;> ring

noncomputable def E4 : Fin 5 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 0, 2 * X (none) - (1)]
noncomputable def U4 : Fin 5 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![1, -(X (none)) + (1), -(X (none)) + (1), X (none), X (none)]
noncomputable def R4 : Fin 5 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 0, 2 * X (none) - (1)]

noncomputable def reductions4 (j : Fin 5) : FactorReduction U4 (E4 j) (R4 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring

noncomputable def nextE4 : Fin 5 → MvPolynomial (Fin 0) ℚ :=
  ![0, 0, 0, 0, 0]
noncomputable def nextU4 : Fin 5 → MvPolynomial (Fin 0) ℚ :=
  ![1, 1, 1, 1, 1]

noncomputable def step4 : LinearStep (Fin 0) 5 5 where
  sourceE := R4
  sourceU := U4
  targetE := nextE4
  targetU := nextU4
  a := 2
  b := -(1)
  pivot := 4
  pivot_identity := by simp [R4, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := C ((1 : ℚ) / 2)
      identity := by
        simp only [Fin.prod_univ_zero]
        calc
          (1 : _) = C (((1 : ℚ) / 2) * 2) := by norm_num
          _ = C ((1 : ℚ) / 2) * 2 := by simp only [map_mul, map_ofNat]
          _ = _ := by simp only [map_ofNat] <;> ring }
  equation_power := ![0, 0, 0, 0, 1]
  equation_quotient := ![0, 0, 0, 0, 2]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R4, U4, nextE4, nextU4, map_ofNat] <;> ring
  unit_power := ![0, 1, 1, 1, 1]
  unit_quotient := ![0, -(1), -(1), 1, 1]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R4, U4, nextE4, nextU4, map_ofNat] <;> ring

noncomputable def E5 : Fin 5 → MvPolynomial (Fin 0) ℚ :=
  ![0, 0, 0, 0, 0]
noncomputable def U5 : Fin 5 → MvPolynomial (Fin 0) ℚ :=
  ![1, 1, 1, 1, 1]
noncomputable def R5 : Fin 5 → MvPolynomial (Fin 0) ℚ :=
  ![0, 0, 0, 0, 0]

noncomputable def reductions5 (j : Fin 5) : FactorReduction U5 (E5 j) (R5 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U5, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E5, R5]<;> ring
    · simp [E5, R5]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U5, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E5, R5]<;> ring
    · simp [E5, R5]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U5, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E5, R5]<;> ring
    · simp [E5, R5]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U5, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E5, R5]<;> ring
    · simp [E5, R5]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U5, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E5, R5]<;> ring
    · simp [E5, R5]<;> ring

theorem dense5 : RationallyDenseSystem E5 U5 := by
  apply dense_system_of_factor_reductions E5 R5 U5 reductions5
  apply zero_equations_system_dense R5 U5
  intro j; fin_cases j <;> rfl

theorem dense4 : RationallyDenseSystem E4 U4 := by
  apply dense_system_of_factor_reductions E4 R4 U4 reductions4
  exact step4.preserves_density dense5

theorem dense3 : RationallyDenseSystem E3 U3 := by
  apply dense_system_of_factor_reductions E3 R3 U3 reductions3
  exact step3.preserves_density dense4

theorem dense2 : RationallyDenseSystem E2 U2 := by
  apply dense_system_of_factor_reductions E2 R2 U2 reductions2
  exact step2.preserves_density dense3

theorem dense1 : RationallyDenseSystem E1 U1 := by
  apply dense_system_of_factor_reductions E1 R1 U1 reductions1
  exact step1.preserves_density dense2

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  exact step0.preserves_density dense1

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart570
end

/- Source: ChartTables/Case570.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart570
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Option (Option (Option (Fin 0)))))) :=
  ![![.one, .one, .zero, .one], ![.one, .variable (none), .one, .zero], ![.zero, .one, .variable (some (none)), .variable (some (some (none)))], ![.one, .zero, .variable (some (some (some (none)))), .variable (some (some (some (some (none)))))]]

noncomputable def chartPositions : (Option (Option (Option (Option (Option (Fin 0)))))) → Coordinate × Coordinate :=
  Option.elim' (1, 1) (Option.elim' (2, 2) (Option.elim' (2, 3) (Option.elim' (3, 2) (Option.elim' (3, 3) (Fin.elim0)))))

noncomputable def chartUnitVariables : Fin 5 → (Option (Option (Option (Option (Option (Fin 0)))))) :=
  ![none, some (none), some (some (none)), some (some (some (none))), some (some (some (some (none))))]

noncomputable def chartLabelCode : ℕ := 16398984

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, true, false, true, true, false, true, true, true, true, true, true, true, true, false, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, false, true, true, true, true, true, true, true, false, true, true, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, false, true, false, false, true, false, false, false, false, false, false, false, false, true, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, true, false, false, false, false, false, false, false, true, false, false, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 570)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 570) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨52, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (52 : Fin 70)
      rw [minorFormula_at_52]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨55, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (55 : Fin 70)
      rw [minorFormula_at_55]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨31, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (31 : Fin 70)
      rw [minorFormula_at_31]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨14, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (14 : Fin 70)
      rw [minorFormula_at_14]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨63, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (63 : Fin 70)
      rw [minorFormula_at_63]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
  · intro i hi
    fin_cases i
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (2 : Fin 70) = _
      rw [minorFormula_at_2]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (5 : Fin 70) = _
      rw [minorFormula_at_5]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨3, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (14 : Fin 70)
      rw [minorFormula_at_14]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (18 : Fin 70) = _
      rw [minorFormula_at_18]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨2, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (31 : Fin 70)
      rw [minorFormula_at_31]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (37 : Fin 70) = _
      rw [minorFormula_at_37]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (52 : Fin 70)
      rw [minorFormula_at_52]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨1, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (55 : Fin 70)
      rw [minorFormula_at_55]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨4, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (63 : Fin 70)
      rw [minorFormula_at_63]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,7),(4,1),(4,3),(5,2),(1,6)]

theorem chart_schedule : Papers.MatrixGaugeNormalization.checkSchedule chartForestRoots chartForestSteps = true := by
  decide +kernel

theorem chart_steps_are_ones : ∀ e ∈ chartForestSteps,
    (∃ i j : Coordinate, e = (firstFour i, lastFour j) ∧ chartEntries i j = .one) ∨
    (∃ i j : Coordinate, e = (lastFour j, firstFour i) ∧ chartEntries i j = .one) := by
  decide +kernel

theorem chart_ones_are_steps : ∀ i j : Coordinate, chartEntries i j = .one →
    (firstFour i, lastFour j) ∈ chartForestSteps ∨
    (lastFour j, firstFour i) ∈ chartForestSteps := by
  decide +kernel

theorem chart_all_nonbases : ∀ i, chartBasisMark i ≠ true → chartRequiredZero i = true := by
  decide +kernel

noncomputable def chart_certificate : ChartCertificate (Option (Option (Option (Option (Option (Fin 0)))))) 5 5
    (MatroidCatalogue.N8R4.family 570) where
  entries := chartEntries
  positions := chartPositions
  unitVariables := chartUnitVariables
  labelCode := chartLabelCode
  basisMark := chartBasisMark
  requiredZero := chartRequiredZero
  polynomials := chartMinorPolynomials
  equations := E0
  units := U0
  roots := chartForestRoots
  steps := chartForestSteps
  parameters := chart_parameters
  minors := chart_minors
  pattern := chart_pattern
  first_basis := chart_first_basis
  constraints := chart_entry_constraints
  equation_table := chart_equations
  units_exact := chart_units_exact
  required_nonbasis := chart_required_nonbasis
  schedule := chart_schedule
  steps_are_ones := chart_steps_are_ones
  ones_are_steps := chart_ones_are_steps

/-- Every real representation of this catalogue entry has rational zero-minor-preserving approximations. -/
theorem family_rationally_dense : MatroidChecked.ChartRealization.FamilyRationallyDense
    (MatroidCatalogue.N8R4.family 570) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart570
end

/- Source: Charts/Case571.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart571
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![-(X (none) * X (some (some (some (none))))) - (X (some (none)) * X (some (some (none))) * X (some (some (some (some (none)))))) + (X (some (none)) * X (some (some (some (none))))), -(X (some (some (none))) * X (some (some (some (some (none)))))) + (X (some (some (some (none))))) - (1), -(X (none)) + (X (some (some (some (some (none)))))), -(X (some (none)) * X (some (some (some (none))))) + (X (some (none))) + (X (some (some (some (none))))), X (none) - (X (some (none))) + (1)]
noncomputable def U0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![X (some (some (none))), X (none), X (some (none)), X (some (some (some (some (none))))), X (some (some (some (none))))]
noncomputable def R0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![X (none) * X (some (some (some (none)))) + (X (some (none)) * X (some (some (none))) * X (some (some (some (some (none)))))) - (X (some (none)) * X (some (some (some (none))))), X (some (some (none))) * X (some (some (some (some (none))))) - (X (some (some (some (none))))) + (1), X (none) - (X (some (some (some (some (none)))))), X (some (none)) * X (some (some (some (none)))) - (X (some (none))) - (X (some (some (some (none))))), X (none) - (X (some (none))) + (1)]

noncomputable def reductions0 (j : Fin 5) : FactorReduction U0 (E0 j) (R0 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring

noncomputable def nextE0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (none) * X (some (none)) * X (some (some (some (none)))) - (X (none) * X (some (some (none)))) + (X (some (some (none))) * X (some (some (some (none))))), X (some (none)) * X (some (some (some (none)))) - (X (some (some (none)))) + (1), 0, X (none) * X (some (some (none))) - (X (none)) - (X (some (some (none)))), -(X (none)) + (X (some (some (some (none))))) + (1)]
noncomputable def nextU0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (some (none)), X (some (some (some (none)))), X (none), X (some (some (some (none)))), X (some (some (none)))]

noncomputable def step0 : LinearStep (Option (Option (Option (Option (Fin 0))))) 5 5 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := 1
  b := -(X (some (some (some (none)))))
  pivot := 2
  pivot_identity := by simp [R0, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1, 0, 1, 0, 1]
  equation_quotient := ![X (some (some (some (none)))), 0, 1, 0, 1]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![0, 1, 0, 0, 0]
  unit_quotient := ![0, 1, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (none) * X (some (none)) * X (some (some (some (none)))) - (X (none) * X (some (some (none)))) + (X (some (some (none))) * X (some (some (some (none))))), X (some (none)) * X (some (some (some (none)))) - (X (some (some (none)))) + (1), 0, X (none) * X (some (some (none))) - (X (none)) - (X (some (some (none)))), -(X (none)) + (X (some (some (some (none))))) + (1)]
noncomputable def U1 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (some (none)), X (some (some (some (none)))), X (none), X (some (some (some (none)))), X (some (some (none)))]
noncomputable def R1 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (none) * X (some (none)) * X (some (some (some (none)))) - (X (none) * X (some (some (none)))) + (X (some (some (none))) * X (some (some (some (none))))), X (some (none)) * X (some (some (some (none)))) - (X (some (some (none)))) + (1), 0, X (none) * X (some (some (none))) - (X (none)) - (X (some (some (none)))), X (none) - (X (some (some (some (none))))) - (1)]

noncomputable def reductions1 (j : Fin 5) : FactorReduction U1 (E1 j) (R1 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring

noncomputable def nextE1 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none) * (X (some (some (none)))) ^ 2 + (X (none) * X (some (some (none)))) - (X (some (none))), X (none) * X (some (some (none))) - (X (some (none))) + (1), 0, X (some (none)) * X (some (some (none))) - (X (some (some (none)))) - (1), 0]
noncomputable def nextU1 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none), X (some (some (none))), X (some (some (none))) + (1), X (some (some (none))), X (some (none))]

noncomputable def step1 : LinearStep (Option (Option (Option (Fin 0)))) 5 5 where
  sourceE := R1
  sourceU := U1
  targetE := nextE1
  targetU := nextU1
  a := 1
  b := -(X (some (some (none)))) - (1)
  pivot := 4
  pivot_identity := by simp [R1, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1, 0, 0, 1, 1]
  equation_quotient := ![X (some (none)) * X (some (some (some (none)))) - (X (some (some (none)))), 0, 0, X (some (some (none))) - (1), 1]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring
  unit_power := ![0, 0, 1, 0, 0]
  unit_quotient := ![0, 0, 1, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring

noncomputable def E2 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none) * (X (some (some (none)))) ^ 2 + (X (none) * X (some (some (none)))) - (X (some (none))), X (none) * X (some (some (none))) - (X (some (none))) + (1), 0, X (some (none)) * X (some (some (none))) - (X (some (some (none)))) - (1), 0]
noncomputable def U2 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none), X (some (some (none))), X (some (some (none))) + (1), X (some (some (none))), X (some (none))]
noncomputable def R2 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none) * (X (some (some (none)))) ^ 2 + (X (none) * X (some (some (none)))) - (X (some (none))), X (none) * X (some (some (none))) - (X (some (none))) + (1), 0, X (some (none)) * X (some (some (none))) - (X (some (some (none)))) - (1), 0]

noncomputable def reductions2 (j : Fin 5) : FactorReduction U2 (E2 j) (R2 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring

noncomputable def nextE2 : Fin 5 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (none) * (X (some (none))) ^ 2 - ((X (some (none))) ^ 2) - (X (some (none))), 0, 0, X (none) * X (some (none)) - (X (some (none))) - (1), 0]
noncomputable def nextU2 : Fin 5 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (none) - (1), X (some (none)), X (some (none)) + (1), X (some (none)), X (none)]

noncomputable def step2 : LinearStep (Option (Option (Fin 0))) 5 5 where
  sourceE := R2
  sourceU := U2
  targetE := nextE2
  targetU := nextU2
  a := X (some (none))
  b := -(X (none)) + (1)
  pivot := 1
  pivot_identity := by simp [R2, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 1
      selected := ![1]
      quotient := 1
      identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1, 1, 0, 0, 0]
  equation_quotient := ![(X (some (some (none)))) ^ 2 + (X (some (some (none)))), X (some (some (none))), 0, 0, 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring
  unit_power := ![1, 0, 0, 0, 0]
  unit_quotient := ![1, 0, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring

noncomputable def E3 : Fin 5 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (none) * (X (some (none))) ^ 2 - ((X (some (none))) ^ 2) - (X (some (none))), 0, 0, X (none) * X (some (none)) - (X (some (none))) - (1), 0]
noncomputable def U3 : Fin 5 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (none) - (1), X (some (none)), X (some (none)) + (1), X (some (none)), X (none)]
noncomputable def R3 : Fin 5 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (none) * X (some (none)) - (X (some (none))) - (1), 0, 0, X (none) * X (some (none)) - (X (some (none))) - (1), 0]

noncomputable def reductions3 (j : Fin 5) : FactorReduction U3 (E3 j) (R3 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := X (some (none))
      unit_witness := {
        count := 1
        selected := ![1]
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := X (some (none))
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring

noncomputable def nextE3 : Fin 5 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 0, 0]
noncomputable def nextU3 : Fin 5 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![1, X (none), X (none) + (1), X (none), X (none) + (1)]

noncomputable def step3 : LinearStep (Option (Fin 0)) 5 5 where
  sourceE := R3
  sourceU := U3
  targetE := nextE3
  targetU := nextU3
  a := X (none)
  b := -(X (none)) - (1)
  pivot := 0
  pivot_identity := by simp [R3, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 1
      selected := ![1]
      quotient := 1
      identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1, 0, 0, 1, 0]
  equation_quotient := ![X (some (none)), 0, 0, X (some (none)), 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R3, U3, nextE3, nextU3, map_ofNat] <;> ring
  unit_power := ![1, 0, 0, 0, 1]
  unit_quotient := ![1, 0, 0, 0, 1]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R3, U3, nextE3, nextU3, map_ofNat] <;> ring

noncomputable def E4 : Fin 5 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 0, 0]
noncomputable def U4 : Fin 5 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![1, X (none), X (none) + (1), X (none), X (none) + (1)]
noncomputable def R4 : Fin 5 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 0, 0]

noncomputable def reductions4 (j : Fin 5) : FactorReduction U4 (E4 j) (R4 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring

theorem dense4 : RationallyDenseSystem E4 U4 := by
  apply dense_system_of_factor_reductions E4 R4 U4 reductions4
  apply zero_equations_system_dense R4 U4
  intro j; fin_cases j <;> rfl

theorem dense3 : RationallyDenseSystem E3 U3 := by
  apply dense_system_of_factor_reductions E3 R3 U3 reductions3
  exact step3.preserves_density dense4

theorem dense2 : RationallyDenseSystem E2 U2 := by
  apply dense_system_of_factor_reductions E2 R2 U2 reductions2
  exact step2.preserves_density dense3

theorem dense1 : RationallyDenseSystem E1 U1 := by
  apply dense_system_of_factor_reductions E1 R1 U1 reductions1
  exact step1.preserves_density dense2

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  exact step0.preserves_density dense1

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart571
end

/- Source: ChartTables/Case571.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart571
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Option (Option (Option (Fin 0)))))) :=
  ![![.one, .zero, .one, .one], ![.zero, .one, .one, .variable (some (some (none)))], ![.one, .variable (none), .variable (some (none)), .zero], ![.one, .variable (some (some (some (some (none))))), .zero, .variable (some (some (some (none))))]]

noncomputable def chartPositions : (Option (Option (Option (Option (Option (Fin 0)))))) → Coordinate × Coordinate :=
  Option.elim' (2, 1) (Option.elim' (2, 2) (Option.elim' (1, 3) (Option.elim' (3, 3) (Option.elim' (3, 1) ![]))))

noncomputable def chartUnitVariables : Fin 5 → (Option (Option (Option (Option (Option (Fin 0)))))) :=
  ![some (some (none)), none, some (none), some (some (some (some (none)))), some (some (some (none)))]

noncomputable def chartLabelCode : ℕ := 16358160

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, true, true, false, true, true, true, true, false, false, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, false, true, true, false, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, false, false, true, false, false, false, false, true, true, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, true, false, false, true, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 571)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 571) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨34, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (34 : Fin 70)
      rw [minorFormula_at_34]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨62, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (62 : Fin 70)
      rw [minorFormula_at_62]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨9, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (9 : Fin 70)
      rw [minorFormula_at_9]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨53, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (53 : Fin 70)
      rw [minorFormula_at_53]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨65, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (65 : Fin 70)
      rw [minorFormula_at_65]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
  · intro i hi
    fin_cases i
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (3 : Fin 70) = _
      rw [minorFormula_at_3]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (8 : Fin 70) = _
      rw [minorFormula_at_8]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine Or.inr ⟨2, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (9 : Fin 70)
      rw [minorFormula_at_9]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (15 : Fin 70) = _
      rw [minorFormula_at_15]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (34 : Fin 70)
      rw [minorFormula_at_34]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (36 : Fin 70) = _
      rw [minorFormula_at_36]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨3, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (53 : Fin 70)
      rw [minorFormula_at_53]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨1, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (62 : Fin 70)
      rw [minorFormula_at_62]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨4, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (65 : Fin 70)
      rw [minorFormula_at_65]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,6),(0,7),(4,2),(4,3),(6,1),(1,5)]

theorem chart_schedule : Papers.MatrixGaugeNormalization.checkSchedule chartForestRoots chartForestSteps = true := by
  decide +kernel

theorem chart_steps_are_ones : ∀ e ∈ chartForestSteps,
    (∃ i j : Coordinate, e = (firstFour i, lastFour j) ∧ chartEntries i j = .one) ∨
    (∃ i j : Coordinate, e = (lastFour j, firstFour i) ∧ chartEntries i j = .one) := by
  decide +kernel

theorem chart_ones_are_steps : ∀ i j : Coordinate, chartEntries i j = .one →
    (firstFour i, lastFour j) ∈ chartForestSteps ∨
    (lastFour j, firstFour i) ∈ chartForestSteps := by
  decide +kernel

theorem chart_all_nonbases : ∀ i, chartBasisMark i ≠ true → chartRequiredZero i = true := by
  decide +kernel

noncomputable def chart_certificate : ChartCertificate (Option (Option (Option (Option (Option (Fin 0)))))) 5 5
    (MatroidCatalogue.N8R4.family 571) where
  entries := chartEntries
  positions := chartPositions
  unitVariables := chartUnitVariables
  labelCode := chartLabelCode
  basisMark := chartBasisMark
  requiredZero := chartRequiredZero
  polynomials := chartMinorPolynomials
  equations := E0
  units := U0
  roots := chartForestRoots
  steps := chartForestSteps
  parameters := chart_parameters
  minors := chart_minors
  pattern := chart_pattern
  first_basis := chart_first_basis
  constraints := chart_entry_constraints
  equation_table := chart_equations
  units_exact := chart_units_exact
  required_nonbasis := chart_required_nonbasis
  schedule := chart_schedule
  steps_are_ones := chart_steps_are_ones
  ones_are_steps := chart_ones_are_steps

/-- Every real representation of this catalogue entry has rational zero-minor-preserving approximations. -/
theorem family_rationally_dense : MatroidChecked.ChartRealization.FamilyRationallyDense
    (MatroidCatalogue.N8R4.family 571) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart571
end

/- Source: Charts/Case572.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart572
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![-(X (none)) - (X (some (none))) + (X (some (some (none)))), -(X (none)) + (X (some (some (some (none))))), X (some (none)) * X (some (some (some (some (none))))) - (X (some (some (none))) * X (some (some (some (some (none)))))) + (X (some (some (none)))), X (some (some (some (none)))) - (X (some (some (some (some (none)))))) + (1)]
noncomputable def U0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![X (some (none)), X (none), X (some (some (none))), X (some (some (some (none)))), X (some (some (some (some (none)))))]
noncomputable def R0 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![X (none) + (X (some (none))) - (X (some (some (none)))), X (none) - (X (some (some (some (none))))), X (some (none)) * X (some (some (some (some (none))))) - (X (some (some (none))) * X (some (some (some (some (none)))))) + (X (some (some (none)))), X (some (some (some (none)))) - (X (some (some (some (some (none)))))) + (1)]

noncomputable def reductions0 (j : Fin 4) : FactorReduction U0 (E0 j) (R0 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring

noncomputable def nextE0 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![0, -(X (none)) + (X (some (none))) - (X (some (some (none)))), X (none) * X (some (some (some (none)))) - (X (some (none)) * X (some (some (some (none))))) + (X (some (none))), X (some (some (none))) - (X (some (some (some (none))))) + (1)]
noncomputable def nextU0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (none), -(X (none)) + (X (some (none))), X (some (none)), X (some (some (none))), X (some (some (some (none))))]

noncomputable def step0 : LinearStep (Option (Option (Option (Option (Fin 0))))) 4 5 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := 1
  b := X (none) - (X (some (none)))
  pivot := 0
  pivot_identity := by simp [R0, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1, 1, 0, 0]
  equation_quotient := ![1, 1, 0, 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![0, 1, 0, 0, 0]
  unit_quotient := ![0, 1, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![0, -(X (none)) + (X (some (none))) - (X (some (some (none)))), X (none) * X (some (some (some (none)))) - (X (some (none)) * X (some (some (some (none))))) + (X (some (none))), X (some (some (none))) - (X (some (some (some (none))))) + (1)]
noncomputable def U1 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (none), -(X (none)) + (X (some (none))), X (some (none)), X (some (some (none))), X (some (some (some (none))))]
noncomputable def R1 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![0, X (none) - (X (some (none))) + (X (some (some (none)))), X (none) * X (some (some (some (none)))) - (X (some (none)) * X (some (some (some (none))))) + (X (some (none))), X (some (some (none))) - (X (some (some (some (none))))) + (1)]

noncomputable def reductions1 (j : Fin 4) : FactorReduction U1 (E1 j) (R1 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring

noncomputable def nextE1 : Fin 4 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![0, 0, X (none) - (X (some (none)) * X (some (some (none)))), X (some (none)) - (X (some (some (none)))) + (1)]
noncomputable def nextU1 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none) - (X (some (none))), X (some (none)), X (none), X (some (none)), X (some (some (none)))]

noncomputable def step1 : LinearStep (Option (Option (Option (Fin 0)))) 4 5 where
  sourceE := R1
  sourceU := U1
  targetE := nextE1
  targetU := nextU1
  a := 1
  b := -(X (none)) + (X (some (none)))
  pivot := 1
  pivot_identity := by simp [R1, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 1, 1, 0]
  equation_quotient := ![0, 1, X (some (some (some (none)))), 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring
  unit_power := ![1, 1, 0, 0, 0]
  unit_quotient := ![1, -(1), 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring

noncomputable def E2 : Fin 4 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![0, 0, X (none) - (X (some (none)) * X (some (some (none)))), X (some (none)) - (X (some (some (none)))) + (1)]
noncomputable def U2 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none) - (X (some (none))), X (some (none)), X (none), X (some (none)), X (some (some (none)))]
noncomputable def R2 : Fin 4 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![0, 0, X (none) - (X (some (none)) * X (some (some (none)))), X (some (none)) - (X (some (some (none)))) + (1)]

noncomputable def reductions2 (j : Fin 4) : FactorReduction U2 (E2 j) (R2 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring

noncomputable def nextE2 : Fin 4 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, 0, 0, X (none) - (X (some (none))) + (1)]
noncomputable def nextU2 : Fin 5 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (none) * X (some (none)) - (X (none)), X (none), X (none) * X (some (none)), X (none), X (some (none))]

noncomputable def step2 : LinearStep (Option (Option (Fin 0))) 4 5 where
  sourceE := R2
  sourceU := U2
  targetE := nextE2
  targetU := nextU2
  a := 1
  b := -(X (none) * X (some (none)))
  pivot := 2
  pivot_identity := by simp [R2, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 0, 1, 0]
  equation_quotient := ![0, 0, 1, 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring
  unit_power := ![1, 0, 1, 0, 0]
  unit_quotient := ![1, 0, 1, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring

noncomputable def E3 : Fin 4 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, 0, 0, X (none) - (X (some (none))) + (1)]
noncomputable def U3 : Fin 5 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (none) * X (some (none)) - (X (none)), X (none), X (none) * X (some (none)), X (none), X (some (none))]
noncomputable def R3 : Fin 4 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, 0, 0, X (none) - (X (some (none))) + (1)]

noncomputable def reductions3 (j : Fin 4) : FactorReduction U3 (E3 j) (R3 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring

noncomputable def nextE3 : Fin 4 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 0]
noncomputable def nextU3 : Fin 5 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![(X (none)) ^ 2 - (2 * X (none)) + (1), X (none) - (1), (X (none)) ^ 2 - (X (none)), X (none) - (1), X (none)]

noncomputable def step3 : LinearStep (Option (Fin 0)) 4 5 where
  sourceE := R3
  sourceU := U3
  targetE := nextE3
  targetU := nextU3
  a := 1
  b := -(X (none)) + (1)
  pivot := 3
  pivot_identity := by simp [R3, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 0, 0, 1]
  equation_quotient := ![0, 0, 0, 1]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R3, U3, nextE3, nextU3, map_ofNat] <;> ring
  unit_power := ![1, 1, 1, 1, 0]
  unit_quotient := ![X (some (none)) - (1), 1, X (some (none)), 1, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R3, U3, nextE3, nextU3, map_ofNat] <;> ring

noncomputable def E4 : Fin 4 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 0]
noncomputable def U4 : Fin 5 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![(X (none)) ^ 2 - (2 * X (none)) + (1), X (none) - (1), (X (none)) ^ 2 - (X (none)), X (none) - (1), X (none)]
noncomputable def R4 : Fin 4 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 0]

noncomputable def reductions4 (j : Fin 4) : FactorReduction U4 (E4 j) (R4 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring

theorem dense4 : RationallyDenseSystem E4 U4 := by
  apply dense_system_of_factor_reductions E4 R4 U4 reductions4
  apply zero_equations_system_dense R4 U4
  intro j; fin_cases j <;> rfl

theorem dense3 : RationallyDenseSystem E3 U3 := by
  apply dense_system_of_factor_reductions E3 R3 U3 reductions3
  exact step3.preserves_density dense4

theorem dense2 : RationallyDenseSystem E2 U2 := by
  apply dense_system_of_factor_reductions E2 R2 U2 reductions2
  exact step2.preserves_density dense3

theorem dense1 : RationallyDenseSystem E1 U1 := by
  apply dense_system_of_factor_reductions E1 R1 U1 reductions1
  exact step1.preserves_density dense2

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  exact step0.preserves_density dense1

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart572
end

/- Source: ChartTables/Case572.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart572
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Option (Option (Option (Fin 0)))))) :=
  ![![.zero, .one, .one, .one], ![.one, .zero, .one, .variable (some (none))], ![.one, .variable (none), .zero, .variable (some (some (none)))], ![.one, .variable (some (some (some (none)))), .variable (some (some (some (some (none))))), .zero]]

noncomputable def chartPositions : (Option (Option (Option (Option (Option (Fin 0)))))) → Coordinate × Coordinate :=
  Option.elim' (2, 1) (Option.elim' (1, 3) (Option.elim' (2, 3) (Option.elim' (3, 1) (Option.elim' (3, 2) ![]))))

noncomputable def chartUnitVariables : Fin 5 → (Option (Option (Option (Option (Option (Fin 0)))))) :=
  ![some (none), none, some (some (none)), some (some (some (none))), some (some (some (some (none))))]

noncomputable def chartLabelCode : ℕ := 16325400

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, true, true, true, false, true, true, false, true, false, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, false, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, false, false, false, true, false, false, true, false, true, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, true, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 572)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 572) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨66, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (66 : Fin 70)
      rw [minorFormula_at_66]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨9, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (9 : Fin 70)
      rw [minorFormula_at_9]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨33, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (33 : Fin 70)
      rw [minorFormula_at_33]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨61, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70)
      rw [minorFormula_at_61]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
  · intro i hi
    fin_cases i
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (4 : Fin 70) = _
      rw [minorFormula_at_4]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (7 : Fin 70) = _
      rw [minorFormula_at_7]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨1, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (9 : Fin 70)
      rw [minorFormula_at_9]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (16 : Fin 70) = _
      rw [minorFormula_at_16]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨2, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (33 : Fin 70)
      rw [minorFormula_at_33]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (35 : Fin 70) = _
      rw [minorFormula_at_35]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨3, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70)
      rw [minorFormula_at_61]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (66 : Fin 70)
      rw [minorFormula_at_66]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,5),(0,6),(0,7),(6,1),(1,4),(4,2),(4,3)]

theorem chart_schedule : Papers.MatrixGaugeNormalization.checkSchedule chartForestRoots chartForestSteps = true := by
  decide +kernel

theorem chart_steps_are_ones : ∀ e ∈ chartForestSteps,
    (∃ i j : Coordinate, e = (firstFour i, lastFour j) ∧ chartEntries i j = .one) ∨
    (∃ i j : Coordinate, e = (lastFour j, firstFour i) ∧ chartEntries i j = .one) := by
  decide +kernel

theorem chart_ones_are_steps : ∀ i j : Coordinate, chartEntries i j = .one →
    (firstFour i, lastFour j) ∈ chartForestSteps ∨
    (lastFour j, firstFour i) ∈ chartForestSteps := by
  decide +kernel

theorem chart_all_nonbases : ∀ i, chartBasisMark i ≠ true → chartRequiredZero i = true := by
  decide +kernel

noncomputable def chart_certificate : ChartCertificate (Option (Option (Option (Option (Option (Fin 0)))))) 4 5
    (MatroidCatalogue.N8R4.family 572) where
  entries := chartEntries
  positions := chartPositions
  unitVariables := chartUnitVariables
  labelCode := chartLabelCode
  basisMark := chartBasisMark
  requiredZero := chartRequiredZero
  polynomials := chartMinorPolynomials
  equations := E0
  units := U0
  roots := chartForestRoots
  steps := chartForestSteps
  parameters := chart_parameters
  minors := chart_minors
  pattern := chart_pattern
  first_basis := chart_first_basis
  constraints := chart_entry_constraints
  equation_table := chart_equations
  units_exact := chart_units_exact
  required_nonbasis := chart_required_nonbasis
  schedule := chart_schedule
  steps_are_ones := chart_steps_are_ones
  ones_are_steps := chart_ones_are_steps

/-- Every real representation of this catalogue entry has rational zero-minor-preserving approximations. -/
theorem family_rationally_dense : MatroidChecked.ChartRealization.FamilyRationallyDense
    (MatroidCatalogue.N8R4.family 572) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart572
end

/- Source: Charts/Case573.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart573
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![-(X (none) * X (some (some (some (none))))) - (X (some (none))) + (X (some (some (some (none)))) * X (some (some (some (some (none)))))), -(X (none)) + (X (some (some (none)))), X (none) + (X (some (some (none))) * X (some (some (some (some (none)))))) - (X (some (some (some (some (none)))))), X (some (none)) - (1)]
noncomputable def U0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![X (some (some (some (none)))), X (none), X (some (some (none))), X (some (some (some (some (none))))), X (some (none))]
noncomputable def R0 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![X (none) * X (some (some (some (none)))) + (X (some (none))) - (X (some (some (some (none)))) * X (some (some (some (some (none)))))), X (none) - (X (some (some (none)))), X (none) + (X (some (some (none))) * X (some (some (some (some (none)))))) - (X (some (some (some (some (none)))))), X (some (none)) - (1)]

noncomputable def reductions0 (j : Fin 4) : FactorReduction U0 (E0 j) (R0 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring

noncomputable def nextE0 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (none) + (X (some (none)) * X (some (some (none)))) - (X (some (some (none))) * X (some (some (some (none))))), 0, X (some (none)) * X (some (some (some (none)))) + (X (some (none))) - (X (some (some (some (none))))), X (none) - (1)]
noncomputable def nextU0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (some (some (none))), X (some (none)), X (some (none)), X (some (some (some (none)))), X (none)]

noncomputable def step0 : LinearStep (Option (Option (Option (Option (Fin 0))))) 4 5 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := 1
  b := -(X (some (none)))
  pivot := 1
  pivot_identity := by simp [R0, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1, 1, 1, 0]
  equation_quotient := ![X (some (some (some (none)))), 1, 1, 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![0, 1, 0, 0, 0]
  unit_quotient := ![0, 1, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (none) + (X (some (none)) * X (some (some (none)))) - (X (some (some (none))) * X (some (some (some (none))))), 0, X (some (none)) * X (some (some (some (none)))) + (X (some (none))) - (X (some (some (some (none))))), X (none) - (1)]
noncomputable def U1 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (some (some (none))), X (some (none)), X (some (none)), X (some (some (some (none)))), X (none)]
noncomputable def R1 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (none) + (X (some (none)) * X (some (some (none)))) - (X (some (some (none))) * X (some (some (some (none))))), 0, X (some (none)) * X (some (some (some (none)))) + (X (some (none))) - (X (some (some (some (none))))), X (none) - (1)]

noncomputable def reductions1 (j : Fin 4) : FactorReduction U1 (E1 j) (R1 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring

noncomputable def nextE1 : Fin 4 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![0, 0, X (none) * X (some (some (none))) + (X (none)) - (X (some (some (none)))), -(X (none) * X (some (none))) + (X (some (none)) * X (some (some (none)))) - (1)]
noncomputable def nextU1 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (some (none)), X (none), X (none), X (some (some (none))), -(X (none) * X (some (none))) + (X (some (none)) * X (some (some (none))))]

noncomputable def step1 : LinearStep (Option (Option (Option (Fin 0)))) 4 5 where
  sourceE := R1
  sourceU := U1
  targetE := nextE1
  targetU := nextU1
  a := 1
  b := X (none) * X (some (none)) - (X (some (none)) * X (some (some (none))))
  pivot := 0
  pivot_identity := by simp [R1, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1, 0, 0, 1]
  equation_quotient := ![1, 0, 0, 1]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring
  unit_power := ![0, 0, 0, 0, 1]
  unit_quotient := ![0, 0, 0, 0, 1]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring

noncomputable def E2 : Fin 4 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![0, 0, X (none) * X (some (some (none))) + (X (none)) - (X (some (some (none)))), -(X (none) * X (some (none))) + (X (some (none)) * X (some (some (none)))) - (1)]
noncomputable def U2 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (some (none)), X (none), X (none), X (some (some (none))), -(X (none) * X (some (none))) + (X (some (none)) * X (some (some (none))))]
noncomputable def R2 : Fin 4 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![0, 0, X (none) * X (some (some (none))) + (X (none)) - (X (some (some (none)))), X (none) * X (some (none)) - (X (some (none)) * X (some (some (none)))) + (1)]

noncomputable def reductions2 (j : Fin 4) : FactorReduction U2 (E2 j) (R2 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring

noncomputable def nextE2 : Fin 4 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, 0, 0, -(X (none) * (X (some (none))) ^ 2) + (X (some (none))) + (1)]
noncomputable def nextU2 : Fin 5 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (none), X (some (none)), X (some (none)), X (some (none)), X (none) * (X (some (none))) ^ 2]

noncomputable def step2 : LinearStep (Option (Option (Fin 0))) 4 5 where
  sourceE := R2
  sourceU := U2
  targetE := nextE2
  targetU := nextU2
  a := X (some (none)) + (1)
  b := -(X (some (none)))
  pivot := 2
  pivot_identity := by simp [R2, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inr {
      count := 1
      selected := ![3]
      quotient := -(1)
      identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 0, 1, 1]
  equation_quotient := ![0, 0, X (some (some (none))) + (1), X (some (none))]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring
  unit_power := ![0, 1, 1, 0, 1]
  unit_quotient := ![0, 1, 1, 0, -(X (some (none)))]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring

noncomputable def E3 : Fin 4 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, 0, 0, -(X (none) * (X (some (none))) ^ 2) + (X (some (none))) + (1)]
noncomputable def U3 : Fin 5 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (none), X (some (none)), X (some (none)), X (some (none)), X (none) * (X (some (none))) ^ 2]
noncomputable def R3 : Fin 4 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, 0, 0, X (none) * (X (some (none))) ^ 2 - (X (some (none))) - (1)]

noncomputable def reductions3 (j : Fin 4) : FactorReduction U3 (E3 j) (R3 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring

noncomputable def nextE3 : Fin 4 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 0]
noncomputable def nextU3 : Fin 5 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none) + (1), X (none), X (none), X (none), (X (none)) ^ 3 + ((X (none)) ^ 2)]

noncomputable def step3 : LinearStep (Option (Fin 0)) 4 5 where
  sourceE := R3
  sourceU := U3
  targetE := nextE3
  targetU := nextU3
  a := (X (none)) ^ 2
  b := -(X (none)) - (1)
  pivot := 3
  pivot_identity := by simp [R3, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 1
      selected := ![4]
      quotient := X (none)
      identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 0, 0, 1]
  equation_quotient := ![0, 0, 0, (X (some (none))) ^ 2]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R3, U3, nextE3, nextU3, map_ofNat] <;> ring
  unit_power := ![1, 0, 0, 0, 1]
  unit_quotient := ![1, 0, 0, 0, (X (some (none))) ^ 2]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R3, U3, nextE3, nextU3, map_ofNat] <;> ring

noncomputable def E4 : Fin 4 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 0]
noncomputable def U4 : Fin 5 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none) + (1), X (none), X (none), X (none), (X (none)) ^ 3 + ((X (none)) ^ 2)]
noncomputable def R4 : Fin 4 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 0]

noncomputable def reductions4 (j : Fin 4) : FactorReduction U4 (E4 j) (R4 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring

theorem dense4 : RationallyDenseSystem E4 U4 := by
  apply dense_system_of_factor_reductions E4 R4 U4 reductions4
  apply zero_equations_system_dense R4 U4
  intro j; fin_cases j <;> rfl

theorem dense3 : RationallyDenseSystem E3 U3 := by
  apply dense_system_of_factor_reductions E3 R3 U3 reductions3
  exact step3.preserves_density dense4

theorem dense2 : RationallyDenseSystem E2 U2 := by
  apply dense_system_of_factor_reductions E2 R2 U2 reductions2
  exact step2.preserves_density dense3

theorem dense1 : RationallyDenseSystem E1 U1 := by
  apply dense_system_of_factor_reductions E1 R1 U1 reductions1
  exact step1.preserves_density dense2

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  exact step0.preserves_density dense1

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart573
end

/- Source: ChartTables/Case573.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart573
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Option (Option (Option (Fin 0)))))) :=
  ![![.one, .zero, .one, .one], ![.zero, .one, .one, .variable (some (some (some (none))))], ![.one, .variable (none), .variable (some (some (none))), .zero], ![.one, .variable (some (some (some (some (none))))), .zero, .variable (some (none))]]

noncomputable def chartPositions : (Option (Option (Option (Option (Option (Fin 0)))))) → Coordinate × Coordinate :=
  Option.elim' (2, 1) (Option.elim' (3, 3) (Option.elim' (2, 2) (Option.elim' (1, 3) (Option.elim' (3, 1) ![]))))

noncomputable def chartUnitVariables : Fin 5 → (Option (Option (Option (Option (Option (Fin 0)))))) :=
  ![some (some (some (none))), none, some (some (none)), some (some (some (some (none)))), some (none)]

noncomputable def chartLabelCode : ℕ := 16434824

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, true, true, false, true, true, true, true, false, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true, false, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, false, false, true, false, false, false, false, true, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, false, true, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 573)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 573) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨32, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (32 : Fin 70)
      rw [minorFormula_at_32]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨28, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (28 : Fin 70)
      rw [minorFormula_at_28]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨51, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (51 : Fin 70)
      rw [minorFormula_at_51]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨41, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (41 : Fin 70)
      rw [minorFormula_at_41]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
  · intro i hi
    fin_cases i
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (3 : Fin 70) = _
      rw [minorFormula_at_3]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (8 : Fin 70) = _
      rw [minorFormula_at_8]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (15 : Fin 70) = _
      rw [minorFormula_at_15]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨1, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (28 : Fin 70)
      rw [minorFormula_at_28]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (32 : Fin 70)
      rw [minorFormula_at_32]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (36 : Fin 70) = _
      rw [minorFormula_at_36]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨3, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (41 : Fin 70)
      rw [minorFormula_at_41]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨2, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (51 : Fin 70)
      rw [minorFormula_at_51]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,6),(0,7),(4,2),(4,3),(6,1),(1,5)]

theorem chart_schedule : Papers.MatrixGaugeNormalization.checkSchedule chartForestRoots chartForestSteps = true := by
  decide +kernel

theorem chart_steps_are_ones : ∀ e ∈ chartForestSteps,
    (∃ i j : Coordinate, e = (firstFour i, lastFour j) ∧ chartEntries i j = .one) ∨
    (∃ i j : Coordinate, e = (lastFour j, firstFour i) ∧ chartEntries i j = .one) := by
  decide +kernel

theorem chart_ones_are_steps : ∀ i j : Coordinate, chartEntries i j = .one →
    (firstFour i, lastFour j) ∈ chartForestSteps ∨
    (lastFour j, firstFour i) ∈ chartForestSteps := by
  decide +kernel

theorem chart_all_nonbases : ∀ i, chartBasisMark i ≠ true → chartRequiredZero i = true := by
  decide +kernel

noncomputable def chart_certificate : ChartCertificate (Option (Option (Option (Option (Option (Fin 0)))))) 4 5
    (MatroidCatalogue.N8R4.family 573) where
  entries := chartEntries
  positions := chartPositions
  unitVariables := chartUnitVariables
  labelCode := chartLabelCode
  basisMark := chartBasisMark
  requiredZero := chartRequiredZero
  polynomials := chartMinorPolynomials
  equations := E0
  units := U0
  roots := chartForestRoots
  steps := chartForestSteps
  parameters := chart_parameters
  minors := chart_minors
  pattern := chart_pattern
  first_basis := chart_first_basis
  constraints := chart_entry_constraints
  equation_table := chart_equations
  units_exact := chart_units_exact
  required_nonbasis := chart_required_nonbasis
  schedule := chart_schedule
  steps_are_ones := chart_steps_are_ones
  ones_are_steps := chart_ones_are_steps

/-- Every real representation of this catalogue entry has rational zero-minor-preserving approximations. -/
theorem family_rationally_dense : MatroidChecked.ChartRealization.FamilyRationallyDense
    (MatroidCatalogue.N8R4.family 573) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart573
end

/- Source: Charts/Case574.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart574
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![-(X (some (none)) * X (some (some (some (none))))) - (X (some (some (none)))) + (X (some (some (some (none))))), -(X (none) * X (some (none))) + (X (some (some (some (some (none)))))), X (none) + (X (some (some (some (none)))) * X (some (some (some (some (none)))))) - (X (some (some (some (none))))), X (some (none)) + (X (some (some (some (some (none)))))) - (1)]
noncomputable def U0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![X (some (some (none))), X (none), X (some (some (some (none)))), X (some (none)), X (some (some (some (some (none)))))]
noncomputable def R0 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![X (some (none)) * X (some (some (some (none)))) + (X (some (some (none)))) - (X (some (some (some (none))))), X (none) * X (some (none)) - (X (some (some (some (some (none)))))), X (none) + (X (some (some (some (none)))) * X (some (some (some (some (none)))))) - (X (some (some (some (none))))), X (some (none)) + (X (some (some (some (some (none)))))) - (1)]

noncomputable def reductions0 (j : Fin 4) : FactorReduction U0 (E0 j) (R0 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring

noncomputable def nextE0 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (none) * X (some (some (none))) + (X (some (none))) - (X (some (some (none)))), -(X (none) * X (some (some (none))) * X (some (some (some (none))))) + (X (none) * X (some (some (none)))) - (X (some (some (some (none))))), 0, X (none) + (X (some (some (some (none))))) - (1)]
noncomputable def nextU0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (some (none)), -(X (some (some (none))) * X (some (some (some (none))))) + (X (some (some (none)))), X (some (some (none))), X (none), X (some (some (some (none))))]

noncomputable def step0 : LinearStep (Option (Option (Option (Option (Fin 0))))) 4 5 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := 1
  b := X (some (some (none))) * X (some (some (some (none)))) - (X (some (some (none))))
  pivot := 2
  pivot_identity := by simp [R0, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 1, 1, 0]
  equation_quotient := ![0, X (some (none)), 1, 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![0, 1, 0, 0, 0]
  unit_quotient := ![0, 1, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (none) * X (some (some (none))) + (X (some (none))) - (X (some (some (none)))), -(X (none) * X (some (some (none))) * X (some (some (some (none))))) + (X (none) * X (some (some (none)))) - (X (some (some (some (none))))), 0, X (none) + (X (some (some (some (none))))) - (1)]
noncomputable def U1 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (some (none)), -(X (some (some (none))) * X (some (some (some (none))))) + (X (some (some (none)))), X (some (some (none))), X (none), X (some (some (some (none))))]
noncomputable def R1 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (none) * X (some (some (none))) + (X (some (none))) - (X (some (some (none)))), X (none) * X (some (some (none))) * X (some (some (some (none)))) - (X (none) * X (some (some (none)))) + (X (some (some (some (none))))), 0, X (none) + (X (some (some (some (none))))) - (1)]

noncomputable def reductions1 (j : Fin 4) : FactorReduction U1 (E1 j) (R1 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring

noncomputable def nextE1 : Fin 4 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none) - (X (some (none)) * X (some (some (none)))), -(X (some (none)) * (X (some (some (none)))) ^ 2) + (2 * X (some (none)) * X (some (some (none)))) - (X (some (none))) + (X (some (some (none)))), 0, 0]
noncomputable def nextU1 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none), -(X (some (none)) * X (some (some (none)))) + (X (some (none))), X (some (none)), -(X (some (some (none)))) + (1), X (some (some (none)))]

noncomputable def step1 : LinearStep (Option (Option (Option (Fin 0)))) 4 5 where
  sourceE := R1
  sourceU := U1
  targetE := nextE1
  targetU := nextU1
  a := 1
  b := X (some (some (none))) - (1)
  pivot := 3
  pivot_identity := by simp [R1, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1, 1, 0, 1]
  equation_quotient := ![X (some (some (none))), X (some (some (none))) * X (some (some (some (none)))) - (X (some (some (none)))), 0, 1]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring
  unit_power := ![0, 0, 0, 1, 0]
  unit_quotient := ![0, 0, 0, 1, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring

noncomputable def E2 : Fin 4 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none) - (X (some (none)) * X (some (some (none)))), -(X (some (none)) * (X (some (some (none)))) ^ 2) + (2 * X (some (none)) * X (some (some (none)))) - (X (some (none))) + (X (some (some (none)))), 0, 0]
noncomputable def U2 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none), -(X (some (none)) * X (some (some (none)))) + (X (some (none))), X (some (none)), -(X (some (some (none)))) + (1), X (some (some (none)))]
noncomputable def R2 : Fin 4 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none) - (X (some (none)) * X (some (some (none)))), X (some (none)) * (X (some (some (none)))) ^ 2 - (2 * X (some (none)) * X (some (some (none)))) + (X (some (none))) - (X (some (some (none)))), 0, 0]

noncomputable def reductions2 (j : Fin 4) : FactorReduction U2 (E2 j) (R2 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring

noncomputable def nextE2 : Fin 4 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, X (none) * (X (some (none))) ^ 2 - (2 * X (none) * X (some (none))) + (X (none)) - (X (some (none))), 0, 0]
noncomputable def nextU2 : Fin 5 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (none) * X (some (none)), -(X (none) * X (some (none))) + (X (none)), X (none), -(X (some (none))) + (1), X (some (none))]

noncomputable def step2 : LinearStep (Option (Option (Fin 0))) 4 5 where
  sourceE := R2
  sourceU := U2
  targetE := nextE2
  targetU := nextU2
  a := 1
  b := -(X (none) * X (some (none)))
  pivot := 0
  pivot_identity := by simp [R2, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1, 0, 0, 0]
  equation_quotient := ![1, 0, 0, 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring
  unit_power := ![1, 0, 0, 0, 0]
  unit_quotient := ![1, 0, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring

noncomputable def E3 : Fin 4 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, X (none) * (X (some (none))) ^ 2 - (2 * X (none) * X (some (none))) + (X (none)) - (X (some (none))), 0, 0]
noncomputable def U3 : Fin 5 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (none) * X (some (none)), -(X (none) * X (some (none))) + (X (none)), X (none), -(X (some (none))) + (1), X (some (none))]
noncomputable def R3 : Fin 4 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, X (none) * (X (some (none))) ^ 2 - (2 * X (none) * X (some (none))) + (X (none)) - (X (some (none))), 0, 0]

noncomputable def reductions3 (j : Fin 4) : FactorReduction U3 (E3 j) (R3 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring

noncomputable def nextE3 : Fin 4 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 0]
noncomputable def nextU3 : Fin 5 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![(X (none)) ^ 2, -((X (none)) ^ 2) + (X (none)), X (none), -(X (none)) + (1), X (none)]

noncomputable def step3 : LinearStep (Option (Fin 0)) 4 5 where
  sourceE := R3
  sourceU := U3
  targetE := nextE3
  targetU := nextU3
  a := (X (none)) ^ 2 - (2 * X (none)) + (1)
  b := -(X (none))
  pivot := 1
  pivot_identity := by simp [R3, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 2
      selected := ![3, 3]
      quotient := 1
      identity := by simp [U3, Fin.prod_univ_succ, map_ofNat]<;> ring }
  equation_power := ![0, 1, 0, 0]
  equation_quotient := ![0, (X (some (none))) ^ 2 - (2 * X (some (none))) + (1), 0, 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R3, U3, nextE3, nextU3, map_ofNat] <;> ring
  unit_power := ![1, 1, 1, 0, 0]
  unit_quotient := ![X (some (none)), -(X (some (none))) + (1), 1, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R3, U3, nextE3, nextU3, map_ofNat] <;> ring

noncomputable def E4 : Fin 4 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 0]
noncomputable def U4 : Fin 5 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![(X (none)) ^ 2, -((X (none)) ^ 2) + (X (none)), X (none), -(X (none)) + (1), X (none)]
noncomputable def R4 : Fin 4 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 0]

noncomputable def reductions4 (j : Fin 4) : FactorReduction U4 (E4 j) (R4 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring

theorem dense4 : RationallyDenseSystem E4 U4 := by
  apply dense_system_of_factor_reductions E4 R4 U4 reductions4
  apply zero_equations_system_dense R4 U4
  intro j; fin_cases j <;> rfl

theorem dense3 : RationallyDenseSystem E3 U3 := by
  apply dense_system_of_factor_reductions E3 R3 U3 reductions3
  exact step3.preserves_density dense4

theorem dense2 : RationallyDenseSystem E2 U2 := by
  apply dense_system_of_factor_reductions E2 R2 U2 reductions2
  exact step2.preserves_density dense3

theorem dense1 : RationallyDenseSystem E1 U1 := by
  apply dense_system_of_factor_reductions E1 R1 U1 reductions1
  exact step1.preserves_density dense2

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  exact step0.preserves_density dense1

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart574
end

/- Source: ChartTables/Case574.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart574
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Option (Option (Option (Fin 0)))))) :=
  ![![.one, .zero, .one, .one], ![.one, .one, .zero, .variable (some (some (none)))], ![.zero, .one, .variable (none), .variable (some (some (some (none))))], ![.one, .variable (some (none)), .variable (some (some (some (some (none))))), .zero]]

noncomputable def chartPositions : (Option (Option (Option (Option (Option (Fin 0)))))) → Coordinate × Coordinate :=
  Option.elim' (2, 2) (Option.elim' (3, 1) (Option.elim' (1, 3) (Option.elim' (2, 3) (Option.elim' (3, 2) ![]))))

noncomputable def chartUnitVariables : Fin 5 → (Option (Option (Option (Option (Option (Fin 0)))))) :=
  ![some (some (none)), none, some (some (some (none))), some (none), some (some (some (some (none))))]

noncomputable def chartLabelCode : ℕ := 14040712

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, true, true, true, false, false, true, true, true, true, true, true, false, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, false, false, false, true, true, false, false, false, false, false, false, true, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 574)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 574) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨32, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (32 : Fin 70)
      rw [minorFormula_at_32]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨12, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (12 : Fin 70)
      rw [minorFormula_at_12]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨53, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (53 : Fin 70)
      rw [minorFormula_at_53]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨61, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70)
      rw [minorFormula_at_61]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
  · intro i hi
    fin_cases i
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (4 : Fin 70) = _
      rw [minorFormula_at_4]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (5 : Fin 70) = _
      rw [minorFormula_at_5]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨1, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (12 : Fin 70)
      rw [minorFormula_at_12]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (17 : Fin 70) = _
      rw [minorFormula_at_17]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (32 : Fin 70)
      rw [minorFormula_at_32]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (36 : Fin 70) = _
      rw [minorFormula_at_36]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨2, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (53 : Fin 70)
      rw [minorFormula_at_53]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨3, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70)
      rw [minorFormula_at_61]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,6),(0,7),(4,1),(4,3),(1,5),(5,2)]

theorem chart_schedule : Papers.MatrixGaugeNormalization.checkSchedule chartForestRoots chartForestSteps = true := by
  decide +kernel

theorem chart_steps_are_ones : ∀ e ∈ chartForestSteps,
    (∃ i j : Coordinate, e = (firstFour i, lastFour j) ∧ chartEntries i j = .one) ∨
    (∃ i j : Coordinate, e = (lastFour j, firstFour i) ∧ chartEntries i j = .one) := by
  decide +kernel

theorem chart_ones_are_steps : ∀ i j : Coordinate, chartEntries i j = .one →
    (firstFour i, lastFour j) ∈ chartForestSteps ∨
    (lastFour j, firstFour i) ∈ chartForestSteps := by
  decide +kernel

theorem chart_all_nonbases : ∀ i, chartBasisMark i ≠ true → chartRequiredZero i = true := by
  decide +kernel

noncomputable def chart_certificate : ChartCertificate (Option (Option (Option (Option (Option (Fin 0)))))) 4 5
    (MatroidCatalogue.N8R4.family 574) where
  entries := chartEntries
  positions := chartPositions
  unitVariables := chartUnitVariables
  labelCode := chartLabelCode
  basisMark := chartBasisMark
  requiredZero := chartRequiredZero
  polynomials := chartMinorPolynomials
  equations := E0
  units := U0
  roots := chartForestRoots
  steps := chartForestSteps
  parameters := chart_parameters
  minors := chart_minors
  pattern := chart_pattern
  first_basis := chart_first_basis
  constraints := chart_entry_constraints
  equation_table := chart_equations
  units_exact := chart_units_exact
  required_nonbasis := chart_required_nonbasis
  schedule := chart_schedule
  steps_are_ones := chart_steps_are_ones
  ones_are_steps := chart_ones_are_steps

/-- Every real representation of this catalogue entry has rational zero-minor-preserving approximations. -/
theorem family_rationally_dense : MatroidChecked.ChartRealization.FamilyRationallyDense
    (MatroidCatalogue.N8R4.family 574) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart574
end

/- Source: Charts/Case575.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart575
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 3 → MvPolynomial (Option (Option (Option (Option (Fin 1))))) ℚ :=
  ![-(X (none)) + (X (some (none))), X (some (some (none))) * X (some (some (some (some (0 : Fin 1))))) - (X (some (some (some (none)))) * X (some (some (some (some (0 : Fin 1)))))) + (X (some (some (some (none))))), X (some (none)) - (X (some (some (some (some (0 : Fin 1)))))) + (1)]
noncomputable def U0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 1))))) ℚ :=
  ![X (some (some (none))), X (none), X (some (some (some (none)))), X (some (none)), X (some (some (some (some (0 : Fin 1)))))]
noncomputable def R0 : Fin 3 → MvPolynomial (Option (Option (Option (Option (Fin 1))))) ℚ :=
  ![X (none) - (X (some (none))), X (some (some (none))) * X (some (some (some (some (0 : Fin 1))))) - (X (some (some (some (none)))) * X (some (some (some (some (0 : Fin 1)))))) + (X (some (some (some (none))))), X (some (none)) - (X (some (some (some (some (0 : Fin 1)))))) + (1)]

noncomputable def reductions0 (j : Fin 3) : FactorReduction U0 (E0 j) (R0 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring

noncomputable def nextE0 : Fin 3 → MvPolynomial (Option (Option (Option (Fin 1)))) ℚ :=
  ![0, X (some (none)) * X (some (some (some (0 : Fin 1)))) - (X (some (some (none))) * X (some (some (some (0 : Fin 1))))) + (X (some (some (none)))), X (none) - (X (some (some (some (0 : Fin 1))))) + (1)]
noncomputable def nextU0 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 1)))) ℚ :=
  ![X (some (none)), X (none), X (some (some (none))), X (none), X (some (some (some (0 : Fin 1))))]

noncomputable def step0 : LinearStep (Option (Option (Option (Fin 1)))) 3 5 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := 1
  b := -(X (none))
  pivot := 0
  pivot_identity := by simp [R0, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1, 0, 0]
  equation_quotient := ![1, 0, 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![0, 1, 0, 0, 0]
  unit_quotient := ![0, 1, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 3 → MvPolynomial (Option (Option (Option (Fin 1)))) ℚ :=
  ![0, X (some (none)) * X (some (some (some (0 : Fin 1)))) - (X (some (some (none))) * X (some (some (some (0 : Fin 1))))) + (X (some (some (none)))), X (none) - (X (some (some (some (0 : Fin 1))))) + (1)]
noncomputable def U1 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 1)))) ℚ :=
  ![X (some (none)), X (none), X (some (some (none))), X (none), X (some (some (some (0 : Fin 1))))]
noncomputable def R1 : Fin 3 → MvPolynomial (Option (Option (Option (Fin 1)))) ℚ :=
  ![0, X (some (none)) * X (some (some (some (0 : Fin 1)))) - (X (some (some (none))) * X (some (some (some (0 : Fin 1))))) + (X (some (some (none)))), X (none) - (X (some (some (some (0 : Fin 1))))) + (1)]

noncomputable def reductions1 (j : Fin 3) : FactorReduction U1 (E1 j) (R1 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring

noncomputable def nextE1 : Fin 3 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![0, X (none) * X (some (some (0 : Fin 1))) - (X (some (none)) * X (some (some (0 : Fin 1)))) + (X (some (none))), 0]
noncomputable def nextU1 : Fin 5 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![X (none), X (some (some (0 : Fin 1))) - (1), X (some (none)), X (some (some (0 : Fin 1))) - (1), X (some (some (0 : Fin 1)))]

noncomputable def step1 : LinearStep (Option (Option (Fin 1))) 3 5 where
  sourceE := R1
  sourceU := U1
  targetE := nextE1
  targetU := nextU1
  a := 1
  b := -(X (some (some (0 : Fin 1)))) + (1)
  pivot := 2
  pivot_identity := by simp [R1, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 0, 1]
  equation_quotient := ![0, 0, 1]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring
  unit_power := ![0, 1, 0, 1, 0]
  unit_quotient := ![0, 1, 0, 1, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring

noncomputable def E2 : Fin 3 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![0, X (none) * X (some (some (0 : Fin 1))) - (X (some (none)) * X (some (some (0 : Fin 1)))) + (X (some (none))), 0]
noncomputable def U2 : Fin 5 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![X (none), X (some (some (0 : Fin 1))) - (1), X (some (none)), X (some (some (0 : Fin 1))) - (1), X (some (some (0 : Fin 1)))]
noncomputable def R2 : Fin 3 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![0, X (none) * X (some (some (0 : Fin 1))) - (X (some (none)) * X (some (some (0 : Fin 1)))) + (X (some (none))), 0]

noncomputable def reductions2 (j : Fin 3) : FactorReduction U2 (E2 j) (R2 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring

noncomputable def nextE2 : Fin 3 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![0, 0, 0]
noncomputable def nextU2 : Fin 5 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![X (none) * X (some (0 : Fin 1)) - (X (none)), X (some (0 : Fin 1)) - (1), X (none), X (some (0 : Fin 1)) - (1), X (some (0 : Fin 1))]

noncomputable def step2 : LinearStep (Option (Fin 1)) 3 5 where
  sourceE := R2
  sourceU := U2
  targetE := nextE2
  targetU := nextU2
  a := X (some (0 : Fin 1))
  b := -(X (none) * X (some (0 : Fin 1))) + (X (none))
  pivot := 1
  pivot_identity := by simp [R2, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 1
      selected := ![4]
      quotient := 1
      identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 1, 0]
  equation_quotient := ![0, X (some (some (0 : Fin 1))), 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring
  unit_power := ![1, 0, 0, 0, 0]
  unit_quotient := ![1, 0, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring

noncomputable def E3 : Fin 3 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![0, 0, 0]
noncomputable def U3 : Fin 5 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![X (none) * X (some (0 : Fin 1)) - (X (none)), X (some (0 : Fin 1)) - (1), X (none), X (some (0 : Fin 1)) - (1), X (some (0 : Fin 1))]
noncomputable def R3 : Fin 3 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![0, 0, 0]

noncomputable def reductions3 (j : Fin 3) : FactorReduction U3 (E3 j) (R3 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring

theorem dense3 : RationallyDenseSystem E3 U3 := by
  apply dense_system_of_factor_reductions E3 R3 U3 reductions3
  apply zero_equations_system_dense R3 U3
  intro j; fin_cases j <;> rfl

theorem dense2 : RationallyDenseSystem E2 U2 := by
  apply dense_system_of_factor_reductions E2 R2 U2 reductions2
  exact step2.preserves_density dense3

theorem dense1 : RationallyDenseSystem E1 U1 := by
  apply dense_system_of_factor_reductions E1 R1 U1 reductions1
  exact step1.preserves_density dense2

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  exact step0.preserves_density dense1

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart575
end

/- Source: ChartTables/Case575.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart575
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Option (Option (Fin 1))))) :=
  ![![.zero, .one, .one, .one], ![.one, .zero, .one, .variable (some (some (none)))], ![.one, .variable (none), .zero, .variable (some (some (some (none))))], ![.one, .variable (some (none)), .variable (some (some (some (some (0 : Fin 1))))), .zero]]

noncomputable def chartPositions : (Option (Option (Option (Option (Fin 1))))) → Coordinate × Coordinate :=
  Option.elim' (2, 1) (Option.elim' (3, 1) (Option.elim' (1, 3) (Option.elim' (2, 3) ![(3, 2)])))

noncomputable def chartUnitVariables : Fin 5 → (Option (Option (Option (Option (Fin 1))))) :=
  ![some (some (none)), none, some (some (some (none))), some (none), some (some (some (some (0 : Fin 1))))]

noncomputable def chartLabelCode : ℕ := 16394952

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, true, true, true, false, true, true, false, true, false, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, false, false, false, true, false, false, true, false, true, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Option (Option (Fin 1))))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 575)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 575) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨9, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (9 : Fin 70)
      rw [minorFormula_at_9]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨33, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (33 : Fin 70)
      rw [minorFormula_at_33]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨61, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70)
      rw [minorFormula_at_61]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
  · intro i hi
    fin_cases i
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (4 : Fin 70) = _
      rw [minorFormula_at_4]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (7 : Fin 70) = _
      rw [minorFormula_at_7]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (9 : Fin 70)
      rw [minorFormula_at_9]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (16 : Fin 70) = _
      rw [minorFormula_at_16]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨1, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (33 : Fin 70)
      rw [minorFormula_at_33]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (35 : Fin 70) = _
      rw [minorFormula_at_35]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨2, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70)
      rw [minorFormula_at_61]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,5),(0,6),(0,7),(6,1),(1,4),(4,2),(4,3)]

theorem chart_schedule : Papers.MatrixGaugeNormalization.checkSchedule chartForestRoots chartForestSteps = true := by
  decide +kernel

theorem chart_steps_are_ones : ∀ e ∈ chartForestSteps,
    (∃ i j : Coordinate, e = (firstFour i, lastFour j) ∧ chartEntries i j = .one) ∨
    (∃ i j : Coordinate, e = (lastFour j, firstFour i) ∧ chartEntries i j = .one) := by
  decide +kernel

theorem chart_ones_are_steps : ∀ i j : Coordinate, chartEntries i j = .one →
    (firstFour i, lastFour j) ∈ chartForestSteps ∨
    (lastFour j, firstFour i) ∈ chartForestSteps := by
  decide +kernel

theorem chart_all_nonbases : ∀ i, chartBasisMark i ≠ true → chartRequiredZero i = true := by
  decide +kernel

noncomputable def chart_certificate : ChartCertificate (Option (Option (Option (Option (Fin 1))))) 3 5
    (MatroidCatalogue.N8R4.family 575) where
  entries := chartEntries
  positions := chartPositions
  unitVariables := chartUnitVariables
  labelCode := chartLabelCode
  basisMark := chartBasisMark
  requiredZero := chartRequiredZero
  polynomials := chartMinorPolynomials
  equations := E0
  units := U0
  roots := chartForestRoots
  steps := chartForestSteps
  parameters := chart_parameters
  minors := chart_minors
  pattern := chart_pattern
  first_basis := chart_first_basis
  constraints := chart_entry_constraints
  equation_table := chart_equations
  units_exact := chart_units_exact
  required_nonbasis := chart_required_nonbasis
  schedule := chart_schedule
  steps_are_ones := chart_steps_are_ones
  ones_are_steps := chart_ones_are_steps

/-- Every real representation of this catalogue entry has rational zero-minor-preserving approximations. -/
theorem family_rationally_dense : MatroidChecked.ChartRealization.FamilyRationallyDense
    (MatroidCatalogue.N8R4.family 575) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart575
end

/- Source: Charts/Case576.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart576
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Option (Option (Fin 0))))))) ℚ :=
  ![-(X (none)) + (X (some (some (some (some (some (none))))))), -(X (some (none))) + (X (some (some (some (some (none)))))), -(X (none) * X (some (none)) * X (some (some (none)))) + (X (none) * X (some (some (some (none)))) * X (some (some (some (some (none)))))) + (X (some (some (none))) * X (some (some (some (some (some (none))))))), X (some (none)) + (X (some (some (some (none))))) - (1), X (some (some (none))) - (1)]
noncomputable def U0 : Fin 6 → MvPolynomial (Option (Option (Option (Option (Option (Option (Fin 0))))))) ℚ :=
  ![X (none), X (some (some (some (none)))), X (some (none)), X (some (some (some (some (some (none)))))), X (some (some (none))), X (some (some (some (some (none)))))]
noncomputable def R0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Option (Option (Fin 0))))))) ℚ :=
  ![X (none) - (X (some (some (some (some (some (none))))))), X (some (none)) - (X (some (some (some (some (none)))))), -(X (none) * X (some (none)) * X (some (some (none)))) + (X (none) * X (some (some (some (none)))) * X (some (some (some (some (none)))))) + (X (some (some (none))) * X (some (some (some (some (some (none))))))), X (some (none)) + (X (some (some (some (none))))) - (1), X (some (some (none))) - (1)]

noncomputable def reductions0 (j : Fin 5) : FactorReduction U0 (E0 j) (R0 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring

noncomputable def nextE0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![0, X (none) - (X (some (some (some (none))))), -(X (none) * X (some (none)) * X (some (some (some (some (none)))))) + (X (some (none)) * X (some (some (some (some (none)))))) + (X (some (some (none))) * X (some (some (some (none)))) * X (some (some (some (some (none)))))), X (none) + (X (some (some (none)))) - (1), X (some (none)) - (1)]
noncomputable def nextU0 : Fin 6 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![X (some (some (some (some (none))))), X (some (some (none))), X (none), X (some (some (some (some (none))))), X (some (none)), X (some (some (some (none))))]

noncomputable def step0 : LinearStep (Option (Option (Option (Option (Option (Fin 0)))))) 5 6 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := 1
  b := -(X (some (some (some (some (none))))))
  pivot := 0
  pivot_identity := by simp [R0, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1, 0, 1, 0, 0]
  equation_quotient := ![1, 0, -(X (some (none)) * X (some (some (none)))) + (X (some (some (some (none)))) * X (some (some (some (some (none)))))), 0, 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![1, 0, 0, 0, 0, 0]
  unit_quotient := ![1, 0, 0, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![0, X (none) - (X (some (some (some (none))))), -(X (none) * X (some (none)) * X (some (some (some (some (none)))))) + (X (some (none)) * X (some (some (some (some (none)))))) + (X (some (some (none))) * X (some (some (some (none)))) * X (some (some (some (some (none)))))), X (none) + (X (some (some (none)))) - (1), X (some (none)) - (1)]
noncomputable def U1 : Fin 6 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![X (some (some (some (some (none))))), X (some (some (none))), X (none), X (some (some (some (some (none))))), X (some (none)), X (some (some (some (none))))]
noncomputable def R1 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![0, X (none) - (X (some (some (some (none))))), -(X (none) * X (some (none))) + (X (some (none))) + (X (some (some (none))) * X (some (some (some (none))))), X (none) + (X (some (some (none)))) - (1), X (some (none)) - (1)]

noncomputable def reductions1 (j : Fin 5) : FactorReduction U1 (E1 j) (R1 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := X (some (some (some (some (none)))))
      unit_witness := {
        count := 1
        selected := ![0]
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := X (some (some (some (some (none)))))
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring

noncomputable def nextE1 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![0, 0, -(X (none) * X (some (some (none)))) + (X (none)) + (X (some (none)) * X (some (some (none)))), X (some (none)) + (X (some (some (none)))) - (1), X (none) - (1)]
noncomputable def nextU1 : Fin 6 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (some (some (some (none)))), X (some (none)), X (some (some (none))), X (some (some (some (none)))), X (none), X (some (some (none)))]

noncomputable def step1 : LinearStep (Option (Option (Option (Option (Fin 0))))) 5 6 where
  sourceE := R1
  sourceU := U1
  targetE := nextE1
  targetU := nextU1
  a := 1
  b := -(X (some (some (none))))
  pivot := 1
  pivot_identity := by simp [R1, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 1, 1, 1, 0]
  equation_quotient := ![0, 1, -(X (some (none))), 1, 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring
  unit_power := ![0, 0, 1, 0, 0, 0]
  unit_quotient := ![0, 0, 1, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring

noncomputable def E2 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![0, 0, -(X (none) * X (some (some (none)))) + (X (none)) + (X (some (none)) * X (some (some (none)))), X (some (none)) + (X (some (some (none)))) - (1), X (none) - (1)]
noncomputable def U2 : Fin 6 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (some (some (some (none)))), X (some (none)), X (some (some (none))), X (some (some (some (none)))), X (none), X (some (some (none)))]
noncomputable def R2 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![0, 0, -(X (none) * X (some (some (none)))) + (X (none)) + (X (some (none)) * X (some (some (none)))), X (some (none)) + (X (some (some (none)))) - (1), X (none) - (1)]

noncomputable def reductions2 (j : Fin 5) : FactorReduction U2 (E2 j) (R2 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring

noncomputable def nextE2 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![0, 0, X (none) * X (some (none)) - (X (some (none))) + (1), X (none) + (X (some (none))) - (1), 0]
noncomputable def nextU2 : Fin 6 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (some (some (none))), X (none), X (some (none)), X (some (some (none))), 1, X (some (none))]

noncomputable def step2 : LinearStep (Option (Option (Option (Fin 0)))) 5 6 where
  sourceE := R2
  sourceU := U2
  targetE := nextE2
  targetU := nextU2
  a := 1
  b := -(1)
  pivot := 4
  pivot_identity := by simp [R2, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 0, 1, 0, 1]
  equation_quotient := ![0, 0, -(X (some (some (none)))) + (1), 0, 1]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring
  unit_power := ![0, 0, 0, 0, 1, 0]
  unit_quotient := ![0, 0, 0, 0, 1, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring

noncomputable def E3 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![0, 0, X (none) * X (some (none)) - (X (some (none))) + (1), X (none) + (X (some (none))) - (1), 0]
noncomputable def U3 : Fin 6 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (some (some (none))), X (none), X (some (none)), X (some (some (none))), 1, X (some (none))]
noncomputable def R3 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![0, 0, X (none) * X (some (none)) - (X (some (none))) + (1), X (none) + (X (some (none))) - (1), 0]

noncomputable def reductions3 (j : Fin 5) : FactorReduction U3 (E3 j) (R3 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring

noncomputable def nextE3 : Fin 5 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, 0, -((X (none)) ^ 2) + (1), 0, 0]
noncomputable def nextU3 : Fin 6 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (some (none)), -(X (none)) + (1), X (none), X (some (none)), 1, X (none)]

noncomputable def step3 : LinearStep (Option (Option (Fin 0))) 5 6 where
  sourceE := R3
  sourceU := U3
  targetE := nextE3
  targetU := nextU3
  a := 1
  b := X (none) - (1)
  pivot := 3
  pivot_identity := by simp [R3, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 0, 1, 1, 0]
  equation_quotient := ![0, 0, X (some (none)), 1, 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R3, U3, nextE3, nextU3, map_ofNat] <;> ring
  unit_power := ![0, 1, 0, 0, 0, 0]
  unit_quotient := ![0, 1, 0, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R3, U3, nextE3, nextU3, map_ofNat] <;> ring

noncomputable def E4 : Fin 5 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, 0, -((X (none)) ^ 2) + (1), 0, 0]
noncomputable def U4 : Fin 6 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (some (none)), -(X (none)) + (1), X (none), X (some (none)), 1, X (none)]
noncomputable def R4 : Fin 5 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, 0, X (none) + (1), 0, 0]

noncomputable def reductions4 (j : Fin 5) : FactorReduction U4 (E4 j) (R4 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(X (none)) + (1)
      unit_witness := {
        count := 1
        selected := ![1]
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(X (none)) + (1)
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring

noncomputable def nextE4 : Fin 5 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 0, 0]
noncomputable def nextU4 : Fin 6 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none), 2, -(1), X (none), 1, -(1)]

noncomputable def step4 : LinearStep (Option (Fin 0)) 5 6 where
  sourceE := R4
  sourceU := U4
  targetE := nextE4
  targetU := nextU4
  a := 1
  b := 1
  pivot := 2
  pivot_identity := by simp [R4, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 0, 1, 0, 0]
  equation_quotient := ![0, 0, 1, 0, 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R4, U4, nextE4, nextU4, map_ofNat] <;> ring
  unit_power := ![0, 1, 1, 0, 0, 1]
  unit_quotient := ![0, -(1), 1, 0, 0, 1]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R4, U4, nextE4, nextU4, map_ofNat] <;> ring

noncomputable def E5 : Fin 5 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 0, 0]
noncomputable def U5 : Fin 6 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none), 2, -(1), X (none), 1, -(1)]
noncomputable def R5 : Fin 5 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 0, 0]

noncomputable def reductions5 (j : Fin 5) : FactorReduction U5 (E5 j) (R5 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U5, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E5, R5]<;> ring
    · simp [E5, R5]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U5, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E5, R5]<;> ring
    · simp [E5, R5]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U5, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E5, R5]<;> ring
    · simp [E5, R5]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U5, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E5, R5]<;> ring
    · simp [E5, R5]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U5, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E5, R5]<;> ring
    · simp [E5, R5]<;> ring

theorem dense5 : RationallyDenseSystem E5 U5 := by
  apply dense_system_of_factor_reductions E5 R5 U5 reductions5
  apply zero_equations_system_dense R5 U5
  intro j; fin_cases j <;> rfl

theorem dense4 : RationallyDenseSystem E4 U4 := by
  apply dense_system_of_factor_reductions E4 R4 U4 reductions4
  exact step4.preserves_density dense5

theorem dense3 : RationallyDenseSystem E3 U3 := by
  apply dense_system_of_factor_reductions E3 R3 U3 reductions3
  exact step3.preserves_density dense4

theorem dense2 : RationallyDenseSystem E2 U2 := by
  apply dense_system_of_factor_reductions E2 R2 U2 reductions2
  exact step2.preserves_density dense3

theorem dense1 : RationallyDenseSystem E1 U1 := by
  apply dense_system_of_factor_reductions E1 R1 U1 reductions1
  exact step1.preserves_density dense2

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  exact step0.preserves_density dense1

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart576
end

/- Source: ChartTables/Case576.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart576
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Option (Option (Option (Option (Fin 0))))))) :=
  ![![.one, .one, .zero, .one], ![.one, .zero, .one, .variable (none)], ![.one, .variable (some (some (some (none)))), .variable (some (none)), .variable (some (some (some (some (some (none))))))], ![.one, .variable (some (some (none))), .variable (some (some (some (some (none))))), .zero]]

noncomputable def chartPositions : (Option (Option (Option (Option (Option (Option (Fin 0))))))) → Coordinate × Coordinate :=
  Option.elim' (1, 3) (Option.elim' (2, 2) (Option.elim' (3, 1) (Option.elim' (2, 1) (Option.elim' (3, 2) (Option.elim' (2, 3) ![])))))

noncomputable def chartUnitVariables : Fin 6 → (Option (Option (Option (Option (Option (Option (Fin 0))))))) :=
  ![none, some (some (some (none))), some (none), some (some (some (some (some (none))))), some (some (none)), some (some (some (some (none))))]

noncomputable def chartLabelCode : ℕ := 16434824

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, false, true, true, false, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, false, false, false, true, false, false, false, false, false, true, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, true, false, false, true, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Option (Option (Option (Option (Fin 0))))))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 576)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 576) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨27, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (27 : Fin 70)
      rw [minorFormula_at_27]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨10, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (10 : Fin 70)
      rw [minorFormula_at_10]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨34, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (34 : Fin 70)
      rw [minorFormula_at_34]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨65, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (65 : Fin 70)
      rw [minorFormula_at_65]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨39, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (39 : Fin 70)
      rw [minorFormula_at_39]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
  · intro i hi
    fin_cases i
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (4 : Fin 70) = _
      rw [minorFormula_at_4]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨1, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (10 : Fin 70)
      rw [minorFormula_at_10]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (16 : Fin 70) = _
      rw [minorFormula_at_16]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (27 : Fin 70)
      rw [minorFormula_at_27]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨2, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (34 : Fin 70)
      rw [minorFormula_at_34]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (37 : Fin 70) = _
      rw [minorFormula_at_37]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨4, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (39 : Fin 70)
      rw [minorFormula_at_39]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨3, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (65 : Fin 70)
      rw [minorFormula_at_65]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,7),(4,1),(4,2),(4,3),(1,6)]

theorem chart_schedule : Papers.MatrixGaugeNormalization.checkSchedule chartForestRoots chartForestSteps = true := by
  decide +kernel

theorem chart_steps_are_ones : ∀ e ∈ chartForestSteps,
    (∃ i j : Coordinate, e = (firstFour i, lastFour j) ∧ chartEntries i j = .one) ∨
    (∃ i j : Coordinate, e = (lastFour j, firstFour i) ∧ chartEntries i j = .one) := by
  decide +kernel

theorem chart_ones_are_steps : ∀ i j : Coordinate, chartEntries i j = .one →
    (firstFour i, lastFour j) ∈ chartForestSteps ∨
    (lastFour j, firstFour i) ∈ chartForestSteps := by
  decide +kernel

theorem chart_all_nonbases : ∀ i, chartBasisMark i ≠ true → chartRequiredZero i = true := by
  decide +kernel

noncomputable def chart_certificate : ChartCertificate (Option (Option (Option (Option (Option (Option (Fin 0))))))) 5 6
    (MatroidCatalogue.N8R4.family 576) where
  entries := chartEntries
  positions := chartPositions
  unitVariables := chartUnitVariables
  labelCode := chartLabelCode
  basisMark := chartBasisMark
  requiredZero := chartRequiredZero
  polynomials := chartMinorPolynomials
  equations := E0
  units := U0
  roots := chartForestRoots
  steps := chartForestSteps
  parameters := chart_parameters
  minors := chart_minors
  pattern := chart_pattern
  first_basis := chart_first_basis
  constraints := chart_entry_constraints
  equation_table := chart_equations
  units_exact := chart_units_exact
  required_nonbasis := chart_required_nonbasis
  schedule := chart_schedule
  steps_are_ones := chart_steps_are_ones
  ones_are_steps := chart_ones_are_steps

/-- Every real representation of this catalogue entry has rational zero-minor-preserving approximations. -/
theorem family_rationally_dense : MatroidChecked.ChartRealization.FamilyRationallyDense
    (MatroidCatalogue.N8R4.family 576) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart576
end
