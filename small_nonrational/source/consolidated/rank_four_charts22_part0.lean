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

/- Source: Charts/Case705.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart705
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 3 → MvPolynomial (Option (Option (Option (Option (Fin 2))))) ℚ :=
  ![X (none) - (1), -(X (some (none)) * X (some (some (some (some (0 : Fin 2)))))) + (X (some (some (none))) * X (some (some (some (some (1 : Fin 2)))))), X (some (none)) - (1)]
noncomputable def U0 : Fin 6 → MvPolynomial (Option (Option (Option (Option (Fin 2))))) ℚ :=
  ![X (none), X (some (some (some (none)))), X (some (some (none))), X (some (some (some (some (0 : Fin 2))))), X (some (none)), X (some (some (some (some (1 : Fin 2)))))]
noncomputable def R0 : Fin 3 → MvPolynomial (Option (Option (Option (Option (Fin 2))))) ℚ :=
  ![X (none) - (1), -(X (some (none)) * X (some (some (some (some (0 : Fin 2)))))) + (X (some (some (none))) * X (some (some (some (some (1 : Fin 2)))))), X (some (none)) - (1)]

noncomputable def reductions0 (j : Fin 3) : FactorReduction U0 (E0 j) (R0 j) := by
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
        identity := by simp [U0, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U0, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U0, Fin.prod_univ_succ, map_ofNat]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring

noncomputable def nextE0 : Fin 3 → MvPolynomial (Option (Option (Option (Fin 2)))) ℚ :=
  ![0, -(X (none) * X (some (some (some (0 : Fin 2))))) + (X (some (none)) * X (some (some (some (1 : Fin 2))))), X (none) - (1)]
noncomputable def nextU0 : Fin 6 → MvPolynomial (Option (Option (Option (Fin 2)))) ℚ :=
  ![1, X (some (some (none))), X (some (none)), X (some (some (some (0 : Fin 2)))), X (none), X (some (some (some (1 : Fin 2))))]

noncomputable def step0 : LinearStep (Option (Option (Option (Fin 2)))) 3 6 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := 1
  b := -(1)
  pivot := 0
  pivot_identity := by simp [R0, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U0, Fin.prod_univ_succ, map_ofNat]<;> ring }
  equation_power := ![1, 0, 0]
  equation_quotient := ![1, 0, 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![1, 0, 0, 0, 0, 0]
  unit_quotient := ![1, 0, 0, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 3 → MvPolynomial (Option (Option (Option (Fin 2)))) ℚ :=
  ![0, -(X (none) * X (some (some (some (0 : Fin 2))))) + (X (some (none)) * X (some (some (some (1 : Fin 2))))), X (none) - (1)]
noncomputable def U1 : Fin 6 → MvPolynomial (Option (Option (Option (Fin 2)))) ℚ :=
  ![1, X (some (some (none))), X (some (none)), X (some (some (some (0 : Fin 2)))), X (none), X (some (some (some (1 : Fin 2))))]
noncomputable def R1 : Fin 3 → MvPolynomial (Option (Option (Option (Fin 2)))) ℚ :=
  ![0, -(X (none) * X (some (some (some (0 : Fin 2))))) + (X (some (none)) * X (some (some (some (1 : Fin 2))))), X (none) - (1)]

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
        identity := by simp [U1, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U1, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U1, Fin.prod_univ_succ, map_ofNat]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring

noncomputable def nextE1 : Fin 3 → MvPolynomial (Option (Option (Fin 2))) ℚ :=
  ![0, X (none) * X (some (some (1 : Fin 2))) - (X (some (some (0 : Fin 2)))), 0]
noncomputable def nextU1 : Fin 6 → MvPolynomial (Option (Option (Fin 2))) ℚ :=
  ![1, X (some (none)), X (none), X (some (some (0 : Fin 2))), 1, X (some (some (1 : Fin 2)))]

noncomputable def step1 : LinearStep (Option (Option (Fin 2))) 3 6 where
  sourceE := R1
  sourceU := U1
  targetE := nextE1
  targetU := nextU1
  a := 1
  b := -(1)
  pivot := 2
  pivot_identity := by simp [R1, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U1, Fin.prod_univ_succ, map_ofNat]<;> ring }
  equation_power := ![0, 1, 1]
  equation_quotient := ![0, -(X (some (some (some (0 : Fin 2))))), 1]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring
  unit_power := ![0, 0, 0, 0, 1, 0]
  unit_quotient := ![0, 0, 0, 0, 1, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring

noncomputable def E2 : Fin 3 → MvPolynomial (Option (Option (Fin 2))) ℚ :=
  ![0, X (none) * X (some (some (1 : Fin 2))) - (X (some (some (0 : Fin 2)))), 0]
noncomputable def U2 : Fin 6 → MvPolynomial (Option (Option (Fin 2))) ℚ :=
  ![1, X (some (none)), X (none), X (some (some (0 : Fin 2))), 1, X (some (some (1 : Fin 2)))]
noncomputable def R2 : Fin 3 → MvPolynomial (Option (Option (Fin 2))) ℚ :=
  ![0, X (none) * X (some (some (1 : Fin 2))) - (X (some (some (0 : Fin 2)))), 0]

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
        identity := by simp [U2, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U2, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U2, Fin.prod_univ_succ, map_ofNat]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring

noncomputable def nextE2 : Fin 3 → MvPolynomial (Option (Fin 2)) ℚ :=
  ![0, 0, 0]
noncomputable def nextU2 : Fin 6 → MvPolynomial (Option (Fin 2)) ℚ :=
  ![1, X (none), X (some (0 : Fin 2)), X (some (0 : Fin 2)), 1, X (some (1 : Fin 2))]

noncomputable def step2 : LinearStep (Option (Fin 2)) 3 6 where
  sourceE := R2
  sourceU := U2
  targetE := nextE2
  targetU := nextU2
  a := X (some (1 : Fin 2))
  b := -(X (some (0 : Fin 2)))
  pivot := 1
  pivot_identity := by simp [R2, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 1
      selected := ![5]
      quotient := 1
      identity := by simp [U2, Fin.prod_univ_succ, map_ofNat]<;> ring }
  equation_power := ![0, 1, 0]
  equation_quotient := ![0, X (some (some (1 : Fin 2))), 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring
  unit_power := ![0, 0, 1, 0, 0, 0]
  unit_quotient := ![0, 0, 1, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring

noncomputable def E3 : Fin 3 → MvPolynomial (Option (Fin 2)) ℚ :=
  ![0, 0, 0]
noncomputable def U3 : Fin 6 → MvPolynomial (Option (Fin 2)) ℚ :=
  ![1, X (none), X (some (0 : Fin 2)), X (some (0 : Fin 2)), 1, X (some (1 : Fin 2))]
noncomputable def R3 : Fin 3 → MvPolynomial (Option (Fin 2)) ℚ :=
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
        identity := by simp [U3, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U3, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U3, Fin.prod_univ_succ, map_ofNat]<;> ring }
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

end Papers.RationalityTen.Chart705
end

/- Source: ChartTables/Case705.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart705
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Option (Option (Fin 2))))) :=
  ![![.one, .one, .one, .one], ![.one, .variable (none), .variable (some (some (some (none)))), .zero], ![.zero, .one, .variable (some (some (none))), .variable (some (some (some (some (0 : Fin 2)))))], ![.one, .zero, .variable (some (none)), .variable (some (some (some (some (1 : Fin 2)))))]]

noncomputable def chartPositions : (Option (Option (Option (Option (Fin 2))))) → Coordinate × Coordinate :=
  Option.elim' (1, 1) (Option.elim' (3, 2) (Option.elim' (2, 2) (Option.elim' (1, 2) ![(2, 3), (3, 3)])))

noncomputable def chartUnitVariables : Fin 6 → (Option (Option (Option (Option (Fin 2))))) :=
  ![none, some (some (some (none))), some (some (none)), some (some (some (some (0 : Fin 2)))), some (none), some (some (some (some (1 : Fin 2))))]

noncomputable def chartLabelCode : ℕ := 16434824

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, true, false, true, true, false, true, true, true, true, true, true, true, true, false, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, false, true, false, false, true, false, false, false, false, false, false, false, false, true, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Option (Option (Fin 2))))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 705)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 705) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨55, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (55 : Fin 70)
      rw [minorFormula_at_55]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
    · refine ⟨14, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (14 : Fin 70)
      rw [minorFormula_at_14]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
    · refine ⟨40, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (40 : Fin 70)
      rw [minorFormula_at_40]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
  · intro i hi
    fin_cases i
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (2 : Fin 70) = _
      rw [minorFormula_at_2]
      dsimp [
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (5 : Fin 70) = _
      rw [minorFormula_at_5]
      dsimp [
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
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
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (14 : Fin 70)
      rw [minorFormula_at_14]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (18 : Fin 70) = _
      rw [minorFormula_at_18]
      dsimp [
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
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
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (40 : Fin 70)
      rw [minorFormula_at_40]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
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
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (55 : Fin 70)
      rw [minorFormula_at_55]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
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
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(0,7),(4,1),(4,3),(5,2)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Option (Option (Option (Fin 2))))) 3 6
    (MatroidCatalogue.N8R4.family 705) where
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
    (MatroidCatalogue.N8R4.family 705) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart705
end

/- Source: Charts/Case706.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart706
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 3 → MvPolynomial (Option (Option (Option (Option (Fin 2))))) ℚ :=
  ![-(X (none) * X (some (some (some (some (0 : Fin 2)))))) + (X (some (none))) - (X (some (some (none)))), X (none) - (1), X (some (some (none))) * X (some (some (some (some (1 : Fin 2))))) - (X (some (some (some (none)))) * X (some (some (some (some (0 : Fin 2))))))]
noncomputable def U0 : Fin 6 → MvPolynomial (Option (Option (Option (Option (Fin 2))))) ℚ :=
  ![X (none), X (some (none)), X (some (some (none))), X (some (some (some (none)))), X (some (some (some (some (0 : Fin 2))))), X (some (some (some (some (1 : Fin 2)))))]
noncomputable def R0 : Fin 3 → MvPolynomial (Option (Option (Option (Option (Fin 2))))) ℚ :=
  ![X (none) * X (some (some (some (some (0 : Fin 2))))) - (X (some (none))) + (X (some (some (none)))), X (none) - (1), X (some (some (none))) * X (some (some (some (some (1 : Fin 2))))) - (X (some (some (some (none)))) * X (some (some (some (some (0 : Fin 2))))))]

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
        identity := by simp [U0, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U0, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U0, Fin.prod_univ_succ, map_ofNat]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring

noncomputable def nextE0 : Fin 3 → MvPolynomial (Option (Option (Option (Fin 2)))) ℚ :=
  ![-(X (none)) + (X (some (none))) + (X (some (some (some (0 : Fin 2))))), 0, X (some (none)) * X (some (some (some (1 : Fin 2)))) - (X (some (some (none))) * X (some (some (some (0 : Fin 2)))))]
noncomputable def nextU0 : Fin 6 → MvPolynomial (Option (Option (Option (Fin 2)))) ℚ :=
  ![1, X (none), X (some (none)), X (some (some (none))), X (some (some (some (0 : Fin 2)))), X (some (some (some (1 : Fin 2))))]

noncomputable def step0 : LinearStep (Option (Option (Option (Fin 2)))) 3 6 where
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
      identity := by simp [U0, Fin.prod_univ_succ, map_ofNat]<;> ring }
  equation_power := ![1, 1, 0]
  equation_quotient := ![X (some (some (some (some (0 : Fin 2))))), 1, 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![1, 0, 0, 0, 0, 0]
  unit_quotient := ![1, 0, 0, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 3 → MvPolynomial (Option (Option (Option (Fin 2)))) ℚ :=
  ![-(X (none)) + (X (some (none))) + (X (some (some (some (0 : Fin 2))))), 0, X (some (none)) * X (some (some (some (1 : Fin 2)))) - (X (some (some (none))) * X (some (some (some (0 : Fin 2)))))]
noncomputable def U1 : Fin 6 → MvPolynomial (Option (Option (Option (Fin 2)))) ℚ :=
  ![1, X (none), X (some (none)), X (some (some (none))), X (some (some (some (0 : Fin 2)))), X (some (some (some (1 : Fin 2))))]
noncomputable def R1 : Fin 3 → MvPolynomial (Option (Option (Option (Fin 2)))) ℚ :=
  ![X (none) - (X (some (none))) - (X (some (some (some (0 : Fin 2))))), 0, X (some (none)) * X (some (some (some (1 : Fin 2)))) - (X (some (some (none))) * X (some (some (some (0 : Fin 2)))))]

noncomputable def reductions1 (j : Fin 3) : FactorReduction U1 (E1 j) (R1 j) := by
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
        identity := by simp [U1, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U1, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U1, Fin.prod_univ_succ, map_ofNat]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring

noncomputable def nextE1 : Fin 3 → MvPolynomial (Option (Option (Fin 2))) ℚ :=
  ![0, 0, X (none) * X (some (some (1 : Fin 2))) - (X (some (none)) * X (some (some (0 : Fin 2))))]
noncomputable def nextU1 : Fin 6 → MvPolynomial (Option (Option (Fin 2))) ℚ :=
  ![1, X (none) + (X (some (some (0 : Fin 2)))), X (none), X (some (none)), X (some (some (0 : Fin 2))), X (some (some (1 : Fin 2)))]

noncomputable def step1 : LinearStep (Option (Option (Fin 2))) 3 6 where
  sourceE := R1
  sourceU := U1
  targetE := nextE1
  targetU := nextU1
  a := 1
  b := -(X (none)) - (X (some (some (0 : Fin 2))))
  pivot := 0
  pivot_identity := by simp [R1, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U1, Fin.prod_univ_succ, map_ofNat]<;> ring }
  equation_power := ![1, 0, 0]
  equation_quotient := ![1, 0, 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring
  unit_power := ![0, 1, 0, 0, 0, 0]
  unit_quotient := ![0, 1, 0, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring

noncomputable def E2 : Fin 3 → MvPolynomial (Option (Option (Fin 2))) ℚ :=
  ![0, 0, X (none) * X (some (some (1 : Fin 2))) - (X (some (none)) * X (some (some (0 : Fin 2))))]
noncomputable def U2 : Fin 6 → MvPolynomial (Option (Option (Fin 2))) ℚ :=
  ![1, X (none) + (X (some (some (0 : Fin 2)))), X (none), X (some (none)), X (some (some (0 : Fin 2))), X (some (some (1 : Fin 2)))]
noncomputable def R2 : Fin 3 → MvPolynomial (Option (Option (Fin 2))) ℚ :=
  ![0, 0, X (none) * X (some (some (1 : Fin 2))) - (X (some (none)) * X (some (some (0 : Fin 2))))]

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
        identity := by simp [U2, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U2, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U2, Fin.prod_univ_succ, map_ofNat]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring

noncomputable def nextE2 : Fin 3 → MvPolynomial (Option (Fin 2)) ℚ :=
  ![0, 0, 0]
noncomputable def nextU2 : Fin 6 → MvPolynomial (Option (Fin 2)) ℚ :=
  ![1, X (none) * X (some (0 : Fin 2)) + (X (some (0 : Fin 2)) * X (some (1 : Fin 2))), X (none) * X (some (0 : Fin 2)), X (none), X (some (0 : Fin 2)), X (some (1 : Fin 2))]

noncomputable def step2 : LinearStep (Option (Fin 2)) 3 6 where
  sourceE := R2
  sourceU := U2
  targetE := nextE2
  targetU := nextU2
  a := X (some (1 : Fin 2))
  b := -(X (none) * X (some (0 : Fin 2)))
  pivot := 2
  pivot_identity := by simp [R2, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 1
      selected := ![5]
      quotient := 1
      identity := by simp [U2, Fin.prod_univ_succ, map_ofNat]<;> ring }
  equation_power := ![0, 0, 1]
  equation_quotient := ![0, 0, X (some (some (1 : Fin 2)))]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring
  unit_power := ![0, 1, 1, 0, 0, 0]
  unit_quotient := ![0, 1, 1, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring

noncomputable def E3 : Fin 3 → MvPolynomial (Option (Fin 2)) ℚ :=
  ![0, 0, 0]
noncomputable def U3 : Fin 6 → MvPolynomial (Option (Fin 2)) ℚ :=
  ![1, X (none) * X (some (0 : Fin 2)) + (X (some (0 : Fin 2)) * X (some (1 : Fin 2))), X (none) * X (some (0 : Fin 2)), X (none), X (some (0 : Fin 2)), X (some (1 : Fin 2))]
noncomputable def R3 : Fin 3 → MvPolynomial (Option (Fin 2)) ℚ :=
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
        identity := by simp [U3, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U3, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U3, Fin.prod_univ_succ, map_ofNat]<;> ring }
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

end Papers.RationalityTen.Chart706
end

/- Source: ChartTables/Case706.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart706
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Option (Option (Fin 2))))) :=
  ![![.one, .one, .one, .one], ![.one, .variable (none), .variable (some (none)), .zero], ![.one, .zero, .variable (some (some (none))), .variable (some (some (some (none))))], ![.zero, .one, .variable (some (some (some (some (0 : Fin 2))))), .variable (some (some (some (some (1 : Fin 2)))))]]

noncomputable def chartPositions : (Option (Option (Option (Option (Fin 2))))) → Coordinate × Coordinate :=
  Option.elim' (1, 1) (Option.elim' (1, 2) (Option.elim' (2, 2) (Option.elim' (2, 3) ![(3, 2), (3, 3)])))

noncomputable def chartUnitVariables : Fin 6 → (Option (Option (Option (Option (Fin 2))))) :=
  ![none, some (none), some (some (none)), some (some (some (none))), some (some (some (some (0 : Fin 2)))), some (some (some (some (1 : Fin 2))))]

noncomputable def chartLabelCode : ℕ := 16431240

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, true, true, true, true, false, true, true, true, true, true, true, true, false, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, false, false, false, false, true, false, false, false, false, false, false, false, true, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Option (Option (Fin 2))))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 706)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 706) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨31, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (31 : Fin 70)
      rw [minorFormula_at_31]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
    · refine ⟨55, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (55 : Fin 70)
      rw [minorFormula_at_55]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
    · refine ⟨14, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (14 : Fin 70)
      rw [minorFormula_at_14]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
  · intro i hi
    fin_cases i
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (1 : Fin 70) = _
      rw [minorFormula_at_1]
      dsimp [
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (6 : Fin 70) = _
      rw [minorFormula_at_6]
      dsimp [
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨2, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (14 : Fin 70)
      rw [minorFormula_at_14]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (18 : Fin 70) = _
      rw [minorFormula_at_18]
      dsimp [
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
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
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (31 : Fin 70)
      rw [minorFormula_at_31]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
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
    · refine Or.inr ⟨1, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (55 : Fin 70)
      rw [minorFormula_at_55]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
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
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(0,7),(4,1),(4,2),(5,3)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Option (Option (Option (Fin 2))))) 3 6
    (MatroidCatalogue.N8R4.family 706) where
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
    (MatroidCatalogue.N8R4.family 706) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart706
end

/- Source: Charts/Case707.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart707
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 2 → MvPolynomial (Option (Option (Option (Fin 3)))) ℚ :=
  ![X (none) - (X (some (some (some (1 : Fin 3))))), X (some (none)) - (1)]
noncomputable def U0 : Fin 6 → MvPolynomial (Option (Option (Option (Fin 3)))) ℚ :=
  ![X (none), X (some (some (none))), X (some (none)), X (some (some (some (0 : Fin 3)))), X (some (some (some (1 : Fin 3)))), X (some (some (some (2 : Fin 3))))]
noncomputable def R0 : Fin 2 → MvPolynomial (Option (Option (Option (Fin 3)))) ℚ :=
  ![X (none) - (X (some (some (some (1 : Fin 3))))), X (some (none)) - (1)]

noncomputable def reductions0 (j : Fin 2) : FactorReduction U0 (E0 j) (R0 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U0, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U0, Fin.prod_univ_succ, map_ofNat]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring

noncomputable def nextE0 : Fin 2 → MvPolynomial (Option (Option (Fin 3))) ℚ :=
  ![0, X (none) - (1)]
noncomputable def nextU0 : Fin 6 → MvPolynomial (Option (Option (Fin 3))) ℚ :=
  ![X (some (some (1 : Fin 3))), X (some (none)), X (none), X (some (some (0 : Fin 3))), X (some (some (1 : Fin 3))), X (some (some (2 : Fin 3)))]

noncomputable def step0 : LinearStep (Option (Option (Fin 3))) 2 6 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := 1
  b := -(X (some (some (1 : Fin 3))))
  pivot := 0
  pivot_identity := by simp [R0, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U0, Fin.prod_univ_succ, map_ofNat]<;> ring }
  equation_power := ![1, 0]
  equation_quotient := ![1, 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![1, 0, 0, 0, 0, 0]
  unit_quotient := ![1, 0, 0, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 2 → MvPolynomial (Option (Option (Fin 3))) ℚ :=
  ![0, X (none) - (1)]
noncomputable def U1 : Fin 6 → MvPolynomial (Option (Option (Fin 3))) ℚ :=
  ![X (some (some (1 : Fin 3))), X (some (none)), X (none), X (some (some (0 : Fin 3))), X (some (some (1 : Fin 3))), X (some (some (2 : Fin 3)))]
noncomputable def R1 : Fin 2 → MvPolynomial (Option (Option (Fin 3))) ℚ :=
  ![0, X (none) - (1)]

noncomputable def reductions1 (j : Fin 2) : FactorReduction U1 (E1 j) (R1 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U1, Fin.prod_univ_succ, map_ofNat]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring

noncomputable def nextE1 : Fin 2 → MvPolynomial (Option (Fin 3)) ℚ :=
  ![0, 0]
noncomputable def nextU1 : Fin 6 → MvPolynomial (Option (Fin 3)) ℚ :=
  ![X (some (1 : Fin 3)), X (none), 1, X (some (0 : Fin 3)), X (some (1 : Fin 3)), X (some (2 : Fin 3))]

noncomputable def step1 : LinearStep (Option (Fin 3)) 2 6 where
  sourceE := R1
  sourceU := U1
  targetE := nextE1
  targetU := nextU1
  a := 1
  b := -(1)
  pivot := 1
  pivot_identity := by simp [R1, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U1, Fin.prod_univ_succ, map_ofNat]<;> ring }
  equation_power := ![0, 1]
  equation_quotient := ![0, 1]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring
  unit_power := ![0, 0, 1, 0, 0, 0]
  unit_quotient := ![0, 0, 1, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring

noncomputable def E2 : Fin 2 → MvPolynomial (Option (Fin 3)) ℚ :=
  ![0, 0]
noncomputable def U2 : Fin 6 → MvPolynomial (Option (Fin 3)) ℚ :=
  ![X (some (1 : Fin 3)), X (none), 1, X (some (0 : Fin 3)), X (some (1 : Fin 3)), X (some (2 : Fin 3))]
noncomputable def R2 : Fin 2 → MvPolynomial (Option (Fin 3)) ℚ :=
  ![0, 0]

noncomputable def reductions2 (j : Fin 2) : FactorReduction U2 (E2 j) (R2 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U2, Fin.prod_univ_succ, map_ofNat]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring

theorem dense2 : RationallyDenseSystem E2 U2 := by
  apply dense_system_of_factor_reductions E2 R2 U2 reductions2
  apply zero_equations_system_dense R2 U2
  intro j; fin_cases j <;> rfl

theorem dense1 : RationallyDenseSystem E1 U1 := by
  apply dense_system_of_factor_reductions E1 R1 U1 reductions1
  exact step1.preserves_density dense2

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  exact step0.preserves_density dense1

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart707
end

/- Source: ChartTables/Case707.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart707
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Option (Fin 3)))) :=
  ![![.zero, .one, .one, .one], ![.one, .one, .variable (none), .variable (some (some (none)))], ![.one, .variable (some (none)), .variable (some (some (some (0 : Fin 3)))), .zero], ![.one, .zero, .variable (some (some (some (1 : Fin 3)))), .variable (some (some (some (2 : Fin 3))))]]

noncomputable def chartPositions : (Option (Option (Option (Fin 3)))) → Coordinate × Coordinate :=
  Option.elim' (1, 2) (Option.elim' (2, 1) (Option.elim' (1, 3) ![(2, 2), (3, 2), (3, 3)]))

noncomputable def chartUnitVariables : Fin 6 → (Option (Option (Option (Fin 3)))) :=
  ![none, some (some (none)), some (none), some (some (some (0 : Fin 3))), some (some (some (1 : Fin 3))), some (some (some (2 : Fin 3)))]

noncomputable def chartLabelCode : ℕ := 16434824

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, true, false, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, false, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, false, true, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, true, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Option (Fin 3)))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 707)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 707) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨20, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (20 : Fin 70)
      rw [minorFormula_at_20]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
    · refine ⟨25, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (25 : Fin 70)
      rw [minorFormula_at_25]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
  · intro i hi
    fin_cases i
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (2 : Fin 70) = _
      rw [minorFormula_at_2]
      dsimp [
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (8 : Fin 70) = _
      rw [minorFormula_at_8]
      dsimp [
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
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
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (20 : Fin 70)
      rw [minorFormula_at_20]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨1, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (25 : Fin 70)
      rw [minorFormula_at_25]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (35 : Fin 70) = _
      rw [minorFormula_at_35]
      dsimp [
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
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
noncomputable def chartForestSteps : List (Point × Point) := [(0,5),(0,6),(0,7),(5,1),(1,4),(4,2),(4,3)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Option (Option (Fin 3)))) 2 6
    (MatroidCatalogue.N8R4.family 707) where
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
    (MatroidCatalogue.N8R4.family 707) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart707
end

/- Source: Charts/Case708.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart708
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 2 → MvPolynomial (Option (Option (Option (Fin 2)))) ℚ :=
  ![X (none) - (1), X (some (none)) * X (some (some (some (1 : Fin 2)))) - (X (some (some (none))) * X (some (some (some (0 : Fin 2)))))]
noncomputable def U0 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 2)))) ℚ :=
  ![X (none), X (some (none)), X (some (some (none))), X (some (some (some (0 : Fin 2)))), X (some (some (some (1 : Fin 2))))]
noncomputable def R0 : Fin 2 → MvPolynomial (Option (Option (Option (Fin 2)))) ℚ :=
  ![X (none) - (1), X (some (none)) * X (some (some (some (1 : Fin 2)))) - (X (some (some (none))) * X (some (some (some (0 : Fin 2)))))]

noncomputable def reductions0 (j : Fin 2) : FactorReduction U0 (E0 j) (R0 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U0, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U0, Fin.prod_univ_succ, map_ofNat]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring

noncomputable def nextE0 : Fin 2 → MvPolynomial (Option (Option (Fin 2))) ℚ :=
  ![0, X (none) * X (some (some (1 : Fin 2))) - (X (some (none)) * X (some (some (0 : Fin 2))))]
noncomputable def nextU0 : Fin 5 → MvPolynomial (Option (Option (Fin 2))) ℚ :=
  ![1, X (none), X (some (none)), X (some (some (0 : Fin 2))), X (some (some (1 : Fin 2)))]

noncomputable def step0 : LinearStep (Option (Option (Fin 2))) 2 5 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := 1
  b := -(1)
  pivot := 0
  pivot_identity := by simp [R0, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U0, Fin.prod_univ_succ, map_ofNat]<;> ring }
  equation_power := ![1, 0]
  equation_quotient := ![1, 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![1, 0, 0, 0, 0]
  unit_quotient := ![1, 0, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 2 → MvPolynomial (Option (Option (Fin 2))) ℚ :=
  ![0, X (none) * X (some (some (1 : Fin 2))) - (X (some (none)) * X (some (some (0 : Fin 2))))]
noncomputable def U1 : Fin 5 → MvPolynomial (Option (Option (Fin 2))) ℚ :=
  ![1, X (none), X (some (none)), X (some (some (0 : Fin 2))), X (some (some (1 : Fin 2)))]
noncomputable def R1 : Fin 2 → MvPolynomial (Option (Option (Fin 2))) ℚ :=
  ![0, X (none) * X (some (some (1 : Fin 2))) - (X (some (none)) * X (some (some (0 : Fin 2))))]

noncomputable def reductions1 (j : Fin 2) : FactorReduction U1 (E1 j) (R1 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U1, Fin.prod_univ_succ, map_ofNat]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring

noncomputable def nextE1 : Fin 2 → MvPolynomial (Option (Fin 2)) ℚ :=
  ![0, 0]
noncomputable def nextU1 : Fin 5 → MvPolynomial (Option (Fin 2)) ℚ :=
  ![1, X (none) * X (some (0 : Fin 2)), X (none), X (some (0 : Fin 2)), X (some (1 : Fin 2))]

noncomputable def step1 : LinearStep (Option (Fin 2)) 2 5 where
  sourceE := R1
  sourceU := U1
  targetE := nextE1
  targetU := nextU1
  a := X (some (1 : Fin 2))
  b := -(X (none) * X (some (0 : Fin 2)))
  pivot := 1
  pivot_identity := by simp [R1, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 1
      selected := ![4]
      quotient := 1
      identity := by simp [U1, Fin.prod_univ_succ, map_ofNat]<;> ring }
  equation_power := ![0, 1]
  equation_quotient := ![0, X (some (some (1 : Fin 2)))]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring
  unit_power := ![0, 1, 0, 0, 0]
  unit_quotient := ![0, 1, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring

noncomputable def E2 : Fin 2 → MvPolynomial (Option (Fin 2)) ℚ :=
  ![0, 0]
noncomputable def U2 : Fin 5 → MvPolynomial (Option (Fin 2)) ℚ :=
  ![1, X (none) * X (some (0 : Fin 2)), X (none), X (some (0 : Fin 2)), X (some (1 : Fin 2))]
noncomputable def R2 : Fin 2 → MvPolynomial (Option (Fin 2)) ℚ :=
  ![0, 0]

noncomputable def reductions2 (j : Fin 2) : FactorReduction U2 (E2 j) (R2 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U2, Fin.prod_univ_succ, map_ofNat]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring

theorem dense2 : RationallyDenseSystem E2 U2 := by
  apply dense_system_of_factor_reductions E2 R2 U2 reductions2
  apply zero_equations_system_dense R2 U2
  intro j; fin_cases j <;> rfl

theorem dense1 : RationallyDenseSystem E1 U1 := by
  apply dense_system_of_factor_reductions E1 R1 U1 reductions1
  exact step1.preserves_density dense2

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  exact step0.preserves_density dense1

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart708
end

/- Source: ChartTables/Case708.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart708
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Option (Fin 2)))) :=
  ![![.one, .one, .zero, .one], ![.one, .variable (none), .one, .zero], ![.one, .zero, .variable (some (none)), .variable (some (some (none)))], ![.zero, .one, .variable (some (some (some (0 : Fin 2)))), .variable (some (some (some (1 : Fin 2))))]]

noncomputable def chartPositions : (Option (Option (Option (Fin 2)))) → Coordinate × Coordinate :=
  Option.elim' (1, 1) (Option.elim' (2, 2) (Option.elim' (2, 3) ![(3, 2), (3, 3)]))

noncomputable def chartUnitVariables : Fin 5 → (Option (Option (Option (Fin 2)))) :=
  ![none, some (none), some (some (none)), some (some (some (0 : Fin 2))), some (some (some (1 : Fin 2)))]

noncomputable def chartLabelCode : ℕ := 16434824

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, true, true, true, true, false, true, true, true, true, true, true, true, false, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, false, false, false, false, true, false, false, false, false, false, false, false, true, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Option (Fin 2)))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 708)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 708) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨55, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (55 : Fin 70)
      rw [minorFormula_at_55]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
    · refine ⟨14, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (14 : Fin 70)
      rw [minorFormula_at_14]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
  · intro i hi
    fin_cases i
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (1 : Fin 70) = _
      rw [minorFormula_at_1]
      dsimp [
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (6 : Fin 70) = _
      rw [minorFormula_at_6]
      dsimp [
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨1, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (14 : Fin 70)
      rw [minorFormula_at_14]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (18 : Fin 70) = _
      rw [minorFormula_at_18]
      dsimp [
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (37 : Fin 70) = _
      rw [minorFormula_at_37]
      dsimp [
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
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
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (55 : Fin 70)
      rw [minorFormula_at_55]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
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
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,7),(4,1),(4,2),(5,3),(1,6)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Option (Option (Fin 2)))) 2 5
    (MatroidCatalogue.N8R4.family 708) where
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
    (MatroidCatalogue.N8R4.family 708) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart708
end

/- Source: Charts/Case709.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart709
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 3 → MvPolynomial (Option (Option (Option (Option (Fin 1))))) ℚ :=
  ![-(X (none)) + (X (some (some (some (none))))), -(X (none) * X (some (some (some (some (0 : Fin 1)))))) - (X (some (none)) * X (some (some (some (none))))), X (some (none)) + (X (some (some (none))) * X (some (some (some (some (0 : Fin 1))))))]
noncomputable def U0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 1))))) ℚ :=
  ![X (some (some (none))), X (none), X (some (none)), X (some (some (some (none)))), X (some (some (some (some (0 : Fin 1)))))]
noncomputable def R0 : Fin 3 → MvPolynomial (Option (Option (Option (Option (Fin 1))))) ℚ :=
  ![X (none) - (X (some (some (some (none))))), X (none) * X (some (some (some (some (0 : Fin 1))))) + (X (some (none)) * X (some (some (some (none))))), X (some (none)) + (X (some (some (none))) * X (some (some (some (some (0 : Fin 1))))))]

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
        identity := by simp [U0, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U0, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U0, Fin.prod_univ_succ, map_ofNat]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring

noncomputable def nextE0 : Fin 3 → MvPolynomial (Option (Option (Option (Fin 1)))) ℚ :=
  ![0, X (none) * X (some (some (none))) + (X (some (some (none))) * X (some (some (some (0 : Fin 1))))), X (none) + (X (some (none)) * X (some (some (some (0 : Fin 1)))))]
noncomputable def nextU0 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 1)))) ℚ :=
  ![X (some (none)), X (some (some (none))), X (none), X (some (some (none))), X (some (some (some (0 : Fin 1))))]

noncomputable def step0 : LinearStep (Option (Option (Option (Fin 1)))) 3 5 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := 1
  b := -(X (some (some (none))))
  pivot := 0
  pivot_identity := by simp [R0, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U0, Fin.prod_univ_succ, map_ofNat]<;> ring }
  equation_power := ![1, 1, 0]
  equation_quotient := ![1, X (some (some (some (some (0 : Fin 1))))), 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![0, 1, 0, 0, 0]
  unit_quotient := ![0, 1, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 3 → MvPolynomial (Option (Option (Option (Fin 1)))) ℚ :=
  ![0, X (none) * X (some (some (none))) + (X (some (some (none))) * X (some (some (some (0 : Fin 1))))), X (none) + (X (some (none)) * X (some (some (some (0 : Fin 1)))))]
noncomputable def U1 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 1)))) ℚ :=
  ![X (some (none)), X (some (some (none))), X (none), X (some (some (none))), X (some (some (some (0 : Fin 1))))]
noncomputable def R1 : Fin 3 → MvPolynomial (Option (Option (Option (Fin 1)))) ℚ :=
  ![0, X (none) + (X (some (some (some (0 : Fin 1))))), X (none) + (X (some (none)) * X (some (some (some (0 : Fin 1)))))]

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
        identity := by simp [U1, Fin.prod_univ_succ, map_ofNat]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := X (some (some (none)))
      unit_witness := {
        count := 1
        selected := ![1]
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ, map_ofNat]<;> ring }
      forward_identity := ?_
      reverse_quotient := X (some (some (none)))
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
        identity := by simp [U1, Fin.prod_univ_succ, map_ofNat]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring

noncomputable def nextE1 : Fin 3 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![0, 0, X (none) * X (some (some (0 : Fin 1))) - (X (some (some (0 : Fin 1))))]
noncomputable def nextU1 : Fin 5 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![X (none), X (some (none)), -(X (some (some (0 : Fin 1)))), X (some (none)), X (some (some (0 : Fin 1)))]

noncomputable def step1 : LinearStep (Option (Option (Fin 1))) 3 5 where
  sourceE := R1
  sourceU := U1
  targetE := nextE1
  targetU := nextU1
  a := 1
  b := X (some (some (0 : Fin 1)))
  pivot := 1
  pivot_identity := by simp [R1, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U1, Fin.prod_univ_succ, map_ofNat]<;> ring }
  equation_power := ![0, 1, 1]
  equation_quotient := ![0, 1, 1]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring
  unit_power := ![0, 0, 1, 0, 0]
  unit_quotient := ![0, 0, 1, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring

noncomputable def E2 : Fin 3 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![0, 0, X (none) * X (some (some (0 : Fin 1))) - (X (some (some (0 : Fin 1))))]
noncomputable def U2 : Fin 5 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![X (none), X (some (none)), -(X (some (some (0 : Fin 1)))), X (some (none)), X (some (some (0 : Fin 1)))]
noncomputable def R2 : Fin 3 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![0, 0, X (none) - (1)]

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
        identity := by simp [U2, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U2, Fin.prod_univ_succ, map_ofNat]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := X (some (some (0 : Fin 1)))
      unit_witness := {
        count := 1
        selected := ![2]
        quotient := -(1)
        identity := by simp [U2, Fin.prod_univ_succ, map_ofNat]<;> ring }
      forward_identity := ?_
      reverse_quotient := X (some (some (0 : Fin 1)))
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring

noncomputable def nextE2 : Fin 3 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![0, 0, 0]
noncomputable def nextU2 : Fin 5 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![1, X (none), -(X (some (0 : Fin 1))), X (none), X (some (0 : Fin 1))]

noncomputable def step2 : LinearStep (Option (Fin 1)) 3 5 where
  sourceE := R2
  sourceU := U2
  targetE := nextE2
  targetU := nextU2
  a := 1
  b := -(1)
  pivot := 2
  pivot_identity := by simp [R2, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U2, Fin.prod_univ_succ, map_ofNat]<;> ring }
  equation_power := ![0, 0, 1]
  equation_quotient := ![0, 0, 1]
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
  ![1, X (none), -(X (some (0 : Fin 1))), X (none), X (some (0 : Fin 1))]
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
        identity := by simp [U3, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U3, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U3, Fin.prod_univ_succ, map_ofNat]<;> ring }
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

end Papers.RationalityTen.Chart709
end

/- Source: ChartTables/Case709.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart709
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Option (Option (Fin 1))))) :=
  ![![.one, .zero, .one, .one], ![.zero, .one, .one, .variable (some (some (none)))], ![.one, .variable (none), .zero, .variable (some (none))], ![.one, .variable (some (some (some (none)))), .variable (some (some (some (some (0 : Fin 1))))), .zero]]

noncomputable def chartPositions : (Option (Option (Option (Option (Fin 1))))) → Coordinate × Coordinate :=
  Option.elim' (2, 1) (Option.elim' (2, 3) (Option.elim' (1, 3) (Option.elim' (3, 1) ![(3, 2)])))

noncomputable def chartUnitVariables : Fin 5 → (Option (Option (Option (Option (Fin 1))))) :=
  ![some (some (none)), none, some (none), some (some (some (none))), some (some (some (some (0 : Fin 1))))]

noncomputable def chartLabelCode : ℕ := 16362248

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, true, true, true, false, true, true, false, true, false, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, false, false, false, true, false, false, true, false, true, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Option (Option (Fin 1))))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 709)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 709) chartLabelCode chartEntries
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
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
    · refine ⟨54, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (54 : Fin 70)
      rw [minorFormula_at_54]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
    · refine ⟨33, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (33 : Fin 70)
      rw [minorFormula_at_33]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
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
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (7 : Fin 70) = _
      rw [minorFormula_at_7]
      dsimp [
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (9 : Fin 70)
      rw [minorFormula_at_9]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
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
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
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
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (33 : Fin 70)
      rw [minorFormula_at_33]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (36 : Fin 70) = _
      rw [minorFormula_at_36]
      dsimp [
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
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
    · refine Or.inr ⟨1, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (54 : Fin 70)
      rw [minorFormula_at_54]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
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

noncomputable def chart_certificate : ChartCertificate (Option (Option (Option (Option (Fin 1))))) 3 5
    (MatroidCatalogue.N8R4.family 709) where
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
    (MatroidCatalogue.N8R4.family 709) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart709
end

/- Source: Charts/Case710.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart710
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 2 → MvPolynomial (Option (Option (Option (Fin 2)))) ℚ :=
  ![-(X (none)) + (X (some (some (some (0 : Fin 2))))), X (some (none)) * X (some (some (some (1 : Fin 2)))) + (X (some (some (none))))]
noncomputable def U0 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 2)))) ℚ :=
  ![X (some (none)), X (none), X (some (some (none))), X (some (some (some (0 : Fin 2)))), X (some (some (some (1 : Fin 2))))]
noncomputable def R0 : Fin 2 → MvPolynomial (Option (Option (Option (Fin 2)))) ℚ :=
  ![X (none) - (X (some (some (some (0 : Fin 2))))), X (some (none)) * X (some (some (some (1 : Fin 2)))) + (X (some (some (none))))]

noncomputable def reductions0 (j : Fin 2) : FactorReduction U0 (E0 j) (R0 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U0, Fin.prod_univ_succ, map_ofNat]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring

noncomputable def nextE0 : Fin 2 → MvPolynomial (Option (Option (Fin 2))) ℚ :=
  ![0, X (none) * X (some (some (1 : Fin 2))) + (X (some (none)))]
noncomputable def nextU0 : Fin 5 → MvPolynomial (Option (Option (Fin 2))) ℚ :=
  ![X (none), X (some (some (0 : Fin 2))), X (some (none)), X (some (some (0 : Fin 2))), X (some (some (1 : Fin 2)))]

noncomputable def step0 : LinearStep (Option (Option (Fin 2))) 2 5 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := 1
  b := -(X (some (some (0 : Fin 2))))
  pivot := 0
  pivot_identity := by simp [R0, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U0, Fin.prod_univ_succ, map_ofNat]<;> ring }
  equation_power := ![1, 0]
  equation_quotient := ![1, 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![0, 1, 0, 0, 0]
  unit_quotient := ![0, 1, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 2 → MvPolynomial (Option (Option (Fin 2))) ℚ :=
  ![0, X (none) * X (some (some (1 : Fin 2))) + (X (some (none)))]
noncomputable def U1 : Fin 5 → MvPolynomial (Option (Option (Fin 2))) ℚ :=
  ![X (none), X (some (some (0 : Fin 2))), X (some (none)), X (some (some (0 : Fin 2))), X (some (some (1 : Fin 2)))]
noncomputable def R1 : Fin 2 → MvPolynomial (Option (Option (Fin 2))) ℚ :=
  ![0, X (none) * X (some (some (1 : Fin 2))) + (X (some (none)))]

noncomputable def reductions1 (j : Fin 2) : FactorReduction U1 (E1 j) (R1 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U1, Fin.prod_univ_succ, map_ofNat]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring

noncomputable def nextE1 : Fin 2 → MvPolynomial (Option (Fin 2)) ℚ :=
  ![0, 0]
noncomputable def nextU1 : Fin 5 → MvPolynomial (Option (Fin 2)) ℚ :=
  ![-(X (none)), X (some (0 : Fin 2)), X (none), X (some (0 : Fin 2)), X (some (1 : Fin 2))]

noncomputable def step1 : LinearStep (Option (Fin 2)) 2 5 where
  sourceE := R1
  sourceU := U1
  targetE := nextE1
  targetU := nextU1
  a := X (some (1 : Fin 2))
  b := X (none)
  pivot := 1
  pivot_identity := by simp [R1, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 1
      selected := ![4]
      quotient := 1
      identity := by simp [U1, Fin.prod_univ_succ, map_ofNat]<;> ring }
  equation_power := ![0, 1]
  equation_quotient := ![0, X (some (some (1 : Fin 2)))]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring
  unit_power := ![1, 0, 0, 0, 0]
  unit_quotient := ![1, 0, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring

noncomputable def E2 : Fin 2 → MvPolynomial (Option (Fin 2)) ℚ :=
  ![0, 0]
noncomputable def U2 : Fin 5 → MvPolynomial (Option (Fin 2)) ℚ :=
  ![-(X (none)), X (some (0 : Fin 2)), X (none), X (some (0 : Fin 2)), X (some (1 : Fin 2))]
noncomputable def R2 : Fin 2 → MvPolynomial (Option (Fin 2)) ℚ :=
  ![0, 0]

noncomputable def reductions2 (j : Fin 2) : FactorReduction U2 (E2 j) (R2 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U2, Fin.prod_univ_succ, map_ofNat]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring

theorem dense2 : RationallyDenseSystem E2 U2 := by
  apply dense_system_of_factor_reductions E2 R2 U2 reductions2
  apply zero_equations_system_dense R2 U2
  intro j; fin_cases j <;> rfl

theorem dense1 : RationallyDenseSystem E1 U1 := by
  apply dense_system_of_factor_reductions E1 R1 U1 reductions1
  exact step1.preserves_density dense2

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  exact step0.preserves_density dense1

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart710
end

/- Source: ChartTables/Case710.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart710
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Option (Fin 2)))) :=
  ![![.one, .zero, .one, .one], ![.zero, .one, .one, .variable (some (none))], ![.one, .variable (none), .zero, .variable (some (some (none)))], ![.one, .variable (some (some (some (0 : Fin 2)))), .variable (some (some (some (1 : Fin 2)))), .zero]]

noncomputable def chartPositions : (Option (Option (Option (Fin 2)))) → Coordinate × Coordinate :=
  Option.elim' (2, 1) (Option.elim' (1, 3) (Option.elim' (2, 3) ![(3, 1), (3, 2)]))

noncomputable def chartUnitVariables : Fin 5 → (Option (Option (Option (Fin 2)))) :=
  ![some (none), none, some (some (none)), some (some (some (0 : Fin 2))), some (some (some (1 : Fin 2)))]

noncomputable def chartLabelCode : ℕ := 16427208

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, true, true, true, false, true, true, false, true, false, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, false, false, false, true, false, false, true, false, true, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Option (Fin 2)))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 710)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 710) chartLabelCode chartEntries
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
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
    · refine ⟨33, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (33 : Fin 70)
      rw [minorFormula_at_33]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
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
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (7 : Fin 70) = _
      rw [minorFormula_at_7]
      dsimp [
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (9 : Fin 70)
      rw [minorFormula_at_9]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
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
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
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
    · refine Or.inr ⟨1, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (33 : Fin 70)
      rw [minorFormula_at_33]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (36 : Fin 70) = _
      rw [minorFormula_at_36]
      dsimp [
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
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

noncomputable def chart_certificate : ChartCertificate (Option (Option (Option (Fin 2)))) 2 5
    (MatroidCatalogue.N8R4.family 710) where
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
    (MatroidCatalogue.N8R4.family 710) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart710
end

/- Source: Charts/Case711.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart711
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 1 → MvPolynomial (Option (Option (Fin 3))) ℚ :=
  ![-(X (none)) + (X (some (some (1 : Fin 3))))]
noncomputable def U0 : Fin 5 → MvPolynomial (Option (Option (Fin 3))) ℚ :=
  ![X (some (none)), X (none), X (some (some (0 : Fin 3))), X (some (some (1 : Fin 3))), X (some (some (2 : Fin 3)))]
noncomputable def R0 : Fin 1 → MvPolynomial (Option (Option (Fin 3))) ℚ :=
  ![X (none) - (X (some (some (1 : Fin 3))))]

noncomputable def reductions0 (j : Fin 1) : FactorReduction U0 (E0 j) (R0 j) := by
  refine Fin.cases ?_ (fun j => Fin.elim0 j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ, map_ofNat]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring

noncomputable def nextE0 : Fin 1 → MvPolynomial (Option (Fin 3)) ℚ :=
  ![0]
noncomputable def nextU0 : Fin 5 → MvPolynomial (Option (Fin 3)) ℚ :=
  ![X (none), X (some (1 : Fin 3)), X (some (0 : Fin 3)), X (some (1 : Fin 3)), X (some (2 : Fin 3))]

noncomputable def step0 : LinearStep (Option (Fin 3)) 1 5 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := 1
  b := -(X (some (1 : Fin 3)))
  pivot := 0
  pivot_identity := by simp [R0, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U0, Fin.prod_univ_succ, map_ofNat]<;> ring }
  equation_power := ![1]
  equation_quotient := ![1]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![0, 1, 0, 0, 0]
  unit_quotient := ![0, 1, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 1 → MvPolynomial (Option (Fin 3)) ℚ :=
  ![0]
noncomputable def U1 : Fin 5 → MvPolynomial (Option (Fin 3)) ℚ :=
  ![X (none), X (some (1 : Fin 3)), X (some (0 : Fin 3)), X (some (1 : Fin 3)), X (some (2 : Fin 3))]
noncomputable def R1 : Fin 1 → MvPolynomial (Option (Fin 3)) ℚ :=
  ![0]

noncomputable def reductions1 (j : Fin 1) : FactorReduction U1 (E1 j) (R1 j) := by
  refine Fin.cases ?_ (fun j => Fin.elim0 j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ, map_ofNat]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring

theorem dense1 : RationallyDenseSystem E1 U1 := by
  apply dense_system_of_factor_reductions E1 R1 U1 reductions1
  apply zero_equations_system_dense R1 U1
  intro j; fin_cases j <;> rfl

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  exact step0.preserves_density dense1

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart711
end

/- Source: ChartTables/Case711.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart711
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Fin 3))) :=
  ![![.one, .zero, .one, .one], ![.zero, .one, .one, .variable (some (none))], ![.one, .variable (none), .zero, .variable (some (some (0 : Fin 3)))], ![.one, .variable (some (some (1 : Fin 3))), .variable (some (some (2 : Fin 3))), .zero]]

noncomputable def chartPositions : (Option (Option (Fin 3))) → Coordinate × Coordinate :=
  Option.elim' (2, 1) (Option.elim' (1, 3) ![(2, 3), (3, 1), (3, 2)])

noncomputable def chartUnitVariables : Fin 5 → (Option (Option (Fin 3))) :=
  ![some (none), none, some (some (0 : Fin 3)), some (some (1 : Fin 3)), some (some (2 : Fin 3))]

noncomputable def chartLabelCode : ℕ := 16434824

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, true, true, true, false, true, true, false, true, false, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, false, false, false, true, false, false, true, false, true, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Fin 3))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 711)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 711) chartLabelCode chartEntries
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
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
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
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (7 : Fin 70) = _
      rw [minorFormula_at_7]
      dsimp [
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (9 : Fin 70)
      rw [minorFormula_at_9]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
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
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (36 : Fin 70) = _
      rw [minorFormula_at_36]
      dsimp [
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
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

noncomputable def chart_certificate : ChartCertificate (Option (Option (Fin 3))) 1 5
    (MatroidCatalogue.N8R4.family 711) where
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
    (MatroidCatalogue.N8R4.family 711) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart711
end

/- Source: Charts/Case712.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart712
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Option (Fin 1)))))) ℚ :=
  ![-(X (none) * X (some (none))) + (X (none) * X (some (some (some (none))))) - (X (some (some (none))) * X (some (some (some (none))))), X (none) - (1), X (some (some (none))) * X (some (some (some (some (some (0 : Fin 1)))))) + (X (some (some (some (some (none)))))) - (X (some (some (some (some (some (0 : Fin 1))))))), X (some (none)) + (X (some (some (some (some (none)))))) - (1), X (some (none)) * X (some (some (some (some (some (0 : Fin 1)))))) - (X (some (some (some (none)))) * X (some (some (some (some (none))))))]
noncomputable def U0 : Fin 6 → MvPolynomial (Option (Option (Option (Option (Option (Fin 1)))))) ℚ :=
  ![X (none), X (some (some (none))), X (some (none)), X (some (some (some (none)))), X (some (some (some (some (none))))), X (some (some (some (some (some (0 : Fin 1))))))]
noncomputable def R0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Option (Fin 1)))))) ℚ :=
  ![X (none) * X (some (none)) - (X (none) * X (some (some (some (none))))) + (X (some (some (none))) * X (some (some (some (none))))), X (none) - (1), X (some (some (none))) * X (some (some (some (some (some (0 : Fin 1)))))) + (X (some (some (some (some (none)))))) - (X (some (some (some (some (some (0 : Fin 1))))))), X (some (none)) + (X (some (some (some (some (none)))))) - (1), X (some (none)) * X (some (some (some (some (some (0 : Fin 1)))))) - (X (some (some (some (none)))) * X (some (some (some (some (none))))))]

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
        identity := by simp [U0, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U0, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U0, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U0, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U0, Fin.prod_univ_succ, map_ofNat]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring

noncomputable def nextE0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 1))))) ℚ :=
  ![X (none) + (X (some (none)) * X (some (some (none)))) - (X (some (some (none)))), 0, X (some (none)) * X (some (some (some (some (0 : Fin 1))))) + (X (some (some (some (none))))) - (X (some (some (some (some (0 : Fin 1)))))), X (none) + (X (some (some (some (none))))) - (1), X (none) * X (some (some (some (some (0 : Fin 1))))) - (X (some (some (none))) * X (some (some (some (none)))))]
noncomputable def nextU0 : Fin 6 → MvPolynomial (Option (Option (Option (Option (Fin 1))))) ℚ :=
  ![1, X (some (none)), X (none), X (some (some (none))), X (some (some (some (none)))), X (some (some (some (some (0 : Fin 1)))))]

noncomputable def step0 : LinearStep (Option (Option (Option (Option (Fin 1))))) 5 6 where
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
      identity := by simp [U0, Fin.prod_univ_succ, map_ofNat]<;> ring }
  equation_power := ![1, 1, 0, 0, 0]
  equation_quotient := ![X (some (none)) - (X (some (some (some (none))))), 1, 0, 0, 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![1, 0, 0, 0, 0, 0]
  unit_quotient := ![1, 0, 0, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 1))))) ℚ :=
  ![X (none) + (X (some (none)) * X (some (some (none)))) - (X (some (some (none)))), 0, X (some (none)) * X (some (some (some (some (0 : Fin 1))))) + (X (some (some (some (none))))) - (X (some (some (some (some (0 : Fin 1)))))), X (none) + (X (some (some (some (none))))) - (1), X (none) * X (some (some (some (some (0 : Fin 1))))) - (X (some (some (none))) * X (some (some (some (none)))))]
noncomputable def U1 : Fin 6 → MvPolynomial (Option (Option (Option (Option (Fin 1))))) ℚ :=
  ![1, X (some (none)), X (none), X (some (some (none))), X (some (some (some (none)))), X (some (some (some (some (0 : Fin 1)))))]
noncomputable def R1 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 1))))) ℚ :=
  ![X (none) + (X (some (none)) * X (some (some (none)))) - (X (some (some (none)))), 0, X (some (none)) * X (some (some (some (some (0 : Fin 1))))) + (X (some (some (some (none))))) - (X (some (some (some (some (0 : Fin 1)))))), X (none) + (X (some (some (some (none))))) - (1), X (none) * X (some (some (some (some (0 : Fin 1))))) - (X (some (some (none))) * X (some (some (some (none)))))]

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
        identity := by simp [U1, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U1, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U1, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U1, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U1, Fin.prod_univ_succ, map_ofNat]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring

noncomputable def nextE1 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 1)))) ℚ :=
  ![0, 0, X (none) * X (some (some (some (0 : Fin 1)))) + (X (some (some (none)))) - (X (some (some (some (0 : Fin 1))))), -(X (none) * X (some (none))) + (X (some (none))) + (X (some (some (none)))) - (1), -(X (none) * X (some (none)) * X (some (some (some (0 : Fin 1))))) - (X (some (none)) * X (some (some (none)))) + (X (some (none)) * X (some (some (some (0 : Fin 1)))))]
noncomputable def nextU1 : Fin 6 → MvPolynomial (Option (Option (Option (Fin 1)))) ℚ :=
  ![1, X (none), -(X (none) * X (some (none))) + (X (some (none))), X (some (none)), X (some (some (none))), X (some (some (some (0 : Fin 1))))]

noncomputable def step1 : LinearStep (Option (Option (Option (Fin 1)))) 5 6 where
  sourceE := R1
  sourceU := U1
  targetE := nextE1
  targetU := nextU1
  a := 1
  b := X (none) * X (some (none)) - (X (some (none)))
  pivot := 0
  pivot_identity := by simp [R1, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U1, Fin.prod_univ_succ, map_ofNat]<;> ring }
  equation_power := ![1, 0, 0, 1, 1]
  equation_quotient := ![1, 0, 0, 1, X (some (some (some (some (0 : Fin 1)))))]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring
  unit_power := ![0, 0, 1, 0, 0, 0]
  unit_quotient := ![0, 0, 1, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring

noncomputable def E2 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 1)))) ℚ :=
  ![0, 0, X (none) * X (some (some (some (0 : Fin 1)))) + (X (some (some (none)))) - (X (some (some (some (0 : Fin 1))))), -(X (none) * X (some (none))) + (X (some (none))) + (X (some (some (none)))) - (1), -(X (none) * X (some (none)) * X (some (some (some (0 : Fin 1))))) - (X (some (none)) * X (some (some (none)))) + (X (some (none)) * X (some (some (some (0 : Fin 1)))))]
noncomputable def U2 : Fin 6 → MvPolynomial (Option (Option (Option (Fin 1)))) ℚ :=
  ![1, X (none), -(X (none) * X (some (none))) + (X (some (none))), X (some (none)), X (some (some (none))), X (some (some (some (0 : Fin 1))))]
noncomputable def R2 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 1)))) ℚ :=
  ![0, 0, X (none) * X (some (some (some (0 : Fin 1)))) + (X (some (some (none)))) - (X (some (some (some (0 : Fin 1))))), X (none) * X (some (none)) - (X (some (none))) - (X (some (some (none)))) + (1), X (none) * X (some (some (some (0 : Fin 1)))) + (X (some (some (none)))) - (X (some (some (some (0 : Fin 1)))))]

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
        identity := by simp [U2, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U2, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U2, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U2, Fin.prod_univ_succ, map_ofNat]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(X (some (none)))
      unit_witness := {
        count := 1
        selected := ![3]
        quotient := -(1)
        identity := by simp [U2, Fin.prod_univ_succ, map_ofNat]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(X (some (none)))
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring

noncomputable def nextE2 : Fin 5 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![0, 0, 0, -(X (none) * X (some (none))) - (X (some (none)) * X (some (some (0 : Fin 1)))) + (X (some (some (0 : Fin 1)))), 0]
noncomputable def nextU2 : Fin 6 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![1, -(X (some (none))) + (X (some (some (0 : Fin 1)))), X (none) * X (some (none)), X (none), X (some (none)), X (some (some (0 : Fin 1)))]

noncomputable def step2 : LinearStep (Option (Option (Fin 1))) 5 6 where
  sourceE := R2
  sourceU := U2
  targetE := nextE2
  targetU := nextU2
  a := X (some (some (0 : Fin 1)))
  b := X (some (none)) - (X (some (some (0 : Fin 1))))
  pivot := 2
  pivot_identity := by simp [R2, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 1
      selected := ![5]
      quotient := 1
      identity := by simp [U2, Fin.prod_univ_succ, map_ofNat]<;> ring }
  equation_power := ![0, 0, 1, 1, 1]
  equation_quotient := ![0, 0, X (some (some (some (0 : Fin 1)))), X (some (none)), X (some (some (some (0 : Fin 1))))]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring
  unit_power := ![0, 1, 1, 0, 0, 0]
  unit_quotient := ![0, 1, -(X (some (none))), 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring

noncomputable def E3 : Fin 5 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![0, 0, 0, -(X (none) * X (some (none))) - (X (some (none)) * X (some (some (0 : Fin 1)))) + (X (some (some (0 : Fin 1)))), 0]
noncomputable def U3 : Fin 6 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![1, -(X (some (none))) + (X (some (some (0 : Fin 1)))), X (none) * X (some (none)), X (none), X (some (none)), X (some (some (0 : Fin 1)))]
noncomputable def R3 : Fin 5 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![0, 0, 0, X (none) * X (some (none)) + (X (some (none)) * X (some (some (0 : Fin 1)))) - (X (some (some (0 : Fin 1)))), 0]

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
        identity := by simp [U3, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U3, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U3, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U3, Fin.prod_univ_succ, map_ofNat]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
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
        identity := by simp [U3, Fin.prod_univ_succ, map_ofNat]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring

noncomputable def nextE3 : Fin 5 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![0, 0, 0, 0, 0]
noncomputable def nextU3 : Fin 6 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![1, -(X (none)) + (X (some (0 : Fin 1))), -((X (none)) ^ 2 * X (some (0 : Fin 1))) + (X (none) * X (some (0 : Fin 1))), -(X (none) * X (some (0 : Fin 1))) + (X (some (0 : Fin 1))), X (none), X (some (0 : Fin 1))]

noncomputable def step3 : LinearStep (Option (Fin 1)) 5 6 where
  sourceE := R3
  sourceU := U3
  targetE := nextE3
  targetU := nextU3
  a := X (none)
  b := X (none) * X (some (0 : Fin 1)) - (X (some (0 : Fin 1)))
  pivot := 3
  pivot_identity := by simp [R3, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 1
      selected := ![4]
      quotient := 1
      identity := by simp [U3, Fin.prod_univ_succ, map_ofNat]<;> ring }
  equation_power := ![0, 0, 0, 1, 0]
  equation_quotient := ![0, 0, 0, X (some (none)), 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R3, U3, nextE3, nextU3, map_ofNat] <;> ring
  unit_power := ![0, 0, 1, 1, 0, 0]
  unit_quotient := ![0, 0, X (some (none)), 1, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R3, U3, nextE3, nextU3, map_ofNat] <;> ring

noncomputable def E4 : Fin 5 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![0, 0, 0, 0, 0]
noncomputable def U4 : Fin 6 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![1, -(X (none)) + (X (some (0 : Fin 1))), -((X (none)) ^ 2 * X (some (0 : Fin 1))) + (X (none) * X (some (0 : Fin 1))), -(X (none) * X (some (0 : Fin 1))) + (X (some (0 : Fin 1))), X (none), X (some (0 : Fin 1))]
noncomputable def R4 : Fin 5 → MvPolynomial (Option (Fin 1)) ℚ :=
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
        identity := by simp [U4, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U4, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U4, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U4, Fin.prod_univ_succ, map_ofNat]<;> ring }
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
        identity := by simp [U4, Fin.prod_univ_succ, map_ofNat]<;> ring }
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

end Papers.RationalityTen.Chart712
end

/- Source: ChartTables/Case712.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart712
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Option (Option (Option (Fin 1)))))) :=
  ![![.one, .one, .one, .one], ![.one, .variable (none), .variable (some (some (none))), .zero], ![.one, .zero, .variable (some (none)), .variable (some (some (some (none))))], ![.zero, .one, .variable (some (some (some (some (none))))), .variable (some (some (some (some (some (0 : Fin 1))))))]]

noncomputable def chartPositions : (Option (Option (Option (Option (Option (Fin 1)))))) → Coordinate × Coordinate :=
  Option.elim' (1, 1) (Option.elim' (2, 2) (Option.elim' (1, 2) (Option.elim' (2, 3) (Option.elim' (3, 2) ![(3, 3)]))))

noncomputable def chartUnitVariables : Fin 6 → (Option (Option (Option (Option (Option (Fin 1)))))) :=
  ![none, some (some (none)), some (none), some (some (some (none))), some (some (some (some (none)))), some (some (some (some (some (0 : Fin 1)))))]

noncomputable def chartLabelCode : ℕ := 16431240

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, true, true, true, true, false, true, true, true, true, true, true, true, false, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, false, true, true, true, true, true, true, true, false, true, true, true, true, false, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, false, false, false, false, true, false, false, false, false, false, false, false, true, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, true, false, false, false, false, false, false, false, true, false, false, false, false, true, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Option (Option (Option (Fin 1)))))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 712)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 712) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨68, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (68 : Fin 70)
      rw [minorFormula_at_68]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
    · refine ⟨55, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (55 : Fin 70)
      rw [minorFormula_at_55]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
    · refine ⟨63, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (63 : Fin 70)
      rw [minorFormula_at_63]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
    · refine ⟨51, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (51 : Fin 70)
      rw [minorFormula_at_51]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
    · refine ⟨14, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (14 : Fin 70)
      rw [minorFormula_at_14]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
  · intro i hi
    fin_cases i
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (1 : Fin 70) = _
      rw [minorFormula_at_1]
      dsimp [
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (6 : Fin 70) = _
      rw [minorFormula_at_6]
      dsimp [
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨4, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (14 : Fin 70)
      rw [minorFormula_at_14]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (18 : Fin 70) = _
      rw [minorFormula_at_18]
      dsimp [
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨3, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (51 : Fin 70)
      rw [minorFormula_at_51]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨1, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (55 : Fin 70)
      rw [minorFormula_at_55]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨2, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (63 : Fin 70)
      rw [minorFormula_at_63]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (68 : Fin 70)
      rw [minorFormula_at_68]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> (try simp) <;> ring
    · simp [chartRequiredZero] at hi

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(0,7),(4,1),(4,2),(5,3)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Option (Option (Option (Option (Fin 1)))))) 5 6
    (MatroidCatalogue.N8R4.family 712) where
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
    (MatroidCatalogue.N8R4.family 712) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart712
end
