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

/- Source: Charts/Case128.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart128
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 1 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![-(X (none)) - (1)]
noncomputable def U0 : Fin 1 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none)]
noncomputable def R0 : Fin 1 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none) + (1)]

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
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring

noncomputable def nextE0 : Fin 1 → MvPolynomial (Fin 0) ℚ :=
  ![0]
noncomputable def nextU0 : Fin 1 → MvPolynomial (Fin 0) ℚ :=
  ![-(1)]

noncomputable def step0 : LinearStep (Fin 0) 1 1 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := 1
  b := 1
  pivot := 0
  pivot_identity := by simp [R0]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1]
  equation_quotient := ![1]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![1]
  unit_quotient := ![1]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 1 → MvPolynomial (Fin 0) ℚ :=
  ![0]
noncomputable def U1 : Fin 1 → MvPolynomial (Fin 0) ℚ :=
  ![-(1)]
noncomputable def R1 : Fin 1 → MvPolynomial (Fin 0) ℚ :=
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
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
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

end Papers.RationalityTen.Chart128
end

/- Source: ChartTables/Case128.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart128
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 0)) :=
  ![![.one, .one, .zero, .one], ![.zero, .one, .one, .zero], ![.zero, .zero, .one, .variable (none)], ![.zero, .zero, .zero, .one]]

noncomputable def chartPositions : (Option (Fin 0)) → Coordinate × Coordinate :=
  Option.elim' (2, 3) (Fin.elim0)

noncomputable def chartUnitVariables : Fin 1 → (Option (Fin 0)) :=
  ![none]

noncomputable def chartLabelCode : ℕ := 16096528

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, true, false, false, true, true, false, false, false, false, false, true, false, true, true, false, false, false, false, false, true, true, false, false, false, true, true, true, false, false, false, true, true, true, false, true, false, false, true, false, true, false, false, true, true, true, true, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, true, true, false, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, false, true, true, false, false, true, true, true, true, true, false, true, false, false, true, true, true, true, true, false, false, true, true, true, false, false, false, true, true, true, false, false, false, true, false, true, true, false, true, false, true, true, false, false, false, false, false, true, true, false, false, false, false, true, false, false, false, true, false, false, false, false, false, false, true, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 0)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 128)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 128) chartLabelCode chartEntries
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (2 : Fin 70) = _
      rw [minorFormula_at_2]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (3 : Fin 70) = _
      rw [minorFormula_at_3]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (5 : Fin 70) = _
      rw [minorFormula_at_5]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (6 : Fin 70) = _
      rw [minorFormula_at_6]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (9 : Fin 70) = _
      rw [minorFormula_at_9]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (10 : Fin 70) = _
      rw [minorFormula_at_10]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (11 : Fin 70) = _
      rw [minorFormula_at_11]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (12 : Fin 70) = _
      rw [minorFormula_at_12]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (13 : Fin 70) = _
      rw [minorFormula_at_13]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (15 : Fin 70) = _
      rw [minorFormula_at_15]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (18 : Fin 70) = _
      rw [minorFormula_at_18]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (20 : Fin 70) = _
      rw [minorFormula_at_20]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (21 : Fin 70) = _
      rw [minorFormula_at_21]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (25 : Fin 70) = _
      rw [minorFormula_at_25]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (26 : Fin 70) = _
      rw [minorFormula_at_26]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (27 : Fin 70) = _
      rw [minorFormula_at_27]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (31 : Fin 70) = _
      rw [minorFormula_at_31]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (32 : Fin 70) = _
      rw [minorFormula_at_32]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (33 : Fin 70) = _
      rw [minorFormula_at_33]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (39 : Fin 70) = _
      rw [minorFormula_at_39]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (40 : Fin 70) = _
      rw [minorFormula_at_40]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (42 : Fin 70) = _
      rw [minorFormula_at_42]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (44 : Fin 70) = _
      rw [minorFormula_at_44]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (45 : Fin 70) = _
      rw [minorFormula_at_45]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (51 : Fin 70) = _
      rw [minorFormula_at_51]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (52 : Fin 70) = _
      rw [minorFormula_at_52]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (57 : Fin 70) = _
      rw [minorFormula_at_57]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (68 : Fin 70)
      rw [minorFormula_at_68]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,7),(5,1),(7,3),(1,6),(6,2)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Fin 0)) 1 1
    (MatroidCatalogue.N8R4.family 128) where
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
    (MatroidCatalogue.N8R4.family 128) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart128
end

/- Source: Charts/Case129.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart129
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 0 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![]
noncomputable def U0 : Fin 1 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none)]
noncomputable def R0 : Fin 0 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![]

noncomputable def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart129
end

/- Source: ChartTables/Case129.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart129
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 0)) :=
  ![![.one, .one, .zero, .one], ![.zero, .one, .one, .zero], ![.zero, .zero, .one, .variable (none)], ![.zero, .zero, .zero, .one]]

noncomputable def chartPositions : (Option (Fin 0)) → Coordinate × Coordinate :=
  Option.elim' (2, 3) ![]

noncomputable def chartUnitVariables : Fin 1 → (Option (Fin 0)) :=
  ![none]

noncomputable def chartLabelCode : ℕ := 16096528

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, true, false, false, true, true, false, false, false, false, false, true, false, true, true, false, false, false, false, false, true, true, false, false, false, true, true, true, false, false, false, true, true, true, false, true, false, false, true, false, true, false, false, true, true, true, true, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, false, true, true, false, false, true, true, true, true, true, false, true, false, false, true, true, true, true, true, false, false, true, true, true, false, false, false, true, true, true, false, false, false, true, false, true, true, false, true, false, true, true, false, false, false, false, false, true, true, false, false, false, false, true, false, false, false, true, false, false, false, false, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 0)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 129)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 129) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    exact Fin.elim0 j
  · intro i hi
    fin_cases i
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (1 : Fin 70) = _
      rw [minorFormula_at_1]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (2 : Fin 70) = _
      rw [minorFormula_at_2]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (3 : Fin 70) = _
      rw [minorFormula_at_3]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (5 : Fin 70) = _
      rw [minorFormula_at_5]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (6 : Fin 70) = _
      rw [minorFormula_at_6]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (9 : Fin 70) = _
      rw [minorFormula_at_9]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (10 : Fin 70) = _
      rw [minorFormula_at_10]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (11 : Fin 70) = _
      rw [minorFormula_at_11]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (12 : Fin 70) = _
      rw [minorFormula_at_12]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (13 : Fin 70) = _
      rw [minorFormula_at_13]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (15 : Fin 70) = _
      rw [minorFormula_at_15]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (18 : Fin 70) = _
      rw [minorFormula_at_18]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (20 : Fin 70) = _
      rw [minorFormula_at_20]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (21 : Fin 70) = _
      rw [minorFormula_at_21]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (25 : Fin 70) = _
      rw [minorFormula_at_25]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (26 : Fin 70) = _
      rw [minorFormula_at_26]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (27 : Fin 70) = _
      rw [minorFormula_at_27]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (31 : Fin 70) = _
      rw [minorFormula_at_31]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (32 : Fin 70) = _
      rw [minorFormula_at_32]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (33 : Fin 70) = _
      rw [minorFormula_at_33]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (39 : Fin 70) = _
      rw [minorFormula_at_39]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (40 : Fin 70) = _
      rw [minorFormula_at_40]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (42 : Fin 70) = _
      rw [minorFormula_at_42]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (44 : Fin 70) = _
      rw [minorFormula_at_44]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (45 : Fin 70) = _
      rw [minorFormula_at_45]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (51 : Fin 70) = _
      rw [minorFormula_at_51]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (52 : Fin 70) = _
      rw [minorFormula_at_52]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (57 : Fin 70) = _
      rw [minorFormula_at_57]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
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

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,7),(5,1),(7,3),(1,6),(6,2)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Fin 0)) 0 1
    (MatroidCatalogue.N8R4.family 129) where
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
    (MatroidCatalogue.N8R4.family 129) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart129
end

/- Source: Charts/Case130.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart130
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 1 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (none) - (1)]
noncomputable def U0 : Fin 2 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (none), X (some (none))]
noncomputable def R0 : Fin 1 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (none) - (1)]

noncomputable def reductions0 (j : Fin 1) : FactorReduction U0 (E0 j) (R0 j) := by
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
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring

noncomputable def nextE0 : Fin 1 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0]
noncomputable def nextU0 : Fin 2 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![1, X (none)]

noncomputable def step0 : LinearStep (Option (Fin 0)) 1 2 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := 1
  b := -(1)
  pivot := 0
  pivot_identity := by simp [R0]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1]
  equation_quotient := ![1]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![1, 0]
  unit_quotient := ![1, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 1 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0]
noncomputable def U1 : Fin 2 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![1, X (none)]
noncomputable def R1 : Fin 1 → MvPolynomial (Option (Fin 0)) ℚ :=
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
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
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

end Papers.RationalityTen.Chart130
end

/- Source: ChartTables/Case130.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart130
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Fin 0))) :=
  ![![.one, .one, .zero, .one], ![.zero, .one, .one, .variable (none)], ![.zero, .zero, .one, .variable (some (none))], ![.zero, .zero, .zero, .one]]

noncomputable def chartPositions : (Option (Option (Fin 0))) → Coordinate × Coordinate :=
  Option.elim' (1, 3) (Option.elim' (2, 3) ![])

noncomputable def chartUnitVariables : Fin 2 → (Option (Option (Fin 0))) :=
  ![none, some (none)]

noncomputable def chartLabelCode : ℕ := 16096528

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, true, false, false, true, true, false, false, false, false, false, true, false, true, true, true, false, false, false, false, true, true, false, false, false, true, true, true, false, false, false, true, true, true, false, true, false, false, true, false, true, false, false, true, true, true, true, true, false, false, true, true, true, true, true, true, false, true, false, true, true, true, true, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, false, true, true, false, false, true, true, true, true, true, false, true, false, false, false, true, true, true, true, false, false, true, true, true, false, false, false, true, true, true, false, false, false, true, false, true, true, false, true, false, true, true, false, false, false, false, false, true, true, false, false, false, false, false, false, true, false, true, false, false, false, false, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 130)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 130) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨59, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (59 : Fin 70)
      rw [minorFormula_at_59]
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (2 : Fin 70) = _
      rw [minorFormula_at_2]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (3 : Fin 70) = _
      rw [minorFormula_at_3]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (5 : Fin 70) = _
      rw [minorFormula_at_5]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (6 : Fin 70) = _
      rw [minorFormula_at_6]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (9 : Fin 70) = _
      rw [minorFormula_at_9]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (10 : Fin 70) = _
      rw [minorFormula_at_10]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (11 : Fin 70) = _
      rw [minorFormula_at_11]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (12 : Fin 70) = _
      rw [minorFormula_at_12]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (13 : Fin 70) = _
      rw [minorFormula_at_13]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (20 : Fin 70) = _
      rw [minorFormula_at_20]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (21 : Fin 70) = _
      rw [minorFormula_at_21]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (25 : Fin 70) = _
      rw [minorFormula_at_25]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (26 : Fin 70) = _
      rw [minorFormula_at_26]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (27 : Fin 70) = _
      rw [minorFormula_at_27]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (31 : Fin 70) = _
      rw [minorFormula_at_31]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (32 : Fin 70) = _
      rw [minorFormula_at_32]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (33 : Fin 70) = _
      rw [minorFormula_at_33]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (39 : Fin 70) = _
      rw [minorFormula_at_39]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (40 : Fin 70) = _
      rw [minorFormula_at_40]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (42 : Fin 70) = _
      rw [minorFormula_at_42]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (44 : Fin 70) = _
      rw [minorFormula_at_44]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (45 : Fin 70) = _
      rw [minorFormula_at_45]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (51 : Fin 70) = _
      rw [minorFormula_at_51]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (52 : Fin 70) = _
      rw [minorFormula_at_52]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (59 : Fin 70)
      rw [minorFormula_at_59]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
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

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,7),(5,1),(7,3),(1,6),(6,2)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Option (Fin 0))) 1 2
    (MatroidCatalogue.N8R4.family 130) where
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
    (MatroidCatalogue.N8R4.family 130) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart130
end

/- Source: Charts/Case131.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart131
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 0 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![]
noncomputable def U0 : Fin 2 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![X (none), X (some (0 : Fin 1))]
noncomputable def R0 : Fin 0 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![]

noncomputable def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart131
end

/- Source: ChartTables/Case131.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart131
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 1)) :=
  ![![.one, .one, .zero, .one], ![.zero, .one, .one, .variable (none)], ![.zero, .zero, .one, .variable (some (0 : Fin 1))], ![.zero, .zero, .zero, .one]]

noncomputable def chartPositions : (Option (Fin 1)) → Coordinate × Coordinate :=
  Option.elim' (1, 3) ![(2, 3)]

noncomputable def chartUnitVariables : Fin 2 → (Option (Fin 1)) :=
  ![none, some (0 : Fin 1)]

noncomputable def chartLabelCode : ℕ := 16096528

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, true, false, false, true, true, false, false, false, false, false, true, false, true, true, true, false, false, false, false, true, true, false, false, false, true, true, true, false, false, false, true, true, true, false, true, false, false, true, false, true, false, false, true, true, true, true, true, false, false, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, false, true, true, false, false, true, true, true, true, true, false, true, false, false, false, true, true, true, true, false, false, true, true, true, false, false, false, true, true, true, false, false, false, true, false, true, true, false, true, false, true, true, false, false, false, false, false, true, true, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 1)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 131)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 131) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    exact Fin.elim0 j
  · intro i hi
    fin_cases i
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (1 : Fin 70) = _
      rw [minorFormula_at_1]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (2 : Fin 70) = _
      rw [minorFormula_at_2]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (3 : Fin 70) = _
      rw [minorFormula_at_3]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (5 : Fin 70) = _
      rw [minorFormula_at_5]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (6 : Fin 70) = _
      rw [minorFormula_at_6]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (9 : Fin 70) = _
      rw [minorFormula_at_9]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (10 : Fin 70) = _
      rw [minorFormula_at_10]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (11 : Fin 70) = _
      rw [minorFormula_at_11]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (12 : Fin 70) = _
      rw [minorFormula_at_12]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (13 : Fin 70) = _
      rw [minorFormula_at_13]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (20 : Fin 70) = _
      rw [minorFormula_at_20]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (21 : Fin 70) = _
      rw [minorFormula_at_21]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (25 : Fin 70) = _
      rw [minorFormula_at_25]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (26 : Fin 70) = _
      rw [minorFormula_at_26]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (27 : Fin 70) = _
      rw [minorFormula_at_27]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (31 : Fin 70) = _
      rw [minorFormula_at_31]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (32 : Fin 70) = _
      rw [minorFormula_at_32]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (33 : Fin 70) = _
      rw [minorFormula_at_33]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (39 : Fin 70) = _
      rw [minorFormula_at_39]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (40 : Fin 70) = _
      rw [minorFormula_at_40]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (42 : Fin 70) = _
      rw [minorFormula_at_42]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (44 : Fin 70) = _
      rw [minorFormula_at_44]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (45 : Fin 70) = _
      rw [minorFormula_at_45]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (51 : Fin 70) = _
      rw [minorFormula_at_51]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (52 : Fin 70) = _
      rw [minorFormula_at_52]
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
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

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,7),(5,1),(7,3),(1,6),(6,2)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Fin 1)) 0 2
    (MatroidCatalogue.N8R4.family 131) where
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
    (MatroidCatalogue.N8R4.family 131) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart131
end

/- Source: Charts/Case132.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart132
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 1 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![-(X (none)) + (X (some (none)))]
noncomputable def U0 : Fin 2 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (none), X (some (none))]
noncomputable def R0 : Fin 1 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (none) - (X (some (none)))]

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
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring

noncomputable def nextE0 : Fin 1 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0]
noncomputable def nextU0 : Fin 2 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none), X (none)]

noncomputable def step0 : LinearStep (Option (Fin 0)) 1 2 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := 1
  b := -(X (none))
  pivot := 0
  pivot_identity := by simp [R0]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1]
  equation_quotient := ![1]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![1, 0]
  unit_quotient := ![1, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 1 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0]
noncomputable def U1 : Fin 2 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none), X (none)]
noncomputable def R1 : Fin 1 → MvPolynomial (Option (Fin 0)) ℚ :=
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
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
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

end Papers.RationalityTen.Chart132
end

/- Source: ChartTables/Case132.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart132
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Fin 0))) :=
  ![![.one, .one, .one, .one], ![.zero, .one, .variable (none), .variable (some (none))], ![.zero, .zero, .one, .zero], ![.zero, .zero, .zero, .one]]

noncomputable def chartPositions : (Option (Option (Fin 0))) → Coordinate × Coordinate :=
  Option.elim' (1, 2) (Option.elim' (1, 3) ![])

noncomputable def chartUnitVariables : Fin 2 → (Option (Option (Fin 0))) :=
  ![none, some (none)]

noncomputable def chartLabelCode : ℕ := 16096528

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, true, false, false, true, false, false, false, false, false, false, true, false, true, true, true, false, false, false, false, true, true, false, false, false, true, false, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, true, true, true, true, true, false, false, true, true, true, true, false, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, false, true, true, false, true, true, true, true, true, true, false, true, false, false, false, true, true, true, true, false, false, true, true, true, false, true, false, true, true, true, false, false, false, false, false, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, false, false, false, false, false, false, true, true, false, false, false, false, true, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 132)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 132) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨60, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (60 : Fin 70)
      rw [minorFormula_at_60]
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (2 : Fin 70) = _
      rw [minorFormula_at_2]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (3 : Fin 70) = _
      rw [minorFormula_at_3]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (5 : Fin 70) = _
      rw [minorFormula_at_5]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (6 : Fin 70) = _
      rw [minorFormula_at_6]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (8 : Fin 70) = _
      rw [minorFormula_at_8]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (9 : Fin 70) = _
      rw [minorFormula_at_9]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (10 : Fin 70) = _
      rw [minorFormula_at_10]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (11 : Fin 70) = _
      rw [minorFormula_at_11]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (12 : Fin 70) = _
      rw [minorFormula_at_12]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (13 : Fin 70) = _
      rw [minorFormula_at_13]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (20 : Fin 70) = _
      rw [minorFormula_at_20]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (21 : Fin 70) = _
      rw [minorFormula_at_21]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (25 : Fin 70) = _
      rw [minorFormula_at_25]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (26 : Fin 70) = _
      rw [minorFormula_at_26]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (27 : Fin 70) = _
      rw [minorFormula_at_27]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (29 : Fin 70) = _
      rw [minorFormula_at_29]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (31 : Fin 70) = _
      rw [minorFormula_at_31]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (32 : Fin 70) = _
      rw [minorFormula_at_32]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (33 : Fin 70) = _
      rw [minorFormula_at_33]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (39 : Fin 70) = _
      rw [minorFormula_at_39]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (40 : Fin 70) = _
      rw [minorFormula_at_40]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (42 : Fin 70) = _
      rw [minorFormula_at_42]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (45 : Fin 70) = _
      rw [minorFormula_at_45]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (47 : Fin 70) = _
      rw [minorFormula_at_47]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (49 : Fin 70) = _
      rw [minorFormula_at_49]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (51 : Fin 70) = _
      rw [minorFormula_at_51]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (52 : Fin 70) = _
      rw [minorFormula_at_52]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (60 : Fin 70)
      rw [minorFormula_at_60]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (66 : Fin 70) = _
      rw [minorFormula_at_66]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(0,7),(5,1),(6,2),(7,3)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Option (Fin 0))) 1 2
    (MatroidCatalogue.N8R4.family 132) where
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
    (MatroidCatalogue.N8R4.family 132) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart132
end

/- Source: Charts/Case133.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart133
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 0 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![]
noncomputable def U0 : Fin 2 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![X (none), X (some (0 : Fin 1))]
noncomputable def R0 : Fin 0 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![]

noncomputable def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart133
end

/- Source: ChartTables/Case133.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart133
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 1)) :=
  ![![.one, .one, .one, .one], ![.zero, .one, .variable (none), .variable (some (0 : Fin 1))], ![.zero, .zero, .one, .zero], ![.zero, .zero, .zero, .one]]

noncomputable def chartPositions : (Option (Fin 1)) → Coordinate × Coordinate :=
  Option.elim' (1, 2) ![(1, 3)]

noncomputable def chartUnitVariables : Fin 2 → (Option (Fin 1)) :=
  ![none, some (0 : Fin 1)]

noncomputable def chartLabelCode : ℕ := 16096528

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, true, false, false, true, false, false, false, false, false, false, true, false, true, true, true, false, false, false, false, true, true, false, false, false, true, false, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, true, true, true, true, true, true, false, true, true, true, true, false, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, false, true, true, false, true, true, true, true, true, true, false, true, false, false, false, true, true, true, true, false, false, true, true, true, false, true, false, true, true, true, false, false, false, false, false, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, false, false, false, false, false, false, false, true, false, false, false, false, true, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 1)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 133)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 133) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    exact Fin.elim0 j
  · intro i hi
    fin_cases i
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (1 : Fin 70) = _
      rw [minorFormula_at_1]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (2 : Fin 70) = _
      rw [minorFormula_at_2]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (3 : Fin 70) = _
      rw [minorFormula_at_3]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (5 : Fin 70) = _
      rw [minorFormula_at_5]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (6 : Fin 70) = _
      rw [minorFormula_at_6]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (8 : Fin 70) = _
      rw [minorFormula_at_8]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (9 : Fin 70) = _
      rw [minorFormula_at_9]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (10 : Fin 70) = _
      rw [minorFormula_at_10]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (11 : Fin 70) = _
      rw [minorFormula_at_11]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (12 : Fin 70) = _
      rw [minorFormula_at_12]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (13 : Fin 70) = _
      rw [minorFormula_at_13]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (20 : Fin 70) = _
      rw [minorFormula_at_20]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (21 : Fin 70) = _
      rw [minorFormula_at_21]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (25 : Fin 70) = _
      rw [minorFormula_at_25]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (26 : Fin 70) = _
      rw [minorFormula_at_26]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (27 : Fin 70) = _
      rw [minorFormula_at_27]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (29 : Fin 70) = _
      rw [minorFormula_at_29]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (31 : Fin 70) = _
      rw [minorFormula_at_31]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (32 : Fin 70) = _
      rw [minorFormula_at_32]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (33 : Fin 70) = _
      rw [minorFormula_at_33]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (39 : Fin 70) = _
      rw [minorFormula_at_39]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (40 : Fin 70) = _
      rw [minorFormula_at_40]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (42 : Fin 70) = _
      rw [minorFormula_at_42]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (45 : Fin 70) = _
      rw [minorFormula_at_45]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (47 : Fin 70) = _
      rw [minorFormula_at_47]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (49 : Fin 70) = _
      rw [minorFormula_at_49]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (51 : Fin 70) = _
      rw [minorFormula_at_51]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (52 : Fin 70) = _
      rw [minorFormula_at_52]
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (66 : Fin 70) = _
      rw [minorFormula_at_66]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(0,7),(5,1),(6,2),(7,3)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Fin 1)) 0 2
    (MatroidCatalogue.N8R4.family 133) where
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
    (MatroidCatalogue.N8R4.family 133) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart133
end

/- Source: Charts/Case134.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart134
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 0 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![]
noncomputable def U0 : Fin 1 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none)]
noncomputable def R0 : Fin 0 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![]

noncomputable def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart134
end

/- Source: ChartTables/Case134.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart134
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 0)) :=
  ![![.one, .one, .one, .zero], ![.zero, .one, .variable (none), .zero], ![.zero, .zero, .one, .one], ![.zero, .zero, .zero, .one]]

noncomputable def chartPositions : (Option (Fin 0)) → Coordinate × Coordinate :=
  Option.elim' (1, 2) ![]

noncomputable def chartUnitVariables : Fin 1 → (Option (Fin 0)) :=
  ![none]

noncomputable def chartLabelCode : ℕ := 16096528

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, true, false, false, true, true, false, false, false, false, false, true, false, true, true, false, false, false, false, false, true, true, false, false, false, true, true, true, false, false, false, true, true, true, true, false, false, false, true, false, true, true, false, true, true, true, true, true, false, false, true, true, true, true, false, true, false, false, false, true, true, true, true, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, false, true, true, false, false, true, true, true, true, true, false, true, false, false, true, true, true, true, true, false, false, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, true, false, true, false, false, true, false, false, false, false, false, true, true, false, false, false, false, true, false, true, true, true, false, false, false, false, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 0)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 134)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 134) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    exact Fin.elim0 j
  · intro i hi
    fin_cases i
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (1 : Fin 70) = _
      rw [minorFormula_at_1]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (2 : Fin 70) = _
      rw [minorFormula_at_2]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (3 : Fin 70) = _
      rw [minorFormula_at_3]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (5 : Fin 70) = _
      rw [minorFormula_at_5]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (6 : Fin 70) = _
      rw [minorFormula_at_6]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (9 : Fin 70) = _
      rw [minorFormula_at_9]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (10 : Fin 70) = _
      rw [minorFormula_at_10]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (11 : Fin 70) = _
      rw [minorFormula_at_11]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (12 : Fin 70) = _
      rw [minorFormula_at_12]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (13 : Fin 70) = _
      rw [minorFormula_at_13]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (15 : Fin 70) = _
      rw [minorFormula_at_15]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (18 : Fin 70) = _
      rw [minorFormula_at_18]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (20 : Fin 70) = _
      rw [minorFormula_at_20]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (21 : Fin 70) = _
      rw [minorFormula_at_21]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (25 : Fin 70) = _
      rw [minorFormula_at_25]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (26 : Fin 70) = _
      rw [minorFormula_at_26]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (27 : Fin 70) = _
      rw [minorFormula_at_27]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (31 : Fin 70) = _
      rw [minorFormula_at_31]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (32 : Fin 70) = _
      rw [minorFormula_at_32]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (33 : Fin 70) = _
      rw [minorFormula_at_33]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (39 : Fin 70) = _
      rw [minorFormula_at_39]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (40 : Fin 70) = _
      rw [minorFormula_at_40]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (42 : Fin 70) = _
      rw [minorFormula_at_42]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (45 : Fin 70) = _
      rw [minorFormula_at_45]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (51 : Fin 70) = _
      rw [minorFormula_at_51]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (52 : Fin 70) = _
      rw [minorFormula_at_52]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (57 : Fin 70) = _
      rw [minorFormula_at_57]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (59 : Fin 70) = _
      rw [minorFormula_at_59]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (60 : Fin 70) = _
      rw [minorFormula_at_60]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
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

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(5,1),(6,2),(2,7),(7,3)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Fin 0)) 0 1
    (MatroidCatalogue.N8R4.family 134) where
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
    (MatroidCatalogue.N8R4.family 134) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart134
end

/- Source: Charts/Case135.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart135
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 1 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![-(X (none)) + (X (some (none)))]
noncomputable def U0 : Fin 3 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![X (none), X (some (none)), X (some (some (0 : Fin 1)))]
noncomputable def R0 : Fin 1 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![X (none) - (X (some (none)))]

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
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring

noncomputable def nextE0 : Fin 1 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![0]
noncomputable def nextU0 : Fin 3 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![X (none), X (none), X (some (0 : Fin 1))]

noncomputable def step0 : LinearStep (Option (Fin 1)) 1 3 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := 1
  b := -(X (none))
  pivot := 0
  pivot_identity := by simp [R0]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1]
  equation_quotient := ![1]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![1, 0, 0]
  unit_quotient := ![1, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 1 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![0]
noncomputable def U1 : Fin 3 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![X (none), X (none), X (some (0 : Fin 1))]
noncomputable def R1 : Fin 1 → MvPolynomial (Option (Fin 1)) ℚ :=
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
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
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

end Papers.RationalityTen.Chart135
end

/- Source: ChartTables/Case135.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart135
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Fin 1))) :=
  ![![.one, .one, .one, .one], ![.zero, .one, .variable (none), .variable (some (none))], ![.zero, .zero, .one, .variable (some (some (0 : Fin 1)))], ![.zero, .zero, .zero, .one]]

noncomputable def chartPositions : (Option (Option (Fin 1))) → Coordinate × Coordinate :=
  Option.elim' (1, 2) (Option.elim' (1, 3) ![(2, 3)])

noncomputable def chartUnitVariables : Fin 3 → (Option (Option (Fin 1))) :=
  ![none, some (none), some (some (0 : Fin 1))]

noncomputable def chartLabelCode : ℕ := 16096528

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, true, false, false, true, true, false, false, false, false, false, true, false, true, true, true, false, false, false, false, true, true, false, false, false, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, true, true, true, true, true, false, false, true, true, true, true, true, true, true, false, false, true, true, true, true, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, false, true, true, false, false, true, true, true, true, true, false, true, false, false, false, true, true, true, true, false, false, true, true, true, false, false, false, true, true, true, false, false, false, false, false, true, true, false, true, false, false, true, false, false, false, false, false, true, true, false, false, false, false, false, false, false, true, true, false, false, false, false, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 135)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 135) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨60, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (60 : Fin 70)
      rw [minorFormula_at_60]
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (2 : Fin 70) = _
      rw [minorFormula_at_2]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (3 : Fin 70) = _
      rw [minorFormula_at_3]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (5 : Fin 70) = _
      rw [minorFormula_at_5]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (6 : Fin 70) = _
      rw [minorFormula_at_6]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (9 : Fin 70) = _
      rw [minorFormula_at_9]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (10 : Fin 70) = _
      rw [minorFormula_at_10]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (11 : Fin 70) = _
      rw [minorFormula_at_11]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (12 : Fin 70) = _
      rw [minorFormula_at_12]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (13 : Fin 70) = _
      rw [minorFormula_at_13]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (20 : Fin 70) = _
      rw [minorFormula_at_20]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (21 : Fin 70) = _
      rw [minorFormula_at_21]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (25 : Fin 70) = _
      rw [minorFormula_at_25]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (26 : Fin 70) = _
      rw [minorFormula_at_26]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (27 : Fin 70) = _
      rw [minorFormula_at_27]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (31 : Fin 70) = _
      rw [minorFormula_at_31]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (32 : Fin 70) = _
      rw [minorFormula_at_32]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (33 : Fin 70) = _
      rw [minorFormula_at_33]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (39 : Fin 70) = _
      rw [minorFormula_at_39]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (40 : Fin 70) = _
      rw [minorFormula_at_40]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (42 : Fin 70) = _
      rw [minorFormula_at_42]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (45 : Fin 70) = _
      rw [minorFormula_at_45]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (51 : Fin 70) = _
      rw [minorFormula_at_51]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (52 : Fin 70) = _
      rw [minorFormula_at_52]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (60 : Fin 70)
      rw [minorFormula_at_60]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
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

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(0,7),(5,1),(6,2),(7,3)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Option (Fin 1))) 1 3
    (MatroidCatalogue.N8R4.family 135) where
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
    (MatroidCatalogue.N8R4.family 135) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart135
end

/- Source: Charts/Case136.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart136
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 1 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![-(X (none)) + (1)]
noncomputable def U0 : Fin 2 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (some (none)), X (none)]
noncomputable def R0 : Fin 1 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (none) - (1)]

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
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring

noncomputable def nextE0 : Fin 1 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0]
noncomputable def nextU0 : Fin 2 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none), 1]

noncomputable def step0 : LinearStep (Option (Fin 0)) 1 2 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := 1
  b := -(1)
  pivot := 0
  pivot_identity := by simp [R0]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1]
  equation_quotient := ![1]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![0, 1]
  unit_quotient := ![0, 1]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 1 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0]
noncomputable def U1 : Fin 2 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none), 1]
noncomputable def R1 : Fin 1 → MvPolynomial (Option (Fin 0)) ℚ :=
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
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
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

end Papers.RationalityTen.Chart136
end

/- Source: ChartTables/Case136.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart136
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Fin 0))) :=
  ![![.one, .one, .one, .one], ![.zero, .one, .variable (some (none)), .zero], ![.zero, .zero, .one, .variable (none)], ![.zero, .zero, .zero, .one]]

noncomputable def chartPositions : (Option (Option (Fin 0))) → Coordinate × Coordinate :=
  Option.elim' (2, 3) (Option.elim' (1, 2) ![])

noncomputable def chartUnitVariables : Fin 2 → (Option (Option (Fin 0))) :=
  ![some (none), none]

noncomputable def chartLabelCode : ℕ := 16096528

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, true, false, false, true, true, false, false, false, false, false, true, false, true, true, false, false, false, false, false, true, true, false, false, false, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, true, true, true, true, false, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, false, true, true, false, false, true, true, true, true, true, false, true, false, false, true, true, true, true, true, false, false, true, true, true, false, false, false, true, true, true, false, false, false, false, false, true, true, false, true, false, false, true, false, false, false, false, true, true, true, false, false, false, false, true, false, false, false, true, false, false, false, false, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 136)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 136) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨50, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (50 : Fin 70)
      rw [minorFormula_at_50]
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (2 : Fin 70) = _
      rw [minorFormula_at_2]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (3 : Fin 70) = _
      rw [minorFormula_at_3]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (5 : Fin 70) = _
      rw [minorFormula_at_5]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (6 : Fin 70) = _
      rw [minorFormula_at_6]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (9 : Fin 70) = _
      rw [minorFormula_at_9]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (10 : Fin 70) = _
      rw [minorFormula_at_10]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (11 : Fin 70) = _
      rw [minorFormula_at_11]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (12 : Fin 70) = _
      rw [minorFormula_at_12]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (13 : Fin 70) = _
      rw [minorFormula_at_13]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (15 : Fin 70) = _
      rw [minorFormula_at_15]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (18 : Fin 70) = _
      rw [minorFormula_at_18]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (20 : Fin 70) = _
      rw [minorFormula_at_20]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (21 : Fin 70) = _
      rw [minorFormula_at_21]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (25 : Fin 70) = _
      rw [minorFormula_at_25]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (26 : Fin 70) = _
      rw [minorFormula_at_26]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (27 : Fin 70) = _
      rw [minorFormula_at_27]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (31 : Fin 70) = _
      rw [minorFormula_at_31]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (32 : Fin 70) = _
      rw [minorFormula_at_32]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (33 : Fin 70) = _
      rw [minorFormula_at_33]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (39 : Fin 70) = _
      rw [minorFormula_at_39]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (40 : Fin 70) = _
      rw [minorFormula_at_40]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (42 : Fin 70) = _
      rw [minorFormula_at_42]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (45 : Fin 70) = _
      rw [minorFormula_at_45]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (50 : Fin 70)
      rw [minorFormula_at_50]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (51 : Fin 70) = _
      rw [minorFormula_at_51]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (52 : Fin 70) = _
      rw [minorFormula_at_52]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (57 : Fin 70) = _
      rw [minorFormula_at_57]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
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

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(0,7),(5,1),(6,2),(7,3)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Option (Fin 0))) 1 2
    (MatroidCatalogue.N8R4.family 136) where
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
    (MatroidCatalogue.N8R4.family 136) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart136
end

/- Source: Charts/Case137.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart137
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 0 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![]
noncomputable def U0 : Fin 2 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![X (none), X (some (0 : Fin 1))]
noncomputable def R0 : Fin 0 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![]

noncomputable def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart137
end

/- Source: ChartTables/Case137.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart137
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 1)) :=
  ![![.one, .one, .one, .one], ![.zero, .one, .variable (none), .zero], ![.zero, .zero, .one, .variable (some (0 : Fin 1))], ![.zero, .zero, .zero, .one]]

noncomputable def chartPositions : (Option (Fin 1)) → Coordinate × Coordinate :=
  Option.elim' (1, 2) ![(2, 3)]

noncomputable def chartUnitVariables : Fin 2 → (Option (Fin 1)) :=
  ![none, some (0 : Fin 1)]

noncomputable def chartLabelCode : ℕ := 16096528

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, true, false, false, true, true, false, false, false, false, false, true, false, true, true, false, false, false, false, false, true, true, false, false, false, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, true, true, true, true, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, false, true, true, false, false, true, true, true, true, true, false, true, false, false, true, true, true, true, true, false, false, true, true, true, false, false, false, true, true, true, false, false, false, false, false, true, true, false, true, false, false, true, false, false, false, false, false, true, true, false, false, false, false, true, false, false, false, true, false, false, false, false, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 1)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 137)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 137) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    exact Fin.elim0 j
  · intro i hi
    fin_cases i
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (1 : Fin 70) = _
      rw [minorFormula_at_1]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (2 : Fin 70) = _
      rw [minorFormula_at_2]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (3 : Fin 70) = _
      rw [minorFormula_at_3]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (5 : Fin 70) = _
      rw [minorFormula_at_5]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (6 : Fin 70) = _
      rw [minorFormula_at_6]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (9 : Fin 70) = _
      rw [minorFormula_at_9]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (10 : Fin 70) = _
      rw [minorFormula_at_10]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (11 : Fin 70) = _
      rw [minorFormula_at_11]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (12 : Fin 70) = _
      rw [minorFormula_at_12]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (13 : Fin 70) = _
      rw [minorFormula_at_13]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (15 : Fin 70) = _
      rw [minorFormula_at_15]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (18 : Fin 70) = _
      rw [minorFormula_at_18]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (20 : Fin 70) = _
      rw [minorFormula_at_20]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (21 : Fin 70) = _
      rw [minorFormula_at_21]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (25 : Fin 70) = _
      rw [minorFormula_at_25]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (26 : Fin 70) = _
      rw [minorFormula_at_26]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (27 : Fin 70) = _
      rw [minorFormula_at_27]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (31 : Fin 70) = _
      rw [minorFormula_at_31]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (32 : Fin 70) = _
      rw [minorFormula_at_32]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (33 : Fin 70) = _
      rw [minorFormula_at_33]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (39 : Fin 70) = _
      rw [minorFormula_at_39]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (40 : Fin 70) = _
      rw [minorFormula_at_40]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (42 : Fin 70) = _
      rw [minorFormula_at_42]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (45 : Fin 70) = _
      rw [minorFormula_at_45]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (51 : Fin 70) = _
      rw [minorFormula_at_51]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (52 : Fin 70) = _
      rw [minorFormula_at_52]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (57 : Fin 70) = _
      rw [minorFormula_at_57]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
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

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(0,7),(5,1),(6,2),(7,3)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Fin 1)) 0 2
    (MatroidCatalogue.N8R4.family 137) where
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
    (MatroidCatalogue.N8R4.family 137) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart137
end

/- Source: Charts/Case138.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart138
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 1 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![-(X (none) * X (some (none))) + (X (some (none))) + (1)]
noncomputable def U0 : Fin 2 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (none), X (some (none))]
noncomputable def R0 : Fin 1 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (none) * X (some (none)) - (X (some (none))) - (1)]

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
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring

noncomputable def nextE0 : Fin 1 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0]
noncomputable def nextU0 : Fin 2 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none) + (1), X (none)]

noncomputable def step0 : LinearStep (Option (Fin 0)) 1 2 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := X (none)
  b := -(X (none)) - (1)
  pivot := 0
  pivot_identity := by simp [R0]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 1
      selected := ![1]
      quotient := 1
      identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1]
  equation_quotient := ![X (some (none))]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![1, 0]
  unit_quotient := ![1, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 1 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0]
noncomputable def U1 : Fin 2 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none) + (1), X (none)]
noncomputable def R1 : Fin 1 → MvPolynomial (Option (Fin 0)) ℚ :=
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
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
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

end Papers.RationalityTen.Chart138
end

/- Source: ChartTables/Case138.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart138
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Fin 0))) :=
  ![![.one, .one, .one, .zero], ![.zero, .one, .variable (none), .one], ![.zero, .zero, .one, .variable (some (none))], ![.zero, .zero, .zero, .one]]

noncomputable def chartPositions : (Option (Option (Fin 0))) → Coordinate × Coordinate :=
  Option.elim' (1, 2) (Option.elim' (2, 3) ![])

noncomputable def chartUnitVariables : Fin 2 → (Option (Option (Fin 0))) :=
  ![none, some (none)]

noncomputable def chartLabelCode : ℕ := 16096528

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, true, false, false, true, true, false, false, false, false, false, true, false, true, true, true, false, false, false, false, true, true, false, false, false, true, true, true, false, false, false, true, true, true, true, false, false, false, true, false, true, true, false, true, true, true, true, true, false, false, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, false, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, false, true, true, false, false, true, true, true, true, true, false, true, false, false, false, true, true, true, true, false, false, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, true, false, true, false, false, true, false, false, false, false, false, true, true, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, true, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 138)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 138) chartLabelCode chartEntries
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (2 : Fin 70) = _
      rw [minorFormula_at_2]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (3 : Fin 70) = _
      rw [minorFormula_at_3]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (5 : Fin 70) = _
      rw [minorFormula_at_5]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (6 : Fin 70) = _
      rw [minorFormula_at_6]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (9 : Fin 70) = _
      rw [minorFormula_at_9]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (10 : Fin 70) = _
      rw [minorFormula_at_10]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (11 : Fin 70) = _
      rw [minorFormula_at_11]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (12 : Fin 70) = _
      rw [minorFormula_at_12]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (13 : Fin 70) = _
      rw [minorFormula_at_13]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (20 : Fin 70) = _
      rw [minorFormula_at_20]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (21 : Fin 70) = _
      rw [minorFormula_at_21]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (25 : Fin 70) = _
      rw [minorFormula_at_25]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (26 : Fin 70) = _
      rw [minorFormula_at_26]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (27 : Fin 70) = _
      rw [minorFormula_at_27]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (31 : Fin 70) = _
      rw [minorFormula_at_31]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (32 : Fin 70) = _
      rw [minorFormula_at_32]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (33 : Fin 70) = _
      rw [minorFormula_at_33]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (39 : Fin 70) = _
      rw [minorFormula_at_39]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (40 : Fin 70) = _
      rw [minorFormula_at_40]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (42 : Fin 70) = _
      rw [minorFormula_at_42]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (45 : Fin 70) = _
      rw [minorFormula_at_45]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (51 : Fin 70) = _
      rw [minorFormula_at_51]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (52 : Fin 70) = _
      rw [minorFormula_at_52]
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (68 : Fin 70)
      rw [minorFormula_at_68]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(5,1),(6,2),(1,7),(7,3)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Option (Fin 0))) 1 2
    (MatroidCatalogue.N8R4.family 138) where
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
    (MatroidCatalogue.N8R4.family 138) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart138
end

/- Source: Charts/Case139.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart139
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 0 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![]
noncomputable def U0 : Fin 2 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![X (none), X (some (0 : Fin 1))]
noncomputable def R0 : Fin 0 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![]

noncomputable def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart139
end

/- Source: ChartTables/Case139.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart139
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 1)) :=
  ![![.one, .one, .one, .zero], ![.zero, .one, .variable (none), .one], ![.zero, .zero, .one, .variable (some (0 : Fin 1))], ![.zero, .zero, .zero, .one]]

noncomputable def chartPositions : (Option (Fin 1)) → Coordinate × Coordinate :=
  Option.elim' (1, 2) ![(2, 3)]

noncomputable def chartUnitVariables : Fin 2 → (Option (Fin 1)) :=
  ![none, some (0 : Fin 1)]

noncomputable def chartLabelCode : ℕ := 16096528

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, true, false, false, true, true, false, false, false, false, false, true, false, true, true, true, false, false, false, false, true, true, false, false, false, true, true, true, false, false, false, true, true, true, true, false, false, false, true, false, true, true, false, true, true, true, true, true, false, false, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, false, true, true, false, false, true, true, true, true, true, false, true, false, false, false, true, true, true, true, false, false, true, true, true, false, false, false, true, true, true, false, false, false, false, true, true, true, false, true, false, false, true, false, false, false, false, false, true, true, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 1)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 139)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 139) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    exact Fin.elim0 j
  · intro i hi
    fin_cases i
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (1 : Fin 70) = _
      rw [minorFormula_at_1]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (2 : Fin 70) = _
      rw [minorFormula_at_2]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (3 : Fin 70) = _
      rw [minorFormula_at_3]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (5 : Fin 70) = _
      rw [minorFormula_at_5]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (6 : Fin 70) = _
      rw [minorFormula_at_6]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (9 : Fin 70) = _
      rw [minorFormula_at_9]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (10 : Fin 70) = _
      rw [minorFormula_at_10]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (11 : Fin 70) = _
      rw [minorFormula_at_11]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (12 : Fin 70) = _
      rw [minorFormula_at_12]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (13 : Fin 70) = _
      rw [minorFormula_at_13]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (20 : Fin 70) = _
      rw [minorFormula_at_20]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (21 : Fin 70) = _
      rw [minorFormula_at_21]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (25 : Fin 70) = _
      rw [minorFormula_at_25]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (26 : Fin 70) = _
      rw [minorFormula_at_26]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (27 : Fin 70) = _
      rw [minorFormula_at_27]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (31 : Fin 70) = _
      rw [minorFormula_at_31]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (32 : Fin 70) = _
      rw [minorFormula_at_32]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (33 : Fin 70) = _
      rw [minorFormula_at_33]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (39 : Fin 70) = _
      rw [minorFormula_at_39]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (40 : Fin 70) = _
      rw [minorFormula_at_40]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (42 : Fin 70) = _
      rw [minorFormula_at_42]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (45 : Fin 70) = _
      rw [minorFormula_at_45]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (51 : Fin 70) = _
      rw [minorFormula_at_51]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (52 : Fin 70) = _
      rw [minorFormula_at_52]
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
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

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(5,1),(6,2),(1,7),(7,3)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Fin 1)) 0 2
    (MatroidCatalogue.N8R4.family 139) where
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
    (MatroidCatalogue.N8R4.family 139) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart139
end

/- Source: Charts/Case140.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart140
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 0 → MvPolynomial (Option (Fin 2)) ℚ :=
  ![]
noncomputable def U0 : Fin 3 → MvPolynomial (Option (Fin 2)) ℚ :=
  ![X (none), X (some (0 : Fin 2)), X (some (1 : Fin 2))]
noncomputable def R0 : Fin 0 → MvPolynomial (Option (Fin 2)) ℚ :=
  ![]

noncomputable def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart140
end

/- Source: ChartTables/Case140.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart140
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 2)) :=
  ![![.one, .one, .one, .one], ![.zero, .one, .variable (none), .variable (some (0 : Fin 2))], ![.zero, .zero, .one, .variable (some (1 : Fin 2))], ![.zero, .zero, .zero, .one]]

noncomputable def chartPositions : (Option (Fin 2)) → Coordinate × Coordinate :=
  Option.elim' (1, 2) ![(1, 3), (2, 3)]

noncomputable def chartUnitVariables : Fin 3 → (Option (Fin 2)) :=
  ![none, some (0 : Fin 2), some (1 : Fin 2)]

noncomputable def chartLabelCode : ℕ := 16096528

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, true, false, false, true, true, false, false, false, false, false, true, false, true, true, true, false, false, false, false, true, true, false, false, false, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, true, true, true, true, true, false, false, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, false, true, true, false, false, true, true, true, true, true, false, true, false, false, false, true, true, true, true, false, false, true, true, true, false, false, false, true, true, true, false, false, false, false, false, true, true, false, true, false, false, true, false, false, false, false, false, true, true, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 2)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 140)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 140) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    exact Fin.elim0 j
  · intro i hi
    fin_cases i
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (1 : Fin 70) = _
      rw [minorFormula_at_1]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (2 : Fin 70) = _
      rw [minorFormula_at_2]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (3 : Fin 70) = _
      rw [minorFormula_at_3]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (5 : Fin 70) = _
      rw [minorFormula_at_5]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (6 : Fin 70) = _
      rw [minorFormula_at_6]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (9 : Fin 70) = _
      rw [minorFormula_at_9]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (10 : Fin 70) = _
      rw [minorFormula_at_10]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (11 : Fin 70) = _
      rw [minorFormula_at_11]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (12 : Fin 70) = _
      rw [minorFormula_at_12]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (13 : Fin 70) = _
      rw [minorFormula_at_13]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (20 : Fin 70) = _
      rw [minorFormula_at_20]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (21 : Fin 70) = _
      rw [minorFormula_at_21]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (25 : Fin 70) = _
      rw [minorFormula_at_25]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (26 : Fin 70) = _
      rw [minorFormula_at_26]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (27 : Fin 70) = _
      rw [minorFormula_at_27]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (31 : Fin 70) = _
      rw [minorFormula_at_31]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (32 : Fin 70) = _
      rw [minorFormula_at_32]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (33 : Fin 70) = _
      rw [minorFormula_at_33]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (39 : Fin 70) = _
      rw [minorFormula_at_39]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (40 : Fin 70) = _
      rw [minorFormula_at_40]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (42 : Fin 70) = _
      rw [minorFormula_at_42]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (45 : Fin 70) = _
      rw [minorFormula_at_45]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (51 : Fin 70) = _
      rw [minorFormula_at_51]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (52 : Fin 70) = _
      rw [minorFormula_at_52]
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
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

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(0,7),(5,1),(6,2),(7,3)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Fin 2)) 0 3
    (MatroidCatalogue.N8R4.family 140) where
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
    (MatroidCatalogue.N8R4.family 140) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart140
end

/- Source: Charts/Case141.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart141
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 0 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![]
noncomputable def U0 : Fin 1 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none)]
noncomputable def R0 : Fin 0 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![]

noncomputable def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart141
end

/- Source: ChartTables/Case141.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart141
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 0)) :=
  ![![.one, .zero, .zero, .zero], ![.zero, .one, .zero, .zero], ![.zero, .zero, .one, .one], ![.zero, .zero, .one, .variable (none)]]

noncomputable def chartPositions : (Option (Fin 0)) → Coordinate × Coordinate :=
  Option.elim' (3, 3) ![]

noncomputable def chartUnitVariables : Fin 1 → (Option (Fin 0)) :=
  ![none]

noncomputable def chartLabelCode : ℕ := 16358160

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, true, true, false, false, true, true, false, false, false, false, false, true, false, true, false, false, false, false, false, true, true, false, false, false, false, true, true, false, false, false, false, true, true, false, false, false, false, true, true, false, false, false, false, true, true, false, false, false, false, false, true, false, true, false, false, false, false, false, true, true, false, false, true, true, false, false, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, false, false, true, true, false, false, true, true, true, true, true, false, true, false, true, true, true, true, true, false, false, true, true, true, true, false, false, true, true, true, true, false, false, true, true, true, true, false, false, true, true, true, true, false, false, true, true, true, true, true, false, true, false, true, true, true, true, true, false, false, true, true, false, false, true, true, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 0)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 141)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 141) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    exact Fin.elim0 j
  · intro i hi
    fin_cases i
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (1 : Fin 70) = _
      rw [minorFormula_at_1]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (6 : Fin 70) = _
      rw [minorFormula_at_6]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (9 : Fin 70) = _
      rw [minorFormula_at_9]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (10 : Fin 70) = _
      rw [minorFormula_at_10]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (11 : Fin 70) = _
      rw [minorFormula_at_11]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (12 : Fin 70) = _
      rw [minorFormula_at_12]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (13 : Fin 70) = _
      rw [minorFormula_at_13]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (15 : Fin 70) = _
      rw [minorFormula_at_15]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (17 : Fin 70) = _
      rw [minorFormula_at_17]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (18 : Fin 70) = _
      rw [minorFormula_at_18]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (20 : Fin 70) = _
      rw [minorFormula_at_20]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (21 : Fin 70) = _
      rw [minorFormula_at_21]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (24 : Fin 70) = _
      rw [minorFormula_at_24]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (25 : Fin 70) = _
      rw [minorFormula_at_25]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (26 : Fin 70) = _
      rw [minorFormula_at_26]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (27 : Fin 70) = _
      rw [minorFormula_at_27]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (30 : Fin 70) = _
      rw [minorFormula_at_30]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (31 : Fin 70) = _
      rw [minorFormula_at_31]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (32 : Fin 70) = _
      rw [minorFormula_at_32]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (33 : Fin 70) = _
      rw [minorFormula_at_33]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (36 : Fin 70) = _
      rw [minorFormula_at_36]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (37 : Fin 70) = _
      rw [minorFormula_at_37]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (38 : Fin 70) = _
      rw [minorFormula_at_38]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (39 : Fin 70) = _
      rw [minorFormula_at_39]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (42 : Fin 70) = _
      rw [minorFormula_at_42]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (43 : Fin 70) = _
      rw [minorFormula_at_43]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (44 : Fin 70) = _
      rw [minorFormula_at_44]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (45 : Fin 70) = _
      rw [minorFormula_at_45]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (48 : Fin 70) = _
      rw [minorFormula_at_48]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (49 : Fin 70) = _
      rw [minorFormula_at_49]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (50 : Fin 70) = _
      rw [minorFormula_at_50]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (51 : Fin 70) = _
      rw [minorFormula_at_51]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (52 : Fin 70) = _
      rw [minorFormula_at_52]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (54 : Fin 70) = _
      rw [minorFormula_at_54]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (56 : Fin 70) = _
      rw [minorFormula_at_56]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (57 : Fin 70) = _
      rw [minorFormula_at_57]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (58 : Fin 70) = _
      rw [minorFormula_at_58]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (59 : Fin 70) = _
      rw [minorFormula_at_59]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (60 : Fin 70) = _
      rw [minorFormula_at_60]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (63 : Fin 70) = _
      rw [minorFormula_at_63]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (64 : Fin 70) = _
      rw [minorFormula_at_64]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (67 : Fin 70) = _
      rw [minorFormula_at_67]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (68 : Fin 70) = _
      rw [minorFormula_at_68]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi

noncomputable def chartForestRoots : Finset Point := {0,1,2}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(1,5),(2,6),(2,7),(6,3)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Fin 0)) 0 1
    (MatroidCatalogue.N8R4.family 141) where
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
    (MatroidCatalogue.N8R4.family 141) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart141
end

/- Source: Charts/Case142.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart142
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 0 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![]
noncomputable def U0 : Fin 1 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none)]
noncomputable def R0 : Fin 0 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![]

noncomputable def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart142
end

/- Source: ChartTables/Case142.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart142
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 0)) :=
  ![![.one, .one, .zero, .one], ![.one, .variable (none), .zero, .zero], ![.zero, .zero, .one, .zero], ![.zero, .zero, .zero, .one]]

noncomputable def chartPositions : (Option (Fin 0)) → Coordinate × Coordinate :=
  Option.elim' (1, 1) ![]

noncomputable def chartUnitVariables : Fin 1 → (Option (Fin 0)) :=
  ![none]

noncomputable def chartLabelCode : ℕ := 16100616

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, true, false, false, true, false, false, false, false, false, false, true, true, true, false, false, false, false, true, false, true, false, false, true, false, true, false, false, false, false, true, true, true, true, false, true, false, false, true, false, true, false, false, true, false, true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, false, true, true, false, true, true, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, true, false, true, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, true, true, false, false, false, true, false, true, false, true, true, false, true, true, false, true, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 0)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 142)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 142) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    exact Fin.elim0 j
  · intro i hi
    fin_cases i
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (1 : Fin 70) = _
      rw [minorFormula_at_1]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (2 : Fin 70) = _
      rw [minorFormula_at_2]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (3 : Fin 70) = _
      rw [minorFormula_at_3]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (5 : Fin 70) = _
      rw [minorFormula_at_5]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (6 : Fin 70) = _
      rw [minorFormula_at_6]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (8 : Fin 70) = _
      rw [minorFormula_at_8]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (9 : Fin 70) = _
      rw [minorFormula_at_9]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (10 : Fin 70) = _
      rw [minorFormula_at_10]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (11 : Fin 70) = _
      rw [minorFormula_at_11]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (12 : Fin 70) = _
      rw [minorFormula_at_12]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (13 : Fin 70) = _
      rw [minorFormula_at_13]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (17 : Fin 70) = _
      rw [minorFormula_at_17]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (18 : Fin 70) = _
      rw [minorFormula_at_18]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (20 : Fin 70) = _
      rw [minorFormula_at_20]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (24 : Fin 70) = _
      rw [minorFormula_at_24]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (25 : Fin 70) = _
      rw [minorFormula_at_25]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (27 : Fin 70) = _
      rw [minorFormula_at_27]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (29 : Fin 70) = _
      rw [minorFormula_at_29]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (30 : Fin 70) = _
      rw [minorFormula_at_30]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (31 : Fin 70) = _
      rw [minorFormula_at_31]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (32 : Fin 70) = _
      rw [minorFormula_at_32]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (39 : Fin 70) = _
      rw [minorFormula_at_39]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (40 : Fin 70) = _
      rw [minorFormula_at_40]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (42 : Fin 70) = _
      rw [minorFormula_at_42]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (44 : Fin 70) = _
      rw [minorFormula_at_44]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (45 : Fin 70) = _
      rw [minorFormula_at_45]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (47 : Fin 70) = _
      rw [minorFormula_at_47]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (49 : Fin 70) = _
      rw [minorFormula_at_49]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (51 : Fin 70) = _
      rw [minorFormula_at_51]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (52 : Fin 70) = _
      rw [minorFormula_at_52]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (56 : Fin 70) = _
      rw [minorFormula_at_56]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (58 : Fin 70) = _
      rw [minorFormula_at_58]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (60 : Fin 70) = _
      rw [minorFormula_at_60]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (63 : Fin 70) = _
      rw [minorFormula_at_63]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (64 : Fin 70) = _
      rw [minorFormula_at_64]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (66 : Fin 70) = _
      rw [minorFormula_at_66]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi

noncomputable def chartForestRoots : Finset Point := {0,2}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,7),(4,1),(7,3),(2,6)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Fin 0)) 0 1
    (MatroidCatalogue.N8R4.family 142) where
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
    (MatroidCatalogue.N8R4.family 142) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart142
end

/- Source: Charts/Case143.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart143
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 0 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![]
noncomputable def U0 : Fin 2 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![X (none), X (some (0 : Fin 1))]
noncomputable def R0 : Fin 0 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![]

noncomputable def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart143
end

/- Source: ChartTables/Case143.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart143
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 1)) :=
  ![![.one, .one, .zero, .one], ![.one, .variable (none), .zero, .variable (some (0 : Fin 1))], ![.zero, .zero, .one, .zero], ![.zero, .zero, .zero, .one]]

noncomputable def chartPositions : (Option (Fin 1)) → Coordinate × Coordinate :=
  Option.elim' (1, 1) ![(1, 3)]

noncomputable def chartUnitVariables : Fin 2 → (Option (Fin 1)) :=
  ![none, some (0 : Fin 1)]

noncomputable def chartLabelCode : ℕ := 16100616

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, true, false, false, true, false, false, false, false, false, false, true, true, true, false, true, false, false, true, false, true, false, false, true, false, true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, false, false, true, false, true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, false, true, true, false, true, true, true, true, true, true, false, false, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, true, true, false, false, false, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, true, true, false, false, false, true, false, true, false, true, true, false, true, true, false, true, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 1)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 143)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 143) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    exact Fin.elim0 j
  · intro i hi
    fin_cases i
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (1 : Fin 70) = _
      rw [minorFormula_at_1]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (2 : Fin 70) = _
      rw [minorFormula_at_2]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (3 : Fin 70) = _
      rw [minorFormula_at_3]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (5 : Fin 70) = _
      rw [minorFormula_at_5]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (6 : Fin 70) = _
      rw [minorFormula_at_6]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (8 : Fin 70) = _
      rw [minorFormula_at_8]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (9 : Fin 70) = _
      rw [minorFormula_at_9]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (10 : Fin 70) = _
      rw [minorFormula_at_10]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (11 : Fin 70) = _
      rw [minorFormula_at_11]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (12 : Fin 70) = _
      rw [minorFormula_at_12]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (13 : Fin 70) = _
      rw [minorFormula_at_13]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (20 : Fin 70) = _
      rw [minorFormula_at_20]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (24 : Fin 70) = _
      rw [minorFormula_at_24]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (25 : Fin 70) = _
      rw [minorFormula_at_25]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (27 : Fin 70) = _
      rw [minorFormula_at_27]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (29 : Fin 70) = _
      rw [minorFormula_at_29]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (31 : Fin 70) = _
      rw [minorFormula_at_31]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (32 : Fin 70) = _
      rw [minorFormula_at_32]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (39 : Fin 70) = _
      rw [minorFormula_at_39]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (40 : Fin 70) = _
      rw [minorFormula_at_40]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (42 : Fin 70) = _
      rw [minorFormula_at_42]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (44 : Fin 70) = _
      rw [minorFormula_at_44]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (45 : Fin 70) = _
      rw [minorFormula_at_45]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (47 : Fin 70) = _
      rw [minorFormula_at_47]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (49 : Fin 70) = _
      rw [minorFormula_at_49]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (51 : Fin 70) = _
      rw [minorFormula_at_51]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (52 : Fin 70) = _
      rw [minorFormula_at_52]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (56 : Fin 70) = _
      rw [minorFormula_at_56]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (58 : Fin 70) = _
      rw [minorFormula_at_58]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (60 : Fin 70) = _
      rw [minorFormula_at_60]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (63 : Fin 70) = _
      rw [minorFormula_at_63]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (64 : Fin 70) = _
      rw [minorFormula_at_64]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (66 : Fin 70) = _
      rw [minorFormula_at_66]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi

noncomputable def chartForestRoots : Finset Point := {0,2}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,7),(4,1),(7,3),(2,6)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Fin 1)) 0 2
    (MatroidCatalogue.N8R4.family 143) where
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
    (MatroidCatalogue.N8R4.family 143) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart143
end

/- Source: Charts/Case144.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart144
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 0 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![]
noncomputable def U0 : Fin 1 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none)]
noncomputable def R0 : Fin 0 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![]

noncomputable def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart144
end

/- Source: ChartTables/Case144.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart144
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 0)) :=
  ![![.one, .zero, .zero, .one], ![.zero, .one, .one, .zero], ![.zero, .one, .variable (none), .zero], ![.zero, .zero, .zero, .one]]

noncomputable def chartPositions : (Option (Fin 0)) → Coordinate × Coordinate :=
  Option.elim' (2, 2) ![]

noncomputable def chartUnitVariables : Fin 1 → (Option (Fin 0)) :=
  ![none]

noncomputable def chartLabelCode : ℕ := 16129232

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, true, false, true, true, false, false, false, false, false, true, true, false, true, true, false, false, false, false, false, true, true, false, false, false, true, false, false, false, false, false, true, true, false, false, true, false, false, true, false, false, false, true, true, false, false, true, true, false, true, true, false, true, true, false, false, true, true, false, true, true, false, true, false, false, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, false, true, false, false, true, true, true, true, true, false, false, true, false, false, true, true, true, true, true, false, false, true, true, true, false, true, true, true, true, true, false, false, true, true, false, true, true, false, true, true, true, false, false, true, true, false, false, true, false, false, true, false, false, true, true, false, false, true, false, false, true, false, true, true, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 0)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 144)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 144) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    exact Fin.elim0 j
  · intro i hi
    fin_cases i
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (1 : Fin 70) = _
      rw [minorFormula_at_1]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (2 : Fin 70) = _
      rw [minorFormula_at_2]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (3 : Fin 70) = _
      rw [minorFormula_at_3]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (5 : Fin 70) = _
      rw [minorFormula_at_5]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (8 : Fin 70) = _
      rw [minorFormula_at_8]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (9 : Fin 70) = _
      rw [minorFormula_at_9]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (10 : Fin 70) = _
      rw [minorFormula_at_10]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (11 : Fin 70) = _
      rw [minorFormula_at_11]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (12 : Fin 70) = _
      rw [minorFormula_at_12]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (18 : Fin 70) = _
      rw [minorFormula_at_18]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (20 : Fin 70) = _
      rw [minorFormula_at_20]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (21 : Fin 70) = _
      rw [minorFormula_at_21]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (25 : Fin 70) = _
      rw [minorFormula_at_25]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (26 : Fin 70) = _
      rw [minorFormula_at_26]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (27 : Fin 70) = _
      rw [minorFormula_at_27]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (29 : Fin 70) = _
      rw [minorFormula_at_29]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (30 : Fin 70) = _
      rw [minorFormula_at_30]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (31 : Fin 70) = _
      rw [minorFormula_at_31]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (32 : Fin 70) = _
      rw [minorFormula_at_32]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (33 : Fin 70) = _
      rw [minorFormula_at_33]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (36 : Fin 70) = _
      rw [minorFormula_at_36]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (37 : Fin 70) = _
      rw [minorFormula_at_37]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (39 : Fin 70) = _
      rw [minorFormula_at_39]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (40 : Fin 70) = _
      rw [minorFormula_at_40]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (42 : Fin 70) = _
      rw [minorFormula_at_42]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (43 : Fin 70) = _
      rw [minorFormula_at_43]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (44 : Fin 70) = _
      rw [minorFormula_at_44]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (47 : Fin 70) = _
      rw [minorFormula_at_47]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (48 : Fin 70) = _
      rw [minorFormula_at_48]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (51 : Fin 70) = _
      rw [minorFormula_at_51]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (54 : Fin 70) = _
      rw [minorFormula_at_54]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (57 : Fin 70) = _
      rw [minorFormula_at_57]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (58 : Fin 70) = _
      rw [minorFormula_at_58]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (64 : Fin 70) = _
      rw [minorFormula_at_64]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (66 : Fin 70) = _
      rw [minorFormula_at_66]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (67 : Fin 70) = _
      rw [minorFormula_at_67]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi

noncomputable def chartForestRoots : Finset Point := {0,1}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,7),(7,3),(1,5),(1,6),(5,2)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Fin 0)) 0 1
    (MatroidCatalogue.N8R4.family 144) where
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
    (MatroidCatalogue.N8R4.family 144) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart144
end

/- Source: Charts/Case145.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart145
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 0 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![]
noncomputable def U0 : Fin 1 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none)]
noncomputable def R0 : Fin 0 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![]

noncomputable def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart145
end

/- Source: ChartTables/Case145.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart145
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 0)) :=
  ![![.one, .zero, .zero, .one], ![.zero, .one, .one, .one], ![.zero, .one, .variable (none), .zero], ![.zero, .zero, .zero, .one]]

noncomputable def chartPositions : (Option (Fin 0)) → Coordinate × Coordinate :=
  Option.elim' (2, 2) ![]

noncomputable def chartUnitVariables : Fin 1 → (Option (Fin 0)) :=
  ![none]

noncomputable def chartLabelCode : ℕ := 16129232

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, true, false, true, true, false, false, false, false, false, true, true, false, true, true, true, false, false, false, false, true, true, false, false, false, true, true, true, false, false, false, true, true, false, false, true, false, false, true, false, false, false, true, true, false, false, true, true, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, false, true, false, false, true, true, true, true, true, false, false, true, false, false, false, true, true, true, true, false, false, true, true, true, false, false, false, true, true, true, false, false, true, true, false, true, true, false, true, true, true, false, false, true, true, false, false, true, false, false, true, false, false, false, true, false, false, true, false, false, true, false, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 0)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 145)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 145) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    exact Fin.elim0 j
  · intro i hi
    fin_cases i
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (1 : Fin 70) = _
      rw [minorFormula_at_1]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (2 : Fin 70) = _
      rw [minorFormula_at_2]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (3 : Fin 70) = _
      rw [minorFormula_at_3]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (5 : Fin 70) = _
      rw [minorFormula_at_5]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (8 : Fin 70) = _
      rw [minorFormula_at_8]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (9 : Fin 70) = _
      rw [minorFormula_at_9]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (10 : Fin 70) = _
      rw [minorFormula_at_10]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (11 : Fin 70) = _
      rw [minorFormula_at_11]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (12 : Fin 70) = _
      rw [minorFormula_at_12]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (20 : Fin 70) = _
      rw [minorFormula_at_20]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (21 : Fin 70) = _
      rw [minorFormula_at_21]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (25 : Fin 70) = _
      rw [minorFormula_at_25]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (26 : Fin 70) = _
      rw [minorFormula_at_26]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (27 : Fin 70) = _
      rw [minorFormula_at_27]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (31 : Fin 70) = _
      rw [minorFormula_at_31]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (32 : Fin 70) = _
      rw [minorFormula_at_32]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (33 : Fin 70) = _
      rw [minorFormula_at_33]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (36 : Fin 70) = _
      rw [minorFormula_at_36]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (37 : Fin 70) = _
      rw [minorFormula_at_37]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (39 : Fin 70) = _
      rw [minorFormula_at_39]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (40 : Fin 70) = _
      rw [minorFormula_at_40]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (42 : Fin 70) = _
      rw [minorFormula_at_42]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (43 : Fin 70) = _
      rw [minorFormula_at_43]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (44 : Fin 70) = _
      rw [minorFormula_at_44]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (47 : Fin 70) = _
      rw [minorFormula_at_47]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (48 : Fin 70) = _
      rw [minorFormula_at_48]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (51 : Fin 70) = _
      rw [minorFormula_at_51]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (54 : Fin 70) = _
      rw [minorFormula_at_54]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (58 : Fin 70) = _
      rw [minorFormula_at_58]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (64 : Fin 70) = _
      rw [minorFormula_at_64]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,7),(7,1),(7,3),(1,5),(1,6),(5,2)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Fin 0)) 0 1
    (MatroidCatalogue.N8R4.family 145) where
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
    (MatroidCatalogue.N8R4.family 145) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart145
end

/- Source: Charts/Case146.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart146
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 0 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![]
noncomputable def U0 : Fin 2 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![X (none), X (some (0 : Fin 1))]
noncomputable def R0 : Fin 0 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![]

noncomputable def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart146
end

/- Source: ChartTables/Case146.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart146
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 1)) :=
  ![![.one, .zero, .zero, .one], ![.zero, .one, .one, .one], ![.zero, .one, .variable (none), .variable (some (0 : Fin 1))], ![.zero, .zero, .zero, .one]]

noncomputable def chartPositions : (Option (Fin 1)) → Coordinate × Coordinate :=
  Option.elim' (2, 2) ![(2, 3)]

noncomputable def chartUnitVariables : Fin 2 → (Option (Fin 1)) :=
  ![none, some (0 : Fin 1)]

noncomputable def chartLabelCode : ℕ := 16129232

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, true, false, true, true, true, false, false, false, false, true, true, false, true, true, true, false, false, false, false, true, true, false, false, false, true, true, true, false, false, false, true, true, false, false, true, false, false, true, false, false, false, true, true, true, false, true, true, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, false, true, false, false, false, true, true, true, true, false, false, true, false, false, false, true, true, true, true, false, false, true, true, true, false, false, false, true, true, true, false, false, true, true, false, true, true, false, true, true, true, false, false, false, true, false, false, true, false, false, true, false, false, false, true, false, false, true, false, false, true, false, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 1)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 146)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 146) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    exact Fin.elim0 j
  · intro i hi
    fin_cases i
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (1 : Fin 70) = _
      rw [minorFormula_at_1]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (2 : Fin 70) = _
      rw [minorFormula_at_2]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (3 : Fin 70) = _
      rw [minorFormula_at_3]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (9 : Fin 70) = _
      rw [minorFormula_at_9]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (10 : Fin 70) = _
      rw [minorFormula_at_10]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (11 : Fin 70) = _
      rw [minorFormula_at_11]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (12 : Fin 70) = _
      rw [minorFormula_at_12]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (20 : Fin 70) = _
      rw [minorFormula_at_20]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (21 : Fin 70) = _
      rw [minorFormula_at_21]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (25 : Fin 70) = _
      rw [minorFormula_at_25]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (26 : Fin 70) = _
      rw [minorFormula_at_26]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (27 : Fin 70) = _
      rw [minorFormula_at_27]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (31 : Fin 70) = _
      rw [minorFormula_at_31]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (32 : Fin 70) = _
      rw [minorFormula_at_32]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (33 : Fin 70) = _
      rw [minorFormula_at_33]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (36 : Fin 70) = _
      rw [minorFormula_at_36]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (37 : Fin 70) = _
      rw [minorFormula_at_37]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (39 : Fin 70) = _
      rw [minorFormula_at_39]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (40 : Fin 70) = _
      rw [minorFormula_at_40]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (42 : Fin 70) = _
      rw [minorFormula_at_42]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (43 : Fin 70) = _
      rw [minorFormula_at_43]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (44 : Fin 70) = _
      rw [minorFormula_at_44]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (48 : Fin 70) = _
      rw [minorFormula_at_48]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (51 : Fin 70) = _
      rw [minorFormula_at_51]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (54 : Fin 70) = _
      rw [minorFormula_at_54]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (58 : Fin 70) = _
      rw [minorFormula_at_58]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (64 : Fin 70) = _
      rw [minorFormula_at_64]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,7),(7,1),(7,3),(1,5),(1,6),(5,2)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Fin 1)) 0 2
    (MatroidCatalogue.N8R4.family 146) where
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
    (MatroidCatalogue.N8R4.family 146) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart146
end

/- Source: Charts/Case147.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart147
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 0 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![]
noncomputable def U0 : Fin 1 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none)]
noncomputable def R0 : Fin 0 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![]

noncomputable def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart147
end

/- Source: ChartTables/Case147.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart147
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 0)) :=
  ![![.one, .one, .one, .one], ![.one, .variable (none), .zero, .zero], ![.zero, .zero, .one, .zero], ![.zero, .zero, .zero, .one]]

noncomputable def chartPositions : (Option (Fin 0)) → Coordinate × Coordinate :=
  Option.elim' (1, 1) ![]

noncomputable def chartUnitVariables : Fin 1 → (Option (Fin 0)) :=
  ![none]

noncomputable def chartLabelCode : ℕ := 16100616

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, true, false, false, true, false, false, false, false, false, false, true, true, true, false, false, false, false, true, false, true, false, false, true, false, true, false, false, false, false, true, true, true, true, true, true, false, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, true, true, true, true, true, false, false, true, true, true, true, false, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, false, true, true, false, true, true, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, true, false, true, false, true, true, true, true, false, false, false, false, false, false, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, false, false, false, false, false, false, true, true, false, false, false, false, true, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 0)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 147)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 147) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    exact Fin.elim0 j
  · intro i hi
    fin_cases i
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (1 : Fin 70) = _
      rw [minorFormula_at_1]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (2 : Fin 70) = _
      rw [minorFormula_at_2]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (3 : Fin 70) = _
      rw [minorFormula_at_3]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (5 : Fin 70) = _
      rw [minorFormula_at_5]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (6 : Fin 70) = _
      rw [minorFormula_at_6]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (8 : Fin 70) = _
      rw [minorFormula_at_8]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (9 : Fin 70) = _
      rw [minorFormula_at_9]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (10 : Fin 70) = _
      rw [minorFormula_at_10]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (11 : Fin 70) = _
      rw [minorFormula_at_11]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (12 : Fin 70) = _
      rw [minorFormula_at_12]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (13 : Fin 70) = _
      rw [minorFormula_at_13]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (17 : Fin 70) = _
      rw [minorFormula_at_17]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (18 : Fin 70) = _
      rw [minorFormula_at_18]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (20 : Fin 70) = _
      rw [minorFormula_at_20]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (24 : Fin 70) = _
      rw [minorFormula_at_24]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (25 : Fin 70) = _
      rw [minorFormula_at_25]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (27 : Fin 70) = _
      rw [minorFormula_at_27]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (29 : Fin 70) = _
      rw [minorFormula_at_29]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (30 : Fin 70) = _
      rw [minorFormula_at_30]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (31 : Fin 70) = _
      rw [minorFormula_at_31]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (32 : Fin 70) = _
      rw [minorFormula_at_32]
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
      change minorFormula (fun r c => (chartEntries r c).polynomial) (39 : Fin 70) = _
      rw [minorFormula_at_39]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (40 : Fin 70) = _
      rw [minorFormula_at_40]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (42 : Fin 70) = _
      rw [minorFormula_at_42]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (45 : Fin 70) = _
      rw [minorFormula_at_45]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (47 : Fin 70) = _
      rw [minorFormula_at_47]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (49 : Fin 70) = _
      rw [minorFormula_at_49]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (51 : Fin 70) = _
      rw [minorFormula_at_51]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (52 : Fin 70) = _
      rw [minorFormula_at_52]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (60 : Fin 70) = _
      rw [minorFormula_at_60]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (66 : Fin 70) = _
      rw [minorFormula_at_66]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(0,7),(4,1),(6,2),(7,3)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Fin 0)) 0 1
    (MatroidCatalogue.N8R4.family 147) where
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
    (MatroidCatalogue.N8R4.family 147) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart147
end

/- Source: Charts/Case148.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart148
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 0 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![]
noncomputable def U0 : Fin 1 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none)]
noncomputable def R0 : Fin 0 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![]

noncomputable def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart148
end

/- Source: ChartTables/Case148.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart148
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 0)) :=
  ![![.one, .one, .zero, .one], ![.one, .variable (none), .one, .zero], ![.zero, .zero, .one, .zero], ![.zero, .zero, .zero, .one]]

noncomputable def chartPositions : (Option (Fin 0)) → Coordinate × Coordinate :=
  Option.elim' (1, 1) ![]

noncomputable def chartUnitVariables : Fin 1 → (Option (Fin 0)) :=
  ![none]

noncomputable def chartLabelCode : ℕ := 16100616

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, true, false, false, true, false, false, false, false, false, false, true, true, true, true, false, false, false, true, false, true, true, false, true, false, true, false, false, false, false, true, true, true, true, false, true, false, false, true, false, true, false, false, true, false, true, false, true, false, false, true, true, true, true, true, true, true, true, false, true, true, true, true, false, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, true, false, true, false, false, true, false, true, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, true, true, false, false, false, false, false, false, false, false, true, false, false, false, false, true, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 0)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 148)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 148) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    exact Fin.elim0 j
  · intro i hi
    fin_cases i
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (1 : Fin 70) = _
      rw [minorFormula_at_1]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (2 : Fin 70) = _
      rw [minorFormula_at_2]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (3 : Fin 70) = _
      rw [minorFormula_at_3]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (5 : Fin 70) = _
      rw [minorFormula_at_5]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (6 : Fin 70) = _
      rw [minorFormula_at_6]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (8 : Fin 70) = _
      rw [minorFormula_at_8]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (9 : Fin 70) = _
      rw [minorFormula_at_9]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (10 : Fin 70) = _
      rw [minorFormula_at_10]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (11 : Fin 70) = _
      rw [minorFormula_at_11]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (12 : Fin 70) = _
      rw [minorFormula_at_12]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (13 : Fin 70) = _
      rw [minorFormula_at_13]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (18 : Fin 70) = _
      rw [minorFormula_at_18]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (20 : Fin 70) = _
      rw [minorFormula_at_20]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (25 : Fin 70) = _
      rw [minorFormula_at_25]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (27 : Fin 70) = _
      rw [minorFormula_at_27]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (29 : Fin 70) = _
      rw [minorFormula_at_29]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (30 : Fin 70) = _
      rw [minorFormula_at_30]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (31 : Fin 70) = _
      rw [minorFormula_at_31]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (32 : Fin 70) = _
      rw [minorFormula_at_32]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (39 : Fin 70) = _
      rw [minorFormula_at_39]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (40 : Fin 70) = _
      rw [minorFormula_at_40]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (42 : Fin 70) = _
      rw [minorFormula_at_42]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (44 : Fin 70) = _
      rw [minorFormula_at_44]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (45 : Fin 70) = _
      rw [minorFormula_at_45]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (47 : Fin 70) = _
      rw [minorFormula_at_47]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (49 : Fin 70) = _
      rw [minorFormula_at_49]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (51 : Fin 70) = _
      rw [minorFormula_at_51]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (52 : Fin 70) = _
      rw [minorFormula_at_52]
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (66 : Fin 70) = _
      rw [minorFormula_at_66]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,7),(4,1),(7,3),(1,6),(6,2)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Fin 0)) 0 1
    (MatroidCatalogue.N8R4.family 148) where
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
    (MatroidCatalogue.N8R4.family 148) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart148
end

/- Source: Charts/Case149.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart149
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 0 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![]
noncomputable def U0 : Fin 2 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![X (none), X (some (0 : Fin 1))]
noncomputable def R0 : Fin 0 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![]

noncomputable def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart149
end

/- Source: ChartTables/Case149.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart149
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 1)) :=
  ![![.one, .one, .one, .one], ![.one, .variable (none), .zero, .variable (some (0 : Fin 1))], ![.zero, .zero, .one, .zero], ![.zero, .zero, .zero, .one]]

noncomputable def chartPositions : (Option (Fin 1)) → Coordinate × Coordinate :=
  Option.elim' (1, 1) ![(1, 3)]

noncomputable def chartUnitVariables : Fin 2 → (Option (Fin 1)) :=
  ![none, some (0 : Fin 1)]

noncomputable def chartLabelCode : ℕ := 16100616

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, true, false, false, true, false, false, false, false, false, false, true, true, true, false, true, false, false, true, false, true, false, false, true, false, true, false, true, false, false, true, true, true, true, true, true, false, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, true, true, true, true, true, true, false, true, true, true, true, false, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, false, true, true, false, true, true, true, true, true, true, false, false, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, true, true, false, false, false, false, false, false, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, false, false, false, false, false, false, false, true, false, false, false, false, true, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 1)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 149)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 149) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    exact Fin.elim0 j
  · intro i hi
    fin_cases i
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (1 : Fin 70) = _
      rw [minorFormula_at_1]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (2 : Fin 70) = _
      rw [minorFormula_at_2]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (3 : Fin 70) = _
      rw [minorFormula_at_3]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (5 : Fin 70) = _
      rw [minorFormula_at_5]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (6 : Fin 70) = _
      rw [minorFormula_at_6]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (8 : Fin 70) = _
      rw [minorFormula_at_8]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (9 : Fin 70) = _
      rw [minorFormula_at_9]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (10 : Fin 70) = _
      rw [minorFormula_at_10]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (11 : Fin 70) = _
      rw [minorFormula_at_11]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (12 : Fin 70) = _
      rw [minorFormula_at_12]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (13 : Fin 70) = _
      rw [minorFormula_at_13]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (20 : Fin 70) = _
      rw [minorFormula_at_20]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (24 : Fin 70) = _
      rw [minorFormula_at_24]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (25 : Fin 70) = _
      rw [minorFormula_at_25]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (27 : Fin 70) = _
      rw [minorFormula_at_27]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (29 : Fin 70) = _
      rw [minorFormula_at_29]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (31 : Fin 70) = _
      rw [minorFormula_at_31]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (32 : Fin 70) = _
      rw [minorFormula_at_32]
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
      change minorFormula (fun r c => (chartEntries r c).polynomial) (39 : Fin 70) = _
      rw [minorFormula_at_39]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (40 : Fin 70) = _
      rw [minorFormula_at_40]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (42 : Fin 70) = _
      rw [minorFormula_at_42]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (45 : Fin 70) = _
      rw [minorFormula_at_45]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (47 : Fin 70) = _
      rw [minorFormula_at_47]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (49 : Fin 70) = _
      rw [minorFormula_at_49]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (51 : Fin 70) = _
      rw [minorFormula_at_51]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (52 : Fin 70) = _
      rw [minorFormula_at_52]
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (66 : Fin 70) = _
      rw [minorFormula_at_66]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(0,7),(4,1),(6,2),(7,3)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Fin 1)) 0 2
    (MatroidCatalogue.N8R4.family 149) where
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
    (MatroidCatalogue.N8R4.family 149) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart149
end

/- Source: Charts/Case150.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart150
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 0 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![]
noncomputable def U0 : Fin 1 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none)]
noncomputable def R0 : Fin 0 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![]

noncomputable def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart150
end

/- Source: ChartTables/Case150.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart150
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 0)) :=
  ![![.one, .one, .one, .zero], ![.one, .variable (none), .zero, .zero], ![.zero, .zero, .one, .one], ![.zero, .zero, .zero, .one]]

noncomputable def chartPositions : (Option (Fin 0)) → Coordinate × Coordinate :=
  Option.elim' (1, 1) ![]

noncomputable def chartUnitVariables : Fin 1 → (Option (Fin 0)) :=
  ![none]

noncomputable def chartLabelCode : ℕ := 16100616

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, true, false, false, true, true, false, false, false, false, false, true, true, true, false, false, false, false, true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, true, false, true, true, false, true, true, true, true, true, false, false, true, true, true, true, false, true, false, false, false, true, true, true, true, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, false, true, true, false, false, true, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, true, false, false, false, false, true, true, true, false, false, false, false, false, true, true, true, false, true, false, false, true, false, false, false, false, false, true, true, false, false, false, false, true, false, true, true, true, false, false, false, false, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 0)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 150)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 150) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    exact Fin.elim0 j
  · intro i hi
    fin_cases i
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (1 : Fin 70) = _
      rw [minorFormula_at_1]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (2 : Fin 70) = _
      rw [minorFormula_at_2]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (3 : Fin 70) = _
      rw [minorFormula_at_3]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (5 : Fin 70) = _
      rw [minorFormula_at_5]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (6 : Fin 70) = _
      rw [minorFormula_at_6]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (9 : Fin 70) = _
      rw [minorFormula_at_9]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (10 : Fin 70) = _
      rw [minorFormula_at_10]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (11 : Fin 70) = _
      rw [minorFormula_at_11]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (12 : Fin 70) = _
      rw [minorFormula_at_12]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (13 : Fin 70) = _
      rw [minorFormula_at_13]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (17 : Fin 70) = _
      rw [minorFormula_at_17]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (18 : Fin 70) = _
      rw [minorFormula_at_18]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (20 : Fin 70) = _
      rw [minorFormula_at_20]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (24 : Fin 70) = _
      rw [minorFormula_at_24]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (25 : Fin 70) = _
      rw [minorFormula_at_25]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (30 : Fin 70) = _
      rw [minorFormula_at_30]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (31 : Fin 70) = _
      rw [minorFormula_at_31]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (32 : Fin 70) = _
      rw [minorFormula_at_32]
      dsimp [
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (39 : Fin 70) = _
      rw [minorFormula_at_39]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (40 : Fin 70) = _
      rw [minorFormula_at_40]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (42 : Fin 70) = _
      rw [minorFormula_at_42]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (45 : Fin 70) = _
      rw [minorFormula_at_45]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (51 : Fin 70) = _
      rw [minorFormula_at_51]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (52 : Fin 70) = _
      rw [minorFormula_at_52]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (57 : Fin 70) = _
      rw [minorFormula_at_57]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (59 : Fin 70) = _
      rw [minorFormula_at_59]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (60 : Fin 70) = _
      rw [minorFormula_at_60]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
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

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(4,1),(6,2),(2,7),(7,3)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Fin 0)) 0 1
    (MatroidCatalogue.N8R4.family 150) where
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
    (MatroidCatalogue.N8R4.family 150) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart150
end

/- Source: Charts/Case151.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart151
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 0 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![]
noncomputable def U0 : Fin 2 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![X (none), X (some (0 : Fin 1))]
noncomputable def R0 : Fin 0 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![]

noncomputable def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart151
end

/- Source: ChartTables/Case151.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart151
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 1)) :=
  ![![.one, .one, .one, .one], ![.one, .variable (none), .zero, .zero], ![.zero, .zero, .one, .variable (some (0 : Fin 1))], ![.zero, .zero, .zero, .one]]

noncomputable def chartPositions : (Option (Fin 1)) → Coordinate × Coordinate :=
  Option.elim' (1, 1) ![(2, 3)]

noncomputable def chartUnitVariables : Fin 2 → (Option (Fin 1)) :=
  ![none, some (0 : Fin 1)]

noncomputable def chartLabelCode : ℕ := 16100616

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, true, false, false, true, true, false, false, false, false, false, true, true, true, false, false, false, false, true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, true, false, false, true, false, true, true, false, true, true, true, true, true, false, false, true, true, true, true, true, true, true, false, false, true, true, true, true, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, false, true, true, false, false, true, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, true, false, false, false, false, true, true, true, false, false, false, false, false, false, true, true, false, true, false, false, true, false, false, false, false, false, true, true, false, false, false, false, false, false, false, true, true, false, false, false, false, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 1)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 151)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 151) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    exact Fin.elim0 j
  · intro i hi
    fin_cases i
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (1 : Fin 70) = _
      rw [minorFormula_at_1]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (2 : Fin 70) = _
      rw [minorFormula_at_2]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (3 : Fin 70) = _
      rw [minorFormula_at_3]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (5 : Fin 70) = _
      rw [minorFormula_at_5]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (6 : Fin 70) = _
      rw [minorFormula_at_6]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (9 : Fin 70) = _
      rw [minorFormula_at_9]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (10 : Fin 70) = _
      rw [minorFormula_at_10]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (11 : Fin 70) = _
      rw [minorFormula_at_11]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (12 : Fin 70) = _
      rw [minorFormula_at_12]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (13 : Fin 70) = _
      rw [minorFormula_at_13]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (17 : Fin 70) = _
      rw [minorFormula_at_17]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (18 : Fin 70) = _
      rw [minorFormula_at_18]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (20 : Fin 70) = _
      rw [minorFormula_at_20]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (24 : Fin 70) = _
      rw [minorFormula_at_24]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (25 : Fin 70) = _
      rw [minorFormula_at_25]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (30 : Fin 70) = _
      rw [minorFormula_at_30]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (31 : Fin 70) = _
      rw [minorFormula_at_31]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (32 : Fin 70) = _
      rw [minorFormula_at_32]
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
      change minorFormula (fun r c => (chartEntries r c).polynomial) (39 : Fin 70) = _
      rw [minorFormula_at_39]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (40 : Fin 70) = _
      rw [minorFormula_at_40]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (42 : Fin 70) = _
      rw [minorFormula_at_42]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (45 : Fin 70) = _
      rw [minorFormula_at_45]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (51 : Fin 70) = _
      rw [minorFormula_at_51]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (52 : Fin 70) = _
      rw [minorFormula_at_52]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (60 : Fin 70) = _
      rw [minorFormula_at_60]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
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

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(0,7),(4,1),(6,2),(7,3)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Fin 1)) 0 2
    (MatroidCatalogue.N8R4.family 151) where
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
    (MatroidCatalogue.N8R4.family 151) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart151
end

/- Source: Charts/Case152.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart152
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 1 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (none) + (1)]
noncomputable def U0 : Fin 2 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (some (none)), X (none)]
noncomputable def R0 : Fin 1 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (none) + (1)]

noncomputable def reductions0 (j : Fin 1) : FactorReduction U0 (E0 j) (R0 j) := by
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
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring

noncomputable def nextE0 : Fin 1 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0]
noncomputable def nextU0 : Fin 2 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none), -(1)]

noncomputable def step0 : LinearStep (Option (Fin 0)) 1 2 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := 1
  b := 1
  pivot := 0
  pivot_identity := by simp [R0]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1]
  equation_quotient := ![1]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![0, 1]
  unit_quotient := ![0, 1]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 1 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0]
noncomputable def U1 : Fin 2 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none), -(1)]
noncomputable def R1 : Fin 1 → MvPolynomial (Option (Fin 0)) ℚ :=
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
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
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

end Papers.RationalityTen.Chart152
end

/- Source: ChartTables/Case152.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart152
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Fin 0))) :=
  ![![.one, .one, .one, .zero], ![.one, .variable (some (none)), .zero, .one], ![.zero, .zero, .one, .variable (none)], ![.zero, .zero, .zero, .one]]

noncomputable def chartPositions : (Option (Option (Fin 0))) → Coordinate × Coordinate :=
  Option.elim' (2, 3) (Option.elim' (1, 1) ![])

noncomputable def chartUnitVariables : Fin 2 → (Option (Option (Fin 0))) :=
  ![some (none), none]

noncomputable def chartLabelCode : ℕ := 16100616

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, true, false, false, true, true, false, false, false, false, false, true, true, true, false, true, false, false, true, false, true, false, false, true, true, true, true, true, false, false, true, true, true, true, true, false, false, false, true, false, true, true, false, true, true, true, true, true, false, false, true, true, true, true, true, true, true, true, false, true, true, true, true, true, false, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, false, true, true, false, false, true, true, true, true, true, false, false, false, true, false, true, true, false, true, false, true, true, false, false, false, false, false, true, true, false, false, false, false, false, true, true, true, false, true, false, false, true, false, false, false, false, false, true, true, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 152)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 152) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨67, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (67 : Fin 70)
      rw [minorFormula_at_67]
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (2 : Fin 70) = _
      rw [minorFormula_at_2]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (3 : Fin 70) = _
      rw [minorFormula_at_3]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (5 : Fin 70) = _
      rw [minorFormula_at_5]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (6 : Fin 70) = _
      rw [minorFormula_at_6]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (9 : Fin 70) = _
      rw [minorFormula_at_9]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (10 : Fin 70) = _
      rw [minorFormula_at_10]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (11 : Fin 70) = _
      rw [minorFormula_at_11]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (12 : Fin 70) = _
      rw [minorFormula_at_12]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (13 : Fin 70) = _
      rw [minorFormula_at_13]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (20 : Fin 70) = _
      rw [minorFormula_at_20]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (24 : Fin 70) = _
      rw [minorFormula_at_24]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (25 : Fin 70) = _
      rw [minorFormula_at_25]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (31 : Fin 70) = _
      rw [minorFormula_at_31]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (32 : Fin 70) = _
      rw [minorFormula_at_32]
      dsimp [
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (39 : Fin 70) = _
      rw [minorFormula_at_39]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (40 : Fin 70) = _
      rw [minorFormula_at_40]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (42 : Fin 70) = _
      rw [minorFormula_at_42]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (45 : Fin 70) = _
      rw [minorFormula_at_45]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (51 : Fin 70) = _
      rw [minorFormula_at_51]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (52 : Fin 70) = _
      rw [minorFormula_at_52]
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (67 : Fin 70)
      rw [minorFormula_at_67]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(4,1),(6,2),(1,7),(7,3)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Option (Fin 0))) 1 2
    (MatroidCatalogue.N8R4.family 152) where
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
    (MatroidCatalogue.N8R4.family 152) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart152
end

/- Source: Charts/Case153.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart153
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 0 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![]
noncomputable def U0 : Fin 2 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![X (none), X (some (0 : Fin 1))]
noncomputable def R0 : Fin 0 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![]

noncomputable def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart153
end

/- Source: ChartTables/Case153.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart153
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 1)) :=
  ![![.one, .one, .one, .zero], ![.one, .variable (none), .zero, .one], ![.zero, .zero, .one, .variable (some (0 : Fin 1))], ![.zero, .zero, .zero, .one]]

noncomputable def chartPositions : (Option (Fin 1)) → Coordinate × Coordinate :=
  Option.elim' (1, 1) ![(2, 3)]

noncomputable def chartUnitVariables : Fin 2 → (Option (Fin 1)) :=
  ![none, some (0 : Fin 1)]

noncomputable def chartLabelCode : ℕ := 16100616

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, true, false, false, true, true, false, false, false, false, false, true, true, true, false, true, false, false, true, false, true, false, false, true, true, true, true, true, false, false, true, true, true, true, true, false, false, false, true, false, true, true, false, true, true, true, true, true, false, false, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, false, true, true, false, false, true, true, true, true, true, false, false, false, true, false, true, true, false, true, false, true, true, false, false, false, false, false, true, true, false, false, false, false, false, true, true, true, false, true, false, false, true, false, false, false, false, false, true, true, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 1)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 153)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 153) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    exact Fin.elim0 j
  · intro i hi
    fin_cases i
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (1 : Fin 70) = _
      rw [minorFormula_at_1]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (2 : Fin 70) = _
      rw [minorFormula_at_2]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (3 : Fin 70) = _
      rw [minorFormula_at_3]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (5 : Fin 70) = _
      rw [minorFormula_at_5]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (6 : Fin 70) = _
      rw [minorFormula_at_6]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (9 : Fin 70) = _
      rw [minorFormula_at_9]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (10 : Fin 70) = _
      rw [minorFormula_at_10]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (11 : Fin 70) = _
      rw [minorFormula_at_11]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (12 : Fin 70) = _
      rw [minorFormula_at_12]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (13 : Fin 70) = _
      rw [minorFormula_at_13]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (20 : Fin 70) = _
      rw [minorFormula_at_20]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (24 : Fin 70) = _
      rw [minorFormula_at_24]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (25 : Fin 70) = _
      rw [minorFormula_at_25]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (31 : Fin 70) = _
      rw [minorFormula_at_31]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (32 : Fin 70) = _
      rw [minorFormula_at_32]
      dsimp [
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (39 : Fin 70) = _
      rw [minorFormula_at_39]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (40 : Fin 70) = _
      rw [minorFormula_at_40]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (42 : Fin 70) = _
      rw [minorFormula_at_42]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (45 : Fin 70) = _
      rw [minorFormula_at_45]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (51 : Fin 70) = _
      rw [minorFormula_at_51]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (52 : Fin 70) = _
      rw [minorFormula_at_52]
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
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

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(4,1),(6,2),(1,7),(7,3)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Fin 1)) 0 2
    (MatroidCatalogue.N8R4.family 153) where
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
    (MatroidCatalogue.N8R4.family 153) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart153
end

/- Source: Charts/Case154.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart154
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 0 → MvPolynomial (Option (Fin 2)) ℚ :=
  ![]
noncomputable def U0 : Fin 3 → MvPolynomial (Option (Fin 2)) ℚ :=
  ![X (none), X (some (0 : Fin 2)), X (some (1 : Fin 2))]
noncomputable def R0 : Fin 0 → MvPolynomial (Option (Fin 2)) ℚ :=
  ![]

noncomputable def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart154
end

/- Source: ChartTables/Case154.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart154
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 2)) :=
  ![![.one, .one, .one, .one], ![.one, .variable (none), .zero, .variable (some (0 : Fin 2))], ![.zero, .zero, .one, .variable (some (1 : Fin 2))], ![.zero, .zero, .zero, .one]]

noncomputable def chartPositions : (Option (Fin 2)) → Coordinate × Coordinate :=
  Option.elim' (1, 1) ![(1, 3), (2, 3)]

noncomputable def chartUnitVariables : Fin 3 → (Option (Fin 2)) :=
  ![none, some (0 : Fin 2), some (1 : Fin 2)]

noncomputable def chartLabelCode : ℕ := 16100616

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, true, false, false, true, true, false, false, false, false, false, true, true, true, false, true, false, false, true, false, true, false, false, true, true, true, true, true, false, false, true, true, true, true, true, true, false, false, true, false, true, true, false, true, true, true, true, true, false, false, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, false, true, true, false, false, true, true, true, true, true, false, false, false, true, false, true, true, false, true, false, true, true, false, false, false, false, false, true, true, false, false, false, false, false, false, true, true, false, true, false, false, true, false, false, false, false, false, true, true, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 2)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 154)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 154) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    exact Fin.elim0 j
  · intro i hi
    fin_cases i
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (1 : Fin 70) = _
      rw [minorFormula_at_1]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (2 : Fin 70) = _
      rw [minorFormula_at_2]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (3 : Fin 70) = _
      rw [minorFormula_at_3]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (5 : Fin 70) = _
      rw [minorFormula_at_5]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (6 : Fin 70) = _
      rw [minorFormula_at_6]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (9 : Fin 70) = _
      rw [minorFormula_at_9]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (10 : Fin 70) = _
      rw [minorFormula_at_10]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (11 : Fin 70) = _
      rw [minorFormula_at_11]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (12 : Fin 70) = _
      rw [minorFormula_at_12]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (13 : Fin 70) = _
      rw [minorFormula_at_13]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (20 : Fin 70) = _
      rw [minorFormula_at_20]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (24 : Fin 70) = _
      rw [minorFormula_at_24]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (25 : Fin 70) = _
      rw [minorFormula_at_25]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (31 : Fin 70) = _
      rw [minorFormula_at_31]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (32 : Fin 70) = _
      rw [minorFormula_at_32]
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
      change minorFormula (fun r c => (chartEntries r c).polynomial) (39 : Fin 70) = _
      rw [minorFormula_at_39]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (40 : Fin 70) = _
      rw [minorFormula_at_40]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (42 : Fin 70) = _
      rw [minorFormula_at_42]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (45 : Fin 70) = _
      rw [minorFormula_at_45]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (51 : Fin 70) = _
      rw [minorFormula_at_51]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (52 : Fin 70) = _
      rw [minorFormula_at_52]
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
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

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(0,7),(4,1),(6,2),(7,3)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Fin 2)) 0 3
    (MatroidCatalogue.N8R4.family 154) where
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
    (MatroidCatalogue.N8R4.family 154) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart154
end

/- Source: Charts/Case155.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart155
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 1 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![-(X (none)) + (X (some (some (0 : Fin 1))))]
noncomputable def U0 : Fin 3 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![X (some (none)), X (none), X (some (some (0 : Fin 1)))]
noncomputable def R0 : Fin 1 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![X (none) - (X (some (some (0 : Fin 1))))]

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
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring

noncomputable def nextE0 : Fin 1 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![0]
noncomputable def nextU0 : Fin 3 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![X (none), X (some (0 : Fin 1)), X (some (0 : Fin 1))]

noncomputable def step0 : LinearStep (Option (Fin 1)) 1 3 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := 1
  b := -(X (some (0 : Fin 1)))
  pivot := 0
  pivot_identity := by simp [R0]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1]
  equation_quotient := ![1]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![0, 1, 0]
  unit_quotient := ![0, 1, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 1 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![0]
noncomputable def U1 : Fin 3 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![X (none), X (some (0 : Fin 1)), X (some (0 : Fin 1))]
noncomputable def R1 : Fin 1 → MvPolynomial (Option (Fin 1)) ℚ :=
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
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
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

end Papers.RationalityTen.Chart155
end

/- Source: ChartTables/Case155.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart155
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Fin 1))) :=
  ![![.one, .one, .one, .one], ![.one, .variable (some (none)), .variable (none), .variable (some (some (0 : Fin 1)))], ![.zero, .zero, .one, .zero], ![.zero, .zero, .zero, .one]]

noncomputable def chartPositions : (Option (Option (Fin 1))) → Coordinate × Coordinate :=
  Option.elim' (1, 2) (Option.elim' (1, 1) ![(1, 3)])

noncomputable def chartUnitVariables : Fin 3 → (Option (Option (Fin 1))) :=
  ![some (none), none, some (some (0 : Fin 1))]

noncomputable def chartLabelCode : ℕ := 16100616

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, true, false, false, true, false, false, false, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, true, true, true, true, false, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, true, true, true, true, true, false, false, true, true, true, true, false, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, false, true, true, false, true, true, true, true, true, true, false, false, false, false, false, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, false, false, false, false, false, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, false, false, false, false, false, false, true, true, false, false, false, false, true, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 155)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 155) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨60, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (60 : Fin 70)
      rw [minorFormula_at_60]
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (2 : Fin 70) = _
      rw [minorFormula_at_2]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (3 : Fin 70) = _
      rw [minorFormula_at_3]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (5 : Fin 70) = _
      rw [minorFormula_at_5]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (6 : Fin 70) = _
      rw [minorFormula_at_6]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (8 : Fin 70) = _
      rw [minorFormula_at_8]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (9 : Fin 70) = _
      rw [minorFormula_at_9]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (10 : Fin 70) = _
      rw [minorFormula_at_10]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (11 : Fin 70) = _
      rw [minorFormula_at_11]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (12 : Fin 70) = _
      rw [minorFormula_at_12]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (13 : Fin 70) = _
      rw [minorFormula_at_13]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (20 : Fin 70) = _
      rw [minorFormula_at_20]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (25 : Fin 70) = _
      rw [minorFormula_at_25]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (27 : Fin 70) = _
      rw [minorFormula_at_27]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (29 : Fin 70) = _
      rw [minorFormula_at_29]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (31 : Fin 70) = _
      rw [minorFormula_at_31]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (32 : Fin 70) = _
      rw [minorFormula_at_32]
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
      change minorFormula (fun r c => (chartEntries r c).polynomial) (39 : Fin 70) = _
      rw [minorFormula_at_39]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (40 : Fin 70) = _
      rw [minorFormula_at_40]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (42 : Fin 70) = _
      rw [minorFormula_at_42]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (45 : Fin 70) = _
      rw [minorFormula_at_45]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (47 : Fin 70) = _
      rw [minorFormula_at_47]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (49 : Fin 70) = _
      rw [minorFormula_at_49]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (51 : Fin 70) = _
      rw [minorFormula_at_51]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (52 : Fin 70) = _
      rw [minorFormula_at_52]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (60 : Fin 70)
      rw [minorFormula_at_60]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (66 : Fin 70) = _
      rw [minorFormula_at_66]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(0,7),(4,1),(6,2),(7,3)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Option (Fin 1))) 1 3
    (MatroidCatalogue.N8R4.family 155) where
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
    (MatroidCatalogue.N8R4.family 155) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart155
end

/- Source: Charts/Case156.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart156
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 0 → MvPolynomial (Option (Fin 2)) ℚ :=
  ![]
noncomputable def U0 : Fin 3 → MvPolynomial (Option (Fin 2)) ℚ :=
  ![X (none), X (some (0 : Fin 2)), X (some (1 : Fin 2))]
noncomputable def R0 : Fin 0 → MvPolynomial (Option (Fin 2)) ℚ :=
  ![]

noncomputable def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart156
end

/- Source: ChartTables/Case156.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart156
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 2)) :=
  ![![.one, .one, .one, .one], ![.one, .variable (none), .variable (some (0 : Fin 2)), .variable (some (1 : Fin 2))], ![.zero, .zero, .one, .zero], ![.zero, .zero, .zero, .one]]

noncomputable def chartPositions : (Option (Fin 2)) → Coordinate × Coordinate :=
  Option.elim' (1, 1) ![(1, 2), (1, 3)]

noncomputable def chartUnitVariables : Fin 3 → (Option (Fin 2)) :=
  ![none, some (0 : Fin 2), some (1 : Fin 2)]

noncomputable def chartLabelCode : ℕ := 16100616

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, true, false, false, true, false, false, false, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, true, true, true, true, false, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, true, true, true, true, true, true, false, true, true, true, true, false, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, false, true, true, false, true, true, true, true, true, true, false, false, false, false, false, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, false, false, false, false, false, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, false, false, false, false, false, false, false, true, false, false, false, false, true, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 2)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 156)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 156) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    exact Fin.elim0 j
  · intro i hi
    fin_cases i
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (1 : Fin 70) = _
      rw [minorFormula_at_1]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (2 : Fin 70) = _
      rw [minorFormula_at_2]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (3 : Fin 70) = _
      rw [minorFormula_at_3]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (5 : Fin 70) = _
      rw [minorFormula_at_5]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (6 : Fin 70) = _
      rw [minorFormula_at_6]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (8 : Fin 70) = _
      rw [minorFormula_at_8]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (9 : Fin 70) = _
      rw [minorFormula_at_9]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (10 : Fin 70) = _
      rw [minorFormula_at_10]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (11 : Fin 70) = _
      rw [minorFormula_at_11]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (12 : Fin 70) = _
      rw [minorFormula_at_12]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (13 : Fin 70) = _
      rw [minorFormula_at_13]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (20 : Fin 70) = _
      rw [minorFormula_at_20]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (25 : Fin 70) = _
      rw [minorFormula_at_25]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (27 : Fin 70) = _
      rw [minorFormula_at_27]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (29 : Fin 70) = _
      rw [minorFormula_at_29]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (31 : Fin 70) = _
      rw [minorFormula_at_31]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (32 : Fin 70) = _
      rw [minorFormula_at_32]
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
      change minorFormula (fun r c => (chartEntries r c).polynomial) (39 : Fin 70) = _
      rw [minorFormula_at_39]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (40 : Fin 70) = _
      rw [minorFormula_at_40]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (42 : Fin 70) = _
      rw [minorFormula_at_42]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (45 : Fin 70) = _
      rw [minorFormula_at_45]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (47 : Fin 70) = _
      rw [minorFormula_at_47]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (49 : Fin 70) = _
      rw [minorFormula_at_49]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (51 : Fin 70) = _
      rw [minorFormula_at_51]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (52 : Fin 70) = _
      rw [minorFormula_at_52]
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (66 : Fin 70) = _
      rw [minorFormula_at_66]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(0,7),(4,1),(6,2),(7,3)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Fin 2)) 0 3
    (MatroidCatalogue.N8R4.family 156) where
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
    (MatroidCatalogue.N8R4.family 156) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart156
end

/- Source: Charts/Case157.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart157
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 0 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![]
noncomputable def U0 : Fin 2 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![X (none), X (some (0 : Fin 1))]
noncomputable def R0 : Fin 0 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![]

noncomputable def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart157
end

/- Source: ChartTables/Case157.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart157
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 1)) :=
  ![![.one, .one, .one, .zero], ![.one, .variable (none), .variable (some (0 : Fin 1)), .zero], ![.zero, .zero, .one, .one], ![.zero, .zero, .zero, .one]]

noncomputable def chartPositions : (Option (Fin 1)) → Coordinate × Coordinate :=
  Option.elim' (1, 1) ![(1, 2)]

noncomputable def chartUnitVariables : Fin 2 → (Option (Fin 1)) :=
  ![none, some (0 : Fin 1)]

noncomputable def chartLabelCode : ℕ := 16100616

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, true, false, false, true, true, false, false, false, false, false, true, true, true, true, false, false, false, true, false, true, true, false, true, true, true, true, true, false, false, true, true, true, true, true, false, false, false, true, false, true, true, false, true, true, true, true, true, false, false, true, true, true, true, false, true, false, false, false, true, true, true, true, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, false, true, true, false, false, true, true, true, true, true, false, false, false, false, true, true, true, false, true, false, false, true, false, false, false, false, false, true, true, false, false, false, false, false, true, true, true, false, true, false, false, true, false, false, false, false, false, true, true, false, false, false, false, true, false, true, true, true, false, false, false, false, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 1)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 157)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 157) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    exact Fin.elim0 j
  · intro i hi
    fin_cases i
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (1 : Fin 70) = _
      rw [minorFormula_at_1]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (2 : Fin 70) = _
      rw [minorFormula_at_2]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (3 : Fin 70) = _
      rw [minorFormula_at_3]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (5 : Fin 70) = _
      rw [minorFormula_at_5]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (6 : Fin 70) = _
      rw [minorFormula_at_6]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (9 : Fin 70) = _
      rw [minorFormula_at_9]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (10 : Fin 70) = _
      rw [minorFormula_at_10]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (11 : Fin 70) = _
      rw [minorFormula_at_11]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (12 : Fin 70) = _
      rw [minorFormula_at_12]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (13 : Fin 70) = _
      rw [minorFormula_at_13]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (18 : Fin 70) = _
      rw [minorFormula_at_18]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (20 : Fin 70) = _
      rw [minorFormula_at_20]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (25 : Fin 70) = _
      rw [minorFormula_at_25]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (31 : Fin 70) = _
      rw [minorFormula_at_31]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (32 : Fin 70) = _
      rw [minorFormula_at_32]
      dsimp [
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (39 : Fin 70) = _
      rw [minorFormula_at_39]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (40 : Fin 70) = _
      rw [minorFormula_at_40]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (42 : Fin 70) = _
      rw [minorFormula_at_42]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (45 : Fin 70) = _
      rw [minorFormula_at_45]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (51 : Fin 70) = _
      rw [minorFormula_at_51]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (52 : Fin 70) = _
      rw [minorFormula_at_52]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (57 : Fin 70) = _
      rw [minorFormula_at_57]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (59 : Fin 70) = _
      rw [minorFormula_at_59]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (60 : Fin 70) = _
      rw [minorFormula_at_60]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
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

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(4,1),(6,2),(2,7),(7,3)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Fin 1)) 0 2
    (MatroidCatalogue.N8R4.family 157) where
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
    (MatroidCatalogue.N8R4.family 157) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart157
end

/- Source: Charts/Case158.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart158
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 1 → MvPolynomial (Option (Option (Fin 2))) ℚ :=
  ![-(X (none)) + (X (some (some (0 : Fin 2))))]
noncomputable def U0 : Fin 4 → MvPolynomial (Option (Option (Fin 2))) ℚ :=
  ![X (some (none)), X (none), X (some (some (0 : Fin 2))), X (some (some (1 : Fin 2)))]
noncomputable def R0 : Fin 1 → MvPolynomial (Option (Option (Fin 2))) ℚ :=
  ![X (none) - (X (some (some (0 : Fin 2))))]

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
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring

noncomputable def nextE0 : Fin 1 → MvPolynomial (Option (Fin 2)) ℚ :=
  ![0]
noncomputable def nextU0 : Fin 4 → MvPolynomial (Option (Fin 2)) ℚ :=
  ![X (none), X (some (0 : Fin 2)), X (some (0 : Fin 2)), X (some (1 : Fin 2))]

noncomputable def step0 : LinearStep (Option (Fin 2)) 1 4 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := 1
  b := -(X (some (0 : Fin 2)))
  pivot := 0
  pivot_identity := by simp [R0]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1]
  equation_quotient := ![1]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![0, 1, 0, 0]
  unit_quotient := ![0, 1, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 1 → MvPolynomial (Option (Fin 2)) ℚ :=
  ![0]
noncomputable def U1 : Fin 4 → MvPolynomial (Option (Fin 2)) ℚ :=
  ![X (none), X (some (0 : Fin 2)), X (some (0 : Fin 2)), X (some (1 : Fin 2))]
noncomputable def R1 : Fin 1 → MvPolynomial (Option (Fin 2)) ℚ :=
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
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
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

end Papers.RationalityTen.Chart158
end

/- Source: ChartTables/Case158.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart158
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Fin 2))) :=
  ![![.one, .one, .one, .one], ![.one, .variable (some (none)), .variable (none), .variable (some (some (0 : Fin 2)))], ![.zero, .zero, .one, .variable (some (some (1 : Fin 2)))], ![.zero, .zero, .zero, .one]]

noncomputable def chartPositions : (Option (Option (Fin 2))) → Coordinate × Coordinate :=
  Option.elim' (1, 2) (Option.elim' (1, 1) ![(1, 3), (2, 3)])

noncomputable def chartUnitVariables : Fin 4 → (Option (Option (Fin 2))) :=
  ![some (none), none, some (some (0 : Fin 2)), some (some (1 : Fin 2))]

noncomputable def chartLabelCode : ℕ := 16100616

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, true, false, false, true, true, false, false, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, true, true, true, true, true, false, false, true, true, true, true, true, true, false, false, true, false, true, true, false, true, true, true, true, true, false, false, true, true, true, true, true, true, true, false, false, true, true, true, true, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, false, true, true, false, false, true, true, true, true, true, false, false, false, false, false, true, true, false, true, false, false, true, false, false, false, false, false, true, true, false, false, false, false, false, false, true, true, false, true, false, false, true, false, false, false, false, false, true, true, false, false, false, false, false, false, false, true, true, false, false, false, false, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Fin 2))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 158)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 158) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨60, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (60 : Fin 70)
      rw [minorFormula_at_60]
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (2 : Fin 70) = _
      rw [minorFormula_at_2]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (3 : Fin 70) = _
      rw [minorFormula_at_3]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (5 : Fin 70) = _
      rw [minorFormula_at_5]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (6 : Fin 70) = _
      rw [minorFormula_at_6]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (9 : Fin 70) = _
      rw [minorFormula_at_9]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (10 : Fin 70) = _
      rw [minorFormula_at_10]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (11 : Fin 70) = _
      rw [minorFormula_at_11]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (12 : Fin 70) = _
      rw [minorFormula_at_12]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (13 : Fin 70) = _
      rw [minorFormula_at_13]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (20 : Fin 70) = _
      rw [minorFormula_at_20]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (25 : Fin 70) = _
      rw [minorFormula_at_25]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (31 : Fin 70) = _
      rw [minorFormula_at_31]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (32 : Fin 70) = _
      rw [minorFormula_at_32]
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
      change minorFormula (fun r c => (chartEntries r c).polynomial) (39 : Fin 70) = _
      rw [minorFormula_at_39]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (40 : Fin 70) = _
      rw [minorFormula_at_40]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (42 : Fin 70) = _
      rw [minorFormula_at_42]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (45 : Fin 70) = _
      rw [minorFormula_at_45]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (51 : Fin 70) = _
      rw [minorFormula_at_51]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (52 : Fin 70) = _
      rw [minorFormula_at_52]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (60 : Fin 70)
      rw [minorFormula_at_60]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
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

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(0,7),(4,1),(6,2),(7,3)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Option (Fin 2))) 1 4
    (MatroidCatalogue.N8R4.family 158) where
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
    (MatroidCatalogue.N8R4.family 158) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart158
end

/- Source: Charts/Case159.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart159
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 1 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![-(X (none)) + (1)]
noncomputable def U0 : Fin 3 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![X (some (none)), X (some (some (0 : Fin 1))), X (none)]
noncomputable def R0 : Fin 1 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![X (none) - (1)]

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
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring

noncomputable def nextE0 : Fin 1 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![0]
noncomputable def nextU0 : Fin 3 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![X (none), X (some (0 : Fin 1)), 1]

noncomputable def step0 : LinearStep (Option (Fin 1)) 1 3 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := 1
  b := -(1)
  pivot := 0
  pivot_identity := by simp [R0]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1]
  equation_quotient := ![1]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![0, 0, 1]
  unit_quotient := ![0, 0, 1]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 1 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![0]
noncomputable def U1 : Fin 3 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![X (none), X (some (0 : Fin 1)), 1]
noncomputable def R1 : Fin 1 → MvPolynomial (Option (Fin 1)) ℚ :=
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
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
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

end Papers.RationalityTen.Chart159
end

/- Source: ChartTables/Case159.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart159
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Fin 1))) :=
  ![![.one, .one, .one, .one], ![.one, .variable (some (none)), .variable (some (some (0 : Fin 1))), .zero], ![.zero, .zero, .one, .variable (none)], ![.zero, .zero, .zero, .one]]

noncomputable def chartPositions : (Option (Option (Fin 1))) → Coordinate × Coordinate :=
  Option.elim' (2, 3) (Option.elim' (1, 1) ![(1, 2)])

noncomputable def chartUnitVariables : Fin 3 → (Option (Option (Fin 1))) :=
  ![some (none), some (some (0 : Fin 1)), none]

noncomputable def chartLabelCode : ℕ := 16100616

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, true, false, false, true, true, false, false, false, false, false, true, true, true, true, false, false, false, true, false, true, true, false, true, true, true, true, true, false, false, true, true, true, true, true, true, false, false, true, false, true, true, false, true, true, true, true, false, false, false, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, false, true, true, false, false, true, true, true, true, true, false, false, false, false, true, true, true, false, true, false, false, true, false, false, false, false, false, true, true, false, false, false, false, false, false, true, true, false, true, false, false, true, false, false, false, false, true, true, true, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 159)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 159) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨50, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (50 : Fin 70)
      rw [minorFormula_at_50]
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (2 : Fin 70) = _
      rw [minorFormula_at_2]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (3 : Fin 70) = _
      rw [minorFormula_at_3]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (5 : Fin 70) = _
      rw [minorFormula_at_5]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (6 : Fin 70) = _
      rw [minorFormula_at_6]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (9 : Fin 70) = _
      rw [minorFormula_at_9]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (10 : Fin 70) = _
      rw [minorFormula_at_10]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (11 : Fin 70) = _
      rw [minorFormula_at_11]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (12 : Fin 70) = _
      rw [minorFormula_at_12]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (13 : Fin 70) = _
      rw [minorFormula_at_13]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (18 : Fin 70) = _
      rw [minorFormula_at_18]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (20 : Fin 70) = _
      rw [minorFormula_at_20]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (25 : Fin 70) = _
      rw [minorFormula_at_25]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (31 : Fin 70) = _
      rw [minorFormula_at_31]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (32 : Fin 70) = _
      rw [minorFormula_at_32]
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
      change minorFormula (fun r c => (chartEntries r c).polynomial) (39 : Fin 70) = _
      rw [minorFormula_at_39]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (40 : Fin 70) = _
      rw [minorFormula_at_40]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (42 : Fin 70) = _
      rw [minorFormula_at_42]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (45 : Fin 70) = _
      rw [minorFormula_at_45]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (50 : Fin 70)
      rw [minorFormula_at_50]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (51 : Fin 70) = _
      rw [minorFormula_at_51]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (52 : Fin 70) = _
      rw [minorFormula_at_52]
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
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

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(0,7),(4,1),(6,2),(7,3)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Option (Fin 1))) 1 3
    (MatroidCatalogue.N8R4.family 159) where
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
    (MatroidCatalogue.N8R4.family 159) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart159
end
