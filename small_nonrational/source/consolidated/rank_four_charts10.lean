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

/- Source: Charts/Case320.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart320
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
  pivot_identity := by simp [R0, map_ofNat]<;> ring
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

end Papers.RationalityTen.Chart320
end

/- Source: ChartTables/Case320.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart320
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Fin 0))) :=
  ![![.one, .one, .zero, .one], ![.one, .zero, .one, .zero], ![.zero, .one, .zero, .variable (some (none))], ![.zero, .zero, .one, .variable (none)]]

noncomputable def chartPositions : (Option (Option (Fin 0))) → Coordinate × Coordinate :=
  Option.elim' (3, 3) (Option.elim' (2, 3) ![])

noncomputable def chartUnitVariables : Fin 2 → (Option (Option (Fin 0))) :=
  ![some (none), none]

noncomputable def chartLabelCode : ℕ := 16434824

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, true, true, false, true, false, true, false, false, false, true, true, true, true, false, true, false, false, true, true, false, false, true, true, false, true, true, false, true, true, true, true, true, true, true, false, true, false, true, true, true, true, true, true, false, true, false, true, false, true, true, true, true, true, true, true, true, false, true, true, true, false, true, true, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, false, false, true, false, true, false, true, true, true, false, false, false, false, true, false, true, true, false, false, true, true, false, false, true, false, false, true, false, false, false, false, false, false, false, true, false, true, false, false, false, false, false, false, true, false, true, false, true, false, false, false, false, false, false, false, false, true, false, false, false, true, false, false, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 320)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 320) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨63, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (63 : Fin 70)
      rw [minorFormula_at_63]
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (5 : Fin 70) = _
      rw [minorFormula_at_5]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (7 : Fin 70) = _
      rw [minorFormula_at_7]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (23 : Fin 70) = _
      rw [minorFormula_at_23]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (26 : Fin 70) = _
      rw [minorFormula_at_26]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (29 : Fin 70) = _
      rw [minorFormula_at_29]
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (46 : Fin 70) = _
      rw [minorFormula_at_46]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (48 : Fin 70) = _
      rw [minorFormula_at_48]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (50 : Fin 70) = _
      rw [minorFormula_at_50]
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
      change minorFormula (fun r c => (chartEntries r c).polynomial) (59 : Fin 70) = _
      rw [minorFormula_at_59]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨0, ?_⟩
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
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,7),(4,1),(5,2),(1,6),(6,3)]

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
    (MatroidCatalogue.N8R4.family 320) where
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
    (MatroidCatalogue.N8R4.family 320) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart320
end

/- Source: Charts/Case321.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart321
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

end Papers.RationalityTen.Chart321
end

/- Source: ChartTables/Case321.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart321
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 1)) :=
  ![![.one, .one, .zero, .one], ![.zero, .one, .one, .zero], ![.zero, .zero, .one, .variable (none)], ![.one, .zero, .zero, .variable (some (0 : Fin 1))]]

noncomputable def chartPositions : (Option (Fin 1)) → Coordinate × Coordinate :=
  Option.elim' (2, 3) ![(3, 3)]

noncomputable def chartUnitVariables : Fin 2 → (Option (Fin 1)) :=
  ![none, some (0 : Fin 1)]

noncomputable def chartLabelCode : ℕ := 16434824

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, true, false, false, true, false, false, true, true, false, true, true, false, false, true, false, true, true, false, true, true, false, false, true, true, false, false, false, true, true, true, true, true, true, true, true, true, false, true, true, false, true, false, true, false, false, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, false, true, true, false, true, true, false, false, true, false, false, true, true, false, true, false, false, true, false, false, true, true, false, false, true, true, true, false, false, false, false, false, false, false, false, false, true, false, false, true, false, true, false, true, true, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 1)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 321)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 321) chartLabelCode chartEntries
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
    · simp [chartRequiredZero] at hi
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
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
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
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
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,7),(4,3),(5,1),(1,6),(6,2)]

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
    (MatroidCatalogue.N8R4.family 321) where
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
    (MatroidCatalogue.N8R4.family 321) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart321
end

/- Source: Charts/Case322.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart322
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 2 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![-(X (none)) + (X (some (some (none)))) + (1), X (none) + (X (some (none))) - (1)]
noncomputable def U0 : Fin 3 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none), X (some (none)), X (some (some (none)))]
noncomputable def R0 : Fin 2 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none) - (X (some (some (none)))) - (1), X (none) + (X (some (none))) - (1)]

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

noncomputable def nextE0 : Fin 2 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, X (none) + (X (some (none)))]
noncomputable def nextU0 : Fin 3 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (some (none)) + (1), X (none), X (some (none))]

noncomputable def step0 : LinearStep (Option (Option (Fin 0))) 2 3 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := 1
  b := -(X (some (none))) - (1)
  pivot := 0
  pivot_identity := by simp [R0, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1, 1]
  equation_quotient := ![1, 1]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![1, 0, 0]
  unit_quotient := ![1, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 2 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, X (none) + (X (some (none)))]
noncomputable def U1 : Fin 3 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (some (none)) + (1), X (none), X (some (none))]
noncomputable def R1 : Fin 2 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, X (none) + (X (some (none)))]

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

noncomputable def nextE1 : Fin 2 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0]
noncomputable def nextU1 : Fin 3 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none) + (1), -(X (none)), X (none)]

noncomputable def step1 : LinearStep (Option (Fin 0)) 2 3 where
  sourceE := R1
  sourceU := U1
  targetE := nextE1
  targetU := nextU1
  a := 1
  b := X (none)
  pivot := 1
  pivot_identity := by simp [R1, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 1]
  equation_quotient := ![0, 1]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring
  unit_power := ![0, 1, 0]
  unit_quotient := ![0, 1, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring

noncomputable def E2 : Fin 2 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0]
noncomputable def U2 : Fin 3 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none) + (1), -(X (none)), X (none)]
noncomputable def R2 : Fin 2 → MvPolynomial (Option (Fin 0)) ℚ :=
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

end Papers.RationalityTen.Chart322
end

/- Source: ChartTables/Case322.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart322
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Option (Fin 0)))) :=
  ![![.one, .zero, .one, .one], ![.one, .one, .zero, .variable (none)], ![.zero, .zero, .one, .variable (some (none))], ![.zero, .one, .zero, .variable (some (some (none)))]]

noncomputable def chartPositions : (Option (Option (Option (Fin 0)))) → Coordinate × Coordinate :=
  Option.elim' (1, 3) (Option.elim' (2, 3) (Option.elim' (3, 3) ![]))

noncomputable def chartUnitVariables : Fin 3 → (Option (Option (Option (Fin 0)))) :=
  ![none, some (none), some (some (none))]

noncomputable def chartLabelCode : ℕ := 16427208

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, true, false, true, false, false, true, true, false, false, false, true, true, true, true, true, false, true, true, false, true, false, true, false, false, true, true, true, true, true, true, true, true, true, true, false, true, true, true, false, true, true, true, true, false, true, true, false, false, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, false, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, false, true, false, true, true, false, false, true, true, true, false, false, false, false, false, true, false, false, true, false, true, false, true, true, false, false, false, false, false, false, false, false, false, false, true, false, false, false, true, false, false, false, false, true, false, false, true, true, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, true, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 322)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 322) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨62, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (62 : Fin 70)
      rw [minorFormula_at_62]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · simp [chartRequiredZero] at hi
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
    · simp [chartRequiredZero] at hi
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
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (40 : Fin 70) = _
      rw [minorFormula_at_40]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
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
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (62 : Fin 70)
      rw [minorFormula_at_62]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨1, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (67 : Fin 70)
      rw [minorFormula_at_67]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,6),(0,7),(4,1),(6,2),(1,5),(5,3)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Option (Option (Fin 0)))) 2 3
    (MatroidCatalogue.N8R4.family 322) where
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
    (MatroidCatalogue.N8R4.family 322) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart322
end

/- Source: Charts/Case323.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart323
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 1 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![X (none) - (1)]
noncomputable def U0 : Fin 3 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![X (none), X (some (none)), X (some (some (0 : Fin 1)))]
noncomputable def R0 : Fin 1 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
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

noncomputable def nextE0 : Fin 1 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![0]
noncomputable def nextU0 : Fin 3 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![1, X (none), X (some (0 : Fin 1))]

noncomputable def step0 : LinearStep (Option (Fin 1)) 1 3 where
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
  ![1, X (none), X (some (0 : Fin 1))]
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

end Papers.RationalityTen.Chart323
end

/- Source: ChartTables/Case323.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart323
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Fin 1))) :=
  ![![.one, .zero, .one, .one], ![.one, .one, .zero, .variable (none)], ![.zero, .zero, .one, .variable (some (none))], ![.zero, .one, .zero, .variable (some (some (0 : Fin 1)))]]

noncomputable def chartPositions : (Option (Option (Fin 1))) → Coordinate × Coordinate :=
  Option.elim' (1, 3) (Option.elim' (2, 3) ![(3, 3)])

noncomputable def chartUnitVariables : Fin 3 → (Option (Option (Fin 1))) :=
  ![none, some (none), some (some (0 : Fin 1))]

noncomputable def chartLabelCode : ℕ := 16427208

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, true, false, true, false, false, true, true, false, false, false, true, true, true, true, true, false, true, true, false, true, false, true, false, false, true, true, true, true, true, true, true, true, true, true, false, true, true, true, false, true, true, true, true, false, true, true, false, false, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, false, true, false, true, true, false, false, true, true, true, false, false, false, false, false, true, false, false, true, false, true, false, true, true, false, false, false, false, false, false, false, false, false, false, true, false, false, false, true, false, false, false, false, true, false, false, true, true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 323)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 323) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨57, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (57 : Fin 70)
      rw [minorFormula_at_57]
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
    · simp [chartRequiredZero] at hi
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
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (40 : Fin 70) = _
      rw [minorFormula_at_40]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (57 : Fin 70)
      rw [minorFormula_at_57]
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

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,6),(0,7),(4,1),(6,2),(1,5),(5,3)]

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
    (MatroidCatalogue.N8R4.family 323) where
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
    (MatroidCatalogue.N8R4.family 323) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart323
end

/- Source: Charts/Case324.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart324
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

end Papers.RationalityTen.Chart324
end

/- Source: ChartTables/Case324.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart324
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 2)) :=
  ![![.one, .zero, .one, .one], ![.one, .one, .zero, .variable (none)], ![.zero, .zero, .one, .variable (some (0 : Fin 2))], ![.zero, .one, .zero, .variable (some (1 : Fin 2))]]

noncomputable def chartPositions : (Option (Fin 2)) → Coordinate × Coordinate :=
  Option.elim' (1, 3) ![(2, 3), (3, 3)]

noncomputable def chartUnitVariables : Fin 3 → (Option (Fin 2)) :=
  ![none, some (0 : Fin 2), some (1 : Fin 2)]

noncomputable def chartLabelCode : ℕ := 16427208

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, true, false, true, false, false, true, true, false, false, false, true, true, true, true, true, false, true, true, false, true, false, true, false, false, true, true, true, true, true, true, true, true, true, true, false, true, true, true, false, true, true, true, true, false, true, true, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, false, true, false, true, true, false, false, true, true, true, false, false, false, false, false, true, false, false, true, false, true, false, true, true, false, false, false, false, false, false, false, false, false, false, true, false, false, false, true, false, false, false, false, true, false, false, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 2)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 324)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 324) chartLabelCode chartEntries
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
    · simp [chartRequiredZero] at hi
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
    · simp [chartRequiredZero] at hi
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
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (40 : Fin 70) = _
      rw [minorFormula_at_40]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
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
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,6),(0,7),(4,1),(6,2),(1,5),(5,3)]

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
    (MatroidCatalogue.N8R4.family 324) where
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
    (MatroidCatalogue.N8R4.family 324) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart324
end

/- Source: Charts/Case325.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart325
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 2 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![-(X (none) * X (some (some (none)))) + (X (none)) + (X (some (none))) - (1), X (none) - (1)]
noncomputable def U0 : Fin 3 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (some (none)), X (some (some (none))), X (none)]
noncomputable def R0 : Fin 2 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![-(X (none) * X (some (some (none)))) + (X (none)) + (X (some (none))) - (1), X (none) - (1)]

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

noncomputable def nextE0 : Fin 2 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (none) - (X (some (none))), 0]
noncomputable def nextU0 : Fin 3 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (none), X (some (none)), 1]

noncomputable def step0 : LinearStep (Option (Option (Fin 0))) 2 3 where
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
  equation_power := ![1, 1]
  equation_quotient := ![-(X (some (some (none)))) + (1), 1]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![0, 0, 1]
  unit_quotient := ![0, 0, 1]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 2 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (none) - (X (some (none))), 0]
noncomputable def U1 : Fin 3 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (none), X (some (none)), 1]
noncomputable def R1 : Fin 2 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (none) - (X (some (none))), 0]

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

noncomputable def nextE1 : Fin 2 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0]
noncomputable def nextU1 : Fin 3 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none), X (none), 1]

noncomputable def step1 : LinearStep (Option (Fin 0)) 2 3 where
  sourceE := R1
  sourceU := U1
  targetE := nextE1
  targetU := nextU1
  a := 1
  b := -(X (none))
  pivot := 0
  pivot_identity := by simp [R1, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1, 0]
  equation_quotient := ![1, 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring
  unit_power := ![1, 0, 0]
  unit_quotient := ![1, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring

noncomputable def E2 : Fin 2 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0]
noncomputable def U2 : Fin 3 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none), X (none), 1]
noncomputable def R2 : Fin 2 → MvPolynomial (Option (Fin 0)) ℚ :=
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

end Papers.RationalityTen.Chart325
end

/- Source: ChartTables/Case325.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart325
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Option (Fin 0)))) :=
  ![![.one, .one, .one, .one], ![.one, .zero, .zero, .variable (some (none))], ![.zero, .one, .variable (some (some (none))), .zero], ![.zero, .zero, .one, .variable (none)]]

noncomputable def chartPositions : (Option (Option (Option (Fin 0)))) → Coordinate × Coordinate :=
  Option.elim' (3, 3) (Option.elim' (1, 3) (Option.elim' (2, 2) ![]))

noncomputable def chartUnitVariables : Fin 3 → (Option (Option (Option (Fin 0)))) :=
  ![some (none), some (some (none)), none]

noncomputable def chartLabelCode : ℕ := 16394952

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, true, true, false, true, true, false, false, false, false, true, true, true, true, false, false, true, false, true, true, false, false, true, true, true, false, false, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, false, true, true, false, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, false]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, false, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, false, true, true, false, false, false, true, true, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, true, false, false, true, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, true]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 325)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 325) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨69, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (69 : Fin 70)
      rw [minorFormula_at_69]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨44, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (44 : Fin 70)
      rw [minorFormula_at_44]
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (23 : Fin 70) = _
      rw [minorFormula_at_23]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (27 : Fin 70) = _
      rw [minorFormula_at_27]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (28 : Fin 70) = _
      rw [minorFormula_at_28]
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (39 : Fin 70) = _
      rw [minorFormula_at_39]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨1, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (44 : Fin 70)
      rw [minorFormula_at_44]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (47 : Fin 70) = _
      rw [minorFormula_at_47]
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (58 : Fin 70) = _
      rw [minorFormula_at_58]
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
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (69 : Fin 70)
      rw [minorFormula_at_69]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(0,7),(4,1),(5,2),(6,3)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Option (Option (Fin 0)))) 2 3
    (MatroidCatalogue.N8R4.family 325) where
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
    (MatroidCatalogue.N8R4.family 325) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart325
end

/- Source: Charts/Case326.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart326
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 1 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![X (none) - (1)]
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
  pivot_identity := by simp [R0, map_ofNat]<;> ring
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

end Papers.RationalityTen.Chart326
end

/- Source: ChartTables/Case326.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart326
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Fin 1))) :=
  ![![.one, .one, .one, .one], ![.one, .zero, .zero, .variable (some (none))], ![.zero, .one, .variable (some (some (0 : Fin 1))), .zero], ![.zero, .zero, .one, .variable (none)]]

noncomputable def chartPositions : (Option (Option (Fin 1))) → Coordinate × Coordinate :=
  Option.elim' (3, 3) (Option.elim' (1, 3) ![(2, 2)])

noncomputable def chartUnitVariables : Fin 3 → (Option (Option (Fin 1))) :=
  ![some (none), some (some (0 : Fin 1)), none]

noncomputable def chartLabelCode : ℕ := 16398984

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, true, true, false, true, true, false, false, false, false, true, true, true, true, false, false, true, false, true, true, false, false, true, true, true, false, false, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, false, true, true, false, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, false, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, false, true, true, false, false, false, true, true, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, true, false, false, true, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 326)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 326) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨44, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (44 : Fin 70)
      rw [minorFormula_at_44]
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (23 : Fin 70) = _
      rw [minorFormula_at_23]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (27 : Fin 70) = _
      rw [minorFormula_at_27]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (28 : Fin 70) = _
      rw [minorFormula_at_28]
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (39 : Fin 70) = _
      rw [minorFormula_at_39]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (44 : Fin 70)
      rw [minorFormula_at_44]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (47 : Fin 70) = _
      rw [minorFormula_at_47]
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (58 : Fin 70) = _
      rw [minorFormula_at_58]
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

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(0,7),(4,1),(5,2),(6,3)]

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
    (MatroidCatalogue.N8R4.family 326) where
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
    (MatroidCatalogue.N8R4.family 326) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart326
end

/- Source: Charts/Case327.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart327
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

end Papers.RationalityTen.Chart327
end

/- Source: ChartTables/Case327.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart327
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 2)) :=
  ![![.one, .one, .one, .one], ![.one, .zero, .zero, .variable (none)], ![.zero, .one, .variable (some (0 : Fin 2)), .zero], ![.zero, .zero, .one, .variable (some (1 : Fin 2))]]

noncomputable def chartPositions : (Option (Fin 2)) → Coordinate × Coordinate :=
  Option.elim' (1, 3) ![(2, 2), (3, 3)]

noncomputable def chartUnitVariables : Fin 3 → (Option (Fin 2)) :=
  ![none, some (0 : Fin 2), some (1 : Fin 2)]

noncomputable def chartLabelCode : ℕ := 16394952

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, true, true, false, true, true, false, false, false, false, true, true, true, true, false, false, true, false, true, true, false, false, true, true, true, false, false, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, false, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, false, true, true, false, false, false, true, true, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 2)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 327)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 327) chartLabelCode chartEntries
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (23 : Fin 70) = _
      rw [minorFormula_at_23]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (27 : Fin 70) = _
      rw [minorFormula_at_27]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (28 : Fin 70) = _
      rw [minorFormula_at_28]
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (39 : Fin 70) = _
      rw [minorFormula_at_39]
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
      change minorFormula (fun r c => (chartEntries r c).polynomial) (47 : Fin 70) = _
      rw [minorFormula_at_47]
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (58 : Fin 70) = _
      rw [minorFormula_at_58]
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

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(0,7),(4,1),(5,2),(6,3)]

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
    (MatroidCatalogue.N8R4.family 327) where
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
    (MatroidCatalogue.N8R4.family 327) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart327
end

/- Source: Charts/Case328.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart328
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 2 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![-(X (none) * X (some (none))) - (1), X (none) * X (some (some (none))) - (X (some (some (none)))) - (1)]
noncomputable def U0 : Fin 3 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none), X (some (none)), X (some (some (none)))]
noncomputable def R0 : Fin 2 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none) * X (some (none)) + (1), X (none) * X (some (some (none))) - (X (some (some (none)))) - (1)]

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

noncomputable def nextE0 : Fin 2 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, -(X (none) * X (some (none))) - (X (none)) - (X (some (none)))]
noncomputable def nextU0 : Fin 3 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![-(1), X (none), X (some (none))]

noncomputable def step0 : LinearStep (Option (Option (Fin 0))) 2 3 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := X (none)
  b := 1
  pivot := 0
  pivot_identity := by simp [R0, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 1
      selected := ![1]
      quotient := 1
      identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1, 1]
  equation_quotient := ![X (some (none)), X (some (some (none)))]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![1, 0, 0]
  unit_quotient := ![1, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 2 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, -(X (none) * X (some (none))) - (X (none)) - (X (some (none)))]
noncomputable def U1 : Fin 3 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![-(1), X (none), X (some (none))]
noncomputable def R1 : Fin 2 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, X (none) * X (some (none)) + (X (none)) + (X (some (none)))]

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

noncomputable def nextE1 : Fin 2 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0]
noncomputable def nextU1 : Fin 3 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![-(1), -(X (none)), X (none)]

noncomputable def step1 : LinearStep (Option (Fin 0)) 2 3 where
  sourceE := R1
  sourceU := U1
  targetE := nextE1
  targetU := nextU1
  a := X (none) + (1)
  b := X (none)
  pivot := 1
  pivot_identity := by simp [R1, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inr {
      count := 1
      selected := ![2]
      quotient := 1
      identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 1]
  equation_quotient := ![0, X (some (none)) + (1)]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring
  unit_power := ![0, 1, 0]
  unit_quotient := ![0, 1, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring

noncomputable def E2 : Fin 2 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0]
noncomputable def U2 : Fin 3 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![-(1), -(X (none)), X (none)]
noncomputable def R2 : Fin 2 → MvPolynomial (Option (Fin 0)) ℚ :=
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

end Papers.RationalityTen.Chart328
end

/- Source: ChartTables/Case328.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart328
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Option (Fin 0)))) :=
  ![![.one, .one, .one, .zero], ![.one, .zero, .variable (none), .one], ![.zero, .one, .zero, .variable (some (none))], ![.zero, .zero, .one, .variable (some (some (none)))]]

noncomputable def chartPositions : (Option (Option (Option (Fin 0)))) → Coordinate × Coordinate :=
  Option.elim' (1, 2) (Option.elim' (2, 3) (Option.elim' (3, 3) ![]))

noncomputable def chartUnitVariables : Fin 3 → (Option (Option (Option (Fin 0)))) :=
  ![none, some (none), some (some (none))]

noncomputable def chartLabelCode : ℕ := 16133320

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, true, true, false, true, false, true, false, false, false, true, true, true, true, false, true, true, false, true, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, false, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, false, false, true, false, true, false, true, true, true, false, false, false, false, true, false, false, true, false, false, true, true, false, false, true, false, false, false, false, false, false, false, false, false, false, false, true, true, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, true, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 328)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 328) chartLabelCode chartEntries
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
    · refine ⟨63, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (63 : Fin 70)
      rw [minorFormula_at_63]
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (5 : Fin 70) = _
      rw [minorFormula_at_5]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (7 : Fin 70) = _
      rw [minorFormula_at_7]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (23 : Fin 70) = _
      rw [minorFormula_at_23]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (26 : Fin 70) = _
      rw [minorFormula_at_26]
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (46 : Fin 70) = _
      rw [minorFormula_at_46]
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
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (63 : Fin 70)
      rw [minorFormula_at_63]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(4,1),(5,2),(6,3),(1,7)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Option (Option (Fin 0)))) 2 3
    (MatroidCatalogue.N8R4.family 328) where
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
    (MatroidCatalogue.N8R4.family 328) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart328
end

/- Source: Charts/Case329.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart329
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 1 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![-(X (none) * X (some (none))) - (1)]
noncomputable def U0 : Fin 3 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![X (none), X (some (none)), X (some (some (0 : Fin 1)))]
noncomputable def R0 : Fin 1 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![X (none) * X (some (none)) + (1)]

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
  ![-(1), X (none), X (some (0 : Fin 1))]

noncomputable def step0 : LinearStep (Option (Fin 1)) 1 3 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := X (none)
  b := 1
  pivot := 0
  pivot_identity := by simp [R0, map_ofNat]<;> ring
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
  unit_power := ![1, 0, 0]
  unit_quotient := ![1, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 1 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![0]
noncomputable def U1 : Fin 3 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![-(1), X (none), X (some (0 : Fin 1))]
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

end Papers.RationalityTen.Chart329
end

/- Source: ChartTables/Case329.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart329
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Fin 1))) :=
  ![![.one, .one, .one, .zero], ![.one, .zero, .variable (none), .one], ![.zero, .one, .zero, .variable (some (none))], ![.zero, .zero, .one, .variable (some (some (0 : Fin 1)))]]

noncomputable def chartPositions : (Option (Option (Fin 1))) → Coordinate × Coordinate :=
  Option.elim' (1, 2) (Option.elim' (2, 3) ![(3, 3)])

noncomputable def chartUnitVariables : Fin 3 → (Option (Option (Fin 1))) :=
  ![none, some (none), some (some (0 : Fin 1))]

noncomputable def chartLabelCode : ℕ := 16394952

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, true, true, false, true, false, true, false, false, false, true, true, true, true, false, true, true, false, true, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, false, false, true, false, true, false, true, true, true, false, false, false, false, true, false, false, true, false, false, true, true, false, false, true, false, false, false, false, false, false, false, false, false, false, false, true, true, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 329)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 329) chartLabelCode chartEntries
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (5 : Fin 70) = _
      rw [minorFormula_at_5]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (7 : Fin 70) = _
      rw [minorFormula_at_7]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (23 : Fin 70) = _
      rw [minorFormula_at_23]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (26 : Fin 70) = _
      rw [minorFormula_at_26]
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (46 : Fin 70) = _
      rw [minorFormula_at_46]
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
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (68 : Fin 70)
      rw [minorFormula_at_68]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(4,1),(5,2),(6,3),(1,7)]

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
    (MatroidCatalogue.N8R4.family 329) where
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
    (MatroidCatalogue.N8R4.family 329) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart329
end

/- Source: Charts/Case330.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart330
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 1 → MvPolynomial (Option (Option (Fin 2))) ℚ :=
  ![-(X (none)) + (X (some (none)))]
noncomputable def U0 : Fin 4 → MvPolynomial (Option (Option (Fin 2))) ℚ :=
  ![X (none), X (some (none)), X (some (some (0 : Fin 2))), X (some (some (1 : Fin 2)))]
noncomputable def R0 : Fin 1 → MvPolynomial (Option (Option (Fin 2))) ℚ :=
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

noncomputable def nextE0 : Fin 1 → MvPolynomial (Option (Fin 2)) ℚ :=
  ![0]
noncomputable def nextU0 : Fin 4 → MvPolynomial (Option (Fin 2)) ℚ :=
  ![X (none), X (none), X (some (0 : Fin 2)), X (some (1 : Fin 2))]

noncomputable def step0 : LinearStep (Option (Fin 2)) 1 4 where
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
  equation_power := ![1]
  equation_quotient := ![1]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![1, 0, 0, 0]
  unit_quotient := ![1, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 1 → MvPolynomial (Option (Fin 2)) ℚ :=
  ![0]
noncomputable def U1 : Fin 4 → MvPolynomial (Option (Fin 2)) ℚ :=
  ![X (none), X (none), X (some (0 : Fin 2)), X (some (1 : Fin 2))]
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

end Papers.RationalityTen.Chart330
end

/- Source: ChartTables/Case330.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart330
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Fin 2))) :=
  ![![.one, .one, .one, .one], ![.one, .zero, .variable (none), .variable (some (none))], ![.zero, .one, .zero, .variable (some (some (0 : Fin 2)))], ![.zero, .zero, .one, .variable (some (some (1 : Fin 2)))]]

noncomputable def chartPositions : (Option (Option (Fin 2))) → Coordinate × Coordinate :=
  Option.elim' (1, 2) (Option.elim' (1, 3) ![(2, 3), (3, 3)])

noncomputable def chartUnitVariables : Fin 4 → (Option (Option (Fin 2))) :=
  ![none, some (none), some (some (0 : Fin 2)), some (some (1 : Fin 2))]

noncomputable def chartLabelCode : ℕ := 16394952

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, true, true, false, true, false, true, false, false, false, true, true, true, true, false, true, true, false, true, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, false, false, true, false, true, false, true, true, true, false, false, false, false, true, false, false, true, false, false, true, true, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Fin 2))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 330)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 330) chartLabelCode chartEntries
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (5 : Fin 70) = _
      rw [minorFormula_at_5]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (7 : Fin 70) = _
      rw [minorFormula_at_7]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (23 : Fin 70) = _
      rw [minorFormula_at_23]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (26 : Fin 70) = _
      rw [minorFormula_at_26]
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (39 : Fin 70) = _
      rw [minorFormula_at_39]
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
      change minorFormula (fun r c => (chartEntries r c).polynomial) (46 : Fin 70) = _
      rw [minorFormula_at_46]
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
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (60 : Fin 70)
      rw [minorFormula_at_60]
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

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(0,7),(4,1),(5,2),(6,3)]

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
    (MatroidCatalogue.N8R4.family 330) where
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
    (MatroidCatalogue.N8R4.family 330) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart330
end

/- Source: Charts/Case331.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart331
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 1 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![-(X (none) * X (some (some (0 : Fin 1)))) + (X (some (none))) + (X (some (some (0 : Fin 1)))) + (1)]
noncomputable def U0 : Fin 3 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![X (none), X (some (none)), X (some (some (0 : Fin 1)))]
noncomputable def R0 : Fin 1 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![X (none) * X (some (some (0 : Fin 1))) - (X (some (none))) - (X (some (some (0 : Fin 1)))) - (1)]

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
  ![X (none) + (X (some (0 : Fin 1))) + (1), X (none), X (some (0 : Fin 1))]

noncomputable def step0 : LinearStep (Option (Fin 1)) 1 3 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := X (some (0 : Fin 1))
  b := -(X (none)) - (X (some (0 : Fin 1))) - (1)
  pivot := 0
  pivot_identity := by simp [R0, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 1
      selected := ![2]
      quotient := 1
      identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1]
  equation_quotient := ![X (some (some (0 : Fin 1)))]
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
  ![X (none) + (X (some (0 : Fin 1))) + (1), X (none), X (some (0 : Fin 1))]
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

end Papers.RationalityTen.Chart331
end

/- Source: ChartTables/Case331.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart331
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Fin 1))) :=
  ![![.one, .one, .one, .zero], ![.one, .zero, .variable (none), .one], ![.zero, .one, .zero, .variable (some (none))], ![.zero, .zero, .one, .variable (some (some (0 : Fin 1)))]]

noncomputable def chartPositions : (Option (Option (Fin 1))) → Coordinate × Coordinate :=
  Option.elim' (1, 2) (Option.elim' (2, 3) ![(3, 3)])

noncomputable def chartUnitVariables : Fin 3 → (Option (Option (Fin 1))) :=
  ![none, some (none), some (some (0 : Fin 1))]

noncomputable def chartLabelCode : ℕ := 16133320

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, true, true, false, true, false, true, false, false, false, true, true, true, true, false, true, true, false, true, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, false, false, true, false, true, false, true, true, true, false, false, false, false, true, false, false, true, false, false, true, true, false, false, true, false, false, false, false, false, false, false, false, false, false, false, true, true, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 331)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 331) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨69, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (69 : Fin 70)
      rw [minorFormula_at_69]
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (5 : Fin 70) = _
      rw [minorFormula_at_5]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (7 : Fin 70) = _
      rw [minorFormula_at_7]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (23 : Fin 70) = _
      rw [minorFormula_at_23]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (26 : Fin 70) = _
      rw [minorFormula_at_26]
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (46 : Fin 70) = _
      rw [minorFormula_at_46]
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
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (69 : Fin 70)
      rw [minorFormula_at_69]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(4,1),(5,2),(6,3),(1,7)]

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
    (MatroidCatalogue.N8R4.family 331) where
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
    (MatroidCatalogue.N8R4.family 331) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart331
end

/- Source: Charts/Case332.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart332
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 3 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (some (none)) * X (some (some (none))) - (X (some (none))) - (1), X (none) + (1), X (none) + (X (some (none)))]
noncomputable def U0 : Fin 3 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (some (some (none))), X (none), X (some (none))]
noncomputable def R0 : Fin 3 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (some (none)) * X (some (some (none))) - (X (some (none))) - (1), X (none) + (1), X (none) + (X (some (none)))]

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

noncomputable def nextE0 : Fin 3 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (none) * X (some (none)) - (X (none)) - (1), 0, X (none) - (1)]
noncomputable def nextU0 : Fin 3 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (some (none)), -(1), X (none)]

noncomputable def step0 : LinearStep (Option (Option (Fin 0))) 3 3 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := 1
  b := 1
  pivot := 1
  pivot_identity := by simp [R0, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 1, 1]
  equation_quotient := ![0, 1, 1]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![0, 1, 0]
  unit_quotient := ![0, 1, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 3 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (none) * X (some (none)) - (X (none)) - (1), 0, X (none) - (1)]
noncomputable def U1 : Fin 3 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (some (none)), -(1), X (none)]
noncomputable def R1 : Fin 3 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (none) * X (some (none)) - (X (none)) - (1), 0, X (none) - (1)]

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

noncomputable def nextE1 : Fin 3 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none) - (2), 0, 0]
noncomputable def nextU1 : Fin 3 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none), -(1), 1]

noncomputable def step1 : LinearStep (Option (Fin 0)) 3 3 where
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
      identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1, 0, 1]
  equation_quotient := ![X (some (none)) - (1), 0, 1]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring
  unit_power := ![0, 0, 1]
  unit_quotient := ![0, 0, 1]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring

noncomputable def E2 : Fin 3 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none) - (2), 0, 0]
noncomputable def U2 : Fin 3 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none), -(1), 1]
noncomputable def R2 : Fin 3 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none) - (2), 0, 0]

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

noncomputable def nextE2 : Fin 3 → MvPolynomial (Fin 0) ℚ :=
  ![0, 0, 0]
noncomputable def nextU2 : Fin 3 → MvPolynomial (Fin 0) ℚ :=
  ![2, -(1), 1]

noncomputable def step2 : LinearStep (Fin 0) 3 3 where
  sourceE := R2
  sourceU := U2
  targetE := nextE2
  targetU := nextU2
  a := 1
  b := -(2)
  pivot := 0
  pivot_identity := by simp [R2, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1, 0, 0]
  equation_quotient := ![1, 0, 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring
  unit_power := ![1, 0, 0]
  unit_quotient := ![1, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring

noncomputable def E3 : Fin 3 → MvPolynomial (Fin 0) ℚ :=
  ![0, 0, 0]
noncomputable def U3 : Fin 3 → MvPolynomial (Fin 0) ℚ :=
  ![2, -(1), 1]
noncomputable def R3 : Fin 3 → MvPolynomial (Fin 0) ℚ :=
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

end Papers.RationalityTen.Chart332
end

/- Source: ChartTables/Case332.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart332
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Option (Fin 0)))) :=
  ![![.one, .one, .one, .zero], ![.one, .zero, .variable (some (some (none))), .one], ![.zero, .one, .zero, .variable (none)], ![.zero, .zero, .one, .variable (some (none))]]

noncomputable def chartPositions : (Option (Option (Option (Fin 0)))) → Coordinate × Coordinate :=
  Option.elim' (2, 3) (Option.elim' (3, 3) (Option.elim' (1, 2) (Fin.elim0)))

noncomputable def chartUnitVariables : Fin 3 → (Option (Option (Option (Fin 0)))) :=
  ![some (some (none)), none, some (none)]

noncomputable def chartLabelCode : ℕ := 16394952

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, true, true, false, true, false, true, false, false, false, true, true, true, true, false, true, true, false, true, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, true, true, true, false, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, false, true, true, false, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, false, false, true, false, true, false, true, true, true, false, false, false, false, true, false, false, true, false, false, true, true, false, false, true, false, false, false, false, false, false, false, false, false, false, false, true, true, false, false, false, false, false, false, true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, true, false, false, true, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 332)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 332) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨63, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (63 : Fin 70)
      rw [minorFormula_at_63]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨66, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (66 : Fin 70)
      rw [minorFormula_at_66]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨54, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (54 : Fin 70)
      rw [minorFormula_at_54]
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (5 : Fin 70) = _
      rw [minorFormula_at_5]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (7 : Fin 70) = _
      rw [minorFormula_at_7]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (23 : Fin 70) = _
      rw [minorFormula_at_23]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (26 : Fin 70) = _
      rw [minorFormula_at_26]
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (46 : Fin 70) = _
      rw [minorFormula_at_46]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨2, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (54 : Fin 70)
      rw [minorFormula_at_54]
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
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (63 : Fin 70)
      rw [minorFormula_at_63]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨1, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (66 : Fin 70)
      rw [minorFormula_at_66]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(4,1),(5,2),(6,3),(1,7)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Option (Option (Fin 0)))) 3 3
    (MatroidCatalogue.N8R4.family 332) where
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
    (MatroidCatalogue.N8R4.family 332) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart332
end

/- Source: Charts/Case333.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart333
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 2 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (some (none)) * X (some (some (none))) - (X (some (some (none)))) - (1), X (none) + (X (some (some (none))))]
noncomputable def U0 : Fin 3 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (some (none)), X (none), X (some (some (none)))]
noncomputable def R0 : Fin 2 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (some (none)) * X (some (some (none))) - (X (some (some (none)))) - (1), X (none) + (X (some (some (none))))]

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

noncomputable def nextE0 : Fin 2 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (none) * X (some (none)) - (X (some (none))) - (1), 0]
noncomputable def nextU0 : Fin 3 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (none), -(X (some (none))), X (some (none))]

noncomputable def step0 : LinearStep (Option (Option (Fin 0))) 2 3 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := 1
  b := X (some (none))
  pivot := 1
  pivot_identity := by simp [R0, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 1]
  equation_quotient := ![0, 1]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![0, 1, 0]
  unit_quotient := ![0, 1, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 2 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (none) * X (some (none)) - (X (some (none))) - (1), 0]
noncomputable def U1 : Fin 3 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (none), -(X (some (none))), X (some (none))]
noncomputable def R1 : Fin 2 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (none) * X (some (none)) - (X (some (none))) - (1), 0]

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

noncomputable def nextE1 : Fin 2 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0]
noncomputable def nextU1 : Fin 3 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none) + (1), -(X (none)), X (none)]

noncomputable def step1 : LinearStep (Option (Fin 0)) 2 3 where
  sourceE := R1
  sourceU := U1
  targetE := nextE1
  targetU := nextU1
  a := X (none)
  b := -(X (none)) - (1)
  pivot := 0
  pivot_identity := by simp [R1, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 1
      selected := ![1]
      quotient := -(1)
      identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1, 0]
  equation_quotient := ![X (some (none)), 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring
  unit_power := ![1, 0, 0]
  unit_quotient := ![1, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring

noncomputable def E2 : Fin 2 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0]
noncomputable def U2 : Fin 3 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none) + (1), -(X (none)), X (none)]
noncomputable def R2 : Fin 2 → MvPolynomial (Option (Fin 0)) ℚ :=
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

end Papers.RationalityTen.Chart333
end

/- Source: ChartTables/Case333.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart333
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Option (Fin 0)))) :=
  ![![.one, .one, .one, .zero], ![.one, .zero, .variable (some (none)), .one], ![.zero, .one, .zero, .variable (none)], ![.zero, .zero, .one, .variable (some (some (none)))]]

noncomputable def chartPositions : (Option (Option (Option (Fin 0)))) → Coordinate × Coordinate :=
  Option.elim' (2, 3) (Option.elim' (1, 2) (Option.elim' (3, 3) ![]))

noncomputable def chartUnitVariables : Fin 3 → (Option (Option (Option (Fin 0)))) :=
  ![some (none), none, some (some (none))]

noncomputable def chartLabelCode : ℕ := 16133320

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, true, true, false, true, false, true, false, false, false, true, true, true, true, false, true, true, false, true, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, true, true, true, false, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, false, false, true, false, true, false, true, true, true, false, false, false, false, true, false, false, true, false, false, true, true, false, false, true, false, false, false, false, false, false, false, false, false, false, false, true, true, false, false, false, false, false, false, true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 333)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 333) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨63, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (63 : Fin 70)
      rw [minorFormula_at_63]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨54, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (54 : Fin 70)
      rw [minorFormula_at_54]
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (5 : Fin 70) = _
      rw [minorFormula_at_5]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (7 : Fin 70) = _
      rw [minorFormula_at_7]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (23 : Fin 70) = _
      rw [minorFormula_at_23]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (26 : Fin 70) = _
      rw [minorFormula_at_26]
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (46 : Fin 70) = _
      rw [minorFormula_at_46]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(4,1),(5,2),(6,3),(1,7)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Option (Option (Fin 0)))) 2 3
    (MatroidCatalogue.N8R4.family 333) where
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
    (MatroidCatalogue.N8R4.family 333) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart333
end

/- Source: Charts/Case334.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart334
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 1 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![X (none) + (1)]
noncomputable def U0 : Fin 3 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![X (some (none)), X (none), X (some (some (0 : Fin 1)))]
noncomputable def R0 : Fin 1 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
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

noncomputable def nextE0 : Fin 1 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![0]
noncomputable def nextU0 : Fin 3 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![X (none), -(1), X (some (0 : Fin 1))]

noncomputable def step0 : LinearStep (Option (Fin 1)) 1 3 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := 1
  b := 1
  pivot := 0
  pivot_identity := by simp [R0, map_ofNat]<;> ring
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
  ![X (none), -(1), X (some (0 : Fin 1))]
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

end Papers.RationalityTen.Chart334
end

/- Source: ChartTables/Case334.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart334
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Fin 1))) :=
  ![![.one, .one, .one, .zero], ![.one, .zero, .variable (some (none)), .one], ![.zero, .one, .zero, .variable (none)], ![.zero, .zero, .one, .variable (some (some (0 : Fin 1)))]]

noncomputable def chartPositions : (Option (Option (Fin 1))) → Coordinate × Coordinate :=
  Option.elim' (2, 3) (Option.elim' (1, 2) ![(3, 3)])

noncomputable def chartUnitVariables : Fin 3 → (Option (Option (Fin 1))) :=
  ![some (none), none, some (some (0 : Fin 1))]

noncomputable def chartLabelCode : ℕ := 16394952

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, true, true, false, true, false, true, false, false, false, true, true, true, true, false, true, true, false, true, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, false, false, true, false, true, false, true, true, true, false, false, false, false, true, false, false, true, false, false, true, true, false, false, true, false, false, false, false, false, false, false, false, false, false, false, true, true, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 334)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 334) chartLabelCode chartEntries
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
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (7 : Fin 70) = _
      rw [minorFormula_at_7]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (23 : Fin 70) = _
      rw [minorFormula_at_23]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (26 : Fin 70) = _
      rw [minorFormula_at_26]
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (46 : Fin 70) = _
      rw [minorFormula_at_46]
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
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(4,1),(5,2),(6,3),(1,7)]

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
    (MatroidCatalogue.N8R4.family 334) where
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
    (MatroidCatalogue.N8R4.family 334) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart334
end

/- Source: Charts/Case335.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart335
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 1 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![X (none) * X (some (some (0 : Fin 1))) - (X (some (some (0 : Fin 1)))) - (1)]
noncomputable def U0 : Fin 3 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![X (none), X (some (none)), X (some (some (0 : Fin 1)))]
noncomputable def R0 : Fin 1 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![X (none) * X (some (some (0 : Fin 1))) - (X (some (some (0 : Fin 1)))) - (1)]

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

noncomputable def nextE0 : Fin 1 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![0]
noncomputable def nextU0 : Fin 3 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![X (some (0 : Fin 1)) + (1), X (none), X (some (0 : Fin 1))]

noncomputable def step0 : LinearStep (Option (Fin 1)) 1 3 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := X (some (0 : Fin 1))
  b := -(X (some (0 : Fin 1))) - (1)
  pivot := 0
  pivot_identity := by simp [R0, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 1
      selected := ![2]
      quotient := 1
      identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1]
  equation_quotient := ![X (some (some (0 : Fin 1)))]
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
  ![X (some (0 : Fin 1)) + (1), X (none), X (some (0 : Fin 1))]
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

end Papers.RationalityTen.Chart335
end

/- Source: ChartTables/Case335.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart335
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Fin 1))) :=
  ![![.one, .one, .one, .zero], ![.one, .zero, .variable (none), .one], ![.zero, .one, .zero, .variable (some (none))], ![.zero, .zero, .one, .variable (some (some (0 : Fin 1)))]]

noncomputable def chartPositions : (Option (Option (Fin 1))) → Coordinate × Coordinate :=
  Option.elim' (1, 2) (Option.elim' (2, 3) ![(3, 3)])

noncomputable def chartUnitVariables : Fin 3 → (Option (Option (Fin 1))) :=
  ![none, some (none), some (some (0 : Fin 1))]

noncomputable def chartLabelCode : ℕ := 16133320

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, true, true, false, true, false, true, false, false, false, true, true, true, true, false, true, true, false, true, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, false, false, true, false, true, false, true, true, true, false, false, false, false, true, false, false, true, false, false, true, true, false, false, true, false, false, false, false, false, false, false, false, false, false, false, true, true, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 335)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 335) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨63, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (63 : Fin 70)
      rw [minorFormula_at_63]
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (5 : Fin 70) = _
      rw [minorFormula_at_5]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (7 : Fin 70) = _
      rw [minorFormula_at_7]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (23 : Fin 70) = _
      rw [minorFormula_at_23]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (26 : Fin 70) = _
      rw [minorFormula_at_26]
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (46 : Fin 70) = _
      rw [minorFormula_at_46]
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
    · refine Or.inr ⟨0, ?_⟩
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
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(4,1),(5,2),(6,3),(1,7)]

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
    (MatroidCatalogue.N8R4.family 335) where
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
    (MatroidCatalogue.N8R4.family 335) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart335
end

/- Source: Charts/Case336.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart336
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 1 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![X (none) + (X (some (some (0 : Fin 1))))]
noncomputable def U0 : Fin 3 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![X (some (none)), X (none), X (some (some (0 : Fin 1)))]
noncomputable def R0 : Fin 1 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![X (none) + (X (some (some (0 : Fin 1))))]

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

noncomputable def nextE0 : Fin 1 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![0]
noncomputable def nextU0 : Fin 3 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![X (none), -(X (some (0 : Fin 1))), X (some (0 : Fin 1))]

noncomputable def step0 : LinearStep (Option (Fin 1)) 1 3 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := 1
  b := X (some (0 : Fin 1))
  pivot := 0
  pivot_identity := by simp [R0, map_ofNat]<;> ring
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
  ![X (none), -(X (some (0 : Fin 1))), X (some (0 : Fin 1))]
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

end Papers.RationalityTen.Chart336
end

/- Source: ChartTables/Case336.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart336
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Fin 1))) :=
  ![![.one, .one, .one, .zero], ![.one, .zero, .variable (some (none)), .one], ![.zero, .one, .zero, .variable (none)], ![.zero, .zero, .one, .variable (some (some (0 : Fin 1)))]]

noncomputable def chartPositions : (Option (Option (Fin 1))) → Coordinate × Coordinate :=
  Option.elim' (2, 3) (Option.elim' (1, 2) ![(3, 3)])

noncomputable def chartUnitVariables : Fin 3 → (Option (Option (Fin 1))) :=
  ![some (none), none, some (some (0 : Fin 1))]

noncomputable def chartLabelCode : ℕ := 16133320

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, true, true, false, true, false, true, false, false, false, true, true, true, true, false, true, true, false, true, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, true, true, true, false, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, false, false, true, false, true, false, true, true, true, false, false, false, false, true, false, false, true, false, false, true, true, false, false, true, false, false, false, false, false, false, false, false, false, false, false, true, true, false, false, false, false, false, false, true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 336)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 336) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨54, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (54 : Fin 70)
      rw [minorFormula_at_54]
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (5 : Fin 70) = _
      rw [minorFormula_at_5]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (7 : Fin 70) = _
      rw [minorFormula_at_7]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (23 : Fin 70) = _
      rw [minorFormula_at_23]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (26 : Fin 70) = _
      rw [minorFormula_at_26]
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (46 : Fin 70) = _
      rw [minorFormula_at_46]
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
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (54 : Fin 70)
      rw [minorFormula_at_54]
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

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(4,1),(5,2),(6,3),(1,7)]

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
    (MatroidCatalogue.N8R4.family 336) where
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
    (MatroidCatalogue.N8R4.family 336) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart336
end

/- Source: Charts/Case337.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart337
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

end Papers.RationalityTen.Chart337
end

/- Source: ChartTables/Case337.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart337
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 2)) :=
  ![![.one, .one, .one, .zero], ![.one, .zero, .variable (none), .one], ![.zero, .one, .zero, .variable (some (0 : Fin 2))], ![.zero, .zero, .one, .variable (some (1 : Fin 2))]]

noncomputable def chartPositions : (Option (Fin 2)) → Coordinate × Coordinate :=
  Option.elim' (1, 2) ![(2, 3), (3, 3)]

noncomputable def chartUnitVariables : Fin 3 → (Option (Fin 2)) :=
  ![none, some (0 : Fin 2), some (1 : Fin 2)]

noncomputable def chartLabelCode : ℕ := 16394952

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, true, true, false, true, false, true, false, false, false, true, true, true, true, false, true, true, false, true, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, false, false, true, false, true, false, true, true, true, false, false, false, false, true, false, false, true, false, false, true, true, false, false, true, false, false, false, false, false, false, false, false, false, false, false, true, true, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 2)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 337)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 337) chartLabelCode chartEntries
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
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (7 : Fin 70) = _
      rw [minorFormula_at_7]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (23 : Fin 70) = _
      rw [minorFormula_at_23]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (26 : Fin 70) = _
      rw [minorFormula_at_26]
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (46 : Fin 70) = _
      rw [minorFormula_at_46]
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

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(4,1),(5,2),(6,3),(1,7)]

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
    (MatroidCatalogue.N8R4.family 337) where
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
    (MatroidCatalogue.N8R4.family 337) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart337
end

/- Source: Charts/Case338.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart338
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 0 → MvPolynomial (Option (Fin 3)) ℚ :=
  ![]
noncomputable def U0 : Fin 4 → MvPolynomial (Option (Fin 3)) ℚ :=
  ![X (none), X (some (0 : Fin 3)), X (some (1 : Fin 3)), X (some (2 : Fin 3))]
noncomputable def R0 : Fin 0 → MvPolynomial (Option (Fin 3)) ℚ :=
  ![]

noncomputable def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart338
end

/- Source: ChartTables/Case338.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart338
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 3)) :=
  ![![.one, .one, .one, .one], ![.one, .zero, .variable (none), .variable (some (0 : Fin 3))], ![.zero, .one, .zero, .variable (some (1 : Fin 3))], ![.zero, .zero, .one, .variable (some (2 : Fin 3))]]

noncomputable def chartPositions : (Option (Fin 3)) → Coordinate × Coordinate :=
  Option.elim' (1, 2) ![(1, 3), (2, 3), (3, 3)]

noncomputable def chartUnitVariables : Fin 4 → (Option (Fin 3)) :=
  ![none, some (0 : Fin 3), some (1 : Fin 3), some (2 : Fin 3)]

noncomputable def chartLabelCode : ℕ := 16394952

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, true, true, false, true, false, true, false, false, false, true, true, true, true, false, true, true, false, true, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, false, false, true, false, true, false, true, true, true, false, false, false, false, true, false, false, true, false, false, true, true, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 3)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 338)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 338) chartLabelCode chartEntries
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
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (7 : Fin 70) = _
      rw [minorFormula_at_7]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (23 : Fin 70) = _
      rw [minorFormula_at_23]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (26 : Fin 70) = _
      rw [minorFormula_at_26]
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (39 : Fin 70) = _
      rw [minorFormula_at_39]
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
      change minorFormula (fun r c => (chartEntries r c).polynomial) (46 : Fin 70) = _
      rw [minorFormula_at_46]
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

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(0,7),(4,1),(5,2),(6,3)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Fin 3)) 0 4
    (MatroidCatalogue.N8R4.family 338) where
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
    (MatroidCatalogue.N8R4.family 338) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart338
end

/- Source: Charts/Case339.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart339
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![-(X (none)) + (X (some (some (none)))), -(X (some (none))) - (1), X (none) + (X (some (none)) * X (some (some (none)))), X (none) + (X (some (none)) * X (some (some (none)))) - (X (some (none))) - (1), X (none) - (X (some (some (none))))]
noncomputable def U0 : Fin 3 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none), X (some (some (none))), X (some (none))]
noncomputable def R0 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none) - (X (some (some (none)))), X (some (none)) + (1), X (none) + (X (some (none)) * X (some (some (none)))), X (none) + (X (some (none)) * X (some (some (none)))) - (X (some (none))) - (1), X (none) - (X (some (some (none))))]

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

noncomputable def nextE0 : Fin 5 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, X (none) + (1), X (none) * X (some (none)) + (X (some (none))), X (none) * X (some (none)) - (X (none)) + (X (some (none))) - (1), 0]
noncomputable def nextU0 : Fin 3 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (some (none)), X (some (none)), X (none)]

noncomputable def step0 : LinearStep (Option (Option (Fin 0))) 5 3 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := 1
  b := -(X (some (none)))
  pivot := 0
  pivot_identity := by simp [R0, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1, 0, 1, 1, 1]
  equation_quotient := ![1, 0, 1, 1, 1]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![1, 0, 0]
  unit_quotient := ![1, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 5 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, X (none) + (1), X (none) * X (some (none)) + (X (some (none))), X (none) * X (some (none)) - (X (none)) + (X (some (none))) - (1), 0]
noncomputable def U1 : Fin 3 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (some (none)), X (some (none)), X (none)]
noncomputable def R1 : Fin 5 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, X (none) + (1), X (none) + (1), X (none) * X (some (none)) - (X (none)) + (X (some (none))) - (1), 0]

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
      unit := X (some (none))
      unit_witness := {
        count := 1
        selected := ![0]
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := X (some (none))
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

noncomputable def nextE1 : Fin 5 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 0, 0]
noncomputable def nextU1 : Fin 3 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none), X (none), -(1)]

noncomputable def step1 : LinearStep (Option (Fin 0)) 5 3 where
  sourceE := R1
  sourceU := U1
  targetE := nextE1
  targetU := nextU1
  a := 1
  b := 1
  pivot := 1
  pivot_identity := by simp [R1, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 1, 1, 1, 0]
  equation_quotient := ![0, 1, 1, X (some (none)) - (1), 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring
  unit_power := ![0, 0, 1]
  unit_quotient := ![0, 0, 1]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring

noncomputable def E2 : Fin 5 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 0, 0]
noncomputable def U2 : Fin 3 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none), X (none), -(1)]
noncomputable def R2 : Fin 5 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 0, 0]

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

end Papers.RationalityTen.Chart339
end

/- Source: ChartTables/Case339.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart339
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Option (Fin 0)))) :=
  ![![.one, .zero, .one, .one], ![.one, .zero, .variable (none), .variable (some (some (none)))], ![.zero, .one, .zero, .one], ![.zero, .one, .variable (some (none)), .zero]]

noncomputable def chartPositions : (Option (Option (Option (Fin 0)))) → Coordinate × Coordinate :=
  Option.elim' (1, 2) (Option.elim' (3, 2) (Option.elim' (1, 3) ![]))

noncomputable def chartUnitVariables : Fin 3 → (Option (Option (Option (Fin 0)))) :=
  ![none, some (some (none)), some (none)]

noncomputable def chartLabelCode : ℕ := 16362248

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, true, true, false, false, true, false, true, false, false, false, true, true, true, true, false, true, true, true, true, false, true, true, true, true, false, true, true, true, true, true, true, true, false, true, false, true, true, true, true, false, true, true, true, true, false, true, true, true, true, true, true, true, false, false, true, true, false, false, false, true, true, true, false, true, true, true, false, false]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, false, false, true, true, false, true, false, true, true, true, false, false, false, false, true, false, false, false, false, true, false, false, false, false, true, false, false, false, false, false, false, false, true, false, true, false, false, false, false, true, false, false, false, false, true, false, false, false, false, false, false, false, true, true, false, false, true, true, true, false, false, false, true, false, false, false, true, true]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 339)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 339) chartLabelCode chartEntries
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
    · refine ⟨54, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (54 : Fin 70)
      rw [minorFormula_at_54]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨34, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (34 : Fin 70)
      rw [minorFormula_at_34]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨69, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (69 : Fin 70)
      rw [minorFormula_at_69]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (7 : Fin 70) = _
      rw [minorFormula_at_7]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (21 : Fin 70) = _
      rw [minorFormula_at_21]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (26 : Fin 70) = _
      rw [minorFormula_at_26]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (41 : Fin 70) = _
      rw [minorFormula_at_41]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (46 : Fin 70) = _
      rw [minorFormula_at_46]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (55 : Fin 70) = _
      rw [minorFormula_at_55]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
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
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (60 : Fin 70)
      rw [minorFormula_at_60]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (64 : Fin 70)
      rw [minorFormula_at_64]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨4, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (68 : Fin 70)
      rw [minorFormula_at_68]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine Or.inr ⟨3, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (69 : Fin 70)
      rw [minorFormula_at_69]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,6),(0,7),(4,1),(7,2),(2,5),(5,3)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Option (Option (Fin 0)))) 5 3
    (MatroidCatalogue.N8R4.family 339) where
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
    (MatroidCatalogue.N8R4.family 339) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart339
end

/- Source: Charts/Case340.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart340
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 1 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![X (none) + (1)]
noncomputable def U0 : Fin 3 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![X (some (none)), X (none), X (some (some (0 : Fin 1)))]
noncomputable def R0 : Fin 1 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
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

noncomputable def nextE0 : Fin 1 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![0]
noncomputable def nextU0 : Fin 3 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![X (none), -(1), X (some (0 : Fin 1))]

noncomputable def step0 : LinearStep (Option (Fin 1)) 1 3 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := 1
  b := 1
  pivot := 0
  pivot_identity := by simp [R0, map_ofNat]<;> ring
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
  ![X (none), -(1), X (some (0 : Fin 1))]
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

end Papers.RationalityTen.Chart340
end

/- Source: ChartTables/Case340.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart340
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Fin 1))) :=
  ![![.one, .zero, .one, .one], ![.zero, .one, .one, .variable (some (none))], ![.one, .variable (none), .zero, .zero], ![.zero, .zero, .one, .variable (some (some (0 : Fin 1)))]]

noncomputable def chartPositions : (Option (Option (Fin 1))) → Coordinate × Coordinate :=
  Option.elim' (2, 1) (Option.elim' (1, 3) ![(3, 3)])

noncomputable def chartUnitVariables : Fin 3 → (Option (Option (Fin 1))) :=
  ![some (none), none, some (some (0 : Fin 1))]

noncomputable def chartLabelCode : ℕ := 16398984

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, true, true, false, false, false, true, true, true, true, true, true, true, true, false, true, true, true, true, true, false, true, true, false, true, true, false, false, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, false, false, false, false, true, true, true, false, false, false, false, true, true, false, false, false, true, true, true, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, false, true, false, false, true, true, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 340)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 340) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨65, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (65 : Fin 70)
      rw [minorFormula_at_65]
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (7 : Fin 70) = _
      rw [minorFormula_at_7]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (14 : Fin 70) = _
      rw [minorFormula_at_14]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
      change minorFormula (fun r c => (chartEntries r c).polynomial) (30 : Fin 70) = _
      rw [minorFormula_at_30]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (50 : Fin 70) = _
      rw [minorFormula_at_50]
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
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (65 : Fin 70)
      rw [minorFormula_at_65]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,6),(0,7),(4,2),(6,1),(6,3),(1,5)]

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
    (MatroidCatalogue.N8R4.family 340) where
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
    (MatroidCatalogue.N8R4.family 340) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart340
end

/- Source: Charts/Case341.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart341
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![-(X (none) * X (some (none))) + (X (some (some (none)))), -(X (some (some (none)))) + (1), X (none) - (1), X (some (none)) + (1)]
noncomputable def U0 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (none), X (some (none)), X (some (some (none))), X (some (some (some (none))))]
noncomputable def R0 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (none) * X (some (none)) - (X (some (some (none)))), X (some (some (none))) - (1), X (none) - (1), X (some (none)) + (1)]

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

noncomputable def nextE0 : Fin 4 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none) - (X (some (none))), X (some (none)) - (1), 0, X (none) + (1)]
noncomputable def nextU0 : Fin 4 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![1, X (none), X (some (none)), X (some (some (none)))]

noncomputable def step0 : LinearStep (Option (Option (Option (Fin 0)))) 4 4 where
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
  equation_power := ![1, 0, 1, 0]
  equation_quotient := ![X (some (none)), 0, 1, 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![1, 0, 0, 0]
  unit_quotient := ![1, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 4 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none) - (X (some (none))), X (some (none)) - (1), 0, X (none) + (1)]
noncomputable def U1 : Fin 4 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![1, X (none), X (some (none)), X (some (some (none)))]
noncomputable def R1 : Fin 4 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none) - (X (some (none))), X (some (none)) - (1), 0, X (none) + (1)]

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

noncomputable def nextE1 : Fin 4 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, X (none) - (1), 0, X (none) + (1)]
noncomputable def nextU1 : Fin 4 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![1, X (none), X (none), X (some (none))]

noncomputable def step1 : LinearStep (Option (Option (Fin 0))) 4 4 where
  sourceE := R1
  sourceU := U1
  targetE := nextE1
  targetU := nextU1
  a := 1
  b := -(X (none))
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
  unit_power := ![0, 1, 0, 0]
  unit_quotient := ![0, 1, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring

noncomputable def E2 : Fin 4 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, X (none) - (1), 0, X (none) + (1)]
noncomputable def U2 : Fin 4 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![1, X (none), X (none), X (some (none))]
noncomputable def R2 : Fin 4 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, X (none) - (1), 0, X (none) + (1)]

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

noncomputable def nextE2 : Fin 4 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 2]
noncomputable def nextU2 : Fin 4 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![1, 1, 1, X (none)]

noncomputable def step2 : LinearStep (Option (Fin 0)) 4 4 where
  sourceE := R2
  sourceU := U2
  targetE := nextE2
  targetU := nextU2
  a := 1
  b := -(1)
  pivot := 1
  pivot_identity := by simp [R2, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 1, 0, 1]
  equation_quotient := ![0, 1, 0, 1]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring
  unit_power := ![0, 1, 1, 0]
  unit_quotient := ![0, 1, 1, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring

noncomputable def E3 : Fin 4 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 2]
noncomputable def U3 : Fin 4 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![1, 1, 1, X (none)]
noncomputable def R3 : Fin 4 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 1]

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
      unit := 2
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := C ((1 : ℚ) / 2)
        identity := by
          simp only [Fin.prod_univ_zero]
          calc
            (1 : _) = C (((1 : ℚ) / 2) * 2) := by norm_num
            _ = C ((1 : ℚ) / 2) * 2 := by simp only [map_mul, map_ofNat]
            _ = _ := by ring }
      forward_identity := ?_
      reverse_quotient := 2
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring

theorem dense3 : RationallyDenseSystem E3 U3 := by
  intro x hx
  have hz := ((reductions3 3).zero_iff x hx.2).mp (hx.1 3)
  norm_num [R3, MultiaffineDensity.evalRat] at hz

theorem dense2 : RationallyDenseSystem E2 U2 := by
  apply dense_system_of_factor_reductions E2 R2 U2 reductions2
  exact step2.preserves_density dense3

theorem dense1 : RationallyDenseSystem E1 U1 := by
  apply dense_system_of_factor_reductions E1 R1 U1 reductions1
  exact step1.preserves_density dense2

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  exact step0.preserves_density dense1

/-- This case has no real allowed point; density is vacuous only after that proof. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart341
end

/- Source: ChartTables/Case341.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart341
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Option (Option (Fin 0))))) :=
  ![![.one, .one, .zero, .one], ![.one, .zero, .one, .variable (none)], ![.zero, .one, .variable (some (none)), .variable (some (some (none)))], ![.zero, .zero, .one, .variable (some (some (some (none))))]]

noncomputable def chartPositions : (Option (Option (Option (Option (Fin 0))))) → Coordinate × Coordinate :=
  Option.elim' (1, 3) (Option.elim' (2, 2) (Option.elim' (2, 3) (Option.elim' (3, 3) ![])))

noncomputable def chartUnitVariables : Fin 4 → (Option (Option (Option (Option (Fin 0))))) :=
  ![none, some (none), some (some (none)), some (some (some (none)))]

noncomputable def chartLabelCode : ℕ := 16394952

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, true, true, false, true, true, true, false, false, false, true, true, true, true, false, true, true, false, true, true, false, false, true, true, true, true, true, true, false, true, true, true, true, true, true, false, true, false, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, false, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, false, false, true, false, false, false, true, true, true, false, false, false, false, true, false, false, true, false, false, true, true, false, false, false, false, false, false, true, false, false, false, false, false, false, true, false, true, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, true, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 341)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 341) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨30, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (30 : Fin 70)
      rw [minorFormula_at_30]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨49, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (49 : Fin 70)
      rw [minorFormula_at_49]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨57, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (57 : Fin 70)
      rw [minorFormula_at_57]
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (23 : Fin 70) = _
      rw [minorFormula_at_23]
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
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (30 : Fin 70)
      rw [minorFormula_at_30]
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
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (49 : Fin 70)
      rw [minorFormula_at_49]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨2, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (57 : Fin 70)
      rw [minorFormula_at_57]
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
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (65 : Fin 70)
      rw [minorFormula_at_65]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,7),(4,1),(5,2),(1,6),(6,3)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Option (Option (Option (Fin 0))))) 4 4
    (MatroidCatalogue.N8R4.family 341) where
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
    (MatroidCatalogue.N8R4.family 341) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart341
end

/- Source: Charts/Case342.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart342
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 3 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![-(X (some (none))) + (1), X (none) - (1), X (some (some (none))) + (1)]
noncomputable def U0 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (none), X (some (some (none))), X (some (none)), X (some (some (some (none))))]
noncomputable def R0 : Fin 3 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (some (none)) - (1), X (none) - (1), X (some (some (none))) + (1)]

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

noncomputable def nextE0 : Fin 3 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none) - (1), 0, X (some (none)) + (1)]
noncomputable def nextU0 : Fin 4 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![1, X (some (none)), X (none), X (some (some (none)))]

noncomputable def step0 : LinearStep (Option (Option (Option (Fin 0)))) 3 4 where
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
  equation_power := ![0, 1, 0]
  equation_quotient := ![0, 1, 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![1, 0, 0, 0]
  unit_quotient := ![1, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 3 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none) - (1), 0, X (some (none)) + (1)]
noncomputable def U1 : Fin 4 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![1, X (some (none)), X (none), X (some (some (none)))]
noncomputable def R1 : Fin 3 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none) - (1), 0, X (some (none)) + (1)]

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

noncomputable def nextE1 : Fin 3 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, 0, X (none) + (1)]
noncomputable def nextU1 : Fin 4 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![1, X (none), 1, X (some (none))]

noncomputable def step1 : LinearStep (Option (Option (Fin 0))) 3 4 where
  sourceE := R1
  sourceU := U1
  targetE := nextE1
  targetU := nextU1
  a := 1
  b := -(1)
  pivot := 0
  pivot_identity := by simp [R1, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1, 0, 0]
  equation_quotient := ![1, 0, 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring
  unit_power := ![0, 0, 1, 0]
  unit_quotient := ![0, 0, 1, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring

noncomputable def E2 : Fin 3 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, 0, X (none) + (1)]
noncomputable def U2 : Fin 4 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![1, X (none), 1, X (some (none))]
noncomputable def R2 : Fin 3 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, 0, X (none) + (1)]

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

noncomputable def nextE2 : Fin 3 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0]
noncomputable def nextU2 : Fin 4 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![1, -(1), 1, X (none)]

noncomputable def step2 : LinearStep (Option (Fin 0)) 3 4 where
  sourceE := R2
  sourceU := U2
  targetE := nextE2
  targetU := nextU2
  a := 1
  b := 1
  pivot := 2
  pivot_identity := by simp [R2, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 0, 1]
  equation_quotient := ![0, 0, 1]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring
  unit_power := ![0, 1, 0, 0]
  unit_quotient := ![0, 1, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring

noncomputable def E3 : Fin 3 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0]
noncomputable def U3 : Fin 4 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![1, -(1), 1, X (none)]
noncomputable def R3 : Fin 3 → MvPolynomial (Option (Fin 0)) ℚ :=
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

end Papers.RationalityTen.Chart342
end

/- Source: ChartTables/Case342.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart342
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Option (Option (Fin 0))))) :=
  ![![.one, .one, .zero, .one], ![.one, .zero, .one, .variable (none)], ![.zero, .one, .variable (some (some (none))), .variable (some (none))], ![.zero, .zero, .one, .variable (some (some (some (none))))]]

noncomputable def chartPositions : (Option (Option (Option (Option (Fin 0))))) → Coordinate × Coordinate :=
  Option.elim' (1, 3) (Option.elim' (2, 3) (Option.elim' (2, 2) (Option.elim' (3, 3) ![])))

noncomputable def chartUnitVariables : Fin 4 → (Option (Option (Option (Option (Fin 0))))) :=
  ![none, some (some (none)), some (none), some (some (some (none)))]

noncomputable def chartLabelCode : ℕ := 16394952

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, true, true, false, true, true, true, false, false, false, true, true, true, true, false, true, true, false, true, true, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, false, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, false, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, false, false, true, false, false, false, true, true, true, false, false, false, false, true, false, false, true, false, false, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, true, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, true, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 342)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 342) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨49, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (49 : Fin 70)
      rw [minorFormula_at_49]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨57, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (57 : Fin 70)
      rw [minorFormula_at_57]
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (23 : Fin 70) = _
      rw [minorFormula_at_23]
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
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (49 : Fin 70)
      rw [minorFormula_at_49]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨1, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (57 : Fin 70)
      rw [minorFormula_at_57]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨2, ?_⟩
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
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,7),(4,1),(5,2),(1,6),(6,3)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Option (Option (Option (Fin 0))))) 3 4
    (MatroidCatalogue.N8R4.family 342) where
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
    (MatroidCatalogue.N8R4.family 342) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart342
end

/- Source: Charts/Case343.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart343
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![-(X (some (none))) + (X (some (some (some (none))))) + (1), X (none) - (X (some (none)) * X (some (some (none)))), -(X (none)) + (1), X (some (some (none))) + (1)]
noncomputable def U0 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (some (none)), X (some (some (none))), X (none), X (some (some (some (none))))]
noncomputable def R0 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (some (none)) - (X (some (some (some (none))))) - (1), -(X (none)) + (X (some (none)) * X (some (some (none)))), X (none) - (1), X (some (some (none))) + (1)]

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

noncomputable def nextE0 : Fin 4 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none) - (X (some (some (none)))) - (1), 0, -(X (none) * X (some (none))) + (1), X (some (none)) + (1)]
noncomputable def nextU0 : Fin 4 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none), X (some (none)), -(X (none) * X (some (none))), X (some (some (none)))]

noncomputable def step0 : LinearStep (Option (Option (Option (Fin 0)))) 4 4 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := -(1)
  b := X (none) * X (some (none))
  pivot := 1
  pivot_identity := by simp [R0, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := -(1)
      identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 1, 1, 0]
  equation_quotient := ![0, -(1), 1, 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![0, 0, 1, 0]
  unit_quotient := ![0, 0, 1, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 4 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none) - (X (some (some (none)))) - (1), 0, -(X (none) * X (some (none))) + (1), X (some (none)) + (1)]
noncomputable def U1 : Fin 4 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none), X (some (none)), -(X (none) * X (some (none))), X (some (some (none)))]
noncomputable def R1 : Fin 4 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none) - (X (some (some (none)))) - (1), 0, X (none) * X (some (none)) - (1), X (some (none)) + (1)]

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

noncomputable def nextE1 : Fin 4 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, 0, X (none) * X (some (none)) + (X (none)) - (1), X (none) + (1)]
noncomputable def nextU1 : Fin 4 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (some (none)) + (1), X (none), -(X (none) * X (some (none))) - (X (none)), X (some (none))]

noncomputable def step1 : LinearStep (Option (Option (Fin 0))) 4 4 where
  sourceE := R1
  sourceU := U1
  targetE := nextE1
  targetU := nextU1
  a := 1
  b := -(X (some (none))) - (1)
  pivot := 0
  pivot_identity := by simp [R1, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1, 0, 1, 0]
  equation_quotient := ![1, 0, X (some (none)), 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring
  unit_power := ![1, 0, 1, 0]
  unit_quotient := ![1, 0, -(X (some (none))), 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring

noncomputable def E2 : Fin 4 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, 0, X (none) * X (some (none)) + (X (none)) - (1), X (none) + (1)]
noncomputable def U2 : Fin 4 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (some (none)) + (1), X (none), -(X (none) * X (some (none))) - (X (none)), X (some (none))]
noncomputable def R2 : Fin 4 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, 0, X (none) * X (some (none)) + (X (none)) - (1), X (none) + (1)]

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

noncomputable def nextE2 : Fin 4 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, -(X (none)) - (2), 0]
noncomputable def nextU2 : Fin 4 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none) + (1), -(1), X (none) + (1), X (none)]

noncomputable def step2 : LinearStep (Option (Fin 0)) 4 4 where
  sourceE := R2
  sourceU := U2
  targetE := nextE2
  targetU := nextU2
  a := 1
  b := 1
  pivot := 3
  pivot_identity := by simp [R2, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 0, 1, 1]
  equation_quotient := ![0, 0, X (some (none)) + (1), 1]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring
  unit_power := ![0, 1, 1, 0]
  unit_quotient := ![0, 1, -(X (some (none))) - (1), 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring

noncomputable def E3 : Fin 4 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, -(X (none)) - (2), 0]
noncomputable def U3 : Fin 4 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none) + (1), -(1), X (none) + (1), X (none)]
noncomputable def R3 : Fin 4 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, X (none) + (2), 0]

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

noncomputable def nextE3 : Fin 4 → MvPolynomial (Fin 0) ℚ :=
  ![0, 0, 0, 0]
noncomputable def nextU3 : Fin 4 → MvPolynomial (Fin 0) ℚ :=
  ![-(1), -(1), -(1), -(2)]

noncomputable def step3 : LinearStep (Fin 0) 4 4 where
  sourceE := R3
  sourceU := U3
  targetE := nextE3
  targetU := nextU3
  a := 1
  b := 2
  pivot := 2
  pivot_identity := by simp [R3, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 0, 1, 0]
  equation_quotient := ![0, 0, 1, 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R3, U3, nextE3, nextU3, map_ofNat] <;> ring
  unit_power := ![1, 0, 1, 1]
  unit_quotient := ![1, 0, 1, 1]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R3, U3, nextE3, nextU3, map_ofNat] <;> ring

noncomputable def E4 : Fin 4 → MvPolynomial (Fin 0) ℚ :=
  ![0, 0, 0, 0]
noncomputable def U4 : Fin 4 → MvPolynomial (Fin 0) ℚ :=
  ![-(1), -(1), -(1), -(2)]
noncomputable def R4 : Fin 4 → MvPolynomial (Fin 0) ℚ :=
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

end Papers.RationalityTen.Chart343
end

/- Source: ChartTables/Case343.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart343
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Option (Option (Fin 0))))) :=
  ![![.one, .one, .zero, .one], ![.one, .zero, .one, .variable (some (none))], ![.zero, .one, .variable (some (some (none))), .variable (none)], ![.zero, .zero, .one, .variable (some (some (some (none))))]]

noncomputable def chartPositions : (Option (Option (Option (Option (Fin 0))))) → Coordinate × Coordinate :=
  Option.elim' (2, 3) (Option.elim' (1, 3) (Option.elim' (2, 2) (Option.elim' (3, 3) (Fin.elim0))))

noncomputable def chartUnitVariables : Fin 4 → (Option (Option (Option (Option (Fin 0))))) :=
  ![some (none), some (some (none)), none, some (some (some (none)))]

noncomputable def chartLabelCode : ℕ := 16394952

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, true, true, false, true, true, true, false, false, false, true, true, true, true, false, true, true, false, true, true, false, false, true, true, true, true, true, true, false, true, true, true, true, true, true, false, true, false, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, false, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, false, false, true, false, false, false, true, true, true, false, false, false, false, true, false, false, true, false, false, true, true, false, false, false, false, false, false, true, false, false, false, false, false, false, true, false, true, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, true, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 343)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 343) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨63, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (63 : Fin 70)
      rw [minorFormula_at_63]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨30, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (30 : Fin 70)
      rw [minorFormula_at_30]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨49, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (49 : Fin 70)
      rw [minorFormula_at_49]
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (23 : Fin 70) = _
      rw [minorFormula_at_23]
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
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (30 : Fin 70)
      rw [minorFormula_at_30]
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
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (49 : Fin 70)
      rw [minorFormula_at_49]
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
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (63 : Fin 70)
      rw [minorFormula_at_63]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,7),(4,1),(5,2),(1,6),(6,3)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Option (Option (Option (Fin 0))))) 4 4
    (MatroidCatalogue.N8R4.family 343) where
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
    (MatroidCatalogue.N8R4.family 343) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart343
end

/- Source: Charts/Case344.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart344
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 3 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![-(X (some (none))) + (X (some (some (some (none))))) + (1), -(X (none)) + (1), X (some (some (none))) + (1)]
noncomputable def U0 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (some (none)), X (some (some (none))), X (none), X (some (some (some (none))))]
noncomputable def R0 : Fin 3 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (some (none)) - (X (some (some (some (none))))) - (1), X (none) - (1), X (some (some (none))) + (1)]

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

noncomputable def nextE0 : Fin 3 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none) - (X (some (some (none)))) - (1), 0, X (some (none)) + (1)]
noncomputable def nextU0 : Fin 4 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none), X (some (none)), 1, X (some (some (none)))]

noncomputable def step0 : LinearStep (Option (Option (Option (Fin 0)))) 3 4 where
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
  equation_power := ![0, 1, 0]
  equation_quotient := ![0, 1, 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![0, 0, 1, 0]
  unit_quotient := ![0, 0, 1, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 3 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none) - (X (some (some (none)))) - (1), 0, X (some (none)) + (1)]
noncomputable def U1 : Fin 4 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none), X (some (none)), 1, X (some (some (none)))]
noncomputable def R1 : Fin 3 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none) - (X (some (some (none)))) - (1), 0, X (some (none)) + (1)]

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

noncomputable def nextE1 : Fin 3 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, 0, X (none) + (1)]
noncomputable def nextU1 : Fin 4 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (some (none)) + (1), X (none), 1, X (some (none))]

noncomputable def step1 : LinearStep (Option (Option (Fin 0))) 3 4 where
  sourceE := R1
  sourceU := U1
  targetE := nextE1
  targetU := nextU1
  a := 1
  b := -(X (some (none))) - (1)
  pivot := 0
  pivot_identity := by simp [R1, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1, 0, 0]
  equation_quotient := ![1, 0, 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring
  unit_power := ![1, 0, 0, 0]
  unit_quotient := ![1, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring

noncomputable def E2 : Fin 3 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, 0, X (none) + (1)]
noncomputable def U2 : Fin 4 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (some (none)) + (1), X (none), 1, X (some (none))]
noncomputable def R2 : Fin 3 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, 0, X (none) + (1)]

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

noncomputable def nextE2 : Fin 3 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0]
noncomputable def nextU2 : Fin 4 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none) + (1), -(1), 1, X (none)]

noncomputable def step2 : LinearStep (Option (Fin 0)) 3 4 where
  sourceE := R2
  sourceU := U2
  targetE := nextE2
  targetU := nextU2
  a := 1
  b := 1
  pivot := 2
  pivot_identity := by simp [R2, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 0, 1]
  equation_quotient := ![0, 0, 1]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring
  unit_power := ![0, 1, 0, 0]
  unit_quotient := ![0, 1, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring

noncomputable def E3 : Fin 3 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0]
noncomputable def U3 : Fin 4 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none) + (1), -(1), 1, X (none)]
noncomputable def R3 : Fin 3 → MvPolynomial (Option (Fin 0)) ℚ :=
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

end Papers.RationalityTen.Chart344
end

/- Source: ChartTables/Case344.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart344
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Option (Option (Fin 0))))) :=
  ![![.one, .one, .zero, .one], ![.one, .zero, .one, .variable (some (none))], ![.zero, .one, .variable (some (some (none))), .variable (none)], ![.zero, .zero, .one, .variable (some (some (some (none))))]]

noncomputable def chartPositions : (Option (Option (Option (Option (Fin 0))))) → Coordinate × Coordinate :=
  Option.elim' (2, 3) (Option.elim' (1, 3) (Option.elim' (2, 2) (Option.elim' (3, 3) ![])))

noncomputable def chartUnitVariables : Fin 4 → (Option (Option (Option (Option (Fin 0))))) :=
  ![some (none), some (some (none)), none, some (some (some (none)))]

noncomputable def chartLabelCode : ℕ := 16394952

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, true, true, false, true, true, true, false, false, false, true, true, true, true, false, true, true, false, true, true, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, false, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, false, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, false, false, true, false, false, false, true, true, true, false, false, false, false, true, false, false, true, false, false, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, true, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, true, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 344)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 344) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨63, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (63 : Fin 70)
      rw [minorFormula_at_63]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨49, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (49 : Fin 70)
      rw [minorFormula_at_49]
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (23 : Fin 70) = _
      rw [minorFormula_at_23]
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
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (49 : Fin 70)
      rw [minorFormula_at_49]
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
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (63 : Fin 70)
      rw [minorFormula_at_63]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨2, ?_⟩
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
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,7),(4,1),(5,2),(1,6),(6,3)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Option (Option (Option (Fin 0))))) 3 4
    (MatroidCatalogue.N8R4.family 344) where
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
    (MatroidCatalogue.N8R4.family 344) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart344
end

/- Source: Charts/Case345.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart345
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 3 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![-(X (some (none))) + (1), X (none) - (1), X (none) * X (some (some (none))) - (X (some (none)))]
noncomputable def U0 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (none), X (some (none)), X (some (some (none))), X (some (some (some (none))))]
noncomputable def R0 : Fin 3 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (some (none)) - (1), X (none) - (1), X (none) * X (some (some (none))) - (X (some (none)))]

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

noncomputable def nextE0 : Fin 3 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none) - (1), 0, -(X (none)) + (X (some (none)))]
noncomputable def nextU0 : Fin 4 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![1, X (none), X (some (none)), X (some (some (none)))]

noncomputable def step0 : LinearStep (Option (Option (Option (Fin 0)))) 3 4 where
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
  equation_power := ![0, 1, 1]
  equation_quotient := ![0, 1, X (some (some (none)))]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![1, 0, 0, 0]
  unit_quotient := ![1, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 3 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none) - (1), 0, -(X (none)) + (X (some (none)))]
noncomputable def U1 : Fin 4 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![1, X (none), X (some (none)), X (some (some (none)))]
noncomputable def R1 : Fin 3 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none) - (1), 0, X (none) - (X (some (none)))]

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

noncomputable def nextE1 : Fin 3 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, 0, -(X (none)) + (1)]
noncomputable def nextU1 : Fin 4 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![1, 1, X (none), X (some (none))]

noncomputable def step1 : LinearStep (Option (Option (Fin 0))) 3 4 where
  sourceE := R1
  sourceU := U1
  targetE := nextE1
  targetU := nextU1
  a := 1
  b := -(1)
  pivot := 0
  pivot_identity := by simp [R1, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1, 0, 1]
  equation_quotient := ![1, 0, 1]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring
  unit_power := ![0, 1, 0, 0]
  unit_quotient := ![0, 1, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring

noncomputable def E2 : Fin 3 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, 0, -(X (none)) + (1)]
noncomputable def U2 : Fin 4 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![1, 1, X (none), X (some (none))]
noncomputable def R2 : Fin 3 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
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

noncomputable def nextE2 : Fin 3 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0]
noncomputable def nextU2 : Fin 4 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![1, 1, 1, X (none)]

noncomputable def step2 : LinearStep (Option (Fin 0)) 3 4 where
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
      identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 0, 1]
  equation_quotient := ![0, 0, 1]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring
  unit_power := ![0, 0, 1, 0]
  unit_quotient := ![0, 0, 1, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring

noncomputable def E3 : Fin 3 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0]
noncomputable def U3 : Fin 4 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![1, 1, 1, X (none)]
noncomputable def R3 : Fin 3 → MvPolynomial (Option (Fin 0)) ℚ :=
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

end Papers.RationalityTen.Chart345
end

/- Source: ChartTables/Case345.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart345
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Option (Option (Fin 0))))) :=
  ![![.one, .one, .one, .zero], ![.one, .zero, .variable (none), .one], ![.zero, .one, .variable (some (none)), .variable (some (some (none)))], ![.zero, .zero, .one, .variable (some (some (some (none))))]]

noncomputable def chartPositions : (Option (Option (Option (Option (Fin 0))))) → Coordinate × Coordinate :=
  Option.elim' (1, 2) (Option.elim' (2, 2) (Option.elim' (2, 3) (Option.elim' (3, 3) ![])))

noncomputable def chartUnitVariables : Fin 4 → (Option (Option (Option (Option (Fin 0))))) :=
  ![none, some (none), some (some (none)), some (some (some (none)))]

noncomputable def chartLabelCode : ℕ := 16398984

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, true, true, false, true, true, true, false, false, false, true, true, true, true, false, true, true, false, true, true, false, false, true, true, true, true, true, true, false, true, true, true, true, true, true, true, false, false, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, false, false, true, false, false, false, true, true, true, false, false, false, false, true, false, false, true, false, false, true, true, false, false, false, false, false, false, true, false, false, false, false, false, false, false, true, true, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 345)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 345) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨48, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (48 : Fin 70)
      rw [minorFormula_at_48]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨56, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (56 : Fin 70)
      rw [minorFormula_at_56]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨30, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (30 : Fin 70)
      rw [minorFormula_at_30]
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (23 : Fin 70) = _
      rw [minorFormula_at_23]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨2, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (30 : Fin 70)
      rw [minorFormula_at_30]
      dsimp [E0,
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (48 : Fin 70)
      rw [minorFormula_at_48]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨1, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (56 : Fin 70)
      rw [minorFormula_at_56]
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

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(4,1),(5,2),(6,3),(1,7)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Option (Option (Option (Fin 0))))) 3 4
    (MatroidCatalogue.N8R4.family 345) where
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
    (MatroidCatalogue.N8R4.family 345) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart345
end

/- Source: Charts/Case346.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart346
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 2 → MvPolynomial (Option (Option (Option (Fin 1)))) ℚ :=
  ![-(X (some (none))) + (1), X (none) - (1)]
noncomputable def U0 : Fin 4 → MvPolynomial (Option (Option (Option (Fin 1)))) ℚ :=
  ![X (none), X (some (none)), X (some (some (none))), X (some (some (some (0 : Fin 1))))]
noncomputable def R0 : Fin 2 → MvPolynomial (Option (Option (Option (Fin 1)))) ℚ :=
  ![X (some (none)) - (1), X (none) - (1)]

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

noncomputable def nextE0 : Fin 2 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![X (none) - (1), 0]
noncomputable def nextU0 : Fin 4 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![1, X (none), X (some (none)), X (some (some (0 : Fin 1)))]

noncomputable def step0 : LinearStep (Option (Option (Fin 1))) 2 4 where
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
  equation_power := ![0, 1]
  equation_quotient := ![0, 1]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![1, 0, 0, 0]
  unit_quotient := ![1, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 2 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![X (none) - (1), 0]
noncomputable def U1 : Fin 4 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![1, X (none), X (some (none)), X (some (some (0 : Fin 1)))]
noncomputable def R1 : Fin 2 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![X (none) - (1), 0]

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

noncomputable def nextE1 : Fin 2 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![0, 0]
noncomputable def nextU1 : Fin 4 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![1, 1, X (none), X (some (0 : Fin 1))]

noncomputable def step1 : LinearStep (Option (Fin 1)) 2 4 where
  sourceE := R1
  sourceU := U1
  targetE := nextE1
  targetU := nextU1
  a := 1
  b := -(1)
  pivot := 0
  pivot_identity := by simp [R1, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1, 0]
  equation_quotient := ![1, 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring
  unit_power := ![0, 1, 0, 0]
  unit_quotient := ![0, 1, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring

noncomputable def E2 : Fin 2 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![0, 0]
noncomputable def U2 : Fin 4 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![1, 1, X (none), X (some (0 : Fin 1))]
noncomputable def R2 : Fin 2 → MvPolynomial (Option (Fin 1)) ℚ :=
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

end Papers.RationalityTen.Chart346
end

/- Source: ChartTables/Case346.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart346
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Option (Fin 1)))) :=
  ![![.one, .one, .one, .zero], ![.one, .zero, .variable (none), .one], ![.zero, .one, .variable (some (none)), .variable (some (some (none)))], ![.zero, .zero, .one, .variable (some (some (some (0 : Fin 1))))]]

noncomputable def chartPositions : (Option (Option (Option (Fin 1)))) → Coordinate × Coordinate :=
  Option.elim' (1, 2) (Option.elim' (2, 2) (Option.elim' (2, 3) ![(3, 3)]))

noncomputable def chartUnitVariables : Fin 4 → (Option (Option (Option (Fin 1)))) :=
  ![none, some (none), some (some (none)), some (some (some (0 : Fin 1)))]

noncomputable def chartLabelCode : ℕ := 16398984

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, true, true, false, true, true, true, false, false, false, true, true, true, true, false, true, true, false, true, true, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, false, false, true, false, false, false, true, true, true, false, false, false, false, true, false, false, true, false, false, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Option (Fin 1)))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 346)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 346) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨48, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (48 : Fin 70)
      rw [minorFormula_at_48]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨56, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (56 : Fin 70)
      rw [minorFormula_at_56]
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (23 : Fin 70) = _
      rw [minorFormula_at_23]
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (48 : Fin 70)
      rw [minorFormula_at_48]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨1, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (56 : Fin 70)
      rw [minorFormula_at_56]
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

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(4,1),(5,2),(6,3),(1,7)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Option (Option (Fin 1)))) 2 4
    (MatroidCatalogue.N8R4.family 346) where
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
    (MatroidCatalogue.N8R4.family 346) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart346
end

/- Source: Charts/Case347.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart347
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 2 → MvPolynomial (Option (Option (Option (Fin 1)))) ℚ :=
  ![-(X (none) * X (some (none))) + (X (some (some (none)))), X (some (none)) + (1)]
noncomputable def U0 : Fin 4 → MvPolynomial (Option (Option (Option (Fin 1)))) ℚ :=
  ![X (none), X (some (none)), X (some (some (none))), X (some (some (some (0 : Fin 1))))]
noncomputable def R0 : Fin 2 → MvPolynomial (Option (Option (Option (Fin 1)))) ℚ :=
  ![X (none) * X (some (none)) - (X (some (some (none)))), X (some (none)) + (1)]

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

noncomputable def nextE0 : Fin 2 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![0, X (none) + (1)]
noncomputable def nextU0 : Fin 4 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![X (some (none)), X (none), X (some (none)), X (some (some (0 : Fin 1)))]

noncomputable def step0 : LinearStep (Option (Option (Fin 1))) 2 4 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := X (none)
  b := -(X (some (none)))
  pivot := 0
  pivot_identity := by simp [R0, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 1
      selected := ![1]
      quotient := 1
      identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1, 0]
  equation_quotient := ![X (some (none)), 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![1, 0, 0, 0]
  unit_quotient := ![1, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 2 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![0, X (none) + (1)]
noncomputable def U1 : Fin 4 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![X (some (none)), X (none), X (some (none)), X (some (some (0 : Fin 1)))]
noncomputable def R1 : Fin 2 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![0, X (none) + (1)]

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

noncomputable def nextE1 : Fin 2 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![0, 0]
noncomputable def nextU1 : Fin 4 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![X (none), -(1), X (none), X (some (0 : Fin 1))]

noncomputable def step1 : LinearStep (Option (Fin 1)) 2 4 where
  sourceE := R1
  sourceU := U1
  targetE := nextE1
  targetU := nextU1
  a := 1
  b := 1
  pivot := 1
  pivot_identity := by simp [R1, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 1]
  equation_quotient := ![0, 1]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring
  unit_power := ![0, 1, 0, 0]
  unit_quotient := ![0, 1, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring

noncomputable def E2 : Fin 2 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![0, 0]
noncomputable def U2 : Fin 4 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![X (none), -(1), X (none), X (some (0 : Fin 1))]
noncomputable def R2 : Fin 2 → MvPolynomial (Option (Fin 1)) ℚ :=
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

end Papers.RationalityTen.Chart347
end

/- Source: ChartTables/Case347.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart347
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Option (Fin 1)))) :=
  ![![.one, .one, .zero, .one], ![.one, .zero, .one, .variable (none)], ![.zero, .one, .variable (some (none)), .variable (some (some (none)))], ![.zero, .zero, .one, .variable (some (some (some (0 : Fin 1))))]]

noncomputable def chartPositions : (Option (Option (Option (Fin 1)))) → Coordinate × Coordinate :=
  Option.elim' (1, 3) (Option.elim' (2, 2) (Option.elim' (2, 3) ![(3, 3)]))

noncomputable def chartUnitVariables : Fin 4 → (Option (Option (Option (Fin 1)))) :=
  ![none, some (none), some (some (none)), some (some (some (0 : Fin 1)))]

noncomputable def chartLabelCode : ℕ := 16394952

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, true, true, false, true, true, true, false, false, false, true, true, true, true, false, true, true, false, true, true, false, false, true, true, true, true, true, true, false, true, true, true, true, true, true, false, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, false, false, true, false, false, false, true, true, true, false, false, false, false, true, false, false, true, false, false, true, true, false, false, false, false, false, false, true, false, false, false, false, false, false, true, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Option (Fin 1)))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 347)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 347) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨30, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (30 : Fin 70)
      rw [minorFormula_at_30]
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (23 : Fin 70) = _
      rw [minorFormula_at_23]
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
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (30 : Fin 70)
      rw [minorFormula_at_30]
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
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
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (65 : Fin 70)
      rw [minorFormula_at_65]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,7),(4,1),(5,2),(1,6),(6,3)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Option (Option (Fin 1)))) 2 4
    (MatroidCatalogue.N8R4.family 347) where
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
    (MatroidCatalogue.N8R4.family 347) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart347
end

/- Source: Charts/Case348.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart348
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 1 → MvPolynomial (Option (Option (Fin 2))) ℚ :=
  ![X (none) + (1)]
noncomputable def U0 : Fin 4 → MvPolynomial (Option (Option (Fin 2))) ℚ :=
  ![X (some (none)), X (none), X (some (some (0 : Fin 2))), X (some (some (1 : Fin 2)))]
noncomputable def R0 : Fin 1 → MvPolynomial (Option (Option (Fin 2))) ℚ :=
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

noncomputable def nextE0 : Fin 1 → MvPolynomial (Option (Fin 2)) ℚ :=
  ![0]
noncomputable def nextU0 : Fin 4 → MvPolynomial (Option (Fin 2)) ℚ :=
  ![X (none), -(1), X (some (0 : Fin 2)), X (some (1 : Fin 2))]

noncomputable def step0 : LinearStep (Option (Fin 2)) 1 4 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := 1
  b := 1
  pivot := 0
  pivot_identity := by simp [R0, map_ofNat]<;> ring
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
  ![X (none), -(1), X (some (0 : Fin 2)), X (some (1 : Fin 2))]
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

end Papers.RationalityTen.Chart348
end

/- Source: ChartTables/Case348.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart348
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Fin 2))) :=
  ![![.one, .one, .zero, .one], ![.one, .zero, .one, .variable (some (none))], ![.zero, .one, .variable (none), .variable (some (some (0 : Fin 2)))], ![.zero, .zero, .one, .variable (some (some (1 : Fin 2)))]]

noncomputable def chartPositions : (Option (Option (Fin 2))) → Coordinate × Coordinate :=
  Option.elim' (2, 2) (Option.elim' (1, 3) ![(2, 3), (3, 3)])

noncomputable def chartUnitVariables : Fin 4 → (Option (Option (Fin 2))) :=
  ![some (none), none, some (some (0 : Fin 2)), some (some (1 : Fin 2))]

noncomputable def chartLabelCode : ℕ := 16394952

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, true, true, false, true, true, true, false, false, false, true, true, true, true, false, true, true, false, true, true, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, false, false, true, false, false, false, true, true, true, false, false, false, false, true, false, false, true, false, false, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Fin 2))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 348)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 348) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨65, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (65 : Fin 70)
      rw [minorFormula_at_65]
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (19 : Fin 70) = _
      rw [minorFormula_at_19]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (22 : Fin 70) = _
      rw [minorFormula_at_22]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (23 : Fin 70) = _
      rw [minorFormula_at_23]
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
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
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (65 : Fin 70)
      rw [minorFormula_at_65]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,7),(4,1),(5,2),(1,6),(6,3)]

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
    (MatroidCatalogue.N8R4.family 348) where
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
    (MatroidCatalogue.N8R4.family 348) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart348
end

/- Source: Charts/Case349.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart349
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 2 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![-(X (none)) + (1), X (none) - (1)]
noncomputable def U0 : Fin 3 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![X (none), X (some (none)), X (some (some (0 : Fin 1)))]
noncomputable def R0 : Fin 2 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![X (none) - (1), X (none) - (1)]

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

noncomputable def nextE0 : Fin 2 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![0, 0]
noncomputable def nextU0 : Fin 3 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![1, X (none), X (some (0 : Fin 1))]

noncomputable def step0 : LinearStep (Option (Fin 1)) 2 3 where
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
      identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1, 1]
  equation_quotient := ![1, 1]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![1, 0, 0]
  unit_quotient := ![1, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 2 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![0, 0]
noncomputable def U1 : Fin 3 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![1, X (none), X (some (0 : Fin 1))]
noncomputable def R1 : Fin 2 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![0, 0]

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

theorem dense1 : RationallyDenseSystem E1 U1 := by
  apply dense_system_of_factor_reductions E1 R1 U1 reductions1
  apply zero_equations_system_dense R1 U1
  intro j; fin_cases j <;> rfl

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  exact step0.preserves_density dense1

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart349
end

/- Source: ChartTables/Case349.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart349
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Fin 1))) :=
  ![![.zero, .zero, .one, .one], ![.one, .one, .zero, .one], ![.one, .variable (none), .variable (some (none)), .zero], ![.one, .variable (some (some (0 : Fin 1))), .zero, .zero]]

noncomputable def chartPositions : (Option (Option (Fin 1))) → Coordinate × Coordinate :=
  Option.elim' (2, 1) (Option.elim' (2, 2) ![(3, 1)])

noncomputable def chartUnitVariables : Fin 3 → (Option (Option (Fin 1))) :=
  ![none, some (none), some (some (0 : Fin 1))]

noncomputable def chartLabelCode : ℕ := 16434824

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, true, true, false, false, true, true, true, false, true, true, false, true, false, false, true, true, false, true, true, false, true, false, true, false, false, true, true, true, true, true, true, true, true, true, false, false, true, true, false, true, true, true, true, false, false, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, false, false, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, false, false, true, true, false, false, false, true, false, false, true, false, true, true, false, false, true, false, false, true, false, true, false, true, true, false, false, false, false, false, false, false, false, false, true, true, false, false, true, false, false, false, false, true, true, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, true, true, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 349)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 349) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨65, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (65 : Fin 70)
      rw [minorFormula_at_65]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨25, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (25 : Fin 70)
      rw [minorFormula_at_25]
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (4 : Fin 70) = _
      rw [minorFormula_at_4]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (11 : Fin 70) = _
      rw [minorFormula_at_11]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (13 : Fin 70) = _
      rw [minorFormula_at_13]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (14 : Fin 70) = _
      rw [minorFormula_at_14]
      dsimp [
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
    · refine Or.inr ⟨1, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (25 : Fin 70)
      rw [minorFormula_at_25]
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (35 : Fin 70) = _
      rw [minorFormula_at_35]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (36 : Fin 70) = _
      rw [minorFormula_at_36]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (39 : Fin 70) = _
      rw [minorFormula_at_39]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (55 : Fin 70) = _
      rw [minorFormula_at_55]
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
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (65 : Fin 70)
      rw [minorFormula_at_65]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
noncomputable def chartForestSteps : List (Point × Point) := [(0,6),(0,7),(7,1),(1,4),(1,5),(4,2),(4,3)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Option (Fin 1))) 2 3
    (MatroidCatalogue.N8R4.family 349) where
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
    (MatroidCatalogue.N8R4.family 349) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart349
end

/- Source: Charts/Case350.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart350
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

end Papers.RationalityTen.Chart350
end

/- Source: ChartTables/Case350.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart350
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 2)) :=
  ![![.one, .zero, .one, .one], ![.zero, .one, .one, .variable (none)], ![.one, .variable (some (0 : Fin 2)), .zero, .zero], ![.zero, .zero, .one, .variable (some (1 : Fin 2))]]

noncomputable def chartPositions : (Option (Fin 2)) → Coordinate × Coordinate :=
  Option.elim' (1, 3) ![(2, 1), (3, 3)]

noncomputable def chartUnitVariables : Fin 3 → (Option (Fin 2)) :=
  ![none, some (0 : Fin 2), some (1 : Fin 2)]

noncomputable def chartLabelCode : ℕ := 16398984

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, true, true, false, false, false, true, true, true, true, true, true, true, true, false, true, true, true, true, true, false, true, true, false, true, true, false, false, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, false, false, false, false, true, true, true, false, false, false, false, true, true, false, false, false, true, true, true, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, false, true, false, false, true, true, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 2)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 350)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 350) chartLabelCode chartEntries
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (7 : Fin 70) = _
      rw [minorFormula_at_7]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (14 : Fin 70) = _
      rw [minorFormula_at_14]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
      change minorFormula (fun r c => (chartEntries r c).polynomial) (30 : Fin 70) = _
      rw [minorFormula_at_30]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (50 : Fin 70) = _
      rw [minorFormula_at_50]
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

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,6),(0,7),(4,2),(6,1),(6,3),(1,5)]

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
    (MatroidCatalogue.N8R4.family 350) where
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
    (MatroidCatalogue.N8R4.family 350) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart350
end

/- Source: Charts/Case351.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart351
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 2 → MvPolynomial (Option (Option (Option (Fin 1)))) ℚ :=
  ![X (none) - (X (some (none)) * X (some (some (none)))) + (X (some (some (none)))), -(X (none)) + (1)]
noncomputable def U0 : Fin 4 → MvPolynomial (Option (Option (Option (Fin 1)))) ℚ :=
  ![X (some (none)), X (none), X (some (some (none))), X (some (some (some (0 : Fin 1))))]
noncomputable def R0 : Fin 2 → MvPolynomial (Option (Option (Option (Fin 1)))) ℚ :=
  ![-(X (none)) + (X (some (none)) * X (some (some (none)))) - (X (some (some (none)))), X (none) - (1)]

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

noncomputable def nextE0 : Fin 2 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![0, -(X (none) * X (some (none))) + (X (some (none))) + (1)]
noncomputable def nextU0 : Fin 4 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![X (none), -(X (none) * X (some (none))) + (X (some (none))), X (some (none)), X (some (some (0 : Fin 1)))]

noncomputable def step0 : LinearStep (Option (Option (Fin 1))) 2 4 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := -(1)
  b := X (none) * X (some (none)) - (X (some (none)))
  pivot := 0
  pivot_identity := by simp [R0, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := -(1)
      identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1, 1]
  equation_quotient := ![-(1), 1]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![0, 1, 0, 0]
  unit_quotient := ![0, 1, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 2 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![0, -(X (none) * X (some (none))) + (X (some (none))) + (1)]
noncomputable def U1 : Fin 4 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![X (none), -(X (none) * X (some (none))) + (X (some (none))), X (some (none)), X (some (some (0 : Fin 1)))]
noncomputable def R1 : Fin 2 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![0, X (none) * X (some (none)) - (X (some (none))) - (1)]

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

noncomputable def nextE1 : Fin 2 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![0, 0]
noncomputable def nextU1 : Fin 4 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![X (none) + (1), -(X (none)), X (none), X (some (0 : Fin 1))]

noncomputable def step1 : LinearStep (Option (Fin 1)) 2 4 where
  sourceE := R1
  sourceU := U1
  targetE := nextE1
  targetU := nextU1
  a := X (none)
  b := -(X (none)) - (1)
  pivot := 1
  pivot_identity := by simp [R1, map_ofNat]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 1
      selected := ![2]
      quotient := 1
      identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 1]
  equation_quotient := ![0, X (some (none))]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring
  unit_power := ![1, 1, 0, 0]
  unit_quotient := ![1, -(X (some (none))), 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring

noncomputable def E2 : Fin 2 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![0, 0]
noncomputable def U2 : Fin 4 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![X (none) + (1), -(X (none)), X (none), X (some (0 : Fin 1))]
noncomputable def R2 : Fin 2 → MvPolynomial (Option (Fin 1)) ℚ :=
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

end Papers.RationalityTen.Chart351
end

/- Source: ChartTables/Case351.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart351
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Option (Fin 1)))) :=
  ![![.one, .one, .one, .zero], ![.zero, .one, .variable (some (none)), .one], ![.one, .zero, .variable (none), .variable (some (some (none)))], ![.zero, .zero, .one, .variable (some (some (some (0 : Fin 1))))]]

noncomputable def chartPositions : (Option (Option (Option (Fin 1)))) → Coordinate × Coordinate :=
  Option.elim' (2, 2) (Option.elim' (1, 2) (Option.elim' (2, 3) ![(3, 3)]))

noncomputable def chartUnitVariables : Fin 4 → (Option (Option (Option (Fin 1)))) :=
  ![some (none), none, some (some (none)), some (some (some (0 : Fin 1)))]

noncomputable def chartLabelCode : ℕ := 16398984

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, true, true, true, false, true, true, false, true, true, false, false, true, false, true, true, true, false, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, false, false, false, true, false, false, true, false, false, true, true, false, true, false, false, false, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Option (Fin 1)))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 351)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 351) chartLabelCode chartEntries
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
    · refine ⟨46, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (46 : Fin 70)
      rw [minorFormula_at_46]
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (9 : Fin 70) = _
      rw [minorFormula_at_9]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨1, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (46 : Fin 70)
      rw [minorFormula_at_46]
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
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (68 : Fin 70)
      rw [minorFormula_at_68]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(4,2),(5,1),(6,3),(1,7)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Option (Option (Fin 1)))) 2 4
    (MatroidCatalogue.N8R4.family 351) where
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
    (MatroidCatalogue.N8R4.family 351) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart351
end
