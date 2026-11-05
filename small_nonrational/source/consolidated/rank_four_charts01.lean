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

/- Source: Charts/Case32.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart32
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

end Papers.RationalityTen.Chart32
end

/- Source: ChartTables/Case32.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart32
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 1)) :=
  ![![.one, .one, .one, .one], ![.zero, .zero, .one, .variable (none)], ![.zero, .zero, .one, .variable (some (0 : Fin 1))], ![.zero, .zero, .zero, .zero]]

noncomputable def chartPositions : (Option (Fin 1)) → Coordinate × Coordinate :=
  Option.elim' (1, 3) ![(2, 3)]

noncomputable def chartUnitVariables : Fin 2 → (Option (Fin 1)) :=
  ![none, some (0 : Fin 1)]

noncomputable def chartLabelCode : ℕ := 13967128

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, true, true, false, false, false, false, false, false, false, false, true, true, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, true, true, true, true, false, false, false, false, false, false, false, true, true, true, true, true, false, false, false, false, false, true, true, true, true, true, false, false, false, false, false, false, true, true, false]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, false, false, true, true, true, true, true, true, true, true, false, false, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, false, false, false, false, true, true, true, true, true, true, true, false, false, false, false, false, true, true, true, true, true, false, false, false, false, false, true, true, true, true, true, true, false, false, true]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 1)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 32)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 32) chartLabelCode chartEntries
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (23 : Fin 70) = _
      rw [minorFormula_at_23]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (28 : Fin 70) = _
      rw [minorFormula_at_28]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (34 : Fin 70) = _
      rw [minorFormula_at_34]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (41 : Fin 70) = _
      rw [minorFormula_at_41]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (53 : Fin 70) = _
      rw [minorFormula_at_53]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (54 : Fin 70) = _
      rw [minorFormula_at_54]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (62 : Fin 70) = _
      rw [minorFormula_at_62]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (65 : Fin 70) = _
      rw [minorFormula_at_65]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (66 : Fin 70) = _
      rw [minorFormula_at_66]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (69 : Fin 70) = _
      rw [minorFormula_at_69]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring

noncomputable def chartForestRoots : Finset Point := {0,3}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(0,7),(6,1),(6,2)]

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
    (MatroidCatalogue.N8R4.family 32) where
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
    (MatroidCatalogue.N8R4.family 32) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart32
end

/- Source: Charts/Case33.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart33
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]
noncomputable def U0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]
noncomputable def R0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]

noncomputable def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart33
end

/- Source: ChartTables/Case33.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart33
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Fin 0) :=
  ![![.one, .zero, .zero, .one], ![.zero, .one, .zero, .one], ![.zero, .zero, .one, .one], ![.zero, .zero, .zero, .zero]]

noncomputable def chartPositions : (Fin 0) → Coordinate × Coordinate :=
  Fin.elim0

noncomputable def chartUnitVariables : Fin 0 → (Fin 0) :=
  Fin.elim0

noncomputable def chartLabelCode : ℕ := 13999888

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, true, true, false, false, false, false, false, false, false, true, false, true, false, false, false, false, false, false, false, false, false, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, false, false, false, true, true, false, false, true, false, false, false, false, true, false, true, false, true, false, false, false, false, false, true, true, true, true, false]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, false, false, true, true, true, true, true, true, true, false, true, false, true, true, true, true, true, true, true, true, true, false, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, true, true, false, false, true, true, false, true, true, true, true, false, true, false, true, false, true, true, true, true, true, false, false, false, false, true]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Fin 0) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  exact fun j => Fin.elim0 j

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 33)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 33) chartLabelCode chartEntries
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (23 : Fin 70) = _
      rw [minorFormula_at_23]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (34 : Fin 70) = _
      rw [minorFormula_at_34]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (41 : Fin 70) = _
      rw [minorFormula_at_41]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (53 : Fin 70) = _
      rw [minorFormula_at_53]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (62 : Fin 70) = _
      rw [minorFormula_at_62]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (69 : Fin 70) = _
      rw [minorFormula_at_69]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring

noncomputable def chartForestRoots : Finset Point := {0,3}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,7),(7,1),(7,2),(1,5),(2,6)]

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

noncomputable def chart_certificate : ChartCertificate (Fin 0) 0 0
    (MatroidCatalogue.N8R4.family 33) where
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
    (MatroidCatalogue.N8R4.family 33) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart33
end

/- Source: Charts/Case34.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart34
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]
noncomputable def U0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]
noncomputable def R0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]

noncomputable def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart34
end

/- Source: ChartTables/Case34.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart34
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Fin 0) :=
  ![![.one, .zero, .zero, .one], ![.zero, .one, .one, .zero], ![.zero, .zero, .one, .one], ![.zero, .zero, .zero, .zero]]

noncomputable def chartPositions : (Fin 0) → Coordinate × Coordinate :=
  Fin.elim0

noncomputable def chartUnitVariables : Fin 0 → (Fin 0) :=
  Fin.elim0

noncomputable def chartLabelCode : ℕ := 13999888

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, true, true, false, false, false, false, false, false, false, true, true, false, false, false, false, false, false, false, false, false, false, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, false, false, false, true, true, false, false, true, false, false, false, false, true, true, false, false, true, true, false, false, false, false, true, true, true, true, false]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, false, false, true, true, true, true, true, true, true, false, false, true, true, true, true, true, true, true, true, true, true, false, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, true, true, false, false, true, true, false, true, true, true, true, false, false, true, true, false, false, true, true, true, true, false, false, false, false, true]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Fin 0) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  exact fun j => Fin.elim0 j

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 34)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 34) chartLabelCode chartEntries
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (23 : Fin 70) = _
      rw [minorFormula_at_23]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (34 : Fin 70) = _
      rw [minorFormula_at_34]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (41 : Fin 70) = _
      rw [minorFormula_at_41]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (53 : Fin 70) = _
      rw [minorFormula_at_53]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (62 : Fin 70) = _
      rw [minorFormula_at_62]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (69 : Fin 70) = _
      rw [minorFormula_at_69]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring

noncomputable def chartForestRoots : Finset Point := {0,3}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,7),(7,2),(2,6),(6,1),(1,5)]

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

noncomputable def chart_certificate : ChartCertificate (Fin 0) 0 0
    (MatroidCatalogue.N8R4.family 34) where
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
    (MatroidCatalogue.N8R4.family 34) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart34
end

/- Source: Charts/Case35.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart35
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

end Papers.RationalityTen.Chart35
end

/- Source: ChartTables/Case35.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart35
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 0)) :=
  ![![.one, .zero, .one, .one], ![.zero, .one, .zero, .one], ![.zero, .zero, .one, .variable (none)], ![.zero, .zero, .zero, .zero]]

noncomputable def chartPositions : (Option (Fin 0)) → Coordinate × Coordinate :=
  Option.elim' (2, 3) ![]

noncomputable def chartUnitVariables : Fin 1 → (Option (Fin 0)) :=
  ![none]

noncomputable def chartLabelCode : ℕ := 13999888

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, true, true, false, false, false, false, false, false, false, true, false, true, false, false, false, false, false, false, false, false, false, true, true, true, false, false, false, false, true, false, true, true, false, false, false, false, false, false, false, true, true, false, false, true, false, false, false, false, true, false, true, true, true, true, false, false, false, false, true, true, true, true, false]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, false, false, true, true, true, true, true, true, true, false, true, false, true, true, true, true, true, true, true, true, true, false, false, false, true, true, true, true, false, true, false, false, true, true, true, true, true, true, true, false, false, true, true, false, true, true, true, true, false, true, false, false, false, false, true, true, true, true, false, false, false, false, true]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 0)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 35)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 35) chartLabelCode chartEntries
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (23 : Fin 70) = _
      rw [minorFormula_at_23]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (34 : Fin 70) = _
      rw [minorFormula_at_34]
      dsimp [
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (41 : Fin 70) = _
      rw [minorFormula_at_41]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (53 : Fin 70) = _
      rw [minorFormula_at_53]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (62 : Fin 70) = _
      rw [minorFormula_at_62]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (69 : Fin 70) = _
      rw [minorFormula_at_69]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring

noncomputable def chartForestRoots : Finset Point := {0,3}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,6),(0,7),(6,2),(7,1),(1,5)]

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
    (MatroidCatalogue.N8R4.family 35) where
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
    (MatroidCatalogue.N8R4.family 35) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart35
end

/- Source: Charts/Case36.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart36
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

end Papers.RationalityTen.Chart36
end

/- Source: ChartTables/Case36.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart36
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Fin 0))) :=
  ![![.one, .zero, .one, .one], ![.zero, .one, .one, .variable (none)], ![.zero, .zero, .one, .variable (some (none))], ![.zero, .zero, .zero, .zero]]

noncomputable def chartPositions : (Option (Option (Fin 0))) → Coordinate × Coordinate :=
  Option.elim' (1, 3) (Option.elim' (2, 3) ![])

noncomputable def chartUnitVariables : Fin 2 → (Option (Option (Fin 0))) :=
  ![none, some (none)]

noncomputable def chartLabelCode : ℕ := 13999888

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, true, true, false, false, false, false, false, false, false, true, true, true, false, false, false, false, false, false, false, false, false, true, true, true, false, false, false, false, true, false, true, true, false, false, false, false, false, false, false, true, true, false, false, true, false, false, false, false, true, true, true, true, true, false, false, false, false, false, true, true, true, true, false]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, false, false, true, true, true, true, true, true, true, false, false, false, true, true, true, true, true, true, true, true, true, false, false, false, true, true, true, true, false, true, false, false, true, true, true, true, true, true, true, false, false, true, true, false, true, true, true, true, false, false, false, false, false, true, true, true, true, true, false, false, false, false, true]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 36)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 36) chartLabelCode chartEntries
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (34 : Fin 70) = _
      rw [minorFormula_at_34]
      dsimp [
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (41 : Fin 70) = _
      rw [minorFormula_at_41]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (53 : Fin 70) = _
      rw [minorFormula_at_53]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (54 : Fin 70) = _
      rw [minorFormula_at_54]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (62 : Fin 70) = _
      rw [minorFormula_at_62]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (69 : Fin 70) = _
      rw [minorFormula_at_69]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring

noncomputable def chartForestRoots : Finset Point := {0,3}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,6),(0,7),(6,1),(6,2),(1,5)]

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
    (MatroidCatalogue.N8R4.family 36) where
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
    (MatroidCatalogue.N8R4.family 36) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart36
end

/- Source: Charts/Case37.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart37
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

end Papers.RationalityTen.Chart37
end

/- Source: ChartTables/Case37.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart37
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 1)) :=
  ![![.one, .zero, .one, .one], ![.zero, .one, .one, .variable (none)], ![.zero, .zero, .one, .variable (some (0 : Fin 1))], ![.zero, .zero, .zero, .zero]]

noncomputable def chartPositions : (Option (Fin 1)) → Coordinate × Coordinate :=
  Option.elim' (1, 3) ![(2, 3)]

noncomputable def chartUnitVariables : Fin 2 → (Option (Fin 1)) :=
  ![none, some (0 : Fin 1)]

noncomputable def chartLabelCode : ℕ := 13999888

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, true, true, false, false, false, false, false, false, false, true, true, true, false, false, false, false, false, false, false, false, false, true, true, true, false, false, false, false, true, false, true, true, false, false, false, false, false, false, false, true, true, false, false, true, false, false, false, false, true, true, true, true, true, true, false, false, false, false, true, true, true, true, false]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, false, false, true, true, true, true, true, true, true, false, false, false, true, true, true, true, true, true, true, true, true, false, false, false, true, true, true, true, false, true, false, false, true, true, true, true, true, true, true, false, false, true, true, false, true, true, true, true, false, false, false, false, false, false, true, true, true, true, false, false, false, false, true]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 1)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 37)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 37) chartLabelCode chartEntries
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (34 : Fin 70) = _
      rw [minorFormula_at_34]
      dsimp [
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (41 : Fin 70) = _
      rw [minorFormula_at_41]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (53 : Fin 70) = _
      rw [minorFormula_at_53]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (54 : Fin 70) = _
      rw [minorFormula_at_54]
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
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (62 : Fin 70) = _
      rw [minorFormula_at_62]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (69 : Fin 70) = _
      rw [minorFormula_at_69]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring

noncomputable def chartForestRoots : Finset Point := {0,3}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,6),(0,7),(6,1),(6,2),(1,5)]

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
    (MatroidCatalogue.N8R4.family 37) where
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
    (MatroidCatalogue.N8R4.family 37) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart37
end

/- Source: Charts/Case38.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart38
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 1 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none) + (1)]
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

end Papers.RationalityTen.Chart38
end

/- Source: ChartTables/Case38.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart38
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 0)) :=
  ![![.one, .one, .one, .zero], ![.zero, .one, .zero, .one], ![.zero, .zero, .one, .variable (none)], ![.zero, .zero, .zero, .zero]]

noncomputable def chartPositions : (Option (Fin 0)) → Coordinate × Coordinate :=
  Option.elim' (2, 3) (Fin.elim0)

noncomputable def chartUnitVariables : Fin 1 → (Option (Fin 0)) :=
  ![none]

noncomputable def chartLabelCode : ℕ := 13999888

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, true, true, false, false, false, false, false, false, false, true, false, true, false, false, false, false, false, false, false, false, false, true, true, true, false, false, false, false, true, true, true, false, false, false, false, false, false, false, false, true, true, true, true, true, false, false, false, false, true, false, true, true, true, true, false, false, false, false, true, true, true, false, false]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, false, false, true, true, true, true, true, true, true, false, true, false, true, true, true, true, true, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, true, true, true, true, true, true, true, false, false, false, false, false, true, true, true, true, false, true, false, false, false, false, true, true, true, true, false, false, false, true, true]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 0)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 38)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 38) chartLabelCode chartEntries
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (23 : Fin 70) = _
      rw [minorFormula_at_23]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (34 : Fin 70) = _
      rw [minorFormula_at_34]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (41 : Fin 70) = _
      rw [minorFormula_at_41]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (53 : Fin 70) = _
      rw [minorFormula_at_53]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (62 : Fin 70) = _
      rw [minorFormula_at_62]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (68 : Fin 70)
      rw [minorFormula_at_68]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (69 : Fin 70) = _
      rw [minorFormula_at_69]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring

noncomputable def chartForestRoots : Finset Point := {0,3}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(5,1),(6,2),(1,7)]

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
    (MatroidCatalogue.N8R4.family 38) where
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
    (MatroidCatalogue.N8R4.family 38) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart38
end

/- Source: Charts/Case39.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart39
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

end Papers.RationalityTen.Chart39
end

/- Source: ChartTables/Case39.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart39
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 0)) :=
  ![![.one, .one, .one, .zero], ![.zero, .one, .zero, .one], ![.zero, .zero, .one, .variable (none)], ![.zero, .zero, .zero, .zero]]

noncomputable def chartPositions : (Option (Fin 0)) → Coordinate × Coordinate :=
  Option.elim' (2, 3) ![]

noncomputable def chartUnitVariables : Fin 1 → (Option (Fin 0)) :=
  ![none]

noncomputable def chartLabelCode : ℕ := 14032592

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, true, true, false, false, false, false, false, false, false, true, false, true, false, false, false, false, false, false, false, false, false, true, true, true, false, false, false, false, true, true, true, false, false, false, false, false, false, false, false, true, true, true, true, true, false, false, false, false, true, false, true, true, true, true, false, false, false, false, true, true, true, true, false]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, false, false, true, true, true, true, true, true, true, false, true, false, true, true, true, true, true, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, true, true, true, true, true, true, true, false, false, false, false, false, true, true, true, true, false, true, false, false, false, false, true, true, true, true, false, false, false, false, true]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 0)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 39)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 39) chartLabelCode chartEntries
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (23 : Fin 70) = _
      rw [minorFormula_at_23]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (34 : Fin 70) = _
      rw [minorFormula_at_34]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (41 : Fin 70) = _
      rw [minorFormula_at_41]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (53 : Fin 70) = _
      rw [minorFormula_at_53]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (62 : Fin 70) = _
      rw [minorFormula_at_62]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (69 : Fin 70) = _
      rw [minorFormula_at_69]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring

noncomputable def chartForestRoots : Finset Point := {0,3}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(5,1),(6,2),(1,7)]

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
    (MatroidCatalogue.N8R4.family 39) where
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
    (MatroidCatalogue.N8R4.family 39) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart39
end

/- Source: Charts/Case40.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart40
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

end Papers.RationalityTen.Chart40
end

/- Source: ChartTables/Case40.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart40
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 1)) :=
  ![![.one, .one, .one, .one], ![.zero, .one, .zero, .variable (none)], ![.zero, .zero, .one, .variable (some (0 : Fin 1))], ![.zero, .zero, .zero, .zero]]

noncomputable def chartPositions : (Option (Fin 1)) → Coordinate × Coordinate :=
  Option.elim' (1, 3) ![(2, 3)]

noncomputable def chartUnitVariables : Fin 2 → (Option (Fin 1)) :=
  ![none, some (0 : Fin 1)]

noncomputable def chartLabelCode : ℕ := 13999888

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, true, true, false, false, false, false, false, false, false, true, false, true, false, false, false, false, false, false, false, false, false, true, true, true, false, false, false, false, true, true, true, true, false, false, false, false, false, false, false, true, true, true, true, true, false, false, false, false, true, false, true, true, true, true, false, false, false, false, true, true, true, true, false]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, false, false, true, true, true, true, true, true, true, false, true, false, true, true, true, true, true, true, true, true, true, false, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, true, true, false, false, false, false, false, true, true, true, true, false, true, false, false, false, false, true, true, true, true, false, false, false, false, true]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 1)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 40)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 40) chartLabelCode chartEntries
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (23 : Fin 70) = _
      rw [minorFormula_at_23]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (34 : Fin 70) = _
      rw [minorFormula_at_34]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (41 : Fin 70) = _
      rw [minorFormula_at_41]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (53 : Fin 70) = _
      rw [minorFormula_at_53]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (62 : Fin 70) = _
      rw [minorFormula_at_62]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (69 : Fin 70) = _
      rw [minorFormula_at_69]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring

noncomputable def chartForestRoots : Finset Point := {0,3}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(0,7),(5,1),(6,2)]

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
    (MatroidCatalogue.N8R4.family 40) where
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
    (MatroidCatalogue.N8R4.family 40) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart40
end

/- Source: Charts/Case41.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart41
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

end Papers.RationalityTen.Chart41
end

/- Source: ChartTables/Case41.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart41
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 0)) :=
  ![![.one, .zero, .zero, .one], ![.zero, .one, .one, .one], ![.zero, .one, .variable (none), .zero], ![.zero, .zero, .zero, .zero]]

noncomputable def chartPositions : (Option (Fin 0)) → Coordinate × Coordinate :=
  Option.elim' (2, 2) ![]

noncomputable def chartUnitVariables : Fin 1 → (Option (Fin 0)) :=
  ![none]

noncomputable def chartLabelCode : ℕ := 14032592

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, true, true, false, false, false, false, false, false, false, false, true, true, true, false, false, false, false, false, false, false, false, false, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, false, false, true, true, false, false, true, true, false, false, false, false, true, true, true, false, true, true, false, false, false, false, true, true, true, true, false]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, false, false, true, true, true, true, true, true, true, true, false, false, false, true, true, true, true, true, true, true, true, true, false, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, true, false, false, true, true, false, false, true, true, true, true, false, false, false, true, false, false, true, true, true, true, false, false, false, false, true]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 0)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 41)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 41) chartLabelCode chartEntries
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (34 : Fin 70) = _
      rw [minorFormula_at_34]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (41 : Fin 70) = _
      rw [minorFormula_at_41]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (52 : Fin 70) = _
      rw [minorFormula_at_52]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (53 : Fin 70) = _
      rw [minorFormula_at_53]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (62 : Fin 70) = _
      rw [minorFormula_at_62]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (69 : Fin 70) = _
      rw [minorFormula_at_69]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring

noncomputable def chartForestRoots : Finset Point := {0,3}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,7),(7,1),(1,5),(1,6),(5,2)]

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
    (MatroidCatalogue.N8R4.family 41) where
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
    (MatroidCatalogue.N8R4.family 41) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart41
end

/- Source: Charts/Case42.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart42
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

end Papers.RationalityTen.Chart42
end

/- Source: ChartTables/Case42.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart42
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Fin 0))) :=
  ![![.one, .one, .one, .zero], ![.zero, .one, .variable (none), .one], ![.zero, .zero, .one, .variable (some (none))], ![.zero, .zero, .zero, .zero]]

noncomputable def chartPositions : (Option (Option (Fin 0))) → Coordinate × Coordinate :=
  Option.elim' (1, 2) (Option.elim' (2, 3) ![])

noncomputable def chartUnitVariables : Fin 2 → (Option (Option (Fin 0))) :=
  ![none, some (none)]

noncomputable def chartLabelCode : ℕ := 13999888

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, true, true, false, false, false, false, false, false, false, true, true, true, false, false, false, false, false, false, false, false, false, true, true, true, false, false, false, false, true, true, true, false, false, false, false, false, false, false, false, true, true, true, true, true, false, false, false, false, true, true, true, false, true, true, false, false, false, false, true, true, true, true, false]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, false, false, true, true, true, true, true, true, true, false, false, false, true, true, true, true, true, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, true, true, true, true, true, true, true, false, false, false, false, false, true, true, true, true, false, false, false, true, false, false, true, true, true, true, false, false, false, false, true]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 42)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 42) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨58, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (58 : Fin 70)
      rw [minorFormula_at_58]
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (34 : Fin 70) = _
      rw [minorFormula_at_34]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (41 : Fin 70) = _
      rw [minorFormula_at_41]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (53 : Fin 70) = _
      rw [minorFormula_at_53]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (54 : Fin 70) = _
      rw [minorFormula_at_54]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (58 : Fin 70)
      rw [minorFormula_at_58]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (62 : Fin 70) = _
      rw [minorFormula_at_62]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (69 : Fin 70) = _
      rw [minorFormula_at_69]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring

noncomputable def chartForestRoots : Finset Point := {0,3}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(5,1),(6,2),(1,7)]

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
    (MatroidCatalogue.N8R4.family 42) where
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
    (MatroidCatalogue.N8R4.family 42) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart42
end

/- Source: Charts/Case43.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart43
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

end Papers.RationalityTen.Chart43
end

/- Source: ChartTables/Case43.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart43
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 1)) :=
  ![![.one, .one, .zero, .one], ![.zero, .one, .one, .variable (none)], ![.zero, .zero, .one, .variable (some (0 : Fin 1))], ![.zero, .zero, .zero, .zero]]

noncomputable def chartPositions : (Option (Fin 1)) → Coordinate × Coordinate :=
  Option.elim' (1, 3) ![(2, 3)]

noncomputable def chartUnitVariables : Fin 2 → (Option (Fin 1)) :=
  ![none, some (0 : Fin 1)]

noncomputable def chartLabelCode : ℕ := 13999888

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, true, true, false, false, false, false, false, false, false, true, true, true, false, false, false, false, false, false, false, false, false, true, true, true, false, false, false, false, true, true, false, true, false, false, false, false, false, false, false, true, true, true, true, true, false, false, false, false, true, true, true, true, true, true, false, false, false, false, true, true, true, true, false]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, false, false, true, true, true, true, true, true, true, false, false, false, true, true, true, true, true, true, true, true, true, false, false, false, true, true, true, true, false, false, true, false, true, true, true, true, true, true, true, false, false, false, false, false, true, true, true, true, false, false, false, false, false, false, true, true, true, true, false, false, false, false, true]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 1)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 43)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 43) chartLabelCode chartEntries
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (34 : Fin 70) = _
      rw [minorFormula_at_34]
      dsimp [
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (41 : Fin 70) = _
      rw [minorFormula_at_41]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (53 : Fin 70) = _
      rw [minorFormula_at_53]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (54 : Fin 70) = _
      rw [minorFormula_at_54]
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
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (62 : Fin 70) = _
      rw [minorFormula_at_62]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (69 : Fin 70) = _
      rw [minorFormula_at_69]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring

noncomputable def chartForestRoots : Finset Point := {0,3}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,7),(5,1),(1,6),(6,2)]

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
    (MatroidCatalogue.N8R4.family 43) where
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
    (MatroidCatalogue.N8R4.family 43) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart43
end

/- Source: Charts/Case44.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart44
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

end Papers.RationalityTen.Chart44
end

/- Source: ChartTables/Case44.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart44
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Fin 1))) :=
  ![![.one, .one, .one, .one], ![.zero, .one, .variable (none), .variable (some (none))], ![.zero, .zero, .one, .variable (some (some (0 : Fin 1)))], ![.zero, .zero, .zero, .zero]]

noncomputable def chartPositions : (Option (Option (Fin 1))) → Coordinate × Coordinate :=
  Option.elim' (1, 2) (Option.elim' (1, 3) ![(2, 3)])

noncomputable def chartUnitVariables : Fin 3 → (Option (Option (Fin 1))) :=
  ![none, some (none), some (some (0 : Fin 1))]

noncomputable def chartLabelCode : ℕ := 13999888

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, true, true, false, false, false, false, false, false, false, true, true, true, false, false, false, false, false, false, false, false, false, true, true, true, false, false, false, false, true, true, true, true, false, false, false, false, false, false, false, true, true, true, true, true, false, false, false, false, true, true, true, true, true, false, false, false, false, false, true, true, true, true, false]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, false, false, true, true, true, true, true, true, true, false, false, false, true, true, true, true, true, true, true, true, true, false, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, true, true, false, false, false, false, false, true, true, true, true, false, false, false, false, false, true, true, true, true, true, false, false, false, false, true]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 44)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 44) chartLabelCode chartEntries
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (34 : Fin 70) = _
      rw [minorFormula_at_34]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (41 : Fin 70) = _
      rw [minorFormula_at_41]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (53 : Fin 70) = _
      rw [minorFormula_at_53]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (54 : Fin 70) = _
      rw [minorFormula_at_54]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (62 : Fin 70) = _
      rw [minorFormula_at_62]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (69 : Fin 70) = _
      rw [minorFormula_at_69]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring

noncomputable def chartForestRoots : Finset Point := {0,3}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(0,7),(5,1),(6,2)]

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
    (MatroidCatalogue.N8R4.family 44) where
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
    (MatroidCatalogue.N8R4.family 44) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart44
end

/- Source: Charts/Case45.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart45
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

end Papers.RationalityTen.Chart45
end

/- Source: ChartTables/Case45.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart45
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 2)) :=
  ![![.one, .one, .one, .one], ![.zero, .one, .variable (none), .variable (some (0 : Fin 2))], ![.zero, .zero, .one, .variable (some (1 : Fin 2))], ![.zero, .zero, .zero, .zero]]

noncomputable def chartPositions : (Option (Fin 2)) → Coordinate × Coordinate :=
  Option.elim' (1, 2) ![(1, 3), (2, 3)]

noncomputable def chartUnitVariables : Fin 3 → (Option (Fin 2)) :=
  ![none, some (0 : Fin 2), some (1 : Fin 2)]

noncomputable def chartLabelCode : ℕ := 13999888

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, true, true, false, false, false, false, false, false, false, true, true, true, false, false, false, false, false, false, false, false, false, true, true, true, false, false, false, false, true, true, true, true, false, false, false, false, false, false, false, true, true, true, true, true, false, false, false, false, true, true, true, true, true, true, false, false, false, false, true, true, true, true, false]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, false, false, true, true, true, true, true, true, true, false, false, false, true, true, true, true, true, true, true, true, true, false, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, true, true, false, false, false, false, false, true, true, true, true, false, false, false, false, false, false, true, true, true, true, false, false, false, false, true]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 2)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 45)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 45) chartLabelCode chartEntries
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (34 : Fin 70) = _
      rw [minorFormula_at_34]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (41 : Fin 70) = _
      rw [minorFormula_at_41]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (53 : Fin 70) = _
      rw [minorFormula_at_53]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (54 : Fin 70) = _
      rw [minorFormula_at_54]
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
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (62 : Fin 70) = _
      rw [minorFormula_at_62]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (69 : Fin 70) = _
      rw [minorFormula_at_69]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring

noncomputable def chartForestRoots : Finset Point := {0,3}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(0,7),(5,1),(6,2)]

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
    (MatroidCatalogue.N8R4.family 45) where
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
    (MatroidCatalogue.N8R4.family 45) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart45
end

/- Source: Charts/Case46.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart46
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

end Papers.RationalityTen.Chart46
end

/- Source: ChartTables/Case46.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart46
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 1)) :=
  ![![.one, .zero, .zero, .one], ![.zero, .one, .one, .one], ![.zero, .one, .variable (none), .variable (some (0 : Fin 1))], ![.zero, .zero, .zero, .zero]]

noncomputable def chartPositions : (Option (Fin 1)) → Coordinate × Coordinate :=
  Option.elim' (2, 2) ![(2, 3)]

noncomputable def chartUnitVariables : Fin 2 → (Option (Fin 1)) :=
  ![none, some (0 : Fin 1)]

noncomputable def chartLabelCode : ℕ := 14032592

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, true, true, true, false, false, false, false, false, false, false, true, true, true, false, false, false, false, false, false, false, false, false, true, true, true, false, false, false, false, true, false, false, true, false, false, false, false, false, false, true, true, true, false, true, true, false, false, false, false, true, true, true, false, true, true, false, false, false, false, true, true, true, true, false]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, false, false, false, true, true, true, true, true, true, true, false, false, false, true, true, true, true, true, true, true, true, true, false, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, true, false, false, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, true, true, true, false, false, false, false, true]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 1)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 46)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 46) chartLabelCode chartEntries
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (34 : Fin 70) = _
      rw [minorFormula_at_34]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (41 : Fin 70) = _
      rw [minorFormula_at_41]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (52 : Fin 70) = _
      rw [minorFormula_at_52]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (53 : Fin 70) = _
      rw [minorFormula_at_53]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (62 : Fin 70) = _
      rw [minorFormula_at_62]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (69 : Fin 70) = _
      rw [minorFormula_at_69]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring

noncomputable def chartForestRoots : Finset Point := {0,3}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,7),(7,1),(1,5),(1,6),(5,2)]

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
    (MatroidCatalogue.N8R4.family 46) where
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
    (MatroidCatalogue.N8R4.family 46) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart46
end

/- Source: Charts/Case47.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart47
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

end Papers.RationalityTen.Chart47
end

/- Source: ChartTables/Case47.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart47
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 1)) :=
  ![![.one, .one, .one, .one], ![.one, .zero, .zero, .variable (none)], ![.zero, .one, .variable (some (0 : Fin 1)), .zero], ![.zero, .zero, .zero, .zero]]

noncomputable def chartPositions : (Option (Fin 1)) → Coordinate × Coordinate :=
  Option.elim' (1, 3) ![(2, 2)]

noncomputable def chartUnitVariables : Fin 2 → (Option (Fin 1)) :=
  ![none, some (0 : Fin 1)]

noncomputable def chartLabelCode : ℕ := 14036680

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, true, true, false, false, false, false, false, false, false, true, false, false, true, false, false, false, false, false, false, true, true, false, false, true, true, false, false, false, false, true, true, true, true, false, false, false, false, false, false, true, true, false, true, true, true, false, false, false, false, true, true, true, false, true, true, false, false, false, false, true, true, true, true, false]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, false, false, true, true, true, true, true, true, true, false, true, true, false, true, true, true, true, true, true, false, false, true, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, true, false, false, true, false, false, false, true, true, true, true, false, false, false, true, false, false, true, true, true, true, false, false, false, false, true]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 1)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 47)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 47) chartLabelCode chartEntries
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (14 : Fin 70) = _
      rw [minorFormula_at_14]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (23 : Fin 70) = _
      rw [minorFormula_at_23]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (24 : Fin 70) = _
      rw [minorFormula_at_24]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (34 : Fin 70) = _
      rw [minorFormula_at_34]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (41 : Fin 70) = _
      rw [minorFormula_at_41]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (53 : Fin 70) = _
      rw [minorFormula_at_53]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (62 : Fin 70) = _
      rw [minorFormula_at_62]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (69 : Fin 70) = _
      rw [minorFormula_at_69]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring

noncomputable def chartForestRoots : Finset Point := {0,3}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(0,7),(4,1),(5,2)]

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
    (MatroidCatalogue.N8R4.family 47) where
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
    (MatroidCatalogue.N8R4.family 47) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart47
end

/- Source: Charts/Case48.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart48
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

end Papers.RationalityTen.Chart48
end

/- Source: ChartTables/Case48.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart48
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Fin 0))) :=
  ![![.one, .one, .one, .zero], ![.one, .variable (some (none)), .zero, .one], ![.zero, .zero, .one, .variable (none)], ![.zero, .zero, .zero, .zero]]

noncomputable def chartPositions : (Option (Option (Fin 0))) → Coordinate × Coordinate :=
  Option.elim' (2, 3) (Option.elim' (1, 1) ![])

noncomputable def chartUnitVariables : Fin 2 → (Option (Option (Fin 0))) :=
  ![some (none), none]

noncomputable def chartLabelCode : ℕ := 11644808

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, true, true, false, false, false, false, false, false, true, true, false, true, false, false, false, false, false, false, false, true, true, true, true, true, false, false, false, false, true, true, true, false, false, false, false, false, false, false, false, true, true, true, true, true, false, false, false, false, true, true, true, true, true, true, false, false, false, false, true, true, false, true, false]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, false, false, true, true, true, true, true, true, false, false, true, false, true, true, true, true, true, true, true, false, false, false, false, false, true, true, true, true, false, false, false, true, true, true, true, true, true, true, true, false, false, false, false, false, true, true, true, true, false, false, false, false, false, false, true, true, true, true, false, false, true, false, true]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 48)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 48) chartLabelCode chartEntries
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (23 : Fin 70) = _
      rw [minorFormula_at_23]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (33 : Fin 70) = _
      rw [minorFormula_at_33]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (34 : Fin 70) = _
      rw [minorFormula_at_34]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (41 : Fin 70) = _
      rw [minorFormula_at_41]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (53 : Fin 70) = _
      rw [minorFormula_at_53]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (54 : Fin 70) = _
      rw [minorFormula_at_54]
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
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (62 : Fin 70) = _
      rw [minorFormula_at_62]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (67 : Fin 70)
      rw [minorFormula_at_67]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (69 : Fin 70) = _
      rw [minorFormula_at_69]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring

noncomputable def chartForestRoots : Finset Point := {0,3}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(4,1),(6,2),(1,7)]

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
    (MatroidCatalogue.N8R4.family 48) where
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
    (MatroidCatalogue.N8R4.family 48) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart48
end

/- Source: Charts/Case49.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart49
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

end Papers.RationalityTen.Chart49
end

/- Source: ChartTables/Case49.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart49
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 1)) :=
  ![![.one, .one, .zero, .one], ![.one, .variable (none), .one, .zero], ![.zero, .zero, .one, .variable (some (0 : Fin 1))], ![.zero, .zero, .zero, .zero]]

noncomputable def chartPositions : (Option (Fin 1)) → Coordinate × Coordinate :=
  Option.elim' (1, 1) ![(2, 3)]

noncomputable def chartUnitVariables : Fin 2 → (Option (Fin 1)) :=
  ![none, some (0 : Fin 1)]

noncomputable def chartLabelCode : ℕ := 14003976

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, true, true, false, false, false, false, false, false, true, true, true, false, false, false, false, false, false, false, false, true, true, true, true, true, false, false, false, false, true, true, false, true, false, false, false, false, false, false, false, true, true, true, true, true, false, false, false, false, true, true, true, true, true, true, false, false, false, false, true, true, true, true, false]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, false, false, true, true, true, true, true, true, false, false, false, true, true, true, true, true, true, true, true, false, false, false, false, false, true, true, true, true, false, false, true, false, true, true, true, true, true, true, true, false, false, false, false, false, true, true, true, true, false, false, false, false, false, false, true, true, true, true, false, false, false, false, true]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 1)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 49)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 49) chartLabelCode chartEntries
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (14 : Fin 70) = _
      rw [minorFormula_at_14]
      dsimp [
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (23 : Fin 70) = _
      rw [minorFormula_at_23]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (33 : Fin 70) = _
      rw [minorFormula_at_33]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (34 : Fin 70) = _
      rw [minorFormula_at_34]
      dsimp [
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (41 : Fin 70) = _
      rw [minorFormula_at_41]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (53 : Fin 70) = _
      rw [minorFormula_at_53]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (54 : Fin 70) = _
      rw [minorFormula_at_54]
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
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (62 : Fin 70) = _
      rw [minorFormula_at_62]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (69 : Fin 70) = _
      rw [minorFormula_at_69]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring

noncomputable def chartForestRoots : Finset Point := {0,3}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,7),(4,1),(1,6),(6,2)]

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
    (MatroidCatalogue.N8R4.family 49) where
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
    (MatroidCatalogue.N8R4.family 49) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart49
end

/- Source: Charts/Case50.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart50
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

end Papers.RationalityTen.Chart50
end

/- Source: ChartTables/Case50.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart50
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 2)) :=
  ![![.one, .one, .one, .one], ![.one, .variable (none), .zero, .variable (some (0 : Fin 2))], ![.zero, .zero, .one, .variable (some (1 : Fin 2))], ![.zero, .zero, .zero, .zero]]

noncomputable def chartPositions : (Option (Fin 2)) → Coordinate × Coordinate :=
  Option.elim' (1, 1) ![(1, 3), (2, 3)]

noncomputable def chartUnitVariables : Fin 3 → (Option (Fin 2)) :=
  ![none, some (0 : Fin 2), some (1 : Fin 2)]

noncomputable def chartLabelCode : ℕ := 14003976

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, true, true, false, false, false, false, false, false, true, true, false, true, false, false, false, false, false, false, false, true, true, true, true, true, false, false, false, false, true, true, true, true, false, false, false, false, false, false, false, true, true, true, true, true, false, false, false, false, true, true, true, true, true, true, false, false, false, false, true, true, true, true, false]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, false, false, true, true, true, true, true, true, false, false, true, false, true, true, true, true, true, true, true, false, false, false, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, true, true, false, false, false, false, false, true, true, true, true, false, false, false, false, false, false, true, true, true, true, false, false, false, false, true]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 2)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 50)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 50) chartLabelCode chartEntries
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (23 : Fin 70) = _
      rw [minorFormula_at_23]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (33 : Fin 70) = _
      rw [minorFormula_at_33]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (34 : Fin 70) = _
      rw [minorFormula_at_34]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (41 : Fin 70) = _
      rw [minorFormula_at_41]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (53 : Fin 70) = _
      rw [minorFormula_at_53]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (54 : Fin 70) = _
      rw [minorFormula_at_54]
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
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (62 : Fin 70) = _
      rw [minorFormula_at_62]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (69 : Fin 70) = _
      rw [minorFormula_at_69]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring

noncomputable def chartForestRoots : Finset Point := {0,3}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(0,7),(4,1),(6,2)]

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
    (MatroidCatalogue.N8R4.family 50) where
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
    (MatroidCatalogue.N8R4.family 50) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart50
end

/- Source: Charts/Case51.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart51
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

end Papers.RationalityTen.Chart51
end

/- Source: ChartTables/Case51.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart51
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Fin 2))) :=
  ![![.one, .one, .one, .one], ![.one, .variable (some (none)), .variable (none), .variable (some (some (0 : Fin 2)))], ![.zero, .zero, .one, .variable (some (some (1 : Fin 2)))], ![.zero, .zero, .zero, .zero]]

noncomputable def chartPositions : (Option (Option (Fin 2))) → Coordinate × Coordinate :=
  Option.elim' (1, 2) (Option.elim' (1, 1) ![(1, 3), (2, 3)])

noncomputable def chartUnitVariables : Fin 4 → (Option (Option (Fin 2))) :=
  ![some (none), none, some (some (0 : Fin 2)), some (some (1 : Fin 2))]

noncomputable def chartLabelCode : ℕ := 14003976

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, true, true, false, false, false, false, false, false, true, true, true, true, false, false, false, false, false, false, false, true, true, true, true, true, false, false, false, false, true, true, true, true, false, false, false, false, false, false, false, true, true, true, true, true, false, false, false, false, true, true, true, true, true, false, false, false, false, false, true, true, true, true, false]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, false, false, true, true, true, true, true, true, false, false, false, false, true, true, true, true, true, true, true, false, false, false, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, true, true, false, false, false, false, false, true, true, true, true, false, false, false, false, false, true, true, true, true, true, false, false, false, false, true]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Fin 2))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 51)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 51) chartLabelCode chartEntries
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (14 : Fin 70) = _
      rw [minorFormula_at_14]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (23 : Fin 70) = _
      rw [minorFormula_at_23]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (33 : Fin 70) = _
      rw [minorFormula_at_33]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (34 : Fin 70) = _
      rw [minorFormula_at_34]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (41 : Fin 70) = _
      rw [minorFormula_at_41]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (53 : Fin 70) = _
      rw [minorFormula_at_53]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (54 : Fin 70) = _
      rw [minorFormula_at_54]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (62 : Fin 70) = _
      rw [minorFormula_at_62]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (69 : Fin 70) = _
      rw [minorFormula_at_69]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring

noncomputable def chartForestRoots : Finset Point := {0,3}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(0,7),(4,1),(6,2)]

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
    (MatroidCatalogue.N8R4.family 51) where
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
    (MatroidCatalogue.N8R4.family 51) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart51
end

/- Source: Charts/Case52.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart52
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

end Papers.RationalityTen.Chart52
end

/- Source: ChartTables/Case52.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart52
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 3)) :=
  ![![.one, .one, .one, .one], ![.one, .variable (none), .variable (some (0 : Fin 3)), .variable (some (1 : Fin 3))], ![.zero, .zero, .one, .variable (some (2 : Fin 3))], ![.zero, .zero, .zero, .zero]]

noncomputable def chartPositions : (Option (Fin 3)) → Coordinate × Coordinate :=
  Option.elim' (1, 1) ![(1, 2), (1, 3), (2, 3)]

noncomputable def chartUnitVariables : Fin 4 → (Option (Fin 3)) :=
  ![none, some (0 : Fin 3), some (1 : Fin 3), some (2 : Fin 3)]

noncomputable def chartLabelCode : ℕ := 14003976

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, true, true, false, false, false, false, false, false, true, true, true, true, false, false, false, false, false, false, false, true, true, true, true, true, false, false, false, false, true, true, true, true, false, false, false, false, false, false, false, true, true, true, true, true, false, false, false, false, true, true, true, true, true, true, false, false, false, false, true, true, true, true, false]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, false, false, true, true, true, true, true, true, false, false, false, false, true, true, true, true, true, true, true, false, false, false, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, true, true, false, false, false, false, false, true, true, true, true, false, false, false, false, false, false, true, true, true, true, false, false, false, false, true]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 3)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 52)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 52) chartLabelCode chartEntries
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (14 : Fin 70) = _
      rw [minorFormula_at_14]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (23 : Fin 70) = _
      rw [minorFormula_at_23]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (33 : Fin 70) = _
      rw [minorFormula_at_33]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (34 : Fin 70) = _
      rw [minorFormula_at_34]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (41 : Fin 70) = _
      rw [minorFormula_at_41]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (53 : Fin 70) = _
      rw [minorFormula_at_53]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (54 : Fin 70) = _
      rw [minorFormula_at_54]
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
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (62 : Fin 70) = _
      rw [minorFormula_at_62]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (69 : Fin 70) = _
      rw [minorFormula_at_69]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring

noncomputable def chartForestRoots : Finset Point := {0,3}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(0,7),(4,1),(6,2)]

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
    (MatroidCatalogue.N8R4.family 52) where
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
    (MatroidCatalogue.N8R4.family 52) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart52
end

/- Source: Charts/Case53.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart53
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 1 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![-(X (none)) + (1)]
noncomputable def U0 : Fin 3 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![X (some (none)), X (none), X (some (some (0 : Fin 1)))]
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
  ![X (none), 1, X (some (0 : Fin 1))]

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
  unit_power := ![0, 1, 0]
  unit_quotient := ![0, 1, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 1 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![0]
noncomputable def U1 : Fin 3 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![X (none), 1, X (some (0 : Fin 1))]
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

end Papers.RationalityTen.Chart53
end

/- Source: ChartTables/Case53.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart53
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Fin 1))) :=
  ![![.one, .one, .one, .zero], ![.zero, .one, .variable (some (none)), .one], ![.zero, .one, .variable (none), .variable (some (some (0 : Fin 1)))], ![.zero, .zero, .zero, .zero]]

noncomputable def chartPositions : (Option (Option (Fin 1))) → Coordinate × Coordinate :=
  Option.elim' (2, 2) (Option.elim' (1, 2) ![(2, 3)])

noncomputable def chartUnitVariables : Fin 3 → (Option (Option (Fin 1))) :=
  ![some (none), none, some (some (0 : Fin 1))]

noncomputable def chartLabelCode : ℕ := 14032592

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, true, true, true, false, false, false, false, false, false, false, true, true, true, false, false, false, false, false, false, false, false, false, true, true, true, false, false, false, false, true, true, true, false, false, false, false, false, false, false, true, true, true, false, true, true, false, false, false, false, true, true, true, true, true, true, false, false, false, false, true, true, true, true, false]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, false, false, false, true, true, true, true, true, true, true, false, false, false, true, true, true, true, true, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, true, true, true, true, true, true, false, false, false, true, false, false, true, true, true, true, false, false, false, false, false, false, true, true, true, true, false, false, false, false, true]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 53)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 53) chartLabelCode chartEntries
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (34 : Fin 70) = _
      rw [minorFormula_at_34]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (41 : Fin 70) = _
      rw [minorFormula_at_41]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (48 : Fin 70)
      rw [minorFormula_at_48]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (53 : Fin 70) = _
      rw [minorFormula_at_53]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (54 : Fin 70) = _
      rw [minorFormula_at_54]
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
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (62 : Fin 70) = _
      rw [minorFormula_at_62]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (69 : Fin 70) = _
      rw [minorFormula_at_69]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring

noncomputable def chartForestRoots : Finset Point := {0,3}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(5,1),(5,2),(1,7)]

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
    (MatroidCatalogue.N8R4.family 53) where
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
    (MatroidCatalogue.N8R4.family 53) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart53
end

/- Source: Charts/Case54.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart54
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

end Papers.RationalityTen.Chart54
end

/- Source: ChartTables/Case54.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart54
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 2)) :=
  ![![.one, .zero, .one, .one], ![.zero, .one, .one, .variable (none)], ![.zero, .one, .variable (some (0 : Fin 2)), .variable (some (1 : Fin 2))], ![.zero, .zero, .zero, .zero]]

noncomputable def chartPositions : (Option (Fin 2)) → Coordinate × Coordinate :=
  Option.elim' (1, 3) ![(2, 2), (2, 3)]

noncomputable def chartUnitVariables : Fin 3 → (Option (Fin 2)) :=
  ![none, some (0 : Fin 2), some (1 : Fin 2)]

noncomputable def chartLabelCode : ℕ := 14032592

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, true, true, true, false, false, false, false, false, false, false, true, true, true, false, false, false, false, false, false, false, false, false, true, true, true, false, false, false, false, true, false, true, true, false, false, false, false, false, false, true, true, true, true, true, true, false, false, false, false, true, true, true, true, true, true, false, false, false, false, true, true, true, true, false]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, false, false, false, true, true, true, true, true, true, true, false, false, false, true, true, true, true, true, true, true, true, true, false, false, false, true, true, true, true, false, true, false, false, true, true, true, true, true, true, false, false, false, false, false, false, true, true, true, true, false, false, false, false, false, false, true, true, true, true, false, false, false, false, true]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 2)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 54)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 54) chartLabelCode chartEntries
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (34 : Fin 70) = _
      rw [minorFormula_at_34]
      dsimp [
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (41 : Fin 70) = _
      rw [minorFormula_at_41]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (53 : Fin 70) = _
      rw [minorFormula_at_53]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (54 : Fin 70) = _
      rw [minorFormula_at_54]
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
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (62 : Fin 70) = _
      rw [minorFormula_at_62]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (69 : Fin 70) = _
      rw [minorFormula_at_69]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring

noncomputable def chartForestRoots : Finset Point := {0,3}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,6),(0,7),(6,1),(1,5),(5,2)]

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
    (MatroidCatalogue.N8R4.family 54) where
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
    (MatroidCatalogue.N8R4.family 54) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart54
end

/- Source: Charts/Case55.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart55
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

end Papers.RationalityTen.Chart55
end

/- Source: ChartTables/Case55.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart55
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 3)) :=
  ![![.one, .one, .one, .one], ![.zero, .one, .variable (none), .variable (some (0 : Fin 3))], ![.zero, .one, .variable (some (1 : Fin 3)), .variable (some (2 : Fin 3))], ![.zero, .zero, .zero, .zero]]

noncomputable def chartPositions : (Option (Fin 3)) → Coordinate × Coordinate :=
  Option.elim' (1, 2) ![(1, 3), (2, 2), (2, 3)]

noncomputable def chartUnitVariables : Fin 4 → (Option (Fin 3)) :=
  ![none, some (0 : Fin 3), some (1 : Fin 3), some (2 : Fin 3)]

noncomputable def chartLabelCode : ℕ := 14032592

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, true, true, true, false, false, false, false, false, false, false, true, true, true, false, false, false, false, false, false, false, false, false, true, true, true, false, false, false, false, true, true, true, true, false, false, false, false, false, false, true, true, true, true, true, true, false, false, false, false, true, true, true, true, true, true, false, false, false, false, true, true, true, true, false]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, false, false, false, true, true, true, true, true, true, true, false, false, false, true, true, true, true, true, true, true, true, true, false, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, true, false, false, false, false, false, false, true, true, true, true, false, false, false, false, false, false, true, true, true, true, false, false, false, false, true]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 3)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 55)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 55) chartLabelCode chartEntries
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (34 : Fin 70) = _
      rw [minorFormula_at_34]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (41 : Fin 70) = _
      rw [minorFormula_at_41]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (53 : Fin 70) = _
      rw [minorFormula_at_53]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (54 : Fin 70) = _
      rw [minorFormula_at_54]
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
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (62 : Fin 70) = _
      rw [minorFormula_at_62]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (69 : Fin 70) = _
      rw [minorFormula_at_69]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring

noncomputable def chartForestRoots : Finset Point := {0,3}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(0,7),(5,1),(5,2)]

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
    (MatroidCatalogue.N8R4.family 55) where
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
    (MatroidCatalogue.N8R4.family 55) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart55
end

/- Source: Charts/Case56.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart56
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 4 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![-(X (none) * X (some (none))) + (X (some (some (none)))), -(X (some (some (none)))) + (1), X (none) - (1), X (some (none)) + (1)]
noncomputable def U0 : Fin 3 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none), X (some (none)), X (some (some (none)))]
noncomputable def R0 : Fin 4 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
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

noncomputable def nextE0 : Fin 4 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (none) - (X (some (none))), X (some (none)) - (1), 0, X (none) + (1)]
noncomputable def nextU0 : Fin 3 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![1, X (none), X (some (none))]

noncomputable def step0 : LinearStep (Option (Option (Fin 0))) 4 3 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := 1
  b := -(1)
  pivot := 2
  pivot_identity := by simp [R0]<;> ring
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
  unit_power := ![1, 0, 0]
  unit_quotient := ![1, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 4 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (none) - (X (some (none))), X (some (none)) - (1), 0, X (none) + (1)]
noncomputable def U1 : Fin 3 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![1, X (none), X (some (none))]
noncomputable def R1 : Fin 4 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
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

noncomputable def nextE1 : Fin 4 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, X (none) - (1), 0, X (none) + (1)]
noncomputable def nextU1 : Fin 3 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![1, X (none), X (none)]

noncomputable def step1 : LinearStep (Option (Fin 0)) 4 3 where
  sourceE := R1
  sourceU := U1
  targetE := nextE1
  targetU := nextU1
  a := 1
  b := -(X (none))
  pivot := 0
  pivot_identity := by simp [R1]<;> ring
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
  unit_power := ![0, 1, 0]
  unit_quotient := ![0, 1, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring

noncomputable def E2 : Fin 4 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, X (none) - (1), 0, X (none) + (1)]
noncomputable def U2 : Fin 3 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![1, X (none), X (none)]
noncomputable def R2 : Fin 4 → MvPolynomial (Option (Fin 0)) ℚ :=
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

noncomputable def nextE2 : Fin 4 → MvPolynomial (Fin 0) ℚ :=
  ![0, 0, 0, 2]
noncomputable def nextU2 : Fin 3 → MvPolynomial (Fin 0) ℚ :=
  ![1, 1, 1]

noncomputable def step2 : LinearStep (Fin 0) 4 3 where
  sourceE := R2
  sourceU := U2
  targetE := nextE2
  targetU := nextU2
  a := 1
  b := -(1)
  pivot := 1
  pivot_identity := by simp [R2]<;> ring
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
  unit_power := ![0, 1, 1]
  unit_quotient := ![0, 1, 1]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring

noncomputable def E3 : Fin 4 → MvPolynomial (Fin 0) ℚ :=
  ![0, 0, 0, 2]
noncomputable def U3 : Fin 3 → MvPolynomial (Fin 0) ℚ :=
  ![1, 1, 1]
noncomputable def R3 : Fin 4 → MvPolynomial (Fin 0) ℚ :=
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

end Papers.RationalityTen.Chart56
end

/- Source: ChartTables/Case56.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart56
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Option (Fin 0)))) :=
  ![![.one, .one, .zero, .one], ![.one, .zero, .one, .variable (none)], ![.zero, .one, .variable (some (none)), .variable (some (some (none)))], ![.zero, .zero, .zero, .zero]]

noncomputable def chartPositions : (Option (Option (Option (Fin 0)))) → Coordinate × Coordinate :=
  Option.elim' (1, 3) (Option.elim' (2, 2) (Option.elim' (2, 3) (Fin.elim0)))

noncomputable def chartUnitVariables : Fin 3 → (Option (Option (Option (Fin 0)))) :=
  ![none, some (none), some (some (none))]

noncomputable def chartLabelCode : ℕ := 14040712

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, true, true, true, false, false, false, false, false, false, true, false, true, true, false, false, false, false, false, false, true, true, true, true, true, false, false, false, false, false, true, true, false, true, false, false, false, false, false, false, true, true, true, true, false, true, false, false, false, false, true, true, false, true, true, true, false, false, false, false, false, true, true, true, false]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, false, false, false, true, true, true, true, true, true, false, true, false, false, true, true, true, true, true, true, false, false, false, false, false, true, true, true, true, true, false, false, true, false, true, true, true, true, true, true, false, false, false, false, true, false, true, true, true, true, false, false, true, false, false, false, true, true, true, true, true, false, false, false, true]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 56)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 56) chartLabelCode chartEntries
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (23 : Fin 70) = _
      rw [minorFormula_at_23]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (24 : Fin 70) = _
      rw [minorFormula_at_24]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (34 : Fin 70) = _
      rw [minorFormula_at_34]
      dsimp [
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (41 : Fin 70) = _
      rw [minorFormula_at_41]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨1, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (49 : Fin 70)
      rw [minorFormula_at_49]
      dsimp [E0,
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (53 : Fin 70) = _
      rw [minorFormula_at_53]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (54 : Fin 70) = _
      rw [minorFormula_at_54]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (62 : Fin 70) = _
      rw [minorFormula_at_62]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · refine Or.inr ⟨3, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (65 : Fin 70)
      rw [minorFormula_at_65]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (69 : Fin 70) = _
      rw [minorFormula_at_69]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring

noncomputable def chartForestRoots : Finset Point := {0,3}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,7),(4,1),(5,2),(1,6)]

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

noncomputable def chart_certificate : ChartCertificate (Option (Option (Option (Fin 0)))) 4 3
    (MatroidCatalogue.N8R4.family 56) where
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
    (MatroidCatalogue.N8R4.family 56) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart56
end

/- Source: Charts/Case57.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart57
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 3 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![-(X (some (none))) + (1), X (none) - (1), X (some (some (none))) - (1)]
noncomputable def U0 : Fin 3 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none), X (some (none)), X (some (some (none)))]
noncomputable def R0 : Fin 3 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (some (none)) - (1), X (none) - (1), X (some (some (none))) - (1)]

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

noncomputable def nextE0 : Fin 3 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (none) - (1), 0, X (some (none)) - (1)]
noncomputable def nextU0 : Fin 3 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![1, X (none), X (some (none))]

noncomputable def step0 : LinearStep (Option (Option (Fin 0))) 3 3 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := 1
  b := -(1)
  pivot := 1
  pivot_identity := by simp [R0]<;> ring
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
  unit_power := ![1, 0, 0]
  unit_quotient := ![1, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 3 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (none) - (1), 0, X (some (none)) - (1)]
noncomputable def U1 : Fin 3 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![1, X (none), X (some (none))]
noncomputable def R1 : Fin 3 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (none) - (1), 0, X (some (none)) - (1)]

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
  ![0, 0, X (none) - (1)]
noncomputable def nextU1 : Fin 3 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![1, 1, X (none)]

noncomputable def step1 : LinearStep (Option (Fin 0)) 3 3 where
  sourceE := R1
  sourceU := U1
  targetE := nextE1
  targetU := nextU1
  a := 1
  b := -(1)
  pivot := 0
  pivot_identity := by simp [R1]<;> ring
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
  unit_power := ![0, 1, 0]
  unit_quotient := ![0, 1, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring

noncomputable def E2 : Fin 3 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, X (none) - (1)]
noncomputable def U2 : Fin 3 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![1, 1, X (none)]
noncomputable def R2 : Fin 3 → MvPolynomial (Option (Fin 0)) ℚ :=
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
  ![1, 1, 1]

noncomputable def step2 : LinearStep (Fin 0) 3 3 where
  sourceE := R2
  sourceU := U2
  targetE := nextE2
  targetU := nextU2
  a := 1
  b := -(1)
  pivot := 2
  pivot_identity := by simp [R2]<;> ring
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
  unit_power := ![0, 0, 1]
  unit_quotient := ![0, 0, 1]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring

noncomputable def E3 : Fin 3 → MvPolynomial (Fin 0) ℚ :=
  ![0, 0, 0]
noncomputable def U3 : Fin 3 → MvPolynomial (Fin 0) ℚ :=
  ![1, 1, 1]
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

end Papers.RationalityTen.Chart57
end

/- Source: ChartTables/Case57.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart57
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Option (Fin 0)))) :=
  ![![.one, .one, .one, .zero], ![.one, .zero, .variable (none), .one], ![.one, .variable (some (none)), .zero, .variable (some (some (none)))], ![.zero, .zero, .zero, .zero]]

noncomputable def chartPositions : (Option (Option (Option (Fin 0)))) → Coordinate × Coordinate :=
  Option.elim' (1, 2) (Option.elim' (2, 1) (Option.elim' (2, 3) (Fin.elim0)))

noncomputable def chartUnitVariables : Fin 3 → (Option (Option (Option (Fin 0)))) :=
  ![none, some (none), some (some (none))]

noncomputable def chartLabelCode : ℕ := 14040712

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, true, true, false, true, false, false, false, false, false, false, true, false, true, true, false, false, false, false, false, false, true, true, false, true, true, true, false, false, false, false, true, true, true, false, false, false, false, false, false, false, false, true, true, true, true, true, false, false, false, false, true, false, true, true, true, true, false, false, false, false, true, true, true, true, false]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, false, false, true, false, true, true, true, true, true, true, false, true, false, false, true, true, true, true, true, true, false, false, true, false, false, false, true, true, true, true, false, false, false, true, true, true, true, true, true, true, true, false, false, false, false, false, true, true, true, true, false, true, false, false, false, false, true, true, true, true, false, false, false, false, true]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 57)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 57) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨45, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (45 : Fin 70)
      rw [minorFormula_at_45]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨56, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (56 : Fin 70)
      rw [minorFormula_at_56]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨27, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (27 : Fin 70)
      rw [minorFormula_at_27]
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (14 : Fin 70) = _
      rw [minorFormula_at_14]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (23 : Fin 70) = _
      rw [minorFormula_at_23]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (24 : Fin 70) = _
      rw [minorFormula_at_24]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨2, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (27 : Fin 70)
      rw [minorFormula_at_27]
      dsimp [E0,
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (34 : Fin 70) = _
      rw [minorFormula_at_34]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (41 : Fin 70) = _
      rw [minorFormula_at_41]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (45 : Fin 70)
      rw [minorFormula_at_45]
      dsimp [E0,
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (53 : Fin 70) = _
      rw [minorFormula_at_53]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (54 : Fin 70) = _
      rw [minorFormula_at_54]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (62 : Fin 70) = _
      rw [minorFormula_at_62]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (69 : Fin 70) = _
      rw [minorFormula_at_69]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring

noncomputable def chartForestRoots : Finset Point := {0,3}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(4,1),(4,2),(1,7)]

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
    (MatroidCatalogue.N8R4.family 57) where
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
    (MatroidCatalogue.N8R4.family 57) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart57
end

/- Source: Charts/Case58.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart58
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 2 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none) - (X (some (none))), X (some (none)) - (1)]
noncomputable def U0 : Fin 3 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (some (some (none))), X (none), X (some (none))]
noncomputable def R0 : Fin 2 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none) - (X (some (none))), X (some (none)) - (1)]

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
  ![0, X (none) - (1)]
noncomputable def nextU0 : Fin 3 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (some (none)), X (none), X (none)]

noncomputable def step0 : LinearStep (Option (Option (Fin 0))) 2 3 where
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
  equation_power := ![1, 0]
  equation_quotient := ![1, 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![0, 1, 0]
  unit_quotient := ![0, 1, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 2 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, X (none) - (1)]
noncomputable def U1 : Fin 3 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (some (none)), X (none), X (none)]
noncomputable def R1 : Fin 2 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
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
  ![X (none), 1, 1]

noncomputable def step1 : LinearStep (Option (Fin 0)) 2 3 where
  sourceE := R1
  sourceU := U1
  targetE := nextE1
  targetU := nextU1
  a := 1
  b := -(1)
  pivot := 1
  pivot_identity := by simp [R1]<;> ring
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
  unit_power := ![0, 1, 1]
  unit_quotient := ![0, 1, 1]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring

noncomputable def E2 : Fin 2 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0]
noncomputable def U2 : Fin 3 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none), 1, 1]
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

end Papers.RationalityTen.Chart58
end

/- Source: ChartTables/Case58.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart58
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Option (Fin 0)))) :=
  ![![.zero, .one, .one, .one], ![.one, .zero, .one, .variable (some (some (none)))], ![.one, .variable (none), .variable (some (none)), .zero], ![.zero, .zero, .zero, .zero]]

noncomputable def chartPositions : (Option (Option (Option (Fin 0)))) → Coordinate × Coordinate :=
  Option.elim' (2, 1) (Option.elim' (2, 2) (Option.elim' (1, 3) ![]))

noncomputable def chartUnitVariables : Fin 3 → (Option (Option (Option (Fin 0)))) :=
  ![some (some (none)), none, some (none)]

noncomputable def chartLabelCode : ℕ := 14040712

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, true, true, true, false, false, false, false, false, false, false, true, false, true, true, false, false, false, false, false, false, true, false, true, true, true, true, false, false, false, false, false, true, true, true, false, false, false, false, false, false, true, true, true, false, true, true, false, false, false, false, true, true, true, true, true, true, false, false, false, false, true, true, true, true, false]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, false, false, false, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, true, true, false, true, false, false, false, false, true, true, true, true, true, false, false, false, true, true, true, true, true, true, false, false, false, true, false, false, true, true, true, true, false, false, false, false, false, false, true, true, true, true, false, false, false, false, true]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 58)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 58) chartLabelCode chartEntries
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
    · refine ⟨26, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (26 : Fin 70)
      rw [minorFormula_at_26]
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (14 : Fin 70) = _
      rw [minorFormula_at_14]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (23 : Fin 70) = _
      rw [minorFormula_at_23]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (24 : Fin 70) = _
      rw [minorFormula_at_24]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨1, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (26 : Fin 70)
      rw [minorFormula_at_26]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (33 : Fin 70) = _
      rw [minorFormula_at_33]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (34 : Fin 70) = _
      rw [minorFormula_at_34]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (35 : Fin 70) = _
      rw [minorFormula_at_35]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (41 : Fin 70) = _
      rw [minorFormula_at_41]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (48 : Fin 70)
      rw [minorFormula_at_48]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (53 : Fin 70) = _
      rw [minorFormula_at_53]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (54 : Fin 70) = _
      rw [minorFormula_at_54]
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
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (62 : Fin 70) = _
      rw [minorFormula_at_62]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (69 : Fin 70) = _
      rw [minorFormula_at_69]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring

noncomputable def chartForestRoots : Finset Point := {0,3}
noncomputable def chartForestSteps : List (Point × Point) := [(0,5),(0,6),(0,7),(6,1),(1,4),(4,2)]

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
    (MatroidCatalogue.N8R4.family 58) where
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
    (MatroidCatalogue.N8R4.family 58) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart58
end

/- Source: Charts/Case59.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart59
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

end Papers.RationalityTen.Chart59
end

/- Source: ChartTables/Case59.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart59
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Fin 1))) :=
  ![![.one, .one, .zero, .one], ![.one, .zero, .one, .variable (some (none))], ![.zero, .one, .variable (none), .variable (some (some (0 : Fin 1)))], ![.zero, .zero, .zero, .zero]]

noncomputable def chartPositions : (Option (Option (Fin 1))) → Coordinate × Coordinate :=
  Option.elim' (2, 2) (Option.elim' (1, 3) ![(2, 3)])

noncomputable def chartUnitVariables : Fin 3 → (Option (Option (Fin 1))) :=
  ![some (none), none, some (some (0 : Fin 1))]

noncomputable def chartLabelCode : ℕ := 14040712

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, true, true, true, false, false, false, false, false, false, true, false, true, true, false, false, false, false, false, false, true, true, true, true, true, true, false, false, false, false, true, true, false, true, false, false, false, false, false, false, true, true, true, true, true, true, false, false, false, false, true, true, true, true, true, true, false, false, false, false, false, true, true, true, false]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, false, false, false, true, true, true, true, true, true, false, true, false, false, true, true, true, true, true, true, false, false, false, false, false, false, true, true, true, true, false, false, true, false, true, true, true, true, true, true, false, false, false, false, false, false, true, true, true, true, false, false, false, false, false, false, true, true, true, true, true, false, false, false, true]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 59)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 59) chartLabelCode chartEntries
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (23 : Fin 70) = _
      rw [minorFormula_at_23]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (24 : Fin 70) = _
      rw [minorFormula_at_24]
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (34 : Fin 70) = _
      rw [minorFormula_at_34]
      dsimp [
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (41 : Fin 70) = _
      rw [minorFormula_at_41]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (53 : Fin 70) = _
      rw [minorFormula_at_53]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (54 : Fin 70) = _
      rw [minorFormula_at_54]
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
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (62 : Fin 70) = _
      rw [minorFormula_at_62]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (65 : Fin 70)
      rw [minorFormula_at_65]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (69 : Fin 70) = _
      rw [minorFormula_at_69]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring

noncomputable def chartForestRoots : Finset Point := {0,3}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,7),(4,1),(5,2),(1,6)]

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
    (MatroidCatalogue.N8R4.family 59) where
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
    (MatroidCatalogue.N8R4.family 59) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart59
end

/- Source: Charts/Case60.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart60
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 2 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![-(X (some (none)) * X (some (some (none)))) + (X (some (none))) + (X (some (some (none)))), X (none) - (1)]
noncomputable def U0 : Fin 3 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (some (none)), X (some (some (none))), X (none)]
noncomputable def R0 : Fin 2 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (some (none)) * X (some (some (none))) - (X (some (none))) - (X (some (some (none)))), X (none) - (1)]

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
  ![X (none) * X (some (none)) - (X (none)) - (X (some (none))), 0]
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
  pivot_identity := by simp [R0]<;> ring
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
  unit_power := ![0, 0, 1]
  unit_quotient := ![0, 0, 1]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 2 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (none) * X (some (none)) - (X (none)) - (X (some (none))), 0]
noncomputable def U1 : Fin 3 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (none), X (some (none)), 1]
noncomputable def R1 : Fin 2 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (none) * X (some (none)) - (X (none)) - (X (some (none))), 0]

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
  a := X (none) - (1)
  b := -(X (none))
  pivot := 0
  pivot_identity := by simp [R1]<;> ring
  coefficient_or_constant_unit := Sum.inr {
      count := 1
      selected := ![1]
      quotient := -(1)
      identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1, 0]
  equation_quotient := ![X (some (none)) - (1), 0]
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

end Papers.RationalityTen.Chart60
end

/- Source: ChartTables/Case60.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart60
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Option (Fin 0)))) :=
  ![![.one, .one, .one, .zero], ![.one, .variable (some (none)), .zero, .one], ![.one, .zero, .variable (some (some (none))), .variable (none)], ![.zero, .zero, .zero, .zero]]

noncomputable def chartPositions : (Option (Option (Option (Fin 0)))) → Coordinate × Coordinate :=
  Option.elim' (2, 3) (Option.elim' (1, 1) (Option.elim' (2, 2) ![]))

noncomputable def chartUnitVariables : Fin 3 → (Option (Option (Option (Fin 0)))) :=
  ![some (none), some (some (none)), none]

noncomputable def chartLabelCode : ℕ := 14040712

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, true, false, true, true, false, false, false, false, false, false, true, true, false, true, false, false, false, false, false, false, true, true, false, true, true, true, false, false, false, false, true, true, true, false, false, false, false, false, false, false, true, true, true, true, true, true, false, false, false, false, true, true, true, true, true, true, false, false, false, false, false, true, true, true, false]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, false, true, false, false, true, true, true, true, true, true, false, false, true, false, true, true, true, true, true, true, false, false, true, false, false, false, true, true, true, true, false, false, false, true, true, true, true, true, true, true, false, false, false, false, false, false, true, true, true, true, false, false, false, false, false, false, true, true, true, true, true, false, false, false, true]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 60)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 60) chartLabelCode chartEntries
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
    · refine ⟨27, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (27 : Fin 70)
      rw [minorFormula_at_27]
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (4 : Fin 70) = _
      rw [minorFormula_at_4]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (23 : Fin 70) = _
      rw [minorFormula_at_23]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (24 : Fin 70) = _
      rw [minorFormula_at_24]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨1, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (27 : Fin 70)
      rw [minorFormula_at_27]
      dsimp [E0,
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (34 : Fin 70) = _
      rw [minorFormula_at_34]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (41 : Fin 70) = _
      rw [minorFormula_at_41]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (53 : Fin 70) = _
      rw [minorFormula_at_53]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (54 : Fin 70) = _
      rw [minorFormula_at_54]
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
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (62 : Fin 70) = _
      rw [minorFormula_at_62]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (65 : Fin 70)
      rw [minorFormula_at_65]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (69 : Fin 70) = _
      rw [minorFormula_at_69]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring

noncomputable def chartForestRoots : Finset Point := {0,3}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(4,1),(4,2),(1,7)]

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
    (MatroidCatalogue.N8R4.family 60) where
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
    (MatroidCatalogue.N8R4.family 60) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart60
end

/- Source: Charts/Case61.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart61
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 1 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![X (none) - (X (some (some (0 : Fin 1)))) + (1)]
noncomputable def U0 : Fin 3 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![X (some (none)), X (none), X (some (some (0 : Fin 1)))]
noncomputable def R0 : Fin 1 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![X (none) - (X (some (some (0 : Fin 1)))) + (1)]

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
  ![X (none), X (some (0 : Fin 1)) - (1), X (some (0 : Fin 1))]

noncomputable def step0 : LinearStep (Option (Fin 1)) 1 3 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := 1
  b := -(X (some (0 : Fin 1))) + (1)
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
  ![X (none), X (some (0 : Fin 1)) - (1), X (some (0 : Fin 1))]
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

end Papers.RationalityTen.Chart61
end

/- Source: ChartTables/Case61.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart61
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Fin 1))) :=
  ![![.one, .zero, .one, .one], ![.zero, .one, .one, .variable (some (none))], ![.one, .variable (none), .variable (some (some (0 : Fin 1))), .zero], ![.zero, .zero, .zero, .zero]]

noncomputable def chartPositions : (Option (Option (Fin 1))) → Coordinate × Coordinate :=
  Option.elim' (2, 1) (Option.elim' (1, 3) ![(2, 2)])

noncomputable def chartUnitVariables : Fin 3 → (Option (Option (Fin 1))) :=
  ![some (none), none, some (some (0 : Fin 1))]

noncomputable def chartLabelCode : ℕ := 14040712

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, true, true, true, false, false, false, false, false, false, false, false, true, true, true, false, false, false, false, false, false, true, true, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, false, false, false, true, true, true, true, true, true, false, false, false, false, true, true, true, true, true, true, false, false, false, false, false, true, true, true, false]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, false, false, false, true, true, true, true, true, true, true, true, false, false, false, true, true, true, true, true, true, false, false, false, false, false, false, true, true, true, true, false, true, false, false, true, true, true, true, true, true, false, false, false, false, false, false, true, true, true, true, false, false, false, false, false, false, true, true, true, true, true, false, false, false, true]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 61)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 61) chartLabelCode chartEntries
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (24 : Fin 70) = _
      rw [minorFormula_at_24]
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (34 : Fin 70) = _
      rw [minorFormula_at_34]
      dsimp [
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (41 : Fin 70) = _
      rw [minorFormula_at_41]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (53 : Fin 70) = _
      rw [minorFormula_at_53]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (54 : Fin 70) = _
      rw [minorFormula_at_54]
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
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (62 : Fin 70) = _
      rw [minorFormula_at_62]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (65 : Fin 70)
      rw [minorFormula_at_65]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (69 : Fin 70) = _
      rw [minorFormula_at_69]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring

noncomputable def chartForestRoots : Finset Point := {0,3}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,6),(0,7),(4,2),(6,1),(1,5)]

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
    (MatroidCatalogue.N8R4.family 61) where
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
    (MatroidCatalogue.N8R4.family 61) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart61
end

/- Source: Charts/Case62.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart62
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

end Papers.RationalityTen.Chart62
end

/- Source: ChartTables/Case62.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart62
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Fin 1))) :=
  ![![.zero, .one, .one, .one], ![.one, .zero, .one, .variable (some (none))], ![.one, .variable (some (some (0 : Fin 1))), .variable (none), .zero], ![.zero, .zero, .zero, .zero]]

noncomputable def chartPositions : (Option (Option (Fin 1))) → Coordinate × Coordinate :=
  Option.elim' (2, 2) (Option.elim' (1, 3) ![(2, 1)])

noncomputable def chartUnitVariables : Fin 3 → (Option (Option (Fin 1))) :=
  ![some (none), some (some (0 : Fin 1)), none]

noncomputable def chartLabelCode : ℕ := 14040712

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, true, true, true, false, false, false, false, false, false, false, true, false, true, true, false, false, false, false, false, false, true, false, true, true, true, true, false, false, false, false, false, true, true, true, false, false, false, false, false, false, true, true, true, true, true, true, false, false, false, false, true, true, true, true, true, true, false, false, false, false, true, true, true, true, false]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, false, false, false, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, true, true, false, true, false, false, false, false, true, true, true, true, true, false, false, false, true, true, true, true, true, true, false, false, false, false, false, false, true, true, true, true, false, false, false, false, false, false, true, true, true, true, false, false, false, false, true]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 62)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 62) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨26, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (26 : Fin 70)
      rw [minorFormula_at_26]
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (14 : Fin 70) = _
      rw [minorFormula_at_14]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (23 : Fin 70) = _
      rw [minorFormula_at_23]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (24 : Fin 70) = _
      rw [minorFormula_at_24]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (26 : Fin 70)
      rw [minorFormula_at_26]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (33 : Fin 70) = _
      rw [minorFormula_at_33]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (34 : Fin 70) = _
      rw [minorFormula_at_34]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (35 : Fin 70) = _
      rw [minorFormula_at_35]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (41 : Fin 70) = _
      rw [minorFormula_at_41]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (53 : Fin 70) = _
      rw [minorFormula_at_53]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (54 : Fin 70) = _
      rw [minorFormula_at_54]
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
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (62 : Fin 70) = _
      rw [minorFormula_at_62]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (69 : Fin 70) = _
      rw [minorFormula_at_69]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring

noncomputable def chartForestRoots : Finset Point := {0,3}
noncomputable def chartForestSteps : List (Point × Point) := [(0,5),(0,6),(0,7),(6,1),(1,4),(4,2)]

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
    (MatroidCatalogue.N8R4.family 62) where
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
    (MatroidCatalogue.N8R4.family 62) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart62
end

/- Source: Charts/Case63.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart63
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

end Papers.RationalityTen.Chart63
end

/- Source: ChartTables/Case63.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart63
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 2)) :=
  ![![.one, .one, .zero, .one], ![.one, .zero, .one, .variable (none)], ![.zero, .one, .variable (some (0 : Fin 2)), .variable (some (1 : Fin 2))], ![.zero, .zero, .zero, .zero]]

noncomputable def chartPositions : (Option (Fin 2)) → Coordinate × Coordinate :=
  Option.elim' (1, 3) ![(2, 2), (2, 3)]

noncomputable def chartUnitVariables : Fin 3 → (Option (Fin 2)) :=
  ![none, some (0 : Fin 2), some (1 : Fin 2)]

noncomputable def chartLabelCode : ℕ := 14040712

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, true, true, true, false, false, false, false, false, false, true, false, true, true, false, false, false, false, false, false, true, true, true, true, true, true, false, false, false, false, true, true, false, true, false, false, false, false, false, false, true, true, true, true, true, true, false, false, false, false, true, true, true, true, true, true, false, false, false, false, true, true, true, true, false]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, false, false, false, true, true, true, true, true, true, false, true, false, false, true, true, true, true, true, true, false, false, false, false, false, false, true, true, true, true, false, false, true, false, true, true, true, true, true, true, false, false, false, false, false, false, true, true, true, true, false, false, false, false, false, false, true, true, true, true, false, false, false, false, true]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 2)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 63)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 63) chartLabelCode chartEntries
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (14 : Fin 70) = _
      rw [minorFormula_at_14]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (23 : Fin 70) = _
      rw [minorFormula_at_23]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (24 : Fin 70) = _
      rw [minorFormula_at_24]
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (34 : Fin 70) = _
      rw [minorFormula_at_34]
      dsimp [
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (41 : Fin 70) = _
      rw [minorFormula_at_41]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (53 : Fin 70) = _
      rw [minorFormula_at_53]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (54 : Fin 70) = _
      rw [minorFormula_at_54]
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
      change minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70) = _
      rw [minorFormula_at_61]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (62 : Fin 70) = _
      rw [minorFormula_at_62]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
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
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (69 : Fin 70) = _
      rw [minorFormula_at_69]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring

noncomputable def chartForestRoots : Finset Point := {0,3}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,7),(4,1),(5,2),(1,6)]

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
    (MatroidCatalogue.N8R4.family 63) where
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
    (MatroidCatalogue.N8R4.family 63) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart63
end
