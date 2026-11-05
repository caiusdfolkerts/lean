module
public import Consolidated.MatrixNormalization
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases
public import MatroidCatalogue.N8R4
public import MatroidChecked.ChartRealization
public import Papers.RationalElimination

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/- Source: Charts/Case0.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart0
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

def E0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]
def U0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]
def R0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]

def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart0
end

/- Source: ChartTables/Case0.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart0
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
def chartEntries : Coordinate → Coordinate → Entry (Fin 0) :=
  ![![.one, .one, .one, .one], ![.zero, .zero, .zero, .zero], ![.zero, .zero, .zero, .zero], ![.zero, .zero, .zero, .zero]]

def chartPositions : (Fin 0) → Coordinate × Coordinate :=
  Fin.elim0

def chartUnitVariables : Fin 0 → (Fin 0) :=
  Fin.elim0

def chartLabelCode : ℕ := 9248680

def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true]

def chartMinorPolynomials : Fin 70 → MvPolynomial (Fin 0) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  exact fun j => Fin.elim0 j

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 0)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 0) chartLabelCode chartEntries
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
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring

def chartForestRoots : Finset Point := {0,1,2,3}
def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(0,7)]

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

def chart_certificate : ChartCertificate (Fin 0) 0 0
    (MatroidCatalogue.N8R4.family 0) where
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
    (MatroidCatalogue.N8R4.family 0) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart0
end

/- Source: Charts/Case1.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart1
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

def E0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]
def U0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]
def R0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]

def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart1
end

/- Source: ChartTables/Case1.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart1
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
def chartEntries : Coordinate → Coordinate → Entry (Fin 0) :=
  ![![.one, .one, .one, .zero], ![.zero, .zero, .zero, .one], ![.zero, .zero, .zero, .zero], ![.zero, .zero, .zero, .zero]]

def chartPositions : (Fin 0) → Coordinate × Coordinate :=
  Fin.elim0

def chartUnitVariables : Fin 0 → (Fin 0) :=
  Fin.elim0

def chartLabelCode : ℕ := 11345824

def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, true, true, false, false, false, false, false, false, false, false, false]

def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, true, true, true, true, true]

def chartMinorPolynomials : Fin 70 → MvPolynomial (Fin 0) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  exact fun j => Fin.elim0 j

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 1)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 1) chartLabelCode chartEntries
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
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring

def chartForestRoots : Finset Point := {0,1,2,3}
def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(1,7)]

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

def chart_certificate : ChartCertificate (Fin 0) 0 0
    (MatroidCatalogue.N8R4.family 1) where
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
    (MatroidCatalogue.N8R4.family 1) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart1
end

/- Source: Charts/Case2.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart2
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

def E0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]
def U0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]
def R0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]

def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart2
end

/- Source: ChartTables/Case2.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart2
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
def chartEntries : Coordinate → Coordinate → Entry (Fin 0) :=
  ![![.one, .one, .one, .one], ![.zero, .zero, .zero, .one], ![.zero, .zero, .zero, .zero], ![.zero, .zero, .zero, .zero]]

def chartPositions : (Fin 0) → Coordinate × Coordinate :=
  Fin.elim0

def chartUnitVariables : Fin 0 → (Fin 0) :=
  Fin.elim0

def chartLabelCode : ℕ := 11345824

def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, true, true, false, false, false, false, false, false, false, false, false]

def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, true, true, true, true, true]

def chartMinorPolynomials : Fin 70 → MvPolynomial (Fin 0) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  exact fun j => Fin.elim0 j

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 2)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 2) chartLabelCode chartEntries
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
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring

def chartForestRoots : Finset Point := {0,2,3}
def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(0,7),(7,1)]

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

def chart_certificate : ChartCertificate (Fin 0) 0 0
    (MatroidCatalogue.N8R4.family 2) where
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
    (MatroidCatalogue.N8R4.family 2) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart2
end

/- Source: Charts/Case3.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart3
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

def E0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]
def U0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]
def R0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]

def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart3
end

/- Source: ChartTables/Case3.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart3
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
def chartEntries : Coordinate → Coordinate → Entry (Fin 0) :=
  ![![.one, .one, .zero, .zero], ![.zero, .zero, .one, .one], ![.zero, .zero, .zero, .zero], ![.zero, .zero, .zero, .zero]]

def chartPositions : (Fin 0) → Coordinate × Coordinate :=
  Fin.elim0

def chartUnitVariables : Fin 0 → (Fin 0) :=
  Fin.elim0

def chartLabelCode : ℕ := 11607960

def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, true, false, false, false, false, false, false, false, false, false, false]

def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, true, true, true, true, true, true, true, true, true, true]

def chartMinorPolynomials : Fin 70 → MvPolynomial (Fin 0) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  exact fun j => Fin.elim0 j

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 3)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 3) chartLabelCode chartEntries
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
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring

def chartForestRoots : Finset Point := {0,1,2,3}
def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(1,6),(1,7)]

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

def chart_certificate : ChartCertificate (Fin 0) 0 0
    (MatroidCatalogue.N8R4.family 3) where
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
    (MatroidCatalogue.N8R4.family 3) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart3
end

/- Source: Charts/Case4.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart4
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

def E0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]
def U0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]
def R0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]

def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart4
end

/- Source: ChartTables/Case4.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart4
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
def chartEntries : Coordinate → Coordinate → Entry (Fin 0) :=
  ![![.one, .one, .zero, .one], ![.zero, .zero, .one, .one], ![.zero, .zero, .zero, .zero], ![.zero, .zero, .zero, .zero]]

def chartPositions : (Fin 0) → Coordinate × Coordinate :=
  Fin.elim0

def chartUnitVariables : Fin 0 → (Fin 0) :=
  Fin.elim0

def chartLabelCode : ℕ := 11607960

def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, true, true, false, false, false, false, false, false, false, false, false]

def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, false, true, true, true, true, true, true, true, true, true]

def chartMinorPolynomials : Fin 70 → MvPolynomial (Fin 0) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  exact fun j => Fin.elim0 j

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 4)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 4) chartLabelCode chartEntries
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
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring

def chartForestRoots : Finset Point := {0,2,3}
def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,7),(7,1),(1,6)]

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

def chart_certificate : ChartCertificate (Fin 0) 0 0
    (MatroidCatalogue.N8R4.family 4) where
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
    (MatroidCatalogue.N8R4.family 4) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart4
end

/- Source: Charts/Case5.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart5
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

def E0 : Fin 0 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![]
def U0 : Fin 1 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none)]
def R0 : Fin 0 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![]

def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart5
end

/- Source: ChartTables/Case5.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart5
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 0)) :=
  ![![.one, .one, .one, .one], ![.zero, .zero, .one, .variable (none)], ![.zero, .zero, .zero, .zero], ![.zero, .zero, .zero, .zero]]

def chartPositions : (Option (Fin 0)) → Coordinate × Coordinate :=
  Option.elim' (1, 3) ![]

def chartUnitVariables : Fin 1 → (Option (Fin 0)) :=
  ![none]

def chartLabelCode : ℕ := 11607960

def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, true, true, false, false, false, false, false, false, false, false, false]

def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, false, true, true, true, true, true, true, true, true, true]

def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 0)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 5)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 5) chartLabelCode chartEntries
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
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring

def chartForestRoots : Finset Point := {0,2,3}
def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(0,7),(6,1)]

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

def chart_certificate : ChartCertificate (Option (Fin 0)) 0 1
    (MatroidCatalogue.N8R4.family 5) where
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
    (MatroidCatalogue.N8R4.family 5) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart5
end

/- Source: Charts/Case6.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart6
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

def E0 : Fin 1 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none) - (1)]
def U0 : Fin 1 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none)]
def R0 : Fin 1 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none) - (1)]

def reductions0 (j : Fin 1) : FactorReduction U0 (E0 j) (R0 j) := by
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

def nextE0 : Fin 1 → MvPolynomial (Fin 0) ℚ :=
  ![0]
def nextU0 : Fin 1 → MvPolynomial (Fin 0) ℚ :=
  ![1]

def step0 : LinearStep (Fin 0) 1 1 where
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
  unit_power := ![1]
  unit_quotient := ![1]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

def E1 : Fin 1 → MvPolynomial (Fin 0) ℚ :=
  ![0]
def U1 : Fin 1 → MvPolynomial (Fin 0) ℚ :=
  ![1]
def R1 : Fin 1 → MvPolynomial (Fin 0) ℚ :=
  ![0]

def reductions1 (j : Fin 1) : FactorReduction U1 (E1 j) (R1 j) := by
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

end Papers.RationalityTen.Chart6
end

/- Source: ChartTables/Case6.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart6
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 0)) :=
  ![![.one, .zero, .one, .one], ![.zero, .one, .one, .variable (none)], ![.zero, .zero, .zero, .zero], ![.zero, .zero, .zero, .zero]]

def chartPositions : (Option (Fin 0)) → Coordinate × Coordinate :=
  Option.elim' (1, 3) (Fin.elim0)

def chartUnitVariables : Fin 1 → (Option (Fin 0)) :=
  ![none]

def chartLabelCode : ℕ := 11640720

def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, true, true, false, false, false, false, false, false, false, false, false, false]

def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, false, true, true, true, true, true, true, true, true, true, true]

def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 0)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 6)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 6) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨60, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [E0, minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
  · intro i hi
    fin_cases i
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [E0, minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring

def chartForestRoots : Finset Point := {0,2,3}
def chartForestSteps : List (Point × Point) := [(0,4),(0,6),(0,7),(6,1),(1,5)]

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

def chart_certificate : ChartCertificate (Option (Fin 0)) 1 1
    (MatroidCatalogue.N8R4.family 6) where
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
    (MatroidCatalogue.N8R4.family 6) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart6
end

/- Source: Charts/Case7.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart7
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

def E0 : Fin 0 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![]
def U0 : Fin 1 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none)]
def R0 : Fin 0 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![]

def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart7
end

/- Source: ChartTables/Case7.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart7
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 0)) :=
  ![![.one, .zero, .one, .one], ![.zero, .one, .one, .variable (none)], ![.zero, .zero, .zero, .zero], ![.zero, .zero, .zero, .zero]]

def chartPositions : (Option (Fin 0)) → Coordinate × Coordinate :=
  Option.elim' (1, 3) ![]

def chartUnitVariables : Fin 1 → (Option (Fin 0)) :=
  ![none]

def chartLabelCode : ℕ := 11640720

def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, true, true, true, false, false, false, false, false, false, false, false, false]

def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, false, false, true, true, true, true, true, true, true, true, true]

def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 0)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 7)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 7) chartLabelCode chartEntries
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
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring

def chartForestRoots : Finset Point := {0,2,3}
def chartForestSteps : List (Point × Point) := [(0,4),(0,6),(0,7),(6,1),(1,5)]

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

def chart_certificate : ChartCertificate (Option (Fin 0)) 0 1
    (MatroidCatalogue.N8R4.family 7) where
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
    (MatroidCatalogue.N8R4.family 7) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart7
end

/- Source: Charts/Case8.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart8
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

def E0 : Fin 0 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![]
def U0 : Fin 2 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![X (none), X (some (0 : Fin 1))]
def R0 : Fin 0 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![]

def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart8
end

/- Source: ChartTables/Case8.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart8
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 1)) :=
  ![![.one, .one, .one, .one], ![.zero, .one, .variable (none), .variable (some (0 : Fin 1))], ![.zero, .zero, .zero, .zero], ![.zero, .zero, .zero, .zero]]

def chartPositions : (Option (Fin 1)) → Coordinate × Coordinate :=
  Option.elim' (1, 2) ![(1, 3)]

def chartUnitVariables : Fin 2 → (Option (Fin 1)) :=
  ![none, some (0 : Fin 1)]

def chartLabelCode : ℕ := 11640720

def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, true, true, true, false, false, false, false, false, false, false, false, false]

def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, false, false, true, true, true, true, true, true, true, true, true]

def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 1)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 8)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 8) chartLabelCode chartEntries
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
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring

def chartForestRoots : Finset Point := {0,2,3}
def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(0,7),(5,1)]

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

def chart_certificate : ChartCertificate (Option (Fin 1)) 0 2
    (MatroidCatalogue.N8R4.family 8) where
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
    (MatroidCatalogue.N8R4.family 8) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart8
end

/- Source: Charts/Case9.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart9
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

def E0 : Fin 0 → MvPolynomial (Option (Fin 2)) ℚ :=
  ![]
def U0 : Fin 3 → MvPolynomial (Option (Fin 2)) ℚ :=
  ![X (none), X (some (0 : Fin 2)), X (some (1 : Fin 2))]
def R0 : Fin 0 → MvPolynomial (Option (Fin 2)) ℚ :=
  ![]

def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart9
end

/- Source: ChartTables/Case9.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart9
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 2)) :=
  ![![.one, .one, .one, .one], ![.one, .variable (none), .variable (some (0 : Fin 2)), .variable (some (1 : Fin 2))], ![.zero, .zero, .zero, .zero], ![.zero, .zero, .zero, .zero]]

def chartPositions : (Option (Fin 2)) → Coordinate × Coordinate :=
  Option.elim' (1, 1) ![(1, 2), (1, 3)]

def chartUnitVariables : Fin 3 → (Option (Fin 2)) :=
  ![none, some (0 : Fin 2), some (1 : Fin 2)]

def chartLabelCode : ℕ := 11644808

def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, true, true, true, false, false, false, false, false, false, false, false, false]

def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, false, false, true, true, true, true, true, true, true, true, true]

def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 2)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 9)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 9) chartLabelCode chartEntries
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
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring

def chartForestRoots : Finset Point := {0,2,3}
def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(0,7),(4,1)]

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

def chart_certificate : ChartCertificate (Option (Fin 2)) 0 3
    (MatroidCatalogue.N8R4.family 9) where
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
    (MatroidCatalogue.N8R4.family 9) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart9
end

/- Source: Charts/Case10.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart10
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

def E0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]
def U0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]
def R0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]

def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart10
end

/- Source: ChartTables/Case10.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart10
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
def chartEntries : Coordinate → Coordinate → Entry (Fin 0) :=
  ![![.one, .one, .one, .zero], ![.zero, .zero, .zero, .one], ![.zero, .zero, .zero, .one], ![.zero, .zero, .zero, .zero]]

def chartPositions : (Fin 0) → Coordinate × Coordinate :=
  Fin.elim0

def chartUnitVariables : Fin 0 → (Fin 0) :=
  Fin.elim0

def chartLabelCode : ℕ := 13442912

def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, false, false, false, false, false, false, false, false, false, true, false, true, true, false, false, false, false, false, false, true, false, true, true, false, false, false, false, false, false, false, false, false]

def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, true, true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, true, true, false, true, false, false, true, true, true, true, true, true, true, true, true]

def chartMinorPolynomials : Fin 70 → MvPolynomial (Fin 0) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  exact fun j => Fin.elim0 j

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 10)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 10) chartLabelCode chartEntries
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
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring

def chartForestRoots : Finset Point := {0,1,3}
def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(1,7),(7,2)]

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

def chart_certificate : ChartCertificate (Fin 0) 0 0
    (MatroidCatalogue.N8R4.family 10) where
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
    (MatroidCatalogue.N8R4.family 10) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart10
end

/- Source: Charts/Case11.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart11
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

def E0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]
def U0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]
def R0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]

def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart11
end

/- Source: ChartTables/Case11.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart11
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
def chartEntries : Coordinate → Coordinate → Entry (Fin 0) :=
  ![![.one, .one, .one, .one], ![.zero, .zero, .zero, .one], ![.zero, .zero, .zero, .one], ![.zero, .zero, .zero, .zero]]

def chartPositions : (Fin 0) → Coordinate × Coordinate :=
  Fin.elim0

def chartUnitVariables : Fin 0 → (Fin 0) :=
  Fin.elim0

def chartLabelCode : ℕ := 13442912

def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, true, false, false, false, false, false, false, false, false, true, false, true, true, false, false, false, false, false, false, true, false, true, true, false, false, false, false, false, false, false, false, false]

def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, true, true, false, true, false, false, true, true, true, true, true, true, true, true, true]

def chartMinorPolynomials : Fin 70 → MvPolynomial (Fin 0) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  exact fun j => Fin.elim0 j

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 11)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 11) chartLabelCode chartEntries
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
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring

def chartForestRoots : Finset Point := {0,3}
def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(0,7),(7,1),(7,2)]

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

def chart_certificate : ChartCertificate (Fin 0) 0 0
    (MatroidCatalogue.N8R4.family 11) where
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
    (MatroidCatalogue.N8R4.family 11) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart11
end

/- Source: Charts/Case12.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart12
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

def E0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]
def U0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]
def R0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]

def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart12
end

/- Source: ChartTables/Case12.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart12
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
def chartEntries : Coordinate → Coordinate → Entry (Fin 0) :=
  ![![.one, .one, .zero, .zero], ![.zero, .zero, .zero, .one], ![.zero, .zero, .one, .zero], ![.zero, .zero, .zero, .zero]]

def chartPositions : (Fin 0) → Coordinate × Coordinate :=
  Fin.elim0

def chartUnitVariables : Fin 0 → (Fin 0) :=
  Fin.elim0

def chartLabelCode : ℕ := 13967128

def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, true, true, false, false, false, false, false, false, false, false, false, true, false, true, false, false, false, false, false, false, false, false, true, false, true, false, false, false, false, false, false, false, true, true, false]

def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, false, false, true, true, true, true, true, true, true, true, true, false, true, false, true, true, true, true, true, true, true, true, false, true, false, true, true, true, true, true, true, true, false, false, true]

def chartMinorPolynomials : Fin 70 → MvPolynomial (Fin 0) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  exact fun j => Fin.elim0 j

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 12)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 12) chartLabelCode chartEntries
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
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring

def chartForestRoots : Finset Point := {0,1,2,3}
def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(1,7),(2,6)]

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

def chart_certificate : ChartCertificate (Fin 0) 0 0
    (MatroidCatalogue.N8R4.family 12) where
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
    (MatroidCatalogue.N8R4.family 12) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart12
end

/- Source: Charts/Case13.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart13
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

def E0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]
def U0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]
def R0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]

def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart13
end

/- Source: ChartTables/Case13.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart13
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
def chartEntries : Coordinate → Coordinate → Entry (Fin 0) :=
  ![![.one, .one, .zero, .one], ![.zero, .zero, .one, .zero], ![.zero, .zero, .zero, .one], ![.zero, .zero, .zero, .zero]]

def chartPositions : (Fin 0) → Coordinate × Coordinate :=
  Fin.elim0

def chartUnitVariables : Fin 0 → (Fin 0) :=
  Fin.elim0

def chartLabelCode : ℕ := 13705048

def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, true, true, false, true, false, false, false, false, false, false, false, false, true, false, true, false, false, false, false, false, false, true, false, true, false, true, false, false, false, false, false, false, true, true, false]

def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, false, false, true, false, true, true, true, true, true, true, true, true, false, true, false, true, true, true, true, true, true, false, true, false, true, false, true, true, true, true, true, true, false, false, true]

def chartMinorPolynomials : Fin 70 → MvPolynomial (Fin 0) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  exact fun j => Fin.elim0 j

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 13)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 13) chartLabelCode chartEntries
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
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring

def chartForestRoots : Finset Point := {0,1,3}
def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,7),(7,2),(1,6)]

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

def chart_certificate : ChartCertificate (Fin 0) 0 0
    (MatroidCatalogue.N8R4.family 13) where
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
    (MatroidCatalogue.N8R4.family 13) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart13
end

/- Source: Charts/Case14.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart14
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

def E0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]
def U0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]
def R0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]

def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart14
end

/- Source: ChartTables/Case14.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart14
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
def chartEntries : Coordinate → Coordinate → Entry (Fin 0) :=
  ![![.one, .one, .zero, .zero], ![.zero, .zero, .one, .one], ![.zero, .zero, .zero, .one], ![.zero, .zero, .zero, .zero]]

def chartPositions : (Fin 0) → Coordinate × Coordinate :=
  Fin.elim0

def chartUnitVariables : Fin 0 → (Fin 0) :=
  Fin.elim0

def chartLabelCode : ℕ := 13705048

def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, true, true, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, true, true, false, false, false, false, false, false, false, false, false, false, true, false, true, false, false, false, false, false, false, true, true, true, true, false, false, false, false, false, false, false, true, true, false]

def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, false, false, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, false, false, true, true, true, true, true, true, true, true, true, true, false, true, false, true, true, true, true, true, true, false, false, false, false, true, true, true, true, true, true, true, false, false, true]

def chartMinorPolynomials : Fin 70 → MvPolynomial (Fin 0) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  exact fun j => Fin.elim0 j

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 14)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 14) chartLabelCode chartEntries
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
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring

def chartForestRoots : Finset Point := {0,1,3}
def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(1,6),(1,7),(7,2)]

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

def chart_certificate : ChartCertificate (Fin 0) 0 0
    (MatroidCatalogue.N8R4.family 14) where
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
    (MatroidCatalogue.N8R4.family 14) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart14
end

/- Source: Charts/Case15.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart15
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

def E0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]
def U0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]
def R0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]

def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart15
end

/- Source: ChartTables/Case15.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart15
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
def chartEntries : Coordinate → Coordinate → Entry (Fin 0) :=
  ![![.one, .one, .zero, .one], ![.zero, .zero, .one, .one], ![.zero, .zero, .zero, .one], ![.zero, .zero, .zero, .zero]]

def chartPositions : (Fin 0) → Coordinate × Coordinate :=
  Fin.elim0

def chartUnitVariables : Fin 0 → (Fin 0) :=
  Fin.elim0

def chartLabelCode : ℕ := 13705048

def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, true, true, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, true, true, false, true, false, false, false, false, false, false, false, false, true, false, true, false, false, false, false, false, false, true, true, true, true, true, false, false, false, false, false, false, true, true, false]

def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, false, false, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, false, false, true, false, true, true, true, true, true, true, true, true, false, true, false, true, true, true, true, true, true, false, false, false, false, false, true, true, true, true, true, true, false, false, true]

def chartMinorPolynomials : Fin 70 → MvPolynomial (Fin 0) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  exact fun j => Fin.elim0 j

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 15)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 15) chartLabelCode chartEntries
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
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring

def chartForestRoots : Finset Point := {0,3}
def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,7),(7,1),(7,2),(1,6)]

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

def chart_certificate : ChartCertificate (Fin 0) 0 0
    (MatroidCatalogue.N8R4.family 15) where
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
    (MatroidCatalogue.N8R4.family 15) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart15
end

/- Source: Charts/Case16.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart16
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

def E0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]
def U0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]
def R0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]

def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart16
end

/- Source: ChartTables/Case16.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart16
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
def chartEntries : Coordinate → Coordinate → Entry (Fin 0) :=
  ![![.one, .one, .one, .one], ![.zero, .zero, .zero, .one], ![.zero, .zero, .one, .zero], ![.zero, .zero, .zero, .zero]]

def chartPositions : (Fin 0) → Coordinate × Coordinate :=
  Fin.elim0

def chartUnitVariables : Fin 0 → (Fin 0) :=
  Fin.elim0

def chartLabelCode : ℕ := 13967128

def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, true, true, true, true, false, false, false, false, false, false, false, true, false, true, false, true, false, false, false, false, false, false, true, false, true, true, false, false, false, false, false, false, true, true, false]

def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, false, false, false, false, true, true, true, true, true, true, true, false, true, false, true, false, true, true, true, true, true, true, false, true, false, false, true, true, true, true, true, true, false, false, true]

def chartMinorPolynomials : Fin 70 → MvPolynomial (Fin 0) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  exact fun j => Fin.elim0 j

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 16)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 16) chartLabelCode chartEntries
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
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring

def chartForestRoots : Finset Point := {0,3}
def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(0,7),(6,2),(7,1)]

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

def chart_certificate : ChartCertificate (Fin 0) 0 0
    (MatroidCatalogue.N8R4.family 16) where
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
    (MatroidCatalogue.N8R4.family 16) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart16
end

/- Source: Charts/Case17.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart17
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

def E0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]
def U0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]
def R0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]

def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart17
end

/- Source: ChartTables/Case17.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart17
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
def chartEntries : Coordinate → Coordinate → Entry (Fin 0) :=
  ![![.one, .one, .one, .zero], ![.zero, .zero, .one, .one], ![.zero, .zero, .zero, .one], ![.zero, .zero, .zero, .zero]]

def chartPositions : (Fin 0) → Coordinate × Coordinate :=
  Fin.elim0

def chartUnitVariables : Fin 0 → (Fin 0) :=
  Fin.elim0

def chartLabelCode : ℕ := 13705048

def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, true, true, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, true, true, true, false, false, false, false, false, false, false, false, false, true, false, true, true, false, false, false, false, false, true, true, true, true, true, false, false, false, false, false, false, true, true, false]

def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, false, false, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, false, false, false, true, true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, true, false, false, false, false, false, true, true, true, true, true, true, false, false, true]

def chartMinorPolynomials : Fin 70 → MvPolynomial (Fin 0) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  exact fun j => Fin.elim0 j

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 17)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 17) chartLabelCode chartEntries
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
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring

def chartForestRoots : Finset Point := {0,3}
def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(6,1),(1,7),(7,2)]

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

def chart_certificate : ChartCertificate (Fin 0) 0 0
    (MatroidCatalogue.N8R4.family 17) where
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
    (MatroidCatalogue.N8R4.family 17) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart17
end

/- Source: Charts/Case18.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart18
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

def E0 : Fin 0 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![]
def U0 : Fin 1 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none)]
def R0 : Fin 0 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![]

def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart18
end

/- Source: ChartTables/Case18.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart18
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 0)) :=
  ![![.one, .one, .one, .one], ![.zero, .zero, .one, .variable (none)], ![.zero, .zero, .zero, .one], ![.zero, .zero, .zero, .zero]]

def chartPositions : (Option (Fin 0)) → Coordinate × Coordinate :=
  Option.elim' (1, 3) ![]

def chartUnitVariables : Fin 1 → (Option (Fin 0)) :=
  ![none]

def chartLabelCode : ℕ := 13705048

def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, true, true, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, true, true, true, true, false, false, false, false, false, false, false, false, true, false, true, true, false, false, false, false, false, true, true, true, true, true, false, false, false, false, false, false, true, true, false]

def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, false, false, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, false, false, false, false, true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, true, false, false, false, false, false, true, true, true, true, true, true, false, false, true]

def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 0)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 18)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 18) chartLabelCode chartEntries
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
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring

def chartForestRoots : Finset Point := {0,3}
def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(0,7),(6,1),(7,2)]

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

def chart_certificate : ChartCertificate (Option (Fin 0)) 0 1
    (MatroidCatalogue.N8R4.family 18) where
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
    (MatroidCatalogue.N8R4.family 18) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart18
end

/- Source: Charts/Case19.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart19
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

def E0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]
def U0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]
def R0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]

def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart19
end

/- Source: ChartTables/Case19.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart19
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
def chartEntries : Coordinate → Coordinate → Entry (Fin 0) :=
  ![![.one, .zero, .zero, .one], ![.zero, .one, .zero, .one], ![.zero, .zero, .one, .zero], ![.zero, .zero, .zero, .zero]]

def chartPositions : (Fin 0) → Coordinate × Coordinate :=
  Fin.elim0

def chartUnitVariables : Fin 0 → (Fin 0) :=
  Fin.elim0

def chartLabelCode : ℕ := 13999888

def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, true, false, true, false, false, false, false, false, false, false, false, false, true, false, true, false, false, false, false, true, false, false, true, false, false, false, false, false, false, false, true, false, false, false, true, false, false, false, false, true, false, true, false, true, false, false, false, false, false, true, false, true, true, false]

def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, false, true, false, true, true, true, true, true, true, true, true, true, false, true, false, true, true, true, true, false, true, true, false, true, true, true, true, true, true, true, false, true, true, true, false, true, true, true, true, false, true, false, true, false, true, true, true, true, true, false, true, false, false, true]

def chartMinorPolynomials : Fin 70 → MvPolynomial (Fin 0) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  exact fun j => Fin.elim0 j

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 19)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 19) chartLabelCode chartEntries
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
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring

def chartForestRoots : Finset Point := {0,2,3}
def chartForestSteps : List (Point × Point) := [(0,4),(0,7),(7,1),(1,5),(2,6)]

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

def chart_certificate : ChartCertificate (Fin 0) 0 0
    (MatroidCatalogue.N8R4.family 19) where
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
    (MatroidCatalogue.N8R4.family 19) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart19
end

/- Source: Charts/Case20.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart20
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

def E0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]
def U0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]
def R0 : Fin 0 → MvPolynomial (Fin 0) ℚ :=
  ![]

def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart20
end

/- Source: ChartTables/Case20.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart20
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
def chartEntries : Coordinate → Coordinate → Entry (Fin 0) :=
  ![![.one, .zero, .one, .one], ![.zero, .one, .one, .zero], ![.zero, .zero, .zero, .one], ![.zero, .zero, .zero, .zero]]

def chartPositions : (Fin 0) → Coordinate × Coordinate :=
  Fin.elim0

def chartUnitVariables : Fin 0 → (Fin 0) :=
  Fin.elim0

def chartLabelCode : ℕ := 13737808

def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, true, true, false, false, false, false, false, false, false, false, false, false, false, true, true, false, false, false, false, true, false, true, true, false, false, false, false, false, false, false, false, true, false, false, true, false, false, false, false, true, true, false, true, true, true, false, false, false, false, false, true, true, true, false]

def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, false, false, true, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, true, false, true, false, false, true, true, true, true, true, true, true, true, false, true, true, false, true, true, true, true, false, false, true, false, false, false, true, true, true, true, true, false, false, false, true]

def chartMinorPolynomials : Fin 70 → MvPolynomial (Fin 0) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  exact fun j => Fin.elim0 j

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 20)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 20) chartLabelCode chartEntries
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
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring

def chartForestRoots : Finset Point := {0,3}
def chartForestSteps : List (Point × Point) := [(0,4),(0,6),(0,7),(6,1),(7,2),(1,5)]

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

def chart_certificate : ChartCertificate (Fin 0) 0 0
    (MatroidCatalogue.N8R4.family 20) where
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
    (MatroidCatalogue.N8R4.family 20) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart20
end

/- Source: Charts/Case21.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart21
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

def E0 : Fin 1 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none) - (1)]
def U0 : Fin 1 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none)]
def R0 : Fin 1 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none) - (1)]

def reductions0 (j : Fin 1) : FactorReduction U0 (E0 j) (R0 j) := by
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

def nextE0 : Fin 1 → MvPolynomial (Fin 0) ℚ :=
  ![0]
def nextU0 : Fin 1 → MvPolynomial (Fin 0) ℚ :=
  ![1]

def step0 : LinearStep (Fin 0) 1 1 where
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
  unit_power := ![1]
  unit_quotient := ![1]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

def E1 : Fin 1 → MvPolynomial (Fin 0) ℚ :=
  ![0]
def U1 : Fin 1 → MvPolynomial (Fin 0) ℚ :=
  ![1]
def R1 : Fin 1 → MvPolynomial (Fin 0) ℚ :=
  ![0]

def reductions1 (j : Fin 1) : FactorReduction U1 (E1 j) (R1 j) := by
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

end Papers.RationalityTen.Chart21
end

/- Source: ChartTables/Case21.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart21
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 0)) :=
  ![![.one, .zero, .one, .one], ![.zero, .one, .one, .variable (none)], ![.zero, .zero, .zero, .one], ![.zero, .zero, .zero, .zero]]

def chartPositions : (Option (Fin 0)) → Coordinate × Coordinate :=
  Option.elim' (1, 3) (Fin.elim0)

def chartUnitVariables : Fin 1 → (Option (Fin 0)) :=
  ![none]

def chartLabelCode : ℕ := 13737808

def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, true, true, true, false, false, false, false, false, false, false, false, false, false, true, true, false, false, false, false, true, false, true, true, false, false, false, false, false, false, false, false, true, false, false, true, false, false, false, false, true, true, true, true, true, false, false, false, false, false, false, true, true, true, false]

def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, false, false, false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, true, false, true, false, false, true, true, true, true, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, false, false, true, true, true, true, true, true, false, false, false, true]

def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 0)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 21)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 21) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨60, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [E0, minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
  · intro i hi
    fin_cases i
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [E0, minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring

def chartForestRoots : Finset Point := {0,3}
def chartForestSteps : List (Point × Point) := [(0,4),(0,6),(0,7),(6,1),(7,2),(1,5)]

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

def chart_certificate : ChartCertificate (Option (Fin 0)) 1 1
    (MatroidCatalogue.N8R4.family 21) where
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
    (MatroidCatalogue.N8R4.family 21) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart21
end

/- Source: Charts/Case22.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart22
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

def E0 : Fin 0 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![]
def U0 : Fin 1 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none)]
def R0 : Fin 0 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![]

def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart22
end

/- Source: ChartTables/Case22.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart22
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 0)) :=
  ![![.one, .zero, .one, .one], ![.zero, .one, .one, .variable (none)], ![.zero, .zero, .zero, .one], ![.zero, .zero, .zero, .zero]]

def chartPositions : (Option (Fin 0)) → Coordinate × Coordinate :=
  Option.elim' (1, 3) ![]

def chartUnitVariables : Fin 1 → (Option (Fin 0)) :=
  ![none]

def chartLabelCode : ℕ := 13737808

def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, true, true, true, false, false, false, false, false, false, false, false, false, false, true, true, false, false, false, false, true, false, true, true, false, false, false, false, false, false, false, false, true, false, false, true, false, false, false, false, true, true, true, true, true, true, false, false, false, false, false, true, true, true, false]

def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, false, false, false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, true, false, true, false, false, true, true, true, true, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, false, false, false, true, true, true, true, true, false, false, false, true]

def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 0)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 22)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 22) chartLabelCode chartEntries
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
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring

def chartForestRoots : Finset Point := {0,3}
def chartForestSteps : List (Point × Point) := [(0,4),(0,6),(0,7),(6,1),(7,2),(1,5)]

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

def chart_certificate : ChartCertificate (Option (Fin 0)) 0 1
    (MatroidCatalogue.N8R4.family 22) where
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
    (MatroidCatalogue.N8R4.family 22) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart22
end

/- Source: Charts/Case23.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart23
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

def E0 : Fin 0 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![]
def U0 : Fin 1 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none)]
def R0 : Fin 0 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![]

def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart23
end

/- Source: ChartTables/Case23.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart23
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 0)) :=
  ![![.one, .one, .one, .zero], ![.zero, .one, .variable (none), .zero], ![.zero, .zero, .zero, .one], ![.zero, .zero, .zero, .zero]]

def chartPositions : (Option (Fin 0)) → Coordinate × Coordinate :=
  Option.elim' (1, 2) ![]

def chartUnitVariables : Fin 1 → (Option (Fin 0)) :=
  ![none]

def chartLabelCode : ℕ := 13737808

def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, true, true, false, false, false, false, false, false, false, false, false, false, false, true, true, false, false, false, false, true, true, true, false, false, false, false, false, false, false, false, false, true, false, true, true, false, false, false, false, true, true, false, true, false, false, false, false, false, false, false, true, true, true, false]

def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, false, false, true, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, true, false, true, true, true, true, true, true, true, false, false, false, true]

def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 0)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 23)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 23) chartLabelCode chartEntries
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
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring

def chartForestRoots : Finset Point := {0,2,3}
def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(5,1),(2,7)]

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

def chart_certificate : ChartCertificate (Option (Fin 0)) 0 1
    (MatroidCatalogue.N8R4.family 23) where
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
    (MatroidCatalogue.N8R4.family 23) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart23
end

/- Source: Charts/Case24.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart24
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

def E0 : Fin 0 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![]
def U0 : Fin 1 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none)]
def R0 : Fin 0 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![]

def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart24
end

/- Source: ChartTables/Case24.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart24
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 0)) :=
  ![![.one, .one, .one, .one], ![.zero, .one, .variable (none), .zero], ![.zero, .zero, .zero, .one], ![.zero, .zero, .zero, .zero]]

def chartPositions : (Option (Fin 0)) → Coordinate × Coordinate :=
  Option.elim' (1, 2) ![]

def chartUnitVariables : Fin 1 → (Option (Fin 0)) :=
  ![none]

def chartLabelCode : ℕ := 13737808

def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, true, true, false, false, false, false, false, false, false, false, false, false, false, true, true, false, false, false, false, true, true, true, true, false, false, false, false, false, false, false, false, true, false, true, true, false, false, false, false, true, true, false, true, true, true, false, false, false, false, false, true, true, true, false]

def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, false, false, true, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, true, false, false, false, true, true, true, true, true, false, false, false, true]

def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 0)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 24)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 24) chartLabelCode chartEntries
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
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring

def chartForestRoots : Finset Point := {0,3}
def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(0,7),(5,1),(7,2)]

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

def chart_certificate : ChartCertificate (Option (Fin 0)) 0 1
    (MatroidCatalogue.N8R4.family 24) where
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
    (MatroidCatalogue.N8R4.family 24) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart24
end

/- Source: Charts/Case25.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart25
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

def E0 : Fin 0 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![]
def U0 : Fin 1 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none)]
def R0 : Fin 0 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![]

def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart25
end

/- Source: ChartTables/Case25.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart25
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 0)) :=
  ![![.one, .one, .one, .zero], ![.zero, .one, .variable (none), .one], ![.zero, .zero, .zero, .one], ![.zero, .zero, .zero, .zero]]

def chartPositions : (Option (Fin 0)) → Coordinate × Coordinate :=
  Option.elim' (1, 2) ![]

def chartUnitVariables : Fin 1 → (Option (Fin 0)) :=
  ![none]

def chartLabelCode : ℕ := 13737808

def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, true, true, true, false, false, false, false, false, false, false, false, false, false, true, true, false, false, false, false, true, true, true, false, false, false, false, false, false, false, false, false, true, false, true, true, false, false, false, false, true, true, true, true, true, true, false, false, false, false, false, true, true, true, false]

def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, false, false, false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, false, false, false, true, true, true, true, true, false, false, false, true]

def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 0)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 25)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 25) chartLabelCode chartEntries
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
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring

def chartForestRoots : Finset Point := {0,3}
def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(5,1),(1,7),(7,2)]

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

def chart_certificate : ChartCertificate (Option (Fin 0)) 0 1
    (MatroidCatalogue.N8R4.family 25) where
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
    (MatroidCatalogue.N8R4.family 25) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart25
end

/- Source: Charts/Case26.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart26
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

def E0 : Fin 0 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![]
def U0 : Fin 2 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![X (none), X (some (0 : Fin 1))]
def R0 : Fin 0 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![]

def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart26
end

/- Source: ChartTables/Case26.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart26
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 1)) :=
  ![![.one, .one, .one, .one], ![.zero, .one, .variable (none), .variable (some (0 : Fin 1))], ![.zero, .zero, .zero, .one], ![.zero, .zero, .zero, .zero]]

def chartPositions : (Option (Fin 1)) → Coordinate × Coordinate :=
  Option.elim' (1, 2) ![(1, 3)]

def chartUnitVariables : Fin 2 → (Option (Fin 1)) :=
  ![none, some (0 : Fin 1)]

def chartLabelCode : ℕ := 13737808

def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, true, true, true, false, false, false, false, false, false, false, false, false, false, true, true, false, false, false, false, true, true, true, true, false, false, false, false, false, false, false, false, true, false, true, true, false, false, false, false, true, true, true, true, true, true, false, false, false, false, false, true, true, true, false]

def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, false, false, false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, false, false, false, true, true, true, true, true, false, false, false, true]

def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 1)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 26)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 26) chartLabelCode chartEntries
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
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring

def chartForestRoots : Finset Point := {0,3}
def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(0,7),(5,1),(7,2)]

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

def chart_certificate : ChartCertificate (Option (Fin 1)) 0 2
    (MatroidCatalogue.N8R4.family 26) where
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
    (MatroidCatalogue.N8R4.family 26) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart26
end

/- Source: Charts/Case27.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart27
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

def E0 : Fin 0 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![]
def U0 : Fin 2 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![X (none), X (some (0 : Fin 1))]
def R0 : Fin 0 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![]

def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart27
end

/- Source: ChartTables/Case27.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart27
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 1)) :=
  ![![.one, .one, .one, .zero], ![.one, .variable (none), .variable (some (0 : Fin 1)), .zero], ![.zero, .zero, .zero, .one], ![.zero, .zero, .zero, .zero]]

def chartPositions : (Option (Fin 1)) → Coordinate × Coordinate :=
  Option.elim' (1, 1) ![(1, 2)]

def chartUnitVariables : Fin 2 → (Option (Fin 1)) :=
  ![none, some (0 : Fin 1)]

def chartLabelCode : ℕ := 13741896

def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, true, true, true, false, false, false, false, false, false, false, false, false, true, false, true, true, false, false, false, false, true, true, true, false, false, false, false, false, false, false, false, false, true, false, true, true, false, false, false, false, true, true, false, true, false, false, false, false, false, false, false, true, true, true, false]

def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, true, false, true, true, true, true, true, true, false, false, false, true, true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, true, false, true, true, true, true, true, true, true, false, false, false, true]

def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 1)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 27)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 27) chartLabelCode chartEntries
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
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring

def chartForestRoots : Finset Point := {0,2,3}
def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(4,1),(2,7)]

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

def chart_certificate : ChartCertificate (Option (Fin 1)) 0 2
    (MatroidCatalogue.N8R4.family 27) where
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
    (MatroidCatalogue.N8R4.family 27) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart27
end

/- Source: Charts/Case28.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart28
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

def E0 : Fin 0 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![]
def U0 : Fin 2 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![X (none), X (some (0 : Fin 1))]
def R0 : Fin 0 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![]

def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart28
end

/- Source: ChartTables/Case28.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart28
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 1)) :=
  ![![.one, .one, .one, .one], ![.one, .variable (none), .variable (some (0 : Fin 1)), .zero], ![.zero, .zero, .zero, .one], ![.zero, .zero, .zero, .zero]]

def chartPositions : (Option (Fin 1)) → Coordinate × Coordinate :=
  Option.elim' (1, 1) ![(1, 2)]

def chartUnitVariables : Fin 2 → (Option (Fin 1)) :=
  ![none, some (0 : Fin 1)]

def chartLabelCode : ℕ := 13741896

def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, true, true, true, false, false, false, false, false, false, false, false, false, true, false, true, true, false, false, false, false, true, true, true, true, false, false, false, false, false, false, false, false, true, false, true, true, false, false, false, false, true, true, true, true, true, true, false, false, false, false, false, true, true, true, false]

def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, true, false, true, true, true, true, true, true, false, false, false, true, true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, false, false, false, true, true, true, true, true, false, false, false, true]

def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 1)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 28)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 28) chartLabelCode chartEntries
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
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring

def chartForestRoots : Finset Point := {0,3}
def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(0,7),(4,1),(7,2)]

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

def chart_certificate : ChartCertificate (Option (Fin 1)) 0 2
    (MatroidCatalogue.N8R4.family 28) where
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
    (MatroidCatalogue.N8R4.family 28) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart28
end

/- Source: Charts/Case29.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart29
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

def E0 : Fin 0 → MvPolynomial (Option (Fin 2)) ℚ :=
  ![]
def U0 : Fin 3 → MvPolynomial (Option (Fin 2)) ℚ :=
  ![X (none), X (some (0 : Fin 2)), X (some (1 : Fin 2))]
def R0 : Fin 0 → MvPolynomial (Option (Fin 2)) ℚ :=
  ![]

def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart29
end

/- Source: ChartTables/Case29.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart29
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 2)) :=
  ![![.one, .one, .one, .one], ![.one, .variable (none), .variable (some (0 : Fin 2)), .variable (some (1 : Fin 2))], ![.zero, .zero, .zero, .one], ![.zero, .zero, .zero, .zero]]

def chartPositions : (Option (Fin 2)) → Coordinate × Coordinate :=
  Option.elim' (1, 1) ![(1, 2), (1, 3)]

def chartUnitVariables : Fin 3 → (Option (Fin 2)) :=
  ![none, some (0 : Fin 2), some (1 : Fin 2)]

def chartLabelCode : ℕ := 13741896

def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, true, true, true, true, false, false, false, false, false, false, false, false, true, false, true, true, false, false, false, false, true, true, true, true, false, false, false, false, false, false, false, false, true, false, true, true, false, false, false, false, true, true, true, true, true, true, false, false, false, false, false, true, true, true, false]

def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, false, false, false, true, true, true, true, true, false, false, false, true]

def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 2)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 29)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 29) chartLabelCode chartEntries
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
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring

def chartForestRoots : Finset Point := {0,3}
def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(0,7),(4,1),(7,2)]

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

def chart_certificate : ChartCertificate (Option (Fin 2)) 0 3
    (MatroidCatalogue.N8R4.family 29) where
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
    (MatroidCatalogue.N8R4.family 29) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart29
end

/- Source: Charts/Case30.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart30
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

def E0 : Fin 0 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![]
def U0 : Fin 1 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none)]
def R0 : Fin 0 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![]

def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart30
end

/- Source: ChartTables/Case30.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart30
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 0)) :=
  ![![.one, .one, .zero, .zero], ![.zero, .zero, .one, .one], ![.zero, .zero, .one, .variable (none)], ![.zero, .zero, .zero, .zero]]

def chartPositions : (Option (Fin 0)) → Coordinate × Coordinate :=
  Option.elim' (2, 3) ![]

def chartUnitVariables : Fin 1 → (Option (Fin 0)) :=
  ![none]

def chartLabelCode : ℕ := 13967128

def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, true, true, false, false, false, false, false, false, false, false, true, true, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, true, true, false, false, false, false, false, false, false, false, false, true, true, true, true, false, false, false, false, false, false, true, true, true, true, false, false, false, false, false, false, false, true, true, false]

def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, false, false, true, true, true, true, true, true, true, true, false, false, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, false, false, true, true, true, true, true, true, true, true, true, false, false, false, false, true, true, true, true, true, true, false, false, false, false, true, true, true, true, true, true, true, false, false, true]

def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 0)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 30)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 30) chartLabelCode chartEntries
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
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring

def chartForestRoots : Finset Point := {0,1,3}
def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(1,6),(1,7),(6,2)]

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

def chart_certificate : ChartCertificate (Option (Fin 0)) 0 1
    (MatroidCatalogue.N8R4.family 30) where
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
    (MatroidCatalogue.N8R4.family 30) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart30
end

/- Source: Charts/Case31.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart31
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

def E0 : Fin 0 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![]
def U0 : Fin 1 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none)]
def R0 : Fin 0 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![]

def reductions0 (j : Fin 0) : FactorReduction U0 (E0 j) (R0 j) := by
  exact Fin.elim0 j

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  apply zero_equations_system_dense R0 U0
  exact fun j => Fin.elim0 j

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart31
end

/- Source: ChartTables/Case31.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart31
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
def chartEntries : Coordinate → Coordinate → Entry (Option (Fin 0)) :=
  ![![.one, .one, .zero, .one], ![.zero, .zero, .one, .one], ![.zero, .zero, .one, .variable (none)], ![.zero, .zero, .zero, .zero]]

def chartPositions : (Option (Fin 0)) → Coordinate × Coordinate :=
  Option.elim' (2, 3) ![]

def chartUnitVariables : Fin 1 → (Option (Fin 0)) :=
  ![none]

def chartLabelCode : ℕ := 13967128

def chartBasisMark : Fin 70 → Bool :=
  ![true, false, false, false, false, false, false, true, true, false, false, false, false, false, false, false, false, true, true, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, true, true, false, true, false, false, false, false, false, false, false, true, true, true, true, true, false, false, false, false, false, true, true, true, true, true, false, false, false, false, false, false, true, true, false]

def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, true, true, true, true, true, false, false, true, true, true, true, true, true, true, true, false, false, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, false, false, true, false, true, true, true, true, true, true, true, false, false, false, false, false, true, true, true, true, true, false, false, false, false, false, true, true, true, true, true, true, false, false, true]

def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Fin 0)) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 31)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 31) chartLabelCode chartEntries
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
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      dsimp [minorFormula, minorFormulaTree, FormulaTable.get,
        chartEntries, Entry.polynomial] <;> simp <;> ring

def chartForestRoots : Finset Point := {0,3}
def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,7),(7,1),(1,6),(6,2)]

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

def chart_certificate : ChartCertificate (Option (Fin 0)) 0 1
    (MatroidCatalogue.N8R4.family 31) where
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
    (MatroidCatalogue.N8R4.family 31) :=
  chart_certificate.family_density chart_all_nonbases rationally_dense

end Papers.RationalityTen.Chart31
end
