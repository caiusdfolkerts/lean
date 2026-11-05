module
public import Papers.RationalityTenResidualCurves
public import Papers.AlgebraicChartDensity
public import Mathlib.Tactic.FinCases

@[expose] public section
noncomputable section

namespace Papers.RationalityTen.ResidualPolynomialDensity

open Set Filter Topology MvPolynomial
open MultiaffineDensity ResidualCurves

/-- The literal exceptional rational quartic, in the same coordinate type
as the finite normalized charts. -/
def quartic : MvPolynomial (Option (Fin 1)) ℚ :=
  (X none)^2 * (X (some 0))^2 -
  2 * X none * (X (some 0))^2 + 3 * X none * X (some 0) -
  X none + (X (some 0))^2 - 2 * X (some 0) + 1

def pairVector (p : ℝ × ℝ) : Option (Fin 1) → ℝ :=
  Option.elim' p.1 (fun _ => p.2)

theorem continuous_pairVector : Continuous pairVector := by
  apply continuous_pi
  intro i
  cases i with
  | none => exact continuous_fst
  | some i => exact continuous_snd

theorem pairVector_rational {p : ℝ × ℝ} (hp : RationalPoint p) :
    RationalVector (pairVector p) := by
  intro i
  cases i with
  | none => exact hp.1
  | some i => exact hp.2

@[simp] theorem eval_quartic_pair (p : ℝ × ℝ) :
    evalRat quartic (pairVector p) = quarticPolynomial p := by
  simp [quartic, evalRat, pairVector, quarticPolynomial]

theorem quartic_rationally_dense (x : Option (Fin 1) → ℝ)
    (hx : evalRat quartic x = 0) :
    x ∈ closure {q | RationalVector q ∧ evalRat quartic q = 0} := by
  let p : ℝ × ℝ := (x none, x (some 0))
  have hround : pairVector p = x := by
    funext i
    cases i with
    | none => rfl
    | some i => fin_cases i; rfl
  have hp : quarticPolynomial p = 0 := by
    rw [← eval_quartic_pair, hround]
    exact hx
  have hd := quartic_rational_density p hp
  have himage := mem_closure_image continuous_pairVector.continuousAt hd
  rw [hround] at himage
  apply closure_mono ?_ himage
  rintro _ ⟨q, ⟨hr, he⟩, rfl⟩
  exact ⟨pairVector_rational hr, by simpa only [eval_quartic_pair] using he⟩

end Papers.RationalityTen.ResidualPolynomialDensity
