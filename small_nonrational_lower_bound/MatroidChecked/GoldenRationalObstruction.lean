module
public import MatroidChecked.RationalScheduledCharts
public import ChartTables.Case563
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Tactic.LinearCombination

@[expose] public section
noncomputable section

/-!
# No rational representation of the exceptional eight-element matroid

The five equations below are the actual zero minors of the normalized
chart. Their consequence is a quadratic with discriminant five. Rational
normalization transports any purported rational representation into this
chart, so the obstruction applies to every representation and relabeling.
-/

namespace Papers.RationalityTen.MatroidChecked.GoldenRationalObstruction
open Matrix MvPolynomial ChartPolynomial ChartRealization
open Papers.RationalKernelCharts
open MultiaffineDensity RationalElimination
open VectorBasisFamilies (vectorBases)

/-- This calculation uses the actual defining equations, without cancelling
any parameter or imposing a sign condition on either real root. -/
theorem quadratic_of_chart_equations (a b c d e : ℝ)
    (h₀ : -a - d + 1 = 0)
    (h₁ : -(c*a) + c - 1 = 0)
    (h₂ : -(a*e) + d = 0)
    (h₃ : -b + 1 = 0)
    (h₄ : b*e - c = 0) : e^2 - e - 1 = 0 := by
  have hb : b = 1 := by linarith
  subst b
  have hc : c = e := by linarith
  subst c
  linear_combination (e+1)*h₁ - e*h₀ - e*h₂

theorem golden_root_not_rational (t : ℝ) (ht : t^2 - t - 1 = 0) :
    ¬ RatScalar t := by
  intro hrat
  have hs : (2*t-1)^2 = 5 := by nlinarith only [ht]
  have hscalar : RatScalar (2*t-1) :=
    ((show RatScalar 2 from ⟨2,by norm_num⟩).mul hrat).sub ⟨1,by simp⟩
  obtain ⟨q,hq⟩ := hscalar
  have hroot : (Real.sqrt 5)^2 = 5 := Real.sq_sqrt (by norm_num)
  have hirr : Irrational (Real.sqrt 5) := by
    simpa using (show Nat.Prime 5 by decide).irrational_sqrt
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp (hs.trans hroot.symm) with heq | heq
  · exact hirr ⟨q,hq.trans heq⟩
  · exact hirr ⟨-q,by simpa only [Rat.cast_neg,hq,heq,neg_neg]⟩

/-- No rational matrix has the exceptional basis family, with any labels. -/
theorem no_rational_representation
    (p : Matrix Point Coordinate ℝ) (hp : RationalCoordinates p)
    (σ : Equiv.Perm Point)
    (hcatalogue : (vectorBases p).image (fun S => S.image σ) =
      MatroidCatalogue.N8R4.family 563) : False := by
  obtain ⟨R,hR⟩ := Chart563.chart_certificate.realize_rational p hp σ hcatalogue
  let x := R.point
  have heq := R.solution.1
  change EquationsHold Chart563.E0 x at heq
  have h0 := heq 0
  have h1 := heq 1
  have h2 := heq 2
  have h3 := heq 3
  have h4 := heq 4
  norm_num [Chart563.E0,evalRat] at h0 h1 h2 h3 h4
  have hquad := quadratic_of_chart_equations
    (x (some (some none))) (x none) (x (some none))
    (x (some (some (some none)))) (x (some (some (some (some none)))))
    h0 h1 h2 h3 h4
  exact golden_root_not_rational _ hquad (hR (some (some (some (some none)))))

end Papers.RationalityTen.MatroidChecked.GoldenRationalObstruction
