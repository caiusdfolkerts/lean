module

public import VolumePolynomials.HolonomyArea
public import VolumePolynomials.HolonomyNonsemialgebraic
public import VolumePolynomials.AreaRatFuncTranscendence

@[expose] public section
noncomputable section

namespace VolumePolynomials.Holonomy

open scoped Pointwise
open Set MeasureTheory Metric

theorem return_pow_e1 (n : ℕ) : (returnContinuous ^ n) (1, 0) = orbit n := by
  first
  | rw [return_pow_apply]
    simp

theorem forcedBody_series_summable (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1)
    (t : SegmentChoice) :
    Summable (fun n => ((t n : ℝ) * lam ^ n) • (returnContinuous ^ n) (1, 0)) := by
  first
  | simpa only [weightedOrbit, smul_smul, return_pow_e1] using
      series_summable (weightedOrbit lam) (weightedOrbit_summable lam hlam₀ hlam₁) t

/-- The constructed body is exactly the infinite Minkowski sum in (7.10), interpreted as
all convergent choices of one point from every centered generating segment. -/
theorem forcedBody_eq_minkowski_series (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1) :
    (forcedBody lam hlam₀ hlam₁ : Set (ℝ × ℝ)) =
      {x | ∃ t : SegmentChoice,
        x = ∑' n, ((t n : ℝ) * lam ^ n) • (returnContinuous ^ n) (1, 0)} := by
  first
  | ext x
    simp only [forcedBody_carrier, segmentSeries, Set.mem_range, Set.mem_setOf_eq]
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨t, ?_⟩
      simp only [seriesPoint, weightedOrbit, smul_smul, return_pow_e1]
    · rintro ⟨t, ht⟩
      refine ⟨t, ?_⟩
      rw [ht]
      simp only [seriesPoint, weightedOrbit, smul_smul, return_pow_e1]

/-- The exact compact-convex uniqueness assertion of Theorem 7.3. -/
theorem existsUnique_forced_body (lam : ℝ) (hlam₀ : 0 < lam) (hlam₁ : lam < 1) :
    ∃! K : ConvexBody (ℝ × ℝ), (K : Set (ℝ × ℝ)) =
      centeredSegment (1, 0) + scaledReturn lam '' (K : Set (ℝ × ℝ)) := by
  first
  | refine ⟨forcedBody lam hlam₀.le hlam₁, forcedBody_fixed lam hlam₀.le hlam₁, ?_⟩
    intro K hK
    apply SetLike.coe_injective
    exact forcedBody_unique lam hlam₀.le hlam₁ K K.isCompact K.nonempty hK

/-- The geometric conclusions of Theorem 7.3 for every parameter in its full range. -/
theorem theorem_7_3_geometric (lam : ℝ) (hlam₀ : 0 < lam) (hlam₁ : lam < 1) :
    (0 < volume.real (forcedBody lam hlam₀.le hlam₁ : Set (ℝ × ℝ))) ∧
    (volume.real (forcedBody lam hlam₀.le hlam₁ : Set (ℝ × ℝ)) = realAreaSeries angle lam) ∧
    (∃ a : ℕ → ℝ × ℝ, ∀ j,
      (orbitNormal lam j).toExposed (forcedBody lam hlam₀.le hlam₁ : Set (ℝ × ℝ)) =
        {x | ∃ t : Icc (- (1/2 : ℝ)) (1/2 : ℝ),
          x = a j + (t : ℝ) • weightedOrbit lam j}) ∧
    (∀ i j : ℕ, i ≠ j → det (weightedOrbit lam i) (weightedOrbit lam j) ≠ 0) ∧
    ¬ TauCeti.IsSemialgebraic ((Homeomorph.finTwoArrow (X := ℝ)) ⁻¹'
      (forcedBody lam hlam₀.le hlam₁ : Set (ℝ × ℝ))) := by
  first
  | exact ⟨forcedBody_area_positive lam hlam₀ hlam₁, forcedBody_area lam hlam₀.le hlam₁,
      forcedBody_exposed_faces lam hlam₀ hlam₁, weightedOrbit_nonparallel lam hlam₀,
      forcedBody_not_semialgebraic lam hlam₀ hlam₁⟩

/-- The analytic and algebraic conclusions of Theorem 7.3, for the actual area formula. -/
theorem theorem_7_3_analytic :
    AnalyticOnNhd ℂ (areaGeneratingFunction angle) (ball 0 1) ∧
    (∀ ζ : Circle, ¬ HasLocalContinuousExtension (areaGeneratingFunction angle) ζ) ∧
    (∀ n : ℕ, iteratedDeriv n (areaGeneratingFunction angle) 0 / (n.factorial : ℂ) =
      (areaTaylorCoefficient n : ℂ)) ∧
    (∀ P : Polynomial (Polynomial ℝ), P ≠ 0 →
      ¬ ∀ lam : ℝ, lam ∈ Ioo 0 1 →
        P.eval₂ (Polynomial.evalRingHom lam) (realAreaSeries angle lam) = 0) := by
  first
  | exact ⟨holonomy_area_analytic_properties.1, holonomy_area_analytic_properties.2.1,
      holonomy_area_analytic_properties.2.2,
      fun P hP => realAreaSeries_no_polynomial_relation cos_angle sin_angle_pos.ne' P hP⟩


/-- Transcendence in the literal rational-function field, evaluated at the
identity germ on a right-hand neighborhood of the origin. -/
theorem theorem_7_3_transcendentalRatFunc :
    letI : Algebra (RatFunc ℝ) PositiveRealGerm := rationalFunctionGermAlgebra
    Transcendental (RatFunc ℝ)
      (Filter.Germ.ofFun (realAreaSeries angle) : PositiveRealGerm) :=
  realAreaSeries_transcendental_ratFunc cos_angle sin_angle_pos.ne'



end VolumePolynomials.Holonomy
