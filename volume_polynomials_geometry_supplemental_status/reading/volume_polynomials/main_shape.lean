module

public import VolumePolynomials.ShapeNormalization
public import VolumePolynomials.NormalizedShape
public import VolumePolynomials.CanonicalShapeConditions
public import VolumePolynomials.AffineShapeTransfer
public import VolumePolynomials.HolonomyEdges
public import VolumePolynomials.Theorem73

@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped Pointwise

namespace VolumePolynomials.Holonomy

open ShapeConditions

/-- Exact graph projection of the explicit finite rational system. -/
theorem feasible_iff_area_graph (lam a : ℝ) :
    Feasible lam a ↔ 0 < lam ∧ lam < 1 ∧ a = realAreaSeries angle lam := by
  first
  | constructor
    · rintro ⟨c, ⟨K, hK⟩, hcond⟩
      have hv := hcond.ordinary_volume hK
      obtain ⟨L, hKL, hL⟩ := normalize_shape_conditions lam a K hv
      have hvL : OrdinaryConditions lam a (volumeFunction L) := by
        rw [hKL.volumeFunction_eq]
        exact hv
      obtain ⟨hlam₀, hlam₁, a₀, b₀, c₀, hA, hB, hC, ha⟩ :=
        calibrated_conditions_force_shape lam a L hL hvL
      exact ⟨hlam₀, hlam₁, ha.trans (forcedBody_area lam hlam₀.le hlam₁)⟩
    · rintro ⟨hlam₀, hlam₁, rfl⟩
      exact canonicalTuple_feasible lam hlam₀ hlam₁

/-- Every realization of every coefficient vector satisfying the system has
the specified body affinely equivalent to the exact infinite Minkowski sum. -/
theorem every_realization_forced (lam a : ℝ) (c : Coefficients 9 3)
    (K : Fin 9 → Body 3) (hreal : Realizes K c) (hcond : Holds lam a c) :
    ∃ (hlam₀ : 0 < lam) (hlam₁ : lam < 1),
      AffineCopy (forcedBody lam hlam₀.le hlam₁) (K bodyA) ∧
      ¬ TauCeti.IsSemialgebraic (K bodyA : Set ThreeSpace) := by
  first
  | have hv := hcond.ordinary_volume hreal
    obtain ⟨L, hKL, hL⟩ := normalize_shape_conditions lam a K hv
    have hvL : OrdinaryConditions lam a (volumeFunction L) := by
      rw [hKL.volumeFunction_eq]
      exact hv
    obtain ⟨hlam₀, hlam₁, a₀, b₀, c₀, hA, hB, hC, ha⟩ :=
      calibrated_conditions_force_shape lam a L hL hvL
    have hcopy := hKL.undo_affineCopy bodyA (forcedBody lam hlam₀.le hlam₁)
      embedXY embedXY_injective (embedXY a₀) hA
    exact ⟨hlam₀, hlam₁, hcopy, affineCopy_not_semialgebraic lam hlam₀ hlam₁ hcopy⟩

/-- An actual volume polynomial with no semialgebraic realization exists. -/
theorem exists_no_semialgebraic_realization :
    ∃ c : Coefficients 9 3, c ∈ VolumeLocus 9 3 ∧
      ∀ K : Fin 9 → Body 3, Realizes K c →
        ¬ TauCeti.IsSemialgebraic (K bodyA : Set ThreeSpace) := by
  first
  | obtain ⟨c, hc, hcond⟩ := canonicalTuple_feasible (1 / 2) (by norm_num) (by norm_num)
    refine ⟨c, hc, ?_⟩
    intro K hK
    obtain ⟨hlam₀, hlam₁, hcopy, hnon⟩ :=
      every_realization_forced (1 / 2) (realAreaSeries angle (1 / 2)) c K hK hcond
    exact hnon

end VolumePolynomials.Holonomy

namespace VolumePolynomials.Main

open ShapeConditions Holonomy Metric

/-- Satisfaction of an arbitrary finite list of rational polynomial equalities
and strict inequalities in the parameters and all ordinary cubic coefficients. -/
def SatisfiesShapeSystem (P Q : List RationalPolynomial)
    (lam a : ℝ) (c : Coefficients 9 3) : Prop :=
  (∀ p ∈ P, polynomialValue lam a c p = 0) ∧
  (∀ q ∈ Q, 0 < polynomialValue lam a c q)

/-- The complete principal shape-forcing theorem (Theorem 1.2).

The two finite polynomial lists have rational coefficients by type. Their
projection is the exact area graph on the full open unit interval, every
realization has the prescribed affine copy, the body has an actually infinite
set of exposed edges, and the analytic area extension has rational Taylor
coefficients, a natural boundary, no nonzero real polynomial relation, and
literal transcendence over the rational-function field.
-/
theorem shape_forcing :
    ∃ P Q : List RationalPolynomial,
      P.length = 39 ∧ Q.length = 8 ∧
      (∀ lam a : ℝ,
        (∃ c ∈ VolumeLocus 9 3, SatisfiesShapeSystem P Q lam a c) ↔
          0 < lam ∧ lam < 1 ∧ a = realAreaSeries angle lam) ∧
      (∀ (lam a : ℝ) (c : Coefficients 9 3) (K : Fin 9 → Body 3),
        Realizes K c → SatisfiesShapeSystem P Q lam a c →
          ∃ (hlam₀ : 0 < lam) (hlam₁ : lam < 1),
            AffineCopy (forcedBody lam hlam₀.le hlam₁) (K bodyA) ∧
            Set.Infinite {R : Set ThreeSpace | IsExposedEdge (K bodyA) R} ∧
            ¬ TauCeti.IsSemialgebraic (K bodyA : Set ThreeSpace)) ∧
      (∀ (lam : ℝ) (hlam₀ : 0 < lam) (hlam₁ : lam < 1),
        Set.Infinite {F : Set Plane | IsExposedEdge (forcedBody lam hlam₀.le hlam₁) F} ∧
        ¬ TauCeti.IsSemialgebraic ((Homeomorph.finTwoArrow (X := ℝ)) ⁻¹'
          (forcedBody lam hlam₀.le hlam₁ : Set Plane))) ∧
      (∀ lam : ℝ, (realAreaSeries angle lam : ℂ) = areaGeneratingFunction angle (lam : ℂ)) ∧
      AnalyticOnNhd ℂ (areaGeneratingFunction angle) (ball 0 1) ∧
      (∀ ζ : Circle, ¬ HasLocalContinuousExtension (areaGeneratingFunction angle) ζ) ∧
      (∀ n : ℕ, iteratedDeriv n (areaGeneratingFunction angle) 0 / (n.factorial : ℂ) =
        (areaTaylorCoefficient n : ℂ)) ∧
      (∀ p : Polynomial (Polynomial ℝ), p ≠ 0 →
        ¬ ∀ lam : ℝ, lam ∈ Ioo 0 1 →
          p.eval₂ (Polynomial.evalRingHom lam) (realAreaSeries angle lam) = 0) ∧
      (letI : Algebra (RatFunc ℝ) PositiveRealGerm := rationalFunctionGermAlgebra
       Transcendental (RatFunc ℝ)
         (Filter.Germ.ofFun (realAreaSeries angle) : PositiveRealGerm)) := by
  first
  | refine ⟨equations, inequalities, equations_length, inequalities_length, ?_, ?_,
      ?_, ofReal_realAreaSeries angle, theorem_7_3_analytic.1,
      theorem_7_3_analytic.2.1, theorem_7_3_analytic.2.2.1, theorem_7_3_analytic.2.2.2,
      theorem_7_3_transcendentalRatFunc⟩
    · exact feasible_iff_area_graph
    · intro lam a c K hreal hcond
      obtain ⟨hlam₀, hlam₁, hcopy, hnon⟩ := every_realization_forced lam a c K hreal hcond
      exact ⟨hlam₀, hlam₁, hcopy,
        affineCopy_infinitely_many_exposed_edges lam hlam₀ hlam₁ hcopy, hnon⟩
    · intro lam hlam₀ hlam₁
      exact ⟨forcedBody_infinitely_many_exposed_edges lam hlam₀ hlam₁,
        forcedBody_not_semialgebraic lam hlam₀ hlam₁⟩


end VolumePolynomials.Main
