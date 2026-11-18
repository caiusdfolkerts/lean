module

public import volume_polynomials

/-! # Volume polynomials and the Heine-Shephard problem
The geometric semantics are literal convex sets, Lebesgue volume, and equality
at every nonnegative real Minkowski weight. The entry compares all principal
claims, including the exact shape series, countable characterization, strict
separation, finite certificates, rejection, and whole-sequence reconstruction.
Three algorithm values are supplied through Comparator definition_names;
no geometric concept or realizability predicate is left unspecified.
-/

@[expose] public section
noncomputable section
open Set MeasureTheory Filter Metric Polynomial
open scoped BigOperators Pointwise Topology

namespace VolumePolynomials
/-- The literal carrier of the source forced body. -/
def PalomarForcedSet (lam : ℝ) : Set (ℝ × ℝ) :=
  segmentSeries (Holonomy.weightedOrbit lam)
end VolumePolynomials
open VolumePolynomials VolumePolynomials.Main VolumePolynomials.ShapeConditions
open VolumePolynomials.Holonomy
namespace PalomarVolumePolynomials

theorem semialgebraicity_iff {n d : ℕ} (hn : 1 ≤ n) (hd : 3 ≤ d) :
    TauCeti.IsSemialgebraic (VolumeLocus n d) ↔ n ≤ 2 := VolumePolynomials.Main.semialgebraicity_iff hn hd
theorem polytope_locus_not_semialgebraic {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d) :
    ¬ TauCeti.IsSemialgebraic (FullDimensionalPolytopeLocus n d) := VolumePolynomials.Main.polytope_locus_not_semialgebraic hn hd
theorem shape_forcing :
    ∃ P Q : List RationalPolynomial,
      P.length = 39 ∧ Q.length = 8 ∧
      (∀ lam a : ℝ,
        (∃ c ∈ VolumeLocus 9 3, SatisfiesShapeSystem P Q lam a c) ↔
          0 < lam ∧ lam < 1 ∧ a = realAreaSeries angle lam) ∧
      (∀ (lam a : ℝ) (c : Coefficients 9 3) (K : Fin 9 → Body 3),
        Realizes K c → SatisfiesShapeSystem P Q lam a c →
          ∃ (hlam₀ : 0 < lam) (hlam₁ : lam < 1),
            AffineCopy (PalomarForcedSet lam) (K bodyA) ∧
            Set.Infinite {R : Set ThreeSpace | IsExposedEdge (K bodyA) R} ∧
            ¬ TauCeti.IsSemialgebraic (K bodyA : Set ThreeSpace)) ∧
      (∀ (lam : ℝ) (hlam₀ : 0 < lam) (hlam₁ : lam < 1),
        Set.Infinite {F : Set Plane | IsExposedEdge (PalomarForcedSet lam) F} ∧
        ¬ TauCeti.IsSemialgebraic ((Homeomorph.finTwoArrow (X := ℝ)) ⁻¹'
          (PalomarForcedSet lam : Set Plane))) ∧
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
  simpa only [VolumePolynomials.Holonomy.forcedBody_carrier, VolumePolynomials.PalomarForcedSet] using
    VolumePolynomials.Main.shape_forcing

theorem countable_characterization (n d : ℕ) (hd : 0 < d) :
    (∀ k, (volumeInequalityPolynomial n d k).IsHomogeneous 2) ∧
      ∀ c : Coefficients n d, c ∈ VolumeLocus n d ↔
        (∀ α, 0 ≤ c α) ∧ ∀ k : ℕ,
          0 ≤ MvPolynomial.eval₂ (algebraMap ℚ ℝ) c (volumeInequalityPolynomial n d k) := VolumePolynomials.Main.countable_characterization n d hd
theorem nonrealizable_strict_inequality (n d : ℕ) (hd : 0 < d) (c : Coefficients n d)
    (hc : c ∉ VolumeLocus n d) :
    (∃ α, c α < 0) ∨ ∃ k, RationalCertificates.realQuadratic (volumeInequalityMatrix n d k) c < 0 := VolumePolynomials.Main.nonrealizable_strict_inequality n d hd c hc
theorem finite_rational_certificate (n d : ℕ) (hd : 0 < d) (c : Coefficients n d)
    (a : ℕ → MultiIndex n d → ℚ) (ha : RationalCertificates.IsName c a) :
    c ∉ VolumeLocus n d ↔
      ∃ cert, RationalCertificates.Valid (volumeInequalityMatrix n d) a cert := VolumePolynomials.Main.finite_rational_certificate n d hd c a ha
theorem rational_rejection_terminates (n d : ℕ) (hd : 0 < d) (c : Coefficients n d)
    (a : ℕ → MultiIndex n d → ℚ) (ha : RationalCertificates.IsName c a) :
    c ∉ VolumeLocus n d ↔ ∃ j cert,
      RationalCertificates.enumerate (volumeInequalityMatrix n d) a j = some cert := VolumePolynomials.Main.rational_rejection_terminates n d hd c a ha
theorem rational_polytope_reconstruction (n d : ℕ) (hd : 0 < d)
    (c : Coefficients n d) (a : ℕ → MultiIndex n d → ℚ)
    (ha : RationalCertificates.IsName c a) :
    (c ∈ VolumeLocus n d →
      (∀ h, RationalReconstruction.reconstruct n d a h ≠ none) ∧
      ∃ K : Fin n → Body d,
        Tendsto (fun h => RationalReconstruction.stateBodies
          ((RationalReconstruction.reconstruct n d a h).getD default)) atTop (𝓝 K) ∧
        Realizes K c) ∧
    (c ∉ VolumeLocus n d ↔ ∃ h, RationalReconstruction.reconstruct n d a h = none) ∧
    (∀ h s, RationalReconstruction.reconstruct n d a h = some s →
      ∀ i, 0 ∈ s.vertices i ∧
        (RationalReconstruction.stateBodies s i : Set (Space d)) = RationalHulls.hull (s.vertices i)) := VolumePolynomials.Main.rational_polytope_reconstruction n d hd c a ha
end PalomarVolumePolynomials
