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

namespace VolumePolynomials.PalomarGeometry
universe uPG
/-- The exact normalized interval, with explicit natural casts. -/
abbrev SegmentChoice := ℕ → Icc (- ((Nat.cast 1 : ℝ) / Nat.cast 2)) ((Nat.cast 1 : ℝ) / Nat.cast 2)
/-- The actual infinite sum of the selected segment coefficients. -/
noncomputable def seriesPoint {E : Type uPG} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (u : ℕ → E) (t : SegmentChoice) : E :=
  ∑' n, (t n : ℝ) • u n
/-- The literal range of all segment choices. -/
def segmentSeries {E : Type uPG} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (u : ℕ → E) : Set E := Set.range (seriesPoint u)
/-- The exact angle arccos(1/3), with explicit natural casts. -/
def angle : ℝ := Real.arccos ((Nat.cast 1 : ℝ) / Nat.cast 3)
/-- A whole exposed face which is a nondegenerate closed segment. -/
def IsExposedEdge {E : Type uPG} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K F : Set E) : Prop :=
  ∃ l : E →L[ℝ] ℝ, l ≠ 0 ∧ F = l.toExposed K ∧
    ∃ a v : E, v ≠ 0 ∧
      F = {x | ∃ t : Icc (- ((Nat.cast 1 : ℝ) / Nat.cast 2)) ((Nat.cast 1 : ℝ) / Nat.cast 2),
        x = a + (t : ℝ) • v}
end VolumePolynomials.PalomarGeometry

namespace VolumePolynomials
/-- The literal carrier of the source forced body. -/
def PalomarForcedSet (lam : ℝ) : Set (ℝ × ℝ) :=
  PalomarGeometry.segmentSeries (Holonomy.weightedOrbit lam)
end VolumePolynomials
namespace VolumePolynomials
/-- The actual rational hull, with zero among its explicitly listed vertices. -/
noncomputable def PalomarRationalBody {d : ℕ}
    (L : List (RationalHulls.RationalPoint d)) (hL : 0 ∈ L) : Body d where
  carrier := RationalHulls.hull L
  convex' := convex_convexHull ℝ _
  isCompact' := (RationalHulls.vertices_finite L).isCompact_convexHull ℝ
  nonempty' := ⟨(0 : Space d),
    subset_convexHull ℝ _ ⟨(0 : RationalHulls.RationalPoint d),hL,RationalHulls.realPoint_zero d⟩⟩
/-- Decode every state as its literal rational hulls, returning the singleton
zero body precisely for a vertex list omitting zero. The logical branch
uses the explicitly specified classical decision procedure. -/
noncomputable def PalomarStateBodies {n d : ℕ}
    (s : RationalReconstruction.State n d) : Fin n → Body d :=
  fun i => @dite (Body d) (0 ∈ s.vertices i) (Classical.propDecidable _)
    (fun h => PalomarRationalBody (s.vertices i) h) (fun _ => 0)
end VolumePolynomials

namespace VolumePolynomials
/-- Both constructors have the same carrier and differ only by proof fields. -/
theorem PalomarRationalBody_eq {d : ℕ} (L : List (RationalHulls.RationalPoint d))
    (hL : 0 ∈ L) : PalomarRationalBody L hL = RationalHulls.body L hL := by rfl
/-- The full state decoder agrees on every state, including invalid lists. -/
theorem PalomarStateBodies_eq {n d : ℕ} (s : RationalReconstruction.State n d) :
    PalomarStateBodies s = RationalReconstruction.stateBodies s := by
  funext i
  unfold PalomarStateBodies RationalReconstruction.stateBodies
  split_ifs <;> rfl
end VolumePolynomials

namespace VolumePolynomials
/-- Equality of the explicit normalized half with the original literal. -/
theorem palomarHalf_eq : ((Nat.cast 1 : ℝ) / Nat.cast 2) = (1/2 : ℝ) := by norm_num
/-- Equality of the explicit normalized third with the original literal. -/
theorem palomarThird_eq : ((Nat.cast 1 : ℝ) / Nat.cast 3) = (1/3 : ℝ) := by norm_num
/-- Exact equality of the original and normalized coefficient types. -/
theorem palomarSegmentChoice_oldFormula :
    PalomarGeometry.SegmentChoice = (ℕ → Icc (- (1/2 : ℝ)) (1/2 : ℝ)) :=
  congrArg (fun h : ℝ => (ℕ → Icc (-h) h)) palomarHalf_eq
/-- The literal normalized series has exactly the displayed sum. -/
theorem palomarSeriesPoint_oldFormula {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (u : ℕ → E) (t : PalomarGeometry.SegmentChoice) :
    PalomarGeometry.seriesPoint u t = ∑' n, (t n : ℝ) • u n := by rfl
/-- Coefficient-wise identity transports the entire series range in both directions. -/
theorem palomarSegmentSeries_eq_source {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (u : ℕ → E) :
    PalomarGeometry.segmentSeries u = segmentSeries u := by
  ext x
  change (∃ t : PalomarGeometry.SegmentChoice, PalomarGeometry.seriesPoint u t = x) ↔
    (∃ t : SegmentChoice, seriesPoint u t = x)
  constructor
  · rintro ⟨t, ht⟩
    let s : SegmentChoice := fun n => ⟨(t n : ℝ), by simpa only [palomarHalf_eq] using (t n).property⟩
    refine ⟨s, ?_⟩
    have hs : seriesPoint u s = PalomarGeometry.seriesPoint u t := by rfl
    exact hs.trans ht
  · rintro ⟨s, hs⟩
    let t : PalomarGeometry.SegmentChoice := fun n =>
      ⟨(s n : ℝ), by simpa only [palomarHalf_eq] using (s n).property⟩
    refine ⟨t, ?_⟩
    have ht : PalomarGeometry.seriesPoint u t = seriesPoint u s := by rfl
    exact ht.trans hs
/-- The canonical Nat eliminator retains precisely the original coefficient formula. -/
theorem palomarRationalSineCoefficient_oldFormula (n : ℕ) :
    rationalSineCoefficient n =
      (match n with
       | 0 => 0
       | k + 1 => |(Polynomial.Chebyshev.U ℚ (k : ℤ)).eval (1 / 3)|) := by
  cases n <;> rfl
/-- Exact angle equality supplies every analytic clause in the shape theorem. -/
theorem palomarAngle_oldFormula : PalomarGeometry.angle = Real.arccos (1/3) :=
  congrArg Real.arccos palomarThird_eq
theorem palomarAngle_eq_source : PalomarGeometry.angle = Holonomy.angle :=
  palomarAngle_oldFormula
/-- The complete exposed-face predicate is transported without dropping a clause. -/
theorem palomarIsExposedEdge_eq_source {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (K F : Set E) :
    PalomarGeometry.IsExposedEdge K F ↔ Holonomy.IsExposedEdge K F := by
  unfold PalomarGeometry.IsExposedEdge Holonomy.IsExposedEdge
  rw [palomarHalf_eq]
namespace ShapeConditions
/-- The distinguished label retains its original Fin numeral. -/
theorem palomarBodyA_oldFormula : bodyA = (6 : Label) := by rfl
/-- The complete parameter and coefficient substitution is unchanged. -/
theorem palomarAssignment_oldFormula (lam a : ℝ) (c : Coefficients 9 3) :
    assignment lam a c = Sum.elim (fun i : Fin 2 => if i = 0 then lam else a) c := by rfl
end ShapeConditions
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
          0 < lam ∧ lam < 1 ∧ a = realAreaSeries VolumePolynomials.PalomarGeometry.angle lam) ∧
      (∀ (lam a : ℝ) (c : Coefficients 9 3) (K : Fin 9 → Body 3),
        Realizes K c → SatisfiesShapeSystem P Q lam a c →
          ∃ (hlam₀ : 0 < lam) (hlam₁ : lam < 1),
            AffineCopy (PalomarForcedSet lam) (K bodyA) ∧
            Set.Infinite {R : Set ThreeSpace | VolumePolynomials.PalomarGeometry.IsExposedEdge (K bodyA) R} ∧
            ¬ TauCeti.IsSemialgebraic (K bodyA : Set ThreeSpace)) ∧
      (∀ (lam : ℝ) (hlam₀ : 0 < lam) (hlam₁ : lam < 1),
        Set.Infinite {F : Set Plane | VolumePolynomials.PalomarGeometry.IsExposedEdge (PalomarForcedSet lam) F} ∧
        ¬ TauCeti.IsSemialgebraic ((Homeomorph.finTwoArrow (X := ℝ)) ⁻¹'
          (PalomarForcedSet lam : Set Plane))) ∧
      (∀ lam : ℝ, (realAreaSeries VolumePolynomials.PalomarGeometry.angle lam : ℂ) = areaGeneratingFunction VolumePolynomials.PalomarGeometry.angle (lam : ℂ)) ∧
      AnalyticOnNhd ℂ (areaGeneratingFunction VolumePolynomials.PalomarGeometry.angle) (ball 0 1) ∧
      (∀ ζ : Circle, ¬ HasLocalContinuousExtension (areaGeneratingFunction VolumePolynomials.PalomarGeometry.angle) ζ) ∧
      (∀ n : ℕ, iteratedDeriv n (areaGeneratingFunction VolumePolynomials.PalomarGeometry.angle) 0 / (n.factorial : ℂ) =
        (areaTaylorCoefficient n : ℂ)) ∧
      (∀ p : Polynomial (Polynomial ℝ), p ≠ 0 →
        ¬ ∀ lam : ℝ, lam ∈ Ioo 0 1 →
          p.eval₂ (Polynomial.evalRingHom lam) (realAreaSeries VolumePolynomials.PalomarGeometry.angle lam) = 0) ∧
      (letI : Algebra (RatFunc ℝ) PositiveRealGerm := rationalFunctionGermAlgebra
       Transcendental (RatFunc ℝ)
         (Filter.Germ.ofFun (realAreaSeries VolumePolynomials.PalomarGeometry.angle) : PositiveRealGerm)) := by
  simpa only [VolumePolynomials.Holonomy.forcedBody_carrier, VolumePolynomials.PalomarForcedSet,
    VolumePolynomials.palomarSegmentSeries_eq_source, VolumePolynomials.palomarAngle_eq_source,
    VolumePolynomials.palomarIsExposedEdge_eq_source] using
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
        Tendsto (fun h => PalomarStateBodies
          ((RationalReconstruction.reconstruct n d a h).getD default)) atTop (𝓝 K) ∧
        Realizes K c) ∧
    (c ∉ VolumeLocus n d ↔ ∃ h, RationalReconstruction.reconstruct n d a h = none) ∧
    (∀ h s, RationalReconstruction.reconstruct n d a h = some s →
      ∀ i, 0 ∈ s.vertices i ∧
        (PalomarStateBodies s i : Set (Space d)) = RationalHulls.hull (s.vertices i)) := by
  have h := VolumePolynomials.Main.rational_polytope_reconstruction n d hd c a ha
  simpa only [VolumePolynomials.PalomarStateBodies_eq] using h
end PalomarVolumePolynomials
