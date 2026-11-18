module

public import mixed_volume

/-! # Undecidability of mixed-volume realization
Every coefficient is an ordinary homogeneous polynomial coefficient of actual
Lebesgue volume, including repeated-index terms and lower-dimensional bodies.
Exact rational inputs are represented surjectively by finite natural triples.
Theorems retain the actual nonnegative input restriction, the uniform program
quantifier order, and all parameters in the fixed and scalar sections.
Two algorithm values are supplied through Comparator definition_names; all
geometric, automaton, representation and rational-decoding semantics are literal.
-/

@[expose] public section
noncomputable section
open Set MeasureTheory Matrix Filter Metric
open scoped BigOperators Pointwise Topology

section
open VolumePolynomials MixedVolume MixedVolume.MainResults MixedVolume.CoefficientCoding MixedVolume.Completeness MixedVolume.AutomatonWords
open MixedVolume.AutomatonMoments MixedVolume.GeneralLocus
namespace PalomarMixedVolume.MainResults
theorem theorem_1_1 :
    CoREComplete (Realizable : ArrayCode 44 3 → Prop) ∧
    CoREComplete (fun c : NonnegativeArray 44 3 => Realizable c.val) ∧
    ¬ ComputablePred (Realizable : ArrayCode 44 3 → Prop) ∧
    ¬ ComputablePred (fun c : NonnegativeArray 44 3 => Realizable c.val) ∧
    ¬ ∃ verify : ArrayCode 44 3 × ℕ → Prop, ComputablePred verify ∧
        ∀ c, Realizable c ↔ ∃ certificate, verify (c,certificate) := MixedVolume.MainResults.theorem_1_1
end PalomarMixedVolume.MainResults
end

section
open VolumePolynomials MixedVolume MixedVolume.MainResults MixedVolume.CoefficientCoding MixedVolume.Completeness MixedVolume.AutomatonWords
open MixedVolume.AutomatonMoments MixedVolume.GeneralLocus
namespace PalomarMixedVolume.MainResults
theorem theorem_1_1_all_n (n : ℕ) (hn : 44 ≤ n) :
    CoREComplete (Realizable : ArrayCode n 3 → Prop) ∧
    CoREComplete (fun c : NonnegativeArray n 3 => Realizable c.val) ∧
    ¬ ComputablePred (Realizable : ArrayCode n 3 → Prop) ∧
    ¬ ComputablePred (fun c : NonnegativeArray n 3 => Realizable c.val) ∧
    ¬ ∃ verify : ArrayCode n 3 × ℕ → Prop, ComputablePred verify ∧
        ∀ c, Realizable c ↔ ∃ certificate, verify (c,certificate) := MixedVolume.MainResults.theorem_1_1_all_n n hn
end PalomarMixedVolume.MainResults
end

section
open VolumePolynomials MixedVolume MixedVolume.MainResults MixedVolume.CoefficientCoding MixedVolume.Completeness MixedVolume.AutomatonWords
open MixedVolume.AutomatonMoments MixedVolume.GeneralLocus
namespace PalomarMixedVolume.MainResults
theorem theorem_4_3 :
    Partrec UniformEncoding.program ∧
    (∀ (s m : ℕ) (A : AutomatonMoments.RationalData s m)
      (p : Fin m → ℚ) (theta : ℚ),
      ∃ c : Represented.Code UniformEncoding.Input,
        Represented.decode c = UniformEncoding.encodeInput A p theta) ∧
    (∀ (s m : ℕ) (A : AutomatonMoments.RationalData s m) (hs : 0 < s)
      (p : Fin m → ℚ) (theta : ℚ) (c : Represented.Code UniformEncoding.Input),
      Represented.decode c = UniformEncoding.encodeInput A p theta →
        (UniformEncoding.program c).Dom ∧
        ∀ result ∈ UniformEncoding.program c,
          (Represented.decode result).1 = GeneralLocus.numberOfBodies s m ∧
          (Represented.decode result).2.length =
            RationalExtraction.interpolationSize (GeneralLocus.numberOfBodies s m) 3 ∧
          UniformEncoding.decodedArray (GeneralLocus.numberOfBodies s m) result =
            UniformQuadratic.coefficientMap A (fun j => (p j : ℝ)) (theta : ℝ)) ∧
    (∀ (s m : ℕ) (A : AutomatonMoments.RationalData s m) (hs : 0 < s),
      (∀ a : MultiIndex (GeneralLocus.numberOfBodies s m) 3,
        (UniformQuadratic.coefficientSymbol A a).totalDegree ≤ 2) ∧
      (∀ p : Fin m → ℝ, AutomatonWords.ProbabilityRow p →
        ∀ theta : ℝ, 0 < theta → theta < 1 →
          (UniformQuadratic.coefficientMap A p theta ∈
            VolumeLocus (GeneralLocus.numberOfBodies s m) 3 ↔
              A.toReal.UniversalCutpoint p theta))) := MixedVolume.MainResults.theorem_4_3
end PalomarMixedVolume.MainResults
end

section
open VolumePolynomials MixedVolume MixedVolume.FixedSection MixedVolume.CoefficientCoding MixedVolume.Completeness MixedVolume.AutomatonWords
namespace PalomarMixedVolume.FixedSection
theorem corollary_5_1_exists :
    ∃ P : Index → MvPolynomial (Fin 28) ℚ,
      (∀ a, (P a).totalDegree ≤ 2) ∧
        ¬ ∃ decision : ArrayCode 91 3 →. Bool, Partrec decision ∧
          ∀ c, (∃ p : Fin 28 → ℝ, ProbabilityRow p ∧
              realDecode c = fun a => MvPolynomial.aeval p (P a)) →
            ∃ answer : Bool, answer ∈ decision c ∧
              (answer = true ↔ Realizable c) := MixedVolume.FixedSection.corollary_5_1_exists
end PalomarMixedVolume.FixedSection
end

section
open VolumePolynomials MixedVolume MixedVolume.ScalarSection MixedVolume.CoefficientCoding MixedVolume.Completeness MixedVolume.AutomatonWords
open MixedVolume.ScalarPolynomial MvPolynomial
namespace PalomarMixedVolume.ScalarSection
theorem theorem_6_1 :
    (∀ α, (rationalCoefficient α).totalDegree ≤ 2) ∧
      coefficientMap ⁻¹' VolumeLocus 12 3 = DyadicCone.cone ∧
      (∀ (k : ℕ) (R : ℝ), 0 < R →
        ∃ a : Fin 3 → ℝ, ∃ δ : ℝ, 0 < δ ∧
          a ∈ DyadicCone.plane k ∩ Metric.ball 0 R ∧
          ∀ b, dist b a < δ → b ∈ DyadicCone.plane k →
            b ∈ frontier DyadicCone.cone ∩ Metric.ball 0 R) ∧
      ¬ TauCeti.IsSemialgebraic (VolumeLocus 12 3) := MixedVolume.ScalarSection.theorem_6_1
end PalomarMixedVolume.ScalarSection
end

section
open VolumePolynomials MixedVolume MixedVolume.ScalarSection MixedVolume.CoefficientCoding MixedVolume.Completeness MixedVolume.AutomatonWords
open MixedVolume.ScalarPolynomial MvPolynomial
namespace PalomarMixedVolume.ScalarSection
theorem theorem_6_1_all_n (n : ℕ) (hn : 12 ≤ n) :
    ∃ p : MultiIndex n 3 → MvPolynomial (Fin 3) ℚ,
      (∀ β, (p β).totalDegree ≤ 2) ∧
      (fun a β => eval₂ (algebraMap ℚ ℝ) a (p β)) ⁻¹' VolumeLocus n 3 =
        DyadicCone.cone ∧
      (∀ (k : ℕ) (R : ℝ), 0 < R →
        ∃ a : Fin 3 → ℝ, ∃ δ : ℝ, 0 < δ ∧
          a ∈ DyadicCone.plane k ∩ Metric.ball 0 R ∧
          ∀ b, dist b a < δ → b ∈ DyadicCone.plane k →
            b ∈ frontier DyadicCone.cone ∩ Metric.ball 0 R) ∧
      ¬ TauCeti.IsSemialgebraic (VolumeLocus n 3) := MixedVolume.ScalarSection.theorem_6_1_all_n n hn
end PalomarMixedVolume.ScalarSection
end
