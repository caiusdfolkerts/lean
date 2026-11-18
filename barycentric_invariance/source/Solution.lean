module
public import theorem13

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial

namespace PalomarBarycentric
open FourPapers.Universal
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)

/-- The global parameter-module, usual-grading and rank-weight-filtration
clauses of Theorem 1.1, on the actual quotient presentations. -/
theorem parameterModuleComparison (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d) :
    ∃ e : BarycentricRing (P := P) K ≃ₗ[K] FaceRing K hs,
      (∀ (a : MvPolynomial (Fin d) K) x,
        e (barycentricParameterAction (P := P) K d a * x) =
          faceParameterAction K hs d a * e x) ∧
      (∀ n x, e x ∈ usualFaceDegreePiece K hs n ↔ x ∈ usualBarycentricDegreePiece K n) ∧
      (∀ n x, e x ∈ usualFaceWeightLevel K hs d n ↔ x ∈ usualBarycentricWeightLevel K d n)  := by
  obtain ⟨T⟩ := FourPapers.Universal.theorem_1_1 K hs d hrank
  exact ⟨T.parameterEquiv.toLinearEquiv, T.parameterEquiv.map_parameter_mul, T.graded, T.filtered⟩

end PalomarBarycentric


namespace PalomarBarycentric
open FourPapers.Universal
universe v
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (hs : IsSimplicialPoset P)

/-- One integral comparison extends to every coefficient ring, with actual
parameter actions, ordinary grading, the rank-weight filtration, a coherent
family on every face, and the identification of every relative restriction
kernel. The coefficient maps are literal maps of the original quotients. -/
theorem integralCoherentComparison (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d) :
    ∃ eZ : BarycentricRing (P := P) ℤ ≃ₗ[ℤ] FaceRing ℤ hs,
      ∀ (K : Type v) [CommRing K],
        ∃ (e : BarycentricRing (P := P) K ≃ₗ[K] FaceRing K hs)
          (E : CoherentEquiv (barycentricDiagram (P := P) K) (polynomialDiagram K)),
          (∀ (a : MvPolynomial (Fin d) K) x,
            e (barycentricParameterAction (P := P) K d a * x) =
              faceParameterAction K hs d a * e x) ∧
          (∀ n x, e x ∈ usualFaceDegreePiece K hs n ↔ x ∈ usualBarycentricDegreePiece K n) ∧
          (∀ n x, e x ∈ usualFaceWeightLevel K hs d n ↔ x ∈ usualBarycentricWeightLevel K d n) ∧
          (∀ x p, faceRingEvaluation K hs p (e x) = E.component p (barycentricRingEvaluation K hs p x)) ∧
          (∀ (Q : Set P) x,
            (∀ p ∈ Q, faceRingEvaluation K hs p (e x) = 0) ↔
              ∀ p ∈ Q, barycentricRingEvaluation K hs p x = 0) ∧
          (∀ x : BarycentricRing (P := P) ℤ,
            originalFaceCoefficientChange hs (Int.castRingHom K) (eZ x) =
              e (originalBarycentricCoefficientChange (P := P) (Int.castRingHom K) x))  := by
  refine ⟨(FourPapers.Universal.universalOriginalParameterComparison ℤ hs d hrank).toLinearEquiv, ?_⟩
  intro K inst
  let T := FourPapers.Universal.theoremOneComparison K hs d hrank
  refine ⟨T.parameterEquiv.toLinearEquiv, T.stalkEquiv,
    T.parameterEquiv.map_parameter_mul, T.graded, T.filtered, T.evaluation_compat, ?_, ?_⟩
  · intro Q x
    constructor
    · intro h p hp
      apply (T.stalkEquiv.component p).injective
      simpa only [map_zero] using (T.evaluation_compat x p).symm.trans (h p hp)
    · intro h p hp
      rw [T.evaluation_compat, h p hp, map_zero]
  · intro x
    exact FourPapers.Universal.universalOriginalParameterComparison_baseChange
      hs (Int.castRingHom K) d hrank x

end PalomarBarycentric
