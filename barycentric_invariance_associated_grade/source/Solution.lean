module
public import theorem13
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace PalomarBarycentricAssociatedGrade
section
open Classical MvPolynomial Finset
open FourPapers.Universal
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)
/-- Theorem 1.1's prescribed associated-graded comparison on the literal quotient rings. -/
theorem prescribedAssociatedGrade (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d) :
    ∃ e : BarycentricRing (P := P) K ≃ₗ[K] FaceRing K hs,
      (∀ (a : MvPolynomial (Fin d) K) x,
        e (barycentricParameterAction (P := P) K d a * x) =
          faceParameterAction K hs d a * e x) ∧
      (∀ n x, e x ∈ usualFaceDegreePiece K hs n ↔ x ∈ usualBarycentricDegreePiece K n) ∧
      ∃ hf : ∀ n x, e x ∈ usualFaceWeightLevel K hs d n ↔ x ∈ usualBarycentricWeightLevel K d n,
        ∀ n : ℤ,
          weightFiltrationGradeEquiv (usualBarycentricWeightLevel (P := P) K d)
            (usualFaceWeightLevel K hs d) e hf n =
          weightFiltrationGradeEquiv (usualBarycentricWeightLevel (P := P) K d)
            (usualFaceWeightLevel K hs d) (canonicalOriginalComparison K hs)
            (canonicalOriginalComparison_usualFiltered K hs d) n := by
  obtain ⟨T⟩ := FourPapers.Universal.theorem_1_1 K hs d hrank
  exact ⟨T.parameterEquiv.toLinearEquiv, T.parameterEquiv.map_parameter_mul,
    T.graded, T.filtered, T.associatedGrade⟩
end
end PalomarBarycentricAssociatedGrade
