module
public import theorem12
@[expose] public section
noncomputable section
namespace FourPapers.Universal
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open scoped DirectSum
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
open Classical CategoryTheory FourPapers.FilteredHomology
universe u v
variable {P K : Type u} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d)
variable (Q : Set P) (hQ : ∀ ⦃p q : P⦄, p ≤ q → q ∈ Q → p ∈ Q)
include hQ in
theorem palomarRelativeWeightEquivariance (j i : ℕ) :
    ∃ F : Filtration (K := K) (originalRelativeInternalHomology K hs d Q hrank j i),
      F.level (2*d*j+1) = ⊤ ∧
      ∃ hF : ∀ (e : P ≃o P) (hsQ : ∀ p, e p ∈ Q ↔ p ∈ Q),
        Preserves F F (originalRelativeInternalHomologyAction K hs d hrank Q e hsQ j i),
      ∀ n, ∃ E : Grade F n ≃ₗ[K]
        (∀ S : {S : Finset (Fin d) // rankSubsetDegree S = j ∧ rankSubsetWeight d S = n},
          rankSelectedRelativeCohomology K hs d hrank Q S.val i),
        ∀ (e : P ≃o P) (hsQ : ∀ p, e p ∈ Q ↔ p ∈ Q) x S,
          E (gradeMap F F (originalRelativeInternalHomologyAction K hs d hrank Q e hsQ j i)
            (hF e hsQ) n x) S =
            (rankColoredPairOrderAut hs d hrank Q e hsQ).reducedCohomologyMap
              (D := rankColoredOrderComplex hs d hrank) K S.val ((S.val.card : ℤ)-i-1) (E x S) := by
  refine ⟨originalRelativeInternalHomologyFiltration K hs d Q hrank j i,
    originalRelativeInternalHomologyFiltration_finite K hs d Q hrank j i,
    fun e h => originalRelativeInternalHomologyAction_filtered K hs d hrank Q e h j i, ?_⟩
  intro n
  let B := originalRelativeAssociatedBigradedHomology K d Q hs hQ hrank j i n
  let C := barycentricRelativeBigradedCohomologyEquiv K hs d hrank Q hQ j n i
  refine ⟨B.trans C, ?_⟩
  intro e h x S
  change C (B _) S = _ (C (B x) S)
  rw [show B _ = _ from originalRelativeAssociatedBigradedHomology_equivariant K d e Q h hs hQ hrank j i n x]
  exact barycentricRelativeBigradedCohomologyEquiv_natural K hs d hrank Q hQ e h j n i (B x) S
end FourPapers.Universal
