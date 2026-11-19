module
public import theorem12
@[expose] public section
noncomputable section
open scoped BigOperators DirectSum
namespace FourPapers.Universal
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Classical CategoryTheory CommAlg FourPapers.FilteredHomology
universe u
variable {P K : Type u} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d)
variable (Q : Set P) (hQ : ∀ ⦃p q : P⦄, p ≤ q → q ∈ Q → p ∈ Q)
theorem palomarRelativeRankSelectedFactor (j n i : ℕ) :
    Nonempty (barycentricRelativeBigradedHomology (P := P) K d Q j n i ≃ₗ[K]
      ∀ S : {S : Finset (Fin d) // rankSubsetDegree S = j ∧ rankSubsetWeight d S = n},
        rankSelectedRelativeCohomology K hs d hrank Q S.val i) := ⟨barycentricRelativeBigradedCohomologyEquiv K hs d hrank Q hQ j n i⟩
end
end FourPapers.Universal
