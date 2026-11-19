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
open Classical CategoryTheory FourPapers.FilteredHomology FourPapers.RepresentationGrothendieck
universe u v
variable {P K : Type u} {G : Type v} [PartialOrder P] [OrderBot P] [Fintype P] [Field K] [Group G]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d)
variable (Q : Set P) (hQ : ∀ ⦃p q : P⦄, p ≤ q → q ∈ Q → p ∈ Q)
variable (a : PosetGroupAction G P) (hstable : ∀ g p, a.orderIso g p ∈ Q ↔ p ∈ Q)
include hQ in
theorem palomarRelativeGrothendieck (j i : ℕ) :
    ∃ hV : Module.Finite K (originalRelativeInternalHomology K hs d Q hrank j i),
    ∃ hW : ∀ S : Finset (Fin d), Module.Finite K (rankSelectedRelativeCohomology K hs d hrank Q S i),
    ∃ A : Representation K G (originalRelativeInternalHomology K hs d Q hrank j i),
    ∃ B : ∀ S : Finset (Fin d), Representation K G (rankSelectedRelativeCohomology K hs d hrank Q S i),
      (∀ g x, A g x = originalRelativeInternalHomologyAction K hs d hrank Q (a.orderIso g) (hstable g) j i x) ∧
      (∀ S g x, B S g x = (rankColoredPairOrderAut hs d hrank Q (a.orderIso g) (hstable g)).reducedCohomologyMap
        (D := rankColoredOrderComplex hs d hrank) K S ((S.card : ℤ)-i-1) x) ∧
      classOf K G (@FiniteRepresentation.of K G _ _ _ _ _ hV A) =
        ∑ S : {S : Finset (Fin d) // rankSubsetDegree S = j},
          classOf K G (@FiniteRepresentation.of K G _ _ _ _ _ (hW S.val) (B S.val)) := by
  let A := originalRelativeInternalHomologyRepresentation K hs d hrank Q a hstable j i
  let B := rankSelectedRelativeRepresentation K hs d hrank Q hQ a hstable
  refine ⟨originalRelativeInternalHomology_finiteDimensional K hs d hrank Q j i,
    fun S => (rankSelectedRelativeFiniteRepresentation K hs d hrank Q hQ a hstable S i).finite,
    A, fun S => B S i, fun _ _ => rfl, fun _ _ _ => rfl, ?_⟩
  trans classOf K G (originalRelativeTorFiniteRepresentation K hs d hrank Q a hstable hQ j i)
  · apply class_equiv (originalRelativeTorDegreeEquiv K hs d hrank Q hQ j i)
    intro g x
    exact (originalRelativeTorDegreeEquiv_equivariant K hs d Q (a.orderIso g) (hstable g) hrank hQ j i x).symm
  · exact theorem_1_2_relative_grothendieck K hs d hrank Q hQ a hstable j i
end FourPapers.Universal
