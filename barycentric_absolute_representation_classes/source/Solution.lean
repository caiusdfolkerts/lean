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
variable (a : PosetGroupAction G P)
theorem palomarAbsoluteKoszulClasses (j i : ℕ) :
    ∃ hV : Module.Finite K (originalRelativeInternalHomology K hs d (∅ : Set P) hrank j i),
    ∃ hW : ∀ S : Finset (Fin d), Module.Finite K (rankSelectedCohomology K hs d hrank S i),
    ∃ A : Representation K G (originalRelativeInternalHomology K hs d (∅ : Set P) hrank j i),
    ∃ B : ∀ S : Finset (Fin d), Representation K G (rankSelectedCohomology K hs d hrank S i),
      (∀ g x, A g x = originalRelativeInternalHomologyAction K hs d hrank (∅ : Set P) (a.orderIso g) (by simp) j i x) ∧
      (∀ S g x, B S g x = rankSelectedCohomologyAction K hs d hrank (a.orderIso g) S i x) ∧
      classOf K G (@FiniteRepresentation.of K G _ _ _ _ _ hV A) =
        ∑ S : {S : Finset (Fin d) // rankSubsetDegree S = j},
          classOf K G (@FiniteRepresentation.of K G _ _ _ _ _ (hW S.val) (B S.val)) := by
  let Q : Set P := ∅
  have hQ : ∀ ⦃p q : P⦄, p ≤ q → q ∈ Q → p ∈ Q := by simp [Q]
  have hstable : ∀ g p, a.orderIso g p ∈ Q ↔ p ∈ Q := by simp [Q]
  refine ⟨originalRelativeInternalHomology_finiteDimensional K hs d Q hrank j i,
    fun S => (rankSelectedFiniteRepresentation K hs d hrank a S i).finite,
    originalRelativeInternalHomologyRepresentation K hs d hrank Q a hstable j i,
    fun S => (rankSelectedFiniteRepresentation K hs d hrank a S i).action,
    fun _ _ => rfl, fun _ _ _ => rfl, ?_⟩
  trans classOf K G (originalRelativeTorFiniteRepresentation K hs d hrank Q a hstable hQ j i)
  · apply class_equiv (originalRelativeTorDegreeEquiv K hs d hrank Q hQ j i)
    intro g x
    exact (originalRelativeTorDegreeEquiv_equivariant K hs d Q (a.orderIso g) (hstable g) hrank hQ j i x).symm
  · trans classOf K G (originalTorFiniteRepresentation K hs d hrank a j i)
    · exact class_equiv (originalEmptyRelativeTorDegreeEquiv K hs d hrank j i)
        (fun g x => originalEmptyRelativeTorDegreeEquiv_equivariant K hs d hrank (a.orderIso g) j i x)
    · exact theorem_1_2_grothendieck K hs d hrank a j i
end FourPapers.Universal
