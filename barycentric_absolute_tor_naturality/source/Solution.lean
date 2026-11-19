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
set_option maxHeartbeats 900000
open Classical CategoryTheory FourPapers.FilteredHomology
universe u v
variable {P K : Type u} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ)
attribute [local instance] absoluteParameterAlgebra
-- PALOMAR_CONTEXT_ORIGIN 25259
variable (hrank : ∀ p : P, faceRank p ≤ d)
variable (e : P ≃o P)
theorem palomarAbsoluteTorDegreeNaturality (j i : ℕ)
    (x : originalRelativeTorDegreePiece K hs d hrank (∅ : Set P) j i) :
    ∃ hy : originalRelativeTorOrderMap K hs d (∅ : Set P) e (by simp) i x.val ∈
        originalRelativeTorDegreePiece K hs d hrank (∅ : Set P) j i,
      (originalEmptyRelativeTorDegreeEquiv K hs d hrank j i
        ⟨originalRelativeTorOrderMap K hs d (∅ : Set P) e (by simp) i x.val, hy⟩).val =
        originalTorOrderMap K hs d e i ((originalEmptyRelativeTorDegreeEquiv K hs d hrank j i x).val) := by
  refine ⟨(originalRelativeTorDegreeAction K hs d (∅ : Set P) e (by simp) hrank j i x).property, ?_⟩
  exact congrArg Subtype.val (originalEmptyRelativeTorDegreeEquiv_equivariant K hs d hrank e j i x)
end FourPapers.Universal
